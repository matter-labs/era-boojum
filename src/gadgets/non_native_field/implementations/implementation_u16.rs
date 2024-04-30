use crypto_bigint::CheckedMul;

use crate::cs::gates::{
    ConstantAllocatableCS, DotProductGate, FmaGateInBaseFieldWithoutConstant, UIntXAddGate,
};
use crate::cs::traits::cs::DstBuffer;
use crate::gadgets::boolean::Boolean;
use crate::gadgets::num::Num;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::traits::castable::WitnessCastable;
use crate::gadgets::traits::selectable::Selectable;
use crate::gadgets::traits::witnessable::{CSWitnessable, WitnessHookable};

use super::utils::*;
use super::*;

impl<F: SmallField, T: pairing::ff::PrimeField, const N: usize> NonNativeFieldOverU16<F, T, N>
where
    [(); N + 1]:,
{
    #[must_use]
    pub fn allocated_constant<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        value: T,
        params: &Arc<NonNativeFieldOverU16Params<T, N>>,
    ) -> Self {
        let limbs = fe_to_u16_words::<_, N>(&value);

        let limbs = limbs.map(|el| cs.allocate_constant(F::from_u64_unchecked(el as u64)));
        Self {
            limbs,
            non_zero_limbs: params.modulus_limbs,
            tracker: OverflowTracker {
                max_moduluses: params.max_mods_in_allocation,
            },
            form: RepresentationForm::Normalized,
            params: params.clone(),
            _marker: std::marker::PhantomData,
        }
    }

    #[must_use]
    pub fn allocate_checked_without_value<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        params: &Arc<NonNativeFieldOverU16Params<T, N>>,
    ) -> Self {
        let zero_var = cs.allocate_constant(F::ZERO);
        let mut limbs = [zero_var; N];
        for dst in limbs.iter_mut().take(params.modulus_limbs) {
            *dst = cs.alloc_variable_without_value();
        }

        // range check
        for limb in limbs.iter().take(params.modulus_limbs) {
            range_check_u16(cs, *limb);
        }

        let mut new = Self {
            limbs,
            non_zero_limbs: params.modulus_limbs,
            tracker: OverflowTracker {
                max_moduluses: params.max_mods_in_allocation,
            },
            form: RepresentationForm::Normalized,
            params: params.clone(),
            _marker: std::marker::PhantomData,
        };

        // for now we use explicit normalized form for allocated values
        new.enforce_reduced(cs);

        new
    }

    #[must_use]
    pub fn allocate_checked<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        witness: T,
        params: &Arc<NonNativeFieldOverU16Params<T, N>>,
    ) -> Self {
        let new = Self::allocate_checked_without_value(cs, params);

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
            let modulus_limbs = params.modulus_limbs;
            let value_fn = move |_input: &[F], dst: &mut DstBuffer<'_, '_, F>| {
                let limbs = fe_to_u16_words::<_, N>(&witness);
                for (idx, el) in limbs.into_iter().enumerate() {
                    if idx < modulus_limbs {
                        dst.push(F::from_u64_unchecked(el as u64));
                    } else {
                        assert_eq!(el, 0);
                    }
                }
            };

            let mut outputs = Vec::with_capacity(params.modulus_limbs);
            outputs.extend(
                Place::from_variables(new.limbs)
                    .into_iter()
                    .take(params.modulus_limbs),
            );

            cs.set_values_with_dependencies_vararg(&[], &outputs, value_fn);
        }

        new
    }

    pub fn enforce_reduced<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) {
        assert_eq!(self.form, RepresentationForm::Normalized);
        if self.tracker.max_moduluses == 1 && self.form == RepresentationForm::Normalized {
            return;
        }

        // assert that we only have "modulus limbs" moduluses in this element
        assert_eq!(self.non_zero_limbs, self.params.modulus_limbs);

        // sub modulus
        let modulus = self
            .params
            .modulus
            .map(|el| cs.allocate_constant(F::from_u64_unchecked(el as u64)));
        // for rare case when our modulus is exactly 16 * K bits, but we use larger representation
        let els_to_skip = N - self.params.modulus_limbs;
        let _ = u16_long_subtraction_noborrow_must_borrow(cs, &self.limbs, &modulus, els_to_skip);
        self.tracker.max_moduluses = 1;
    }

    pub fn normalize<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS)
    where
        [(); N + 1]:,
    {
        if self.tracker.max_moduluses == 1 && self.form == RepresentationForm::Normalized {
            return;
        }
        // well, we just mul by 1
        let mut one: NonNativeFieldOverU16<F, T, N> =
            Self::allocated_constant(cs, T::one(), &self.params);
        let mut normalized = self.mul(cs, &mut one);

        // assert that we only have "modulus limbs" moduluses in this element
        assert_eq!(normalized.non_zero_limbs, normalized.params.modulus_limbs);

        // sub modulus
        let modulus = self
            .params
            .modulus
            .map(|el| cs.allocate_constant(F::from_u64_unchecked(el as u64)));
        // for rare case when our modulus is exactly 16 * K bits, but we use larger representation
        let els_to_skip = N - self.params.modulus_limbs;
        let _ =
            u16_long_subtraction_noborrow_must_borrow(cs, &normalized.limbs, &modulus, els_to_skip);
        assert!(normalized.form == RepresentationForm::Normalized);
        normalized.tracker.max_moduluses = 1;

        // update self to normalized one
        *self = normalized;
    }

    #[must_use]
    pub fn add<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        let new = if self.form == RepresentationForm::Normalized
            && other.form == RepresentationForm::Normalized
        {
            let total_range = self.tracker.add(&other.tracker);
            let used_words =
                total_range.used_words_if_normalized(self.params.modulus_u1024.as_ref());
            debug_assert!(used_words <= N);

            let num_overflow_bits = total_range.overflow_over_representation(
                self.params.modulus_u1024.as_ref(),
                self.params.repr_bits(),
            );
            // classical long addition

            if num_overflow_bits == 0 {
                // all our intermediate products will fit into 16 bit limbs, including the upper one
                let zero = cs.allocate_constant(F::ZERO);
                let mut carry = zero;
                let mut result = [zero; N];
                for (idx, ((a, b), dst)) in self.limbs[..used_words]
                    .iter()
                    .zip(other.limbs[..used_words].iter())
                    .zip(result[..used_words].iter_mut())
                    .enumerate()
                {
                    let last_round = idx == used_words - 1;
                    if last_round == false {
                        let (c, new_carry) =
                            UIntXAddGate::<16>::perform_addition(cs, *a, *b, carry);
                        range_check_u16(cs, c);
                        *dst = c;
                        carry = new_carry;
                    } else {
                        let c =
                            UIntXAddGate::<16>::perform_addition_no_carry(cs, *a, *b, carry, zero);
                        range_check_u16(cs, c);
                        *dst = c;
                    }
                }

                let new = Self {
                    limbs: result,
                    non_zero_limbs: used_words,
                    tracker: total_range,
                    form: RepresentationForm::Normalized,
                    params: self.params.clone(),
                    _marker: std::marker::PhantomData,
                };

                new
            } else {
                unimplemented!("we do not support `tight` implementations yet");
            }
        } else {
            // do lazy one
            assert_eq!(self.non_zero_limbs, other.non_zero_limbs);
            let used_words = self.non_zero_limbs;
            debug_assert!(used_words <= N);

            let total_range = self.tracker.add(&other.tracker);
            assert!(total_range.max_moduluses < self.params.max_mods_before_multiplication as u32);
            assert!(total_range.max_moduluses < self.params.max_mods_to_fit);
            assert!(total_range.max_moduluses < 16);

            let mut limbs = self.limbs;
            for (dst, src) in limbs[..used_words]
                .iter_mut()
                .zip(other.limbs[..used_words].iter())
            {
                *dst = Num::from_variable(*dst)
                    .add(cs, &Num::from_variable(*src))
                    .variable;
            }

            let new = Self {
                limbs,
                non_zero_limbs: used_words,
                tracker: total_range,
                form: RepresentationForm::Lazy,
                params: self.params.clone(),
                _marker: std::marker::PhantomData,
            };

            new
        };

        if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS == true {
            if let Some(t) = cs
                .get_value_for_multiple(Place::from_variables(new.limbs))
                .wait()
            {
                for (idx, el) in t.into_iter().enumerate() {
                    if idx >= new.non_zero_limbs {
                        assert_eq!(el, F::ZERO, "failed for {:?}", new);
                    }
                }
            }
        }

        new
    }

    #[must_use]
    pub fn double<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        let mut tmp = self.clone();
        let new = self.add(cs, &mut tmp);

        if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS == true {
            if let Some(t) = cs
                .get_value_for_multiple(Place::from_variables(new.limbs))
                .wait()
            {
                for (idx, el) in t.into_iter().enumerate() {
                    if idx >= new.non_zero_limbs {
                        assert_eq!(el, F::ZERO, "failed for {:?}", new);
                    }
                }
            }
        }

        new
    }

    #[must_use]
    pub fn lazy_double<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        let mut tmp = self.clone();
        self.lazy_add(cs, &mut tmp)
    }

    // we add limbs only without range checks
    #[must_use]
    pub fn lazy_add<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        let total_range = self.tracker.add(&other.tracker);
        assert_eq!(self.non_zero_limbs, other.non_zero_limbs);
        let used_words = self.non_zero_limbs;
        debug_assert!(used_words <= N);

        let zero = cs.allocate_constant(F::ZERO);
        let mut result = [zero; N];
        for ((a, b), dst) in self.limbs[..used_words]
            .iter()
            .zip(other.limbs[..used_words].iter())
            .zip(result[..used_words].iter_mut())
        {
            let c = Num::from_variable(*a)
                .add(cs, &Num::from_variable(*b))
                .variable;
            *dst = c;
        }

        let new = Self {
            limbs: result,
            non_zero_limbs: used_words,
            tracker: total_range,
            form: RepresentationForm::Lazy,
            params: self.params.clone(),
            _marker: std::marker::PhantomData,
        };

        // assert that we never overflow limbs
        assert!(new.tracker.max_moduluses as u64 <= F::CHAR / (u16::MAX as u64));

        if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS == true {
            if let Some(t) = cs
                .get_value_for_multiple(Place::from_variables(new.limbs))
                .wait()
            {
                for (idx, el) in t.into_iter().enumerate() {
                    if idx >= new.non_zero_limbs {
                        assert_eq!(el, F::ZERO, "failed for {:?}", new);
                    }
                }
            }
        }

        new
    }

    #[must_use]
    pub fn add_many_lazy<CS: ConstraintSystem<F>, const M: usize>(
        cs: &mut CS,
        mut inputs: [&mut Self; M],
    ) -> Self {
        assert!(inputs.len() > 1);
        let [a, b] = inputs.array_chunks_mut::<2>().next().unwrap();
        let mut result = a.lazy_add(cs, b);

        for el in inputs.into_iter().skip(2) {
            result = result.lazy_add(cs, el);
        }

        // assert that we never overflow limbs
        assert!(result.tracker.max_moduluses as u64 <= F::CHAR / (u16::MAX as u64));

        result
    }

    #[must_use]
    pub fn mul<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        [(); N + 1]:,
    {
        // we prove that a * b = q * P + r

        // We also need to ensure that a*b doesn't overflow our range of intermediate representation

        // whether we use normalized or lazy form for limbs,
        // max value is irrespective of that

        let a_max = self.tracker.into_max_value(&self.params.modulus_u1024);
        let b_max = other.tracker.into_max_value(&self.params.modulus_u1024);

        assert!(
            self.tracker.max_moduluses * other.tracker.max_moduluses
                < self.params.max_mods_before_multiplication as u32
        );
        assert!(
            self.tracker.max_moduluses * other.tracker.max_moduluses < self.params.max_mods_to_fit
        );

        let lhs_max = a_max.checked_mul(&b_max).unwrap();

        // and if a or b are in "lazy" form, then multiplication of those + additions do not overflow
        // modulus. We only check worst case
        let mut max_intermediate_limb_value = (1u64 << 48) - 1;
        max_intermediate_limb_value -= u32::MAX as u64; // from potential carry
        let max_lhs_limb = match self.form {
            RepresentationForm::Normalized => u16::MAX as u64,
            RepresentationForm::Lazy => (u16::MAX as u64)
                .checked_mul(self.tracker.max_moduluses as u64)
                .unwrap(),
        };
        let max_rhs_limb = match other.form {
            RepresentationForm::Normalized => u16::MAX as u64,
            RepresentationForm::Lazy => (u16::MAX as u64)
                .checked_mul(other.tracker.max_moduluses as u64)
                .unwrap(),
        };

        assert!(max_lhs_limb < F::CHAR);
        assert!(max_rhs_limb < F::CHAR);

        let max_from_product = max_lhs_limb
            .checked_mul(max_rhs_limb)
            .unwrap()
            .checked_mul(2 * N as u64)
            .unwrap();
        assert!(max_from_product < F::CHAR);

        let (_, uf) = max_intermediate_limb_value.overflowing_sub(max_from_product);
        assert!(uf == false);

        let q_max_value = lhs_max
            .checked_div(self.params.modulus_u1024.as_ref())
            .unwrap();
        let q_max_value_bits = q_max_value.bits_vartime();
        let mut q_max_words = q_max_value_bits / 16;
        if q_max_value_bits % 16 != 0 {
            q_max_words += 1;
        }

        // we do not want to overflow too much in general
        assert!(q_max_words <= N + 1);

        let a_max_words = self.non_zero_limbs;
        let b_max_words = other.non_zero_limbs;

        // then allocate q and r
        let mut q = [Variable::placeholder(); N + 1];
        let zero_var = cs.allocate_constant(F::ZERO);

        let mut r = [zero_var; N];
        // only lowest limbs are non-zero
        for dst in r.iter_mut().take(self.params.modulus_limbs) {
            *dst = cs.alloc_variable_without_value();
        }
        for dst in q.iter_mut().take(q_max_words) {
            *dst = cs.alloc_variable_without_value();
        }

        if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS == true {
            if let Some(t) = cs
                .get_value_for_multiple(Place::from_variables(self.limbs))
                .wait()
            {
                for (idx, el) in t.into_iter().enumerate() {
                    if idx >= a_max_words {
                        assert_eq!(el, F::ZERO, "failed for {:?}", self);
                    }
                }
            }

            if let Some(t) = cs
                .get_value_for_multiple(Place::from_variables(other.limbs))
                .wait()
            {
                for (idx, el) in t.into_iter().enumerate() {
                    if idx >= b_max_words {
                        assert_eq!(el, F::ZERO, "failed for {:?}", self);
                    }
                }
            }
        }

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
            let params = self.params.clone();

            let value_fn = move |inputs: &[F], buffer: &mut DstBuffer<'_, '_, F>| {
                debug_assert_eq!(inputs.len(), N * 2);

                let a = unnormalized_u16_field_words_to_u1024(&inputs[..N]);
                for el in inputs[a_max_words..N].iter() {
                    assert!(el.is_zero());
                }
                let b = unnormalized_u16_field_words_to_u1024(&inputs[N..]);
                for el in inputs[(N + b_max_words)..].iter() {
                    assert!(el.is_zero());
                }

                let product = a.checked_mul(&b).unwrap();
                assert!(
                    product <= params.max_product_before_reduction,
                    "can not reduce product of 0x{:x} and 0x{:x}",
                    &a,
                    &b
                );
                let (q, r) = product.div_rem(&params.modulus_u1024);

                // first q, then r
                let mut j = 0;
                for word in q.as_words().iter() {
                    if j >= q_max_words {
                        assert_eq!(*word, 0);
                        continue;
                    }
                    let mut word = *word;
                    for _ in 0..4 {
                        if j >= q_max_words {
                            break;
                        }
                        let chunk = word as u16;
                        word >>= 16;
                        buffer.push(F::from_u64_unchecked(chunk as u64));
                        j += 1;
                    }
                }

                let mut j = 0;
                for word in r.as_words().iter() {
                    if j >= params.modulus_limbs {
                        assert_eq!(*word, 0);
                        continue;
                    }
                    let mut word = *word;
                    for _ in 0..4 {
                        if j >= params.modulus_limbs {
                            break;
                        }
                        let chunk = word as u16;
                        word >>= 16;
                        buffer.push(F::from_u64_unchecked(chunk as u64));
                        j += 1;
                    }
                }
            };

            let mut dependencies = Vec::with_capacity(N * 2);
            dependencies.extend(Place::from_variables(self.limbs));
            dependencies.extend(Place::from_variables(other.limbs));

            let mut outputs = Vec::with_capacity(q_max_words + N);
            outputs.extend(q[..q_max_words].iter().map(|el| Place::from_variable(*el)));
            outputs.extend(
                Place::from_variables(r)
                    .into_iter()
                    .take(self.params.modulus_limbs),
            );

            cs.set_values_with_dependencies_vararg(&dependencies, &outputs, value_fn);
        }

        // range_check
        for src in q.iter().take(q_max_words) {
            range_check_u16(cs, *src);
        }

        for src in r.iter() {
            range_check_u16(cs, *src);
        }

        // we follow an aproach that we try to form a linear combination for a word of intermediate product of lhs - rhs, shift it right
        // and range-check to get carry

        let mut lhs_products_buffer = Vec::with_capacity(N * N + 2);
        let mut rhs_products_buffer = Vec::with_capacity(N * N + N + 2);

        // first we need to create a quotient
        let zero = cs.allocate_constant(F::ZERO);
        let one = cs.allocate_constant(F::ONE);
        let minus_one = cs.allocate_constant(F::MINUS_ONE);
        let mut swap_carry_sign = Boolean::allocated_constant(cs, false);

        // example
        // let mut carry = (q[0] * p[0] + r[0] - a[0] * b[0]) >> 16;
        // carry = (q[1] * p[0] + q[0] * p[1] + r[1] - a[1] * b[0] - a[0] * b[0] + carry) >> 16;

        let mut carry = None;
        for intermediate_word_idx in 0..(N * 2) {
            let first_round = intermediate_word_idx == 0;
            let last_round = intermediate_word_idx == N * 2 - 1;
            if first_round == false {
                assert!(carry.is_some());
            }

            lhs_products_buffer.clear();
            rhs_products_buffer.clear();

            for (i, a_word) in self.limbs[..a_max_words].iter().enumerate() {
                for (j, b_word) in other.limbs[..b_max_words].iter().enumerate() {
                    if i + j == intermediate_word_idx {
                        // for LHS we need to push a product
                        lhs_products_buffer.push((*a_word, *b_word));
                    }
                }
            }

            for (i, q_word) in q[..q_max_words].iter().enumerate() {
                for (j, p_word) in self.params.modulus.iter().enumerate() {
                    if *p_word == 0 {
                        continue;
                    }
                    if i + j == intermediate_word_idx {
                        let modulus_subword = F::from_raw_u64_unchecked(*p_word as u64);
                        // for LHS we need to push a product
                        rhs_products_buffer.push((*q_word, modulus_subword));
                    }
                }
            }
            // then linear parts
            if intermediate_word_idx < self.params.modulus_limbs {
                rhs_products_buffer.push((r[intermediate_word_idx], F::ONE));
            }

            if let Some(carry) = carry.take() {
                // place to lhs
                let carry_coeff = Selectable::conditionally_select(
                    cs,
                    swap_carry_sign,
                    &Num::from_variable(minus_one),
                    &Num::from_variable(one),
                )
                .variable;
                lhs_products_buffer.push((carry, carry_coeff));
            }

            // now compute, shift and enforce
            // LHS is dot-product
            let mut num_terms_to_consume = lhs_products_buffer.len();
            let mut previous = None;

            let mut lhs_iter = lhs_products_buffer.drain(..);
            if num_terms_to_consume == 1 {
                let (a, b) = lhs_iter.next().unwrap();
                let intermediate = FmaGateInBaseFieldWithoutConstant::compute_fma(
                    cs,
                    F::ONE,
                    (a, b),
                    F::ZERO,
                    zero,
                );

                num_terms_to_consume -= 1;
                previous = Some(intermediate);
            } else {
                let max_rounds = (num_terms_to_consume / 3) + 1;

                for _ in 0..max_rounds {
                    if num_terms_to_consume == 0 {
                        break;
                    }
                    let mut terms = [(Variable::placeholder(), Variable::placeholder()); 4];
                    for dst in terms.iter_mut() {
                        // if we have something to drag from previous - take it
                        if let Some(previous) = previous.take() {
                            *dst = (previous, one);
                        } else {
                            // otherwise try to take from iterator
                            if let Some(next) = lhs_iter.next() {
                                num_terms_to_consume -= 1;
                                *dst = next;
                            } else {
                                *dst = (zero, zero);
                            }
                        }
                    }
                    let intermediate = DotProductGate::<4>::compute_dot_product(cs, terms);

                    previous = Some(intermediate);
                }
            }

            assert_eq!(num_terms_to_consume, 0);
            assert!(lhs_iter.next().is_none());

            let lhs_accumulated = if let Some(previous) = previous {
                previous
            } else {
                zero
            };
            // RHS is linear combination
            let rhs_accumulated = if rhs_products_buffer.len() > 0 {
                Num::linear_combination(cs, &rhs_products_buffer).variable
            } else {
                zero
            };

            let (swap_next_carry, (low, high)) =
                split_out_u32_carry_from_zero_low(cs, lhs_accumulated, rhs_accumulated);

            swap_carry_sign = swap_next_carry;

            if last_round == false {
                // now create carry
                let new_carry = FmaGateInBaseFieldWithoutConstant::compute_fma(
                    cs,
                    F::from_u64_unchecked(1u64 << 16),
                    (one, high),
                    F::ONE,
                    low,
                );

                carry = Some(new_carry);
            } else {
                Num::enforce_equal(cs, &Num::from_variable(low), &Num::from_variable(zero));
                Num::enforce_equal(cs, &Num::from_variable(high), &Num::from_variable(zero));
            }
        }

        assert!(carry.is_none());

        let mut new = Self {
            limbs: r,
            non_zero_limbs: self.params.modulus_limbs,
            tracker: OverflowTracker {
                max_moduluses: self.params.max_mods_in_allocation,
            },
            form: RepresentationForm::Normalized,
            params: self.params.clone(),
            _marker: std::marker::PhantomData,
        };

        // enforce that r is canonical
        new.enforce_reduced(cs);

        new
    }

    #[must_use]
    pub fn square<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self
    where
        [(); N + 1]:,
    {
        let mut other = self.clone();
        self.mul(cs, &mut other)
    }

    #[allow(unreachable_code)]
    #[must_use]
    pub fn negated<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self
    where
        [(); N + 1]:,
    {
        let new = if self.form == RepresentationForm::Normalized {
            if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS == true {
                if let Some(t) = cs
                    .get_value_for_multiple(Place::from_variables(self.limbs))
                    .wait()
                {
                    for (idx, el) in t.into_iter().enumerate() {
                        if idx >= self.non_zero_limbs {
                            assert_eq!(el, F::ZERO, "failed for {:?}", self);
                        }
                    }
                }
            }

            // lazy path is not possible in this case
            let modulus_shifted = self
                .params
                .modulus_u1024
                .wrapping_mul(&U1024::from_word(self.tracker.max_moduluses as u64));
            let used_words = self
                .tracker
                .used_words_if_normalized(self.params.modulus_u1024.as_ref());
            debug_assert!(used_words <= N);

            let modulus_words = u1024_to_u16_words::<N>(&modulus_shifted);
            let modulus_words =
                modulus_words.map(|el| cs.allocate_constant(F::from_u64_unchecked(el as u64)));
            let limbs =
                u16_long_subtraction_noborrow(cs, &modulus_words, &self.limbs, N - used_words);

            let new = Self {
                limbs,
                non_zero_limbs: used_words,
                tracker: OverflowTracker { max_moduluses: 2 }, // NOTE: if self == 0, then limbs will be == modulus, so use 2
                form: RepresentationForm::Normalized,
                params: self.params.clone(),
                _marker: std::marker::PhantomData,
            };

            new
        } else {
            todo!();
            // a little tricky here. We want to fill all the words, or at least some of them
            assert!(self.non_zero_limbs == N || self.non_zero_limbs == N - 1);

            if self.non_zero_limbs == N {
                todo!();
                assert!(self.params.modulus_is_word_aligned() == false);
                let mut limbs = self.limbs;
                for (dst, src) in limbs.iter_mut().zip(self.params.modulus.iter()) {
                    assert!(
                        (*src as u64)
                            .checked_mul(self.tracker.max_moduluses as u64)
                            .unwrap()
                            < F::CHAR
                    );
                    let modulus_lazy = F::from_u64_unchecked(
                        (*src as u64)
                            .checked_mul(self.tracker.max_moduluses as u64)
                            .unwrap(),
                    );
                    let value = Num::allocated_constant(cs, modulus_lazy)
                        .sub(cs, &Num::from_variable(*dst));
                    *dst = value.get_variable();
                }

                let new = Self {
                    limbs,
                    non_zero_limbs: self.non_zero_limbs,
                    tracker: self.tracker,
                    form: RepresentationForm::Lazy,
                    params: self.params.clone(),
                    _marker: std::marker::PhantomData,
                };

                new
            } else {
                assert!(self.params.modulus_is_word_aligned() == true);

                let mut limbs = self.limbs;
                let used_words = self.non_zero_limbs;
                for (dst, src) in limbs[..used_words]
                    .iter_mut()
                    .zip(self.params.modulus[..used_words].iter())
                {
                    assert!(
                        (*src as u64)
                            .checked_mul(self.tracker.max_moduluses as u64)
                            .unwrap()
                            < F::CHAR
                    );
                    let modulus_lazy = F::from_u64_unchecked(
                        (*src as u64)
                            .checked_mul(self.tracker.max_moduluses as u64)
                            .unwrap(),
                    );
                    let value = Num::allocated_constant(cs, modulus_lazy)
                        .sub(cs, &Num::from_variable(*dst));
                    *dst = value.get_variable();
                }

                let new = Self {
                    limbs,
                    non_zero_limbs: self.non_zero_limbs,
                    tracker: self.tracker,
                    form: RepresentationForm::Lazy,
                    params: self.params.clone(),
                    _marker: std::marker::PhantomData,
                };

                new
            }
        };

        if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS == true {
            if let Some(t) = cs
                .get_value_for_multiple(Place::from_variables(new.limbs))
                .wait()
            {
                for (idx, el) in t.into_iter().enumerate() {
                    if idx >= new.non_zero_limbs {
                        assert_eq!(el, F::ZERO, "failed for {:?} -> {:?}", self, new);
                    }
                }
            }
        }

        new
    }

    #[must_use]
    pub fn sub<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        // sub is only lazy for now
        let mut other_negated = other.negated(cs);
        let new = self.add(cs, &mut other_negated);

        if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS == true {
            if let Some(t) = cs
                .get_value_for_multiple(Place::from_variables(new.limbs))
                .wait()
            {
                for (idx, el) in t.into_iter().enumerate() {
                    if idx >= new.non_zero_limbs {
                        assert_eq!(el, F::ZERO, "failed for {:?}", new);
                    }
                }
            }
        }

        new
    }

    #[must_use]
    pub fn allocate_inverse_or_zero<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Self {
        let new = Self::allocate_checked_without_value(cs, &self.params);

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
            let modulus_u1024 = self.params.modulus_u1024;
            let modulus_limbs = self.params.modulus_limbs;
            let value_fn = move |input: &[F], dst: &mut DstBuffer<'_, '_, F>| {
                let mut value = unnormalized_u16_field_words_to_u1024(input);
                value = value.checked_rem(&modulus_u1024).unwrap();

                let inner = u1024_to_fe::<T>(&value);
                match inner.inverse() {
                    Some(inversed) => {
                        let words: [F; N] =
                            fe_to_u16_words(&inversed).map(|el| F::from_u64_unchecked(el as u64));
                        for (idx, word) in words.into_iter().enumerate() {
                            if idx < modulus_limbs {
                                dst.push(word)
                            } else {
                                assert!(word.is_zero());
                            }
                        }
                    }
                    None => {
                        for _ in 0..modulus_limbs {
                            dst.push(F::ZERO);
                        }
                    }
                }
            };

            let mut outputs = Vec::with_capacity(modulus_limbs);
            outputs.extend(
                Place::from_variables(new.limbs)
                    .into_iter()
                    .take(modulus_limbs),
            );

            cs.set_values_with_dependencies_vararg(
                &Place::from_variables(self.limbs),
                &outputs,
                value_fn,
            );
        }

        new
    }

    #[must_use]
    pub fn inverse_unchecked<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self
    where
        [(); N + 1]:,
    {
        let mut inverse = self.allocate_inverse_or_zero(cs);
        let product = self.mul(cs, &mut inverse);
        // enforce that product is normalized 1
        let zero = cs.allocate_constant(F::ZERO);
        let one = cs.allocate_constant(F::ONE);
        for (idx, el) in product.limbs.into_iter().enumerate() {
            if idx == 0 {
                Num::enforce_equal(cs, &Num::from_variable(el), &Num::from_variable(one));
            } else {
                Num::enforce_equal(cs, &Num::from_variable(el), &Num::from_variable(zero));
            }
        }

        inverse
    }

    #[must_use]
    pub fn div_unchecked<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        [(); N + 1]:,
    {
        let mut inversed = other.inverse_unchecked(cs);
        self.mul(cs, &mut inversed)
    }

    #[must_use]
    pub fn is_zero<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Boolean<F>
    where
        [(); N + 1]:,
    {
        self.normalize(cs);
        let zeroes = self.limbs.map(|el| Num::from_variable(el).is_zero(cs));

        Boolean::multi_and(cs, &zeroes)
    }

    #[must_use]
    pub fn mask<CS: ConstraintSystem<F>>(&self, cs: &mut CS, masking_bit: Boolean<F>) -> Self {
        let mut new = self.clone();
        for dst in new.limbs.iter_mut() {
            *dst = Num::from_variable(*dst).mask(cs, masking_bit).variable;
        }

        new
    }

    #[must_use]
    pub fn mask_negated<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        masking_bit: Boolean<F>,
    ) -> Self {
        let mut new = self.clone();
        for dst in new.limbs.iter_mut() {
            *dst = Num::from_variable(*dst)
                .mask_negated(cs, masking_bit)
                .variable;
        }

        new
    }

    #[must_use]
    pub fn equals<CS: ConstraintSystem<F>>(cs: &mut CS, a: &mut Self, b: &mut Self) -> Boolean<F> {
        a.normalize(cs);
        b.normalize(cs);

        let equalities: [_; N] = std::array::from_fn(|i| {
            Num::equals(
                cs,
                &Num::from_variable(a.limbs[i]),
                &Num::from_variable(b.limbs[i]),
            )
        });

        Boolean::multi_and(cs, &equalities)
    }
}

impl<F: SmallField, T: pairing::ff::PrimeField, const N: usize> CSAllocatable<F>
    for NonNativeFieldOverU16<F, T, N>
{
    type Witness = FFProxyValue<T, N>;

    fn placeholder_witness() -> Self::Witness {
        FFProxyValue { value: T::zero() }
    }
    fn allocate_without_value<CS: ConstraintSystem<F>>(_cs: &mut CS) -> Self {
        unimplemented!("we need parameters to do it")
    }
    fn allocate<CS: ConstraintSystem<F>>(_cs: &mut CS, _witness: Self::Witness) -> Self {
        unimplemented!("we need parameters to do it")
    }
}

// We need this to ensure no conflicting implementations without negative impls

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash)]
pub struct FFProxyValue<T: pairing::ff::PrimeField, const N: usize> {
    value: T,
}

impl<T: pairing::ff::PrimeField, const N: usize> FFProxyValue<T, N> {
    pub const fn get(&self) -> T {
        self.value
    }
}

impl<F: SmallField, T: pairing::ff::PrimeField, const N: usize> WitnessCastable<F, [F; N]>
    for FFProxyValue<T, N>
{
    fn cast_from_source(witness: [F; N]) -> Self {
        // note that we do not make a judgement about reduction here, so it's kind of expecnsive
        let mut modulus_u1024 = U1024::ZERO;
        for (dst, src) in modulus_u1024
            .as_words_mut()
            .iter_mut()
            .zip(T::char().as_ref())
        {
            *dst = *src;
        }
        let modulus_u1024 = NonZero::<U1024>::new(modulus_u1024).unwrap();

        let mut value = U1024::ZERO;
        for (idx, el) in witness.into_iter().enumerate() {
            let tmp = U1024::from_word(el.as_u64_reduced());
            value = value.wrapping_add(&tmp.shl_vartime(idx * 16));
        }

        let (_, rem) = value.div_rem(&modulus_u1024);

        let inner = u1024_to_fe::<T>(&rem);

        Self { value: inner }
    }

    fn cast_into_source(self) -> [F; N] {
        unimplemented!("we allow non-reduced representations, so we should not use this function")
    }
}

use crate::gadgets::traits::castable::Convertor;

impl<F: SmallField, T: pairing::ff::PrimeField, const N: usize> CSWitnessable<F, N>
    for NonNativeFieldOverU16<F, T, N>
{
    type ConversionFunction = Convertor<F, [F; N], FFProxyValue<T, N>>;

    fn witness_from_set_of_values(values: [F; N]) -> Self::Witness {
        <FFProxyValue<T, N> as WitnessCastable<F, [F; N]>>::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; N] {
        self.limbs
    }
}

impl<F: SmallField, T: pairing::ff::PrimeField, const N: usize> WitnessHookable<F>
    for NonNativeFieldOverU16<F, T, N>
{
    fn witness_hook<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
    ) -> Box<dyn FnOnce() -> Option<Self::Witness>> {
        let raw_witness = self.get_witness(cs);
        Box::new(move || raw_witness.wait())
    }
}

impl<F: SmallField, T: pairing::ff::PrimeField, const N: usize> Selectable<F>
    for NonNativeFieldOverU16<F, T, N>
{
    const SUPPORTS_PARALLEL_SELECT: bool = false;

    #[must_use]
    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self {
        let a_limbs = a.limbs.map(|el| Num::from_variable(el));
        let b_limbs = b.limbs.map(|el| Num::from_variable(el));

        let selected_limbs = Num::parallel_select(cs, flag, &a_limbs, &b_limbs);

        let max_moduluses = std::cmp::max(a.tracker.max_moduluses, b.tracker.max_moduluses);
        let new_tracker = OverflowTracker { max_moduluses };

        let new_form = match (a.form, b.form) {
            (RepresentationForm::Normalized, RepresentationForm::Normalized) => {
                RepresentationForm::Normalized
            }
            _ => RepresentationForm::Lazy,
        };

        let used_words = std::cmp::max(a.non_zero_limbs, b.non_zero_limbs);

        Self {
            limbs: selected_limbs.map(|el| el.get_variable()),
            non_zero_limbs: used_words,
            tracker: new_tracker,
            form: new_form,
            params: a.params.clone(),
            _marker: std::marker::PhantomData,
        }
    }
}

#[cfg(test)]
mod test {
    use std::alloc::Global;

    use super::*;
    use crate::cs::*;

    use crate::cs::gates::*;
    use crate::cs::traits::gate::GatePlacementStrategy;
    use crate::dag::CircuitResolverOpts;
    use crate::field::goldilocks::GoldilocksField;
    use crate::gadgets::tables::range_check_16_bits::{
        create_range_check_16_bits_table, RangeCheck16BitsTable,
    };
    use crate::worker::Worker;
    use pairing::ff::{Field, PrimeField};

    type F = GoldilocksField;
    type Ext = pairing::bn256::Fq;
    type NN = NonNativeFieldOverU16<F, Ext, 16>;
    type Params = NonNativeFieldOverU16Params<Ext, 16>;

    #[test]
    fn test_mul() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 60,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 4,
        };

        use crate::config::DevCSConfig;
        type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, 1 << 18);
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = builder.allow_lookup(
            crate::cs::LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                width: 1,
                num_repetitions: 10,
                share_table_id: true,
            },
        );

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ReductionGate::<F, 4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = DotProductGate::<4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = UIntXAddGate::<16>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = SelectionGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(CircuitResolverOpts::new(1 << 20));

        // add tables
        let table = create_range_check_16_bits_table();
        owned_cs.add_lookup_table::<RangeCheck16BitsTable, 1>(table);

        let cs = &mut owned_cs;

        let a_value = Ext::from_str("123").unwrap();
        let b_value = Ext::from_str("456").unwrap();

        let params = Params::create();
        let params = std::sync::Arc::new(params);

        let mut a = NN::allocate_checked(cs, a_value, &params);
        let mut b = NN::allocate_checked(cs, b_value, &params);

        let c = a.mul(cs, &mut b);

        let mut c_value = a_value;
        c_value.mul_assign(&b_value);

        let witness = c.witness_hook(&*cs)().unwrap().get();

        assert_eq!(c_value, witness);

        let worker = Worker::new_with_num_threads(8);

        drop(cs);
        owned_cs.pad_and_shrink();
        let mut owned_cs = owned_cs.into_assembly::<Global>();
        assert!(owned_cs.check_if_satisfied(&worker));
    }
}
