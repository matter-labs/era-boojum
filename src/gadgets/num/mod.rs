use super::boolean::Boolean;
use super::impls::lc::linear_combination_collapse;
use super::*;
use crate::cs::gates::zero_check::ZeroCheckGate;
use crate::cs::gates::{ConditionalSwapGate, ConstantAllocatableCS, ZeroCheckMemoizableCS};
use crate::cs::gates::{DotProductGate, ParallelSelectionGate, ReductionGate, SelectionGate};

use crate::config::*;
use crate::cs::gates::fma_gate_without_constant::{
    FmaGateInBaseFieldWithoutConstant, FmaGateInBaseWithoutConstantParams,
};
use crate::cs::gates::ReductionByPowersGate;
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::cs::DstBuffer;
use crate::gadgets::impls::limbs_decompose::*;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::u8::UInt8;
use crate::gadgets::u8::*;
use crate::utils::LSBIterator;
use crate::{cs::Variable, field::SmallField};
use arrayvec::ArrayVec;

pub mod prime_field_like;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct Num<F: SmallField> {
    pub(crate) variable: Variable,
    pub(crate) _marker: std::marker::PhantomData<F>,
}

// it's allocatable and witnessable

impl<F: SmallField> CSAllocatable<F> for Num<F> {
    type Witness = F;
    fn placeholder_witness() -> Self::Witness {
        F::ZERO
    }

    #[inline(always)]
    #[must_use]
    fn allocate_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let var = cs.alloc_variable_without_value();

        Self {
            variable: var,
            _marker: std::marker::PhantomData,
        }
    }

    #[inline(always)]
    #[must_use]
    fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let var = cs.alloc_single_variable_from_witness(witness);

        Self {
            variable: var,
            _marker: std::marker::PhantomData,
        }
    }

    #[inline(always)]
    #[must_use]
    fn allocate_constant<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let var = cs.allocate_constant(witness);

        Self {
            variable: var,
            _marker: std::marker::PhantomData,
        }
    }
}

use crate::gadgets::traits::witnessable::CSWitnessable;

use super::traits::castable::{Convertor, WitnessCastable};
use super::traits::witnessable::WitnessHookable;

impl<F: SmallField> CSWitnessable<F, 1> for Num<F> {
    type ConversionFunction = Convertor<F, [F; 1], F>;

    fn witness_from_set_of_values(values: [F; 1]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; 1] {
        [self.get_variable()]
    }
}

impl<F: SmallField, const N: usize> CSWitnessable<F, N> for [Num<F>; N] {
    type ConversionFunction = Convertor<F, [F; N], [F; N]>;

    fn witness_from_set_of_values(values: [F; N]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; N] {
        self.map(|el| el.get_variable())
    }
}

impl<F: SmallField> WitnessHookable<F> for Num<F> {
    fn witness_hook<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
    ) -> Box<dyn FnOnce() -> Option<Self::Witness>> {
        let raw_witness = self.get_witness(cs);
        Box::new(move || raw_witness.wait())
    }
}

// impl<F: SmallField, const N: usize> WitnessHookable<F> for [Num<F>; N] {
//     fn witness_hook<CS: ConstraintSystem<F>>(
//         &self,
//         cs: &CS,
//     ) -> Box<dyn FnOnce() -> Option<Self::Witness>> {
//         let raw_witness = self.get_witness(cs);
//         Box::new(move || raw_witness.wait())
//     }
// }

use crate::gadgets::traits::selectable::Selectable;

impl<F: SmallField> Selectable<F> for Num<F> {
    #[must_use]
    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self {
        if a.get_variable() == b.get_variable() {
            return *a;
        }

        if cs.gate_is_allowed::<SelectionGate>() {
            let result_var =
                SelectionGate::select(cs, a.get_variable(), b.get_variable(), flag.get_variable());

            Self {
                variable: result_var,
                _marker: std::marker::PhantomData,
            }
        } else {
            unimplemented!()
        }
    }

    const SUPPORTS_PARALLEL_SELECT: bool = true;

    #[must_use]
    fn parallel_select<CS: ConstraintSystem<F>, const N: usize>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &[Self; N],
        b: &[Self; N],
    ) -> [Self; N] {
        if N >= 4 && cs.gate_is_allowed::<ParallelSelectionGate<4>>() {
            let mut result = [Variable::placeholder(); N];

            let mut a = a.array_chunks::<4>();
            let mut b = b.array_chunks::<4>();
            let mut dst = result.array_chunks_mut::<4>();

            for ((a, b), dst) in (&mut a).zip(&mut b).zip(&mut dst) {
                let a = a.map(|el| el.get_variable());
                let b = b.map(|el| el.get_variable());
                *dst = ParallelSelectionGate::<4>::select(cs, &a, &b, flag.get_variable());
            }

            if a.remainder().is_empty() == false {
                for ((a, b), dst) in (a.remainder().iter())
                    .zip(b.remainder().iter())
                    .zip(dst.into_remainder().iter_mut())
                {
                    *dst = Self::conditionally_select(cs, flag, a, b).get_variable();
                }
            }

            result.map(|el| Num::from_variable(el))
        } else {
            let mut result = [Variable::placeholder(); N];
            for ((a, b), dst) in a.iter().zip(b.iter()).zip(result.iter_mut()) {
                *dst = Self::conditionally_select(cs, flag, a, b).get_variable();
            }

            result.map(|el| Num::from_variable(el))
        }
    }
}

impl<F: SmallField> Num<F> {
    #[inline]
    #[must_use]
    pub const fn get_variable(&self) -> Variable {
        self.variable
    }

    #[inline(always)]
    #[must_use]
    pub const fn from_variable(var: Variable) -> Self {
        Self {
            variable: var,
            _marker: std::marker::PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub fn allocated_constant<CS: ConstraintSystem<F>>(cs: &mut CS, constant: F) -> Self {
        let constant_var = cs.allocate_constant(constant);

        Self {
            variable: constant_var,
            _marker: std::marker::PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub fn zero<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::allocated_constant(cs, F::ZERO)
    }

    #[inline]
    #[must_use]
    pub fn is_zero<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Boolean<F> {
        if let Some(existing_check) = cs.check_is_zero_memoization(self.variable) {
            return unsafe { Boolean::from_variable_unchecked(existing_check) };
        }

        let result_var = ZeroCheckGate::check_if_zero(cs, self.get_variable());

        cs.set_is_zero_memoization(self.variable, result_var);

        Boolean {
            variable: result_var,
            _marker: std::marker::PhantomData,
        }
    }

    #[must_use]
    pub fn add<CS: ConstraintSystem<F>>(&self, cs: &mut CS, other: &Self) -> Self {
        if cs.gate_is_allowed::<FmaGateInBaseFieldWithoutConstant<F>>() {
            let one = cs.allocate_constant(F::ONE);
            let result_var = FmaGateInBaseFieldWithoutConstant::compute_fma(
                cs,
                F::ONE,
                (self.get_variable(), one),
                F::ONE,
                other.get_variable(),
            );

            Self {
                variable: result_var,
                _marker: std::marker::PhantomData,
            }
        } else {
            unimplemented!()
        }
    }

    #[must_use]
    pub fn sub<CS: ConstraintSystem<F>>(&self, cs: &mut CS, other: &Self) -> Self {
        if cs.gate_is_allowed::<FmaGateInBaseFieldWithoutConstant<F>>() {
            let one = cs.allocate_constant(F::ONE);
            let result_var = FmaGateInBaseFieldWithoutConstant::compute_fma(
                cs,
                F::ONE,
                (self.get_variable(), one),
                F::MINUS_ONE,
                other.get_variable(),
            );

            Self {
                variable: result_var,
                _marker: std::marker::PhantomData,
            }
        } else {
            unimplemented!()
        }
    }

    #[must_use]
    pub fn mul<CS: ConstraintSystem<F>>(&self, cs: &mut CS, other: &Self) -> Self {
        if cs.gate_is_allowed::<FmaGateInBaseFieldWithoutConstant<F>>() {
            let result_var = FmaGateInBaseFieldWithoutConstant::compute_fma(
                cs,
                F::ONE,
                (self.get_variable(), other.get_variable()),
                F::ZERO,
                other.get_variable(),
            );

            Self {
                variable: result_var,
                _marker: std::marker::PhantomData,
            }
        } else {
            unimplemented!()
        }
    }

    #[must_use]
    pub fn spread_into_bits<CS: ConstraintSystem<F>, const LIMIT: usize>(
        &self,
        cs: &mut CS,
    ) -> [Boolean<F>; LIMIT] {
        // allocate and compute

        debug_assert!(LIMIT <= F::CHAR_BITS);

        let vars = cs.alloc_multiple_variables_without_values::<LIMIT>();
        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 1]| {
                let as_u64 = inputs[0].as_u64_reduced();
                let bits = [as_u64];
                let mut iterator = LSBIterator::new(&bits);
                let mut result = [F::ZERO; LIMIT];
                for (dst, src) in result.iter_mut().zip(&mut iterator) {
                    if src {
                        *dst = F::ONE;
                    }
                }

                result
            };

            let dependencies = [self.get_variable().into()];

            cs.set_values_with_dependencies(&dependencies, &Place::from_variables(vars), value_fn);
        }

        // prove equality by chunks

        if cs.gate_is_allowed::<ReductionGate<F, 4>>() {
            let mut powers = [F::ZERO; LIMIT];
            powers.copy_from_slice(&F::SHIFTS[..LIMIT]);
            linear_combination_collapse(
                cs,
                &mut vars.into_iter().zip(powers),
                Some(self.get_variable()),
            );
        } else if cs.gate_is_allowed::<ReductionByPowersGate<F, 4>>() {
            // this is very much like linear combination for num, but in a tree form
            let mut final_var = Variable::placeholder();

            // tree like aggregation
            let zero = Num::allocated_constant(cs, F::ZERO);

            let mut num_reduction_steps = 0;
            let mut limit = LIMIT;
            while limit > 0 {
                limit /= 4;
                num_reduction_steps += 1;
            }

            let mut vars_array_vec = ArrayVec::<Variable, LIMIT>::new_const();
            vars_array_vec.extend(vars);

            let mut reduction_constant = F::TWO;

            for _ in 0..num_reduction_steps {
                let mut tmp = ArrayVec::<Variable, LIMIT>::new_const();

                let mut chunks = vars_array_vec.array_chunks::<4>();
                for chunk in &mut chunks {
                    let subword =
                        ReductionByPowersGate::<F, 4>::reduce_terms(cs, reduction_constant, *chunk);
                    tmp.push(subword);
                }

                let remainder_len = chunks.remainder().len();
                if remainder_len != 0 {
                    let mut buffer = [zero.get_variable(); 4];
                    buffer[..remainder_len].copy_from_slice(chunks.remainder());
                    let subword =
                        ReductionByPowersGate::<F, 4>::reduce_terms(cs, reduction_constant, buffer);
                    tmp.push(subword);
                }

                debug_assert!(tmp.len() > 0);

                if tmp.len() == 1 {
                    final_var = tmp.pop().unwrap();
                } else {
                    vars_array_vec = tmp;
                }

                for _ in 0..4 {
                    reduction_constant.double();
                }
            }

            debug_assert!(final_var.is_placeholder() == false);

            // enforce equality

            Num::enforce_equal(cs, &Num::from_variable(final_var), self);
        } else {
            unimplemented!()
        }

        vars.map(|el| Boolean::from_variable_checked(cs, el))
    }

    #[track_caller]
    pub fn enforce_equal<CS: ConstraintSystem<F>>(cs: &mut CS, a: &Self, b: &Self) {
        if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS {
            if let (Some(a), Some(b)) = ((a.witness_hook(cs))(), (b.witness_hook(cs))()) {
                assert_eq!(a, b, "enforce equal failed");
            }
        }

        if cs.gate_is_allowed::<FmaGateInBaseFieldWithoutConstant<F>>() {
            let zero_var = cs.allocate_constant(F::ZERO);
            let one_var = cs.allocate_constant(F::ONE);

            let gate = FmaGateInBaseFieldWithoutConstant {
                params: FmaGateInBaseWithoutConstantParams {
                    coeff_for_quadtaric_part: F::ONE,
                    linear_term_coeff: F::MINUS_ONE,
                },
                quadratic_part: (a.get_variable(), one_var),
                linear_part: b.get_variable(),
                rhs_part: zero_var,
            };

            gate.add_to_cs(cs);
        } else {
            unimplemented!()
        }
    }

    // Returns the value unchanges if `bit` is `true`, and 0 otherwise
    #[must_use]
    pub fn mask<CS: ConstraintSystem<F>>(&self, cs: &mut CS, masking_bit: Boolean<F>) -> Self {
        // there isn't much of a reason to use one gate than the other

        if cs.gate_is_allowed::<SelectionGate>() {
            let zero = cs.allocate_constant(F::ZERO);
            let result =
                SelectionGate::select(cs, self.get_variable(), zero, masking_bit.get_variable());

            Self::from_variable(result)
        } else if cs.gate_is_allowed::<FmaGateInBaseFieldWithoutConstant<F>>() {
            // do it by multiplication
            let result = FmaGateInBaseFieldWithoutConstant::compute_fma(
                cs,
                F::ONE,
                (self.get_variable(), masking_bit.get_variable()),
                F::ZERO,
                self.get_variable(),
            );

            Self::from_variable(result)
        } else {
            unimplemented!()
        }
    }

    // Returns the value unchanges if `bit` is `false`, and 0 otherwise
    #[must_use]
    pub fn mask_negated<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        masking_bit: Boolean<F>,
    ) -> Self {
        // there isn't much of a reason to use one gate than the other

        if cs.gate_is_allowed::<SelectionGate>() {
            let zero = cs.allocate_constant(F::ZERO);
            let result =
                SelectionGate::select(cs, zero, self.get_variable(), masking_bit.get_variable());

            Self::from_variable(result)
        } else if cs.gate_is_allowed::<FmaGateInBaseFieldWithoutConstant<F>>() {
            // do it by multiplication self * (1 - bit)
            let result = FmaGateInBaseFieldWithoutConstant::compute_fma(
                cs,
                F::MINUS_ONE,
                (self.get_variable(), masking_bit.get_variable()),
                F::ONE,
                self.get_variable(),
            );

            Self::from_variable(result)
        } else {
            unimplemented!()
        }
    }

    #[must_use]
    fn decompose_into_bytes_inner<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        num_bytes: usize,
    ) -> ArrayVec<UInt8<F>, 8> {
        let mut result = ArrayVec::new_const();

        if num_bytes == 1 {
            range_check_u8(cs, self.get_variable());

            result.push(UInt8 {
                variable: self.get_variable(),
                _marker: std::marker::PhantomData,
            })
        } else if num_bytes == 2 {
            let zero_var = cs.allocate_constant(F::ZERO);

            let bytes = decompose_into_limbs_limited::<_, _, 4>(
                cs,
                F::SHIFTS[8],
                self.get_variable(),
                2,
                zero_var,
            );

            range_check_u8_pair(cs, &[bytes[0], bytes[1]]);

            result.extend(
                bytes[..2]
                    .iter()
                    .copied()
                    .map(|el| unsafe { UInt8::from_variable_unchecked(el) }),
            );
        } else if num_bytes == 3 {
            let zero_var = cs.allocate_constant(F::ZERO);

            let bytes = decompose_into_limbs_limited::<_, _, 4>(
                cs,
                F::SHIFTS[8],
                self.get_variable(),
                3,
                zero_var,
            );

            range_check_u8_pair(cs, &[bytes[0], bytes[1]]);
            range_check_u8(cs, bytes[2]);

            result.extend(
                bytes[..3]
                    .iter()
                    .copied()
                    .map(|el| unsafe { UInt8::from_variable_unchecked(el) }),
            );
        } else if num_bytes == 4 {
            let bytes = decompose_into_limbs::<_, _, 4>(cs, F::SHIFTS[8], self.get_variable());

            range_check_u8_pair(cs, &[bytes[0], bytes[1]]);
            range_check_u8_pair(cs, &[bytes[2], bytes[3]]);

            result.extend(bytes.map(|el| unsafe { UInt8::from_variable_unchecked(el) }));
        } else if num_bytes == 6 {
            let zero_var = cs.allocate_constant(F::ZERO);

            let [low, high, _, _] =
                decompose_into_limbs_limited(cs, F::SHIFTS[24], self.get_variable(), 2, zero_var);

            let [byte0, byte1, byte2, _] =
                decompose_into_limbs_limited(cs, F::SHIFTS[8], low, 3, zero_var);

            let [byte3, byte4, byte5, _] =
                decompose_into_limbs_limited(cs, F::SHIFTS[8], high, 3, zero_var);

            range_check_u8_pair(cs, &[byte0, byte1]);
            range_check_u8_pair(cs, &[byte2, byte3]);
            range_check_u8_pair(cs, &[byte4, byte5]);

            result.extend(
                [byte0, byte1, byte2, byte3, byte4, byte5]
                    .map(|el| unsafe { UInt8::from_variable_unchecked(el) }),
            );
        } else if num_bytes == 8 {
            let zero_var = cs.allocate_constant(F::ZERO);

            let [t0, t1, t2, t3] =
                decompose_into_limbs_limited(cs, F::SHIFTS[16], self.get_variable(), 4, zero_var);

            let [byte0, byte1, _, _] =
                decompose_into_limbs_limited(cs, F::SHIFTS[8], t0, 2, zero_var);
            let [byte2, byte3, _, _] =
                decompose_into_limbs_limited(cs, F::SHIFTS[8], t1, 2, zero_var);
            let [byte4, byte5, _, _] =
                decompose_into_limbs_limited(cs, F::SHIFTS[8], t2, 2, zero_var);
            let [byte6, byte7, _, _] =
                decompose_into_limbs_limited(cs, F::SHIFTS[8], t3, 2, zero_var);

            range_check_u8_pair(cs, &[byte0, byte1]);
            range_check_u8_pair(cs, &[byte2, byte3]);
            range_check_u8_pair(cs, &[byte4, byte5]);
            range_check_u8_pair(cs, &[byte6, byte7]);

            result.extend(
                [byte0, byte1, byte2, byte3, byte4, byte5, byte6, byte7]
                    .map(|el| unsafe { UInt8::from_variable_unchecked(el) }),
            );
        } else {
            unimplemented!("not implemented for {} bytes", num_bytes)
        }

        result
    }

    #[must_use]
    pub fn constraint_bit_length_as_bytes<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        length: usize,
    ) -> ArrayVec<UInt8<F>, 8> {
        assert!(
            length % 8 == 0,
            "can only constrait length multiple to 8 bytes with this function"
        );

        self.decompose_into_bytes_inner(cs, length / 8)
    }

    #[must_use]
    pub fn linear_combination<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        input: &[(Variable, F)],
    ) -> Self {
        // create new variable that will be a result and form new combination to be equal to zero

        let result_var = cs.alloc_variable_without_value();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let (all_dependencies, all_coeffs): (Vec<Variable>, Vec<F>) =
                input.iter().copied().unzip();

            let value_fn = move |inputs: &[F], buffer: &mut DstBuffer<'_, '_, F>| {
                debug_assert_eq!(all_coeffs.len(), inputs.len());

                let mut result = F::ZERO;
                for (a, b) in all_coeffs.into_iter().zip(inputs.iter()) {
                    F::mul_and_accumulate_into(&mut result, &a, b);
                }

                buffer.push(result);
            };

            let all_dependencies: Vec<_> =
                all_dependencies.into_iter().map(|el| el.into()).collect();

            cs.set_values_with_dependencies_vararg(
                &all_dependencies,
                &Place::from_variables([result_var]),
                value_fn,
            );
        }

        let mut it = input.iter().copied();
        linear_combination_collapse(cs, &mut it, Some(result_var));

        Self {
            variable: result_var,
            _marker: std::marker::PhantomData,
        }
    }

    #[track_caller]
    pub fn enforce_zero_for_linear_combination<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        input: &[(Variable, F)],
    ) {
        linear_combination_collapse(cs, &mut input.iter().copied(), None);
    }

    pub fn enforce_zero_for_linear_combination_ext<CS: ConstraintSystem<F>>(
        _cs: &mut CS,
        _input: &[(Variable, F)],
        _extra: Option<(Variable, F)>,
    ) {
        unimplemented!()
        // if cs.gate_is_allowed::<QuadraticCombinationGate<4>>() {
        //     let mut length = input.len();
        //     if extra.is_some() {
        //         length += 1;
        //     }

        //     if length < 4 {
        //         let mut gate = QuadraticCombinationGate {
        //             pairs: [(Variable::placeholder(), Variable::placeholder()); 4],
        //         };

        //         let zero_var = cs.allocate_constant(F::ZERO);
        //         for idx in length..4 {
        //             gate.pairs[idx].0 = zero_var;
        //             gate.pairs[idx].1 = zero_var;
        //         }

        //         for ((var, coeff), dst) in input
        //             .iter()
        //             .copied()
        //             .chain(extra)
        //             .zip(gate.pairs.iter_mut())
        //         {
        //             let constant = cs.allocate_constant(coeff);
        //             dst.0 = constant;
        //             dst.1 = var;
        //         }

        //         gate.add_to_cs(cs);
        //     } else if length == 4 {
        //         let mut gate = QuadraticCombinationGate {
        //             pairs: [(Variable::placeholder(), Variable::placeholder()); 4],
        //         };

        //         for ((var, coeff), dst) in input
        //             .iter()
        //             .copied()
        //             .chain(extra)
        //             .zip(gate.pairs.iter_mut())
        //         {
        //             let constant = cs.allocate_constant(coeff);
        //             dst.0 = constant;
        //             dst.1 = var;
        //         }

        //         gate.add_to_cs(cs);
        //     } else {
        //         // recurse
        //         let mut chunks = input.array_chunks::<3>();
        //         let chunk = (&mut chunks).next().expect("is some");
        //         let intermediate_var = cs.alloc_variable_without_value();

        //         if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
        //             let coeffs = chunk.map(|el| el.1);
        //             let inputs = chunk.map(|el| el.0);

        //             let value_fn = move |inputs: [F; 3]| {
        //                 let mut result = F::ZERO;
        //                 for (a, b) in coeffs.into_iter().zip(inputs.into_iter()) {
        //                     let mut tmp = a;
        //                     tmp.mul_assign(&b);
        //                     result.add_assign(&tmp);
        //                 }

        //                 [result]
        //             };

        //             cs.set_values_with_dependencies(
        //                 &Place::from_variables(inputs),
        //                 &[intermediate_var.into()],
        //                 value_fn,
        //             );
        //         }

        //         let mut gate = QuadraticCombinationGate {
        //             pairs: [(Variable::placeholder(), Variable::placeholder()); 4],
        //         };

        //         for ((var, coeff), dst) in chunk.iter().copied().zip(gate.pairs.iter_mut()) {
        //             let constant = cs.allocate_constant(coeff);
        //             dst.0 = constant;
        //             dst.1 = var;
        //         }

        //         let minus_one = cs.allocate_constant(F::MINUS_ONE);

        //         gate.pairs[3].0 = minus_one;
        //         gate.pairs[3].1 = intermediate_var;

        //         gate.add_to_cs(cs);

        //         let rest = chunks.remainder();

        //         Self::enforce_zero_for_linear_combination_ext(
        //             cs,
        //             rest,
        //             Some((intermediate_var, F::ONE)),
        //         );
        //     }
        // } else {
        //     unimplemented!()
        // }
    }

    #[track_caller]
    pub fn enforce_linear_combination_converge_into<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        input: &[(Variable, F)],
        extra: Option<(Variable, F)>,
        final_var: Variable,
    ) {
        if cs.gate_is_allowed::<DotProductGate<4>>() {
            let mut length = input.len();
            if extra.is_some() {
                length += 1;
            }
            if length <= 4 {
                let mut gate = DotProductGate::<4> {
                    terms: [Variable::placeholder(); 8],
                    result: final_var,
                };

                if length < 4 {
                    let zero_var = cs.allocate_constant(F::ZERO);
                    for idx in length..4 {
                        gate.terms[2 * idx] = zero_var;
                        gate.terms[2 * idx + 1] = zero_var;
                    }
                }

                for ((var, coeff), dst) in input
                    .iter()
                    .copied()
                    .chain(extra)
                    .zip(gate.terms.array_chunks_mut::<2>())
                {
                    let constant = cs.allocate_constant(coeff);
                    dst[0] = constant;
                    dst[1] = var;
                }

                gate.add_to_cs(cs);
            } else {
                // recurse
                if extra.is_none() {
                    let mut chunks = input.array_chunks::<4>();
                    let chunk = chunks.next().expect("is some");
                    let intermediate_var = cs.alloc_variable_without_value();

                    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
                        let coeffs = chunk.map(|el| el.1);
                        let inputs = chunk.map(|el| el.0);

                        let value_fn = move |inputs: [F; 4]| {
                            let mut result = F::ZERO;
                            for (a, b) in coeffs.into_iter().zip(inputs.into_iter()) {
                                let mut tmp = a;
                                tmp.mul_assign(&b);
                                result.add_assign(&tmp);
                            }

                            [result]
                        };

                        cs.set_values_with_dependencies(
                            &Place::from_variables(inputs),
                            &[intermediate_var.into()],
                            value_fn,
                        );
                    }

                    let mut gate = DotProductGate::<4> {
                        terms: [Variable::placeholder(); 8],
                        result: intermediate_var,
                    };

                    for ((var, coeff), dst) in chunk
                        .iter()
                        .copied()
                        .zip(gate.terms.array_chunks_mut::<2>())
                    {
                        let constant = cs.allocate_constant(coeff);
                        dst[0] = constant;
                        dst[1] = var;
                    }

                    gate.add_to_cs(cs);

                    let rest = chunks.remainder();

                    Self::enforce_linear_combination_converge_into(
                        cs,
                        rest,
                        Some((intermediate_var, F::ONE)),
                        final_var,
                    )
                } else {
                    let mut chunks = input.array_chunks::<3>();
                    let chunk = chunks.next().expect("is some");
                    let intermediate_var = cs.alloc_variable_without_value();

                    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
                        let mut coeffs = [F::ZERO; 4];
                        let mut inputs = [Variable::placeholder(); 4];
                        coeffs[..3].copy_from_slice(&chunk.map(|el| el.1));
                        inputs[..3].copy_from_slice(&chunk.map(|el| el.0));

                        let value_fn = move |inputs: [F; 4]| {
                            let mut result = F::ZERO;
                            for (a, b) in coeffs.into_iter().zip(inputs.into_iter()) {
                                let mut tmp = a;
                                tmp.mul_assign(&b);
                                result.add_assign(&tmp);
                            }

                            [result]
                        };

                        cs.set_values_with_dependencies(
                            &Place::from_variables(inputs),
                            &[intermediate_var.into()],
                            value_fn,
                        );
                    }

                    let mut gate = DotProductGate::<4> {
                        terms: [Variable::placeholder(); 8],
                        result: intermediate_var,
                    };

                    for ((var, coeff), dst) in chunk
                        .iter()
                        .copied()
                        .chain(extra)
                        .zip(gate.terms.array_chunks_mut::<2>())
                    {
                        let constant = cs.allocate_constant(coeff);
                        dst[0] = constant;
                        dst[1] = var;
                    }

                    gate.add_to_cs(cs);

                    let rest = chunks.remainder();

                    Self::enforce_linear_combination_converge_into(
                        cs,
                        rest,
                        Some((intermediate_var, F::ONE)),
                        final_var,
                    )
                }
            }
        } else {
            unimplemented!()
        }
    }

    #[must_use]
    pub fn equals<CS: ConstraintSystem<F>>(cs: &mut CS, a: &Self, b: &Self) -> Boolean<F> {
        // we sub and then check for zero
        let diff = a.sub(cs, b);
        diff.is_zero(cs)
    }

    #[must_use]
    pub fn allocate_multiple_from_closure_and_dependencies<
        CS: ConstraintSystem<F>,
        const N: usize,
        FN: FnOnce(&[F]) -> [F; N] + 'static + Send + Sync,
    >(
        cs: &mut CS,
        witness_closure: FN,
        dependencies: &[Place],
    ) -> [Self; N] {
        let outputs = cs.alloc_multiple_variables_without_values::<N>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: &[F], output_buffer: &mut DstBuffer<'_, '_, F>| {
                debug_assert!(F::CAPACITY_BITS >= 32);
                let witness = (witness_closure)(inputs);

                output_buffer.extend(witness);
            };

            cs.set_values_with_dependencies_vararg(
                dependencies,
                &Place::from_variables(outputs),
                value_fn,
            );
        }

        outputs.map(|el| Self::from_variable(el))
    }

    #[track_caller]
    pub fn conditionally_enforce_equal<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        should_enforce: Boolean<F>,
        a: &Self,
        b: &Self,
    ) {
        // we mask a into 0 if we do not need to enforce,
        // and then simultaneously enforce over masked 0

        if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS {
            if let (Some(a), Some(b), Some(should_enforce)) = (
                (a.witness_hook(cs))(),
                (b.witness_hook(cs))(),
                (should_enforce.witness_hook(cs))(),
            ) {
                if should_enforce {
                    assert_eq!(a, b, "conditional enforce to equal failed");
                }
            }
        }

        let a_masked = a.mask(cs, should_enforce);

        let zero = cs.allocate_constant(F::ZERO);

        let gate = FmaGateInBaseFieldWithoutConstant {
            params: FmaGateInBaseWithoutConstantParams {
                coeff_for_quadtaric_part: F::ONE,
                linear_term_coeff: F::MINUS_ONE,
            },
            quadratic_part: (b.get_variable(), should_enforce.get_variable()),
            linear_part: a_masked.get_variable(),
            rhs_part: zero,
        };

        gate.add_to_cs(cs);
    }

    #[must_use]
    pub fn fma<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: &Self,
        b: &Self,
        quadratic_coeff: &F,
        c: &Self,
        linear_coeff: &F,
    ) -> Self {
        if cs.gate_is_allowed::<FmaGateInBaseFieldWithoutConstant<F>>() {
            let output = FmaGateInBaseFieldWithoutConstant::compute_fma(
                cs,
                *quadratic_coeff,
                (a.get_variable(), b.get_variable()),
                *linear_coeff,
                c.get_variable(),
            );

            Self::from_variable(output)
        } else {
            unimplemented!()
        }
    }

    #[must_use]
    pub fn inverse_unchecked<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Self {
        if cs.gate_is_allowed::<FmaGateInBaseFieldWithoutConstant<F>>() {
            let one = cs.allocate_constant(F::ONE);
            let output = FmaGateInBaseFieldWithoutConstant::create_inversion_constraint(
                cs,
                self.variable,
                one,
            );

            Self::from_variable(output)
        } else {
            unimplemented!()
        }
    }

    #[must_use]
    pub fn conditionally_swap<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        should_swap: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> (Self, Self) {
        if cs.gate_is_allowed::<ConditionalSwapGate<1>>() {
            let ([new_a], [new_b]) = ConditionalSwapGate::conditionally_swap(
                cs,
                &[a.get_variable()],
                &[b.get_variable()],
                should_swap.get_variable(),
            );

            (Num::from_variable(new_a), Num::from_variable(new_b))
        } else {
            // two selectes
            let new_a = Self::conditionally_select(cs, should_swap, b, a);
            let new_b = Self::conditionally_select(cs, should_swap, a, b);

            (new_a, new_b)
        }
    }

    #[must_use]
    pub fn conditionally_swap_multiple<CS: ConstraintSystem<F>, const N: usize>(
        cs: &mut CS,
        should_swap: Boolean<F>,
        a: &[Self; N],
        b: &[Self; N],
    ) -> ([Self; N], [Self; N]) {
        if cs.gate_is_allowed::<ConditionalSwapGate<N>>() {
            let (new_a, new_b) = ConditionalSwapGate::<N>::conditionally_swap(
                cs,
                &a.map(|el| el.get_variable()),
                &b.map(|el| el.get_variable()),
                should_swap.get_variable(),
            );

            (
                new_a.map(|el| Num::from_variable(el)),
                new_b.map(|el| Num::from_variable(el)),
            )
        } else {
            // two selectes
            let new_a = Self::parallel_select(cs, should_swap, b, a);
            let new_b = Self::parallel_select(cs, should_swap, a, b);

            (new_a, new_b)
        }
    }
}

/// Returns dot product of the variable, padding by 0 if necessary
#[must_use]
pub fn dot_product<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut candidates: impl Iterator<Item = (Variable, Variable)>,
    length: usize,
) -> Variable {
    assert!(length > 0);

    if length == 1 {
        // FMA is enough
        let (a0, b0) = candidates.next().expect("is some");
        assert!(candidates.next().is_none());

        let result =
            FmaGateInBaseFieldWithoutConstant::compute_fma(cs, F::ONE, (a0, b0), F::ZERO, a0);

        return result;
    }

    if cs.gate_is_allowed::<DotProductGate<4>>() {
        dot_product_using_dot_product_gate(cs, candidates, length)
    } else {
        // We may use naive select, but not needed for now
        unimplemented!()
    }
}

#[must_use]
pub fn dot_product_using_dot_product_gate<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut candidates: impl Iterator<Item = (Variable, Variable)>,
    length: usize,
) -> Variable {
    assert!(length > 0);
    debug_assert!(cs.gate_is_allowed::<DotProductGate<4>>());

    let mut intermediate_var = None;
    let mut length = length;

    // long chain
    if length >= 4 {
        length -= 4;

        let (a0, b0) = candidates.next().expect("is some");
        let (a1, b1) = candidates.next().expect("is some");
        let (a2, b2) = candidates.next().expect("is some");
        let (a3, b3) = candidates.next().expect("is some");

        let result =
            DotProductGate::compute_dot_product(cs, [(a0, b0), (a1, b1), (a2, b2), (a3, b3)]);

        if length == 0 {
            assert!(candidates.next().is_none());
            return result;
        } else {
            intermediate_var = Some(result);
        }

        // chain

        while length > 3 {
            length -= 3;
            let a0 = intermediate_var.take().unwrap();
            let b0 = cs.allocate_constant(F::ONE);
            let (a1, b1) = candidates.next().expect("is some");
            let (a2, b2) = candidates.next().expect("is some");
            let (a3, b3) = candidates.next().expect("is some");

            let result =
                DotProductGate::compute_dot_product(cs, [(a0, b0), (a1, b1), (a2, b2), (a3, b3)]);

            intermediate_var = Some(result)
        }
    }

    assert!(length > 0);
    assert!(length < 4);

    // final step
    let (a0, b0) = if let Some(intermediate_var) = intermediate_var {
        let a0 = intermediate_var;
        let b0 = cs.allocate_constant(F::ONE);

        (a0, b0)
    } else {
        candidates.next().expect("is some")
    };

    let (a1, b1) = candidates.next().unwrap_or({
        let zero = cs.allocate_constant(F::ZERO);

        (zero, zero)
    });
    let (a2, b2) = candidates.next().unwrap_or({
        let zero = cs.allocate_constant(F::ZERO);

        (zero, zero)
    });
    let (a3, b3) = candidates.next().unwrap_or({
        let zero = cs.allocate_constant(F::ZERO);

        (zero, zero)
    });

    assert!(candidates.next().is_none());

    let result = DotProductGate::compute_dot_product(cs, [(a0, b0), (a1, b1), (a2, b2), (a3, b3)]);

    result
}

use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;

impl<F: SmallField> CircuitVarLengthEncodable<F> for Num<F> {
    #[inline(always)]
    fn encoding_length(&self) -> usize {
        1
    }
    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, _cs: &mut CS, dst: &mut Vec<Variable>) {
        dst.push(self.get_variable());
    }
}

use crate::gadgets::traits::allocatable::CSAllocatableExt;

impl<F: SmallField> CSAllocatableExt<F> for Num<F> {
    const INTERNAL_STRUCT_LEN: usize = 1;

    fn witness_from_set_of_values(values: [F; Self::INTERNAL_STRUCT_LEN]) -> Self::Witness {
        values[0]
    }

    // we should be able to allocate without knowing values yet
    fn create_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::allocate_without_value(cs)
    }

    fn flatten_as_variables(&self) -> [Variable; Self::INTERNAL_STRUCT_LEN]
    where
        [(); Self::INTERNAL_STRUCT_LEN]:,
    {
        [self.variable]
    }

    #[inline]
    fn set_internal_variables_values(witness: Self::Witness, dst: &mut DstBuffer<'_, '_, F>) {
        dst.push(witness);
    }
}
