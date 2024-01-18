use super::*;

use crate::cs::gates::{
    BoundedBooleanConstraintGate, ConstantAllocatableCS, FmaGateInBaseFieldWithoutConstant,
    FmaGateInBaseWithoutConstantParams,
};

use crate::cs::gates::boolean_allocator::BooleanConstraintGate;

use crate::config::*;
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::cs::DstBuffer;
use crate::gadgets::num::Num;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::traits::allocatable::CSAllocatableExt;
use crate::gadgets::traits::castable::WitnessCastable;
use crate::{cs::Variable, field::SmallField};

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct Boolean<F: SmallField> {
    pub(crate) variable: Variable,
    pub(crate) _marker: std::marker::PhantomData<F>,
}

// it's allocatable and witnessable

impl<F: SmallField> CSAllocatable<F> for Boolean<F> {
    type Witness = bool;
    fn placeholder_witness() -> Self::Witness {
        false
    }

    #[inline(always)]
    #[must_use]
    fn allocate_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let var = cs.alloc_variable_without_value();

        Self::from_variable_checked(cs, var)
    }

    #[must_use]
    fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let var = cs.alloc_single_variable_from_witness(F::from_u64_unchecked(witness as u64));

        Self::from_variable_checked(cs, var)
    }
}

impl<F: SmallField> CSAllocatableExt<F> for Boolean<F> {
    const INTERNAL_STRUCT_LEN: usize = 1;

    fn witness_from_set_of_values(values: [F; Self::INTERNAL_STRUCT_LEN]) -> Self::Witness {
        <bool as WitnessCastable<F, F>>::cast_from_source(values[0])
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

    fn set_internal_variables_values(witness: Self::Witness, dst: &mut DstBuffer<'_, '_, F>) {
        dst.push(F::from_u64_unchecked(witness as u64));
    }
}

use crate::gadgets::traits::witnessable::CSWitnessable;

use super::traits::castable::Convertor;
use super::traits::witnessable::WitnessHookable;

impl<F: SmallField> CSWitnessable<F, 1> for Boolean<F> {
    type ConversionFunction = Convertor<F, [F; 1], bool>;

    fn witness_from_set_of_values(values: [F; 1]) -> Self::Witness {
        <bool as WitnessCastable<F, [F; 1]>>::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; 1] {
        [self.variable]
    }
}

impl<F: SmallField, const N: usize> CSWitnessable<F, N> for [Boolean<F>; N] {
    type ConversionFunction = Convertor<F, [F; N], [bool; N]>;

    fn witness_from_set_of_values(values: [F; N]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; N] {
        self.map(|el| el.variable)
    }
}

impl<F: SmallField> WitnessHookable<F> for Boolean<F> {
    fn witness_hook<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
    ) -> Box<dyn FnOnce() -> Option<Self::Witness>> {
        let raw_witness = self.get_witness(cs);
        Box::new(move || raw_witness.wait())
    }
}

use crate::cs::gates::SelectionGate;
use crate::gadgets::traits::selectable::Selectable;

impl<F: SmallField> Selectable<F> for Boolean<F> {
    #[must_use]
    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self {
        if a.variable == b.variable {
            return *a;
        }

        if cs.gate_is_allowed::<SelectionGate>() {
            let result_var = SelectionGate::select(cs, a.variable, b.variable, flag.variable);

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
        let a = a.map(|el| Num::from_variable(el.variable));
        let b = b.map(|el| Num::from_variable(el.variable));

        let tmp = Num::parallel_select(cs, flag, &a, &b);
        unsafe { tmp.map(|el| Self::from_variable_unchecked(el.variable)) }
    }
}

pub const BOOLEAN_NEGATION_LOOKUP_TOOLING: &str = "Boolean negation tooling";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BooleanNegationTooling;

pub type NegationTooling = std::collections::HashMap<Variable, Variable>;

impl<F: SmallField> Boolean<F> {
    #[inline]
    #[must_use]
    pub const fn get_variable(&self) -> Variable {
        self.variable
    }

    #[inline]
    #[must_use]
    pub const fn into_num(self) -> Num<F> {
        Num {
            variable: self.variable,
            _marker: std::marker::PhantomData,
        }
    }

    #[inline]
    #[must_use]
    pub fn from_variable_checked<CS: ConstraintSystem<F>>(cs: &mut CS, variable: Variable) -> Self {
        if cs.gate_is_allowed::<BooleanConstraintGate>() {
            BooleanConstraintGate::enforce_boolean(cs, variable);
        } else if cs.gate_is_allowed::<BoundedBooleanConstraintGate>() {
            BoundedBooleanConstraintGate::enforce_boolean(cs, variable);
        } else if cs.gate_is_allowed::<FmaGateInBaseFieldWithoutConstant<F>>() {
            // a * (a - 1) == 0
            let zero_var = cs.allocate_constant(F::ZERO);

            let gate = FmaGateInBaseFieldWithoutConstant {
                params: FmaGateInBaseWithoutConstantParams {
                    coeff_for_quadtaric_part: F::ONE,
                    linear_term_coeff: F::MINUS_ONE,
                },
                quadratic_part: (variable, variable),
                linear_part: variable,
                rhs_part: zero_var,
            };
            gate.add_to_cs(cs);
        } else {
            unimplemented!()
        }

        Self {
            variable,
            _marker: std::marker::PhantomData,
        }
    }

    /// # Safety
    ///
    /// Does not check the variable to be valid.
    #[inline(always)]
    #[must_use]
    pub const unsafe fn from_variable_unchecked(variable: Variable) -> Self {
        Self {
            variable,
            _marker: std::marker::PhantomData,
        }
    }

    #[must_use]
    pub fn allocated_constant<CS: ConstraintSystem<F>>(cs: &mut CS, constant: bool) -> Self {
        debug_assert!(F::CAPACITY_BITS >= 32);

        let constant_var = cs.allocate_constant(F::from_u64_unchecked(constant as u64));

        Self {
            variable: constant_var,
            _marker: std::marker::PhantomData,
        }
    }

    #[must_use]
    pub fn negated<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> Self {
        let tooling: &NegationTooling =
            cs.get_or_create_dynamic_tool::<BooleanNegationTooling, _>();
        if let Some(existing) = tooling.get(&self.variable).copied() {
            return unsafe { Self::from_variable_unchecked(existing) };
        }
        drop(tooling);

        // we just need 1 - self
        let one_variable = cs.allocate_constant(F::ONE);

        let result_var = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            F::ONE,
            (one_variable, one_variable),
            F::MINUS_ONE,
            self.variable,
        );

        let tooling: &mut NegationTooling =
            cs.get_or_create_dynamic_tool_mut::<BooleanNegationTooling, _>();
        let existing = tooling.insert(self.variable, result_var);
        debug_assert!(existing.is_none());

        Self {
            variable: result_var,
            _marker: std::marker::PhantomData,
        }
    }

    #[must_use]
    pub fn and<CS: ConstraintSystem<F>>(self, cs: &mut CS, other: Self) -> Self {
        let result_var = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            F::ONE,
            (self.variable, other.variable),
            F::ZERO,
            other.variable,
        );

        Self {
            variable: result_var,
            _marker: std::marker::PhantomData,
        }
    }

    #[must_use]
    pub fn or<CS: ConstraintSystem<F>>(self, cs: &mut CS, other: Self) -> Self {
        // (1 - a) * (1 - b) = (1 - c)
        // it doesn't fit into FMA gate, so we use quadratic combination

        // ab-a-b+c=0

        use crate::cs::gates::dot_product_gate::DotProductGate;
        use crate::cs::gates::quadratic_combination::QuadraticCombinationGate;

        if cs.gate_is_allowed::<DotProductGate<4>>() {
            let minus_one_var = cs.allocate_constant(F::MINUS_ONE);
            let one_var = cs.allocate_constant(F::ONE);
            let zero_var = cs.allocate_constant(F::ZERO);

            let result = cs.alloc_variable_without_value();

            if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
                let value_fn = move |inputs: [F; 2]| {
                    let [a, b] = inputs;

                    let a = <bool as WitnessCastable<F, F>>::cast_from_source(a);
                    let b = <bool as WitnessCastable<F, F>>::cast_from_source(b);

                    if a || b {
                        [F::ONE]
                    } else {
                        [F::ZERO]
                    }
                };

                let dependencies = Place::from_variables([self.variable, other.variable]);

                cs.set_values_with_dependencies(&dependencies, &[result.into()], value_fn);
            }

            if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                let gate = DotProductGate::<4> {
                    terms: [
                        self.variable,
                        other.variable,
                        minus_one_var,
                        self.variable,
                        minus_one_var,
                        other.variable,
                        one_var,
                        result,
                    ],

                    result: zero_var,
                };

                gate.add_to_cs(cs);
            }

            Self {
                variable: result,
                _marker: std::marker::PhantomData,
            }
        } else if cs.gate_is_allowed::<QuadraticCombinationGate<4>>() {
            let minus_one_var = cs.allocate_constant(F::MINUS_ONE);
            let one_var = cs.allocate_constant(F::ONE);

            let result = cs.alloc_variable_without_value();

            if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
                let value_fn = move |inputs: [F; 2]| {
                    let [a, b] = inputs;

                    let a = <bool as WitnessCastable<F, F>>::cast_from_source(a);
                    let b = <bool as WitnessCastable<F, F>>::cast_from_source(b);

                    if a || b {
                        [F::ONE]
                    } else {
                        [F::ZERO]
                    }
                };

                let dependencies = Place::from_variables([self.variable, other.variable]);

                cs.set_values_with_dependencies(&dependencies, &[result.into()], value_fn);
            }

            if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                let gate = QuadraticCombinationGate::<4> {
                    pairs: [
                        (self.variable, other.variable),
                        (minus_one_var, self.variable),
                        (minus_one_var, other.variable),
                        (one_var, result),
                    ],
                };

                gate.add_to_cs(cs);
            }

            Self {
                variable: result,
                _marker: std::marker::PhantomData,
            }
        } else if cs.gate_is_allowed::<FmaGateInBaseFieldWithoutConstant<F>>() {
            let result = cs.alloc_variable_without_value();

            if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
                let value_fn = move |inputs: [F; 2]| {
                    let [a, b] = inputs;

                    let a = <bool as WitnessCastable<F, F>>::cast_from_source(a);
                    let b = <bool as WitnessCastable<F, F>>::cast_from_source(b);

                    if a || b {
                        [F::ONE]
                    } else {
                        [F::ZERO]
                    }
                };

                let dependencies = Place::from_variables([self.variable, other.variable]);

                cs.set_values_with_dependencies(&dependencies, &[result.into()], value_fn);
            }

            let one_var = cs.allocate_constant(F::ONE);
            let t0 = FmaGateInBaseFieldWithoutConstant::compute_fma(
                cs,
                F::ONE,
                (one_var, one_var),
                F::MINUS_ONE,
                self.variable,
            );
            let t1 = FmaGateInBaseFieldWithoutConstant::compute_fma(
                cs,
                F::ONE,
                (one_var, one_var),
                F::MINUS_ONE,
                other.variable,
            );

            let one_var = cs.allocate_constant(F::ONE);

            if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                // t0 * t1 + result == 1
                let gate = FmaGateInBaseFieldWithoutConstant {
                    params: FmaGateInBaseWithoutConstantParams {
                        coeff_for_quadtaric_part: F::ONE,
                        linear_term_coeff: F::ONE,
                    },
                    quadratic_part: (t0, t1),
                    linear_part: result,
                    rhs_part: one_var,
                };

                gate.add_to_cs(cs);
            }

            Self {
                variable: result,
                _marker: std::marker::PhantomData,
            }
        } else {
            unimplemented!()
        }
    }

    #[must_use]
    pub fn xor<CS: ConstraintSystem<F>>(self, cs: &mut CS, other: Self) -> Self {
        // Constrain (a + a) * (b) = (a + b - c)
        // Given that a and b are boolean constrained, if they
        // are equal, the only solution for c is 0, and if they
        // are different, the only solution for c is 1.
        //
        // ¬(a ∧ b) ∧ ¬(¬a ∧ ¬b) = c
        // (1 - (a * b)) * (1 - ((1 - a) * (1 - b))) = c
        // (1 - ab) * (1 - (1 - a - b + ab)) = c
        // (1 - ab) * (a + b - ab) = c
        // a + b - ab - (a^2)b - (b^2)a + (a^2)(b^2) = c
        // a + b - ab - ab - ab + ab = c
        // a + b - 2ab = c
        // -2a * b = c - a - b
        // 2a * b = a + b - c
        // (a + a) * b = a + b - c

        // 2a*b - a - b + c = 0
        let one_variable = cs.allocate_constant(F::ONE);

        let a_plus_b = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            F::ONE,
            (self.variable, one_variable),
            F::ONE,
            other.variable,
        );

        let mut minus_two = F::TWO;
        minus_two.negate();

        let c = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            minus_two,
            (self.variable, other.variable),
            F::ONE,
            a_plus_b,
        );

        Boolean::from_variable_checked(cs, c)
    }

    // `self` should be "true" if "should_enforce" is true, otherwise can be any
    #[track_caller]
    pub fn conditionally_enforce_true<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        should_enforce: Self,
    ) {
        if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS {
            if let (Some(this), Some(should_enforce)) = (
                (self.witness_hook(cs))(),
                (should_enforce.witness_hook(cs))(),
            ) {
                if should_enforce {
                    assert!(this, "conditional enforce to `true` failed");
                }
            }
        }

        // this is equal to having !self && should_enforce == false;
        // so (1 - self) * should_enforce == 0

        if cs.gate_is_allowed::<FmaGateInBaseFieldWithoutConstant<F>>() {
            let zero_var = cs.allocate_constant(F::ZERO);

            let gate = FmaGateInBaseFieldWithoutConstant {
                params: FmaGateInBaseWithoutConstantParams {
                    coeff_for_quadtaric_part: F::MINUS_ONE,
                    linear_term_coeff: F::ONE,
                },
                quadratic_part: (self.variable, should_enforce.variable),
                linear_part: should_enforce.variable,
                rhs_part: zero_var,
            };

            gate.add_to_cs(cs);
        } else {
            unimplemented!()
        }
    }

    // `self` should be "false" if "should_enforce" is true, otherwise can be any
    #[track_caller]
    pub fn conditionally_enforce_false<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        should_enforce: Self,
    ) {
        // this is equal to having self && should_enforce == false;
        // so self * should_enforce == 0

        if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS {
            if let (Some(this), Some(should_enforce)) = (
                (self.witness_hook(cs))(),
                (should_enforce.witness_hook(cs))(),
            ) {
                if should_enforce {
                    assert!(this == false, "conditional enforce to `false` failed");
                }
            }
        }

        if cs.gate_is_allowed::<FmaGateInBaseFieldWithoutConstant<F>>() {
            let zero_var = cs.allocate_constant(F::ZERO);

            let gate = FmaGateInBaseFieldWithoutConstant {
                params: FmaGateInBaseWithoutConstantParams {
                    coeff_for_quadtaric_part: F::ONE,
                    linear_term_coeff: F::ZERO,
                },
                quadratic_part: (self.variable, should_enforce.variable),
                linear_part: should_enforce.variable,
                rhs_part: zero_var,
            };

            gate.add_to_cs(cs);
        } else {
            unimplemented!()
        }
    }

    #[must_use]
    pub fn multi_and<CS: ConstraintSystem<F>>(cs: &mut CS, candidates: &[Self]) -> Self {
        debug_assert!(candidates.len() > 0);

        if candidates.len() == 1 {
            return candidates[0];
        }
        // we have two ways here:
        // - use normal AND (1 FMA gate)
        // - make a linear combination of all elements - length, and check if it's zero

        if candidates.len() <= 4 {
            let mut it = candidates.iter();
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            let mut tmp = a.and(cs, *b);

            for c in it {
                tmp = tmp.and(cs, *c);
            }

            tmp
        } else {
            use crate::gadgets::u32::UInt32;

            let length = UInt32::allocated_constant(cs, candidates.len() as u32);

            let mut lc = Vec::with_capacity(candidates.len() + 1);
            lc.extend(candidates.iter().map(|el| (el.variable, F::ONE)));
            lc.push((length.variable, F::MINUS_ONE));

            let lc = Num::linear_combination(cs, &lc);

            lc.is_zero(cs)
        }
    }

    #[must_use]
    pub fn multi_or<CS: ConstraintSystem<F>>(cs: &mut CS, candidates: &[Self]) -> Self {
        debug_assert!(candidates.len() > 0);

        if candidates.len() == 1 {
            return candidates[0];
        }

        debug_assert!(candidates.len() >= 2);
        // we have two ways here:
        // - use normal or (dot product, or quadratic combination gate)
        // - make a linear combination of all elements, and check if it's zero

        if candidates.len() <= 4 {
            let mut it = candidates.iter();
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            let mut tmp = a.or(cs, *b);

            for c in it {
                tmp = tmp.or(cs, *c);
            }

            tmp
        } else {
            let input: Vec<_> = candidates.iter().map(|el| (el.variable, F::ONE)).collect();
            let lc = Num::linear_combination(cs, &input);
            let lc_is_zero = lc.is_zero(cs);
            // we need to negate it

            lc_is_zero.negated(cs)
        }
    }

    // Returns the value unchanges if `bit` is `true`, and 0 otherwise
    #[must_use]
    pub fn mask<CS: ConstraintSystem<F>>(&self, cs: &mut CS, masking_bit: Boolean<F>) -> Self {
        // do it through Num
        let var = Num::from_variable(self.variable)
            .mask(cs, masking_bit)
            .variable;
        unsafe { Self::from_variable_unchecked(var) }
    }

    // Returns the value unchanges if `bit` is `false`, and 0 otherwise
    #[must_use]
    pub fn mask_negated<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        masking_bit: Boolean<F>,
    ) -> Self {
        // do it through Num
        let var = Num::from_variable(self.variable)
            .mask_negated(cs, masking_bit)
            .variable;
        unsafe { Self::from_variable_unchecked(var) }
    }

    #[track_caller]
    pub fn enforce_equal<CS: ConstraintSystem<F>>(cs: &mut CS, a: &Self, b: &Self) {
        if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS {
            if let (Some(a), Some(b)) = ((a.witness_hook(cs))(), (b.witness_hook(cs))()) {
                assert_eq!(a, b, "Boolean enforce equal failed");
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
                quadratic_part: (a.variable, one_var),
                linear_part: b.variable,
                rhs_part: zero_var,
            };

            gate.add_to_cs(cs);
        } else {
            unimplemented!()
        }
    }

    #[inline]
    #[must_use]
    pub fn equals<CS: ConstraintSystem<F>>(cs: &mut CS, a: &Self, b: &Self) -> Boolean<F> {
        Num::equals(
            cs,
            &Num::from_variable(a.variable),
            &Num::from_variable(b.variable),
        )
    }
}

use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;

impl<F: SmallField> CircuitVarLengthEncodable<F> for Boolean<F> {
    #[inline(always)]
    fn encoding_length(&self) -> usize {
        1
    }
    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, _cs: &mut CS, dst: &mut Vec<Variable>) {
        dst.push(self.variable);
    }
}
