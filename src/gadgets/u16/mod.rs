use super::*;
use crate::config::*;
use crate::cs::gates::ConstantAllocatableCS;
use crate::cs::gates::UIntXAddGate;
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::cs::DstBuffer;
use crate::gadgets::boolean::Boolean;
use crate::gadgets::impls::limbs_decompose::decompose_into_limbs_limited;
use crate::gadgets::impls::limbs_decompose::reduce_terms;
use crate::gadgets::num::Num;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::traits::allocatable::CSAllocatableExt;
use crate::gadgets::traits::castable::WitnessCastable;
use crate::gadgets::u8::*;
use crate::{cs::Variable, field::SmallField};

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash)]
pub struct UInt16<F: SmallField> {
    pub(crate) variable: Variable,
    pub(crate) _marker: std::marker::PhantomData<F>,
}

// it's allocatable and witnessable

impl<F: SmallField> CSAllocatable<F> for UInt16<F> {
    type Witness = u16;
    fn placeholder_witness() -> Self::Witness {
        0u16
    }

    #[inline(always)]
    fn allocate_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let var = cs.alloc_variable_without_value();

        Self::from_variable_checked(cs, var)
    }

    #[inline(always)]
    fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let var = Self::allocate_checked(cs, witness);

        var
    }

    #[inline(always)]
    fn allocate_constant<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        Self::allocated_constant(cs, witness)
    }
}

impl<F: SmallField> CSAllocatableExt<F> for UInt16<F> {
    const INTERNAL_STRUCT_LEN: usize = 1;

    fn witness_from_set_of_values(values: [F; Self::INTERNAL_STRUCT_LEN]) -> Self::Witness {
        <u16 as WitnessCastable<F, F>>::cast_from_source(values[0])
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
        debug_assert!(F::CAPACITY_BITS >= 16);
        dst.push(F::from_u64_unchecked(witness as u64));
    }
}

use crate::gadgets::traits::witnessable::CSWitnessable;

use super::traits::castable::Convertor;
use super::traits::witnessable::WitnessHookable;

pub const UINT16_DECOMPOSITION_LOOKUP_TOOLING: &str = "UInt16 decomposition tooling";
pub const UINT16_RECOMPOSITION_LOOKUP_TOOLING: &str = "UInt16 recomposition tooling";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UInt16DecompositionTooling;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UInt16RecompositionTooling;

pub type DecompositionTooling = std::collections::HashMap<Variable, [Variable; 2]>;
pub type RecompositionTooling = std::collections::HashMap<[Variable; 2], Variable>;

impl<F: SmallField> CSWitnessable<F, 1> for UInt16<F> {
    type ConversionFunction = Convertor<F, [F; 1], u16>;

    fn witness_from_set_of_values(values: [F; 1]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; 1] {
        [self.variable]
    }
}

impl<F: SmallField, const N: usize> CSWitnessable<F, N> for [UInt16<F>; N] {
    type ConversionFunction = Convertor<F, [F; N], [u16; N]>;

    fn witness_from_set_of_values(values: [F; N]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; N] {
        self.map(|el| el.variable)
    }
}

impl<F: SmallField> WitnessHookable<F> for UInt16<F> {
    fn witness_hook<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
    ) -> Box<dyn FnOnce() -> Option<Self::Witness>> {
        let raw_witness = self.get_witness(cs);
        Box::new(move || raw_witness.wait())
    }
}

// impl<F: SmallField, const N: usize> WitnessHookable<F> for [UInt16<F>; N] {
//     fn witness_hook<CS: ConstraintSystem<F>>(
//         &self,
//         cs: &CS,
//     ) -> Box<dyn FnOnce() -> Option<Self::Witness>> {
//         let raw_witness = self.get_witness(cs);
//         Box::new(move || raw_witness.wait())
//     }
// }

use crate::gadgets::traits::selectable::Selectable;

impl<F: SmallField> Selectable<F> for UInt16<F> {
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

        let tmp = Num::conditionally_select(
            cs,
            flag,
            &Num::from_variable(a.variable),
            &Num::from_variable(b.variable),
        );
        unsafe { Self::from_variable_unchecked(tmp.variable) }
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

impl<F: SmallField> UInt16<F> {
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

    #[must_use]
    pub fn allocated_constant<CS: ConstraintSystem<F>>(cs: &mut CS, constant: u16) -> Self {
        debug_assert!(F::CAPACITY_BITS >= 16);

        let constant_var = cs.allocate_constant(F::from_u64_unchecked(constant as u64));

        Self {
            variable: constant_var,
            _marker: std::marker::PhantomData,
        }
    }

    #[must_use]
    pub fn zero<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::allocated_constant(cs, 0)
    }

    #[must_use]
    pub fn allocate_checked<CS: ConstraintSystem<F>>(cs: &mut CS, witness: u16) -> Self {
        let result_var =
            cs.alloc_single_variable_from_witness(F::from_u64_with_reduction(witness as u64));

        let result = Self::from_variable_checked(cs, result_var);

        result
    }

    #[inline]
    #[must_use]
    pub fn from_variable_checked<CS: ConstraintSystem<F>>(cs: &mut CS, variable: Variable) -> Self {
        let result = Self {
            variable,
            _marker: std::marker::PhantomData,
        };

        let _chunks = result.decompose_into_bytes(cs);

        result
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
    pub fn overflowing_add<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> (Self, Boolean<F>) {
        if cs.gate_is_allowed::<UIntXAddGate<16>>() {
            let no_carry_in = cs.allocate_constant(F::ZERO);
            let (result_var, carry_out_var) = UIntXAddGate::<16>::perform_addition(
                cs,
                self.variable,
                other.variable,
                no_carry_in,
            );

            let carry_out = Boolean {
                variable: carry_out_var,
                _marker: std::marker::PhantomData,
            };

            let result = Self::from_variable_checked(cs, result_var);

            (result, carry_out)
        } else {
            unimplemented!()
        }
    }

    #[must_use]
    pub fn overflowing_add_with_carry_in<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
        carry_in: Boolean<F>,
    ) -> (Self, Boolean<F>) {
        if cs.gate_is_allowed::<UIntXAddGate<16>>() {
            let (result_var, carry_out_var) = UIntXAddGate::<16>::perform_addition(
                cs,
                self.variable,
                other.variable,
                carry_in.variable,
            );

            let carry_out = Boolean {
                variable: carry_out_var,
                _marker: std::marker::PhantomData,
            };

            let result = Self::from_variable_checked(cs, result_var);

            (result, carry_out)
        } else {
            unimplemented!()
        }
    }

    #[must_use]
    pub fn overflowing_sub<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> (Self, Boolean<F>) {
        if cs.gate_is_allowed::<UIntXAddGate<16>>() {
            let no_borrow_in = cs.allocate_constant(F::ZERO);
            let (result_var, borrow_out_var) = UIntXAddGate::<16>::perform_subtraction(
                cs,
                self.variable,
                other.variable,
                no_borrow_in,
            );

            let borrow_out = Boolean {
                variable: borrow_out_var,
                _marker: std::marker::PhantomData,
            };

            let result = Self::from_variable_checked(cs, result_var);

            (result, borrow_out)
        } else {
            unimplemented!()
        }
    }

    #[must_use]
    pub fn overflowing_sub_with_borrow_in<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
        borrow_in: Boolean<F>,
    ) -> (Self, Boolean<F>) {
        if cs.gate_is_allowed::<UIntXAddGate<16>>() {
            let (result_var, borrow_out_var) = UIntXAddGate::<16>::perform_subtraction(
                cs,
                self.variable,
                other.variable,
                borrow_in.variable,
            );

            let borrow_out = Boolean {
                variable: borrow_out_var,
                _marker: std::marker::PhantomData,
            };

            let result = Self::from_variable_checked(cs, result_var);

            (result, borrow_out)
        } else {
            unimplemented!()
        }
    }

    #[must_use]
    fn decompose_into_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 2] {
        let tooling: &DecompositionTooling =
            cs.get_or_create_dynamic_tool::<UInt16DecompositionTooling, _>();
        if let Some(existing_decomposition) = tooling.get(&self.variable).copied() {
            return existing_decomposition.map(|el| unsafe { UInt8::from_variable_unchecked(el) });
        }
        drop(tooling);

        let zero_var = cs.allocate_constant(F::ZERO);

        let bytes =
            decompose_into_limbs_limited::<_, _, 4>(cs, F::SHIFTS[8], self.variable, 2, zero_var);

        let bytes = [bytes[0], bytes[1]];

        range_check_u8_pair(cs, &bytes);

        let tooling: &mut DecompositionTooling =
            cs.get_or_create_dynamic_tool_mut::<UInt16DecompositionTooling, _>();
        let existing = tooling.insert(self.variable, bytes);
        debug_assert!(existing.is_none());

        bytes.map(|el| unsafe { UInt8::from_variable_unchecked(el) })
    }

    #[must_use]
    pub fn from_le_bytes<CS: ConstraintSystem<F>>(cs: &mut CS, bytes: [UInt8<F>; 2]) -> Self {
        let bytes = bytes.map(|el| el.variable);
        let tooling: &RecompositionTooling =
            cs.get_or_create_dynamic_tool::<UInt16RecompositionTooling, _>();
        if let Some(existing_recomposition) = tooling.get(&bytes).copied() {
            return Self {
                variable: existing_recomposition,
                _marker: std::marker::PhantomData,
            };
        }
        drop(tooling);

        let zero_var = cs.allocate_constant(F::ZERO);

        let bytes_ext = [bytes[0], bytes[1], zero_var, zero_var];

        let result = reduce_terms(cs, F::SHIFTS[8], bytes_ext);

        let tooling: &mut RecompositionTooling =
            cs.get_or_create_dynamic_tool_mut::<UInt16RecompositionTooling, _>();
        let existing = tooling.insert(bytes, result);
        debug_assert!(existing.is_none());

        Self {
            variable: result,
            _marker: std::marker::PhantomData,
        }
    }

    #[track_caller]
    #[must_use]
    pub fn add_no_overflow<CS: ConstraintSystem<F>>(self, cs: &mut CS, other: Self) -> Self {
        if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS {
            if let (Some(a), Some(b)) = (self.witness_hook(&*cs)(), other.witness_hook(&*cs)()) {
                let (_, of) = a.overflowing_add(b);
                assert!(
                    of == false,
                    "trying to add {} and {} that leads to overflow",
                    a,
                    b
                );
            }
        }

        if cs.gate_is_allowed::<UIntXAddGate<16>>() {
            let no_carry = cs.allocate_constant(F::ZERO);
            let result_var = UIntXAddGate::<16>::perform_addition_no_carry(
                cs,
                self.variable,
                other.variable,
                no_carry,
                no_carry,
            );

            let result = Self::from_variable_checked(cs, result_var);

            result
        } else {
            unimplemented!()
        }
    }

    #[track_caller]
    #[must_use]
    pub fn sub_no_overflow<CS: ConstraintSystem<F>>(self, cs: &mut CS, other: Self) -> Self {
        if <CS::Config as CSConfig>::DebugConfig::PERFORM_RUNTIME_ASSERTS {
            if let (Some(a), Some(b)) = (self.witness_hook(&*cs)(), other.witness_hook(&*cs)()) {
                let (_, uf) = a.overflowing_sub(b);
                assert!(
                    uf == false,
                    "trying to sub {} and {} that leads to underflow",
                    a,
                    b
                );
            }
        }

        if cs.gate_is_allowed::<UIntXAddGate<16>>() {
            let no_borrow = cs.allocate_constant(F::ZERO);
            let result_var = UIntXAddGate::<16>::perform_subtraction_no_borrow(
                cs,
                self.variable,
                other.variable,
                no_borrow,
                no_borrow,
            );

            let result = Self::from_variable_checked(cs, result_var);

            result
        } else {
            unimplemented!()
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

    #[inline]
    #[must_use]
    pub fn equals<CS: ConstraintSystem<F>>(cs: &mut CS, a: &Self, b: &Self) -> Boolean<F> {
        Num::equals(
            cs,
            &Num::from_variable(a.variable),
            &Num::from_variable(b.variable),
        )
    }

    /// # Safety
    ///
    /// Does not check if the resulting variable is valid.
    #[must_use]
    pub unsafe fn increment_unchecked<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Self {
        let one = cs.allocate_constant(F::ONE);
        let var = Num::from_variable(self.variable)
            .add(cs, &Num::from_variable(one))
            .variable;

        Self::from_variable_unchecked(var)
    }

    /// # Safety
    ///
    /// Does not check if the resulting variable is valid.
    #[must_use]
    pub unsafe fn decrement_unchecked<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Self {
        let one = cs.allocate_constant(F::ONE);
        let var = Num::from_variable(self.variable)
            .sub(cs, &Num::from_variable(one))
            .variable;

        Self::from_variable_unchecked(var)
    }

    #[inline]
    #[must_use]
    pub fn is_zero<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Boolean<F> {
        self.into_num().is_zero(cs)
    }

    #[must_use]
    pub fn to_le_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 2] {
        self.decompose_into_bytes(cs)
    }

    #[must_use]
    pub fn to_be_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 2] {
        let mut bytes = self.to_le_bytes(cs);
        bytes.reverse();

        bytes
    }
}

use crate::gadgets::traits::encodable::{CircuitVarLengthEncodable, WitnessVarLengthEncodable};

impl<F: SmallField> CircuitVarLengthEncodable<F> for UInt16<F> {
    #[inline(always)]
    fn encoding_length(&self) -> usize {
        1
    }
    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, _cs: &mut CS, dst: &mut Vec<Variable>) {
        dst.push(self.variable);
    }
}

impl<F: SmallField> WitnessVarLengthEncodable<F> for UInt16<F> {
    #[inline(always)]
    fn witness_encoding_length(_witness: &Self::Witness) -> usize {
        1
    }
    fn encode_witness_to_buffer(witness: &Self::Witness, dst: &mut Vec<F>) {
        dst.push(F::from_u64_with_reduction(*witness as u64));
    }
}
