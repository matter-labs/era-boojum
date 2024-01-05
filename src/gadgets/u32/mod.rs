use super::*;
use crate::cs::gates::ConstantAllocatableCS;
use crate::cs::gates::UIntXAddGate;

use crate::cs::gates::u32_add::U32AddGate;
use crate::cs::gates::u32_fma::U8x4FMAGate;
use crate::cs::gates::u32_sub::U32SubGate;

use crate::config::*;

use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::cs::DstBuffer;
use crate::gadgets::blake2s::mixing_function::merge_byte_using_table;
use crate::gadgets::boolean::Boolean;
use crate::gadgets::impls::limbs_decompose::decompose_into_limbs;
use crate::gadgets::impls::limbs_decompose::reduce_terms;
use crate::gadgets::num::Num;
use crate::gadgets::tables::ByteSplitTable;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::traits::allocatable::CSAllocatableExt;
use crate::gadgets::traits::castable::WitnessCastable;
use crate::gadgets::u16::UInt16;
use crate::gadgets::u8::*;
use crate::{cs::Variable, field::SmallField};

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub struct UInt32<F: SmallField> {
    pub(crate) variable: Variable,
    pub(crate) _marker: std::marker::PhantomData<F>,
}

// it's allocatable and witnessable

impl<F: SmallField> CSAllocatable<F> for UInt32<F> {
    type Witness = u32;
    fn placeholder_witness() -> Self::Witness {
        0u32
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

impl<F: SmallField> CSAllocatableExt<F> for UInt32<F> {
    const INTERNAL_STRUCT_LEN: usize = 1;

    fn witness_from_set_of_values(values: [F; Self::INTERNAL_STRUCT_LEN]) -> Self::Witness {
        <u32 as WitnessCastable<F, F>>::cast_from_source(values[0])
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
        debug_assert!(F::CAPACITY_BITS >= 32);
        dst.push(F::from_u64_unchecked(witness as u64));
    }
}

use crate::gadgets::traits::witnessable::CSWitnessable;

use super::traits::castable::Convertor;
use super::traits::witnessable::WitnessHookable;

pub const UINT32_DECOMPOSITION_LOOKUP_TOOLING: &str = "UInt32 decomposition tooling";
pub const UINT32_RECOMPOSITION_LOOKUP_TOOLING: &str = "UInt32 recomposition tooling";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UInt32DecompositionTooling;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UInt32RecompositionTooling;

pub type DecompositionTooling = std::collections::HashMap<Variable, [Variable; 4]>;
pub type RecompositionTooling = std::collections::HashMap<[Variable; 4], Variable>;

impl<F: SmallField> CSWitnessable<F, 1> for UInt32<F> {
    type ConversionFunction = Convertor<F, [F; 1], u32>;

    fn witness_from_set_of_values(values: [F; 1]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; 1] {
        [self.variable]
    }
}

impl<F: SmallField, const N: usize> CSWitnessable<F, N> for [UInt32<F>; N] {
    type ConversionFunction = Convertor<F, [F; N], [u32; N]>;

    fn witness_from_set_of_values(values: [F; N]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; N] {
        self.map(|el| el.variable)
    }
}

impl<F: SmallField> WitnessHookable<F> for UInt32<F> {
    fn witness_hook<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
    ) -> Box<dyn FnOnce() -> Option<Self::Witness>> {
        let raw_witness = self.get_witness(cs);
        Box::new(move || raw_witness.wait())
    }
}

// impl<F: SmallField, const N: usize> WitnessHookable<F> for [UInt32<F>; N] {
//     fn witness_hook<CS: ConstraintSystem<F>>(
//         &self,
//         cs: &CS,
//     ) -> Box<dyn FnOnce() -> Option<Self::Witness>> {
//         let raw_witness = self.get_witness(cs);
//         Box::new(move || raw_witness.wait())
//     }
// }

use crate::gadgets::traits::selectable::Selectable;

impl<F: SmallField> Selectable<F> for UInt32<F> {
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

impl<F: SmallField> UInt32<F> {
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
    pub fn allocated_constant<CS: ConstraintSystem<F>>(cs: &mut CS, constant: u32) -> Self {
        debug_assert!(F::CAPACITY_BITS >= 32);

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
    pub fn allocate_checked<CS: ConstraintSystem<F>>(cs: &mut CS, witness: u32) -> Self {
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
        self,
        cs: &mut CS,
        other: Self,
    ) -> (Self, Boolean<F>) {
        if cs.gate_is_allowed::<UIntXAddGate<32>>() {
            let no_carry_in = cs.allocate_constant(F::ZERO);
            let (result_var, carry_out_var) = UIntXAddGate::<32>::perform_addition(
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
        } else if cs.gate_is_allowed::<U32AddGate>() {
            let no_carry_in = cs.allocate_constant(F::ZERO);
            let (result_var, carry_out_var) =
                U32AddGate::perform_addition(cs, self.variable, other.variable, no_carry_in);

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
        self,
        cs: &mut CS,
        other: Self,
        carry_in: Boolean<F>,
    ) -> (Self, Boolean<F>) {
        if cs.gate_is_allowed::<UIntXAddGate<32>>() {
            let (result_var, carry_out_var) = UIntXAddGate::<32>::perform_addition(
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
        } else if cs.gate_is_allowed::<U32AddGate>() {
            let (result_var, carry_out_var) =
                U32AddGate::perform_addition(cs, self.variable, other.variable, carry_in.variable);

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
        self,
        cs: &mut CS,
        other: Self,
    ) -> (Self, Boolean<F>) {
        if cs.gate_is_allowed::<UIntXAddGate<32>>() {
            let no_borrow_in = cs.allocate_constant(F::ZERO);
            let (result_var, borrow_out_var) = UIntXAddGate::<32>::perform_subtraction(
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
        } else if cs.gate_is_allowed::<U32AddGate>() {
            let no_borrow_in = cs.allocate_constant(F::ZERO);
            let (result_var, borrow_out_var) =
                U32AddGate::perform_subtraction(cs, self.variable, other.variable, no_borrow_in);

            let borrow_out = Boolean {
                variable: borrow_out_var,
                _marker: std::marker::PhantomData,
            };

            let _result = Self {
                variable: result_var,
                _marker: std::marker::PhantomData,
            };

            let result = Self::from_variable_checked(cs, result_var);

            (result, borrow_out)
        } else if cs.gate_is_allowed::<U32SubGate>() {
            let no_borrow_in = cs.allocate_constant(F::ZERO);
            let (result_var, borrow_out_var) =
                U32SubGate::perform_subtraction(cs, self.variable, other.variable, no_borrow_in);

            let borrow_out = Boolean {
                variable: borrow_out_var,
                _marker: std::marker::PhantomData,
            };

            let _result = Self {
                variable: result_var,
                _marker: std::marker::PhantomData,
            };

            let result = Self::from_variable_checked(cs, result_var);

            (result, borrow_out)
        } else {
            unimplemented!()
        }
    }

    pub fn overflowing_sub_with_borrow_in<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
        other: Self,
        borrow_in: Boolean<F>,
    ) -> (Self, Boolean<F>) {
        if cs.gate_is_allowed::<UIntXAddGate<32>>() {
            let (result_var, borrow_out_var) = UIntXAddGate::<32>::perform_subtraction(
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
        } else if cs.gate_is_allowed::<U32AddGate>() {
            let (result_var, borrow_out_var) = U32AddGate::perform_subtraction(
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
        } else if cs.gate_is_allowed::<U32SubGate>() {
            let (result_var, borrow_out_var) = U32SubGate::perform_subtraction(
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
    pub fn decompose_into_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 4] {
        let tooling: &DecompositionTooling =
            cs.get_or_create_dynamic_tool::<UInt32DecompositionTooling, _>();
        if let Some(existing_decomposition) = tooling.get(&self.variable).copied() {
            return existing_decomposition.map(|el| unsafe { UInt8::from_variable_unchecked(el) });
        }
        drop(tooling);

        let bytes = decompose_into_limbs(cs, F::from_u64_unchecked(1u64 << 8), self.variable);

        range_check_u8_pair(cs, &[bytes[0], bytes[1]]);
        range_check_u8_pair(cs, &[bytes[2], bytes[3]]);

        let tooling: &mut DecompositionTooling =
            cs.get_or_create_dynamic_tool_mut::<UInt32DecompositionTooling, _>();
        let existing = tooling.insert(self.variable, bytes);
        debug_assert!(existing.is_none());

        bytes.map(|el| unsafe { UInt8::from_variable_unchecked(el) })
    }

    /// # Safety
    ///
    /// Assumes that the variable is valid.
    #[must_use]
    pub unsafe fn decompose_into_bytes_unchecked<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
    ) -> [UInt8<F>; 4] {
        let tooling: &DecompositionTooling =
            cs.get_or_create_dynamic_tool::<UInt32DecompositionTooling, _>();
        if let Some(existing_decomposition) = tooling.get(&self.variable).copied() {
            return existing_decomposition.map(|el| unsafe { UInt8::from_variable_unchecked(el) });
        }
        drop(tooling);

        let bytes = decompose_into_limbs(cs, F::SHIFTS[8], self.variable);

        let tooling: &mut DecompositionTooling =
            cs.get_or_create_dynamic_tool_mut::<UInt32DecompositionTooling, _>();
        let existing = tooling.insert(self.variable, bytes);
        debug_assert!(existing.is_none());

        bytes.map(|el| unsafe { UInt8::from_variable_unchecked(el) })
    }

    #[must_use]
    pub fn from_le_bytes<CS: ConstraintSystem<F>>(cs: &mut CS, bytes: [UInt8<F>; 4]) -> Self {
        let bytes = bytes.map(|el| el.get_variable());
        let tooling: &RecompositionTooling =
            cs.get_or_create_dynamic_tool::<UInt32RecompositionTooling, _>();
        if let Some(existing_recomposition) = tooling.get(&bytes).copied() {
            return Self {
                variable: existing_recomposition,
                _marker: std::marker::PhantomData,
            };
        }
        drop(tooling);

        let result = reduce_terms(cs, F::from_u64_unchecked(1u64 << 8), bytes);

        let tooling: &mut RecompositionTooling =
            cs.get_or_create_dynamic_tool_mut::<UInt32RecompositionTooling, _>();
        let existing = tooling.insert(bytes, result);
        debug_assert!(existing.is_none());

        Self {
            variable: result,
            _marker: std::marker::PhantomData,
        }
    }

    #[must_use]
    pub fn from_be_bytes<CS: ConstraintSystem<F>>(cs: &mut CS, bytes: [UInt8<F>; 4]) -> Self {
        let mut le_bytes = bytes;
        le_bytes.reverse();
        Self::from_le_bytes(cs, le_bytes)
    }

    #[must_use]
    pub fn fma_with_carry<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: Self,
        b: Self,
        c: Self,
        carry_in: Self,
    ) -> [(Self, [UInt8<F>; 4]); 2] {
        // decompose
        let a = a.decompose_into_bytes(cs);
        let b = b.decompose_into_bytes(cs);
        let c = c.decompose_into_bytes(cs);
        let carry_in = carry_in.decompose_into_bytes(cs);

        let a = a.map(|el| el.variable);
        let b = b.map(|el| el.variable);
        let c = c.map(|el| el.variable);
        let carry_in = carry_in.map(|el| el.variable);

        let (low_limbs, high_limbs, internal_carries) =
            U8x4FMAGate::perform_fma(cs, a, b, c, carry_in);

        let low_limbs = low_limbs.map(|el| unsafe { UInt8::from_variable_unchecked(el) });
        let high_limbs = high_limbs.map(|el| unsafe { UInt8::from_variable_unchecked(el) });

        let low = Self::from_le_bytes(cs, low_limbs);
        let high = Self::from_le_bytes(cs, high_limbs);

        range_check_u8_pair(cs, &[low_limbs[0].variable, low_limbs[1].variable]);
        range_check_u8_pair(cs, &[low_limbs[2].variable, low_limbs[3].variable]);
        range_check_u8_pair(cs, &[high_limbs[0].variable, high_limbs[1].variable]);
        range_check_u8_pair(cs, &[high_limbs[2].variable, high_limbs[3].variable]);
        range_check_u8_pair(cs, &[internal_carries[0], internal_carries[1]]);

        [(low, low_limbs), (high, high_limbs)]
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

        if cs.gate_is_allowed::<UIntXAddGate<32>>() {
            let no_carry = cs.allocate_constant(F::ZERO);
            let result_var = UIntXAddGate::<32>::perform_addition_no_carry(
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

        if cs.gate_is_allowed::<UIntXAddGate<32>>() {
            let no_borrow = cs.allocate_constant(F::ZERO);
            let result_var = UIntXAddGate::<32>::perform_subtraction_no_borrow(
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

    #[must_use]
    pub fn increment_checked<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> (Self, Boolean<F>) {
        let one = UInt32::allocated_constant(cs, 1u32);
        let (new, of) = self.overflowing_add(cs, one);

        (new, of)
    }

    #[must_use]
    pub fn low_u16<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> UInt16<F> {
        let bytes = self.decompose_into_bytes(cs);
        UInt16::from_le_bytes(cs, [bytes[0], bytes[1]])
    }

    pub fn decompose_into_uint16<CS: ConstraintSystem<F>>(&self, _cs: &mut CS) -> [UInt16<F>; 2] {
        todo!();
    }

    #[inline]
    #[must_use]
    pub fn is_zero<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Boolean<F> {
        self.into_num().is_zero(cs)
    }

    // multiply and enforce that result of multiplication fits into itself
    #[inline]
    #[must_use]
    pub fn non_widening_mul<CS: ConstraintSystem<F>>(&self, cs: &mut CS, other: &Self) -> Self {
        let var = Num::from_variable(self.variable)
            .mul(cs, &Num::from_variable(other.variable))
            .variable;

        Self::from_variable_checked(cs, var)
    }

    #[must_use]
    pub fn allocate_from_closure_and_dependencies<
        CS: ConstraintSystem<F>,
        FN: FnOnce(&[F]) -> u32 + 'static + Send + Sync,
    >(
        cs: &mut CS,
        witness_closure: FN,
        dependencies: &[Place],
    ) -> Self {
        let output = cs.alloc_variable_without_value();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: &[F], output_buffer: &mut DstBuffer<'_, '_, F>| {
                debug_assert!(F::CAPACITY_BITS >= 32);
                let witness = (witness_closure)(inputs);

                output_buffer.push(F::from_u64_unchecked(witness as u64));
            };

            cs.set_values_with_dependencies_vararg(
                dependencies,
                &Place::from_variables([output]),
                value_fn,
            );
        }

        Self::from_variable_checked(cs, output)
    }

    #[must_use]
    pub fn div_by_constant<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        constant: u32,
    ) -> (Self, Self) {
        let outputs = cs.alloc_multiple_variables_without_values::<2>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 1]| {
                let input = inputs[0].as_u64() as u32;
                let (q, r) = (input / constant, input % constant);

                [
                    F::from_u64_unchecked(q as u64),
                    F::from_u64_unchecked(r as u64),
                ]
            };

            let dependencies = [self.variable.into()];

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables(outputs),
                value_fn,
            );
        }

        let quotient = Self::from_variable_checked(cs, outputs[0]);
        let remainder = Self::from_variable_checked(cs, outputs[1]);

        // now we need to enforce FMA
        use crate::cs::gates::FmaGateInBaseFieldWithoutConstant;
        if cs.gate_is_allowed::<FmaGateInBaseFieldWithoutConstant<F>>() {
            let one = cs.allocate_constant(F::ONE);

            use crate::cs::gates::fma_gate_without_constant::FmaGateInBaseWithoutConstantParams;

            let gate = FmaGateInBaseFieldWithoutConstant {
                params: FmaGateInBaseWithoutConstantParams {
                    coeff_for_quadtaric_part: F::from_u64_unchecked(constant as u64),
                    linear_term_coeff: F::ONE,
                },
                quadratic_part: (quotient.variable, one),
                linear_part: remainder.variable,
                rhs_part: self.variable,
            };

            gate.add_to_cs(cs);
        } else {
            unimplemented!()
        }

        // and check that remainder is small

        if cs.gate_is_allowed::<UIntXAddGate<32>>() {
            let boolean_true = Boolean::allocated_constant(cs, true);
            let allocated_constant = UInt32::allocated_constant(cs, constant);
            let no_borrow = cs.allocate_constant(F::ZERO);
            let _ = UIntXAddGate::<32>::perform_subtraction_with_expected_borrow_out(
                cs,
                remainder.variable,
                allocated_constant.variable,
                no_borrow,
                no_borrow,
                boolean_true.variable,
            );
        } else {
            unimplemented!()
        }

        (quotient, remainder)
    }

    #[must_use]
    pub fn to_le_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 4] {
        self.decompose_into_bytes(cs)
    }

    #[must_use]
    pub fn to_be_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 4] {
        let mut bytes = self.decompose_into_bytes(cs);
        bytes.reverse();

        bytes
    }

    #[must_use]
    pub fn div2<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Self {
        let byte_split_id = cs
            .get_table_id_for_marker::<ByteSplitTable<1>>()
            .expect("table should exist");
        let mut bytes = self.to_le_bytes(cs);
        let mut bit: Option<Variable> = None;
        bytes.iter_mut().rev().for_each(|b| {
            let res = cs.perform_lookup::<1, 2>(byte_split_id, &[b.get_variable()]);
            let mut shifted = res[1];
            let new_bit = res[0];
            if let Some(top_bit) = bit {
                shifted = merge_byte_using_table::<_, _, 7>(cs, shifted, top_bit);
            }
            *b = UInt8 {
                variable: shifted,
                _marker: std::marker::PhantomData,
            };
            bit = Some(new_bit);
        });
        Self::from_le_bytes(cs, bytes)
    }
}

use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;

impl<F: SmallField> CircuitVarLengthEncodable<F> for UInt32<F> {
    #[inline(always)]
    fn encoding_length(&self) -> usize {
        1
    }
    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, _cs: &mut CS, dst: &mut Vec<Variable>) {
        dst.push(self.variable);
    }
}

use crate::gadgets::traits::allocatable::CSPlaceholder;

impl<F: SmallField> CSPlaceholder<F> for UInt32<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::zero(cs)
    }
}

// #[cfg(test)]
// mod test {
//     use crate::cs::traits::cs::{EmptyGatesConfiguration, GatesConfigulation};
//     use crate::cs::{create_test_cs_with_lookup, tables::binop_table::create_binop_table};

//     use super::*;
//     use crate::worker::Worker;
//     type F = crate::field::goldilocks::GoldilocksField;
//     use crate::cs::gates::*;

//     #[test]
//     fn test_add_sub() {
//         let gates = EmptyGatesConfiguration::new()
//             .allow_gate::<ConstantsAllocatorGate<_>>(())
//             .allow_gate::<BooleanConstraintGate>(())
//             .allow_gate::<U32AddGate>(())
//             .allow_gate::<ReductionByPowersGate<F, 4>>(());

//         let mut cs = create_test_cs_with_lookup(128, 8, gates);

//         let (a, _) = UInt32::allocate_checked(&mut cs, u32::MAX);
//         let (b, _) = UInt32::allocate_checked(&mut cs, u32::MAX);
//         let carry_in = Boolean::allocate(&mut cs, true);

//         let (c, carry_out, _) = a.overflowing_add_with_carry_in(&mut cs, b, carry_in);

//         log!("c = {:x}", c.witness_hook(&cs)().unwrap());
//         log!("carry = {}", carry_out.witness_hook(&cs)().unwrap());

//         let borrow_in = Boolean::allocate(&mut cs, false);
//         let (d, borrow_out, _) = a.overflowing_sub_with_borrow_in(&mut cs, b, borrow_in);

//         log!("d = {:x}", d.witness_hook(&cs)().unwrap());
//         log!("borrow = {}", borrow_out.witness_hook(&cs)().unwrap());

//         let worker = Worker::new();

//         log!("Checking if satisfied");

//         assert!(cs.check_if_satisfied(&worker));
//     }

//     #[test]
//     fn test_add_sub_uintx_gate() {
//         let gates = EmptyGatesConfiguration::new()
//             .allow_gate::<ConstantsAllocatorGate<_>>(())
//             .allow_gate::<BooleanConstraintGate>(())
//             .allow_gate::<UIntXAddGate<32>>(())
//             .allow_gate::<ReductionByPowersGate<F, 4>>(());

//         let mut cs = create_test_cs_with_lookup(128, 8, gates);

//         let (a, _) = UInt32::allocate_checked(&mut cs, u32::MAX);
//         let (b, _) = UInt32::allocate_checked(&mut cs, u32::MAX);
//         let carry_in = Boolean::allocate(&mut cs, true);

//         let (c, carry_out, _) = a.overflowing_add_with_carry_in(&mut cs, b, carry_in);

//         log!("c = {:x}", c.witness_hook(&cs)().unwrap());
//         log!("carry = {}", carry_out.witness_hook(&cs)().unwrap());

//         let borrow_in = Boolean::allocate(&mut cs, false);
//         let (d, borrow_out, _) = a.overflowing_sub_with_borrow_in(&mut cs, b, borrow_in);

//         log!("d = {:x}", d.witness_hook(&cs)().unwrap());
//         log!("borrow = {}", borrow_out.witness_hook(&cs)().unwrap());

//         let worker = Worker::new();

//         log!("Checking if satisfied");

//         assert!(cs.check_if_satisfied(&worker));
//     }

//     #[test]
//     fn test_simple_fma() {
//         let gates = EmptyGatesConfiguration::new()
//             .allow_gate::<ConstantsAllocatorGate<_>>(())
//             .allow_gate::<BooleanConstraintGate>(())
//             .allow_gate::<FmaGateInBaseFieldWithoutConstant<F>>(())
//             .allow_gate::<ReductionByPowersGate<F, 4>>(())
//             .allow_gate::<U8x4FMAGate>(());

//         let mut cs = create_test_cs_with_lookup(128, 8, gates);

//         let (a, _) = UInt32::allocate_checked(&mut cs, u32::MAX);
//         let (b, _) = UInt32::allocate_checked(&mut cs, u32::MAX);
//         let (c, _) = UInt32::allocate_checked(&mut cs, u32::MAX);
//         let (carry_in, _) = UInt32::allocate_checked(&mut cs, u32::MAX);

//         let [(low, _), (high, _)] = UInt32::fma_with_carry(&mut cs, a, b, c, carry_in);

//         log!("low = {:x}", low.witness_hook(&cs)().unwrap());
//         log!("high = {:x}", high.witness_hook(&cs)().unwrap());
//         // dbg!(&low.witness_hook(&cs)());
//         // dbg!(&high.witness_hook(&cs)());

//         let worker = Worker::new();

//         log!("Checking if satisfied");

//         assert!(cs.check_if_satisfied(&worker));
//     }
// }
