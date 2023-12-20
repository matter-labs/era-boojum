use super::tables::ch4::Ch4Table;
use super::tables::trixor4::TriXor4Table;
use super::tables::xor8::Xor8Table;
use super::tables::RangeCheckTable;
use super::*;

use crate::config::*;
use crate::cs::gates::ConstantAllocatableCS;
use crate::cs::gates::UIntXAddGate;
use crate::cs::gates::*;
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::cs::DstBuffer;
use crate::gadgets::boolean::Boolean;
use crate::gadgets::num::Num;
use crate::gadgets::tables::binop_table::BinopTable;
use crate::gadgets::tables::maj4::Maj4Table;
use crate::gadgets::tables::ByteSplitTable;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::traits::allocatable::CSAllocatableExt;
use crate::gadgets::traits::castable::WitnessCastable;
use crate::{cs::Variable, field::SmallField};

#[inline(always)]
pub fn get_8_by_8_range_check_table<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &CS,
) -> Option<u32> {
    cs.get_table_id_for_marker::<BinopTable>()
        .or_else(|| cs.get_table_id_for_marker::<Xor8Table>())
}

#[inline(always)]
pub fn get_8_bit_range_check_table<F: SmallField, CS: ConstraintSystem<F>>(cs: &CS) -> Option<u32> {
    cs.get_table_id_for_marker::<RangeCheckTable<8>>()
}

#[inline(always)]
pub fn get_4x4x4_range_check_table<F: SmallField, CS: ConstraintSystem<F>>(cs: &CS) -> Option<u32> {
    cs.get_table_id_for_marker::<TriXor4Table>()
        .or_else(|| cs.get_table_id_for_marker::<Ch4Table>())
        .or_else(|| cs.get_table_id_for_marker::<Maj4Table>())
}

#[inline(always)]
pub fn range_check_u8_pair<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    pair: &[Variable; 2],
) {
    if let Some(table_id) = get_8_by_8_range_check_table(cs) {
        let _ = cs.perform_lookup::<2, 1>(table_id, pair);
    } else if let Some(table_id) = get_8_bit_range_check_table(cs) {
        let _ = cs.perform_lookup::<1, 0>(table_id, &[pair[0]]);
        let _ = cs.perform_lookup::<1, 0>(table_id, &[pair[1]]);
    } else if let Some(table_id) = get_4x4x4_range_check_table(cs) {
        let [low, high] = uint8_into_4bit_chunks_unchecked(cs, pair[0]);
        let _ = cs.perform_lookup::<3, 1>(table_id, &[low, high, low]);
        let [low, high] = uint8_into_4bit_chunks_unchecked(cs, pair[1]);
        let _ = cs.perform_lookup::<3, 1>(table_id, &[low, high, low]);
    } else {
        // baseline one by one
        range_check_u8(cs, pair[0]);
        range_check_u8(cs, pair[1]);
    }
}

#[inline(always)]
pub fn range_check_u8<F: SmallField, CS: ConstraintSystem<F>>(cs: &mut CS, input: Variable) {
    if let Some(table_id) = get_8_bit_range_check_table(cs) {
        let _ = cs.perform_lookup::<1, 0>(table_id, &[input]);
    } else if let Some(table_id) = get_8_by_8_range_check_table(cs) {
        let zero = cs.allocate_constant(F::ZERO);
        let _ = cs.perform_lookup::<2, 1>(table_id, &[input, zero]);
    } else if let Some(table_id) = get_4x4x4_range_check_table(cs) {
        let [low, high] = uint8_into_4bit_chunks_unchecked(cs, input);
        let _ = cs.perform_lookup::<3, 1>(table_id, &[low, high, low]);
    } else {
        // degrade to booleanity gate
        let _bits = Num::from_variable(input).spread_into_bits::<CS, 8>(cs);
    }
}

fn uint8_into_4bit_chunks_unchecked<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Variable,
) -> [Variable; 2] {
    let chunks = cs.alloc_multiple_variables_without_values::<2>();
    use crate::config::*;

    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
        let value_fn = move |input: [F; 1]| {
            let input = <u8 as WitnessCastable<F, F>>::cast_from_source(input[0]);
            let low = input % (1u8 << 4);
            let high = input >> 4;
            [
                F::from_u64_unchecked(low as u64),
                F::from_u64_unchecked(high as u64),
            ]
        };

        let outputs = Place::from_variables(chunks);
        cs.set_values_with_dependencies(&[input.into()], &outputs, value_fn);
    }

    let one = cs.allocate_constant(F::ONE);

    let gate = FmaGateInBaseFieldWithoutConstant {
        params: FmaGateInBaseWithoutConstantParams {
            coeff_for_quadtaric_part: F::from_u64_unchecked(1u64 << 4),
            linear_term_coeff: F::ONE,
        },
        quadratic_part: (one, chunks[1]),
        linear_part: chunks[0],
        rhs_part: input,
    };

    gate.add_to_cs(cs);

    chunks
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash)]
pub struct UInt8<F: SmallField> {
    pub(crate) variable: Variable,
    pub(crate) _marker: std::marker::PhantomData<F>,
}

// it's allocatable and witnessable

impl<F: SmallField> CSAllocatable<F> for UInt8<F> {
    type Witness = u8;
    fn placeholder_witness() -> Self::Witness {
        0u8
    }

    #[inline(always)]
    fn allocate_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let var = cs.alloc_variable_without_value();

        Self::from_variable_checked(cs, var)
    }

    #[inline(always)]
    fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        Self::allocate_checked(cs, witness)
    }

    #[inline(always)]
    fn allocate_constant<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        Self::allocated_constant(cs, witness)
    }
}

impl<F: SmallField> CSAllocatableExt<F> for UInt8<F> {
    const INTERNAL_STRUCT_LEN: usize = 1;

    fn witness_from_set_of_values(values: [F; Self::INTERNAL_STRUCT_LEN]) -> Self::Witness {
        <u8 as WitnessCastable<F, F>>::cast_from_source(values[0])
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
        debug_assert!(F::CAPACITY_BITS >= 8);
        dst.push(F::from_u64_unchecked(witness as u64));
    }
}

use crate::gadgets::traits::witnessable::CSWitnessable;

use super::traits::castable::Convertor;
use super::traits::witnessable::WitnessHookable;

impl<F: SmallField> CSWitnessable<F, 1> for UInt8<F> {
    type ConversionFunction = Convertor<F, [F; 1], u8>;

    fn witness_from_set_of_values(values: [F; 1]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; 1] {
        [self.variable]
    }
}

impl<F: SmallField, const N: usize> CSWitnessable<F, N> for [UInt8<F>; N] {
    type ConversionFunction = Convertor<F, [F; N], [u8; N]>;

    fn witness_from_set_of_values(values: [F; N]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; N] {
        self.map(|el| el.variable)
    }
}

impl<F: SmallField> WitnessHookable<F> for UInt8<F> {
    fn witness_hook<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
    ) -> Box<dyn FnOnce() -> Option<Self::Witness>> {
        let raw_witness = self.get_witness(cs);
        Box::new(move || raw_witness.wait())
    }
}

// impl<F: SmallField, const N: usize> WitnessHookable<F> for [UInt8<F>; N] {
//     fn witness_hook<CS: ConstraintSystem<F>>(
//         &self,
//         cs: &CS,
//     ) -> Box<dyn FnOnce() -> Option<Self::Witness>> {
//         let raw_witness = self.get_witness(cs);
//         Box::new(move || raw_witness.wait())
//     }
// }

use crate::gadgets::traits::selectable::Selectable;

impl<F: SmallField> Selectable<F> for UInt8<F> {
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

impl<F: SmallField> UInt8<F> {
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

    // this routine is not too efficient because we can allocate more per lookup, so use carefully
    pub fn from_variable_checked<CS: ConstraintSystem<F>>(cs: &mut CS, variable: Variable) -> Self {
        range_check_u8(cs, variable);

        let a = Self {
            variable,
            _marker: std::marker::PhantomData,
        };

        a
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
    pub fn allocated_constant<CS: ConstraintSystem<F>>(cs: &mut CS, constant: u8) -> Self {
        debug_assert!(F::CAPACITY_BITS >= 8);

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
    pub fn allocate_checked<CS: ConstraintSystem<F>>(cs: &mut CS, witness: u8) -> Self {
        let a = cs.alloc_single_variable_from_witness(F::from_u64_with_reduction(witness as u64));
        range_check_u8(cs, a);

        let a = Self {
            variable: a,
            _marker: std::marker::PhantomData,
        };

        a
    }

    #[must_use]
    pub fn allocate_pair<CS: ConstraintSystem<F>>(cs: &mut CS, pair: [u8; 2]) -> [Self; 2] {
        let a = cs.alloc_single_variable_from_witness(F::from_u64_with_reduction(pair[0] as u64));
        let b = cs.alloc_single_variable_from_witness(F::from_u64_with_reduction(pair[1] as u64));

        range_check_u8_pair(cs, &[a, b]);

        let a = Self {
            variable: a,
            _marker: std::marker::PhantomData,
        };

        let b = Self {
            variable: b,
            _marker: std::marker::PhantomData,
        };

        [a, b]
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

        if cs.gate_is_allowed::<UIntXAddGate<8>>() {
            let no_carry = cs.allocate_constant(F::ZERO);
            let result_var = UIntXAddGate::<8>::perform_addition_no_carry(
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

        if cs.gate_is_allowed::<UIntXAddGate<8>>() {
            let no_borrow = cs.allocate_constant(F::ZERO);
            let result_var = UIntXAddGate::<8>::perform_subtraction_no_borrow(
                cs,
                self.variable,
                other.variable,
                no_borrow,
                no_borrow,
            );

            let result = Self {
                variable: result_var,
                _marker: std::marker::PhantomData,
            };
            result
        } else {
            unimplemented!()
        }
    }

    #[must_use]
    pub fn overflowing_add<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> (Self, Boolean<F>) {
        if cs.gate_is_allowed::<UIntXAddGate<8>>() {
            let no_carry_in = cs.allocate_constant(F::ZERO);
            let (result_var, carry_out_var) =
                UIntXAddGate::<8>::perform_addition(cs, self.variable, other.variable, no_carry_in);

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
        if cs.gate_is_allowed::<UIntXAddGate<8>>() {
            let no_borrow_in = cs.allocate_constant(F::ZERO);
            let (result_var, borrow_out_var) = UIntXAddGate::<8>::perform_subtraction(
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

    #[inline]
    #[must_use]
    pub fn is_zero<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Boolean<F> {
        self.into_num().is_zero(cs)
    }

    // Give the two's complement inversion of the given UInt8.
    #[must_use]
    pub fn negate<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Self {
        let is_zero = self.is_zero(cs);
        let xor_id = cs
            .get_table_id_for_marker::<Xor8Table>()
            .expect("table should exist");
        let max = UInt8::allocated_constant(cs, u8::MAX).get_variable();
        let mut b = UInt8 {
            variable: cs.perform_lookup::<2, 1>(xor_id, &[self.get_variable(), max])[0],
            _marker: std::marker::PhantomData,
        };
        unsafe {
            b = b.increment_unchecked(cs);
        }
        Selectable::conditionally_select(cs, is_zero, self, &b)
    }

    // Assuming a two's complement representation, give the absolute
    // value of the UInt8.
    #[must_use]
    pub fn abs<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Self {
        let overflow_checker = UInt8::allocated_constant(cs, 2u8.pow(7));
        let (_, of) = self.overflowing_sub(cs, &overflow_checker);
        let neg_self = self.negate(cs);
        Selectable::conditionally_select(cs, of, self, &neg_self)
    }

    #[must_use]
    pub fn div2<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Self {
        let byte_split_id = cs
            .get_table_id_for_marker::<ByteSplitTable<1>>()
            .expect("table should exist");
        UInt8 {
            variable: cs.perform_lookup::<1, 2>(byte_split_id, &[self.get_variable()])[1],
            _marker: std::marker::PhantomData,
        }
    }
}

use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;

impl<F: SmallField> CircuitVarLengthEncodable<F> for UInt8<F> {
    #[inline(always)]
    fn encoding_length(&self) -> usize {
        1
    }
    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, _cs: &mut CS, dst: &mut Vec<Variable>) {
        dst.push(self.variable);
    }
}

use crate::gadgets::traits::allocatable::CSPlaceholder;

impl<F: SmallField> CSPlaceholder<F> for UInt8<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::zero(cs)
    }
}
