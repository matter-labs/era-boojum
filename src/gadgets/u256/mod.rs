use super::*;
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::cs::DstBuffer;
use crate::field::SmallField;
use crate::gadgets::blake2s::mixing_function::merge_byte_using_table;
use crate::gadgets::boolean::Boolean;
use crate::gadgets::tables::ByteSplitTable;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::traits::allocatable::CSAllocatableExt;
use crate::gadgets::traits::witnessable::CSWitnessable;
use crate::gadgets::traits::witnessable::WitnessHookable;
use crate::gadgets::u32::UInt32;
use crate::gadgets::u512::UInt512;
use crate::gadgets::u8::UInt8;
use ethereum_types::U256;

use crate::config::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash)]
pub struct UInt256<F: SmallField> {
    pub inner: [UInt32<F>; 8],
}

pub fn decompose_u256_as_u32x8(value: U256) -> [u32; 8] {
    [
        value.0[0] as u32,
        (value.0[0] >> 32) as u32,
        value.0[1] as u32,
        (value.0[1] >> 32) as u32,
        value.0[2] as u32,
        (value.0[2] >> 32) as u32,
        value.0[3] as u32,
        (value.0[3] >> 32) as u32,
    ]
}

pub fn recompose_u256_as_u32x8(value: [u32; 8]) -> U256 {
    let mut result = U256::zero();
    result.0[0] = (value[0] as u64) | ((value[1] as u64) << 32);
    result.0[1] = (value[2] as u64) | ((value[3] as u64) << 32);
    result.0[2] = (value[4] as u64) | ((value[5] as u64) << 32);
    result.0[3] = (value[6] as u64) | ((value[7] as u64) << 32);

    result
}

impl<F: SmallField> CSAllocatable<F> for UInt256<F> {
    type Witness = U256;
    fn placeholder_witness() -> Self::Witness {
        U256::zero()
    }

    #[inline(always)]
    fn allocate_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let vars = cs.alloc_multiple_variables_without_values::<8>();

        let as_u32 = vars.map(|el| UInt32::from_variable_checked(cs, el));

        Self { inner: as_u32 }
    }

    fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let chunks = decompose_u256_as_u32x8(witness);
        let chunks = chunks.map(|el| UInt32::allocate_checked(cs, el));
        Self { inner: chunks }
    }

    fn allocate_constant<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let chunks = decompose_u256_as_u32x8(witness);
        let chunks = chunks.map(|el| UInt32::allocate_constant(cs, el));
        Self { inner: chunks }
    }
}

impl<F: SmallField> CSAllocatableExt<F> for UInt256<F> {
    const INTERNAL_STRUCT_LEN: usize = 8;

    fn witness_from_set_of_values(values: [F; Self::INTERNAL_STRUCT_LEN]) -> Self::Witness {
        // value
        recompose_u256_as_u32x8(
            values.map(|el| <u32 as WitnessCastable<F, F>>::cast_from_source(el)),
        )
    }

    // we should be able to allocate without knowing values yet
    fn create_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::allocate_without_value(cs)
    }

    fn flatten_as_variables(&self) -> [Variable; Self::INTERNAL_STRUCT_LEN]
    where
        [(); Self::INTERNAL_STRUCT_LEN]:,
    {
        self.inner.map(|el| el.get_variable())
    }

    fn set_internal_variables_values(witness: Self::Witness, dst: &mut DstBuffer<'_, '_, F>) {
        decompose_u256_as_u32x8(witness).map(|el| UInt32::set_internal_variables_values(el, dst));
    }
}

use crate::gadgets::traits::selectable::Selectable;

impl<F: SmallField> Selectable<F> for UInt256<F> {
    #[must_use]
    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self {
        let inner = Selectable::conditionally_select(cs, flag, &a.inner, &b.inner);

        Self { inner }
    }
}

impl<F: SmallField> UInt256<F> {
    #[must_use]
    pub fn allocated_constant<CS: ConstraintSystem<F>>(cs: &mut CS, constant: U256) -> Self {
        debug_assert!(F::CAPACITY_BITS >= 32);

        let chunks = decompose_u256_as_u32x8(constant);
        let chunks = chunks.map(|el| UInt32::allocated_constant(cs, el));
        Self { inner: chunks }
    }

    #[must_use]
    pub fn allocate_from_closure_and_dependencies<
        CS: ConstraintSystem<F>,
        FN: FnOnce(&[F]) -> U256 + 'static + Send + Sync,
    >(
        cs: &mut CS,
        witness_closure: FN,
        dependencies: &[Place],
    ) -> Self {
        let outputs = cs.alloc_multiple_variables_without_values::<8>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: &[F], output_buffer: &mut DstBuffer<'_, '_, F>| {
                debug_assert!(F::CAPACITY_BITS >= 32);
                let witness = (witness_closure)(inputs);
                let chunks = decompose_u256_as_u32x8(witness);

                output_buffer.extend(chunks.map(|el| F::from_u64_unchecked(el as u64)));
            };

            cs.set_values_with_dependencies_vararg(
                dependencies,
                &Place::from_variables(outputs),
                value_fn,
            );
        }

        let chunks = outputs.map(|el| UInt32::from_variable_checked(cs, el));
        Self { inner: chunks }
    }

    #[must_use]
    pub fn zero<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::allocated_constant(cs, U256::zero())
    }

    #[must_use]
    pub fn overflowing_add<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> (Self, Boolean<F>) {
        let mut carry_out = Boolean::allocated_constant(cs, false);
        let mut result = *self; // any uninit would be fine too
        for ((a, b), dst) in self
            .inner
            .iter()
            .zip(other.inner.iter())
            .zip(result.inner.iter_mut())
        {
            let (c, carry) = (*a).overflowing_add_with_carry_in(cs, *b, carry_out);
            *dst = c;
            carry_out = carry;
        }

        (result, carry_out)
    }

    #[must_use]
    pub fn overflowing_sub<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
    ) -> (Self, Boolean<F>) {
        let mut borrow_out = Boolean::allocated_constant(cs, false);
        let mut result = *self; // any uninit would be fine too
        for ((a, b), dst) in self
            .inner
            .iter()
            .zip(other.inner.iter())
            .zip(result.inner.iter_mut())
        {
            let (c, borrow) = (*a).overflowing_sub_with_borrow_in(cs, *b, borrow_out);
            *dst = c;
            borrow_out = borrow;
        }

        (result, borrow_out)
    }

    // Returns the result of multiplication between two 256-bit unsigned
    // integers as a 512-bit wide integer.
    //
    // NOTE: This merely implements the multiplication with the assumption
    // that `other` is no wider than 192 bits. TODO assert
    // TODO: This could really be cleaned up with a bit of metaprogramming
    // NOTE: Since this `other` variable is pretty constant for use with secp,
    // maybe we can actually shave off more limbs to make this cheaper
    #[must_use]
    pub fn widening_mul<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
        self_limbs: usize,
        other_limbs: usize,
    ) -> UInt512<F> {
        assert!(self_limbs + other_limbs <= 16);

        let zero = UInt32::allocated_constant(cs, 0);
        let mut remainders = vec![UInt32::<F>::zero(cs); self_limbs + other_limbs];

        for i in 0..self_limbs {
            let mut carry = UInt32::allocated_constant(cs, 0);
            for j in 0..other_limbs {
                let res = UInt32::fma_with_carry(
                    cs,
                    self.inner[i],
                    other.inner[j],
                    if i == 0 { zero } else { remainders[i + j] },
                    carry,
                );
                (remainders[i + j], carry) = (res[0].0, res[1].0);
            }
            remainders[i + other_limbs] = carry;
        }

        let mut inner = [UInt32::<F>::zero(cs); 16];
        inner[..self_limbs + other_limbs].copy_from_slice(&remainders);
        UInt512 { inner }
    }

    // Returns the value unchanges if `bit` is `true`, and 0 otherwise
    #[must_use]
    pub fn mask<CS: ConstraintSystem<F>>(&self, cs: &mut CS, masking_bit: Boolean<F>) -> Self {
        let new_inner = self.inner.map(|el| el.mask(cs, masking_bit));
        Self { inner: new_inner }
    }

    // Returns the value unchanges if `bit` is `false`, and 0 otherwise
    #[must_use]
    pub fn mask_negated<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        masking_bit: Boolean<F>,
    ) -> Self {
        let new_inner = self.inner.map(|el| el.mask_negated(cs, masking_bit));
        Self { inner: new_inner }
    }

    #[must_use]
    pub fn equals<CS: ConstraintSystem<F>>(cs: &mut CS, a: &Self, b: &Self) -> Boolean<F> {
        let equals: [_; 8] =
            std::array::from_fn(|idx| UInt32::equals(cs, &a.inner[idx], &b.inner[idx]));

        Boolean::multi_and(cs, &equals)
    }

    #[must_use]
    pub fn from_le_bytes<CS: ConstraintSystem<F>>(cs: &mut CS, bytes: [UInt8<F>; 32]) -> Self {
        let mut inner = [std::mem::MaybeUninit::uninit(); 8];
        for (dst, src) in inner.iter_mut().zip(bytes.array_chunks::<4>()) {
            dst.write(UInt32::from_le_bytes(cs, *src));
        }

        let inner = unsafe { inner.map(|el| el.assume_init()) };

        Self { inner }
    }

    #[must_use]
    pub fn from_be_bytes<CS: ConstraintSystem<F>>(cs: &mut CS, bytes: [UInt8<F>; 32]) -> Self {
        let mut inner = [std::mem::MaybeUninit::uninit(); 8];
        for (dst, src) in inner.iter_mut().rev().zip(bytes.array_chunks::<4>()) {
            dst.write(UInt32::from_be_bytes(cs, *src));
        }

        let inner = unsafe { inner.map(|el| el.assume_init()) };

        Self { inner }
    }

    #[must_use]
    pub fn is_zero<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Boolean<F> {
        let limbs_are_zero = self.inner.map(|el| el.is_zero(cs));
        Boolean::multi_and(cs, &limbs_are_zero)
    }

    #[must_use]
    pub fn is_odd<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Boolean<F> {
        self.inner[0].into_num().spread_into_bits::<CS, 32>(cs)[0]
    }

    #[must_use]
    pub fn to_le_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 32] {
        let mut encoding = [std::mem::MaybeUninit::uninit(); 32];
        for (dst, src) in encoding
            .iter_mut()
            .zip(self.inner.iter().flat_map(|el| el.to_le_bytes(cs)))
        {
            dst.write(src);
        }

        unsafe { encoding.map(|el| el.assume_init()) }
    }

    #[must_use]
    pub fn to_be_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 32] {
        let mut bytes = self.to_le_bytes(cs);
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

use crate::cs::Variable;
use crate::gadgets::traits::castable::Convertor;
use crate::gadgets::traits::castable::WitnessCastable;

impl<F: SmallField> WitnessCastable<F, [F; 8]> for U256 {
    #[inline]
    fn cast_from_source(witness: [F; 8]) -> Self {
        let reduced = witness.map(|el| {
            let el = el.as_u64_reduced();
            debug_assert!(el <= u32::MAX as u64);

            el as u32
        });

        recompose_u256_as_u32x8(reduced)
    }
    #[inline]
    fn cast_into_source(self) -> [F; 8] {
        let limbs = decompose_u256_as_u32x8(self);
        limbs.map(|el| WitnessCastable::cast_into_source(el))
    }
}

impl<F: SmallField> CSWitnessable<F, 8> for UInt256<F> {
    type ConversionFunction = Convertor<F, [F; 8], U256>;

    fn witness_from_set_of_values(values: [F; 8]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; 8] {
        self.inner.map(|el| el.get_variable())
    }
}

impl<F: SmallField> WitnessHookable<F> for UInt256<F> {
    fn witness_hook<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
    ) -> Box<dyn FnOnce() -> Option<Self::Witness>> {
        let raw_witness = self.get_witness(cs);
        Box::new(move || raw_witness.wait())
    }
}

use crate::gadgets::traits::selectable::MultiSelectable;
// multiselect doesn't make much sense here because we can do parallel over chunks,
// so we degrade to default impl via normal select
impl<F: SmallField> MultiSelectable<F> for UInt256<F> {}

use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;

impl<F: SmallField> CircuitVarLengthEncodable<F> for UInt256<F> {
    #[inline(always)]
    fn encoding_length(&self) -> usize {
        8
    }
    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, cs: &mut CS, dst: &mut Vec<Variable>) {
        CircuitVarLengthEncodable::<F>::encode_to_buffer(&self.inner, cs, dst);
    }
}

use crate::gadgets::traits::allocatable::CSPlaceholder;

impl<F: SmallField> CSPlaceholder<F> for UInt256<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::zero(cs)
    }
}
