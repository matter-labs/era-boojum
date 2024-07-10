use super::*;
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::cs::DstBuffer;
use crate::field::SmallField;
use crate::gadgets::boolean::Boolean;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::traits::allocatable::CSAllocatableExt;
use crate::gadgets::traits::witnessable::CSWitnessable;
use crate::gadgets::traits::witnessable::WitnessHookable;
use crate::gadgets::u32::UInt32;
use crate::gadgets::u8::UInt8;
use blake2s::mixing_function::merge_byte_using_table;
use crypto_bigint::U1024;
use tables::ByteSplitTable;
use u1024::UInt1024;
use u4096::UInt4096;

use crate::config::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash)]
pub struct UInt2048<F: SmallField> {
    pub inner: [UInt32<F>; 64],
}

pub fn decompose_u2048_as_u32x64(value: (U1024, U1024)) -> [u32; 64] {
    let low_limbs = value.0.as_limbs();
    let high_limbs = value.1.as_limbs();

    let mut result = [0u32; 64];
    // Filling the low limb
    for i in 0..16 {
        result[i * 2] = low_limbs[i].0 as u32;
        result[i * 2 + 1] = (low_limbs[i].0 >> 32) as u32;
    }
    // Filling the high limb
    for i in 0..16 {
        result[i * 2 + 32] = high_limbs[i].0 as u32;
        result[i * 2 + 1 + 32] = (high_limbs[i].0 >> 32) as u32;
    }

    result
}

pub fn recompose_u2048_as_u32x64(value: [u32; 64]) -> (U1024, U1024) {
    // Filling the low limb
    let mut low = [0u64; 16];
    for i in 0..16 {
        low[i] = (value[i * 2] as u64) | ((value[i * 2 + 1] as u64) << 32);
    }

    // Filling the high limb
    let mut high = [0u64; 16];
    for i in 0..16 {
        high[i] = (value[i * 2 + 32] as u64) | ((value[i * 2 + 1 + 32] as u64) << 32);
    }

    (U1024::from_words(low), U1024::from_words(high))
}

impl<F: SmallField> CSAllocatable<F> for UInt2048<F> {
    type Witness = (U1024, U1024);
    fn placeholder_witness() -> Self::Witness {
        (U1024::ZERO, U1024::ZERO)
    }

    #[inline(always)]
    #[must_use]
    fn allocate_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let vars = cs.alloc_multiple_variables_without_values::<64>();

        let as_u32 = vars.map(|el| UInt32::from_variable_checked(cs, el));

        Self { inner: as_u32 }
    }

    #[must_use]
    fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let chunks = decompose_u2048_as_u32x64(witness);
        let chunks = chunks.map(|el| UInt32::allocate_checked(cs, el));
        Self { inner: chunks }
    }
}

impl<F: SmallField> CSAllocatableExt<F> for UInt2048<F> {
    const INTERNAL_STRUCT_LEN: usize = 64;

    fn witness_from_set_of_values(values: [F; Self::INTERNAL_STRUCT_LEN]) -> Self::Witness {
        // value
        recompose_u2048_as_u32x64(
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
        decompose_u2048_as_u32x64(witness).map(|el| UInt32::set_internal_variables_values(el, dst));
    }
}

use crate::gadgets::traits::selectable::Selectable;

impl<F: SmallField> Selectable<F> for UInt2048<F> {
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

impl<F: SmallField> UInt2048<F> {
    #[must_use]
    pub fn allocated_constant<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        constant: (U1024, U1024),
    ) -> Self {
        debug_assert!(F::CAPACITY_BITS >= 32);

        let chunks = decompose_u2048_as_u32x64(constant);
        let chunks = chunks.map(|el| UInt32::allocated_constant(cs, el));
        Self { inner: chunks }
    }

    #[must_use]
    pub fn allocate_from_closure_and_dependencies<
        CS: ConstraintSystem<F>,
        FN: FnOnce(&[F]) -> (U1024, U1024) + 'static + Send + Sync,
    >(
        cs: &mut CS,
        witness_closure: FN,
        dependencies: &[Place],
    ) -> Self {
        let outputs = cs.alloc_multiple_variables_without_values::<64>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: &[F], output_buffer: &mut DstBuffer<'_, '_, F>| {
                debug_assert!(F::CAPACITY_BITS >= 64);
                let witness = (witness_closure)(inputs);
                let chunks = decompose_u2048_as_u32x64(witness);

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
        Self::allocated_constant(cs, (U1024::ZERO, U1024::ZERO))
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

    #[must_use]
    pub fn widening_mul<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &Self,
        self_limbs: usize,
        other_limbs: usize,
    ) -> UInt4096<F> {
        assert!(
            self_limbs + other_limbs <= 128,
            "total number of limbs must be <= 128"
        );

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

        let mut inner = [UInt32::<F>::zero(cs); 128];
        inner[..self_limbs + other_limbs].copy_from_slice(&remainders);
        UInt4096 { inner }
    }

    /// Multiplies a number by 2^{32}. Panics if the number overflows.
    #[must_use]
    pub fn must_mul_by_two_pow_32<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Self {
        let boolean_true = Boolean::allocated_constant(cs, true);
        let last_limb_zero = self.inner[63].is_zero(cs);
        Boolean::enforce_equal(cs, &last_limb_zero, &boolean_true);

        let mut new_inner = self.inner;
        new_inner.copy_within(0..65, 1);
        new_inner[0] = UInt32::zero(cs);

        Self { inner: new_inner }
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

    /// Finds the result of multiplying `self` by `other` mod `modulo`.
    pub fn modmul<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        other: &UInt2048<F>,
        modulo: &UInt2048<F>,
    ) -> UInt2048<F> {
        // We take 8 limbs since scalar can be of any size
        let product = self.widening_mul(cs, other, 64, 64);
        let (_, remainder) = product.long_division(cs, modulo);
        remainder
    }

    #[must_use]
    pub fn is_odd<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Boolean<F> {
        self.inner[0].into_num().spread_into_bits::<CS, 32>(cs)[0]
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
    pub fn to_u4096<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> UInt4096<F> {
        let mut u4096: UInt4096<F> = UInt4096::zero(cs);
        u4096.inner[..64].copy_from_slice(&self.inner);
        u4096
    }

    #[must_use]
    pub fn equals<CS: ConstraintSystem<F>>(cs: &mut CS, a: &Self, b: &Self) -> Boolean<F> {
        let equals: [_; 64] =
            std::array::from_fn(|idx| UInt32::equals(cs, &a.inner[idx], &b.inner[idx]));

        Boolean::multi_and(cs, &equals)
    }

    #[must_use]
    pub fn from_le_bytes<CS: ConstraintSystem<F>>(cs: &mut CS, bytes: [UInt8<F>; 256]) -> Self {
        let mut inner = [std::mem::MaybeUninit::uninit(); 64];
        for (dst, src) in inner.iter_mut().zip(bytes.array_chunks::<4>()) {
            dst.write(UInt32::from_le_bytes(cs, *src));
        }

        let inner = unsafe { inner.map(|el| el.assume_init()) };

        Self { inner }
    }

    #[must_use]
    pub fn from_limbs(limbs: [UInt32<F>; 64]) -> Self {
        Self { inner: limbs }
    }

    #[must_use]
    pub fn from_be_bytes<CS: ConstraintSystem<F>>(cs: &mut CS, bytes: [UInt8<F>; 256]) -> Self {
        let mut inner = [std::mem::MaybeUninit::uninit(); 64];
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
    pub fn to_le_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 256] {
        let mut encoding = [std::mem::MaybeUninit::uninit(); 256];
        for (dst, src) in encoding
            .iter_mut()
            .zip(self.inner.iter().flat_map(|el| el.to_le_bytes(cs)))
        {
            dst.write(src);
        }

        unsafe { encoding.map(|el| el.assume_init()) }
    }

    #[must_use]
    pub fn to_be_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 256] {
        let mut bytes = self.to_le_bytes(cs);
        bytes.reverse();

        bytes
    }

    #[must_use]
    pub fn to_low(self) -> UInt1024<F> {
        UInt1024 {
            inner: self.inner[..32].try_into().expect("incorrect slice size"),
        }
    }

    #[must_use]
    pub fn to_high(self) -> UInt1024<F> {
        UInt1024 {
            inner: self.inner[32..].try_into().expect("incorrect slice size"),
        }
    }
}

use crate::cs::Variable;
use crate::gadgets::traits::castable::Convertor;
use crate::gadgets::traits::castable::WitnessCastable;

impl<F: SmallField> WitnessCastable<F, [F; 64]> for (U1024, U1024) {
    #[inline]
    fn cast_from_source(witness: [F; 64]) -> Self {
        let reduced = witness.map(|el| {
            let el = el.as_u64_reduced();
            debug_assert!(el <= u32::MAX as u64);

            el as u32
        });

        recompose_u2048_as_u32x64(reduced)
    }

    #[inline]
    fn cast_into_source(self) -> [F; 64] {
        let limbs = decompose_u2048_as_u32x64(self);
        limbs.map(|el| WitnessCastable::cast_into_source(el))
    }
}

impl<F: SmallField> CSWitnessable<F, 64> for UInt2048<F> {
    type ConversionFunction = Convertor<F, [F; 64], (U1024, U1024)>;

    fn witness_from_set_of_values(values: [F; 64]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; 64] {
        self.inner.map(|el| el.get_variable())
    }
}

impl<F: SmallField> WitnessHookable<F> for UInt2048<F> {
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
impl<F: SmallField> MultiSelectable<F> for UInt2048<F> {}

use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;

impl<F: SmallField> CircuitVarLengthEncodable<F> for UInt2048<F> {
    #[inline(always)]
    fn encoding_length(&self) -> usize {
        64
    }
    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, cs: &mut CS, dst: &mut Vec<Variable>) {
        CircuitVarLengthEncodable::<F>::encode_to_buffer(&self.inner, cs, dst);
    }
}

use crate::gadgets::traits::allocatable::CSPlaceholder;

impl<F: SmallField> CSPlaceholder<F> for UInt2048<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::zero(cs)
    }
}
