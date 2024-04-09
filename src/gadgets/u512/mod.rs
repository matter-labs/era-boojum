use super::*;
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::cs::DstBuffer;
use crate::field::SmallField;
use crate::gadgets::boolean::Boolean;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::traits::allocatable::CSAllocatableExt;
use crate::gadgets::traits::witnessable::CSWitnessable;
use crate::gadgets::traits::witnessable::WitnessHookable;
use crate::gadgets::u256::UInt256;
use crate::gadgets::u32::UInt32;
use crate::gadgets::u8::UInt8;
use ethereum_types::U256;

use crate::config::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash)]
pub struct UInt512<F: SmallField> {
    pub inner: [UInt32<F>; 16],
}

pub fn decompose_u512_as_u32x16(value: (U256, U256)) -> [u32; 16] {
    [
        value.0 .0[0] as u32,
        (value.0 .0[0] >> 32) as u32,
        value.0 .0[1] as u32,
        (value.0 .0[1] >> 32) as u32,
        value.0 .0[2] as u32,
        (value.0 .0[2] >> 32) as u32,
        value.0 .0[3] as u32,
        (value.0 .0[3] >> 32) as u32,
        value.1 .0[0] as u32,
        (value.1 .0[0] >> 32) as u32,
        value.1 .0[1] as u32,
        (value.1 .0[1] >> 32) as u32,
        value.1 .0[2] as u32,
        (value.1 .0[2] >> 32) as u32,
        value.1 .0[3] as u32,
        (value.1 .0[3] >> 32) as u32,
    ]
}

pub fn recompose_u512_as_u32x16(value: [u32; 16]) -> (U256, U256) {
    let mut result_1 = U256::zero();
    result_1.0[0] = (value[0] as u64) | ((value[1] as u64) << 32);
    result_1.0[1] = (value[2] as u64) | ((value[3] as u64) << 32);
    result_1.0[2] = (value[4] as u64) | ((value[5] as u64) << 32);
    result_1.0[3] = (value[6] as u64) | ((value[7] as u64) << 32);
    let mut result_2 = U256::zero();
    result_2.0[0] = (value[8] as u64) | ((value[9] as u64) << 32);
    result_2.0[1] = (value[10] as u64) | ((value[11] as u64) << 32);
    result_2.0[2] = (value[12] as u64) | ((value[13] as u64) << 32);
    result_2.0[3] = (value[14] as u64) | ((value[15] as u64) << 32);

    (result_1, result_2)
}

impl<F: SmallField> CSAllocatable<F> for UInt512<F> {
    type Witness = (U256, U256);
    fn placeholder_witness() -> Self::Witness {
        (U256::zero(), U256::zero())
    }

    #[inline(always)]
    #[must_use]
    fn allocate_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let vars = cs.alloc_multiple_variables_without_values::<16>();

        let as_u32 = vars.map(|el| UInt32::from_variable_checked(cs, el));

        Self { inner: as_u32 }
    }

    #[must_use]
    fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let chunks = decompose_u512_as_u32x16(witness);
        let chunks = chunks.map(|el| UInt32::allocate_checked(cs, el));
        Self { inner: chunks }
    }
}

impl<F: SmallField> CSAllocatableExt<F> for UInt512<F> {
    const INTERNAL_STRUCT_LEN: usize = 16;

    fn witness_from_set_of_values(values: [F; Self::INTERNAL_STRUCT_LEN]) -> Self::Witness {
        // value
        recompose_u512_as_u32x16(
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
        decompose_u512_as_u32x16(witness).map(|el| UInt32::set_internal_variables_values(el, dst));
    }
}

use crate::gadgets::traits::selectable::Selectable;

impl<F: SmallField> Selectable<F> for UInt512<F> {
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

impl<F: SmallField> UInt512<F> {
    #[must_use]
    pub fn allocated_constant<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        constant: (U256, U256),
    ) -> Self {
        debug_assert!(F::CAPACITY_BITS >= 32);

        let chunks = decompose_u512_as_u32x16(constant);
        let chunks = chunks.map(|el| UInt32::allocated_constant(cs, el));
        Self { inner: chunks }
    }

    #[must_use]
    pub fn allocate_from_closure_and_dependencies<
        CS: ConstraintSystem<F>,
        FN: FnOnce(&[F]) -> (U256, U256) + 'static + Send + Sync,
    >(
        cs: &mut CS,
        witness_closure: FN,
        dependencies: &[Place],
    ) -> Self {
        let outputs = cs.alloc_multiple_variables_without_values::<16>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: &[F], output_buffer: &mut DstBuffer<'_, '_, F>| {
                debug_assert!(F::CAPACITY_BITS >= 32);
                let witness = (witness_closure)(inputs);
                let chunks = decompose_u512_as_u32x16(witness);

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
        Self::allocated_constant(cs, (U256::zero(), U256::zero()))
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
        let equals: [_; 16] =
            std::array::from_fn(|idx| UInt32::equals(cs, &a.inner[idx], &b.inner[idx]));

        Boolean::multi_and(cs, &equals)
    }

    #[must_use]
    pub fn from_le_bytes<CS: ConstraintSystem<F>>(cs: &mut CS, bytes: [UInt8<F>; 64]) -> Self {
        let mut inner = [std::mem::MaybeUninit::uninit(); 16];
        for (dst, src) in inner.iter_mut().zip(bytes.array_chunks::<4>()) {
            dst.write(UInt32::from_le_bytes(cs, *src));
        }

        let inner = unsafe { inner.map(|el| el.assume_init()) };

        Self { inner }
    }

    #[must_use]
    pub fn from_be_bytes<CS: ConstraintSystem<F>>(cs: &mut CS, bytes: [UInt8<F>; 64]) -> Self {
        let mut inner = [std::mem::MaybeUninit::uninit(); 16];
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
    pub fn to_le_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 64] {
        let mut encoding = [std::mem::MaybeUninit::uninit(); 64];
        for (dst, src) in encoding
            .iter_mut()
            .zip(self.inner.iter().flat_map(|el| el.to_le_bytes(cs)))
        {
            dst.write(src);
        }

        unsafe { encoding.map(|el| el.assume_init()) }
    }

    #[must_use]
    pub fn to_be_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 64] {
        let mut bytes = self.to_le_bytes(cs);
        bytes.reverse();

        bytes
    }

    #[must_use]
    pub fn to_low(self) -> UInt256<F> {
        UInt256 {
            inner: [
                self.inner[0],
                self.inner[1],
                self.inner[2],
                self.inner[3],
                self.inner[4],
                self.inner[5],
                self.inner[6],
                self.inner[7],
            ],
        }
    }

    #[must_use]
    pub fn to_high(self) -> UInt256<F> {
        UInt256 {
            inner: [
                self.inner[8],
                self.inner[9],
                self.inner[10],
                self.inner[11],
                self.inner[12],
                self.inner[13],
                self.inner[14],
                self.inner[15],
            ],
        }
    }
}

use crate::cs::Variable;
use crate::gadgets::traits::castable::Convertor;
use crate::gadgets::traits::castable::WitnessCastable;

impl<F: SmallField> WitnessCastable<F, [F; 16]> for (U256, U256) {
    #[inline]
    fn cast_from_source(witness: [F; 16]) -> Self {
        let reduced = witness.map(|el| {
            let el = el.as_u64_reduced();
            debug_assert!(el <= u32::MAX as u64);

            el as u32
        });

        recompose_u512_as_u32x16(reduced)
    }
    #[inline]
    fn cast_into_source(self) -> [F; 16] {
        let limbs = decompose_u512_as_u32x16(self);
        limbs.map(|el| WitnessCastable::cast_into_source(el))
    }
}

impl<F: SmallField> CSWitnessable<F, 16> for UInt512<F> {
    type ConversionFunction = Convertor<F, [F; 16], (U256, U256)>;

    fn witness_from_set_of_values(values: [F; 16]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; 16] {
        self.inner.map(|el| el.get_variable())
    }
}

impl<F: SmallField> WitnessHookable<F> for UInt512<F> {
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
impl<F: SmallField> MultiSelectable<F> for UInt512<F> {}

use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;

impl<F: SmallField> CircuitVarLengthEncodable<F> for UInt512<F> {
    #[inline(always)]
    fn encoding_length(&self) -> usize {
        16
    }
    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, cs: &mut CS, dst: &mut Vec<Variable>) {
        CircuitVarLengthEncodable::<F>::encode_to_buffer(&self.inner, cs, dst);
    }
}

use crate::gadgets::traits::allocatable::CSPlaceholder;

impl<F: SmallField> CSPlaceholder<F> for UInt512<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::zero(cs)
    }
}
