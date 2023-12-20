use super::*;
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::cs::DstBuffer;
use crate::cs::Variable;
use crate::field::SmallField;
use crate::gadgets::boolean::Boolean;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::traits::allocatable::CSAllocatableExt;
use crate::gadgets::traits::witnessable::WitnessHookable;
use crate::gadgets::u32::UInt32;
use crate::gadgets::u8::UInt8;
use ethereum_types::Address;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash)]
pub struct UInt160<F: SmallField> {
    pub inner: [UInt32<F>; 5],
}

pub fn decompose_address_as_u32x5(value: Address) -> [u32; 5] {
    [
        u32::from_le_bytes([value.0[19], value.0[18], value.0[17], value.0[16]]),
        u32::from_le_bytes([value.0[15], value.0[14], value.0[13], value.0[12]]),
        u32::from_le_bytes([value.0[11], value.0[10], value.0[9], value.0[8]]),
        u32::from_le_bytes([value.0[7], value.0[6], value.0[5], value.0[4]]),
        u32::from_le_bytes([value.0[3], value.0[2], value.0[1], value.0[0]]),
    ]
}

pub fn recompose_address_from_u32x5(value: [u32; 5]) -> Address {
    let w0 = value[0].to_be_bytes();
    let w1 = value[1].to_be_bytes();
    let w2 = value[2].to_be_bytes();
    let w3 = value[3].to_be_bytes();
    let w4 = value[4].to_be_bytes();

    let mut result = Address::zero();
    result.0.copy_from_slice(&[
        w4[0], w4[1], w4[2], w4[3], w3[0], w3[1], w3[2], w3[3], w2[0], w2[1], w2[2], w2[3], w1[0],
        w1[1], w1[2], w1[3], w0[0], w0[1], w0[2], w0[3],
    ]);

    result
}

impl<F: SmallField> CSAllocatable<F> for UInt160<F> {
    type Witness = Address;
    fn placeholder_witness() -> Self::Witness {
        Address::zero()
    }

    #[inline(always)]
    fn allocate_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let vars = cs.alloc_multiple_variables_without_values::<5>();

        let as_u32 = vars.map(|el| UInt32::from_variable_checked(cs, el));

        Self { inner: as_u32 }
    }

    fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let chunks = decompose_address_as_u32x5(witness);
        let chunks = chunks.map(|el| UInt32::allocate_checked(cs, el));
        Self { inner: chunks }
    }

    #[inline(always)]
    fn allocate_constant<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let chunks = decompose_address_as_u32x5(witness);
        let chunks = chunks.map(|el| UInt32::allocate_constant(cs, el));
        Self { inner: chunks }
    }
}

impl<F: SmallField> CSAllocatableExt<F> for UInt160<F> {
    const INTERNAL_STRUCT_LEN: usize = 5;

    fn witness_from_set_of_values(values: [F; Self::INTERNAL_STRUCT_LEN]) -> Self::Witness {
        recompose_address_from_u32x5(
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
        decompose_address_as_u32x5(witness)
            .map(|el| UInt32::set_internal_variables_values(el, dst));
    }
}

impl<F: SmallField> UInt160<F> {
    #[must_use]
    pub fn allocated_constant<CS: ConstraintSystem<F>>(cs: &mut CS, constant: Address) -> Self {
        debug_assert!(F::CAPACITY_BITS >= 32);

        let chunks = decompose_address_as_u32x5(constant);
        let chunks = chunks.map(|el| UInt32::allocated_constant(cs, el));
        Self { inner: chunks }
    }

    #[must_use]
    pub fn zero<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::allocated_constant(cs, Address::zero())
    }

    /// # Safety
    ///
    /// Does not check the variable to be valid.
    #[inline(always)]
    #[must_use]
    pub unsafe fn from_variables_unchecked(variables: [Variable; 5]) -> Self {
        Self {
            inner: variables.map(|el| UInt32::from_variable_unchecked(el)),
        }
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
        let equals: [_; 5] =
            std::array::from_fn(|idx| UInt32::equals(cs, &a.inner[idx], &b.inner[idx]));

        Boolean::multi_and(cs, &equals)
    }

    #[must_use]
    pub fn is_zero<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Boolean<F> {
        let limbs_are_zero = self.inner.map(|el| el.is_zero(cs));
        Boolean::multi_and(cs, &limbs_are_zero)
    }

    #[must_use]
    pub fn to_le_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 20] {
        let mut encoding = [std::mem::MaybeUninit::uninit(); 20];
        for (dst, src) in encoding
            .iter_mut()
            .zip(self.inner.iter().flat_map(|el| el.to_le_bytes(cs)))
        {
            dst.write(src);
        }

        unsafe { encoding.map(|el| el.assume_init()) }
    }

    #[must_use]
    pub fn to_be_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 20] {
        let mut bytes = self.to_le_bytes(cs);
        bytes.reverse();

        bytes
    }
}

use crate::gadgets::traits::selectable::Selectable;

impl<F: SmallField> Selectable<F> for UInt160<F> {
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

use crate::gadgets::traits::castable::Convertor;
use crate::gadgets::traits::castable::WitnessCastable;
use crate::gadgets::traits::witnessable::CSWitnessable;

impl<F: SmallField> WitnessCastable<F, [F; 5]> for Address {
    #[inline]
    fn cast_from_source(witness: [F; 5]) -> Self {
        let reduced = witness.map(|el| {
            let el = el.as_u64_reduced();
            debug_assert!(el <= u32::MAX as u64);

            el as u32
        });

        recompose_address_from_u32x5(reduced)
    }
    #[inline]
    fn cast_into_source(self) -> [F; 5] {
        let limbs = decompose_address_as_u32x5(self);
        limbs.map(|el| WitnessCastable::cast_into_source(el))
    }
}

impl<F: SmallField> CSWitnessable<F, 5> for UInt160<F> {
    type ConversionFunction = Convertor<F, [F; 5], Address>;

    fn witness_from_set_of_values(values: [F; 5]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; 5] {
        self.inner.map(|el| el.get_variable())
    }
}

impl<F: SmallField> WitnessHookable<F> for UInt160<F> {
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
impl<F: SmallField> MultiSelectable<F> for UInt160<F> {}

use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;

impl<F: SmallField> CircuitVarLengthEncodable<F> for UInt160<F> {
    #[inline(always)]
    fn encoding_length(&self) -> usize {
        5
    }
    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, cs: &mut CS, dst: &mut Vec<Variable>) {
        CircuitVarLengthEncodable::<F>::encode_to_buffer(&self.inner, cs, dst);
    }
}

use crate::gadgets::traits::allocatable::CSPlaceholder;

impl<F: SmallField> CSPlaceholder<F> for UInt160<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::zero(cs)
    }
}
