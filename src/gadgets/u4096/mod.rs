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
use crypto_bigint::U1024;
use crypto_bigint::U2048;
use u2048::UInt2048;

use crate::config::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash)]
pub struct UInt4096<F: SmallField> {
    pub inner: [UInt32<F>; 128],
}

pub fn decompose_u4096_as_u32x128(value: (U2048, U2048)) -> [u32; 128] {
    let low_limbs = value.0.as_limbs();
    let high_limbs = value.1.as_limbs();

    let mut result = [0u32; 128];
    // Filling the low limb
    for i in 0..32 {
        result[i * 2] = low_limbs[i].0 as u32;
        result[i * 2 + 1] = (low_limbs[i].0 >> 32) as u32;
    }
    // Filling the high limb
    for i in 0..32 {
        result[i * 2 + 64] = high_limbs[i].0 as u32;
        result[i * 2 + 1 + 64] = (high_limbs[i].0 >> 32) as u32;
    }

    result
}

pub fn recompose_u4096_as_u32x128(value: [u32; 128]) -> (U2048, U2048) {
    // Filling the low limb
    let mut low = [0u64; 32];
    for i in 0..32 {
        low[i] = (value[i * 2] as u64) | ((value[i * 2 + 1] as u64) << 32);
    }

    // Filling the high limb
    let mut high = [0u64; 32];
    for i in 0..32 {
        high[i] = (value[i * 2 + 32] as u64) | ((value[i * 2 + 1 + 32] as u64) << 32);
    }

    (U2048::from_words(low), U2048::from_words(high))
}

pub fn convert_limb_to_u4096<F, CS>(cs: &mut CS, limb: &UInt32<F>) -> UInt4096<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let mut u4096 = UInt4096::zero(cs);
    u4096.inner[0] = *limb;
    u4096
}

impl<F: SmallField> CSAllocatable<F> for UInt4096<F> {
    type Witness = (U2048, U2048);
    fn placeholder_witness() -> Self::Witness {
        (U2048::ZERO, U2048::ZERO)
    }

    #[inline(always)]
    #[must_use]
    fn allocate_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let vars = cs.alloc_multiple_variables_without_values::<128>();

        let as_u32 = vars.map(|el| UInt32::from_variable_checked(cs, el));

        Self { inner: as_u32 }
    }

    #[must_use]
    fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let chunks = decompose_u4096_as_u32x128(witness);
        let chunks = chunks.map(|el| UInt32::allocate_checked(cs, el));
        Self { inner: chunks }
    }
}

impl<F: SmallField> CSAllocatableExt<F> for UInt4096<F> {
    const INTERNAL_STRUCT_LEN: usize = 128;

    fn witness_from_set_of_values(values: [F; Self::INTERNAL_STRUCT_LEN]) -> Self::Witness {
        // value
        recompose_u4096_as_u32x128(
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
        decompose_u4096_as_u32x128(witness)
            .map(|el| UInt32::set_internal_variables_values(el, dst));
    }
}

use crate::gadgets::traits::selectable::Selectable;

impl<F: SmallField> Selectable<F> for UInt4096<F> {
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

impl<F: SmallField> UInt4096<F> {
    #[must_use]
    pub fn allocated_constant<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        constant: (U2048, U2048),
    ) -> Self {
        debug_assert!(F::CAPACITY_BITS >= 32);

        let chunks = decompose_u4096_as_u32x128(constant);
        let chunks = chunks.map(|el| UInt32::allocated_constant(cs, el));
        Self { inner: chunks }
    }

    #[must_use]
    pub fn allocate_from_closure_and_dependencies<
        CS: ConstraintSystem<F>,
        FN: FnOnce(&[F]) -> (U2048, U2048) + 'static + Send + Sync,
    >(
        cs: &mut CS,
        witness_closure: FN,
        dependencies: &[Place],
    ) -> Self {
        let outputs = cs.alloc_multiple_variables_without_values::<128>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: &[F], output_buffer: &mut DstBuffer<'_, '_, F>| {
                debug_assert!(F::CAPACITY_BITS >= 64);
                let witness = (witness_closure)(inputs);
                let chunks = decompose_u4096_as_u32x128(witness);

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
        Self::allocated_constant(cs, (U2048::ZERO, U2048::ZERO))
    }

    /// Returns `true` if `self >= other`, and `false` otherwise.
    /// Here, `self` and `other` are represented as [`UInt4096<F>`] and [`UInt2048<F>`] respectively.
    #[must_use]
    pub fn geq_than_u2048<CS>(&self, cs: &mut CS, other: &UInt2048<F>) -> Boolean<F>
    where
        CS: ConstraintSystem<F>,
    {
        let high = self.to_high();
        let under_2048 = high.is_zero(cs);
        let over_2048 = under_2048.negated(cs);
        let low = self.to_low();
        let (sub, overflow) = other.overflowing_sub(cs, &low);
        let a_equal_b = sub.is_zero(cs);
        Boolean::multi_or(cs, &[overflow, a_equal_b, over_2048])
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

    /// Multiplies a number by 2^{32}. Panics if the number overflows.
    #[must_use]
    pub fn must_mul_by_two_pow_32<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Self {
        let boolean_true = Boolean::allocated_constant(cs, true);
        let last_limb_zero = self.inner[127].is_zero(cs);
        Boolean::enforce_equal(cs, &last_limb_zero, &boolean_true);

        let mut new_inner = self.inner;
        new_inner.copy_within(0..127, 1);
        new_inner[0] = UInt32::zero(cs);

        Self { inner: new_inner }
    }

    /// Find quotient and remainder of division of `self` by `other` using the naive long division algorithm in base `2^{32}`
    /// since both [`UInt4096<F>`] and [`UInt2048<F>`] are represented as arrays of [`UInt32<F>`]. The implementation is based on
    /// algorithm https://en.wikipedia.org/wiki/Long_division#Algorithm_for_arbitrary_base,
    /// where `k=128`, `l=64`, and base `b=2^{32}`.
    #[must_use]
    pub fn long_division<CS>(&self, cs: &mut CS, other: &UInt2048<F>) -> (UInt4096<F>, UInt2048<F>)
    where
        CS: ConstraintSystem<F>,
    {
        const U2048_MAX_LIMBS: usize = 64;
        const U4096_MAX_LIMBS: usize = 128;
        const MAX_BINARY_SEARCH_ITERATIONS: usize = 1025;

        // Initializing constants
        let base = U1024::from_le_hex("0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000");
        let base = UInt2048::allocated_constant(cs, (base, U1024::ZERO));
        let boolean_false = Boolean::allocated_constant(cs, false);
        let one = UInt2048::allocated_constant(cs, (U1024::ONE, U1024::ZERO));

        // q <- 0
        let mut q = UInt4096::zero(cs);

        // r <- first 63 limbs of self, thus it fits in UInt2048
        let mut r = self.to_high();
        r.inner[0] = UInt32::zero(cs);
        r.inner.copy_within(1..U2048_MAX_LIMBS, 0);
        r.inner[U2048_MAX_LIMBS - 1] = UInt32::zero(cs);

        for i in 0..U2048_MAX_LIMBS + 1 {
            // \alpha_{i+l-1} is (k-l-i)th limb of n
            let alpha = self.inner[U2048_MAX_LIMBS - i];
            let alpha = convert_limb_to_u4096(cs, &alpha);

            // d_i <- b*r_{i-1} + \alpha_{i+l-1}
            // d_i can safely be UInt512 in size.
            // r can have any number of limbs up to 8.
            // base is 2 limbs wide since b=(2^{32}-1)+1
            // TODO: Mul by base might be optimized
            let d = base.widening_mul(cs, &r, 2, 8);
            let (d_plus_alpha, overflow) = d.overflowing_add(cs, &alpha);
            // d_i cannot overflow UInt512
            Boolean::enforce_equal(cs, &overflow, &boolean_false);
            let d = d_plus_alpha;

            // beta_i <- next digit of quotient. We use
            // binary search to find suitable beta_i
            let mut beta = UInt2048::zero(cs);
            let mut left = UInt2048::zero(cs);
            let mut right = base;

            // Preparing new_r to further update r
            let mut new_r = UInt4096::zero(cs);

            for _ in 0..MAX_BINARY_SEARCH_ITERATIONS {
                // beta <- ceil((right + left) / 2)
                let (new_beta, overflow) = right.overflowing_add(cs, &left);
                // Cannot overflow since right and left are less than b=2^{32}
                Boolean::enforce_equal(cs, &overflow, &boolean_false);

                // Since new_beta.div2 gives floor, we need to add 1 if new_beta is odd to get ceil
                let odd = new_beta.is_odd(cs);
                let beta_div_2 = new_beta.div2(cs);
                let (beta_div_2_plus_1, overflow) = beta_div_2.overflowing_add(cs, &one);
                // Cannot overflow since beta_div_2+one is less than b=2^{32}
                Boolean::enforce_equal(cs, &overflow, &boolean_false);
                beta = UInt2048::conditionally_select(cs, odd, &beta_div_2_plus_1, &beta_div_2);

                // r <- d - m * beta
                // beta can fit in 2 limbs since it is less or equal to b=2^{32}
                let m_beta = other.widening_mul(cs, &beta, 8, 2);
                let (r, r_negative) = d.overflowing_sub(cs, &m_beta);

                // if r < 0 (that is, overflow occurred), then right <- beta - 1
                // beta - 1 might overflow at step 33, but we don't care about it
                let (beta_minus_1, _) = beta.overflowing_sub(cs, &one);
                right = UInt2048::conditionally_select(cs, r_negative, &beta_minus_1, &right);

                // if r >= m, then left <- beta + 1
                let r_geq_m = r.geq_than_u2048(cs, other);
                // We should handle the case when r overflowed
                let r_positive = r_negative.negated(cs);
                let r_greater_m = r_geq_m.and(cs, r_positive);
                let (beta_plus_1, overflow) = beta.overflowing_add(cs, &one);
                // Cannot overflow since beta < b=2^{32}
                Boolean::enforce_equal(cs, &overflow, &boolean_false);
                left = UInt2048::conditionally_select(cs, r_greater_m, &beta_plus_1, &left);

                // Updating r
                new_r = r
            }

            // Asserting that new_r is indeed fits in UInt256
            let boolean_true = Boolean::allocated_constant(cs, true);
            for limb in new_r.inner[8..].iter() {
                let limb_is_zero = limb.is_zero(cs);
                Boolean::enforce_equal(cs, &limb_is_zero, &boolean_true);
            }
            // Update r
            r = new_r.to_low();

            // Asserting that r < m
            let (_, overflow) = other.overflowing_sub(cs, &r);
            Boolean::enforce_equal(cs, &overflow, &boolean_false);

            // q_i <- b*q_{i-1} + beta_i
            let beta_u512 = beta.to_u4096(cs);
            q = q.must_mul_by_two_pow_32(cs);
            let (new_q, overflow) = q.overflowing_add(cs, &beta_u512);
            // Cannot overflow since quotient cannot exceed 2^{512}
            Boolean::enforce_equal(cs, &overflow, &boolean_false);
            q = new_q;
        }

        (q, r)
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
        let equals: [_; 128] =
            std::array::from_fn(|idx| UInt32::equals(cs, &a.inner[idx], &b.inner[idx]));

        Boolean::multi_and(cs, &equals)
    }

    #[must_use]
    pub fn from_le_bytes<CS: ConstraintSystem<F>>(cs: &mut CS, bytes: [UInt8<F>; 512]) -> Self {
        let mut inner = [std::mem::MaybeUninit::uninit(); 128];
        for (dst, src) in inner.iter_mut().zip(bytes.array_chunks::<4>()) {
            dst.write(UInt32::from_le_bytes(cs, *src));
        }

        let inner = unsafe { inner.map(|el| el.assume_init()) };

        Self { inner }
    }

    #[must_use]
    pub fn from_limbs(limbs: [UInt32<F>; 128]) -> Self {
        Self { inner: limbs }
    }

    #[must_use]
    pub fn from_be_bytes<CS: ConstraintSystem<F>>(cs: &mut CS, bytes: [UInt8<F>; 512]) -> Self {
        let mut inner = [std::mem::MaybeUninit::uninit(); 128];
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
    pub fn to_le_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 512] {
        let mut encoding = [std::mem::MaybeUninit::uninit(); 512];
        for (dst, src) in encoding
            .iter_mut()
            .zip(self.inner.iter().flat_map(|el| el.to_le_bytes(cs)))
        {
            dst.write(src);
        }

        unsafe { encoding.map(|el| el.assume_init()) }
    }

    #[must_use]
    pub fn to_be_bytes<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> [UInt8<F>; 512] {
        let mut bytes = self.to_le_bytes(cs);
        bytes.reverse();

        bytes
    }

    #[must_use]
    pub fn to_low(self) -> UInt2048<F> {
        UInt2048 {
            inner: self.inner[..64].try_into().expect("incorrect slice size"),
        }
    }

    #[must_use]
    pub fn to_high(self) -> UInt2048<F> {
        UInt2048 {
            inner: self.inner[64..].try_into().expect("incorrect slice size"),
        }
    }
}

use crate::cs::Variable;
use crate::gadgets::traits::castable::Convertor;
use crate::gadgets::traits::castable::WitnessCastable;

impl<F: SmallField> WitnessCastable<F, [F; 128]> for (U2048, U2048) {
    #[inline]
    fn cast_from_source(witness: [F; 128]) -> Self {
        let reduced = witness.map(|el| {
            let el = el.as_u64_reduced();
            debug_assert!(el <= u32::MAX as u64);

            el as u32
        });

        recompose_u4096_as_u32x128(reduced)
    }

    #[inline]
    fn cast_into_source(self) -> [F; 128] {
        let limbs = decompose_u4096_as_u32x128(self);
        limbs.map(|el| WitnessCastable::cast_into_source(el))
    }
}

impl<F: SmallField> CSWitnessable<F, 128> for UInt4096<F> {
    type ConversionFunction = Convertor<F, [F; 128], (U2048, U2048)>;

    fn witness_from_set_of_values(values: [F; 128]) -> Self::Witness {
        WitnessCastable::cast_from_source(values)
    }

    fn as_variables_set(&self) -> [Variable; 128] {
        self.inner.map(|el| el.get_variable())
    }
}

impl<F: SmallField> WitnessHookable<F> for UInt4096<F> {
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
impl<F: SmallField> MultiSelectable<F> for UInt4096<F> {}

use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;

impl<F: SmallField> CircuitVarLengthEncodable<F> for UInt4096<F> {
    #[inline(always)]
    fn encoding_length(&self) -> usize {
        64
    }
    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, cs: &mut CS, dst: &mut Vec<Variable>) {
        CircuitVarLengthEncodable::<F>::encode_to_buffer(&self.inner, cs, dst);
    }
}

use crate::gadgets::traits::allocatable::CSPlaceholder;

impl<F: SmallField> CSPlaceholder<F> for UInt4096<F> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::zero(cs)
    }
}
