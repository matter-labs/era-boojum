use ethereum_types::U256;

use crate::{cs::traits::cs::ConstraintSystem, field::SmallField, gadgets::traits::witnessable::CSWitnessable};

use super::{
    boolean::Boolean,
    traits::{selectable::Selectable, witnessable::WitnessHookable},
    u256::UInt256,
    u32::UInt32,
    u512::UInt512,
};

const U256_MAX_BITS: usize = 256;
const U512_MAX_BITS: usize = 512;
const U256_MAX_LIMBS: usize = 8;
const U512_MAX_LIMBS: usize = 16;

const MAX_BINARY_SEARCH_ITERATIONS: usize = 33;

fn convert_limb_to_u512<F, CS>(cs: &mut CS, limb: &UInt32<F>) -> UInt512<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let mut u512 = UInt512::zero(cs);
    u512.inner[0] = limb.clone();
    u512
}

fn convert_u256_to_u512<F, CS>(cs: &mut CS, u256: &UInt256<F>) -> UInt512<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let mut u512 = UInt512::zero(cs);
    u512.inner[..8].copy_from_slice(&u256.inner);
    u512
}

/// Returns `true` if `a >= b`, `false` otherwise.
/// Here, `a` and `b` are represented as `UInt512<F>` and `UInt256<F>` respectively.
fn u512_geq_than_u256<F, CS>(cs: &mut CS, a: &UInt512<F>, b: &UInt256<F>) -> Boolean<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let mut limbs = [UInt32::zero(cs); 16];
    // Put b.inner into first 8 elements
    limbs[..8].copy_from_slice(&b.inner);

    let b_u512 = UInt512::from_limbs(limbs);
    // If a >= b, then b-a should overflow or equal to 0
    let (sub, overflow) = b_u512.overflowing_sub(cs, a);
    let a_equal_b = sub.is_zero(cs);

    overflow.or(cs, a_equal_b)
}

/// Find quotient and remainder of division of `n` by `m` using the naive long division algorithm in base 2^{32}
/// since both `UInt512<F>` and `UInt256<F>` are represented as arrays of `UInt8<F>`. The implementation is based on
/// algorithm https://en.wikipedia.org/wiki/Long_division#Algorithm_for_arbitrary_base,
/// where k=16, l=8, and base b=2^{32}.
fn long_division<F, CS>(cs: &mut CS, n: &UInt512<F>, m: &UInt256<F>) -> (UInt512<F>, UInt256<F>)
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    // Initializing constants
    let base = U256::from_str_radix("0x100000000", 16).unwrap();
    let base = UInt256::allocated_constant(cs, base);
    let boolean_false = Boolean::allocated_constant(cs, false);
    let one = UInt256::allocated_constant(cs, U256::one());

    // q <- 0
    let mut q = UInt512::zero(cs);

    // r <- first 7 limbs of n, thus it fits in UInt256
    let mut r = n.to_high();
    r.inner[0] = UInt32::zero(cs);
    r.inner.copy_within(1..U256_MAX_LIMBS, 0);
    r.inner[U256_MAX_LIMBS - 1] = UInt32::zero(cs);

    for i in 0..U256_MAX_LIMBS + 1 {
        // \alpha_{i+l-1} is (k-l-i)th limb of n
        let alpha = n.inner[U256_MAX_LIMBS - i];
        let alpha = convert_limb_to_u512(cs, &alpha);

        // d_i <- b*r_{i-1} + \alpha_{i+l-1}
        // d_i can safely be UInt512 in size.
        // r can have any number of limbs up to 8.
        // base is 2 limbs wide since b=(2^{32}-1)+1
        let d = base.widening_mul(cs, &mut r, 2, 8);
        let (d_plus_alpha, overflow) = d.overflowing_add(cs, &alpha);
        // d_i cannot overflow UInt512
        Boolean::enforce_equal(cs, &overflow, &boolean_false);
        let d = d_plus_alpha;

        // beta_i <- next digit of quotient. We use
        // binary search to find suitable beta_i
        let mut beta = UInt256::zero(cs);
        let mut left = UInt256::zero(cs);
        let mut right = base.clone();

        // Preparing new_r to further update r
        let mut new_r = UInt512::zero(cs);

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
            beta = UInt256::conditionally_select(cs, odd, &beta_div_2_plus_1, &beta_div_2);

            // r <- d - m * beta
            // beta can fit in 2 limbs since it is less or equal to b=2^{32}
            let m_beta = m.widening_mul(cs, &beta, 8, 2);
            let (r, r_negative) = d.overflowing_sub(cs, &m_beta);

            // if r < 0 (that is, overflow occurred), then right <- beta - 1
            // beta - 1 might overflow at step 33, but we don't care about it
            let (beta_minus_1, _) = beta.overflowing_sub(cs, &one);
            right = UInt256::conditionally_select(cs, r_negative, &beta_minus_1, &right);

            // if r >= m, then left <- beta + 1
            let r_geq_m = u512_geq_than_u256(cs, &r, m);
            // We should handle the case when r overflowed
            let r_positive = r_negative.negated(cs);
            let r_greater_m = r_geq_m.and(cs, r_positive);
            let (beta_plus_1, overflow) = beta.overflowing_add(cs, &one);
            // Cannot overflow since beta < b=2^{32}
            Boolean::enforce_equal(cs, &overflow, &boolean_false);
            left = UInt256::conditionally_select(cs, r_greater_m, &beta_plus_1, &left);

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
        let (_, overflow) = m.overflowing_sub(cs, &r);
        Boolean::enforce_equal(cs, &overflow, &boolean_false);

        // q_i <- b*q_{i-1} + beta_i
        let beta_u512 = convert_u256_to_u512(cs, &beta);
        q = q.must_mul_by_two_pow_32(cs);
        let (new_q, overflow) = q.overflowing_add(cs, &beta_u512);
        // Cannot overflow since quotient cannot exceed 2^{512}
        Boolean::enforce_equal(cs, &overflow, &boolean_false);
        q = new_q;
    }

    (q, r)
}

/// Finds the result of multiplying `a` by `b` modulo `modulus`.
pub fn modmul<F, CS>(
    cs: &mut CS,
    a: &UInt256<F>,
    b: &UInt256<F>,
    modulus: &UInt256<F>,
) -> UInt256<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    // We take 8 limbs since scalar can be of any size
    let ab = a.widening_mul(cs, &b, 8, 8);
    let (_, remainder) = long_division(cs, &ab, modulus);
    remainder
}

/// Finds the result of exponentiating `base` to the power of `exponent` modulo `modulus`.
/// Input parameters format is done according to EIP-198:
/// https://eips.ethereum.org/EIPS/eip-198.
///
/// Implementation is based on _Algorithm 1_ from the paper
/// https://cse.buffalo.edu/srds2009/escs2009_submission_Gopal.pdf
pub fn modexp<F, CS>(
    cs: &mut CS,
    base: &UInt256<F>,
    exponent: &UInt256<F>,
    modulus: &UInt256<F>,
) -> UInt256<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let mut a = UInt256::allocated_constant(cs, U256::one());
    let binary_expansion = exponent
        .to_le_bytes(cs)
        .into_iter()
        .map(|x| x.into_num().spread_into_bits::<CS, 8>(cs))
        .flatten()
        .collect::<Vec<_>>();

    println!("binary_expansion={:?}", binary_expansion.iter().map(|x| x.witness_hook(cs)().unwrap()).collect::<Vec<_>>());

    for e in binary_expansion.into_iter().rev() {
        println!("a={:?}, ei={:?}", a.witness_hook(cs)().unwrap(), e.witness_hook(cs)().unwrap());

        // a <- a^2 mod (modulus)
        let a_squared = modmul(cs, &a, &a, &modulus);

        // a <- a^2 * (base) mod (modulus)
        let a_base = modmul(cs, &a_squared, base, modulus);

        // If the i-th bit of the exponent is 1, then a <- a^2 * (base) mod (modulus)
        // Otherwise, we just set a <- a^2 mod (modulus)
        a = UInt256::conditionally_select(cs, e, &a_base, &a_squared);
    }

    a
}
