use ethereum_types::U256;

use crate::{cs::traits::cs::ConstraintSystem, field::SmallField};

use super::{
    boolean::Boolean, tables::ByteSplitTable, traits::selectable::Selectable, u256::UInt256, u512::UInt512, u8::UInt8
};

const U256_MAX_BITS: usize = 256;
const U512_MAX_BITS: usize = 512;

/// Finds n % d using the standard long division with no fancy optimizations.
pub fn naive_modulo<F, CS>(cs: &mut CS, n: &UInt512<F>, d: &UInt256<F>) -> UInt256<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    // Defining constants
    let mut n = n.clone();
    let mut q = UInt512::zero(cs);
    let mut r = UInt256::zero(cs);
    let boolean_false = Boolean::allocated_constant(cs, false);

    // Align the most-significant ones
    let d_le_bytes = d.to_le_bytes(cs);
    // Extend the modulus to 512 bits
    let mut d_bytes = [UInt8::zero(cs); 64];
    d_bytes[..32].copy_from_slice(&d_le_bytes);
    let mut d = UInt512::from_le_bytes(cs, d_bytes);

    // Getting the byte split table
    let byte_split_id = cs
        .get_table_id_for_marker::<ByteSplitTable<1>>()
        .expect("table should exist");

    for i in (0..U512_MAX_BITS).into_iter().rev() {
        // r <- 2*r (left-shift by 1 bit)
        let (r_doubled, overflow)= r.overflowing_add(cs, &r);
        Boolean::enforce_equal(cs, &boolean_false, &overflow);
        r = r_doubled;

        // Set the least-significant bit of R equal to bit i of the numerator
        // let bits = r.into_num().spread_into_bits::<CS, 32>(cs)[0];
    }

    r
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
    let one = U256::from_str_radix("0x1", 16).unwrap();
    let mut a = UInt256::allocated_constant(cs, one);
    let mut exponent = exponent.clone();

    for i in 0..U256_MAX_BITS {
        // We take 8 limbs since scalar can be of any size
        // a <- a^2 mod (modulus)
        let a_squared = a.widening_mul(cs, &a, 8, 8);
        let a_squared = naive_modulo(cs, &a_squared, modulus);

        // a <- a^2 * (base) mod (modulus)
        let a_base = a_squared.widening_mul(cs, base, 8, 8);
        let a_base = naive_modulo(cs, &a_base, modulus);

        // If the i-th bit of the exponent is 1, then a <- a^2 * (base) mod (modulus)
        // Otherwise, we just set a <- a^2 mod (modulus)
        let is_odd = exponent.is_odd(cs);
        a = UInt256::conditionally_select(cs, is_odd, &a_base, &a_squared);
        exponent = exponent.div2(cs);
    }

    a
}
