use ethereum_types::U256;

use crate::{cs::traits::cs::ConstraintSystem, field::SmallField};

use super::{u256::UInt256, u512::UInt512, u8::UInt8};

const MAX_BITS: usize = 256;

/// Computes the result of multiplying `a` and `b` modulo `modulus`.
fn mulmod<F, CS>(
    a: &UInt256<F>,
    b: &UInt256<F>,
    modulus: &UInt256<F>,
) -> U256<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>
{
    int fp256_mod_mul(fp256 *r, const fp256 *a, const fp256 *b, const fp256 *m)
{
    size_t rl, reml;
    u64 rd[8];
    u64 remd[4];

    ll_set_zero(rd, 8);

    /* rd = a->d * b->d */
    ll_u256_mul(rd, a->d, b->d);
    rl = ll_num_limbs(rd, 8);

    /* remd = rd mod md */
    if (ll_div(remd, NULL, &reml, NULL, rd, m->d, rl, m->nlimbs) != FP256_OK)
        return FP256_ERR;

    fp256_set_limbs(r, remd, reml);

    return FP256_OK;
}
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
    CS: ConstraintSystem<F>
{
    // Defining one in U256
    let one = U256::from_str_radix("0x0", 16).unwrap();
    
    // Converting exponent in U256 to U512
    let exponent_libms = exponent.to_le_bytes(cs);
    // Concatenate exponent_libms and zero into a single array of size 64
    let mut exponent_bytes = [UInt8::zero(cs); 64];
    exponent_bytes[0..32].copy_from_slice(&exponent_libms);
    let exponent_u512 = UInt512::from_le_bytes(cs, exponent_bytes);

    // Main Algorithm flow
    let a = UInt256::allocated_constant(cs, one);
    for i in (0..MAX_BITS).into_iter().rev() {
        // Calculating a <- a^2 mod e
        // Since a can be of any size, we take 8 libms for both self_libms and other_libms
        let a_square = a.widening_mul(cs, &a, 8, 8);
        
        // If a exceeds e, we subtract e from a
        let (a_sub_e, a_out_of_range) = a_square.overflowing_sub(cs, &exponent_u512);
        
        let k1 = <BN256ScalarNNField<F> as NonNativeField<F, BN256Fr>>::conditionally_select(
            cs,
            k1_out_of_range,
            &k1,
            &k1_negated,
        );
    }
    
    a
}