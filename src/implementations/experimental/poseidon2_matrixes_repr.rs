use crate::field::goldilocks::GoldilocksField;
use crate::field::traits::field::Field;
use crate::implementations::poseidon2::params::INNER_ROUNDS_MATRIX_DIAGONAL_ELEMENTS_MINUS_ONE_SHIFTS;
use unroll::unroll_for_loops;

// 64 bit fields usually have a problem with carry-chains, so we can check if doing a little more
// ops is beneficial, because we if field element is c = a + b * 2^32, then we can perform MDS multiplication
// (or any linear operation in general) as MDS(c) = MDS(a) + 2^32 * MDS(b)

#[inline(always)]
#[unroll_for_loops]
pub fn poseidon2_mds_split_mul(state: &mut [GoldilocksField; 12]) {
    let mut result = [GoldilocksField::ZERO; 12];

    let mut state_l = [0u64; 12];
    let mut state_h = [0u64; 12];

    for r in 0..12 {
        let s = state[r].to_nonreduced_u64();
        state_h[r] = s >> 32;
        state_l[r] = (s as u32) as u64;
    }

    poseidon2_suggested_mds_mul_u64(&mut state_h);
    poseidon2_suggested_mds_mul_u64(&mut state_l);

    for r in 0..12 {
        let s = state_l[r] as u128 + ((state_h[r] as u128) << 32);
        result[r] = GoldilocksField::from_u128_with_reduction(s);
    }
    *state = result;
}

// we assume that we never hit overflows here
#[inline(always)]
fn block_mul_u64(x0: &mut u64, x1: &mut u64, x2: &mut u64, x3: &mut u64) {
    let t0 = x0.wrapping_add(*x1);
    let t1 = x2.wrapping_add(*x3);

    let t2 = x1.wrapping_shl(1).wrapping_add(t1);
    let t3 = x3.wrapping_shl(1).wrapping_add(t0);

    let t4 = t1.wrapping_shl(2).wrapping_add(t3);
    let t5 = t0.wrapping_shl(2).wrapping_add(t2);

    let t6 = t3.wrapping_add(t5);
    let t7 = t2.wrapping_add(t4);

    *x0 = t6;
    *x1 = t5;
    *x2 = t7;
    *x3 = t4;
}

#[inline(always)]
#[unroll_for_loops]
pub(crate) fn poseidon2_suggested_mds_mul_u64(state: &mut [u64; 12]) {
    let [mut x0, mut x1, mut x2, mut x3, mut x4, mut x5, mut x6, mut x7, mut x8, mut x9, mut x10, mut x11] =
        *state;

    // percompute subblock results

    block_mul_u64(&mut x0, &mut x1, &mut x2, &mut x3);
    block_mul_u64(&mut x4, &mut x5, &mut x6, &mut x7);
    block_mul_u64(&mut x8, &mut x9, &mut x10, &mut x11);

    // we may wrap it back into array and unroll, later on

    let t = x4.wrapping_add(x8);
    state[0] = x0.wrapping_shl(1).wrapping_add(t);
    let t = x5.wrapping_add(x9);
    state[1] = x1.wrapping_shl(1).wrapping_add(t);
    let t = x6.wrapping_add(x10);
    state[2] = x2.wrapping_shl(1).wrapping_add(t);
    let t = x7.wrapping_add(x11);
    state[3] = x3.wrapping_shl(1).wrapping_add(t);

    let t = x0.wrapping_add(x8);
    state[4] = x4.wrapping_shl(1).wrapping_add(t);
    let t = x1.wrapping_add(x9);
    state[5] = x5.wrapping_shl(1).wrapping_add(t);
    let t = x2.wrapping_add(x10);
    state[6] = x6.wrapping_shl(1).wrapping_add(t);
    let t = x3.wrapping_add(x11);
    state[7] = x7.wrapping_shl(1).wrapping_add(t);

    let t = x0.wrapping_add(x4);
    state[8] = x8.wrapping_shl(1).wrapping_add(t);
    let t = x1.wrapping_add(x5);
    state[9] = x9.wrapping_shl(1).wrapping_add(t);
    let t = x2.wrapping_add(x6);
    state[10] = x10.wrapping_shl(1).wrapping_add(t);
    let t = x3.wrapping_add(x7);
    state[11] = x11.wrapping_shl(1).wrapping_add(t);
}

// for external benchmarks
#[inline(never)]
pub fn poseidon2_mds_split_mul_ext(state: &mut [GoldilocksField; 12]) {
    poseidon2_mds_split_mul(state);
}

#[inline(always)]
#[unroll_for_loops]
pub fn poseidon2_inner_split_mul(state: &mut [GoldilocksField; 12]) {
    let mut result = [GoldilocksField::ZERO; 12];

    let mut state_l = [0u64; 12];
    let mut state_h = [0u64; 12];

    for r in 0..12 {
        let s = state[r].to_nonreduced_u64();
        state_h[r] = s >> 32;
        state_l[r] = (s as u32) as u64;
    }

    poseidon2_inner_mul_u64(&mut state_h);
    poseidon2_inner_mul_u64(&mut state_l);

    for r in 0..12 {
        let s = state_l[r] as u128 + ((state_h[r] as u128) << 32);
        result[r] = GoldilocksField::from_u128_with_reduction(s);
    }
    *state = result;
}

#[inline(always)]
#[unroll_for_loops]
pub(crate) fn poseidon2_inner_mul_u64(state: &mut [u64; 12]) {
    let t0 = state[0].wrapping_add(state[1]);
    let t1 = state[2].wrapping_add(state[3]);
    let t2 = state[4].wrapping_add(state[5]);
    let t3 = state[6].wrapping_add(state[7]);
    let t4 = state[8].wrapping_add(state[9]);
    let t5 = state[10].wrapping_add(state[11]);

    let t0 = t0.wrapping_add(t1);
    let t1 = t2.wrapping_add(t3);
    let t2 = t3.wrapping_add(t4);

    let t0 = t0.wrapping_add(t5);
    let t1 = t1.wrapping_add(t2);

    let base = t0.wrapping_add(t1);

    for r in 0..12 {
        state[r] = state[r]
            .wrapping_shl(INNER_ROUNDS_MATRIX_DIAGONAL_ELEMENTS_MINUS_ONE_SHIFTS[r])
            .wrapping_add(base);
    }
}

#[inline(never)]
pub fn poseidon2_inner_split_mul_ext(state: &mut [GoldilocksField; 12]) {
    poseidon2_inner_split_mul(state);
}
