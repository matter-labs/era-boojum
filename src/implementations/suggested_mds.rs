use crate::field::goldilocks::GoldilocksField;
use crate::field::Field;
use unroll::unroll_for_loops;

// even though we do not use vectorization here, we will resort to additions
// instead of shifts to reduce register spills

// the matrix itself is a block-circulant of (2 * M_4, M_4, ...),
// with M_4 = [
//     [5, 7, 1, 3],
//     [4, 6, 1, 1],
//     [1, 3, 5, 7],
//     [1, 1, 4, 6],
// ]

// we will follow the multiplication procedure suggested in the Poseidon2 paper
// https://eprint.iacr.org/2023/323.pdf

#[unroll_for_loops]
#[inline(always)]
fn block_mul(
    x0: &mut GoldilocksField,
    x1: &mut GoldilocksField,
    x2: &mut GoldilocksField,
    x3: &mut GoldilocksField,
) {
    let mut t0 = *x0;
    t0.add_assign(&*x1);

    let mut t1 = *x2;
    t1.add_assign(&*x3);

    let mut t2 = *x1;
    t2.double().add_assign(&t1);

    let mut t3 = *x3;
    t3.double().add_assign(&t0);

    let mut t4 = t1;
    t4.double().double().add_assign(&t3);

    let mut t5 = t0;
    t5.double().double().add_assign(&t2);

    let mut t6 = t3;
    t6.add_assign(&t5);

    let mut t7 = t2;
    t7.add_assign(&t4);

    *x0 = t6;
    *x1 = t5;
    *x2 = t7;
    *x3 = t4;
}

#[unroll_for_loops]
#[inline(always)]
pub(crate) fn suggested_mds_mul(state: &mut [GoldilocksField; 12]) {
    let [mut x0, mut x1, mut x2, mut x3, mut x4, mut x5, mut x6, mut x7, mut x8, mut x9, mut x10, mut x11] =
        *state;

    // precompute subblock results

    block_mul(&mut x0, &mut x1, &mut x2, &mut x3);
    block_mul(&mut x4, &mut x5, &mut x6, &mut x7);
    block_mul(&mut x8, &mut x9, &mut x10, &mut x11);

    // we may wrap it back into array and unroll, later on

    state[0] = x0;
    state[0].double().add_assign(&x4).add_assign(&x8);
    state[1] = x1;
    state[1].double().add_assign(&x5).add_assign(&x9);
    state[2] = x2;
    state[2].double().add_assign(&x6).add_assign(&x10);
    state[3] = x3;
    state[3].double().add_assign(&x7).add_assign(&x11);

    state[4] = x4;
    state[4].double().add_assign(&x0).add_assign(&x8);
    state[5] = x5;
    state[5].double().add_assign(&x1).add_assign(&x9);
    state[6] = x6;
    state[6].double().add_assign(&x2).add_assign(&x10);
    state[7] = x7;
    state[7].double().add_assign(&x3).add_assign(&x11);

    state[8] = x8;
    state[8].double().add_assign(&x0).add_assign(&x4);
    state[9] = x9;
    state[9].double().add_assign(&x1).add_assign(&x5);
    state[10] = x10;
    state[10].double().add_assign(&x2).add_assign(&x6);
    state[11] = x11;
    state[11].double().add_assign(&x3).add_assign(&x7);
}

// for external benchmarks
#[inline(never)]
pub fn suggested_mds_mul_ext(state: &mut [GoldilocksField; 12]) {
    suggested_mds_mul(state);
}
