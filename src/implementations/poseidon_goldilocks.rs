//! An efficient poseidon implementation for this field depends the MDS matrix properties,
//! but we have to carefully consider three options for the case when an MDS matrix is a circular powers-of-two matrix
//! - use multiplications. In this case we can have an access to tricks described in the original Poseidon
//! paper, where for partial rounds we can perform special optimized matrix multiplication. But note that
//! on x86-64 `mul` operand has latency of 4 and throughput of 1, and on ARM it's latency of 6-7 to get high part.
//! On x86-64 one of the operands is implicit (RDX), so utilizing the throughput of 1 is hard
//! - use naive shifts. Those have a latency of 1 and shifting u64 into u128 is 2 separate ops (shl and shr by different offsets). In this case we
//! will be limited by the carry computation when we will absorb u128s
//! - use creative approach. In this case we can go from u64 representation into sparse representation, and do NOT
//! do carry propagation immediately. Our shifts are <= 16, so we can do something like an a-priori split of the
//! u64 into (u32, u32), then shift each of those with an extension into (u64, u64), do non-overlapping carry propagation,
//! and only at the very end normalize into u128 (or even smaller) and perform the final reduction into the field
//! As was found by MIR team, for the small goldilocks field a circulant matrix where the first row is
//! 2^n element for the exponents below is an MDS. As one can see shifts are small, so in fact an unreduced
//! row element will fit into 64 + 16 + 1 bits
use super::matrix_routines::{
    identity_matrix, matrix_inverse, row_add_assign, square_matrix_by_matrix_multiply,
    square_matrix_by_vector_multiply, square_matrix_transpose,
};

use derivative::*;
use unroll::unroll_for_loops;

use crate::field::{goldilocks::GoldilocksField, Field, SmallField, U64Representable};

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PoseidonGoldilocks;

pub const MDS_MATRIX_EXPS: [usize; 12] = [0, 0, 1, 0, 3, 5, 1, 8, 12, 3, 16, 10];

pub const MDS_MATRIX: [[GoldilocksField; 12]; 12] = const {
    let mut result = [[GoldilocksField::ZERO; 12]; 12];
    let mut row = 0;
    while row < 12 {
        let mut column = 0;
        while column < 12 {
            // so it's circular
            // e.g. result[1][0] = 1 << MDS_MATRIX_EXPS[11]
            // result[1][1] = 1 << MDS_MATRIX_EXPS[0]
            // result[1][11] = 1 << MDS_MATRIX_EXPS[10]
            result[row][column] = GoldilocksField::from_u64_with_reduction(
                1u64 << (MDS_MATRIX_EXPS[(12 - row + column) % 12]),
            );
            column += 1;
        }
        row += 1;
    }

    result
};

const MDS_MATRIX_INVERSE: [[GoldilocksField; 12]; 12] = matrix_inverse(&MDS_MATRIX);
const _: () = const {
    const EXPECTED_IDENTITY: [[GoldilocksField; 12]; 12] =
        square_matrix_by_matrix_multiply(&MDS_MATRIX, &MDS_MATRIX_INVERSE);
    const TRUE_IDENTITY: [[GoldilocksField; 12]; 12] = identity_matrix::<GoldilocksField, 12>();
    if matrix_const_equal(&EXPECTED_IDENTITY, &TRUE_IDENTITY) == false {
        panic!()
    } else {
    }
};

const MDS_MATRIX_MODIFIED_M_PRIME: [[GoldilocksField; 12]; 12] =
    compute_poseidon_matrix_decomposition(&MDS_MATRIX).0;
const MDS_MATRIX_MODIFIED_M_DOUBLE_PRIME: [[GoldilocksField; 12]; 12] =
    compute_poseidon_matrix_decomposition(&MDS_MATRIX).1;

// what we will want in the future is
// to have MDS not decomposed as M' * M'' as in the original paper,
// but more like K'' * K'
// It's easy to see that MDS_T = M''_T * M'_T,
// so let's name a matrix K = MDS_T, and so K_T = K''_T * K'_T = MDS

// Because we will need to compute such decompisitions and updates many times,
// We can just make a function for it once

pub(crate) const fn compute_poseidon_matrix_decomposition<F: SmallField, const N: usize>(
    matrix: &[[F; N]; N],
) -> ([[F; N]; N], [[F; N]; N]) {
    let input_transposed = square_matrix_transpose(&matrix);

    let m_prime = m_prime_form(&input_transposed);
    let m_double_prime = m_double_prime_form(&input_transposed);

    assert!(
        matrix_const_equal(
            &square_matrix_by_matrix_multiply(&m_prime, &m_double_prime),
            &input_transposed
        ) == true
    );

    // and we need to transpose once again

    let modified_m_prime = square_matrix_transpose(&m_prime);
    let modified_m_double_prime = square_matrix_transpose(&m_double_prime);

    assert!(
        matrix_const_equal(
            &square_matrix_by_matrix_multiply(&modified_m_double_prime, &modified_m_prime),
            matrix
        ) == true
    );

    (modified_m_prime, modified_m_double_prime)
}

const fn m_prime_form<F: SmallField, const N: usize>(input: &[[F; N]; N]) -> [[F; N]; N] {
    let mut result = *input;
    // clear M00
    result[0][0] = F::ONE;

    // clear top row
    let mut column = 0;
    while column < 11 {
        result[0][column + 1] = F::ZERO;
        column += 1;
    }

    // clear first column
    let mut row = 0;
    while row < 11 {
        result[row + 1][0] = F::ZERO;
        row += 1;
    }

    result
}

const fn m_double_prime_form<F: SmallField, const N: usize>(input: &[[F; N]; N]) -> [[F; N]; N] {
    let mut w = [F::ZERO; N];
    w[0] = F::ZERO;

    let mut row = 0;
    while row < 11 {
        w[row + 1] = input[row + 1][0];
        row += 1;
    }

    let m_prime = m_prime_form(&input);
    let m_prime_inversed = matrix_inverse(&m_prime);

    assert!(
        matrix_const_equal(
            &square_matrix_by_matrix_multiply(&m_prime, &m_prime_inversed),
            &identity_matrix()
        ) == true
    );

    let w_hat = square_matrix_by_vector_multiply(&m_prime_inversed, &w);

    let mut result = identity_matrix();
    result[0][0] = input[0][0];

    // copy top row
    let mut column = 0;
    while column < 11 {
        result[0][column + 1] = input[0][column + 1];
        column += 1;
    }

    // copy first column
    let mut row = 0;
    while row < 11 {
        result[row + 1][0] = w_hat[row + 1];
        row += 1;
    }

    result
}

const MAX_ROW_VALUE: u128 = const {
    let mut result = 0u128;
    let mut i = 0;
    while i < 12 {
        result += ((GoldilocksField::ORDER - 1) as u128) << MDS_MATRIX_EXPS[i];
        i += 1;
    }

    result
};

const MAX_ROW_VALUE_WITH_NEXT_ROUND_CONSTANT: u128 =
    MAX_ROW_VALUE + ((GoldilocksField::ORDER - 1) as u128);

const MAX_ROW_VALUE_BITS: u32 = MAX_ROW_VALUE.next_power_of_two().trailing_zeros();
const MAX_ROW_VALUE_WITH_NEXT_ROUND_CONSTANT_BITS: u32 = MAX_ROW_VALUE_WITH_NEXT_ROUND_CONSTANT
    .next_power_of_two()
    .trailing_zeros();
const _: () = if MAX_ROW_VALUE_BITS != 81 {
    panic!()
};
const _: () = if MAX_ROW_VALUE_WITH_NEXT_ROUND_CONSTANT_BITS != 81 {
    panic!()
};

// As we see we can very naively split any element into (u32, u32) tuple,
// and do lazy carry propagation

// We do not plan to implement it for other sizes, so we will use

#[inline(always)]
#[unroll_for_loops]
const fn mds_mul_naive(state: &mut [GoldilocksField; STATE_WIDTH]) {
    let mut result = [GoldilocksField::ZERO; STATE_WIDTH];
    // per element of the state
    for row in 0..12 {
        let mut acc = 0u128;
        // compiler will unroll it and try to do it's best to perform independent
        // additions and shifts, but we can do better in specialized implementation

        // per element of the matrix
        for column in 0..12 {
            // we have to use STATE_WIDTH - i to ensure that we are circulant,
            // and not anti-circulant
            acc = acc.wrapping_add(
                (state[column].as_u64() as u128)
                    << (MDS_MATRIX_EXPS[(column + STATE_WIDTH - row) % STATE_WIDTH]),
            )
        }

        result[row] = GoldilocksField::from_u128_with_reduction(acc);
    }

    *state = result;
}

// for external benchmarks
#[inline(never)]
pub const fn maive_mds_mul_ext(state: &mut [GoldilocksField; STATE_WIDTH]) {
    mds_mul_naive(state);
}

// for base field x^7 is a permutation
const _: () = if (GoldilocksField::CHAR - 1) % 7 == 0 {
    panic!()
};

#[inline(always)]
pub const fn apply_non_linearity(el: &mut GoldilocksField) {
    let mut t = *el; // 1
    el.square(); //2
    t.mul_assign(&*el); // 3
    el.square(); // 4
    el.mul_assign(&t);
}

#[inline(always)]
#[unroll_for_loops]
pub const fn apply_round_constants(state: &mut [GoldilocksField; STATE_WIDTH], round: usize) {
    for i in 0..12 {
        state[i].add_assign(&GoldilocksField::from_u64_unchecked(
            ALL_ROUND_CONSTANTS[round * STATE_WIDTH + i],
        ));
    }
}

#[inline(always)]
#[unroll_for_loops]
const fn full_round(state: &mut [GoldilocksField; STATE_WIDTH], round_counter: &mut usize) {
    // add constants
    apply_round_constants(state, *round_counter);
    // apply non-linearity
    for i in 0..12 {
        apply_non_linearity(&mut state[i]);
    }
    // multiply by MDS
    mds_mul_naive(state);

    *round_counter += 1;
}

#[inline(always)]
const fn partial_round(state: &mut [GoldilocksField; STATE_WIDTH], round_counter: &mut usize) {
    // add constants
    apply_round_constants(state, *round_counter);
    // apply non-linearity to the single element
    apply_non_linearity(&mut state[0]);
    // multiply by MDS
    mds_mul_naive(state);

    *round_counter += 1;
}

#[inline(always)]
pub const fn poseidon_permutation(state: &mut [GoldilocksField; STATE_WIDTH]) {
    poseidon_permutation_optimized(state);
}

#[unroll_for_loops]
pub const fn poseidon_permutation_naive(state: &mut [GoldilocksField; STATE_WIDTH]) {
    let mut round_counter = 0;
    for _i in 0..4 {
        full_round(state, &mut round_counter);
    }
    for _i in 0..22 {
        partial_round(state, &mut round_counter);
    }
    for _i in 0..4 {
        full_round(state, &mut round_counter);
    }
}

#[inline(always)]
#[unroll_for_loops]
const fn full_and_partial_round_fuzed_mul(state: &mut [GoldilocksField; STATE_WIDTH]) {
    let mut result = [GoldilocksField::ZERO; STATE_WIDTH];
    // per element of the state
    for row in 0..12 {
        let mut acc = (0u128, 0u32);
        // per element of the matrix
        for column in 0..12 {
            // we have to use STATE_WIDTH - i to ensure that we are circulant,
            // and not anti-circulant
            acc = GoldilocksField::accumulate_extended(
                acc,
                (state[column].as_u64() as u128)
                    * (FUZED_DENSE_MATRIX_LAST_FULL_AND_FIRST_PARTIAL[row][column].as_u64()
                        as u128),
            );
        }

        result[row] = GoldilocksField::reduce_from_extended_accumulator(acc);
    }

    *state = result;
}

#[inline(always)]
#[unroll_for_loops]
const fn partial_round_optimized(
    state: &mut [GoldilocksField; STATE_WIDTH],
    round_counter: &mut usize,
) {
    // apply non-linearity to the single element
    apply_non_linearity(&mut state[0]);
    // add round constant to first element
    state[0].add_assign(&ROUND_CONSTANTS_FOR_FUZED_SBOXES[*round_counter - HALF_NUM_FULL_ROUNDS]);

    // unrolled multiplication to matrix in M'' form
    let vs = &VS_FOR_PARTIAL_ROUNDS[*round_counter - HALF_NUM_FULL_ROUNDS];
    // NOTE: by the check in optimization routine below we know that M''[0][0] == 1 in our case,
    // so we just initialize accumulator with first element of the state
    let mut s0_acc = (state[0].as_u64() as u128, 0u32);
    for i in 0..11 {
        s0_acc = GoldilocksField::accumulate_extended(
            s0_acc,
            (vs[i].as_u64() as u128) * (state[i + 1].as_u64() as u128),
        );
    }
    let s0 = GoldilocksField::reduce_from_extended_accumulator(s0_acc);

    let original_s0 = state[0];
    state[0] = s0;

    let w_hats = &W_HATS_FOR_PARTIAL_ROUNDS[*round_counter - HALF_NUM_FULL_ROUNDS];
    // for the rest of the elements their form is state[0] * w_hat[i] + state[i]
    for i in 1..12 {
        state[i] = GoldilocksField::fma(original_s0, w_hats[i - 1], state[i]);
    }

    *round_counter += 1;
}

// for external benchmarks
#[inline(never)]
pub const fn partial_round_optimized_ext(state: &mut [GoldilocksField; STATE_WIDTH]) {
    let mut round_counter = HALF_NUM_FULL_ROUNDS;
    partial_round_optimized(state, &mut round_counter);
}

#[unroll_for_loops]
#[inline(always)]
pub const fn poseidon_permutation_optimized(state: &mut [GoldilocksField; STATE_WIDTH]) {
    let mut round_counter = 0;
    for _i in 0..3 {
        full_round(state, &mut round_counter);
    }
    // special fuzed full and partial

    // last full round - add round constants
    apply_round_constants(state, round_counter);

    // last full round - apply non-linearity
    for i in 0..12 {
        apply_non_linearity(&mut state[i]);
    }
    round_counter += 1;

    // merged part - round constants
    for i in 0..12 {
        state[i].add_assign(&ROUND_CONSTANTS_FUZED_LAST_FULL_AND_FIRST_PARTIAL[i]);
    }

    // merged part - multiply by dense matrix
    full_and_partial_round_fuzed_mul(state);

    // optimized partial rounds - consists of partial Sbox, add round constant to state[0],
    // and multiply by M'' like matrix
    for _i in 0..22 {
        partial_round_optimized(state, &mut round_counter);
    }

    // first full round doesn't need to add round constants
    // as those were propagated all the way up

    // apply non-linearity
    for i in 0..12 {
        apply_non_linearity(&mut state[i]);
    }
    // multiply by MDS
    mds_mul_naive(state);

    round_counter += 1;

    // unchanged other full rounds
    for _i in 0..3 {
        full_round(state, &mut round_counter);
    }
}

use crate::algebraic_props::round_function::{
    AbsorptionMode, AbsorptionModeTrait, AlgebraicRoundFunction, AlgebraicRoundFunctionWithParams,
};
use crate::implementations::matrix_routines::{array_const_equal, matrix_const_equal};

impl AlgebraicRoundFunctionWithParams<GoldilocksField, 8, 12, 4> for PoseidonGoldilocks {
    #[inline(always)]
    fn round_function(&self, state: &mut [GoldilocksField; 12]) {
        poseidon_permutation(state);
    }
    #[inline(always)]
    fn initial_state(&self) -> [GoldilocksField; 12] {
        [GoldilocksField::ZERO; STATE_WIDTH]
    }
    #[inline(always)]
    fn specialize_for_len(&self, len: u32, state: &mut [GoldilocksField; 12]) {
        // as described in the original Poseidon paper we use
        // the last element of the state
        state[11] = GoldilocksField::from_nonreduced_u64(len as u64);
    }
    #[unroll_for_loops]
    #[inline(always)]
    fn absorb_into_state(
        &self,
        state: &mut [GoldilocksField; 12],
        to_absorb: &[GoldilocksField; 8],
        mode: AbsorptionMode,
    ) {
        match mode {
            AbsorptionMode::Overwrite => {
                let mut i = 0;
                while i < 8 {
                    state[i] = to_absorb[i];
                    i += 1;
                }
            }
            AbsorptionMode::Addition => {
                let mut i = 0;
                while i < 8 {
                    state[i].add_assign(&to_absorb[i]);
                    i += 1;
                }
            }
        }
    }

    #[inline(always)]
    fn state_get_commitment<'a>(&self, state: &'a [GoldilocksField; 12]) -> &'a [GoldilocksField] {
        &state[0..4]
    }

    #[inline(always)]
    fn state_into_commitment_fixed<const N: usize>(
        &self,
        state: &[GoldilocksField; 12],
    ) -> [GoldilocksField; N] {
        debug_assert!(N <= 8);
        let mut result = [GoldilocksField::ZERO; N];
        result.copy_from_slice(&state[..N]);

        result
    }
}

impl AlgebraicRoundFunction<GoldilocksField, 8, 12, 4> for PoseidonGoldilocks {
    #[inline(always)]
    fn round_function(state: &mut [GoldilocksField; 12]) {
        poseidon_permutation(state);
    }
    #[inline(always)]
    fn initial_state() -> [GoldilocksField; 12] {
        [GoldilocksField::ZERO; STATE_WIDTH]
    }
    #[inline(always)]
    fn specialize_for_len(len: u32, state: &mut [GoldilocksField; 12]) {
        // as described in the original Poseidon paper we use
        // the last element of the state
        state[11] = GoldilocksField::from_nonreduced_u64(len as u64);
    }
    #[inline(always)]
    #[unroll_for_loops]
    fn absorb_into_state<M: AbsorptionModeTrait<GoldilocksField>>(
        state: &mut [GoldilocksField; 12],
        to_absorb: &[GoldilocksField; 8],
    ) {
        for i in 0..8 {
            M::absorb(&mut state[i], &to_absorb[i]);
        }
    }

    #[inline(always)]
    fn state_into_commitment<const N: usize>(
        state: &[GoldilocksField; 12],
    ) -> [GoldilocksField; N] {
        debug_assert!(N <= 8);
        let mut result = [GoldilocksField::ZERO; N];
        result.copy_from_slice(&state[..N]);

        result
    }
}

// optimized case: as described in https://eprint.iacr.org/2019/458.pdf we can do some manipulations
// to speedup computations of partial rounds

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash)]
enum Operation<F: SmallField, const N: usize> {
    Nop,
    AddRoundConstants([F; N]),
    FullSBox,
    MulByMDS,
    MulByMDSInPartialRound,
    PartialSBox,
    MulByMPrimeModified,
    MulByMDoublePrimeModified,
    SBoxAndRoundConstantForEl0(F),
    MulByExplicitMPrimeForm([[F; N]; N]),
    MulByExplicitMDoublePrimeForm([[F; N]; N]),
}

impl<F: SmallField, const N: usize> const PartialEq<Self> for Operation<F, N> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::MulByExplicitMPrimeForm(a), Self::MulByExplicitMPrimeForm(b))
            | (Self::MulByExplicitMDoublePrimeForm(a), Self::MulByExplicitMDoublePrimeForm(b)) => {
                matrix_const_equal(a, b)
            }
            (Self::AddRoundConstants(a), Self::AddRoundConstants(b)) => array_const_equal(a, b),
            (Self::Nop, Self::Nop)
            | (Self::FullSBox, Self::FullSBox)
            | (Self::PartialSBox, Self::PartialSBox)
            | (Self::MulByMPrimeModified, Self::MulByMPrimeModified)
            | (Self::MulByMDSInPartialRound, Self::MulByMDSInPartialRound)
            | (Self::MulByMDoublePrimeModified, Self::MulByMDoublePrimeModified)
            | (Self::MulByMDS, Self::MulByMDS) => true,
            (Self::SBoxAndRoundConstantForEl0(a), Self::SBoxAndRoundConstantForEl0(b)) => *a == *b,
            _ => false,
        }
    }
}

impl<F: SmallField, const N: usize> Eq for Operation<F, N> {}

impl Operation<GoldilocksField, 12> {
    #[allow(dead_code)]
    const fn apply_over_state(&self, state: &mut [GoldilocksField; 12]) {
        match self {
            Self::Nop => {}
            Self::AddRoundConstants(constants) => row_add_assign(state, constants),
            Self::FullSBox => {
                let mut idx = 0;
                while idx < 12 {
                    apply_non_linearity(&mut state[idx]);
                    idx += 1
                }
            }
            Self::MulByMDS => {
                *state = square_matrix_by_vector_multiply(&MDS_MATRIX, &*state);
            }
            Self::PartialSBox => {
                apply_non_linearity(&mut state[0]);
            }
            Self::MulByMPrimeModified => {
                // happens in unoptimized case
                *state = square_matrix_by_vector_multiply(&MDS_MATRIX_MODIFIED_M_PRIME, &*state);
            }
            Self::MulByMDoublePrimeModified => {
                *state =
                    square_matrix_by_vector_multiply(&MDS_MATRIX_MODIFIED_M_DOUBLE_PRIME, &*state);
            }
            Self::SBoxAndRoundConstantForEl0(c) => {
                apply_non_linearity(&mut state[0]);
                state[0].add_assign(c);
            }
            Self::MulByExplicitMPrimeForm(matrix) => {
                *state = square_matrix_by_vector_multiply(matrix, &*state);
            }
            Self::MulByExplicitMDoublePrimeForm(matrix) => {
                *state = square_matrix_by_vector_multiply(matrix, &*state);
            }
            Self::MulByMDSInPartialRound => {
                *state = square_matrix_by_vector_multiply(&MDS_MATRIX, &*state);
            }
        }
    }
}

const fn array_u64_to_field<F: SmallField, const N: usize>(input: [u64; N]) -> [F; N] {
    let mut result = [F::ZERO; N];
    let mut idx = 0;
    while idx < N {
        result[idx] = F::from_u64_with_reduction(input[idx]);
        idx += 1;
    }

    result
}

const NUM_OPS_IN_DEFINITION: usize = 3 * NUM_FULL_ROUNDS_TOTAL + (NUM_PARTIAL_ROUNDS - 1) * 3 + 4;

const DEFAULT_ROUNDS_STRUCTURE: [Operation<GoldilocksField, 12>; NUM_OPS_IN_DEFINITION] = const {
    let mut result: [Operation<GoldilocksField, 12>; NUM_OPS_IN_DEFINITION] =
        [Operation::Nop; NUM_OPS_IN_DEFINITION];
    let mut idx = 0;
    while idx < HALF_NUM_FULL_ROUNDS {
        result[idx * 3 + 0] = Operation::AddRoundConstants(array_u64_to_field(
            ROUND_CONSTANTS_ALIGNED_PER_ROUND[idx],
        ));
        result[idx * 3 + 1] = Operation::FullSBox;
        result[idx * 3 + 2] = Operation::MulByMDS;
        idx += 1;
    }

    let mut idx = 0;
    while idx < NUM_PARTIAL_ROUNDS - 1 {
        result[HALF_NUM_FULL_ROUNDS * 3 + idx * 3 + 0] = Operation::AddRoundConstants(
            array_u64_to_field(ROUND_CONSTANTS_ALIGNED_PER_ROUND[HALF_NUM_FULL_ROUNDS + idx]),
        );
        result[HALF_NUM_FULL_ROUNDS * 3 + idx * 3 + 1] = Operation::PartialSBox;
        result[HALF_NUM_FULL_ROUNDS * 3 + idx * 3 + 2] = Operation::MulByMDSInPartialRound;

        idx += 1;
    }

    result[HALF_NUM_FULL_ROUNDS * 3 + (NUM_PARTIAL_ROUNDS - 1) * 3 + 0] =
        Operation::AddRoundConstants(array_u64_to_field(
            ROUND_CONSTANTS_ALIGNED_PER_ROUND[HALF_NUM_FULL_ROUNDS + idx],
        ));
    result[HALF_NUM_FULL_ROUNDS * 3 + (NUM_PARTIAL_ROUNDS - 1) * 3 + 1] = Operation::PartialSBox;
    result[HALF_NUM_FULL_ROUNDS * 3 + (NUM_PARTIAL_ROUNDS - 1) * 3 + 2] =
        Operation::MulByMPrimeModified;
    result[HALF_NUM_FULL_ROUNDS * 3 + (NUM_PARTIAL_ROUNDS - 1) * 3 + 3] =
        Operation::MulByMDoublePrimeModified;

    let mut idx = 0;
    while idx < HALF_NUM_FULL_ROUNDS {
        result[HALF_NUM_FULL_ROUNDS * 3 + (NUM_PARTIAL_ROUNDS - 1) * 3 + 4 + idx * 3 + 0] =
            Operation::AddRoundConstants(array_u64_to_field(
                ROUND_CONSTANTS_ALIGNED_PER_ROUND[HALF_NUM_FULL_ROUNDS + NUM_PARTIAL_ROUNDS + idx],
            ));
        result[HALF_NUM_FULL_ROUNDS * 3 + (NUM_PARTIAL_ROUNDS - 1) * 3 + 4 + idx * 3 + 1] =
            Operation::FullSBox;
        result[HALF_NUM_FULL_ROUNDS * 3 + (NUM_PARTIAL_ROUNDS - 1) * 3 + 4 + idx * 3 + 2] =
            Operation::MulByMDS;
        idx += 1;
    }

    let mut idx = 0;
    while idx < NUM_OPS_IN_DEFINITION {
        assert!(result[idx] != Operation::Nop);

        idx += 1;
    }

    result
};

const fn apply_optimization_deterministic_propagate_round_constants<const N: usize>(
    initial_sequence: [Operation<GoldilocksField, 12>; N],
) -> [Operation<GoldilocksField, 12>; N] {
    let mut structure = initial_sequence;

    // carry round constants

    // once to swap one last partial round
    {
        let mut new_structure = structure;
        let mut idx = N - 1;
        while idx > 1 {
            let c = new_structure[idx];
            let b = new_structure[idx - 1];
            let a = new_structure[idx - 2];

            match (c, b, a) {
                (
                    Operation::AddRoundConstants(constants),
                    Operation::MulByMDoublePrimeModified,
                    Operation::MulByMPrimeModified,
                ) => {
                    let new_constants =
                        square_matrix_by_vector_multiply(&MDS_MATRIX_INVERSE, &constants);
                    new_structure[idx] = b;
                    new_structure[idx - 1] = a;
                    new_structure[idx - 2] = Operation::AddRoundConstants(new_constants);
                }
                _ => {}
            }

            idx -= 1;
        }

        structure = new_structure
    }

    // loop to propagate all other
    loop {
        let mut new_structure = structure;

        let mut idx = N - 1;
        while idx > 0 {
            let b = new_structure[idx];
            let a = new_structure[idx - 1];

            match (a, b) {
                (Operation::PartialSBox, Operation::AddRoundConstants(constants)) => {
                    let mut new_constants = constants;
                    new_constants[0] = GoldilocksField::ZERO;

                    new_structure[idx] = Operation::SBoxAndRoundConstantForEl0(constants[0]);
                    new_structure[idx - 1] = Operation::AddRoundConstants(new_constants);
                }
                (
                    Operation::SBoxAndRoundConstantForEl0(existing_constant),
                    Operation::AddRoundConstants(constants),
                ) => {
                    let mut new_constants = constants;
                    new_constants[0] = GoldilocksField::ZERO;

                    let mut new_sbox_constant = existing_constant;
                    new_sbox_constant.add_assign(&constants[0]);

                    new_structure[idx] = Operation::SBoxAndRoundConstantForEl0(new_sbox_constant);
                    new_structure[idx - 1] = Operation::AddRoundConstants(new_constants);
                }
                (Operation::AddRoundConstants(a), Operation::AddRoundConstants(b)) => {
                    let mut new_constants = a;
                    row_add_assign(&mut new_constants, &b);

                    new_structure[idx] = Operation::AddRoundConstants(new_constants);
                    new_structure[idx - 1] = Operation::Nop;
                }
                (Operation::MulByMDSInPartialRound, Operation::AddRoundConstants(constants)) => {
                    let new_constants =
                        square_matrix_by_vector_multiply(&MDS_MATRIX_INVERSE, &constants);

                    new_structure[idx] = Operation::MulByMDSInPartialRound;
                    new_structure[idx - 1] = Operation::AddRoundConstants(new_constants);
                }
                // and get rid of NOPs
                (a, Operation::Nop) => {
                    new_structure[idx] = a;
                    new_structure[idx - 1] = Operation::Nop;
                }
                _ => {}
            }

            idx -= 1;
        }

        if array_const_equal(&structure, &new_structure) != true {
            structure = new_structure;
        } else {
            break;
        }
    }

    structure
}

const fn apply_optimization_deterministic_compute_equivalent_matrixes<const N: usize>(
    initial_sequence: [Operation<GoldilocksField, 12>; N],
) -> [Operation<GoldilocksField, 12>; N] {
    let mut structure = initial_sequence;
    // compute equivalent matrixes

    // carry multiplication my M', single loop because we propagate from the end to the start

    {
        let mut new_structure = structure;

        let mut idx = N - 1;
        while idx > 0 {
            let b = new_structure[idx];
            let a = new_structure[idx - 1];

            let (new_a, new_b) = match (a, b) {
                (
                    a @ Operation::SBoxAndRoundConstantForEl0(..),
                    b @ Operation::MulByMPrimeModified,
                ) => (b, a),
                (
                    a @ Operation::SBoxAndRoundConstantForEl0(..),
                    b @ Operation::MulByExplicitMPrimeForm(..),
                ) => (b, a),
                (Operation::MulByMDSInPartialRound, Operation::MulByMPrimeModified) => {
                    let equivalent_matrix =
                        square_matrix_by_matrix_multiply(&MDS_MATRIX_MODIFIED_M_PRIME, &MDS_MATRIX);
                    let (new_m_prime, new_m_double_prime) =
                        compute_poseidon_matrix_decomposition(&equivalent_matrix);
                    (
                        Operation::MulByExplicitMPrimeForm(new_m_prime),
                        Operation::MulByExplicitMDoublePrimeForm(new_m_double_prime),
                    )
                }
                (
                    Operation::MulByMDSInPartialRound,
                    Operation::MulByExplicitMPrimeForm(m_prime),
                ) => {
                    let equivalent_matrix = square_matrix_by_matrix_multiply(&m_prime, &MDS_MATRIX);
                    let (new_m_prime, new_m_double_prime) =
                        compute_poseidon_matrix_decomposition(&equivalent_matrix);
                    (
                        Operation::MulByExplicitMPrimeForm(new_m_prime),
                        Operation::MulByExplicitMDoublePrimeForm(new_m_double_prime),
                    )
                }
                (a, b) => (a, b),
            };

            new_structure[idx] = new_b;
            new_structure[idx - 1] = new_a;

            idx -= 1;
        }

        structure = new_structure;
    }

    structure
}

const CARRIED_ROUNDS_STRUCTURE_PROPED_CONSTANTS: [Operation<GoldilocksField, 12>;
    NUM_OPS_IN_DEFINITION] =
    apply_optimization_deterministic_propagate_round_constants(DEFAULT_ROUNDS_STRUCTURE);

const NUM_NOPS_TO_IGNORE: usize = const {
    let mut num_nops = 0;

    let mut idx = 0;
    while idx < NUM_OPS_IN_DEFINITION {
        if CARRIED_ROUNDS_STRUCTURE_PROPED_CONSTANTS[idx] == Operation::Nop {
            num_nops += 1;
        } else {
            break;
        }
        idx += 1;
    }

    num_nops
};

const CLEANED_DEFINITION: [Operation<GoldilocksField, 12>;
    NUM_OPS_IN_DEFINITION - NUM_NOPS_TO_IGNORE] = const {
    let mut result = [Operation::Nop; NUM_OPS_IN_DEFINITION - NUM_NOPS_TO_IGNORE];
    let mut idx = 0;
    while idx < NUM_OPS_IN_DEFINITION - NUM_NOPS_TO_IGNORE {
        result[idx] = CARRIED_ROUNDS_STRUCTURE_PROPED_CONSTANTS[NUM_NOPS_TO_IGNORE + idx];
        idx += 1;
    }

    result
};

const OPTIMIZED_ROUNDS_STRUCTURE: [Operation<GoldilocksField, 12>;
    NUM_OPS_IN_DEFINITION - NUM_NOPS_TO_IGNORE] =
    apply_optimization_deterministic_compute_equivalent_matrixes(CLEANED_DEFINITION);

// we need:
// round constants for a first partial round
// dense matrix for first partial round (merged with last matrix from full round)
// round constants for each partial round for fuzed sbox
// M'' matrix forms: "v" row and "w_hat" columns
const fn produce_optimied_params(
    optimized_structure: [Operation<GoldilocksField, 12>;
        NUM_OPS_IN_DEFINITION - NUM_NOPS_TO_IGNORE],
) -> (
    [GoldilocksField; 12],                       // updated first round constants
    [[GoldilocksField; 12]; 12],                 // dense matrix for the first full round
    [GoldilocksField; NUM_PARTIAL_ROUNDS], // round constants for partial rounds where element is under S-box
    [[GoldilocksField; 11]; NUM_PARTIAL_ROUNDS], // `v` row
    [[GoldilocksField; 11]; NUM_PARTIAL_ROUNDS], // `w_hat` column
) {
    let mut vs = [[GoldilocksField::ZERO; 11]; NUM_PARTIAL_ROUNDS];
    let mut w_hats = [[GoldilocksField::ZERO; 11]; NUM_PARTIAL_ROUNDS];
    let mut round_constants_fuzed_with_sbox = [GoldilocksField::ZERO; NUM_PARTIAL_ROUNDS];

    let mut idx = 0;
    idx += HALF_NUM_FULL_ROUNDS * 3;

    idx -= 1; // we capture MDS multiplication from the end of full round

    assert!(matches!(optimized_structure[idx], Operation::MulByMDS));
    idx += 1;

    let expected_round_constants = optimized_structure[idx];
    let first_partial_round_constants =
        if let Operation::AddRoundConstants(c) = expected_round_constants {
            c
        } else {
            unreachable!()
        };
    // propagate
    let updated_first_partial_round_constants =
        square_matrix_by_vector_multiply(&MDS_MATRIX_INVERSE, &first_partial_round_constants);
    assert!(array_const_equal(
        &square_matrix_by_vector_multiply(&MDS_MATRIX, &updated_first_partial_round_constants),
        &first_partial_round_constants,
    ));
    idx += 1;
    let expected_m_prime_form = optimized_structure[idx];
    let m_prime_form_first_found =
        if let Operation::MulByExplicitMPrimeForm(c) = expected_m_prime_form {
            c
        } else {
            unreachable!()
        };
    idx += 1;

    let dense_matrix_first_partial_round =
        square_matrix_by_matrix_multiply(&m_prime_form_first_found, &MDS_MATRIX);

    let mut round = 0;
    while round < NUM_PARTIAL_ROUNDS {
        let expected_partial_s_box = optimized_structure[idx];
        let partial_s_box_constant =
            if let Operation::SBoxAndRoundConstantForEl0(c) = expected_partial_s_box {
                c
            } else {
                unreachable!()
            };
        idx += 1;
        round_constants_fuzed_with_sbox[round] = partial_s_box_constant;

        let expected_m_double_prime = optimized_structure[idx];
        let m_double_prime_matrix =
            if let Operation::MulByExplicitMDoublePrimeForm(c) = expected_m_double_prime {
                c
            } else {
                if let Operation::MulByMDoublePrimeModified = expected_m_double_prime {
                    MDS_MATRIX_MODIFIED_M_DOUBLE_PRIME
                } else {
                    unreachable!()
                }
            };

        // check that it's still 1s on diagonal
        let mut j = 0;
        while j < 12 {
            assert!(m_double_prime_matrix[j][j] == GoldilocksField::ONE);
            j += 1;
        }

        // copy non-trivial row and column
        let mut column = 0;
        while column < 11 {
            vs[round][column] = m_double_prime_matrix[0][column + 1];
            column += 1;
        }

        let mut row = 0;
        while row < 11 {
            w_hats[round][row] = m_double_prime_matrix[row + 1][0];
            row += 1;
        }
        idx += 1;

        round += 1;
    }

    let expected_full_sbox = optimized_structure[idx];
    assert!(matches!(expected_full_sbox, Operation::FullSBox));

    (
        updated_first_partial_round_constants,
        dense_matrix_first_partial_round,
        round_constants_fuzed_with_sbox,
        vs,
        w_hats,
    )
}

pub const ROUND_CONSTANTS_FUZED_LAST_FULL_AND_FIRST_PARTIAL: [GoldilocksField; 12] =
    produce_optimied_params(OPTIMIZED_ROUNDS_STRUCTURE).0;
pub const FUZED_DENSE_MATRIX_LAST_FULL_AND_FIRST_PARTIAL: [[GoldilocksField; 12]; 12] =
    produce_optimied_params(OPTIMIZED_ROUNDS_STRUCTURE).1;
pub const ROUND_CONSTANTS_FOR_FUZED_SBOXES: [GoldilocksField; NUM_PARTIAL_ROUNDS] =
    produce_optimied_params(OPTIMIZED_ROUNDS_STRUCTURE).2;
pub const VS_FOR_PARTIAL_ROUNDS: [[GoldilocksField; 11]; NUM_PARTIAL_ROUNDS] =
    produce_optimied_params(OPTIMIZED_ROUNDS_STRUCTURE).3;
pub const W_HATS_FOR_PARTIAL_ROUNDS: [[GoldilocksField; 11]; NUM_PARTIAL_ROUNDS] =
    produce_optimied_params(OPTIMIZED_ROUNDS_STRUCTURE).4;

pub const VS_FOR_PARTIAL_ROUNDS_EXTENDED: [[GoldilocksField; 12]; NUM_PARTIAL_ROUNDS] = const {
    let mut result = [[GoldilocksField::ONE; 12]; NUM_PARTIAL_ROUNDS];
    let mut round = 0;
    while round < NUM_PARTIAL_ROUNDS {
        let mut idx = 0;
        while idx < 11 {
            result[round][1 + idx] = VS_FOR_PARTIAL_ROUNDS[round][idx];
            idx += 1;
        }
        round += 1;
    }

    result
};

pub const W_HATS_FOR_PARTIAL_ROUNDS_EXTENDED: [[GoldilocksField; 12]; NUM_PARTIAL_ROUNDS] = const {
    let mut result = [[GoldilocksField::ONE; 12]; NUM_PARTIAL_ROUNDS];
    let mut round = 0;
    while round < NUM_PARTIAL_ROUNDS {
        let mut idx = 0;
        while idx < 11 {
            result[round][1 + idx] = W_HATS_FOR_PARTIAL_ROUNDS[round][idx];
            idx += 1;
        }
        round += 1;
    }

    result
};

#[test]
fn test_valid_transformation() {
    let mut state = [GoldilocksField::ONE; 12];

    for el in DEFAULT_ROUNDS_STRUCTURE.iter() {
        el.apply_over_state(&mut state);
    }

    let mut state_2 = [GoldilocksField::ONE; 12];

    for el in OPTIMIZED_ROUNDS_STRUCTURE.iter() {
        el.apply_over_state(&mut state_2);
    }

    assert_eq!(state, state_2);
}

#[test]
fn test_show_optimal_sequence() {
    // dbg!(&FUZED_DENSE_MATRIX_LAST_FULL_AND_FIRST_PARTIAL);

    dbg!(OPTIMIZED_ROUNDS_STRUCTURE);
}

#[test]
fn test_show_vs_and_whats() {
    dbg!(&VS_FOR_PARTIAL_ROUNDS);
    dbg!(&W_HATS_FOR_PARTIAL_ROUNDS);
}

#[test]
fn test_valid_implementation() {
    let builder = std::thread::Builder::new().stack_size(80 * 1024 * 1024);
    let handler = builder
        .spawn(|| {
            let mut state = [GoldilocksField::ONE; 12];
            poseidon_permutation_naive(&mut state);

            let mut state_2 = [GoldilocksField::ONE; 12];
            poseidon_permutation_optimized(&mut state_2);

            assert_eq!(state, state_2);
        })
        .unwrap();

    handler.join().unwrap();
}
