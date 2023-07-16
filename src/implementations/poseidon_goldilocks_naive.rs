use super::poseidon_goldilocks_params::*;
use derivative::*;
use unroll::unroll_for_loops;

use crate::field::{goldilocks::GoldilocksField, Field, SmallField};

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
            result[row][column] = GoldilocksField::from_nonreduced_u64(
                1u64 << (MDS_MATRIX_EXPS[(12 - row + column) % 12]),
            );
            column += 1;
        }
        row += 1;
    }

    result
};

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
                (state[column].to_nonreduced_u64() as u128)
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
    el.square_impl(); //2
    t.mul_assign_impl(&*el); // 3
    el.square_impl(); // 4
    el.mul_assign_impl(&t);
}

#[inline(always)]
#[unroll_for_loops]
pub const fn apply_round_constants(state: &mut [GoldilocksField; STATE_WIDTH], round: usize) {
    for i in 0..12 {
        state[i].add_assign_impl(&GoldilocksField(
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
pub fn poseidon_permutation(state: &mut [GoldilocksField; STATE_WIDTH]) {
    poseidon_permutation_naive(state);
}

//#[unroll_for_loops]
pub fn poseidon_permutation_naive(state: &mut [GoldilocksField; STATE_WIDTH]) {
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

use crate::algebraic_props::round_function::{
    AbsorptionMode, AbsorptionModeTrait, AlgebraicRoundFunction, AlgebraicRoundFunctionWithParams,
};

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
