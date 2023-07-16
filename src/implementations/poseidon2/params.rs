//! A set of matrix parameters used for poseidon2.
use super::*;
use crate::field::traits::field::*;
use crate::implementations::poseidon_goldilocks_params::{
    self, HALF_NUM_FULL_ROUNDS, NUM_FULL_ROUNDS_TOTAL, NUM_PARTIAL_ROUNDS,
};

pub const EXTERNAL_MDS_MATRIX_BLOCK: [[GoldilocksField; 4]; 4] = [
    [
        GoldilocksField(5),
        GoldilocksField(7),
        GoldilocksField(1),
        GoldilocksField(3),
    ],
    [
        GoldilocksField(4),
        GoldilocksField(6),
        GoldilocksField(1),
        GoldilocksField(1),
    ],
    [
        GoldilocksField(1),
        GoldilocksField(3),
        GoldilocksField(5),
        GoldilocksField(7),
    ],
    [
        GoldilocksField(1),
        GoldilocksField(1),
        GoldilocksField(4),
        GoldilocksField(6),
    ],
];

pub const INNER_ROUNDS_MATRIX_DIAGONAL_ELEMENTS_MINUS_ONE_SHIFTS: [u32; 12] =
    [4, 14, 11, 8, 0, 5, 2, 9, 13, 6, 3, 12];

pub const INNER_ROUNDS_MATRIX_DIAGONAL_ELEMENTS_MINUS_ONE: [GoldilocksField; 12] = const {
    let mut result = [GoldilocksField::ZERO; 12];
    let mut i = 0;
    while i < 12 {
        result[i] =
            GoldilocksField(1u64 << INNER_ROUNDS_MATRIX_DIAGONAL_ELEMENTS_MINUS_ONE_SHIFTS[i]);
        i += 1;
    }

    result
};

pub const INNER_ROUNDS_MATRIX_DIAGONAL_ELEMENTS: [GoldilocksField; 12] = const {
    let mut result = [GoldilocksField::ZERO; 12];
    let mut i = 0;
    while i < 12 {
        result[i] = GoldilocksField(
            (1u64 << INNER_ROUNDS_MATRIX_DIAGONAL_ELEMENTS_MINUS_ONE_SHIFTS[i]) + 1,
        );
        i += 1;
    }

    result
};

pub const EXTERNAL_MDS_MATRIX: [[GoldilocksField; 12]; 12] = const {
    let mut result = [[GoldilocksField::ZERO; 12]; 12];
    let mut block_row = 0;
    while block_row < 3 {
        let mut block_column = 0;
        while block_column < 3 {
            let mut inner_row = 0;
            while inner_row < 4 {
                let mut inner_column = 0;
                while inner_column < 4 {
                    // so it's block circulant
                    let should_double = block_row == block_column;

                    let row = block_row * 4 + inner_row;
                    let column = block_column * 4 + inner_column;

                    result[row][column] = EXTERNAL_MDS_MATRIX_BLOCK[inner_row][inner_column];
                    if should_double {
                        result[row][column].double_impl();
                    }
                    inner_column += 1;
                }
                inner_row += 1;
            }

            block_column += 1;
        }
        block_row += 1;
    }

    result
};

pub const INNER_ROUNDS_MATRIX: [[GoldilocksField; 12]; 12] = const {
    let mut result = [[GoldilocksField::ONE; 12]; 12];
    let mut i = 0;
    while i < 12 {
        result[i][i] = INNER_ROUNDS_MATRIX_DIAGONAL_ELEMENTS[i];
        i += 1;
    }

    result
};

pub const FULL_ROUND_CONSTANTS: [[GoldilocksField; STATE_WIDTH]; NUM_FULL_ROUNDS_TOTAL] = const {
    let mut constants_array = [[GoldilocksField::ZERO; STATE_WIDTH]; NUM_FULL_ROUNDS_TOTAL];
    let mut i = 0;
    while i < HALF_NUM_FULL_ROUNDS {
        constants_array[i] =
            poseidon_goldilocks_params::ROUND_CONSTANTS_ALIGNED_PER_ROUND_AS_FIELD_ELEMENTS[i];
        i += 1;
    }
    let mut i = 0;
    while i < HALF_NUM_FULL_ROUNDS {
        constants_array[i + HALF_NUM_FULL_ROUNDS] =
            poseidon_goldilocks_params::ROUND_CONSTANTS_ALIGNED_PER_ROUND_AS_FIELD_ELEMENTS
                [HALF_NUM_FULL_ROUNDS + NUM_PARTIAL_ROUNDS + i];
        i += 1;
    }

    constants_array
};

pub const PARTIAL_ROUND_CONSTANTS: [GoldilocksField; NUM_PARTIAL_ROUNDS] = const {
    let mut constants_array = [GoldilocksField::ZERO; NUM_PARTIAL_ROUNDS];
    let mut i = 0;
    while i < NUM_PARTIAL_ROUNDS {
        constants_array[i] =
            poseidon_goldilocks_params::ROUND_CONSTANTS_ALIGNED_PER_ROUND_AS_FIELD_ELEMENTS
                [HALF_NUM_FULL_ROUNDS + i][0];
        i += 1;
    }
    constants_array
};
