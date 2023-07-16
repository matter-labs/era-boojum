use crate::field::goldilocks::GoldilocksField;
use crate::field::PrimeField;
use crate::implementations::poseidon_goldilocks::{self, PoseidonGoldilocks};

pub trait PoseidonParameters<
    F: PrimeField,
    const AW: usize,
    const SW: usize,
    const CW: usize,
>: 'static + Clone + Send + Sync
{
    const NUM_ROUNDS: usize;
    const NUM_PARTIAL_ROUNDS: usize;
    const NUM_FULL_ROUNDS: usize;
    const HALF_NUM_FULL_ROUNDS: usize;
    const FULL_NUM_ROUNDS: usize;
    const NONLINEARITY_DEGREE: usize;
    const ROUND_CONSTANTS_FUZED_LAST_FULL_AND_FIRST_PARTIAL: [F; SW];
    const FUZED_DENSE_MATRIX_LAST_FULL_AND_FIRST_PARTIAL: [[F; SW]; SW];

    type MdsMatrixParams: MatrixParameters<F, SW>;

    fn all_round_constants() -> &'static [[F; SW]];
    fn fuzed_round_constants_for_partial_rounds() -> &'static [F];
    fn vs_for_partial_rounds() -> &'static [[F; SW]];
    fn w_hats_for_partial_rounds() -> &'static [[F; SW]];
}

impl MatrixParameters<GoldilocksField, 12> for PoseidonGoldilocks {
    const COEFFS: [[GoldilocksField; 12]; 12] = poseidon_goldilocks::MDS_MATRIX;
}

impl PoseidonParameters<GoldilocksField, 8, 12, 4> for PoseidonGoldilocks {
    const NUM_ROUNDS: usize = poseidon_goldilocks::TOTAL_NUM_ROUNDS;
    const NUM_PARTIAL_ROUNDS: usize = poseidon_goldilocks::NUM_PARTIAL_ROUNDS;
    const NUM_FULL_ROUNDS: usize = poseidon_goldilocks::NUM_FULL_ROUNDS_TOTAL;
    const HALF_NUM_FULL_ROUNDS: usize = poseidon_goldilocks::HALF_NUM_FULL_ROUNDS;
    const FULL_NUM_ROUNDS: usize = poseidon_goldilocks::TOTAL_NUM_ROUNDS;
    const NONLINEARITY_DEGREE: usize = 7;
    const ROUND_CONSTANTS_FUZED_LAST_FULL_AND_FIRST_PARTIAL: [GoldilocksField; 12] =
        poseidon_goldilocks::ROUND_CONSTANTS_FUZED_LAST_FULL_AND_FIRST_PARTIAL;
    const FUZED_DENSE_MATRIX_LAST_FULL_AND_FIRST_PARTIAL: [[GoldilocksField; 12]; 12] =
        poseidon_goldilocks::FUZED_DENSE_MATRIX_LAST_FULL_AND_FIRST_PARTIAL;

    type MdsMatrixParams = Self;

    #[inline]
    fn all_round_constants() -> &'static [[GoldilocksField; 12]] {
        &poseidon_goldilocks::ROUND_CONSTANTS_ALIGNED_PER_ROUND_AS_FIELD_ELEMENTS[..]
    }

    #[inline]
    fn fuzed_round_constants_for_partial_rounds() -> &'static [GoldilocksField] {
        &poseidon_goldilocks::ROUND_CONSTANTS_FOR_FUZED_SBOXES[..]
    }

    #[inline]
    fn vs_for_partial_rounds() -> &'static [[GoldilocksField; 12]] {
        &poseidon_goldilocks::VS_FOR_PARTIAL_ROUNDS_EXTENDED[..]
    }

    #[inline]
    fn w_hats_for_partial_rounds() -> &'static [[GoldilocksField; 12]] {
        &poseidon_goldilocks::W_HATS_FOR_PARTIAL_ROUNDS_EXTENDED[..]
    }
}
