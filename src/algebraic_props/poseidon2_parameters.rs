use crate::algebraic_props::matrix_parameters::MatrixParameters;
use crate::cs::traits::cs::DstBuffer;
use crate::field::goldilocks::GoldilocksField;
use crate::field::PrimeField;
use crate::implementations::poseidon2;
use crate::implementations::poseidon2::Poseidon2Goldilocks;
use crate::implementations::poseidon_goldilocks_params;
use derivative::*;

/// Exposes all the needed constants for the Poseidon2 hash function.
pub trait Poseidon2Parameters<F: PrimeField, const AW: usize, const SW: usize, const CW: usize>:
    'static + Clone + Send + Sync
{
    const NUM_ROUNDS: usize;
    const NUM_PARTIAL_ROUNDS: usize;
    const NUM_FULL_ROUNDS: usize;
    const HALF_NUM_FULL_ROUNDS: usize;
    const FULL_NUM_ROUNDS: usize;
    const NONLINEARITY_DEGREE: usize;

    type ExternalMatrixParams: MatrixParameters<F, SW>;
    type InternalMatrixParams: MatrixParameters<F, SW>;

    fn full_round_constants() -> &'static [[F; SW]];
    fn inner_round_constants() -> &'static [F];

    const SUPPORTS_SPECIALIZED_FLATTENED_EVALUATION: bool = false;

    fn specialized_evaluator<const PRODUCE_OUTPUT: bool>(
        _inputs: &[F],
        _output_buffer: &mut DstBuffer<'_, '_, F>,
    ) {
        if Self::SUPPORTS_SPECIALIZED_FLATTENED_EVALUATION == false {
            unreachable!()
        } else {
            panic!("please implement specialized evaluator")
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Poseidon2GoldilocksExternalMatrix;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Poseidon2GoldilocksInnerMatrix;

impl MatrixParameters<GoldilocksField, 12> for Poseidon2GoldilocksExternalMatrix {
    const COEFFS: [[GoldilocksField; 12]; 12] = poseidon2::params::EXTERNAL_MDS_MATRIX;
}

impl MatrixParameters<GoldilocksField, 12> for Poseidon2GoldilocksInnerMatrix {
    const COEFFS: [[GoldilocksField; 12]; 12] = poseidon2::params::INNER_ROUNDS_MATRIX;
}

impl Poseidon2Parameters<GoldilocksField, 8, 12, 4> for Poseidon2Goldilocks {
    const NUM_ROUNDS: usize = poseidon_goldilocks_params::TOTAL_NUM_ROUNDS;
    const NUM_PARTIAL_ROUNDS: usize = poseidon_goldilocks_params::NUM_PARTIAL_ROUNDS;
    const NUM_FULL_ROUNDS: usize = poseidon_goldilocks_params::NUM_FULL_ROUNDS_TOTAL;
    const HALF_NUM_FULL_ROUNDS: usize = poseidon_goldilocks_params::HALF_NUM_FULL_ROUNDS;
    const FULL_NUM_ROUNDS: usize = poseidon_goldilocks_params::TOTAL_NUM_ROUNDS;
    const NONLINEARITY_DEGREE: usize = 7;

    type ExternalMatrixParams = Poseidon2GoldilocksExternalMatrix;
    type InternalMatrixParams = Poseidon2GoldilocksInnerMatrix;

    #[inline]
    fn full_round_constants() -> &'static [[GoldilocksField; 12]] {
        &poseidon2::params::FULL_ROUND_CONSTANTS[..]
    }

    #[inline]
    fn inner_round_constants() -> &'static [GoldilocksField] {
        &poseidon2::params::PARTIAL_ROUND_CONSTANTS[..]
    }

    const SUPPORTS_SPECIALIZED_FLATTENED_EVALUATION: bool = true;

    #[inline]
    #[unroll::unroll_for_loops]
    fn specialized_evaluator<const PRODUCE_OUTPUT: bool>(
        inputs: &[GoldilocksField],
        output_buffer: &mut DstBuffer<'_, '_, GoldilocksField>,
    ) {
        use crate::field::traits::field::Field;

        // use optimized implementation and capture some variables
        let state: [GoldilocksField; 12] = std::array::from_fn(|idx| inputs[idx]);
        let mut state = crate::implementations::poseidon2::state_generic_impl::State(state);
        state.suggested_mds_mul();
        let mut round_counter = 0;
        for _i in 0..4 {
            if _i != 0 {
                // save after non-linearity and MDS
                output_buffer.extend(state.0);
            }
            state.full_round(&mut round_counter);
        }
        for _i in 0..22 {
            // save after adding round constant, right before non-linearity on element 0
            // add constant
            state.0[0].add_assign(&crate::implementations::poseidon2::state_generic_impl::State::ALL_INNER_ROUND_CONSTANTS_AS_FIELD_ELEMENTS[round_counter]);
            output_buffer.push(state.0[0]);
            // apply non-linearity to the single element
            let mut t = state.0[0];
            state.0[0].square();
            t.mul_assign(&state.0[0]);
            state.0[0].square();
            state.0[0].mul_assign(&t);

            // multiply by MDS
            crate::implementations::poseidon2::state_generic_impl::State::m_i_mul(&mut state.0);

            round_counter += 1;

            // state.partial_round_poseidon2(&mut round_counter);
        }
        for _i in 0..4 {
            output_buffer.extend(state.0);
            state.full_round(&mut round_counter);
        }

        if PRODUCE_OUTPUT {
            output_buffer.extend(state.0);
        }
    }
}
