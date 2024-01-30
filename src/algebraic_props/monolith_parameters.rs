use crate::algebraic_props::matrix_parameters::MatrixParameters;
use crate::cs::traits::cs::DstBuffer;
use crate::field::mersenne::MersenneField;
use crate::field::PrimeField;
use crate::implementations::monolith;
use crate::implementations::monolith::state_generic_impl;
use crate::implementations::monolith::state_generic_impl::Monolith;
use crate::implementations::monolith::MonolithMersenne;
use crate::implementations::monolith::state24_params;
use derivative::*;

/// Exposes all the needed constants for the Poseidon2 hash function.
pub trait MonolithParameters<F: PrimeField, const AW: usize, const SW: usize, const CW: usize>:
    'static + Clone + Send + Sync
{
    const NUM_ROUNDS: usize;
    const NUM_BARS: usize;
    const LOOKUP_BITS: usize;
    const LOOKUP_SIZE: usize = 1 << Self::LOOKUP_BITS;
    const LOOKUP_NUM_LIMBS: usize = 32 / Self::LOOKUP_BITS;

    type MatrixParams: MatrixParameters<F, SW>;

    fn round_constants() -> &'static [[F; SW]];

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
pub struct MonolithMersenneMatrix;

impl MatrixParameters<MersenneField, {MersenneField::SPONGE_WIDTH}> for MonolithMersenneMatrix {
    const COEFFS: [[MersenneField; MersenneField::SPONGE_WIDTH]; MersenneField::SPONGE_WIDTH] = MersenneField::MDS_FIELD;
}

impl MonolithParameters<
    MersenneField, 
    {MersenneField::SPONGE_RATE}, 
    {MersenneField::SPONGE_WIDTH}, 
    {MersenneField::SPONGE_CAPACITY}
> for MonolithMersenne {
    const NUM_ROUNDS: usize = state_generic_impl::N_ROUNDS;
    const NUM_BARS: usize = state_generic_impl::NUM_BARS;
    const LOOKUP_BITS: usize = state_generic_impl::LOOKUP_BITS;

    type MatrixParams = MonolithMersenneMatrix;

    #[inline]
    fn round_constants() -> &'static [[MersenneField; MersenneField::SPONGE_WIDTH]] {
        &MersenneField::ROUND_CONSTANTS_FIELD[..]
    }

    const SUPPORTS_SPECIALIZED_FLATTENED_EVALUATION: bool = true;

    // #[inline]
    // #[unroll::unroll_for_loops]
    // fn specialized_evaluator<const PRODUCE_OUTPUT: bool>(
    //     inputs: &[MersenneField],
    //     output_buffer: &mut DstBuffer<'_, '_, MersenneField>,
    // ) {
    //     use crate::field::traits::field::Field;

    //     // use optimized implementation and capture some variables
    //     let state: [MersenneField; 12] = std::array::from_fn(|idx| inputs[idx]);
    //     let mut state = crate::implementations::poseidon2::state_generic_impl::State(state);
    //     state.suggested_mds_mul();
    //     let mut round_counter = 0;
    //     for _i in 0..4 {
    //         if _i != 0 {
    //             // save after non-linearity and MDS
    //             output_buffer.extend(state.0);
    //         }
    //         state.full_round(&mut round_counter);
    //     }
    //     for _i in 0..22 {
    //         // save after adding round constant, right before non-linearity on element 0
    //         // add constant
    //         state.0[0].add_assign(&crate::implementations::poseidon2::state_generic_impl::State::ALL_INNER_ROUND_CONSTANTS_AS_FIELD_ELEMENTS[round_counter]);
    //         output_buffer.push(state.0[0]);
    //         // apply non-linearity to the single element
    //         let mut t = state.0[0];
    //         state.0[0].square();
    //         t.mul_assign(&state.0[0]);
    //         state.0[0].square();
    //         state.0[0].mul_assign(&t);

    //         // multiply by MDS
    //         crate::implementations::poseidon2::state_generic_impl::State::m_i_mul(&mut state.0);

    //         round_counter += 1;

    //         // state.partial_round_poseidon2(&mut round_counter);
    //     }
    //     for _i in 0..4 {
    //         output_buffer.extend(state.0);
    //         state.full_round(&mut round_counter);
    //     }

    //     if PRODUCE_OUTPUT {
    //         output_buffer.extend(state.0);
    //     }
    // }
}
