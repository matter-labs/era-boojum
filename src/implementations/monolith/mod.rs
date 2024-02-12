use super::*;
use crate::field::mersenne::MersenneField;
use crate::implementations::monolith::state_generic_impl::Monolith;

pub mod state24_params;

#[cfg(not(target_feature = "avx512f"))]
pub mod state_generic_impl;
#[cfg(not(target_feature = "avx512f"))]
pub use state_generic_impl::*;

#[cfg(target_feature = "avx512f")]
pub mod state24_avx512_impl;
#[cfg(target_feature = "avx512f")]
pub use state24_avx512_impl::*;

use crate::algebraic_props::round_function::*;
use crate::field::traits::field::Field;
use derivative::*;
use unroll::unroll_for_loops;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct MonolithMersenne;

impl AlgebraicRoundFunctionWithParams<
    MersenneField, 
    {MersenneField::SPONGE_RATE}, 
    {MersenneField::SPONGE_WIDTH}, 
    {MersenneField::SPONGE_CAPACITY}
> for MonolithMersenne {
    #[inline(always)]
    fn round_function(&self, state: &mut [MersenneField; MersenneField::SPONGE_WIDTH]) {
        let res = MersenneField::monolith_permutation(*state);
        *state = res;
    }
    #[inline(always)]
    fn initial_state(&self) -> [MersenneField; MersenneField::SPONGE_WIDTH] {
        [MersenneField::ZERO; MersenneField::SPONGE_WIDTH]
    }
    #[inline(always)]
    fn specialize_for_len(&self, len: u32, state: &mut [MersenneField; MersenneField::SPONGE_WIDTH]) {
        // as described in the original Poseidon paper we use
        // the last element of the state
        state[MersenneField::SPONGE_WIDTH-1] = MersenneField::from_u64_with_reduction(len as u64);
    }
    #[unroll_for_loops]
    #[inline(always)]
    fn absorb_into_state(
        &self,
        state: &mut [MersenneField; MersenneField::SPONGE_WIDTH],
        to_absorb: &[MersenneField; MersenneField::SPONGE_RATE],
        mode: AbsorptionMode,
    ) {
        match mode {
            AbsorptionMode::Overwrite => {
                let mut i = 0;
                while i < MersenneField::SPONGE_RATE {
                    state[i] = to_absorb[i];
                    i += 1;
                }
            }
            AbsorptionMode::Addition => {
                let mut i = 0;
                while i < MersenneField::SPONGE_RATE {
                    state[i].add_assign(&to_absorb[i]);
                    i += 1;
                }
            }
        }
    }

    #[inline(always)]
    fn state_get_commitment<'a>(&self, state: &'a [MersenneField; MersenneField::SPONGE_WIDTH]) -> &'a [MersenneField] {
        &state[0..MersenneField::SPONGE_CAPACITY]
    }

    #[inline(always)]
    fn state_into_commitment_fixed<const N: usize>(
        &self,
        state: &[MersenneField; MersenneField::SPONGE_WIDTH],
    ) -> [MersenneField; N] {
        debug_assert!(N <= MersenneField::SPONGE_RATE);
        let mut result = [MersenneField::ZERO; N];
        result.copy_from_slice(&state[..N]);

        result
    }
}

impl AlgebraicRoundFunction<
    MersenneField, 
    {MersenneField::SPONGE_RATE}, 
    {MersenneField::SPONGE_WIDTH}, 
    {MersenneField::SPONGE_CAPACITY}
> for MonolithMersenne {
    #[inline(always)]
    fn round_function(state: &mut [MersenneField; MersenneField::SPONGE_WIDTH]) {
        let res = MersenneField::monolith_permutation(*state);
        *state = res;
    }
    #[inline(always)]
    fn initial_state() -> [MersenneField; MersenneField::SPONGE_WIDTH] {
        [MersenneField::ZERO; MersenneField::SPONGE_WIDTH]
    }
    #[inline(always)]
    fn specialize_for_len(len: u32, state: &mut [MersenneField; MersenneField::SPONGE_WIDTH]) {
        // as described in the original Poseidon paper we use
        // the last element of the state
        state[MersenneField::SPONGE_WIDTH-1] = MersenneField::from_u64_with_reduction(len as u64);
    }
    #[inline(always)]
    #[unroll_for_loops]
    fn absorb_into_state<M: AbsorptionModeTrait<MersenneField>>(
        state: &mut [MersenneField; MersenneField::SPONGE_WIDTH],
        to_absorb: &[MersenneField; MersenneField::SPONGE_RATE],
    ) {
        for i in 0..MersenneField::SPONGE_RATE {
            M::absorb(&mut state[i], &to_absorb[i]);
        }
    }

    #[inline(always)]
    fn state_into_commitment<const N: usize>(
        state: &[MersenneField; MersenneField::SPONGE_WIDTH],
    ) -> [MersenneField; N] {
        debug_assert!(N <= MersenneField::SPONGE_RATE);
        let mut result = [MersenneField::ZERO; N];
        result.copy_from_slice(&state[..N]);

        result
    }
}

