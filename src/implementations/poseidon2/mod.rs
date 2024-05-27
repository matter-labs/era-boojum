use super::*;
use crate::field::goldilocks::GoldilocksField;

pub mod params;

pub mod state_generic_impl;
#[cfg(not(all(
    feature = "include_packed_simd",
    any(
        target_feature = "neon",
        target_feature = "avx2",
        target_feature = "avx512bw",
        target_feature = "avx512cd",
        target_feature = "avx512dq",
        target_feature = "avx512f",
        target_feature = "avx512vl",
    )
)))]
pub use state_generic_impl::*;

// Other poseidon implementations depend on packed_simd 128
// which is no longer available in std::simd (and packed_simd is no longer
// supported in the newest rust nightly).
#[cfg(all(
    feature = "include_packed_simd",
    any(target_feature = "neon", target_feature = "avx2"),
    not(any(
        target_feature = "avx512bw",
        target_feature = "avx512cd",
        target_feature = "avx512dq",
        target_feature = "avx512f",
        target_feature = "avx512vl"
    ))
))]
pub mod state_vectorized_double;

#[cfg(all(
    feature = "include_packed_simd",
    any(target_feature = "neon", target_feature = "avx2"),
    not(any(
        target_feature = "avx512bw",
        target_feature = "avx512cd",
        target_feature = "avx512dq",
        target_feature = "avx512f",
        target_feature = "avx512vl"
    ))
))]
pub use state_vectorized_double::*;

#[cfg(all(
    feature = "include_packed_simd",
    target_feature = "avx512bw",
    target_feature = "avx512cd",
    target_feature = "avx512dq",
    target_feature = "avx512f",
    target_feature = "avx512vl"
))]
pub mod state_avx512;

#[cfg(all(
    feature = "include_packed_simd",
    target_feature = "avx512bw",
    target_feature = "avx512cd",
    target_feature = "avx512dq",
    target_feature = "avx512f",
    target_feature = "avx512vl"
))]
pub use state_avx512::*;

use crate::algebraic_props::round_function::*;
use crate::field::traits::field::Field;
use crate::implementations::poseidon_goldilocks_params::STATE_WIDTH;
use derivative::*;
use unroll::unroll_for_loops;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct Poseidon2Goldilocks;

impl AlgebraicRoundFunctionWithParams<GoldilocksField, 8, 12, 4> for Poseidon2Goldilocks {
    #[inline(always)]
    fn round_function(&self, state: &mut [GoldilocksField; 12]) {
        poseidon2_permutation(state);
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

impl AlgebraicRoundFunction<GoldilocksField, 8, 12, 4> for Poseidon2Goldilocks {
    #[inline(always)]
    fn round_function(state: &mut [GoldilocksField; 12]) {
        poseidon2_permutation(state);
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
