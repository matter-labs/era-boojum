

use unroll::unroll_for_loops;

use crate::field::{
    Field, U64Representable,
};

// /// Monolith implementation for Mersenne prime field
// pub mod monolith_mersenne_t16;
// // pub use monolith_mersenne_t16::*;
// #[cfg(target_feature = "avx512f")]
// pub mod monolith_mersenne_t16_avx512;
// // pub use monolith_mersenne_t16_avx512::*;

// pub use monolith_mersenne_t24;
// // pub use monolith_mersenne_t24::*;
// #[cfg(target_feature = "avx512f")]
// pub mod monolith_mersenne_t24_avx512;
// // pub use monolith_mersenne_t24_avx512::*;

/// Number of state elements involved in the `Bars` layer
pub const NUM_BARS: usize = 8;

// The number of full rounds and partial rounds is given by the
// calc_round_numbers.py script. They happen to be the same for both
// width 8 and width 12 with s-box x^7.
//
// NB: Changing any of these values will require regenerating all of
// the precomputed constant arrays in this file.
/// Number of rounds in Monolith permutations
pub const N_ROUNDS: usize = 6;
/// Bit-size of the domain of the lookup function applied in the `Bars` layer: a state element is
/// split in limbs of `LOOKUP_BITS` bits, and the lookup function is applied to each limb.
pub const LOOKUP_BITS: usize = 16;
/// Size of the domain of the lookup function applied in the `Bars` layer
pub const LOOKUP_SIZE: usize = 1 << LOOKUP_BITS;
/// Number of limbs necessary to represent a 32-bit state element
pub const LOOKUP_NUM_LIMBS: usize = 32 / LOOKUP_BITS;

// #[inline]
// pub(crate) fn split(x: u128) -> (u64, u32) {
//     (x as u64, (x >> 64) as u32)
// }

// helper function to compute concrete layer. The function requires to provide a buffer with
// `T` elements initialized to 0 to compute the outcome of the layer
#[inline(always)]
#[unroll_for_loops]
pub fn concrete_u64_with_tmp_buffer<M: Monolith<T>, const T: usize>(
    state_u64: &[u64; T],
    round_constants: &[u32; T],
    res: &mut [u64; T],
) {
    for row in 0..T {
        for (column, input) in state_u64.iter().enumerate() {
            res[row] += *input * (M::MDS[row][column] as u64);
        }
        res[row] += round_constants[row] as u64;
        res[row] = M::from_u64_with_reduction(res[row]).as_u64();
    }
}

#[inline(always)]
#[unroll_for_loops]
fn concrete_u64_with_tmp_buffer_on_shifts<M: Monolith<T>, const T: usize>(
    state_u64: &[u64; T],
    round_constants: &[u32; T],
    res: &mut [u64; T],
) {
    for row in 0..T {
        for (column, input) in state_u64.iter().enumerate() {
            res[row] += *input << (M::M_POWERS[row][column] as u64);
            if row == ((column + 1) % T) {
                res[row] += *input;
            }
        }
        res[row] += round_constants[row] as u64;
        res[row] = M::from_u64_with_reduction(res[row]).as_u64();
    }
}

/// `Monolith` trait provides all the functions necessary to perform a Monolith permutation
pub trait Monolith<const T: usize>: Field + U64Representable 
// where [(); Self::SPONGE_WIDTH]:
{
    // Static data
    const SPONGE_WIDTH: usize = T;
    const SPONGE_CAPACITY: usize = 8;
    const SPONGE_RATE: usize = Self::SPONGE_WIDTH - Self::SPONGE_CAPACITY;

    /// Number of round constants employed in a full Monolith permutation
    const N_ROUND_CONSTANTS: usize = T * (N_ROUNDS + 1);
    /// All the round constants employed in a full Monolith permutation
    const ROUND_CONSTANTS: [[u32; T]; N_ROUNDS + 1];
    /// This constant contains the first row of a circulant `T x T` MDS matrix
    /// M. All of the remaining rows of M are rotations of this constant vector. A multiplication
    /// by M is used in the affine layer of Monolith.
    const MDS: [[u32; T]; T];
    const M_POWERS: [[u32; T]; T];

    const ROUND_CONSTANTS_FIELD: [[Self; T]; N_ROUNDS + 1];
    const MDS_FIELD: [[Self; T]; T];

    /// Compute the "Bar" component
    /// element is split in (16-bit lookups, analogous for 8-bit lookups):
    /// [x_3 || x_2 || x_1 || x_0], where x_i is 16 bits large
    /// element = 2^48 * x_3 + 2^32 * x_2 + 2^16 * x_1 + x_0
    /// Use lookups on x_3, x_2, x_1, x_0 and obtain y_3, y_2, y_1, y_0
    /// [y_3 || y_2 || y_1 || y_0], where y_i is 16 bits large
    /// Output y is set such that y = 2^48 * x_3 + 2^32 * x_2 + 2^16 * x_1 + x_0
    #[inline(always)]
    fn bar_32(limb: u32) -> u32 {
        match LOOKUP_BITS {
            8 => {
                let limbl1 =
                    ((!limb & 0x40000000) >> 6) | ((!limb & 0x808080) >> 7) | ((!limb & 0x3F7F7F7F) << 1); // Left rotation by 1
                let limbl2 =
                    ((limb & 0x60000000) >> 5) | ((limb & 0xC0C0C0) >> 6) | ((limb & 0x1F3F3F3F) << 2); // Left rotation by 2
                let limbl3 =
                    ((limb & 0xE0E0E0) >> 5) | ((limb & 0x1F1F1F) << 3); // Left rotation by 3

                // y_i = x_i + (1 + x_{i+1}) * x_{i+2} * x_{i+3}
                let tmp = limb ^ limbl1 & limbl2 & limbl3;
                ((tmp & 0x40000000) >> 6) | ((tmp & 0x808080) >> 7) | ((tmp & 0x3F7F7F7F) << 1)
            }
            16 => {
                let limbl1 =
                    ((!limb & 0x40000000) >> 14) | ((!limb & 0x8000) >> 15) | ((!limb & 0x3FFF7FFF) << 1); // Left rotation by 1
                let limbl2 =
                    ((limb & 0x60000000) >> 13) | ((limb & 0xC000) >> 14) | ((limb & 0x1FFF3FFF) << 2); // Left rotation by 2
                let limbl3 =
                    ((limb & 0xE000) >> 13) | ((limb & 0x1FFF) << 3); // Left rotation by 3

                // y_i = x_i + (1 + x_{i+1}) * x_{i+2} * x_{i+3}
                let tmp = limb ^ limbl1 & limbl2 & limbl3;
                ((tmp & 0x40000000) >> 14) | ((tmp & 0x8000) >> 15) | ((tmp & 0x3FFF7FFF) << 1)
                // Final rotation
            }
            _ => {
                panic!("Unsupported lookup size");
            }
        }
    }

    /// Same as `bar` optimized for u64
    #[inline(always)]
    fn bar_u64(el: &mut u64) {
        let limb = *el as u32;
        *el = match LOOKUP_BITS {
            8 => {
                let limbl1 =
                    ((!limb & 0x40000000) >> 6) | ((!limb & 0x808080) >> 7) | ((!limb & 0x3F7F7F7F) << 1); // Left rotation by 1
                let limbl2 =
                    ((limb & 0x60000000) >> 5) | ((limb & 0xC0C0C0) >> 6) | ((limb & 0x1F3F3F3F) << 2); // Left rotation by 2
                let limbl3 =
                    0xFF000000 | ((limb & 0xE0E0E0) >> 5) | ((limb & 0x1F1F1F) << 3); // Left rotation by 3

                // y_i = x_i + (1 + x_{i+1}) * x_{i+2} * x_{i+3}
                let tmp = limb ^ limbl1 & limbl2 & limbl3;
                ((tmp & 0x40000000) >> 6) | ((tmp & 0x808080) >> 7) | ((tmp & 0x3F7F7F7F) << 1)
            }
            16 => {
                let limbl1 =
                    ((!limb & 0x40000000) >> 14) | ((!limb & 0x8000) >> 15) | ((!limb & 0x3FFF7FFF) << 1); // Left rotation by 1
                let limbl2 =
                    ((limb & 0x60000000) >> 13) | ((limb & 0xC000) >> 14) | ((limb & 0x1FFF3FFF) << 2); // Left rotation by 2
                let limbl3 =
                    0xFFFF0000 | ((limb & 0xE000) >> 13) | ((limb & 0x1FFF) << 3); // Left rotation by 3

                // y_i = x_i + (1 + x_{i+1}) * x_{i+2} * x_{i+3}
                let tmp = limb ^ limbl1 & limbl2 & limbl3;
                ((tmp & 0x40000000) >> 14) | ((tmp & 0x8000) >> 15) | ((tmp & 0x3FFF7FFF) << 1)
                // Final rotation
            }
            _ => {
                panic!("Unsupported lookup size");
            }
        } as u64;
    }

    /// Same as `bars` optimized for u128
    #[inline(always)]
    #[unroll_for_loops]
    fn bars_u64(state_u64: &mut [u64; T]) {
        for i in 0..NUM_BARS {
            Self::bar_u64(&mut state_u64[i]);
        }
    }

    /// Compute the "Bricks" component
    #[inline(always)]
    #[unroll_for_loops]
    fn bricks(state: &mut [Self; T]) {
        // Feistel Type-3
        for i in (1..T).rev() {
            let prev = state[i - 1];
            let mut tmp_square = prev;
            tmp_square.mul_assign(&prev);
            state[i].add_assign(&tmp_square);
        }
    }

    /// Same as `bricks` optimized for u64
    /// Result is not reduced!
    #[unroll_for_loops]
    fn bricks_u64(state_u64: &mut [u64; T]) {
        // Feistel Type-3
        // Use "& 0xFFFFFFFF" to tell the compiler it is dealing with 32-bit values (save
        // some instructions for upper half)
        for i in (1..T).rev() {
            let prev = state_u64[i - 1];
            let mut tmp_square =
                (prev & 0xFFFFFFFF_u64) * (prev & 0xFFFFFFFF_u64);
            tmp_square = Self::from_u64_with_reduction(tmp_square).as_u64();
            state_u64[i] =
                (state_u64[i] & 0xFFFFFFFF_u64) + (tmp_square & 0xFFFFFFFF_u64);
        }
    }

    /// Compute the "Concrete" component
    #[inline(always)]
    #[unroll_for_loops]
    fn concrete(state: &mut [Self; T], round_constants: &[u32; T]) {
        let mut state_tmp = [0u64; T];
        let mut state_u64 = [0u64; T];
        for (dst, src) in state_u64.iter_mut().zip(state.iter()) {
            *dst = src.as_u64();
        }
        concrete_u64_with_tmp_buffer::<Self, T>(&state_u64, round_constants, &mut state_tmp);
        for (dst, src) in state.iter_mut().zip(state_tmp.iter()) {
            *dst = Self::from_u64_with_reduction(*src as u64)
        }
    }

    /// Same as `concrete` optimized for u64
    fn concrete_u64(state_u64: &mut [u64; T], round_constants: &[u32; T]) {
        let mut state_tmp = [0_u64; T];
        concrete_u64_with_tmp_buffer::<Self, T>(state_u64, round_constants, &mut state_tmp);
        state_u64.copy_from_slice(&state_tmp);
    }

    fn concrete_u64_on_shifts(state_u64: &mut [u64; T], round_constants: &[u32; T]) {
        let mut state_tmp = [0_u64; T];
        concrete_u64_with_tmp_buffer_on_shifts::<Self, T>(state_u64, round_constants, &mut state_tmp);
        state_u64.copy_from_slice(&state_tmp);
    }

    /// Full Monolith permutation
    #[inline]
    fn monolith(input: [Self; T]) -> [Self; T] {
        let mut state_u64 = [0; T];
        for (out, inp) in state_u64.iter_mut().zip(input.iter()) {
            *out = inp.as_u64();
        }

        Self::concrete_u64(&mut state_u64, &Self::ROUND_CONSTANTS[0]);
        for rc in Self::ROUND_CONSTANTS.iter().skip(1) {
            Self::bars_u64(&mut state_u64);
            Self::bricks_u64(&mut state_u64);
            Self::concrete_u64(&mut state_u64, rc);
        }

        // Convert back
        let mut state_f = [Self::ZERO; T];
        for (out, inp) in state_f.iter_mut().zip(state_u64.iter()) {
            *out = Self::from_u64_unchecked(*inp);
        }
        state_f
    }

    #[inline]
    fn monolith_on_shifts(input: [Self; T]) -> [Self; T] {
        let mut state_u64 = [0; T];
        for (out, inp) in state_u64.iter_mut().zip(input.iter()) {
            *out = inp.as_u64();
        }

        Self::concrete_u64_on_shifts(&mut state_u64, &Self::ROUND_CONSTANTS[0]);
        for rc in Self::ROUND_CONSTANTS.iter().skip(1) {
            Self::bars_u64(&mut state_u64);
            Self::bricks_u64(&mut state_u64);
            Self::concrete_u64_on_shifts(&mut state_u64, rc);
        }

        // Convert back
        let mut state_f = [Self::ZERO; T];
        for (out, inp) in state_f.iter_mut().zip(state_u64.iter()) {
            *out = Self::from_u64_unchecked(*inp);
        }
        state_f
    }

    fn monolith_permutation(input: [Self; T]) -> [Self; T] {
        Self::monolith(input)
    }
}
