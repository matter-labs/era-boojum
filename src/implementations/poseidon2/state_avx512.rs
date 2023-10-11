//! A vectorized implementation of the poseidon2 state.
use crate::field::Field;
use crate::field::goldilocks::avx512_impl;
use std::mem::align_of;
use std::ops::{Add, Mul, Shl};
use std::usize;
use unroll::unroll_for_loops;
use std::arch::x86_64::{self, __m512i, __m128i};
use crate::utils::PipeOp;
use crate::field::goldilocks::GoldilocksField;
use crate::field::traits::representation::U64Representable;

use super::poseidon_goldilocks_params;

#[derive(Default, PartialEq, Eq, Hash, Clone, Copy)]
#[repr(C, align(64))]
pub struct State(pub [GoldilocksField; 12]);

#[derive(Default, PartialEq, Eq, Hash, Clone, Copy)]
#[repr(C, align(64))]
pub struct Aligned(pub [u64; 8]);

impl Aligned {
    #[inline(always)]
    fn as_u64_ptr(&self) -> *const i64 {
        self.0.as_ptr() as *const _
    }
}

// we also need holder for SIMD targets, because u64x4 has smaller alignment than u64x8
#[derive(Clone, Copy)]
#[repr(C, align(64))]
struct U128x4Holder([packed_simd::u128x4; 3]);

impl std::fmt::Debug for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl std::fmt::Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl State {
    pub const ORDER_BITS: usize = GoldilocksField::ORDER_BITS;
    pub const ORDER: u128 = GoldilocksField::ORDER as u128;
    pub const TWO_ADICITY: usize = GoldilocksField::TWO_ADICITY;
    pub const T: u128 = (Self::ORDER - 1) >> Self::TWO_ADICITY;
    pub const BARRETT: u128 = 18446744078004518912; // 0x10000000100000000
    pub const EPSILON: u128 = (1 << 32) - 1;
    pub const EPSILON_VECTOR: packed_simd::u128x4 = packed_simd::u128x4::splat(Self::EPSILON);

    pub const RATE: usize = poseidon_goldilocks_params::RATE;
    pub const CAPACITY: usize = poseidon_goldilocks_params::CAPACITY;
    pub const STATE_WIDTH: usize = poseidon_goldilocks_params::STATE_WIDTH;
    pub const HALF_NUM_FULL_ROUNDS: usize = poseidon_goldilocks_params::HALF_NUM_FULL_ROUNDS;
    pub const NUM_FULL_ROUNDS_TOTAL: usize = poseidon_goldilocks_params::NUM_FULL_ROUNDS_TOTAL;
    pub const NUM_PARTIAL_ROUNDS: usize = poseidon_goldilocks_params::NUM_PARTIAL_ROUNDS;
    pub const TOTAL_NUM_ROUNDS: usize = poseidon_goldilocks_params::TOTAL_NUM_ROUNDS;
    pub const ALL_ROUND_CONSTANTS: [Self; Self::TOTAL_NUM_ROUNDS] = const {
        let mut constants_array = [Self([GoldilocksField::ZERO; Self::STATE_WIDTH]); Self::TOTAL_NUM_ROUNDS];
        let mut i = 0;
        while i < Self::TOTAL_NUM_ROUNDS {
            let mut t = [GoldilocksField::ZERO; 12];
            let mut j = 0;
            while j < 12 {
                t[j] = 
                    GoldilocksField::from_nonreduced_u64(
                    poseidon_goldilocks_params::ALL_ROUND_CONSTANTS[i * Self::STATE_WIDTH + j]);
                j += 1;
            }
            constants_array[i] = Self(t);
            i += 1;
        }
        constants_array
    };

    pub const ALL_INNER_ROUND_CONSTANTS: [u128; Self::TOTAL_NUM_ROUNDS] = const {
        let mut constants_array = [0u128; Self::TOTAL_NUM_ROUNDS];
        let mut i = 0;
        while i < Self::TOTAL_NUM_ROUNDS {
            constants_array[i] =
                poseidon_goldilocks_params::ALL_ROUND_CONSTANTS[i * Self::STATE_WIDTH] as u128;
            i += 1;
        }
        constants_array
    };

    pub const M_I_DIAGONAL_ELEMENTS_POWS: [packed_simd::u128x4; 3] = [
        packed_simd::u128x4::new(4, 14, 11, 8),
        packed_simd::u128x4::new(0, 5, 2, 9),
        packed_simd::u128x4::new(13, 6, 3, 12),
    ];

    pub const M_I_DIAGONAL_ELEMENTS: [packed_simd::u128x4; 3] = [
        packed_simd::u128x4::new(1 << 4, 1 << 14, 1 << 11, 1 << 8),
        packed_simd::u128x4::new(1 << 0, 1 << 5, 1 << 2, 1 << 9),
        packed_simd::u128x4::new(1 << 13, 1 << 6, 1 << 3, 1 << 12),
    ];

    #[inline(always)]
    pub fn new() -> Self {
        Self([GoldilocksField::ZERO; 12])
    }

    // #[inline(always)]
    // pub const fn from_u128_array(value: [u128; 12]) -> Self {
    //     Self(value)
    // }

    #[inline(always)]
    #[unroll_for_loops]
    pub fn to_reduced(&mut self) -> &mut Self {
        todo!();
        // let mut a_u64 = Self::as_u128x4_arrays(self);
        //
        // for i in 0..3 {
        //     let a = a_u64.0[i];
        //     let a_reduced = a.add(Self::EPSILON_VECTOR);
        //     let cmp = a_reduced.lt(Self::EPSILON_VECTOR);
        //     let res = cmp.select(a_reduced, a);
        //
        //     a_u64.0[i] = res;
        // }
        //
        // *self = Self::from_u128x4_arrays(a_u64);
        // self
    }

    #[inline(always)]
    #[unroll_for_loops]
    fn mul_assign_impl_without_prereduction(&mut self, other: &Self) -> &mut Self {
        for i in 0..12 {
            let c = self.0[i] * other.0[i];
            self.0[i] = c;
        }

        self
    }

    #[inline(always)]
    pub fn from_field_array(input: [GoldilocksField; 12]) -> Self {
        let mut d = Self::new();
        for i in 0..12 {
            d.0[i] = input[i];
        }
        d
    }

    #[inline(always)]
    pub fn as_field_array(self) -> [GoldilocksField; 12] {
        let mut d = [GoldilocksField::ZERO; 12];
        for i in 0..12 {
            d[i] = self.0[i];
        }
        d
    }

    // #[inline(always)]
    // fn as_u128x4_arrays(input: &Self) -> U128x4Holder {
    //     // this preserves an alignment
    //     unsafe { std::mem::transmute(*input) }
    // }
    //
    // #[inline(always)]
    // fn from_u128x4_arrays(input: U128x4Holder) -> Self {
    //     // this preserves an alignment
    //     unsafe { std::mem::transmute(input) }
    // }

    //vectorized mds_mul
    #[rustfmt::skip]
    #[inline(always)]
    #[unroll_for_loops]
    pub fn suggested_mds_mul(&mut self) {
        unsafe {
            // Block 0, 2
            let ix_b2_repl = x86_64::_mm512_load_epi64(Aligned([0, 1, 2, 3, 0, 1, 2, 3]).as_u64_ptr());

            // NOTE: perhaps may be combined.
            let ix_odd_cmb    = x86_64::_mm512_load_epi64(Aligned([1u64, 3, 5, 7,  9, 11, 0, 0]).as_u64_ptr());
            let ix_odd_cmb_r  = x86_64::_mm512_load_epi64(Aligned([1u64, 3, 5, 7, 13, 15, 0, 0]).as_u64_ptr());
            let ix_even_cmb_r = x86_64::_mm512_load_epi64(Aligned([0u64, 2, 4, 6, 12, 14, 0, 0]).as_u64_ptr());

            // TODO: check if constructing with broadcast is faster. 
            let b3_mul_factor = x86_64::_mm512_load_epi64(Aligned([2, 2, 2, 2, 4, 4, 4, 4]).as_u64_ptr());
            // let x4_mul_factor = x86_64::_mm512_set1_epi64(4);

            let x_0_7_x1 = x86_64::_mm512_load_epi64(&self.0[0] as *const _ as *const _);
            let x_0_7_x1 = avx512_impl::MixedGL::canonicalize(x_0_7_x1);
            let x_8_11_x1 = x86_64::_mm512_maskz_load_epi64(0b00001111, &self.0[8] as *const _ as *const _);
            let x_8_11_x1 = avx512_impl::MixedGL::canonicalize(x_8_11_x1);

            let x_0_7_x2 = avx512_impl::MixedGL::add_no_double_overflow_64_64(x_0_7_x1, x_0_7_x1);
            let x_0_7_x2 = avx512_impl::MixedGL::canonicalize(x_0_7_x2);
            let x_0_7_x4 = avx512_impl::MixedGL::add_no_double_overflow_64_64(x_0_7_x2, x_0_7_x2);

            let x_8_11_r_x1 = x86_64::_mm512_permutexvar_epi64(ix_b2_repl, x_8_11_x1);
            // [ 2x_8-11, 4x8-11 ]
            let x_8_11_r_x2_x4 = avx512_impl::MixedGL::reduce128(avx512_impl::MixedGL::mul64_64(x_8_11_r_x1, b3_mul_factor));

            // [ 4x_2i, 2x_2i+1 ]
            let x_0_7_x4_x2 = x86_64::_mm512_mask_blend_epi64(0b01010101, x_0_7_x2, x_0_7_x4);

            // [ 5x_2i, 3x_2i+1 ]
            let x_0_7_x5_x3 = avx512_impl::MixedGL::add_no_double_overflow_64_64(x_0_7_x4_x2, x_0_7_x1);

            // NOTE: can add 4 elements to the addition.
            // [ 3x8-11, 5x8-11 ]
            let x_8_11_r_x3_x5 = avx512_impl::MixedGL::add_no_double_overflow_64_64(x_8_11_r_x2_x4, x_8_11_r_x1); // TODO: canonicalise

            let x_odd_x2 = x86_64::_mm512_permutex2var_epi64(x_0_7_x2, ix_odd_cmb, x_8_11_r_x2_x4);
            let x_odd_x3 = x86_64::_mm512_permutex2var_epi64(x_0_7_x5_x3, ix_odd_cmb, x_8_11_r_x3_x5);
            let x_odd_x4 = x86_64::_mm512_permutex2var_epi64(x_0_7_x4, ix_odd_cmb_r, x_8_11_r_x2_x4);
            let x_odd_x4 = avx512_impl::MixedGL::canonicalize(x_odd_x4);
            let x_even_x4 = x86_64::_mm512_permutex2var_epi64(x_0_7_x4, ix_even_cmb_r, x_8_11_r_x2_x4);
            let x_even_x4 = avx512_impl::MixedGL::canonicalize(x_even_x4);

            // NOTE: can fit 2 more additions
            let x_odd_x6 = avx512_impl::MixedGL::add_no_double_overflow_64_64(x_odd_x2, x_odd_x4);
            // NOTE: can fit 2 more additions
            let x_odd_x7 = avx512_impl::MixedGL::add_no_double_overflow_64_64(x_odd_x3, x_odd_x4);

            let x_odd_x3 = avx512_impl::MixedGL::canonicalize(x_odd_x3);

            // mds: [ 5 7 1 3
            //        4 6 1 1
            //        1 3 5 7
            //        1 1 4 6 ]
            //
            // r0: q0 + w0, q0 = x2 + 5x0, w0 = 3x3 + 7x1
            // r1: q1 + w1, q1 = x2 + x3,  w1 = 4x0 + 6x1
            // r2: q2 + w2, q2 = x0 + 5x2, w2 = 3x1 + 7x3
            // r3: q3 + w3, q3 = x0 + x1,  w3 = 4x2 + 6x3

            // [0q0, 0q1, 0q2, 0q3, 1q0, 1q1, 1q2, 1q3]
            // [5x0, 1x3, 5x2, 1x1, 5x4, 1x7, 5x6, 1x5]
            // [1x2, 1x2, 1x0, 1x0, 1x6, 1x6, 1x4, 1x4]
            let ix_0_7_q_l = x86_64::_mm512_load_epi64(Aligned([8, 3, 10, 1, 12, 7, 14, 5]).as_u64_ptr());
            let ix_0_7_q_r = x86_64::_mm512_load_epi64(Aligned([2, 2, 0, 0, 6, 6, 4, 4]).as_u64_ptr());
            let q_0_7_l = x86_64::_mm512_permutex2var_epi64(x_0_7_x1, ix_0_7_q_l, x_0_7_x5_x3);
            let q_0_7_r = x86_64::_mm512_permutexvar_epi64(ix_0_7_q_r, x_0_7_x1);

            let q_0_7 = avx512_impl::MixedGL::add_no_double_overflow_64_64(q_0_7_l, q_0_7_r);
            let q_0q_1q = avx512_impl::MixedGL::canonicalize(q_0_7);

            // [ 2q0,  2q1,  2q2, 2q3] 
            // [ 5x8, 1x11, 5x10, 1x9] 
            // [1x10, 1x10,  1x8, 1x8] 
            let ix_8_11_h1_l = x86_64::_mm512_load_epi64(Aligned([12, 3, 14, 1,  0,  0,  0,  0]).as_u64_ptr());
            let ix_8_11_h1_r = x86_64::_mm512_load_epi64(Aligned([ 2, 2,  0, 0, 0, 0, 0, 0]).as_u64_ptr());
            let r_8_11_h1_l = x86_64::_mm512_permutex2var_epi64(x_8_11_x1, ix_8_11_h1_l, x_8_11_r_x3_x5);
            let r_8_11_h1_r = x86_64::_mm512_permutex2var_epi64(x_8_11_x1, ix_8_11_h1_r, q_0q_1q);
            let r_8_11_h1_r = x86_64::_mm512_permutexvar_epi64(ix_8_11_h1_r, x_8_11_x1);
            // let r_8_11_h1_l = x86_64::_mm512_mask_blend_epi64(0b11110000, r_8_11_h1_l, q_0q_1q);

            let __2q = avx512_impl::MixedGL::add_no_double_overflow_64_64(r_8_11_h1_l, r_8_11_h1_r);
            let __2q = avx512_impl::MixedGL::canonicalize(__2q);

            // [0w0, 0w2, 1w0, 1w2, 2w0, 2w2, _, _]
            let ix_0_11_h2_x7 = x86_64::_mm512_load_epi64(Aligned([1, 0, 3, 2, 5, 4, 0, 0]).as_u64_ptr());
            let x_odd_perm_x7 = x86_64::_mm512_permutexvar_epi64(ix_0_11_h2_x7, x_odd_x7);
            // NOTE: can fit 2 more additions
            let w02 = avx512_impl::MixedGL::add_no_double_overflow_64_64(x_odd_perm_x7, x_odd_x3);

            // [0w1, 0w3, 1w1, 1w3, 2w1, 2w3, _, _]
            // NOTE: can fit 2 more additions
            let w13 = avx512_impl::MixedGL::add_no_double_overflow_64_64(x_odd_x6, x_even_x4);

            // [0r0, 0r1, 0r2, 0r3, 1r0, 1r1, 1r2, 1r3]
            // [0w0, 0w1, 0w2, 0w3, 1w0, 1w1, 1w2, 1w3]
            let ix_w_0_7 = x86_64::_mm512_load_epi64(Aligned([0, 8, 1, 9, 2, 10, 3, 11]).as_u64_ptr());
            let w_0w_1w = x86_64::_mm512_permutex2var_epi64(w02, ix_w_0_7, w13);
            let __0r_1r = avx512_impl::MixedGL::add_no_double_overflow_64_64(w_0w_1w, q_0q_1q);
            let __0r_1r = avx512_impl::MixedGL::canonicalize(__0r_1r);

            // NOTE: can fit 4 more additions
            // [2r0, 2r1, 2r2, 2r3] [01r0, 01r1, 01r2, 01r3]
            // [2w0, 2w1, 2w2, 2w3] [1r0, 1r1, 1r2, 1r3]
            // [2q0, 2q1, 2q2, 2q3] [0r0, 0r1, 0r2, 0r3]
            let ix_2w_l = x86_64::_mm512_load_epi64(Aligned([4, 12, 5, 13, 0, 0, 0, 0]).as_u64_ptr());
            let __2w_l = x86_64::_mm512_permutex2var_epi64(w02, ix_2w_l, w13);
            let __2w_l = x86_64::_mm512_mask_blend_epi64(0b11110000, __2w_l, __0r_1r);
            let ix_2w_r = x86_64::_mm512_load_epi64(Aligned([0, 1, 2, 3, 8, 9, 10, 11]).as_u64_ptr());
            let __2w_r = x86_64::_mm512_permutex2var_epi64(__2q, ix_2w_r, __0r_1r);
            let __2r_01r = avx512_impl::MixedGL::add_no_double_overflow_64_64(__2w_l, __2w_r);
            let __2r_01r = avx512_impl::MixedGL::canonicalize(__2r_01r);


            // [r0, r1, r2, r3, r0, r1, r2, r3]
            let ix_01r_2r = x86_64::_mm512_load_epi64(Aligned([4, 5, 6, 7, 0, 1, 2, 3]).as_u64_ptr());
            let __01r_2r = x86_64::_mm512_permutexvar_epi64(ix_01r_2r, __2r_01r);
            let __r_r = avx512_impl::MixedGL::add_no_double_overflow_64_64(__2r_01r, __01r_2r);

            // [0f0, 0f1, 0f2, 0f3, 1f0, 1f1, 1f2, 1f3]
            let __0f_1f = avx512_impl::MixedGL::add_no_double_overflow_64_64(__r_r, __0r_1r);

            let __2f = avx512_impl::MixedGL::add_no_double_overflow_64_64(__r_r, __2r_01r);

            x86_64::_mm512_store_epi64(&mut self.0[0] as *mut _ as *mut _, __0f_1f);
            x86_64::_mm512_mask_store_epi64(&mut self.0[8] as *mut _ as *mut _, 0b00001111, __2f);
        }
    }

    #[inline(always)]
    #[unroll_for_loops]
    pub fn apply_round_constants(&mut self, round: usize) {
        todo!();
        // let const_current = Self::ALL_ROUND_CONSTANTS[round];
        // let const_u64 = Self::as_u128x4_arrays(&const_current);
        // let mut state_u64 = Self::as_u128x4_arrays(self);
        // for i in 0..3 {
        //     state_u64.0[i] = state_u64.0[i].add(const_u64.0[i]);
        // }
        // *self = Self::from_u128x4_arrays(state_u64);
    }

    #[inline(always)]
    #[unroll_for_loops]
    pub fn apply_non_linearity(&mut self) {
        for i in 0..12 {
            todo!();
            // self.0[i] = GoldilocksField::from_u128_with_reduction(self.0[i]).as_u64() as u128;
        }
        let mut t = *self;
        self.elementwise_square();
        t.elementwise_mul_assign(&*self);
        self.elementwise_square();
        self.elementwise_mul_assign(&t);
    }

    #[inline(always)]
    fn elementwise_mul_assign(&mut self, other: &Self) {
        Self::mul_assign_impl_without_prereduction(self, other);
    }

    #[inline(always)]
    fn elementwise_square(&mut self) {
        let t = *self;
        self.elementwise_mul_assign(&t);
    }

    #[inline(always)]
    fn full_round(&mut self, round_counter: &mut usize) {
        // add constants
        self.apply_round_constants(*round_counter);
        // apply non-linearity
        self.apply_non_linearity();
        // multiply by MDS
        self.suggested_mds_mul();

        *round_counter += 1;
    }

    #[inline(always)]
    #[unroll_for_loops]
    pub fn m_i_mul(&mut self) {
        todo!();
        // let mut state_u64 = Self::as_u128x4_arrays(self);
        // let mut rowwise_sum = 0u128;
        // for i in 0..3 {
        //     rowwise_sum += state_u64.0[i].wrapping_sum();
        // }
        //
        // for i in 0..3 {
        //     state_u64.0[i] = state_u64.0[i].mul(Self::M_I_DIAGONAL_ELEMENTS[i]);
        //     state_u64.0[i] = state_u64.0[i].add(rowwise_sum);
        // }
        //
        // *self = Self::from_u128x4_arrays(state_u64);
    }

    #[inline(always)]
    fn partial_round_poseidon2(&mut self, round_counter: &mut usize) {
        todo!();
        // // add constant
        // use std::ops::AddAssign;
        // self.0[0].add_assign(&Self::ALL_INNER_ROUND_CONSTANTS[*round_counter]);
        // // apply non-linearity to the single element
        // let mut s = GoldilocksField::from_u128_with_reduction(self.0[0]);
        // let mut t = s;
        // s.square();
        // t.mul_assign(&s);
        // s.square();
        // s.mul_assign(&t);
        // self.0[0] = s.as_u64() as u128;
        //
        // // multiply by MDS
        // self.m_i_mul();
        //
        // *round_counter += 1;
    }

    #[inline(always)]
    #[unroll_for_loops]
    pub fn poseidon2_permutation(&mut self) {
        self.suggested_mds_mul();
        let mut round_counter = 0;
        for _i in 0..4 {
            self.full_round(&mut round_counter);
        }
        for i in 0..22 {
            self.partial_round_poseidon2(&mut round_counter);

            if i % 3 == 1 {
                for j in 0..12 {
                    todo!();
                    // self.0[j] =
                    //     GoldilocksField::from_u128_with_reduction(self.0[j]).as_u64() as u128;
                }
            }
        }
        for _i in 0..4 {
            self.full_round(&mut round_counter);
        }

        for i in 0..12 {
            todo!();
            // self.0[i] = GoldilocksField::from_u128_with_reduction(self.0[i]).as_u64() as u128;
        }
    }
}

#[inline(always)]
pub fn poseidon2_permutation(state: &mut [GoldilocksField; State::STATE_WIDTH]) {
    let mut state_vec = State::from_field_array(*state);
    state_vec.poseidon2_permutation();
    *state = state_vec.as_field_array();
}

#[cfg(test)]
mod test {

    use crate::field::rand_from_rng;
    use crate::field::{goldilocks::GoldilocksField, Field};
    use crate::implementations::poseidon2::State;
    use crate::implementations::poseidon_goldilocks_naive;
    use crate::implementations::suggested_mds;

    //test for apply_round_constants
    #[test]
    fn test_apply_round_constants() {
        let mut rng = rand::thread_rng();
        let mut state = [GoldilocksField::ONE; 12];

        for i in 0..state.len() {
            state[i] = rand_from_rng(&mut rng);
        }
        dbg!(state);

        let mut state_ref = state;
        poseidon_goldilocks_naive::apply_round_constants(&mut state_ref, 0);

        let mut state_vec = State::from_field_array(state);
        state_vec.apply_round_constants(0);

        // dbg!(&state_vec);

        assert_eq!(state_ref, state_vec.as_field_array());
    }

    //test for apply_non_linearity
    #[test]
    fn test_apply_non_linearity() {
        let mut rng = rand::thread_rng();
        let mut state = [GoldilocksField::ONE; 12];

        for i in 0..state.len() {
            state[i] = rand_from_rng(&mut rng);
        }
        dbg!(state);

        let mut state_ref = state;
        for i in 0..12 {
            poseidon_goldilocks_naive::apply_non_linearity(&mut state_ref[i]);
        }

        let mut state_vec = State::from_field_array(state);
        state_vec.apply_non_linearity();

        // dbg!(&state_vec);

        assert_eq!(state_ref, state_vec.as_field_array());
    }

    //test for suggested_mds_mul
    #[test]
    fn test_suggested_mds_mul() {
        let mut rng = rand::thread_rng();
        let mut state = [GoldilocksField::ONE; 12];

        for i in 0..state.len() {
            // state[i] = GoldilocksField(1);// rand_from_rng(&mut rng);
            state[i] = GoldilocksField(i as u64 + 1);// rand_from_rng(&mut rng);
        }
        dbg!(state);

        let mut state_ref = state;
        suggested_mds::suggested_mds_mul(&mut state_ref);

        let mut state_vec = State::from_field_array(state);
        state_vec.suggested_mds_mul();

        // dbg!(&state_vec);

        assert_eq!(state_ref, state_vec.as_field_array());
    }

    //test for poseidon2_permutation
    #[test]
    fn test_poseidon2_permutation() {
        let mut rng = rand::thread_rng();
        let mut state = [GoldilocksField::ONE; 12];

        for i in 0..state.len() {
            state[i] = rand_from_rng(&mut rng);
        }

        let state = [GoldilocksField(GoldilocksField::ORDER - 1); 12];
        dbg!(state);

        let mut state_ref = State::from_field_array(state);
        State::poseidon2_permutation(&mut state_ref);

        let mut state_vec = State::from_field_array(state);
        state_vec.poseidon2_permutation();

        assert_eq!(state_ref, state_vec);
    }
}
