//! A vectorized implementation of the poseidon2 state.
use crate::field::goldilocks::avx512_impl;
use crate::field::goldilocks::GoldilocksField;
use crate::field::traits::representation::U64Representable;
use crate::field::Field;
use std::arch::x86_64::{self, __m512i};
use std::usize;
use unroll::unroll_for_loops;

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
    pub const STATE_WIDTH: usize = poseidon_goldilocks_params::STATE_WIDTH;
    pub const TOTAL_NUM_ROUNDS: usize = poseidon_goldilocks_params::TOTAL_NUM_ROUNDS;
    pub const ALL_ROUND_CONSTANTS: [Self; Self::TOTAL_NUM_ROUNDS] = const {
        let mut constants_array =
            [Self([GoldilocksField::ZERO; Self::STATE_WIDTH]); Self::TOTAL_NUM_ROUNDS];
        let mut i = 0;
        while i < Self::TOTAL_NUM_ROUNDS {
            let mut t = [GoldilocksField::ZERO; 12];
            let mut j = 0;
            while j < 12 {
                t[j] = GoldilocksField::from_nonreduced_u64(
                    poseidon_goldilocks_params::ALL_ROUND_CONSTANTS[i * Self::STATE_WIDTH + j],
                );
                j += 1;
            }
            constants_array[i] = Self(t);
            i += 1;
        }
        constants_array
    };

    pub const ALL_INNER_ROUND_CONSTANTS: [u64; Self::TOTAL_NUM_ROUNDS] = const {
        let mut constants_array = [0u64; Self::TOTAL_NUM_ROUNDS];
        let mut i = 0;
        while i < Self::TOTAL_NUM_ROUNDS {
            constants_array[i] =
                poseidon_goldilocks_params::ALL_ROUND_CONSTANTS[i * Self::STATE_WIDTH] as u64;
            i += 1;
        }
        constants_array
    };
    pub const ALL_INNER_ROUND_CONSTANTS_AS_FIELD_ELEMENTS: [GoldilocksField;
        Self::TOTAL_NUM_ROUNDS] = const {
        // those are reduced, so we can just cast
        unsafe { std::mem::transmute(Self::ALL_INNER_ROUND_CONSTANTS) }
    };

    pub const M_I_DIAGONAL_ELEMENTS_MINUS_ONE: [Aligned; 2] = [
        Aligned([
            1 << 4,
            1 << 14,
            1 << 11,
            1 << 8,
            1 << 0,
            1 << 5,
            1 << 2,
            1 << 9,
        ]),
        Aligned([1 << 13, 1 << 6, 1 << 3, 1 << 12, 0, 0, 0, 0]),
    ];

    #[inline(always)]
    pub fn new() -> Self {
        Self([GoldilocksField::ZERO; 12])
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

    #[rustfmt::skip]
    #[inline(always)]
    #[unroll_for_loops]
    pub fn suggested_mds_mul(x: (__m512i, __m512i)) -> (__m512i, __m512i) {
        unsafe {
            let (x_0_7, x_8_11) = x;
            // Block 0, 2
            let ix_b2_repl = x86_64::_mm512_load_epi64(Aligned([0, 1, 2, 3, 0, 1, 2, 3]).as_u64_ptr());

            // NOTE: perhaps may be combined.
            let ix_odd_cmb    = x86_64::_mm512_load_epi64(Aligned([1, 3, 5, 7,  9, 11, 0, 0]).as_u64_ptr());
            let ix_odd_cmb_r  = x86_64::_mm512_load_epi64(Aligned([1, 3, 5, 7, 13, 15, 0, 0]).as_u64_ptr());
            let ix_even_cmb_r = x86_64::_mm512_load_epi64(Aligned([0, 2, 4, 6, 12, 14, 0, 0]).as_u64_ptr());

            // TODO: check if constructing with broadcast is faster. 
            let b3_mul_factor = x86_64::_mm512_load_epi64(Aligned([2, 2, 2, 2, 4, 4, 4, 4]).as_u64_ptr());
            let x_0_7_x1 = x_0_7;
            let x_0_7_x1 = avx512_impl::MixedGL::canonicalize(x_0_7_x1);
            let x_0_7_x1_lo = x86_64::_mm512_and_epi64(x_0_7_x1, x86_64::_mm512_set1_epi64(0xFFFFFFFF));
            let x_0_7_x1_hi = x86_64::_mm512_srli_epi64::<32>(x_0_7_x1);
            let x_8_11_x1 = x_8_11;
            let x_8_11_x1 = avx512_impl::MixedGL::canonicalize(x_8_11_x1);
            let x_8_11_x1 = x86_64::_mm512_permutexvar_epi64(ix_b2_repl, x_8_11_x1);
            let x_8_11_x1_lo = x86_64::_mm512_and_epi64(x_8_11_x1, x86_64::_mm512_set1_epi64(0xFFFFFFFF));
            let x_8_11_x1_hi = x86_64::_mm512_srli_epi64::<32>(x_8_11_x1);

            let x_0_7_x2_lo = x86_64::_mm512_add_epi64(x_0_7_x1_lo, x_0_7_x1_lo);
            let x_0_7_x2_hi = x86_64::_mm512_add_epi64(x_0_7_x1_hi, x_0_7_x1_hi);
            // Rust doesn't have the _mm512_mul_epu64, so we do 32 bit mul just once.
            let x_0_7_x4_lo = x86_64::_mm512_mul_epu32(x_0_7_x1_lo, x86_64::_mm512_set1_epi64(4));
            let x_0_7_x4_hi = x86_64::_mm512_mul_epu32(x_0_7_x1_hi, x86_64::_mm512_set1_epi64(4));

            // [ 2x_8-11, 4x8-11 ]

            let x_8_11_r_x2_x4_lo = x86_64::_mm512_mul_epu32(x_8_11_x1_lo, b3_mul_factor);
            let x_8_11_r_x2_x4_hi = x86_64::_mm512_mul_epu32(x_8_11_x1_hi, b3_mul_factor);

            // [ 4x_2i, 2x_2i+1 ]
            let x_0_7_x4_x2_lo = x86_64::_mm512_mask_blend_epi64(0b01010101, x_0_7_x2_lo, x_0_7_x4_lo);
            let x_0_7_x4_x2_hi = x86_64::_mm512_mask_blend_epi64(0b01010101, x_0_7_x2_hi, x_0_7_x4_hi);

            // [ 5x_2i, 3x_2i+1 ]
            let x_0_7_x5_x3_lo = x86_64::_mm512_add_epi64(x_0_7_x4_x2_lo, x_0_7_x1_lo);
            let x_0_7_x5_x3_hi = x86_64::_mm512_add_epi64(x_0_7_x4_x2_hi, x_0_7_x1_hi);

            // NOTE: can add 4 elements to the addition.
            // [ 3x8-11, 5x8-11 ]
            let x_8_11_r_x3_x5_lo = x86_64::_mm512_add_epi64(x_8_11_r_x2_x4_lo, x_8_11_x1_lo);
            let x_8_11_r_x3_x5_hi = x86_64::_mm512_add_epi64(x_8_11_r_x2_x4_hi, x_8_11_x1_hi);

            let x_odd_x2_lo = x86_64::_mm512_permutex2var_epi64(x_0_7_x2_lo, ix_odd_cmb, x_8_11_r_x2_x4_lo);
            let x_odd_x2_hi = x86_64::_mm512_permutex2var_epi64(x_0_7_x2_hi, ix_odd_cmb, x_8_11_r_x2_x4_hi);
            let x_odd_x3_lo = x86_64::_mm512_permutex2var_epi64(x_0_7_x5_x3_lo, ix_odd_cmb, x_8_11_r_x3_x5_lo);
            let x_odd_x3_hi = x86_64::_mm512_permutex2var_epi64(x_0_7_x5_x3_hi, ix_odd_cmb, x_8_11_r_x3_x5_hi);
            let x_odd_x4_lo = x86_64::_mm512_permutex2var_epi64(x_0_7_x4_lo, ix_odd_cmb_r, x_8_11_r_x2_x4_lo);
            let x_odd_x4_hi = x86_64::_mm512_permutex2var_epi64(x_0_7_x4_hi, ix_odd_cmb_r, x_8_11_r_x2_x4_hi);
            let x_even_x4_lo = x86_64::_mm512_permutex2var_epi64(x_0_7_x4_lo, ix_even_cmb_r, x_8_11_r_x2_x4_lo);
            let x_even_x4_hi = x86_64::_mm512_permutex2var_epi64(x_0_7_x4_hi, ix_even_cmb_r, x_8_11_r_x2_x4_hi);

            // NOTE: can fit 2 more additions
            let x_odd_x6_lo = x86_64::_mm512_add_epi64(x_odd_x2_lo, x_odd_x4_lo);
            let x_odd_x6_hi = x86_64::_mm512_add_epi64(x_odd_x2_hi, x_odd_x4_hi);
            // NOTE: can fit 2 more additions
            let x_odd_x7_lo = x86_64::_mm512_add_epi64(x_odd_x3_lo, x_odd_x4_lo);
            let x_odd_x7_hi = x86_64::_mm512_add_epi64(x_odd_x3_hi, x_odd_x4_hi);

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
            let q_0_7_l_lo = x86_64::_mm512_permutex2var_epi64(x_0_7_x1_lo, ix_0_7_q_l, x_0_7_x5_x3_lo);
            let q_0_7_l_hi = x86_64::_mm512_permutex2var_epi64(x_0_7_x1_hi, ix_0_7_q_l, x_0_7_x5_x3_hi);
            let q_0_7_r_lo = x86_64::_mm512_permutexvar_epi64(ix_0_7_q_r, x_0_7_x1_lo);
            let q_0_7_r_hi = x86_64::_mm512_permutexvar_epi64(ix_0_7_q_r, x_0_7_x1_hi);

            let q_0q_1q_lo = avx512_impl::MixedGL::add_no_double_overflow_64_64(q_0_7_l_lo, q_0_7_r_lo);
            let q_0q_1q_hi = avx512_impl::MixedGL::add_no_double_overflow_64_64(q_0_7_l_hi, q_0_7_r_hi);

            // [ 2q0,  2q1,  2q2, 2q3] 
            // [ 5x8, 1x11, 5x10, 1x9] 
            // [1x10, 1x10,  1x8, 1x8] 
            let ix_8_11_h1_l = x86_64::_mm512_load_epi64(Aligned([12, 3, 14, 1,  0,  0,  0,  0]).as_u64_ptr());
            let ix_8_11_h1_r = x86_64::_mm512_load_epi64(Aligned([ 2, 2,  0, 0, 0, 0, 0, 0]).as_u64_ptr());
            let r_8_11_h1_l_lo = x86_64::_mm512_permutex2var_epi64(x_8_11_x1_lo, ix_8_11_h1_l, x_8_11_r_x3_x5_lo);
            let r_8_11_h1_l_hi = x86_64::_mm512_permutex2var_epi64(x_8_11_x1_hi, ix_8_11_h1_l, x_8_11_r_x3_x5_hi);
            let r_8_11_h1_r_lo = x86_64::_mm512_permutex2var_epi64(x_8_11_x1_lo, ix_8_11_h1_r, q_0q_1q_lo);
            let r_8_11_h1_r_hi = x86_64::_mm512_permutex2var_epi64(x_8_11_x1_hi, ix_8_11_h1_r, q_0q_1q_hi);

            let __2q_lo = x86_64::_mm512_add_epi64(r_8_11_h1_l_lo, r_8_11_h1_r_lo);
            let __2q_hi = x86_64::_mm512_add_epi64(r_8_11_h1_l_hi, r_8_11_h1_r_hi);

            // [0w0, 0w2, 1w0, 1w2, 2w0, 2w2, _, _]
            let ix_0_11_h2_x7 = x86_64::_mm512_load_epi64(Aligned([1, 0, 3, 2, 5, 4, 0, 0]).as_u64_ptr());
            let x_odd_perm_x7_lo = x86_64::_mm512_permutexvar_epi64(ix_0_11_h2_x7, x_odd_x7_lo);
            let x_odd_perm_x7_hi = x86_64::_mm512_permutexvar_epi64(ix_0_11_h2_x7, x_odd_x7_hi);

            // NOTE: can fit 2 more additions
            let w02_lo = x86_64::_mm512_add_epi64(x_odd_perm_x7_lo, x_odd_x3_lo);
            let w02_hi = x86_64::_mm512_add_epi64(x_odd_perm_x7_hi, x_odd_x3_hi);

            // [0w1, 0w3, 1w1, 1w3, 2w1, 2w3, _, _]
            // NOTE: can fit 2 more additions
            let w13_lo = x86_64::_mm512_add_epi64(x_odd_x6_lo, x_even_x4_lo);
            let w13_hi = x86_64::_mm512_add_epi64(x_odd_x6_hi, x_even_x4_hi);

            // [0r0, 0r1, 0r2, 0r3, 1r0, 1r1, 1r2, 1r3]
            // [0w0, 0w1, 0w2, 0w3, 1w0, 1w1, 1w2, 1w3]
            let ix_w_0_7 = x86_64::_mm512_load_epi64(Aligned([1, 8, 0, 9, 3, 10, 2, 11]).as_u64_ptr());
            let w_0w_1w_lo = x86_64::_mm512_permutex2var_epi64(w02_lo, ix_w_0_7, w13_lo);
            let w_0w_1w_hi = x86_64::_mm512_permutex2var_epi64(w02_hi, ix_w_0_7, w13_hi);
            let __0r_1r_lo = x86_64::_mm512_add_epi64(w_0w_1w_lo, q_0q_1q_lo);
            let __0r_1r_hi = x86_64::_mm512_add_epi64(w_0w_1w_hi, q_0q_1q_hi);

            // NOTE: can fit 4 more additions
            // [2r0, 2r1, 2r2, 2r3] [01r0, 01r1, 01r2, 01r3]
            // [2w0, 2w1, 2w2, 2w3] [1r0, 1r1, 1r2, 1r3]
            // [2q0, 2q1, 2q2, 2q3] [0r0, 0r1, 0r2, 0r3]
            let ix_2w_l = x86_64::_mm512_load_epi64(Aligned([5, 12, 4, 13, 0, 0, 0, 0]).as_u64_ptr());
            let __2w_l_lo = x86_64::_mm512_permutex2var_epi64(w02_lo, ix_2w_l, w13_lo);
            let __2w_l_hi = x86_64::_mm512_permutex2var_epi64(w02_hi, ix_2w_l, w13_hi);
            let __2w_l_lo = x86_64::_mm512_mask_blend_epi64(0b11110000, __2w_l_lo, __0r_1r_lo);
            let __2w_l_hi = x86_64::_mm512_mask_blend_epi64(0b11110000, __2w_l_hi, __0r_1r_hi);
            let ix_2w_r = x86_64::_mm512_load_epi64(Aligned([0, 1, 2, 3, 8, 9, 10, 11]).as_u64_ptr());
            let __2w_r_lo = x86_64::_mm512_permutex2var_epi64(__2q_lo, ix_2w_r, __0r_1r_lo);
            let __2w_r_hi = x86_64::_mm512_permutex2var_epi64(__2q_hi, ix_2w_r, __0r_1r_hi);
            let __2r_01r_lo = x86_64::_mm512_add_epi64(__2w_l_lo, __2w_r_lo);
            let __2r_01r_hi = x86_64::_mm512_add_epi64(__2w_l_hi, __2w_r_hi);


            // [r0, r1, r2, r3, r0, r1, r2, r3]
            let ix_01r_2r = x86_64::_mm512_load_epi64(Aligned([4, 5, 6, 7, 0, 1, 2, 3]).as_u64_ptr());
            let __01r_2r_lo = x86_64::_mm512_permutexvar_epi64(ix_01r_2r, __2r_01r_lo);
            let __01r_2r_hi = x86_64::_mm512_permutexvar_epi64(ix_01r_2r, __2r_01r_hi);
            let __r_r_lo = x86_64::_mm512_add_epi64(__2r_01r_lo, __01r_2r_lo);
            let __r_r_hi = x86_64::_mm512_add_epi64(__2r_01r_hi, __01r_2r_hi);

            // [0f0, 0f1, 0f2, 0f3, 1f0, 1f1, 1f2, 1f3]
            let __0f_1f_lo = x86_64::_mm512_add_epi64(__r_r_lo, __0r_1r_lo);
            let __0f_1f_hi = x86_64::_mm512_add_epi64(__r_r_hi, __0r_1r_hi);

            let __2f_lo = x86_64::_mm512_maskz_add_epi64(0b00001111, __r_r_lo, __2r_01r_lo);
            let __2f_hi = x86_64::_mm512_maskz_add_epi64(0b00001111, __r_r_hi, __2r_01r_hi);

            let __0f_1f_hi_lo = x86_64::_mm512_slli_epi64::<32>(__0f_1f_hi);
            let __0f_1f_c_lo = x86_64::_mm512_add_epi64(__0f_1f_hi_lo, __0f_1f_lo);
            let mask = x86_64::_mm512_cmplt_epu64_mask(__0f_1f_c_lo, __0f_1f_lo);
            let carry = x86_64::_mm512_maskz_set1_epi64(mask, 1);
            let __0f_1f_c_hi = x86_64::_mm512_srli_epi64::<32>(__0f_1f_hi);
            let __0f_1f_c_hi = x86_64::_mm512_add_epi64(__0f_1f_c_hi, carry);

            let __0f_1f = avx512_impl::MixedGL::reduce128((__0f_1f_c_hi, __0f_1f_c_lo));

            let __2f_hi_lo = x86_64::_mm512_slli_epi64::<32>(__2f_hi);
            let __2f_c_lo = x86_64::_mm512_add_epi64(__2f_hi_lo, __2f_lo);
            let mask = x86_64::_mm512_cmplt_epu64_mask(__2f_c_lo, __2f_lo);
            let carry = x86_64::_mm512_maskz_set1_epi64(mask, 1);
            let __2f_c_hi = x86_64::_mm512_srli_epi64::<32>(__2f_hi);
            let __2f_c_hi = x86_64::_mm512_add_epi64(__2f_c_hi, carry);

            let __2f = avx512_impl::MixedGL::reduce128((__2f_c_hi, __2f_c_lo));

            (__0f_1f, __2f)
        }
    }

    #[inline(always)]
    #[unroll_for_loops]
    pub fn apply_round_constants(x: (__m512i, __m512i), round: usize) -> (__m512i, __m512i) {
        unsafe {
            let const_current = Self::ALL_ROUND_CONSTANTS[round];
            let (x_0_7, x_8_11) = x;
            let const_0_7 = x86_64::_mm512_load_epi64(&const_current.0[0] as *const _ as *const _);
            let const_8_11 = x86_64::_mm512_load_epi64(&const_current.0[8] as *const _ as *const _);

            let x_0_7 = avx512_impl::MixedGL::add_no_double_overflow_64_64(x_0_7, const_0_7);
            let x_8_11 = avx512_impl::MixedGL::add_no_double_overflow_64_64(x_8_11, const_8_11);

            (x_0_7, x_8_11)
        }
    }

    #[inline(always)]
    #[unroll_for_loops]
    pub fn apply_non_linearity(x: (__m512i, __m512i)) -> (__m512i, __m512i) {
        unsafe {
            let (t_0_7, t_8_11) = x;
            let x_0_7 = avx512_impl::MixedGL::reduce128(avx512_impl::MixedGL::square64(t_0_7));
            let x_8_11 = avx512_impl::MixedGL::reduce128(avx512_impl::MixedGL::square64(t_8_11));

            let t_0_7 =
                avx512_impl::MixedGL::reduce128(avx512_impl::MixedGL::mul64_64(t_0_7, x_0_7));
            let t_8_11 =
                avx512_impl::MixedGL::reduce128(avx512_impl::MixedGL::mul64_64(t_8_11, x_8_11));

            let x_0_7 = avx512_impl::MixedGL::reduce128(avx512_impl::MixedGL::square64(x_0_7));
            let x_8_11 = avx512_impl::MixedGL::reduce128(avx512_impl::MixedGL::square64(x_8_11));

            let x_0_7 =
                avx512_impl::MixedGL::reduce128(avx512_impl::MixedGL::mul64_64(x_0_7, t_0_7));
            let x_8_11 =
                avx512_impl::MixedGL::reduce128(avx512_impl::MixedGL::mul64_64(x_8_11, t_8_11));

            (x_0_7, x_8_11)
        }
    }

    #[inline(always)]
    fn full_round(x: (__m512i, __m512i), round_counter: &mut usize) -> (__m512i, __m512i) {
        let (x_0_7, x_8_11) = x;
        // add constants
        let (x_0_7, x_8_11) = State::apply_round_constants((x_0_7, x_8_11), *round_counter);
        // apply non-linearity
        let (x_0_7, x_8_11) = State::apply_non_linearity((x_0_7, x_8_11));
        // multiply by MDS
        let (x_0_7, x_8_11) = State::suggested_mds_mul((x_0_7, x_8_11));

        *round_counter += 1;

        (x_0_7, x_8_11)
    }

    #[inline(always)]
    #[unroll_for_loops]
    pub fn m_i_mul(x: (__m512i, __m512i)) -> (__m512i, __m512i) {
        unsafe {
            let (x_0_7, x_8_11) = x;
            let x_0_7_lo = x86_64::_mm512_and_epi64(x_0_7, x86_64::_mm512_set1_epi64(0xFFFFFFFF));
            let x_0_7_hi = x86_64::_mm512_srli_epi64::<32>(x_0_7);
            let x_8_11_lo = x86_64::_mm512_and_epi64(x_8_11, x86_64::_mm512_set1_epi64(0xFFFFFFFF));
            let x_8_11_hi = x86_64::_mm512_srli_epi64::<32>(x_8_11);

            let x_lo = x86_64::_mm512_add_epi64(x_0_7_lo, x_8_11_lo);
            let x_hi = x86_64::_mm512_add_epi64(x_0_7_hi, x_8_11_hi);

            let x_sum_lo = x86_64::_mm512_reduce_add_epi64(x_lo) as u128;
            let x_sum_hi = (x86_64::_mm512_reduce_add_epi64(x_hi) as u128) << 32;

            let x_sum = x_sum_lo + x_sum_hi;
            let x_sum = GoldilocksField::from_u128_with_reduction(x_sum);

            let m_0_7 =
                x86_64::_mm512_load_epi64(State::M_I_DIAGONAL_ELEMENTS_MINUS_ONE[0].as_u64_ptr());
            let m_8_11 =
                x86_64::_mm512_load_epi64(State::M_I_DIAGONAL_ELEMENTS_MINUS_ONE[1].as_u64_ptr());

            let xm_0_7 = avx512_impl::MixedGL::mul64_64(x_0_7, m_0_7);
            let xm_0_7 = avx512_impl::MixedGL::reduce128(xm_0_7);
            let xm_8_11 = avx512_impl::MixedGL::mul64_64(x_8_11, m_8_11);
            let xm_8_11 = avx512_impl::MixedGL::reduce128(xm_8_11);

            let x_sum = x86_64::_mm512_set1_epi64(x_sum.as_u64() as i64);

            let r_0_7 = avx512_impl::MixedGL::add_no_double_overflow_64_64(xm_0_7, x_sum);
            let r_8_11 = avx512_impl::MixedGL::add_no_double_overflow_64_64_maskz(
                0b00001111, xm_8_11, x_sum,
            );

            (r_0_7, r_8_11)
        }
    }

    #[inline(always)]
    fn partial_round_poseidon2(
        x: (__m512i, __m512i),
        round_counter: &mut usize,
    ) -> (__m512i, __m512i) {
        // add constant
        let (x_0_7, x_8_11) = x;
        let s = unsafe { *(&x_0_7 as *const _ as *const u64) };
        let mut s = GoldilocksField::from_nonreduced_u64(s);

        s.add_assign(&Self::ALL_INNER_ROUND_CONSTANTS_AS_FIELD_ELEMENTS[*round_counter]);
        // apply non-linearity to the single element
        let mut t = s;
        s.square();
        t.mul_assign(&s);
        s.square();
        s.mul_assign(&t);

        // Set `s` back to 0th place.
        let x_0_7 = unsafe { x86_64::_mm512_mask_set1_epi64(x_0_7, 1, s.as_u64() as i64) };

        // multiply by MDS
        let r = Self::m_i_mul((x_0_7, x_8_11));

        *round_counter += 1;

        r
    }

    #[inline(always)]
    #[unroll_for_loops]
    pub fn poseidon2_permutation(&mut self) {
        unsafe {
            let mut x_0_7 = x86_64::_mm512_load_epi64(&self.0[0] as *const _ as *const _);
            let mut x_8_11 =
                x86_64::_mm512_maskz_load_epi64(0b00001111, &self.0[8] as *const _ as *const _);

            (x_0_7, x_8_11) = Self::suggested_mds_mul((x_0_7, x_8_11));

            let mut round_counter = 0;
            for _i in 0..4 {
                (x_0_7, x_8_11) = Self::full_round((x_0_7, x_8_11), &mut round_counter);
            }

            for _i in 0..22 {
                (x_0_7, x_8_11) =
                    Self::partial_round_poseidon2((x_0_7, x_8_11), &mut round_counter);
            }

            for _i in 0..4 {
                (x_0_7, x_8_11) = Self::full_round((x_0_7, x_8_11), &mut round_counter);
            }

            x_0_7 = avx512_impl::MixedGL::canonicalize(x_0_7);
            x_8_11 = avx512_impl::MixedGL::canonicalize(x_8_11);

            x86_64::_mm512_store_epi64(&mut self.0[0] as *mut _ as *mut _, x_0_7);
            x86_64::_mm512_mask_store_epi64(&mut self.0[8] as *mut _ as *mut _, 0b00001111, x_8_11);
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

    use std::arch::x86_64;

    use itertools::Itertools;

    use crate::field::rand_from_rng;
    use crate::field::{goldilocks::GoldilocksField, Field};
    use crate::implementations::poseidon2::{state_generic_impl, State};
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
        unsafe {
            let x_0_7 = x86_64::_mm512_load_epi64(&state_vec.0[0] as *const _ as *const _);
            let x_8_11 = x86_64::_mm512_maskz_load_epi64(
                0b00001111,
                &state_vec.0[8] as *const _ as *const _,
            );
            let (x_0_7, x_8_11) = State::apply_round_constants((x_0_7, x_8_11), 0);
            x86_64::_mm512_store_epi64(&mut state_vec.0[0] as *mut _ as *mut _, x_0_7);
            x86_64::_mm512_mask_store_epi64(
                &mut state_vec.0[8] as *mut _ as *mut _,
                0b00001111,
                x_8_11,
            );
        }

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
        unsafe {
            let x_0_7 = x86_64::_mm512_load_epi64(&state_vec.0[0] as *const _ as *const _);
            let x_8_11 = x86_64::_mm512_maskz_load_epi64(
                0b00001111,
                &state_vec.0[8] as *const _ as *const _,
            );
            let (x_0_7, x_8_11) = State::apply_non_linearity((x_0_7, x_8_11));
            x86_64::_mm512_store_epi64(&mut state_vec.0[0] as *mut _ as *mut _, x_0_7);
            x86_64::_mm512_mask_store_epi64(
                &mut state_vec.0[8] as *mut _ as *mut _,
                0b00001111,
                x_8_11,
            );
        }

        // dbg!(&state_vec);

        assert_eq!(state_ref, state_vec.as_field_array());
    }

    #[test]
    fn test_poseidon2_partial_round() {
        let mut rng = rand::thread_rng();
        let mut state = [GoldilocksField::ONE; 12];

        for i in 0..state.len() {
            state[i] = rand_from_rng(&mut rng);
        }
        dbg!(state);

        let mut state_ref = state_generic_impl::State::from_field_array(state);
        // for i in 0..12 {
        //     poseidon_goldilocks_naive::(&mut state_ref[i]);
        // }
        state_ref.partial_round_poseidon2(&mut 1);

        let mut state_vec = State::from_field_array(state);
        unsafe {
            let x_0_7 = x86_64::_mm512_load_epi64(&state_vec.0[0] as *const _ as *const _);
            let x_8_11 = x86_64::_mm512_maskz_load_epi64(
                0b00001111,
                &state_vec.0[8] as *const _ as *const _,
            );
            let (x_0_7, x_8_11) = State::partial_round_poseidon2((x_0_7, x_8_11), &mut 1);
            x86_64::_mm512_store_epi64(&mut state_vec.0[0] as *mut _ as *mut _, x_0_7);
            x86_64::_mm512_mask_store_epi64(
                &mut state_vec.0[8] as *mut _ as *mut _,
                0b00001111,
                x_8_11,
            );
        }

        // dbg!(&state_vec);

        assert_eq!(state_ref.as_field_array(), state_vec.as_field_array());
    }

    //test for suggested_mds_mul
    #[test]
    fn test_suggested_mds_mul() {
        let mut rng = rand::thread_rng();
        let mut state = [GoldilocksField::ONE; 12];

        for i in 0..state.len() {
            state[i] = rand_from_rng(&mut rng);
        }
        dbg!(state);

        let mut state_ref = state;
        suggested_mds::suggested_mds_mul(&mut state_ref);

        let mut state_vec = State::from_field_array(state);
        unsafe {
            let x_0_7 = x86_64::_mm512_load_epi64(&state_vec.0[0] as *const _ as *const _);
            let x_8_11 = x86_64::_mm512_maskz_load_epi64(
                0b00001111,
                &state_vec.0[8] as *const _ as *const _,
            );
            let (x_0_7, x_8_11) = State::suggested_mds_mul((x_0_7, x_8_11));
            x86_64::_mm512_store_epi64(&mut state_vec.0[0] as *mut _ as *mut _, x_0_7);
            x86_64::_mm512_mask_store_epi64(
                &mut state_vec.0[8] as *mut _ as *mut _,
                0b00001111,
                x_8_11,
            );
        }

        // dbg!(&state_vec);

        assert_eq!(state_ref, state_vec.as_field_array());
    }

    #[test]
    fn test_i_m_mul() {
        let mut rng = rand::thread_rng();
        let mut state = [GoldilocksField::ONE; 12];

        for i in 0..state.len() {
            state[i] = rand_from_rng(&mut rng);
        }
        dbg!(state);

        let mut state_ref = state_generic_impl::State::from_field_array(state);
        // for i in 0..12 {
        //     poseidon_goldilocks_naive::(&mut state_ref[i]);
        // }
        state_generic_impl::State::m_i_mul(&mut state_ref.0);

        let mut state_vec = State::from_field_array(state);
        unsafe {
            let x_0_7 = x86_64::_mm512_load_epi64(&state_vec.0[0] as *const _ as *const _);
            let x_8_11 = x86_64::_mm512_maskz_load_epi64(
                0b00001111,
                &state_vec.0[8] as *const _ as *const _,
            );
            let (x_0_7, x_8_11) = State::m_i_mul((x_0_7, x_8_11));
            x86_64::_mm512_store_epi64(&mut state_vec.0[0] as *mut _ as *mut _, x_0_7);
            x86_64::_mm512_mask_store_epi64(
                &mut state_vec.0[8] as *mut _ as *mut _,
                0b00001111,
                x_8_11,
            );
        }

        // dbg!(&state_vec);

        assert_eq!(state_ref.as_field_array(), state_vec.as_field_array());
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

        // let mut state_ref = state.clone();// State::from_field_array(state);
        let mut state_ref = state_generic_impl::State::from_field_array(state);
        state_ref.poseidon2_permutation();
        // poseidon_goldilocks_naive::poseidon_permutation(&mut state_ref);
        // State::poseidon2_permutation(&mut state_ref);

        let mut state_vec = State::from_field_array(state);
        state_vec.poseidon2_permutation();

        assert_eq!(
            state_ref
                .as_field_array()
                .iter()
                .map(|x| x.to_reduced_u64())
                .collect_vec(),
            state_vec
                .as_field_array()
                .iter()
                .map(|x| x.to_reduced_u64())
                .collect_vec()
        );
    }
}
