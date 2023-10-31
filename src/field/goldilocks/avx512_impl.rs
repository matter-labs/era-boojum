use crate::cs::implementations::utils::precompute_twiddles_for_fft;
use crate::cs::traits::GoodAllocator;
// use crate::field::traits::field_like::PrimeFieldLike;
use crate::field::{Field, PrimeField};
use crate::worker::Worker;
use std::mem::transmute;
use std::ops::BitOr;
use std::usize;

use super::GoldilocksField;

use std::arch::x86_64::_mm512_cmplt_epu64_mask;
use std::arch::x86_64::_mm512_load_epi64 as load_aligned;
use std::arch::x86_64::_mm512_loadu_epi64 as load_unaligned;
use std::arch::x86_64::_mm512_mask_blend_epi64 as op_select;
use std::arch::x86_64::_mm512_store_epi64 as store_aligned;
use std::arch::x86_64::_mm512_storeu_epi64 as store_unaligned;
use std::arch::x86_64::_mm512_sub_epi64;
use std::arch::x86_64::{
    __m512i, __mmask16, _mm512_add_epi64, _mm512_and_si512, _mm512_castps_si512,
    _mm512_castsi512_ps, _mm512_cmpge_epu64_mask, _mm512_mask_add_epi64, _mm512_mask_blend_epi32,
    _mm512_mask_sub_epi64, _mm512_movehdup_ps, _mm512_moveldup_ps, _mm512_mul_epu32,
    _mm512_permutex2var_epi64, _mm512_permutexvar_epi64, _mm512_shuffle_i64x2, _mm512_srli_epi64,
    _mm512_unpackhi_epi64, _mm512_unpacklo_epi64,
};
use std::arch::x86_64::{
    _mm512_cmpeq_epu64_mask as op_eq, _mm512_maskz_add_epi64, _mm512_slli_epi64,
};

use std::arch::x86_64::_mm512_set1_epi64 as op_set1;
use std::arch::x86_64::_mm512_setzero_epi32 as op_setzero;

use std::arch::x86_64::_mm256_load_epi32 as load_aligned_256_i32;
use std::arch::x86_64::_mm256_loadu_epi32 as load_unaligned_256_i32;
use std::arch::x86_64::_mm512_i32gather_epi64 as gather;
use std::arch::x86_64::_mm512_i32scatter_epi64 as scatter;

// Helper struct to guarantee alignment
#[derive(Hash, Clone, Copy)]
#[repr(C, align(64))]
struct AlignedArray([u64; 8]);

#[derive(Hash, Clone, Copy)]
#[repr(C, align(64))]
pub struct MixedGL(pub [GoldilocksField; 8]);

impl std::fmt::Debug for MixedGL {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl std::fmt::Display for MixedGL {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl MixedGL {
    pub const ORDER_BITS: usize = GoldilocksField::ORDER_BITS;
    pub const ORDER: u64 = GoldilocksField::ORDER;
    pub const TWO_ADICITY: usize = GoldilocksField::TWO_ADICITY;
    pub const T: u64 = (Self::ORDER - 1) >> Self::TWO_ADICITY;
    pub const BARRETT: u128 = 18446744078004518912; // 0x10000000100000000
                                                    // pub const EPSILON: u64 = (1 << 32) - 1;
    const FIELD_ORDER: __m512i = unsafe { transmute(AlignedArray([GoldilocksField::ORDER; 8])) };
    const EPSILON: __m512i =
        unsafe { transmute(AlignedArray([GoldilocksField::ORDER.wrapping_neg(); 8])) };
    const EPSILON_SCALAR: u64 = (1 << 32) - 1;
    const LO_32_BITS_MASK: __mmask16 = unsafe { transmute(0b0101010101010101u16) };

    #[inline(always)]
    pub fn new() -> Self {
        Self([GoldilocksField::ZERO; 8])
    }

    #[inline(always)]
    pub fn from_constant(value: GoldilocksField) -> Self {
        Self([value; 8])
    }

    #[inline(always)]
    pub fn from_array(value: [GoldilocksField; 8]) -> Self {
        Self(value)
    }

    #[inline(always)]
    pub fn from_field_array(input: [GoldilocksField; 8]) -> Self {
        Self(input)
    }

    #[inline(always)]
    pub fn from_v(x: __m512i) -> Self {
        unsafe { transmute(x) }
    }

    #[inline(always)]
    fn to_v(&self) -> __m512i {
        unsafe { transmute(*self) }
    }

    #[inline(always)]
    pub fn permute(&mut self, ix: &[u64; 8]) -> &mut Self {
        let ix = AlignedArray(*ix);
        let ix: __m512i = unsafe { transmute(ix) };
        let r = unsafe { _mm512_permutexvar_epi64(ix, self.to_v()) };

        *self = Self::from_v(r);
        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn to_reduced(&mut self) -> &mut Self {
        let r = unsafe { Self::canonicalize(self.to_v()) };
        *self = Self::from_v(r);
        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub fn mul_constant_assign(&'_ mut self, other: &GoldilocksField) -> &mut Self {
        let other = MixedGL::from_constant(*other);
        self.mul_assign_impl(&other);

        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn mul_assign_impl(&mut self, other: &Self) -> &mut Self {
        let r = unsafe { Self::reduce128(Self::mul64_64(self.to_v(), other.to_v())) };
        *self = Self::from_v(r);
        self
    }

    #[inline]
    unsafe fn negate_impl(y: __m512i) -> __m512i {
        _mm512_sub_epi64(Self::FIELD_ORDER, Self::canonicalize(y))
    }

    #[inline(always)]
    pub fn interleave(&self, other: Self, block_len: usize) -> (Self, Self) {
        let (v0, v1) = (self.to_v(), other.to_v());
        let (res0, res1) = match block_len {
            1 => unsafe { Self::interleave1(v0, v1) },
            2 => unsafe { Self::interleave2(v0, v1) },
            4 => unsafe { Self::interleave4(v0, v1) },
            8 => (v0, v1),
            _ => panic!("unsupported block_len"),
        };
        (Self::from_v(res0), Self::from_v(res1))
    }

    #[inline(always)]
    unsafe fn interleave1(x: __m512i, y: __m512i) -> (__m512i, __m512i) {
        let a = _mm512_unpacklo_epi64(x, y);
        let b = _mm512_unpackhi_epi64(x, y);
        (a, b)
    }

    const INTERLEAVE2_IDX_A: __m512i = unsafe {
        transmute(AlignedArray([
            0o00u64, 0o01u64, 0o10u64, 0o11u64, 0o04u64, 0o05u64, 0o14u64, 0o15u64,
        ]))
    };
    const INTERLEAVE2_IDX_B: __m512i = unsafe {
        transmute(AlignedArray([
            0o02u64, 0o03u64, 0o12u64, 0o13u64, 0o06u64, 0o07u64, 0o16u64, 0o17u64,
        ]))
    };

    #[inline(always)]
    unsafe fn interleave2(x: __m512i, y: __m512i) -> (__m512i, __m512i) {
        let a = _mm512_permutex2var_epi64(x, Self::INTERLEAVE2_IDX_A, y);
        let b = _mm512_permutex2var_epi64(x, Self::INTERLEAVE2_IDX_B, y);
        (a, b)
    }

    #[inline(always)]
    unsafe fn interleave4(x: __m512i, y: __m512i) -> (__m512i, __m512i) {
        let a = _mm512_shuffle_i64x2::<0x44>(x, y);
        let b = _mm512_shuffle_i64x2::<0xee>(x, y);
        (a, b)
    }

    pub unsafe fn butterfly_1x1_impl(&mut self) -> &mut Self {
        // unreachable!("This implementation is only used by fft that uses 8x8 butterfly");
        const OFFSET1: [u32; 8] = [0, 2, 4, 6, 8, 10, 12, 14];
        const OFFSET2: [u32; 8] = [1, 3, 5, 7, 9, 11, 13, 15];
        let offset1 = load_aligned_256_i32(OFFSET1.as_ptr() as *const i32);
        let offset2 = load_aligned_256_i32(OFFSET2.as_ptr() as *const i32);
        let u = gather::<8>(offset1, self.0.as_ptr() as *const u8);
        let v = gather::<8>(offset2, self.0.as_ptr() as *const u8);
        let epsilon_vec = op_set1(Self::EPSILON_SCALAR as i64);
        //additional reduction over v
        let v_reduced = _mm512_add_epi64(v, epsilon_vec);
        let cmp = _mm512_cmplt_epu64_mask(v_reduced, epsilon_vec);
        let v = op_select(cmp, v, v_reduced);
        // u + v
        let sum = _mm512_add_epi64(u, v);
        let sum_reduced = _mm512_add_epi64(sum, epsilon_vec);
        let cmp0 = _mm512_cmplt_epu64_mask(sum_reduced, sum);
        let cmp1 = _mm512_cmplt_epu64_mask(sum, u);
        let reduce_flag = cmp0.bitor(cmp1);
        let res1 = op_select(reduce_flag, sum, sum_reduced);
        // u - v
        let diff = _mm512_sub_epi64(u, v);
        let diff_reduced = _mm512_sub_epi64(diff, epsilon_vec);
        let cmp = _mm512_cmplt_epu64_mask(u, v);
        let res2 = op_select(cmp, diff, diff_reduced);

        scatter::<8>(self.0.as_ptr() as *mut u8, offset1, res1);
        scatter::<8>(self.0.as_ptr() as *mut u8, offset2, res2);

        self
    }

    pub unsafe fn butterfly_2x2_impl(&mut self) -> &mut Self {
        // unreachable!("This implementation is only used by fft that uses 8x8 butterfly");
        const OFFSET1: [u32; 8] = [0, 1, 4, 5, 8, 9, 12, 13];
        const OFFSET2: [u32; 8] = [2, 3, 6, 7, 10, 11, 14, 15];
        let offset1 = load_aligned_256_i32(OFFSET1.as_ptr() as *const i32);
        let offset2 = load_aligned_256_i32(OFFSET2.as_ptr() as *const i32);
        let u = gather::<8>(offset1, self.0.as_ptr() as *const u8);
        let v = gather::<8>(offset2, self.0.as_ptr() as *const u8);
        let epsilon_vec = op_set1(Self::EPSILON_SCALAR as i64);
        //additional reduction over v
        let v_reduced = _mm512_add_epi64(v, epsilon_vec);
        let cmp = _mm512_cmplt_epu64_mask(v_reduced, epsilon_vec);
        let v = op_select(cmp, v, v_reduced);
        // u + v
        let sum = _mm512_add_epi64(u, v);
        let sum_reduced = _mm512_add_epi64(sum, epsilon_vec);
        let cmp0 = _mm512_cmplt_epu64_mask(sum_reduced, sum);
        let cmp1 = _mm512_cmplt_epu64_mask(sum, u);
        let reduce_flag = cmp0.bitor(cmp1);
        let res1 = op_select(reduce_flag, sum, sum_reduced);
        // u - v
        let diff = _mm512_sub_epi64(u, v);
        let diff_reduced = _mm512_sub_epi64(diff, epsilon_vec);
        let cmp = _mm512_cmplt_epu64_mask(u, v);
        let res2 = op_select(cmp, diff, diff_reduced);

        scatter::<8>(self.0.as_ptr() as *mut u8, offset1, res1);
        scatter::<8>(self.0.as_ptr() as *mut u8, offset2, res2);

        self
    }

    pub unsafe fn butterfly_4x4_impl(&mut self) -> &mut Self {
        // unreachable!("This implementation is only used by fft that uses 8x8 butterfly");
        const OFFSET1: [u32; 8] = [0, 1, 2, 3, 8, 9, 10, 11];
        const OFFSET2: [u32; 8] = [4, 5, 6, 7, 12, 13, 14, 15];
        let offset1 = load_aligned_256_i32(OFFSET1.as_ptr() as *const i32);
        let offset2 = load_aligned_256_i32(OFFSET2.as_ptr() as *const i32);
        let u = gather::<8>(offset1, self.0.as_ptr() as *const u8);
        let v = gather::<8>(offset2, self.0.as_ptr() as *const u8);
        let epsilon_vec = op_set1(Self::EPSILON_SCALAR as i64);
        //additional reduction over v
        let v_reduced = _mm512_add_epi64(v, epsilon_vec);
        let cmp = _mm512_cmplt_epu64_mask(v_reduced, epsilon_vec);
        let v = op_select(cmp, v, v_reduced);
        // u + v
        let sum = _mm512_add_epi64(u, v);
        let sum_reduced = _mm512_add_epi64(sum, epsilon_vec);
        let cmp0 = _mm512_cmplt_epu64_mask(sum_reduced, sum);
        let cmp1 = _mm512_cmplt_epu64_mask(sum, u);
        let reduce_flag = cmp0.bitor(cmp1);
        let res1 = op_select(reduce_flag, sum, sum_reduced);
        // u - v
        let diff = _mm512_sub_epi64(u, v);
        let diff_reduced = _mm512_sub_epi64(diff, epsilon_vec);
        let cmp = _mm512_cmplt_epu64_mask(u, v);
        let res2 = op_select(cmp, diff, diff_reduced);

        scatter::<8>(self.0.as_ptr() as *mut u8, offset1, res1);
        scatter::<8>(self.0.as_ptr() as *mut u8, offset2, res2);

        self
    }

    #[inline(always)]
    pub unsafe fn butterfly_8x8_impl(this: *mut u64, other: *mut u64) {
        debug_assert!(this.addr() % std::mem::align_of::<MixedGL>() == 0);
        debug_assert!(other.addr() % std::mem::align_of::<MixedGL>() == 0);

        let u = &mut *(this as *mut MixedGL);
        let u_v = u.to_v();

        let v = &mut *(other as *mut MixedGL);
        let v_v = Self::canonicalize(v.to_v());

        let pos = Self::add_no_double_overflow_64_64(u_v, v_v);
        let neg = Self::sub_no_double_overflow_64_64(u_v, v_v);

        *u = Self::from_v(pos);
        *v = Self::from_v(neg);
    }

    pub unsafe fn butterfly_16x16_impl(mut this: *mut u64, mut other: *mut u64) {
        // unreachable!("This implementation is only used by fft that uses 8x8 butterfly");
        Self::butterfly_8x8_impl(this, other);
        this = this.offset(8);
        other = other.offset(8);
        Self::butterfly_8x8_impl(this, other);
    }

    pub fn vec_add_assign(a: &mut Vec<Self>, b: &Vec<Self>) {
        use crate::field::traits::field_like::PrimeFieldLike;
        for (a, b) in a.iter_mut().zip(b.iter()) {
            a.add_assign(b, &mut ());
        }
    }

    pub fn vec_mul_assign(a: &mut Vec<Self>, b: &Vec<Self>) {
        use crate::field::traits::field_like::PrimeFieldLike;
        for (a, b) in a.iter_mut().zip(b.iter()) {
            a.mul_assign(b, &mut ());
        }
    }

    #[inline(always)]
    pub(crate) unsafe fn add_no_double_overflow_64_64(x: __m512i, y: __m512i) -> __m512i {
        let res_wrapped = _mm512_add_epi64(x, y);
        let mask = _mm512_cmplt_epu64_mask(res_wrapped, y); // mask set if add overflowed
        let res = _mm512_mask_sub_epi64(res_wrapped, mask, res_wrapped, Self::FIELD_ORDER);
        res
    }

    pub(crate) unsafe fn add_no_double_overflow_64_64_maskz(
        mask: u8,
        x: __m512i,
        y: __m512i,
    ) -> __m512i {
        let res_wrapped = _mm512_maskz_add_epi64(mask, x, y);
        let mask = _mm512_cmplt_epu64_mask(res_wrapped, y) & mask; // mask set if add overflowed
        let res = _mm512_mask_sub_epi64(res_wrapped, mask, res_wrapped, Self::FIELD_ORDER);
        res
    }

    #[inline(always)]
    pub(crate) unsafe fn sub_no_double_overflow_64_64(x: __m512i, y: __m512i) -> __m512i {
        let mask = _mm512_cmplt_epu64_mask(x, y); // mask set if sub will underflow (x < y)
        let res_wrapped = _mm512_sub_epi64(x, y);
        let res = _mm512_mask_add_epi64(res_wrapped, mask, res_wrapped, Self::FIELD_ORDER);
        res
    }

    #[inline(always)]
    pub(crate) unsafe fn canonicalize(x: __m512i) -> __m512i {
        let mask = _mm512_cmpge_epu64_mask(x, Self::FIELD_ORDER);
        _mm512_mask_sub_epi64(x, mask, x, Self::FIELD_ORDER)
    }

    #[inline(always)]
    pub(crate) unsafe fn mul64_64(x: __m512i, y: __m512i) -> (__m512i, __m512i) {
        // We want to move the high 32 bits to the low position. The multiplication instruction ignores
        // the high 32 bits, so it's ok to just duplicate it into the low position. This duplication can
        // be done on port 5; bitshifts run on port 0, competing with multiplication.
        //   This instruction is only provided for 32-bit floats, not integers. Idk why Intel makes the
        // distinction; the casts are free and it guarantees that the exact bit pattern is preserved.
        // Using a swizzle instruction of the wrong domain (float vs int) does not increase latency
        // since Haswell.
        let x_hi = _mm512_castps_si512(_mm512_movehdup_ps(_mm512_castsi512_ps(x)));
        let y_hi = _mm512_castps_si512(_mm512_movehdup_ps(_mm512_castsi512_ps(y)));

        // All four pairwise multiplications
        let mul_ll = _mm512_mul_epu32(x, y);
        let mul_lh = _mm512_mul_epu32(x, y_hi);
        let mul_hl = _mm512_mul_epu32(x_hi, y);
        let mul_hh = _mm512_mul_epu32(x_hi, y_hi);

        // Bignum addition
        // Extract high 32 bits of mul_ll and add to mul_hl. This cannot overflow.
        let mul_ll_hi = _mm512_srli_epi64::<32>(mul_ll);
        let t0 = _mm512_add_epi64(mul_hl, mul_ll_hi);
        // Extract low 32 bits of t0 and add to mul_lh. Again, this cannot overflow.
        // Also, extract high 32 bits of t0 and add to mul_hh.
        let t0_lo = _mm512_and_si512(t0, Self::EPSILON);
        let t0_hi = _mm512_srli_epi64::<32>(t0);
        let t1 = _mm512_add_epi64(mul_lh, t0_lo);
        let t2 = _mm512_add_epi64(mul_hh, t0_hi);
        // Lastly, extract the high 32 bits of t1 and add to t2.
        let t1_hi = _mm512_srli_epi64::<32>(t1);
        let res_hi = _mm512_add_epi64(t2, t1_hi);

        // Form res_lo by combining the low half of mul_ll with the low half of t1 (shifted into high
        // position).
        let t1_lo = _mm512_castps_si512(_mm512_moveldup_ps(_mm512_castsi512_ps(t1)));
        let res_lo = _mm512_mask_blend_epi32(Self::LO_32_BITS_MASK, t1_lo, mul_ll);

        (res_hi, res_lo)
    }

    #[inline]
    pub(crate) unsafe fn square64(x: __m512i) -> (__m512i, __m512i) {
        // Get high 32 bits of x. See comment in mul64_64_s.
        let x_hi = _mm512_castps_si512(_mm512_movehdup_ps(_mm512_castsi512_ps(x)));

        // All pairwise multiplications.
        let mul_ll = _mm512_mul_epu32(x, x);
        let mul_lh = _mm512_mul_epu32(x, x_hi);
        let mul_hh = _mm512_mul_epu32(x_hi, x_hi);

        // Bignum addition, but mul_lh is shifted by 33 bits (not 32).
        let mul_ll_hi = _mm512_srli_epi64::<33>(mul_ll);
        let t0 = _mm512_add_epi64(mul_lh, mul_ll_hi);
        let t0_hi = _mm512_srli_epi64::<31>(t0);
        let res_hi = _mm512_add_epi64(mul_hh, t0_hi);

        // Form low result by adding the mul_ll and the low 31 bits of mul_lh (shifted to the high
        // position).
        let mul_lh_lo = _mm512_slli_epi64::<33>(mul_lh);
        let res_lo = _mm512_add_epi64(mul_ll, mul_lh_lo);

        (res_hi, res_lo)
    }

    #[inline(always)]
    pub(crate) unsafe fn reduce128(x: (__m512i, __m512i)) -> __m512i {
        let (hi0, lo0) = x;
        let hi_hi0 = _mm512_srli_epi64::<32>(hi0);
        let lo1 = Self::sub_no_double_overflow_64_64(lo0, hi_hi0);
        let t1 = _mm512_mul_epu32(hi0, Self::EPSILON);
        let lo2 = Self::add_no_double_overflow_64_64(lo1, t1);
        lo2
    }
}

impl Default for MixedGL {
    fn default() -> Self {
        Self([GoldilocksField::ZERO; 8])
    }
}

impl PartialEq for MixedGL {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for MixedGL {}

impl crate::field::traits::field_like::PrimeFieldLike for MixedGL {
    type Base = GoldilocksField;
    type Context = ();

    #[inline(always)]
    fn zero(_ctx: &mut Self::Context) -> Self {
        Self([GoldilocksField::ZERO; 8])
    }
    #[inline(always)]
    fn one(_ctx: &mut Self::Context) -> Self {
        Self([GoldilocksField::ONE; 8])
    }
    #[inline(always)]
    fn minus_one(_ctx: &mut Self::Context) -> Self {
        Self([GoldilocksField::MINUS_ONE; 8])
    }

    #[inline(always)]
    fn add_assign(&mut self, other: &Self, _ctx: &mut Self::Context) -> &mut Self {
        let x = self.to_v();
        let y = other.to_v();
        let r = unsafe { Self::add_no_double_overflow_64_64(x, Self::canonicalize(y)) };

        *self = Self::from_v(r);

        self
    }

    #[inline(always)]
    fn sub_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &mut Self {
        let x = self.to_v();
        let y = other.to_v();
        let r = unsafe { Self::sub_no_double_overflow_64_64(x, Self::canonicalize(y)) };

        *self = Self::from_v(r);

        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn mul_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &mut Self {
        let r = unsafe { Self::reduce128(Self::mul64_64(self.to_v(), other.to_v())) };
        *self = Self::from_v(r);
        self
    }

    #[inline(always)]
    fn square(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        let t = *self;
        self.mul_assign(&t, _ctx);

        self
    }

    #[inline(always)]
    fn negate(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        unsafe {
            let x = self.to_v();
            let r = Self::negate_impl(x);

            *self = Self::from_v(r);
            self
        }
    }

    #[inline(always)]
    fn double(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        let t = *self;
        self.add_assign(&t, _ctx);

        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn inverse(&self, _ctx: &mut Self::Context) -> Self {
        let mut result = *self;
        for i in 0..8 {
            result.0[i] = PrimeField::inverse(&result.0[i]).expect("inverse must exist");
        }

        result
    }

    #[inline(always)]
    fn constant(value: Self::Base, _ctx: &mut Self::Context) -> Self {
        Self([value; 8])
    }
}

impl crate::field::traits::field_like::PrimeFieldLikeVectorized for MixedGL {
    type Twiddles<A: GoodAllocator> = Vec<GoldilocksField, A>;
    type InverseTwiddles<A: GoodAllocator> = Vec<GoldilocksField, A>;
    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.0 == [GoldilocksField::ZERO; 8]
    }

    #[inline(always)]
    fn equals(&self, other: &Self) -> bool {
        self.eq(&other)
    }

    #[inline(always)]
    fn mul_all_by_base(&'_ mut self, other: &Self::Base, _ctx: &mut Self::Context) -> &'_ mut Self {
        Self::mul_constant_assign(self, other)
    }

    #[inline(always)]
    fn slice_from_base_slice(input: &[Self::Base]) -> &[Self] {
        if input.len() < Self::SIZE_FACTOR {
            panic!("too small input size to cast");
        }
        debug_assert!(input.len() % Self::SIZE_FACTOR == 0);
        debug_assert!(input.as_ptr().addr() % std::mem::align_of::<Self>() == 0);
        let result_len = input.len() / 8;
        unsafe { std::slice::from_raw_parts(input.as_ptr() as *mut Self, result_len) }
    }

    #[inline(always)]
    fn slice_into_base_slice(input: &[Self]) -> &[Self::Base] {
        let result_len = input.len() * 8;
        unsafe { std::slice::from_raw_parts(input.as_ptr() as *mut GoldilocksField, result_len) }
    }

    #[inline(always)]
    fn slice_into_base_slice_mut(input: &mut [Self]) -> &mut [Self::Base] {
        let result_len = input.len() * 8;
        unsafe {
            std::slice::from_raw_parts_mut(input.as_ptr() as *mut GoldilocksField, result_len)
        }
    }

    #[inline(always)]
    fn vec_from_base_vec<A: GoodAllocator>(input: Vec<Self::Base, A>) -> Vec<Self, A> {
        if input.len() < Self::SIZE_FACTOR {
            panic!("too small input size to cast");
        }
        let (ptr, len, capacity, allocator) = input.into_raw_parts_with_alloc();
        debug_assert!(ptr.addr() % std::mem::align_of::<Self>() == 0);
        debug_assert!(len % Self::SIZE_FACTOR == 0);
        debug_assert!(capacity % Self::SIZE_FACTOR == 0);

        unsafe {
            Vec::from_raw_parts_in(
                ptr as _,
                len / Self::SIZE_FACTOR,
                capacity / Self::SIZE_FACTOR,
                allocator,
            )
        }
    }

    #[inline(always)]
    fn vec_into_base_vec<A: GoodAllocator>(input: Vec<Self, A>) -> Vec<Self::Base, A> {
        let (ptr, len, capacity, allocator) = input.into_raw_parts_with_alloc();

        unsafe {
            Vec::from_raw_parts_in(
                ptr as _,
                len * Self::SIZE_FACTOR,
                capacity * Self::SIZE_FACTOR,
                allocator,
            )
        }
    }

    #[inline(always)]
    fn fft_natural_to_bitreversed<A: GoodAllocator>(
        input: &mut [Self],
        coset: Self::Base,
        twiddles: &Self::Twiddles<A>,
        _ctx: &mut Self::Context,
    ) {
        // let input = crate::utils::cast_check_alignment_ref_mut_unpack::<Self, GoldilocksField>(input);
        // crate::fft::fft_natural_to_bitreversed_cache_friendly(input, coset, twiddles);

        crate::fft::fft_natural_to_bitreversed_mixedgl_interleaving(input, coset, twiddles);
    }

    #[inline(always)]
    fn ifft_natural_to_natural<A: GoodAllocator>(
        input: &mut [Self],
        coset: Self::Base,
        twiddles: &Self::InverseTwiddles<A>,
        _ctx: &mut Self::Context,
    ) {
        // let input = crate::utils::cast_check_alignment_ref_mut_unpack::<Self, GoldilocksField>(input);
        // crate::fft::ifft_natural_to_natural_cache_friendly(input, coset, twiddles);

        crate::fft::ifft_natural_to_natural_mixedgl_interleaving(input, coset, twiddles);
    }

    #[inline(always)]
    fn precompute_forward_twiddles_for_fft<A: GoodAllocator>(
        fft_size: usize,
        worker: &Worker,
        ctx: &mut Self::Context,
    ) -> Self::Twiddles<A> {
        precompute_twiddles_for_fft::<GoldilocksField, GoldilocksField, A, false>(
            fft_size, &worker, ctx,
        )
    }

    #[inline(always)]
    fn precompute_inverse_twiddles_for_fft<A: GoodAllocator>(
        fft_size: usize,
        worker: &Worker,
        ctx: &mut Self::Context,
    ) -> Self::Twiddles<A> {
        precompute_twiddles_for_fft::<GoldilocksField, GoldilocksField, A, true>(
            fft_size, &worker, ctx,
        )
    }
}

#[cfg(test)]
mod test {

    use crate::field::goldilocks::MixedGL;
    use crate::field::rand_from_rng;
    use crate::field::traits::field_like::PrimeFieldLike;
    use crate::field::traits::field_like::PrimeFieldLikeVectorized;
    use crate::field::{goldilocks::GoldilocksField, Field};
    use crate::utils::clone_respecting_allignment;

    #[test]
    fn test_mixedgl_negate() {
        let mut ctx = ();
        const POLY_SIZE: usize = 1 << 20;
        let mut rng = rand::thread_rng();

        // Generate random Vec<GoldilocksField>
        let a: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| rand_from_rng(&mut rng)).collect();

        let mut ag = a.clone();

        for aa in ag.iter_mut() {
            Field::negate(aa);
        }

        let mut av: Vec<MixedGL> =
            MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
                &a,
            ));

        // Test over GLPS
        for aa in av.iter_mut() {
            aa.negate(&mut ctx);
        }

        assert_eq!(MixedGL::vec_into_base_vec(av), ag);
    }

    #[test]
    fn test_mixedgl_add_assign() {
        let mut ctx = ();
        const POLY_SIZE: usize = 1 << 20;
        let mut rng = rand::thread_rng();

        // Generate random Vec<GoldilocksField>
        let a: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| rand_from_rng(&mut rng)).collect();
        let b: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| rand_from_rng(&mut rng)).collect();
        // let a: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| GoldilocksField(2)).collect();
        // let b: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| GoldilocksField(2)).collect();

        let mut ag = a.clone();
        let bg = b.clone();

        for (aa, bb) in ag.iter_mut().zip(bg.iter()) {
            Field::add_assign(aa, bb);
        }

        let mut av: Vec<MixedGL> =
            MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
                &a,
            ));
        let bv: Vec<MixedGL> =
            MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
                &b,
            ));

        // Test over GLPS
        for (aa, bb) in av.iter_mut().zip(bv.iter()) {
            aa.add_assign(&bb, &mut ctx);
        }

        assert_eq!(MixedGL::vec_into_base_vec(av), ag);
    }

    #[test]
    fn test_mixedgl_sub_assign() {
        let mut ctx = ();
        const POLY_SIZE: usize = 1 << 20;
        let mut rng = rand::thread_rng();

        // Generate random Vec<GoldilocksField>
        let a: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| rand_from_rng(&mut rng)).collect();
        let b: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| rand_from_rng(&mut rng)).collect();

        // Test over Goldilocks
        let mut ag = a.clone();
        let bg = b.clone();

        for (aa, bb) in ag.iter_mut().zip(bg.iter()) {
            Field::sub_assign(aa, bb);
        }

        let mut av: Vec<MixedGL> =
            MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
                &a,
            ));
        let bv: Vec<MixedGL> =
            MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
                &b,
            ));

        // Test over GLPS
        for (aa, bb) in av.iter_mut().zip(bv.iter()) {
            aa.sub_assign(&bb, &mut ctx);
        }

        // dbg!(&ag);
        // dbg!(&av);

        assert_eq!(ag, MixedGL::vec_into_base_vec(av));
    }

    #[test]
    fn test_mixedgl_mul_assign() {
        let mut ctx = ();
        const POLY_SIZE: usize = 1 << 20;
        let mut rng = rand::thread_rng();

        // Generate random Vec<GoldilocksField>
        let a: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| rand_from_rng(&mut rng)).collect();
        let b: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| rand_from_rng(&mut rng)).collect();

        // Test over Goldilocks
        let mut ag = a.clone();
        let bg = b.clone();

        for (aa, bb) in ag.iter_mut().zip(bg.iter()) {
            Field::mul_assign(aa, bb);
        }

        let mut av: Vec<MixedGL> =
            MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
                &a,
            ));
        let bv: Vec<MixedGL> =
            MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
                &b,
            ));

        // Test over GLPS
        for (aa, bb) in av.iter_mut().zip(bv.iter()) {
            aa.mul_assign(&bb, &mut ctx);
        }

        // dbg!(&ag);
        // dbg!(&av);

        assert_eq!(ag, MixedGL::vec_into_base_vec(av));
    }
}
