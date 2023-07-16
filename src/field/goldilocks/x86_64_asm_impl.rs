use crate::cs::implementations::utils::precompute_twiddles_for_fft;
use crate::cs::traits::GoodAllocator;
use crate::field::{Field, PrimeField};
use crate::worker::Worker;
use std::ops::BitOr;
use std::usize;

use super::GoldilocksField;

use std::arch::x86_64::_mm512_add_epi64 as op_add;
use std::arch::x86_64::_mm512_cmpeq_epu64_mask as op_eq;
use std::arch::x86_64::_mm512_cmplt_epu64_mask as op_less_then;
use std::arch::x86_64::_mm512_load_epi64 as load_aligned;
use std::arch::x86_64::_mm512_loadu_epi64 as load_unaligned;
use std::arch::x86_64::_mm512_mask_blend_epi64 as op_select;
use std::arch::x86_64::_mm512_store_epi64 as store_aligned;
use std::arch::x86_64::_mm512_storeu_epi64 as store_unaligned;
use std::arch::x86_64::_mm512_sub_epi64 as op_sub;

use std::arch::x86_64::_mm512_set1_epi64 as op_set1;
use std::arch::x86_64::_mm512_setzero_epi32 as op_setzero;

use std::arch::x86_64::_mm256_load_epi32 as load_aligned_256_i32;
use std::arch::x86_64::_mm256_loadu_epi32 as load_unaligned_256_i32;
use std::arch::x86_64::_mm512_i32gather_epi64 as gather;
use std::arch::x86_64::_mm512_i32scatter_epi64 as scatter;

#[derive(Hash, Clone, Copy)]
#[repr(C, align(64))]
pub struct MixedGL(pub [GoldilocksField; 16]);

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
    pub const EPSILON: u64 = (1 << 32) - 1;

    #[inline(always)]
    pub fn new() -> Self {
        Self([GoldilocksField::ZERO; 16])
    }

    #[inline(always)]
    pub fn from_constant(value: GoldilocksField) -> Self {
        Self([value; 16])
    }

    #[inline(always)]
    pub fn from_array(value: [GoldilocksField; 16]) -> Self {
        Self(value)
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn to_reduced(&mut self) -> &mut Self {
        let mut ap = self.0.as_ptr() as *const u64;
        unsafe {
            for i in 0..2 {
                let a = load_aligned(ap as *const i64);
                let epsilon_vec = op_set1(Self::EPSILON as i64);
                let a_reduced = op_add(a, epsilon_vec);
                let cmp = op_less_then(a_reduced, epsilon_vec);
                let res = op_select(cmp, a, a_reduced);
                store_aligned(ap as *mut i64, res);

                ap = ap.offset(8);
            }
        }

        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub fn mul_constant_assign(&'_ mut self, other: &GoldilocksField) -> &mut Self {
        for i in 0..16 {
            self.0[i].mul_assign(&other);
        }

        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn mul_assign_impl(&mut self, other: &Self) -> &mut Self {
        for i in 0..16 {
            self.0[i].mul_assign(&other.0[i]);
        }

        self
    }

    unsafe fn add_assign_x86(this: *const u64, other: *const u64) {
        let a = load_aligned(this as *const i64);
        let b = load_aligned(other as *const i64);
        let epsilon_vec = op_set1(Self::EPSILON as i64);
        //additional reduction over b
        let b_reduced = op_add(b, epsilon_vec);
        let cmp = op_less_then(b_reduced, epsilon_vec);
        let b = op_select(cmp, b, b_reduced);
        //a+b
        let sum = op_add(a, b);
        let sum_reduced = op_add(sum, epsilon_vec);
        let cmp0 = op_less_then(sum_reduced, sum);
        let cmp1 = op_less_then(sum, a);
        let reduce_flag = cmp0.bitor(cmp1);
        let res = op_select(reduce_flag, sum, sum_reduced);
        store_aligned(this as *mut i64, res);
    }

    unsafe fn sub_assign_x86(this: *const u64, other: *const u64) {
        let a = load_aligned(this as *const i64);
        let b = load_aligned(other as *const i64);
        let epsilon_vec = op_set1(Self::EPSILON as i64);
        //additional reduction over b
        let b_reduced = op_add(b, epsilon_vec);
        let cmp = op_less_then(b_reduced, epsilon_vec);
        let b = op_select(cmp, b, b_reduced);
        //a-b
        let diff = op_sub(a, b);
        let diff_reduced = op_sub(diff, epsilon_vec);
        let cmp = op_less_then(a, b);
        let res = op_select(cmp, diff, diff_reduced);

        store_aligned(this as *mut i64, res);
    }

    unsafe fn negate_impl(this: *const u64) {
        let a = load_aligned(this as *const i64);
        let order_vec = op_set1(Self::ORDER as i64);
        let zero_vec = op_setzero();

        let is_zero = op_eq(a, zero_vec);
        let neg = op_sub(order_vec, a);
        let res = op_select(is_zero, neg, a);

        store_aligned(this as *mut i64, res);
    }

    pub unsafe fn butterfly_1x1_impl(&mut self) -> &mut Self {
        const OFFSET1: [u32; 8] = [0, 2, 4, 6, 8, 10, 12, 14];
        const OFFSET2: [u32; 8] = [1, 3, 5, 7, 9, 11, 13, 15];
        let offset1 = load_aligned_256_i32(OFFSET1.as_ptr() as *const i32);
        let offset2 = load_aligned_256_i32(OFFSET2.as_ptr() as *const i32);
        let u = gather::<8>(offset1, self.0.as_ptr() as *const u8);
        let v = gather::<8>(offset2, self.0.as_ptr() as *const u8);
        let epsilon_vec = op_set1(Self::EPSILON as i64);
        //additional reduction over v
        let v_reduced = op_add(v, epsilon_vec);
        let cmp = op_less_then(v_reduced, epsilon_vec);
        let v = op_select(cmp, v, v_reduced);
        // u + v
        let sum = op_add(u, v);
        let sum_reduced = op_add(sum, epsilon_vec);
        let cmp0 = op_less_then(sum_reduced, sum);
        let cmp1 = op_less_then(sum, u);
        let reduce_flag = cmp0.bitor(cmp1);
        let res1 = op_select(reduce_flag, sum, sum_reduced);
        // u - v
        let diff = op_sub(u, v);
        let diff_reduced = op_sub(diff, epsilon_vec);
        let cmp = op_less_then(u, v);
        let res2 = op_select(cmp, diff, diff_reduced);

        scatter::<8>(self.0.as_ptr() as *mut u8, offset1, res1);
        scatter::<8>(self.0.as_ptr() as *mut u8, offset2, res2);

        self
    }

    pub unsafe fn butterfly_2x2_impl(&mut self) -> &mut Self {
        const OFFSET1: [u32; 8] = [0, 1, 4, 5, 8, 9, 12, 13];
        const OFFSET2: [u32; 8] = [2, 3, 6, 7, 10, 11, 14, 15];
        let offset1 = load_aligned_256_i32(OFFSET1.as_ptr() as *const i32);
        let offset2 = load_aligned_256_i32(OFFSET2.as_ptr() as *const i32);
        let u = gather::<8>(offset1, self.0.as_ptr() as *const u8);
        let v = gather::<8>(offset2, self.0.as_ptr() as *const u8);
        let epsilon_vec = op_set1(Self::EPSILON as i64);
        //additional reduction over v
        let v_reduced = op_add(v, epsilon_vec);
        let cmp = op_less_then(v_reduced, epsilon_vec);
        let v = op_select(cmp, v, v_reduced);
        // u + v
        let sum = op_add(u, v);
        let sum_reduced = op_add(sum, epsilon_vec);
        let cmp0 = op_less_then(sum_reduced, sum);
        let cmp1 = op_less_then(sum, u);
        let reduce_flag = cmp0.bitor(cmp1);
        let res1 = op_select(reduce_flag, sum, sum_reduced);
        // u - v
        let diff = op_sub(u, v);
        let diff_reduced = op_sub(diff, epsilon_vec);
        let cmp = op_less_then(u, v);
        let res2 = op_select(cmp, diff, diff_reduced);

        scatter::<8>(self.0.as_ptr() as *mut u8, offset1, res1);
        scatter::<8>(self.0.as_ptr() as *mut u8, offset2, res2);

        self
    }

    pub unsafe fn butterfly_4x4_impl(&mut self) -> &mut Self {
        const OFFSET1: [u32; 8] = [0, 1, 2, 3, 8, 9, 10, 11];
        const OFFSET2: [u32; 8] = [4, 5, 6, 7, 12, 13, 14, 15];
        let offset1 = load_aligned_256_i32(OFFSET1.as_ptr() as *const i32);
        let offset2 = load_aligned_256_i32(OFFSET2.as_ptr() as *const i32);
        let u = gather::<8>(offset1, self.0.as_ptr() as *const u8);
        let v = gather::<8>(offset2, self.0.as_ptr() as *const u8);
        let epsilon_vec = op_set1(Self::EPSILON as i64);
        //additional reduction over v
        let v_reduced = op_add(v, epsilon_vec);
        let cmp = op_less_then(v_reduced, epsilon_vec);
        let v = op_select(cmp, v, v_reduced);
        // u + v
        let sum = op_add(u, v);
        let sum_reduced = op_add(sum, epsilon_vec);
        let cmp0 = op_less_then(sum_reduced, sum);
        let cmp1 = op_less_then(sum, u);
        let reduce_flag = cmp0.bitor(cmp1);
        let res1 = op_select(reduce_flag, sum, sum_reduced);
        // u - v
        let diff = op_sub(u, v);
        let diff_reduced = op_sub(diff, epsilon_vec);
        let cmp = op_less_then(u, v);
        let res2 = op_select(cmp, diff, diff_reduced);

        scatter::<8>(self.0.as_ptr() as *mut u8, offset1, res1);
        scatter::<8>(self.0.as_ptr() as *mut u8, offset2, res2);

        self
    }

    pub unsafe fn butterfly_8x8_impl(this: *const u64, other: *const u64) {
        debug_assert!(this.addr() % std::mem::align_of::<MixedGL>() == 0);
        debug_assert!(other.addr() % std::mem::align_of::<MixedGL>() == 0);

        let u = load_aligned(this as *const i64);
        let v = load_aligned(other as *const i64);
        let epsilon_vec = op_set1(Self::EPSILON as i64);
        //additional reduction over v
        let v_reduced = op_add(v, epsilon_vec);
        let cmp = op_less_then(v_reduced, epsilon_vec);
        let v = op_select(cmp, v, v_reduced);
        // u + v
        let sum = op_add(u, v);
        let sum_reduced = op_add(sum, epsilon_vec);
        let cmp0 = op_less_then(sum_reduced, sum);
        let cmp1 = op_less_then(sum, u);
        let reduce_flag = cmp0.bitor(cmp1);
        let res1 = op_select(reduce_flag, sum, sum_reduced);
        // u - v
        let diff = op_sub(u, v);
        let diff_reduced = op_sub(diff, epsilon_vec);
        let cmp = op_less_then(u, v);
        let res2 = op_select(cmp, diff, diff_reduced);

        store_aligned(this as *mut i64, res1);
        store_aligned(other as *mut i64, res2);
    }

    pub unsafe fn butterfly_16x16_impl(mut this: *mut u64, mut other: *mut u64) {
        Self::butterfly_8x8_impl(this, other);
        this = this.offset(8);
        other = other.offset(8);
        Self::butterfly_8x8_impl(this, other);
    }

    #[inline(always)]
    pub fn from_field_array(input: [GoldilocksField; 16]) -> Self {
        Self(input)
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
}

impl Default for MixedGL {
    fn default() -> Self {
        Self([GoldilocksField::ZERO; 16])
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
        Self([GoldilocksField::ZERO; 16])
    }
    #[inline(always)]
    fn one(_ctx: &mut Self::Context) -> Self {
        Self([GoldilocksField::ONE; 16])
    }
    #[inline(always)]
    fn minus_one(_ctx: &mut Self::Context) -> Self {
        Self([GoldilocksField::MINUS_ONE; 16])
    }

    fn add_assign(&mut self, other: &Self, _ctx: &mut Self::Context) -> &mut Self {
        let mut ap = self.0.as_ptr() as *const u64;
        let mut bp = other.0.as_ptr() as *const u64;
        unsafe {
            Self::add_assign_x86(ap, bp);
            ap = ap.offset(8);
            bp = bp.offset(8);
            Self::add_assign_x86(ap, bp);
        }

        self
    }

    fn sub_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &mut Self {
        let mut ap = self.0.as_ptr() as *const u64;
        let mut bp = other.0.as_ptr() as *const u64;
        unsafe {
            Self::sub_assign_x86(ap, bp);
            ap = ap.offset(8);
            bp = bp.offset(8);
            Self::sub_assign_x86(ap, bp);
        }

        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn mul_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &mut Self {
        Self::mul_assign_impl(self, other)
    }

    #[inline(always)]
    fn square(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        let t = *self;
        self.mul_assign(&t, _ctx);

        self
    }

    #[inline(always)]
    fn negate(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        let mut ap = self.0.as_ptr() as *const u64;
        unsafe {
            Self::negate_impl(ap);
            ap = ap.offset(8);
            Self::negate_impl(ap);
        }

        self
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
        for i in 0..16 {
            result.0[i] = PrimeField::inverse(&result.0[i]).expect("inverse must exist");
        }

        result
    }

    #[inline(always)]
    fn constant(value: Self::Base, _ctx: &mut Self::Context) -> Self {
        Self([value; 16])
    }
}

impl crate::field::traits::field_like::PrimeFieldLikeVectorized for MixedGL {
    type Twiddles<A: GoodAllocator> = Vec<GoldilocksField, A>;
    type InverseTwiddles<A: GoodAllocator> = Vec<GoldilocksField, A>;
    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.0 == [GoldilocksField::ZERO; 16]
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
        let result_len = input.len() / 16;
        unsafe { std::slice::from_raw_parts(input.as_ptr() as *mut Self, result_len) }
    }

    #[inline(always)]
    fn slice_into_base_slice(input: &[Self]) -> &[Self::Base] {
        let result_len = input.len() * 16;
        unsafe { std::slice::from_raw_parts(input.as_ptr() as *mut GoldilocksField, result_len) }
    }

    #[inline(always)]
    fn slice_into_base_slice_mut(input: &mut [Self]) -> &mut [Self::Base] {
        let result_len = input.len() * 16;
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

        crate::fft::fft_natural_to_bitreversed_mixedgl(input, coset, twiddles);
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

        crate::fft::ifft_natural_to_natural_mixedgl(input, coset, twiddles);
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
