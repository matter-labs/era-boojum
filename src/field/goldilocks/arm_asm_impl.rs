use crate::cs::implementations::utils::precompute_twiddles_for_fft;
use crate::cs::traits::GoodAllocator;
use crate::field::{Field, PrimeField};
use crate::worker::Worker;
use packed_simd::shuffle;
use std::ops::{Add, BitOr, Sub};
use std::usize;

use super::GoldilocksField;

// we need max of an alignment of u64x4 and u64x8 in this implementation, so 64

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
#[repr(C, align(64))]
pub struct MixedGL(pub [GoldilocksField; 16]);

// we also need holder for SIMD targets, because u64x4 has smaller alignment than u64x8
#[derive(Clone, Copy)]
#[repr(C, align(64))]
struct U64x4Holder([packed_simd::u64x4; 4]);

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
    pub const EPSILON_VECTOR: packed_simd::u64x4 = packed_simd::u64x4::splat(Self::EPSILON);
    pub const EPSILON_VECTOR_D: packed_simd::u64x8 = packed_simd::u64x8::splat(Self::EPSILON);

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
    pub fn to_reduced(&mut self) -> &mut Self {
        let mut a_u64 = Self::as_u64x4_arrays(self);

        for i in 0..4 {
            let a = a_u64.0[i];
            let a_reduced = a.add(Self::EPSILON_VECTOR);
            let cmp = a_reduced.lt(Self::EPSILON_VECTOR);
            let res = cmp.select(a_reduced, a);

            a_u64.0[i] = res;
        }

        unsafe {
            *self = Self::from_u64x4_arrays(a_u64);
        }

        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub fn mul_constant_assign(&'_ mut self, other: &GoldilocksField) -> &mut Self {
        for i in 0..16 {
            self.0[i].mul_assign(other);
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

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn add_assign_impl(&mut self, other: &Self) -> &mut Self {
        let mut a_u64 = Self::as_u64x4_arrays(self);
        let b_u64 = Self::as_u64x4_arrays(other);

        for i in 0..4 {
            let a = a_u64.0[i];
            let b = b_u64.0[i];
            //additional reduction over b
            let b_reduced = b.add(Self::EPSILON_VECTOR);
            let cmp = b_reduced.lt(Self::EPSILON_VECTOR);
            let b = cmp.select(b_reduced, b);
            //a+b
            let sum = a.add(b);
            let sum_reduced = sum.add(Self::EPSILON_VECTOR);
            let cmp0 = sum_reduced.lt(sum);
            let cmp1 = sum.lt(a);
            let reduce_flag = cmp0.bitor(cmp1);
            let res = reduce_flag.select(sum_reduced, sum);

            a_u64.0[i] = res;
        }

        unsafe {
            *self = Self::from_u64x4_arrays(a_u64);
        }

        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn sub_assign_impl(&'_ mut self, other: &Self) -> &mut Self {
        let mut a_u64 = Self::as_u64x4_arrays(self);
        let b_u64 = Self::as_u64x4_arrays(other);

        for i in 0..4 {
            let a = a_u64.0[i];
            let b = b_u64.0[i];
            //additional reduction over b
            let b_reduced = b.add(Self::EPSILON_VECTOR);
            let cmp = b_reduced.lt(Self::EPSILON_VECTOR);
            let b = cmp.select(b_reduced, b);
            //a-b
            let diff = a.sub(b);
            let diff_reduced = diff.sub(Self::EPSILON_VECTOR);
            let cmp = a.lt(b);
            let res = cmp.select(diff_reduced, diff);

            a_u64.0[i] = res;
        }

        unsafe {
            *self = Self::from_u64x4_arrays(a_u64);
        }

        self
    }

    pub unsafe fn butterfly_1x1_impl(&mut self) -> &mut Self {
        let [part1, part2] = MixedGL::as_u64x8_arrays(&*self);
        let u: packed_simd::u64x8 = shuffle!(part1, part2, [0, 2, 4, 6, 8, 10, 12, 14]);
        let v: packed_simd::u64x8 = shuffle!(part1, part2, [1, 3, 5, 7, 9, 11, 13, 15]);
        //additional reduction over v
        let v_reduced = v.add(Self::EPSILON_VECTOR_D);
        let cmp = v_reduced.lt(Self::EPSILON_VECTOR_D);
        let v = cmp.select(v_reduced, v);
        // u + v
        let sum = u.add(v);
        let sum_reduced = sum.add(Self::EPSILON_VECTOR_D);
        let cmp0 = sum_reduced.lt(sum);
        let cmp1 = sum.lt(u);
        let reduce_flag = cmp0.bitor(cmp1);
        let res1 = reduce_flag.select(sum_reduced, sum);
        // u - v
        let diff = u.sub(v);
        let diff_reduced = diff.sub(Self::EPSILON_VECTOR_D);
        let cmp = u.lt(v);
        let res2 = cmp.select(diff_reduced, diff);

        let part1: packed_simd::u64x8 = shuffle!(res1, res2, [0, 8, 1, 9, 2, 10, 3, 11]);
        let part2: packed_simd::u64x8 = shuffle!(res1, res2, [4, 12, 5, 13, 6, 14, 7, 15]);

        *self = MixedGL::from_u64x8_arrays([part1, part2]);

        self
    }

    pub unsafe fn butterfly_2x2_impl(&mut self) -> &mut Self {
        let [part1, part2] = MixedGL::as_u64x8_arrays(&*self);
        let u: packed_simd::u64x8 = shuffle!(part1, part2, [0, 1, 4, 5, 8, 9, 12, 13]);
        let v: packed_simd::u64x8 = shuffle!(part1, part2, [2, 3, 6, 7, 10, 11, 14, 15]);
        //additional reduction over v
        let v_reduced = v.add(Self::EPSILON_VECTOR_D);
        let cmp = v_reduced.lt(Self::EPSILON_VECTOR_D);
        let v = cmp.select(v_reduced, v);
        // u + v
        let sum = u.add(v);
        let sum_reduced = sum.add(Self::EPSILON_VECTOR_D);
        let cmp0 = sum_reduced.lt(sum);
        let cmp1 = sum.lt(u);
        let reduce_flag = cmp0.bitor(cmp1);
        let res1 = reduce_flag.select(sum_reduced, sum);
        // u - v
        let diff = u.sub(v);
        let diff_reduced = diff.sub(Self::EPSILON_VECTOR_D);
        let cmp = u.lt(v);
        let res2 = cmp.select(diff_reduced, diff);

        let part1: packed_simd::u64x8 = shuffle!(res1, res2, [0, 1, 8, 9, 2, 3, 10, 11]);
        let part2: packed_simd::u64x8 = shuffle!(res1, res2, [4, 5, 12, 13, 6, 7, 14, 15]);

        *self = MixedGL::from_u64x8_arrays([part1, part2]);

        self
    }

    pub unsafe fn butterfly_4x4_impl(&mut self) -> &mut Self {
        let [part1, part2] = MixedGL::as_u64x8_arrays(&*self);
        let u: packed_simd::u64x8 = shuffle!(part1, part2, [0, 1, 2, 3, 8, 9, 10, 11]);
        let v: packed_simd::u64x8 = shuffle!(part1, part2, [4, 5, 6, 7, 12, 13, 14, 15]);
        //additional reduction over v
        let v_reduced = v.add(Self::EPSILON_VECTOR_D);
        let cmp = v_reduced.lt(Self::EPSILON_VECTOR_D);
        let v = cmp.select(v_reduced, v);
        // u + v
        let sum = u.add(v);
        let sum_reduced = sum.add(Self::EPSILON_VECTOR_D);
        let cmp0 = sum_reduced.lt(sum);
        let cmp1 = sum.lt(u);
        let reduce_flag = cmp0.bitor(cmp1);
        let res1 = reduce_flag.select(sum_reduced, sum);
        // u - v
        let diff = u.sub(v);
        let diff_reduced = diff.sub(Self::EPSILON_VECTOR_D);
        let cmp = u.lt(v);
        let res2 = cmp.select(diff_reduced, diff);

        let part1: packed_simd::u64x8 = shuffle!(res1, res2, [0, 1, 2, 3, 8, 9, 10, 11]);
        let part2: packed_simd::u64x8 = shuffle!(res1, res2, [4, 5, 6, 7, 12, 13, 14, 15]);

        *self = MixedGL::from_u64x8_arrays([part1, part2]);

        self
    }

    /// # Safety
    ///
    /// Pointers must be properly aligned for `MixedGL` type, should point to arrays of length 8, and should point
    /// to memory that can be mutated.
    /// No references to the same memory should exist when this function is called.
    /// Pointers should be different.
    pub unsafe fn butterfly_8x8_impl(this: *const u64, other: *const u64) {
        debug_assert!(this.addr() % std::mem::align_of::<MixedGL>() == 0);
        debug_assert!(other.addr() % std::mem::align_of::<MixedGL>() == 0);

        let u = std::slice::from_raw_parts_mut(this as *mut u64, 8);
        let v = std::slice::from_raw_parts_mut(other as *mut u64, 8);
        let a = packed_simd::u64x8::from_slice_aligned(u);
        let b = packed_simd::u64x8::from_slice_aligned(v);
        //additional reduction over b
        let b_reduced = b.add(Self::EPSILON_VECTOR_D);
        let cmp = b_reduced.lt(Self::EPSILON_VECTOR_D);
        let b = cmp.select(b_reduced, b);
        // u + v
        let sum = a.add(b);
        let sum_reduced = sum.add(Self::EPSILON_VECTOR_D);
        let cmp0 = sum_reduced.lt(sum);
        let cmp1 = sum.lt(a);
        let reduce_flag = cmp0.bitor(cmp1);
        let res1 = reduce_flag.select(sum_reduced, sum);
        // u - v
        let diff = a.sub(b);
        let diff_reduced = diff.sub(Self::EPSILON_VECTOR_D);
        let cmp = a.lt(b);
        let res2 = cmp.select(diff_reduced, diff);

        res1.write_to_slice_aligned(u);
        res2.write_to_slice_aligned(v);
    }

    /// # Safety
    ///
    /// Pointers must be properly aligned for `MixedGL` type, should point to arrays of length 16, and should point
    /// to memory that can be mutated.
    /// No references to the same memory should exist when this function is called.
    /// Pointers should be different.
    pub unsafe fn butterfly_16x16_impl(mut this: *mut u64, mut other: *mut u64) {
        debug_assert!(this.addr() % std::mem::align_of::<MixedGL>() == 0);
        debug_assert!(other.addr() % std::mem::align_of::<MixedGL>() == 0);

        Self::butterfly_8x8_impl(this, other);
        this = this.offset(8);
        other = other.offset(8);
        Self::butterfly_8x8_impl(this, other);
    }

    // pub unsafe fn butterfly_16x16_impl(
    //     this: &mut Self,
    //     other: &mut Self,
    // ) {
    //     let mut this_ptr = this.0.as_ptr() as *mut u64;
    //     let mut other_ptr = other.0.as_ptr() as *mut u64;

    //     debug_assert!(this_ptr.addr() % std::mem::align_of::<MixedGL>() == 0);
    //     debug_assert!(other_ptr.addr() % std::mem::align_of::<MixedGL>() == 0);

    //     Self::butterfly_8x8_impl(this_ptr, other_ptr);
    //     this_ptr = this_ptr.offset(8);
    //     other_ptr = other_ptr.offset(8);
    //     Self::butterfly_8x8_impl(this_ptr, other_ptr);
    // }

    #[inline(always)]
    pub fn from_field_array(input: [GoldilocksField; 16]) -> Self {
        Self(input)
    }

    #[inline(always)]
    fn as_u64x4_arrays(input: &Self) -> U64x4Holder {
        // this preserves an alignment
        unsafe { std::mem::transmute(*input) }
    }

    #[inline(always)]
    pub(crate) fn as_u64x8_arrays(input: &Self) -> [packed_simd::u64x8; 2] {
        // this preserves an alignment
        unsafe { std::mem::transmute(*input) }
    }

    #[inline(always)]
    unsafe fn from_u64x4_arrays(input: U64x4Holder) -> Self {
        // this preserves an alignment
        std::mem::transmute(input)
    }

    #[inline(always)]
    pub(crate) unsafe fn from_u64x8_arrays(input: [packed_simd::u64x8; 2]) -> Self {
        // this preserves an alignment
        std::mem::transmute(input)
    }

    #[inline(always)]
    pub fn vec_add_assign(a: &mut [Self], b: &[Self]) {
        use crate::field::traits::field_like::PrimeFieldLike;
        for (a, b) in a.iter_mut().zip(b.iter()) {
            a.add_assign(b, &mut ());
        }
    }

    #[inline(always)]
    pub fn vec_mul_assign(a: &mut [Self], b: &[Self]) {
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

    #[inline(always)]
    fn add_assign(&mut self, other: &Self, _ctx: &mut Self::Context) -> &mut Self {
        Self::add_assign_impl(self, other)
    }

    #[inline(always)]
    fn sub_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &mut Self {
        Self::sub_assign_impl(self, other)
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
    #[unroll::unroll_for_loops]
    fn negate(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        let mut a_u64 = Self::as_u64x4_arrays(self);

        for i in 0..4 {
            let a = a_u64.0[i];

            let is_zero = a.eq(packed_simd::u64x4::splat(0));
            let neg = packed_simd::u64x4::splat(Self::ORDER).sub(a);
            let res = is_zero.select(a, neg);

            a_u64.0[i] = res;
        }

        unsafe {
            *self = Self::from_u64x4_arrays(a_u64);
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
        self.eq(other)
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
            fft_size, worker, ctx,
        )
    }

    #[inline(always)]
    fn precompute_inverse_twiddles_for_fft<A: GoodAllocator>(
        fft_size: usize,
        worker: &Worker,
        ctx: &mut Self::Context,
    ) -> Self::Twiddles<A> {
        precompute_twiddles_for_fft::<GoldilocksField, GoldilocksField, A, true>(
            fft_size, worker, ctx,
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

    use rand::Rng;

    #[test]
    fn test_mixedgl_add_assign() {
        let mut ctx = ();
        const POLY_SIZE: usize = 1 << 24;
        let mut rng = rand::thread_rng();
        let _s = GoldilocksField(0x0000000001000000);

        // Generate random Vec<GoldilocksField>
        // let a: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| rand_from_rng(&mut rng)).collect();
        // let b: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| rand_from_rng(&mut rng)).collect();
        // let a: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| GoldilocksField(0x0000000000000001)).collect();
        // let b: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| GoldilocksField(0x0000000001000000)).collect();
        let b: Vec<GoldilocksField> = (0..POLY_SIZE)
            .map(|_| GoldilocksField(rng.gen_range(GoldilocksField::ORDER..u64::MAX)))
            .collect();
        let a: Vec<GoldilocksField> = (0..POLY_SIZE)
            .map(|_| GoldilocksField(rng.gen_range(GoldilocksField::ORDER..u64::MAX)))
            .collect();
        // let a: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| GoldilocksField(0xfffffffff67f1442)).collect();
        // let b: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| GoldilocksField(0xffffffff9c1d065d)).collect();

        // dbg!(&a);
        // dbg!(&b);

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
            aa.add_assign(bb, &mut ctx);
        }

        let avv = MixedGL::vec_into_base_vec(av);
        // for i in 0..avv.len() {
        //     assert_eq!(avv[i], ag[i], "error {}", i);
        // }

        // dbg!(&ag[0]);
        // dbg!(&avv[0]);

        assert_eq!(avv, ag);
    }

    #[test]
    fn test_mixedgl_sub_assign() {
        let mut ctx = ();
        const POLY_SIZE: usize = 1 << 20;
        let _rng = rand::thread_rng();

        // Generate random Vec<GoldilocksField>
        // let a: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| rand_from_rng(&mut rng)).collect();
        // let b: Vec<GoldilocksField> = (0..POLY_SIZE).map(|_| rand_from_rng(&mut rng)).collect();
        let a: Vec<GoldilocksField> = (0..POLY_SIZE)
            .map(|_| GoldilocksField(0x0000000000000001))
            .collect();
        let b: Vec<GoldilocksField> = (0..POLY_SIZE)
            .map(|_| GoldilocksField(0x0000000001000000))
            .collect();

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
            aa.sub_assign(bb, &mut ctx);
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
            aa.mul_assign(bb, &mut ctx);
        }

        // dbg!(&ag);
        // dbg!(&av);

        assert_eq!(ag, MixedGL::vec_into_base_vec(av));
    }

    #[test]
    fn test_mixedgl_butterfly16x16() {
        // let mut ctx = ();

        // let am: [u64;32] = [0x0001000000000000, 0x0000000000000001, 0x0001000000000000, 0x0000000000000001, 0x0000000000000000, 0xffffffff00000000, 0x0000000000000001, 0x0000ffffffffffff, 0x0000000000000000, 0x0001000000000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xfffeffff00000001, 0xfffeffff00000002, 0xfffeffff00000002,
        //     0x0000000000000000, 0x0000000000000001, 0x0000000000000000, 0x0001000000000001, 0xfffeffff00000001, 0xffffffff00000000, 0x0001000000000000, 0xfffeffff00000002, 0x0000000000000000, 0xfffeffff00000001, 0xffffffff00000000, 0x0000000000000001, 0x0000ffffffffffff, 0x0000000000000000, 0x0000000000000001, 0x0001000000000000];

        let am: [u64; 32] = [
            0x0001000000000000,
            0x0000000000000001,
            0x0001000000000000,
            0x0000000000000001,
            0x0000000000000000,
            0xffffffff00000000,
            0x0000000000000001,
            0x0000ffffffffffff,
            0x0000000000000000,
            0x0001000000000000,
            0xffffffff00000000,
            0xffffffff00000000,
            0xffffffff00000000,
            0xfffeffff00000001,
            0xfffeffff00000002,
            0xfffeffff00000002,
            0x0000000000000000,
            0xffffffff01000001,
            0x0000000000000000,
            0x0000010000ffff00,
            0xfffffeff00000101,
            0xfffffffeff000001,
            0x000000ffffffff00,
            0xfffffeff01000101,
            0x0000000000000000,
            0xfffffeff00000101,
            0xfffffffeff000001,
            0xffffffff01000001,
            0x000000fffeffff00,
            0x0000000000000000,
            0xffffffff01000001,
            0x000000ffffffff00,
        ];

        let a: Vec<GoldilocksField> = am.into_iter().map(GoldilocksField).collect();
        // let b: Vec<GoldilocksField> = bm.into_iter().map(GoldilocksField).collect();
        let _s = GoldilocksField(0x0000000001000000);

        // Test over Goldilocks
        let mut ag = a.clone();
        // let mut bg = b.clone();
        let distance_in_cache = 16;

        let mut j = 0;
        while j < 16 {
            let mut u = ag[j];
            let v = ag[j + distance_in_cache];
            // Field::mul_assign(&mut v, &s);
            Field::sub_assign(&mut u, &v);
            ag[j + distance_in_cache] = u;
            Field::add_assign(&mut ag[j], &v);

            j += 1;
        }

        let av: Vec<MixedGL> =
            MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
                &a,
            ));
        // let mut bv: Vec<MixedGL> = MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(&b));
        // let mut av = av[0];
        // let mut bv = bv[0];

        // Test over MixedGL
        // av[1].mul_constant_assign(&s);
        unsafe {
            MixedGL::butterfly_16x16_impl(
                av[0].0.as_ptr() as *mut u64,
                av[1].0.as_ptr() as *mut u64,
            );
        }
        // let mut u = av[0];
        // let mut v = av[1];
        // unsafe { MixedGL::butterfly_16x16_impl(&mut u, &mut v); }
        // av[0] = u;
        // av[1] = v;

        let ag =
            MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
                &ag,
            ));
        // let bg = MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(&bg));

        dbg!(&ag);
        dbg!(&av);

        // dbg!(&bg);
        // dbg!(&bv);

        assert_eq!(ag, av);
        // assert_eq!(bg, bv);
    }
}
