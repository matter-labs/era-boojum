use crate::cs::implementations::utils::precompute_twiddles_for_fft;
use crate::cs::traits::GoodAllocator;
use crate::field::{Field, PrimeField};
use crate::worker::Worker;
use std::usize;

use super::GoldilocksField;

// we need max of an alignment of u64x4 and u64x8 in this implementation, so 64

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
        for i in 0..16 {
            let r = self.0[i].to_reduced_u64();
            self.0[i] = GoldilocksField(r);
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
    pub unsafe fn butterfly_1x1_impl(&mut self) -> &mut Self {
        for i in 0..8 {
            let u = self.0[i * 2];
            let v = self.0[i * 2 + 1];
            let mut tmp = u;
            tmp.sub_assign(&v);
            self.0[i * 2 + 1] = tmp;
            self.0[i * 2].add_assign(&v);
        }
        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub unsafe fn butterfly_2x2_impl(&mut self) -> &mut Self {
        for i in 0..4 {
            for j in 0..2 {
                let u = self.0[i * 4 + j];
                let v = self.0[i * 4 + 2 + j];
                let mut tmp = u;
                tmp.sub_assign(&v);
                self.0[i * 4 + 2 + j] = tmp;
                self.0[i * 4 + j].add_assign(&v);
            }
        }
        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub unsafe fn butterfly_4x4_impl(&mut self) -> &mut Self {
        for i in 0..2 {
            for j in 0..4 {
                let u = self.0[i * 8 + j];
                let v = self.0[i * 8 + 4 + j];
                let mut tmp = u;
                tmp.sub_assign(&v);
                self.0[i * 8 + 4 + j] = tmp;
                self.0[i * 8 + j].add_assign(&v);
            }
        }
        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub unsafe fn butterfly_8x8_impl(this: *const u64, other: *const u64) {
        debug_assert!(this.addr() % std::mem::align_of::<MixedGL>() == 0);
        debug_assert!(other.addr() % std::mem::align_of::<MixedGL>() == 0);

        let u = std::slice::from_raw_parts_mut(this as *mut GoldilocksField, 8);
        let v = std::slice::from_raw_parts_mut(other as *mut GoldilocksField, 8);
        for i in 0..8 {
            let mut tmp = u[i];
            tmp.sub_assign(&v[i]);
            u[i].add_assign(&v[i]);
            v[i] = tmp;
        }
    }

    pub unsafe fn butterfly_16x16_impl(mut this: *mut u64, mut other: *mut u64) {
        debug_assert!(this.addr() % std::mem::align_of::<MixedGL>() == 0);
        debug_assert!(other.addr() % std::mem::align_of::<MixedGL>() == 0);

        Self::butterfly_8x8_impl(this, other);
        this = this.offset(8);
        other = other.offset(8);
        Self::butterfly_8x8_impl(this, other);
    }

    #[inline(always)]
    pub fn from_field_array(input: [GoldilocksField; 16]) -> Self {
        Self(input)
    }

    #[inline(always)]
    pub fn vec_add_assign(a: &mut Vec<Self>, b: &Vec<Self>) {
        use crate::field::traits::field_like::PrimeFieldLike;
        for (a, b) in a.iter_mut().zip(b.iter()) {
            a.add_assign(b, &mut ());
        }
    }

    #[inline(always)]
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

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn add_assign(&mut self, other: &Self, _ctx: &mut Self::Context) -> &mut Self {
        for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
            Field::add_assign(a, b);
        }
        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn sub_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &mut Self {
        for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
            Field::sub_assign(a, b);
        }
        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn mul_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &mut Self {
        for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
            Field::mul_assign(a, b);
        }
        self
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
        for a in self.0.iter_mut() {
            Field::negate(a);
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
    #[unroll::unroll_for_loops]
    fn mul_all_by_base(&'_ mut self, other: &Self::Base, _ctx: &mut Self::Context) -> &'_ mut Self {
        for a in self.0.iter_mut() {
            Field::mul_assign(a, &other);
        }
        self
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
    use crate::log;
    use crate::utils::clone_respecting_allignment;

    #[test]
    fn test_mixedgl_negate() {
        let mut ctx = ();
        const POLY_SIZE: usize = 1 << 20;
        let mut rng = rand::thread_rng();
        log!("generic impl");

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
            aa.add_assign(&bb, &mut ctx);
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

        let a: Vec<GoldilocksField> = am.into_iter().map(|x| GoldilocksField(x)).collect();
        // let b: Vec<GoldilocksField> = bm.into_iter().map(|x| GoldilocksField(x)).collect();
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
