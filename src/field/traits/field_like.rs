use std::alloc::Global;

use crate::field::{ExtensionField, FieldExtension};
use crate::worker::Worker;
use crate::{
    cs::{implementations::utils::precompute_twiddles_for_fft, traits::GoodAllocator},
    field::{Field, PrimeField, SmallField},
};

pub trait TrivialContext: 'static + Send + Sync + Clone + Copy + std::fmt::Debug {
    fn placeholder() -> Self;
}

impl TrivialContext for () {
    #[inline(always)]
    fn placeholder() -> Self {}
}

// for some cases we want to be abstract not over algebraic properties of the field, but also
// from some larger scope of abstract function signatures

// So this is largely a duplicate of PrimeField, but also can capture a "context" value
// We do not need constness here
pub trait PrimeFieldLike:
    'static
    + Clone
    + Copy
    + std::fmt::Display
    + std::fmt::Debug
    + std::hash::Hash
    + std::marker::Send
    + std::marker::Sync
{
    // context for all math ops
    type Base: PrimeFieldLike;
    type Context;
    // identities
    fn zero(ctx: &mut Self::Context) -> Self;
    fn one(ctx: &mut Self::Context) -> Self;
    fn minus_one(ctx: &mut Self::Context) -> Self;
    // Arithmetics. Expressed in mutable way. It would not matter in after inlining
    fn add_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self;
    fn sub_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self;
    fn mul_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self;
    fn square(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self;
    fn negate(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self;
    fn double(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self;
    // infallible inverse
    fn inverse(&self, ctx: &mut Self::Context) -> Self;
    // constant creation
    fn constant(value: Self::Base, ctx: &mut Self::Context) -> Self;
    // exponentiate for short "constant" exponent
    fn pow_u64(&self, power: u64, ctx: &mut Self::Context) -> Self {
        let mut current = *self;
        let mut product = Self::one(ctx);

        let mut j = 0;
        let num_bits = crate::utils::num_bits_u64(power);
        while j < num_bits {
            if (power >> j & 1) != 0 {
                product.mul_assign(&current, ctx);
            }
            current.square(ctx);
            j += 1;
        }

        product
    }

    #[inline]
    fn mul_and_accumulate_into(acc: &mut Self, a: &Self, b: &Self, ctx: &mut Self::Context) {
        let mut tmp = *a;
        tmp.mul_assign(b, ctx);
        acc.add_assign(&tmp, ctx);
    }

    #[inline]
    fn small_pow(&mut self, pow: usize, ctx: &mut Self::Context) {
        match pow {
            3 => {
                let mut tmp = *self;
                tmp.square(ctx).mul_assign(&*self, ctx);

                *self = tmp;
            }
            5 => {
                let mut tmp = *self;
                tmp.square(ctx).square(ctx).mul_assign(&*self, ctx);

                *self = tmp;
            }
            7 => {
                let mut tmp = *self;
                tmp.square(ctx);
                let pow2 = tmp;
                tmp.square(ctx)
                    .mul_assign(&pow2, ctx)
                    .mul_assign(&*self, ctx);

                *self = tmp;
            }
            _ => {
                unimplemented!()
            }
        }
    }
}

// extension trait only useful in provers where benefits from vectorization are expected

pub trait PrimeFieldLikeVectorized: PrimeFieldLike<Context = ()> {
    type Twiddles<A: GoodAllocator>: Send + Sync + std::fmt::Debug;
    type InverseTwiddles<A: GoodAllocator>: Send + Sync + std::fmt::Debug;
    const SIZE_FACTOR: usize = std::mem::size_of::<Self>() / std::mem::size_of::<Self::Base>();
    // zero check
    fn is_zero(&self) -> bool;
    fn equals(&self, other: &Self) -> bool;

    // this will happen a lot
    fn mul_all_by_base(&'_ mut self, other: &Self::Base, ctx: &mut Self::Context) -> &'_ mut Self;

    // we can cast reference to base slice too
    fn as_base_elements(&self) -> &[Self::Base] {
        let as_slice = std::slice::from_ref(self);
        Self::slice_into_base_slice(as_slice)
    }

    // we assume that in many places we will want to convert
    // between base of vectorized

    fn slice_from_base_slice(input: &[Self::Base]) -> &[Self]; // no context here
    fn slice_into_base_slice(input: &[Self]) -> &[Self::Base]; // no context here

    fn slice_into_base_slice_mut(input: &mut [Self]) -> &mut [Self::Base]; // no context here

    fn vec_from_base_vec<A: GoodAllocator>(input: Vec<Self::Base, A>) -> Vec<Self, A>; // no context here
    fn vec_into_base_vec<A: GoodAllocator>(input: Vec<Self, A>) -> Vec<Self::Base, A>; // no context here
                                                                                       // and FFT to allow to switch to any accelerated implementations for free
    fn fft_natural_to_bitreversed<A: GoodAllocator>(
        input: &mut [Self],
        coset: Self::Base,
        twiddles: &Self::Twiddles<A>,
        ctx: &mut Self::Context,
    );
    fn ifft_natural_to_natural<A: GoodAllocator>(
        input: &mut [Self],
        coset: Self::Base,
        twiddles: &Self::InverseTwiddles<A>,
        ctx: &mut Self::Context,
    );

    fn precompute_forward_twiddles_for_fft<A: GoodAllocator>(
        fft_size: usize,
        worker: &Worker,
        ctx: &mut Self::Context,
    ) -> Self::Twiddles<A>;
    fn precompute_inverse_twiddles_for_fft<A: GoodAllocator>(
        fft_size: usize,
        worker: &Worker,
        ctx: &mut Self::Context,
    ) -> Self::InverseTwiddles<A>;
}

pub trait BaseField: PrimeField {}

impl<F: SmallField> BaseField for F {}

// default implementation under specialization
impl<F: BaseField> PrimeFieldLike for F {
    type Base = F;
    type Context = ();
    #[inline(always)]
    fn zero(_ctx: &mut Self::Context) -> Self {
        <Self as Field>::ZERO
    }
    #[inline(always)]
    fn one(_ctx: &mut Self::Context) -> Self {
        <Self as Field>::ONE
    }
    #[inline(always)]
    fn minus_one(_ctx: &mut Self::Context) -> Self {
        <Self as Field>::MINUS_ONE
    }
    #[inline(always)]
    fn add_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &'_ mut Self {
        <Self as Field>::add_assign(self, other)
    }
    #[inline(always)]
    fn sub_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &'_ mut Self {
        <Self as Field>::sub_assign(self, other)
    }
    #[inline(always)]
    fn mul_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &'_ mut Self {
        <Self as Field>::mul_assign(self, other)
    }
    #[inline(always)]
    fn square(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        <Self as Field>::square(self)
    }
    #[inline(always)]
    fn negate(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        <Self as Field>::negate(self)
    }
    #[inline(always)]
    fn double(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        <Self as Field>::double(self)
    }
    #[inline(always)]
    fn inverse(&self, _ctx: &mut Self::Context) -> Self {
        <Self as PrimeField>::inverse(self).expect("inverse must exist for PrimeFieldLike calls")
    }
    #[inline(always)]
    fn constant(value: F, _ctx: &mut Self::Context) -> Self {
        value
    }
}

impl<F: BaseField> PrimeFieldLikeVectorized for F {
    type Twiddles<A: GoodAllocator> = Vec<F, A>;
    type InverseTwiddles<A: GoodAllocator> = Vec<F, A>;
    #[inline(always)]
    fn is_zero(&self) -> bool {
        <Self as Field>::is_zero(self)
    }
    #[inline(always)]
    fn equals(&self, other: &Self) -> bool {
        self.eq(other)
    }
    #[inline(always)]
    fn mul_all_by_base(&'_ mut self, other: &F, _ctx: &mut Self::Context) -> &'_ mut Self {
        <Self as Field>::mul_assign(self, other)
    }
    #[inline(always)]
    fn slice_from_base_slice(input: &[Self::Base]) -> &[Self] {
        input
    }
    #[inline(always)]
    fn slice_into_base_slice(input: &[Self]) -> &[Self::Base] {
        input
    }
    #[inline(always)]
    fn slice_into_base_slice_mut(input: &mut [Self]) -> &mut [Self::Base] {
        input
    }
    #[inline(always)]
    fn vec_from_base_vec<A: GoodAllocator>(input: Vec<F, A>) -> Vec<Self, A> {
        input
    }
    #[inline(always)]
    fn vec_into_base_vec<A: GoodAllocator>(input: Vec<F, A>) -> Vec<Self, A> {
        input
    }
    #[inline(always)]
    fn fft_natural_to_bitreversed<A: GoodAllocator>(
        input: &mut [Self],
        coset: Self::Base,
        twiddles: &Self::Twiddles<A>,
        _ctx: &mut Self::Context,
    ) {
        crate::fft::fft_natural_to_bitreversed::<F>(input, coset, twiddles)
    }
    #[inline(always)]
    fn ifft_natural_to_natural<A: GoodAllocator>(
        input: &mut [Self],
        coset: Self::Base,
        twiddles: &Self::InverseTwiddles<A>,
        _ctx: &mut Self::Context,
    ) {
        crate::fft::ifft_natural_to_natural::<F>(input, coset, twiddles)
    }
    #[inline(always)]
    fn precompute_forward_twiddles_for_fft<A: GoodAllocator>(
        fft_size: usize,
        worker: &Worker,
        ctx: &mut Self::Context,
    ) -> Self::Twiddles<A> {
        precompute_twiddles_for_fft::<F, Self, A, false>(fft_size, worker, ctx)
    }
    #[inline(always)]
    fn precompute_inverse_twiddles_for_fft<A: GoodAllocator>(
        fft_size: usize,
        worker: &Worker,
        ctx: &mut Self::Context,
    ) -> Self::Twiddles<A> {
        precompute_twiddles_for_fft::<F, Self, A, true>(fft_size, worker, ctx)
    }
}

pub(crate) fn fft_natural_to_bitreversed<F: SmallField>(input: &mut [F], coset: F) {
    debug_assert!(input.len().is_power_of_two());
    let worker = Worker::new();
    let twiddles =
        precompute_twiddles_for_fft::<F, F, Global, false>(input.len(), &worker, &mut ());
    crate::fft::fft_natural_to_bitreversed::<F>(input, coset, &twiddles);
}

pub(crate) fn ifft_natural_to_natural<F: SmallField>(input: &mut [F], coset: F) {
    debug_assert!(input.len().is_power_of_two());
    let worker = Worker::new();
    let twiddles = precompute_twiddles_for_fft::<F, F, Global, true>(input.len(), &worker, &mut ());
    crate::fft::ifft_natural_to_natural::<F>(input, coset, &twiddles);
}
pub(crate) struct Flattener<'a, F: PrimeField, P: PrimeFieldLikeVectorized<Base = F>> {
    source: Vec<&'a [P::Base]>,
    idx: usize,
    take_by: usize,
    bound: usize,
    buffer: Vec<P::Base>,
}

impl<'a, F: PrimeField, P: PrimeFieldLikeVectorized<Base = F>> Flattener<'a, F, P> {
    pub(crate) fn new(source: impl ExactSizeIterator<Item = &'a [P]>, take_by: usize) -> Self {
        debug_assert!(source.len() > 0);
        debug_assert!(take_by.is_power_of_two());
        let buffer_size = source.len() * take_by;
        let source: Vec<&'a [F]> = source.map(|el| P::slice_into_base_slice(el)).collect();

        let bound = source[0].len();
        debug_assert!(bound > 0);
        debug_assert!(
            bound % take_by == 0,
            "want to take by {} element per list, but have upper bound of {}",
            take_by,
            bound
        );
        let buffer = Vec::with_capacity(buffer_size);

        Self {
            source,
            idx: 0,
            take_by,
            bound,
            buffer,
        }
    }

    pub(crate) fn num_iterations(&self) -> usize {
        (self.bound - self.idx) / self.take_by
    }

    pub(crate) fn next(&mut self) -> &[P::Base] {
        self.buffer.truncate(0);
        for el in self.source.iter() {
            self.buffer
                .extend_from_slice(&el[self.idx..(self.idx + self.take_by)]);
        }

        self.idx += self.take_by;

        &self.buffer
    }
}

impl<F: BaseField, E: FieldExtension<2, BaseField = F>> PrimeFieldLike for ExtensionField<F, 2, E> {
    type Base = F;
    type Context = ();
    #[inline(always)]
    fn zero(_ctx: &mut Self::Context) -> Self {
        <Self as Field>::ZERO
    }
    #[inline(always)]
    fn one(_ctx: &mut Self::Context) -> Self {
        <Self as Field>::ONE
    }
    #[inline(always)]
    fn minus_one(_ctx: &mut Self::Context) -> Self {
        <Self as Field>::MINUS_ONE
    }
    #[inline(always)]
    fn add_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &'_ mut Self {
        <Self as Field>::add_assign(self, other)
    }
    #[inline(always)]
    fn sub_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &'_ mut Self {
        <Self as Field>::sub_assign(self, other)
    }
    #[inline(always)]
    fn mul_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &'_ mut Self {
        <Self as Field>::mul_assign(self, other)
    }
    #[inline(always)]
    fn square(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        <Self as Field>::square(self)
    }
    #[inline(always)]
    fn negate(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        <Self as Field>::negate(self)
    }
    #[inline(always)]
    fn double(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        <Self as Field>::double(self)
    }
    #[inline(always)]
    fn inverse(&self, _ctx: &mut Self::Context) -> Self {
        <Self as PrimeField>::inverse(self).expect("inverse must exist for PrimeFieldLike calls")
    }
    #[inline(always)]
    fn constant(value: F, _ctx: &mut Self::Context) -> Self {
        Self {
            coeffs: [value, F::ZERO],
            _marker: std::marker::PhantomData,
        }
    }
    // #[inline(always)]
    // fn mul_by_base(&'_ mut self, other: &F, _ctx: &mut Self::Context) -> &'_ mut Self {
    //     self.coeffs[0].mul_assign(other);
    //     self.coeffs[1].mul_assign(other);

    //     self
    // }
}

// we also can define the same trait for extension as we did for Field

pub trait PrimeFieldLikeExtension<const DEGREE: usize>:
    'static
    + Clone
    + Copy
    + std::fmt::Display
    + std::fmt::Debug
    + std::hash::Hash
    + std::marker::Send
    + std::marker::Sync
{
    const TWO_ADICITY: usize;

    type BaseField: PrimeFieldLike;
    // generator's parametrization should also happen here
    fn multiplicative_generator_coeffs(
        ctx: &mut <Self::BaseField as PrimeFieldLike>::Context,
    ) -> [Self::BaseField; DEGREE];
    // norm
    fn compute_norm(
        el: &[Self::BaseField; DEGREE],
        ctx: &mut <Self::BaseField as PrimeFieldLike>::Context,
    ) -> Self::BaseField;
    // there is no &self paramter here as we do not expect runtime parametrization
    fn mul_by_non_residue(
        el: &mut Self::BaseField,
        ctx: &mut <Self::BaseField as PrimeFieldLike>::Context,
    );
}

#[derive(Clone, Copy, Hash)]
pub struct PrimeFieldLikeExtensionField<
    P: PrimeFieldLike,
    const DEGREE: usize,
    E: PrimeFieldLikeExtension<DEGREE, BaseField = P>,
> {
    pub coeffs: [P; DEGREE],
    pub _marker: std::marker::PhantomData<E>,
}

impl<P: PrimeFieldLike, E: PrimeFieldLikeExtension<2, BaseField = P>> std::fmt::Debug
    for PrimeFieldLikeExtensionField<P, 2, E>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "F2{{")?;
        writeln!(f, "{},", self.coeffs[0])?;
        writeln!(f, "{}", self.coeffs[1])?;
        writeln!(f, "}}")
    }
}

impl<P: PrimeFieldLike, E: PrimeFieldLikeExtension<2, BaseField = P>> std::fmt::Display
    for PrimeFieldLikeExtensionField<P, 2, E>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "F2{{")?;
        writeln!(f, "{},", self.coeffs[0])?;
        writeln!(f, "{}", self.coeffs[1])?;
        writeln!(f, "}}")
    }
}

impl<P: PrimeFieldLike, E: PrimeFieldLikeExtension<2, BaseField = P>> PrimeFieldLike
    for PrimeFieldLikeExtensionField<P, 2, E>
{
    type Base = P;
    type Context = <E::BaseField as PrimeFieldLike>::Context;
    #[inline(always)]
    fn zero(ctx: &mut Self::Context) -> Self {
        Self {
            coeffs: [P::zero(ctx), P::zero(ctx)],
            _marker: std::marker::PhantomData,
        }
    }
    #[inline(always)]
    fn one(ctx: &mut Self::Context) -> Self {
        Self {
            coeffs: [P::one(ctx), P::zero(ctx)],
            _marker: std::marker::PhantomData,
        }
    }
    #[inline(always)]
    fn minus_one(ctx: &mut Self::Context) -> Self {
        Self {
            coeffs: [P::minus_one(ctx), P::zero(ctx)],
            _marker: std::marker::PhantomData,
        }
    }
    #[inline]
    fn add_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        self.coeffs[0].add_assign(&other.coeffs[0], ctx);
        self.coeffs[1].add_assign(&other.coeffs[1], ctx);

        self
    }
    #[inline]
    fn sub_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        self.coeffs[0].sub_assign(&other.coeffs[0], ctx);
        self.coeffs[1].sub_assign(&other.coeffs[1], ctx);

        self
    }
    #[inline]
    fn mul_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        let mut v0 = self.coeffs[0];
        v0.mul_assign(&other.coeffs[0], ctx);
        let mut v1 = self.coeffs[1];
        v1.mul_assign(&other.coeffs[1], ctx);
        let t = self.coeffs[0];
        self.coeffs[1].add_assign(&t, ctx);
        let mut t0 = other.coeffs[0];
        t0.add_assign(&other.coeffs[1], ctx);
        self.coeffs[1].mul_assign(&t0, ctx);
        self.coeffs[1].sub_assign(&v0, ctx);
        self.coeffs[1].sub_assign(&v1, ctx);
        self.coeffs[0] = v0;
        E::mul_by_non_residue(&mut v1, ctx);
        self.coeffs[0].add_assign(&v1, ctx);

        self
    }
    #[inline]
    fn square(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        let mut v0 = self.coeffs[0];
        v0.sub_assign(&self.coeffs[1], ctx);
        let mut v3 = self.coeffs[0];
        let mut t0 = self.coeffs[1];
        E::mul_by_non_residue(&mut t0, ctx);
        v3.sub_assign(&t0, ctx);
        let mut v2 = self.coeffs[0];
        v2.mul_assign(&self.coeffs[1], ctx);
        v0.mul_assign(&v3, ctx);
        v0.add_assign(&v2, ctx);

        self.coeffs[1] = v2;
        self.coeffs[1].double(ctx);
        self.coeffs[0] = v0;
        E::mul_by_non_residue(&mut v2, ctx);
        self.coeffs[0].add_assign(&v2, ctx);

        self
    }
    #[inline(always)]
    fn negate(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        self.coeffs[0].negate(ctx);
        self.coeffs[1].negate(ctx);

        self
    }
    #[inline(always)]
    fn double(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        self.coeffs[0].double(ctx);
        self.coeffs[1].double(ctx);

        self
    }
    #[inline]
    fn inverse(&self, _ctx: &mut Self::Context) -> Self {
        todo!()
        // <Self as PrimeField>::inverse(self).expect("inverse must exist for PrimeFieldLike calls")
    }
    #[inline(always)]
    fn constant(value: Self::Base, ctx: &mut Self::Context) -> Self {
        Self {
            coeffs: [value, P::zero(ctx)],
            _marker: std::marker::PhantomData,
        }
    }
    // #[inline(always)]
    // fn mul_by_base(&'_ mut self, other: &Self::Base, ctx: &mut Self::Context) -> &'_ mut Self {
    //     self.coeffs[0].mul_assign(other, ctx);
    //     self.coeffs[1].mul_assign(other, ctx);

    //     self
    // }
}

impl<P: PrimeFieldLike, E: PrimeFieldLikeExtension<2, BaseField = P>>
    PrimeFieldLikeExtensionField<P, 2, E>
{
    #[inline(always)]
    pub fn mul_assign_by_base(
        &mut self,
        base: &<Self as PrimeFieldLike>::Base,
        ctx: &mut <E::BaseField as PrimeFieldLike>::Context,
    ) where
        P: PrimeFieldLike,
        E: PrimeFieldLikeExtension<2, BaseField = P>,
    {
        self.coeffs[0].mul_assign(base, ctx);
        self.coeffs[1].mul_assign(base, ctx);
    }
    #[inline(always)]
    pub const fn as_coeffs_in_base(&self) -> &[<Self as PrimeFieldLike>::Base; 2] {
        &self.coeffs
    }
    #[inline(always)]
    pub const fn into_coeffs_in_base(self) -> [<Self as PrimeFieldLike>::Base; 2] {
        self.coeffs
    }
}

#[inline]
pub fn mul_assign_vectorized_in_extension<
    F: PrimeField,
    P: PrimeFieldLikeVectorized<Base = F>,
    EXT: FieldExtension<2, BaseField = F>,
>(
    a_c0: &mut P,
    a_c1: &mut P,
    b_c0: &P,
    b_c1: &P,
    ctx: &mut (),
) {
    let mut v0 = *a_c0;
    v0.mul_assign(b_c0, ctx);
    let mut v1 = *a_c1;
    v1.mul_assign(b_c1, ctx);
    let t = *a_c0;
    a_c1.add_assign(&t, ctx);
    let mut t0 = *b_c0;
    t0.add_assign(b_c1, ctx);
    a_c1.mul_assign(&t0, ctx);
    a_c1.sub_assign(&v0, ctx);
    a_c1.sub_assign(&v1, ctx);
    *a_c0 = v0;
    v1.mul_all_by_base(&EXT::non_residue(), ctx);
    a_c0.add_assign(&v1, ctx);
}

#[inline]
pub fn mul_assign_in_extension<F: PrimeField, EXT: FieldExtension<2, BaseField = F>>(
    a_c0: &mut F,
    a_c1: &mut F,
    b_c0: &F,
    b_c1: &F,
) {
    let mut a = ExtensionField::<F, 2, EXT>::from_coeff_in_base([*a_c0, *a_c1]);
    let b = ExtensionField::<F, 2, EXT>::from_coeff_in_base([*b_c0, *b_c1]);
    crate::field::Field::mul_assign(&mut a, &b);
    let [c0, c1] = a.into_coeffs_in_base();
    *a_c0 = c0;
    *a_c1 = c1;
}
