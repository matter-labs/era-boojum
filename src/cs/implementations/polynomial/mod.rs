use crate::cs::traits::GoodAllocator;
use crate::field::traits::field_like::PrimeFieldLikeVectorized;
use crate::field::PrimeField;
use crate::utils::*;
use std::alloc::Global;

use super::fast_serialization::MemcopySerializable;
use super::*;

pub mod lde;

pub trait PolynomialForm:
    'static + Send + Sync + Clone + Copy + PartialEq + Eq + std::hash::Hash
{
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct MonomialForm;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LagrangeForm;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BitreversedLagrangeForm;

impl PolynomialForm for MonomialForm {}
impl PolynomialForm for LagrangeForm {}
impl PolynomialForm for BitreversedLagrangeForm {}

// Note: no SmallField here in the definition, but it will happen in implementations
#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Debug)]
#[serde(
    bound = "F: serde::Serialize + serde::de::DeserializeOwned, P: serde::Serialize + serde::de::DeserializeOwned"
)]
pub struct GenericPolynomial<
    F: PrimeField,
    FORM: PolynomialForm,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator = Global,
> {
    #[serde(serialize_with = "crate::utils::serialize_vec_with_allocator")]
    #[serde(deserialize_with = "crate::utils::deserialize_vec_with_allocator")]
    pub storage: Vec<P, A>,
    pub _marker: std::marker::PhantomData<(F, P, FORM)>,
}

impl<
        F: PrimeField,
        FORM: PolynomialForm,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
    > Clone for GenericPolynomial<F, FORM, P, A>
{
    #[inline(always)]
    fn clone(&self) -> Self {
        let storage = Vec::clone(&self.storage);

        Self {
            storage,
            _marker: std::marker::PhantomData,
        }
    }

    #[inline(always)]
    fn clone_from(&mut self, source: &Self) {
        Vec::clone_from(&mut self.storage, &source.storage);
    }
}

impl<
        F: PrimeField,
        FORM: PolynomialForm,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
    > PartialEq for GenericPolynomial<F, FORM, P, A>
{
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        P::slice_into_base_slice(&self.storage) == P::slice_into_base_slice(&other.storage)
    }
}

impl<
        F: PrimeField,
        FORM: PolynomialForm,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
    > Eq for GenericPolynomial<F, FORM, P, A>
{
}

impl<
        F: SmallField,
        FORM: PolynomialForm,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
    > MemcopySerializable for GenericPolynomial<F, FORM, P, A>
where
    Self: 'static,
{
    fn read_from_buffer<R: std::io::Read>(src: R) -> Result<Self, Box<dyn std::error::Error>> {
        let storage: Vec<P, A> = MemcopySerializable::read_from_buffer(src)?;
        let new = Self::from_storage(storage);

        Ok(new)
    }

    fn write_into_buffer<W: std::io::Write>(
        &self,
        dst: W,
    ) -> Result<(), Box<dyn std::error::Error>> {
        self.storage.write_into_buffer(dst)?;

        Ok(())
    }
}

impl<
        F: SmallField,
        FORM: PolynomialForm,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > MemcopySerializable for Vec<std::sync::Arc<GenericPolynomial<F, FORM, P, A>>, B>
where
    Self: 'static,
{
    fn write_into_buffer<W: std::io::Write>(
        &self,
        mut dst: W,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let outer_len_le_bytes = (self.len() as u64).to_le_bytes();
        dst.write_all(&outer_len_le_bytes).map_err(Box::new)?;

        for el in self.iter() {
            let inner: &GenericPolynomial<F, FORM, P, A> = el;
            MemcopySerializable::write_into_buffer(inner, &mut dst)?;
        }

        Ok(())
    }

    fn read_from_buffer<R: std::io::Read>(mut src: R) -> Result<Self, Box<dyn std::error::Error>> {
        let mut buffer = [0u8; 8];
        src.read_exact(&mut buffer).map_err(Box::new)?;
        let capacity = u64::from_le_bytes(buffer) as usize;

        assert!(capacity.is_power_of_two());

        let mut result = Vec::with_capacity_in(capacity, B::default());

        for _ in 0..capacity {
            let inner: GenericPolynomial<F, FORM, P, A> =
                MemcopySerializable::read_from_buffer(&mut src)?;
            result.push(std::sync::Arc::new(inner));
        }

        Ok(result)
    }
}

pub type Polynomial<F, FORM, A> = GenericPolynomial<F, FORM, F, A>;

impl<
        F: PrimeField,
        FORM: PolynomialForm,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
    > GenericPolynomial<F, FORM, P, A>
{
    #[inline]
    pub fn new() -> Self {
        Self {
            storage: Vec::new_in(A::default()),
            _marker: std::marker::PhantomData,
        }
    }

    pub fn pretty_compare(&self, other: &Self) {
        for (idx, (a, b)) in P::slice_into_base_slice(&self.storage)
            .iter()
            .zip(P::slice_into_base_slice(&other.storage).iter())
            .enumerate()
        {
            if a != b {
                panic!("Different at index {}: a = {}, b = {}", idx, a, b);
            }
        }
    }

    #[inline]
    pub(crate) fn from_storage(storage: Vec<P, A>) -> Self {
        debug_assert!(storage.as_ptr().addr() % std::mem::align_of::<P>() == 0);
        Self {
            storage,
            _marker: std::marker::PhantomData,
        }
    }

    #[inline]
    pub(crate) fn into_storage(self) -> Vec<P, A> {
        self.storage
    }

    #[inline]
    pub fn domain_size(&self) -> usize
    where
        P: PrimeFieldLikeVectorized<Base = F>,
    {
        // invariant over any vectorized cases
        let len = self.storage.len();
        if len.is_power_of_two() {
            len * P::SIZE_FACTOR
        } else {
            len.next_power_of_two() * P::SIZE_FACTOR
        }
    }

    #[inline]
    pub(crate) fn clone_respecting_allignment<U: Sized>(&self) -> Self {
        let buffer = clone_respecting_allignment::<_, U, _>(&self.storage);
        Self {
            storage: buffer,
            _marker: std::marker::PhantomData,
        }
    }

    pub(crate) fn chunks<B: GoodAllocator>(
        self: &std::sync::Arc<Self>,
        chunk_size: usize,
    ) -> Vec<GenericPolynomialChunk<F, FORM, P, A>, B> {
        let len = self.storage.len();
        let mut start = 0;
        let num_chunks = Worker::compute_num_chunks(len, chunk_size);
        let mut result = Vec::with_capacity_in(num_chunks, B::default());
        for _ in 0..num_chunks {
            let mut end = start + chunk_size;
            if end > len {
                end = len;
            }

            let chunk = GenericPolynomialChunk {
                over: std::sync::Arc::clone(self),
                range: start..end,
                _marker: std::marker::PhantomData,
            };

            result.push(chunk);

            start = end;
        }

        result
    }
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
    > GenericPolynomial<F, MonomialForm, P, A>
{
    pub fn chunk_into_subpolys_of_degree<B: GoodAllocator>(self, degree: usize) -> Vec<Self, B> {
        debug_assert!(self.domain_size() % degree == 0);
        debug_assert!(degree.is_power_of_two());

        let num_chunks = self.domain_size() / degree;

        let mut storage = self.storage;

        // there is no easy way to split the allocation
        let mut result = Vec::with_capacity_in(num_chunks, B::default());
        for _ in 0..num_chunks {
            let mut subchunk = Vec::with_capacity_in(degree / P::SIZE_FACTOR, A::default());
            subchunk.extend(storage.drain(..degree / P::SIZE_FACTOR));
            result.push(Self {
                storage: subchunk,
                _marker: std::marker::PhantomData,
            });
        }

        result
    }
}

#[derive(Derivative)]
#[derivative(Debug)]
pub(crate) struct GenericPolynomialChunk<
    F: PrimeField,
    FORM: PolynomialForm,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F> = F,
    A: GoodAllocator = Global,
> {
    pub(crate) over: std::sync::Arc<GenericPolynomial<F, FORM, P, A>>,
    pub(crate) range: std::ops::Range<usize>,
    _marker: std::marker::PhantomData<(FORM, A)>,
}

impl<
        F: PrimeField,
        FORM: PolynomialForm,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
    > GenericPolynomialChunk<F, FORM, P, A>
{
    pub(crate) fn as_ref(&self) -> &[P] {
        &self.over.storage[self.range.clone()]
    }
}

#[derive(Derivative)]
#[derivative(Debug)]
pub(crate) struct GenericPolynomialChunks<
    'a,
    F: PrimeField,
    FORM: PolynomialForm,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    pub(crate) inner: Vec<Vec<&'a [F], B>, B>,
    _marker: std::marker::PhantomData<(FORM, A)>,
}

impl<'a, F: PrimeField, FORM: PolynomialForm, A: GoodAllocator, B: GoodAllocator>
    GenericPolynomialChunks<'a, F, FORM, A, B>
{
    pub(crate) fn from_polys_with_chunk_size(
        polys: &'a Vec<Polynomial<F, FORM, A>, B>,
        chunk_size: usize,
    ) -> Self
    where
        F: SmallField,
    {
        let num_chunks = polys[0].storage.chunks(chunk_size).len();
        // trick to be able to fill the vectors and then assign by index instead of push
        let mut transposed_chunks = Vec::with_capacity_in(num_chunks, B::default());
        for _ in 0..num_chunks {
            let inner: Vec<&'a [F], B> = Vec::with_capacity_in(polys.len(), B::default());
            transposed_chunks.push(inner);
        }

        let mut tmp: Vec<_> = polys
            .iter()
            .map(|el| el.storage.chunks(chunk_size))
            .collect();
        for chunk_idx in 0..num_chunks {
            for poly_chunks in tmp.iter_mut() {
                let chunk = poly_chunks.next().unwrap();

                transposed_chunks[chunk_idx].push(chunk);
            }
        }

        Self {
            inner: transposed_chunks,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'a, F: PrimeField, A: GoodAllocator, B: GoodAllocator>
    GenericPolynomialChunks<'a, F, LagrangeForm, A, B>
{
    pub(crate) fn from_columns_with_chunk_size(
        polys: &'a Vec<Vec<F, A>, B>,
        domain_size: usize,
        chunk_size: usize,
    ) -> Self
    where
        F: SmallField,
    {
        let num_chunks = vec![(); domain_size].chunks(chunk_size).len();

        // we still want to have proper number of chunks, even though they are empty internally
        if polys.len() == 0 {
            let mut inner = Vec::with_capacity_in(num_chunks, B::default());
            for _ in 0..num_chunks {
                inner.push(Vec::new_in(B::default()));
            }
            return Self {
                inner,
                _marker: std::marker::PhantomData,
            };
        }
        assert_eq!(polys[0].len(), domain_size);
        // trick to be able to fill the vectors and then assign by index instead of push
        let mut transposed_chunks = Vec::with_capacity_in(num_chunks, B::default());
        for _ in 0..num_chunks {
            let inner: Vec<&'a [F], B> = Vec::with_capacity_in(polys.len(), B::default());
            transposed_chunks.push(inner);
        }

        let mut tmp: Vec<_> = polys.iter().map(|el| el.chunks(chunk_size)).collect();
        for chunk_idx in 0..num_chunks {
            for poly_chunks in tmp.iter_mut() {
                let chunk = poly_chunks.next().unwrap();

                transposed_chunks[chunk_idx].push(chunk);
            }
        }

        Self {
            inner: transposed_chunks,
            _marker: std::marker::PhantomData,
        }
    }
}

#[derive(Derivative)]
#[derivative(Debug)]
pub(crate) struct GenericPolynomialChunksMut<
    'a,
    F: PrimeField,
    FORM: PolynomialForm,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    pub(crate) inner: Vec<Vec<&'a mut [F], B>, B>,
    _marker: std::marker::PhantomData<(FORM, A)>,
}

impl<'a, F: PrimeField, FORM: PolynomialForm, A: GoodAllocator, B: GoodAllocator>
    GenericPolynomialChunksMut<'a, F, FORM, A, B>
{
    pub(crate) fn from_polys_with_chunk_size(
        polys: &'a mut Vec<Polynomial<F, FORM, A>>,
        chunk_size: usize,
    ) -> Self
    where
        F: SmallField,
    {
        assert!(polys.len() > 0);

        let num_chunks = polys[0].storage.chunks(chunk_size).len();
        // trick to be able to fill the vectors and then assign by index instead of push
        let mut transposed_chunks = Vec::with_capacity_in(num_chunks, B::default());
        for _ in 0..num_chunks {
            let inner: Vec<&'a mut [F], B> = Vec::with_capacity_in(polys.len(), B::default());
            transposed_chunks.push(inner);
        }

        let mut tmp: Vec<_> = polys
            .iter_mut()
            .map(|el| el.storage.chunks_mut(chunk_size))
            .collect();
        for chunk_idx in 0..num_chunks {
            for poly_chunks in tmp.iter_mut() {
                let chunk = poly_chunks.next().unwrap();

                transposed_chunks[chunk_idx].push(chunk);
            }
        }

        Self {
            inner: transposed_chunks,
            _marker: std::marker::PhantomData,
        }
    }
}

// pub(crate) fn dissect_fft_style<
//     F: PrimeField,
//     P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
//     A: GoodAllocator,
//     B: GoodAllocator
// >(
//     presumably_bitreversed_lde_chunks: Vec<Vec<P, A>, B>,
//     inverse_omegas_bitreversed: &[P], // IMPORTANT: here it's only for "final" domain size
//     worker: &Worker,
//     ctx: P::Context
// ) -> Vec<GenericPolynomial<F, MonomialForm, P, A>, B> {
//     use crate::cs::implementations::utils::*;
//     use crate::fft::bitreverse_enumeration_inplace;

//     let outer = presumably_bitreversed_lde_chunks.len();
//     let inner = presumably_bitreversed_lde_chunks[0].len();

//     let mut transposed = Vec::with_capacity_in(inner, B::default());
//     for _ in 0..inner {
//         let mut tmp = Vec::with_capacity_in(outer, A::default());
//         unsafe {tmp.set_len(outer)};
//         transposed.push(tmp);
//     }

//     for i in 0..inner {
//         for j in 0..outer {
//             transposed[i][j] = presumably_bitreversed_lde_chunks[j][i];
//         }
//     }

//     let multiplicative_generator = P::constant(F::multiplicative_generator(), ctx);
//     let t = if config::DEBUG_SATISFIABLE == false {
//         multiplicative_generator
//     } else {
//         P::one(ctx)
//     };

//     let short_twiddles = precompute_twiddles_for_fft::<F, P, A, true>(outer, worker, ctx);
//     for el in transposed.iter_mut() {
//         bitreverse_enumeration_inplace(el);
//         P::ifft_natural_to_natural(el, t, &short_twiddles, ctx);
//     }

//     dbg!(&transposed);

//     // here we assume that `presumably_bitreversed_lde_chunks`
//     // is (if concatenated) an evaluations of some polynomial F(x) of degree N on domain
//     // multiplicative_generator * {1, omega', omega'^2, ..} where omega' ^ N == 1

//     // if we want to somehow split that into k polynomials of degree of N/k and save on IFFT size,
//     // we should properly restructure the initial values

//     // we can not take each of those sets on multiplicative_generator * gamma^i X {1, omega, omega^2, ...},
//     // where gamma^k == omega, omega^(N/k) == 1 because it's not possible to find a compact
//     // composition of initial polynomial of degree N as function of k polynomials of degree N/k

//     // f_1(x^M) +

//     // f_1(x^N/k) + x * f_2(x^N/k) + ... (k terms),
//     // then we

//     // we can use an observation that omega^(N/k) == 1, so if we will look for a final decomposition
//     // as form f_1(x) + x^{N/k} * f_2(x) + ... where every f_{i} is of degree N-1 and there are k terms in total
//     // at every evaluation point of gamma^i X {1, omega, omega^2, ...} x^N/k == 1 * gamma^iN/k =

//     // but what we can notice is:
//     // - recomposition should be in a form f_1(x^k) + x * f_2(x^k) + x^2 * f_3(x^k) + ...

//     // but every of those subvectors can be considered as evaluations of SOME polynomial
//     // of degree N/k over set multiplicative_generator * gamma^i X {1, omega, omega^2, ...},
//     // where gamma^k == omega, omega^(N/k) == 1

//     // so we kind of "guess" an good interpolation here: we
//     // - we do IFFT for each of those subvectors assuming they are values of poly of degree N/k on domain
//     // multiplicative_generator * gamma^i X {1, omega, omega^2, ...}
//     // - now we need to understand how we can construct our initial polynomial from those k subpolys

//     // 1 : f1(1) + 1 * f2(1) + ...
//     // gamma : f1(omega) + gamma * f2(omega) + ...
//     // gamma^2: f1(omega^2) + gamma^2 * f2(omega^2) + ... omega * f_{k/2}(omega^2) + gamma^2 * omega * f_{k/2 + 1}(omega^2)

//     // what we want is instead of doing IFFT of size N to do k IFFTs of size N/k,
//     // and get polynomials f_1(x) .. f_k(x) such that F(x) = f_1(x^k) + x^m * f_2(x^k) + ...

//     let initial_domain_size = presumably_bitreversed_lde_chunks.len() * presumably_bitreversed_lde_chunks[0].len() * P::SIZE_FACTOR;
//     dbg!(&initial_domain_size);
//     debug_assert!(initial_domain_size.is_power_of_two());
//     let fold_into = presumably_bitreversed_lde_chunks.len();

//     let multiplicative_generator = P::constant(F::multiplicative_generator(), ctx);
//     let twiddles = precompute_twiddles_for_fft::<_, _, A, true>(initial_domain_size, worker, ctx);

//     let t = if config::DEBUG_SATISFIABLE == false {
//         multiplicative_generator
//     } else {
//         P::one(ctx)
//     };

//     let mut tmp = presumably_bitreversed_lde_chunks.clone();
//     bitreverse_enumeration_inplace(&mut tmp);

//     let mut flattened = vec![];
//     for el in tmp.into_iter() {
//         let mut el = el;
//         bitreverse_enumeration_inplace(&mut el);
//         flattened.extend(el);
//     }

//     P::ifft_natural_to_natural(
//         &mut flattened,
//         t,
//         &twiddles,
//         ctx
//     );

//     let coset = domain_generator_for_size::<F>(initial_domain_size as u64);
//     // let coset = coset.inverse().expect("inverse of domain generator always exists");
//     let powers_of_coset = materialize_powers_serial::<F, A>(coset, fold_into);
//     let powers_of_coset_ref = &powers_of_coset;
//     let mut presumably_bitreversed_lde_chunks = presumably_bitreversed_lde_chunks;

//     worker.scope(presumably_bitreversed_lde_chunks.len(), |scope, chunk_size| {
//         for (chunk_idx, dst) in presumably_bitreversed_lde_chunks.chunks_mut(chunk_size).enumerate() {
//             scope.spawn(move |_| {
//                 for (i, dst) in dst.iter_mut().enumerate() {
//                     let coset_idx = chunk_idx * chunk_size + i;
//                     let mut coset = P::constant(powers_of_coset_ref[coset_idx], ctx);
//                     if config::DEBUG_SATISFIABLE == false {
//                         coset.mul_assign(&multiplicative_generator, ctx);
//                     }

//                     bitreverse_enumeration_inplace(dst);
//                     P::ifft_natural_to_natural(dst, coset, inverse_omegas_bitreversed, ctx);
//                 }
//             });
//         }
//     });

//     dbg!(&flattened);
//     // dbg!(&presumably_bitreversed_lde_chunks);

//     todo!();

//     // // TODO: may be use IFFT implementation for P to achieve the same, with full vectorization

//     // // so far we need to do slitting like

//     // // f0(x^2) = (f(x) + f(-x)) / 2
//     // // f1(x^2) = (f(x) - f(-x)) / 2x

//     // // where x has a form {1, gamma, gamma^2, ...} X {1, omega, omega^2, ...}

//     // // note that when we construct f0/f1 we go form gamma^i omega^k into gamma^2i omega^2k,
//     // // and when we fold enough times then it's gamma^Ni omega^Nk with a relation that gamma^N == omega, so
//     // // we again span the whole domain {1, omega, omega^2, ...}, but in different order: every
//     // // coset in `presumably_bitreversed_lde_chunks` will give rise to series omega^i if coset was created using gamma^i,
//     // // and subdomain like `{1, omega^N, omega^2N, ...}
//     // // so to properly form f0/f1/... over {1, omega, omega^2, ...} we would need to do some shuffling

//     // // we should have another note: we are not exactly at {1, gamma, gamma^2, ...} X {1, omega, omega^2, ...},
//     // // but on multiplicative_generator * {1, gamma, gamma^2, ...} X {1, omega, omega^2, ...},
//     // // so every time we do "fold" we accumulate another power of multiplicative_generator, so eventually we will have
//     // // evaluations on multiplicative_generator^2N * omega^i x {1, omega^N, omega^2N, ...}

//     // // We also do not need to divide by 2 in practice, and so we do IFFT like butterflies here

//     // debug_assert!(presumably_bitreversed_lde_chunks.len().is_power_of_two());
//     // let initial_domain_size = presumably_bitreversed_lde_chunks.len() * presumably_bitreversed_lde_chunks[0].len() * P::SIZE_FACTOR;
//     // debug_assert!(initial_domain_size.is_power_of_two());
//     // let final_domain_size = presumably_bitreversed_lde_chunks[0].len() * P::SIZE_FACTOR;

//     // let inner_size = presumably_bitreversed_lde_chunks[0].len();

//     // debug_assert!(inverse_omegas_bitreversed.len() * P::SIZE_FACTOR == final_domain_size / 2);

//     // let degree = presumably_bitreversed_lde_chunks.len();

//     // use crate::cs::implementations::utils::*;
//     // use crate::fft::bitreverse_enumeration_inplace;
//     // let coset = domain_generator_for_size::<F>(initial_domain_size as u64);
//     // let coset = coset.inverse().expect("inverse of domain generator always exists");
//     // let mut powers_of_coset = materialize_powers_serial::<F, A>(coset, degree);
//     // bitreverse_enumeration_inplace(&mut powers_of_coset);

//     // // now we should note:
//     // // - every subvector is evaluations on coset * {1, omega, omega^2, ...}.bitreverse()
//     // // - `inverse_omegas_bitreversed` is in the form {1, omega^-1, omega^-2, ...}.bitreverse(),
//     // // - so they are kind of aligned, and we could use vectorized operations, but as one
//     // // will see below values at omega and -omega are always adjustent inside of the vector type,
//     // // so we will have to split into base for most of the time

//     // let inverse_omegas_bitreversed = P::slice_into_base_slice(inverse_omegas_bitreversed);

//     // // let mut tmp_buffer = initialize_in_with_alignment_of::<_, P, _>(F::ZERO, initial_domain_size, A::default());

//     // // the only trick would be that every time we divide by x we divide by both powers of omega from precomputed twiddles

//     // let mut split_polys = Vec::with_capacity_in(degree, B::default());
//     // for _ in 0..degree {
//     //     let tmp = initialize_in_with_alignment_of::<_, P, _>(F::ZERO, final_domain_size, A::default());
//     //     split_polys.push(tmp);
//     // }

//     // for (coset_values, coset) in presumably_bitreversed_lde_chunks.iter().zip(powers_of_coset.iter()) {
//     //     let coset_values = P::slice_into_base_slice(coset_values);

//     //     // those are internally bitreversed, so omega and -omega are always adjustent,
//     //     // but we should be careful about subranges of destinations

//     //     let split_point = degree / 2;
//     //     let (place_for_f0s, place_for_f1s) = split_polys.split_at_mut(split_point);

//     //     // make borrow checked "happy" as we always iterate over non-overlapping ranges
//     //     worker.scope(final_domain_size/2, |scope, chunk_size| {
//     //         for src_chunk in coset_values.chunks(chunk_size * 2) {
//     //             scope.spawn(move |_| {
//     //                 for [f_x, f_minus_x] in src_chunk.array_chunks::<2>() {
//     //                     let mut f0 = *f_x;
//     //                     f0.add_assign(f_minus_x);

//     //                     let mut f1 = *f_x;
//     //                     f1.sub_assign(f_minus_x);

//     //                     // now we should place it into
//     //                     // corresponding location,
//     //                     // and also do it in such a way that it's convenient for any future step

//     //                     // for this we should have a look at our domain structure
//     //                     // omaga and -omega have indexes 0b0X and 0b1X, that are in bitreversed enumeration
//     //                     // map into 0bX_rev0 and 0bX_rev1 and we used such property.
//     //                     // Now we have to place omega^2 such that ideally -omega^2 will be near it and our construction
//     //                     // is recursive. In normal enumerations elements that are sqrt(-omega^2) are located
//     //                     // at 0b10Z and 0b11Z, while sqrt(omega^2) are at 0b00Z and 0b10Z, so one can see
//     //                     // that we also need to place evalues of f0/f1 just continuously in corresponding locations
//     //                     // the only trick is to place all f0s separately and all f1s separately

//     //                 }
//     //             })
//     //         }
//     //     })

//     // }

//     //  // // the only trick would be that every time we divide by x we divide by both powers of omega from precomputed twiddles

//     // // let mut split_polys = Vec::with_capacity_in(degree, B::default());
//     // // for _ in 0..degree {
//     // //     let tmp = initialize_in_with_alignment_of::<_, P, _>(F::ZERO, final_domain_size, A::default());
//     // //     split_polys.push(tmp);
//     // // }

//     // // for (coset_values, coset) in presumably_bitreversed_lde_chunks.iter().zip(powers_of_coset.iter()) {
//     // //     let mut extra_divisor = two_inv;
//     // //     extra_divisor.mul_assign(&coset);
//     // //     let coset_values = P::slice_into_base_slice(coset_values);

//     // //     // those are internally bitreversed, so omega and -omega are always adjustent,
//     // //     // but we should be careful about subranges of destinations

//     // //     let dst = &mut split_polys[..];
//     // //     let dst_ptr = dst as *mut [Vec<F, A>];
//     // //     // make borrow checked "happy" as we always iterate over non-overlapping ranges
//     // //     worker.scope(final_domain_size/2, |scope, chunk_size| {
//     // //         for src_chunk in coset_values.chunks(chunk_size * 2) {
//     // //             let dst = unsafe {&mut *dst_ptr};
//     // //             scope.spawn(move |_| {
//     // //                 for [f_x, f_minus_x] in src_chunk.array_chunks::<2>() {
//     // //                     let mut f0 = *f_x;
//     // //                     f0.add_assign(f_minus_x);

//     // //                     let mut f1 = *f_x;
//     // //                     f1.sub_assign(f_minus_x);

//     // //                     // now we should place it into
//     // //                     // corresponding location for every
//     // //                 }
//     // //             })
//     // //         }
//     // //     })

//     // // }

//     // todo!()
// }
