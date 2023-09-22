use crate::cs::traits::GoodAllocator;

use super::*;
use std::sync::Arc;

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq)]
pub struct LdeIterator {
    chunks: SmallVec<[(usize, std::ops::Range<usize>); 8]>,
}

impl LdeIterator {
    pub fn num_iterations(&self) -> usize {
        self.chunks.iter().map(|el| el.1.len()).sum()
    }
    #[inline(always)]
    pub fn current(&self) -> (usize, usize) {
        let (outer, range) = &self.chunks[0];
        let outer = *outer;
        debug_assert!(range.is_empty() == false);

        let inner = range.start;

        (outer, inner)
    }

    #[inline(always)]
    pub fn advance(&mut self) {
        self.chunks[0].1.start += 1;
        if self.chunks[0].1.is_empty() {
            let _ = self.chunks.drain(..1).next();
        }
    }

    pub fn full_iterator(lde_degree: usize, inner_size: usize) -> Self {
        let mut subchunks = SmallVec::new();
        for outer in 0..lde_degree {
            subchunks.push((outer, 0..inner_size));
        }

        Self { chunks: subchunks }
    }

    // Implementations below made sure we can project from LDE storage to uniform storage or back

    pub fn chunk_lde_storage_for_num_workers(
        lde_degree: usize,
        inner_size: usize,
        num_workers: usize,
    ) -> Vec<Self> {
        let total_work_size = inner_size * lde_degree;
        let mut num_workers = num_workers;
        if num_workers > total_work_size {
            num_workers = total_work_size;
        }
        let mut result = Vec::with_capacity(num_workers);
        // quick trick
        let artificial_data = vec![(); total_work_size];
        let chunk_size = Worker::compute_chunk_size(total_work_size, num_workers);
        let mut start = 0;
        for chunk in artificial_data.chunks(chunk_size) {
            let mut subchunks = SmallVec::new();
            let end = start + chunk.len();
            debug_assert!(end <= total_work_size);
            debug_assert!(end > 0);

            let (start_outer, start_inner) = (start / inner_size, start % inner_size);
            let (end_outer, end_inner) = (end / inner_size, end % inner_size);
            if start_outer == end_outer {
                subchunks.push((start_outer, start_inner..end_inner));
                result.push(Self { chunks: subchunks });
            } else {
                for outer in start_outer..=end_outer {
                    if outer == start_outer {
                        if start_inner != inner_size {
                            subchunks.push((outer, start_inner..inner_size));
                        }
                    } else if outer == end_outer {
                        if end_inner != 0 {
                            subchunks.push((outer, 0..end_inner));
                        }
                    } else {
                        subchunks.push((outer, 0..inner_size));
                    }
                }

                result.push(Self { chunks: subchunks });
            }

            start = end;
        }

        debug_assert!(result.len() > 0);
        debug_assert!(result.len() <= num_workers);

        result
    }

    pub fn chunk_single_storage_for_num_workers(_size: usize, _num_worker: usize) -> Vec<Self> {
        todo!();
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct GenericLdeStorage<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F> = F,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    pub storage: Vec<GenericPolynomial<F, BitreversedLagrangeForm, P, A>, B>,
}

pub type LdeStorage<F, A = Global, B = Global> = GenericLdeStorage<F, F, A, B>;

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > GenericLdeStorage<F, P, A, B>
{
    #[inline]
    pub fn empty_with_capacity_in(capacity: usize, allocator: B) -> Self {
        debug_assert!(capacity.is_power_of_two());
        Self {
            storage: Vec::with_capacity_in(capacity, allocator),
        }
    }
    #[inline]
    pub fn inner_len(&self) -> usize {
        self.storage[0].storage.len()
    }
    #[inline]
    pub fn outer_len(&self) -> usize {
        self.storage.len()
    }
    #[inline]
    pub fn from_single(values: GenericPolynomial<F, BitreversedLagrangeForm, P, A>) -> Self {
        let mut storage = Vec::with_capacity_in(1, B::default());
        storage.push(values);

        Self { storage }
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LdeParameters<F: PrimeField> {
    pub domain_size: usize,
    pub ldes_generator: F,
    pub additional_coset: F,
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, PartialEq(bound = ""), Eq)]
#[serde(
    bound = "F: serde::Serialize + serde::de::DeserializeOwned, P: serde::Serialize + serde::de::DeserializeOwned"
)]
pub struct ArcGenericLdeStorage<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    #[serde(serialize_with = "crate::utils::serialize_vec_arc")]
    #[serde(deserialize_with = "crate::utils::deserialize_vec_arc")]
    pub storage: Vec<Arc<GenericPolynomial<F, BitreversedLagrangeForm, P, A>>, B>,
}

pub type ArcLdeStorage<F, A = Global, B = Global> = ArcGenericLdeStorage<F, F, A, B>;

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > MemcopySerializable for ArcGenericLdeStorage<F, P, A, B>
where
    Self: 'static,
{
    fn write_into_buffer<W: std::io::Write>(
        &self,
        mut dst: W,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let outer_len_le_bytes = (self.storage.len() as u64).to_le_bytes();
        dst.write_all(&outer_len_le_bytes).map_err(Box::new)?;

        for el in self.storage.iter() {
            let inner: &GenericPolynomial<F, BitreversedLagrangeForm, P, A> = el;
            MemcopySerializable::write_into_buffer(inner, &mut dst)?;
        }

        Ok(())
    }

    fn read_from_buffer<R: std::io::Read>(mut src: R) -> Result<Self, Box<dyn std::error::Error>> {
        let mut buffer = [0u8; 8];
        src.read_exact(&mut buffer).map_err(Box::new)?;
        let capacity = u64::from_le_bytes(buffer) as usize;

        assert!(capacity.is_power_of_two());

        let mut storage = Vec::with_capacity_in(capacity, B::default());

        for _ in 0..capacity {
            let inner: GenericPolynomial<F, BitreversedLagrangeForm, P, A> =
                MemcopySerializable::read_from_buffer(&mut src)?;
            storage.push(Arc::new(inner));
        }

        let new = Self { storage };

        Ok(new)
    }
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > ArcGenericLdeStorage<F, P, A, B>
{
    #[inline]
    pub fn empty_with_capacity_in(capacity: usize, allocator: B) -> Self {
        debug_assert!(capacity.is_power_of_two());
        Self {
            storage: Vec::with_capacity_in(capacity, allocator),
        }
    }

    #[inline]
    pub fn zeroed(
        inner_size: usize,
        outer_size: usize,
        inner_allocator: A,
        outer_allocator: B,
    ) -> Self {
        debug_assert!(inner_size.is_power_of_two());
        debug_assert!(outer_size.is_power_of_two());
        let mut storage = Vec::with_capacity_in(outer_size, outer_allocator);
        for _ in 0..outer_size {
            let mut inner = Vec::with_capacity_in(inner_size, inner_allocator.clone());
            inner.resize(inner_size, P::zero(&mut ()));
            let as_poly = GenericPolynomial::from_storage(inner);
            storage.push(Arc::new(as_poly));
        }

        Self { storage }
    }

    #[inline]
    pub fn uninit(
        inner_size: usize,
        outer_size: usize,
        inner_allocator: A,
        outer_allocator: B,
    ) -> Self {
        debug_assert!(inner_size.is_power_of_two());
        debug_assert!(outer_size.is_power_of_two());
        let mut storage = Vec::with_capacity_in(outer_size, outer_allocator);
        for _ in 0..outer_size {
            let as_poly = GenericPolynomial::from_storage(Vec::with_capacity_in(
                inner_size,
                inner_allocator.clone(),
            ));
            storage.push(Arc::new(as_poly));
        }

        Self { storage }
    }

    /// # Safety
    ///
    /// The internal state must be initialized prior to calling this function.
    #[inline]
    pub unsafe fn assume_init(&mut self, inner_size: usize) {
        debug_assert!(inner_size.is_power_of_two());
        for el in self.storage.iter_mut() {
            Arc::get_mut(el).unwrap().storage.set_len(inner_size);
        }
    }

    #[inline]
    pub fn from_owned(owned: GenericLdeStorage<F, P, A, B>) -> Self {
        let mut storage = Vec::with_capacity_in(owned.storage.len(), B::default());
        for el in owned.storage.into_iter() {
            storage.push(Arc::new(el));
        }

        Self { storage }
    }

    // shallow clone, for readonly
    #[track_caller]
    pub fn subset_for_degree(&self, degree: usize) -> Self {
        assert!(degree <= self.storage.len());
        assert!((self.storage.len() / degree).is_power_of_two());

        let mut storage = Vec::with_capacity_in(degree, B::default());
        for i in 0..degree {
            storage.push(Arc::clone(&self.storage[i]));
        }

        Self { storage }
    }

    // deep clone, when we want to create a new one
    pub fn owned_subset_for_degree(&self, degree: usize) -> Self {
        assert!(degree <= self.storage.len());
        assert!((self.storage.len() / degree).is_power_of_two());

        let mut storage = Vec::with_capacity_in(degree, B::default());
        for i in 0..degree {
            let owned_chunk = Clone::clone(self.storage[i].as_ref());
            debug_assert!(owned_chunk.storage.as_ptr().addr() % std::mem::align_of::<P>() == 0);
            storage.push(Arc::new(owned_chunk));
        }

        Self { storage }
    }

    #[inline]
    pub fn inner_len(&self) -> usize {
        self.storage[0].storage.len()
    }
    #[inline]
    pub fn outer_len(&self) -> usize {
        self.storage.len()
    }
    #[inline]
    pub fn compute_chunks_for_num_workers(&self, num_workers: usize) -> Vec<LdeIterator> {
        LdeIterator::chunk_lde_storage_for_num_workers(
            self.outer_len(),
            self.inner_len(),
            num_workers,
        )
    }
}

// Note: no SmallField here in the definition, but it will happen in implementations
// NOTE: it's not that important how we enumerate cosets over which we made LDE,
// but we take a convension that it MUST be itself bitreversed
#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct GenericPolynomialLde<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F> = F,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    pub storage: ArcGenericLdeStorage<F, P, A, B>,
    pub lde_params: LdeParameters<F>,
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > GenericPolynomialLde<F, P, A, B>
{
    pub fn subset_for_degree(&self, degree: usize) -> Self {
        assert!(degree <= self.storage.outer_len());
        assert!((self.storage.outer_len() / degree).is_power_of_two());
        let extra_pow = self.storage.outer_len() / degree;

        let mut new_params = self.lde_params;
        new_params.ldes_generator = new_params.ldes_generator.pow_u64(extra_pow as u64);

        let mut new_storage = Vec::with_capacity_in(degree, B::default());
        for i in 0..degree {
            new_storage.push(Arc::clone(&self.storage.storage[i]));
        }

        let storage = ArcGenericLdeStorage {
            storage: new_storage,
        };

        Self {
            storage,
            lde_params: new_params,
        }
    }

    #[inline]
    pub fn inner_len(&self) -> usize {
        self.storage.inner_len()
    }
    #[inline]
    pub fn outer_len(&self) -> usize {
        self.storage.outer_len()
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct GenericLdeRowView<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F> = F,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    pub(crate) over: ArcGenericLdeStorage<F, P, A, B>,
    pub(crate) iterator: LdeIterator,
}

pub type LdeRowView<F, A, B> = GenericLdeRowView<F, F, A, B>;

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > GenericLdeRowView<F, P, A, B>
{
    #[inline]
    pub fn num_iterations(&self) -> usize {
        self.iterator.num_iterations()
    }
    #[inline]
    pub(crate) fn from_storage(storage: ArcGenericLdeStorage<F, P, A, B>) -> Self {
        let typical_len = storage.inner_len();
        debug_assert!(storage.outer_len() > 0);
        let iterator = LdeIterator::full_iterator(storage.outer_len(), typical_len);
        Self {
            over: storage,
            iterator,
        }
    }
    #[inline(always)]
    pub fn advance(&mut self) {
        self.iterator.advance()
    }

    #[inline(always)]
    pub fn get_value(&self) -> &P {
        let (outer, inner) = self.iterator.current();
        &self.over.storage[outer].storage[inner]
    }
}
