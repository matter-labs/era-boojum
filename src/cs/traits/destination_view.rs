use super::*;
use crate::field::traits::field_like::BaseField;
use crate::{cs::implementations::polynomial::lde::*, field::PrimeField};

// we want to place evaluations of the value into some slot for it

pub trait EvaluationDestination<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
>: Sized + 'static + Send + Sync + std::fmt::Debug
{
    fn push_evaluation_result(&mut self, value: P, ctx: &mut P::Context);
}

pub trait EvaluationDestinationDrivable<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
>: EvaluationDestination<F, P>
{
    // should return only number of evaluations without terms due to extra
    // challanges drawn due to small field
    fn expected_num_iterations(&self) -> usize;
    fn advance(&mut self, ctx: &mut P::Context);
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct TestingEvaluationDestination<F: PrimeField, P: field::traits::field_like::PrimeFieldLike>
{
    pub columns: Vec<Vec<P>>,
    pub expected_trace_length: usize,
    pub current_row: usize,
    pub offset: usize,
    _marker: std::marker::PhantomData<F>,
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLike>
    TestingEvaluationDestination<F, P>
{
    pub fn new_for_length(num_terms: usize, max_trace_length: usize) -> Self {
        Self {
            columns: vec![Vec::with_capacity(max_trace_length); num_terms],
            expected_trace_length: max_trace_length,
            current_row: 0,
            offset: 0,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLike<Base = F>>
    EvaluationDestination<F, P> for TestingEvaluationDestination<F, P>
{
    #[inline(always)]
    fn push_evaluation_result(&mut self, value: P, _ctx: &mut P::Context) {
        self.columns[self.offset].push(value);
        self.offset += 1;
    }
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLike<Base = F>>
    EvaluationDestinationDrivable<F, P> for TestingEvaluationDestination<F, P>
{
    #[inline]
    fn expected_num_iterations(&self) -> usize {
        self.expected_trace_length
    }
    #[inline(always)]
    fn advance(&mut self, _ctx: &mut P::Context) {
        self.current_row += 1;
        self.offset = 0;
    }
}

impl<F: BaseField> EvaluationDestination<F, F> for Vec<F> {
    #[inline(always)]
    fn push_evaluation_result(&mut self, value: F, _ctx: &mut ()) {
        self.push(value);
    }
}

impl<F: BaseField> EvaluationDestinationDrivable<F, F> for Vec<F> {
    #[inline]
    fn expected_num_iterations(&self) -> usize {
        1
    }
    #[inline(always)]
    fn advance(&mut self, _ctx: &mut ()) {
        // self.truncate(0);
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct GateEvaluationReducingDestination<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
> {
    pub challenges_powers: std::sync::Arc<Vec<[F; 2]>>, // we do not expect too many repetitions of the protocol
    pub quotient_buffers: std::sync::Arc<[Vec<Vec<P>>; 2]>, // closely mimic structure of LDE storage
    pub ctx: P::Context,
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct GateEvaluationReducingDestinationChunk<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
> {
    pub destination: GateEvaluationReducingDestination<F, P>,
    pub selectors_view: GenericLdeRowView<F, P>,
    pub work_buffer: [P; 2], // we store as coefficients of Fp2
    base_challenge_offset: usize,
    current_challenge_offset: usize,
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>>
    GateEvaluationReducingDestinationChunk<F, P>
{
    pub fn set_challenge_offset(&mut self, offset: usize) {
        debug_assert_eq!(self.base_challenge_offset, 0);
        debug_assert_eq!(self.current_challenge_offset, 0);

        self.base_challenge_offset = offset;
        self.current_challenge_offset = offset;
    }
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>>
    GateEvaluationReducingDestination<F, P>
{
    pub fn new(
        inner_size: usize,
        degree: usize,
        pregenerated_challenges: Vec<[F; 2]>,
        ctx: &mut P::Context,
    ) -> Self {
        let buffer: [_; 2] = std::array::from_fn(|_| vec![vec![P::zero(ctx); inner_size]; degree]);

        Self {
            challenges_powers: std::sync::Arc::new(pregenerated_challenges),
            quotient_buffers: std::sync::Arc::new(buffer),
            ctx: *ctx,
        }
    }

    pub fn into_chunks(
        &self,
        num_workers: usize,
        selectors_storage: &ArcGenericLdeStorage<F, P>,
    ) -> Vec<GateEvaluationReducingDestinationChunk<F, P>> {
        debug_assert_eq!(
            self.quotient_buffers[0].len(),
            selectors_storage.outer_len()
        );
        debug_assert_eq!(
            self.quotient_buffers[0][0].len(),
            selectors_storage.inner_len()
        );
        let lde_iterators = selectors_storage.compute_chunks_for_num_workers(num_workers);
        let mut ctx = self.ctx;

        let mut result = Vec::with_capacity(num_workers);
        let zero = P::zero(&mut ctx);
        for subiterator in lde_iterators.into_iter() {
            let chunk = GateEvaluationReducingDestinationChunk {
                destination: self.clone(),
                work_buffer: [zero; 2],
                selectors_view: GenericLdeRowView {
                    over: selectors_storage.clone(),
                    iterator: subiterator,
                },
                base_challenge_offset: 0,
                current_challenge_offset: 0,
            };

            result.push(chunk);
        }

        debug_assert!(result.len() <= num_workers);

        result
    }

    pub fn into_chunks_without_selector(
        &self,
        num_workers: usize,
    ) -> Vec<GateEvaluationReducingDestinationChunk<F, P>> {
        let lde_iterators = LdeIterator::chunk_lde_storage_for_num_workers(
            self.quotient_buffers[0].len(),
            self.quotient_buffers[0][0].len(),
            num_workers,
        );

        let mut ctx = self.ctx;

        let mut result = Vec::with_capacity(num_workers);
        let zero = P::zero(&mut ctx);
        for subiterator in lde_iterators.into_iter() {
            let chunk = GateEvaluationReducingDestinationChunk {
                destination: self.clone(),
                work_buffer: [zero; 2],
                selectors_view: GenericLdeRowView {
                    over: ArcGenericLdeStorage {
                        storage: Vec::new(),
                    },
                    iterator: subiterator,
                },
                base_challenge_offset: 0,
                current_challenge_offset: 0,
            };

            result.push(chunk);
        }

        debug_assert!(result.len() <= num_workers);

        result
    }
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>>
    EvaluationDestination<F, P> for GateEvaluationReducingDestinationChunk<F, P>
{
    #[inline(always)]
    fn push_evaluation_result(&mut self, value: P, ctx: &mut P::Context) {
        // simultaneously reduce by multiplying by challenge and adding into accumulator
        let mut c0 = value;
        c0.mul_all_by_base(
            &self.destination.challenges_powers[self.current_challenge_offset][0],
            ctx,
        );

        let mut c1 = value;
        c1.mul_all_by_base(
            &self.destination.challenges_powers[self.current_challenge_offset][1],
            ctx,
        );

        // add into accumulator
        self.work_buffer[0].add_assign(&c0, ctx);
        self.work_buffer[1].add_assign(&c1, ctx);

        self.current_challenge_offset += 1;
    }
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>>
    EvaluationDestinationDrivable<F, P> for GateEvaluationReducingDestinationChunk<F, P>
{
    #[inline]
    fn expected_num_iterations(&self) -> usize {
        self.selectors_view.num_iterations()
    }
    #[inline]
    fn advance(&mut self, ctx: &mut P::Context) {
        let (outer, inner) = self.selectors_view.iterator.current();
        let gate_selector_value = if self.selectors_view.over.storage.is_empty() {
            P::one(ctx)
        } else {
            self.selectors_view.over.storage[outer].storage[inner]
        };

        // we actually want to do the reduction and swap the result
        if crate::config::DEBUG_SATISFIABLE == true && outer == 0 {
            let selector = [gate_selector_value];
            let value = [self.work_buffer[0]];
            let selector = P::slice_into_base_slice(&selector);
            let value = P::slice_into_base_slice(&value);

            for (idx, (selector, value)) in selector.iter().zip(value.iter()).enumerate() {
                let inner = inner * P::SIZE_FACTOR + idx;
                if selector.is_zero() == false {
                    debug_assert!(
                            value.is_zero() == true,
                            "aggregated term value is non-zero and has value {} for selector value {} at trace row {}", 
                            value,
                            selector,
                            {
                                let mut normal_enumeration = inner.reverse_bits();
                                normal_enumeration >>= usize::BITS - self.destination.quotient_buffers[0][0].len().trailing_zeros();

                                normal_enumeration
                            }
                        );
                }
            }
        }

        let zero = P::zero(ctx);
        let [mut c0, mut c1] = std::mem::replace(&mut self.work_buffer, [zero; 2]);
        // mul by selector once
        c0.mul_assign(&gate_selector_value, ctx);
        c1.mul_assign(&gate_selector_value, ctx);

        // actually place it. When we created chunks those were non-overlapping, so we can
        // transitively move statement over non-overlapping to the outer vector too
        unsafe {
            std::sync::Arc::get_mut_unchecked(&mut self.destination.quotient_buffers)[0][outer]
                [inner]
                .add_assign(&c0, ctx);

            std::sync::Arc::get_mut_unchecked(&mut self.destination.quotient_buffers)[1][outer]
                [inner]
                .add_assign(&c1, ctx);
        };

        // reset offset of challenges for next row
        self.current_challenge_offset = self.base_challenge_offset;

        self.selectors_view.advance();
    }
}
