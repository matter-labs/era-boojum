use super::*;
use crate::cs::traits::evaluator::PerChunkOffset;
use crate::cs::traits::trace_source::*;
use crate::cs::traits::GoodAllocator;
use crate::field::PrimeField;
use std::alloc::Global;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct BufferingPolyStorage<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F> = F,
    A: GoodAllocator = Global,
> {
    pub chunk_offset: PerChunkOffset,
    pub constants_offset: usize,
    pub variables_offset_in_buffer: usize,
    pub witness_offset_in_buffer: usize,
    pub constants_offset_in_buffer: usize,
    pub buffer: Vec<P, A>,
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLike<Base = F>, A: GoodAllocator>
    BufferingPolyStorage<F, P, A>
{
    pub fn new_with_capacity(num_variables: usize, num_witnesses: usize, capacity: usize) -> Self {
        Self {
            chunk_offset: PerChunkOffset::zero(),
            constants_offset: 0,
            variables_offset_in_buffer: 0,
            witness_offset_in_buffer: num_variables,
            constants_offset_in_buffer: num_variables + num_witnesses,
            buffer: Vec::with_capacity_in(capacity, A::default()),
        }
    }

    pub fn new_with_explicit_offsets_and_capacity(
        variables_offset_in_buffer: usize,
        witness_offset_in_buffer: usize,
        constants_offset_in_buffer: usize,
        capacity: usize,
    ) -> Self {
        Self {
            chunk_offset: PerChunkOffset::zero(),
            constants_offset: 0,
            variables_offset_in_buffer,
            witness_offset_in_buffer,
            constants_offset_in_buffer,
            buffer: Vec::with_capacity_in(capacity, A::default()),
        }
    }
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLike<Base = F>, A: GoodAllocator>
    TraceSource<F, P> for BufferingPolyStorage<F, P, A>
{
    #[inline(always)]
    fn get_variable_value(&self, variable_idx: usize) -> P {
        debug_assert!(
            self.variables_offset_in_buffer + self.chunk_offset.variables_offset + variable_idx < self.witness_offset_in_buffer,
            "trying to access a variables column number {} (zero enumerated) at chunk offset {}, but there are only {} columns in the system",
            variable_idx,
            self.chunk_offset.variables_offset,
            self.witness_offset_in_buffer,
        );

        self.buffer
            [self.variables_offset_in_buffer + self.chunk_offset.variables_offset + variable_idx]
    }
    #[inline(always)]
    fn get_witness_value(&self, witness_idx: usize) -> P {
        debug_assert!(
            self.witness_offset_in_buffer + self.chunk_offset.witnesses_offset + witness_idx < self.constants_offset_in_buffer,
            "trying to access a witness column number {} (zero enumerated) at chunk offset {}, but there are only {} columns in the system",
            witness_idx,
            self.chunk_offset.witnesses_offset,
            self.constants_offset_in_buffer,
        );

        self.buffer
            [self.witness_offset_in_buffer + self.chunk_offset.witnesses_offset + witness_idx]
    }
    #[inline(always)]
    fn get_constant_value(&self, constant_idx: usize) -> P {
        debug_assert!(
            self.constants_offset_in_buffer + self.constants_offset + self.chunk_offset.constants_offset + constant_idx < self.buffer.len(),
            "trying to access a constant column number {} (zero enumerated) at chunk offset {} and placement offset {}, but there are only {} columns in the system",
            constant_idx,
            self.chunk_offset.constants_offset,
            self.constants_offset,
            self.buffer.len() - self.constants_offset_in_buffer,
        );

        self.buffer[self.constants_offset_in_buffer
            + self.constants_offset
            + self.chunk_offset.constants_offset
            + constant_idx]
    }
    #[inline(always)]
    fn dump_current_row<C: GoodAllocator>(&self, _dst: &mut Vec<P, C>) {
        unimplemented!("Not used by buffering source");
    }
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLike<Base = F>, A: GoodAllocator>
    TraceSourceDerivable<F, P> for BufferingPolyStorage<F, P, A>
{
    #[inline(always)]
    fn num_iterations(&self) -> usize {
        1
    }
    #[inline(always)]
    fn advance(&mut self) {}
    #[inline(always)]
    fn reset_gate_chunk_offset(&mut self) {
        self.chunk_offset = PerChunkOffset::zero();
    }
    #[inline(always)]
    fn offset_for_next_chunk(&mut self, chunk_offset: &PerChunkOffset) {
        self.chunk_offset.add_offset(chunk_offset);
    }
    #[inline(always)]
    fn set_constants_offset(&mut self, offset: usize) {
        self.constants_offset = offset;
    }
}

use crate::cs::implementations::polynomial::lde::*;
use crate::cs::traits::destination_view::GateEvaluationReducingDestination;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct BufferedGateEvaluationReducingDestinationChunk<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F> = F,
> {
    pub chunks_iterator: LdeIterator,
    pub current_selector_idx: usize,
    pub selectors: Vec<ArcGenericLdeStorage<F, P>>,
    pub destination: GateEvaluationReducingDestination<F, P>,
    pub work_buffer: [P; 2],
    base_challenge_offset: usize,
    current_challenge_offset: usize,
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>>
    BufferedGateEvaluationReducingDestinationChunk<F, P>
{
    pub fn set_challenge_offset(&mut self, offset: usize) {
        debug_assert_eq!(self.base_challenge_offset, 0);
        debug_assert_eq!(self.current_challenge_offset, 0);

        self.base_challenge_offset = offset;
        self.current_challenge_offset = offset;
    }

    #[inline(always)]
    pub fn proceed_to_next_gate(&mut self) {
        // we multiply currently accumulated set by selector and accumulate
        let ctx = &mut self.destination.ctx;
        let (outer, inner) = self.chunks_iterator.current();
        let gate_selector_value = if self.selectors.is_empty() {
            P::one(ctx)
        } else {
            self.selectors[self.current_selector_idx].storage[outer].storage[inner]
        };

        debug_assert_eq!(
            self.destination.quotient_buffers.len(),
            self.work_buffer.len()
        );

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

        // mul by selector once
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

        // proceed to next selector for next set of terms.
        // Note that it's ok to set it 1 beyond the bound
        self.current_selector_idx += 1;
    }
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>>
    GateEvaluationReducingDestination<F, P>
{
    pub fn into_buffering_chunks(
        &self,
        num_workers: usize,
        ordered_selectors: Vec<ArcGenericLdeStorage<F, P>>,
    ) -> Vec<BufferedGateEvaluationReducingDestinationChunk<F, P>> {
        debug_assert_eq!(
            self.quotient_buffers[0].len(),
            ordered_selectors[0].outer_len()
        );
        debug_assert_eq!(
            self.quotient_buffers[0][0].len(),
            ordered_selectors[0].inner_len()
        );
        let lde_iterators = ordered_selectors[0].compute_chunks_for_num_workers(num_workers);
        let mut ctx = self.ctx;

        let mut result = Vec::with_capacity(num_workers);
        let zero = P::zero(&mut ctx);
        for subiterator in lde_iterators.into_iter() {
            let chunk = BufferedGateEvaluationReducingDestinationChunk {
                destination: self.clone(),
                chunks_iterator: subiterator,
                work_buffer: [zero; 2],
                selectors: ordered_selectors.clone(),
                base_challenge_offset: 0,
                current_challenge_offset: 0,
                current_selector_idx: 0,
            };

            result.push(chunk);
        }

        debug_assert!(result.len() <= num_workers);

        result
    }

    pub fn into_buffering_chunks_without_selector(
        &self,
        num_workers: usize,
    ) -> Vec<BufferedGateEvaluationReducingDestinationChunk<F, P>> {
        let lde_iterators = LdeIterator::chunk_lde_storage_for_num_workers(
            self.quotient_buffers[0].len(),
            self.quotient_buffers[0][0].len(),
            num_workers,
        );

        let mut ctx = self.ctx;

        let mut result = Vec::with_capacity(num_workers);
        let zero = P::zero(&mut ctx);
        for subiterator in lde_iterators.into_iter() {
            let chunk = BufferedGateEvaluationReducingDestinationChunk {
                destination: self.clone(),
                chunks_iterator: subiterator,
                work_buffer: [zero; 2],
                selectors: vec![],
                base_challenge_offset: 0,
                current_challenge_offset: 0,
                current_selector_idx: 0,
            };

            result.push(chunk);
        }

        debug_assert!(result.len() <= num_workers);

        result
    }
}

use crate::cs::traits::destination_view::*;

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>>
    EvaluationDestination<F, P> for BufferedGateEvaluationReducingDestinationChunk<F, P>
{
    #[inline(always)]
    fn push_evaluation_result(&mut self, value: P, _ctx: &mut P::Context) {
        if crate::config::DEBUG_SATISFIABLE {
            let (outer, inner) = self.chunks_iterator.current();
            if outer == 0 {
                let gate_selector_value = if self.selectors.is_empty() {
                    P::one(&mut P::Context::placeholder())
                } else {
                    self.selectors[self.current_selector_idx].storage[outer].storage[inner]
                };

                // now we need to split and check individual terms

                let selector = [gate_selector_value];
                let value = [value];
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
        }

        // simultaneously reduce and accumulate.
        // We take a term from the current gate (that only depends on witness, and so is deterministic),
        // then multiply by independent challenges and place into corresponding independent accumulators to
        // make something like alpha * term0 + alpha^2 * term1 + ...
        // Later of if necessary those terms will be multiplied by the corresponding selector
        let ctx = &mut self.destination.ctx;
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

        self.work_buffer[0].add_assign(&c0, ctx);
        self.work_buffer[1].add_assign(&c1, ctx);

        self.current_challenge_offset += 1;
    }
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>>
    EvaluationDestinationDrivable<F, P> for BufferedGateEvaluationReducingDestinationChunk<F, P>
{
    #[inline]
    fn expected_num_iterations(&self) -> usize {
        self.chunks_iterator.num_iterations()
    }
    #[inline(always)]
    fn advance(&mut self, _ctx: &mut P::Context) {
        self.current_selector_idx = 0;
        self.chunks_iterator.advance();
        self.current_challenge_offset = self.base_challenge_offset;
    }
}
