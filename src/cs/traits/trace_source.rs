use super::*;
use crate::cs::traits::evaluator::PerChunkOffset;
use crate::field::PrimeField;

pub trait TraceSource<F: PrimeField, P: field::traits::field_like::PrimeFieldLike>:
    Send + Sync
{
    // // trick to have static PhantomData over this trait
    // type Tag: 'static + Send + Sync = ();

    fn get_variable_value(&self, variable_offset: usize) -> P;
    fn get_constant_value(&self, constant_offset: usize) -> P;
    fn get_witness_value(&self, witness_offset: usize) -> P;
    fn dump_current_row<A: GoodAllocator>(&self, dst: &mut Vec<P, A>);
}

pub trait TraceSourceDerivable<F: PrimeField, P: field::traits::field_like::PrimeFieldLike>:
    TraceSource<F, P> + Clone
{
    fn set_constants_offset(&mut self, offset: usize);
    fn offset_for_next_chunk(&mut self, chunk_offset: &PerChunkOffset);
    fn reset_gate_chunk_offset(&mut self);
    fn num_iterations(&self) -> usize;
    fn advance(&mut self);
}
