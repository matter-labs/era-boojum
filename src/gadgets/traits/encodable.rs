use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::Variable;
use crate::field::SmallField;
use crate::gadgets::traits::allocatable::{CSAllocatable, CSAllocatableExt};

pub trait CircuitEncodable<F: SmallField, const N: usize>:
    'static + Send + Sync + CSAllocatable<F>
{
    fn encode<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> [Variable; N];
}

pub trait WitnessEncodable<F: SmallField, const N: usize>:
    'static + Send + Sync + CSAllocatable<F>
{
    fn encode_witness(witness: &Self::Witness, dst: &mut Vec<F>);
}

pub trait CircuitEncodableExt<F: SmallField, const N: usize>:
    CircuitEncodable<F, N> + CSAllocatableExt<F>
{
}

pub trait CircuitVarLengthEncodable<F: SmallField>:
    'static + Send + Sync + CSAllocatable<F>
{
    fn encoding_length(&self) -> usize;
    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, cs: &mut CS, dst: &mut Vec<Variable>);
}

pub trait WitnessVarLengthEncodable<F: SmallField>:
    'static + Send + Sync + CSAllocatable<F>
{
    fn witness_encoding_length(witness: &Self::Witness) -> usize;
    fn encode_witness_to_buffer(witness: &Self::Witness, dst: &mut Vec<F>);
}

// unfortunately default implementation is impossible as compiler can not have constraint "for all N"

// impl<F: SmallField, const N: usize, T: CircuitEncodable<F, N>> CircuitVarLengthEncodable<F> for T {
//     #[inline(always)]
//     fn encoding_length(&self) -> usize {
//         N
//     }
//     fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, cs: &mut CS, dst: &mut Vec<Variable>) {
//         todo!();
//     }
// }

// But we can still extend for case of arrays
impl<F: SmallField, const N: usize, T: CircuitVarLengthEncodable<F>> CircuitVarLengthEncodable<F>
    for [T; N]
{
    #[inline(always)]
    fn encoding_length(&self) -> usize {
        debug_assert!(N > 0);

        N * self[0].encoding_length()
    }
    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, cs: &mut CS, dst: &mut Vec<Variable>) {
        for el in self.iter() {
            el.encode_to_buffer(cs, dst);
        }
    }
}

impl<F: SmallField, const N: usize, T: WitnessVarLengthEncodable<F>> WitnessVarLengthEncodable<F>
    for [T; N]
{
    fn witness_encoding_length(witness: &Self::Witness) -> usize {
        debug_assert!(N > 0);

        N * T::witness_encoding_length(&witness[0])
    }

    fn encode_witness_to_buffer(witness: &Self::Witness, dst: &mut Vec<F>) {
        for el in witness.iter() {
            T::encode_witness_to_buffer(el, dst);
        }
    }
}

impl<F: SmallField> CircuitVarLengthEncodable<F> for () {
    #[inline(always)]
    fn encoding_length(&self) -> usize {
        0
    }
    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, _cs: &mut CS, _dst: &mut Vec<Variable>) {
        // do nothing
    }
}

impl<F: SmallField> WitnessVarLengthEncodable<F> for () {
    #[inline(always)]
    fn witness_encoding_length(_witness: &Self::Witness) -> usize {
        0
    }
    fn encode_witness_to_buffer(_witness: &Self::Witness, _dst: &mut Vec<F>) {
        // do nothing
    }
}
