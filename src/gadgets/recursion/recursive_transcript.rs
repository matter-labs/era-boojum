use super::*;
use crate::algebraic_props::sponge::GenericAlgebraicSpongeState;
use crate::cs::implementations::transcript::Transcript;
use crate::cs::traits::cs::ConstraintSystem;
use crate::field::goldilocks::GoldilocksField;
use crate::gadgets::num::Num;

pub trait CircuitTranscript<F: SmallField>: Clone + Send + Sync + std::fmt::Debug {
    type CircuitCompatibleCap: Clone;
    type TransciptParameters: Clone + Send + Sync;

    const IS_ALGEBRAIC: bool = true;

    fn new<CS: ConstraintSystem<F>>(cs: &mut CS, params: Self::TransciptParameters) -> Self;
    fn witness_field_elements<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        field_els: &[Num<F>],
    );
    fn witness_merkle_tree_cap<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        cap: &[Self::CircuitCompatibleCap],
    );
    fn get_challenge<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Num<F>;
    fn get_multiple_challenges_fixed<CS: ConstraintSystem<F>, const N: usize>(
        &mut self,
        cs: &mut CS,
    ) -> [Num<F>; N] {
        let result = std::array::from_fn(|_| self.get_challenge(cs));

        result
    }
    fn get_multiple_challenges<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        num_challenges: usize,
    ) -> Vec<Num<F>> {
        let mut result = Vec::with_capacity(num_challenges);
        for _ in 0..num_challenges {
            let chal = self.get_challenge(cs);
            result.push(chal);
        }

        result
    }
    fn get_challenge_bytes<CS: ConstraintSystem<F>>(
        &mut self,
        _cs: &mut CS,
        _num_bytes: usize,
    ) -> Vec<u8> {
        if Self::IS_ALGEBRAIC {
            unimplemented!("Should not be called on algebraic transcripts")
        } else {
            todo!("Should be implemented if non-algebraic")
        }
    }
}

pub trait RecursiveTranscript<F: SmallField>: Transcript<F> {
    type CircuitReflection: CircuitTranscript<
        F,
        TransciptParameters = <Self as Transcript<F>>::TransciptParameters,
    >;
}

use crate::gadgets::boolean::Boolean;
use crate::gadgets::traits::round_function::CircuitRoundFunction;

pub(crate) struct BoolsBuffer<F: SmallField> {
    pub(crate) available: Vec<Boolean<F>>,
    pub(crate) max_needed: usize,
}

impl<F: SmallField> BoolsBuffer<F> {
    pub fn get_bits<CS: ConstraintSystem<F>, T: CircuitTranscript<F>>(
        &mut self,
        cs: &mut CS,
        transcript: &mut T,
        num_bits: usize,
    ) -> Vec<Boolean<F>> {
        if self.available.len() >= num_bits {
            let give: Vec<_> = self.available.drain(..num_bits).collect();

            give
        } else {
            let bits_avaiable = F::CHAR_BITS - self.max_needed;

            // get 1 field element form transcript
            let field_el = transcript.get_challenge(cs);
            let el_bits = field_el.spread_into_bits::<CS, 64>(cs);
            let mut lsb_iterator = el_bits.iter();

            for _ in 0..bits_avaiable {
                let bit = lsb_iterator.next().unwrap();
                self.available.push(*bit);
            }

            self.get_bits(cs, transcript, num_bits)
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct CircuitAlgebraicSpongeBasedTranscript<
    F: SmallField,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    R: CircuitRoundFunction<F, AW, SW, CW>,
> {
    buffer: Vec<Num<F>>,
    available_challenges: Vec<Num<F>>,
    #[derivative(Debug = "ignore")]
    sponge: GenericAlgebraicSpongeState<Num<F>, AW, SW, CW>,
    _marker: std::marker::PhantomData<R>,
}

impl<
        F: SmallField,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        R: CircuitRoundFunction<F, AW, SW, CW>,
    > CircuitAlgebraicSpongeBasedTranscript<F, AW, SW, CW, R>
{
    pub fn try_get_commitment<const N: usize>(&self) -> Option<[Num<F>; N]> {
        if self.sponge.filled == 0 {
            Some(
                R::state_into_commitment::<N>(&self.sponge.state.map(|el| el.get_variable()))
                    .map(|el| Num::from_variable(el)),
            )
        } else {
            None
        }
    }

    pub fn absorb<const N: usize>(&mut self) -> Option<[Num<F>; N]> {
        if self.sponge.filled == 0 {
            Some(
                R::state_into_commitment::<N>(&self.sponge.state.map(|el| el.get_variable()))
                    .map(|el| Num::from_variable(el)),
            )
        } else {
            None
        }
    }
}

impl<
        F: SmallField,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        R: CircuitRoundFunction<F, AW, SW, CW>,
    > CircuitTranscript<F> for CircuitAlgebraicSpongeBasedTranscript<F, AW, SW, CW, R>
{
    type CircuitCompatibleCap = [Num<F>; CW];
    type TransciptParameters = ();

    fn new<CS: ConstraintSystem<F>>(cs: &mut CS, _params: Self::TransciptParameters) -> Self {
        let filler = Num::zero(cs);
        let sponge = GenericAlgebraicSpongeState::empty_from_filler(filler);

        Self {
            buffer: Vec::new(),
            available_challenges: Vec::new(),
            sponge,
            _marker: std::marker::PhantomData,
        }
    }
    fn witness_field_elements<CS: ConstraintSystem<F>>(
        &mut self,
        _cs: &mut CS,
        field_els: &[Num<F>],
    ) {
        self.buffer.extend_from_slice(field_els);
    }
    fn witness_merkle_tree_cap<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        cap: &[Self::CircuitCompatibleCap],
    ) {
        for el in cap.iter() {
            self.witness_field_elements(cs, &el[..]);
        }
    }
    fn get_challenge<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Num<F> {
        assert_eq!(self.sponge.filled, 0);

        if self.buffer.is_empty() {
            if self.available_challenges.len() > 0 {
                let next_challenge = self.available_challenges.drain(..1).next().unwrap();
                // log!("Retuning challenge {}", next_challenge);

                return next_challenge;
            } else {
                self.sponge.state = R::compute_round_function_over_nums(cs, self.sponge.state);
                let new_set = self
                    .try_get_commitment::<AW>()
                    .expect("must have no pending elements in the buffer");
                self.available_challenges = new_set.to_vec();

                return self.get_challenge(cs);
            }
        }

        let mut to_absorb = std::mem::take(&mut self.buffer);
        let one_num = Num::allocated_constant(cs, F::ONE);
        let zero_num = Num::zero(cs);
        // we do rescue prime padding and absorb
        to_absorb.push(one_num);
        let mut multiple = to_absorb.len() / AW;
        if to_absorb.len() % AW != 0 {
            multiple += 1;
        }
        to_absorb.resize(multiple * AW, zero_num);
        for chunk in to_absorb.array_chunks::<AW>() {
            let els_to_keep =
                R::split_capacity_elements(&self.sponge.state.map(|el| el.get_variable()))
                    .map(|el| Num::from_variable(el));
            self.sponge.state = R::absorb_with_replacement_over_nums(cs, *chunk, els_to_keep);
            self.sponge.state = R::compute_round_function_over_nums(cs, self.sponge.state);
        }

        let commitment = self
            .try_get_commitment::<AW>()
            .expect("must have no pending elements in the buffer");
        self.available_challenges = commitment.to_vec();

        // to avoid duplication
        self.get_challenge(cs)
    }
}

use crate::cs::implementations::transcript::GoldilocksPoisedon2Transcript;
use crate::implementations::poseidon2::Poseidon2Goldilocks;

pub type GoldilocksPoisedon2CircuitTranscript =
    CircuitAlgebraicSpongeBasedTranscript<GoldilocksField, 8, 12, 4, Poseidon2Goldilocks>;

impl RecursiveTranscript<GoldilocksField> for GoldilocksPoisedon2Transcript {
    type CircuitReflection = GoldilocksPoisedon2CircuitTranscript;
}
