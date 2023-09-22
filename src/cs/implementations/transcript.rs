use crate::field::goldilocks::GoldilocksField;
use crate::utils::LSBIterator;
use crate::{cs::traits::GoodAllocator, field::PrimeField};

use super::*;

pub trait Transcript<F: PrimeField>: Clone + Send + Sync + std::fmt::Debug {
    type CompatibleCap: Clone;
    type TransciptParameters: Clone + Send + Sync + std::fmt::Debug;

    const IS_ALGEBRAIC: bool = true;

    fn new(params: Self::TransciptParameters) -> Self;
    fn witness_field_elements(&mut self, field_els: &[F]);
    fn witness_merkle_tree_cap(&mut self, cap: &[Self::CompatibleCap]);
    fn get_challenge(&mut self) -> F;
    fn get_multiple_challenges_fixed<const N: usize>(&mut self) -> [F; N] {
        let mut result = [F::ZERO; N];
        for dst in result.iter_mut() {
            *dst = self.get_challenge();
        }

        result
    }
    fn get_multiple_challenges<B: GoodAllocator>(&mut self, num_challenges: usize) -> Vec<F, B> {
        let mut result = Vec::with_capacity_in(num_challenges, B::default());
        for _ in 0..num_challenges {
            let chal = self.get_challenge();
            result.push(chal);
        }

        result
    }
    fn get_challenge_bytes(&mut self, _num_bytes: usize) -> Vec<u8> {
        if Self::IS_ALGEBRAIC {
            unimplemented!("Should not be called on algebraic transcripts")
        } else {
            todo!("Should be implemented if non-algebraic")
        }
    }
}

use crate::algebraic_props::round_function::*;
use crate::algebraic_props::sponge::*;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct AlgebraicSpongeBasedTranscript<
    F: SmallField,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    R: AlgebraicRoundFunction<F, AW, SW, CW>,
    M: AbsorptionModeTrait<F>,
> {
    buffer: Vec<F>,
    available_challenges: Vec<F>,
    #[derivative(Debug = "ignore")]
    sponge: SimpleAlgebraicSponge<F, AW, SW, CW, R, M>,
}

impl<
        F: SmallField,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        R: AlgebraicRoundFunction<F, AW, SW, CW>,
        M: AbsorptionModeTrait<F>,
    > Transcript<F> for AlgebraicSpongeBasedTranscript<F, AW, SW, CW, R, M>
{
    type CompatibleCap = [F; CW];
    type TransciptParameters = ();
    fn new(_params: Self::TransciptParameters) -> Self {
        Self {
            buffer: Vec::new(),
            available_challenges: Vec::new(),
            sponge: SimpleAlgebraicSponge::<F, AW, SW, CW, R, M>::default(),
        }
    }
    fn witness_field_elements(&mut self, field_els: &[F]) {
        self.buffer.extend_from_slice(field_els);
    }
    fn witness_merkle_tree_cap(&mut self, cap: &[Self::CompatibleCap]) {
        for el in cap.iter() {
            // log!("Witnessing cap element {:?}", el);
            self.witness_field_elements(&el[..]);
        }
    }
    fn get_challenge(&mut self) -> F {
        assert_eq!(self.sponge.filled, 0);

        if self.buffer.is_empty() {
            if self.available_challenges.len() > 0 {
                let next_challenge = self.available_challenges.drain(..1).next().unwrap();
                // log!("Retuning challenge {}", next_challenge);

                return next_challenge;
            } else {
                self.sponge.run_round_function();
                let new_set = self
                    .sponge
                    .try_get_commitment::<AW>()
                    .expect("must have no pending elements in the buffer");
                self.available_challenges = new_set.to_vec();

                return self.get_challenge();
            }
        }

        let mut to_absorb = std::mem::take(&mut self.buffer);
        // we do rescue prime padding and absorb
        to_absorb.push(F::ONE);
        let mut multiple = to_absorb.len() / AW;
        if to_absorb.len() % AW != 0 {
            multiple += 1;
        }
        to_absorb.resize(multiple * AW, F::ZERO);
        for chunk in to_absorb.array_chunks::<AW>() {
            self.sponge.absorb(chunk);
            assert_eq!(self.sponge.filled, 0);
        }

        let commitment = self.sponge.finalize::<AW>();
        self.available_challenges = commitment.to_vec();

        // to avoid duplication
        self.get_challenge()
    }
}

use crate::implementations::poseidon_goldilocks_naive::PoseidonGoldilocks;

pub type GoldilocksPoisedonTranscript = AlgebraicSpongeBasedTranscript<
    GoldilocksField,
    8,
    12,
    4,
    PoseidonGoldilocks,
    AbsorptionModeOverwrite,
>;

use crate::implementations::poseidon2::Poseidon2Goldilocks;

pub type GoldilocksPoisedon2Transcript = AlgebraicSpongeBasedTranscript<
    GoldilocksField,
    8,
    12,
    4,
    Poseidon2Goldilocks,
    AbsorptionModeOverwrite,
>;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct Blake2sTranscript {
    inner: blake2::Blake2s256,
    buffer: Vec<u8>,
    available_challenge_bytes: Vec<u8>,
}

use blake2::Digest;

impl<F: SmallField> Transcript<F> for Blake2sTranscript {
    type CompatibleCap = [u8; 32];
    type TransciptParameters = ();

    const IS_ALGEBRAIC: bool = false;

    fn new(_params: Self::TransciptParameters) -> Self {
        Self {
            inner: blake2::Blake2s256::new(),
            buffer: Vec::with_capacity(64),
            available_challenge_bytes: Vec::with_capacity(32),
        }
    }
    fn witness_field_elements(&mut self, field_els: &[F]) {
        for el in field_els.iter() {
            self.buffer.extend(el.as_u64_reduced().to_le_bytes());
        }
    }
    fn witness_merkle_tree_cap(&mut self, cap: &[Self::CompatibleCap]) {
        for el in cap.iter() {
            self.buffer.extend_from_slice(&el[..]);
        }
    }
    fn get_challenge(&mut self) -> F {
        if self.buffer.is_empty() == false {
            self.inner.update(&self.buffer);
            self.buffer.clear();
            self.available_challenge_bytes.clear();

            // reseed
            let mut output = [0u8; 32];
            let raw_output = self.inner.finalize_reset();
            output[..].copy_from_slice(raw_output.as_slice());

            self.inner.update(output);
            self.available_challenge_bytes.extend(output);
        }

        if self.available_challenge_bytes.is_empty() == false {
            assert!(self.available_challenge_bytes.len() % 8 == 0);
            let mut buffer = [0u8; 8];
            for (dst, src) in buffer
                .iter_mut()
                .zip(self.available_challenge_bytes.drain(..8))
            {
                *dst = src;
            }
            let as_u64 = u64::from_le_bytes(buffer);
            let challenge = F::from_u64_with_reduction(as_u64);

            challenge
        } else {
            // reseed
            let mut output = [0u8; 32];
            let raw_output = self.inner.finalize_reset();
            output[..].copy_from_slice(raw_output.as_slice());

            self.inner.update(output);
            self.available_challenge_bytes.extend(output);

            assert!(self.available_challenge_bytes.is_empty() == false);
            Transcript::<F>::get_challenge(self)
        }
    }

    fn get_challenge_bytes(&mut self, num_bytes: usize) -> Vec<u8> {
        if self.buffer.is_empty() == false {
            self.inner.update(&self.buffer);
            self.buffer.clear();
            self.available_challenge_bytes.clear();

            // reseed
            let mut output = [0u8; 32];
            let raw_output = self.inner.finalize_reset();
            output[..].copy_from_slice(raw_output.as_slice());

            self.inner.update(output);
            self.available_challenge_bytes.extend(output);
        }

        if self.available_challenge_bytes.len() >= num_bytes {
            let result: Vec<u8> = self.available_challenge_bytes.drain(..num_bytes).collect();

            result
        } else {
            // reseed
            let mut output = [0u8; 32];
            let raw_output = self.inner.finalize_reset();
            output[..].copy_from_slice(raw_output.as_slice());

            self.inner.update(output);
            self.available_challenge_bytes.extend(output);

            assert!(self.available_challenge_bytes.is_empty() == false);
            Transcript::<F>::get_challenge_bytes(self, num_bytes)
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct Keccak256Transcript {
    inner: sha3::Keccak256,
    buffer: Vec<u8>,
    available_challenge_bytes: Vec<u8>,
}

impl<F: SmallField> Transcript<F> for Keccak256Transcript {
    type CompatibleCap = [u8; 32];
    type TransciptParameters = ();

    const IS_ALGEBRAIC: bool = false;

    fn new(_params: Self::TransciptParameters) -> Self {
        Self {
            inner: sha3::Keccak256::new(),
            buffer: Vec::with_capacity(64),
            available_challenge_bytes: Vec::with_capacity(32),
        }
    }
    fn witness_field_elements(&mut self, field_els: &[F]) {
        for el in field_els.iter() {
            self.buffer.extend(el.as_u64_reduced().to_le_bytes());
        }
    }
    fn witness_merkle_tree_cap(&mut self, cap: &[Self::CompatibleCap]) {
        for el in cap.iter() {
            self.buffer.extend_from_slice(&el[..]);
        }
    }
    fn get_challenge(&mut self) -> F {
        if self.buffer.is_empty() == false {
            self.inner.update(&self.buffer);
            self.buffer.clear();
            self.available_challenge_bytes.clear();

            // reseed
            let mut output = [0u8; 32];
            let raw_output = self.inner.finalize_reset();
            output[..].copy_from_slice(raw_output.as_slice());

            self.inner.update(output);
            self.available_challenge_bytes.extend(output);
        }

        if self.available_challenge_bytes.is_empty() == false {
            assert!(self.available_challenge_bytes.len() % 8 == 0);
            let mut buffer = [0u8; 8];
            for (dst, src) in buffer
                .iter_mut()
                .zip(self.available_challenge_bytes.drain(..8))
            {
                *dst = src;
            }
            let as_u64 = u64::from_le_bytes(buffer);
            let challenge = F::from_u64_with_reduction(as_u64);

            challenge
        } else {
            // reseed
            let mut output = [0u8; 32];
            let raw_output = self.inner.finalize_reset();
            output[..].copy_from_slice(raw_output.as_slice());

            self.inner.update(output);
            self.available_challenge_bytes.extend(output);

            assert!(self.available_challenge_bytes.is_empty() == false);
            Transcript::<F>::get_challenge(self)
        }
    }

    fn get_challenge_bytes(&mut self, num_bytes: usize) -> Vec<u8> {
        if self.buffer.is_empty() == false {
            self.inner.update(&self.buffer);
            self.buffer.clear();
            self.available_challenge_bytes.clear();

            // reseed
            let mut output = [0u8; 32];
            let raw_output = self.inner.finalize_reset();
            output[..].copy_from_slice(raw_output.as_slice());

            self.inner.update(output);
            self.available_challenge_bytes.extend(output);
        }

        if self.available_challenge_bytes.len() >= num_bytes {
            let result: Vec<u8> = self.available_challenge_bytes.drain(..num_bytes).collect();

            result
        } else {
            // reseed
            let mut output = [0u8; 32];
            let raw_output = self.inner.finalize_reset();
            output[..].copy_from_slice(raw_output.as_slice());

            self.inner.update(output);
            self.available_challenge_bytes.extend(output);

            assert!(self.available_challenge_bytes.is_empty() == false);
            Transcript::<F>::get_challenge_bytes(self, num_bytes)
        }
    }
}

pub struct BoolsBuffer {
    pub available: Vec<bool>,
    pub max_needed: usize,
}

impl BoolsBuffer {
    pub fn get_bits<F: SmallField, T: Transcript<F>>(
        &mut self,
        transcript: &mut T,
        num_bits: usize,
    ) -> Vec<bool> {
        if self.available.len() >= num_bits {
            let give: Vec<_> = self.available.drain(..num_bits).collect();

            give
        } else {
            if T::IS_ALGEBRAIC {
                // we use some heuristics to only take part of the bits from field
                // element to get better uniformity of query indexes
                let bits_avaiable = F::CHAR_BITS - self.max_needed;

                // get 1 field element from transcript
                let field_el = transcript.get_challenge();
                let field_el_u64 = field_el.as_u64_reduced();
                let t = [field_el_u64];
                let mut lsb_iterator = LSBIterator::new(&t);
                for _ in 0..bits_avaiable {
                    let bit = lsb_iterator.next().unwrap();
                    self.available.push(bit);
                }
            } else {
                // we assume that it produced BYTES and those are uniform
                let bytes: [u8; 8] = transcript
                    .get_challenge_bytes(8)
                    .try_into()
                    .expect("length must match");
                let as_u64 = u64::from_le_bytes(bytes);
                let t = [as_u64];
                let mut lsb_iterator = LSBIterator::new(&t);
                for _ in 0..64 {
                    let bit = lsb_iterator.next().unwrap();
                    self.available.push(bit);
                }
            }

            self.get_bits(transcript, num_bits)
        }
    }
}
