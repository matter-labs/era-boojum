use crate::field::traits::field_like::TrivialContext;

use super::round_function::*;
use super::*;

use derivative::*;

/// A generic wrapper over an algebraic sponge hash function.
/// Can use either absorption mode and is capable of performing any
/// round function that conforms to the [`AlgebraicRoundFunctionWithParams`] trait.
#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AlgebraicSponge<
    F: PrimeField,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    R: AlgebraicRoundFunctionWithParams<F, AW, SW, CW>,
> {
    pub(crate) buffer: [F; AW],
    pub(crate) filled: usize,
    pub(crate) state: [F; SW],
    pub(crate) round_function: R,
    pub(crate) mode: AbsorptionMode,
}

impl<
        F: PrimeField,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        R: AlgebraicRoundFunctionWithParams<F, AW, SW, CW>,
    > Default for AlgebraicSponge<F, AW, SW, CW, R>
where
    R: Default,
{
    fn default() -> Self {
        Self::new(R::default(), AbsorptionMode::Overwrite)
    }
}

impl<
        F: PrimeField,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        R: AlgebraicRoundFunctionWithParams<F, AW, SW, CW>,
    > AlgebraicSponge<F, AW, SW, CW, R>
{
    #[inline]
    pub fn new(round_function: R, mode: AbsorptionMode) -> Self {
        Self {
            buffer: [F::ZERO; AW],
            filled: 0,
            state: round_function.initial_state(),
            round_function,
            mode,
        }
    }

    pub fn absorb(&mut self, values: &[F]) {
        let mut rest = values;
        // quickly fill the unfilled, then do full absorbtion rounds, then save the rest
        if rest.len() > AW - self.filled {
            self.filled = 0;
            let (to_use, other) = rest.split_at(AW - self.filled);
            rest = other;
            for (dst, src) in self.state[..AW]
                .iter_mut()
                .zip(self.buffer[..self.filled].iter().chain(to_use.iter()))
            {
                match self.mode {
                    AbsorptionMode::Addition => {
                        dst.add_assign(src);
                    }
                    AbsorptionMode::Overwrite => {
                        *dst = *src;
                    }
                }
            }

            self.round_function.round_function(&mut self.state);
        }
        debug_assert!(self.filled == 0);
        let mut it = rest.chunks_exact(AW);
        for chunk in &mut it {
            for (dst, src) in self.state[..AW].iter_mut().zip(chunk.iter()) {
                match self.mode {
                    AbsorptionMode::Addition => {
                        dst.add_assign(src);
                    }
                    AbsorptionMode::Overwrite => {
                        *dst = *src;
                    }
                }
            }

            self.round_function.round_function(&mut self.state);
        }

        let tail = it.remainder();
        self.filled += tail.len();
        for (dst, src) in self.buffer.iter_mut().zip(tail.iter()) {
            *dst = *src; // save only for a future
        }
    }

    pub fn finalize<const N: usize>(self) -> [F; N] {
        let Self {
            buffer,
            filled,
            state,
            round_function,
            mode,
        } = self;

        let mut state = state;

        if filled > 0 {
            for (dst, src) in state[..filled].iter_mut().zip(buffer[..filled].iter()) {
                match mode {
                    AbsorptionMode::Addition => {
                        dst.add_assign(src);
                    }
                    AbsorptionMode::Overwrite => {
                        *dst = *src;
                    }
                }
            }

            match mode {
                AbsorptionMode::Addition => {}
                AbsorptionMode::Overwrite => {
                    for dst in state[filled..AW].iter_mut() {
                        *dst = F::ZERO;
                    }
                }
            }

            round_function.round_function(&mut state);
        }

        round_function.state_into_commitment_fixed::<N>(&state)
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GenericAlgebraicSpongeState<T, const AW: usize, const SW: usize, const CW: usize> {
    pub(crate) buffer: [T; AW],
    pub(crate) filled: usize,
    pub(crate) state: [T; SW],
}

impl<T, const AW: usize, const SW: usize, const CW: usize>
    GenericAlgebraicSpongeState<T, AW, SW, CW>
{
    pub fn empty_from_filler(filler: T) -> Self
    where
        T: Copy,
    {
        Self {
            buffer: [filler; AW],
            filled: 0,
            state: [filler; SW],
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GenericAlgebraicSponge<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    R: GenericAlgebraicRoundFunction<F, P, AW, SW, CW>,
    M: AbsorptionModeTrait<P>,
> {
    pub(crate) buffer: [P; AW],
    pub(crate) filled: usize,
    pub(crate) state: [P; SW],
    _marker: std::marker::PhantomData<(R, M)>,
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        R: GenericAlgebraicRoundFunction<F, P, AW, SW, CW>,
        M: AbsorptionModeTrait<P>,
    > Default for GenericAlgebraicSponge<F, P, AW, SW, CW, R, M>
where
    P::Context: TrivialContext,
{
    fn default() -> Self {
        Self::new(&mut P::Context::placeholder())
    }
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        R: GenericAlgebraicRoundFunction<F, P, AW, SW, CW>,
        M: AbsorptionModeTrait<P>,
    > GenericAlgebraicSponge<F, P, AW, SW, CW, R, M>
{
    #[inline]
    pub fn new(ctx: &mut P::Context) -> Self {
        Self {
            buffer: [P::zero(ctx); AW],
            filled: 0,
            state: R::initial_state(),
            _marker: std::marker::PhantomData,
        }
    }

    pub fn absorb_single(&mut self, value: &P) {
        debug_assert!(self.filled < AW);
        self.buffer[self.filled] = *value;
        self.filled += 1;
        if self.filled == AW {
            for (dst, src) in self.state[..AW]
                .iter_mut()
                .zip(self.buffer[..self.filled].iter())
            {
                M::absorb(dst, src);
            }

            R::round_function(&mut self.state);
            self.filled = 0;
        }
    }

    pub fn absorb(&mut self, values: &[P]) {
        debug_assert!(self.filled < AW);

        let mut rest = values;
        // quickly fill the unfilled, then do full absorption rounds, then save the rest
        if rest.len() >= AW - self.filled {
            let (to_use, other) = rest.split_at(AW - self.filled);
            rest = other;
            for (dst, src) in self.state[..AW]
                .iter_mut()
                .zip(self.buffer[..self.filled].iter().chain(to_use.iter()))
            {
                M::absorb(dst, src);
            }

            R::round_function(&mut self.state);
            self.filled = 0;
        } else {
            // we only have enough to place into buffer

            for (dst, src) in self.buffer[self.filled..].iter_mut().zip(rest.iter()) {
                *dst = *src; // save only for a future
            }
            self.filled += rest.len();
            debug_assert!(self.filled < AW);

            return;
        }
        debug_assert!(self.filled == 0);
        let mut it = rest.chunks_exact(AW);
        for chunk in &mut it {
            for (dst, src) in self.state[..AW].iter_mut().zip(chunk.iter()) {
                M::absorb(dst, src);
            }

            R::round_function(&mut self.state);
        }

        let tail = it.remainder();
        self.filled += tail.len();
        for (dst, src) in self.buffer.iter_mut().zip(tail.iter()) {
            *dst = *src; // save only for a future
        }
    }

    // Useful only for cases when we need to get multiple outputs
    pub fn run_round_function(&mut self) {
        assert_eq!(self.filled, 0);
        R::round_function(&mut self.state);
    }

    pub fn try_get_commitment<const N: usize>(&self) -> Option<[P; N]> {
        if self.filled == 0 {
            Some(R::state_into_commitment::<N>(&self.state))
        } else {
            None
        }
    }

    pub fn finalize<const N: usize>(self) -> [P; N] {
        let Self {
            buffer,
            filled,
            state,
            ..
        } = self;

        let mut state = state;

        if filled > 0 {
            for (dst, src) in state[..filled].iter_mut().zip(buffer[..filled].iter()) {
                M::absorb(dst, src);
            }

            for dst in state[filled..AW].iter_mut() {
                M::pad(dst);
            }

            R::round_function(&mut state);
        }

        R::state_into_commitment::<N>(&state)
    }

    pub fn finalize_reset<const N: usize>(&mut self) -> [P; N] {
        // reset
        let mut state = std::mem::replace(&mut self.state, R::initial_state());
        let filled = self.filled;
        self.filled = 0;

        // run round function if necessary
        if filled > 0 {
            for (dst, src) in state[..filled].iter_mut().zip(self.buffer[..filled].iter()) {
                M::absorb(dst, src);
            }

            for dst in state[filled..AW].iter_mut() {
                M::pad(dst);
            }

            R::round_function(&mut state);
        }

        R::state_into_commitment::<N>(&state)
    }
}

pub type SimpleAlgebraicSponge<F, const AW: usize, const SW: usize, const CW: usize, R, M> =
    GenericAlgebraicSponge<F, F, AW, SW, CW, R, M>;

use crate::implementations::poseidon_goldilocks_naive::PoseidonGoldilocks;

pub type GoldilocksPoseidonSponge<M> =
    SimpleAlgebraicSponge<GoldilocksField, 8, 12, 4, PoseidonGoldilocks, M>;

use crate::implementations::poseidon2::Poseidon2Goldilocks;

pub type GoldilocksPoseidon2Sponge<M> =
    SimpleAlgebraicSponge<GoldilocksField, 8, 12, 4, Poseidon2Goldilocks, M>;
