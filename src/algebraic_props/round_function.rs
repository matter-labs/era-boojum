use crate::field::SmallField;

use super::*;

use derivative::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AbsorptionMode {
    Addition = 0,
    Overwrite, // https://keccak.team/files/CSF-0.1.pdf - e.g. some info about this mode
}

pub trait AbsorptionModeTrait<T: Sized>:
    'static + Clone + Copy + Send + Sync + std::fmt::Debug + PartialEq + Eq
{
    fn absorb(dst: &mut T, src: &T);
    fn pad(dst: &mut T);
}

#[derive(Clone, Copy, Eq, Debug)]
pub struct AbsorptionModeAdd;

impl PartialEq<AbsorptionModeAdd> for AbsorptionModeAdd {
    fn eq(&self, _other: &AbsorptionModeAdd) -> bool {
        true
    }
}

impl<F: PrimeField> AbsorptionModeTrait<F> for AbsorptionModeAdd {
    #[inline(always)]
    fn absorb(dst: &mut F, src: &F) {
        dst.add_assign(src);
    }
    #[inline(always)]
    fn pad(_dst: &mut F) {}
}

#[derive(Clone, Copy, Eq, Debug)]
pub struct AbsorptionModeOverwrite;

impl PartialEq<AbsorptionModeOverwrite> for AbsorptionModeOverwrite {
    fn eq(&self, _other: &AbsorptionModeOverwrite) -> bool {
        true
    }
}

impl<F: PrimeField> AbsorptionModeTrait<F> for AbsorptionModeOverwrite {
    #[inline(always)]
    fn absorb(dst: &mut F, src: &F) {
        *dst = *src;
    }
    #[inline(always)]
    fn pad(dst: &mut F) {
        *dst = F::ZERO;
    }
}

pub trait AlgebraicRoundFunctionWithParams<
    F: PrimeField,
    const AW: usize,
    const SW: usize,
    const CW: usize,
>: Clone + Send + Sync
{
    fn round_function(&self, state: &mut [F; SW]);
    fn initial_state(&self) -> [F; SW];
    fn specialize_for_len(&self, len: u32, state: &mut [F; SW]);
    fn absorb_into_state(&self, state: &mut [F; SW], to_absorb: &[F; AW], mode: AbsorptionMode);
    fn state_get_commitment<'a>(&self, state: &'a [F; SW]) -> &'a [F];
    fn state_into_commitment_fixed<const N: usize>(&self, state: &[F; SW]) -> [F; N];
}

pub trait AlgebraicRoundFunction<F: PrimeField, const AW: usize, const SW: usize, const CW: usize>:
    'static + Clone + Copy + Send + Sync
{
    fn round_function(state: &mut [F; SW]);
    fn initial_state() -> [F; SW];
    fn specialize_for_len(len: u32, state: &mut [F; SW]);
    fn absorb_into_state<M: AbsorptionModeTrait<F>>(state: &mut [F; SW], to_absorb: &[F; AW]);
    fn state_into_commitment<const N: usize>(state: &[F; SW]) -> [F; N];
}

pub trait GenericAlgebraicRoundFunction<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
    const AW: usize,
    const SW: usize,
    const CW: usize,
>: 'static + Clone + Copy + Send + Sync
{
    fn round_function(state: &mut [P; SW]);
    fn initial_state() -> [P; SW];
    fn specialize_for_len(len: u32, state: &mut [P; SW]);
    fn absorb_into_state<M: AbsorptionModeTrait<F>>(state: &mut [P; SW], to_absorb: &[P; AW]);
    fn state_into_commitment<const N: usize>(state: &[P; SW]) -> [P; N];
}

// default impl

impl<
        F: SmallField,
        T: AlgebraicRoundFunction<F, AW, SW, CW>,
        const AW: usize,
        const SW: usize,
        const CW: usize,
    > GenericAlgebraicRoundFunction<F, F, AW, SW, CW> for T
{
    #[inline]
    fn round_function(state: &mut [F; SW]) {
        <T as AlgebraicRoundFunction<F, AW, SW, CW>>::round_function(state);
    }
    #[inline]
    fn initial_state() -> [F; SW] {
        <T as AlgebraicRoundFunction<F, AW, SW, CW>>::initial_state()
    }
    #[inline]
    fn specialize_for_len(len: u32, state: &mut [F; SW]) {
        <T as AlgebraicRoundFunction<F, AW, SW, CW>>::specialize_for_len(len, state);
    }
    #[inline]
    fn absorb_into_state<M: AbsorptionModeTrait<F>>(state: &mut [F; SW], to_absorb: &[F; AW]) {
        <T as AlgebraicRoundFunction<F, AW, SW, CW>>::absorb_into_state::<M>(state, to_absorb);
    }
    #[inline]
    fn state_into_commitment<const N: usize>(state: &[F; SW]) -> [F; N] {
        <T as AlgebraicRoundFunction<F, AW, SW, CW>>::state_into_commitment::<N>(state)
    }
}

#[inline]
pub fn absorb_multiple_rounds<
    F: SmallField,
    T: AlgebraicRoundFunction<F, AW, SW, CW>,
    M: AbsorptionModeTrait<F>,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    const ROUNDS: usize,
>(
    state: &mut [F; SW],
    to_absorb: &[F],
) -> [[F; SW]; ROUNDS] {
    debug_assert!(to_absorb.len() % AW == 0);
    debug_assert!(to_absorb.len() / AW == ROUNDS);
    let mut intermediate_final_states = [[F::ZERO; SW]; ROUNDS];
    for (chunk, dst) in to_absorb
        .array_chunks::<AW>()
        .zip(intermediate_final_states.iter_mut())
    {
        T::absorb_into_state::<M>(state, chunk);
        T::round_function(state);
        *dst = *state;
    }

    intermediate_final_states
}

#[inline]
pub fn absorb_into_state_vararg<
    F: SmallField,
    T: AlgebraicRoundFunction<F, AW, SW, CW>,
    M: AbsorptionModeTrait<F>,
    const AW: usize,
    const SW: usize,
    const CW: usize,
>(
    state: &mut [F; SW],
    to_absorb: &[F],
) {
    for chunk in to_absorb.array_chunks::<AW>() {
        T::absorb_into_state::<M>(state, chunk);
        T::round_function(state);
    }

    if to_absorb.array_chunks::<AW>().remainder().is_empty() == false {
        let mut tmp = [F::ZERO; AW];
        let remainder = to_absorb.array_chunks::<AW>().remainder();
        tmp[..remainder.len()].copy_from_slice(remainder);
        T::absorb_into_state::<M>(state, &tmp);
        T::round_function(state);
    }
}
