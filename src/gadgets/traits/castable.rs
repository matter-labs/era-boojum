use super::*;

use crate::field::SmallField;

// instead of defining may closures and implementing Fn traits for them we can abstract away

pub struct Convertor<
    F: SmallField,
    S: 'static + Clone + std::fmt::Debug + Send + Sync,
    U: WitnessCastable<F, S>,
> {
    _marker: std::marker::PhantomData<(F, S, U)>,
}

impl<
        F: SmallField,
        S: 'static + Clone + std::fmt::Debug + Send + Sync,
        U: WitnessCastable<F, S>,
    > Default for Convertor<F, S, U>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<
        F: SmallField,
        S: 'static + Clone + std::fmt::Debug + Send + Sync,
        U: WitnessCastable<F, S>,
    > Convertor<F, S, U>
{
    pub const fn new() -> Self {
        Self {
            _marker: std::marker::PhantomData,
        }
    }
}

impl<
        F: SmallField,
        S: 'static + Clone + std::fmt::Debug + Send + Sync,
        U: WitnessCastable<F, S>,
    > FnOnce<(S,)> for Convertor<F, S, U>
{
    type Output = U;

    extern "rust-call" fn call_once(self, args: (S,)) -> Self::Output {
        <U as WitnessCastable<F, S>>::cast_from_source(args.0)
    }
}

impl<
        F: SmallField,
        S: 'static + Clone + std::fmt::Debug + Send + Sync,
        U: WitnessCastable<F, S>,
    > FnMut<(S,)> for Convertor<F, S, U>
{
    extern "rust-call" fn call_mut(&mut self, args: (S,)) -> Self::Output {
        <U as WitnessCastable<F, S>>::cast_from_source(args.0)
    }
}

impl<
        F: SmallField,
        S: 'static + Clone + std::fmt::Debug + Send + Sync,
        U: WitnessCastable<F, S>,
    > Fn<(S,)> for Convertor<F, S, U>
{
    extern "rust-call" fn call(&self, args: (S,)) -> Self::Output {
        <U as WitnessCastable<F, S>>::cast_from_source(args.0)
    }
}

// type that's purpose to serve as "human readable" witness, and that can form itself from
// array if field elements
pub trait WitnessCastable<F: SmallField, S: Clone + std::fmt::Debug + Send + Sync>:
    'static + Clone + std::fmt::Debug + Send + Sync
{
    fn cast_from_source(witness: S) -> Self;
    fn cast_into_source(self) -> S;
}

// now we can provide default implementations

// We may also want to think about having U <-> T casts too

// identity
impl<F: SmallField> WitnessCastable<F, F> for F {
    #[inline]
    fn cast_from_source(witness: F) -> Self {
        witness
    }
    #[inline]
    fn cast_into_source(self) -> F {
        self
    }
}

impl<F: SmallField> WitnessCastable<F, [F; 1]> for F {
    #[inline]
    fn cast_from_source(witness: [F; 1]) -> Self {
        witness[0]
    }
    #[inline]
    fn cast_into_source(self) -> [F; 1] {
        [self]
    }
}

// boolean
impl<F: SmallField> WitnessCastable<F, F> for bool {
    #[inline]
    fn cast_from_source(witness: F) -> Self {
        let reduced = witness.as_u64_reduced();
        if reduced == 0 {
            false
        } else if reduced == 1 {
            true
        } else {
            unreachable!("expected value is not a boolean, got {}", witness)
        }
    }

    #[inline]
    fn cast_into_source(self) -> F {
        F::from_u64_unchecked(self as u64)
    }
}

impl<F: SmallField> WitnessCastable<F, [F; 1]> for bool {
    #[inline]
    fn cast_from_source(witness: [F; 1]) -> Self {
        <bool as WitnessCastable<F, F>>::cast_from_source(witness[0])
    }
    #[inline]
    fn cast_into_source(self) -> [F; 1] {
        [F::from_u64_unchecked(self as u64)]
    }
}

// small integers
impl<F: SmallField> WitnessCastable<F, F> for u8 {
    #[inline]
    fn cast_from_source(witness: F) -> Self {
        let reduced = witness.as_u64_reduced();
        debug_assert!(
            reduced <= Self::MAX as u64,
            "failed to cast field element to u8: value is {}",
            witness
        );

        reduced as Self
    }
    #[inline]
    fn cast_into_source(self) -> F {
        F::from_u64_unchecked(self as u64)
    }
}

impl<F: SmallField> WitnessCastable<F, F> for u16 {
    #[inline]
    fn cast_from_source(witness: F) -> Self {
        let reduced = witness.as_u64_reduced();
        debug_assert!(
            reduced <= Self::MAX as u64,
            "failed to cast field element to u16: value is {}",
            witness
        );

        reduced as Self
    }
    #[inline]
    fn cast_into_source(self) -> F {
        F::from_u64_unchecked(self as u64)
    }
}

impl<F: SmallField> WitnessCastable<F, F> for u32 {
    #[track_caller]
    #[inline]
    fn cast_from_source(witness: F) -> Self {
        let reduced = witness.as_u64_reduced();
        debug_assert!(
            reduced <= Self::MAX as u64,
            "failed to cast field element to u32: value is {}",
            witness
        );

        reduced as Self
    }
    #[inline]
    fn cast_into_source(self) -> F {
        F::from_u64_unchecked(self as u64)
    }
}

impl<F: SmallField> WitnessCastable<F, [F; 1]> for u8 {
    #[inline]
    fn cast_from_source(witness: [F; 1]) -> Self {
        <Self as WitnessCastable<F, F>>::cast_from_source(witness[0])
    }
    #[inline]
    fn cast_into_source(self) -> [F; 1] {
        [F::from_u64_unchecked(self as u64)]
    }
}

impl<F: SmallField> WitnessCastable<F, [F; 1]> for u16 {
    #[inline]
    fn cast_from_source(witness: [F; 1]) -> Self {
        <Self as WitnessCastable<F, F>>::cast_from_source(witness[0])
    }
    #[inline]
    fn cast_into_source(self) -> [F; 1] {
        [F::from_u64_unchecked(self as u64)]
    }
}

impl<F: SmallField> WitnessCastable<F, [F; 1]> for u32 {
    #[inline]
    fn cast_from_source(witness: [F; 1]) -> Self {
        <Self as WitnessCastable<F, F>>::cast_from_source(witness[0])
    }
    #[inline]
    fn cast_into_source(self) -> [F; 1] {
        [F::from_u64_unchecked(self as u64)]
    }
}

impl<F: SmallField> WitnessCastable<F, [F; 2]> for u16 {
    #[inline]
    fn cast_from_source(witness: [F; 2]) -> Self {
        let low = <u8 as WitnessCastable<F, F>>::cast_from_source(witness[0]) as Self;
        let high = <u8 as WitnessCastable<F, F>>::cast_from_source(witness[1]) as Self;

        let reduced = low | (high << 8);

        reduced as Self
    }
    #[inline]
    fn cast_into_source(self) -> [F; 2] {
        [
            F::from_u64_unchecked((self as u8) as u64),
            F::from_u64_unchecked(((self >> 8) as u8) as u64),
        ]
    }
}

impl<F: SmallField> WitnessCastable<F, [F; 2]> for u32 {
    #[inline]
    fn cast_from_source(witness: [F; 2]) -> Self {
        let low = <u16 as WitnessCastable<F, F>>::cast_from_source(witness[0]) as Self;
        let high = <u16 as WitnessCastable<F, F>>::cast_from_source(witness[1]) as Self;

        let reduced = low | (high << 16);

        reduced as Self
    }
    #[inline]
    fn cast_into_source(self) -> [F; 2] {
        [
            F::from_u64_unchecked((self as u16) as u64),
            F::from_u64_unchecked(((self >> 16) as u16) as u64),
        ]
    }
}

// higher width types will de defined later on

// arrays
impl<
        F: SmallField,
        S: 'static + Clone + std::fmt::Debug + Send + Sync,
        T: WitnessCastable<F, S>,
        const N: usize,
    > WitnessCastable<F, [S; N]> for [T; N]
{
    #[inline]
    fn cast_from_source(witness: [S; N]) -> Self {
        witness.map(|el| T::cast_from_source(el))
    }
    #[inline]
    fn cast_into_source(self) -> [S; N] {
        self.map(|el| WitnessCastable::cast_into_source(el))
    }
}
