use std::sync::Arc;

use super::fp6::Fp6;

use crate::{
    cs::traits::cs::ConstraintSystem, field::SmallField,
    gadgets::non_native_field::traits::NonNativeField,
};

/// `Fp12` field extension implementation in the constraint system. It is implemented
/// as `Fp6[w]/(w^2-v)` where `w^6=9+u`. In other words, it is a set of
/// linear polynomials in a form `c0+c1*w`, where `c0` and `c1` are elements of `Fp6`.
/// See https://hackmd.io/@jpw/bn254#Field-extension-towers for reference. For
/// implementation reference, see https://eprint.iacr.org/2006/471.pdf.
pub struct Fp12<F: SmallField, T: pairing::ff::PrimeField, NN: NonNativeField<F, T>> {
    pub c0: Fp6<F, T, NN>,
    pub c1: Fp6<F, T, NN>,
    _marker: std::marker::PhantomData<(F, T)>,
}

impl<F: SmallField, T: pairing::ff::PrimeField, NN: NonNativeField<F, T>> Fp12<F, T, NN> {
    /// Creates a new `Fp12` element from two `Fp6` components.
    pub fn new(c0: Fp6<F, T, NN>, c1: Fp6<F, T, NN>) -> Self {
        Self {
            c0,
            c1,
            _marker: std::marker::PhantomData::<(F, T)>,
        }
    }

    /// Creates a new zero `Fp12` in a form `0+0*w`
    pub fn zero<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let zero = Fp6::zero(cs, params);
        Self::new(zero, zero)
    }

    /// Creates a unit `Fp12` in a form `1+0*w`
    pub fn one<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let one = Fp6::one(cs, params);
        let zero = Fp6::zero(cs, params);
        Self::new(one, zero)
    }

    /// Conjugates the `Fp12` element by negating the `c1` component.
    pub fn conjugate<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c1 = self.c1.negated(cs);
        Self::new(self.c0, c1)
    }

    #[must_use]
    pub fn add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.add(cs, &mut other.c0);
        let c1 = self.c1.add(cs, &mut other.c1);
        Self::new(c0, c1)
    }

    #[must_use]
    pub fn double<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.double(cs);
        let c1 = self.c1.double(cs);
        Self::new(c0, c1)
    }

    #[must_use]
    pub fn negated<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.negated(cs);
        let c1 = self.c1.negated(cs);
        Self::new(c0, c1)
    }

    #[must_use]
    pub fn sub<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.sub(cs, &mut other.c0);
        let c1 = self.c1.sub(cs, &mut other.c1);
        Self::new(c0, c1)
    }

    #[must_use]
    pub fn mul<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    #[must_use]
    pub fn square<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    #[must_use]
    pub fn inverse<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    #[must_use]
    pub fn div<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut inv = other.inverse(cs);
        self.mul(cs, &mut inv)
    }
}
