use super::fp6::Fp6;

use crate::{
    cs::traits::cs::ConstraintSystem, field::SmallField,
    gadgets::non_native_field::traits::NonNativeField,
};

pub struct Fp12<F: SmallField, T: pairing::ff::PrimeField, NN: NonNativeField<F, T>> {
    pub c0: Fp6<F, T, NN>,
    pub c1: Fp6<F, T, NN>,
    _marker: std::marker::PhantomData<(F, T)>, // Question: what to put here?
}

impl<F: SmallField, T: pairing::ff::PrimeField, NN: NonNativeField<F, T>> Fp12<F, T, NN> {
    pub fn new(c0: Fp6<F, T, NN>, c1: Fp6<F, T, NN>) -> Self {
        Self {
            c0,
            c1,
            _marker: std::marker::PhantomData::<(F, T)>,
        }
    }

    #[must_use]
    pub fn add<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        let c0 = self.c0.add(cs, &mut other.c0);
        let c1 = self.c1.add(cs, &mut other.c1);
        Self::new(c0, c1)
    }

    #[must_use]
    pub fn double<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        let c0 = self.c0.double(cs);
        let c1 = self.c1.double(cs);
        Self::new(c0, c1)
    }

    #[must_use]
    pub fn negated<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        let c0 = self.c0.negated(cs);
        let c1 = self.c1.negated(cs);
        Self::new(c0, c1)
    }

    #[must_use]
    pub fn sub<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        let c0 = self.c0.sub(cs, &mut other.c0);
        let c1 = self.c1.sub(cs, &mut other.c1);
        Self::new(c0, c1)
    }

    #[must_use]
    pub fn mul<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        todo!()
    }

    #[must_use]
    pub fn square<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        todo!()
    }

    #[must_use]
    pub fn inverse<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        todo!()
    }

    #[must_use]
    pub fn div<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        let mut inv = other.inverse(cs);
        self.mul(cs, &mut inv)
    }
}
