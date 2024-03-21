use crate::{
    cs::traits::cs::ConstraintSystem, field::SmallField,
    gadgets::non_native_field::traits::NonNativeField,
};

pub struct Fp2<F: SmallField, T: pairing::ff::PrimeField, NN: NonNativeField<F, T>> {
    pub c0: NN,
    pub c1: NN,
    _marker: std::marker::PhantomData<(F, T)>, // Question: what to put here?
}

impl<F: SmallField, T: pairing::ff::PrimeField, NN: NonNativeField<F, T>> Fp2<F, T, NN> {
    pub fn new(c0: NN, c1: NN) -> Self {
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
        // (a+bi)(c+di) = ac - bd + (ad + bc)i
        let mut ac = self.c0.mul(cs, &mut other.c0);
        let mut bd = self.c1.mul(cs, &mut other.c1);
        let mut ad = self.c0.mul(cs, &mut other.c1);
        let mut bc = self.c1.mul(cs, &mut other.c0);

        let c0 = ac.sub(cs, &mut bd);
        let c1 = ad.add(cs, &mut bc);

        Self::new(c0, c1)
    }

    #[must_use]
    pub fn square<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        let mut c0_squared = self.c0.square(cs);
        let mut c1_squared = self.c1.square(cs);
        let c0 = c0_squared.sub(cs, &mut c1_squared);

        let mut c1 = self.c0.mul(cs, &mut self.c1);
        let c1 = c1.double(cs);

        Self::new(c0, c1)
    }

    #[must_use]
    pub fn mul_fp<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, fp: &mut NN) -> Self {
        let c0 = self.c0.sub(cs, fp);
        let c1 = self.c1.sub(cs, fp);
        Self::new(c0, c1)
    }

    #[must_use]
    pub fn inverse<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        let mut t0 = self.c0.square(cs);
        let mut t1 = self.c1.square(cs);
        t1 = t1.double(cs);
        t0 = t0.add(cs, &mut t1);
        let mut t = t0.inverse_unchecked(cs); // this goes to todo!(), however implementation exist for NonNativeFieldOverU16 - ?
        let c0 = self.c0.mul(cs, &mut t);
        let mut c1 = self.c1.mul(cs, &mut t);
        c1 = c1.negated(cs);

        Self::new(c0, c1)
    }

    #[must_use]
    pub fn div<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        let mut inv = other.inverse(cs);
        self.mul(cs, &mut inv)
    }
}
