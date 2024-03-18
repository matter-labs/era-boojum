use super::*;
use crate::{cs::traits::cs::ConstraintSystem, gadgets::curves::SmallField};

/// BN256Fq2Params represents a pair of elements in the extension field Fq2 = Fq[X] / (X^2 - beta)
/// where beta^2 = -2.
pub struct BN256Fq2Params<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>
{
    pub c0: BN256BaseNNField<F>,
    pub c1: BN256BaseNNField<F>,
    _marker: std::marker::PhantomData<CS>,
}

pub type BN256Fq2ProjectiveCurvePoint<F, CS> = [BN256Fq2Params<F, CS>; 3];

impl<F, CS> BN256Fq2Params<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    pub fn new(c0: BN256BaseNNField<F>, c1: BN256BaseNNField<F>) -> Self {
        Self { c0, c1, _marker: std::marker::PhantomData }
    }

    pub fn add(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        let c0 = self.c0.add(cs, &mut other.c0);
        let c1 = self.c1.add(cs, &mut other.c1);
        Self::new(c0, c1)
    }

    pub fn sub(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        let c0 = self.c0.sub(cs, &mut other.c0);
        let c1 = self.c1.sub(cs, &mut other.c1);
        Self::new(c0, c1)
    }

    pub fn negated(&mut self, cs: &mut CS) -> Self {
        let c0 = self.c0.negated(cs);
        let c1 = self.c1.negated(cs);
        Self::new(c0, c1)
    }

    pub fn mul(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        // (a+bi)(c+di) = ac - 2*bd + (ad + bc)i

        let mut ac = self.c0.mul(cs, &mut other.c0);
        let mut bd = self.c1.mul(cs, &mut other.c1);
        let mut bd2 = bd.double(cs);
        let mut ad = self.c0.mul(cs, &mut other.c1);
        let mut bc = self.c1.mul(cs, &mut other.c0);
        let c0 = ac.sub(cs, &mut bd2);
        let c1 = ad.add(cs, &mut bc);
        Self::new(c0, c1)   
    }

    pub fn mul_fq(&mut self, cs: &mut CS, other: &mut BN256BaseNNField<F>) -> Self {
        let c0 = self.c0.mul(cs, other);
        let c1 = self.c1.mul(cs, other);
        Self::new(c0, c1)
    }

    pub fn inverse(&mut self, cs: &mut CS) -> Self {
        let mut t0 = self.c0.square(cs);
        let mut t1 = self.c1.square(cs);
        t1 = t1.double(cs);
        t0 = t0.add(cs, &mut t1);
        let mut t = t0.inverse_unchecked(cs);
        let c0 = self.c0.mul(cs, &mut t);
        let mut c1 = self.c1.mul(cs, &mut t);
        c1 = c1.negated(cs);

        Self::new(c0, c1)
    }

    pub fn div(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        let mut inv = other.inverse(cs);
        self.mul(cs, &mut inv)
    }
}