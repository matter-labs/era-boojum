use std::sync::Arc;

use crate::{
    cs::traits::cs::ConstraintSystem,
    field::SmallField,
    gadgets::{boolean::Boolean, non_native_field::traits::NonNativeField},
};

/// BN256Fq2Params represents a pair of elements in the extension field `Fq2=Fq[u]/(u^2-beta)`
/// where `beta^2=-1`. The implementation is primarily based on the following paper:
/// https://eprint.iacr.org/2006/471.pdf.
pub struct Fp2<F, T, NN>
where
    F: SmallField,
    T: pairing::ff::PrimeField,
    NN: NonNativeField<F, T>,
{
    pub c0: NN,
    pub c1: NN,
    _marker: std::marker::PhantomData<(F, T)>,
}

impl<F, T, NN> Fp2<F, T, NN>
where
    F: SmallField,
    T: pairing::ff::PrimeField,
    NN: NonNativeField<F, T>,
{
    /// Creates a new `Fp2` element from two `Fp` components.
    pub fn new(c0: NN, c1: NN) -> Self {
        Self {
            c0,
            c1,
            _marker: std::marker::PhantomData::<(F, T)>,
        }
    }

    /// Creates a new `Fp2` in a form `0+0*u`
    pub fn zero<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let zero = NN::allocated_constant(cs, T::zero(), params);

        Self::new(zero, zero)
    }

    /// Creates a new `Fp2` in a form `1+0*u`
    pub fn one<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let one = NN::allocated_constant(cs, T::one(), params);
        let zero = NN::allocated_constant(cs, T::zero(), params);

        Self::new(one, zero)
    }

    /// Adds two elements of `Fp2` by adding their components elementwise.
    #[must_use]
    pub fn add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.add(cs, &mut other.c0);
        let c1 = self.c1.add(cs, &mut other.c1);
        Self::new(c0, c1)
    }

    /// Returns whether the element of `Fp2` is zero.
    pub fn is_zero<CS>(&mut self, cs: &mut CS) -> Boolean<F>
    where
        CS: ConstraintSystem<F>,
    {
        let is_c0_zero = self.c0.is_zero(cs);
        let is_c1_zero = self.c1.is_zero(cs);
        is_c0_zero.and(cs, is_c1_zero)
    }

    /// Doubles the element of `Fp2` by doubling its components.
    #[must_use]
    pub fn double<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.double(cs);
        let c1 = self.c1.double(cs);
        Self::new(c0, c1)
    }

    /// Negates the element of `Fp2` by negating its components.
    #[must_use]
    pub fn negated<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.negated(cs);
        let c1 = self.c1.negated(cs);
        Self::new(c0, c1)
    }

    /// Conjugates the element `c=c0+c1*u` by computing `c=c0-c1*u`.
    #[must_use]
    pub fn conjugate<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0;
        let c1 = self.c1.negated(cs);
        Self::new(c0, c1)
    }

    /// Subtracts two elements of `Fp2` by subtracting their components elementwise.
    #[must_use]
    pub fn sub<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.sub(cs, &mut other.c0);
        let c1 = self.c1.sub(cs, &mut other.c1);
        Self::new(c0, c1)
    }

    /// Multiply the element `a=a0+a1*u` by the element `b=b0+b1*u` using the Karatsuba method.
    #[must_use]
    pub fn mul<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // v0 <- a0*b0, v1 <- a1*b1
        let mut v0 = self.c0.mul(cs, &mut other.c0);
        let mut v1 = self.c1.mul(cs, &mut other.c1);

        // c0 <- v0 + beta*v1
        let c0 = v0.sub(cs, &mut v1);

        // c1 <- (a0 + a1)(b0 + b1) - v0 - v1
        let mut a0_plus_a1 = self.c0.add(cs, &mut self.c1);
        let mut b0_plus_b1 = other.c0.add(cs, &mut other.c1);
        let mut c1 = a0_plus_a1.mul(cs, &mut b0_plus_b1);
        let mut c1 = c1.sub(cs, &mut v0);
        let c1 = c1.sub(cs, &mut v1);

        Self::new(c0, c1)
    }

    /// Square the element `a=a0+a1*u` by using the Karatsuba method.
    #[must_use]
    pub fn square<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // v0 <- a0^2, v1 <- a1^2
        let mut v0 = self.c0.square(cs);
        let mut v1 = self.c1.square(cs);

        // c0 <- v0 + beta*v1
        let c0 = v0.sub(cs, &mut v1);

        // c1 <- (a0 + a1)^2 - v0 - v1
        let mut a0_plus_a1 = self.c0.add(cs, &mut self.c1);
        let mut c1 = a0_plus_a1.square(cs);
        let mut c1 = c1.sub(cs, &mut v0);
        let c1 = c1.sub(cs, &mut v1);

        Self::new(c0, c1)
    }

    /// Multiply the element `a=a0+a1*u` by the element in the base field `Fp`.
    #[must_use]
    pub fn mul_fp<CS>(&mut self, cs: &mut CS, other: &mut NN) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // a*f = (a0 + a1*u)*f = (a0*f) + (a1*f)*u
        let c0 = self.c0.mul(cs, other);
        let c1 = self.c1.mul(cs, other);
        Self::new(c0, c1)
    }

    /// Finds the inverse of the element `a=a0+a1*u` in the extension field `Fp2`.
    #[must_use]
    pub fn inverse<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
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

    /// Divides the element `a=a0+a1*u` by the element `b=b0+b1*u` in the extension field `Fp2`.
    #[must_use]
    pub fn div<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut inv = other.inverse(cs);
        self.mul(cs, &mut inv)
    }

    /// Multiply this element by quadratic nonresidue 9 + u.
    pub fn mul_by_nonresidue<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut t0 = self.c0;
        let mut t1 = self.c1;

        // Finding 8(a0 + a1*u)
        let mut new = self.double(cs);
        new = new.double(cs);
        new = new.double(cs);

        // c0 <- 9*c0 - c1
        let mut c0 = new.c0.add(cs, &mut t0);
        let c0 = c0.sub(cs, &mut t1);

        // c1 <- c0 + 9*c1
        let mut c1 = new.c1.add(cs, &mut t1);
        let c1 = c1.add(cs, &mut t0);

        Self::new(c0, c1)
    }
}
