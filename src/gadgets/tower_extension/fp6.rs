use std::{mem, sync::Arc};

use pairing::ff::PrimeField;

use super::{fp2::Fp2, params::Extension6Params};

use crate::{
    cs::traits::cs::ConstraintSystem,
    field::SmallField,
    gadgets::{boolean::Boolean, non_native_field::traits::NonNativeField},
};

/// `Fp6` field extension implementation in the constraint system. It is implemented
/// as `Fp2[v]/(v^3-xi)` where `xi=9+u`. In other words,
/// it is a set of quadratic polynomials of a form `c0+c1*v+c2*v^2`,
///  where `c0`, `c1`, `c2` are elements of `Fp2`.
/// See https://hackmd.io/@jpw/bn254#Field-extension-towers for reference. For
/// implementation reference, see https://eprint.iacr.org/2006/471.pdf.
#[derive(Clone, Debug, Copy)]
pub struct Fp6<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension6Params<T>,
{
    pub c0: Fp2<F, T, NN, P::Ex2>,
    pub c1: Fp2<F, T, NN, P::Ex2>,
    pub c2: Fp2<F, T, NN, P::Ex2>,
    _marker: std::marker::PhantomData<(F, T)>,
}

impl<F, T, NN, P> Fp6<F, T, NN, P>
where
    F: SmallField,
    T: pairing::ff::PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension6Params<T>,
{
    /// Creates a new `Fp6` element from three `Fp2` components.
    pub fn new(
        c0: Fp2<F, T, NN, P::Ex2>,
        c1: Fp2<F, T, NN, P::Ex2>,
        c2: Fp2<F, T, NN, P::Ex2>,
    ) -> Self {
        Self {
            c0,
            c1,
            c2,
            _marker: std::marker::PhantomData::<(F, T)>,
        }
    }

    /// Creates a new zero `Fp6` in a form `0+0*v+0*v^2`
    pub fn zero<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let zero = Fp2::zero(cs, params);
        Self::new(zero.clone(), zero.clone(), zero)
    }

    /// Creates a unit `Fp6` in a form `1+0*v+0*v^2`
    pub fn one<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let one = Fp2::one(cs, params);
        let zero = Fp2::zero(cs, params);
        Self::new(one, zero.clone(), zero)
    }

    /// Returns true if the `Fp6` element is zero.
    pub fn is_zero<CS>(&mut self, cs: &mut CS) -> Boolean<F>
    where
        CS: ConstraintSystem<F>,
    {
        let is_c0_zero = self.c0.is_zero(cs);
        let is_c1_zero = self.c1.is_zero(cs);
        let is_c2_zero = self.c2.is_zero(cs);
        is_c0_zero.and(cs, is_c1_zero).and(cs, is_c2_zero)
    }

    /// Adds two elements of `Fp6` by adding their components elementwise.
    #[must_use]
    pub fn add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.add(cs, &mut other.c0);
        let c1 = self.c1.add(cs, &mut other.c1);
        let c2 = self.c2.add(cs, &mut other.c2);
        Self::new(c0, c1, c2)
    }

    /// Doubles the element of `Fp6` by doubling its components.
    #[must_use]
    pub fn double<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.double(cs);
        let c1 = self.c1.double(cs);
        let c2 = self.c2.double(cs);
        Self::new(c0, c1, c2)
    }

    /// Negates the element of `Fp6` by negating its components.
    #[must_use]
    pub fn negated<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.negated(cs);
        let c1 = self.c1.negated(cs);
        let c2 = self.c2.negated(cs);
        Self::new(c0, c1, c2)
    }

    /// Subtracts two elements of `Fp6` by subtracting their components elementwise.
    #[must_use]
    pub fn sub<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.sub(cs, &mut other.c0);
        let c1 = self.c1.sub(cs, &mut other.c1);
        let c2 = self.c2.sub(cs, &mut other.c2);
        Self::new(c0, c1, c2)
    }

    /// Multiplies the element in `Fp6` by a non-residue `xi=9+u`.
    pub fn mul_by_nonresidue<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // c0, c1, c2 -> c2, c0, c1
        mem::swap(&mut self.c0, &mut self.c1);
        mem::swap(&mut self.c1, &mut self.c2);
        // c2 -> xi*c2
        let new_c0 = self.c0.mul_by_nonresidue(cs);
        Self::new(new_c0, self.c1.clone(), self.c2.clone())
    }

    /// Multiplies two elements `a=a0+a1*v+a2*v^2`
    /// and `b=b0+b1*v+b2*v^2` in `Fp6` using Karatsuba multiplication.
    #[must_use]
    pub fn mul<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // v0 <- a0*b0, v1 <- a1*b1, v2 <- a2*b2
        let mut v0 = self.c0.mul(cs, &mut other.c0);
        let mut v1 = self.c1.mul(cs, &mut other.c1);
        let mut v2 = self.c2.mul(cs, &mut other.c2);

        // c0 <- v0 + xi*((a1 + a2)(b1 + b2) - v1 - v2)
        let mut a1_plus_a2 = self.c1.add(cs, &mut self.c2);
        let mut b1_plus_b2 = other.c1.add(cs, &mut other.c2);
        let mut a1_plus_a2_b1_plus_b2 = a1_plus_a2.mul(cs, &mut b1_plus_b2);
        let mut c0 = a1_plus_a2_b1_plus_b2.mul(cs, &mut b1_plus_b2);
        let mut c0 = c0.sub(cs, &mut v1);
        let mut c0 = c0.sub(cs, &mut v2);
        let c0 = c0.add(cs, &mut v0);

        // c1 <- (a0 + a1)(b0 + b1) - v0 - v1 + xi*v2
        let mut a0_plus_a1 = self.c0.add(cs, &mut self.c1);
        let mut b0_plus_b1 = other.c0.add(cs, &mut other.c1);
        let mut c1 = a0_plus_a1.mul(cs, &mut b0_plus_b1);
        let mut c1 = c1.sub(cs, &mut v0);
        let mut c1 = c1.add(cs, &mut v1);
        let mut xi_v2 = v2.mul_by_nonresidue(cs);
        let c1 = c1.add(cs, &mut xi_v2);

        // c2 <- (a0 + a2)(b0 + b2) - v0 + v1 - v2
        let mut a0_plus_a2 = self.c0.add(cs, &mut self.c2);
        let mut b0_plus_b2 = other.c0.add(cs, &mut other.c2);
        let mut c2 = a0_plus_a2.mul(cs, &mut b0_plus_b2);
        let mut c2 = c2.sub(cs, &mut v0);
        let mut c2 = c2.add(cs, &mut v1);
        let c2 = c2.sub(cs, &mut v2);

        Self::new(c0, c1, c2)
    }

    /// Squares the element `a=a0+a1*v+a2*v^2` in `Fp6` using Karatsuba squaring.
    #[must_use]
    pub fn square<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        // v0 <- a0^2, v1 <- a1^2, v2 <- a2^2
        let mut v0 = self.c0.square(cs);
        let mut v1 = self.c1.square(cs);
        let mut v2 = self.c2.square(cs);

        // c0 <- v0 + xi*((a1 + a2)^2 - v1 - v2)
        let mut a1_plus_a2 = self.c1.add(cs, &mut self.c2);
        let mut c0 = a1_plus_a2.square(cs);
        let mut c0 = c0.sub(cs, &mut v1);
        let mut c0 = c0.sub(cs, &mut v2);
        let mut c0 = c0.mul_by_nonresidue(cs);
        let c0 = c0.add(cs, &mut v0);

        // c1 <- (a0 + a1)^2 - v0 - v1 + xi*v2
        let mut a0_plus_a1 = self.c0.add(cs, &mut self.c1);
        let mut c1 = a0_plus_a1.square(cs);
        let mut c1 = c1.sub(cs, &mut v0);
        let mut c1 = c1.sub(cs, &mut v1);
        let mut xi_v2 = v2.mul_by_nonresidue(cs);
        let c1 = c1.add(cs, &mut xi_v2);

        // c2 <- (a0 + a2)^2 - v0 + v1 - v2
        let mut a0_plus_a2 = self.c0.add(cs, &mut self.c2);
        let mut c2 = a0_plus_a2.square(cs);
        let mut c2 = c2.sub(cs, &mut v0);
        let mut c2 = c2.add(cs, &mut v1);
        let c2 = c2.sub(cs, &mut v2);

        Self::new(c0, c1, c2)
    }

    /// Multiplies the element `a=a0+a1*v+a2*v^2` in `Fp6` by the element `b = b1*v`
    pub fn mul_by_c1<CS>(&mut self, cs: &mut CS, c1: &mut Fp2<F, T, NN, P::Ex2>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut b_b = self.c1.mul(cs, c1);
        let mut tmp = self.c1.add(cs, &mut self.c2);

        let mut t1 = self.c1.mul(cs, &mut tmp);
        let mut t1 = t1.sub(cs, &mut b_b);
        let t1 = t1.mul_by_nonresidue(cs);

        let mut tmp = self.c0.add(cs, &mut self.c1);
        let mut t2 = c1.mul(cs, &mut tmp);
        let t2 = t2.sub(cs, &mut b_b);

        Self::new(t1, t2, b_b)
    }

    /// Multiplies the element `a=a0+a1*v+a2*v^2` in `Fp6` by the element `b = b0+b1*v`
    pub fn mul_by_c0c1<CS>(
        &mut self,
        cs: &mut CS,
        c0: &mut Fp2<F, T, NN, P::Ex2>,
        c1: &mut Fp2<F, T, NN, P::Ex2>,
    ) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut a_a = self.c0.mul(cs, c0);
        let mut b_b = self.c1.mul(cs, c1);

        let mut tmp = self.c1.add(cs, &mut self.c2);
        let mut t1 = c1.mul(cs, &mut tmp);
        let mut t1 = t1.sub(cs, &mut b_b);
        let mut t1 = t1.mul_by_nonresidue(cs);
        let t1 = t1.add(cs, &mut a_a);

        let mut tmp = self.c0.add(cs, &mut self.c2);
        let mut t3 = c0.mul(cs, &mut tmp);
        let mut t3 = t3.sub(cs, &mut a_a);
        let t3 = t3.add(cs, &mut b_b);

        let mut t2 = c0.add(cs, c1);
        let mut tmp = self.c0.add(cs, &mut self.c1);
        let mut t2 = t2.mul(cs, &mut tmp);
        let mut t2 = t2.sub(cs, &mut a_a);
        let t2 = t2.sub(cs, &mut b_b);

        Self::new(t1, t2, t3)
    }

    /// Compute the Frobenius map - raise this element to power.
    pub fn frobenius_map<CS>(&mut self, cs: &mut CS, power: usize) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // TODO: explain:

        match power % 6 {
            0 | 1 | 2 | 3 => {}
            _ => {
                unreachable!("can not reach power {}", power);
            }
        }

        let c0 = self.c0.frobenius_map(cs, power);
        let mut c1 = self.c1.frobenius_map(cs, power);
        let mut c2 = self.c2.frobenius_map(cs, power);

        // TODO: add multiplication of c1 and c2 by corresponding FROBENIUS_COEFFS c1 and c2.
        // TODO: assert what Fp2 under CS computes frobenius map same as without CS.

        Self::new(c0, c1, c2)
    }
}
