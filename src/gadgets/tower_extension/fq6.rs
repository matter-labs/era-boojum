use std::sync::Arc;

use pairing::ff::PrimeField;

use super::{fq2::Fq2, params::Extension6Params};

use crate::{
    cs::traits::cs::ConstraintSystem,
    field::SmallField,
    gadgets::{boolean::Boolean, non_native_field::traits::NonNativeField},
};

/// `Fq6` field extension implementation in the constraint system. It is implemented
/// as `Fq2[v]/(v^3-xi)` where `xi=9+u`. In other words,
/// it is a set of quadratic polynomials of a form `c0+c1*v+c2*v^2`,
///  where `c0`, `c1`, `c2` are elements of `Fq2`.
/// See https://hackmd.io/@jpw/bn254#Field-extension-towers for reference. For
/// implementation reference, see https://eprint.iacr.org/2006/471.pdf.
#[derive(Clone, Debug, Copy)]
pub struct Fq6<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension6Params<T>,
{
    pub c0: Fq2<F, T, NN, P::Ex2>,
    pub c1: Fq2<F, T, NN, P::Ex2>,
    pub c2: Fq2<F, T, NN, P::Ex2>,
    _marker: std::marker::PhantomData<(F, T)>,
}

impl<F, T, NN, P> Fq6<F, T, NN, P>
where
    F: SmallField,
    T: pairing::ff::PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension6Params<T>,
{
    /// Creates a new `Fq6` element from three `Fq2` components.
    pub fn new(
        c0: Fq2<F, T, NN, P::Ex2>,
        c1: Fq2<F, T, NN, P::Ex2>,
        c2: Fq2<F, T, NN, P::Ex2>,
    ) -> Self {
        Self {
            c0,
            c1,
            c2,
            _marker: std::marker::PhantomData::<(F, T)>,
        }
    }

    /// Creates a new zero `Fq6` in a form `0+0*v+0*v^2`
    pub fn zero<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let zero = Fq2::zero(cs, params);
        Self::new(zero.clone(), zero.clone(), zero)
    }

    /// Creates a unit `Fq6` in a form `1+0*v+0*v^2`
    pub fn one<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let one = Fq2::one(cs, params);
        let zero = Fq2::zero(cs, params);
        Self::new(one, zero.clone(), zero)
    }

    /// Returns true if the `Fq6` element is zero.
    pub fn is_zero<CS>(&mut self, cs: &mut CS) -> Boolean<F>
    where
        CS: ConstraintSystem<F>,
    {
        let is_c0_zero = self.c0.is_zero(cs);
        let is_c1_zero = self.c1.is_zero(cs);
        let is_c2_zero = self.c2.is_zero(cs);
        Boolean::multi_and(cs, &[is_c0_zero, is_c1_zero, is_c2_zero])
    }

    /// Adds two elements of `Fq6` by adding their components elementwise.
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

    /// Doubles the element of `Fq6` by doubling its components.
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

    /// Negates the element of `Fq6` by negating its components.
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

    /// Subtracts two elements of `Fq6` by subtracting their components elementwise.
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

    /// Multiplies the element in `Fq6` by a non-residue `xi=9+u`.
    pub fn mul_by_nonresidue<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // c0, c1, c2 -> c2, c0, c1
        let new_c2 = self.c2.mul_by_nonresidue(cs);
        Self::new(new_c2, self.c0.clone(), self.c1.clone())
    }

    /// Multiplies two elements `a=a0+a1*v+a2*v^2`
    /// and `b=b0+b1*v+b2*v^2` in `Fq6` using Karatsuba multiplication.
    #[must_use]
    pub fn mul<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut v0 = self.c0.mul(cs, &mut other.c0);
        let mut v1 = self.c1.mul(cs, &mut other.c1);
        let mut v2 = self.c2.mul(cs, &mut other.c2);

        let mut t1 = other.c1.add(cs, &mut other.c2);
        let mut tmp = self.c1.add(cs, &mut self.c2);

        let mut t1 = t1.mul(cs, &mut tmp);
        let mut t1 = t1.sub(cs, &mut v1);
        let mut t1 = t1.sub(cs, &mut v2);
        let mut t1 = t1.mul_by_nonresidue(cs);
        let t1 = t1.add(cs, &mut v0);

        let mut t3 = other.c0.add(cs, &mut other.c2);
        let mut tmp = self.c0.add(cs, &mut self.c2);
        let mut t3 = t3.mul(cs, &mut tmp);
        let mut t3 = t3.sub(cs, &mut v0);
        let mut t3 = t3.add(cs, &mut v1);
        let t3 = t3.sub(cs, &mut v2);

        let mut t2 = other.c0.add(cs, &mut other.c1);
        let mut tmp = self.c0.add(cs, &mut self.c1);
        let mut t2 = t2.mul(cs, &mut tmp);
        let mut t2 = t2.sub(cs, &mut v0);
        let mut t2 = t2.sub(cs, &mut v1);
        let mut v2 = v2.mul_by_nonresidue(cs);
        let t2 = t2.add(cs, &mut v2);

        Self::new(t1, t2, t3)
    }

    /// Squares the element `a=a0+a1*v+a2*v^2` in `Fq6` using Karatsuba squaring.
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

    /// Multiplies the element `a=a0+a1*v+a2*v^2` in `Fq6` by the element `b = b1*v`
    pub fn mul_by_c1<CS>(&mut self, cs: &mut CS, c1: &mut Fq2<F, T, NN, P::Ex2>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut b_b = self.c1.mul(cs, c1);
        let mut tmp = self.c1.add(cs, &mut self.c2);

        let mut t1 = c1.mul(cs, &mut tmp);
        let mut t1 = t1.sub(cs, &mut b_b);
        let t1 = t1.mul_by_nonresidue(cs);

        let mut tmp = self.c0.add(cs, &mut self.c1);
        let mut t2 = c1.mul(cs, &mut tmp);
        let t2 = t2.sub(cs, &mut b_b);

        Self::new(t1, t2, b_b)
    }

    /// Multiplies the element `a=a0+a1*v+a2*v^2` in `Fq6` by the element `b = b0+b1*v`
    pub fn mul_by_c0c1<CS>(
        &mut self,
        cs: &mut CS,
        c0: &mut Fq2<F, T, NN, P::Ex2>,
        c1: &mut Fq2<F, T, NN, P::Ex2>,
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

    /// Find the inverse element in Fq6
    pub fn inverse<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut c0 = self.c2.mul_by_nonresidue(cs);
        let mut c0 = c0.mul(cs, &mut self.c1);
        let mut c0 = c0.negated(cs);

        let mut c0s = self.c0.square(cs);
        let mut c0 = c0.add(cs, &mut c0s);

        let mut c1 = self.c2.square(cs);
        let mut c1 = c1.mul_by_nonresidue(cs);

        let mut c01 = self.c0.mul(cs, &mut self.c1);
        let mut c1 = c1.sub(cs, &mut c01);

        let mut c2 = self.c1.square(cs);
        let mut c02 = self.c0.mul(cs, &mut self.c2);
        let mut c2 = c2.sub(cs, &mut c02);

        let mut tmp1 = self.c2.mul(cs, &mut c1);
        let mut tmp2 = self.c1.mul(cs, &mut c2);
        let mut tmp1 = tmp1.add(cs, &mut tmp2);
        let mut tmp1 = tmp1.mul_by_nonresidue(cs);
        let mut tmp2 = self.c0.mul(cs, &mut c0);
        let mut tmp1 = tmp1.add(cs, &mut tmp2);

        let mut t = tmp1.inverse(cs);
        let c0_new = t.mul(cs, &mut c0);
        let c1_new = t.mul(cs, &mut c1);
        let c2_new = t.mul(cs, &mut c2);

        Self::new(c0_new, c1_new, c2_new)
    }

    pub fn div<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut inv = other.inverse(cs);
        self.mul(cs, &mut inv)
    }

    /// Compute the Frobenius map - raise this element to power.
    #[allow(unused_variables)]
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

        let c1_frobenius_constant = P::FROBENIUS_COEFFS_C1[power % 6];
        let c2_frobenius_constant = P::FROBENIUS_COEFFS_C2[power % 6];

        let params = c1.get_params();

        let mut c1_frobenius_coeff = Fq2::constant(cs, c1_frobenius_constant, params);
        let mut c2_frobenius_coeff = Fq2::constant(cs, c2_frobenius_constant, params);

        let c1 = c1.mul(cs, &mut c1_frobenius_coeff);
        let c2 = c2.mul(cs, &mut c2_frobenius_coeff);

        // TODO: assert what Fq2 under CS computes frobenius map same as without CS.

        Self::new(c0, c1, c2)
    }
}
