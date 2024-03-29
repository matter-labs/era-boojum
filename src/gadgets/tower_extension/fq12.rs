use std::sync::Arc;

use pairing::ff::PrimeField;

use super::{
    fq2::Fq2,
    fq6::Fq6,
    params::{Extension12Params, Extension6Params},
};

use crate::{
    cs::traits::cs::ConstraintSystem,
    field::SmallField,
    gadgets::{boolean::Boolean, non_native_field::traits::NonNativeField},
};

/// `Fq12` field extension implementation in the constraint system. It is implemented
/// as `Fq6[w]/(w^2-v)` where `w^6=9+u`. In other words, it is a set of
/// linear polynomials in a form `c0+c1*w`, where `c0` and `c1` are elements of `Fq6`.
/// See https://hackmd.io/@jpw/bn254#Field-extension-towers for reference. For
/// implementation reference, see https://eprint.iacr.org/2006/471.pdf.
#[derive(Clone, Copy)]
pub struct Fq12<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension12Params<T>,
{
    pub c0: Fq6<F, T, NN, P::Ex6>,
    pub c1: Fq6<F, T, NN, P::Ex6>,
    _marker: std::marker::PhantomData<(F, T)>,
}

impl<F, T, NN, P> Fq12<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension12Params<T>,
{
    /// Creates a new `Fq12` element from two `Fq6` components.
    pub fn new(c0: Fq6<F, T, NN, P::Ex6>, c1: Fq6<F, T, NN, P::Ex6>) -> Self {
        Self {
            c0,
            c1,
            _marker: std::marker::PhantomData::<(F, T)>,
        }
    }

    #[allow(unused_variables)]
    pub fn pow<CS>(&mut self, cs: &mut CS, exponent: T) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        todo!();
    }

    /// Creates a new zero `Fq12` in a form `0+0*w`
    pub fn zero<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let zero = Fq6::zero(cs, params);
        Self::new(zero.clone(), zero)
    }

    /// Creates a unit `Fq12` in a form `1+0*w`
    pub fn one<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let one = Fq6::one(cs, params);
        let zero = Fq6::zero(cs, params);
        Self::new(one, zero)
    }

    /// Returns true if the `Fq12` element is zero.
    pub fn is_zero<CS>(&mut self, cs: &mut CS) -> Boolean<F>
    where
        CS: ConstraintSystem<F>,
    {
        let is_c0_zero = self.c0.is_zero(cs);
        let is_c1_zero = self.c1.is_zero(cs);
        is_c0_zero.and(cs, is_c1_zero)
    }

    /// Conjugates the `Fq12` element by negating the `c1` component.
    pub fn conjugate<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c1 = self.c1.negated(cs);
        Self::new(self.c0.clone(), c1)
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
        let mut aa = self.c0.mul(cs, &mut other.c0);
        let mut bb = self.c1.mul(cs, &mut other.c1);
        let mut o = other.c0.add(cs, &mut other.c1);

        let mut c1 = self.c1.add(cs, &mut self.c0);
        let mut c1 = c1.mul(cs, &mut o);
        let mut c1 = c1.sub(cs, &mut aa);
        let c1 = c1.sub(cs, &mut bb);

        let mut c0 = bb.mul_by_nonresidue(cs);
        let c0 = c0.add(cs, &mut aa);

        Self::new(c0, c1)
    }

    #[must_use]
    pub fn square<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut ab = self.c0.mul(cs, &mut self.c1);
        let mut c0c1 = self.c0.add(cs, &mut self.c1);

        let mut c0 = self.c1.mul_by_nonresidue(cs);
        let mut c0 = c0.add(cs, &mut self.c0);
        let mut c0 = c0.mul(cs, &mut c0c1);
        let mut c0 = c0.sub(cs, &mut ab);

        let c1 = ab.double(cs);
        let mut ab_residue = ab.mul_by_nonresidue(cs);
        let c0 = c0.sub(cs, &mut ab_residue);

        Self::new(c0, c1)
    }

    pub fn mul_by_c0c1c4<CS>(
        &mut self,
        cs: &mut CS,
        c0: &mut Fq2<F, T, NN, <<P as Extension12Params<T>>::Ex6 as Extension6Params<T>>::Ex2>,
        c1: &mut Fq2<F, T, NN, <<P as Extension12Params<T>>::Ex6 as Extension6Params<T>>::Ex2>,
        c4: &mut Fq2<F, T, NN, <<P as Extension12Params<T>>::Ex6 as Extension6Params<T>>::Ex2>,
    ) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut aa = self.c0.mul_by_c0c1(cs, c0, c1);
        let mut bb = self.c1.mul_by_c1(cs, c4);
        let mut o = c1.add(cs, c4);

        let mut c1 = self.c1.add(cs, &mut self.c0);
        let mut c1 = c1.mul_by_c1(cs, &mut o);
        let mut c1 = c1.sub(cs, &mut aa);
        let c1 = c1.sub(cs, &mut bb);

        let mut c0 = bb.mul_by_nonresidue(cs);
        let c0 = c0.add(cs, &mut aa);

        Self::new(c0, c1)
    }

    pub fn mul_by_c0c3c4<CS>(
        &mut self,
        cs: &mut CS,
        c0: &mut Fq2<F, T, NN, <<P as Extension12Params<T>>::Ex6 as Extension6Params<T>>::Ex2>,
        c3: &mut Fq2<F, T, NN, <<P as Extension12Params<T>>::Ex6 as Extension6Params<T>>::Ex2>,
        c4: &mut Fq2<F, T, NN, <<P as Extension12Params<T>>::Ex6 as Extension6Params<T>>::Ex2>,
    ) -> Self 
    where 
        CS: ConstraintSystem<F>,
    {
        let zero = Fq2::zero(cs, &c0.c0.get_params());
        let c0 = Fq6::new(c0.clone(), zero.clone(), zero.clone());
        let c1 = Fq6::new(c3.clone(), c4.clone(), zero);
        let mut other = Fq12::new(c0, c1);

        // TODO: make it hand optimized
        self.mul(cs, &mut other)
    }

    /// Compute the Frobenius map - raise this element to power.
    pub fn frobenius_map<CS>(&mut self, cs: &mut CS, power: usize) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // TODO: explain:

        match power {
            1 | 2 | 3 | 6 => {}
            _ => {
                unreachable!("can not reach power {}", power);
            }
        }

        let c0 = self.c0.frobenius_map(cs, power);
        let c1 = self.c1.frobenius_map(cs, power);

        // TODO: add frobenius map of c1 Fp6 to its corresponding c0, c1, c2 FROBENIUS_COEFFS.

        Self::new(c0, c1)
    }

    #[allow(unused_variables)]
    pub fn inverse<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        todo!();
    }
}
