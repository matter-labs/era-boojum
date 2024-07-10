use std::sync::Arc;

use pairing::{bn256::Fq as BN256Fq, ff::PrimeField};

use super::{
    fq2::Fq2,
    params::{
        bn256::{BN256Extension2Params, BN256Extension6Params},
        Extension6Params,
    },
};

use crate::cs::Variable;
use crate::gadgets::traits::allocatable::CSPlaceholder;
use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;
use crate::{
    cs::traits::cs::ConstraintSystem,
    field::SmallField,
    gadgets::{
        boolean::Boolean,
        non_native_field::traits::NonNativeField,
        traits::{
            allocatable::CSAllocatable, selectable::Selectable, witnessable::WitnessHookable,
        },
    },
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

    /// Returns the `\gamma`: square root of `w`, being just a `0+1*v+0*v^2` element.
    pub fn gamma<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let one = Fq2::one(cs, params);
        let zero = Fq2::zero(cs, params);
        Self::new(zero.clone(), one, zero)
    }

    /// Returns `Fq6::one()` if `b` is true, and `Fq6::zero()` if `b` is false.
    pub fn from_boolean<CS>(cs: &mut CS, b: Boolean<F>, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let zero = Self::zero(cs, params);
        let one = Self::one(cs, params);
        Self::conditionally_select(cs, b, &one, &zero)
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

    /// Multiplies the element in `Fq6` by a non-residue `v`.
    pub fn mul_by_nonresidue<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // c0, c1, c2 -> c2, c0, c1
        let new_c2 = self.c2.mul_by_nonresidue(cs);
        Self::new(new_c2, self.c0.clone(), self.c1.clone())
    }

    /// Multiplies the element in `Fq6` by a non-residue `\xi=9+u`.
    pub fn mul_by_xi<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let new_c0 = self.c0.mul_by_nonresidue(cs);
        let new_c1 = self.c1.mul_by_nonresidue(cs);
        let new_c2 = self.c2.mul_by_nonresidue(cs);

        Self::new(new_c0, new_c1, new_c2)
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

    /// Multiplies the element `a=a0+a1*v+a2*v^2` in `Fq6` by the element in `NonNativeField`
    pub fn mul_by_fq<CS>(&mut self, cs: &mut CS, c0: &mut NN) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // Simply multiply element-wise
        let t0 = self.c0.mul_c0(cs, c0);
        let t1 = self.c1.mul_c0(cs, c0);
        let t2 = self.c2.mul_c0(cs, c0);

        Self::new(t0, t1, t2)
    }

    /// Multiplies the element `a=a0+a1*v+a2*v^2` in `Fq6` by the element `c=c0` in `Fq2`
    pub fn mul_by_c0<CS>(&mut self, cs: &mut CS, c0: &mut Fq2<F, T, NN, P::Ex2>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // Simply multiply element-wise
        let t0 = self.c0.mul(cs, c0);
        let t1 = self.c1.mul(cs, c0);
        let t2 = self.c2.mul(cs, c0);

        Self::new(t0, t1, t2)
    }

    /// Multiplies the element `a=a0+a1*v+a2*v^2` in `Fq6` by the element `c2*v^2`
    pub fn mul_by_c2<CS>(&mut self, cs: &mut CS, c2: &mut Fq2<F, T, NN, P::Ex2>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // Suppose a = a0 + a1*v + a2*v^2. In this case,
        // (a0 + a1*v + a2*v^2) * c2 * v^2 =
        // a1*c2*\xi + a2*c2*\xi*v + a0*c2*v^2
        // NOTE: There might be a better way to calculate three coefficients
        // without using 3 multiplications and 2 mul_by_nonresidues, similarly to mul_by_c1

        // Setting coefficients
        let mut a0 = self.c0.clone();
        let mut a1 = self.c1.clone();
        let mut a2 = self.c2.clone();

        // new_c0 <- a1*c2*\xi
        let mut new_c0 = a1.mul(cs, c2);
        new_c0 = new_c0.mul_by_nonresidue(cs);

        // new_c1 <- a2*c2*\xi
        let mut new_c1 = a2.mul(cs, c2);
        new_c1 = new_c1.mul_by_nonresidue(cs);

        // new_c2 <- a0*c2
        let new_c2 = a0.mul(cs, c2);

        Self::new(new_c0, new_c1, new_c2)
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

        Self::new(c0, c1, c2)
    }

    /// Normalizes the element of `Fq6` by normalizing its components.
    pub fn normalize<CS>(&mut self, cs: &mut CS)
    where
        CS: ConstraintSystem<F>,
    {
        self.c0.normalize(cs);
        self.c1.normalize(cs);
        self.c2.normalize(cs);
    }

    /// Allocate `Fq6` tower extension element from the Witness represented in three components
    /// from the `Fq2` tower extension.
    pub fn constant<CS>(cs: &mut CS, wit: P::Witness, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let constants = P::convert_from_structured_witness(wit);
        let c0 = Fq2::constant(cs, constants[0], params);
        let c1 = Fq2::constant(cs, constants[1], params);
        let c2 = Fq2::constant(cs, constants[2], params);

        Self::new(c0, c1, c2)
    }

    /// Allocate `Fq6` tower extension element from the Witness represented in three components
    /// from the `Fq2` tower extension.
    pub fn allocate_from_witness<CS>(cs: &mut CS, wit: P::Witness, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let components = P::convert_from_structured_witness(wit);
        let c0 = Fq2::allocate_from_witness(cs, components[0], params);
        let c1 = Fq2::allocate_from_witness(cs, components[1], params);
        let c2 = Fq2::allocate_from_witness(cs, components[2], params);

        Self::new(c0, c1, c2)
    }
}

impl<F, T, NN, P> CSAllocatable<F> for Fq6<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension6Params<T>,
{
    type Witness = (
        <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::Witness,
        <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::Witness,
        <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::Witness,
    );

    #[inline(always)]
    fn placeholder_witness() -> Self::Witness {
        (
            <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::placeholder_witness(),
            <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::placeholder_witness(),
            <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::placeholder_witness(),
        )
    }

    #[inline(always)]
    fn allocate_without_value<CS>(cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::allocate_without_value(cs);
        let c1 = <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::allocate_without_value(cs);
        let c2 = <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::allocate_without_value(cs);

        Self::new(c0, c1, c2)
    }

    #[inline(always)]
    fn allocate<CS>(cs: &mut CS, witness: Self::Witness) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let (c0, c1, c2) = witness;

        let c0 = <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::allocate(cs, c0);
        let c1 = <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::allocate(cs, c1);
        let c2 = <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::allocate(cs, c2);

        Self::new(c0, c1, c2)
    }

    #[inline(always)]
    fn allocate_constant<CS>(cs: &mut CS, witness: Self::Witness) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let (c0, c1, c2) = witness;

        let c0 = <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::allocate_constant(cs, c0);
        let c1 = <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::allocate_constant(cs, c1);
        let c2 = <Fq2<F, T, NN, P::Ex2> as CSAllocatable<F>>::allocate_constant(cs, c2);

        Self::new(c0, c1, c2)
    }
}

impl<F, T, NN, P> WitnessHookable<F> for Fq6<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension6Params<T>,
{
    fn witness_hook<CS>(&self, cs: &CS) -> Box<dyn FnOnce() -> Option<Self::Witness> + 'static>
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.witness_hook(cs);
        let c1 = self.c1.witness_hook(cs);
        let c2 = self.c2.witness_hook(cs);

        Box::new(move || {
            let c0 = c0()?;
            let c1 = c1()?;
            let c2 = c2()?;

            Some((c0, c1, c2))
        })
    }
}

impl<F, T, NN, P> CSPlaceholder<F> for Fq6<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T> + CSPlaceholder<F>,
    P: Extension6Params<T>,
{
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let placeholder = <Fq2<F, T, NN, P::Ex2> as CSPlaceholder<F>>::placeholder(cs);

        Self::new(placeholder.clone(), placeholder.clone(), placeholder)
    }
}

impl<F, T, NN, P> CircuitVarLengthEncodable<F> for Fq6<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T> + CircuitVarLengthEncodable<F>,
    P: Extension6Params<T>,
{
    fn encoding_length(&self) -> usize {
        self.c0.encoding_length() + self.c1.encoding_length() + self.c1.encoding_length()
    }

    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, cs: &mut CS, dst: &mut Vec<Variable>) {
        self.c0.encode_to_buffer(cs, dst);
        self.c1.encode_to_buffer(cs, dst);
        self.c2.encode_to_buffer(cs, dst);
    }
}

impl<F, T, NN, P> NonNativeField<F, T> for Fq6<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension6Params<T>,
{
    type Params = NN::Params;

    fn get_params(&self) -> &Arc<Self::Params> {
        self.c0.get_params()
    }

    fn allocated_constant<CS>(cs: &mut CS, value: T, params: &Arc<Self::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = NN::allocated_constant(cs, value, params);
        let c0 = Fq2::new(c0, NN::allocated_constant(cs, T::zero(), params));
        let c1 = Fq2::zero(cs, params);
        let c2 = Fq2::zero(cs, params);

        Self::new(c0, c1, c2)
    }

    fn allocate_checked<CS>(cs: &mut CS, witness: T, params: &Arc<Self::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = NN::allocate_checked(cs, witness, params);
        let c0 = Fq2::new(c0, NN::allocated_constant(cs, T::zero(), params));
        let c1 = Fq2::zero(cs, params);
        let c2 = Fq2::zero(cs, params);

        Self::new(c0, c1, c2)
    }

    fn allocate_checked_without_value<CS>(cs: &mut CS, params: &Arc<Self::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = Fq2::allocate_checked_without_value(cs, params);
        let c1 = Fq2::allocate_checked_without_value(cs, params);
        let c2 = Fq2::allocate_checked_without_value(cs, params);

        Self::new(c0, c1, c2)
    }

    fn is_zero<CS>(&mut self, cs: &mut CS) -> Boolean<F>
    where
        CS: ConstraintSystem<F>,
    {
        self.is_zero(cs)
    }

    fn negated<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.negated(cs)
    }

    fn equals<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Boolean<F>
    where
        CS: ConstraintSystem<F>,
    {
        let is_c0_equal = self.c0.equals(cs, &mut other.c0);
        let is_c1_equal = self.c1.equals(cs, &mut other.c1);
        let is_c2_equal = self.c2.equals(cs, &mut other.c2);
        Boolean::multi_and(cs, &[is_c0_equal, is_c1_equal, is_c2_equal])
    }

    fn add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.add(cs, other)
    }

    fn lazy_add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.add(cs, other)
    }

    fn add_many_lazy<CS, const M: usize>(cs: &mut CS, inputs: [&mut Self; M]) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        assert!(M != 0, "add_many_lazy: inputs must not be empty");

        let params = inputs[0].get_params();
        let mut result = Self::zero(cs, params);

        for i in 0..M {
            result = result.add(cs, inputs[i]);
        }

        result
    }

    fn sub<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.sub(cs, other)
    }

    fn lazy_sub<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.sub(cs, other)
    }

    fn double<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.double(cs)
    }

    fn lazy_double<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.double(cs)
    }

    fn mul<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.mul(cs, other)
    }

    fn square<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.square(cs)
    }

    fn div_unchecked<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.div(cs, other)
    }

    #[allow(unused_variables)]
    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self {
        let c0 = <Fq2<F, T, NN, <P as Extension6Params<T>>::Ex2>>::conditionally_select(
            cs, flag, &a.c0, &b.c0,
        );
        let c1 = <Fq2<F, T, NN, <P as Extension6Params<T>>::Ex2>>::conditionally_select(
            cs, flag, &a.c1, &b.c1,
        );
        let c2 = <Fq2<F, T, NN, <P as Extension6Params<T>>::Ex2>>::conditionally_select(
            cs, flag, &a.c2, &b.c2,
        );

        Self::new(c0, c1, c2)
    }

    #[allow(unused_variables)]
    fn allocate_inverse_or_zero<CS>(&self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // TODO: Make check for zero.
        let mut self_cloned = self.clone();
        self_cloned.inverse(cs)
    }

    fn inverse_unchecked<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.inverse(cs)
    }

    #[allow(unused_variables)]
    fn normalize<CS>(&mut self, cs: &mut CS)
    where
        CS: ConstraintSystem<F>,
    {
        self.c0.normalize(cs);
        self.c1.normalize(cs);
        self.c2.normalize(cs);
    }

    fn mask<CS>(&self, cs: &mut CS, masking_bit: Boolean<F>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.mask(cs, masking_bit);
        let c1 = self.c1.mask(cs, masking_bit);
        let c2 = self.c2.mask(cs, masking_bit);

        Self::new(c0, c1, c2)
    }

    fn mask_negated<CS>(&self, cs: &mut CS, masking_bit: Boolean<F>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.mask_negated(cs, masking_bit);
        let c1 = self.c1.mask_negated(cs, masking_bit);
        let c2 = self.c2.mask_negated(cs, masking_bit);

        Self::new(c0, c1, c2)
    }

    fn enforce_reduced<CS>(&mut self, cs: &mut CS)
    where
        CS: ConstraintSystem<F>,
    {
        self.c0.enforce_reduced(cs);
        self.c1.enforce_reduced(cs);
        self.c2.enforce_reduced(cs);
    }

    fn enforce_equal<CS>(cs: &mut CS, a: &Self, b: &Self)
    where
        CS: ConstraintSystem<F>,
    {
        Fq2::enforce_equal(cs, &a.c0, &b.c0);
        Fq2::enforce_equal(cs, &a.c1, &b.c1);
        Fq2::enforce_equal(cs, &a.c2, &b.c2);
    }
}

impl<F, NN> Selectable<F> for Fq6<F, BN256Fq, NN, BN256Extension6Params>
where
    F: SmallField,
    NN: NonNativeField<F, BN256Fq>,
{
    fn conditionally_select<CS>(cs: &mut CS, flag: Boolean<F>, a: &Self, b: &Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 =
            <Fq2<F, BN256Fq, NN, BN256Extension2Params> as Selectable<F>>::conditionally_select(
                cs, flag, &a.c0, &b.c0,
            );
        let c1 =
            <Fq2<F, BN256Fq, NN, BN256Extension2Params> as Selectable<F>>::conditionally_select(
                cs, flag, &a.c1, &b.c1,
            );
        let c2 =
            <Fq2<F, BN256Fq, NN, BN256Extension2Params> as Selectable<F>>::conditionally_select(
                cs, flag, &a.c2, &b.c2,
            );

        Self::new(c0, c1, c2)
    }
}
