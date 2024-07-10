use std::sync::Arc;

use pairing::{bn256::Fq as BN256Fq, ff::PrimeField, BitIterator};

use super::{
    fq2::Fq2,
    fq6::Fq6,
    params::{
        bn256::{BN256Extension12Params, BN256Extension6Params},
        Extension12Params, Extension6Params,
    },
};

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
use crate::{cs::Variable, gadgets::traits::hardexp_compatible::HardexpCompatible};

/// `Fq12` field extension implementation in the constraint system. It is implemented
/// as `Fq6[w]/(w^2-v)` where `w^6=9+u`. In other words, it is a set of
/// linear polynomials in a form `c0+c1*w`, where `c0` and `c1` are elements of `Fq6`.
/// See https://hackmd.io/@jpw/bn254#Field-extension-towers for reference. For
/// implementation reference, see https://eprint.iacr.org/2006/471.pdf.
#[derive(Clone, Debug, Copy)]
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

    pub fn from_c0c3c4<CS>(
        cs: &mut CS,
        c0: Fq2<F, T, NN, <<P as Extension12Params<T>>::Ex6 as Extension6Params<T>>::Ex2>,
        c3: Fq2<F, T, NN, <<P as Extension12Params<T>>::Ex6 as Extension6Params<T>>::Ex2>,
        c4: Fq2<F, T, NN, <<P as Extension12Params<T>>::Ex6 as Extension6Params<T>>::Ex2>,
    ) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let zero = Fq2::zero(cs, c0.c0.get_params());
        let c0 = Fq6::new(c0.clone(), zero.clone(), zero.clone());
        let c1 = Fq6::new(c3.clone(), c4.clone(), zero);

        Self::new(c0, c1)
    }

    pub fn pow_u32<CS, S: AsRef<[u64]>>(&mut self, cs: &mut CS, exponent: S) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut result = Self::one(cs, self.c0.c0.get_params());
        let mut found_one = false;

        for i in BitIterator::new(exponent) {
            let apply_squaring = Boolean::allocated_constant(cs, found_one);
            let result_squared = result.square(cs);
            result = Self::conditionally_select(cs, apply_squaring, &result_squared, &result);
            if !found_one {
                found_one = i;
            }

            let result_multiplied = result.mul(cs, self);
            let apply_multiplication = Boolean::allocated_constant(cs, i);
            result =
                Self::conditionally_select(cs, apply_multiplication, &result_multiplied, &result);

            // Normalize the result to stay in field
            NonNativeField::normalize(&mut result, cs);
        }

        result
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

    /// Creates a unit `Fq12` in a form `0+1*w`
    pub fn one_imaginary<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let one = Fq6::zero(cs, params);
        let zero = Fq6::one(cs, params);
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

    /// Allocate `Fq12` tower extension element from the Witness represented in two components
    /// from the `Fq6` tower extension.
    pub fn constant<CS>(cs: &mut CS, wit: P::Witness, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let (c0, c1) = P::convert_from_structured_witness(wit);
        let c0 = Fq6::constant(cs, c0, params);
        let c1 = Fq6::constant(cs, c1, params);

        Self::new(c0, c1)
    }

    /// Allocate `Fq12` tower extension element from the Witness represented in two components
    /// from the `Fq6` tower extension.
    pub fn allocate_from_witness<CS>(cs: &mut CS, wit: P::Witness, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let (c0, c1) = P::convert_from_structured_witness(wit);
        let c0 = Fq6::allocate_from_witness(cs, c0, params);
        let c1 = Fq6::allocate_from_witness(cs, c1, params);

        Self::new(c0, c1)
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
        let mut v0 = self.c0.mul(cs, &mut other.c0);
        let mut v1 = self.c1.mul(cs, &mut other.c1);
        let mut o = other.c0.add(cs, &mut other.c1);

        let mut c1 = self.c1.add(cs, &mut self.c0);
        let mut c1 = c1.mul(cs, &mut o);
        let mut c1 = c1.sub(cs, &mut v0);
        let c1 = c1.sub(cs, &mut v1);

        let mut c0 = v1.mul_by_nonresidue(cs);
        let c0 = c0.add(cs, &mut v0);

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

        let mut new_c1 = self.c1.add(cs, &mut self.c0);
        let mut new_c1 = new_c1.mul_by_c0c1(cs, c0, &mut o);
        let mut new_c1 = new_c1.sub(cs, &mut aa);
        let new_c1 = new_c1.sub(cs, &mut bb);

        let mut new_c0 = bb.mul_by_nonresidue(cs);
        let new_c0 = new_c0.add(cs, &mut aa);

        Self::new(new_c0, new_c1)
    }

    /// Sparse multiplication by constants `c0` and `c3` and `c4` in the form `c0 + (c3 + c4*v)*w`.
    /// See _Algorithm_ 21 from https://eprint.iacr.org/2010/354.pdf.
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
        // Below, a0+a1*w is self b0+b1*w with b0=b00=c0 and b1=b10+b11*v=c3+c4*v
        // is the element to multiply with

        // t0 <- a0*b0
        let mut t0 = self.c0.mul_by_c0(cs, c0);
        // t1 <- a1*b1
        let mut t1 = self.c1.mul_by_c0c1(cs, c3, c4);
        // c0 <- t0 + t1*gamma
        let mut t1_gamma = t1.mul_by_nonresidue(cs);
        let new_c0 = t0.add(cs, &mut t1_gamma);
        // t2 <- (b0+b10)v + b11*v + 0*v^2
        let mut t2_c0 = c0.add(cs, c3);
        let mut t2_c1 = c4.clone();
        // c1 <- (a0 + a1) * t2
        let mut new_c1 = self.c0.add(cs, &mut self.c1);
        let mut new_c1 = new_c1.mul_by_c0c1(cs, &mut t2_c0, &mut t2_c1);
        // c1 <- c1 - t0 - t1
        let mut new_c1 = new_c1.sub(cs, &mut t0);
        let new_c1 = new_c1.sub(cs, &mut t1);

        Self::new(new_c0, new_c1)
    }

    /// Multiplies the `Fq12` element by a constant `c5*v^2*w` represented as `Fq2`.
    pub fn mul_by_c5<CS>(
        &mut self,
        cs: &mut CS,
        c5: &mut Fq2<F, T, NN, <<P as Extension12Params<T>>::Ex6 as Extension6Params<T>>::Ex2>,
    ) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // Suppose our element is a0+a1*w. Then,
        // (a0+a1*w)*c5*v^2*w = a1*c5*w^2*v^2 + a0*c5*v^2*w
        // Notice that w^2*v^2 = v^3 = \xi and therefore our result
        // is a1*c5*\xi + a0*c5*v^2*w

        // new_c0 <- a1*c5*\xi
        let mut new_c0 = self.c1.mul_by_c0(cs, c5);
        new_c0 = new_c0.mul_by_xi(cs);

        // new_c1 <- a0*c5*v^2*w
        let new_c1 = self.c0.mul_by_c2(cs, c5);

        Self::new(new_c0, new_c1)
    }

    /// Compute the Frobenius map - raise this element to power.
    pub fn frobenius_map<CS>(&mut self, cs: &mut CS, power: usize) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.frobenius_map(cs, power);
        let mut c1 = self.c1.frobenius_map(cs, power);

        let c1_c0_frobenius_constant = P::FROBENIUS_COEFFS_C1[power % 12];
        let c1_c1_frobenius_constant = P::FROBENIUS_COEFFS_C1[power % 12];
        let c1_c2_frobenius_constant = P::FROBENIUS_COEFFS_C1[power % 12];

        let params = c1.c0.get_params();

        let mut c1_c0_frobenius_coeff = Fq2::constant(cs, c1_c0_frobenius_constant, params);
        let mut c1_c1_frobenius_coeff = Fq2::constant(cs, c1_c1_frobenius_constant, params);
        let mut c1_c2_frobenius_coeff = Fq2::constant(cs, c1_c2_frobenius_constant, params);

        let c1_c0 = c1.c0.mul(cs, &mut c1_c0_frobenius_coeff);
        let c1_c1 = c1.c1.mul(cs, &mut c1_c1_frobenius_coeff);
        let c1_c2 = c1.c2.mul(cs, &mut c1_c2_frobenius_coeff);

        let c1 = Fq6::new(c1_c0, c1_c1, c1_c2);

        Self::new(c0, c1)
    }

    pub fn inverse<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut c0s = self.c0.square(cs);
        let mut c1s = self.c1.square(cs);
        let mut c1s = c1s.mul_by_nonresidue(cs);
        let mut c0s = c0s.sub(cs, &mut c1s);

        c0s.normalize(cs);
        let mut t = c0s.inverse(cs);
        let c0_new = t.mul(cs, &mut self.c0);
        let mut c1_new = t.mul(cs, &mut self.c1);
        let c1_new = c1_new.negated(cs);

        Self::new(c0_new, c1_new)
    }

    pub fn div<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut t = other.inverse(cs);
        self.mul(cs, &mut t)
    }
}

impl<F, T, NN, P> CSAllocatable<F> for Fq12<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension12Params<T>,
{
    type Witness = (
        <Fq6<F, T, NN, P::Ex6> as CSAllocatable<F>>::Witness,
        <Fq6<F, T, NN, P::Ex6> as CSAllocatable<F>>::Witness,
    );

    #[inline(always)]
    fn placeholder_witness() -> Self::Witness {
        (
            <Fq6<F, T, NN, P::Ex6> as CSAllocatable<F>>::placeholder_witness(),
            <Fq6<F, T, NN, P::Ex6> as CSAllocatable<F>>::placeholder_witness(),
        )
    }

    #[inline(always)]
    fn allocate_without_value<CS>(cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = <Fq6<F, T, NN, P::Ex6> as CSAllocatable<F>>::allocate_without_value(cs);
        let c1 = <Fq6<F, T, NN, P::Ex6> as CSAllocatable<F>>::allocate_without_value(cs);

        Self::new(c0, c1)
    }

    #[inline(always)]
    fn allocate<CS>(cs: &mut CS, witness: Self::Witness) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let (c0, c1) = witness;

        let c0 = <Fq6<F, T, NN, P::Ex6> as CSAllocatable<F>>::allocate(cs, c0);
        let c1 = <Fq6<F, T, NN, P::Ex6> as CSAllocatable<F>>::allocate(cs, c1);

        Self::new(c0, c1)
    }

    #[inline(always)]
    fn allocate_constant<CS>(cs: &mut CS, witness: Self::Witness) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let (c0, c1) = witness;

        let c0 = <Fq6<F, T, NN, P::Ex6> as CSAllocatable<F>>::allocate_constant(cs, c0);
        let c1 = <Fq6<F, T, NN, P::Ex6> as CSAllocatable<F>>::allocate_constant(cs, c1);

        Self::new(c0, c1)
    }
}

impl<F, T, NN, P> WitnessHookable<F> for Fq12<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension12Params<T>,
{
    fn witness_hook<CS>(&self, cs: &CS) -> Box<dyn FnOnce() -> Option<Self::Witness> + 'static>
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.witness_hook(cs);
        let c1 = self.c1.witness_hook(cs);

        Box::new(move || {
            let c0 = c0()?;
            let c1 = c1()?;

            Some((c0, c1))
        })
    }
}

impl<F, T, NN, P> CSPlaceholder<F> for Fq12<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T> + CSPlaceholder<F>,
    P: Extension12Params<T>,
{
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let placeholder = <Fq6<F, T, NN, P::Ex6> as CSPlaceholder<F>>::placeholder(cs);

        Self::new(placeholder.clone(), placeholder.clone())
    }
}

impl<F, T, NN, P> CircuitVarLengthEncodable<F> for Fq12<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T> + CircuitVarLengthEncodable<F>,
    P: Extension12Params<T>,
{
    fn encoding_length(&self) -> usize {
        self.c0.encoding_length() + self.c1.encoding_length()
    }

    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, cs: &mut CS, dst: &mut Vec<Variable>) {
        self.c0.encode_to_buffer(cs, dst);
        self.c1.encode_to_buffer(cs, dst);
    }
}

impl<F, T, NN, P> NonNativeField<F, T> for Fq12<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension12Params<T>,
{
    type Params = NN::Params;

    fn get_params(&self) -> &Arc<Self::Params> {
        self.c0.get_params()
    }

    fn allocated_constant<CS>(cs: &mut CS, value: T, params: &Arc<Self::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let zero = NN::allocated_constant(cs, T::zero(), params);
        let c0 = NN::allocated_constant(cs, value, params);
        let c0 = Fq2::new(c0, zero);
        let c0 = Fq6::new(c0, Fq2::zero(cs, params), Fq2::zero(cs, params));
        let c1 = Fq6::zero(cs, params);

        Self::new(c0, c1)
    }

    fn allocate_checked<CS>(cs: &mut CS, witness: T, params: &Arc<Self::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let zero = NN::allocate_checked(cs, T::zero(), params);
        let c0 = NN::allocate_checked(cs, witness, params);
        let c0 = Fq2::new(c0, zero);
        let c0 = Fq6::new(c0, Fq2::zero(cs, params), Fq2::zero(cs, params));
        let c1 = Fq6::zero(cs, params);

        Self::new(c0, c1)
    }

    fn allocate_checked_without_value<CS>(cs: &mut CS, params: &Arc<Self::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = Fq6::allocate_checked_without_value(cs, params);
        let c1 = Fq6::allocate_checked_without_value(cs, params);

        Self::new(c0, c1)
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
        is_c0_equal.and(cs, is_c1_equal)
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
        let c0 = <Fq6<F, T, NN, <P as Extension12Params<T>>::Ex6>>::conditionally_select(
            cs, flag, &a.c0, &b.c0,
        );
        let c1 = <Fq6<F, T, NN, <P as Extension12Params<T>>::Ex6>>::conditionally_select(
            cs, flag, &a.c1, &b.c1,
        );

        Self::new(c0, c1)
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
    }

    fn mask<CS>(&self, cs: &mut CS, masking_bit: Boolean<F>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.mask(cs, masking_bit);
        let c1 = self.c1.mask(cs, masking_bit);

        Self::new(c0, c1)
    }

    fn mask_negated<CS>(&self, cs: &mut CS, masking_bit: Boolean<F>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.mask_negated(cs, masking_bit);
        let c1 = self.c1.mask_negated(cs, masking_bit);

        Self::new(c0, c1)
    }

    fn enforce_reduced<CS>(&mut self, cs: &mut CS)
    where
        CS: ConstraintSystem<F>,
    {
        self.c0.enforce_reduced(cs);
        self.c1.enforce_reduced(cs);
    }

    fn enforce_equal<CS>(cs: &mut CS, a: &Self, b: &Self)
    where
        CS: ConstraintSystem<F>,
    {
        Fq6::enforce_equal(cs, &a.c0, &b.c0);
        Fq6::enforce_equal(cs, &a.c1, &b.c1);
    }
}

impl<F, NN> Selectable<F> for Fq12<F, BN256Fq, NN, BN256Extension12Params>
where
    F: SmallField,
    NN: NonNativeField<F, BN256Fq>,
{
    fn conditionally_select<CS>(cs: &mut CS, flag: Boolean<F>, a: &Self, b: &Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 =
            <Fq6<F, BN256Fq, NN, BN256Extension6Params> as Selectable<F>>::conditionally_select(
                cs, flag, &a.c0, &b.c0,
            );
        let c1 =
            <Fq6<F, BN256Fq, NN, BN256Extension6Params> as Selectable<F>>::conditionally_select(
                cs, flag, &a.c1, &b.c1,
            );

        Self::new(c0, c1)
    }
}

impl<F, T, NN, P> HardexpCompatible<F> for Fq12<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension12Params<T>,
{
    fn conjugate<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.conjugate(cs)
    }

    fn pow_u32<CS, S: AsRef<[u64]>>(&mut self, cs: &mut CS, exponent: S) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.pow_u32(cs, exponent)
    }

    fn frobenius_map<CS>(&mut self, cs: &mut CS, power: usize) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.frobenius_map(cs, power)
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

    fn inverse<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.inverse(cs)
    }

    fn normalize<CS>(&mut self, cs: &mut CS)
    where
        CS: ConstraintSystem<F>,
    {
        self.c0.normalize(cs);
        self.c1.normalize(cs);
    }
}
