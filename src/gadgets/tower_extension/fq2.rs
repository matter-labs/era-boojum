use std::sync::Arc;

use pairing::{
    bn256::{Fq as BN256Fq, Fq2 as BN256Fq2, G2Affine},
    ff::PrimeField,
};

use super::params::{bn256::BN256Extension2Params, Extension2Params};

use crate::cs::Variable;
use crate::gadgets::traits::allocatable::CSPlaceholder;
use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;
use crate::{
    cs::traits::cs::ConstraintSystem,
    field::SmallField,
    gadgets::{
        boolean::Boolean,
        non_native_field::traits::{CurveCompatibleNonNativeField, NonNativeField},
        traits::{
            allocatable::CSAllocatable, selectable::Selectable, witnessable::WitnessHookable,
        },
    },
};

/// BN256Fq2Params represents a pair of elements in the extension field `Fq2=Fq[u]/(u^2-beta)`
/// where `beta^2=-1`. The implementation is primarily based on the following paper:
/// https://eprint.iacr.org/2006/471.pdf.
#[derive(Clone, Debug, Copy)]
pub struct Fq2<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension2Params<T>,
{
    pub c0: NN,
    pub c1: NN,
    wit: Option<P::Witness>,
    _marker: std::marker::PhantomData<(F, T, P)>,
}

impl<F, T, NN, P> Fq2<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension2Params<T>,
{
    /// Creates a new `Fq2` element from two `Fq` components.
    pub fn new(c0: NN, c1: NN) -> Self {
        Self {
            c0,
            c1,
            wit: Option::None, // to get placeholder_witness we need CS
            _marker: std::marker::PhantomData::<(F, T, P)>,
        }
    }

    /// Creates a new `Fq2` in a form `0+0*u`
    pub fn zero<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let zero = NN::allocated_constant(cs, T::zero(), params);

        Self::new(zero.clone(), zero)
    }

    /// Creates a new `Fq2` in a form `1+0*u`
    pub fn one<CS>(cs: &mut CS, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let one = NN::allocated_constant(cs, T::one(), params);
        let zero = NN::allocated_constant(cs, T::zero(), params);

        Self::new(one, zero)
    }

    /// Adds two elements of `Fq2` by adding their components elementwise.
    #[must_use]
    pub fn add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.add(cs, &mut other.c0);
        let c1 = self.c1.add(cs, &mut other.c1);
        Self::new(c0, c1)
    }

    /// Returns whether the element of `Fq2` is zero.
    pub fn is_zero<CS>(&mut self, cs: &mut CS) -> Boolean<F>
    where
        CS: ConstraintSystem<F>,
    {
        let is_c0_zero = self.c0.is_zero(cs);
        let is_c1_zero = self.c1.is_zero(cs);
        is_c0_zero.and(cs, is_c1_zero)
    }

    /// Doubles the element of `Fq2` by doubling its components.
    #[must_use]
    pub fn double<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = self.c0.double(cs);
        let c1 = self.c1.double(cs);
        Self::new(c0, c1)
    }

    /// Negates the element of `Fq2` by negating its components.
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
        let c1 = self.c1.negated(cs);
        Self::new(self.c0.clone(), c1)
    }

    /// Subtracts two elements of `Fq2` by subtracting their components elementwise.
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

    /// Multiply the element `a=a0+a1*u` by the element in the base field `Fq`.
    #[must_use]
    pub fn mul_c0<CS>(&mut self, cs: &mut CS, c0: &mut NN) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // a*f = (a0 + a1*u)*f = (a0*f) + (a1*f)*u
        let new_c0 = self.c0.mul(cs, c0);
        let new_c1 = self.c1.mul(cs, c0);
        Self::new(new_c0, new_c1)
    }

    /// Finds the inverse of the element `a=a0+a1*u` in the extension field `Fq2`.
    #[must_use]
    pub fn inverse<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut t0 = self.c0.square(cs);
        let mut t1 = self.c1.square(cs);
        let mut t0 = t0.add(cs, &mut t1);
        let mut t = t0.inverse_unchecked(cs);

        let c0 = self.c0.mul(cs, &mut t);
        let mut c1 = self.c1.mul(cs, &mut t);
        let c1 = c1.negated(cs);

        Self::new(c0, c1)
    }

    /// Divides the element `a=a0+a1*u` by the element `b=b0+b1*u` in the extension field `Fq2`.
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
        // Finding 8(a0 + a1*u)
        let mut new = self.double(cs);
        new = new.double(cs);
        new = new.double(cs);

        // c0 <- 9*c0 - c1
        let mut c0 = new.c0.add(cs, &mut self.c0);
        let c0 = c0.sub(cs, &mut self.c1);

        // c1 <- c0 + 9*c1
        let mut c1 = new.c1.add(cs, &mut self.c1);
        let c1 = c1.add(cs, &mut self.c0);

        Self::new(c0, c1)
    }

    /// Compute the Frobenius map - raise this element to power.
    pub fn frobenius_map<CS>(&mut self, cs: &mut CS, power: usize) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let is_even = Boolean::allocated_constant(cs, power % 2 == 0);

        // TODO: check what non-residue == -1.

        let c0 = self.c0.clone();
        let c1 = self.c1.negated(cs);

        // TODO: assert what Fp2 under CS computes frobenius map same as without CS and this optimizational hack.

        <Fq2<F, T, NN, P> as NonNativeField<F, T>>::conditionally_select(
            cs,
            is_even,
            &self.clone(),
            &Self::new(c0, c1),
        )
    }

    /// Allocate `Fq2` tower extension element from the Witness represented in two PrimeField components `c0` and `c1`.
    pub fn constant<CS>(cs: &mut CS, wit: P::Witness, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let (c0, c1) = P::convert_from_structured_witness(wit);

        let c0 = NN::allocated_constant(cs, c0, params);
        let c1 = NN::allocated_constant(cs, c1, params);

        Self::new(c0, c1)
    }

    /// Allocate `Fq2` tower extension element from the Witness represented in two PrimeField components `c0` and `c1`.
    pub fn allocate_from_witness<CS>(cs: &mut CS, wit: P::Witness, params: &Arc<NN::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let (c0, c1) = P::convert_from_structured_witness(wit);

        let c0 = NN::allocate_checked(cs, c0, params);
        let c1 = NN::allocate_checked(cs, c1, params);

        Self::new(c0, c1)
    }
}

impl<F, T, NN, P> CSAllocatable<F> for Fq2<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension2Params<T>,
{
    type Witness = (NN::Witness, NN::Witness);

    #[inline(always)]
    fn placeholder_witness() -> Self::Witness {
        (NN::placeholder_witness(), NN::placeholder_witness())
    }

    #[inline(always)]
    fn allocate_without_value<CS>(cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = NN::allocate_without_value(cs);
        let c1 = NN::allocate_without_value(cs);

        Self::new(c0, c1)
    }

    #[inline(always)]
    fn allocate<CS>(cs: &mut CS, witness: Self::Witness) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let (c0, c1) = witness;

        let c0 = NN::allocate(cs, c0);
        let c1 = NN::allocate(cs, c1);

        Self::new(c0, c1)
    }

    #[inline(always)]
    fn allocate_constant<CS>(cs: &mut CS, witness: Self::Witness) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let (c0, c1) = witness;

        let c0 = NN::allocate_constant(cs, c0);
        let c1 = NN::allocate_constant(cs, c1);

        Self::new(c0, c1)
    }
}

impl<F, T, NN, P> WitnessHookable<F> for Fq2<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension2Params<T>,
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

impl<F, T, NN, P> CSPlaceholder<F> for Fq2<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T> + CSPlaceholder<F>,
    P: Extension2Params<T>,
{
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let c0 = NN::placeholder(cs);
        let c1 = NN::placeholder(cs);

        Self::new(c0, c1)
    }
}

impl<F, T, NN, P> CircuitVarLengthEncodable<F> for Fq2<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T> + CircuitVarLengthEncodable<F>,
    P: Extension2Params<T>,
{
    fn encoding_length(&self) -> usize {
        self.c0.encoding_length() + self.c1.encoding_length()
    }

    fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, cs: &mut CS, dst: &mut Vec<Variable>) {
        self.c0.encode_to_buffer(cs, dst);
        self.c1.encode_to_buffer(cs, dst);
    }
}

impl<F, T, NN, P> NonNativeField<F, T> for Fq2<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension2Params<T>,
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
        let c1 = NN::allocated_constant(cs, T::zero(), params);

        Self::new(c0, c1)
    }

    fn allocate_checked<CS>(cs: &mut CS, witness: T, params: &Arc<Self::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = NN::allocate_checked(cs, witness, params);
        let c1 = NN::allocate_checked(cs, witness, params);

        Self::new(c0, c1)
    }

    fn allocate_checked_without_value<CS>(cs: &mut CS, params: &Arc<Self::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = NN::allocate_checked_without_value(cs, params);
        let c1 = NN::allocate_checked_without_value(cs, params);

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

    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self {
        let c0 = NN::conditionally_select(cs, flag, &a.c0, &b.c0);
        let c1 = NN::conditionally_select(cs, flag, &a.c1, &b.c1);

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
        NN::enforce_equal(cs, &a.c0, &b.c0);
        NN::enforce_equal(cs, &a.c1, &b.c1);
    }
}

impl<F, NN> Selectable<F> for Fq2<F, BN256Fq, NN, BN256Extension2Params>
where
    F: SmallField,
    NN: NonNativeField<F, BN256Fq>,
{
    fn conditionally_select<CS>(cs: &mut CS, flag: Boolean<F>, a: &Self, b: &Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = NN::conditionally_select(cs, flag, &a.c0, &b.c0);
        let c1 = NN::conditionally_select(cs, flag, &a.c1, &b.c1);

        Self::new(c0, c1)
    }
}

impl<F, NN> CurveCompatibleNonNativeField<F, BN256Fq, G2Affine>
    for Fq2<F, BN256Fq, NN, BN256Extension2Params>
where
    F: SmallField,
    NN: NonNativeField<F, BN256Fq>,
{
    fn from_curve_base<CS>(cs: &mut CS, point: &BN256Fq2, params: &Arc<Self::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let c0 = NN::allocated_constant(cs, point.c0, params);
        let c1 = NN::allocated_constant(cs, point.c1, params);

        Self::new(c0, c1)
    }
}
