use super::*;
use crate::gadgets::boolean::Boolean;
use crate::{cs::traits::cs::ConstraintSystem, gadgets::traits::witnessable::WitnessHookable};
use std::sync::Arc;

pub trait NonNativeField<F: SmallField, T: pairing::ff::PrimeField>:
    'static + Send + Sync + Clone + std::fmt::Debug + WitnessHookable<F>
{
    type Params: 'static + Send + Sync + Clone + std::fmt::Debug;

    fn get_params(&self) -> &Arc<Self::Params>;

    fn allocated_constant<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        value: T,
        params: &Arc<Self::Params>,
    ) -> Self;
    fn allocate_checked_without_value<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        params: &Arc<Self::Params>,
    ) -> Self;
    fn allocate_checked<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        witness: T,
        params: &Arc<Self::Params>,
    ) -> Self;

    fn enforce_reduced<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS);
    fn normalize<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS);

    fn add<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self;

    fn double<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        let mut other = self.clone();
        self.add(cs, &mut other)
    }

    fn negated<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self;

    fn sub<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self;

    fn lazy_add<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self;

    fn lazy_double<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        let mut other = self.clone();
        self.lazy_add(cs, &mut other)
    }

    fn lazy_sub<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self;

    fn add_many_lazy<CS: ConstraintSystem<F>, const M: usize>(
        cs: &mut CS,
        inputs: [&mut Self; M],
    ) -> Self;

    fn mul<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self;

    fn square<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        let mut other = self.clone();
        self.mul(cs, &mut other)
    }

    fn div_unchecked<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self;

    fn allocate_inverse_or_zero<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Self;

    fn inverse_unchecked<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self;

    fn is_zero<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Boolean<F>;
    fn equals<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Boolean<F>;

    fn mask<CS: ConstraintSystem<F>>(&self, cs: &mut CS, masking_bit: Boolean<F>) -> Self;
    fn mask_negated<CS: ConstraintSystem<F>>(&self, cs: &mut CS, masking_bit: Boolean<F>) -> Self;

    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self;
}
