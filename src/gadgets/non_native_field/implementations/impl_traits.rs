use crate::gadgets::traits::selectable::Selectable;

use super::*;

use super::super::traits::NonNativeField;
use crate::gadgets::boolean::Boolean;

impl<F: SmallField, T: pairing::ff::PrimeField, const N: usize> NonNativeField<F, T>
    for NonNativeFieldOverU16<F, T, N>
where
    [(); N + 1]:,
{
    type Params = NonNativeFieldOverU16Params<T, N>;

    fn get_params(&self) -> &Arc<Self::Params> {
        &self.params
    }

    fn allocated_constant<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        value: T,
        params: &Arc<Self::Params>,
    ) -> Self {
        NonNativeFieldOverU16::<F, T, N>::allocated_constant(cs, value, params)
    }
    fn allocate_checked_without_value<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        params: &Arc<Self::Params>,
    ) -> Self {
        NonNativeFieldOverU16::<F, T, N>::allocate_checked_without_value(cs, params)
    }
    fn allocate_checked<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        witness: T,
        params: &Arc<Self::Params>,
    ) -> Self {
        NonNativeFieldOverU16::<F, T, N>::allocate_checked(cs, witness, params)
    }

    fn enforce_reduced<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) {
        NonNativeFieldOverU16::<F, T, N>::enforce_reduced(self, cs)
    }
    fn normalize<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) {
        NonNativeFieldOverU16::<F, T, N>::normalize(self, cs)
    }

    fn add<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        NonNativeFieldOverU16::<F, T, N>::add(self, cs, other)
    }

    fn double<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        NonNativeFieldOverU16::<F, T, N>::double(self, cs)
    }

    fn negated<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        NonNativeFieldOverU16::<F, T, N>::negated(self, cs)
    }

    fn sub<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        NonNativeFieldOverU16::<F, T, N>::sub(self, cs, other)
    }

    fn lazy_add<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        NonNativeFieldOverU16::<F, T, N>::lazy_add(self, cs, other)
    }

    fn lazy_double<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        let mut other = self.clone();
        self.lazy_add(cs, &mut other)
    }

    fn lazy_sub<CS: ConstraintSystem<F>>(&mut self, _cs: &mut CS, _other: &mut Self) -> Self {
        todo!()
    }

    fn add_many_lazy<CS: ConstraintSystem<F>, const M: usize>(
        cs: &mut CS,
        inputs: [&mut Self; M],
    ) -> Self {
        NonNativeFieldOverU16::<F, T, N>::add_many_lazy(cs, inputs)
    }

    fn mul<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        NonNativeFieldOverU16::<F, T, N>::mul(self, cs, other)
    }

    fn square<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        NonNativeFieldOverU16::<F, T, N>::square(self, cs)
    }

    fn div_unchecked<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        NonNativeFieldOverU16::<F, T, N>::div_unchecked(self, cs, other)
    }

    fn allocate_inverse_or_zero<CS: ConstraintSystem<F>>(&self, _cs: &mut CS) -> Self {
        todo!()
    }

    fn inverse_unchecked<CS: ConstraintSystem<F>>(&mut self, _cs: &mut CS) -> Self {
        todo!()
    }

    fn is_zero<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Boolean<F> {
        NonNativeFieldOverU16::<F, T, N>::is_zero(self, cs)
    }

    fn equals<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Boolean<F> {
        NonNativeFieldOverU16::<F, T, N>::equals(cs, self, other)
    }

    fn mask<CS: ConstraintSystem<F>>(&self, cs: &mut CS, masking_bit: Boolean<F>) -> Self {
        NonNativeFieldOverU16::<F, T, N>::mask(self, cs, masking_bit)
    }

    fn mask_negated<CS: ConstraintSystem<F>>(&self, cs: &mut CS, masking_bit: Boolean<F>) -> Self {
        NonNativeFieldOverU16::<F, T, N>::mask_negated(self, cs, masking_bit)
    }

    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self {
        <NonNativeFieldOverU16<F, T, N> as Selectable<F>>::conditionally_select(cs, flag, a, b)
    }
}
