use std::sync::Arc;

use pairing::GenericCurveAffine;

use crate::{
    cs::traits::cs::ConstraintSystem,
    gadgets::{boolean::Boolean, non_native_field::traits::NonNativeField},
};

use super::*;

pub struct ZeroableAffinePoint<F: SmallField, C: GenericCurveAffine, NN: NonNativeField<F, C::Base>>
where
    C::Base: pairing::ff::PrimeField,
{
    pub x: NN,
    pub y: NN,
    pub is_zero: Boolean<F>,
    pub _marker: std::marker::PhantomData<C>,
}

// we only need add/sub/double/negate Mul is implemented by naive double-and-add, and we can have special
// mul that will multiply by an element of scalar field, where zeroness-exception can only happen once.

// We also create decompress function for convenience

impl<F: SmallField, C: GenericCurveAffine, NN: NonNativeField<F, C::Base>>
    ZeroableAffinePoint<F, C, NN>
where
    C::Base: pairing::ff::PrimeField,
{
    pub fn zero_point<CS: ConstraintSystem<F>>(cs: &mut CS, params: &Arc<NN::Params>) -> Self {
        use pairing::ff::Field;
        let zero_nn = NN::allocated_constant(cs, C::Base::zero(), params);
        let boolean_true = Boolean::allocated_constant(cs, true);

        Self {
            x: zero_nn.clone(),
            y: zero_nn,
            is_zero: boolean_true,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn same_x<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Boolean<F> {
        self.x.equals(cs, &mut other.x)
    }

    pub fn same_y<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Boolean<F> {
        self.y.equals(cs, &mut other.y)
    }

    #[allow(unused_assignments)]
    pub fn add_unequal<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, other: &mut Self) -> Self {
        let same_x = self.same_x(cs, other);
        let boolean_false = Boolean::allocated_constant(cs, false);
        Boolean::enforce_equal(cs, &same_x, &boolean_false);

        let mut divisor = self.x.sub(cs, &mut other.x);
        let mut numerator = self.y.sub(cs, &mut other.y);
        let mut slope = numerator.div_unchecked(cs, &mut divisor);
        let mut x2 = slope.clone();
        x2 = x2.mul(cs, &mut slope);
        let mut tmp = self.x.add(cs, &mut other.x);
        x2 = x2.sub(cs, &mut tmp);

        let mut tmp = self.x.sub(cs, &mut x2);
        let mut y2 = slope.mul(cs, &mut tmp);
        y2 = y2.add(cs, &mut self.y);

        todo!()
    }
}
