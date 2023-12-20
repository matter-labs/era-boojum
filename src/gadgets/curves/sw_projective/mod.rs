use super::*;

use crate::gadgets::traits::selectable::Selectable;
use crate::{
    cs::traits::cs::ConstraintSystem,
    gadgets::{boolean::Boolean, non_native_field::traits::NonNativeField},
};
use pairing::GenericCurveAffine;

// https://eprint.iacr.org/2015/1060.pdf

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct SWProjectivePoint<F: SmallField, C: GenericCurveAffine, NN: NonNativeField<F, C::Base>>
where
    C::Base: pairing::ff::PrimeField,
{
    pub x: NN,
    pub y: NN,
    pub z: NN,
    pub _marker: std::marker::PhantomData<(F, C)>,
}

impl<F: SmallField, C: GenericCurveAffine, NN: NonNativeField<F, C::Base>>
    SWProjectivePoint<F, C, NN>
where
    C::Base: pairing::ff::PrimeField,
{
    pub fn from_xy_unchecked<CS: ConstraintSystem<F>>(cs: &mut CS, x: NN, y: NN) -> Self {
        use pairing::ff::Field;

        let params = x.get_params();
        let z = NN::allocated_constant(cs, C::Base::one(), params);

        Self {
            x,
            y,
            z,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn zero<CS: ConstraintSystem<F>>(cs: &mut CS, params: &std::sync::Arc<NN::Params>) -> Self {
        use pairing::ff::Field;

        let x = NN::allocated_constant(cs, C::Base::zero(), params);
        let y = NN::allocated_constant(cs, C::Base::one(), params);
        let z = NN::allocated_constant(cs, C::Base::zero(), params);

        Self {
            x,
            y,
            z,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn double<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        use pairing::ff::Field;
        if C::a_coeff().is_zero() == false {
            return self.generic_double(cs);
        }
        let params = self.x.get_params().clone();

        let mut three = C::Base::one();
        three.double();
        three.add_assign(&C::Base::one());

        let mut four = C::Base::one();
        four.double();
        four.double();

        let curve_b = C::b_coeff();
        let mut curve_b3 = curve_b;
        curve_b3.double();
        curve_b3.add_assign(&curve_b);

        let mut three_nn = NN::allocated_constant(cs, three, &params);
        let mut four_nn = NN::allocated_constant(cs, four, &params);
        let mut curve_b3 = NN::allocated_constant(cs, curve_b3, &params);

        let x = &mut self.x;
        let y = &mut self.y;
        let z = &mut self.z;

        // t0 = y * y
        let mut t0 = y.square(cs);
        // t2 = b3 * z * z
        let mut b3_mul_z = z.mul(cs, &mut curve_b3);
        let mut t2 = b3_mul_z.mul(cs, z);
        // y3 = t0 + t2
        let mut y3: NN = t0.add(cs, &mut t2);
        // t1 = y * z
        let mut t1 = y.mul(cs, z);
        // z3 = 8 * t0 * t1
        let mut t0_mul_4 = t0.mul(cs, &mut four_nn);
        let mut t0_mul_8 = t0_mul_4.double(cs);
        let z3 = t0_mul_8.mul(cs, &mut t1);
        // t4 = 4 * t0 - 3 * y3
        let mut y3_mul_3 = y3.mul(cs, &mut three_nn);
        let mut t4 = t0_mul_4.sub(cs, &mut y3_mul_3);
        // y3 = t4 * y3
        let mut y3 = t4.mul(cs, &mut y3);
        // y3 = 8 * t0 * t2 + y3
        let mut new_y3 = t0_mul_8.mul(cs, &mut t2);
        let new_y3 = new_y3.add(cs, &mut y3);
        let y3 = new_y3;
        // t1 = x * y
        let mut t1 = x.mul(cs, y);
        // x3 = 2 * t4 * t1
        let mut t4_mul_2 = t4.double(cs);
        let x3 = t4_mul_2.mul(cs, &mut t1);

        let new = Self {
            x: x3,
            y: y3,
            z: z3,
            _marker: std::marker::PhantomData,
        };

        new
    }

    fn generic_double<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        use pairing::ff::Field;
        let params = self.x.get_params().clone();

        let curve_b = C::b_coeff();
        let mut curve_b3 = curve_b;
        curve_b3.double();
        curve_b3.add_assign(&curve_b);

        let mut curve_a = NN::allocated_constant(cs, C::a_coeff(), &params);
        let mut curve_b3 = NN::allocated_constant(cs, curve_b3, &params);

        let x = &mut self.x;
        let y = &mut self.y;
        let z = &mut self.z;

        // t0 = x * x
        let mut t0 = x.square(cs);
        // t1 = y * y
        let mut t1 = y.square(cs);
        // t2 = z * z
        let mut t2 = z.square(cs);

        // t3 = x * y
        let mut t3 = x.mul(cs, y);
        // t3 = t3 + t3
        let mut t3 = t3.double(cs);
        // z3 = x * z
        let mut z3 = x.mul(cs, z);

        // z3 = z3 + z3
        let mut z3 = z3.double(cs);
        // x3 = a * z3
        let mut x3 = curve_a.mul(cs, &mut z3);
        // y3 = b3 * t2
        let mut y3 = curve_b3.mul(cs, &mut t2);

        // y3 = x3 + y3
        let mut y3 = x3.add(cs, &mut y3);
        // x3 = t1 - y3
        let mut x3 = t1.sub(cs, &mut y3);
        // y3 = t1 + y3
        let mut y3 = t1.add(cs, &mut y3);

        // y3 = x3 * y3
        let mut y3 = x3.mul(cs, &mut y3);
        // x3 = t3 * x3
        let mut x3 = t3.mul(cs, &mut x3);
        // z3 = b3 * z3
        let mut z3 = curve_b3.mul(cs, &mut z3);

        // t2 = a * t2
        let mut t2 = curve_a.mul(cs, &mut t2);
        // t3 = t0 - t2
        let mut t3 = t0.sub(cs, &mut t2);
        // t3 = a * t3
        let mut t3 = curve_a.mul(cs, &mut t3);

        // t3 = t3 + z3
        let mut t3 = t3.add(cs, &mut z3);
        // z3 = t0 + t0
        let mut z3 = t0.double(cs);
        // t0 = z3 + t0
        let mut t0 = z3.add(cs, &mut t0);

        // t0 = t0 + t2
        let mut t0 = t0.add(cs, &mut t2);
        // t0 = t0 * t3
        let mut t0 = t0.mul(cs, &mut t3);
        // y3 = y3 + y0
        let y3 = y3.add(cs, &mut t0);

        // t2 = y * z
        let mut t2 = y.mul(cs, z);
        // t2 = t2 + t2
        let mut t2 = t2.double(cs);
        // t0 = t2 * t3
        let mut t0 = t2.mul(cs, &mut t3);

        // x3 = x3 - t0
        let x3 = x3.sub(cs, &mut t0);
        // z3 = t2 * t1
        let mut z3 = t2.mul(cs, &mut t1);
        // z3 = z3 + z3
        let mut z3 = z3.double(cs);

        // z3 = z3 + z3
        let z3 = z3.double(cs);

        let new = Self {
            x: x3,
            y: y3,
            z: z3,
            _marker: std::marker::PhantomData,
        };

        new
    }

    pub fn negated<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Self {
        let y_negated = self.y.negated(cs);

        let new = Self {
            x: self.x.clone(),
            y: y_negated,
            z: self.z.clone(),
            _marker: std::marker::PhantomData,
        };

        new
    }

    fn add_sub_mixed_impl<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        other_xy: &mut (NN, NN),
        is_subtraction: bool,
    ) -> Self {
        use pairing::ff::Field;
        if C::a_coeff().is_zero() == false {
            return self.generic_add_sub_mixed_impl(cs, other_xy, is_subtraction);
        }

        let params = self.x.get_params().clone();

        let mut three = C::Base::one();
        three.double();
        three.add_assign(&C::Base::one());

        let curve_b = C::b_coeff();
        let mut curve_b3 = curve_b;
        curve_b3.double();
        curve_b3.add_assign(&curve_b);

        let mut curve_b6 = curve_b3;
        curve_b6.double();

        let mut three_nn = NN::allocated_constant(cs, three, &params);
        let mut curve_b3 = NN::allocated_constant(cs, curve_b3, &params);
        let mut curve_b6 = NN::allocated_constant(cs, curve_b6, &params);

        let x1 = &mut self.x;
        let y1 = &mut self.y;
        let z1 = &mut self.z;

        let mut y2_local: NN = other_xy.1.clone();
        let x2 = &mut other_xy.0;
        if is_subtraction {
            y2_local = y2_local.negated(cs);
        }
        let y2 = &mut y2_local;

        // t4 = y2 * z1 + y1
        let mut t4 = y2.mul(cs, z1);
        let mut t4 = t4.add(cs, y1);

        // y3 = x2 * z1 + x1
        let mut y3 = x2.mul(cs, z1);
        let mut y3 = y3.add(cs, x1);

        // z3 = y1 * y2 + b3 * z1
        let mut z1_mul_b3 = z1.mul(cs, &mut curve_b3);
        let mut z3 = y1.mul(cs, y2);
        let mut z3 = z3.add(cs, &mut z1_mul_b3);

        // t0 = x1 * x2
        let mut t0 = x1.mul(cs, x2);

        // t3 = (x2 + y2) * (x1 + y1) - t0 - z3 + b3 * z1
        let mut a = x2.add(cs, y2);
        let mut b = x1.add(cs, y1);
        let mut t3 = a.mul(cs, &mut b);
        let mut t3 = t3.sub(cs, &mut t0);
        let mut t3 = t3.sub(cs, &mut z3);
        let mut t3 = t3.add(cs, &mut z1_mul_b3);

        // x3 = t4 * b3 * y3
        let mut y3_mul_b3 = y3.mul(cs, &mut curve_b3);
        let mut x3 = t4.mul(cs, &mut y3_mul_b3);

        // t1 = z3 - 2 * b3 * z1
        let mut z1_mul_2_b3 = z1.mul(cs, &mut curve_b6);
        let mut t1 = z3.sub(cs, &mut z1_mul_2_b3);

        // x3 = t3 * t1 - x3
        let mut new_x3 = t3.mul(cs, &mut t1);
        let new_x3 = new_x3.sub(cs, &mut x3);
        let x3 = new_x3;

        // y3 = (b3 * y3) * (3 * t0)
        let mut t0_mul_3 = t0.mul(cs, &mut three_nn);
        let mut y3 = y3_mul_b3.mul(cs, &mut t0_mul_3);

        // y3 = t1 * z3  + y3
        let mut new_y3 = t1.mul(cs, &mut z3);
        let new_y3 = new_y3.add(cs, &mut y3);
        let y3 = new_y3;

        // t0 = (3 * t0) * t3
        let mut t0 = t0_mul_3.mul(cs, &mut t3);

        // z3 = z3 * t4 + t0
        let mut z3 = z3.mul(cs, &mut t4);
        let z3 = z3.add(cs, &mut t0);

        let new = Self {
            x: x3,
            y: y3,
            z: z3,
            _marker: std::marker::PhantomData,
        };

        new
    }

    fn generic_add_sub_mixed_impl<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        other_xy: &mut (NN, NN),
        is_subtraction: bool,
    ) -> Self {
        use pairing::ff::Field;
        let params = self.x.get_params().clone();

        let curve_b = C::b_coeff();
        let mut curve_b3 = curve_b;
        curve_b3.double();
        curve_b3.add_assign(&curve_b);

        let mut curve_a = NN::allocated_constant(cs, C::a_coeff(), &params);
        let mut curve_b3 = NN::allocated_constant(cs, curve_b3, &params);

        let x1 = &mut self.x;
        let y1 = &mut self.y;
        let z1 = &mut self.z;

        let mut y2_local: NN = other_xy.1.clone();
        let x2 = &mut other_xy.0;
        if is_subtraction {
            y2_local = y2_local.negated(cs);
        }
        let y2 = &mut y2_local;

        // t0 = x1 * x2
        let mut t0 = x1.mul(cs, x2);
        // t1 = x1 * y2
        let mut t1 = y1.mul(cs, y2);
        // t3 = x2 + y2
        let mut t3 = x2.add(cs, y2);

        // t4 = x1 + y1
        let mut t4 = x1.add(cs, y1);
        // t3 = t3 * t4
        let mut t3 = t3.mul(cs, &mut t4);
        // t4 = t0 + t1
        let mut t4 = t0.add(cs, &mut t1);

        // t3 = t3 - t4
        let mut t3 = t3.sub(cs, &mut t4);
        // t4 = x2 * z1
        let mut t4 = x2.mul(cs, z1);
        // t4 = t4 + x1
        let mut t4 = t4.add(cs, x1);

        // t5 = y2 * z1
        let mut t5 = y2.mul(cs, z1);
        // t5 = t5 + y1
        let mut t5 = t5.add(cs, y1);
        // z3 = a * t4
        let mut z3 = curve_a.mul(cs, &mut t4);

        // x3 = b3 * z1
        let mut x3 = curve_b3.mul(cs, z1);
        // z3 = x3 + z3
        let mut z3 = x3.add(cs, &mut z3);
        // x3 = t1 - z3
        let mut x3 = t1.sub(cs, &mut z3);

        // z3 = t1 + z3
        let mut z3 = t1.add(cs, &mut z3);
        // y3 = x3 * z3
        let mut y3 = x3.mul(cs, &mut z3);
        // t1 = t0 + t0
        let mut t1 = t0.double(cs);

        // t1 = t1 + t0
        let mut t1 = t1.add(cs, &mut t0);
        // t2 = a * z1
        let mut t2 = curve_a.mul(cs, z1);
        // t4 = b3 * t4
        let mut t4 = curve_b3.mul(cs, &mut t4);

        // t1 = t1 + t2
        let mut t1 = t1.add(cs, &mut t2);
        // t2 = t0 - t2
        let mut t2 = t0.sub(cs, &mut t2);
        // t2 = a * t2
        let mut t2 = curve_a.mul(cs, &mut t2);

        // t4 = t4 + t2
        let mut t4 = t4.add(cs, &mut t2);
        // t0 = t1 * t4
        let mut t0 = t1.mul(cs, &mut t4);
        // y3 = y3 + t0
        let y3 = y3.add(cs, &mut t0);

        // t0 = t5 * t4
        let mut t0 = t5.mul(cs, &mut t4);
        // x3 = t3 * x3
        let mut x3 = t3.mul(cs, &mut x3);
        // x3 = x3 - t0
        let x3 = x3.sub(cs, &mut t0);

        // t0 = t3 * t1
        let mut t0 = t3.mul(cs, &mut t1);
        // z3 = t5 * z3
        let mut z3 = t5.mul(cs, &mut z3);
        // z3 = z3 + t0
        let z3 = z3.add(cs, &mut t0);

        let new = Self {
            x: x3,
            y: y3,
            z: z3,
            _marker: std::marker::PhantomData,
        };

        new
    }

    pub fn add_mixed<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        other_xy: &mut (NN, NN),
    ) -> Self {
        self.add_sub_mixed_impl(cs, other_xy, false)
    }

    pub fn sub_mixed<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        other_xy: &mut (NN, NN),
    ) -> Self {
        self.add_sub_mixed_impl(cs, other_xy, true)
    }

    pub fn convert_to_affine_or_default<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        default: C,
    ) -> ((NN, NN), Boolean<F>) {
        use pairing::ff::Field;
        let params = self.x.get_params().clone();
        let is_point_at_infty = NN::is_zero(&mut self.z, cs);

        let one_nn = NN::allocated_constant(cs, C::Base::one(), &params);
        let mut safe_z = NN::conditionally_select(cs, is_point_at_infty, &one_nn, &self.z);
        let x_for_safe_z = self.x.div_unchecked(cs, &mut safe_z);
        let y_for_safe_z = self.y.div_unchecked(cs, &mut safe_z);

        let (default_x, default_y) = default.into_xy_unchecked();
        let default_x = NN::allocated_constant(cs, default_x, &params);
        let default_y = NN::allocated_constant(cs, default_y, &params);

        let x = NN::conditionally_select(cs, is_point_at_infty, &default_x, &x_for_safe_z);
        let y = NN::conditionally_select(cs, is_point_at_infty, &default_y, &y_for_safe_z);

        ((x, y), is_point_at_infty)
    }
}

impl<F: SmallField, C: GenericCurveAffine, NN: NonNativeField<F, C::Base>> Selectable<F>
    for SWProjectivePoint<F, C, NN>
where
    C::Base: pairing::ff::PrimeField,
{
    const SUPPORTS_PARALLEL_SELECT: bool = false;

    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self {
        let x = NN::conditionally_select(cs, flag, &a.x, &b.x);
        let y = NN::conditionally_select(cs, flag, &a.y, &b.y);
        let z = NN::conditionally_select(cs, flag, &a.z, &b.z);

        Self {
            x,
            y,
            z,
            _marker: std::marker::PhantomData,
        }
    }
}
