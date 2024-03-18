use crate::{cs::traits::cs::ConstraintSystem, gadgets::curves::SmallField};

use super::*;
use super::fr2::{BN256Fq2Params, BN256Fq2ProjectiveCurvePoint};

pub struct LineFunctionEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    c0: BN256Fq2Params<F, CS>,
    c1: BN256Fq2Params<F, CS>,
    c2: BN256Fq2Params<F, CS>,
}

impl<F, CS> LineFunctionEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    #[allow(non_snake_case)]
    pub fn construct_distinct_points(
        cs: &mut CS,
        point1: BN256Fq2ProjectiveCurvePoint<F, CS>,
        point2: BN256Fq2ProjectiveCurvePoint<F, CS>,
        mut at: SWProjectivePoint<F, BN256Affine, BN256BaseNNField<F>>,
    ) -> Self {
        let [mut X2, mut Y2, _] = point1;
        let [mut X, mut Y, mut Z] = point2;

        // c0 <- (X - Z * X2) * yP
        let mut z_x2 = X2.mul(cs, &mut Z);
        let mut x_sub_z_x2 = X.sub(cs, &mut z_x2);
        let c0 = x_sub_z_x2.mul_fq(cs, &mut at.y);

        // c1 <- (Y - Z * Y2) * X2 - (X - Z * X2) * Y2
        let mut z_y2 = Z.mul(cs, &mut Y2);
        let mut y_sub_z_y2 = Y.sub(cs, &mut z_y2);
        let mut c1 = X2.mul(cs, &mut y_sub_z_y2);
        let mut y2_x_sub_z_x2 = Y2.mul(cs, &mut x_sub_z_x2);
        let c1 = c1.sub(cs, &mut y2_x_sub_z_x2);

        // c2 <- -(Y - Z * Y2) * xP
        let mut c2 = y_sub_z_y2.negated(cs);
        let c2 = c2.mul_fq(cs, &mut at.x);

        Self { c0, c1, c2 }
    }
}
