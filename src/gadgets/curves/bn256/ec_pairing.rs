use pairing::ff::PrimeField;

use crate::{cs::traits::cs::ConstraintSystem, gadgets::curves::SmallField};

use super::fr2::{BN256Fq2Params, BN256Fq2ProjectiveCurvePoint};
use super::*;

const B_TWIST_COEFF_REAL: &str =
    "19485874751759354771024239261021720505790618469301721065564631296452457478373";
const B_TWIST_COEFF_IMAGINARY: &str =
    "266929791119991161246907387137283842545076965332900288569378510910307636690";

pub struct LineFunctionEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    c0: BN256Fq2Params<F, CS>,
    c1: BN256Fq2Params<F, CS>,
    c2: BN256Fq2Params<F, CS>,
}

/// This is an implementation of the line function evaluation for the BN256 curve.
/// The line function is used in the Miller loop of the pairing function.
/// Implementation is primarily based on paper https://eprint.iacr.org/2019/077.pdf,
/// section 3: line functions.
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

        // c0 <- (X - Z * X2) * y_P
        let mut z_x2 = X2.mul(cs, &mut Z);
        let mut x_sub_z_x2 = X.sub(cs, &mut z_x2);
        let c0 = x_sub_z_x2.mul_fq(cs, &mut at.y);

        // c1 <- (Y - Z * Y2) * X2 - (X - Z * X2) * Y2
        let mut z_y2 = Z.mul(cs, &mut Y2);
        let mut y_sub_z_y2 = Y.sub(cs, &mut z_y2);
        let mut c1 = X2.mul(cs, &mut y_sub_z_y2);
        let mut y2_x_sub_z_x2 = Y2.mul(cs, &mut x_sub_z_x2);
        let c1 = c1.sub(cs, &mut y2_x_sub_z_x2);

        // c2 <- -(Y - Z * Y2) * x_P
        let mut c2 = y_sub_z_y2.negated(cs);
        let c2 = c2.mul_fq(cs, &mut at.x);

        Self { c0, c1, c2 }
    }

    #[allow(non_snake_case)]
    pub fn construct_tangent(
        cs: &mut CS,
        point: BN256Fq2ProjectiveCurvePoint<F, CS>,
        mut at: SWProjectivePoint<F, BN256Affine, BN256BaseNNField<F>>,
    ) -> Self {
        let [mut X, mut Y, mut Z] = point;

        // Defining b' - the twist coefficient
        let params = X.c0.params.clone();
        let b_twist_real = BN256Fq::from_str(B_TWIST_COEFF_REAL).unwrap();
        let b_twist_real = BN256BaseNNField::allocated_constant(cs, b_twist_real, &params);

        let b_twist_imaginary = BN256Fq::from_str(B_TWIST_COEFF_IMAGINARY).unwrap();
        let b_twist_imaginary =
            BN256BaseNNField::allocated_constant(cs, b_twist_imaginary, &params);

        let mut b_twist = BN256Fq2Params::new(b_twist_real, b_twist_imaginary);

        // c0 <- -2 * Y * Z * y_P
        let mut c0 = Y.mul(cs, &mut Z);
        let mut c0 = c0.mul_fq(cs, &mut at.y);
        let mut c0 = c0.double(cs);
        let c0 = c0.negated(cs);

        // c1 <- 3b' * Z^2 - Y^2
        let mut z2 = Z.square(cs);
        let mut z2 = z2.mul(cs, &mut b_twist);
        let mut c1 = z2.double(cs);
        let mut c1 = c1.add(cs, &mut z2);
        let mut y2 = Y.square(cs);
        let c1 = c1.sub(cs, &mut y2);

        // c2 <- 3 * X^2 * x_P
        let mut x2 = X.square(cs);
        let mut c2 = x2.mul_fq(cs, &mut at.x);
        let mut c2 = c2.double(cs);
        let c2 = c2.add(cs, &mut x2);

        Self { c0, c1, c2 }
    }
}
