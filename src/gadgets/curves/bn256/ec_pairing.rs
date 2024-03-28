use std::sync::Arc;

use pairing::{bn256::G2Affine as BN256G2Affine, GenericCurveAffine};

use crate::{
    cs::traits::cs::ConstraintSystem,
    gadgets::{curves::SmallField, non_native_field::traits::CurveCompatibleNonNativeField},
};

use super::*;

// Curve parameter for the BN256 curve
const CURVE_PARAMETER: &str = "4965661367192848881";
const CURVE_PARAMETER_WNAF: [i8; 63] = [
    1, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0,
    0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0,
    0, 1,
];

/// Struct for the line function evaluation for the BN256 curve.
/// The line function is used in the Miller loop of the pairing function.
/// Implementation is primarily based on paper https://eprint.iacr.org/2019/077.pdf,
/// section 3: line functions.
pub struct LineFunctionEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    c0: BN256Fq2NNField<F>,
    c1: BN256Fq2NNField<F>,
    c2: BN256Fq2NNField<F>,
    _marker: std::marker::PhantomData<CS>,
}

impl<F, CS> LineFunctionEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    pub fn new(cs: &mut CS, params: &Arc<BN256BaseNNFieldParams>) -> Self {
        Self {
            c0: BN256Fq2NNField::zero(cs, params),
            c1: BN256Fq2NNField::zero(cs, params),
            c2: BN256Fq2NNField::zero(cs, params),
            _marker: std::marker::PhantomData::<CS>,
        }
    }

    /// This function computes the line function evaluation for the BN256 curve
    /// `l_{P,Q}(R)` when `P` and `Q` are distinct points on the twisted curve
    /// `E'(F_{p^2})` and `R` is a point on the regular curve `E(F_p)`.
    #[allow(non_snake_case)]
    pub fn at_line(
        mut self,
        cs: &mut CS,
        point1: &mut BN256SWProjectivePointTwisted<F>,
        point2: &mut BN256SWProjectivePointTwisted<F>,
        at: &mut BN256SWProjectivePoint<F>,
    ) -> Self {
        // c0 <- (X - Z * X2) * y_P
        let mut z_x2 = point1.x.mul(cs, &mut point2.z);
        let mut x_sub_z_x2 = point2.x.sub(cs, &mut z_x2);
        let c0 = x_sub_z_x2.mul_c0(cs, &mut at.y);

        // c1 <- (Y - Z * Y2) * X2 - (X - Z * X2) * Y2
        let mut z_y2 = point2.z.mul(cs, &mut point1.y);
        let mut y_sub_z_y2 = point2.y.sub(cs, &mut z_y2);
        let mut c1 = point1.x.mul(cs, &mut y_sub_z_y2);
        let mut y2_x_sub_z_x2 = point1.y.mul(cs, &mut x_sub_z_x2);
        let c1 = c1.sub(cs, &mut y2_x_sub_z_x2);

        // c2 <- -(Y - Z * Y2) * x_P
        let mut c2 = y_sub_z_y2.negated(cs);
        let c2 = c2.mul_c0(cs, &mut at.x);

        self.c0 = c0;
        self.c1 = c1;
        self.c2 = c2;
        self
    }

    /// This function computes the line function evaluation for the BN256 curve
    /// `l_{P,P}(R)` when `P` is a point on the twisted curve `E'(F_{p^2})` and
    /// `R` is a point on the regular curve `E(F_p)`.
    #[allow(non_snake_case)]
    pub fn at_tangent(
        mut self,
        cs: &mut CS,
        point: &mut BN256SWProjectivePointTwisted<F>,
        at: &mut BN256SWProjectivePoint<F>,
    ) -> Self {
        // Defining b' - the twist coefficient
        let params = point.x.c0.params.clone();
        let mut b_twist = BN256Fq2NNField::from_curve_base(cs, &BN256G2Affine::b_coeff(), &params);

        // c0 <- -2 * Y * Z * y_P
        let mut c0 = point.y.mul(cs, &mut point.z);
        let mut c0 = c0.mul_c0(cs, &mut at.y);
        let mut c0 = c0.double(cs);
        let c0 = c0.negated(cs);

        // c1 <- 3b' * Z^2 - Y^2
        let mut z2 = point.z.square(cs);
        let mut z2 = z2.mul(cs, &mut b_twist);
        let mut c1 = z2.double(cs);
        let mut c1 = c1.add(cs, &mut z2);
        let mut y2 = point.y.square(cs);
        let c1 = c1.sub(cs, &mut y2);

        // c2 <- 3 * X^2 * x_P
        let mut x2 = point.x.square(cs);
        let mut c2 = x2.mul_c0(cs, &mut at.x);
        let mut c2 = c2.double(cs);
        let c2 = c2.add(cs, &mut x2);

        self.c0 = c0;
        self.c1 = c1;
        self.c2 = c2;
        self
    }

    pub fn as_tuple(&self) -> (BN256Fq2NNField<F>, BN256Fq2NNField<F>, BN256Fq2NNField<F>) {
        (self.c0.clone(), self.c1.clone(), self.c2.clone())
    }
}

pub struct MillerLoopEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    accumulated_f: BN256Fq12NNField<F>,
    _marker: std::marker::PhantomData<CS>,
}

impl<F, CS> MillerLoopEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    #[allow(non_snake_case)]
    pub fn evaluate(
        cs: &mut CS,
        p: &mut BN256SWProjectivePoint<F>,
        q: &mut BN256SWProjectivePointTwisted<F>,
    ) -> Self {
        let params = p.x.params.clone();
        let mut f1 = BN256Fq12NNField::one(cs, &params);
        let mut r = q.clone();

        for u in CURVE_PARAMETER_WNAF {
            let tangent_fn = LineFunctionEvaluation::new(cs, &params).at_tangent(cs, &mut r, p);
            let (mut c0, mut c1, mut c4) = tangent_fn.as_tuple();
            f1 = f1.square(cs);
            f1 = f1.mul_by_c0c1c4(cs, &mut c0, &mut c1, &mut c4);
            r = r.double(cs);

            if u == 1 {
                let line_fn = LineFunctionEvaluation::new(cs, &params).at_line(cs, &mut r, q, p);
                let (mut c0, mut c1, mut c4) = line_fn.as_tuple();
                f1 = f1.mul_by_c0c1c4(cs, &mut c0, &mut c1, &mut c4);

                let qx = q.x.clone();
                let qy = q.y.clone();
                r = r.add_mixed(cs, &mut (qx, qy));
            }
            if u == -1 {
                *q = q.negated(cs);
                let line_fn = LineFunctionEvaluation::new(cs, &params).at_line(cs, &mut r, q, p);
                let (mut c0, mut c1, mut c4) = line_fn.as_tuple();
                f1 = f1.mul_by_c0c1c4(cs, &mut c0, &mut c1, &mut c4);

                let qx = q.x.clone();
                let qy = q.y.clone();
                r = r.sub_mixed(cs, &mut (qx, qy));
            }
        }

        Self {
            accumulated_f: f1,
            _marker: std::marker::PhantomData::<CS>,
        }
    }
}

pub struct FinalExpEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    resultant_f: BN256Fq12NNField<F>,
    _marker: std::marker::PhantomData<CS>,
}

impl<F, CS> FinalExpEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    pub fn evaluate(cs: &mut CS, f: &mut BN256Fq12NNField<F>) -> Self {
        let mut easy_part_f = Self::easy_part(cs, f);
        let hard_part = Self::hard_part(cs, &mut easy_part_f);
        Self {
            resultant_f: hard_part,
            _marker: std::marker::PhantomData::<CS>,
        }
    }

    pub fn easy_part(cs: &mut CS, f: &mut BN256Fq12NNField<F>) -> BN256Fq12NNField<F> {
        // f1 <- f^(p^6 - 1)
        let mut f1 = f.inverse(cs);
        let mut fp6 = f.frobenius_map(cs, 6);
        let mut f1 = f1.mul(cs, &mut fp6);
    
        // f2 <- f1^(p^2 + 1)
        let mut fp2 = f1.frobenius_map(cs, 2);
        let f2 = f1.mul(cs, &mut fp2);

        f2
    }

    #[allow(unused_variables)]
    pub fn hard_part(cs: &mut CS, f: &mut BN256Fq12NNField<F>) -> BN256Fq12NNField<F> {
        todo!();
    }
}

pub fn ec_mul<F, CS>(
    cs: &mut CS,
    p: &mut BN256SWProjectivePoint<F>,
    q: &mut BN256SWProjectivePointTwisted<F>,
) -> BN256Fq12NNField<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let mut miller_loop = MillerLoopEvaluation::evaluate(cs, p, q);
    let final_exp = FinalExpEvaluation::evaluate(cs, &mut miller_loop.accumulated_f);
    final_exp.resultant_f
}
