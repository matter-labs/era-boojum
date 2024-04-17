use std::sync::Arc;

use pairing::{bn256::G2Affine as BN256G2Affine, GenericCurveAffine};

use crate::{
    cs::traits::cs::ConstraintSystem,
    gadgets::{
        boolean::Boolean, curves::SmallField,
        non_native_field::traits::CurveCompatibleNonNativeField,
    },
};

use super::*;

// Curve parameter for the BN256 curve
const CURVE_PARAMETER: u64 = 4965661367192848881;
const CURVE_DIV_2_PARAMETER: &str = "2482830683596424440";
const CURVE_PARAMETER_WNAF: [i8; 65] = [
    0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0,
    1, 1, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0,
    0, 1, 0, 1, 1,
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
    c3: BN256Fq2NNField<F>,
    c4: BN256Fq2NNField<F>,
    _marker: std::marker::PhantomData<CS>,
}

impl<F, CS> LineFunctionEvaluation<F, CS>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    /// Creates a new instance of the line function evaluation for the BN256 curve.
    pub fn new(c0: BN256Fq2NNField<F>, c3: BN256Fq2NNField<F>, c4: BN256Fq2NNField<F>) -> Self {
        Self {
            c0,
            c3,
            c4,
            _marker: std::marker::PhantomData::<CS>,
        }
    }

    /// Creates a zero instance of the line function evaluation for the BN256 curve.
    pub fn zero(cs: &mut CS, params: &Arc<BN256BaseNNFieldParams>) -> Self {
        Self {
            c0: BN256Fq2NNField::zero(cs, params),
            c3: BN256Fq2NNField::zero(cs, params),
            c4: BN256Fq2NNField::zero(cs, params),
            _marker: std::marker::PhantomData::<CS>,
        }
    }

    /// This function computes the line function evaluation for the BN256 curve
    /// `L_{P,Q}(R)` when `P` and `Q` are distinct points on the twisted curve
    /// `E'(F_{p^2})` and `R` is a point on the regular curve `E(F_p)`. For details,
    /// see _Section 3_ in https://eprint.iacr.org/2019/077.pdf.
    #[allow(non_snake_case)]
    pub fn at_line(
        &mut self,
        cs: &mut CS,
        point1: &mut BN256SWProjectivePointTwisted<F>,
        point2: &mut BN256SWProjectivePointTwisted<F>,
        at: &mut BN256SWProjectivePoint<F>,
    ) -> Self {
        // c0 <- (X - Z * X2) * y_P
        let mut z_x2 = point1.x.mul(cs, &mut point2.z);
        let mut x_sub_z_x2 = point2.x.sub(cs, &mut z_x2);
        let c0 = x_sub_z_x2.mul_c0(cs, &mut at.y);

        // c4 <- (Y - Z * Y2) * X2 - (X - Z * X2) * Y2
        let mut z_y2 = point2.z.mul(cs, &mut point1.y);
        let mut y_sub_z_y2 = point2.y.sub(cs, &mut z_y2);
        let mut c4 = point1.x.mul(cs, &mut y_sub_z_y2);
        let mut y2_x_sub_z_x2 = point1.y.mul(cs, &mut x_sub_z_x2);
        let c4 = c4.sub(cs, &mut y2_x_sub_z_x2);

        // c3 <- -(Y - Z * Y2) * x_P
        let mut c3 = y_sub_z_y2.negated(cs);
        let c3 = c3.mul_c0(cs, &mut at.x);

        Self::new(c0, c3, c4)
    }

    /// This function computes the line function evaluation for the BN256 curve
    /// `L_{P,P}(R)` when `P` is a point on the twisted curve `E'(F_{p^2})` and
    /// `R` is a point on the regular curve `E(F_p)`. For details,
    /// see _Section 3_ in https://eprint.iacr.org/2019/077.pdf.
    #[allow(non_snake_case)]
    pub fn at_tangent(
        &mut self,
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

        // c4 <- 3b' * Z^2 - Y^2
        let mut z2 = point.z.square(cs);
        let mut z2 = z2.mul(cs, &mut b_twist);
        let mut c4 = z2.double(cs);
        let mut c4 = c4.add(cs, &mut z2);
        let mut y2 = point.y.square(cs);
        let c4 = c4.sub(cs, &mut y2);

        // c3 <- 3 * X^2 * x_P
        let mut x2 = point.x.square(cs);
        let mut c3 = x2.mul_c0(cs, &mut at.x);
        let mut c3 = c3.double(cs);
        let c3 = c3.add(cs, &mut x2);

        Self::new(c0, c3, c4)
    }

    pub fn as_tuple(&self) -> (BN256Fq2NNField<F>, BN256Fq2NNField<F>, BN256Fq2NNField<F>) {
        (self.c0.clone(), self.c3.clone(), self.c4.clone())
    }
}

/// Struct for the miller loop evaluation for the BN256 curve.
/// Here, the Miller loop returns the accumulated f value after the loop
/// without the final exponentiation.
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
    /// This function computes the Miller loop for the BN256 curve, using
    /// algorithm from _Section 2_ from https://eprint.iacr.org/2016/130.pdf.
    pub fn evaluate(
        cs: &mut CS,
        p: &mut BN256SWProjectivePoint<F>,
        q: &mut BN256SWProjectivePointTwisted<F>,
    ) -> Self {
        // Verifying that q is normalized
        let q_is_normalized = q.is_normalized(cs);
        let boolean_true = Boolean::allocated_constant(cs, true);
        Boolean::enforce_equal(cs, &q_is_normalized, &boolean_true);

        // Setting evaluation parameters
        let params = p.x.params.clone();
        let mut evaluation = LineFunctionEvaluation::zero(cs, &params);

        let mut f1 = BN256Fq12NNField::one(cs, &params);
        let mut r = q.clone();

        // Reverse the WNAF representation of the curve parameter
        let mut wnaf_reversed = CURVE_PARAMETER_WNAF.clone();
        wnaf_reversed.reverse();

        for u in wnaf_reversed {
            // Doubling step: f1 <- f1^2 * L_{R,R}(P), R <- 2R
            let mut tan_fn = evaluation.at_tangent(cs, &mut r, p);
            f1 = f1.square(cs);
            f1 = Self::mul_f12_by_line_fn(cs, &mut f1, &mut tan_fn);
            r = r.double(cs);

            // Skip if u is zero
            if u == 0 {
                continue;
            }

            // Addition step: f1 <- f1 * L_{R,Q}(P), R <- R + Q.
            // If u is negative, negate Q.
            let mut q = q.clone();
            if u == -1 {
                q = q.negated(cs);
            }

            let mut line_fn = evaluation.at_line(cs, &mut r, &mut q, p);
            f1 = Self::mul_f12_by_line_fn(cs, &mut f1, &mut line_fn);

            let qx = q.x.clone();
            let qy = q.y.clone();
            r = r.add_mixed(cs, &mut (qx, qy));
        }

        Self {
            accumulated_f: f1,
            _marker: std::marker::PhantomData::<CS>,
        }
    }

    fn mul_f12_by_line_fn(
        cs: &mut CS,
        f: &mut BN256Fq12NNField<F>,
        line_fn: &mut LineFunctionEvaluation<F, CS>,
    ) -> BN256Fq12NNField<F> {
        f.mul_by_c0c3c4(cs, &mut line_fn.c0, &mut line_fn.c3, &mut line_fn.c4)
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
    /// This function computes the final exponentiation for the BN256 curve.
    /// The final exponentiation is based on _Algorithm 31_ from
    /// https://eprint.iacr.org/2010/354.pdf.
    pub fn evaluate(cs: &mut CS, r: &mut BN256Fq12NNField<F>) -> Self {
        // TODO: Avoid too many normalizations and cloning
        // Preparing a curve parameter
        let x = CURVE_PARAMETER;

        // 1. f1 <- r; 2. f1 <- f1^*; 3. f2 <- r^{-1}
        let mut f1 = r.clone();
        let f1 = f1.conjugate(cs);
        let mut f2 = r.inverse(cs);
        f2.normalize(cs);
        
        // 4. r <- f1; 5. r <- r*f2; 6. f2 <- r
        let mut r = f1.clone();
        r = r.mul(cs, &mut f2);
        r.normalize(cs);
        f2 = r.clone();

        // 7. r <- r^(q^2); 8. r <- r*f2;
        r = r.frobenius_map(cs, 2);
        r.normalize(cs);
        r = r.mul(cs, &mut f2);
        r.normalize(cs);

        // 9. fp <- r^q; 10. fp2 <- r^(q^2); 11. fp3 <- fp2^q;
        let mut fp = r.clone();
        fp = fp.frobenius_map(cs, 1);
        fp.normalize(cs);
        let mut fp2 = r.clone();
        fp2 = fp2.frobenius_map(cs, 2);
        fp2.normalize(cs);
        let mut fp3 = fp2.clone();
        fp3 = fp3.frobenius_map(cs, 1);
        fp3.normalize(cs);
        
        // 12. fu <- r^x; 13. fu2 <- fu^x; 14. fu3 <- fu2^x;
        let mut fu = r.clone();
        fu = fu.pow_u32(cs, &[x]);
        fu.normalize(cs);
        let mut fu2 = fu.clone();
        fu2 = fu2.pow_u32(cs, &[x]);
        fu2.normalize(cs);
        let mut fu3 = fu2.clone();
        fu3 = fu3.pow_u32(cs, &[x]);
        fu3.normalize(cs);
        
        // 15. y3 <- fu; 16. y3 <- y3^q; 17. fu2p <- fu2; 18. fu2p <- fu2p^q;
        let mut y3 = fu.clone();
        y3 = y3.frobenius_map(cs, 1);
        y3.normalize(cs);
        let mut fu2p = fu2.clone();
        fu2p = fu2p.frobenius_map(cs, 1);
        fu2p.normalize(cs);
        // fu3p = copy(fu3)
        
        // 19. fu3p <- fu3; 20. fu3p <- fu3p^q; 21. y2 <- fu2; y2 <- y2^(q^2);
        let mut fu3p = fu3.clone();
        fu3p = fu3p.frobenius_map(cs, 1);
        fu3p.normalize(cs);
        let mut y2 = fu2.clone();
        y2 = y2.frobenius_map(cs, 2);
        y2.normalize(cs);

        // 22. y0 <- fp; 23. y0 <- y0*fp2; 24. y0 <- y0*fp3;
        let mut y0 = fp.clone();
        y0 = y0.mul(cs, &mut fp2);
        y0.normalize(cs);
        y0 = y0.mul(cs, &mut fp3);
        y0.normalize(cs);

        // 25. y1 <- r; 26. y1 <- y1^*; 27. y5 <- fu2; 28. y5 <- y5^*; 
        let mut y1 = r.clone();
        y1 = y1.conjugate(cs);
        let mut y5 = fu2.clone();
        y5 = y5.conjugate(cs);
        
        // 29. y3 <- y3*y5; 30. y4 <- fu; 31. y4 <- y4*fu2p; 32. y4 <- y4^*;
        y3 = y3.conjugate(cs);
        let mut y4 = fu.clone();
        y4 = y4.mul(cs, &mut fu2p);
        y4.normalize(cs);
        y4 = y4.conjugate(cs);
        
        // 33. y6 <- fu3; 34. y6 <- y6*fu3p; 35. y6 <- y6^*; 36. y6 <- y6^2;
        let mut y6 = fu3.clone();
        y6 = y6.mul(cs, &mut fu3p);
        y6.normalize(cs);
        y6 = y6.conjugate(cs);
        y6 = y6.square(cs);
        y6.normalize(cs);
        
        // 37. y6 <- y6*y4; 38. y6 <- y6*y5; 39. t1 <- y3; 40. t1 <- t1*y5
        y6 = y6.mul(cs, &mut y4);
        y6.normalize(cs);
        y6 = y6.mul(cs, &mut y5);
        y6.normalize(cs);
        let mut t1 = y3.clone();
        t1 = t1.mul(cs, &mut y5);
        t1.normalize(cs);
        
        // 41. t1 <- t1 * y6; 42. y6 <- y6*y2; 43. t1 <- t1^2; 44. t1 <- t1*y6
        t1 = t1.mul(cs, &mut y6);
        t1.normalize(cs);
        y6 = y6.mul(cs, &mut y2);
        y6.normalize(cs);
        t1 = t1.square(cs);
        t1.normalize(cs);
        t1 = t1.mul(cs, &mut y6);
        t1.normalize(cs);
        
        // 45. t1 <- t1^2; 46. t0 <- t1; 47. t0 <- t0*y1; 48. t1 <- t1*y0
        t1 = t1.square(cs);
        t1.normalize(cs);
        let mut t0 = t1.clone();
        t0 = t0.mul(cs, &mut y1);
        t0.normalize(cs);
        t1 = t1.mul(cs, &mut y0);
        t1.normalize(cs);

        // 49. t0 <- t0^2; 50. t0 <- t0*t1; Return t0
        t0 = t0.square(cs);
        t0.normalize(cs);
        t0 = t0.mul(cs, &mut t1);
        t0.normalize(cs);

        Self {
            resultant_f: t0,
            _marker: std::marker::PhantomData::<CS>,
        }
    }

    pub fn get(&self) -> BN256Fq12NNField<F> {
        self.resultant_f.clone()
    }
}

/// This function computes the pairing function for the BN256 curve.
pub fn ec_pairing<F, CS>(
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
