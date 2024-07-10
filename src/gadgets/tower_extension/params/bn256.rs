use pairing::bn256::{fq::Fq as BN256Fq, Fq12 as BN256Fq12, Fq2 as BN256Fq2, Fq6 as BN256Fq6};

use super::*;
use pairing::bn256::fq::{
    FROBENIUS_COEFF_FQ12_C1 as BN256_FROBENIUS_COEFF_FQ12_C1,
    FROBENIUS_COEFF_FQ6_C1 as BN256_FROBENIUS_COEFF_FQ6_C1,
    FROBENIUS_COEFF_FQ6_C2 as BN256_FROBENIUS_COEFF_FQ6_C2,
};

#[derive(Clone, Debug, Copy)]
pub struct BN256Extension2Params {}
impl Extension2Params<BN256Fq> for BN256Extension2Params {
    type Witness = BN256Fq2;

    fn convert_to_structured_witness(c0: BN256Fq, c1: BN256Fq) -> Self::Witness {
        BN256Fq2 { c0, c1 }
    }

    fn convert_from_structured_witness(wit: Self::Witness) -> (BN256Fq, BN256Fq) {
        (wit.c0, wit.c1)
    }
}

#[derive(Clone, Debug, Copy)]
pub struct BN256Extension6Params {}
impl Extension6Params<BN256Fq> for BN256Extension6Params {
    type Ex2 = BN256Extension2Params;
    type Witness = BN256Fq6;

    const FROBENIUS_COEFFS_C1: [BN256Fq2; 6] = BN256_FROBENIUS_COEFF_FQ6_C1;
    const FROBENIUS_COEFFS_C2: [BN256Fq2; 6] = BN256_FROBENIUS_COEFF_FQ6_C2;

    fn convert_to_structured_witness(c0: BN256Fq2, c1: BN256Fq2, c2: BN256Fq2) -> Self::Witness {
        Self::Witness { c0, c1, c2 }
    }

    fn convert_from_structured_witness(wit: Self::Witness) -> [BN256Fq2; 3] {
        [wit.c0, wit.c1, wit.c2]
    }
}

#[derive(Clone, Debug, Copy)]
pub struct BN256Extension12Params {}
impl Extension12Params<BN256Fq> for BN256Extension12Params {
    type Ex6 = BN256Extension6Params;
    type Witness = BN256Fq12;

    // These are Fp2 because we will multiply them with c1 `Fp6`, which has underlying `Fp2`.
    const FROBENIUS_COEFFS_C1:
        [<<Self::Ex6 as Extension6Params<BN256Fq>>::Ex2 as Extension2Params<BN256Fq>>::Witness; 12] =
        BN256_FROBENIUS_COEFF_FQ12_C1;

    fn convert_to_structured_witness(c0: BN256Fq6, c1: BN256Fq6) -> Self::Witness {
        Self::Witness { c0, c1 }
    }

    fn convert_from_structured_witness(wit: Self::Witness) -> (BN256Fq6, BN256Fq6) {
        (wit.c0, wit.c1)
    }
}

// Constants for torus extension
const TWO_INVERSE_C0: &str =
    "10944121435919637611123202872628637544348155578648911831344518947322613104292";
const W_INVERSE_C6_C0: &str =
    "21087453498479301738505683583845423561061080261299122796980902361914303298513";
const W_INVERSE_C6_C1: &str =
    "14681138511599513868579906292550611339979233093309515871315818100066920017952";

impl BN256Extension12Params {
    /// Returns the `gamma` element in `Fq6`,
    /// being simply the element `0+1*v+0*v^2` in `Fq6`.
    pub(super) fn gamma() -> BN256Fq6 {
        BN256Fq6 {
            c0: BN256Fq2::zero(),
            c1: BN256Fq2::one(),
            c2: BN256Fq2::zero(),
        }
    }

    /// Returns the `0+1*w` element in `Fq12`
    pub(super) fn w() -> BN256Fq12 {
        BN256Fq12 {
            c0: BN256Fq6::zero(),
            c1: BN256Fq6::one(),
        }
    }

    /// Decompresses a torus element from Fq6 to a field element Fq12.
    ///
    /// `g -> (g + w) / (g - w)`
    pub(super) fn decompress_torus(g: BN256Fq6) -> BN256Fq12 {
        let mut one = BN256Fq6::one();
        let mut result = BN256Fq12 {
            c0: g,
            c1: one.clone(),
        };
        one.negate();
        let denominator = BN256Fq12 { c0: g, c1: one };
        let denominator_inverse = denominator.inverse().unwrap();
        result.mul_assign(&denominator_inverse);

        result
    }

    /// Compresses a field element from Fq12 to torus Fq6.
    ///
    /// `m -> (1 + m0) / m1, m = m0 + m1*w`
    pub(super) fn compress_torus(m: BN256Fq12) -> BN256Fq6 {
        let mut result = m.c0.clone();
        result.add_assign(&BN256Fq6::one());

        let inverse_denominator = m.c1.inverse().unwrap();
        result.mul_assign(&inverse_denominator);

        result
    }
}

impl TorusExtension12Params<BN256Fq> for BN256Extension12Params {
    fn get_two_inverse_coeffs_c0() -> BN256Fq {
        BN256Fq::from_str(TWO_INVERSE_C0).unwrap()
    }

    fn get_w_inverse_coeffs_c6() -> BN256Fq2 {
        BN256Fq2 {
            c0: BN256Fq::from_str(W_INVERSE_C6_C0).unwrap(),
            c1: BN256Fq::from_str(W_INVERSE_C6_C1).unwrap(),
        }
    }

    /// Native computation of torus squaring on encoding in Fq6.
    ///
    /// `g' = 1/2 (g + \gamma / g)`
    fn torus_square(g: BN256Fq6) -> BN256Fq6 {
        let gamma = Self::gamma();

        let result = if g.is_zero() {
            BN256Fq6::zero()
        } else {
            // Decompress g
            let mut decompressed = Self::decompress_torus(g);
            // Now that we are in fq12, square
            decompressed.square();
            // Now, compress g back onto the torus so we can use it
            Self::compress_torus(decompressed)
        };

        // Constraint check
        // (2g' - g) * g = \gamma
        let mut lhs = result.clone();

        lhs.double();
        lhs.sub_assign(&g);
        lhs.mul_assign(&g);

        let rhs = gamma.clone();

        if !g.is_zero() {
            assert_eq!(lhs, rhs, "witness lhs == rhs");
        } else {
            assert_eq!(lhs, BN256Fq6::zero(), "g is zero, witness lhs == rhs");
        }

        result
    }

    /// Native computation of torus multiplication on encoding in Fq6.
    ///
    /// `(g, g') -> (g * g' + \gamma) / (g + g')`
    fn torus_mul(
        g1: <Self::Ex6 as Extension6Params<BN256Fq>>::Witness,
        g2: <Self::Ex6 as Extension6Params<BN256Fq>>::Witness,
    ) -> <Self::Ex6 as Extension6Params<BN256Fq>>::Witness {
        let gamma = Self::gamma();

        let mut g1_add_g2 = g1.clone();
        g1_add_g2.add_assign(&g2);

        let result = if g1_add_g2.is_zero() {
            BN256Fq6::zero()
        } else {
            // Decompress g1
            let decompressed_g1 = Self::decompress_torus(g1);
            // Decompress g2
            let decompressed_g2 = Self::decompress_torus(g2);
            // Multiply
            let mut decompressed_g1_times_g2 = decompressed_g1.clone();
            decompressed_g1_times_g2.mul_assign(&decompressed_g2);
            // Compress the result
            Self::compress_torus(decompressed_g1_times_g2)
        };

        // Since we have g12 = (g1*g2 + \gamma) / (g1+g2), we can
        // constraint require:
        // g12 * (g1 + g2) == g1 * g2 + \gamma

        let mut lhs = result.clone();
        lhs.mul_assign(&g1_add_g2);

        let mut g1_times_g2 = g1.clone();
        g1_times_g2.mul_assign(&g2);
        let mut rhs = g1_times_g2.clone();
        rhs.add_assign(&gamma);

        if g1_add_g2.is_zero() {
            assert_eq!(lhs, BN256Fq6::zero(), "g1 + g2 is zero, witness lhs == rhs");
        } else {
            assert_eq!(lhs, rhs, "witness lhs == rhs");
        }

        result
    }

    /// Native computation of frobenius map
    /// 
    /// `(g,i) -> f(g,i) / (f(w,i) * w^{-1})` where `f(g,i) = g^{q^{i}}`
    fn torus_frobenius_map(
            g: <Self::Ex6 as Extension6Params<BN256Fq>>::Witness,
            power: usize,
        ) -> <Self::Ex6 as Extension6Params<BN256Fq>>::Witness {
        let mut result = Self::decompress_torus(g);
        result.frobenius_map(power);
        let result = Self::compress_torus(result);

        // Now, we need to check the constraint. Namely, suppose
        // r is our result. Then,
        // w * f(g, i) = f(w, i) * r

        // lhs = f(g, i) * w
        let w = Self::w();
        let mut lhs = g.clone();
        lhs.frobenius_map(power);
        let mut lhs = BN256Fq12{
            c0: lhs,
            c1: BN256Fq6::zero(),
        };
        lhs.mul_assign(&w);

        // rhs = f(w, i) * r
        let mut rhs = Self::w();
        rhs.frobenius_map(power);
        let r = BN256Fq12{
            c0: result,
            c1: BN256Fq6::zero(),
        };
        rhs.mul_assign(&r);

        assert_eq!(lhs, rhs, "witness lhs == rhs");

        result
    }
}
