use pairing::bn256::{fq::Fq as BN256Fq, Fq12 as BN256Fq12, Fq2 as BN256Fq2, Fq6 as BN256Fq6};

use pairing::bn256::fq::{
    FROBENIUS_COEFF_FQ12_C1 as BN256_FROBENIUS_COEFF_FQ12_C1,
    FROBENIUS_COEFF_FQ6_C1 as BN256_FROBENIUS_COEFF_FQ6_C1,
    FROBENIUS_COEFF_FQ6_C2 as BN256_FROBENIUS_COEFF_FQ6_C2,
};
use crate::gadgets::tower_extension::fq6::Fq6;
use super::*;

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

    // Native computation of torus squaring on encoding in Fq6.
    // g' = 1/2 (g + \gamma / g)
    fn torus_square(g: BN256Fq6) -> BN256Fq6 {
        let gamma = BN256Fq6{c0: BN256Fq2::zero(), c1: BN256Fq2::one(), c2: BN256Fq2::zero()};

        let result = if g.is_zero() {
            BN256Fq6::zero()
        } else {
            // decompress g
            let mut one = BN256Fq6::one();
            let mut n = BN256Fq12{c0: g, c1: one.clone()};
            one.negate();
            let d = BN256Fq12{c0: g, c1: one};
            let d_inverse = d.inverse().unwrap();
            n.mul_assign(&d_inverse);

            // now that we are in fq12, square
            n.square();

            // now compress g back onto the torus so we can use it
            let mut result = n.c0.clone();
            result.add_assign(&BN256Fq6::one());
            let inv = n.c1.inverse().unwrap();
            result.mul_assign(&inv);
            result
        };

        /*
        // \gamma / g
        let mut result = match g.inverse() {
            Some(mut inv) => {
                inv.mul_assign(&gamma);
                inv
            }
            None => BN256Fq6::zero(),
        };

        // (g + \gamma/g)
        result.add_assign(&g);

        // (1/2)
        let mut inverse_two = BN256Fq6::one();
        inverse_two.double();
        inverse_two.inverse();

        // (1/2) * (g + \gamma/g)
        result.mul_assign(&inverse_two);
        */

        // CONSTRAINT CHECK
        // (2g' - g) * g = \gamma
        let mut lhs = result.clone();

        lhs.double();
        lhs.sub_assign(&g);
        lhs.mul_assign(&g);

        let rhs = gamma.clone();

        println!("LHS: {lhs}");
        println!("RHS: {rhs}");

        if !g.is_zero() {
            assert_eq!(lhs, rhs, "Witness lhs == rhs");
        }else{
            assert_eq!(lhs, BN256Fq6::zero(), "g is zero, witness lhs == rhs");
        }

        result
    }
}
