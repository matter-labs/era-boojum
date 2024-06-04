use pairing::bn256::{fq::Fq as BN256Fq, Fq12 as BN256Fq12, Fq2 as BN256Fq2, Fq6 as BN256Fq6};

use pairing::bn256::fq::{
    FROBENIUS_COEFF_FQ12_C1 as BN256_FROBENIUS_COEFF_FQ12_C1,
    FROBENIUS_COEFF_FQ6_C1 as BN256_FROBENIUS_COEFF_FQ6_C1,
    FROBENIUS_COEFF_FQ6_C2 as BN256_FROBENIUS_COEFF_FQ6_C2,
};

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
    fn get_two_inverse_coeffs_c0() -> BN256Fq2 {
        BN256Fq2 {
            c0: BN256Fq::from_str(TWO_INVERSE_C0).unwrap(),
            c1: BN256Fq::zero(),
        }
    }

    fn get_w_inverse_coeffs_c6() -> BN256Fq2 {
        BN256Fq2 {
            c0: BN256Fq::from_str(W_INVERSE_C6_C0).unwrap(),
            c1: BN256Fq::from_str(W_INVERSE_C6_C1).unwrap(),
        }
    }
}
