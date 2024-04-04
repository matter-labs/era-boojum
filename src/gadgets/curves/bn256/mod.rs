use super::curves::non_native_field::implementations::{
    NonNativeFieldOverU16, NonNativeFieldOverU16Params,
};
use super::sw_projective::SWProjectivePoint;

// Characteristic of the base field for bn256 curve
use pairing::bn256::fq::Fq as BN256Fq;
// Order of group of points for bn256 curve
use pairing::bn256::fr::Fr as BN256Fr;
// Affine point for bn256 curve
use pairing::bn256::G1Affine as BN256Affine;

pub mod decomp_table;
pub mod ec_mul;
pub mod naf_abs_div2_table;

// --- Base and scalar field params for BN256 curve ---
/// Params of BN256 base field
type BN256BaseNNFieldParams = NonNativeFieldOverU16Params<BN256Fq, 17>;
/// Params of BN256 scalar field
type BN256ScalarNNFieldParams = NonNativeFieldOverU16Params<BN256Fr, 17>;
/// Non-native field over u16 for BN256 base field
type BN256BaseNNField<F> = NonNativeFieldOverU16<F, BN256Fq, 17>;
/// Non-native field over u16 for BN256 scalar field
type BN256ScalarNNField<F> = NonNativeFieldOverU16<F, BN256Fr, 17>;

// P.S. we used 17 bits since 17 bits * 16 bits in u16 = 272 bits > 254 bits
// used in BN254 (so we have some extra space to deal with)

/// SW Projective point for BN256 curve over non-extended base field
type BN256SWProjectivePoint<F> = SWProjectivePoint<F, BN256Affine, BN256BaseNNField<F>>;

fn bn256_base_field_params() -> BN256BaseNNFieldParams {
    NonNativeFieldOverU16Params::create()
}

fn bn256_scalar_field_params() -> BN256ScalarNNFieldParams {
    NonNativeFieldOverU16Params::create()
}
