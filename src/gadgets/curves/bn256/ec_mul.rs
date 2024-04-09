use std::sync::Arc;

use crypto_bigint::{Zero, U1024};
use ethereum_types::U256;
use pairing::{ff::PrimeField, CurveAffine};

use crate::{
    cs::traits::cs::ConstraintSystem,
    gadgets::{
        boolean::Boolean,
        curves::{sw_projective::SWProjectivePoint, SmallField},
        non_native_field::{
            implementations::{OverflowTracker, RepresentationForm},
            traits::NonNativeField,
        },
        num::Num,
        tables::ByteSplitTable,
        traits::{selectable::Selectable, witnessable::WitnessHookable},
        u16::UInt16,
        u256::UInt256,
        u32::UInt32,
        u512::UInt512,
    },
};

use super::*;

// -- GLV constants --

// Decomposition scalars can be a little more than 2^128 in practice, so we use 33 chunks of width 4 bits
const MAX_DECOMPOSITION_VALUE: U256 = U256([u64::MAX, u64::MAX, 0x0f, 0]);

// Width 4 windowed multiplication parameters
const WINDOW_WIDTH: usize = 4;
const NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4: usize = 33;
const PRECOMPUTATION_TABLE_SIZE: usize = (1 << WINDOW_WIDTH) - 1;

/// BETA parameter such that phi(x, y) = (beta*x, y)
/// is a valid endomorphism for the curve. Note
/// that it is possible to use one since 3 divides prime order - 1.
/// Detailed explanation can be found in file `endomorphism.sage` in `sage` folder.
const BETA: &str = "2203960485148121921418603742825762020974279258880205651966";

// Decomposition constants for vectors (a1, b1) and (a2, b2),
// derived through algorithm 3.74 http://tomlr.free.fr/Math%E9matiques/Math%20Complete/Cryptography/Guide%20to%20Elliptic%20Curve%20Cryptography%20-%20D.%20Hankerson,%20A.%20Menezes,%20S.%20Vanstone.pdf
// Also see `balanced_representation.sage` file for details

/// `a1` component of a short vector `v1=(a1, b1)`.
const A1: &str = "0x89d3256894d213e3";
/// `-b1` component of a short vector `v1=(a1, b1)`.
/// Since `b1` is negative, we use `-b1` instead of `b1`.
const B1: &str = "0x6f4d8248eeb859fc8211bbeb7d4f1128";
/// `a2` component of a short vector `v2=(a2, b2)`.
const A2: &str = "0x6f4d8248eeb859fd0be4e1541221250b";
/// `b2` component of a short vector `v2=(a2, b2)`.
const B2: &str = "0x89d3256894d213e3";

/// Precomputed value of `-b1/n << 256`
const G1: &str = "0x24ccef014a773d2cf7a7bd9d4391eb18d";
/// Precomputed value of `b2/n << 256`
const G2: &str = "0x2d91d232ec7e0b3d7";

/// Lambda parameter
const LAMBDA: &str = "0xb3c4d79d41a917585bfc41088d8daaa78b17ea66b99c90dd";

// -- WNAF parameters --

/// The scalar multiplication window size.
const GLV_WINDOW_SIZE: usize = 2;
/// The GLV table length.
const L: usize = 1 << (GLV_WINDOW_SIZE - 1);

/// Converts the `UInt256<F>` element to a non-native field element over `u16`.
fn convert_uint256_to_field_element<F, CS, P, const N: usize>(
    cs: &mut CS,
    value: &UInt256<F>,
    params: &Arc<NonNativeFieldOverU16Params<P, N>>,
) -> NonNativeFieldOverU16<F, P, N>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
    P: PrimeField,
{
    // We still have to decompose it into u16 words
    let zero_var = Num::allocated_constant(cs, F::ZERO).get_variable();
    let mut limbs = [zero_var; N];
    assert!(N >= 16);

    for (dst, src) in limbs.array_chunks_mut::<2>().zip(value.inner.iter()) {
        let [b0, b1, b2, b3] = src.to_le_bytes(cs);
        let low = UInt16::from_le_bytes(cs, [b0, b1]);
        let high = UInt16::from_le_bytes(cs, [b2, b3]);

        *dst = [low.get_variable(), high.get_variable()];
    }

    let mut max_value = U1024::from_word(1u64);
    max_value = max_value.shl_vartime(256);
    max_value = max_value.saturating_sub(&U1024::from_word(1u64));

    let (overflows, rem) = max_value.div_rem(&params.modulus_u1024);
    let mut max_moduluses = overflows.as_words()[0] as u32;
    if rem.is_zero().unwrap_u8() != 1 {
        max_moduluses += 1;
    }

    let element = NonNativeFieldOverU16 {
        limbs,
        non_zero_limbs: 16,
        tracker: OverflowTracker { max_moduluses },
        form: RepresentationForm::Normalized,
        params: params.clone(),
        _marker: std::marker::PhantomData,
    };

    element
}

/// Converts the non-native field eelement over `u16` to a `UInt256`.
/// Note that caller must ensure that the field element is normalized,
/// otherwise this will fail.
fn convert_field_element_to_uint256<F, CS, P, const N: usize>(
    cs: &mut CS,
    mut value: NonNativeFieldOverU16<F, P, N>,
) -> UInt256<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
    P: PrimeField,
{
    assert_eq!(value.form, RepresentationForm::Normalized);
    assert_eq!(value.tracker.max_moduluses, 1);

    let mut limbs = [UInt32::<F>::zero(cs); 8];
    let two_pow_16 = Num::allocated_constant(cs, F::from_u64_unchecked(2u32.pow(16) as u64));
    for (dst, src) in limbs.iter_mut().zip(value.limbs.array_chunks_mut::<2>()) {
        let low = Num::from_variable(src[0]);
        let high = Num::from_variable(src[1]);
        *dst = unsafe {
            UInt32::from_variable_unchecked(
                Num::fma(cs, &high, &two_pow_16, &F::ONE, &low, &F::ONE).get_variable(),
            )
        };
    }

    UInt256 { inner: limbs }
}

#[derive(Debug, Clone)]
pub struct ScalarDecomposition<F: SmallField> {
    pub k1: BN256ScalarNNField<F>,
    pub k2: BN256ScalarNNField<F>,
    pub k1_was_negated: Boolean<F>,
    pub k2_was_negated: Boolean<F>,
}

impl<F> ScalarDecomposition<F>
where
    F: SmallField,
{
    fn u256_from_hex_str<CS>(cs: &mut CS, s: &str) -> UInt256<F>
    where
        CS: ConstraintSystem<F>,
    {
        let v = U256::from_str_radix(s, 16).unwrap();
        UInt256::allocated_constant(cs, v)
    }

    fn bigint_from_hex_str<CS>(cs: &mut CS, s: &str) -> UInt512<F>
    where
        CS: ConstraintSystem<F>,
    {
        let v = U256::from_str_radix(s, 16).unwrap();
        UInt512::allocated_constant(cs, (v, U256::zero()))
    }

    pub fn from<CS>(
        cs: &mut CS,
        scalar: &mut BN256ScalarNNField<F>,
        scalar_field_params: &Arc<BN256ScalarNNFieldParams>,
    ) -> Self
    where
        F: SmallField,
        CS: ConstraintSystem<F>,
    {
        // Defining constants under the constraint system
        let pow_2_128 = UInt512::allocated_constant(cs, (U256([0, 0, 1, 0]), U256::zero()));
        let lambda = Self::u256_from_hex_str(cs, LAMBDA);
        let b1 = Self::u256_from_hex_str(cs, B1);
        let b2 = Self::u256_from_hex_str(cs, B2);
        let g1 = Self::u256_from_hex_str(cs, G1);
        let g2 = Self::u256_from_hex_str(cs, G2);

        let k = convert_field_element_to_uint256(cs, scalar.clone());

        // We take 8 non-zero limbs for the scalar (since it could be of any size), and 4 for G2
        // (since it fits in 128 bits).
        let g2_times_k = k.widening_mul(cs, &g2, 8, 4);
        let c1 = g2_times_k.to_high();

        // We take 8 non-zero limbs for the scalar (since it could be of any size), and 5 for G2
        // (since it fits in 130 bits).
        let g1_times_k = k.widening_mul(cs, &g1, 8, 5);
        let c2 = g1_times_k.to_high();
        
        // Converting all constants to field elements
        let mut b1 = convert_uint256_to_field_element(cs, &b1, scalar_field_params);
        let mut b2 = convert_uint256_to_field_element(cs, &b2, scalar_field_params);
        let mut c1 = convert_uint256_to_field_element(cs, &c1, scalar_field_params);
        let mut c2 = convert_uint256_to_field_element(cs, &c2, scalar_field_params);
        let mut lambda = convert_uint256_to_field_element(cs, &lambda, scalar_field_params);

        // q1 <- c1 * b1
        // q2 <- c2 * b2
        let mut q1 = c1.mul(cs, &mut b1);
        let mut q1 = q1.negated(cs);
        let mut q2 = c2.mul(cs, &mut b2);
        let mut q2 = q2.negated(cs);

        // k2 <- q2 - q1
        let mut k2 = q2.sub(cs, &mut q1);
        k2.normalize(cs);

        // k2_lambda <- k2 * lambda, k1 <- k - k2_lambda
        let mut k2_times_lambda = k2.mul(cs, &mut lambda);
        let mut k1 = scalar.sub(cs, &mut k2_times_lambda);
        k1.normalize(cs);

        let k1_u256 = convert_field_element_to_uint256(cs, k1.clone());
        let k2_u256 = convert_field_element_to_uint256(cs, k2.clone());
        
        dbg!(k1_u256.witness_hook(cs)());
        dbg!(k2_u256.witness_hook(cs)());

        let low_pow_2_128 = pow_2_128.to_low();
        
        // Selecting between k1 and -k1 in Fq
        let (_, k1_out_of_range) = k1_u256.overflowing_sub(cs, &low_pow_2_128);
        let k1_negated = k1.negated(cs);
        let k1 = <BN256ScalarNNField<F> as NonNativeField<F, BN256Fr>>::conditionally_select(
            cs,
            k1_out_of_range,
            &k1,
            &k1_negated,
        );

        // Selecting between k2 and -k2 in Fq
        let (_, k2_out_of_range) = k2_u256.overflowing_sub(cs, &low_pow_2_128);
        let k2_negated = k2.negated(cs);
        let k2 = <BN256ScalarNNField<F> as NonNativeField<F, BN256Fr>>::conditionally_select(
            cs,
            k2_out_of_range,
            &k2,
            &k2_negated,
        );

        Self {
            k1,
            k2,
            k1_was_negated: k1_out_of_range.negated(cs),
            k2_was_negated: k2_out_of_range.negated(cs),
        }
    }
}

pub fn width_4_windowed_multiplication<F, CS>(
    cs: &mut CS,
    mut point: BN256SWProjectivePoint<F>,
    mut scalar: BN256ScalarNNField<F>,
    base_field_params: &Arc<BN256BaseNNFieldParams>,
    scalar_field_params: &Arc<BN256ScalarNNFieldParams>,
) -> BN256SWProjectivePoint<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    // Scalar decomposition
    scalar.enforce_reduced(cs);
    let scalar_decomposition = ScalarDecomposition::from(cs, &mut scalar, scalar_field_params);

    dbg!("Scalar decomposition");
    dbg!(scalar_decomposition.k1.witness_hook(cs)());
    dbg!(scalar_decomposition.k2.witness_hook(cs)());
    dbg!(scalar_decomposition.k1_was_negated.witness_hook(cs)());
    dbg!(scalar_decomposition.k2_was_negated.witness_hook(cs)());

    // create precomputed table of size 1<<4 - 1
    // there is no 0 * P in the table, we will handle it below
    let mut table = Vec::with_capacity(PRECOMPUTATION_TABLE_SIZE);
    let mut tmp = point.clone();
    let (mut p_affine, _) = point.convert_to_affine_or_default(cs, BN256Affine::one());
    table.push(p_affine.clone());
    for _ in 1..PRECOMPUTATION_TABLE_SIZE {
        // 2P, 3P, ...
        tmp = tmp.add_mixed(cs, &mut p_affine);
        let (affine, _) = tmp.convert_to_affine_or_default(cs, BN256Affine::one());
        table.push(affine);
    }
    assert_eq!(table.len(), PRECOMPUTATION_TABLE_SIZE);
    
    let beta = BN256Fq::from_str(BETA).unwrap();
    let mut beta = BN256BaseNNField::allocated_constant(cs, beta, base_field_params);

    let mut endomorphisms_table = table.clone();
    for (x, _) in endomorphisms_table.iter_mut() {
        *x = x.mul(cs, &mut beta);
    }

    // we also know that we will multiply k1 by points, and k2 by their endomorphisms, and if they were
    // negated above to fit into range, we negate bases here
    for (_, y) in table.iter_mut() {
        let negated = y.negated(cs);
        *y = Selectable::conditionally_select(
            cs,
            scalar_decomposition.k1_was_negated,
            &negated,
            &*y,
        );
    }

    for (_, y) in endomorphisms_table.iter_mut() {
        let negated = y.negated(cs);
        *y = Selectable::conditionally_select(
            cs,
            scalar_decomposition.k2_was_negated,
            &negated,
            &*y,
        );
    }

    // now decompose every scalar we are interested in
    dbg!(scalar_decomposition.k1.witness_hook(cs)());
    dbg!(scalar_decomposition.k2.witness_hook(cs)());

    let k1_msb_decomposition = to_width_4_window_form(cs, scalar_decomposition.k1);
    let k2_msb_decomposition = to_width_4_window_form(cs, scalar_decomposition.k2);

    let mut comparison_constants = Vec::with_capacity(PRECOMPUTATION_TABLE_SIZE);
    for i in 1..=PRECOMPUTATION_TABLE_SIZE {
        let constant = Num::allocated_constant(cs, F::from_u64_unchecked(i as u64));
        comparison_constants.push(constant);
    }

    // now we do amortized double and add
    let mut acc = SWProjectivePoint::zero(cs, base_field_params);
    assert_eq!(
        k1_msb_decomposition.len(),
        NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4
    );
    assert_eq!(
        k2_msb_decomposition.len(),
        NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4
    );

    for (idx, (k1_window_idx, k2_window_idx)) in k1_msb_decomposition
        .into_iter()
        .zip(k2_msb_decomposition.into_iter())
        .enumerate()
    {
        let ignore_k1_part = k1_window_idx.is_zero(cs);
        let ignore_k2_part = k2_window_idx.is_zero(cs);

        let (mut selected_k1_part_x, mut selected_k1_part_y) = table[0].clone();
        let (mut selected_k2_part_x, mut selected_k2_part_y) = endomorphisms_table[0].clone();
        for i in 1..PRECOMPUTATION_TABLE_SIZE {
            let should_select_k1 = Num::equals(cs, &comparison_constants[i], &k1_window_idx);
            let should_select_k2 = Num::equals(cs, &comparison_constants[i], &k2_window_idx);
            selected_k1_part_x = Selectable::conditionally_select(
                cs,
                should_select_k1,
                &table[i].0,
                &selected_k1_part_x,
            );
            selected_k1_part_y = Selectable::conditionally_select(
                cs,
                should_select_k1,
                &table[i].1,
                &selected_k1_part_y,
            );
            selected_k2_part_x = Selectable::conditionally_select(
                cs,
                should_select_k2,
                &endomorphisms_table[i].0,
                &selected_k2_part_x,
            );
            selected_k2_part_y = Selectable::conditionally_select(
                cs,
                should_select_k2,
                &endomorphisms_table[i].1,
                &selected_k2_part_y,
            );
        }

        let tmp_acc = acc.add_mixed(cs, &mut (selected_k1_part_x, selected_k1_part_y));
        acc = Selectable::conditionally_select(cs, ignore_k1_part, &acc, &tmp_acc);
        let tmp_acc = acc.add_mixed(cs, &mut (selected_k2_part_x, selected_k2_part_y));
        acc = Selectable::conditionally_select(cs, ignore_k2_part, &acc, &tmp_acc);

        if idx != NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4 - 1 {
            for _ in 0..WINDOW_WIDTH {
                acc = acc.double(cs);
            }
        }
    }

    acc
}

fn to_width_4_window_form<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut limited_width_scalar: BN256ScalarNNField<F>,
) -> Vec<Num<F>> {
    limited_width_scalar.enforce_reduced(cs);
    // we know that width is 128 bits, so just do BE decomposition and put into resulting array
    let zero_num = Num::zero(cs);
    for word in limited_width_scalar.limbs[9..].iter() {
        let word = Num::from_variable(*word);
        Num::enforce_equal(cs, &word, &zero_num);
    }

    let byte_split_id = cs
        .get_table_id_for_marker::<ByteSplitTable<4>>()
        .expect("table should exist");
    let mut result = Vec::with_capacity(32);
    // special case
    {
        let highest_word = limited_width_scalar.limbs[8];
        let word = unsafe { UInt16::from_variable_unchecked(highest_word) };
        let [high, low] = word.to_be_bytes(cs);
        Num::enforce_equal(cs, &high.into_num(), &zero_num);
        let [l, h] = cs.perform_lookup::<1, 2>(byte_split_id, &[low.get_variable()]);
        Num::enforce_equal(cs, &Num::from_variable(h), &zero_num);
        let l = Num::from_variable(l);
        result.push(l);
    }

    for word in limited_width_scalar.limbs[..8].iter().rev() {
        let word = unsafe { UInt16::from_variable_unchecked(*word) };
        let [high, low] = word.to_be_bytes(cs);
        for t in [high, low].into_iter() {
            let [l, h] = cs.perform_lookup::<1, 2>(byte_split_id, &[t.get_variable()]);
            let h = Num::from_variable(h);
            let l = Num::from_variable(l);
            result.push(h);
            result.push(l);
        }
    }
    assert_eq!(result.len(), NUM_MULTIPLICATION_STEPS_FOR_WIDTH_4);

    result
}
