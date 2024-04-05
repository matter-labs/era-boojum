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
        traits::selectable::Selectable,
        u16::UInt16,
        u256::UInt256,
        u32::UInt32,
        u512::UInt512,
    },
};

use super::*;

/// The value of 2**128 in string format
const TWO_POW_128: &str = "340282366920938463463374607431768211456";

// (BN254 elliptic curve primer order - 1) / 2
// (0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001 - 0x1) / 0x2
const MODULUS_MINUS_ONE_DIV_TWO: &str =
    "183227397098d014dc2822db40c0ac2e9419f4243cdcb848a1f0fac9f8000000";

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
const A1: &str = "0x89D3256894D213E3";
/// `-b1` component of a short vector `v1=(a1, b1)`.
/// Since `b1` is negative, we use `-b1` instead of `b1`.
const B1_NEGATIVE: &str = "0x6f4d8248eeb859fc8211bbeb7d4f1128";
/// `a2` component of a short vector `v2=(a2, b2)`.
const A2: &str = "0x6F4D8248EEB859FD0BE4E1541221250B";
/// `b2` component of a short vector `v2=(a2, b2)`.
const B2: &str = "0x89D3256894D213E3";

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

pub fn width_4_windowed_multiplication<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut point: BN256SWProjectivePoint<F>,
    mut scalar: BN256ScalarNNField<F>,
    base_field_params: &Arc<BN256BaseNNFieldParams>,
    scalar_field_params: &Arc<BN256ScalarNNFieldParams>,
) -> BN256SWProjectivePoint<F> {
    scalar.enforce_reduced(cs);

    let beta = BN256Fq::from_str(BETA).unwrap();
    let mut beta = BN256BaseNNField::allocated_constant(cs, beta, &base_field_params);

    let bigint_from_hex_str = |cs: &mut CS, s: &str| -> UInt512<F> {
        let v = U256::from_str_radix(s, 16).unwrap();
        UInt512::allocated_constant(cs, (v, U256::zero()))
    };

    let modulus_minus_one_div_two = bigint_from_hex_str(cs, MODULUS_MINUS_ONE_DIV_TWO);

    let u256_from_hex_str = |cs: &mut CS, s: &str| -> UInt256<F> {
        let v = U256::from_str_radix(s, 16).unwrap();
        UInt256::allocated_constant(cs, v)
    };

    let a1 = u256_from_hex_str(cs, A1);
    let b1_negative = u256_from_hex_str(cs, B1_NEGATIVE);
    let a2 = u256_from_hex_str(cs, A2);
    let b2 = a1.clone();

    let boolean_false = Boolean::allocated_constant(cs, false);

    // Scalar decomposition
    let (k1_was_negated, k1, k2_was_negated, k2) = {
        let k = convert_field_element_to_uint256(cs, scalar.clone());

        // We take 8 non-zero limbs for the scalar (since it could be of any size), and 4 for B2
        // (since it fits in 128 bits).
        let b2_times_k = k.widening_mul(cs, &b2, 8, 4);
        // can not overflow u512
        let (b2_times_k, of) = b2_times_k.overflowing_add(cs, &modulus_minus_one_div_two);
        Boolean::enforce_equal(cs, &of, &boolean_false);
        let c1 = b2_times_k.to_high();

        // We take 8 non-zero limbs for the scalar (since it could be of any size), and 4 for B1
        // (since it fits in 128 bits).
        let b1_times_k = k.widening_mul(cs, &b1_negative, 8, 4);
        // can not overflow u512
        let (b1_times_k, of) = b1_times_k.overflowing_add(cs, &modulus_minus_one_div_two);
        Boolean::enforce_equal(cs, &of, &boolean_false);
        let c2 = b1_times_k.to_high();

        let mut a1 = convert_uint256_to_field_element(cs, &a1, &scalar_field_params);
        let mut b1_negative = convert_uint256_to_field_element(cs, &b1_negative, &scalar_field_params);
        let mut a2 = convert_uint256_to_field_element(cs, &a2, &scalar_field_params);
        let mut b2 = a1.clone();
        let mut c1 = convert_uint256_to_field_element(cs, &c1, &scalar_field_params);
        let mut c2 = convert_uint256_to_field_element(cs, &c2, &scalar_field_params);

        let mut c1_times_a1 = c1.mul(cs, &mut a1);
        let mut c2_times_a2 = c2.mul(cs, &mut a2);
        let mut k1 = scalar.sub(cs, &mut c1_times_a1).sub(cs, &mut c2_times_a2);
        k1.normalize(cs);
        let mut c2_times_b2 = c2.mul(cs, &mut b2);
        let mut k2 = c1.mul(cs, &mut b1_negative).sub(cs, &mut c2_times_b2);
        k2.normalize(cs);

        let k1_u256 = convert_field_element_to_uint256(cs, k1.clone());
        let k2_u256 = convert_field_element_to_uint256(cs, k2.clone());
        let max_k1_or_k2 = UInt256::allocated_constant(cs, MAX_DECOMPOSITION_VALUE);
        // we will need k1 and k2 to be < 2^128, so we can compare via subtraction
        let (_res, k1_out_of_range) = max_k1_or_k2.overflowing_sub(cs, &k1_u256);
        let k1_negated = k1.negated(cs);
        // dbg!(k1.witness_hook(cs)());
        // dbg!(k1_negated.witness_hook(cs)());
        let k1 = <BN256ScalarNNField<F> as NonNativeField<F, BN256Fr>>::conditionally_select(
            cs,
            k1_out_of_range,
            &k1_negated,
            &k1,
        );
        let (_res, k2_out_of_range) = max_k1_or_k2.overflowing_sub(cs, &k2_u256);
        let k2_negated = k2.negated(cs);
        // dbg!(k2.witness_hook(cs)());
        // dbg!(k2_negated.witness_hook(cs)());
        let k2 = <BN256ScalarNNField<F> as NonNativeField<F, BN256Fr>>::conditionally_select(
            cs,
            k2_out_of_range,
            &k2_negated,
            &k2,
        );

        (k1_out_of_range, k1, k2_out_of_range, k2)
    };

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

    let mut endomorphisms_table = table.clone();
    for (x, _) in endomorphisms_table.iter_mut() {
        *x = x.mul(cs, &mut beta);
    }

    // we also know that we will multiply k1 by points, and k2 by their endomorphisms, and if they were
    // negated above to fit into range, we negate bases here
    for (_, y) in table.iter_mut() {
        let negated = y.negated(cs);
        *y = Selectable::conditionally_select(cs, k1_was_negated, &negated, &*y);
    }

    for (_, y) in endomorphisms_table.iter_mut() {
        let negated = y.negated(cs);
        *y = Selectable::conditionally_select(cs, k2_was_negated, &negated, &*y);
    }

    // now decompose every scalar we are interested in
    let k1_msb_decomposition = to_width_4_window_form(cs, k1);
    let k2_msb_decomposition = to_width_4_window_form(cs, k2);

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