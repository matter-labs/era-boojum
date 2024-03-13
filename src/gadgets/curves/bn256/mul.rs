use std::sync::Arc;

use crypto_bigint::{Zero, U1024};
use ethereum_types::U256;
use mul::{decomp_table::WnafDecompTable, naf_abs_div2_table::NafAbsDiv2Table};
use pairing::{ff::PrimeField, CurveAffine};

use super::*;

use crate::{
    cs::traits::cs::ConstraintSystem,
    gadgets::{
        blake2s::mixing_function::merge_byte_using_table, boolean::Boolean, curves::{sw_projective::SWProjectivePoint, SmallField}, non_native_field::{
            implementations::{OverflowTracker, RepresentationForm},
            traits::NonNativeField,
        }, num::Num, tables::ByteSplitTable, traits::{selectable::Selectable, witnessable::WitnessHookable}, u16::UInt16, u256::UInt256, u32::UInt32, u512::UInt512, u8::UInt8
    },
};

// GLV constants
/// The value of 2**128 in string format
const TWO_POW_128: &'static str = "340282366920938463463374607431768211456";

/// BETA parameter such that phi(x, y) = (beta*x, y)
/// is a valid endomorphism for the curve. Note
/// that it is possible to use one since 3 divides prime order - 1
const BETA: &'static str =
    "2203960485148121921418603742825762020974279258880205651966";

// Secp256k1.p - 1 / 2
// 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc2f - 0x1 / 0x2
const MODULUS_MINUS_ONE_DIV_TWO: &'static str =
    "7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0";

// Decomposition constants
// Derived through algorithm 3.74 http://tomlr.free.fr/Math%E9matiques/Math%20Complete/Cryptography/Guide%20to%20Elliptic%20Curve%20Cryptography%20-%20D.%20Hankerson,%20A.%20Menezes,%20S.%20Vanstone.pdf
// NOTE: B2 == A1
const A1: &'static str = "0x3086d221a7d46bcde86c90e49284eb15";
const B1: &'static str = "0xe4437ed6010e88286f547fa90abfe4c3";
const A2: &'static str = "0x114ca50f7a8e2f3f657c1108d9d44cfd8";

fn convert_uint256_to_field_element<F, CS, P, const N: usize>(
    cs: &mut CS,
    elem: &UInt256<F>,
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

    for (dst, src) in limbs.array_chunks_mut::<2>().zip(elem.inner.iter()) {
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
        limbs: limbs,
        non_zero_limbs: 16,
        tracker: OverflowTracker { max_moduluses },
        form: RepresentationForm::Normalized,
        params: params.clone(),
        _marker: std::marker::PhantomData,
    };

    element
}

/// Converts the non-native field eelement over u16 to a UInt256.
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

fn to_wnaf<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    e: BN256ScalarNNField<F>,
    neg: Boolean<F>,
    decomp_id: u32,
    byte_split_id: u32,
) -> Vec<UInt8<F>> {
    let mut naf = vec![];
    let mut bytes = e
        .limbs
        .iter()
        .flat_map(|el| unsafe { UInt16::from_variable_unchecked(*el).to_le_bytes(cs) })
        .collect::<Vec<UInt8<F>>>();

    // Loop for max amount of bits in e to ensure homogenous circuit
    for i in 0..33 {
        // Since each lookup consumes 2 bits of information, and we need at least 3 bits for
        // figuring out the NAF number, we can do two lookups before needing to propagated the
        // changes up the bytestring.
        let mut naf_overflow = None;
        for j in 0..2 {
            let res = cs.perform_lookup::<1, 2>(decomp_id, &[bytes[0].get_variable()]);
            let wnaf_and_carry_bits = unsafe { UInt32::from_variable_unchecked(res[0]) };
            let wnaf_bytes = wnaf_and_carry_bits.to_le_bytes(cs);
            bytes[0] = unsafe { UInt8::from_variable_unchecked(res[1]) };
            wnaf_bytes[..2].iter().for_each(|byte| {
                let byte_neg = byte.negate(cs);
                let byte = Selectable::conditionally_select(cs, neg, byte, &byte_neg);
                naf.push(byte);
            });
            // Save carry bit.
            // It only ever matters to save it on the first iteration as it is not possible
            // to overflow for the second.
            if j == 0 {
                naf_overflow = Some(wnaf_bytes[2]);
            }
        }

        // Break up the first byte into a lower chunk and a (potential) carry bit.
        let res = cs.perform_lookup::<1, 2>(byte_split_id, &[bytes[0].get_variable()]);
        let mut low = res[0];
        let carry_bit = unsafe { UInt8::from_variable_unchecked(res[1]) };
        let mut of = Boolean::allocated_constant(cs, true);

        // Shift e and propagate carry.
        // Because a GLV decomposed scalar is at most 129 bits, we only care to shift
        // the lower 17 bytes of the number initially, and as we progress, more zero bytes
        // will appear, lowering the amount of iterations needed to shift our number.
        let num_iter = 16 - (i / 2);
        bytes
            .iter_mut()
            .skip(1)
            .take(num_iter)
            .enumerate()
            .for_each(|(i, b)| {
                // Propagate carry
                let (added_b, new_of) = b.overflowing_add(cs, &carry_bit);
                *b = Selectable::conditionally_select(cs, of, &added_b, b);
                of = new_of;
                // If this is the first byte, we also add the NAF carry bit.
                if i == 0 {
                    let naf_of;
                    (*b, naf_of) = b.overflowing_add(cs, &naf_overflow.unwrap());
                    // If this overflows, we should remember to add a carry bit to the next element.
                    of = Selectable::conditionally_select(cs, naf_of, &naf_of, &of);
                }

                // Glue bytes
                let res = cs.perform_lookup::<1, 2>(byte_split_id, &[b.get_variable()]);
                *b = unsafe {
                    UInt8::from_variable_unchecked(merge_byte_using_table::<_, _, 4>(
                        cs, low, res[0],
                    ))
                };
                low = res[1];
            });

        // Shift up by one to align.
        bytes = bytes[1..].to_vec();
    }

    naf
}

fn wnaf_ec_scalar_mul<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut point: SWProjectivePoint<F, BN256Affine, BN256BaseNNField<F>>,
    mut scalar: BN256ScalarNNField<F>,
    base_field_params: &Arc<BN256BaseNNFieldParams>,
    scalar_field_params: &Arc<BN256ScalarNNFieldParams>,
) -> SWProjectivePoint<F, BN256Affine, BN256BaseNNField<F>> {
    scalar.enforce_reduced(cs);

    let pow_2_128 = U256::from_dec_str(TWO_POW_128).unwrap();
    let pow_2_128 = UInt512::allocated_constant(cs, (pow_2_128, U256::zero()));

    let beta = BN256Fq::from_str(BETA).unwrap();
    let mut beta = BN256BaseNNField::allocated_constant(cs, beta, &base_field_params);

    let bigint_from_hex_str = |cs: &mut CS, s: &str| -> UInt512<F> {
        let v = U256::from_str_radix(s, 16).unwrap();
        UInt512::allocated_constant(cs, (v, U256::zero()))
    };

    let modulus_minus_one_div_two = bigint_from_hex_str(cs, MODULUS_MINUS_ONE_DIV_TWO);

    // Scalar decomposition
    let (k1_neg, k1, k2_neg, k2) = {
        let u256_from_hex_str = |cs: &mut CS, s: &str| -> UInt256<F> {
            let v = U256::from_str_radix(s, 16).unwrap();
            UInt256::allocated_constant(cs, v)
        };

        let a1 = u256_from_hex_str(cs, A1);
        let b1 = u256_from_hex_str(cs, B1);
        let a2 = u256_from_hex_str(cs, A2);
        let b2 = a1.clone();

        let k = convert_field_element_to_uint256(cs, scalar.clone());

        // We take 8 non-zero limbs for the scalar (since it could be of any size), and 4 for B2
        // (since it fits in 128 bits).
        let b2_times_k = k.widening_mul(cs, &b2, 8, 4);
        let b2_times_k = b2_times_k.overflowing_add(cs, &modulus_minus_one_div_two);
        let c1 = b2_times_k.0.to_high();

        // We take 8 non-zero limbs for the scalar (since it could be of any size), and 4 for B1
        // (since it fits in 128 bits).
        let b1_times_k = k.widening_mul(cs, &b1, 8, 4);
        let b1_times_k = b1_times_k.overflowing_add(cs, &modulus_minus_one_div_two);
        let c2 = b1_times_k.0.to_high();

        let mut a1 = convert_uint256_to_field_element(cs, &a1, &scalar_field_params);
        let mut b1 = convert_uint256_to_field_element(cs, &b1, &scalar_field_params);
        let mut a2 = convert_uint256_to_field_element(cs, &a2, &scalar_field_params);
        let mut b2 = a1.clone();
        let mut c1 = convert_uint256_to_field_element(cs, &c1, &scalar_field_params);
        let mut c2 = convert_uint256_to_field_element(cs, &c2, &scalar_field_params);

        let mut c1_times_a1 = c1.mul(cs, &mut a1);
        let mut c2_times_a2 = c2.mul(cs, &mut a2);
        let mut k1 = scalar.sub(cs, &mut c1_times_a1).sub(cs, &mut c2_times_a2);
        k1.normalize(cs);
        let mut c2_times_b2 = c2.mul(cs, &mut b2);
        let mut k2 = c1.mul(cs, &mut b1).sub(cs, &mut c2_times_b2);
        k2.normalize(cs);

        let k1_u256 = convert_field_element_to_uint256(cs, k1.clone());
        let k2_u256 = convert_field_element_to_uint256(cs, k2.clone());
        let low_pow_2_128 = pow_2_128.to_low();
        let (_res, k1_neg) = k1_u256.overflowing_sub(cs, &low_pow_2_128);
        let k1_negated = k1.negated(cs);
        let k1 = <BN256ScalarNNField<F> as NonNativeField<F, BN256Fr>>::conditionally_select(
            cs,
            k1_neg,
            &k1,
            &k1_negated,
        );
        let (_res, k2_neg) = k2_u256.overflowing_sub(cs, &low_pow_2_128);
        let k2_negated = k2.negated(cs);
        let k2 = <BN256ScalarNNField<F> as NonNativeField<F, BN256Fr>>::conditionally_select(
            cs,
            k2_neg,
            &k2,
            &k2_negated,
        );

        (k1_neg, k1, k2_neg, k2)
    };

    // WNAF
    // The scalar multiplication window size.
    const GLV_WINDOW_SIZE: usize = 2;

    // The GLV table length.
    const L: usize = 1 << (GLV_WINDOW_SIZE - 1);

    let mut t1 = Vec::with_capacity(L);
    // We use `convert_to_affine_or_default`, but we don't need to worry about returning 1, since
    // we know that the point is not infinity.
    let (mut double, _) = point
        .double(cs)
        .convert_to_affine_or_default(cs, BN256Affine::one());
    t1.push(point.clone());
    for i in 1..L {
        let next = t1[i - 1].add_mixed(cs, &mut double);
        t1.push(next);
    }

    let t1 = t1
        .iter_mut()
        .map(|el| el.convert_to_affine_or_default(cs, BN256Affine::one()).0)
        .collect::<Vec<_>>();

    let t2 = t1
        .clone()
        .into_iter()
        .map(|mut el| (el.0.mul(cs, &mut beta), el.1))
        .collect::<Vec<_>>();

    let overflow_checker = UInt8::allocated_constant(cs, 2u8.pow(7));
    let decomp_id = cs
        .get_table_id_for_marker::<WnafDecompTable>()
        .expect("table should exist");
    let byte_split_id = cs
        .get_table_id_for_marker::<ByteSplitTable<4>>()
        .expect("table should exist");

    let naf_abs_div2_table_id = cs
        .get_table_id_for_marker::<NafAbsDiv2Table>()
        .expect("table must exist");

    let naf_add =
        |cs: &mut CS,
         table: &[(BN256BaseNNField<F>, BN256BaseNNField<F>)],
         naf: UInt8<F>,
         acc: &mut SWProjectivePoint<F, BN256Affine, BN256BaseNNField<F>>| {
            let is_zero = naf.is_zero(cs);
            let index = unsafe {
                UInt8::from_variable_unchecked(
                    cs.perform_lookup::<1, 2>(naf_abs_div2_table_id, &[naf.get_variable()])[0],
                )
            };
            let coords = &table[index.witness_hook(cs)().unwrap() as usize];
            let mut p_1 =
                SWProjectivePoint::<F, BN256Affine, BN256BaseNNField<F>>::from_xy_unchecked(
                    cs,
                    coords.0.clone(),
                    coords.1.clone(),
                );
            let (_, naf_is_positive) = naf.overflowing_sub(cs, &overflow_checker);
            let p_1_neg = p_1.negated(cs);
            p_1 = Selectable::conditionally_select(cs, naf_is_positive, &p_1, &p_1_neg);
            let acc_added = acc.add_mixed(cs, &mut (p_1.x, p_1.y));
            *acc = Selectable::conditionally_select(cs, is_zero, &acc, &acc_added);
        };

    let naf1 = to_wnaf(cs, k1, k1_neg, decomp_id, byte_split_id);
    let naf2 = to_wnaf(cs, k2, k2_neg, decomp_id, byte_split_id);
    let mut acc =
        SWProjectivePoint::<F, BN256Affine, BN256BaseNNField<F>>::zero(cs, &base_field_params);
    for i in (0..129).rev() {
        naf_add(cs, &t1, naf1[i], &mut acc);
        naf_add(cs, &t2, naf2[i], &mut acc);
        if i != 0 {
            acc = acc.double(cs);
        }
    }

    acc
}
