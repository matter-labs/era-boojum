use std::mem::MaybeUninit;

use arrayvec::ArrayVec;

use super::*;
use crate::config::*;
use crate::cs::gates::{
    assert_no_placeholder_variables, ConstantAllocatableCS, FmaGateInBaseFieldWithoutConstant,
    FmaGateInBaseWithoutConstantParams, ReductionGate, ReductionGateParams,
};
use crate::cs::Variable;
use crate::gadgets::tables::ch4::Ch4Table;
use crate::gadgets::tables::chunk4bits::Split4BitChunkTable;
use crate::gadgets::tables::maj4::Maj4Table;
use crate::gadgets::tables::trixor4::TriXor4Table;
use crate::gadgets::traits::castable::WitnessCastable;

// in contrast to Blake2s we actually keep words packed as UInt32,
// because we need quite "wide" additions

const MASK_4: u32 = (1u32 << 4) - 1;

pub fn round_function_over_uint32<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    state: &mut [UInt32<F>; 8],
    message_block: &[UInt32<F>; 16],
) -> [UInt8<F>; SHA256_DIGEST_SIZE] {
    let mut state_as_vars = state.map(|el| el.get_variable());
    let message_block_as_vars = message_block.map(|el| el.get_variable());

    let u4_pieces = round_function(cs, &mut state_as_vars, &message_block_as_vars, true)
        .expect("digest output");

    let mut result = [MaybeUninit::uninit(); SHA256_DIGEST_SIZE];
    for (dst, src) in result.iter_mut().zip(u4_pieces.array_chunks::<2>()) {
        let as_u8 = uint8_from_4bit_chunks(cs, src);
        dst.write(as_u8);
    }

    // write state back
    unsafe {
        let state_as_u32 = state_as_vars.map(|el| UInt32::from_variable_unchecked(el));
        *state = state_as_u32;

        result.map(|el| el.assume_init())
    }
}

// we only have variables in the signature because
// - if it's a first round then state is made of constants
// - if it's not the last round then next round will range check when rounds happen
// - if it's the last round then it's done by caller
pub fn round_function<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    state: &mut [Variable; 8],
    message_block: &[Variable; 16],
    range_check_final_state: bool,
) -> Option<[Variable; 64]> {
    // NOTE: assuming that state is all 32 bits
    // - e, f, g are range checked by decomposition + xor
    // - a, b, c are range checked by decomposition + xor
    // - initial d and initial h are assumed to be in range
    // then some variables become results of addition, so we could need to carefylly check those,
    // but in practice we do not need to check all, but only d and h after addition to the state
    // after all 64 inner rounds

    // first we create message schedule (expand)
    let mut expanded = [Variable::placeholder(); 64];
    for (dst, src) in expanded[..16].iter_mut().zip(message_block.iter()) {
        *dst = *src;
    }

    let zero = cs.allocate_constant(F::ZERO);
    let one = cs.allocate_constant(F::ONE);

    // we assume inputs to be range checked, so
    // idx - 15 is range checked by xor
    // idx - 2 is range-checked by xor
    // idx - 7 goes into addition and has to be range checked
    // idx - 16 goes into addition and has to be range checked
    // so we are "safe" as long as our index over which we work right now will become
    // idx - 2 for some next round

    let mut yet_unconstrained_chunks = ArrayVec::<Variable, 46>::new();

    for idx in 16..SHA256_ROUNDS {
        let t0 = expanded[idx - 15];
        // here we can reuse for rotation
        let (t0_rotated_7, _t0_rot_7_decompose_low, t0_rot_7_decompose_high) =
            split_and_rotate(cs, t0, 7);
        let (t0_rotated_18, _, _) = split_and_rotate(cs, t0, 18);
        // we can create t0 >> 3 by properly changing rotation
        let mut t0_shifted_3 = [Variable::placeholder(); 8];
        for idx in 0..7 {
            t0_shifted_3[idx] = t0_rotated_7[(7 + idx) % 8];
        }
        // and instead of highest word we use 1 bit piece that rotation made for us
        t0_shifted_3[7] = t0_rot_7_decompose_high;
        assert_no_placeholder_variables(&t0_shifted_3);

        let s0_chunks = tri_xor_many(cs, &t0_rotated_7, &t0_rotated_18, &t0_shifted_3);

        // for s1 we can not reuse it, so we do all
        let t1 = expanded[idx - 2];
        let (t1_rotated_17, _, _) = split_and_rotate(cs, t1, 17);
        let (t1_rotated_19, _, _) = split_and_rotate(cs, t1, 19);
        let (t1_rotated_10, _, t1_rotated_10_decompose_high) = split_and_rotate(cs, t1, 10);

        let mut t1_shifted_10 = t1_rotated_10;
        t1_shifted_10[7] = zero;
        t1_shifted_10[6] = zero;
        t1_shifted_10[5] = t1_rotated_10_decompose_high;

        for idx in 0..7 {
            t0_shifted_3[idx] = t0_rotated_7[(7 + idx) % 8];
        }

        let s1_chunks = tri_xor_many(cs, &t1_rotated_17, &t1_rotated_19, &t1_shifted_10);

        let s0 = uint32_from_4bit_chunks(cs, &s0_chunks);
        let s1 = uint32_from_4bit_chunks(cs, &s1_chunks);

        // note that message expansion only shows up in rounds
        // as part of addition, so we need to range check here

        let expanded_word = ReductionGate::reduce_terms(
            cs,
            [F::ONE; 4],
            [
                s0.variable,
                s1.variable,
                expanded[idx - 7],
                expanded[idx - 16],
            ],
        );

        // we only need to fully range check if it's one of the last
        let u32_part = if idx + 2 >= 64 {
            let (u32_part, _) = range_check_36_bits_using_sha256_tables(cs, expanded_word);

            u32_part
        } else {
            let (u32_part, high_unchecked) = split_36_bits_unchecked(cs, expanded_word);
            yet_unconstrained_chunks.push(high_unchecked);

            u32_part
        };

        expanded[idx] = u32_part;
    }

    // range check small pieced
    for chunk in yet_unconstrained_chunks.chunks(3) {
        let a = chunk.get(0).copied().unwrap_or(zero);
        let b = chunk.get(1).copied().unwrap_or(zero);
        let c = chunk.get(2).copied().unwrap_or(zero);

        let _ = tri_xor_many(cs, &[a], &[b], &[c]);
    }

    drop(yet_unconstrained_chunks);

    // main part
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;

    for round in 0..SHA256_ROUNDS {
        let (e_rot_6, _, _) = split_and_rotate(cs, e, 6);
        let (e_rot_11, _, _) = split_and_rotate(cs, e, 11);
        let (e_rot_25, _, _) = split_and_rotate(cs, e, 25);
        let s1 = tri_xor_many(cs, &e_rot_6, &e_rot_11, &e_rot_25);
        let s1 = uint32_from_4bit_chunks(cs, &s1).variable;

        let e_decompose = uint32_into_4bit_chunks(cs, e);
        let f_decompose = uint32_into_4bit_chunks(cs, f);
        let g_decompose = uint32_into_4bit_chunks(cs, g);
        let ch = ch_many(cs, &e_decompose, &f_decompose, &g_decompose);
        let ch = uint32_from_4bit_chunks(cs, &ch).variable;

        // add 5 terms first
        let rc = cs.allocate_constant(F::from_raw_u64_unchecked(ROUND_CONSTANTS[round] as u64));
        let tmp1 = ReductionGate::reduce_terms(cs, [F::ONE; 4], [h, s1, ch, rc]);

        let tmp1 = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            F::ONE,
            (one, tmp1),
            F::ONE,
            expanded[round],
        );

        let t = FmaGateInBaseFieldWithoutConstant::compute_fma(cs, F::ONE, (one, tmp1), F::ONE, d);

        let (new_e, _) = range_check_36_bits_using_sha256_tables(cs, t);

        let (a_rot_2, _, _) = split_and_rotate(cs, a, 2);
        let (a_rot_13, _, _) = split_and_rotate(cs, a, 13);
        let mut a_rot_22 = [Variable::placeholder(); 8];
        for idx in 0..8 {
            a_rot_22[idx] = a_rot_2[(idx + 5) % 8];
        }
        assert_no_placeholder_variables(&a_rot_22);
        let s0 = tri_xor_many(cs, &a_rot_2, &a_rot_13, &a_rot_22);
        let s0 = uint32_from_4bit_chunks(cs, &s0).variable;

        let a_decompose = uint32_into_4bit_chunks(cs, a);
        let b_decompose = uint32_into_4bit_chunks(cs, b);
        let c_decompose = uint32_into_4bit_chunks(cs, c);
        let maj = maj_many(cs, &a_decompose, &b_decompose, &c_decompose);
        let maj = uint32_from_4bit_chunks(cs, &maj).variable;

        let t = ReductionGate::reduce_terms(
            cs,
            [F::ONE, F::ONE, F::ONE, F::ZERO],
            [s0, maj, tmp1, zero],
        );
        let (new_a, _) = range_check_36_bits_using_sha256_tables(cs, t);

        h = g;
        g = f;
        f = e;
        e = new_e;
        d = c;
        c = b;
        b = a;
        a = new_a;
    }

    // add into state

    let mut final_d_decomposition = [Variable::placeholder(); 8];
    let mut final_h_decomposition = [Variable::placeholder(); 8];

    let mut yet_unchecked_chunks = ArrayVec::<Variable, 8>::new();

    for (idx, (dst, src)) in state
        .iter_mut()
        .zip([a, b, c, d, e, f, g, h].into_iter())
        .enumerate()
    {
        let tmp =
            FmaGateInBaseFieldWithoutConstant::compute_fma(cs, F::ONE, (one, *dst), F::ONE, src);
        let (tmp, high) = split_36_bits_unchecked(cs, tmp);
        yet_unchecked_chunks.push(high);
        if idx == 3 {
            final_d_decomposition = range_check_uint32_using_sha256_tables(cs, tmp);
        }
        if idx == 7 {
            final_h_decomposition = range_check_uint32_using_sha256_tables(cs, tmp);
        }
        // other variables are range-checked in next round unless requested otherwise
        *dst = tmp;
    }

    for chunk in yet_unchecked_chunks.chunks(3) {
        let a = chunk.get(0).copied().unwrap_or(zero);
        let b = chunk.get(1).copied().unwrap_or(zero);
        let c = chunk.get(2).copied().unwrap_or(zero);

        let _ = tri_xor_many(cs, &[a], &[b], &[c]);
    }

    drop(yet_unchecked_chunks);

    if range_check_final_state {
        let mut le_4bit_chunks = [Variable::placeholder(); 64];
        for (idx, (el, dst)) in state
            .iter()
            .zip(le_4bit_chunks.array_chunks_mut::<8>())
            .enumerate()
        {
            if idx == 3 {
                *dst = final_d_decomposition;
            } else if idx == 7 {
                *dst = final_h_decomposition;
            } else {
                let tmp = uint32_into_4bit_chunks(cs, *el);
                *dst = tmp;
            }
        }
        assert_no_placeholder_variables(&le_4bit_chunks);
        let mut it_to_range_check = le_4bit_chunks[..(3 * 8)]
            .iter()
            .chain(le_4bit_chunks[(4 * 8)..(7 * 8)].iter())
            .copied();
        // we need to check 128 - 16 = 112 variables by chunks of 3
        for _ in 0..38 {
            let a = it_to_range_check.next().unwrap_or(zero);
            let b = it_to_range_check.next().unwrap_or(zero);
            let c = it_to_range_check.next().unwrap_or(zero);
            let _ = tri_xor_many(cs, &[a], &[b], &[c]);
        }

        assert!(it_to_range_check.next().is_none());

        Some(le_4bit_chunks)
    } else {
        None
    }
}

fn uint8_from_4bit_chunks<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    chunks: &[Variable; 2],
) -> UInt8<F> {
    let one = cs.allocate_constant(F::ONE);

    let result = FmaGateInBaseFieldWithoutConstant::compute_fma(
        cs,
        F::from_u64_unchecked(1u64 << 4),
        (one, chunks[1]),
        F::ONE,
        chunks[0],
    );

    unsafe { UInt8::from_variable_unchecked(result) }
}

fn uint32_from_4bit_chunks<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    chunks: &[Variable; 8],
) -> UInt32<F> {
    let to_u16_constants = [
        F::ONE,
        F::from_u64_unchecked(1u64 << 4),
        F::from_u64_unchecked(1u64 << 8),
        F::from_u64_unchecked(1u64 << 12),
    ];

    let low_u16 = ReductionGate::reduce_terms(
        cs,
        to_u16_constants,
        [chunks[0], chunks[1], chunks[2], chunks[3]],
    );

    let high_u16 = ReductionGate::reduce_terms(
        cs,
        to_u16_constants,
        [chunks[4], chunks[5], chunks[6], chunks[7]],
    );

    let one = cs.allocate_constant(F::ONE);

    let result = FmaGateInBaseFieldWithoutConstant::compute_fma(
        cs,
        F::from_u64_unchecked(1u64 << 16),
        (one, high_u16),
        F::ONE,
        low_u16,
    );

    unsafe { UInt32::from_variable_unchecked(result) }
}

fn uint32_into_4bit_chunks<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Variable,
) -> [Variable; 8] {
    let chunks = cs.alloc_multiple_variables_without_values::<8>();

    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
        let value_fn = move |input: [F; 1]| {
            let mut input = <u32 as WitnessCastable<F, F>>::cast_from_source(input[0]);

            let mut result = [F::ZERO; 8];
            for dst in result.iter_mut() {
                let chunk = input & MASK_4;
                input >>= 4;
                *dst = F::from_u64_unchecked(chunk as u64);
            }

            result
        };

        let outputs = Place::from_variables(chunks);
        cs.set_values_with_dependencies(&[input.into()], &outputs, value_fn);
    }

    let to_u16_constants = [
        F::ONE,
        F::from_u64_unchecked(1u64 << 4),
        F::from_u64_unchecked(1u64 << 8),
        F::from_u64_unchecked(1u64 << 12),
    ];

    let low_u16 = ReductionGate::reduce_terms(
        cs,
        to_u16_constants,
        [chunks[0], chunks[1], chunks[2], chunks[3]],
    );

    let high_u16 = ReductionGate::reduce_terms(
        cs,
        to_u16_constants,
        [chunks[4], chunks[5], chunks[6], chunks[7]],
    );

    let one = cs.allocate_constant(F::ONE);

    let gate = FmaGateInBaseFieldWithoutConstant {
        params: FmaGateInBaseWithoutConstantParams {
            coeff_for_quadtaric_part: F::from_u64_unchecked(1u64 << 16),
            linear_term_coeff: F::ONE,
        },
        quadratic_part: (one, high_u16),
        linear_part: low_u16,
        rhs_part: input,
    };

    gate.add_to_cs(cs);

    chunks
}

fn split_and_rotate<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Variable,
    rotation: usize,
) -> ([Variable; 8], Variable, Variable) {
    // our strategy is to output 8 4-bit chunks. When we decompose we actually
    // split only parts of the word in a way that we can later re-merge into 4-bit chunks

    // e.g. if we have rotate right by 7 bits, then we want to have the
    // following after rotation (from lower bits)
    // |4|4|4|4|4|4|4|4|, so we split lowest 7 bits as 3 + 4, and we need the highest bit as well,
    // that we will later on re-merge as 4, so we do
    // |1|4|4|4|4|4|4|4|3| decomposition, then rotate by renumeration,
    // and then only merge once

    let aligned_variables = cs.alloc_multiple_variables_without_values::<7>();
    let decompose_low = cs.alloc_variable_without_value();
    let decompose_high = cs.alloc_variable_without_value();

    let rotate_mod = rotation % 4;

    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
        let value_fn = move |input: [F; 1]| {
            let mut input = <u32 as WitnessCastable<F, F>>::cast_from_source(input[0]);
            let lowest_mask = (1u32 << rotate_mod) - 1;

            let mut result = [F::ZERO; 9];
            let lowest = input & lowest_mask;
            result[0] = F::from_u64_unchecked(lowest as u64);
            input >>= rotate_mod;

            for dst in result[1..8].iter_mut() {
                let chunk = input & MASK_4;
                input >>= 4;
                *dst = F::from_u64_unchecked(chunk as u64);
            }

            let highest = input;
            debug_assert!(input < (1u32 << (4 - rotate_mod)));
            result[8] = F::from_u64_unchecked(highest as u64);

            result
        };

        let outputs = Place::from_variables([
            decompose_low,
            aligned_variables[0],
            aligned_variables[1],
            aligned_variables[2],
            aligned_variables[3],
            aligned_variables[4],
            aligned_variables[5],
            aligned_variables[6],
            decompose_high,
        ]);
        cs.set_values_with_dependencies(&[input.into()], &outputs, value_fn);
    }

    // prove original recomposition
    let mut coeffs = [F::ZERO; 4];
    let mut shift = 0;
    for (idx, dst) in coeffs.iter_mut().enumerate() {
        *dst = F::from_u64_unchecked(1u64 << shift);

        if idx == 0 {
            shift += rotate_mod;
        } else {
            shift += 4;
        }
    }

    let t = ReductionGate::reduce_terms(
        cs,
        coeffs,
        [
            decompose_low,
            aligned_variables[0],
            aligned_variables[1],
            aligned_variables[2],
        ],
    );

    for (_idx, dst) in coeffs.iter_mut().enumerate().skip(1) {
        *dst = F::from_u64_unchecked(1u64 << shift);
        shift += 4;
    }
    coeffs[0] = F::ONE;

    let t = ReductionGate::reduce_terms(
        cs,
        coeffs,
        [
            t,
            aligned_variables[3],
            aligned_variables[4],
            aligned_variables[5],
        ],
    );

    let zero = cs.allocate_constant(F::ZERO);

    for (_idx, dst) in coeffs.iter_mut().enumerate().skip(1).take(2) {
        *dst = F::from_u64_unchecked(1u64 << shift);
        shift += 4;
    }
    coeffs[0] = F::ONE;
    coeffs[3] = F::ZERO;

    let gate = ReductionGate {
        params: ReductionGateParams {
            reduction_constants: coeffs,
        },
        terms: [t, aligned_variables[6], decompose_high, zero],
        reduction_result: input,
    };
    gate.add_to_cs(cs);

    // now we merge once, and leave other chunks aligned
    let merged = match rotate_mod {
        1 => {
            // 1 bit becomes high, so we swap inputs,
            // and swap result
            merge_4bit_chunk::<_, _, 1>(cs, decompose_low, decompose_high, true)
        }
        2 => {
            // here we can use as is
            merge_4bit_chunk::<_, _, 2>(cs, decompose_high, decompose_low, false)
        }
        3 => {
            // 3 bit becomes high, so we do as is
            merge_4bit_chunk::<_, _, 1>(cs, decompose_high, decompose_low, false)
        }
        _ => unreachable!(),
    };

    let mut result = [Variable::placeholder(); 8];
    // copy in proper places
    let full_rotations = rotation / 4;
    // e.g. if we rotate by 7, then 1st aligned variable will still become highest
    for (idx, el) in aligned_variables.into_iter().enumerate() {
        result[(8 - full_rotations + idx) % 8] = el;
    }
    // and place merged piece
    result[(8 - full_rotations - 1) % 8] = merged;

    assert_no_placeholder_variables(&result);

    (result, decompose_low, decompose_high)
}

fn merge_4bit_chunk<F: SmallField, CS: ConstraintSystem<F>, const SPLIT_AT: usize>(
    cs: &mut CS,
    low: Variable,
    high: Variable,
    swap_output: bool,
) -> Variable {
    assert!(SPLIT_AT > 0);
    assert!(SPLIT_AT <= 2);

    let merged = cs.alloc_multiple_variables_without_values::<2>();

    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
        let value_fn = move |input: [F; 2]| {
            // we already swapped
            let low = <u8 as WitnessCastable<F, F>>::cast_from_source(input[0]);
            let high = <u8 as WitnessCastable<F, F>>::cast_from_source(input[1]);

            debug_assert!(
                low < (1u8 << SPLIT_AT),
                "can not merge from chunks of width {}: low is {}",
                SPLIT_AT,
                low
            );
            debug_assert!(
                high < (1u8 << (4 - SPLIT_AT)),
                "can not merge from chunks of width {}: high is {}",
                SPLIT_AT,
                high
            );

            let reconstructed = low | (high << SPLIT_AT);
            let swapped = high | (low << (4 - SPLIT_AT));

            [
                F::from_u64_unchecked(reconstructed as u64),
                F::from_u64_unchecked(swapped as u64),
            ]
        };

        let outputs = Place::from_variables(merged);

        cs.set_values_with_dependencies(&[low.into(), high.into()], &outputs, value_fn);
    }

    let table_id = cs
        .get_table_id_for_marker::<Split4BitChunkTable<SPLIT_AT>>()
        .expect("table must exist");
    cs.enforce_lookup::<4>(table_id, &[merged[0], low, high, merged[1]]);

    if swap_output == false {
        merged[0]
    } else {
        merged[1]
    }
}

fn tri_xor_many<F: SmallField, CS: ConstraintSystem<F>, const N: usize>(
    cs: &mut CS,
    a: &[Variable; N],
    b: &[Variable; N],
    c: &[Variable; N],
) -> [Variable; N] {
    let table_id = cs
        .get_table_id_for_marker::<TriXor4Table>()
        .expect("table must be added");
    let mut result = [Variable::placeholder(); N];

    for (((a, b), c), dst) in a.iter().zip(b.iter()).zip(c.iter()).zip(result.iter_mut()) {
        let [xor] = cs.perform_lookup::<3, 1>(table_id, &[*a, *b, *c]);
        *dst = xor;
    }

    result
}

fn ch_many<F: SmallField, CS: ConstraintSystem<F>, const N: usize>(
    cs: &mut CS,
    a: &[Variable; N],
    b: &[Variable; N],
    c: &[Variable; N],
) -> [Variable; N] {
    let table_id = cs
        .get_table_id_for_marker::<Ch4Table>()
        .expect("table must be added");
    let mut result = [Variable::placeholder(); N];

    for (((a, b), c), dst) in a.iter().zip(b.iter()).zip(c.iter()).zip(result.iter_mut()) {
        let [ch] = cs.perform_lookup::<3, 1>(table_id, &[*a, *b, *c]);
        *dst = ch;
    }

    result
}

fn maj_many<F: SmallField, CS: ConstraintSystem<F>, const N: usize>(
    cs: &mut CS,
    a: &[Variable; N],
    b: &[Variable; N],
    c: &[Variable; N],
) -> [Variable; N] {
    let table_id = cs
        .get_table_id_for_marker::<Maj4Table>()
        .expect("table must be added");
    let mut result = [Variable::placeholder(); N];

    for (((a, b), c), dst) in a.iter().zip(b.iter()).zip(c.iter()).zip(result.iter_mut()) {
        let [maj] = cs.perform_lookup::<3, 1>(table_id, &[*a, *b, *c]);
        *dst = maj;
    }

    result
}

fn range_check_uint32_using_sha256_tables<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Variable,
) -> [Variable; 8] {
    let chunks = uint32_into_4bit_chunks(cs, input);
    let _ = tri_xor_many(cs, &[chunks[0]], &[chunks[1]], &[chunks[2]]);
    let _ = tri_xor_many(cs, &[chunks[3]], &[chunks[4]], &[chunks[5]]);
    let _ = tri_xor_many(cs, &[chunks[6]], &[chunks[7]], &[chunks[0]]);

    chunks
}

// we should not have more than 36 bits here
fn range_check_36_bits_using_sha256_tables<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Variable,
) -> (Variable, [Variable; 9]) {
    let chunks = cs.alloc_multiple_variables_without_values::<9>();

    const MASK_4_U64: u64 = (1u64 << 4) - 1;

    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
        let value_fn = move |input: [F; 1]| {
            let mut input = input[0].as_u64_reduced();

            let mut result = [F::ZERO; 9];
            for dst in result.iter_mut() {
                let chunk = input & MASK_4_U64;
                input >>= 4;
                *dst = F::from_u64_unchecked(chunk);
            }

            debug_assert_eq!(input, 0);

            result
        };

        let outputs = Place::from_variables(chunks);
        cs.set_values_with_dependencies(&[input.into()], &outputs, value_fn);
    }

    let to_u16_constants = [
        F::ONE,
        F::from_u64_unchecked(1u64 << 4),
        F::from_u64_unchecked(1u64 << 8),
        F::from_u64_unchecked(1u64 << 12),
    ];

    let low_u16 = ReductionGate::reduce_terms(
        cs,
        to_u16_constants,
        [chunks[0], chunks[1], chunks[2], chunks[3]],
    );

    let high_u16 = ReductionGate::reduce_terms(
        cs,
        to_u16_constants,
        [chunks[4], chunks[5], chunks[6], chunks[7]],
    );

    let one = cs.allocate_constant(F::ONE);

    let u32_part = FmaGateInBaseFieldWithoutConstant::compute_fma(
        cs,
        F::from_u64_unchecked(1u64 << 16),
        (one, high_u16),
        F::ONE,
        low_u16,
    );

    // and final constraint

    let gate = FmaGateInBaseFieldWithoutConstant {
        params: FmaGateInBaseWithoutConstantParams {
            coeff_for_quadtaric_part: F::from_u64_unchecked(1u64 << 32),
            linear_term_coeff: F::ONE,
        },
        quadratic_part: (one, chunks[8]),
        linear_part: u32_part,
        rhs_part: input,
    };

    gate.add_to_cs(cs);

    let _ = tri_xor_many(cs, &[chunks[0]], &[chunks[1]], &[chunks[2]]);
    let _ = tri_xor_many(cs, &[chunks[3]], &[chunks[4]], &[chunks[5]]);
    let _ = tri_xor_many(cs, &[chunks[6]], &[chunks[7]], &[chunks[8]]);

    (u32_part, chunks)
}

// we should not have more than 36 bits here
fn split_36_bits_unchecked<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Variable,
) -> (Variable, Variable) {
    let chunks = cs.alloc_multiple_variables_without_values::<2>();

    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
        let value_fn = move |input: [F; 1]| {
            let input = input[0].as_u64_reduced();

            let low = input as u32;
            let high = input >> 32;

            debug_assert!(high < 1u64 << 4);

            [
                F::from_u64_unchecked(low as u64),
                F::from_u64_unchecked(high),
            ]
        };

        let outputs = Place::from_variables(chunks);
        cs.set_values_with_dependencies(&[input.into()], &outputs, value_fn);
    }

    let [low, high] = chunks;
    let one = cs.allocate_constant(F::ONE);

    let gate = FmaGateInBaseFieldWithoutConstant {
        params: FmaGateInBaseWithoutConstantParams {
            coeff_for_quadtaric_part: F::from_u64_unchecked(1u64 << 32),
            linear_term_coeff: F::ONE,
        },
        quadratic_part: (one, high),
        linear_part: low,
        rhs_part: input,
    };

    gate.add_to_cs(cs);

    (low, high)
}
