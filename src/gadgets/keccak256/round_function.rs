use crate::cs::gates::assert_no_placeholder_variables;
use crate::cs::gates::ConstantAllocatableCS;
use crate::cs::gates::FmaGateInBaseFieldWithoutConstant;
use crate::cs::gates::FmaGateInBaseWithoutConstantParams;
use crate::cs::gates::ReductionGate;
use crate::gadgets::blake2s::mixing_function::merge_byte_using_table;
use crate::gadgets::blake2s::mixing_function::split_byte_using_table;
use crate::gadgets::blake2s::mixing_function::xor_many;

use crate::gadgets::num::Num;
use crate::gadgets::tables::and8::And8Table;
use crate::gadgets::traits::castable::WitnessCastable;

use super::*;

// we carry internal state as 5x5 matrix, and elements of matrix are 8 pieces of 8-bit chunks
// (LE), even though Keccak256 doesn't have additions, so we basically do a lot of binary ops and that's it

pub fn keccak_256_round_function<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    state: &mut [[[Variable; BYTES_PER_WORD]; LANE_WIDTH]; LANE_WIDTH],
) {
    for i in 0..KECCAK256_NUM_ROUNDS {
        keccak_1600_round(cs, state, ROUND_CONSTANTS[i]);
    }
}

// NOTE: we assume the field modulus to be around 64 bits, so sparse base is not that beneficial,
// and we use 8x8 bit tables for XOR and AND, in the most trivial brute force way

fn keccak_1600_round<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    state: &mut [[[Variable; BYTES_PER_WORD]; LANE_WIDTH]; LANE_WIDTH],
    round_constant: u64,
) {
    // theta step - many xors
    // row-wise XOR

    let mut c = [[Variable::placeholder(); BYTES_PER_WORD]; LANE_WIDTH];
    for i in 0..LANE_WIDTH {
        let mut tmp = xor_many(cs, &state[i][0], &state[i][1]);
        tmp = xor_many(cs, &tmp, &state[i][2]);
        tmp = xor_many(cs, &tmp, &state[i][3]);
        tmp = xor_many(cs, &tmp, &state[i][4]);
        c[i] = tmp;
    }

    let one = cs.allocate_constant(F::ONE);

    let mut c_rot = [[Variable::placeholder(); BYTES_PER_WORD]; LANE_WIDTH];
    // rotated C also becomes input to XOR, so we are ok to use unchecked aligned chunks strategy here
    for i in 0..LANE_WIDTH {
        c_rot[i] = rotate_word(cs, &c[i], one, 1);
    }

    let mut d = [[Variable::placeholder(); BYTES_PER_WORD]; LANE_WIDTH];
    for i in 0..LANE_WIDTH {
        d[i] = xor_many(
            cs,
            &c[(LANE_WIDTH - 1 + i) % LANE_WIDTH],
            &c_rot[(LANE_WIDTH + 1 + i) % LANE_WIDTH],
        );
    }

    for i in 0..LANE_WIDTH {
        for j in 0..LANE_WIDTH {
            state[i][j] = xor_many(cs, &state[i][j], &d[i]);
        }
    }

    // rho and pi step

    // note: we get our intermediate rotations, that will go into xi-step, where each of those will be range checked,
    // and we can do NOT(a) operation by just doing 1<<8 - a

    let (mut i, mut j) = (1, 0);
    let mut current = state[i][j];
    for idx in 0..24 {
        let (new_i, new_j) = (j, (2 * i + 3 * j) % LANE_WIDTH);
        i = new_i;
        j = new_j;
        let existing = state[i][j];
        let rotation = ((idx as u64 + 1) * (idx as u64 + 2)) >> 1;
        let rotation = rotation % 64;
        let rotated = rotate_word(cs, &current, one, rotation as u32);
        state[i][j] = rotated;
        current = existing;
    }

    let negation_constant = cs.allocate_constant(F::from_u64_unchecked((1u64 << 8) - 1));

    // xi-step. Note order of `i` and `j`
    for j in 0..LANE_WIDTH {
        let t = [
            state[0][j],
            state[1][j],
            state[2][j],
            state[3][j],
            state[4][j],
        ];
        for i in 0..LANE_WIDTH {
            let mut tmp = [Variable::placeholder(); BYTES_PER_WORD];
            for (dst, src) in tmp.iter_mut().zip(t[(i + 1) % LANE_WIDTH].iter()) {
                *dst = Num::from_variable(negation_constant)
                    .sub(cs, &Num::from_variable(*src))
                    .variable;
            }
            let tmp = and_many(cs, &tmp, &t[(i + 2) % LANE_WIDTH]);
            state[i][j] = xor_many(cs, &tmp, &t[i]);
        }
    }

    // xor-in round constant
    let rc_le_bytes = round_constant.to_le_bytes();
    let rc_le_bytes = rc_le_bytes.map(|el| cs.allocate_constant(F::from_u64_unchecked(el as u64)));
    state[0][0] = xor_many(cs, &state[0][0], &rc_le_bytes);
}

// keccak is so table-heavy, that merging bytes is done by arithmetic gate
fn merge_byte<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    low: Variable,
    high: Variable,
    one: Variable,
    split_at: u32,
) -> Variable {
    debug_assert!(split_at > 0);
    debug_assert!(split_at < 8);

    let result = FmaGateInBaseFieldWithoutConstant::compute_fma(
        cs,
        F::from_u64_unchecked(1u64 << split_at),
        (one, high),
        F::ONE,
        low,
    );

    result
}

fn rotate_word<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    word: &[Variable; BYTES_PER_WORD],
    one: Variable,
    rotate_by: u32,
) -> [Variable; BYTES_PER_WORD] {
    // first we merge into subwords. Note that we can NOT merge into u64,
    // so we will do it very carefully by using 2xu32

    if rotate_by == 0 {
        // rare case
        return *word;
    }

    if rotate_by % 8 == 0 {
        // also easy case
        let rotate_bytes = rotate_by / 8;
        let mut tmp = *word;
        for (idx, src) in word.iter().enumerate() {
            tmp[(idx + rotate_bytes as usize) % BYTES_PER_WORD] = *src;
        }

        return tmp;
    }

    assert!(
        rotate_by % 8 != 0,
        "rotation is expected to be unaligned below, but rotation constant is {}",
        rotate_by
    );
    // we do not have trivial rorations
    let to_u32_constant = [
        F::ONE,
        F::from_u64_unchecked(1u64 << 8),
        F::from_u64_unchecked(1u64 << 16),
        F::from_u64_unchecked(1u64 << 24),
    ];

    let mut it = word.array_chunks::<4>();

    let low = ReductionGate::reduce_terms(cs, to_u32_constant, it.next().copied().unwrap());
    let high = ReductionGate::reduce_terms(cs, to_u32_constant, it.next().copied().unwrap());
    debug_assert!(it.next().is_none());
    debug_assert!(it.remainder().is_empty());

    // if we rotate by too much we swap words
    let mut rotate_by = rotate_by;
    let (low, high) = if rotate_by > 32 {
        rotate_by -= 32;
        (high, low)
    } else {
        (low, high)
    };

    debug_assert!(rotate_by > 0);
    debug_assert!(rotate_by < 32);

    // now we have a uniform procedure - we only chunk "unaligned" pieces, and declare presumable 8 bit
    let unalignment = rotate_by % 8;
    let aligned_shift_in_bytes_offset = (rotate_by / 8) + 1;

    // dbg!(unsafe { UInt32::from_variable_unchecked(low).witness_hook(&*cs)().unwrap() } );

    let (low_aligned, low_low_chunk, low_high_chunk) =
        split_for_unaligned_rotation(cs, low, one, unalignment);
    let (high_aligned, high_low_chunk, high_high_chunk) =
        split_for_unaligned_rotation(cs, high, one, unalignment);

    // since we cyclic rotate left, we merge like high-high with low-low, and then middle pieces

    let mid_byte = FmaGateInBaseFieldWithoutConstant::compute_fma(
        cs,
        F::from_u64_unchecked(1u64 << unalignment),
        (one, high_low_chunk),
        F::ONE,
        low_high_chunk,
    );

    let cyclic_byte = FmaGateInBaseFieldWithoutConstant::compute_fma(
        cs,
        F::from_u64_unchecked(1u64 << unalignment),
        (one, low_low_chunk),
        F::ONE,
        high_high_chunk,
    );

    // flatten them into array

    let mut result = [Variable::placeholder(); BYTES_PER_WORD];
    for (idx, el) in low_aligned.into_iter().enumerate() {
        let dst_idx = (idx + aligned_shift_in_bytes_offset as usize) % BYTES_PER_WORD;
        result[dst_idx] = el;
    }
    result[(BYTES_PER_WORD - 1 + aligned_shift_in_bytes_offset as usize) % BYTES_PER_WORD] =
        cyclic_byte;

    for (idx, el) in high_aligned.into_iter().enumerate() {
        let dst_idx =
            (idx + aligned_shift_in_bytes_offset as usize + (BYTES_PER_WORD / 2)) % BYTES_PER_WORD;
        result[dst_idx] = el;
    }
    result[(BYTES_PER_WORD - 1 + aligned_shift_in_bytes_offset as usize + (BYTES_PER_WORD / 2))
        % BYTES_PER_WORD] = mid_byte;

    assert_no_placeholder_variables(&result);

    result
}

fn split_byte_using_table_dyn<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Variable,
    split_at: u32,
) -> (Variable, Variable) {
    debug_assert!(split_at > 0);
    debug_assert!(split_at < 8);

    let mut swap = false;
    let mut split_at = split_at;
    if split_at > 4 {
        split_at = 8 - split_at;
        swap = true;
    }

    let (low, high) = match split_at {
        1 => split_byte_using_table::<_, _, 1>(cs, input),
        2 => split_byte_using_table::<_, _, 2>(cs, input),
        3 => split_byte_using_table::<_, _, 3>(cs, input),
        4 => split_byte_using_table::<_, _, 4>(cs, input),
        _ => unreachable!(),
    };

    let (low, high) = if swap { (high, low) } else { (low, high) };

    (low, high)
}

fn prove_split_byte_using_table_dyn<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    low: Variable,
    high: Variable,
    split_at: u32,
) {
    debug_assert!(split_at > 0);
    debug_assert!(split_at < 8);

    let _ = match split_at {
        1 => merge_byte_using_table::<_, _, 1>(cs, low, high),
        2 => merge_byte_using_table::<_, _, 2>(cs, low, high),
        3 => merge_byte_using_table::<_, _, 3>(cs, low, high),
        4 => merge_byte_using_table::<_, _, 4>(cs, low, high),
        5 => merge_byte_using_table::<_, _, 3>(cs, high, low),
        6 => merge_byte_using_table::<_, _, 2>(cs, high, low),
        7 => merge_byte_using_table::<_, _, 1>(cs, high, low),
        _ => unreachable!(),
    };
}

const MASK_8: u32 = (1u32 << 8) - 1;

fn split_for_unaligned_rotation<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Variable,
    one: Variable,
    unalignment: u32,
) -> ([Variable; 3], Variable, Variable) {
    let aligned_variables = cs.alloc_multiple_variables_without_values::<3>();
    let decompose_low = cs.alloc_variable_without_value();
    let decompose_high = cs.alloc_variable_without_value();

    debug_assert!(unalignment > 0);
    debug_assert!(unalignment < 8);

    let low_chunk_size = 8 - unalignment;

    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
        let value_fn = move |input: [F; 1]| {
            let mut input = <u32 as WitnessCastable<F, F>>::cast_from_source(input[0]);
            let lowest_mask = (1u32 << low_chunk_size) - 1;

            let mut result = [F::ZERO; 5];
            let lowest = input & lowest_mask;
            result[0] = F::from_u64_unchecked(lowest as u64);
            input >>= low_chunk_size;

            for dst in result[1..4].iter_mut() {
                let chunk = input & MASK_8;
                input >>= 8;
                *dst = F::from_u64_unchecked(chunk as u64);
            }

            let highest = input;
            debug_assert!(input < (1u32 << unalignment));
            result[4] = F::from_u64_unchecked(highest as u64);

            result
        };

        let outputs = Place::from_variables([
            decompose_low,
            aligned_variables[0],
            aligned_variables[1],
            aligned_variables[2],
            decompose_high,
        ]);
        cs.set_values_with_dependencies(&[input.into()], &outputs, value_fn);
    }

    // prove decomposition
    let mut coeffs = [F::ZERO; 4];
    let mut shift = 0;
    for (idx, dst) in coeffs.iter_mut().enumerate() {
        *dst = F::from_u64_unchecked(1u64 << shift);

        if idx == 0 {
            shift += low_chunk_size;
        } else {
            shift += 8;
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

    // use fma gate for rest
    let gate = FmaGateInBaseFieldWithoutConstant {
        params: FmaGateInBaseWithoutConstantParams {
            coeff_for_quadtaric_part: F::from_u64_unchecked(1u64 << shift),
            linear_term_coeff: F::ONE,
        },
        quadratic_part: (one, decompose_high),
        linear_part: t,
        rhs_part: input,
    };
    gate.add_to_cs(cs);

    // and range-check parts, because here are already prove decompostion and are ok with range check,
    // while if we would try to merge them in byte on upper level of rotation we would need to also have
    // split tables for splitting point > 4
    prove_split_byte_using_table_dyn(cs, decompose_low, decompose_high, low_chunk_size);

    (aligned_variables, decompose_low, decompose_high)
}

pub(crate) fn and_many<F: SmallField, CS: ConstraintSystem<F>, const N: usize>(
    cs: &mut CS,
    a: &[Variable; N],
    b: &[Variable; N],
) -> [Variable; N] {
    let table_id = cs
        .get_table_id_for_marker::<And8Table>()
        .expect("table must be added");
    let mut result = [Variable::placeholder(); N];

    for ((a, b), dst) in a.iter().zip(b.iter()).zip(result.iter_mut()) {
        let [xor] = cs.perform_lookup::<2, 1>(table_id, &[*a, *b]);
        *dst = xor;
    }

    result
}
