use crate::config::*;
use crate::cs::gates::{
    ConstantAllocatableCS, FmaGateInBaseFieldWithoutConstant, FmaGateInBaseWithoutConstantParams,
};
use crate::cs::Variable;
use crate::cs::{
    gates::u32_tri_add_carry_as_chunk::U32TriAddCarryAsChunkGate, traits::cs::ConstraintSystem,
};
use crate::gadgets::tables::xor8::Xor8Table;
use crate::gadgets::traits::castable::WitnessCastable;
use crate::gadgets::u8::range_check_u8_pair;
use arrayvec::ArrayVec;

use super::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct Word<F: SmallField> {
    pub inner: [UInt8<F>; 4],
}

// we HARDCODE rotations here
// Rotations are 16, 12, 8 and 7. Rotations by 16 and 8 are "free", and rorations by 12 and 7 require extra
// decomposition

pub(crate) fn mixing_function_g<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    space: &mut [Word<F>; 16],
    space_idxes: [usize; 4],
    input_word_x: &Word<F>,
    input_word_y: &Word<F>,
) {
    let mut a = space[space_idxes[0]].inner.map(|el| el.variable);
    let mut b = space[space_idxes[1]].inner.map(|el| el.variable);
    // let mut c = space[space_idxes[2]].inner.map(|el| el.variable);
    let mut d = space[space_idxes[3]].inner.map(|el| el.variable);

    let zero_var = cs.allocate_constant(F::ZERO);
    let zero_word = [zero_var; 4];

    let mut all_to_constraint = ArrayVec::<Variable, 8>::new();

    // v[a] := (v[a] + v[b] + x) mod 2**w
    // v[d] := (v[d] ^ v[a]) >>> R1

    // first op has nice structure and rotation
    let (new_a, to_constraint) =
        tri_add_as_byte_chunks(cs, &a, &b, &input_word_x.inner.map(|el| el.variable));
    a = new_a;
    all_to_constraint.extend(to_constraint);
    // we immediatelly use it to XOR (that also does range checks),
    // and rotation by 16
    let not_shifted_d = xor_many(cs, &a, &d);

    d = [
        not_shifted_d[2],
        not_shifted_d[3],
        not_shifted_d[0],
        not_shifted_d[1],
    ];

    // v[c] := (v[c] + v[d])     mod 2**w
    // v[b] := (v[b] ^ v[c]) >>> R2

    // second op has unpleasant roration, but nevetheless
    let (new_c, to_constraint) = tri_add_as_byte_chunks(
        cs,
        &space[space_idxes[2]].inner.map(|el| el.variable),
        &d,
        &zero_word,
    );
    let mut c = new_c;
    all_to_constraint.extend(to_constraint);
    // here we have to rotate by 12 after xor, so we decompose, xor, and recompose

    let not_shifted_b = xor_many(cs, &b, &c);

    let mut not_shifted_b_chunks = [Variable::placeholder(); 8];
    for (dst, src) in not_shifted_b_chunks
        .array_chunks_mut::<2>()
        .zip(not_shifted_b.iter())
    {
        let (low, high) = split_byte_using_table::<_, _, 4>(cs, *src);
        *dst = [low, high];
    }

    let mut b_chunks_shifted_it = not_shifted_b_chunks
        .iter()
        .skip(3)
        .chain(not_shifted_b_chunks.iter().take(3));

    for dst in b.iter_mut() {
        // we "rotated" an iterator by odd number of steps,
        // so next one is "high" of the original byte, but it will become "low" here

        // Our shift/split is symmetric
        let low = *b_chunks_shifted_it.next().unwrap();
        let high = *b_chunks_shifted_it.next().unwrap();
        let assembled_b = merge_byte_using_table::<_, _, 4>(cs, low, high);
        *dst = assembled_b;
    }
    assert!(b_chunks_shifted_it.next().is_none());

    // v[a] := (v[a] + v[b] + y) mod 2**w
    // v[d] := (v[d] ^ v[a]) >>> R3

    // againt nice rotation
    let (new_a, to_constraint) =
        tri_add_as_byte_chunks(cs, &a, &b, &input_word_y.inner.map(|el| el.variable));
    a = new_a;
    all_to_constraint.extend(to_constraint);
    // we immediatelly use it to XOR (that also does range checks),
    // and rotation by 8
    let not_shifted_d = xor_many(cs, &a, &d);

    let d = [
        not_shifted_d[1],
        not_shifted_d[2],
        not_shifted_d[3],
        not_shifted_d[0],
    ];

    // v[c] := (v[c] + v[d])     mod 2**w
    // v[b] := (v[b] ^ v[c]) >>> R4

    // again op has unpleasant roration, but nevetheless
    let (new_c, to_constraint) = tri_add_as_byte_chunks(cs, &c, &d, &zero_word);
    c = new_c;
    all_to_constraint.extend(to_constraint);
    // here we have to rotate by 7 after xor, so we decompose, xor, and recompose

    let not_shifted_b = xor_many(cs, &b, &c);

    let mut not_shifted_b_chunks = [Variable::placeholder(); 8];
    for (dst, src) in not_shifted_b_chunks
        .array_chunks_mut::<2>()
        .zip(not_shifted_b.iter())
    {
        let (low, high) = split_byte_using_table::<_, _, 7>(cs, *src);
        *dst = [low, high];
    }

    let mut b_chunks_shifted_it = not_shifted_b_chunks
        .iter()
        .skip(1)
        .chain(not_shifted_b_chunks.iter().take(1));

    for dst in b.iter_mut() {
        // we "rotated" an iterator by odd number of steps,
        // so next one is "high" of the original byte, but it will become "low" here

        // Our shift/split is NOT symmetric, so we need to use another table here!
        let low = *b_chunks_shifted_it.next().unwrap();
        let high = *b_chunks_shifted_it.next().unwrap();
        let assembled_b = merge_byte_using_table::<_, _, 1>(cs, low, high);
        *dst = assembled_b;
    }
    assert!(b_chunks_shifted_it.next().is_none());

    // constraint final chunks from carries
    if all_to_constraint.len() > 0 {
        assert!(all_to_constraint.len() % 2 == 0);
        for _ in 0..(all_to_constraint.len() / 2) {
            let t0 = all_to_constraint.pop().unwrap();
            let t1 = all_to_constraint.pop().unwrap();

            range_check_u8_pair(cs, &[t0, t1]);
        }
    }

    // just assign. Bit lengths are constrainted by our decompositions/recompositions
    unsafe {
        let a = Word {
            inner: a.map(|el| UInt8::from_variable_unchecked(el)),
        };
        let b = Word {
            inner: b.map(|el| UInt8::from_variable_unchecked(el)),
        };
        let c = Word {
            inner: c.map(|el| UInt8::from_variable_unchecked(el)),
        };
        let d = Word {
            inner: d.map(|el| UInt8::from_variable_unchecked(el)),
        };

        space[space_idxes[0]] = a;
        space[space_idxes[1]] = b;
        space[space_idxes[2]] = c;
        space[space_idxes[3]] = d;
    }
}

fn tri_add_as_byte_chunks<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    a: &[Variable; 4],
    b: &[Variable; 4],
    c: &[Variable; 4],
) -> ([Variable; 4], ArrayVec<Variable, 2>) {
    if cs.gate_is_allowed::<U32TriAddCarryAsChunkGate>() {
        let (out, carry) = U32TriAddCarryAsChunkGate::perform_addition(cs, *a, *b, *c);

        let mut to_constraint = ArrayVec::new();
        to_constraint.push(carry);

        (out, to_constraint)
    } else {
        unimplemented!()
    }
}

pub fn xor_many<F: SmallField, CS: ConstraintSystem<F>, const N: usize>(
    cs: &mut CS,
    a: &[Variable; N],
    b: &[Variable; N],
) -> [Variable; N] {
    let table_id = cs
        .get_table_id_for_marker::<Xor8Table>()
        .expect("table must be added");
    let mut result = [Variable::placeholder(); N];

    for ((a, b), dst) in a.iter().zip(b.iter()).zip(result.iter_mut()) {
        let [xor] = cs.perform_lookup::<2, 1>(table_id, &[*a, *b]);
        *dst = xor;
    }

    result
}

fn split_byte_at<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Variable,
    split_at: usize,
) -> (Variable, Variable) {
    debug_assert!(split_at > 0);
    debug_assert!(split_at < 8);

    let [low, high] = cs.alloc_multiple_variables_without_values::<2>();
    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
        let value_fn = move |input: [F; 1]| {
            let input = <u8 as WitnessCastable<F, F>>::cast_from_source(input[0]);
            let mask = (1u8 << split_at) - 1;
            let low = input & mask;
            let high = input >> split_at;

            [
                F::from_u64_unchecked(low as u64),
                F::from_u64_unchecked(high as u64),
            ]
        };

        let dependencies = [input.into()];
        cs.set_values_with_dependencies(&dependencies, &[low.into(), high.into()], value_fn);
    }

    let one = cs.allocate_constant(F::ONE);

    if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == true {
        let gate = FmaGateInBaseFieldWithoutConstant {
            params: FmaGateInBaseWithoutConstantParams {
                coeff_for_quadtaric_part: F::from_u64_unchecked(1u64 << split_at),
                linear_term_coeff: F::ONE,
            },
            quadratic_part: (one, high),
            linear_part: low,
            rhs_part: input,
        };

        gate.add_to_cs(cs);
    }

    (low, high)
}

pub(crate) fn split_byte_using_table<
    F: SmallField,
    CS: ConstraintSystem<F>,
    const SPLIT_AT: usize,
>(
    cs: &mut CS,
    input: Variable,
) -> (Variable, Variable) {
    debug_assert!(SPLIT_AT > 0);
    debug_assert!(SPLIT_AT < 8);
    use crate::gadgets::tables::byte_split::ByteSplitTable;

    let table_id = cs
        .get_table_id_for_marker::<ByteSplitTable<SPLIT_AT>>()
        .expect("table must exist");
    let [low, high] = cs.perform_lookup::<1, 2>(table_id, &[input]);

    (low, high)
}

pub fn merge_byte_using_table<F: SmallField, CS: ConstraintSystem<F>, const SPLIT_AT: usize>(
    cs: &mut CS,
    low: Variable,
    high: Variable,
) -> Variable {
    debug_assert!(SPLIT_AT > 0);
    debug_assert!(SPLIT_AT < 8);

    let result = cs.alloc_variable_without_value();

    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
        let value_fn = move |input: [F; 2]| {
            let low = <u8 as WitnessCastable<F, F>>::cast_from_source(input[0]);
            let high = <u8 as WitnessCastable<F, F>>::cast_from_source(input[1]);
            debug_assert!(
                low < (1u8 << SPLIT_AT),
                "low is b{:08b} when we are merging at {}",
                low,
                SPLIT_AT
            );
            debug_assert!(
                high < (1u8 << (8 - SPLIT_AT)),
                "high is b{:08b} when we are merging at {}",
                high,
                SPLIT_AT
            );
            let result = (high << SPLIT_AT) | low;

            [F::from_u64_unchecked(result as u64)]
        };

        cs.set_values_with_dependencies(&[low.into(), high.into()], &[result.into()], value_fn);
    }

    use crate::gadgets::tables::byte_split::ByteSplitTable;

    let table_id = cs
        .get_table_id_for_marker::<ByteSplitTable<SPLIT_AT>>()
        .expect("table must exist");
    let _ = cs.enforce_lookup::<3>(table_id, &[result, low, high]);

    result
}
