use super::*;
use crate::{
    cs::gates::{ReductionGate, ReductionGateParams, UIntXAddGate},
    gadgets::{boolean::Boolean, num::Num, traits::selectable::Selectable},
};
use crypto_bigint::U1024;

pub(crate) fn fe_to_u16_words<T: pairing::ff::PrimeField, const N: usize>(src: &T) -> [u16; N] {
    let mut result = [0u16; N];
    let repr = src.into_repr();
    for (idx, el) in repr.as_ref().iter().enumerate() {
        let mut el = *el;
        let a = (el & (u16::MAX as u64)) as u16;
        el >>= 16;
        let b = (el & (u16::MAX as u64)) as u16;
        el >>= 16;
        let c = (el & (u16::MAX as u64)) as u16;
        el >>= 16;
        let d = (el & (u16::MAX as u64)) as u16;

        if 4 * idx < N {
            result[4 * idx] = a;
        } else {
            debug_assert_eq!(a, 0);
        }
        if 4 * idx + 1 < N {
            result[4 * idx + 1] = b;
        } else {
            debug_assert_eq!(b, 0);
        }
        if 4 * idx + 2 < N {
            result[4 * idx + 2] = c;
        } else {
            debug_assert_eq!(c, 0);
        }
        if 4 * idx + 3 < N {
            result[4 * idx + 3] = d;
        } else {
            debug_assert_eq!(d, 0);
        }
    }

    result
}

pub fn u16_words_to_u1024(words: &[u16]) -> U1024 {
    let mut result = U1024::ZERO;
    let mut i = 0;
    let mut it = words.array_chunks::<4>();
    for chunk in &mut it {
        let mut tmp = chunk[3] as u64;
        tmp <<= 16;
        tmp |= chunk[2] as u64;
        tmp <<= 16;
        tmp |= chunk[1] as u64;
        tmp <<= 16;
        tmp |= chunk[0] as u64;

        result.as_words_mut()[i] = tmp;
        i += 1;
    }

    let remainder = it.remainder();
    if remainder.is_empty() == false {
        let mut shift = 0;
        let mut tmp = 0u64;
        for el in remainder.iter() {
            tmp |= (*el as u64) << shift;
            shift += 16;
        }
        result.as_words_mut()[i] = tmp;
    }

    result
}

pub fn unnormalized_u16_field_words_to_u1024<F: SmallField>(words: &[F]) -> U1024 {
    let mut result = U1024::ZERO;
    let mut shift = 0;
    for el in words.iter() {
        let as_u1024 = U1024::from_word(el.as_u64_reduced());
        let as_u1024 = as_u1024.shl_vartime(shift);
        result = result.saturating_add(&as_u1024);
        shift += 16;
    }

    result
}

pub fn u16_field_words_to_u1024<F: SmallField>(words: &[F]) -> U1024 {
    let mut result = U1024::ZERO;
    let mut i = 0;
    let mut it = words.array_chunks::<4>();
    for chunk in &mut it {
        let mut tmp = chunk[3].as_u64_reduced();
        tmp <<= 16;
        tmp |= chunk[2].as_u64_reduced();
        tmp <<= 16;
        tmp |= chunk[1].as_u64_reduced();
        tmp <<= 16;
        tmp |= chunk[0].as_u64_reduced();

        result.as_words_mut()[i] = tmp;
        i += 1;
    }

    let remainder = it.remainder();
    if remainder.is_empty() == false {
        let mut shift = 0;
        let mut tmp = 0u64;
        for el in remainder.iter() {
            tmp |= el.as_u64_reduced() << shift;
            shift += 16;
        }
        result.as_words_mut()[i] = tmp;
    }

    result
}

pub fn u16_long_subtraction<F: SmallField, CS: ConstraintSystem<F>, const N: usize>(
    cs: &mut CS,
    a: &[Variable; N],
    b: &[Variable; N],
) -> ([Variable; N], Boolean<F>) {
    let mut borrow = Boolean::allocated_constant(cs, false);
    let mut result = [Variable::placeholder(); N];
    for ((a, b), dst) in a.iter().zip(b.iter()).zip(result.iter_mut()) {
        let (c, new_borrow) = UIntXAddGate::<16>::perform_subtraction(cs, *a, *b, borrow.variable);
        range_check_u16(cs, c);
        *dst = c;
        borrow = unsafe { Boolean::from_variable_unchecked(new_borrow) };
    }

    (result, borrow)
}

pub fn u16_long_subtraction_noborrow<F: SmallField, CS: ConstraintSystem<F>, const N: usize>(
    cs: &mut CS,
    a: &[Variable; N],
    b: &[Variable; N],
    top_els_to_skip: usize,
) -> [Variable; N] {
    assert!(top_els_to_skip < N - 1); // at least some useful work
    let constant_false = Boolean::allocated_constant(cs, false);
    let mut borrow = constant_false;
    let mut result = [constant_false.variable; N];
    let work_size = N - top_els_to_skip;
    for (idx, ((a, b), dst)) in a[..work_size]
        .iter()
        .zip(b[..work_size].iter())
        .zip(result[..work_size].iter_mut())
        .enumerate()
    {
        let is_last = idx == work_size - 1;
        if is_last == false {
            // subtract with borrow
            let (c, new_borrow) =
                UIntXAddGate::<16>::perform_subtraction(cs, *a, *b, borrow.variable);
            range_check_u16(cs, c);
            *dst = c;
            borrow = unsafe { Boolean::from_variable_unchecked(new_borrow) };
        } else {
            // final one without borrow
            let c = UIntXAddGate::<16>::perform_subtraction_with_expected_borrow_out(
                cs,
                *a,
                *b,
                borrow.variable,
                constant_false.variable,
                constant_false.variable,
            );
            range_check_u16(cs, c);
            *dst = c;
        }
    }

    let zero = Num::allocated_constant(cs, F::ZERO);

    for (a, b) in a[work_size..].iter().zip(b[work_size..].iter()) {
        Num::enforce_equal(cs, &Num::from_variable(*a), &zero);
        Num::enforce_equal(cs, &Num::from_variable(*b), &zero);
    }

    result
}

pub fn u16_long_subtraction_noborrow_must_borrow<
    F: SmallField,
    CS: ConstraintSystem<F>,
    const N: usize,
>(
    cs: &mut CS,
    a: &[Variable; N],
    b: &[Variable; N],
    top_els_to_skip: usize,
) -> [Variable; N] {
    assert!(top_els_to_skip < N - 1); // at least some useful work
    let constant_false = Boolean::allocated_constant(cs, false);
    let constant_true = Boolean::allocated_constant(cs, true);
    let mut borrow = constant_false;
    let mut result = [constant_false.variable; N];
    let work_size = N - top_els_to_skip;
    for (idx, ((a, b), dst)) in a[..work_size]
        .iter()
        .zip(b[..work_size].iter())
        .zip(result[..work_size].iter_mut())
        .enumerate()
    {
        let is_last = idx == work_size - 1;
        if is_last == false {
            // subtract with borrow
            let (c, new_borrow) =
                UIntXAddGate::<16>::perform_subtraction(cs, *a, *b, borrow.variable);
            range_check_u16(cs, c);
            *dst = c;
            borrow = unsafe { Boolean::from_variable_unchecked(new_borrow) };
        } else {
            // final one without borrow
            let c = UIntXAddGate::<16>::perform_subtraction_with_expected_borrow_out(
                cs,
                *a,
                *b,
                borrow.variable,
                constant_false.variable,
                constant_true.variable,
            );
            range_check_u16(cs, c);
            *dst = c;
        }
    }

    let zero = Num::allocated_constant(cs, F::ZERO);

    for (a, b) in a[work_size..].iter().zip(b[work_size..].iter()) {
        Num::enforce_equal(cs, &Num::from_variable(*a), &zero);
        Num::enforce_equal(cs, &Num::from_variable(*b), &zero);
    }

    result
}

pub fn split_out_u32_carry_from_zero_low<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    lhs: Variable,
    rhs: Variable,
) -> (Boolean<F>, (Variable, Variable)) {
    debug_assert!(F::CAPACITY_BITS >= 48);
    let outputs = cs.alloc_multiple_variables_without_values::<3>();
    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
        let value_fn = move |input: [F; 2]| {
            let mut diff = input[0];
            diff.sub_assign(&input[1]);

            let (swap, mut diff) = if diff.as_u64_reduced() % (1u64 << 16) == 0 {
                (false, diff.as_u64_reduced() >> 16)
            } else {
                diff.negate();
                if diff.as_u64_reduced() % (1u64 << 16) == 0 {
                    (true, diff.as_u64_reduced() >> 16)
                } else {
                    unreachable!(
                        "lhs and rhs do not have same lowest 16 bits: LHS = {}, RHS = {}",
                        input[0], input[1]
                    );
                }
            };

            let low = diff as u16;
            diff >>= 16;
            let high = diff as u16;
            diff >>= 16;
            debug_assert_eq!(diff, 0);
            [
                F::from_u64_unchecked(swap as u64),
                F::from_u64_unchecked(low as u64),
                F::from_u64_unchecked(high as u64),
            ]
        };

        cs.set_values_with_dependencies(
            &Place::from_variables([lhs, rhs]),
            &Place::from_variables(outputs),
            value_fn,
        );
    }

    let [swap, low, high] = outputs;

    let swap = Boolean::from_variable_checked(cs, swap);
    range_check_u16(cs, low);
    range_check_u16(cs, high);

    // if we do not swap, then (lhs - rhs) >> 16 == high || low,
    // otherwise (rhs - lhs) >> 16 == high || low

    // enfore equality

    let zero = cs.allocate_constant(F::ZERO);

    let new_lhs = Selectable::conditionally_select(
        cs,
        swap,
        &Num::from_variable(rhs),
        &Num::from_variable(lhs),
    )
    .get_variable();

    let new_rhs = Selectable::conditionally_select(
        cs,
        swap,
        &Num::from_variable(lhs),
        &Num::from_variable(rhs),
    )
    .get_variable();

    // NOTE: because we want LHS - RHS = low << 16 + high << 32, note the signs below

    let gate = ReductionGate::<F, 4> {
        params: ReductionGateParams {
            reduction_constants: [
                F::MINUS_ONE,
                F::ONE,
                F::from_u64_unchecked(1u64 << 16),
                F::from_u64_unchecked(1u64 << 32),
            ],
        },
        terms: [new_lhs, new_rhs, low, high],
        reduction_result: zero,
    };
    gate.add_to_cs(cs);

    (swap, (low, high))
}

#[track_caller]
pub fn u1024_to_fe<T: pairing::ff::PrimeField>(input: &U1024) -> T {
    let mut modulus_u1024 = U1024::ZERO;
    for (dst, src) in modulus_u1024
        .as_words_mut()
        .iter_mut()
        .zip(T::char().as_ref())
    {
        *dst = *src;
    }

    assert!(input < &modulus_u1024);

    let mut repr = T::Repr::default();
    for (dst, src) in repr.as_mut().iter_mut().zip(input.as_words().iter()) {
        *dst = *src;
    }

    T::from_repr(repr).expect("is valid representation")
}

#[track_caller]
pub fn u1024_to_u16_words<const N: usize>(input: &U1024) -> [u16; N] {
    let mut result = [0u16; N];
    let mut tmp = *input;
    for dst in result.iter_mut() {
        let low = tmp.as_words()[0];
        *dst = low as u16;

        tmp = tmp.shr_vartime(16);
    }

    assert!(tmp.is_zero().unwrap_u8() == 1);

    result
}
