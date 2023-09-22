use crate::{
    cs::{
        gates::{
            ConstantAllocatableCS, FmaGateInBaseFieldWithoutConstant,
            FmaGateInBaseWithoutConstantParams, ReductionGate, ReductionGateParams,
        },
        traits::cs::ConstraintSystem,
    },
    field::SmallField,
};

use crate::cs::Variable;

pub fn linear_combination_collapse<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: &mut impl ExactSizeIterator<Item = (Variable, F)>,
    extra: Option<Variable>,
) {
    // if we collapse linear combination then in "extra" we should have a logical output,
    // or any other variable that would have -1 coefficient in the original LC that would be collapsed into 0

    debug_assert!(input.len() > 0);

    let input_len = input.len();
    linear_combination_collapse_with_length(cs, input, extra, input_len);
}

pub fn linear_combination_collapse_with_length<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: &mut impl Iterator<Item = (Variable, F)>,
    extra: Option<Variable>,
    input_len: usize,
) {
    // if we collapse linear combination then in "extra" we should have a logical output,
    // or any other variable that would have -1 coefficient in the original LC that would be collapsed into 0

    debug_assert!(input_len > 0);

    if input_len == 1 {
        let (var, coeff) = input.next().unwrap();
        debug_assert!(input.next().is_none());

        let one = cs.allocate_constant(F::ONE);
        let final_var = extra.unwrap_or(cs.allocate_constant(F::ZERO));

        let gate = FmaGateInBaseFieldWithoutConstant {
            params: FmaGateInBaseWithoutConstantParams {
                coeff_for_quadtaric_part: coeff,
                linear_term_coeff: F::ZERO,
            },
            quadratic_part: (var, one),
            linear_part: one,
            rhs_part: final_var,
        };

        gate.add_to_cs(cs);
        // FMA is enough
    } else if input_len == 2 {
        let (var0, coeff0) = input.next().unwrap();
        let (var1, coeff1) = input.next().unwrap();
        debug_assert!(input.next().is_none());

        let one = cs.allocate_constant(F::ONE);
        let final_var = extra.unwrap_or(cs.allocate_constant(F::ZERO));

        let gate = FmaGateInBaseFieldWithoutConstant {
            params: FmaGateInBaseWithoutConstantParams {
                coeff_for_quadtaric_part: coeff0,
                linear_term_coeff: coeff1,
            },
            quadratic_part: (var0, one),
            linear_part: var1,
            rhs_part: final_var,
        };

        gate.add_to_cs(cs);
        // FMA is also enough
    } else if cs.gate_is_allowed::<ReductionGate<F, 4>>() {
        linear_combination_collapse_with_reduction_gate(cs, input, extra, input_len);
    } else {
        unimplemented!()
    }
}

fn linear_combination_collapse_with_reduction_gate<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: &mut impl Iterator<Item = (Variable, F)>,
    extra: Option<Variable>,
    mut input_len: usize,
) {
    debug_assert!(cs.gate_is_allowed::<ReductionGate<F, 4>>());
    debug_assert!(
        input_len >= 3,
        "function is intended for length 3 and more, while got {}",
        input_len
    );

    // gate always has output var, so we either link it into 0 or requested var
    let mut tmp_var = None;

    if input_len == 3 {
        // single possible "short" case
        let (v0, c0) = input.next().unwrap();
        let (v1, c1) = input.next().unwrap();
        let (v2, c2) = input.next().unwrap();
        debug_assert!(input.next().is_none());

        let zero = cs.allocate_constant(F::ZERO);

        // if it's the only step then we use the final var
        let final_var = extra.unwrap_or(zero);

        let gate = ReductionGate {
            params: ReductionGateParams {
                reduction_constants: [c0, c1, c2, F::ZERO],
            },
            terms: [v0, v1, v2, zero],
            reduction_result: final_var,
        };

        gate.add_to_cs(cs);

        return;
    } else if input_len >= 4 {
        input_len -= 4;
        let (v0, c0) = input.next().unwrap();
        let (v1, c1) = input.next().unwrap();
        let (v2, c2) = input.next().unwrap();
        let (v3, c3) = input.next().unwrap();

        if input_len == 0 {
            // length is exactly 4, we do not need more steps
            debug_assert!(input.next().is_none());

            // if it's the only step then we use the final var
            let final_var = extra.unwrap_or(cs.allocate_constant(F::ZERO));

            let gate = ReductionGate {
                params: ReductionGateParams {
                    reduction_constants: [c0, c1, c2, c3],
                },
                terms: [v0, v1, v2, v3],
                reduction_result: final_var,
            };

            gate.add_to_cs(cs);
            // we are done
            return;
        } else {
            // length is larger, we need intermediate variable to continue chain
            let intermediate = ReductionGate::reduce_terms(cs, [c0, c1, c2, c3], [v0, v1, v2, v3]);
            debug_assert!(tmp_var.is_none());
            tmp_var = Some(intermediate);

            // we continue
        }

        debug_assert!(tmp_var.is_some());

        while input_len >= 3 {
            input_len -= 3;

            let (v0, c0) = input.next().unwrap();
            let (v1, c1) = input.next().unwrap();
            let (v2, c2) = input.next().unwrap();

            let starting_el = tmp_var.take().unwrap_or(cs.allocate_constant(F::ZERO));

            if input_len == 0 {
                // short circuit final step
                debug_assert!(input.next().is_none());

                // if it's the only step then we use the final var
                let final_var = extra.unwrap_or(cs.allocate_constant(F::ZERO));

                let gate = ReductionGate {
                    params: ReductionGateParams {
                        reduction_constants: [F::ONE, c0, c1, c2],
                    },
                    terms: [starting_el, v0, v1, v2],
                    reduction_result: final_var,
                };

                gate.add_to_cs(cs);
                // we are done
                return;
            } else {
                // continue the chain
                let intermediate = ReductionGate::reduce_terms(
                    cs,
                    [F::ONE, c0, c1, c2],
                    [starting_el, v0, v1, v2],
                );
                debug_assert!(tmp_var.is_none());
                tmp_var = Some(intermediate);

                // we continue
            }
        }
    }

    // length is < 3 and we already did few reduction steps
    debug_assert!(tmp_var.is_some());

    assert!(input_len == 1 || input_len == 2);

    let starting_el = tmp_var.take().unwrap();

    if input_len == 1 {
        let (var, coeff) = input.next().unwrap();
        debug_assert!(input.next().is_none());

        let one = cs.allocate_constant(F::ONE);

        // if it's the only step then we use the final var
        let final_var = extra.unwrap_or(cs.allocate_constant(F::ZERO));

        let gate = FmaGateInBaseFieldWithoutConstant {
            params: FmaGateInBaseWithoutConstantParams {
                coeff_for_quadtaric_part: coeff,
                linear_term_coeff: F::ONE,
            },
            quadratic_part: (var, one),
            linear_part: starting_el,
            rhs_part: final_var,
        };

        gate.add_to_cs(cs);
        // FMA is enough
    } else if input_len == 2 {
        // do it by reduction
        let (v0, c0) = input.next().unwrap();
        let (v1, c1) = input.next().unwrap();
        debug_assert!(input.next().is_none());

        // if it's the only step then we use the final var
        let final_var = extra.unwrap_or(cs.allocate_constant(F::ZERO));

        let one = cs.allocate_constant(F::ONE);

        let gate = ReductionGate {
            params: ReductionGateParams {
                reduction_constants: [F::ONE, F::ZERO, c0, c1],
            },
            terms: [starting_el, one, v0, v1],
            reduction_result: final_var,
        };

        gate.add_to_cs(cs);
    } else {
        unreachable!()
    }
}
