
use super::*;
use crate::algebraic_props::poseidon_parameters::PoseidonParameters;
use crate::config::*;
use crate::cs::gates::poseidon::PoseidonFlattenedGate;
use crate::cs::gates::{
    assert_no_placeholder_variables, ConstantAllocatableCS, MatrixMultiplicationGate,
};
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::cs::DstBuffer;
use crate::cs::Variable;
use crate::field::goldilocks::GoldilocksField;
use crate::field::SmallField;
use crate::gadgets::num::Num;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub enum PoseidonImplementationGatesParams {
    UseSpecializedGate,
    UseComposition {
        use_matrix_mul_gates: bool,
        use_non_linearity_gate: bool,
    }
}

use crate::implementations::poseidon_goldilocks::PoseidonGoldilocks;

impl CircuitRoundFunction<GoldilocksField, 8, 12, 4> for PoseidonGoldilocks {
    fn compute_round_function<CS: ConstraintSystem<GoldilocksField>>(
        cs: &mut CS,
        state: [Variable; 12],
    ) -> [Variable; 12] {
        if cs.gate_is_allowed::<PoseidonFlattenedGate<GoldilocksField, 8, 12, 4, PoseidonGoldilocks>>() {
            let a = state.array_chunks::<8>().next().copied().unwrap();
            let b = state[8..].array_chunks::<4>().next().copied().unwrap();
            PoseidonFlattenedGate::<GoldilocksField, 8, 12, 4, PoseidonGoldilocks>::compute_round_function(cs, a, b)
        } else {
            poseidon_goldilocks_not_unrolled(cs, state)
        }
    }

    fn absorb_with_replacement<CS: ConstraintSystem<GoldilocksField>>(
        _cs: &mut CS,
        elements_to_absorb: [Variable; 8],
        state_elements_to_keep: [Variable; 4],
    ) -> [Variable; 12] {
        let mut state = [Variable::placeholder(); 12];
        state[..8].copy_from_slice(&elements_to_absorb);
        state[8..].copy_from_slice(&state_elements_to_keep);
        assert_no_placeholder_variables(&state);

        state
    }

    fn enforce_round_function<CS: ConstraintSystem<GoldilocksField>>(
        cs: &mut CS,
        initial_state: [Variable; 12],
        final_state: [Variable; 12],
    ) {
        if cs.gate_is_allowed::<PoseidonFlattenedGate<GoldilocksField, 8, 12, 4, PoseidonGoldilocks>>() {
            PoseidonFlattenedGate::<GoldilocksField, 8, 12, 4, PoseidonGoldilocks>::enforce_round_function(cs, initial_state, final_state)
        } else {
            unimplemented!()
        }
    }
}

impl BuildableCircuitRoundFunction<GoldilocksField, 8, 12, 4> for PoseidonGoldilocks {
    fn configure_builder<
        T: CsBuilderImpl<GoldilocksField, T>,
        GC: GateConfigurationHolder<GoldilocksField>,
        TB: StaticToolboxHolder,
    >(
        builder: CsBuilder<T, GoldilocksField, GC, TB>,
        placement_strategy: GatePlacementStrategy,
    ) -> CsBuilder<
        T,
        GoldilocksField,
        impl GateConfigurationHolder<GoldilocksField>,
        impl StaticToolboxHolder,
    > {
        PoseidonFlattenedGate::<GoldilocksField, 8, 12, 4, PoseidonGoldilocks>::configure_builder(
            builder,
            placement_strategy,
        )
    }
}

fn poseidon_goldilocks_not_unrolled<CS: ConstraintSystem<GoldilocksField>>(
    cs: &mut CS,
    input: [Variable; 12],
) -> [Variable; 12] {
    assert!(
        cs.gate_is_allowed::<MatrixMultiplicationGate<GoldilocksField, 12, PoseidonGoldilocks>>()
    );
    assert_no_placeholder_variables(&input);

    // here we can do normal structure of poseidon as it doesn't matter too much

    let mut state = input;
    let mut round_counter = 0;
    for _ in 0..PoseidonGoldilocks::NUM_FULL_ROUNDS / 2 {
        poseidon_goldilocks_not_unrolled_full_round(cs, &mut state, &mut round_counter);
    }
    for _ in 0..PoseidonGoldilocks::NUM_PARTIAL_ROUNDS {
        poseidon_goldilocks_not_unrolled_partial_round(cs, &mut state, &mut round_counter);
    }
    for _ in 0..PoseidonGoldilocks::NUM_FULL_ROUNDS / 2 {
        poseidon_goldilocks_not_unrolled_full_round(cs, &mut state, &mut round_counter);
    }

    state
}

fn poseidon_goldilocks_not_unrolled_full_round<CS: ConstraintSystem<GoldilocksField>>(
    cs: &mut CS,
    state: &mut [Variable; 12],
    round_counter: &mut usize,
) {
    use crate::cs::gates::FmaGateInBaseFieldWithoutConstant;
    use crate::field::traits::field::Field;

    // add constants
    // apply non-linearity
    // multiply by MDS

    // we may create a gate that is add constant + apply non-linearity all at once,
    // but for how we just use FMA gate

    let one_variable = cs.allocate_constant(GoldilocksField::ONE);

    let round_constants = &PoseidonGoldilocks::all_round_constants()[*round_counter];
    // with FMA of the form c0 * A * B + c1 * D and we can not make a term of (A + k) ^ k

    for (a, b) in state.iter_mut().zip(round_constants.iter()) {
        *a = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            GoldilocksField::ONE,
            (one_variable, *a),
            *b,
            one_variable,
        );
    }

    // now just raise to the power
    debug_assert_eq!(PoseidonGoldilocks::NONLINEARITY_DEGREE, 7);

    for dst in state.iter_mut() {
        let square = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            GoldilocksField::ONE,
            (*dst, *dst),
            GoldilocksField::ZERO,
            one_variable,
        );

        let third = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            GoldilocksField::ONE,
            (square, *dst),
            GoldilocksField::ZERO,
            one_variable,
        );

        let quad = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            GoldilocksField::ONE,
            (square, square),
            GoldilocksField::ZERO,
            one_variable,
        );

        *dst = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            GoldilocksField::ONE,
            (quad, third),
            GoldilocksField::ZERO,
            one_variable,
        );
    }

    *state =
        MatrixMultiplicationGate::<GoldilocksField, 12, PoseidonGoldilocks>::compute_multiplication(
            cs, *state,
        );

    *round_counter += 1;
}

fn poseidon_goldilocks_not_unrolled_partial_round<CS: ConstraintSystem<GoldilocksField>>(
    cs: &mut CS,
    state: &mut [Variable; 12],
    round_counter: &mut usize,
) {
    use crate::cs::gates::FmaGateInBaseFieldWithoutConstant;
    use crate::field::traits::field::Field;

    // add constants
    // apply non-linearity
    // multiply by MDS

    // we may create a gate that is add constant + apply non-linearity all at once,
    // but for how we just use FMA gate

    let one_variable = cs.allocate_constant(GoldilocksField::ONE);

    let round_constants = &PoseidonGoldilocks::all_round_constants()[*round_counter];
    // with FMA of the form c0 * A * B + c1 * D and we can not make a term of (A + k) ^ k

    for (a, b) in state.iter_mut().zip(round_constants.iter()) {
        *a = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            GoldilocksField::ONE,
            (one_variable, *a),
            *b,
            one_variable,
        );
    }

    // now just raise to the power
    debug_assert_eq!(PoseidonGoldilocks::NONLINEARITY_DEGREE, 7);

    // only first element undergoes non-linearity
    {
        let dst = &mut state[0];
        let square = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            GoldilocksField::ONE,
            (*dst, *dst),
            GoldilocksField::ZERO,
            one_variable,
        );

        let third = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            GoldilocksField::ONE,
            (square, *dst),
            GoldilocksField::ZERO,
            one_variable,
        );

        let quad = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            GoldilocksField::ONE,
            (square, square),
            GoldilocksField::ZERO,
            one_variable,
        );

        *dst = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            GoldilocksField::ONE,
            (quad, third),
            GoldilocksField::ZERO,
            one_variable,
        );
    }

    *state =
        MatrixMultiplicationGate::<GoldilocksField, 12, PoseidonGoldilocks>::compute_multiplication(
            cs, *state,
        );

    *round_counter += 1;
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cs::gates::*;
    use crate::cs::implementations::reference_cs::CSReferenceImplementation;
    use crate::field::traits::field::Field;
    use crate::worker::Worker;

    type F = GoldilocksField;

    #[test]
    fn test_poseidon_not_unrolled_by_matrix_gates() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 80,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 8,
        };

        let owned_cs = CSReferenceImplementation::<F, F, DevCSConfig, _, _>::new_for_geometry(
            geometry,
            1 << 20,
            1 << 16,
        );

        let owned_cs = ConstantsAllocatorGate::configure_builder(
            owned_cs,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let owned_cs = FmaGateInBaseFieldWithoutConstant::configure_builder(
            owned_cs,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let owned_cs = MatrixMultiplicationGate::<F, 12, PoseidonGoldilocks>::configure_builder(
            owned_cs,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let owned_cs =
            NopGate::configure_builder(owned_cs, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = owned_cs;

        let cs = &mut owned_cs;

        let mut inputs = [Variable::placeholder(); 12];
        let mut state = [F::ZERO; 12];
        for (idx, dst) in inputs[..8].iter_mut().enumerate() {
            let value = F::from_u64_with_reduction(idx as u64);
            let var = cs.alloc_single_variable_from_witness(value);
            state[idx] = value;
            *dst = var;
        }

        let capacity_var = cs.allocate_constant(F::ZERO);
        for dst in inputs[8..].iter_mut() {
            *dst = capacity_var;
        }

        let round_function_result = PoseidonGoldilocks::compute_round_function(cs, inputs);

        use crate::implementations::poseidon_goldilocks::*;
        poseidon_permutation(&mut state);

        log!("Out of circuit result = {:?}", state);

        let circuit_result = cs
            .get_value_for_multiple(Place::from_variables(round_function_result))
            .wait()
            .unwrap();

        log!("Circuit result = {:?}", circuit_result);

        assert_eq!(circuit_result, state);

        drop(cs);
        owned_cs.pad_and_shrink();

        let worker = Worker::new();

        log!("Checking if satisfied");

        assert!(owned_cs.check_if_satisfied(&worker));
    }
}
