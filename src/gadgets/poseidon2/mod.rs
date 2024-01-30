use crate::cs::gates::{
    assert_no_placeholder_variables, ConstantAllocatableCS, FmaGateInBaseFieldWithoutConstant,
    MatrixMultiplicationGate, ReductionGate, SimpleNonlinearityGate,
};
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::Variable;
use crate::field::goldilocks::GoldilocksField;
use crate::field::Field;
use crate::gadgets::num::Num;

use crate::algebraic_props::poseidon2_parameters::{
    Poseidon2GoldilocksExternalMatrix, Poseidon2GoldilocksInnerMatrix, Poseidon2Parameters,
};
use crate::cs::gates::Poseidon2FlattenedGate;
use crate::gadgets::traits::round_function::CircuitRoundFunction;
use crate::implementations::poseidon2::Poseidon2Goldilocks;

impl CircuitRoundFunction<GoldilocksField, 8, 12, 4> for Poseidon2Goldilocks {
    fn compute_round_function<CS: ConstraintSystem<GoldilocksField>>(
        cs: &mut CS,
        state: [Variable; 12],
    ) -> [Variable; 12] {
        if cs.gate_is_allowed::<Poseidon2FlattenedGate<GoldilocksField, 8, 12, 4, Poseidon2Goldilocks>>() {
            let a = state.array_chunks::<8>().next().copied().unwrap();
            let b = state[8..].array_chunks::<4>().next().copied().unwrap();
            Poseidon2FlattenedGate::<GoldilocksField, 8, 12, 4, Poseidon2Goldilocks>::compute_round_function(cs, a, b)
        } else {
            poseidon2_goldilocks_not_unrolled(cs, state)
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
        if cs.gate_is_allowed::<Poseidon2FlattenedGate<GoldilocksField, 8, 12, 4, Poseidon2Goldilocks>>() {
            Poseidon2FlattenedGate::<GoldilocksField, 8, 12, 4, Poseidon2Goldilocks>::enforce_round_function(cs, initial_state, final_state)
        } else {
            unimplemented!()
        }
    }
}

use crate::cs::cs_builder::*;
use crate::cs::*;
use crate::gadgets::poseidon2::gates::NextGateCounterWithoutParams;
use crate::gadgets::poseidon2::traits::gate::GatePlacementStrategy;
use crate::gadgets::traits::configuration::*;
use crate::gadgets::traits::round_function::BuildableCircuitRoundFunction;

impl BuildableCircuitRoundFunction<GoldilocksField, 8, 12, 4> for Poseidon2Goldilocks {
    type GateConfiguration<GC: GateConfigurationHolder<GoldilocksField>> = (
        GateTypeEntry<
            GoldilocksField,
            Poseidon2FlattenedGate<GoldilocksField, 8, 12, 4, Poseidon2Goldilocks>,
            NextGateCounterWithoutParams,
        >,
        GC,
    );
    type Toolbox<TB: StaticToolboxHolder> = TB;

    fn configure_builder<
        T: CsBuilderImpl<GoldilocksField, T>,
        GC: GateConfigurationHolder<GoldilocksField>,
        TB: StaticToolboxHolder,
    >(
        builder: CsBuilder<T, GoldilocksField, GC, TB>,
        placement_strategy: GatePlacementStrategy,
    ) -> CsBuilder<T, GoldilocksField, Self::GateConfiguration<GC>, Self::Toolbox<TB>> {
        Poseidon2FlattenedGate::<GoldilocksField, 8, 12, 4, Poseidon2Goldilocks>::configure_builder(
            builder,
            placement_strategy,
        )
    }

    // matrix multiplications, and non-linearity
    fn make_specialization_function_0() -> impl ConfigurationFunction<GoldilocksField> {
        let configuration_fn = IdentityConfiguration::new();
        let configuration_fn = configuration_fn.add_confituration_step::<MatrixMultiplicationGate<
            _,
            12,
            Poseidon2GoldilocksExternalMatrix,
        >>();
        let configuration_fn = configuration_fn.add_confituration_step::<MatrixMultiplicationGate<
            _,
            12,
            Poseidon2GoldilocksInnerMatrix,
        >>();
        let configuration_fn =
            configuration_fn.add_confituration_step::<SimpleNonlinearityGate<_, 7>>();

        configuration_fn
    }

    // matrix multiplications only
    fn make_specialization_function_1() -> impl ConfigurationFunction<GoldilocksField> {
        let configuration_fn = IdentityConfiguration::new();
        let configuration_fn = configuration_fn.add_confituration_step::<MatrixMultiplicationGate<
            _,
            12,
            Poseidon2GoldilocksExternalMatrix,
        >>();
        let configuration_fn = configuration_fn.add_confituration_step::<MatrixMultiplicationGate<
            _,
            12,
            Poseidon2GoldilocksInnerMatrix,
        >>();

        configuration_fn
    }
}

// in case if we do not have unrolled gate
fn poseidon2_goldilocks_not_unrolled<CS: ConstraintSystem<GoldilocksField>>(
    cs: &mut CS,
    input: [Variable; 12],
) -> [Variable; 12] {
    // assert!(cs.gate_is_allowed::<MatrixMultiplicationGate<GoldilocksField, 12, PoseidonGoldilocks>>());
    assert_no_placeholder_variables(&input);

    // here we can do normal structure of poseidon as it doesn't matter too much

    let mut state = input;
    let mut round_counter = 0;

    // first external MDS
    mul_by_external_matrix(cs, &mut state);
    for _ in 0..Poseidon2Goldilocks::NUM_FULL_ROUNDS / 2 {
        poseidon2_goldilocks_not_unrolled_full_round(cs, &mut state, &mut round_counter);
    }
    round_counter -= Poseidon2Goldilocks::NUM_FULL_ROUNDS / 2;
    for _ in 0..Poseidon2Goldilocks::NUM_PARTIAL_ROUNDS {
        poseidon2_goldilocks_not_unrolled_partial_round(cs, &mut state, &mut round_counter);
    }
    round_counter -= Poseidon2Goldilocks::NUM_PARTIAL_ROUNDS;
    round_counter += Poseidon2Goldilocks::NUM_FULL_ROUNDS / 2;
    for _ in 0..Poseidon2Goldilocks::NUM_FULL_ROUNDS / 2 {
        poseidon2_goldilocks_not_unrolled_full_round(cs, &mut state, &mut round_counter);
    }

    state
}

fn mul_by_external_matrix<CS: ConstraintSystem<GoldilocksField>>(
    cs: &mut CS,
    state: &mut [Variable; 12],
) {
    if cs.gate_is_allowed::<MatrixMultiplicationGate<GoldilocksField, 12, Poseidon2GoldilocksExternalMatrix>>() {
        *state = MatrixMultiplicationGate::<GoldilocksField, 12, Poseidon2GoldilocksExternalMatrix>::compute_multiplication(
            cs,
            *state
        );
    } else if cs.gate_is_allowed::<ReductionGate<GoldilocksField, 4>>() {
        use crate::implementations::poseidon2::params::EXTERNAL_MDS_MATRIX_BLOCK;

        // compute block circuilant matrix block by block
        let mut tmp = [Variable::placeholder(); 12];
        // multiplication of 4-element words
        for (dst, src) in tmp.array_chunks_mut::<4>().zip(state.array_chunks::<4>()) {
            for (dst, coeffs) in dst.iter_mut().zip(EXTERNAL_MDS_MATRIX_BLOCK.iter()) {
                *dst = ReductionGate::reduce_terms(cs, *coeffs, *src);
            }
        }

        assert_no_placeholder_variables(&tmp);

        let [x0, x1, x2, x3,
            x4, x5, x6, x7,
            x8, x9, x10, x11] = tmp;

        let zero = cs.allocate_constant(GoldilocksField::ZERO);
        state[0] = ReductionGate::reduce_terms(
            cs,
            [GoldilocksField::TWO, GoldilocksField::ONE, GoldilocksField::ONE, GoldilocksField::ZERO],
            [x0, x4, x8, zero]
        );
        state[1] = ReductionGate::reduce_terms(
            cs,
            [GoldilocksField::TWO, GoldilocksField::ONE, GoldilocksField::ONE, GoldilocksField::ZERO],
            [x1, x5, x9, zero]
        );
        state[2] = ReductionGate::reduce_terms(
            cs,
            [GoldilocksField::TWO, GoldilocksField::ONE, GoldilocksField::ONE, GoldilocksField::ZERO],
            [x2, x6, x10, zero]
        );
        state[3] = ReductionGate::reduce_terms(
            cs,
            [GoldilocksField::TWO, GoldilocksField::ONE, GoldilocksField::ONE, GoldilocksField::ZERO],
            [x3, x7, x11, zero]
        );

        state[4] = ReductionGate::reduce_terms(
            cs,
            [GoldilocksField::TWO, GoldilocksField::ONE, GoldilocksField::ONE, GoldilocksField::ZERO],
            [x4, x0, x8, zero]
        );
        state[5] = ReductionGate::reduce_terms(
            cs,
            [GoldilocksField::TWO, GoldilocksField::ONE, GoldilocksField::ONE, GoldilocksField::ZERO],
            [x5, x1, x9, zero]
        );
        state[6] = ReductionGate::reduce_terms(
            cs,
            [GoldilocksField::TWO, GoldilocksField::ONE, GoldilocksField::ONE, GoldilocksField::ZERO],
            [x6, x2, x10, zero]
        );
        state[7] = ReductionGate::reduce_terms(
            cs,
            [GoldilocksField::TWO, GoldilocksField::ONE, GoldilocksField::ONE, GoldilocksField::ZERO],
            [x7, x3, x11, zero]
        );

        state[8] = ReductionGate::reduce_terms(
            cs,
            [GoldilocksField::TWO, GoldilocksField::ONE, GoldilocksField::ONE, GoldilocksField::ZERO],
            [x8, x0, x4, zero]
        );
        state[9] = ReductionGate::reduce_terms(
            cs,
            [GoldilocksField::TWO, GoldilocksField::ONE, GoldilocksField::ONE, GoldilocksField::ZERO],
            [x9, x1, x5, zero]
        );
        state[10] = ReductionGate::reduce_terms(
            cs,
            [GoldilocksField::TWO, GoldilocksField::ONE, GoldilocksField::ONE, GoldilocksField::ZERO],
            [x10, x2, x6, zero]
        );
        state[11] = ReductionGate::reduce_terms(
            cs,
            [GoldilocksField::TWO, GoldilocksField::ONE, GoldilocksField::ONE, GoldilocksField::ZERO],
            [x11, x3, x7, zero]
        );
    } else {
        unimplemented!()
    }
}

fn mul_by_inner_matrix<CS: ConstraintSystem<GoldilocksField>>(
    cs: &mut CS,
    state: &mut [Variable; 12],
) {
    if cs.gate_is_allowed::<MatrixMultiplicationGate<GoldilocksField, 12, Poseidon2GoldilocksInnerMatrix>>() {
        *state = MatrixMultiplicationGate::<GoldilocksField, 12, Poseidon2GoldilocksInnerMatrix>::compute_multiplication(
            cs,
            *state
        );
    } else if cs.gate_is_allowed::<ReductionGate<GoldilocksField, 4>>() {
        use crate::implementations::poseidon2::params::INNER_ROUNDS_MATRIX_DIAGONAL_ELEMENTS_MINUS_ONE;

        // make full linear combination
        let input: Vec<_> = state.iter().copied().zip(std::iter::repeat(GoldilocksField::ONE)).collect();

        let full_lc = Num::linear_combination(cs, &input).get_variable();
        let one_variable = cs.allocate_constant(GoldilocksField::ONE);

        // now FMA with every diagonal term

        for (dst, coeff) in state.iter_mut().zip(INNER_ROUNDS_MATRIX_DIAGONAL_ELEMENTS_MINUS_ONE.iter()) {
            *dst = FmaGateInBaseFieldWithoutConstant::compute_fma(
                cs,
                *coeff,
                (one_variable, *dst),
                GoldilocksField::ONE,
                full_lc
            );
        }

    } else {
        unimplemented!()
    }
}

fn poseidon2_goldilocks_apply_nonlinearity<CS: ConstraintSystem<GoldilocksField>>(
    cs: &mut CS,
    state: &mut [Variable; 12],
    full_round_counter: &usize,
) {
    // add constants
    // apply non-linearity

    if cs.gate_is_allowed::<SimpleNonlinearityGate<GoldilocksField, 7>>() {
        let round_constants = &Poseidon2Goldilocks::full_round_constants()[*full_round_counter];

        for (a, b) in state.iter_mut().zip(round_constants.iter()) {
            *a = SimpleNonlinearityGate::<GoldilocksField, 7>::apply_nonlinearity(cs, *a, *b);
        }
    } else {
        // we may create a gate that is add constant + apply non-linearity all at once,
        // but for how we just use FMA gate

        let one_variable = cs.allocate_constant(GoldilocksField::ONE);

        let round_constants = &Poseidon2Goldilocks::full_round_constants()[*full_round_counter];
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
        debug_assert_eq!(Poseidon2Goldilocks::NONLINEARITY_DEGREE, 7);

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
    }
}

fn poseidon2_goldilocks_not_unrolled_full_round<CS: ConstraintSystem<GoldilocksField>>(
    cs: &mut CS,
    state: &mut [Variable; 12],
    full_round_counter: &mut usize,
) {
    // add constants
    // apply non-linearity
    // multiply by MDS

    poseidon2_goldilocks_apply_nonlinearity(cs, state, full_round_counter);

    // Mul by external matrix

    mul_by_external_matrix(cs, state);

    *full_round_counter += 1;
}

fn poseidon2_goldilocks_not_unrolled_partial_round<CS: ConstraintSystem<GoldilocksField>>(
    cs: &mut CS,
    state: &mut [Variable; 12],
    partial_round_counter: &mut usize,
) {
    // add constants
    // apply non-linearity
    // multiply by MDS

    let round_constant = Poseidon2Goldilocks::inner_round_constants()[*partial_round_counter];

    // now just raise to the power
    debug_assert_eq!(Poseidon2Goldilocks::NONLINEARITY_DEGREE, 7);

    // only first element undergoes non-linearity
    {
        if cs.gate_is_allowed::<SimpleNonlinearityGate<GoldilocksField, 7>>() {
            state[0] = SimpleNonlinearityGate::<GoldilocksField, 7>::apply_nonlinearity(
                cs,
                state[0],
                round_constant,
            );
        } else {
            let one_variable = cs.allocate_constant(GoldilocksField::ONE);

            // with FMA of the form c0 * A * B + c1 * D and we can not make a term of (A + k) ^ k
            state[0] = FmaGateInBaseFieldWithoutConstant::compute_fma(
                cs,
                GoldilocksField::ONE,
                (one_variable, state[0]),
                round_constant,
                one_variable,
            );

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
    }

    mul_by_inner_matrix(cs, state);

    *partial_round_counter += 1;
}

#[cfg(test)]
mod test {
    use std::alloc::Global;

    use super::*;

    use crate::config::CSConfig;
    use crate::cs::gates::*;
    use crate::dag::CircuitResolverOpts;
    use crate::log;
    use crate::worker::Worker;

    type F = GoldilocksField;

    #[test]
    fn test_poseidon2_not_unrolled() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 80,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 8,
        };

        use crate::config::DevCSConfig;
        type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, 1 << 18);
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ReductionGate::<F, 4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(CircuitResolverOpts::new(1 << 20));

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

        let round_function_result = Poseidon2Goldilocks::compute_round_function(cs, inputs);

        use crate::implementations::poseidon2::*;
        poseidon2_permutation(&mut state);

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
        let mut owned_cs = owned_cs.into_assembly::<Global>();
        assert!(owned_cs.check_if_satisfied(&worker));
    }

    #[test]
    fn test_poseidon2_not_unrolled_by_matrix_gates() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 80,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 8,
        };

        use crate::config::DevCSConfig;
        type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, 1 << 18);
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            MatrixMultiplicationGate::<F, 12, Poseidon2GoldilocksExternalMatrix>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
        let builder =
            MatrixMultiplicationGate::<F, 12, Poseidon2GoldilocksInnerMatrix>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(CircuitResolverOpts::new(1 << 20));

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

        let round_function_result = Poseidon2Goldilocks::compute_round_function(cs, inputs);

        use crate::implementations::poseidon2::*;
        poseidon2_permutation(&mut state);

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
        let mut owned_cs = owned_cs.into_assembly::<Global>();
        assert!(owned_cs.check_if_satisfied(&worker));
    }
}
