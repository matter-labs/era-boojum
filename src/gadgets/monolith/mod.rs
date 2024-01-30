use crate::cs::gates::{
    assert_no_placeholder_variables, ConstantAllocatableCS, FmaGateInBaseFieldWithoutConstant,
    MatrixMultiplicationGate, ReductionGate, SimpleNonlinearityGate,
};
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::Variable;
use crate::field::mersenne::MersenneField;
use crate::field::Field;
use crate::gadgets::num::Num;

use crate::algebraic_props::monolith_parameters::{
    MonolithMersenneMatrix, MonolithParameters,
};
// use crate::cs::gates::Poseidon2FlattenedGate;
use crate::gadgets::traits::round_function::CircuitRoundFunction;
use crate::implementations::monolith::MonolithMersenne;
use crate::implementations::monolith::state_generic_impl::Monolith;
use crate::gadgets::tables::{MonolithSBox, MonolithSBoxUpperLimb};
use crate::log;

impl CircuitRoundFunction<
    MersenneField, 
    {MersenneField::SPONGE_RATE}, 
    {MersenneField::SPONGE_WIDTH}, 
    {MersenneField::SPONGE_CAPACITY}
> for MonolithMersenne {
    fn compute_round_function<CS: ConstraintSystem<MersenneField>>(
        cs: &mut CS,
        state: [Variable; MersenneField::SPONGE_WIDTH],
    ) -> [Variable; MersenneField::SPONGE_WIDTH] {
        monolith_mersenne_not_unrolled(cs, state)
    }

    fn absorb_with_replacement<CS: ConstraintSystem<MersenneField>>(
        _cs: &mut CS,
        elements_to_absorb: [Variable; MersenneField::SPONGE_RATE],
        state_elements_to_keep: [Variable; MersenneField::SPONGE_CAPACITY],
    ) -> [Variable; MersenneField::SPONGE_WIDTH] {
        let mut state = [Variable::placeholder(); MersenneField::SPONGE_WIDTH];
        state[..MersenneField::SPONGE_RATE].copy_from_slice(&elements_to_absorb);
        state[MersenneField::SPONGE_RATE..].copy_from_slice(&state_elements_to_keep);
        assert_no_placeholder_variables(&state);

        state
    }

    fn enforce_round_function<CS: ConstraintSystem<MersenneField>>(
        cs: &mut CS,
        initial_state: [Variable; MersenneField::SPONGE_WIDTH],
        final_state: [Variable; MersenneField::SPONGE_WIDTH],
    ) {
        unimplemented!()
    }
}

// use crate::cs::cs_builder::*;
// use crate::cs::*;
// use crate::gadgets::monolith::gates::NextGateCounterWithoutParams;
// use crate::gadgets::monolith::traits::gate::GatePlacementStrategy;
// use crate::gadgets::traits::configuration::*;
// use crate::gadgets::traits::round_function::BuildableCircuitRoundFunction;

// impl BuildableCircuitRoundFunction<
//     MersenneField, 
//     {MersenneField::SPONGE_RATE}, 
//     {MersenneField::SPONGE_WIDTH}, 
//     {MersenneField::SPONGE_CAPACITY}
// > for MonolithMersenne {
//     type GateConfiguration<GC: GateConfigurationHolder<MersenneField>> = (
//         GateTypeEntry<
//             MersenneField,
//             Poseidon2FlattenedGate<MersenneField, 8, 12, 4, MonolithMersenne>,
//             NextGateCounterWithoutParams,
//         >,
//         GC,
//     );
//     type Toolbox<TB: StaticToolboxHolder> = TB;

//     fn configure_builder<
//         T: CsBuilderImpl<MersenneField, T>,
//         GC: GateConfigurationHolder<MersenneField>,
//         TB: StaticToolboxHolder,
//     >(
//         builder: CsBuilder<T, MersenneField, GC, TB>,
//         placement_strategy: GatePlacementStrategy,
//     ) -> CsBuilder<T, MersenneField, Self::GateConfiguration<GC>, Self::Toolbox<TB>> {
//         Poseidon2FlattenedGate::<MersenneField, 8, 12, 4, MonolithMersenne>::configure_builder(
//             builder,
//             placement_strategy,
//         )
//     }

//     // matrix multiplications, and non-linearity
//     fn make_specialization_function_0() -> impl ConfigurationFunction<MersenneField> {
//         let configuration_fn = IdentityConfiguration::new();
//         let configuration_fn = configuration_fn.add_confituration_step::<MatrixMultiplicationGate<
//             _,
//             12,
//             MonolithMersenneExternalMatrix,
//         >>();
//         let configuration_fn = configuration_fn.add_confituration_step::<MatrixMultiplicationGate<
//             _,
//             12,
//             MonolithMersenneInnerMatrix,
//         >>();
//         let configuration_fn =
//             configuration_fn.add_confituration_step::<SimpleNonlinearityGate<_, 7>>();

//         configuration_fn
//     }

//     // matrix multiplications only
//     fn make_specialization_function_1() -> impl ConfigurationFunction<MersenneField> {
//         let configuration_fn = IdentityConfiguration::new();
//         let configuration_fn = configuration_fn.add_confituration_step::<MatrixMultiplicationGate<
//             _,
//             12,
//             MonolithMersenneExternalMatrix,
//         >>();
//         let configuration_fn = configuration_fn.add_confituration_step::<MatrixMultiplicationGate<
//             _,
//             12,
//             MonolithMersenneInnerMatrix,
//         >>();

//         configuration_fn
//     }
// }

// in case if we do not have unrolled gate
fn monolith_mersenne_not_unrolled<CS: ConstraintSystem<MersenneField>>(
    cs: &mut CS,
    input: [Variable; MersenneField::SPONGE_WIDTH],
) -> [Variable; MersenneField::SPONGE_WIDTH] {
    assert_no_placeholder_variables(&input);

    let mut state = input;
    // let mut round_counter = 0;

    concrete(cs, &mut state, MersenneField::ROUND_CONSTANTS_FIELD[0]);
    for rc in MersenneField::ROUND_CONSTANTS_FIELD.iter().skip(1) {
        bars(cs, &mut state);
        bricks(cs, &mut state);
        concrete(cs, &mut state, *rc);
    }

    state
}

fn bars<CS: ConstraintSystem<MersenneField>>(
    cs: &mut CS,
    state: &mut [Variable; MersenneField::SPONGE_WIDTH],
) {
    for i in 0..MonolithMersenne::NUM_BARS {
        if cs.gate_is_allowed::<ReductionGate<MersenneField, {MonolithMersenne::LOOKUP_NUM_LIMBS}>>() {
            // decompose into limbs
            let limbs: [Variable; MonolithMersenne::LOOKUP_NUM_LIMBS] = ReductionGate::decompose_into_limbs(
                cs, 
                MersenneField::from_u64_unchecked(1u64 << MonolithMersenne::LOOKUP_BITS), 
                state[i]
            );

            // apply lookup tables
            let table_id = cs
                .get_table_id_for_marker::<MonolithSBox>()
                .expect("table must be added");
            let table_id2 = cs
                .get_table_id_for_marker::<MonolithSBoxUpperLimb>()
                .expect("table must be added");
            let mut table_out = [Variable::placeholder(); MonolithMersenne::LOOKUP_NUM_LIMBS];

            for (a, dst) in limbs[..MonolithMersenne::LOOKUP_NUM_LIMBS-1].iter().zip(table_out[..MonolithMersenne::LOOKUP_NUM_LIMBS-1].iter_mut()) {
                let [xor] = cs.perform_lookup::<1, 1>(table_id, &[*a]);
                *dst = xor;
            }
            [table_out[MonolithMersenne::LOOKUP_NUM_LIMBS-1]] = cs.perform_lookup::<1, 1>(table_id2, &[limbs[MonolithMersenne::LOOKUP_NUM_LIMBS-1]]);

            // compose into result
            let mut coeffs = [MersenneField::ZERO; MonolithMersenne::LOOKUP_NUM_LIMBS];
            let mut shift = 0;
            for dst in coeffs.iter_mut() {
                *dst = MersenneField::from_u64_unchecked(1u64 << shift);
                shift += MonolithMersenne::LOOKUP_BITS;
            }

            state[i] = ReductionGate::reduce_terms(
                cs,
                coeffs,
                table_out
            );
    
        } else {
            unimplemented!()
        }
    }
}

fn bricks<CS: ConstraintSystem<MersenneField>>(
    cs: &mut CS,
    state: &mut [Variable; MersenneField::SPONGE_WIDTH],
) {
    for i in (1..MersenneField::SPONGE_WIDTH).rev() {
        let prev = state[i - 1];
        state[i] = FmaGateInBaseFieldWithoutConstant::compute_fma(
            cs,
            MersenneField::ONE,
            (prev, prev),
            MersenneField::ONE,
            state[i],
        );
    }
}

fn concrete<CS: ConstraintSystem<MersenneField>>(
    cs: &mut CS,
    state: &mut [Variable; MersenneField::SPONGE_WIDTH],
    round_constants: [MersenneField; MersenneField::SPONGE_WIDTH],
) {
    if cs.gate_is_allowed::<MatrixMultiplicationGate<MersenneField, {MersenneField::SPONGE_WIDTH}, MonolithMersenneMatrix>>() {
        *state = MatrixMultiplicationGate::<MersenneField, {MersenneField::SPONGE_WIDTH}, MonolithMersenneMatrix>::compute_multiplication(
            cs,
            *state
        );
        let one_variable = cs.allocate_constant(MersenneField::ONE);
        for (a, rc) in state.iter_mut().zip(round_constants.iter()) {
            *a = FmaGateInBaseFieldWithoutConstant::compute_fma(
                cs,
                MersenneField::ONE,
                (one_variable, *a),
                *rc,
                one_variable,
            );
        }
    } else {
        unimplemented!()
    }

}

#[cfg(test)]
mod test {
    use super::*;

    use crate::cs::traits::gate::GatePlacementStrategy;
    use crate::cs::{gates::*, CSGeometry, Place};
    use crate::gadgets::tables::{create_monolith_sbox_table, create_monolith_sbox_upper_limb_table};
    use crate::log;
    use crate::worker::Worker;

    type F = MersenneField;

    #[test]
    fn test_monolith_not_unrolled_by_matrix_gates() {
        const SPONGE_WIDTH: usize = 24;

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 80,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 8,
        };

        use crate::config::DevCSConfig;
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, 1 << 20, 1 << 18);
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = builder.allow_lookup(
            crate::cs::LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                width: 2,
                num_repetitions: 5,
                share_table_id: true,
            },
        );

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            MatrixMultiplicationGate::<F, SPONGE_WIDTH, MonolithMersenneMatrix>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
        let builder = ReductionGate::<F, {MonolithMersenne::LOOKUP_NUM_LIMBS}>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(());

        // add tables
        let table = create_monolith_sbox_table::<F, {MonolithMersenne::LOOKUP_BITS}>();
        owned_cs.add_lookup_table::<MonolithSBox, 2>(table);

        let table = create_monolith_sbox_upper_limb_table::<F, {MonolithMersenne::LOOKUP_BITS}>();
        owned_cs.add_lookup_table::<MonolithSBoxUpperLimb, 2>(table);

        let cs = &mut owned_cs;

        let mut inputs = [Variable::placeholder(); SPONGE_WIDTH];
        let mut state = [F::ZERO; SPONGE_WIDTH];
        for (idx, dst) in inputs[..F::SPONGE_RATE].iter_mut().enumerate() {
            let value = F::from_u64_with_reduction(idx as u64);
            let var = cs.alloc_single_variable_from_witness(value);
            state[idx] = value;
            *dst = var;
        }

        let capacity_var = cs.allocate_constant(F::ZERO);
        for dst in inputs[F::SPONGE_RATE..].iter_mut() {
            *dst = capacity_var;
        }

        let round_function_result = MonolithMersenne::compute_round_function(cs, inputs);

        state = F::monolith_permutation(state);

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
        let mut owned_cs = owned_cs.into_assembly();
        assert!(owned_cs.check_if_satisfied(&worker));
    }

    #[test]
    fn test_monolith_not_unrolled_bars() {
        const SPONGE_WIDTH: usize = 24;

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 80,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 8,
        };

        use crate::config::DevCSConfig;
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, 1 << 20, 1 << 18);
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = builder.allow_lookup(
            crate::cs::LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                width: 2,
                num_repetitions: 5,
                share_table_id: true,
            },
        );

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            MatrixMultiplicationGate::<F, SPONGE_WIDTH, MonolithMersenneMatrix>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
        let builder = ReductionGate::<F, {MonolithMersenne::LOOKUP_NUM_LIMBS}>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(());

        // add tables
        let table = create_monolith_sbox_table::<F, {MonolithMersenne::LOOKUP_BITS}>();
        owned_cs.add_lookup_table::<MonolithSBox, 2>(table);

        let table = create_monolith_sbox_upper_limb_table::<F, {MonolithMersenne::LOOKUP_BITS}>();
        owned_cs.add_lookup_table::<MonolithSBoxUpperLimb, 2>(table);

        let cs = &mut owned_cs;

        let mut inputs = [Variable::placeholder(); SPONGE_WIDTH];
        let mut state = [F::ZERO; SPONGE_WIDTH];
        for (idx, dst) in inputs[..F::SPONGE_RATE].iter_mut().enumerate() {
            let value = F::from_u64_with_reduction(idx as u64);
            let var = cs.alloc_single_variable_from_witness(value);
            state[idx] = value;
            *dst = var;
        }

        let capacity_var = cs.allocate_constant(F::ZERO);
        for dst in inputs[F::SPONGE_RATE..].iter_mut() {
            *dst = capacity_var;
        }

        // bars(cs, &mut inputs);
        // bricks(cs, &mut inputs);
        concrete(cs, &mut inputs, F::ROUND_CONSTANTS_FIELD[0]);
        bars(cs, &mut inputs);
        // bricks(cs, &mut inputs);
        // concrete(cs, &mut inputs, F::ROUND_CONSTANTS_FIELD[2]);
        // for rc in F::ROUND_CONSTANTS_FIELD.iter().skip(5) {
        //     bars(cs, &mut inputs);
        //     bricks(cs, &mut inputs);
        //     concrete(cs, &mut inputs, *rc);
        // }
        let round_function_result = inputs;

        let mut state_u64 = [0; F::SPONGE_WIDTH];
        for (out, inp) in state_u64.iter_mut().zip(state.iter()) {
            *out = inp.as_u64();
        }
        // F::bars_u64(&mut state_u64);
        // F::bricks_u64(&mut state_u64);
        F::concrete_u64(&mut state_u64, &F::ROUND_CONSTANTS[0]);
        F::bars_u64(&mut state_u64);
        // F::bricks_u64(&mut state_u64);
        // F::concrete_u64(&mut state_u64, &F::ROUND_CONSTANTS[2]);
        // for rc in F::ROUND_CONSTANTS.iter().skip(5) {
        //     F::bars_u64(&mut state_u64);
        //     F::bricks_u64(&mut state_u64);
        //     F::concrete_u64(&mut state_u64, rc);
        // }
        // Convert back
        let mut state_f = [F::ZERO; F::SPONGE_WIDTH];
        for (out, inp) in state_f.iter_mut().zip(state_u64.iter()) {
            *out = F::from_u64_unchecked(*inp);
        }

        log!("Out of circuit result = {:?}", state_f);

        let circuit_result = cs
            .get_value_for_multiple(Place::from_variables(round_function_result))
            .wait()
            .unwrap();

        log!("Circuit result = {:?}", circuit_result);

        assert_eq!(circuit_result, state_f);

        drop(cs);
        owned_cs.pad_and_shrink();

        let worker = Worker::new();

        log!("Checking if satisfied");
        let mut owned_cs = owned_cs.into_assembly();
        assert!(owned_cs.check_if_satisfied(&worker));
    }

    #[test]
    fn test_monolith_not_unrolled_bricks() {
        const SPONGE_WIDTH: usize = 24;

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 80,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 8,
        };

        use crate::config::DevCSConfig;
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, 1 << 20, 1 << 18);
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
            MatrixMultiplicationGate::<F, SPONGE_WIDTH, MonolithMersenneMatrix>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
        let builder = ReductionGate::<F, {MonolithMersenne::LOOKUP_NUM_LIMBS}>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(());

        let cs = &mut owned_cs;

        let mut inputs = [Variable::placeholder(); SPONGE_WIDTH];
        let mut state = [F::ZERO; SPONGE_WIDTH];
        for (idx, dst) in inputs[..F::SPONGE_RATE].iter_mut().enumerate() {
            let value = F::from_u64_with_reduction(idx as u64);
            let var = cs.alloc_single_variable_from_witness(value);
            state[idx] = value;
            *dst = var;
        }

        let capacity_var = cs.allocate_constant(F::ZERO);
        for dst in inputs[F::SPONGE_RATE..].iter_mut() {
            *dst = capacity_var;
        }

        bricks(cs, &mut inputs);
        let round_function_result = inputs;

        let mut state_u64 = [0; F::SPONGE_WIDTH];
        for (out, inp) in state_u64.iter_mut().zip(state.iter()) {
            *out = inp.as_u64();
        }
        F::bricks_u64(&mut state_u64);
        // Convert back
        let mut state_f = [F::ZERO; F::SPONGE_WIDTH];
        for (out, inp) in state_f.iter_mut().zip(state_u64.iter()) {
            *out = F::from_u64_unchecked(*inp);
        }

        log!("Out of circuit result = {:?}", state_f);

        let circuit_result = cs
            .get_value_for_multiple(Place::from_variables(round_function_result))
            .wait()
            .unwrap();

        log!("Circuit result = {:?}", circuit_result);

        assert_eq!(circuit_result, state_f);

        drop(cs);
        owned_cs.pad_and_shrink();

        let worker = Worker::new();

        log!("Checking if satisfied");
        let mut owned_cs = owned_cs.into_assembly();
        assert!(owned_cs.check_if_satisfied(&worker));
    }

    #[test]
    fn test_monolith_not_unrolled_concrete() {
        const SPONGE_WIDTH: usize = 24;

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 80,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 8,
        };

        use crate::config::DevCSConfig;
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, 1 << 20, 1 << 18);
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
            MatrixMultiplicationGate::<F, SPONGE_WIDTH, MonolithMersenneMatrix>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
        let builder = ReductionGate::<F, {MonolithMersenne::LOOKUP_NUM_LIMBS}>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(());

        let cs = &mut owned_cs;

        let mut inputs = [Variable::placeholder(); SPONGE_WIDTH];
        let mut state = [F::ZERO; SPONGE_WIDTH];
        for (idx, dst) in inputs[..F::SPONGE_RATE].iter_mut().enumerate() {
            let value = F::from_u64_with_reduction(idx as u64);
            let var = cs.alloc_single_variable_from_witness(value);
            state[idx] = value;
            *dst = var;
        }

        let capacity_var = cs.allocate_constant(F::ZERO);
        for dst in inputs[F::SPONGE_RATE..].iter_mut() {
            *dst = capacity_var;
        }

        concrete(cs, &mut inputs, F::ROUND_CONSTANTS_FIELD[1]);
        let round_function_result = inputs;

        let mut state_u64 = [0; F::SPONGE_WIDTH];
        for (out, inp) in state_u64.iter_mut().zip(state.iter()) {
            *out = inp.as_u64();
        }
        F::concrete_u64(&mut state_u64, &F::ROUND_CONSTANTS[1]);
        // Convert back
        let mut state_f = [F::ZERO; F::SPONGE_WIDTH];
        for (out, inp) in state_f.iter_mut().zip(state_u64.iter()) {
            *out = F::from_u64_unchecked(*inp);
        }

        log!("Out of circuit result = {:?}", state_f);

        let circuit_result = cs
            .get_value_for_multiple(Place::from_variables(round_function_result))
            .wait()
            .unwrap();

        log!("Circuit result = {:?}", circuit_result);

        assert_eq!(circuit_result, state_f);

        drop(cs);
        owned_cs.pad_and_shrink();

        let worker = Worker::new();

        log!("Checking if satisfied");
        let mut owned_cs = owned_cs.into_assembly();
        assert!(owned_cs.check_if_satisfied(&worker));
    }
}
