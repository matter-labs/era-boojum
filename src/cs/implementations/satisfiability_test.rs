use self::traits::GoodAllocator;

use super::reference_cs::CSReferenceAssembly;
use super::*;

use crate::config::DevCSConfig;

use crate::cs::implementations::polynomial_storage::SatisfiabilityCheckRowView;
use crate::cs::traits::evaluator::GatePlacementType;
use crate::cs::traits::gate::GatePlacementStrategy;

type RCFG = <DevCSConfig as CSConfig>::ResolverConfig;

impl<F: SmallField, A: GoodAllocator> CSReferenceAssembly<F, F, DevCSConfig, A> {
    pub fn check_if_satisfied(&mut self, worker: &Worker) -> bool {
        let (constants, selectors_placement, _) = self.create_constant_setup_polys(worker);
        let (_deg, num_constants_for_general_purpose_columns) = selectors_placement.compute_stats();
        log!("Constants are ready");
        let variables = self.materialize_variables_polynomials(worker);
        log!("Variables are ready");
        let witness = self.materialize_witness_polynomials(worker);
        log!("Witnesses are ready");

        let view = SatisfiabilityCheckRowView::from_storages(variables, witness, constants);
        let mut view_over_general_purpose_columns = view.subset(
            0..self.parameters.num_columns_under_copy_permutation,
            0..self.parameters.num_witness_columns,
            0..num_constants_for_general_purpose_columns,
        );

        let mut paths_mappings = vec![];

        for (idx, gate) in self
            .evaluation_data_over_general_purpose_columns
            .evaluators_over_general_purpose_columns
            .iter()
            .enumerate()
        {
            if gate.max_constraint_degree == 0 {
                paths_mappings.push(vec![]);
                continue;
            }

            let path = selectors_placement
                .output_placement(idx)
                .expect("for non trivial gates we should have placement");
            paths_mappings.push(path);
        }

        let mut dst = vec![];

        for (row, gate_idx) in self.gates_application_sets.iter().enumerate() {
            dst.clear();

            let evaluator = &self
                .evaluation_data_over_general_purpose_columns
                .evaluators_over_general_purpose_columns[*gate_idx];
            // log!("On row {} there is a gate {}", row, &evaluator.debug_name);
            let path = &paths_mappings[*gate_idx];
            let constants_placement_offset = path.len();

            let num_terms = evaluator.num_quotient_terms;
            if num_terms == 0 {
                // skip row
                view_over_general_purpose_columns.advance_manually();
                continue;
            }
            let gate_debug_name = &evaluator.debug_name;
            let num_constants_used = evaluator.num_required_constants;
            let mut this_view = view_over_general_purpose_columns.clone();

            let placement = evaluator.placement_type;
            let evaluation_fn = &**evaluator
                .rowwise_satisfiability_function
                .as_ref()
                .expect("must exist");
            match placement {
                GatePlacementType::UniqueOnRow => {
                    evaluation_fn.evaluate_over_general_purpose_columns(
                        &mut this_view,
                        &mut dst,
                        constants_placement_offset,
                        &mut (),
                    );

                    for (idx, term) in dst.iter().enumerate() {
                        if term.is_zero() == false {
                            panic!(
                                "Unsatisfied at row {} with value {} for term number {} for unique instance of gate {}",
                                row, term, idx, gate_debug_name
                            );
                        }
                    }
                }
                GatePlacementType::MultipleOnRow { per_chunk_offset } => {
                    let mut t_view = view_over_general_purpose_columns.clone();
                    evaluation_fn.evaluate_over_general_purpose_columns(
                        &mut this_view,
                        &mut dst,
                        constants_placement_offset,
                        &mut (),
                    );

                    for (chunk_idx, terms) in dst.chunks(num_terms).enumerate() {
                        for (idx, term) in terms.iter().enumerate() {
                            if term.is_zero() == false {
                                let mut vars = vec![];
                                let mut wits = vec![];
                                let mut constants = vec![];
                                let start_variables = per_chunk_offset.variables_offset * chunk_idx;
                                let start_witnesses = per_chunk_offset.witnesses_offset * chunk_idx;

                                for i in 0..per_chunk_offset.variables_offset {
                                    vars.push(t_view.get_variable_value(start_variables + i));
                                }

                                for i in 0..per_chunk_offset.witnesses_offset {
                                    wits.push(t_view.get_witness_value(start_witnesses + i));
                                }

                                t_view.constants_offset = constants_placement_offset;

                                for i in 0..num_constants_used {
                                    constants.push(t_view.get_constant_value(i));
                                }

                                dbg!(vars);
                                dbg!(wits);
                                dbg!(&constants);

                                let mut vars = vec![];
                                let mut wits = vec![];
                                let start_variables = per_chunk_offset.variables_offset * chunk_idx;
                                let start_witnesses = per_chunk_offset.witnesses_offset * chunk_idx;

                                for i in 0..per_chunk_offset.variables_offset {
                                    vars.push(self.copy_permutation_data[start_variables + i][row]);
                                }

                                for i in 0..per_chunk_offset.witnesses_offset {
                                    wits.push(
                                        self.witness_placement_data[start_witnesses + i][row],
                                    );
                                }

                                dbg!(vars);
                                dbg!(wits);

                                panic!(
                                    "Unsatisfied at row {} with value {} for term number {} for subinstance number {} of gate {}",
                                    row, term, idx, chunk_idx, gate_debug_name
                                );
                            }
                        }
                    }
                }
            }

            view_over_general_purpose_columns.advance_manually();
        }

        // now specialized rows
        {
            // we expect our gates to be narrow, so we do not need to buffer row, and instead
            // we can evaluate over limited set of columns
            use crate::cs::traits::evaluator::GenericDynamicEvaluatorOverSpecializedColumns;
            let mut specialized_placement_data = vec![];
            let mut evaluation_functions: Vec<
                &dyn GenericDynamicEvaluatorOverSpecializedColumns<
                    F,
                    F,
                    SatisfiabilityCheckRowView<F>,
                    Vec<F>,
                >,
            > = vec![];
            let mut views = vec![];
            let mut evaluator_names = vec![];

            for (idx, (gate_type_id, evaluator)) in self
                .evaluation_data_over_specialized_columns
                .gate_type_ids_for_specialized_columns
                .iter()
                .zip(
                    self.evaluation_data_over_specialized_columns
                        .evaluators_over_specialized_columns
                        .iter(),
                )
                .enumerate()
            {
                use crate::cs::gates::lookup_marker::LookupFormalGate;
                if gate_type_id == &std::any::TypeId::of::<LookupFormalGate>() {
                    continue;
                }
                assert!(
                    evaluator.total_quotient_terms_over_all_repetitions != 0,
                    "evaluator {} has not contribution to quotient",
                    &evaluator.debug_name,
                );
                log!(
                    "Will be evaluating {} over specialized columns",
                    &evaluator.debug_name
                );

                let num_terms = evaluator.num_quotient_terms;
                let placement_strategy = self
                    .placement_strategies
                    .get(gate_type_id)
                    .copied()
                    .expect("gate must be allowed");
                let GatePlacementStrategy::UseSpecializedColumns {
                    num_repetitions,
                    share_constants,
                } = placement_strategy
                else {
                    unreachable!();
                };

                let total_terms = num_terms * num_repetitions;

                let (initial_offset, per_repetition_offset, total_constants_available) = self
                    .evaluation_data_over_specialized_columns
                    .offsets_for_specialized_evaluators[idx];

                let placement_data = (
                    num_repetitions,
                    share_constants,
                    initial_offset,
                    per_repetition_offset,
                    total_constants_available,
                    total_terms,
                );

                specialized_placement_data.push(placement_data);
                let t = evaluator
                    .columnwise_satisfiability_function
                    .as_ref()
                    .expect("must be properly configured");
                evaluation_functions.push(&**t);

                let (
                    num_repetitions,
                    share_constants,
                    initial_offset,
                    per_repetition_offset,
                    _total_constants_available,
                    _total_terms,
                ) = placement_data;

                // we self-check again
                if share_constants {
                    assert_eq!(per_repetition_offset.constants_offset, 0);
                }
                let mut final_offset = initial_offset;
                for _ in 0..num_repetitions {
                    final_offset.add_offset(&per_repetition_offset);
                }

                let source = view.subset(
                    initial_offset.variables_offset..final_offset.variables_offset,
                    initial_offset.witnesses_offset..final_offset.witnesses_offset,
                    (num_constants_for_general_purpose_columns + initial_offset.constants_offset)
                        ..(num_constants_for_general_purpose_columns
                            + final_offset.constants_offset),
                );

                views.push(source);

                evaluator_names.push(&evaluator.debug_name);
            }

            for row in 0..self.max_trace_len {
                for (((placement_data, evaluation_fn), source), evaluator_name) in
                    specialized_placement_data
                        .iter()
                        .zip(evaluation_functions.iter())
                        .zip(views.iter_mut())
                        .zip(evaluator_names.iter())
                {
                    let (
                        num_repetitions,
                        _share_constants,
                        _initial_offset,
                        _per_repetition_offset,
                        _total_constants_available,
                        total_terms,
                    ) = *placement_data;

                    let num_terms = total_terms / num_repetitions;

                    dst.clear();

                    evaluation_fn.evaluate_over_columns(source, &mut dst, &mut ());
                    for (chunk_idx, terms) in dst.chunks(num_terms).enumerate() {
                        for (idx, term) in terms.iter().enumerate() {
                            if term.is_zero() == false {
                                panic!(
                                "Unsatisfied at row {} with value {} for term number {} for subinstance number {} of gate {}",
                                row, term, idx, chunk_idx, evaluator_name
                            );

                                // let mut vars = vec![];
                                // let mut wits = vec![];
                                // let mut constants = vec![];
                                // let start_variables = per_chunk_offset.variables_offset * chunk_idx;
                                // let start_witnesses = per_chunk_offset.witnesses_offset * chunk_idx;

                                // for i in 0..per_chunk_offset.variables_offset {
                                //     vars.push(t_view.get_variable_value(start_variables + i));
                                // }

                                // for i in 0..per_chunk_offset.witnesses_offset {
                                //     wits.push(t_view.get_witness_value(start_witnesses + i));
                                // }

                                // for i in 0..self.parameters.num_constant_columns {
                                //     constants.push(t_view.get_constant_value(i));
                                // }

                                // dbg!(vars);
                                // dbg!(wits);
                                // dbg!(&constants[constants_placement_offset..]);

                                // let mut vars = vec![];
                                // let mut wits = vec![];
                                // let start_variables = per_chunk_offset.variables_offset * chunk_idx;
                                // let start_witnesses = per_chunk_offset.witnesses_offset * chunk_idx;

                                // for i in 0..per_chunk_offset.variables_offset {
                                //     vars.push(self.copy_permutation_data[start_variables + i][row]);
                                // }

                                // for i in 0..per_chunk_offset.witnesses_offset {
                                //     wits.push(self.witness_placement_data[start_variables + i][row]);
                                // }

                                // dbg!(vars);
                                // dbg!(wits);

                                // panic!(
                                //     "Unsatisfied at row {} with value {} for term number {} for subinstance number {} of gate {}",
                                //     row, term, idx, chunk_idx, gate_debug_name
                                // );
                            }
                        }
                    }

                    source.advance_manually();
                }
            }
        }

        true
    }
}
