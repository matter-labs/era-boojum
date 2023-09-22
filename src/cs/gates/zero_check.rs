use super::*;
use crate::cs::cs_builder::{CsBuilder, CsBuilderImpl};
use crate::cs::traits::gate::FinalizationHintSerialized;
use crate::{config::CSSetupConfig, field::PrimeField};

//  input * inverse_wit = (1 - flag)
//  input * flag = 0

// if input != 0 then flag == 0 from second
// if input == 0 then flag == 1 from first

// so we do not need to constraint flag as boolean additionally

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ZeroCheckGate {
    pub var_to_check: Variable,
    pub is_zero_result: Variable,
    pub inversion_witness: Place,
    pub use_witness_column_for_inversion: bool,
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ZeroCheckEvaluator {
    pub use_witness_column_for_inversion: bool,
}

impl<F: PrimeField> GateConstraintEvaluator<F> for ZeroCheckEvaluator {
    type UniqueParameterizationParams = bool;

    #[inline(always)]
    fn new_from_parameters(params: Self::UniqueParameterizationParams) -> Self {
        Self {
            use_witness_column_for_inversion: params,
        }
    }

    #[inline(always)]
    fn unique_params(&self) -> Self::UniqueParameterizationParams {
        self.use_witness_column_for_inversion
    }

    #[inline]
    fn type_name() -> std::borrow::Cow<'static, str> {
        Cow::Borrowed(std::any::type_name::<Self>())
    }

    #[inline]
    fn instance_width(&self) -> GatePrincipalInstanceWidth {
        GatePrincipalInstanceWidth {
            num_variables: if self.use_witness_column_for_inversion {
                2
            } else {
                3
            },
            num_witnesses: if self.use_witness_column_for_inversion {
                1
            } else {
                0
            },
            num_constants: 0,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: 2,
            num_quotient_terms: 2,
        }
    }

    #[inline]
    fn placement_type(&self) -> GatePlacementType {
        GatePlacementType::MultipleOnRow {
            per_chunk_offset: PerChunkOffset {
                variables_offset: if self.use_witness_column_for_inversion {
                    2
                } else {
                    3
                },
                witnesses_offset: if self.use_witness_column_for_inversion {
                    1
                } else {
                    0
                },
                constants_offset: 0,
            },
        }
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, geometry: &CSGeometry) -> usize {
        let num_required_copiable = if self.use_witness_column_for_inversion {
            2
        } else {
            3
        };
        let num_required_witness = if self.use_witness_column_for_inversion {
            1
        } else {
            0
        };
        let limit_from_copiable =
            geometry.num_columns_under_copy_permutation / num_required_copiable;
        let limit_from_witnesses = if num_required_witness == 0 {
            usize::MAX
        } else {
            geometry.num_witness_columns / num_required_witness
        };

        std::cmp::min(limit_from_copiable, limit_from_witnesses)
    }
    #[inline]
    fn num_required_constants_in_geometry(&self, _geometry: &CSGeometry) -> usize {
        0
    }

    type GlobalConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = ();

    #[inline(always)]
    fn create_global_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>>(
        &self,
        _ctx: &mut P::Context,
    ) -> Self::GlobalConstants<P> {
    }

    type RowSharedConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = ();

    #[inline(always)]
    fn load_row_shared_constants<
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSource<F, P>,
    >(
        &self,
        _trace_source: &S,
        _ctx: &mut P::Context,
    ) -> Self::RowSharedConstants<P> {
    }

    #[inline(always)]
    fn evaluate_once<
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSource<F, P>,
        D: EvaluationDestination<F, P>,
    >(
        &self,
        trace_source: &S,
        destination: &mut D,
        _shared_constants: &Self::RowSharedConstants<P>,
        _global_constants: &Self::GlobalConstants<P>,
        ctx: &mut P::Context,
    ) {
        let one = P::one(ctx);
        let input = trace_source.get_variable_value(0);
        let flag = trace_source.get_variable_value(1);
        let inversion_witness = if self.use_witness_column_for_inversion {
            trace_source.get_witness_value(0)
        } else {
            trace_source.get_variable_value(2)
        };

        //  input * inverse_wit = (1 - flag)
        let mut contribution = flag;
        P::mul_and_accumulate_into(&mut contribution, &input, &inversion_witness, ctx);
        contribution.sub_assign(&one, ctx);

        destination.push_evaluation_result(contribution, ctx);

        //  input * flag = 0
        let mut contribution = input;
        contribution.mul_assign(&flag, ctx);

        destination.push_evaluation_result(contribution, ctx);
    }
}

impl<F: SmallField> Gate<F> for ZeroCheckGate {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        let num_required_copiable = if self.use_witness_column_for_inversion {
            2
        } else {
            3
        };
        let num_required_witness = if self.use_witness_column_for_inversion {
            1
        } else {
            0
        };
        geometry.max_allowed_constraint_degree >= 2
            && geometry.num_columns_under_copy_permutation >= num_required_copiable
            && geometry.num_witness_columns >= num_required_witness
    }

    type Evaluator = ZeroCheckEvaluator;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        ZeroCheckEvaluator {
            use_witness_column_for_inversion: self.use_witness_column_for_inversion,
        }
    }

    // it has non-trivial cleanup
    fn row_finalization_function<CS: ConstraintSystem<F>>(
    ) -> Option<traits::gate::GateRowCleanupFunction<CS>> {
        let closure = move |cs: &mut CS, hint: &Option<FinalizationHintSerialized>| {
            // we need to fill our witnesses with non-trivial values

            // We fill with a strategy that input is 0, so result of logical evaluation is 1
            let geometry = cs.get_params();

            let use_witness_column_for_inversion = cs.get_gate_params::<Self>();

            let mut num_repetitions_for_comparison = 0;

            let finalization_hint: ZeroCheckFinalizationHint =
                if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                    let tooling: &NextGateCounterWithoutParams = cs
                        .get_gates_config()
                        .get_aux_data::<Self, _>()
                        .expect("gate must be allowed");
                    assert!(tooling.is_some(), "at least one gate must be placed in CS");
                    let (_existing_row, num_instances_already_placed) = tooling.unwrap();
                    drop(tooling);
                    let evaluator =
                        <Self::Evaluator as GateConstraintEvaluator<F>>::new_from_parameters(
                            use_witness_column_for_inversion,
                        );
                    let num_repetitions = GateConstraintEvaluator::<F>::num_repetitions_in_geometry(
                        &evaluator, &geometry,
                    );

                    let instances_to_add = num_repetitions - num_instances_already_placed;
                    num_repetitions_for_comparison = num_repetitions;

                    ZeroCheckFinalizationHint { instances_to_add }
                } else {
                    assert!(hint.is_some());

                    let hint = bincode::deserialize(
                        hint.as_ref()
                            .expect("should be present if setup information is not available"),
                    )
                    .expect(&format!(
                        "should have properly encoded padding hint for gate {}",
                        std::any::type_name::<Self>()
                    ));

                    hint
                };

            let ZeroCheckFinalizationHint { instances_to_add } = finalization_hint;

            if instances_to_add > 0 {
                let var = cs.alloc_single_variable_from_witness(F::ONE);
                let inversion = if use_witness_column_for_inversion {
                    cs.alloc_single_witness(F::ONE).into()
                } else {
                    cs.alloc_single_variable_from_witness(F::ONE).into()
                };
                let result = cs.alloc_single_variable_from_witness(F::ZERO);

                let gate = Self {
                    var_to_check: var,
                    is_zero_result: result,
                    inversion_witness: inversion,
                    use_witness_column_for_inversion,
                };

                for _ in 0..instances_to_add {
                    gate.clone().add_to_cs(cs);
                }
            }

            // self-check
            if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                let tooling: &NextGateCounterWithoutParams = cs
                    .get_gates_config()
                    .get_aux_data::<Self, _>()
                    .expect("gate must be allowed");
                assert!(tooling.is_some(), "at least one gate must be placed in CS");
                let (_, num_instances_already_placed) = tooling.unwrap();
                drop(tooling);
                assert_eq!(num_instances_already_placed, num_repetitions_for_comparison);
            }

            if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                let encoded = bincode::serialize(&finalization_hint).expect("must serialize");
                Some(encoded)
            } else {
                None
            }
        };

        Some(Box::new(closure) as _)
    }

    fn columns_finalization_function<CS: ConstraintSystem<F>>(
    ) -> Option<traits::gate::GateColumnsCleanupFunction<CS>> {
        let closure =
            move |cs: &mut CS, min_bound: usize, hint: &Option<FinalizationHintSerialized>| {
                // we need to fill our witnesses with non-trivial values

                let placement_strategy = cs
                    .get_gates_config()
                    .placement_strategy::<Self>()
                    .expect("gate must be allowed");
                let GatePlacementStrategy::UseSpecializedColumns {
                    num_repetitions,
                    share_constants: _,
                } = placement_strategy
                else {
                    unreachable!()
                };

                // We fill with a strategy that input is 0, so result of logical evaluation is 1

                let mut bound_for_comparison = 0;

                let finalization_hint: ZeroCheckFinalizationHint =
                    if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                        let mut instances_to_add = 0;
                        let tooling: &NextGateCounterWithoutParams = cs
                            .get_gates_config()
                            .get_aux_data::<Self, _>()
                            .expect("gate must be allowed");
                        assert!(tooling.is_some(), "at least one gate must be placed in CS");
                        let (row, num_instances_already_placed) = tooling.unwrap();
                        drop(tooling);
                        // first finalize "current row"
                        let mut next_full_row = row;
                        if num_instances_already_placed > 0 {
                            instances_to_add += num_repetitions - num_instances_already_placed;
                            next_full_row += 1;
                        }

                        let mut min_bound = min_bound;

                        if next_full_row > min_bound {
                            min_bound = next_full_row.next_power_of_two() - 1;
                        }

                        let full_rows = min_bound - next_full_row;
                        instances_to_add += full_rows * num_repetitions;

                        bound_for_comparison = min_bound;

                        ZeroCheckFinalizationHint { instances_to_add }
                    } else {
                        assert!(hint.is_some());

                        let hint = bincode::deserialize(
                            hint.as_ref()
                                .expect("should be present if setup information is not available"),
                        )
                        .expect(&format!(
                            "should have properly encoded padding hint for gate {}",
                            std::any::type_name::<Self>()
                        ));

                        hint
                    };

                let ZeroCheckFinalizationHint { instances_to_add } = finalization_hint;

                if instances_to_add > 0 {
                    let var = cs.alloc_single_variable_from_witness(F::ONE);

                    for _ in 0..instances_to_add {
                        Self::check_if_zero(cs, var);
                    }
                }

                // self-check
                if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                    let tooling: &NextGateCounterWithoutParams = cs
                        .get_gates_config()
                        .get_aux_data::<Self, _>()
                        .expect("gate must be allowed");
                    assert!(tooling.is_some(), "at least one gate must be placed in CS");
                    let (row, num_instances_already_placed) = tooling.unwrap();
                    drop(tooling);
                    assert_eq!(row + 1, bound_for_comparison);
                    assert_eq!(num_instances_already_placed, num_repetitions);
                }

                if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                    let encoded = bincode::serialize(&finalization_hint).expect("must serialize");
                    Some(encoded)
                } else {
                    None
                }
            };

        Some(Box::new(closure) as _)
    }
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Default)]
pub struct ZeroCheckFinalizationHint {
    pub instances_to_add: usize,
}

impl ZeroCheckGate {
    pub fn add_to_cs<F: SmallField, CS: ConstraintSystem<F>>(self, cs: &mut CS) {
        debug_assert!(cs.gate_is_allowed::<Self>());

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            return;
        }

        match cs.get_gate_placement_strategy::<Self>() {
            GatePlacementStrategy::UseGeneralPurposeColumns => {
                let offered_row_idx = cs.next_available_row();
                let capacity_per_row = self.capacity_per_row(&*cs);
                let tooling: &mut NextGateCounterWithoutParams = cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, _>()
                    .expect("gate must be allowed");
                let (row, num_instances_already_placed) =
                    find_next_gate_without_params(tooling, capacity_per_row, offered_row_idx);
                drop(tooling);

                let num_required_copiable = if self.use_witness_column_for_inversion {
                    2
                } else {
                    3
                };
                let num_required_witness = if self.use_witness_column_for_inversion {
                    1
                } else {
                    0
                };

                // now we can use methods of CS to inform it of low level operations
                let mut variables_offset = num_instances_already_placed * num_required_copiable;
                let witness_offset = if num_required_witness == 0 {
                    0
                } else {
                    num_instances_already_placed * num_required_witness
                };
                if offered_row_idx == row {
                    cs.place_gate(&self, row);
                }
                cs.place_multiple_variables_into_row(
                    &[self.var_to_check, self.is_zero_result],
                    row,
                    variables_offset,
                );
                variables_offset += 2;
                if self.inversion_witness.is_copiable_variable() {
                    cs.place_variable(self.inversion_witness.as_variable(), row, variables_offset);
                } else {
                    cs.place_witness(self.inversion_witness.as_witness(), row, witness_offset);
                }
            }
            GatePlacementStrategy::UseSpecializedColumns {
                num_repetitions,
                share_constants: _,
            } => {
                // gate knows how to place itself
                let capacity_per_row = num_repetitions;
                let tooling: &mut NextGateCounterWithoutParams = cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, _>()
                    .expect("gate must be allowed");
                let (row, num_instances_already_placed) =
                    find_next_specialized_gate_without_params(tooling, capacity_per_row);
                cs.place_gate_specialized(&self, num_instances_already_placed, row);

                let mut variables_offset = 0;
                cs.place_multiple_variables_into_row_specialized::<Self, 2>(
                    &[self.var_to_check, self.is_zero_result],
                    num_instances_already_placed,
                    row,
                    variables_offset,
                );
                variables_offset += 2;
                if self.inversion_witness.is_copiable_variable() {
                    cs.place_variable_specialized::<Self>(
                        self.inversion_witness.as_variable(),
                        num_instances_already_placed,
                        row,
                        variables_offset,
                    );
                } else {
                    cs.place_witness_specialized::<Self>(
                        self.inversion_witness.as_witness(),
                        num_instances_already_placed,
                        row,
                        0,
                    );
                }
            }
        }
    }

    pub fn configure_builder<
        F: SmallField,
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        TImpl: CsBuilderImpl<F, TImpl>,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
        use_witness_for_inversion: bool,
        // ) -> CsBuilder<TImpl, F, GC::DescendantHolder<Self, NextGateCounterWithoutParams>, TB> {
    ) -> CsBuilder<TImpl, F, (GateTypeEntry<F, Self, NextGateCounterWithoutParams>, GC), TB> {
        builder.allow_gate(placement_strategy, use_witness_for_inversion, None)
    }

    pub fn check_if_zero<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        var_to_check: Variable,
    ) -> Variable {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let use_witness_column_for_inversion = cs.get_gate_params::<Self>();

        let is_zero_result = cs.alloc_variable_without_value();
        let inversion_witness: Place = if use_witness_column_for_inversion {
            cs.alloc_witness_without_value().into()
        } else {
            cs.alloc_variable_without_value().into()
        };

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 1]| {
                let [a] = inputs;

                if a.is_zero() {
                    [F::ONE, F::ZERO]
                } else {
                    let inverse = a.inverse().unwrap();

                    [F::ZERO, inverse]
                }
            };

            let dependencies = Place::from_variables([var_to_check]);

            cs.set_values_with_dependencies(
                &dependencies,
                &[is_zero_result.into(), inversion_witness],
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                var_to_check,
                is_zero_result,
                inversion_witness,
                use_witness_column_for_inversion,
            };

            gate.add_to_cs(cs);
        }

        is_zero_result
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cs::gates::testing_tools::test_evaluator;
    use crate::field::goldilocks::GoldilocksField;
    type F = GoldilocksField;

    #[test]
    fn test_properties() {
        // particular geometry is not important
        let _geometry = CSGeometry {
            num_columns_under_copy_permutation: 80,
            num_witness_columns: 80,
            num_constant_columns: 10,
            max_allowed_constraint_degree: 8,
        };

        let evaluator =
            <ZeroCheckEvaluator as GateConstraintEvaluator<F>>::new_from_parameters(false);

        test_evaluator::<F, _>(evaluator);
    }
}
