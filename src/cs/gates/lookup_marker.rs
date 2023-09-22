use crate::cs::implementations::reference_cs::*;
use crate::cs::traits::gate::FinalizationHintSerialized;

use super::*;

// we use a lookup scheme introduced by [Hab22] with extensions from https://eprint.iacr.org/2022/1763.pdf

// \sum_{i in trace} 1 / (X + f_{i} = \sum_{i in tables} m_{i} / (X + t_{i}),
// where f_{i} - private witness, m_{i} - multiplicities of entries of t_{i} in the whole `f`

// with slight modification as following:

// - when we commit to the full witness we also commit to the multiplicities counts
// - during a copy-permutation commitments phase we could(!) commit to the A(x) poly
// A_{i} = m_{i}/(t_{i} + beta) for all x = omega^i with a modification that instead of
// using individual t_{i} for every lookup column that we use, we actually create
// our t_{i} as t0_{i} + gamma * t1_{i} + gamma^2 * t2_{i} + ... for whatever the width of the
// table is (including table type ID). But in practice we do not need to do so, as we can simulate
// oracle access to A_{i} by using oracle access to tX_{i}
// - same applies for B_{i} = 1/(f_{i} + beta) polynomial, with the same modification
// f_{i} = f0_{i} + gamma * f1_{i} + gamma^2 * f2_{i} + ...
// NOTE: degree of B(X) is our full trace degree. Degree of A(X) is a smallest degree that fits
// all the tables
// - so the only thing that prover sends is A(0) (that is part of sumcheck later on)
// - in the quotient poly we include an extra terms
// 1) QA(X) = (A(X)(T(X) + beta) − m(X)) / Z_small(X) where Z_small(X) is a vanishing poly of "small" degree (fits table entries)
// 2) QB(X) = (B(X)(f(x) + beta) − 1) / Z_large(X) where Z_large(X) is a vanishing poly of full degree (trace degree)
// 3) plainly add A(X) * X^{trace_degree - degree(A(X)) - 1} to the set of polynomials that will be participate in FRI
// to ensure that A(X) is small degree
// - when we do the verification at the random point `z` we automanically check the same relations,
// - and we also need to check that \sum A(x) at "small" domain is equal to \sum B(x) at "large" domain,
// via A(0) * |small domain| == B(0) * |large domain|. To do so we "open"
// B(X) and A(X) (both as simualted oracles) to A(0) and B(0) (that can be computed from A(0)) at 0 quotening and FRI

// This is a marker-only

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LookupGateMarkerFormalEvaluator {
    pub num_variables_to_use: usize,
    pub num_constants_to_use: usize,
    pub share_table_id: bool,
}

impl<F: PrimeField> GateConstraintEvaluator<F> for LookupGateMarkerFormalEvaluator {
    type UniqueParameterizationParams = (usize, usize, bool);

    #[inline(always)]
    fn new_from_parameters(params: Self::UniqueParameterizationParams) -> Self {
        Self {
            num_variables_to_use: params.0,
            num_constants_to_use: params.1,
            share_table_id: params.2,
        }
    }

    #[inline(always)]
    fn unique_params(&self) -> Self::UniqueParameterizationParams {
        (
            self.num_variables_to_use,
            self.num_constants_to_use,
            self.share_table_id,
        )
    }

    #[inline]
    fn type_name() -> std::borrow::Cow<'static, str> {
        Cow::Borrowed(std::any::type_name::<Self>())
    }

    #[inline]
    fn instance_width(&self) -> GatePrincipalInstanceWidth {
        GatePrincipalInstanceWidth {
            num_variables: self.num_variables_to_use,
            num_witnesses: 0,
            num_constants: self.num_constants_to_use,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::MarkerNeedsSelector
    }

    #[inline]
    fn max_constraint_degree() -> usize {
        // we keep in mind that we multiply by selector path
        // separately, that will increase our degree

        1
    }

    #[inline]
    fn placement_type(&self) -> GatePlacementType {
        if self.share_table_id {
            if self.num_constants_to_use == 0 {
                GatePlacementType::MultipleOnRow {
                    per_chunk_offset: PerChunkOffset {
                        variables_offset: self.num_variables_to_use - 1,
                        witnesses_offset: 0,
                        constants_offset: 0,
                    },
                }
            } else {
                assert_eq!(self.num_constants_to_use, 1);
                GatePlacementType::MultipleOnRow {
                    per_chunk_offset: PerChunkOffset {
                        variables_offset: self.num_variables_to_use,
                        witnesses_offset: 0,
                        constants_offset: 0,
                    },
                }
            }
        } else {
            GatePlacementType::MultipleOnRow {
                per_chunk_offset: PerChunkOffset {
                    variables_offset: self.num_variables_to_use,
                    witnesses_offset: 0,
                    constants_offset: self.num_constants_to_use,
                },
            }
        }
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, _geometry: &CSGeometry) -> usize {
        1 // will be handled separately by CS
    }

    #[inline]
    fn num_required_constants_in_geometry(&self, _geometry: &CSGeometry) -> usize {
        0 // will be handled separately by CS
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
        _trace_source: &S,
        _destination: &mut D,
        _shared_constants: &Self::RowSharedConstants<P>,
        _global_constants: &Self::GlobalConstants<P>,
        _ctx: &mut P::Context,
    ) {
        unreachable!("must not be called on lookup gates");
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LookupFormalGate {
    pub num_variables_to_use: usize,
    pub num_constants_to_use: usize,
    pub share_table_id: bool,
}

impl<F: SmallField> Gate<F> for LookupFormalGate {
    type Tools = ();

    #[inline]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, _cs: &CS) -> bool {
        true
    }

    type Evaluator = LookupGateMarkerFormalEvaluator;
    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        LookupGateMarkerFormalEvaluator {
            num_variables_to_use: self.num_variables_to_use,
            num_constants_to_use: self.num_constants_to_use,
            share_table_id: self.share_table_id,
        }
    }

    // fn columns_finalization_function<CS: ConstraintSystem<F>>(
    //     _cs: &CS,
    // ) -> Option<traits::gate::GateColumnsCleanupFunction<CS>> {

    //     let closure = move |cs: &mut CS, min_bound: usize| {
    //         // we need to fill our witnesses with non-trivial values

    //         let placement_strategy = cs.get_gates_config().placement_strategy::<Self>().expect("gate must be allowed");
    //         let GatePlacementStrategy::UseSpecializedColumns { num_repetitions, share_constants } = placement_strategy else {
    //             unreachable!()
    //         };

    //         let lookup_parameters = cs.get_lookup_params();
    //         let geometry = cs.get_params();

    //         // now we need to compute how many lookups of different types we add
    //         match lookup_parameters {
    //             LookupParameters::TableIdAsConstant { .. } | LookupParameters::UseSpecializedColumnsWithTableIdAsConstant { .. } => {
    //                 // we walk over the number of different not fully filled rows first and cleanup them,
    //                 // and then cleanup column in full
    //             },
    //             LookupParameters::TableIdAsVariable { .. } | LookupParameters::UseSpecializedColumnsWithTableIdAsVariable { .. } => {
    //                 // we just compute the number of extra entries we want to add
    //                 let table = cs.get_table(INITIAL_LOOKUP_TABLE_ID_VALUE);

    //                 let capacity_per_row = lookup_parameters.num_sublookup_arguments_for_geometry(&geometry);

    //                 let tooling: &mut LookupTooling = cs
    //                     .get_gates_config_mut()
    //                     .get_aux_data_mut::<LookupFormalGate, _>()
    //                     .expect("tooling must exist");

    //                 let tooling_subid = 0;
    //                 let (mut row, num_instances_already_placed) = tooling.0[tooling_subid].take().expect("at least one entry must be placed");
    //                 let mut num_to_add = 0;
    //                 if num_instances_already_placed < capacity_per_row {
    //                     num_to_add += capacity_per_row - num_instances_already_placed;
    //                 }
    //                 // last row is filled
    //                 // now two options
    //                 let bound_zero_enumerated = min_bound - 1;
    //                 if row <= bound_zero_enumerated {
    //                     (row - bound_zero_enumerated) * capacity_per_row
    //                 } else {
    //                     let next_bound = row.next_power_of_two();
    //                     (next_bound - 1 - row) * capacity_per_row
    //                 };

    //                 table.pad_into_cs(cs, num_to_add, INITIAL_LOOKUP_TABLE_ID_VALUE);
    //             },

    //             _ => {
    //                 unreachable!()
    //             },
    //         }
    //     };

    //     Some(Box::new(closure) as Box<dyn FnOnce(&mut CS, usize) + Send + Sync + 'static>)

    fn columns_finalization_function<CS: ConstraintSystem<F>>(
    ) -> Option<traits::gate::GateColumnsCleanupFunction<CS>> {
        let closure = move |cs: &mut CS,
                            min_bound: usize,
                            hint: &Option<FinalizationHintSerialized>| {
            // we need to fill our witnesses with non-trivial values

            let placement_strategy = cs
                .get_gates_config()
                .placement_strategy::<Self>()
                .expect("gate must be allowed");
            let GatePlacementStrategy::UseSpecializedColumns {
                num_repetitions: _,
                share_constants: _,
            } = placement_strategy
            else {
                unreachable!()
            };

            let lookup_parameters = cs.get_lookup_params();
            let geometry = cs.get_params();

            // now we need to compute how many lookups of different types we add
            match lookup_parameters {
                LookupParameters::UseSpecializedColumnsWithTableIdAsConstant { .. }
                | LookupParameters::UseSpecializedColumnsWithTableIdAsVariable { .. } => {
                    // we just compute the number of extra entries we want to add
                    let capacity_per_row =
                        lookup_parameters.num_sublookup_arguments_for_geometry(&geometry);

                    let tooling: &LookupTooling = cs
                        .get_gates_config()
                        .get_aux_data::<LookupFormalGate, _>()
                        .expect("tooling must exist");
                    let (per_table_tooling, next_row_to_use) = (tooling.0.clone(), tooling.1);
                    drop(tooling);

                    // now we have to branch unfortunately, because if we do not have setup information
                    // available in the CS then we can not get valid data from placement tooling

                    let mut final_bound_to_compare = 0;

                    let finalization_hint: LookupFinalizationHint =
                        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                            let mut hint = LookupFinalizationHint::default();

                            for (tooling_id, subdata) in per_table_tooling.iter().enumerate() {
                                let table_id = tooling_id as u32 + INITIAL_LOOKUP_TABLE_ID_VALUE;
                                let (_, num_instances_already_placed) =
                                    subdata.expect("table must be used at least once");
                                let num_instances_to_add =
                                    capacity_per_row - num_instances_already_placed;
                                hint.pad_partial_rows.push((table_id, num_instances_to_add));
                            }

                            // and now pad with just first table
                            let mut final_bound = min_bound;
                            let num_to_add = if next_row_to_use <= min_bound {
                                (min_bound - next_row_to_use) * capacity_per_row
                            } else {
                                let next_bound = next_row_to_use.next_power_of_two();
                                final_bound = next_bound;
                                (next_bound - next_row_to_use) * capacity_per_row
                            };
                            final_bound_to_compare = final_bound;

                            hint.pad_full_rows = num_to_add;

                            hint
                        } else {
                            assert!(hint.is_some());

                            let hint =
                                bincode::deserialize(hint.as_ref().expect(
                                    "should be present if setup information is not available",
                                ))
                                .expect(&format!(
                                    "should have properly encoded padding hint for gate {}",
                                    std::any::type_name::<Self>()
                                ));

                            hint
                        };

                    for (table_id, num_to_add) in finalization_hint.pad_partial_rows.iter().copied()
                    {
                        let table = cs.get_table(table_id);
                        table.pad_into_cs(cs, num_to_add, table_id);
                    }

                    // and now pad with just first table
                    let default_table_id = INITIAL_LOOKUP_TABLE_ID_VALUE;
                    let table = cs.get_table(default_table_id);
                    table.pad_into_cs(cs, finalization_hint.pad_full_rows, default_table_id);

                    if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                        let tooling: &LookupTooling = cs
                            .get_gates_config()
                            .get_aux_data::<LookupFormalGate, _>()
                            .expect("tooling must exist");
                        let (per_table_tooling, next_row_to_use) = (tooling.0.clone(), tooling.1);
                        drop(tooling);

                        assert!(next_row_to_use == final_bound_to_compare);
                        for (tooling_id, subdata) in per_table_tooling.iter().enumerate() {
                            let (_, num_instances_already_placed) = subdata.expect("must exist");
                            let table_id = tooling_id as u32 + INITIAL_LOOKUP_TABLE_ID_VALUE;
                            assert!(
                                num_instances_already_placed == capacity_per_row,
                                "must properly fill the full row for table {}",
                                table_id
                            );
                        }
                    }

                    if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                        let encoded =
                            bincode::serialize(&finalization_hint).expect("must serialize");
                        Some(encoded)
                    } else {
                        None
                    }
                }

                _ => {
                    unreachable!()
                }
            }
        };

        Some(Box::new(closure) as _)
    }
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Default)]
pub struct LookupFinalizationHint {
    pub pad_partial_rows: Vec<(u32, usize)>, // table_id, num_instances to pad rows
    pub pad_full_rows: usize,
}
