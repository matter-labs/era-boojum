use std::{collections::HashMap, sync::RwLock};

use crate::config::*;

use crate::cs::gates::lookup_marker::LookupFormalGate;
use crate::cs::gates::LookupTooling;
use crate::cs::implementations::reference_cs::INITIAL_LOOKUP_TABLE_ID_VALUE;
use crate::dag::DefaultCircuitResolver;
use crate::{
    config::CSConfig,
    dag::CircuitResolver,
    field::{
        traits::field_like::{PrimeFieldLikeVectorized, TrivialContext},
        SmallField,
    },
};

use super::{
    cs_builder::{CsBuilder, CsBuilderImpl},
    implementations::reference_cs::CSReferenceImplementation,
    traits::{evaluator::GateConstraintEvaluator, gate::Gate},
    GateConfigurationHolder, StaticToolboxHolder,
};
use super::{CSGeometry, GateTypeEntry, LookupParameters, Tool, Variable, Witness};
use crate::cs::implementations::evaluator_data::*;
use crate::cs::traits::gate::GatePlacementStrategy;

pub struct CsReferenceImplementationBuilder<
    F: SmallField,
    P: PrimeFieldLikeVectorized<Base = F>,
    CFG: CSConfig,
    CR: CircuitResolver<F, CFG::ResolverConfig> = DefaultCircuitResolver<
        F,
        <CFG as CSConfig>::ResolverConfig,
    >,
> {
    phantom: std::marker::PhantomData<(P, CFG, CR)>,

    parameters: CSGeometry,
    lookup_parameters: LookupParameters,
    max_trace_len: usize,
    lookup_marker_gate_idx: Option<u32>,

    evaluation_data_over_general_purpose_columns: EvaluationDataOverGeneralPurposeColumns<F, P>,
    evaluation_data_over_specialized_columns: EvaluationDataOverSpecializedColumns<F, P>,
}

impl<
        F: SmallField,
        P: PrimeFieldLikeVectorized<Base = F>,
        CFG: CSConfig,
        CR: CircuitResolver<F, CFG::ResolverConfig>,
    > CsReferenceImplementationBuilder<F, P, CFG, CR>
{
    pub fn new(geometry: CSGeometry, max_trace_len: usize) -> Self {
        Self {
            phantom: std::marker::PhantomData,

            parameters: geometry,
            lookup_parameters: LookupParameters::NoLookup,

            max_trace_len,
            lookup_marker_gate_idx: None,

            evaluation_data_over_general_purpose_columns:
                EvaluationDataOverGeneralPurposeColumns::new(),
            evaluation_data_over_specialized_columns: EvaluationDataOverSpecializedColumns::new(),
        }
    }

    pub(crate) fn ensure_compatible_with_lookup<
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
    >(
        builder: &CsBuilder<Self, F, GC, TB>,
        lookup_parameters: LookupParameters,
    ) {
        match lookup_parameters {
            LookupParameters::NoLookup => {
                panic!("trying to add `no lookup`");
            }
            LookupParameters::TableIdAsVariable { width, .. } => {
                assert!(
                    builder
                        .implementation
                        .parameters
                        .num_columns_under_copy_permutation
                        >= (width as usize) + 1
                );
            }
            LookupParameters::TableIdAsConstant { width, .. } => {
                assert!(
                    builder
                        .implementation
                        .parameters
                        .num_columns_under_copy_permutation
                        >= width as usize
                );
            }
            _ => {
                // there are no checks to made
            }
        }
    }
}

impl<
        F: SmallField,
        P: PrimeFieldLikeVectorized<Base = F>,
        CFG: CSConfig,
        CR: CircuitResolver<F, CFG::ResolverConfig>,
    > CsBuilderImpl<F, CsReferenceImplementationBuilder<F, P, CFG, CR>>
    for CsReferenceImplementationBuilder<F, P, CFG, CR>
{
    type Final<GC: GateConfigurationHolder<F>, TB: StaticToolboxHolder> =
        CSReferenceImplementation<F, P, CFG, GC, TB, CR>;

    type BuildParams<'a> = CR::Arg;

    fn parameters<GC: GateConfigurationHolder<F>, TB: StaticToolboxHolder>(
        builder: &CsBuilder<CsReferenceImplementationBuilder<F, P, CFG, CR>, F, GC, TB>,
    ) -> CSGeometry {
        builder.implementation.parameters
    }

    fn allow_gate<
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        G: Gate<F>,
        TAux: 'static + Send + Sync + Clone,
    >(
        mut builder: CsBuilder<Self, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
        params: <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
        aux_data: TAux,
        // ) -> CsBuilder<Self, F, GC::DescendantHolder<G, TAux>, TB> {
    ) -> CsBuilder<Self, F, (GateTypeEntry<F, G, TAux>, GC), TB> {
        // log!("Adding gate {:?}", std::any::type_name::<G>());

        let this = &mut builder.implementation;

        let new_configuration =
            builder
                .gates_config
                .add_gate::<G, _>(placement_strategy, params.clone(), aux_data);

        if GC::CAN_POSTPONE_DATA_CAPTURE == false {
            let evaluator = G::Evaluator::new_from_parameters(params.clone());

            // depending on the configuration we should place it into corresponding set,
            // and create some extra staff

            match placement_strategy {
                GatePlacementStrategy::UseGeneralPurposeColumns => {
                    this.evaluation_data_over_general_purpose_columns
                        .capture_gate_data::<G>(
                            evaluator,
                            &this.parameters,
                            &mut P::Context::placeholder(),
                        );
                }
                GatePlacementStrategy::UseSpecializedColumns { .. } => {
                    this.evaluation_data_over_specialized_columns
                        .capture_gate_data::<G>(
                            evaluator,
                            placement_strategy,
                            &this.parameters,
                            &mut P::Context::placeholder(),
                        );
                }
            }
        }

        CsBuilder {
            gates_config: new_configuration,
            ..builder
        }
    }

    fn add_tool<
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        M: 'static + Send + Sync + Clone,
        T: 'static + Send + Sync,
    >(
        builder: CsBuilder<CsReferenceImplementationBuilder<F, P, CFG, CR>, F, GC, TB>,
        tool: T,
        // ) -> CsBuilder<CsReferenceImplementationBuilder<F, P, CFG>, F, GC, TB::DescendantHolder<M, T>>
    ) -> CsBuilder<Self, F, GC, (Tool<M, T>, TB)> {
        let new_toolbox = builder.toolbox.add_tool(tool);
        CsBuilder {
            toolbox: new_toolbox,
            ..builder
        }
    }

    type GcWithLookup<GC: GateConfigurationHolder<F>> =
        (GateTypeEntry<F, LookupFormalGate, LookupTooling>, GC);
    // GC::DescendantHolder<LookupFormalGate, LookupTooling>;

    fn allow_lookup<GC: GateConfigurationHolder<F>, TB: StaticToolboxHolder>(
        mut builder: CsBuilder<CsReferenceImplementationBuilder<F, P, CFG, CR>, F, GC, TB>,
        lookup_parameters: super::LookupParameters,
    ) -> CsBuilder<CsReferenceImplementationBuilder<F, P, CFG, CR>, F, Self::GcWithLookup<GC>, TB>
    {
        assert_eq!(
            builder.implementation.lookup_parameters,
            LookupParameters::NoLookup,
            "should only allow lookup once for now"
        );

        Self::ensure_compatible_with_lookup::<GC, TB>(&builder, lookup_parameters);

        let this = &mut builder.implementation;

        assert!(this.lookup_marker_gate_idx.is_none());
        assert!(this
            .evaluation_data_over_general_purpose_columns
            .evaluators_over_general_purpose_columns
            .is_empty());
        assert!(this
            .evaluation_data_over_specialized_columns
            .evaluators_over_specialized_columns
            .is_empty());

        // we are fine by just adding a new gate as the normal one, but modifying the state a little
        // for specific lookup parameters

        this.lookup_marker_gate_idx = Some(0u32);
        this.lookup_parameters = lookup_parameters;

        let (placement_strategy, num_variables, num_constants, share_table_id) =
            match lookup_parameters {
                LookupParameters::NoLookup => {
                    panic!("trying to allow `no lookup`");
                }
                LookupParameters::TableIdAsVariable {
                    width,
                    share_table_id,
                } => {
                    assert!(
                        share_table_id == false,
                        "other option is not yet implemented"
                    );
                    // we need to resize multiplicities
                    assert!(
                        builder
                            .implementation
                            .parameters
                            .num_columns_under_copy_permutation
                            >= (width + 1) as usize
                    );

                    (
                        GatePlacementStrategy::UseGeneralPurposeColumns,
                        (width + 1) as usize,
                        0,
                        share_table_id,
                    )
                }
                LookupParameters::TableIdAsConstant {
                    width,
                    share_table_id,
                } => {
                    assert!(
                        share_table_id == true,
                        "other option is not yet implemented"
                    );
                    assert!(
                        builder
                            .implementation
                            .parameters
                            .num_columns_under_copy_permutation
                            >= width as usize
                    );

                    (
                        GatePlacementStrategy::UseGeneralPurposeColumns,
                        width as usize,
                        1,
                        share_table_id,
                    )
                }
                LookupParameters::UseSpecializedColumnsWithTableIdAsVariable {
                    width,
                    num_repetitions,
                    share_table_id,
                } => {
                    assert!(
                        share_table_id == false,
                        "other option is not yet implemented"
                    );

                    (
                        GatePlacementStrategy::UseSpecializedColumns {
                            num_repetitions,
                            share_constants: false,
                        },
                        (width + 1) as usize,
                        0,
                        share_table_id,
                    )
                }
                LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                    width,
                    num_repetitions,
                    share_table_id,
                } => {
                    assert!(
                        share_table_id == true,
                        "other option is not yet implemented"
                    );

                    (
                        GatePlacementStrategy::UseSpecializedColumns {
                            num_repetitions,
                            share_constants: share_table_id,
                        },
                        width as usize,
                        1,
                        share_table_id,
                    )
                }
            };

        Self::allow_gate::<GC, TB, LookupFormalGate, LookupTooling>(
            builder,
            placement_strategy,
            (num_variables, num_constants, share_table_id),
            (Vec::with_capacity(32), 0),
        )
    }

    fn build<
        'a,
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        ARG: Into<Self::BuildParams<'a>>,
    >(
        builder: CsBuilder<Self, F, GC, TB>,
        params: ARG,
    ) -> Self::Final<GC, TB> {
        let CsReferenceImplementationBuilder {
            parameters,
            lookup_parameters,
            max_trace_len,
            lookup_marker_gate_idx,
            evaluation_data_over_general_purpose_columns,
            evaluation_data_over_specialized_columns,
            ..
        } = builder.implementation;

        assert!(
            CFG::SetupConfig::KEEP_SETUP || CFG::WitnessConfig::EVALUATE_WITNESS,
            "CS must do meaningful work"
        );
        assert!(max_trace_len.is_power_of_two());

        let gates_application_sets = if CFG::SetupConfig::KEEP_SETUP {
            Vec::with_capacity(max_trace_len)
        } else {
            vec![]
        };

        let mut row_cleanups = Vec::with_capacity(16);
        builder
            .gates_config
            .gather_row_finalization_functions::<CSReferenceImplementation<F, P, CFG, GC, TB, CR>>(
                &mut row_cleanups,
            );

        let mut columns_cleanups = Vec::with_capacity(16);
        builder
            .gates_config
            .gather_columns_finalization_functions::<CSReferenceImplementation<F, P, CFG, GC, TB,
            CR>>(
                &mut columns_cleanups,
            );

        let variables_storage = RwLock::new(CR::new(params.into()));

        let mut evaluation_data_over_general_purpose_columns =
            evaluation_data_over_general_purpose_columns;
        let mut evaluation_data_over_specialized_columns = evaluation_data_over_specialized_columns;

        if GC::CAN_POSTPONE_DATA_CAPTURE == true {
            builder
                .gates_config
                .capture_general_purpose_gate_evaluator_data(
                    &parameters,
                    &mut evaluation_data_over_general_purpose_columns,
                    &mut P::Context::placeholder(),
                );

            builder
                .gates_config
                .capture_specialized_gate_evaluator_data(
                    &parameters,
                    &mut evaluation_data_over_specialized_columns,
                    &mut P::Context::placeholder(),
                );
        }

        // now we can create storages

        let total_variables = parameters.num_columns_under_copy_permutation
            + evaluation_data_over_specialized_columns.total_num_variables_for_specialized_columns;
        let total_witnesses = parameters.num_witness_columns
            + evaluation_data_over_specialized_columns.total_num_witnesses_for_specialized_columns;
        let total_specialized_constants =
            evaluation_data_over_specialized_columns.total_num_constants_for_specialized_columns;

        let copy_permutation_data = if CFG::SetupConfig::KEEP_SETUP {
            let mut result = vec![
                vec![Variable::placeholder(); max_trace_len];
                parameters.num_columns_under_copy_permutation
            ];

            result.resize(total_variables, Vec::with_capacity(max_trace_len));

            result
        } else {
            vec![vec![]]
        };

        let witness_placement_data = if CFG::SetupConfig::KEEP_SETUP {
            let mut result =
                vec![vec![Witness::placeholder(); max_trace_len]; parameters.num_witness_columns];

            result.resize(total_witnesses, Vec::with_capacity(max_trace_len));

            result
        } else {
            vec![vec![]]
        };

        let constants_requested_per_row = if CFG::SetupConfig::KEEP_SETUP {
            Vec::with_capacity(max_trace_len)
        } else {
            vec![]
        };

        let constants_for_gates_in_specialized_mode = if CFG::SetupConfig::KEEP_SETUP {
            vec![Vec::with_capacity(max_trace_len); total_specialized_constants]
        } else {
            vec![vec![]]
        };

        CSReferenceImplementation::<F, P, CFG, GC, TB, CR> {
            gates_configuration: builder.gates_config,
            dynamic_tools: HashMap::with_capacity(16),
            variables_storage,
            parameters,
            lookup_parameters,
            evaluation_data_over_general_purpose_columns,
            evaluation_data_over_specialized_columns,
            specialized_gates_rough_stats: HashMap::with_capacity(16),
            gates_application_sets,
            copy_permutation_data,
            witness_placement_data,
            next_available_row: 0,
            next_available_place_idx: 0,
            next_lookup_table_index: INITIAL_LOOKUP_TABLE_ID_VALUE,
            lookup_marker_gate_idx,
            constants_requested_per_row,
            constants_for_gates_in_specialized_mode,
            lookup_table_marker_into_id: HashMap::with_capacity(32),
            lookup_tables: Vec::with_capacity(32),
            lookup_multiplicities: Vec::with_capacity(8),
            table_ids_as_variables: Vec::with_capacity(32),
            public_inputs: Vec::with_capacity(8),
            max_trace_len,
            static_toolbox: builder.toolbox,
            row_cleanups,
            columns_cleanups,
        }
    }
}
