use crate::cs::implementations::verifier::VerifierPolyStorage;
use crate::cs::implementations::verifier::VerifierRelationDestination;
use crate::cs::traits::evaluator::GatePurpose;
use crate::cs::traits::evaluator::GenericDynamicEvaluatorOverGeneralPurposeColumns;
use crate::cs::traits::evaluator::GenericDynamicEvaluatorOverSpecializedColumns;
use crate::cs::traits::evaluator::*;
use crate::cs::traits::gate::GatePlacementStrategy;
use crate::cs::GateTypeEntry;
use crate::cs::Tool;
use crate::cs::{
    cs_builder::{CsBuilder, CsBuilderImpl},
    gates::{lookup_marker::LookupFormalGate, LookupTooling},
    traits::{
        evaluator::{GateBatchEvaluationComparisonFunction, GateConstraintEvaluator},
        gate::Gate,
    },
    CSGeometry, GateConfigurationHolder, LookupParameters, StaticToolboxHolder,
};
use crate::gadgets::num::prime_field_like::*;
use crate::{
    cs::traits::{
        cs::ConstraintSystem,
        evaluator::{GatePlacementType, PerChunkOffset},
    },
    field::{FieldExtension, SmallField},
};
use derivative::*;
use std::{any::TypeId, collections::HashMap};

#[derive(Derivative)]
#[derivative(Debug)]
pub(crate) struct TypeErasedGateEvaluationRecursiveVerificationFunction<
    F: SmallField,
    EXT: FieldExtension<2, BaseField = F>,
    CS: ConstraintSystem<F> + 'static,
> {
    pub(crate) debug_name: String,
    pub(crate) evaluator_type_id: TypeId,
    pub(crate) gate_purpose: GatePurpose,
    pub(crate) max_constraint_degree: usize,
    pub(crate) num_quotient_terms: usize,
    pub(crate) num_required_constants: usize,
    pub(crate) total_quotient_terms_over_all_repetitions: usize,
    pub(crate) num_repetitions_on_row: usize,
    pub(crate) placement_type: GatePlacementType,
    #[derivative(Debug = "ignore")]
    pub(crate) columnwise_satisfiability_function: Option<
        Box<
            dyn GenericDynamicEvaluatorOverSpecializedColumns<
                    F,
                    NumExtAsFieldWrapper<F, EXT, CS>,
                    VerifierPolyStorage<F, NumExtAsFieldWrapper<F, EXT, CS>>,
                    VerifierRelationDestination<F, NumExtAsFieldWrapper<F, EXT, CS>>,
                >
                + 'static
                + Send
                + Sync,
        >,
    >,
    #[derivative(Debug = "ignore")]
    pub(crate) rowwise_satisfiability_function: Option<
        Box<
            dyn GenericDynamicEvaluatorOverGeneralPurposeColumns<
                    F,
                    NumExtAsFieldWrapper<F, EXT, CS>,
                    VerifierPolyStorage<F, NumExtAsFieldWrapper<F, EXT, CS>>,
                    VerifierRelationDestination<F, NumExtAsFieldWrapper<F, EXT, CS>>,
                >
                + 'static
                + Send
                + Sync,
        >,
    >,
}

impl<F: SmallField, EXT: FieldExtension<2, BaseField = F>, CS: ConstraintSystem<F> + 'static>
    TypeErasedGateEvaluationRecursiveVerificationFunction<F, EXT, CS>
{
    pub fn from_evaluator<E: GateConstraintEvaluator<F>>(
        cs: &mut CS,
        evaluator: E,
        geometry: &CSGeometry,
        placement_strategy: GatePlacementStrategy,
    ) -> (Self, GateBatchEvaluationComparisonFunction) {
        let debug_name = evaluator.instance_name();
        let evaluator_type_id = std::any::TypeId::of::<E>();
        let gate_purpose = E::gate_purpose();
        let max_constraint_degree = E::max_constraint_degree();
        let num_quotient_terms = E::num_quotient_terms();
        let num_required_constants = evaluator.num_required_constants_in_geometry(geometry);
        let placement_type = evaluator.placement_type();
        let mut final_per_chunk_offset = PerChunkOffset::zero();
        let (num_repetitions_on_row, total_quotient_terms_over_all_repetitions) =
            match placement_strategy {
                GatePlacementStrategy::UseGeneralPurposeColumns => {
                    let num_repetitions_on_row = evaluator.num_repetitions_in_geometry(geometry);
                    if let GatePlacementType::MultipleOnRow { per_chunk_offset } = &placement_type {
                        debug_assert!(
                            num_repetitions_on_row > 0,
                            "invalid for evaluator {}",
                            std::any::type_name::<E>()
                        );
                        final_per_chunk_offset = *per_chunk_offset;
                    } else {
                        debug_assert_eq!(num_repetitions_on_row, 1);
                    }

                    let total_quotient_terms_in_geometry =
                        evaluator.total_quotient_terms_in_geometry(geometry);

                    (num_repetitions_on_row, total_quotient_terms_in_geometry)
                }
                GatePlacementStrategy::UseSpecializedColumns {
                    num_repetitions,
                    share_constants,
                } => {
                    let principal_width = evaluator.instance_width();
                    final_per_chunk_offset = PerChunkOffset {
                        variables_offset: principal_width.num_variables,
                        witnesses_offset: principal_width.num_witnesses,
                        constants_offset: principal_width.num_constants,
                    };
                    if share_constants {
                        final_per_chunk_offset.constants_offset = 0;
                    }

                    (num_repetitions, num_repetitions * num_quotient_terms)
                }
            };

        let (specialized_satisfiability_evaluator, general_purpose_satisfiability_evaluator) =
            match placement_strategy {
                GatePlacementStrategy::UseSpecializedColumns { .. } => {
                    let specialized_evaluator = GenericColumnwiseEvaluator {
                        evaluator: evaluator.clone(),
                        global_constants: evaluator.create_global_constants(cs),
                        num_repetitions: num_repetitions_on_row,
                        per_chunk_offset: final_per_chunk_offset,
                    };

                    // dbg!(&specialized_evaluator);

                    (
                        Some(Box::new(specialized_evaluator)
                            as Box<
                                dyn GenericDynamicEvaluatorOverSpecializedColumns<
                                        F,
                                        NumExtAsFieldWrapper<F, EXT, CS>,
                                        VerifierPolyStorage<F, NumExtAsFieldWrapper<F, EXT, CS>>,
                                        VerifierRelationDestination<
                                            F,
                                            NumExtAsFieldWrapper<F, EXT, CS>,
                                        >,
                                    >
                                    + 'static
                                    + Send
                                    + Sync,
                            >),
                        None,
                    )
                }
                GatePlacementStrategy::UseGeneralPurposeColumns => {
                    let general_purpose_evaluator = GenericRowwiseEvaluator {
                        evaluator: evaluator.clone(),
                        global_constants: evaluator.create_global_constants(cs),
                        num_repetitions: num_repetitions_on_row,
                        per_chunk_offset: final_per_chunk_offset,
                    };

                    // dbg!(&general_purpose_evaluator);

                    (
                        None,
                        Some(Box::new(general_purpose_evaluator)
                            as Box<
                                dyn GenericDynamicEvaluatorOverGeneralPurposeColumns<
                                        F,
                                        NumExtAsFieldWrapper<F, EXT, CS>,
                                        VerifierPolyStorage<F, NumExtAsFieldWrapper<F, EXT, CS>>,
                                        VerifierRelationDestination<
                                            F,
                                            NumExtAsFieldWrapper<F, EXT, CS>,
                                        >,
                                    >
                                    + 'static
                                    + Send
                                    + Sync,
                            >),
                    )
                }
            };

        let this_params = evaluator.unique_params();

        let comparison_fn = move |other_evaluator: &dyn std::any::Any| -> bool {
            assert_eq!(other_evaluator.type_id(), evaluator_type_id);
            let other_evaluator: &E = other_evaluator.downcast_ref().expect("must downcast");

            this_params == other_evaluator.unique_params()
        };

        let comparator = GateBatchEvaluationComparisonFunction {
            type_id: evaluator_type_id,
            evaluator_dyn: Box::new(evaluator),
            equality_fn: Box::new(comparison_fn),
        };

        let new = Self {
            debug_name,
            evaluator_type_id,
            gate_purpose,
            max_constraint_degree,
            num_quotient_terms,
            num_required_constants,
            total_quotient_terms_over_all_repetitions,
            num_repetitions_on_row,
            placement_type,
            columnwise_satisfiability_function: specialized_satisfiability_evaluator,
            rowwise_satisfiability_function: general_purpose_satisfiability_evaluator,
        };

        (new, comparator)
    }
}

pub struct CsRecursiveVerifierBuilder<
    'a,
    F: SmallField,
    EXT: FieldExtension<2, BaseField = F>,
    CS: ConstraintSystem<F> + 'static,
> {
    pub(crate) cs: &'a mut CS,

    pub parameters: CSGeometry,
    pub lookup_parameters: LookupParameters,

    pub(crate) gate_type_ids_for_specialized_columns: Vec<TypeId>,
    pub(crate) evaluators_over_specialized_columns:
        Vec<TypeErasedGateEvaluationRecursiveVerificationFunction<F, EXT, CS>>,
    pub(crate) offsets_for_specialized_evaluators: Vec<(PerChunkOffset, PerChunkOffset, usize)>,

    pub(crate) evaluators_over_general_purpose_columns:
        Vec<TypeErasedGateEvaluationRecursiveVerificationFunction<F, EXT, CS>>,
    pub(crate) general_purpose_evaluators_comparison_functions:
        HashMap<TypeId, Vec<(GateBatchEvaluationComparisonFunction, usize)>>,

    pub(crate) total_num_variables_for_specialized_columns: usize,
    pub(crate) total_num_witnesses_for_specialized_columns: usize,
    pub(crate) total_num_constants_for_specialized_columns: usize,
}

impl<
        'a,
        F: SmallField,
        EXT: FieldExtension<2, BaseField = F>,
        CS: ConstraintSystem<F> + 'static,
    > CsRecursiveVerifierBuilder<'a, F, EXT, CS>
{
    pub fn new_from_parameters(cs: &'a mut CS, parameters: CSGeometry) -> Self {
        Self {
            cs,

            parameters,
            lookup_parameters: LookupParameters::NoLookup,

            gate_type_ids_for_specialized_columns: Vec::with_capacity(16),
            evaluators_over_specialized_columns: Vec::with_capacity(16),
            offsets_for_specialized_evaluators: Vec::with_capacity(16),

            evaluators_over_general_purpose_columns: Vec::with_capacity(16),
            general_purpose_evaluators_comparison_functions: HashMap::with_capacity(16),

            total_num_variables_for_specialized_columns: 0,
            total_num_witnesses_for_specialized_columns: 0,
            total_num_constants_for_specialized_columns: 0,
        }
    }
}

use super::recursive_verifier::*;

impl<
        'a,
        F: SmallField,
        EXT: FieldExtension<2, BaseField = F>,
        CS: ConstraintSystem<F> + 'static,
    > CsBuilderImpl<F, CsRecursiveVerifierBuilder<'a, F, EXT, CS>>
    for CsRecursiveVerifierBuilder<'a, F, EXT, CS>
{
    type Final<GC: GateConfigurationHolder<F>, TB: StaticToolboxHolder> =
        RecursiveVerifier<F, EXT, CS>;

    type BuildParams<'b> = ();

    fn parameters<GC: GateConfigurationHolder<F>, TB: StaticToolboxHolder>(
        builder: &CsBuilder<Self, F, GC, TB>,
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
        let evaluator_type_id = TypeId::of::<G::Evaluator>();
        let gate_type_id = TypeId::of::<G>();
        let evaluator = G::Evaluator::new_from_parameters(params.clone());

        // depending on the configuration we should place it into corresponding set,
        // and create some extra staff

        match placement_strategy {
            GatePlacementStrategy::UseGeneralPurposeColumns => {
                // we should batch gates that have the same evaluator
                if let Some(comparison_fns) = this
                    .general_purpose_evaluators_comparison_functions
                    .get_mut(&evaluator_type_id)
                {
                    let (dynamic_evaluator, comparator) =
                        TypeErasedGateEvaluationRecursiveVerificationFunction::from_evaluator(
                            this.cs,
                            evaluator,
                            &this.parameters,
                            placement_strategy,
                        );

                    let mut existing_idx = None;
                    for (other_comparator, idx) in comparison_fns.iter() {
                        if other_comparator.equals_to(&comparator) {
                            existing_idx = Some(*idx);
                            break;
                        }
                    }

                    if let Some(_existing_idx) = existing_idx {
                        // nothing, same evaluator
                    } else {
                        if comparison_fns.len() > 0 {
                            panic!("not yet supported");
                        }
                        let idx = this.evaluators_over_general_purpose_columns.len();
                        this.evaluators_over_general_purpose_columns
                            .push(dynamic_evaluator);
                        // evaluator_type_id_into_evaluator_index_over_general_purpose_columns.insert(evaluator_type_id, idx);
                        comparison_fns.push((comparator, idx));
                    }

                    // gate_type_ids_for_general_purpose_columns.push(gate_type_id);
                } else {
                    // new one
                    let idx = this.evaluators_over_general_purpose_columns.len();
                    let (dynamic_evaluator, comparator) =
                        TypeErasedGateEvaluationRecursiveVerificationFunction::from_evaluator(
                            this.cs,
                            evaluator,
                            &this.parameters,
                            placement_strategy,
                        );
                    this.evaluators_over_general_purpose_columns
                        .push(dynamic_evaluator);
                    // gate_type_ids_for_general_purpose_columns.push(gate_type_id);
                    // evaluator_type_id_into_evaluator_index_over_general_purpose_columns.insert(evaluator_type_id, idx);
                    this.general_purpose_evaluators_comparison_functions
                        .insert(evaluator_type_id, vec![(comparator, idx)]);
                }
            }
            GatePlacementStrategy::UseSpecializedColumns {
                num_repetitions,
                share_constants,
            } => {
                // we always add an evaluator

                let (dynamic_evaluator, _comparator) =
                    TypeErasedGateEvaluationRecursiveVerificationFunction::from_evaluator(
                        this.cs,
                        evaluator.clone(),
                        &this.parameters,
                        placement_strategy,
                    );

                // we need to extend copy-permutation data and witness placement data,
                // as well as keep track on offsets into them

                let _idx = this.evaluators_over_specialized_columns.len();
                this.gate_type_ids_for_specialized_columns
                    .push(gate_type_id);
                this.evaluators_over_specialized_columns
                    .push(dynamic_evaluator);
                // gate_type_id_into_evaluator_index_over_specialized_columns.insert(gate_type_id, idx);

                let principal_width = evaluator.instance_width();
                let mut total_width = principal_width;

                for _ in 1..num_repetitions {
                    total_width.num_variables += principal_width.num_variables;
                    total_width.num_witnesses += principal_width.num_witnesses;
                    if share_constants == false {
                        total_width.num_constants += principal_width.num_constants;
                    }
                }

                let total_constants_available = principal_width.num_constants;

                if share_constants {
                    match evaluator.placement_type() {
                        GatePlacementType::MultipleOnRow {
                            per_chunk_offset: _,
                        } => {}
                        GatePlacementType::UniqueOnRow => {
                            panic!("Can not share constants if placement type is unique");
                        }
                    }
                }

                let initial_offset = PerChunkOffset {
                    variables_offset: this.parameters.num_columns_under_copy_permutation
                        + this.total_num_variables_for_specialized_columns,
                    witnesses_offset: this.parameters.num_witness_columns
                        + this.total_num_witnesses_for_specialized_columns,
                    constants_offset: this.total_num_constants_for_specialized_columns, // we use separate vector for them
                };

                let offset_per_repetition = if share_constants == false {
                    PerChunkOffset {
                        variables_offset: principal_width.num_variables,
                        witnesses_offset: principal_width.num_witnesses,
                        constants_offset: principal_width.num_constants,
                    }
                } else {
                    let offset_per_repetition = match evaluator.placement_type() {
                        GatePlacementType::MultipleOnRow { per_chunk_offset } => per_chunk_offset,
                        GatePlacementType::UniqueOnRow => {
                            panic!("Can not share constants if placement type is unique");
                        }
                    };

                    assert_eq!(
                        offset_per_repetition.variables_offset,
                        principal_width.num_variables
                    );
                    assert_eq!(
                        offset_per_repetition.witnesses_offset,
                        principal_width.num_witnesses
                    );

                    // offset_per_repetition.variables_offset = principal_width.num_variables;
                    // offset_per_repetition.witnesses_offset = principal_width.num_witnesses;
                    // and we only leave constants untouched

                    offset_per_repetition
                };

                this.offsets_for_specialized_evaluators.push((
                    initial_offset,
                    offset_per_repetition,
                    total_constants_available,
                ));

                this.total_num_variables_for_specialized_columns += total_width.num_variables;
                this.total_num_witnesses_for_specialized_columns += total_width.num_witnesses;
                this.total_num_constants_for_specialized_columns += total_width.num_constants;
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
        builder: CsBuilder<Self, F, GC, TB>,
        tool: T,
        // ) -> CsBuilder<Self, F, GC, TB::DescendantHolder<M, T>> {
    ) -> CsBuilder<Self, F, GC, (Tool<M, T>, TB)> {
        // TODO: toolbox is not used in the verifier, so perhaps it should be
        // moved out to the builder impl so it would not get in the way and just
        // hold the type in the phantom.
        let new_toolbox = builder.toolbox.add_tool(tool);

        CsBuilder {
            toolbox: new_toolbox,
            ..builder
        }
    }

    // type GcWithLookup<GC: GateConfigurationHolder<F>> = GC;
    type GcWithLookup<GC: GateConfigurationHolder<F>> =
        (GateTypeEntry<F, LookupFormalGate, LookupTooling>, GC);
    // GC::DescendantHolder<LookupFormalGate, LookupTooling>;

    fn allow_lookup<GC: GateConfigurationHolder<F>, TB: StaticToolboxHolder>(
        builder: CsBuilder<Self, F, GC, TB>,
        lookup_parameters: LookupParameters,
    ) -> CsBuilder<Self, F, Self::GcWithLookup<GC>, TB> {
        let mut builder = builder;
        builder.implementation.lookup_parameters = lookup_parameters;

        let (placement_strategy, num_variables, num_constants, share_table_id) =
            match lookup_parameters {
                LookupParameters::NoLookup => {
                    // this is formal

                    (
                        GatePlacementStrategy::UseSpecializedColumns {
                            num_repetitions: 0,
                            share_constants: false,
                        },
                        0,
                        0,
                        false,
                    )
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

        Self::allow_gate(
            builder,
            placement_strategy,
            (num_variables, num_constants, share_table_id),
            (Vec::with_capacity(32), 0),
        )
    }

    fn build<
        'b,
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        ARG: Into<Self::BuildParams<'b>>,
    >(
        builder: CsBuilder<Self, F, GC, TB>,
        _params: ARG,
    ) -> Self::Final<GC, TB> {
        let this: CsRecursiveVerifierBuilder<F, EXT, CS> = builder.implementation;

        let new = RecursiveVerifierProxy::<F, EXT, CS, GC, TB> {
            parameters: this.parameters,
            lookup_parameters: this.lookup_parameters,

            gates_configuration: builder.gates_config,
            gate_type_ids_for_specialized_columns: this.gate_type_ids_for_specialized_columns,
            evaluators_over_specialized_columns: this.evaluators_over_specialized_columns,
            offsets_for_specialized_evaluators: this.offsets_for_specialized_evaluators,

            evaluators_over_general_purpose_columns: this.evaluators_over_general_purpose_columns,

            total_num_variables_for_specialized_columns: this
                .total_num_variables_for_specialized_columns,
            total_num_witnesses_for_specialized_columns: this
                .total_num_witnesses_for_specialized_columns,
            total_num_constants_for_specialized_columns: this
                .total_num_constants_for_specialized_columns,

            _marker: std::marker::PhantomData,
        };

        new.into_verifier()
    }
}
