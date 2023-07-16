use super::*;

use crate::cs::traits::evaluator::*;
use crate::cs::traits::gate::*;
use std::any::TypeId;

pub struct EvaluationDataOverGeneralPurposeColumns<
    F: SmallField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
> {
    pub gate_type_ids_for_general_purpose_columns: Vec<TypeId>,
    pub evaluators_over_general_purpose_columns: Vec<TypeErasedGateEvaluationFunction<F, P>>,
    pub(crate) general_purpose_evaluators_comparison_functions:
        HashMap<TypeId, Vec<(GateBatchEvaluationComparisonFunction, usize)>>,
    pub(crate) evaluator_type_id_into_evaluator_index_over_general_purpose_columns:
        HashMap<TypeId, usize>,
}

impl<F: SmallField, P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>>
    EvaluationDataOverGeneralPurposeColumns<F, P>
{
    pub(crate) fn new() -> Self {
        Self {
            gate_type_ids_for_general_purpose_columns: Vec::with_capacity(16),
            evaluators_over_general_purpose_columns: Vec::with_capacity(16),
            general_purpose_evaluators_comparison_functions: HashMap::with_capacity(16),
            evaluator_type_id_into_evaluator_index_over_general_purpose_columns:
                HashMap::with_capacity(16),
        }
    }

    pub(crate) fn capture_gate_data<G: Gate<F>>(
        &mut self,
        evaluator: G::Evaluator,
        parameters: &CSGeometry,
        ctx: &mut P::Context,
    ) {
        let gate_type_id = TypeId::of::<G>();
        let evaluator_type_id = TypeId::of::<G::Evaluator>();
        let placement_strategy = GatePlacementStrategy::UseGeneralPurposeColumns;

        if let Some(comparison_fns) = self
            .general_purpose_evaluators_comparison_functions
            .get_mut(&evaluator_type_id)
        {
            let (dynamic_evaluator, comparator) = TypeErasedGateEvaluationFunction::from_evaluator(
                evaluator,
                parameters,
                placement_strategy,
                ctx,
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
                let idx = self.evaluators_over_general_purpose_columns.len();
                self.evaluators_over_general_purpose_columns
                    .push(dynamic_evaluator);
                self.evaluator_type_id_into_evaluator_index_over_general_purpose_columns
                    .insert(evaluator_type_id, idx);
                comparison_fns.push((comparator, idx));
            }

            self.gate_type_ids_for_general_purpose_columns
                .push(gate_type_id);
        } else {
            // new one
            let idx = self.evaluators_over_general_purpose_columns.len();
            let (dynamic_evaluator, comparator) = TypeErasedGateEvaluationFunction::from_evaluator(
                evaluator,
                parameters,
                placement_strategy,
                ctx,
            );
            self.evaluators_over_general_purpose_columns
                .push(dynamic_evaluator);
            self.gate_type_ids_for_general_purpose_columns
                .push(gate_type_id);
            self.evaluator_type_id_into_evaluator_index_over_general_purpose_columns
                .insert(evaluator_type_id, idx);
            self.general_purpose_evaluators_comparison_functions
                .insert(evaluator_type_id, vec![(comparator, idx)]);
        }
    }
}

pub struct EvaluationDataOverSpecializedColumns<
    F: SmallField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
> {
    pub gate_type_ids_for_specialized_columns: Vec<TypeId>,
    pub evaluators_over_specialized_columns: Vec<TypeErasedGateEvaluationFunction<F, P>>,
    pub offsets_for_specialized_evaluators: Vec<(PerChunkOffset, PerChunkOffset, usize)>,
    pub gate_type_id_into_evaluator_index_over_specialized_columns: HashMap<TypeId, usize>,
    pub total_num_variables_for_specialized_columns: usize,
    pub total_num_witnesses_for_specialized_columns: usize,
    pub total_num_constants_for_specialized_columns: usize,
}

impl<F: SmallField, P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>>
    EvaluationDataOverSpecializedColumns<F, P>
{
    pub fn new() -> Self {
        Self {
            offsets_for_specialized_evaluators: Vec::with_capacity(16),
            gate_type_ids_for_specialized_columns: Vec::with_capacity(16),
            evaluators_over_specialized_columns: Vec::with_capacity(16),
            gate_type_id_into_evaluator_index_over_specialized_columns: HashMap::with_capacity(16),
            total_num_variables_for_specialized_columns: 0,
            total_num_witnesses_for_specialized_columns: 0,
            total_num_constants_for_specialized_columns: 0,
        }
    }

    pub(crate) fn capture_gate_data<G: Gate<F>>(
        &mut self,
        evaluator: G::Evaluator,
        placement_strategy: GatePlacementStrategy,
        parameters: &CSGeometry,
        ctx: &mut P::Context,
    ) {
        let gate_type_id = TypeId::of::<G>();

        let GatePlacementStrategy::UseSpecializedColumns {
            num_repetitions,
            share_constants,
        } = placement_strategy
        else {
            unreachable!()
        };

        // we always add an evaluator

        let (dynamic_evaluator, _comparator) = TypeErasedGateEvaluationFunction::from_evaluator(
            evaluator.clone(),
            parameters,
            placement_strategy,
            ctx,
        );

        // we need to extend copy-permutation data and witness placement data,
        // as well as keep track on offsets into them

        let idx = self.evaluators_over_specialized_columns.len();
        self.gate_type_ids_for_specialized_columns
            .push(gate_type_id);
        self.evaluators_over_specialized_columns
            .push(dynamic_evaluator);
        self.gate_type_id_into_evaluator_index_over_specialized_columns
            .insert(gate_type_id, idx);

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

        // to properly place constants we need the following:
        // - on what offset to start placement
        // - do we need to offset based on number of repetitions or not
        // - how many constants we have available per repetition in total

        let initial_offset = PerChunkOffset {
            variables_offset: parameters.num_columns_under_copy_permutation
                + self.total_num_variables_for_specialized_columns,
            witnesses_offset: parameters.num_witness_columns
                + self.total_num_witnesses_for_specialized_columns,
            constants_offset: self.total_num_constants_for_specialized_columns, // we use separate vector for them
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

        self.offsets_for_specialized_evaluators.push((
            initial_offset,
            offset_per_repetition,
            total_constants_available,
        ));

        self.total_num_variables_for_specialized_columns += total_width.num_variables;
        self.total_num_witnesses_for_specialized_columns += total_width.num_witnesses;
        self.total_num_constants_for_specialized_columns += total_width.num_constants;
    }
}
