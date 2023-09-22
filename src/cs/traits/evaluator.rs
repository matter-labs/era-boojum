use std::any::TypeId;
use std::hash::Hash;

use super::destination_view::{EvaluationDestination, EvaluationDestinationDrivable};
use super::gate::GatePlacementStrategy;
use super::trace_source::{TraceSource, TraceSourceDerivable};
use super::*;
use crate::field::traits::field_like::BaseField;
use crate::field::PrimeField;

/// Defines the column composition of a gate.
#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GatePrincipalInstanceWidth {
    pub num_variables: usize,
    pub num_witnesses: usize,
    pub num_constants: usize,
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PerChunkOffset {
    pub variables_offset: usize,
    pub witnesses_offset: usize,
    pub constants_offset: usize,
}

impl PerChunkOffset {
    pub const fn zero() -> Self {
        Self {
            variables_offset: 0,
            witnesses_offset: 0,
            constants_offset: 0,
        }
    }

    #[inline]
    pub fn add_offset(&mut self, other: &Self) {
        self.variables_offset += other.variables_offset;
        self.witnesses_offset += other.witnesses_offset;
        self.constants_offset += other.constants_offset;
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GatePlacementType {
    UniqueOnRow,
    MultipleOnRow { per_chunk_offset: PerChunkOffset },
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GatePurpose {
    Evaluatable {
        max_constraint_degree: usize,
        num_quotient_terms: usize,
    },
    MarkerNeedsSelector,   // Nop, Lookup
    MarkerWithoutSelector, // Public input
}

impl GatePurpose {
    pub const fn needs_selector(&self) -> bool {
        match self {
            GatePurpose::Evaluatable {
                max_constraint_degree,
                num_quotient_terms,
            } => {
                debug_assert!(*max_constraint_degree > 0 && *num_quotient_terms > 0);

                true
            }
            GatePurpose::MarkerNeedsSelector => true,
            GatePurpose::MarkerWithoutSelector => false,
        }
    }
}

pub trait ConstantsDescription<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
>
{
    fn external_description(&self) -> Vec<P>;
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLike<Base = F>>
    ConstantsDescription<F, P> for ()
{
    fn external_description(&self) -> Vec<P> {
        vec![]
    }
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLike<Base = F>, const N: usize>
    ConstantsDescription<F, P> for [P; N]
{
    fn external_description(&self) -> Vec<P> {
        Vec::from_iter(self.iter().copied())
    }
}

// this is 100% NOT object safe trait, by design
pub trait GateConstraintEvaluator<
    F: PrimeField
>:
    // some traits to ensure generic convenience
    Sized + Clone + 'static + Send + Sync + std::fmt::Debug + std::any::Any
    // and we also want equality for the following reason: there can be evaluator TYPE
    // that has a generic parametrizable relation, but when we have two such evaluators in the circuit
    // those will produce SEPARATE sets of evaluations into quotient
    + PartialEq + Eq
    // and we want to make a verification key out of it somehow, so we need to serialize
    // but serialization format should also be proxy, so we can use dynamic programming
    // in verifier
{
    // we want some serializable structure to later construct the evaluator in verifier
    type UniqueParameterizationParams: 'static + Clone + Send + Sync + PartialEq + Eq + serde::Serialize + serde::de::DeserializeOwned + Hash;

    // some constructor
    fn new_from_parameters(params: Self::UniqueParameterizationParams) -> Self;
    fn unique_params(&self) -> Self::UniqueParameterizationParams;

    type GlobalConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>>: 'static + Send + Sync + Clone;

    fn create_global_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>>(
        &self,
        ctx: &mut P::Context,
    ) -> Self::GlobalConstants<P>;

    // in general every gate can define it over fixed number of elements,
    // but for trait definition we are enough to have AsRef only for basic
    // sanity checks
    type RowSharedConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>>: ConstantsDescription<F, P> + 'static + Send + Sync;

    fn load_row_shared_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>, S: TraceSource<F, P>>(
        &self,
        trace_source: &S,
        ctx: &mut P::Context,
    ) -> Self::RowSharedConstants<P>;

    // evaluate once modulo GatePlacementType. If GatePlacementType::MultipleOnRow is used it will be called many times
    // by external driver to evaluate every subplacement
    fn evaluate_once<P: field::traits::field_like::PrimeFieldLike<Base = F>, S: TraceSource<F, P>, D: EvaluationDestination<F, P>>(
        &self,
        trace_source: &S,
        destination: &mut D,
        row_constants: &Self::RowSharedConstants<P>,
        global_constants: &Self::GlobalConstants<P>,
        ctx: &mut P::Context,
    );

    // default implementation to evaluate over row, but without moving to another row, in case of placement
    // over general purpose columns
    #[inline(always)]
    fn evaluate_row<P: field::traits::field_like::PrimeFieldLike<Base = F>, S: TraceSourceDerivable<F, P>, D: EvaluationDestination<F, P>>(
        &self,
        evaluation_view: &mut S,
        destination: &mut D,
        geometry: &CSGeometry,
        ctx: &mut P::Context,
    ) {
        let global_constants = self.create_global_constants(ctx);
        match self.placement_type() {
            GatePlacementType::UniqueOnRow => {
            debug_assert_eq!(self.num_repetitions_in_geometry(geometry), 1);
                let constants = self.load_row_shared_constants(&*evaluation_view, ctx);
                self.evaluate_once(
                    &*evaluation_view,
                    destination,
                    &constants,
                    &global_constants,
                    ctx,
                );
            },
            GatePlacementType::MultipleOnRow { per_chunk_offset } => {
                let num_repetitions_per_row = self.num_repetitions_in_geometry(geometry);
                evaluation_view.reset_gate_chunk_offset();
                let constants = self.load_row_shared_constants(&*evaluation_view, ctx);
                for _chunk_idx in 0..num_repetitions_per_row {
                    self.evaluate_once(
                        &*evaluation_view,
                        destination,
                        &constants,
                        &global_constants,
                        ctx,
                    );

                    evaluation_view.offset_for_next_chunk(&per_chunk_offset);
                }
            }
        }
    }

    fn type_name() -> std::borrow::Cow<'static, str>;

    #[inline]
    fn instance_name(&self) -> String {
        Self::type_name().to_string()
    }

    fn instance_width(&self) -> GatePrincipalInstanceWidth;

    fn gate_purpose() -> GatePurpose;

    #[inline]
    fn max_constraint_degree() -> usize {
        match Self::gate_purpose() {
            GatePurpose::MarkerNeedsSelector {..} | GatePurpose::MarkerWithoutSelector => 0,
            GatePurpose::Evaluatable { max_constraint_degree, .. } => max_constraint_degree
        }
    }
    #[inline]
    fn num_quotient_terms() -> usize {
        match Self::gate_purpose() {
            GatePurpose::MarkerNeedsSelector {..} | GatePurpose::MarkerWithoutSelector => 0,
            GatePurpose::Evaluatable { num_quotient_terms, .. } => num_quotient_terms
        }
    }

    fn placement_type(&self) -> GatePlacementType;

    #[inline]
    fn per_chunk_offset_for_repetition_over_general_purpose_columns(&self) -> PerChunkOffset {
        match self.placement_type() {
            GatePlacementType::UniqueOnRow => {
                PerChunkOffset::zero()
            },
            GatePlacementType::MultipleOnRow { per_chunk_offset } => {
                per_chunk_offset
            }
        }
    }

    fn num_repetitions_in_geometry(&self, geometry: &CSGeometry) -> usize;
    fn num_required_constants_in_geometry(&self, geometry: &CSGeometry) -> usize;

    #[inline]
    fn total_quotient_terms_in_geometry(&self, geometry: &CSGeometry) -> usize {
        let num_repetitions = self.num_repetitions_in_geometry(geometry);
        match self.placement_type() {
            GatePlacementType::UniqueOnRow => {
                debug_assert_eq!(num_repetitions, 1, "unexpected number of repetitions for gate placement type");
                Self::num_quotient_terms()
            },
            GatePlacementType::MultipleOnRow { .. } => num_repetitions * Self::num_quotient_terms()
        }
    }
}

#[derive(Derivative)]
#[derivative(Debug)]
pub struct GateBatchEvaluationComparisonFunction {
    pub type_id: std::any::TypeId,
    pub evaluator_dyn: Box<dyn std::any::Any + 'static + Send + Sync>,
    #[derivative(Debug = "ignore")]
    pub equality_fn: Box<dyn Fn(&dyn std::any::Any) -> bool + 'static + Send + Sync>,
}

impl GateBatchEvaluationComparisonFunction {
    pub fn equals_to(&self, other: &Self) -> bool {
        if self.type_id != other.type_id {
            return false;
        }

        // otherwise run dynamic way

        (self.equality_fn)(&*other.evaluator_dyn)
    }
}

use crate::cs::implementations::buffering_source::BufferedGateEvaluationReducingDestinationChunk;
use crate::cs::implementations::polynomial_storage::{ProverTraceView, SatisfiabilityCheckRowView};

// set of traits that will allow dynamic dispatch, but also to drive evaluation as efficient as possible
pub(crate) trait DynamicEvaluatorOverSpecializedColumns<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
>: 'static + Send + Sync
{
    fn evaluate_over_columns(
        &self,
        source: &mut ProverTraceView<F, P>,
        destination: &mut BufferedGateEvaluationReducingDestinationChunk<F, P>,
        ctx: &mut P::Context,
    );
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub(crate) struct ColumnwiseEvaluator<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    E: GateConstraintEvaluator<F>,
> {
    pub(crate) evaluator: E,
    #[derivative(Debug = "ignore")]
    pub(crate) global_constants: E::GlobalConstants<P>,
    pub(crate) num_repetitions: usize,
    pub(crate) per_chunk_offset: PerChunkOffset,
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        E: GateConstraintEvaluator<F>,
    > DynamicEvaluatorOverSpecializedColumns<F, P> for ColumnwiseEvaluator<F, P, E>
{
    fn evaluate_over_columns(
        &self,
        source: &mut ProverTraceView<F, P>,
        destination: &mut BufferedGateEvaluationReducingDestinationChunk<F, P>,
        ctx: &mut P::Context,
    ) {
        let num_iterations = source.num_iterations();
        debug_assert_eq!(num_iterations, destination.expected_num_iterations());

        for _ in 0..num_iterations {
            source.reset_gate_chunk_offset();
            let row_shared_constants = self.evaluator.load_row_shared_constants(&*source, ctx);
            for _ in 0..self.num_repetitions {
                self.evaluator.evaluate_once(
                    source,
                    destination,
                    &row_shared_constants,
                    &self.global_constants,
                    ctx,
                );
                source.offset_for_next_chunk(&self.per_chunk_offset);
                destination.proceed_to_next_gate();
            }

            source.advance();
            destination.advance(ctx);
        }
    }
}

use crate::cs::implementations::buffering_source::BufferingPolyStorage;

pub(crate) trait DynamicEvaluatorOverGeneralPurposeColumns<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
>: 'static + Send + Sync
{
    fn evaluate_over_general_purpose_columns(
        &self,
        source: &mut BufferingPolyStorage<F, P>,
        destination: &mut BufferedGateEvaluationReducingDestinationChunk<F, P>,
        constant_offset: usize,
        ctx: &mut P::Context,
    );
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub(crate) struct RowwiseEvaluator<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    E: GateConstraintEvaluator<F>,
> {
    pub(crate) evaluator: E,
    #[derivative(Debug = "ignore")]
    pub(crate) global_constants: E::GlobalConstants<P>,
    pub(crate) num_repetitions: usize,
    pub(crate) per_chunk_offset: PerChunkOffset,
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        E: GateConstraintEvaluator<F>,
    > DynamicEvaluatorOverGeneralPurposeColumns<F, P> for RowwiseEvaluator<F, P, E>
{
    fn evaluate_over_general_purpose_columns(
        &self,
        source: &mut BufferingPolyStorage<F, P>,
        destination: &mut BufferedGateEvaluationReducingDestinationChunk<F, P>,
        constant_offset: usize,
        ctx: &mut P::Context,
    ) {
        source.reset_gate_chunk_offset(); // cleanup from whatever was before
        source.set_constants_offset(constant_offset);

        let row_shared_constants = self.evaluator.load_row_shared_constants(&*source, ctx);
        for _ in 0..self.num_repetitions {
            self.evaluator.evaluate_once(
                source,
                destination,
                &row_shared_constants,
                &self.global_constants,
                ctx,
            );
            source.offset_for_next_chunk(&self.per_chunk_offset);
        }
    }
}

pub trait GenericDynamicEvaluatorOverGeneralPurposeColumns<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
    S: TraceSourceDerivable<F, P>,
    D: EvaluationDestinationDrivable<F, P>,
>: 'static + Send + Sync
{
    fn evaluate_over_general_purpose_columns(
        &self,
        source: &mut S,
        destination: &mut D,
        constant_offset: usize,
        ctx: &mut P::Context,
    );
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct GenericRowwiseEvaluator<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
    E: GateConstraintEvaluator<F>,
> {
    pub evaluator: E,
    #[derivative(Debug = "ignore")]
    pub global_constants: E::GlobalConstants<P>,
    pub num_repetitions: usize,
    pub per_chunk_offset: PerChunkOffset,
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSourceDerivable<F, P>,
        D: EvaluationDestinationDrivable<F, P>,
        E: GateConstraintEvaluator<F>,
    > GenericDynamicEvaluatorOverGeneralPurposeColumns<F, P, S, D>
    for GenericRowwiseEvaluator<F, P, E>
{
    fn evaluate_over_general_purpose_columns(
        &self,
        source: &mut S,
        destination: &mut D,
        constant_offset: usize,
        ctx: &mut P::Context,
    ) {
        source.reset_gate_chunk_offset();
        source.set_constants_offset(constant_offset);

        let row_shared_constants = self.evaluator.load_row_shared_constants(&*source, ctx);

        for _ in 0..self.num_repetitions {
            self.evaluator.evaluate_once(
                source,
                destination,
                &row_shared_constants,
                &self.global_constants,
                ctx,
            );
            source.offset_for_next_chunk(&self.per_chunk_offset);
        }

        source.advance();
        destination.advance(ctx);
    }
}

// set of traits that will allow dynamic dispatch, but also to drive evaluation as efficient as possible
pub trait GenericDynamicEvaluatorOverSpecializedColumns<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
    S: TraceSourceDerivable<F, P>,
    D: EvaluationDestinationDrivable<F, P>,
>: 'static + Send + Sync
{
    fn evaluate_over_columns(&self, source: &mut S, destination: &mut D, ctx: &mut P::Context);
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct GenericColumnwiseEvaluator<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
    E: GateConstraintEvaluator<F>,
> {
    pub evaluator: E,
    #[derivative(Debug = "ignore")]
    pub global_constants: E::GlobalConstants<P>,
    pub num_repetitions: usize,
    pub per_chunk_offset: PerChunkOffset,
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSourceDerivable<F, P>,
        D: EvaluationDestinationDrivable<F, P>,
        E: GateConstraintEvaluator<F>,
    > GenericDynamicEvaluatorOverSpecializedColumns<F, P, S, D>
    for GenericColumnwiseEvaluator<F, P, E>
{
    fn evaluate_over_columns(&self, source: &mut S, destination: &mut D, ctx: &mut P::Context) {
        source.reset_gate_chunk_offset();
        let row_shared_constants = self.evaluator.load_row_shared_constants(&*source, ctx);

        for _ in 0..self.num_repetitions {
            self.evaluator.evaluate_once(
                source,
                destination,
                &row_shared_constants,
                &self.global_constants,
                ctx,
            );
            source.offset_for_next_chunk(&self.per_chunk_offset);
        }

        source.advance();
        destination.advance(ctx);
    }
}

use crate::gpu_synthesizer::get_evaluator_name;
use std::alloc::Global;

// Now we can define a structure that will do type erasure
// and can be stored by CS implementation
#[derive(Derivative)]
#[derivative(Debug)]
pub struct TypeErasedGateEvaluationFunction<
    F: BaseField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
> {
    pub debug_name: String,
    pub unique_name: String,
    pub evaluator_type_id: TypeId,
    pub gate_purpose: GatePurpose,
    pub max_constraint_degree: usize,
    pub num_quotient_terms: usize,
    pub num_required_constants: usize,
    pub total_quotient_terms_over_all_repetitions: usize,
    pub num_repetitions_on_row: usize,
    pub placement_type: GatePlacementType,
    #[derivative(Debug = "ignore")]
    pub(crate) columnwise_evaluation_function:
        Option<Box<dyn DynamicEvaluatorOverSpecializedColumns<F, P> + 'static + Send + Sync>>,
    #[derivative(Debug = "ignore")]
    pub(crate) rowwise_evaluation_function:
        Option<Box<dyn DynamicEvaluatorOverGeneralPurposeColumns<F, P> + 'static + Send + Sync>>,
    #[derivative(Debug = "ignore")]
    pub(crate) columnwise_satisfiability_function: Option<
        Box<
            dyn GenericDynamicEvaluatorOverSpecializedColumns<
                    F,
                    F,
                    SatisfiabilityCheckRowView<F, Global, Global>,
                    Vec<F>,
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
                    F,
                    SatisfiabilityCheckRowView<F, Global, Global>,
                    Vec<F>,
                >
                + 'static
                + Send
                + Sync,
        >,
    >,
}

impl<F: BaseField, P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>>
    TypeErasedGateEvaluationFunction<F, P>
{
    pub fn from_evaluator<E: GateConstraintEvaluator<F>>(
        evaluator: E,
        geometry: &CSGeometry,
        placement_strategy: GatePlacementStrategy,
        ctx: &mut P::Context,
    ) -> (Self, GateBatchEvaluationComparisonFunction) {
        let debug_name = evaluator.instance_name();
        let unique_name = get_evaluator_name(&evaluator);
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

        let (specialized_evaluator, general_purpose_evaluator) = match placement_strategy {
            GatePlacementStrategy::UseSpecializedColumns { .. } => {
                let specialized_evaluator = ColumnwiseEvaluator {
                    evaluator: evaluator.clone(),
                    global_constants: evaluator.create_global_constants(ctx),
                    num_repetitions: num_repetitions_on_row,
                    per_chunk_offset: final_per_chunk_offset,
                };

                // dbg!(&specialized_evaluator);

                (
                    Some(Box::new(specialized_evaluator)
                        as Box<
                            dyn DynamicEvaluatorOverSpecializedColumns<F, P>
                                + 'static
                                + Send
                                + Sync,
                        >),
                    None,
                )
            }
            GatePlacementStrategy::UseGeneralPurposeColumns => {
                let general_purpose_evaluator = RowwiseEvaluator {
                    evaluator: evaluator.clone(),
                    global_constants: evaluator.create_global_constants(ctx),
                    num_repetitions: num_repetitions_on_row,
                    per_chunk_offset: final_per_chunk_offset,
                };

                // dbg!(&general_purpose_evaluator);

                (
                    None,
                    Some(Box::new(general_purpose_evaluator)
                        as Box<
                            dyn DynamicEvaluatorOverGeneralPurposeColumns<F, P>
                                + 'static
                                + Send
                                + Sync,
                        >),
                )
            }
        };

        let (specialized_satisfiability_evaluator, general_purpose_satisfiability_evaluator) =
            match placement_strategy {
                GatePlacementStrategy::UseSpecializedColumns { .. } => {
                    let specialized_evaluator = GenericColumnwiseEvaluator {
                        evaluator: evaluator.clone(),
                        global_constants: evaluator.create_global_constants(&mut ()),
                        num_repetitions: num_repetitions_on_row,
                        per_chunk_offset: final_per_chunk_offset,
                    };

                    // dbg!(&specialized_evaluator);

                    (
                        Some(Box::new(specialized_evaluator)
                            as Box<
                                dyn GenericDynamicEvaluatorOverSpecializedColumns<
                                        F,
                                        F,
                                        SatisfiabilityCheckRowView<F, Global, Global>,
                                        Vec<F>,
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
                        global_constants: evaluator.create_global_constants(&mut ()),
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
                                        F,
                                        SatisfiabilityCheckRowView<F, Global, Global>,
                                        Vec<F>,
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
            unique_name,
            evaluator_type_id,
            gate_purpose,
            max_constraint_degree,
            num_quotient_terms,
            num_required_constants,
            total_quotient_terms_over_all_repetitions,
            num_repetitions_on_row,
            placement_type,
            columnwise_evaluation_function: specialized_evaluator,
            rowwise_evaluation_function: general_purpose_evaluator,
            columnwise_satisfiability_function: specialized_satisfiability_evaluator,
            rowwise_satisfiability_function: general_purpose_satisfiability_evaluator,
        };

        (new, comparator)
    }
}
