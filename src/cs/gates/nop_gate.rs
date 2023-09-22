use crate::cs::cs_builder::{CsBuilder, CsBuilderImpl};

use super::*;

// Allocates bootlean variables

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NopGate;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NopGateConstraintEvaluator;

impl<F: PrimeField> GateConstraintEvaluator<F> for NopGateConstraintEvaluator {
    type UniqueParameterizationParams = ();

    #[inline(always)]
    fn new_from_parameters(_params: Self::UniqueParameterizationParams) -> Self {
        Self
    }

    #[inline(always)]
    fn unique_params(&self) -> Self::UniqueParameterizationParams {}

    #[inline]
    fn type_name() -> std::borrow::Cow<'static, str> {
        Cow::Borrowed(std::any::type_name::<Self>())
    }

    #[inline]
    fn instance_width(&self) -> GatePrincipalInstanceWidth {
        GatePrincipalInstanceWidth {
            num_variables: 0,
            num_witnesses: 0,
            num_constants: 0,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::MarkerNeedsSelector
    }

    #[inline]
    fn placement_type(&self) -> GatePlacementType {
        GatePlacementType::UniqueOnRow
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, _geometry: &CSGeometry) -> usize {
        1
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
        _trace_source: &S,
        _destination: &mut D,
        _shared_constants: &Self::RowSharedConstants<P>,
        _global_constants: &Self::GlobalConstants<P>,
        _ctx: &mut P::Context,
    ) {
        unreachable!("NOP gate should be filtered from evaluation somewhere before");
    }
}

// const UNIQUE_IDENTIFIER: &'static str = "NOP gate";

impl<F: SmallField> Gate<F> for NopGate {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, _cs: &CS) -> bool {
        true
    }

    type Evaluator = NopGateConstraintEvaluator;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        NopGateConstraintEvaluator
    }
}

impl NopGate {
    pub const fn new() -> Self {
        Self
    }

    pub fn configure_builder<
        F: SmallField,
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        TImpl: CsBuilderImpl<F, TImpl>,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
        // ) -> CsBuilder<TImpl, F, GC::DescendantHolder<Self, ()>, TB> {
    ) -> CsBuilder<TImpl, F, (GateTypeEntry<F, Self, ()>, GC), TB> {
        builder.allow_gate(placement_strategy, (), ())
    }

    pub fn add_to_cs<F: SmallField, CS: ConstraintSystem<F>>(self, cs: &mut CS) {
        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            return;
        }
        let offered_row_idx = cs.next_available_row();
        cs.place_gate(&self, offered_row_idx);
    }
}
