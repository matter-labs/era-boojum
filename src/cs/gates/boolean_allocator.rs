use crate::{
    config::CSSetupConfig,
    cs::{
        cs_builder::{CsBuilder, CsBuilderImpl},
        toolboxes::gate_config::GateConfigurationHolder,
    },
    field::PrimeField,
};

use super::*;

// Allocates boolean variables

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BooleanConstraintGate {
    pub var_to_enforce: Variable,
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BooleanConstraitEvaluator;

impl<F: PrimeField> GateConstraintEvaluator<F> for BooleanConstraitEvaluator {
    type UniqueParameterizationParams = ();

    #[inline(always)]
    fn new_from_parameters(_params: Self::UniqueParameterizationParams) -> Self {
        Self
    }

    #[inline(always)]
    fn unique_params(&self) -> Self::UniqueParameterizationParams {}

    #[inline]
    fn type_name() -> std::borrow::Cow<'static, str> {
        Cow::Borrowed(UNIQUE_IDENTIFIER)
    }

    #[inline]
    fn instance_width(&self) -> GatePrincipalInstanceWidth {
        GatePrincipalInstanceWidth {
            num_variables: 1,
            num_witnesses: 0,
            num_constants: 0,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: 2,
            num_quotient_terms: 1,
        }
    }

    #[inline]
    fn placement_type(&self) -> GatePlacementType {
        GatePlacementType::MultipleOnRow {
            per_chunk_offset: PerChunkOffset {
                variables_offset: PRINCIPAL_WIDTH,
                witnesses_offset: 0,
                constants_offset: 0,
            },
        }
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, geometry: &CSGeometry) -> usize {
        geometry.num_columns_under_copy_permutation / PRINCIPAL_WIDTH
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
        let a = trace_source.get_variable_value(0);
        let mut tmp = one;
        tmp.sub_assign(&a, ctx);

        let mut contribution = a;
        contribution.mul_assign(&tmp, ctx);

        destination.push_evaluation_result(contribution, ctx);
    }
}

const UNIQUE_IDENTIFIER: &str = "Boolean constraint gate";
const PRINCIPAL_WIDTH: usize = 1;

impl<F: SmallField> Gate<F> for BooleanConstraintGate {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 2
    }

    type Evaluator = BooleanConstraitEvaluator;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        BooleanConstraitEvaluator
    }
}

impl BooleanConstraintGate {
    pub fn configure_builder<
        F: SmallField,
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        TImpl: CsBuilderImpl<F, TImpl>,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
        // ) -> CsBuilder<TImpl, F, GC::DescendantHolder<Self, NextGateCounterWithoutParams>, TB> {
    ) -> CsBuilder<TImpl, F, (GateTypeEntry<F, Self, NextGateCounterWithoutParams>, GC), TB> {
        builder.allow_gate(placement_strategy, (), None)
    }

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

                // now we can use methods of CS to inform it of low level operations
                let offset = num_instances_already_placed * PRINCIPAL_WIDTH;
                if offered_row_idx == row {
                    cs.place_gate(&self, row);
                }
                cs.place_variable(self.var_to_enforce, row, offset);
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
                cs.place_variable_specialized::<Self>(
                    self.var_to_enforce,
                    num_instances_already_placed,
                    row,
                    0,
                );
            }
        }
    }

    pub fn alloc_boolean_from_witness<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        witness_value: bool,
    ) -> Variable {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let new_var = cs.alloc_variable_without_value();
        let gate = Self {
            var_to_enforce: new_var,
        };

        let value = if witness_value { F::ONE } else { F::ZERO };

        cs.set_values(&Place::from_variables([new_var]), [value]);
        gate.add_to_cs(cs);

        new_var
    }

    pub fn enforce_boolean<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        variable: Variable,
    ) {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let gate = Self {
            var_to_enforce: variable,
        };

        gate.add_to_cs(cs);
    }
}
