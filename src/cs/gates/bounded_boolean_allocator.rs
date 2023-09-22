use crate::{
    config::CSSetupConfig,
    cs::{
        cs_builder::{CsBuilder, CsBuilderImpl},
        toolboxes::gate_config::GateConfigurationHolder,
    },
    field::PrimeField,
};

use super::*;

// Allocates boolean variables, but doesn't span all the columns

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BoundedBooleanConstraintGate {
    pub var_to_enforce: Variable,
    max_on_row: usize,
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BoundedBooleanConstraitEvaluator {
    max_on_row: usize,
}

impl<F: PrimeField> GateConstraintEvaluator<F> for BoundedBooleanConstraitEvaluator {
    type UniqueParameterizationParams = usize;

    #[inline(always)]
    fn new_from_parameters(params: Self::UniqueParameterizationParams) -> Self {
        Self { max_on_row: params }
    }

    #[inline(always)]
    fn unique_params(&self) -> Self::UniqueParameterizationParams {
        self.max_on_row
    }

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
        let max_by_columns = geometry.num_columns_under_copy_permutation / PRINCIPAL_WIDTH;

        std::cmp::min(max_by_columns, self.max_on_row)
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

// Just keep a position that we can use next

impl<F: SmallField> Gate<F> for BoundedBooleanConstraintGate {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 2
    }

    type Evaluator = BoundedBooleanConstraitEvaluator;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        BoundedBooleanConstraitEvaluator {
            max_on_row: self.max_on_row,
        }
    }
}

impl BoundedBooleanConstraintGate {
    pub fn configure_builder<
        F: SmallField,
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        TImpl: CsBuilderImpl<F, TImpl>,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
        params: usize,
        // ) -> CsBuilder<TImpl, F, GC::DescendantHolder<Self, NextGateCounterWithoutParams>, TB> {
    ) -> CsBuilder<TImpl, F, (GateTypeEntry<F, Self, NextGateCounterWithoutParams>, GC), TB> {
        // check that we have enough columns
        assert!(params > 0);
        assert!(params <= builder.get_params().num_columns_under_copy_permutation);
        assert!(placement_strategy == GatePlacementStrategy::UseGeneralPurposeColumns);

        builder.allow_gate(placement_strategy, params, None)
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
            GatePlacementStrategy::UseSpecializedColumns { .. } => {
                unimplemented!("bounded boolean allocator is not made for specialized columns");
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
            max_on_row: 0,
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

        let max_on_row = cs.get_gate_params::<Self>();

        let gate = Self {
            var_to_enforce: variable,
            max_on_row,
        };

        gate.add_to_cs(cs);
    }
}
