use crate::cs::cs_builder::*;

use super::*;

// Allocate constants by a batch of constraints like (a - constant) == 0

// In this file the allocator uses all constant columns for its work

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConstantsAllocatorGate<F: PrimeField> {
    pub variable_with_constant_value: Variable,
    pub constant_to_add: F,
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ConstantAllocatorConstraintEvaluator;

impl<F: PrimeField> GateConstraintEvaluator<F> for ConstantAllocatorConstraintEvaluator {
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
            num_variables: 1,
            num_witnesses: 0,
            num_constants: 1,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: 1,
            num_quotient_terms: 1,
        }
    }

    #[inline]
    fn placement_type(&self) -> GatePlacementType {
        GatePlacementType::MultipleOnRow {
            per_chunk_offset: PerChunkOffset {
                variables_offset: PRINCIPAL_WIDTH,
                witnesses_offset: 0,
                constants_offset: PRINCIPAL_WIDTH,
            },
        }
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, geometry: &CSGeometry) -> usize {
        debug_assert!(geometry.num_columns_under_copy_permutation >= 1);
        debug_assert!(geometry.num_constant_columns >= 1);

        std::cmp::min(
            geometry.num_constant_columns,
            geometry.num_columns_under_copy_permutation,
        )
    }
    #[inline]
    fn num_required_constants_in_geometry(&self, geometry: &CSGeometry) -> usize {
        debug_assert!(geometry.num_columns_under_copy_permutation >= 1);
        debug_assert!(geometry.num_constant_columns >= 1);

        geometry.num_constant_columns
    }

    type GlobalConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = ();

    #[inline(always)]
    fn create_global_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>>(
        &self,
        _ctx: &mut P::Context,
    ) -> Self::GlobalConstants<P> {
    }

    // there are no constants that would be shared between instances
    // on the same row, so `evaluate_once` loads manually
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
        let a = trace_source.get_variable_value(0);
        let constant = trace_source.get_constant_value(0);

        let mut contribution = a;
        contribution.sub_assign(&constant, ctx);

        destination.push_evaluation_result(contribution, ctx);
    }
}

const PRINCIPAL_WIDTH: usize = 1;

impl<F: SmallField> Gate<F> for ConstantsAllocatorGate<F> {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 1
            && geometry.num_columns_under_copy_permutation >= 1
            && geometry.num_constant_columns >= 1
    }

    type Evaluator = ConstantAllocatorConstraintEvaluator;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        ConstantAllocatorConstraintEvaluator
    }
}

impl<F: SmallField> ConstantsAllocatorGate<F> {
    pub const fn empty() -> Self {
        Self {
            variable_with_constant_value: Variable::placeholder(),
            constant_to_add: F::ZERO,
        }
    }

    pub const fn new_to_enforce(var: Variable, constant: F) -> Self {
        Self {
            variable_with_constant_value: var,
            constant_to_add: constant,
        }
    }

    pub fn configure_builder<
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        TImpl: CsBuilderImpl<F, TImpl>,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
        // ) -> CsBuilder<
        //     TImpl,
        //     F,
        //     GC::DescendantHolder<Self, NextGateCounterWithoutParams>,
        //     TB::DescendantHolder<ConstantToVariableMappingToolMarker, ConstantToVariableMappingTool<F>>,
        // > {
    ) -> CsBuilder<
        TImpl,
        F,
        (GateTypeEntry<F, Self, NextGateCounterWithoutParams>, GC),
        (
            Tool<ConstantToVariableMappingToolMarker, ConstantToVariableMappingTool<F>>,
            TB,
        ),
    > {
        // we want to have a CS-global toolbox under some marker
        builder
            .allow_gate(placement_strategy, (), None)
            .add_tool::<ConstantToVariableMappingToolMarker, _>(
                ConstantToVariableMappingTool::<F>::with_capacity(16),
            )
    }

    pub fn add_to_cs<CS: ConstraintSystem<F>>(self, cs: &mut CS) {
        debug_assert!(cs.gate_is_allowed::<Self>());

        // the rest is not necessary if we do not keep setup
        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            return;
        }

        assert_not_placeholder_variable(self.variable_with_constant_value);

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
                cs.place_variable(self.variable_with_constant_value, row, offset);
                cs.place_constants(&[self.constant_to_add], row, offset);
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
                    self.variable_with_constant_value,
                    num_instances_already_placed,
                    row,
                    0,
                );
                cs.place_constants_specialized::<Self, 1>(
                    &[self.constant_to_add],
                    num_instances_already_placed,
                    row,
                    0,
                );
            }
        }
    }

    pub fn allocate_constant<CS: ConstraintSystem<F>>(cs: &mut CS, constant_to_add: F) -> Variable {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let tooling: &mut ConstantToVariableMappingTool<F> = cs
            .get_static_toolbox_mut()
            .get_tool_mut::<ConstantToVariableMappingToolMarker, ConstantToVariableMappingTool<F>>()
            .expect("tool must be added");
        if let Some(variable) = tooling.get(&constant_to_add).copied() {
            return variable;
        }

        drop(tooling);

        let output_variable = cs.alloc_variable_without_value();

        let tooling: &mut ConstantToVariableMappingTool<F> = cs
            .get_static_toolbox_mut()
            .get_tool_mut::<ConstantToVariableMappingToolMarker, ConstantToVariableMappingTool<F>>()
            .expect("tool must be added");
        let existing = tooling.insert(constant_to_add, output_variable);
        assert!(existing.is_none());
        drop(tooling);

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |_inputs: [F; 0]| [constant_to_add];

            let dependencies = [];

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables([output_variable]),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == true {
            let gate = Self::new_to_enforce(output_variable, constant_to_add);
            gate.add_to_cs(cs);
        }

        output_variable
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
            <ConstantAllocatorConstraintEvaluator as GateConstraintEvaluator<F>>::new_from_parameters(
                (),
            );

        test_evaluator::<F, _>(evaluator);
    }
}
