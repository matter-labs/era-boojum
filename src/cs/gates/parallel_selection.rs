use crate::{
    config::CSSetupConfig,
    cs::cs_builder::{CsBuilder, CsBuilderImpl},
    field::PrimeField,
};

use super::*;

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ParallelSelectionGate<const N: usize> {
    pub a: [Variable; N],
    pub b: [Variable; N],
    pub selector: Variable,
    pub result: [Variable; N],
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ParallelSelectionGateConstraintEvaluator<const N: usize>;

impl<const N: usize> ParallelSelectionGateConstraintEvaluator<N> {
    pub const fn principal_width() -> usize {
        3 * N + 1
    }
}

impl<F: PrimeField, const N: usize> GateConstraintEvaluator<F>
    for ParallelSelectionGateConstraintEvaluator<N>
{
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
            num_variables: Self::principal_width(),
            num_witnesses: 0,
            num_constants: 0,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: 2,
            num_quotient_terms: N,
        }
    }

    #[inline]
    fn placement_type(&self) -> GatePlacementType {
        GatePlacementType::MultipleOnRow {
            per_chunk_offset: PerChunkOffset {
                variables_offset: Self::principal_width(),
                witnesses_offset: 0,
                constants_offset: 0,
            },
        }
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, geometry: &CSGeometry) -> usize {
        geometry.num_columns_under_copy_permutation / Self::principal_width()
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
        let selector = trace_source.get_variable_value(0);

        for i in 0..N {
            let a = trace_source.get_variable_value(3 * i + 1);
            let b = trace_source.get_variable_value(3 * i + 2);
            let result = trace_source.get_variable_value(3 * i + 3);

            let mut contribution = a;
            contribution.mul_assign(&selector, ctx);

            let mut tmp = P::one(ctx);
            tmp.sub_assign(&selector, ctx);
            P::mul_and_accumulate_into(&mut contribution, &tmp, &b, ctx);

            contribution.sub_assign(&result, ctx);

            destination.push_evaluation_result(contribution, ctx);
        }
    }
}

impl<F: SmallField, const N: usize> Gate<F> for ParallelSelectionGate<N> {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 2
            && geometry.num_columns_under_copy_permutation
                >= <Self as Gate<F>>::Evaluator::principal_width()
    }

    type Evaluator = ParallelSelectionGateConstraintEvaluator<N>;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        ParallelSelectionGateConstraintEvaluator
    }
}

impl<const N: usize> ParallelSelectionGate<N> {
    pub const fn empty() -> Self {
        Self {
            a: [Variable::placeholder(); N],
            b: [Variable::placeholder(); N],
            selector: Variable::placeholder(),
            result: [Variable::placeholder(); N],
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
        // ) -> CsBuilder<TImpl, F, GC::DescendantHolder<Self, NextGateCounterWithoutParams>, TB> {
    ) -> CsBuilder<TImpl, F, (GateTypeEntry<F, Self, NextGateCounterWithoutParams>, GC), TB> {
        builder.allow_gate(placement_strategy, (), None)
    }

    pub fn select<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: &[Variable; N],
        b: &[Variable; N],
        selector: Variable,
    ) -> [Variable; N] {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variables = cs.alloc_multiple_variables_without_values::<N>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: &[F], outputs: &mut DstBuffer<'_, '_, F>| {
                let selector = inputs[0];
                use crate::gadgets::traits::castable::WitnessCastable;
                let selector = <bool as WitnessCastable<F, F>>::cast_from_source(selector);

                for (a, b) in inputs[1..(N + 1)].iter().zip(inputs[(N + 1)..].iter()) {
                    let result = if selector { *a } else { *b };

                    outputs.push(result);
                }
            };

            let mut dependencies = Vec::with_capacity(2 * N + 1);
            dependencies.push(selector.into());
            dependencies.extend(Place::from_variables(*a));
            dependencies.extend(Place::from_variables(*b));

            cs.set_values_with_dependencies_vararg(
                &dependencies,
                &Place::from_variables(output_variables),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                a: *a,
                b: *b,
                selector,
                result: output_variables,
            };
            gate.add_to_cs(cs);
        }

        output_variables
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
                let mut offset =
                    num_instances_already_placed * <Self as Gate<F>>::Evaluator::principal_width();
                if offered_row_idx == row {
                    cs.place_gate(&self, row);
                }
                cs.place_variable(self.selector, row, offset);
                offset += 1;
                for ((a, b), result) in self
                    .a
                    .into_iter()
                    .zip(self.b.into_iter())
                    .zip(self.result.into_iter())
                {
                    cs.place_multiple_variables_into_row(&[a, b, result], row, offset);
                    offset += 3;
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
                let mut offset = 0;
                cs.place_variable_specialized::<Self>(
                    self.selector,
                    num_instances_already_placed,
                    row,
                    offset,
                );
                offset += 1;
                for ((a, b), result) in self
                    .a
                    .into_iter()
                    .zip(self.b.into_iter())
                    .zip(self.result.into_iter())
                {
                    cs.place_multiple_variables_into_row_specialized::<Self, 3>(
                        &[a, b, result],
                        num_instances_already_placed,
                        row,
                        offset,
                    );
                    offset += 3;
                }
            }
        }
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

        let evaluator = <ParallelSelectionGateConstraintEvaluator<4> as GateConstraintEvaluator<
            F,
        >>::new_from_parameters(());

        test_evaluator::<F, _>(evaluator);
    }
}
