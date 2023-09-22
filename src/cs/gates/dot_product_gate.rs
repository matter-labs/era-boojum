use crate::cs::cs_builder::{CsBuilder, CsBuilderImpl};

use super::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DotProductConstraintEvaluator<const N: usize>;

impl<const N: usize> DotProductConstraintEvaluator<N> {
    const fn principal_width() -> usize {
        2 * N + 1
    }
}

impl<F: PrimeField, const N: usize> GateConstraintEvaluator<F>
    for DotProductConstraintEvaluator<N>
{
    type UniqueParameterizationParams = ();

    #[inline(always)]
    fn new_from_parameters(_params: Self::UniqueParameterizationParams) -> Self {
        debug_assert!(N > 1);

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
            num_quotient_terms: 1,
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
        debug_assert!(N > 1);
        debug_assert!(geometry.num_columns_under_copy_permutation >= Self::principal_width());

        geometry.num_columns_under_copy_permutation / Self::principal_width()
    }

    #[inline]
    fn num_required_constants_in_geometry(&self, geometry: &CSGeometry) -> usize {
        debug_assert!(N > 1);
        debug_assert!(geometry.num_constant_columns >= 1);

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
        let mut contribution = P::zero(ctx);

        for idx in 0..N {
            let a = trace_source.get_variable_value(2 * idx);
            let b = trace_source.get_variable_value(2 * idx + 1);

            P::mul_and_accumulate_into(&mut contribution, &a, &b, ctx);

            // let mut tmp = a;
            // tmp.mul_assign(&b, ctx);
            // contribution.add_assign(&tmp, ctx);
        }

        let result = trace_source.get_variable_value(2 * N);
        contribution.sub_assign(&result, ctx);

        destination.push_evaluation_result(contribution, ctx);
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DotProductGate<const N: usize>
where
    [(); N * 2]:,
{
    pub terms: [Variable; N * 2],
    pub result: Variable,
}

impl<F: SmallField, const N: usize> Gate<F> for DotProductGate<N>
where
    [(); N * 2]:,
{
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 2
            && geometry.num_columns_under_copy_permutation >= Self::Evaluator::principal_width()
            && geometry.num_constant_columns >= 1
    }

    type Evaluator = DotProductConstraintEvaluator<N>;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        DotProductConstraintEvaluator
    }
}

impl<const N: usize> DotProductGate<N>
where
    [(); N * 2]:,
{
    pub const fn empty() -> Self {
        Self {
            terms: [Variable::placeholder(); N * 2],
            result: Variable::placeholder(),
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

    pub fn compute_dot_product<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        terms: [(Variable, Variable); N],
    ) -> Variable {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let mut terms_flattened: [Variable; N * 2] = [Variable::placeholder(); N * 2];
        for ((a, b), dst) in terms
            .into_iter()
            .zip(terms_flattened.array_chunks_mut::<2>())
        {
            dst[0] = a;
            dst[1] = b;
        }
        let output_variable = cs.alloc_variable_without_value();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; N * 2]| {
                let mut result = F::ZERO;
                for [a, b] in inputs.array_chunks::<2>() {
                    let mut tmp = *a;
                    tmp.mul_assign(b);
                    result.add_assign(&tmp);
                }

                [result]
            };

            let dependencies = Place::from_variables(terms_flattened);

            cs.set_values_with_dependencies(&dependencies, &[output_variable.into()], value_fn);
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                terms: terms_flattened,
                result: output_variable,
            };
            gate.add_to_cs(cs);
        }

        output_variable
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

                cs.place_multiple_variables_into_row(&self.terms, row, offset);
                offset += N * 2;
                cs.place_variable(self.result, row, offset);
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
                let mut offset = 0;
                cs.place_gate_specialized(&self, num_instances_already_placed, row);
                cs.place_multiple_variables_into_row_specialized::<Self, { N * 2 }>(
                    &self.terms,
                    num_instances_already_placed,
                    row,
                    offset,
                );
                offset += N * 2;
                cs.place_variable_specialized::<Self>(
                    self.result,
                    num_instances_already_placed,
                    row,
                    offset,
                );
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

        let evaluator =
            <DotProductConstraintEvaluator<4> as GateConstraintEvaluator<F>>::new_from_parameters(
                (),
            );

        test_evaluator::<F, _>(evaluator);
    }
}
