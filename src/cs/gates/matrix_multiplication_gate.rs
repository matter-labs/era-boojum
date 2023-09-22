use super::*;
use crate::algebraic_props::matrix_parameters::MatrixParameters;

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MatrixMultiplicationEvaluator<F: SmallField, const N: usize, PAR: MatrixParameters<F, N>>
{
    _marker: std::marker::PhantomData<(F, PAR)>,
}

impl<F: SmallField, const N: usize, PAR: MatrixParameters<F, N>> GateConstraintEvaluator<F>
    for MatrixMultiplicationEvaluator<F, N, PAR>
{
    type UniqueParameterizationParams = ();

    #[inline(always)]
    fn new_from_parameters(_params: Self::UniqueParameterizationParams) -> Self {
        Self {
            _marker: std::marker::PhantomData,
        }
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
            num_variables: N * 2,
            num_witnesses: 0,
            num_constants: 0,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: 1,
            num_quotient_terms: N,
        }
    }

    #[inline]
    fn placement_type(&self) -> GatePlacementType {
        GatePlacementType::MultipleOnRow {
            per_chunk_offset: PerChunkOffset {
                variables_offset: N * 2,
                witnesses_offset: 0,
                constants_offset: 0,
            },
        }
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, geometry: &CSGeometry) -> usize {
        debug_assert!(geometry.num_columns_under_copy_permutation >= N * 2);

        geometry.num_columns_under_copy_permutation / (N * 2)
    }

    #[inline]
    fn num_required_constants_in_geometry(&self, _geometry: &CSGeometry) -> usize {
        0
    }

    // we load MDS and round constants
    type GlobalConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = ([[P; N]; N],);

    #[inline(always)]
    fn create_global_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>>(
        &self,
        ctx: &mut P::Context,
    ) -> Self::GlobalConstants<P> {
        let mds_matrix = PAR::COEFFS.map(|row| row.map(|el| P::constant(el, ctx)));

        (mds_matrix,)
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
        global_constants: &Self::GlobalConstants<P>,
        ctx: &mut P::Context,
    ) {
        let (matrix,) = global_constants;

        let input: [P; N] = std::array::from_fn(|idx| trace_source.get_variable_value(idx));
        let result: [P; N] = std::array::from_fn(|idx| trace_source.get_variable_value(N + idx));

        for (idx, a) in result.into_iter().enumerate() {
            let mut term = P::zero(ctx);
            for (b, coeff) in input.iter().zip(matrix[idx].iter()) {
                P::mul_and_accumulate_into(&mut term, b, coeff, ctx);
            }

            let mut contribution = term;
            contribution.sub_assign(&a, ctx);
            destination.push_evaluation_result(contribution, ctx);
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MatrixMultiplicationGate<F: SmallField, const N: usize, PAR: MatrixParameters<F, N>> {
    pub input: [Variable; N],
    pub output: [Variable; N],
    _marker: std::marker::PhantomData<(F, PAR)>,
}

impl<F: SmallField, const N: usize, PAR: MatrixParameters<F, N>> Gate<F>
    for MatrixMultiplicationGate<F, N, PAR>
{
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 1
            && geometry.num_columns_under_copy_permutation >= N * 2
    }

    type Evaluator = MatrixMultiplicationEvaluator<F, N, PAR>;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        MatrixMultiplicationEvaluator {
            _marker: std::marker::PhantomData,
        }
    }
}

use crate::cs::cs_builder::*;

impl<F: SmallField, const N: usize, PAR: MatrixParameters<F, N>>
    MatrixMultiplicationGate<F, N, PAR>
{
    pub fn configure_builder<
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

    pub fn add_to_cs<CS: ConstraintSystem<F>>(self, cs: &mut CS) {
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
                let mut variables_offset = N * 2 * num_instances_already_placed;
                if offered_row_idx == row {
                    cs.place_gate(&self, row);
                }
                // place logical inputs
                cs.place_multiple_variables_into_row(&self.input, row, variables_offset);
                variables_offset += N;

                cs.place_multiple_variables_into_row(&self.output, row, variables_offset);
            }
            GatePlacementStrategy::UseSpecializedColumns {
                num_repetitions: _,
                share_constants: _,
            } => {
                unimplemented!()
            }
        }
    }

    pub fn compute_multiplication<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        input: [Variable; N],
    ) -> [Variable; N] {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variables = cs.alloc_multiple_variables_without_values::<N>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; N]| {
                // we follow the same logic as in the constraints below

                let mut output: [F; N] = [F::ZERO; N];

                for (idx, dst) in output.iter_mut().enumerate() {
                    for (a, b) in inputs.iter().zip(PAR::COEFFS[idx].iter()) {
                        F::mul_and_accumulate_into(dst, a, b);
                    }
                }

                output
            };

            let all_dependencies = Place::from_variables(input);
            let all_outputs = Place::from_variables(output_variables);

            cs.set_values_with_dependencies(&all_dependencies, &all_outputs, value_fn);
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                input,
                output: output_variables,
                _marker: std::marker::PhantomData,
            };

            gate.add_to_cs(cs);
        }

        output_variables
    }
}

use crate::gadgets::traits::configuration::ConfigurationFunction;

impl<F: SmallField, const N: usize, PAR: MatrixParameters<F, N>> ConfigurationFunction<F>
    for MatrixMultiplicationGate<F, N, PAR>
{
    fn configure<TImpl: CsBuilderImpl<F, TImpl>>(
        builder: CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder>,
        placement_strategy: GatePlacementStrategy,
    ) -> CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
        Self::configure_builder(builder, placement_strategy)
    }
}
