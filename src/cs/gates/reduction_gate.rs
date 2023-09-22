use crate::cs::cs_builder::{CsBuilder, CsBuilderImpl};

use super::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ReductionGateConstraintEvaluator<const N: usize>;

impl<const N: usize> ReductionGateConstraintEvaluator<N> {
    const fn principal_width() -> usize {
        N + 1
    }
}

impl<F: PrimeField, const N: usize> GateConstraintEvaluator<F>
    for ReductionGateConstraintEvaluator<N>
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
            num_constants: N,
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
        debug_assert!(geometry.num_constant_columns >= N);

        N
    }

    type GlobalConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = ();

    #[inline(always)]
    fn create_global_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>>(
        &self,
        _ctx: &mut P::Context,
    ) -> Self::GlobalConstants<P> {
    }

    type RowSharedConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = [P; N];

    #[inline(always)]
    fn load_row_shared_constants<
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSource<F, P>,
    >(
        &self,
        trace_source: &S,
        _ctx: &mut P::Context,
    ) -> Self::RowSharedConstants<P> {
        std::array::from_fn(|idx| trace_source.get_constant_value(idx))
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
        shared_constants: &Self::RowSharedConstants<P>,
        _global_constants: &Self::GlobalConstants<P>,
        ctx: &mut P::Context,
    ) {
        let mut contribution = P::zero(ctx);

        for i in 0..N {
            let var = trace_source.get_variable_value(i);
            P::mul_and_accumulate_into(&mut contribution, &var, &shared_constants[i], ctx);
        }

        let reduction_result = trace_source.get_variable_value(N);
        contribution.sub_assign(&reduction_result, ctx);

        destination.push_evaluation_result(contribution, ctx);
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ReductionGateParams<F: SmallField, const N: usize> {
    pub reduction_constants: [F; N],
}

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ReductionGate<F: SmallField, const N: usize> {
    pub params: ReductionGateParams<F, N>,
    pub terms: [Variable; N],
    pub reduction_result: Variable,
}

// HashMap coefficients into row index to know vacant places
type ReductionGateTooling<F, const N: usize> =
    (usize, HashMap<ReductionGateParams<F, N>, (usize, usize)>);

impl<F: SmallField, const N: usize> Gate<F> for ReductionGate<F, N> {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= N
            && geometry.num_columns_under_copy_permutation >= Self::Evaluator::principal_width()
            && geometry.num_constant_columns >= N
    }

    type Evaluator = ReductionGateConstraintEvaluator<N>;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        ReductionGateConstraintEvaluator
    }
}

impl<F: SmallField, const N: usize> ReductionGate<F, N> {
    pub const fn empty() -> Self {
        Self {
            params: ReductionGateParams {
                reduction_constants: [F::ZERO; N],
            },
            terms: [Variable::placeholder(); N],
            reduction_result: Variable::placeholder(),
        }
    }

    pub fn configure_builder<
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        TImpl: CsBuilderImpl<F, TImpl>,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
        // ) -> CsBuilder<TImpl, F, GC::DescendantHolder<Self, ReductionGateTooling<F, N>>, TB> {
    ) -> CsBuilder<TImpl, F, (GateTypeEntry<F, Self, ReductionGateTooling<F, N>>, GC), TB> {
        builder.allow_gate(placement_strategy, (), (0, HashMap::new()))
    }

    pub fn reduce_terms<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        reduction_constants: [F; N],
        terms: [Variable; N],
    ) -> Variable {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variable = cs.alloc_variable_without_value();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; N]| {
                let mut result = F::ZERO;
                for (a, b) in inputs.into_iter().zip(reduction_constants.into_iter()) {
                    let mut tmp = a;
                    tmp.mul_assign(&b);
                    result.add_assign(&tmp);
                }

                [result]
            };

            let dependencies = Place::from_variables(terms);

            cs.set_values_with_dependencies(&dependencies, &[output_variable.into()], value_fn);
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                params: ReductionGateParams {
                    reduction_constants,
                },
                terms,
                reduction_result: output_variable,
            };
            gate.add_to_cs(cs);
        }

        output_variable
    }

    pub fn decompose_into_limbs<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        limb_size: F,
        input: Variable,
    ) -> [Variable; N] {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variables = cs.alloc_multiple_variables_without_values::<N>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 1]| {
                let mut current = inputs[0].as_u64_reduced();
                let limb_size = limb_size.as_u64_reduced();

                let mut results = [F::ZERO; N];
                for dst in results.iter_mut() {
                    let limb_value = current % limb_size;
                    *dst = F::from_u64_with_reduction(limb_value);

                    current /= limb_size;
                }

                results
            };

            cs.set_values_with_dependencies(
                &[input.into()],
                &Place::from_variables(output_variables),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == true {
            let mut current_constant = F::ONE;
            let reduction_constants = std::array::from_fn(|_| {
                let tmp = current_constant;
                current_constant.mul_assign(&limb_size);

                tmp
            });

            let gate = Self {
                params: ReductionGateParams {
                    reduction_constants,
                },
                terms: output_variables,
                reduction_result: input,
            };
            gate.add_to_cs(cs);
        }

        output_variables
    }

    pub fn decompose_into_limbs_limited<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        limb_size: F,
        input: Variable,
        limit: usize,
        zero_var: Variable,
    ) -> [Variable; N] {
        debug_assert!(limit <= N);
        debug_assert!(cs.gate_is_allowed::<Self>());

        let mut places_to_use: ArrayVec<Place, N> = ArrayVec::new();

        for _i in 0..limit {
            places_to_use.push(cs.alloc_variable_without_value().into());
        }

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: &[F], output: &mut DstBuffer<'_, '_, F>| {
                let mut current = inputs[0].as_u64_reduced();
                let limb_size = limb_size.as_u64_reduced();

                for _ in 0..limit {
                    let limb_value = current % limb_size;
                    let limb_value = F::from_u64_with_reduction(limb_value);
                    output.push(limb_value);

                    current /= limb_size;
                }
                debug_assert_eq!(current, 0);
            };

            cs.set_values_with_dependencies_vararg(&[input.into()], &places_to_use, value_fn);
        }

        let mut output_variables = [zero_var; N];
        for i in 0..limit {
            output_variables[i] = places_to_use[i].as_variable();
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let mut current_constant = F::ONE;
            let reduction_constants = std::array::from_fn(|idx| {
                if idx >= limit {
                    F::ZERO
                } else {
                    let tmp = current_constant;
                    current_constant.mul_assign(&limb_size);

                    tmp
                }
            });

            let gate = Self {
                params: ReductionGateParams {
                    reduction_constants,
                },
                terms: output_variables,
                reduction_result: input,
            };
            gate.add_to_cs(cs);
        }

        output_variables
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
                let tooling: &mut ReductionGateTooling<F, N> = cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, _>()
                    .expect("gate must be allowed");
                let (row, num_instances_already_placed) = find_next_gate(
                    &mut tooling.1,
                    self.params,
                    capacity_per_row,
                    offered_row_idx,
                );
                drop(tooling);

                // now we can use methods of CS to inform it of low level operations
                let mut offset =
                    num_instances_already_placed * <Self as Gate<F>>::Evaluator::principal_width();
                if offered_row_idx == row {
                    cs.place_gate(&self, row);
                }
                cs.place_constants(&self.params.reduction_constants, row, 0); // this gate used same constants per row only
                cs.place_multiple_variables_into_row(&self.terms, row, offset);
                offset += N;
                cs.place_variable(self.reduction_result, row, offset);
            }
            GatePlacementStrategy::UseSpecializedColumns {
                num_repetitions,
                share_constants: _,
            } => {
                let t: &mut ReductionGateTooling<F, N> = cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, _>()
                    .expect("gate must be allowed");
                let (next_available_row, tooling) = (&mut t.0, &mut t.1);
                let (row, num_instances_already_placed) = find_next_gate_specialized(
                    tooling,
                    next_available_row,
                    self.params,
                    num_repetitions,
                );
                cs.place_gate_specialized(&self, num_instances_already_placed, row);
                cs.place_constants_specialized::<Self, N>(
                    &self.params.reduction_constants,
                    num_instances_already_placed,
                    row,
                    0,
                );
                assert_no_placeholder_variables(&self.terms);
                cs.place_multiple_variables_into_row_specialized::<Self, N>(
                    &self.terms,
                    num_instances_already_placed,
                    row,
                    0,
                );
                cs.place_variable_specialized::<Self>(
                    self.reduction_result,
                    num_instances_already_placed,
                    row,
                    N,
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
            <ReductionGateConstraintEvaluator<4> as GateConstraintEvaluator<F>>::new_from_parameters(
                (),
            );

        test_evaluator::<F, _>(evaluator);
    }
}
