use super::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ReductionByPowersGateConstraintEvaluator<const N: usize>;

impl<const N: usize> ReductionByPowersGateConstraintEvaluator<N> {
    const fn principal_width() -> usize {
        N + 1
    }
}

impl<F: PrimeField, const N: usize> GateConstraintEvaluator<F>
    for ReductionByPowersGateConstraintEvaluator<N>
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
            num_constants: 1,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: N,
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

        1
    }

    type GlobalConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = ();

    #[inline(always)]
    fn create_global_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>>(
        &self,
        _ctx: &mut P::Context,
    ) -> Self::GlobalConstants<P> {
    }

    type RowSharedConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = [P; 1];

    #[inline(always)]
    fn load_row_shared_constants<
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSource<F, P>,
    >(
        &self,
        trace_source: &S,
        _ctx: &mut P::Context,
    ) -> Self::RowSharedConstants<P> {
        let reduction_constants = trace_source.get_constant_value(0);

        [reduction_constants]
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
        let [reduction_constants] = shared_constants;

        let mut current_constant = P::one(ctx);

        let mut contribution = P::zero(ctx);

        // TODO: update to Horner rule

        for idx in 0..N {
            if idx != 0 {
                current_constant.mul_assign(reduction_constants, ctx);
            }

            let var = trace_source.get_variable_value(idx);
            let mut tmp = var;
            tmp.mul_assign(&current_constant, ctx);
            contribution.add_assign(&tmp, ctx);
        }

        let reduction_result = trace_source.get_variable_value(N);
        contribution.sub_assign(&reduction_result, ctx);

        destination.push_evaluation_result(contribution, ctx);
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ReductionByPowersGateParams<F: SmallField> {
    pub reduction_constant: F,
}

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ReductionByPowersGate<F: SmallField, const N: usize> {
    pub params: ReductionByPowersGateParams<F>,
    pub terms: [Variable; N],
    pub reduction_result: Variable,
}

// HashMap coefficients into row index to know vacant places
type ReductionByPowersGateTooling<F> = HashMap<ReductionByPowersGateParams<F>, (usize, usize)>;

impl<F: SmallField, const N: usize> Gate<F> for ReductionByPowersGate<F, N> {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= N
            && geometry.num_columns_under_copy_permutation >= Self::Evaluator::principal_width()
            && geometry.num_constant_columns >= 1
    }

    type Evaluator = ReductionByPowersGateConstraintEvaluator<N>;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        ReductionByPowersGateConstraintEvaluator
    }
}

impl<F: SmallField, const N: usize> ReductionByPowersGate<F, N> {
    pub const fn empty() -> Self {
        Self {
            params: ReductionByPowersGateParams {
                reduction_constant: F::ZERO,
            },
            terms: [Variable::placeholder(); N],
            reduction_result: Variable::placeholder(),
        }
    }

    pub fn reduce_terms<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        reduction_constant: F,
        terms: [Variable; N],
    ) -> Variable {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variable = cs.alloc_variable_without_value();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; N]| {
                let mut current_constant = F::ONE;
                let mut result = F::ZERO;
                for (idx, el) in inputs.into_iter().enumerate() {
                    if idx != 0 {
                        current_constant.mul_assign(&reduction_constant);
                    }
                    let mut tmp = el;
                    tmp.mul_assign(&current_constant);
                    result.add_assign(&tmp);
                }

                [result]
            };

            let dependencies = Place::from_variables(terms);

            cs.set_values_with_dependencies(&dependencies, &[output_variable.into()], value_fn);
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                params: ReductionByPowersGateParams { reduction_constant },
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

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                params: ReductionByPowersGateParams {
                    reduction_constant: limb_size,
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
            let gate = Self {
                params: ReductionByPowersGateParams {
                    reduction_constant: limb_size,
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
                let tooling: &mut ReductionByPowersGateTooling<F> = cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, _>()
                    .expect("gate must be allowed");
                let (row, num_instances_already_placed) =
                    find_next_gate(tooling, self.params, capacity_per_row, offered_row_idx);
                drop(tooling);

                // now we can use methods of CS to inform it of low level operations
                let mut offset =
                    num_instances_already_placed * <Self as Gate<F>>::Evaluator::principal_width();
                if offered_row_idx == row {
                    cs.place_gate(&self, row);
                }
                cs.place_constants(&[self.params.reduction_constant], row, 0); // this gate used same constants per row only
                cs.place_multiple_variables_into_row(&self.terms, row, offset);
                offset += N;
                cs.place_variable(self.reduction_result, row, offset);
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
                cs.place_constants_specialized::<Self, 1>(
                    &[self.params.reduction_constant],
                    num_instances_already_placed,
                    row,
                    0,
                ); // this gate used same constants per row only
                let mut offset = 0;
                cs.place_multiple_variables_into_row_specialized::<Self, N>(
                    &self.terms,
                    row,
                    offset,
                    0,
                );
                offset += N;
                cs.place_variable_specialized::<Self>(
                    self.reduction_result,
                    num_instances_already_placed,
                    row,
                    offset,
                );
            }
        }
    }
}
