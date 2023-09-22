use crate::cs::cs_builder::{CsBuilder, CsBuilderImpl};
use crate::cs::traits::gate::FinalizationHintSerialized;

use super::*;

// y = (x + constant)^k

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SimpleNonlinearityGateConstraintEvaluator<const N: usize>;

const PRINCIPAL_WIDTH: usize = 2;

impl<F: PrimeField, const N: usize> GateConstraintEvaluator<F>
    for SimpleNonlinearityGateConstraintEvaluator<N>
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
            num_variables: PRINCIPAL_WIDTH,
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
                variables_offset: PRINCIPAL_WIDTH,
                witnesses_offset: 0,
                constants_offset: 0,
            },
        }
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, geometry: &CSGeometry) -> usize {
        debug_assert!(geometry.num_columns_under_copy_permutation >= PRINCIPAL_WIDTH);

        geometry.num_columns_under_copy_permutation / PRINCIPAL_WIDTH
    }

    #[inline]
    fn num_required_constants_in_geometry(&self, geometry: &CSGeometry) -> usize {
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
        let additive_constant = trace_source.get_constant_value(0);

        [additive_constant]
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
        let x = trace_source.get_variable_value(0);
        let y = trace_source.get_variable_value(1);

        let [additive_constant] = shared_constants;

        let mut tmp = x;
        tmp.add_assign(additive_constant, ctx);

        let mut contribution = tmp;
        contribution.small_pow(N, ctx);
        contribution.sub_assign(&y, ctx);

        destination.push_evaluation_result(contribution, ctx);
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SimpleNonlinearityGate<F: SmallField, const N: usize> {
    pub x: Variable,
    pub y: Variable,
    pub additive_constant: F,
}

// HashMap coefficients into row index to know vacant places
type SimpleNonlinearityGateTooling<F> = (usize, HashMap<F, (usize, usize)>);

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Default)]
pub struct NonlinearityGateFinalizationHint<const N: usize> {
    pub instances_to_add: Vec<(u64, usize)>,
}

impl<F: SmallField, const N: usize> Gate<F> for SimpleNonlinearityGate<F, N> {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= N
            && geometry.num_columns_under_copy_permutation >= PRINCIPAL_WIDTH
            && geometry.num_constant_columns >= 1
    }

    type Evaluator = SimpleNonlinearityGateConstraintEvaluator<N>;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        SimpleNonlinearityGateConstraintEvaluator::<N>
    }

    // it has non-trivial cleanup
    fn row_finalization_function<CS: ConstraintSystem<F>>(
    ) -> Option<traits::gate::GateRowCleanupFunction<CS>> {
        let closure = move |cs: &mut CS, hint: &Option<FinalizationHintSerialized>| {
            // we need to fill our witnesses with non-trivial values

            // We fill with a strategy that input is 0, so result of logical evaluation is 1
            let geometry = cs.get_params();

            let finalization_hint: NonlinearityGateFinalizationHint<N> =
                if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                    let mut new_hint = NonlinearityGateFinalizationHint::default();
                    let tooling: &HashMap<F, (usize, usize)> = &cs
                        .get_gates_config()
                        .get_aux_data::<Self, SimpleNonlinearityGateTooling<F>>()
                        .expect("gate must be allowed")
                        .1;

                    // even though it may not be strictly necessary, we DO sort here

                    let evaluator =
                        <Self::Evaluator as GateConstraintEvaluator<F>>::new_from_parameters(());
                    let num_repetitions = GateConstraintEvaluator::<F>::num_repetitions_in_geometry(
                        &evaluator, &geometry,
                    );

                    let keys: Vec<_> = tooling.keys().map(|el| el.as_u64_reduced()).collect();

                    for el in keys.into_iter() {
                        let as_fe = F::from_u64_unchecked(el);
                        let (_row, num_instances_already_placed) = tooling[&as_fe];
                        let instances_to_add = num_repetitions - num_instances_already_placed;

                        assert!(instances_to_add > 0);
                        new_hint.instances_to_add.push((el, instances_to_add));
                    }

                    new_hint
                } else {
                    assert!(hint.is_some());

                    let hint = bincode::deserialize(
                        hint.as_ref()
                            .expect("should be present if setup information is not available"),
                    )
                    .expect(&format!(
                        "should have properly encoded padding hint for gate {}",
                        std::any::type_name::<Self>()
                    ));

                    hint
                };

            let NonlinearityGateFinalizationHint { instances_to_add } = &finalization_hint;

            if !instances_to_add.is_empty() {
                let var = cs.alloc_single_variable_from_witness(F::ONE);

                for (el, instances_to_add) in instances_to_add.iter() {
                    let coeff = F::from_u64_unchecked(*el);
                    for _ in 0..*instances_to_add {
                        Self::apply_nonlinearity(cs, var, coeff);
                    }
                }
            }

            // self-check
            if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                let tooling: &HashMap<F, (usize, usize)> = &cs
                    .get_gates_config()
                    .get_aux_data::<Self, SimpleNonlinearityGateTooling<F>>()
                    .expect("gate must be allowed")
                    .1;

                assert!(tooling.is_empty());
                drop(tooling);
            }

            if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
                let encoded = bincode::serialize(&finalization_hint).expect("must serialize");
                Some(encoded)
            } else {
                None
            }
        };

        Some(Box::new(closure) as _)
    }
}

impl<F: SmallField, const N: usize> SimpleNonlinearityGate<F, N> {
    pub fn configure_builder<
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        TImpl: CsBuilderImpl<F, TImpl>,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
        // ) -> CsBuilder<TImpl, F, GC::DescendantHolder<Self, SimpleNonlinearityGateTooling<F>>, TB> {
    ) -> CsBuilder<TImpl, F, (GateTypeEntry<F, Self, SimpleNonlinearityGateTooling<F>>, GC), TB>
    {
        builder.allow_gate(placement_strategy, (), (0, HashMap::with_capacity(16)))
    }

    pub fn add_to_cs<CS: ConstraintSystem<F>>(self, cs: &mut CS) {
        debug_assert!(cs.gate_is_allowed::<Self>());

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            return;
        }

        let all_variables = [self.x, self.y];
        assert_no_placeholder_variables(&all_variables);

        match cs.get_gate_placement_strategy::<Self>() {
            GatePlacementStrategy::UseGeneralPurposeColumns => {
                let offered_row_idx = cs.next_available_row();
                let capacity_per_row = self.capacity_per_row(&*cs);
                let tooling: &mut HashMap<F, (usize, usize)> = &mut cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, SimpleNonlinearityGateTooling<F>>()
                    .expect("gate must be allowed")
                    .1;
                let (row, num_instances_already_placed) = find_next_gate(
                    tooling,
                    self.additive_constant,
                    capacity_per_row,
                    offered_row_idx,
                );
                drop(tooling);

                // now we can use methods of CS to inform it of low level operations
                let offset = num_instances_already_placed * PRINCIPAL_WIDTH;
                if offered_row_idx == row {
                    cs.place_gate(&self, row);
                }
                cs.place_constants(&[self.additive_constant], row, 0); // this gate used same constants per row only
                assert_no_placeholder_variables(&all_variables);
                cs.place_multiple_variables_into_row(&all_variables, row, offset);
            }
            GatePlacementStrategy::UseSpecializedColumns {
                num_repetitions,
                share_constants: _,
            } => {
                // gate knows how to place itself
                let capacity_per_row = num_repetitions;
                let t: &mut SimpleNonlinearityGateTooling<F> = cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, SimpleNonlinearityGateTooling<F>>()
                    .expect("gate must be allowed");

                let (next_available_row, tooling) = (&mut t.0, &mut t.1);
                let (row, num_instances_already_placed) = find_next_gate_specialized(
                    tooling,
                    next_available_row,
                    self.additive_constant,
                    capacity_per_row,
                );
                cs.place_gate_specialized(&self, num_instances_already_placed, row);
                cs.place_constants_specialized::<Self, 1>(
                    &[self.additive_constant],
                    num_instances_already_placed,
                    row,
                    0,
                ); // this gate used same constants per row only
                assert_no_placeholder_variables(&all_variables);
                cs.place_multiple_variables_into_row_specialized::<Self, 2>(
                    &all_variables,
                    num_instances_already_placed,
                    row,
                    0,
                );
            }
        }
    }

    pub fn apply_nonlinearity<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        x: Variable,
        additive_part: F,
    ) -> Variable {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variable = cs.alloc_variable_without_value();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 1]| {
                let [x] = inputs;
                let mut result = additive_part;
                result.add_assign(&x);
                result.small_pow(N);

                [result]
            };

            let dependencies = Place::from_variables([x]);

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables([output_variable]),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                x,
                y: output_variable,
                additive_constant: additive_part,
            };

            gate.add_to_cs(cs);
        }

        output_variable
    }
}

use crate::gadgets::traits::configuration::ConfigurationFunction;

impl<F: SmallField, const N: usize> ConfigurationFunction<F> for SimpleNonlinearityGate<F, N> {
    fn configure<TImpl: CsBuilderImpl<F, TImpl>>(
        builder: CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder>,
        placement_strategy: GatePlacementStrategy,
    ) -> CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
        Self::configure_builder(builder, placement_strategy)
    }
}
