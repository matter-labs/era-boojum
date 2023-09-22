use crate::cs::cs_builder::{CsBuilder, CsBuilderImpl};

use super::*;

// A simple gate of c0 * A * B + c1 * C -> D

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FmaGateInBaseWithoutConstantConstraintEvaluator;

impl<F: PrimeField> GateConstraintEvaluator<F> for FmaGateInBaseWithoutConstantConstraintEvaluator {
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
            num_variables: 4,
            num_witnesses: 0,
            num_constants: 2,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: 3,
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
        debug_assert!(geometry.num_constant_columns >= 2);

        2
    }

    type GlobalConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = ();

    #[inline(always)]
    fn create_global_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>>(
        &self,
        _ctx: &mut P::Context,
    ) -> Self::GlobalConstants<P> {
    }

    type RowSharedConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = [P; 2];

    #[inline(always)]
    fn load_row_shared_constants<
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSource<F, P>,
    >(
        &self,
        trace_source: &S,
        _ctx: &mut P::Context,
    ) -> Self::RowSharedConstants<P> {
        let quadratic_term_coeff = trace_source.get_constant_value(0);
        let linear_term_coeff = trace_source.get_constant_value(1);

        [quadratic_term_coeff, linear_term_coeff]
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
        let a = trace_source.get_variable_value(0);
        let b = trace_source.get_variable_value(1);
        let c = trace_source.get_variable_value(2);
        let d = trace_source.get_variable_value(3);

        let [quadratic_term_coeff, linear_term_coeff] = shared_constants;

        let mut contribution = c;
        contribution.mul_assign(linear_term_coeff, ctx);

        let mut t = a;
        t.mul_assign(&b, ctx);

        P::mul_and_accumulate_into(&mut contribution, quadratic_term_coeff, &t, ctx);

        contribution.sub_assign(&d, ctx);

        destination.push_evaluation_result(contribution, ctx);
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FmaGateInBaseWithoutConstantParams<F: SmallField> {
    pub coeff_for_quadtaric_part: F,
    pub linear_term_coeff: F,
}

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FmaGateInBaseFieldWithoutConstant<F: SmallField> {
    pub params: FmaGateInBaseWithoutConstantParams<F>,
    pub quadratic_part: (Variable, Variable),
    pub linear_part: Variable,
    pub rhs_part: Variable,
}

const UNIQUE_IDENTIFIER: &str = "c0 * A * B + c1 * C -> D";
const PRINCIPAL_WIDTH: usize = 4;

// HashMap coefficients into row index to know vacant places
type FmaGateTooling<F> = (
    usize,
    HashMap<FmaGateInBaseWithoutConstantParams<F>, (usize, usize)>,
);

impl<F: SmallField> Gate<F> for FmaGateInBaseFieldWithoutConstant<F> {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 3
            && geometry.num_columns_under_copy_permutation >= 4
            && geometry.num_constant_columns >= 2
    }

    type Evaluator = FmaGateInBaseWithoutConstantConstraintEvaluator;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        FmaGateInBaseWithoutConstantConstraintEvaluator
    }
}

impl<F: SmallField> FmaGateInBaseFieldWithoutConstant<F> {
    pub const fn empty() -> Self {
        Self {
            params: FmaGateInBaseWithoutConstantParams {
                coeff_for_quadtaric_part: F::ZERO,
                linear_term_coeff: F::ZERO,
            },
            quadratic_part: (Variable::placeholder(), Variable::placeholder()),
            linear_part: Variable::placeholder(),
            rhs_part: Variable::placeholder(),
        }
    }

    pub fn configure_builder<
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        TImpl: CsBuilderImpl<F, TImpl>,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
        // ) -> CsBuilder<TImpl, F, GC::DescendantHolder<Self, FmaGateTooling<F>>, TB> {
    ) -> CsBuilder<TImpl, F, (GateTypeEntry<F, Self, FmaGateTooling<F>>, GC), TB> {
        builder.allow_gate(placement_strategy, (), (0, HashMap::with_capacity(16)))
    }

    pub fn add_to_cs<CS: ConstraintSystem<F>>(self, cs: &mut CS) {
        debug_assert!(cs.gate_is_allowed::<Self>());

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            return;
        }

        let all_variables = [
            self.quadratic_part.0,
            self.quadratic_part.1,
            self.linear_part,
            self.rhs_part,
        ];

        match cs.get_gate_placement_strategy::<Self>() {
            GatePlacementStrategy::UseGeneralPurposeColumns => {
                let offered_row_idx = cs.next_available_row();
                let capacity_per_row = self.capacity_per_row(&*cs);
                let tooling: &mut HashMap<FmaGateInBaseWithoutConstantParams<F>, (usize, usize)> =
                    &mut cs
                        .get_gates_config_mut()
                        .get_aux_data_mut::<Self, FmaGateTooling<F>>()
                        .expect("gate must be allowed")
                        .1;
                let (row, num_instances_already_placed) =
                    find_next_gate(tooling, self.params, capacity_per_row, offered_row_idx);
                drop(tooling);

                // now we can use methods of CS to inform it of low level operations
                let offset = num_instances_already_placed * PRINCIPAL_WIDTH;
                if offered_row_idx == row {
                    cs.place_gate(&self, row);
                }
                cs.place_constants(
                    &[
                        self.params.coeff_for_quadtaric_part,
                        self.params.linear_term_coeff,
                    ],
                    row,
                    0,
                ); // this gate used same constants per row only
                assert_no_placeholder_variables(&all_variables);
                cs.place_multiple_variables_into_row(&all_variables, row, offset);
            }
            GatePlacementStrategy::UseSpecializedColumns {
                num_repetitions,
                share_constants: _,
            } => {
                // gate knows how to place itself
                let capacity_per_row = num_repetitions;
                let t: &mut FmaGateTooling<F> = cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, FmaGateTooling<F>>()
                    .expect("gate must be allowed");

                let (next_available_row, tooling) = (&mut t.0, &mut t.1);
                let (row, num_instances_already_placed) = find_next_gate_specialized(
                    tooling,
                    next_available_row,
                    self.params,
                    capacity_per_row,
                );
                cs.place_gate_specialized(&self, num_instances_already_placed, row);
                cs.place_constants_specialized::<Self, 2>(
                    &[
                        self.params.coeff_for_quadtaric_part,
                        self.params.linear_term_coeff,
                    ],
                    num_instances_already_placed,
                    row,
                    0,
                ); // this gate used same constants per row only
                assert_no_placeholder_variables(&all_variables);
                cs.place_multiple_variables_into_row_specialized::<Self, 4>(
                    &all_variables,
                    num_instances_already_placed,
                    row,
                    0,
                );
            }
        }
    }

    pub fn compute_fma<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        coeff_for_quadtaric_part: F,
        ab: (Variable, Variable),
        linear_term_coeff: F,
        c: Variable,
    ) -> Variable {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variable = cs.alloc_variable_without_value();

        let params = FmaGateInBaseWithoutConstantParams {
            coeff_for_quadtaric_part,
            linear_term_coeff,
        };

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 3]| {
                let [a, b, c] = inputs;
                let mut result = params.coeff_for_quadtaric_part;
                result.mul_assign(&a).mul_assign(&b);

                let mut tmp = c;
                tmp.mul_assign(&params.linear_term_coeff);

                result.add_assign(&tmp);

                [result]
            };

            let dependencies = Place::from_variables([ab.0, ab.1, c]);

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables([output_variable]),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                params,
                quadratic_part: ab,
                linear_part: c,
                rhs_part: output_variable,
            };

            gate.add_to_cs(cs);
        }

        output_variable
    }

    pub fn create_inversion_constraint<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        variable_to_inverse: Variable,
        one_variable: Variable, // we need constant `1` (from any other consideration) as RHS
    ) -> Variable {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let params = FmaGateInBaseWithoutConstantParams {
            coeff_for_quadtaric_part: F::ONE,
            linear_term_coeff: F::ZERO,
        };

        use crate::config::*;

        // the only thing that we needed was to create a variable with some index.
        // When we are interested in proving only we are not interested in placement of such variable,
        // and instead only need index and value
        let output_variable = cs.alloc_variable_without_value();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 1]| {
                let inverse = inputs[0].inverse().unwrap();

                [inverse]
            };

            let dependencies = Place::from_variables([variable_to_inverse]);

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables([output_variable]),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let this = Self {
                params,
                quadratic_part: (variable_to_inverse, output_variable),
                linear_part: variable_to_inverse,
                rhs_part: one_variable,
            };
            this.add_to_cs(cs);
        }

        output_variable
    }
}
