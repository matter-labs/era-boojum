use crate::cs::cs_builder::{CsBuilder, CsBuilderImpl};
use crate::field::{ExtensionField, FieldExtension};

use super::*;

// A simple gate of c0 * A * B + c1 * C -> D in the extension field

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FmaGateInExtensionWithoutConstantConstraintEvaluator<
    F: PrimeField,
    EXT: FieldExtension<2, BaseField = F>,
> {
    _marker: std::marker::PhantomData<(F, EXT)>,
}

impl<F: PrimeField, EXT: FieldExtension<2, BaseField = F>> GateConstraintEvaluator<F>
    for FmaGateInExtensionWithoutConstantConstraintEvaluator<F, EXT>
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
        Cow::Borrowed(UNIQUE_IDENTIFIER)
    }

    #[inline]
    fn instance_width(&self) -> GatePrincipalInstanceWidth {
        GatePrincipalInstanceWidth {
            num_variables: 8,
            num_witnesses: 0,
            num_constants: 4,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: 3,
            num_quotient_terms: 2,
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
        debug_assert!(geometry.num_constant_columns >= 4);

        4
    }

    type GlobalConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = [P; 1];

    #[inline(always)]
    fn create_global_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>>(
        &self,
        ctx: &mut P::Context,
    ) -> Self::GlobalConstants<P> {
        let non_residue = P::constant(EXT::non_residue(), ctx);

        [non_residue]
    }

    type RowSharedConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = [P; 4];

    #[inline(always)]
    fn load_row_shared_constants<
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSource<F, P>,
    >(
        &self,
        trace_source: &S,
        _ctx: &mut P::Context,
    ) -> Self::RowSharedConstants<P> {
        let quadratic_term_coeff_c0 = trace_source.get_constant_value(0);
        let quadratic_term_coeff_c1 = trace_source.get_constant_value(1);

        let linear_term_coeff_c0 = trace_source.get_constant_value(2);
        let linear_term_coeff_c1 = trace_source.get_constant_value(3);

        [
            quadratic_term_coeff_c0,
            quadratic_term_coeff_c1,
            linear_term_coeff_c0,
            linear_term_coeff_c1,
        ]
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
        global_constants: &Self::GlobalConstants<P>,
        ctx: &mut P::Context,
    ) {
        let a_c0 = trace_source.get_variable_value(0);
        let a_c1 = trace_source.get_variable_value(1);
        let b_c0 = trace_source.get_variable_value(2);
        let b_c1 = trace_source.get_variable_value(3);
        let c_c0 = trace_source.get_variable_value(4);
        let c_c1 = trace_source.get_variable_value(5);
        let d_c0 = trace_source.get_variable_value(6);
        let d_c1 = trace_source.get_variable_value(7);

        let [quadratic_term_coeff_c0, quadratic_term_coeff_c1, linear_term_coeff_c0, linear_term_coeff_c1] =
            shared_constants;

        let [non_residue] = global_constants;

        // linear part is easy

        // c0 * c0
        let mut linear_c0 = c_c0;
        linear_c0.mul_assign(linear_term_coeff_c0, ctx);

        // c1 * c1 * non-res
        let mut t = c_c1;
        t.mul_assign(linear_term_coeff_c1, ctx);
        P::mul_and_accumulate_into(&mut linear_c0, &t, non_residue, ctx);

        // c0 * c1
        let mut linear_c1 = c_c0;
        linear_c1.mul_assign(linear_term_coeff_c1, ctx);
        // c1 * c0
        P::mul_and_accumulate_into(&mut linear_c1, &c_c1, linear_term_coeff_c0, ctx);

        // compute first term of c0 * A * B

        let mut inner_c0 = a_c0;
        inner_c0.mul_assign(&b_c0, ctx);

        let mut t = a_c1;
        t.mul_assign(&b_c1, ctx);
        P::mul_and_accumulate_into(&mut inner_c0, &t, non_residue, ctx);

        let mut inner_c1 = a_c0;
        inner_c1.mul_assign(&b_c1, ctx);
        P::mul_and_accumulate_into(&mut inner_c1, &a_c1, &b_c0, ctx);

        // and use those to make next term

        let mut final_c0 = inner_c0;
        final_c0.mul_assign(quadratic_term_coeff_c0, ctx);

        let mut t = inner_c1;
        t.mul_assign(quadratic_term_coeff_c1, ctx);
        P::mul_and_accumulate_into(&mut final_c0, &t, non_residue, ctx);

        let mut final_c1 = inner_c0;
        final_c1.mul_assign(quadratic_term_coeff_c1, ctx);
        P::mul_and_accumulate_into(&mut final_c1, &inner_c1, quadratic_term_coeff_c0, ctx);

        // add linear part

        final_c0.add_assign(&linear_c0, ctx);
        final_c1.add_assign(&linear_c1, ctx);

        // output contributions

        let mut contribution = final_c0;
        contribution.sub_assign(&d_c0, ctx);
        destination.push_evaluation_result(contribution, ctx);

        let mut contribution = final_c1;
        contribution.sub_assign(&d_c1, ctx);
        destination.push_evaluation_result(contribution, ctx);
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq(bound = ""), Eq(bound = ""), Hash)]
pub struct FmaGateInExtensionWithoutConstantParams<
    F: SmallField,
    EXT: FieldExtension<2, BaseField = F>,
> {
    pub coeff_for_quadtaric_part: ExtensionField<F, 2, EXT>,
    pub linear_term_coeff: ExtensionField<F, 2, EXT>,
}

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FmaGateInExtensionWithoutConstant<F: SmallField, EXT: FieldExtension<2, BaseField = F>> {
    pub params: FmaGateInExtensionWithoutConstantParams<F, EXT>,
    pub quadratic_part: ([Variable; 2], [Variable; 2]),
    pub linear_part: [Variable; 2],
    pub rhs_part: [Variable; 2],
}

const UNIQUE_IDENTIFIER: &str = "c0 * A * B + c1 * C -> D in quadratic extension";
const PRINCIPAL_WIDTH: usize = 8;

// HashMap coefficients into row index to know vacant places
type FmaInExtensionGateTooling<F, EXT> = (
    usize,
    HashMap<FmaGateInExtensionWithoutConstantParams<F, EXT>, (usize, usize)>,
);

impl<F: SmallField, EXT: FieldExtension<2, BaseField = F>> Gate<F>
    for FmaGateInExtensionWithoutConstant<F, EXT>
{
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 3
            && geometry.num_columns_under_copy_permutation >= 8
            && geometry.num_constant_columns >= 4
    }

    type Evaluator = FmaGateInExtensionWithoutConstantConstraintEvaluator<F, EXT>;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        FmaGateInExtensionWithoutConstantConstraintEvaluator {
            _marker: std::marker::PhantomData,
        }
    }
}

impl<F: SmallField, EXT: FieldExtension<2, BaseField = F>>
    FmaGateInExtensionWithoutConstant<F, EXT>
{
    pub fn configure_builder<
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        TImpl: CsBuilderImpl<F, TImpl>,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
        // ) -> CsBuilder<TImpl, F, GC::DescendantHolder<Self, FmaGateTooling<F>>, TB> {
    ) -> CsBuilder<
        TImpl,
        F,
        (
            GateTypeEntry<F, Self, FmaInExtensionGateTooling<F, EXT>>,
            GC,
        ),
        TB,
    > {
        builder.allow_gate(placement_strategy, (), (0, HashMap::with_capacity(16)))
    }

    pub fn add_to_cs<CS: ConstraintSystem<F>>(self, cs: &mut CS) {
        debug_assert!(cs.gate_is_allowed::<Self>());

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            return;
        }

        let all_variables = [
            self.quadratic_part.0[0],
            self.quadratic_part.0[1],
            self.quadratic_part.1[0],
            self.quadratic_part.1[1],
            self.linear_part[0],
            self.linear_part[1],
            self.rhs_part[0],
            self.rhs_part[1],
        ];

        match cs.get_gate_placement_strategy::<Self>() {
            GatePlacementStrategy::UseGeneralPurposeColumns => {
                let offered_row_idx = cs.next_available_row();
                let capacity_per_row = self.capacity_per_row(&*cs);
                let tooling: &mut HashMap<
                    FmaGateInExtensionWithoutConstantParams<F, EXT>,
                    (usize, usize),
                > = &mut cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, FmaInExtensionGateTooling<F, EXT>>()
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
                        self.params.coeff_for_quadtaric_part.coeffs[0],
                        self.params.coeff_for_quadtaric_part.coeffs[1],
                        self.params.linear_term_coeff.coeffs[0],
                        self.params.linear_term_coeff.coeffs[1],
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
                let t: &mut FmaInExtensionGateTooling<F, EXT> = cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, FmaInExtensionGateTooling<F, EXT>>()
                    .expect("gate must be allowed");

                let (next_available_row, tooling) = (&mut t.0, &mut t.1);
                let (row, num_instances_already_placed) = find_next_gate_specialized(
                    tooling,
                    next_available_row,
                    self.params,
                    capacity_per_row,
                );
                cs.place_gate_specialized(&self, num_instances_already_placed, row);
                cs.place_constants_specialized::<Self, 4>(
                    &[
                        self.params.coeff_for_quadtaric_part.coeffs[0],
                        self.params.coeff_for_quadtaric_part.coeffs[1],
                        self.params.linear_term_coeff.coeffs[0],
                        self.params.linear_term_coeff.coeffs[1],
                    ],
                    num_instances_already_placed,
                    row,
                    0,
                ); // this gate used same constants per row only
                assert_no_placeholder_variables(&all_variables);
                cs.place_multiple_variables_into_row_specialized::<Self, 8>(
                    &all_variables,
                    num_instances_already_placed,
                    row,
                    0,
                );
            }
        }
    }

    pub fn compute_fma_in_extension<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        coeff_for_quadtaric_part: ExtensionField<F, 2, EXT>,
        ab: ([Variable; 2], [Variable; 2]),
        linear_term_coeff: ExtensionField<F, 2, EXT>,
        c: [Variable; 2],
    ) -> [Variable; 2] {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variables = cs.alloc_multiple_variables_without_values::<2>();

        let params = FmaGateInExtensionWithoutConstantParams {
            coeff_for_quadtaric_part,
            linear_term_coeff,
        };

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 6]| {
                let [a_c0, a_c1, b_c0, b_c1, c_c0, c_c1] = inputs;
                let a = ExtensionField::<F, 2, EXT>::from_coeff_in_base([a_c0, a_c1]);
                let b = ExtensionField::<F, 2, EXT>::from_coeff_in_base([b_c0, b_c1]);
                let c = ExtensionField::<F, 2, EXT>::from_coeff_in_base([c_c0, c_c1]);

                let mut result = params.coeff_for_quadtaric_part;
                use crate::field::traits::field::Field;
                result.mul_assign(&a).mul_assign(&b);

                let mut tmp = c;
                tmp.mul_assign(&params.linear_term_coeff);

                result.add_assign(&tmp);

                result.into_coeffs_in_base()
            };

            let dependencies =
                Place::from_variables([ab.0[0], ab.0[1], ab.1[0], ab.1[1], c[0], c[1]]);

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables(output_variables),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                params,
                quadratic_part: ab,
                linear_part: c,
                rhs_part: output_variables,
            };

            gate.add_to_cs(cs);
        }

        output_variables
    }

    pub fn create_inversion_constraint<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        variable_to_inverse: [Variable; 2],
        zero_variable: Variable,
        one_variable: Variable, // we need constant `1` (from any other consideration) as RHS
    ) -> [Variable; 2] {
        debug_assert!(cs.gate_is_allowed::<Self>());

        use crate::field::traits::field::Field;
        let params = FmaGateInExtensionWithoutConstantParams {
            coeff_for_quadtaric_part: ExtensionField::ONE,
            linear_term_coeff: ExtensionField::ZERO,
        };

        use crate::config::*;

        // the only thing that we needed was to create a variable with some index.
        // When we are interested in proving only we are not interested in placement of such variable,
        // and instead only need index and value
        let output_variables = cs.alloc_multiple_variables_without_values::<2>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 2]| {
                let value = ExtensionField::<F, 2, EXT>::from_coeff_in_base(inputs);
                let inverse = value.inverse().unwrap();

                inverse.into_coeffs_in_base()
            };

            let dependencies = Place::from_variables(variable_to_inverse);

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables(output_variables),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let this = Self {
                params,
                quadratic_part: (variable_to_inverse, output_variables),
                linear_part: variable_to_inverse, // not important
                rhs_part: [one_variable, zero_variable],
            };
            this.add_to_cs(cs);
        }

        output_variables
    }
}

#[cfg(test)]
mod test {
    use std::alloc::Global;

    use crate::dag::CircuitResolverOpts;
    use crate::dag::DefaultCircuitResolver;
    use crate::field::Field;

    use super::*;
    use crate::worker::Worker;
    type F = crate::field::goldilocks::GoldilocksField;
    type Ext = crate::field::goldilocks::GoldilocksExt2;
    type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;
    type CR = DefaultCircuitResolver<F, RCfg>;
    use crate::cs::cs_builder::*;
    use crate::cs::cs_builder_reference::*;

    #[test]
    fn test_simple_poseidon2() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 16,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 8,
        };

        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig, CR>::new(geometry, 8);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = FmaGateInExtensionWithoutConstant::<F, Ext>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(CircuitResolverOpts::new(128));

        let cs = &mut owned_cs;

        let mut inputs = [Variable::placeholder(); 6];
        for (idx, dst) in inputs.iter_mut().enumerate() {
            let value = F::from_u64_with_reduction((idx + 1) as u64);
            let var = cs.alloc_single_variable_from_witness(value);
            *dst = var;
        }

        let mut k = ExtensionField::<F, 2, Ext>::ONE;
        k.coeffs[1] = F::MINUS_ONE;

        let mut m = ExtensionField::<F, 2, Ext>::TWO;
        m.coeffs[1] = F::TWO;

        let result = FmaGateInExtensionWithoutConstant::compute_fma_in_extension(
            cs,
            k,
            ([inputs[0], inputs[1]], [inputs[2], inputs[3]]),
            m,
            [inputs[4], inputs[5]],
        );

        let zero = cs.allocate_constant(F::ZERO);
        let one = cs.allocate_constant(F::ONE);

        let _result = FmaGateInExtensionWithoutConstant::<F, Ext>::create_inversion_constraint(
            cs, result, zero, one,
        );

        drop(cs);
        owned_cs.pad_and_shrink();

        let worker = Worker::new();

        log!("Checking if satisfied");
        let mut owned_cs = owned_cs.into_assembly::<Global>();
        assert!(owned_cs.check_if_satisfied(&worker));
    }
}
