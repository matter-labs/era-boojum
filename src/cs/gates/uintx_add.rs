use crate::{
    cs::cs_builder::{CsBuilder, CsBuilderImpl},
    gadgets::traits::castable::WitnessCastable,
};

use super::*;

// a + b + carry_in = c + 2^N * carry_out,
// `carry_out` is boolean constrainted
// but `c` is NOT. We will use reduction gate to perform decomposition of `c`, and separate range checks

const UNIQUE_IDENTIFIER: &str = "a + b + carry_in = c + 2^N * carry_out";
const PRINCIPAL_WIDTH: usize = 5;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct UIntXAddConstraintEvaluator;

impl<F: PrimeField> GateConstraintEvaluator<F> for UIntXAddConstraintEvaluator {
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
            num_variables: PRINCIPAL_WIDTH,
            num_witnesses: 0,
            num_constants: 1,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: 2,
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
        [trace_source.get_constant_value(0)]
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
        let [shift] = shared_constants;
        let a = trace_source.get_variable_value(0);
        let b = trace_source.get_variable_value(1);
        let carry_in = trace_source.get_variable_value(2);
        let c = trace_source.get_variable_value(3);
        let carry_out = trace_source.get_variable_value(4);

        // - constraint a + b + carry_in = c + 2^N * carry_out

        let mut contribution = a;
        contribution.add_assign(&b, ctx);
        contribution.add_assign(&carry_in, ctx);
        contribution.sub_assign(&c, ctx);

        let mut tmp = *shift;
        tmp.mul_assign(&carry_out, ctx);
        contribution.sub_assign(&tmp, ctx);

        destination.push_evaluation_result(contribution, ctx);

        // carry_out is boolean

        let mut contribution = carry_out;
        contribution.mul_assign(&carry_out, ctx);
        contribution.sub_assign(&carry_out, ctx);

        destination.push_evaluation_result(contribution, ctx);
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UIntXAddGate<const WIDTH: usize> {
    pub a: Variable,
    pub b: Variable,
    pub carry_in: Variable,
    pub c: Variable,
    pub carry_out: Variable,
}

// individual for each width

impl<F: SmallField, const WIDTH: usize> Gate<F> for UIntXAddGate<WIDTH> {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 2
            && geometry.num_columns_under_copy_permutation >= PRINCIPAL_WIDTH
    }

    // even though we make width a type parameter here, they share the evaluator
    type Evaluator = UIntXAddConstraintEvaluator;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        UIntXAddConstraintEvaluator
    }
}

impl<const WIDTH: usize> UIntXAddGate<WIDTH> {
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

    pub fn add_to_cs<F: SmallField, CS: ConstraintSystem<F>>(self, cs: &mut CS) {
        debug_assert!(F::CAPACITY_BITS >= WIDTH + 1);
        debug_assert!(WIDTH == 8 || WIDTH == 16 || WIDTH == 32);
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
                let all_variables = [self.a, self.b, self.carry_in, self.c, self.carry_out];
                assert_no_placeholder_variables(&all_variables);
                cs.place_constants(&[F::from_u64_unchecked(1u64 << WIDTH)], row, 0);
                cs.place_multiple_variables_into_row(&all_variables, row, offset);
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
                let all_variables = [self.a, self.b, self.carry_in, self.c, self.carry_out];
                assert_no_placeholder_variables(&all_variables);
                cs.place_constants_specialized::<Self, 1>(
                    &[F::from_u64_unchecked(1u64 << WIDTH)],
                    num_instances_already_placed,
                    row,
                    0,
                );
                cs.place_multiple_variables_into_row_specialized::<Self, 5>(
                    &all_variables,
                    num_instances_already_placed,
                    row,
                    0,
                );
            }
        }
    }

    pub fn perform_addition<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: Variable,
        b: Variable,
        carry_in: Variable,
    ) -> (Variable, Variable) {
        debug_assert!(F::CAPACITY_BITS >= WIDTH + 1);
        debug_assert!(WIDTH == 8 || WIDTH == 16 || WIDTH == 32);
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variables = cs.alloc_multiple_variables_without_values::<2>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 3]| {
                let [a, b, carry_in] = inputs;
                let a = a.as_u64_reduced();
                let b = b.as_u64_reduced();
                let carry_in = <bool as WitnessCastable<F, F>>::cast_from_source(carry_in);

                debug_assert!(a < 1u64 << WIDTH);
                debug_assert!(b < 1u64 << WIDTH);

                let result = a + b + carry_in as u64;

                let c = result & ((1u64 << WIDTH) - 1);
                let carry_out = result >= 1u64 << WIDTH;

                let c = F::from_u64_with_reduction(c);
                let carry_out = F::from_u64_with_reduction(carry_out as u64);

                [c, carry_out]
            };

            let dependencies = Place::from_variables([a, b, carry_in]);

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables(output_variables),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                a,
                b,
                carry_in,
                c: output_variables[0],
                carry_out: output_variables[1],
            };

            gate.add_to_cs(cs);
        }

        (output_variables[0], output_variables[1])
    }

    pub fn perform_addition_no_carry<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: Variable,
        b: Variable,
        carry_in: Variable,
        zero_var: Variable,
    ) -> Variable {
        debug_assert!(F::CAPACITY_BITS >= WIDTH + 1);
        debug_assert!(WIDTH == 8 || WIDTH == 16 || WIDTH == 32);
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variable = cs.alloc_variable_without_value();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 3]| {
                let [a, b, carry_in] = inputs;
                let a = a.as_u64_reduced();
                let b = b.as_u64_reduced();
                let carry_in = <bool as WitnessCastable<F, F>>::cast_from_source(carry_in);

                debug_assert!(a < 1u64 << WIDTH);
                debug_assert!(b < 1u64 << WIDTH);

                let result = a + b + carry_in as u64;

                let c = result & ((1u64 << WIDTH) - 1);
                let carry_out = result >= 1u64 << WIDTH;

                let c = F::from_u64_unchecked(c);

                debug_assert_eq!(carry_out, false);

                [c]
            };

            let dependencies = Place::from_variables([a, b, carry_in]);

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables([output_variable]),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                a,
                b,
                carry_in,
                c: output_variable,
                carry_out: zero_var,
            };

            gate.add_to_cs(cs);
        }

        output_variable
    }

    // a + b + carry_in = c + 2^N * carry_out
    // and
    // a - b + 2^N * borrow_out - borrow_in = c -> a + 2^N * borrow_out = b + c + borrow_in
    // can be re-arranged into the same relation
    // Caller is responsible to range-check the output variable
    pub fn perform_subtraction<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: Variable,
        b: Variable,
        borrow_in: Variable,
    ) -> (Variable, Variable) {
        debug_assert!(F::CAPACITY_BITS >= WIDTH + 1);
        debug_assert!(WIDTH == 8 || WIDTH == 16 || WIDTH == 32);
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variables = cs.alloc_multiple_variables_without_values::<2>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 3]| {
                let [a, b, borrow_in] = inputs;
                let a = a.as_u64_reduced();
                let b = b.as_u64_reduced();
                let borrow_in = <bool as WitnessCastable<F, F>>::cast_from_source(borrow_in);

                debug_assert!(a < 1u64 << WIDTH);
                debug_assert!(b < 1u64 << WIDTH);

                let result = (1u64 << WIDTH)
                    .wrapping_add(a)
                    .wrapping_sub(b)
                    .wrapping_sub(borrow_in as u64);

                let c = result & ((1u64 << WIDTH) - 1);
                let borrow_out = result < (1u64 << WIDTH);

                let c = F::from_u64_with_reduction(c);
                let borrow_out = F::from_u64_with_reduction(borrow_out as u64);

                [c, borrow_out]
            };

            let dependencies = Place::from_variables([a, b, borrow_in]);

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables(output_variables),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                a: output_variables[0],
                b,
                carry_in: borrow_in,
                c: a,
                carry_out: output_variables[1],
            };

            gate.add_to_cs(cs);
        }

        (output_variables[0], output_variables[1])
    }

    pub fn perform_subtraction_no_borrow<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: Variable,
        b: Variable,
        borrow_in: Variable,
        zero_var: Variable,
    ) -> Variable {
        debug_assert!(F::CAPACITY_BITS >= WIDTH + 1);
        debug_assert!(WIDTH == 8 || WIDTH == 16 || WIDTH == 32);
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variable = cs.alloc_variable_without_value();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 3]| {
                let [a, b, borrow_in] = inputs;
                let a = a.as_u64_reduced();
                let b = b.as_u64_reduced();
                let borrow_in = <bool as WitnessCastable<F, F>>::cast_from_source(borrow_in);

                debug_assert!(a < 1u64 << WIDTH);
                debug_assert!(b < 1u64 << WIDTH);

                let result = (1u64 << WIDTH)
                    .wrapping_add(a)
                    .wrapping_sub(b)
                    .wrapping_sub(borrow_in as u64);

                let c = result & ((1u64 << WIDTH) - 1);
                let borrow_out = result < (1u64 << WIDTH);

                debug_assert_eq!(borrow_out, false);

                let c = F::from_u64_with_reduction(c);

                [c]
            };

            let dependencies = Place::from_variables([a, b, borrow_in]);

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables([output_variable]),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                a: output_variable,
                b,
                carry_in: borrow_in,
                c: a,
                carry_out: zero_var,
            };

            gate.add_to_cs(cs);
        }

        output_variable
    }

    pub fn enforce_add_relation_compute_carry<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: Variable,
        b: Variable,
        carry_in: Variable,
        c: Variable,
    ) -> Variable {
        debug_assert!(F::CAPACITY_BITS >= WIDTH + 1);
        debug_assert!(WIDTH == 8 || WIDTH == 16 || WIDTH == 32);
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variable = cs.alloc_variable_without_value();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 4]| {
                let [a, b, carry_in, c] = inputs;
                let a = a.as_u64_reduced();
                let b = b.as_u64_reduced();
                let carry_in = <bool as WitnessCastable<F, F>>::cast_from_source(carry_in);
                let c = c.as_u64_reduced();

                debug_assert!(a < 1u64 << WIDTH);
                debug_assert!(b < 1u64 << WIDTH);
                debug_assert!(c < 1u64 << WIDTH);

                let lhs = a + b + carry_in as u64;
                let carry_out = c < lhs;

                debug_assert_eq!(a + b + carry_in as u64, c + ((carry_out as u64) << WIDTH));
                let carry_out = F::from_u64_unchecked(carry_out as u64);

                [carry_out]
            };

            let dependencies = Place::from_variables([a, b, carry_in, c]);

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables([output_variable]),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                a,
                b,
                carry_in,
                c,
                carry_out: output_variable,
            };

            gate.add_to_cs(cs);
        }

        output_variable
    }

    pub fn perform_subtraction_with_expected_borrow_out<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: Variable,
        b: Variable,
        borrow_in: Variable,
        _zero_var: Variable,
        borrow_out: Variable,
    ) -> Variable {
        debug_assert!(F::CAPACITY_BITS >= WIDTH + 1);
        debug_assert!(WIDTH == 8 || WIDTH == 16 || WIDTH == 32);
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variable = cs.alloc_variable_without_value();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 4]| {
                let [a, b, borrow_in, expected_borrow_out] = inputs;
                let a = a.as_u64_reduced();
                let b = b.as_u64_reduced();
                let borrow_in = <bool as WitnessCastable<F, F>>::cast_from_source(borrow_in);

                debug_assert!(a < 1u64 << WIDTH);
                debug_assert!(b < 1u64 << WIDTH);
                let expected_borrow_out = expected_borrow_out.as_u64_reduced();

                let result = (1u64 << WIDTH)
                    .wrapping_add(a)
                    .wrapping_sub(b)
                    .wrapping_sub(borrow_in as u64);

                let c = result & ((1u64 << WIDTH) - 1);
                let borrow_out = result < (1u64 << WIDTH);

                debug_assert_eq!(borrow_out as u64, expected_borrow_out);

                let c = F::from_u64_with_reduction(c);

                [c]
            };

            let dependencies = Place::from_variables([a, b, borrow_in, borrow_out]);

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables([output_variable]),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                a: output_variable,
                b,
                carry_in: borrow_in,
                c: a,
                carry_out: borrow_out,
            };

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
            <UIntXAddConstraintEvaluator as GateConstraintEvaluator<F>>::new_from_parameters(());

        test_evaluator::<F, _>(evaluator);
    }
}
