use super::*;

// a + b + carry_in = c + 2^32 * carry_out,
// `carry_out` is boolean constrainted
// but `c` is NOT. We will use reduction gate to perform decomposition of `c`, and separate range checks

const UNIQUE_IDENTIFIER: &str = "a + b + carry = c + 2^32 * carry";
const PRINCIPAL_WIDTH: usize = 5;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct U32AddConstraintEvaluator;

impl<F: PrimeField> GateConstraintEvaluator<F> for U32AddConstraintEvaluator {
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
            num_constants: 0,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: 1,
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
        let a = trace_source.get_variable_value(0);
        let b = trace_source.get_variable_value(1);
        let carry_in = trace_source.get_variable_value(2);
        let c = trace_source.get_variable_value(3);
        let carry_out = trace_source.get_variable_value(4);

        // - constraint a + b + carry_in = c + 2^32 * carry_out

        let mut contribution = a;
        contribution.add_assign(&b, ctx);
        contribution.add_assign(&carry_in, ctx);
        contribution.sub_assign(&c, ctx);

        let mut tmp = P::constant(F::from_u64_with_reduction(1u64 << 32), ctx);
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
pub struct U32AddGate {
    pub a: Variable,
    pub b: Variable,
    pub carry_in: Variable,
    pub c: Variable,
    pub carry_out: Variable,
}

impl<F: SmallField> Gate<F> for U32AddGate {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 2
            && geometry.num_columns_under_copy_permutation >= PRINCIPAL_WIDTH
    }

    type Evaluator = U32AddConstraintEvaluator;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        U32AddConstraintEvaluator
    }
}

impl U32AddGate {
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
                let offset = num_instances_already_placed * PRINCIPAL_WIDTH;
                if offered_row_idx == row {
                    cs.place_gate(&self, row);
                }
                let all_variables = [self.a, self.b, self.carry_in, self.c, self.carry_out];
                assert_no_placeholder_variables(&all_variables);
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
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variables = cs.alloc_multiple_variables_without_values::<2>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 3]| {
                let [a, b, carry_in] = inputs;
                let a = a.as_u64_reduced();
                let b = b.as_u64_reduced();
                let carry_in = carry_in.as_u64_reduced();

                debug_assert!(a <= u32::MAX as u64);
                debug_assert!(b <= u32::MAX as u64);
                debug_assert!(carry_in == 0 || carry_in == 1);

                // upper bound is 2^32 - 1 + 2^32 - 1 + 1 = 2^33 - 1, so carry is always 1 bit

                let (c, of) = (a as u32).overflowing_add(b as u32);
                let (c, of2) = c.overflowing_add(carry_in as u32);

                let c = F::from_u64_with_reduction(c as u64);
                let carry_out = F::from_u64_with_reduction((of || of2) as u64);

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
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variables = cs.alloc_multiple_variables_without_values::<2>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 3]| {
                let [a, b, borrow_in] = inputs;
                let a = a.as_u64_reduced();
                let b = b.as_u64_reduced();
                let borrow_in = borrow_in.as_u64_reduced();

                debug_assert!(a <= u32::MAX as u64);
                debug_assert!(b <= u32::MAX as u64);
                debug_assert!(borrow_in == 0 || borrow_in == 1);

                let (c, uf) = (a as u32).overflowing_sub(b as u32);
                let (c, uf2) = c.overflowing_sub(borrow_in as u32);

                let c = F::from_u64_with_reduction(c as u64);
                let borrow_out = F::from_u64_with_reduction((uf || uf2) as u64);

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
}
