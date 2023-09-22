use super::*;

// Allocate constants by a batch of constraints like (a - constant) == 0

// In this file the allocator uses an unbounded number of constant columns for its work

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BoundedConstantsAllocatorGate<F: PrimeField> {
    pub variable_with_constant_value: Variable,
    pub constant_to_add: F,
    max_constants_to_add_per_row: usize,
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BoundedConstantAllocatorConstraintEvaluator {
    pub max_constants_to_add_per_row: usize,
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BoundedConstantAllocatorConstraintEvaluatorParams {
    pub max_constants_to_add_per_row: usize,
}

impl<F: PrimeField> GateConstraintEvaluator<F> for BoundedConstantAllocatorConstraintEvaluator {
    type UniqueParameterizationParams = BoundedConstantAllocatorConstraintEvaluatorParams;

    #[inline(always)]
    fn new_from_parameters(params: Self::UniqueParameterizationParams) -> Self {
        Self {
            max_constants_to_add_per_row: params.max_constants_to_add_per_row,
        }
    }

    #[inline(always)]
    fn unique_params(&self) -> Self::UniqueParameterizationParams {
        BoundedConstantAllocatorConstraintEvaluatorParams {
            max_constants_to_add_per_row: self.max_constants_to_add_per_row,
        }
    }

    #[inline]
    fn type_name() -> std::borrow::Cow<'static, str> {
        Cow::Borrowed(std::any::type_name::<Self>())
    }

    #[inline]
    fn instance_width(&self) -> GatePrincipalInstanceWidth {
        GatePrincipalInstanceWidth {
            num_variables: 1,
            num_witnesses: 0,
            num_constants: 1,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: 1,
            num_quotient_terms: 1,
        }
    }

    #[inline]
    fn placement_type(&self) -> GatePlacementType {
        GatePlacementType::MultipleOnRow {
            per_chunk_offset: PerChunkOffset {
                variables_offset: PRINCIPAL_WIDTH,
                witnesses_offset: 0,
                constants_offset: PRINCIPAL_WIDTH,
            },
        }
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, geometry: &CSGeometry) -> usize {
        debug_assert!(
            geometry.num_columns_under_copy_permutation >= self.max_constants_to_add_per_row
        );
        debug_assert!(geometry.num_constant_columns >= self.max_constants_to_add_per_row);

        self.max_constants_to_add_per_row
    }

    #[inline]
    fn num_required_constants_in_geometry(&self, geometry: &CSGeometry) -> usize {
        debug_assert!(geometry.num_constant_columns >= self.max_constants_to_add_per_row);

        self.max_constants_to_add_per_row
    }

    type GlobalConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = ();

    #[inline(always)]
    fn create_global_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>>(
        &self,
        _ctx: &mut P::Context,
    ) -> Self::GlobalConstants<P> {
    }

    // there are no constants that would be shared between instances
    // on the same row, so `evaluate_once` loads manually
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
        let constant = trace_source.get_constant_value(0);

        let mut contribution = a;
        contribution.sub_assign(&constant, ctx);

        destination.push_evaluation_result(contribution, ctx);
    }
}

const PRINCIPAL_WIDTH: usize = 1;

impl<F: SmallField> Gate<F> for BoundedConstantsAllocatorGate<F> {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 1
            && geometry.num_columns_under_copy_permutation >= 1
            && geometry.num_constant_columns > 0
            && geometry.num_constant_columns >= self.max_constants_to_add_per_row
    }

    type Evaluator = BoundedConstantAllocatorConstraintEvaluator;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        BoundedConstantAllocatorConstraintEvaluator {
            max_constants_to_add_per_row: self.max_constants_to_add_per_row,
        }
    }
}

impl<F: SmallField> BoundedConstantsAllocatorGate<F> {
    pub fn new_to_enforce<CS: ConstraintSystem<F>>(cs: &CS, var: Variable, constant: F) -> Self {
        let params = cs.get_gate_params::<Self>();

        Self {
            variable_with_constant_value: var,
            constant_to_add: constant,
            max_constants_to_add_per_row: params.max_constants_to_add_per_row,
        }
    }

    pub fn add_to_cs<CS: ConstraintSystem<F>>(self, cs: &mut CS) {
        debug_assert!(cs.gate_is_allowed::<Self>());

        todo!();

        // // place into lookup
        // let tooling: &mut ConstantToVariableMappingTool<F> =
        //     cs.get_or_create_dynamic_tool_mut(CONSTANT_TO_VARIABLE_TOOLING);
        // tooling.insert(self.constant_to_add, self.variable_with_constant_value);
        // drop(tooling);

        // // the rest is not necessary if we do not keep setup
        // if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
        //     return;
        // }

        // // get location to place
        // let offered_row_idx = cs.next_available_row();
        // let num_constant_columns_per_row = cs.get_params().num_constant_columns;
        // let constant_capacity_per_row = num_constant_columns_per_row / PRINCIPAL_WIDTH;

        // let num_variables_per_row = cs.get_params().num_columns_under_copy_permutation;
        // let variables_capacity_per_row = num_variables_per_row / PRINCIPAL_WIDTH;

        // let capacity_per_row = std::cmp::min(constant_capacity_per_row, variables_capacity_per_row);
        // let capacity_per_row = std::cmp::min(self.max_constants_to_add_per_row, capacity_per_row);

        // let tooling: &mut GateTooling = cs.get_or_create_dynamic_tool_mut(UNIQUE_IDENTIFIER);

        // let (row, num_instances_already_placed) =
        //     find_next_gate_without_params(tooling, capacity_per_row, offered_row_idx);

        // drop(tooling);

        // // now we can use methods of CS to inform it of low level operations
        // let offset = num_instances_already_placed * PRINCIPAL_WIDTH;
        // if offered_row_idx == row {
        //     cs.place_gate(&self, row);
        // }
        // cs.place_constants([self.constant_to_add], row, offset);
        // assert_not_placeholder_variable(self.variable_with_constant_value);
        // cs.place_variable(self.variable_with_constant_value, row, offset);
    }

    pub fn allocate_constant<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        _constant_to_add: F,
    ) -> Variable {
        debug_assert!(cs.gate_is_allowed::<Self>());

        todo!();

        // // check that we are unique
        // if let Some(tooling) = cs.get_tool(CONSTANT_TO_VARIABLE_TOOLING) {
        //     let tooling: &ConstantToVariableMappingTool<F> = tooling;
        //     if let Some(variable) = tooling.get(&constant_to_add).copied() {
        //         return variable;
        //     }
        // } else {
        //     // nothing because such constant is unique
        // }

        // let output_variable = cs.alloc_variable_without_value();

        // if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
        //     let value_fn = move |_inputs: [F; 0]| [constant_to_add];

        //     let dependencies = [];

        //     cs.set_values_with_dependencies(
        //         &dependencies,
        //         &Place::from_variables([output_variable]),
        //         value_fn,
        //     );
        // }

        // if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == true {
        //     let gate = Self::new_to_enforce(&*cs, output_variable, constant_to_add);
        //     gate.add_to_cs(cs);
        // }

        // output_variable
    }
}
