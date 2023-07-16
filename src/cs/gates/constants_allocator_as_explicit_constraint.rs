use std::collections::HashSet;

use super::*;

// The gate below is a way to allocate a specific set of constants.
// Even though it can be achieved by manual crafting of quotient terms,
// we would like to make our lives easier. This gate ALWAYS adds 0, 1 and -1 as
// constants, and can add an arbitrary set. Largely powers of two would be a good case,
// even though they can be produced by just having FMA gate (that also shares coeffients) like 2 * 1 * 1 -> 2,
// 2 * 2 * 1 -> 4, etc

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConstantsAllocationAsConstraintGate<F: SmallField> {
    pub non_trivial_constants_to_add: Vec<F>,
    pub unique_identifier: String, // for different sets of constants this gate is different ID
}

impl<F: SmallField> ConstantsAllocationAsConstraintGate<F> {
    /// Caller should ideally provide unique set without 0, 1, and -1
    pub fn new(constants_set: Vec<F>) -> Self {
        use std::fmt::Write;
        let mut writer = String::new();
        write!(&mut writer, "{}: ", Self::UNIQUE_IDENTIFIER_BASE).unwrap();
        if constants_set.is_empty() {
            write!(&mut writer, "empty set").unwrap();
        } else {
            let num_constants = constants_set.len();
            for el in constants_set[..(num_constants - 1)].iter() {
                write!(&mut writer, "{}, ", el).unwrap();
            }
            write!(&mut writer, "{}", constants_set.last().unwrap()).unwrap();
        }

        let identifier = writer;
        Self {
            non_trivial_constants_to_add: constants_set,
            unique_identifier: identifier,
        }
    }
}

impl<F: SmallField, P: field::traits::field_like::PrimeFieldLike> GateInternal<F, P>
    for ConstantsAllocationAsConstraintGate<F>
{
    fn evaluate_at_set(
        &self,
        view: TraceView,
        destination: DestinationViewMut,
        geometry: &CSGeometry,
        worker: &Worker,
    ) {
        todo!()
    }
    fn evaluate_once(
        &self,
        row_values: RowView<F, P>,
        geometry: &CSGeometry,
        ctx: &mut P::Context,
    ) -> P {
        todo!()
    }
    #[inline]
    fn box_clone(&self) -> Box<dyn GateInternal<F, P>> {
        Box::new(self.clone())
    }
    #[inline(always)]
    fn max_constraint_degree(&self) -> usize {
        1
    }

    #[inline]
    fn unique_identifier(&self) -> &str {
        &self.unique_identifier
    }
}

impl<F: SmallField> ConstantsAllocationAsConstraintGate<F> {
    const UNIQUE_IDENTIFIER_BASE: &'static str = "Constant allocator as batch";

    // this gate need two tools:

    // one to ensure that user doesn't allocate two gates of the same constans set
    // because even though they are the same Rust type, but they are not the same
    // logical entity
    const UNIQUENESS_TESTING_TOOLING_IDENTIFIER: &'static str =
        "Constant allocator  as batch uniqueness tooling";
}

type UniquenessTool = HashSet<String>;

impl<F: SmallField, P: field::traits::field_like::PrimeFieldLike> Gate<F, P>
    for ConstantsAllocationAsConstraintGate<F>
{
    #[inline(always)]
    fn can_apply_many_on_row() -> bool {
        false
    }

    #[inline(always)]
    fn check_compatible_with_cs<
        CS: ConstraintSystem<F, EVALUATE_WITNESS, P>,
        const EVALUATE_WITNESS: bool,
    >(
        &self,
        cs: &CS,
    ) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 1
            && geometry.num_columns_under_copy_permutation
                >= 3 + self.non_trivial_constants_to_add.len()
    }

    type GateNewVariables = ();
    type GateValueEvaluationResult = ();
    fn add<CS: ConstraintSystem<F, EVALUATE_WITNESS, P>, const EVALUATE_WITNESS: bool>(
        self,
        cs: &mut CS,
    ) -> (
        Self::GateNewVariables,
        impl Future<Output = Self::GateValueEvaluationResult> + Send + 'static,
    ) {
        let offered_row_idx = cs.next_available_row();

        // check that we are unique
        let tooling: &mut UniquenessTool =
            cs.get_or_create_dynamic_tool_mut(Self::UNIQUENESS_TESTING_TOOLING_IDENTIFIER);
        let is_unique = tooling.insert(self.unique_identifier.clone());
        debug_assert!(is_unique);
        drop(tooling);

        let mut allocated_variables =
            Vec::with_capacity(3 + self.non_trivial_constants_to_add.len());

        for (column, set_element) in std::iter::once(F::ZERO)
            .chain(std::iter::once(F::ONE))
            .chain(std::iter::once(F::MINUS_ONE))
            .chain(self.non_trivial_constants_to_add.iter().copied())
            .enumerate()
        {
            let future = std::future::ready(set_element);
            let variable = cs.alloc(future);
            cs.place_variable(variable, offered_row_idx, column);
            allocated_variables.push((set_element, variable));
        }

        cs.place_gate(self, offered_row_idx);

        // get mapping tool
        let tooling: &mut ConstantToVariableMappingTool<F> =
            cs.get_or_create_dynamic_tool_mut(CONSTANT_TO_VARIABLE_TOOLING);
        for (constant, variable) in allocated_variables.into_iter() {
            if tooling.contains_key(&constant) {
                continue;
            } else {
                tooling.insert(constant, variable);
            }
        }

        drop(tooling);

        ((), std::future::ready(()))
    }

    type GateWitness = ();
}
