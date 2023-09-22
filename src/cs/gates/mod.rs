use super::*;
use crate::config::*;
use crate::cs::toolboxes::gate_config::GateConfigurationHolder;
use crate::cs::toolboxes::static_toolbox::StaticToolboxHolder;
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::cs::DstBuffer;
use crate::cs::traits::destination_view::EvaluationDestination;
use crate::cs::traits::evaluator::*;
use crate::cs::traits::gate::Gate;
use crate::cs::traits::gate::GatePlacementStrategy;
use crate::field::PrimeField;
use std::borrow::Cow;

pub mod testing_tools;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ConstantToVariableMappingToolMarker;

pub type ConstantToVariableMappingTool<F> = HashMap<F, Variable>;

trait GetConstantFromCS<F: SmallField> {
    fn get_variable_for_constant(&self, constant: &F) -> Option<Variable>;
}

// default extension implementation
impl<F: SmallField, CS: ConstraintSystem<F>> GetConstantFromCS<F> for CS {
    #[inline]
    fn get_variable_for_constant(&self, constant: &F) -> Option<Variable> {
        // get mapping tool
        let tooling: &ConstantToVariableMappingTool<F> = self
            .get_static_toolbox()
            .get_tool::<ConstantToVariableMappingToolMarker, ConstantToVariableMappingTool<F>>(
        )?;
        tooling.get(constant).copied()
    }
}

trait BooleanAllocatableCS<F: SmallField> {
    fn alloc_boolean(&mut self, witness: bool) -> Variable;
}

// default extension implementation
impl<F: SmallField, CS: ConstraintSystem<F>> BooleanAllocatableCS<F> for CS {
    fn alloc_boolean(&mut self, witness: bool) -> Variable {
        if self.gate_is_allowed::<BoundedBooleanConstraintGate>() {
            BoundedBooleanConstraintGate::alloc_boolean_from_witness(self, witness)
        } else if self.gate_is_allowed::<BooleanConstraintGate>() {
            BooleanConstraintGate::alloc_boolean_from_witness(self, witness)
        } else {
            unimplemented!()
        }
    }
}

// Trait to allocate variables that are literal constants
pub trait ConstantAllocatableCS<F: SmallField> {
    fn allocate_constant(&mut self, constant: F) -> Variable;
}

// default extension implementation
impl<F: SmallField, CS: ConstraintSystem<F>> ConstantAllocatableCS<F> for CS {
    fn allocate_constant(&mut self, constant: F) -> Variable {
        if self.gate_is_allowed::<ConstantsAllocatorGate<F>>() {
            ConstantsAllocatorGate::allocate_constant(self, constant)
        } else if self.gate_is_allowed::<BoundedConstantsAllocatorGate<F>>() {
            BoundedConstantsAllocatorGate::allocate_constant(self, constant)
        } else {
            unimplemented!()
        }
    }
}

pub const IS_ZERO_LOOKUP_TOOLING: &str = "Is zero lookup tooling";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IsZeroToolingMarker;

pub type IsZeroLookupTooling = std::collections::HashMap<Variable, Variable>;

pub trait ZeroCheckMemoizableCS<F: SmallField> {
    fn check_is_zero_memoization(&self, var: Variable) -> Option<Variable>;
    fn set_is_zero_memoization(&mut self, var: Variable, is_zero: Variable);
}

impl<F: SmallField, CS: ConstraintSystem<F>> ZeroCheckMemoizableCS<F> for CS {
    #[inline]
    fn check_is_zero_memoization(&self, var: Variable) -> Option<Variable> {
        if let Some(static_tool) = self
            .get_static_toolbox()
            .get_tool::<IsZeroToolingMarker, IsZeroLookupTooling>()
        {
            return static_tool.get(&var).copied();
        } else if let Some(dynamic_tool) =
            self.get_dynamic_tool::<IsZeroToolingMarker, IsZeroLookupTooling>()
        {
            return dynamic_tool.get(&var).copied();
        } else {
            None
        }
    }

    #[inline]
    fn set_is_zero_memoization(&mut self, var: Variable, is_zero: Variable) {
        if let Some(static_tool) = self
            .get_static_toolbox_mut()
            .get_tool_mut::<IsZeroToolingMarker, IsZeroLookupTooling>()
        {
            let _existing = static_tool.insert(var, is_zero);
        } else {
            let dynamic_tool =
                self.get_or_create_dynamic_tool_mut::<IsZeroToolingMarker, IsZeroLookupTooling>();
            let _existing = dynamic_tool.insert(var, is_zero);
        }
    }
}

pub mod boolean_allocator;
pub mod bounded_boolean_allocator;
pub mod bounded_constant_allocator;
pub mod conditional_swap;
pub mod constant_allocator;
pub mod dot_product_gate;
pub mod fma_gate_in_extension_without_constant;
pub mod fma_gate_without_constant;
pub mod lookup_marker;
pub mod nop_gate;
pub mod parallel_selection;
pub mod public_input;
// pub mod poseidon;
pub mod matrix_multiplication_gate;
pub mod poseidon2;
pub mod quadratic_combination;
pub mod reduction_by_powers_gate;
pub mod reduction_gate;
pub mod selection_gate;
pub mod simple_non_linearity_with_constant;
pub mod u32_add;
pub mod u32_fma;
pub mod u32_sub;
pub mod u32_tri_add_carry_as_chunk;
pub mod uintx_add;
pub mod zero_check;

pub mod bounded_wrapper;

pub use self::boolean_allocator::*;
pub use self::bounded_boolean_allocator::*;
pub use self::bounded_constant_allocator::*;
pub use self::conditional_swap::*;
pub use self::constant_allocator::*;
pub use self::dot_product_gate::*;
pub use self::fma_gate_in_extension_without_constant::*;
pub use self::fma_gate_without_constant::*;
pub use self::nop_gate::*;
pub use self::parallel_selection::*;
// pub use self::poseidon::*;
pub use self::matrix_multiplication_gate::*;
pub use self::poseidon2::*;
pub use self::public_input::*;
pub use self::quadratic_combination::*;
pub use self::reduction_by_powers_gate::*;
pub use self::reduction_gate::*;
pub use self::selection_gate::*;
pub use self::simple_non_linearity_with_constant::*;
pub use self::u32_add::*;
pub use self::u32_fma::*;
pub use self::u32_sub::*;
pub use self::u32_tri_add_carry_as_chunk::*;
pub use self::uintx_add::*;
pub use self::zero_check::*;

pub type NextGateCounterWithoutParams = Option<(usize, usize)>;

#[inline]
pub(crate) fn find_next_gate<K: std::hash::Hash + std::cmp::Eq>(
    tooling: &mut HashMap<K, (usize, usize)>,
    params: K,
    capacity_per_row: usize,
    offered_row_idx: usize,
) -> (usize, usize) {
    if let Some((existing_row_idx, num_instances)) = tooling.remove(&params) {
        if num_instances + 1 < capacity_per_row {
            tooling.insert(params, (existing_row_idx, num_instances + 1));
        } else {
            // we removed to indicate that row is taken in full
        }

        (existing_row_idx, num_instances)
    } else {
        // we need a new one
        tooling.insert(params, (offered_row_idx, 1));

        (offered_row_idx, 0)
    }
}

#[inline]
pub(crate) fn find_next_gate_specialized<K: std::hash::Hash + std::cmp::Eq>(
    tooling: &mut HashMap<K, (usize, usize)>,
    next_available_row: &mut usize,
    params: K,
    capacity_per_row: usize,
) -> (usize, usize) {
    if let Some((existing_row_idx, num_instances)) = tooling.remove(&params) {
        debug_assert!(num_instances < capacity_per_row);
        if num_instances + 1 < capacity_per_row {
            tooling.insert(params, (existing_row_idx, num_instances + 1));
        } else {
            // we removed to indicate that row is taken in full
        }

        (existing_row_idx, num_instances)
    } else {
        // we need a new one
        let row_to_use = *next_available_row;
        if capacity_per_row > 1 {
            tooling.insert(params, (row_to_use, 1));
        }
        *next_available_row += 1;

        (row_to_use, 0)
    }
}

#[inline]
pub(crate) fn find_next_gate_without_params(
    tooling: &mut Option<(usize, usize)>,
    capacity_per_row: usize,
    offered_row_idx: usize,
) -> (usize, usize) {
    debug_assert!(capacity_per_row >= 1);

    if capacity_per_row == 1 {
        return (offered_row_idx, 0);
    }

    if let Some((existing_row_idx, num_instances_already_placed)) = tooling.take() {
        if num_instances_already_placed == capacity_per_row {
            // we need a new one
            *tooling = Some((offered_row_idx, 1));

            (offered_row_idx, 0)
        } else {
            *tooling = Some((existing_row_idx, num_instances_already_placed + 1));

            (existing_row_idx, num_instances_already_placed)
        }
    } else {
        // we need a new one
        *tooling = Some((offered_row_idx, 1));

        (offered_row_idx, 0)
    }
}

#[inline]
pub(crate) fn find_next_specialized_gate_without_params(
    tooling: &mut Option<(usize, usize)>,
    capacity_per_row: usize,
) -> (usize, usize) {
    debug_assert!(capacity_per_row >= 1);

    if let Some((existing_row_idx, num_instances_already_placed)) = tooling.take() {
        if num_instances_already_placed == capacity_per_row {
            // we need a new one
            *tooling = Some((existing_row_idx + 1, 1));

            (existing_row_idx + 1, 0)
        } else {
            *tooling = Some((existing_row_idx, num_instances_already_placed + 1));

            (existing_row_idx, num_instances_already_placed)
        }
    } else {
        // first invocation
        *tooling = Some((0, 1));

        (0, 0)
    }
}

#[inline]
pub(crate) fn find_next_gate_without_params_readonly(
    tooling: &Option<(usize, usize)>,
    capacity_per_row: usize,
    offered_row_idx: usize,
) -> (usize, usize) {
    debug_assert!(capacity_per_row >= 1);

    if capacity_per_row == 1 {
        return (offered_row_idx, 0);
    }

    if let Some((existing_row_idx, num_instances_already_placed)) = tooling.as_ref() {
        if *num_instances_already_placed == capacity_per_row {
            (offered_row_idx, 0)
        } else {
            (*existing_row_idx, *num_instances_already_placed)
        }
    } else {
        (offered_row_idx, 0)
    }
}

pub type LookupTooling = (Vec<Option<(usize, usize)>>, usize);

#[inline]
pub(crate) fn find_next_lookup_gate_specialized(
    tooling: &mut (Vec<Option<(usize, usize)>>, usize),
    tooling_sub_id: usize,
    capacity_per_row: usize,
) -> (usize, usize) {
    // we store it as:
    // in Vec<_>: we have a number of now many instances of the particular table (with ID)
    // we placed in some row,
    // in 2nd argument: we have next available row in general for ANY table
    let (per_table_placements, next_available_row) = (&mut tooling.0, &mut tooling.1);
    if let Some((existing_row_idx, num_instances)) = per_table_placements[tooling_sub_id].as_mut() {
        if *num_instances < capacity_per_row {
            let offset = *num_instances;
            *num_instances += 1;

            (*existing_row_idx, offset)
        } else {
            let next_row = *next_available_row;
            *next_available_row += 1;
            *existing_row_idx = next_row;
            *num_instances = 1;

            (next_row, 0)
        }
    } else {
        // we need a new one
        let next_row = *next_available_row;
        *next_available_row += 1;
        per_table_placements[tooling_sub_id] = Some((next_row, 1));

        (next_row, 0)
    }
}

#[inline(always)]
pub(crate) fn find_next_lookup_gate_readonly(
    tooling: &[Option<(usize, usize)>],
    table_id: u32,
    _capacity_per_row: usize,
    offered_row_idx: usize,
) -> (usize, usize) {
    if let Some((existing_row_idx, num_instances)) = tooling[table_id as usize].as_ref() {
        (*existing_row_idx, *num_instances)
    } else {
        // we need a new one
        (offered_row_idx, 0)
    }
}

#[inline(always)]
#[track_caller]
pub fn assert_not_placeholder(place: Place) {
    debug_assert!(place.is_placeholder() == false)
}

#[inline(always)]
#[track_caller]
pub fn assert_no_placeholders(places: &[Place]) {
    debug_assert!({
        let mut ok = true;
        for el in places.iter() {
            if el.is_placeholder() {
                ok = false;
            }
        }

        ok
    })
}

#[inline(always)]
#[track_caller]
pub fn assert_not_placeholder_variable(place: Variable) {
    debug_assert!(place.is_placeholder() == false)
}

#[inline(always)]
#[track_caller]
pub fn assert_no_placeholder_variables(places: &[Variable]) {
    debug_assert!({
        let mut ok = true;
        for el in places.iter() {
            if el.is_placeholder() {
                ok = false;
            }
        }

        ok
    })
}
