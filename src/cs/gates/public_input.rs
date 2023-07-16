use std::collections::VecDeque;

use crate::cs::cs_builder::{CsBuilder, CsBuilderImpl};

use super::{nop_gate::NopGateConstraintEvaluator, *};

// This gate doesn't produce any constraints, but places a marker into CS
// that on some row and column we declare a public input. We also allign all public inputs
// into single row, so we can more efficiently evaluate public input terms

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PublicInputGate {
    pub variable_to_set: Variable,
}

// Public input "gate" is just a NOP gate, but that marks itself in CS
// in addition to just copying variables where they belong

const PRINCIPAL_WIDTH: usize = 1;

#[derive(Derivative)]
#[derivative(Clone, Debug, Copy, PartialEq, Eq, Hash)]
pub struct PublicInputReservedPlacesToolMarker;

pub type PublicInputReservedPlacesBuffer = VecDeque<(usize, usize)>;

impl<F: SmallField> Gate<F> for PublicInputGate {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, _cs: &CS) -> bool {
        true
    }

    type Evaluator = NopGateConstraintEvaluator;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        NopGateConstraintEvaluator
    }
}

impl PublicInputGate {
    pub const fn new(var: Variable) -> Self {
        Self {
            variable_to_set: var,
        }
    }

    // If we allocate public input separately from the moment of knowing it's value
    // we can use this helper function to copy witness. NOTE: caller must ensure equality constraint by himself!
    pub fn assign_witness_value<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        from_variable: Variable,
        to_input: Variable,
    ) {
        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == false {
            return;
        }

        cs.set_values_with_dependencies(
            &[from_variable.into()],
            &[to_input.into()],
            |ins: [F; 1]| ins,
        )
    }

    pub fn reserve_public_input_location<F: SmallField, CS: ConstraintSystem<F>>(cs: &mut CS) {
        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            return;
        }

        match cs.get_gate_placement_strategy::<Self>() {
            GatePlacementStrategy::UseGeneralPurposeColumns => {
                let offered_row_idx = cs.next_available_row();
                let capacity_per_row = cs.get_params().num_columns_under_copy_permutation;
                let tooling: &mut NextGateCounterWithoutParams = cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, _>()
                    .expect("gate must be allowed");
                let (row, num_instances_already_placed) =
                    find_next_gate_without_params(tooling, capacity_per_row, offered_row_idx);
                drop(tooling);

                // now we can use methods of CS to inform it of low level operations
                let offset = num_instances_already_placed * PRINCIPAL_WIDTH;
                let tmp_self = Self::new(Variable::placeholder()); // we only use it to create SELF type
                if offered_row_idx == row {
                    cs.place_gate(&tmp_self, row);
                }
                // instead of putting the variable we note the space
                let tooling: &mut PublicInputReservedPlacesBuffer = cs.get_or_create_dynamic_tool_mut::<PublicInputReservedPlacesToolMarker, PublicInputReservedPlacesBuffer>();
                tooling.push_back((row, offset));
                cs.set_public(offset, row);
            }
            GatePlacementStrategy::UseSpecializedColumns {
                num_repetitions: _,
                share_constants: _,
            } => {
                unimplemented!()
            }
        }
    }

    pub fn use_reserved_public_input_location<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        var: Variable,
    ) {
        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            return;
        }

        let tooling: &mut PublicInputReservedPlacesBuffer = cs.get_dynamic_tool_mut::<PublicInputReservedPlacesToolMarker, PublicInputReservedPlacesBuffer>().expect("tool must be created upfront");
        let (row, offset) = tooling.pop_front().expect("must use reserved space");
        cs.place_variable(var, row, offset);
    }

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
        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            return;
        }

        match cs.get_gate_placement_strategy::<Self>() {
            GatePlacementStrategy::UseGeneralPurposeColumns => {
                let offered_row_idx = cs.next_available_row();
                let capacity_per_row = cs.get_params().num_columns_under_copy_permutation;
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
                cs.place_variable(self.variable_to_set, row, offset);
                cs.set_public(offset, row);
            }
            GatePlacementStrategy::UseSpecializedColumns {
                num_repetitions: _,
                share_constants: _,
            } => {
                unimplemented!()
            }
        }
    }
}
