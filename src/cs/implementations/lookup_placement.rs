use super::*;
use crate::config::*;
use crate::cs::gates::find_next_gate_without_params;
use crate::cs::gates::lookup_marker::LookupFormalGate;
use crate::cs::gates::LookupTooling;
use crate::cs::implementations::reference_cs::*;
use crate::cs::toolboxes::gate_config::GateConfigurationHolder;
use crate::cs::toolboxes::static_toolbox::StaticToolboxHolder;
use crate::cs::traits::cs::ConstraintSystem;
use crate::dag::CircuitResolver;

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        CFG: CSConfig,
        GC: GateConfigurationHolder<F>,
        T: StaticToolboxHolder,
        CR: CircuitResolver<F, CFG::ResolverConfig>,
    > CSReferenceImplementation<F, P, CFG, GC, T, CR>
{
    pub(crate) fn enforce_lookup_over_general_purpose_columns<const N: usize>(
        &mut self,
        table_id: u32,
        keys_and_values: &[Variable; N],
        lookup_width: usize,
        id_in_constant: bool,
    ) {
        // Lookup is both witness computation and placement partially for a purpose to know
        // in what multiplicity poly we should put our sets of kvs

        let non_zero_table_id = table_id;

        let mut principal_width = lookup_width;
        if id_in_constant == false {
            principal_width += 1;
        }

        // we use zero-enumeration in vectors, but 1-enumeration in IDs
        let table_id = table_id - INITIAL_LOOKUP_TABLE_ID_VALUE;

        if <<Self as ConstraintSystem<F>>::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let table = std::sync::Arc::clone(&self.lookup_tables[table_id as usize]);
            let multiplicities_for_table_in_column =
                std::sync::Arc::clone(&self.lookup_multiplicities[table_id as usize]);

            let value_fn = move |inputs: [F; N]| {
                let row_idx = table.lookup_row(&inputs);
                let _ = multiplicities_for_table_in_column[row_idx as usize]
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst);

                []
            };

            self.set_values_with_dependencies(
                &Place::from_variables(*keys_and_values),
                &[],
                value_fn,
            );
        }

        if <<Self as ConstraintSystem<F>>::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            // do placement manually
            let (row, num_instances_already_placed) = {
                let offered_row_idx = self.next_available_row;
                let capacity_per_row =
                    self.parameters.num_columns_under_copy_permutation / principal_width;

                let tooling: &mut LookupTooling = self
                    .get_gates_config_mut()
                    .get_aux_data_mut::<LookupFormalGate, _>()
                    .expect("tooling must exist");

                let tooling_subid = if id_in_constant { table_id as usize } else { 0 };

                let (row, num_instances_already_placed) = find_next_gate_without_params(
                    &mut tooling.0[tooling_subid],
                    capacity_per_row,
                    offered_row_idx,
                );

                (row, num_instances_already_placed)
            };

            // we also manually increment row counter, kind of we place a gate here
            let formal_gate_idx = self.lookup_marker_gate_idx.expect("must exist");
            if row == self.next_available_row {
                // use new row
                self.next_available_row += 1;
                debug_assert!(self.gates_application_sets.len() == row);
                debug_assert!(self.constants_requested_per_row.len() <= row);
                self.gates_application_sets.push(formal_gate_idx as usize);
            } else {
                // we do not need to do anything, we only place variables
            }

            debug_assert!(row < self.next_available_row);
            debug_assert!(self.next_available_row <= self.max_trace_len);

            let mut offset = num_instances_already_placed * principal_width;
            self.place_multiple_variables_into_row(keys_and_values, row, offset);
            offset += N;
            if id_in_constant == false {
                let table_id_variable = self.table_ids_as_variables[table_id as usize];
                self.place_variable(table_id_variable, row, offset);
            } else {
                let table_id_constant = F::from_u64_unchecked(non_zero_table_id as u64);
                self.place_constants(&[table_id_constant], row, 0);
            }
        }
    }

    pub(crate) fn enforce_lookup_over_specialized_columns<const N: usize>(
        &mut self,
        table_id: u32,
        keys_and_values: &[Variable; N],
        num_repetitions: usize,
        id_in_constant: bool,
    ) {
        // Lookup is both witness computation and placement partially for a purpose to know
        // in what multiplicity poly we should put our sets of kvs

        let non_zero_table_id = table_id;

        // we use zero-enumeration in vectors, but 1-enumeration in IDs
        let table_id = table_id - INITIAL_LOOKUP_TABLE_ID_VALUE;

        if <<Self as ConstraintSystem<F>>::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let table = std::sync::Arc::clone(&self.lookup_tables[table_id as usize]);
            let multiplicities_for_table_in_column =
                std::sync::Arc::clone(&self.lookup_multiplicities[table_id as usize]);

            let value_fn = move |inputs: [F; N]| {
                let row_idx = table.lookup_row(&inputs);
                let _previous_counter = multiplicities_for_table_in_column[row_idx as usize]
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst);

                []
            };

            self.set_values_with_dependencies(
                &Place::from_variables(*keys_and_values),
                &[],
                value_fn,
            );
        }

        if <<Self as ConstraintSystem<F>>::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            // do placement manually
            let (row, num_instances_already_placed) = {
                let capacity_per_row = num_repetitions;

                let tooling: &mut LookupTooling = self
                    .get_gates_config_mut()
                    .get_aux_data_mut::<LookupFormalGate, _>()
                    .expect("tooling must exist");

                let tooling_subid = if id_in_constant { table_id as usize } else { 0 };

                use crate::cs::gates::find_next_lookup_gate_specialized;

                let (row, num_instances_already_placed) =
                    find_next_lookup_gate_specialized(tooling, tooling_subid, capacity_per_row);

                debug_assert!(num_instances_already_placed < num_repetitions);
                debug_assert!(num_instances_already_placed < self.num_sublookup_arguments());

                (row, num_instances_already_placed)
            };

            // may be unnecessary
            // ---------------------
            let (num_variables_to_use, num_constants_to_use, share_table_id) = self
                .gates_configuration
                .get_params::<LookupFormalGate>()
                .expect("gate must be allowed");
            let gate = LookupFormalGate {
                num_variables_to_use,
                num_constants_to_use,
                share_table_id,
            };
            self.place_gate_specialized(&gate, num_instances_already_placed, row);
            // ---------------------
            let mut offset = 0;
            self.place_multiple_variables_into_row_specialized::<LookupFormalGate, N>(
                keys_and_values,
                num_instances_already_placed,
                row,
                0,
            );
            offset += N;
            if id_in_constant == false {
                let table_id_variable = self.table_ids_as_variables[table_id as usize];
                self.place_variable_specialized::<LookupFormalGate>(
                    table_id_variable,
                    num_instances_already_placed,
                    row,
                    offset,
                );
            } else {
                let table_id_constant = F::from_u64_unchecked(non_zero_table_id as u64);
                self.place_constants_specialized::<LookupFormalGate, 1>(
                    &[table_id_constant],
                    num_instances_already_placed,
                    row,
                    0,
                );
            }
        }
    }
}
