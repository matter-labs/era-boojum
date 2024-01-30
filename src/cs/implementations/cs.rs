use super::lookup_table::{LookupTableWrapper, Wrappable};

use super::*;
use crate::config::*;
use crate::cs::gates::{
    assert_no_placeholder_variables, assert_not_placeholder_variable, ConstantAllocatableCS,
};
use crate::cs::gates::{assert_no_placeholders, lookup_marker::*, LookupTooling};

use crate::cs::toolboxes::static_toolbox::StaticToolboxHolder;
use crate::cs::traits::gate::GatePlacementStrategy;
use crate::utils::PipeOp;
use std::any::TypeId;
use std::sync::atomic::AtomicU32;

use crate::dag::CircuitResolver;

use crate::cs::toolboxes::gate_config::GateConfigurationHolder;
use crate::cs::traits::cs::{ConstraintSystem, DstBuffer};
use crate::cs::traits::evaluator::*;
use crate::cs::traits::gate::Gate;

use crate::dag::CSWitnessValues;

use crate::cs::implementations::reference_cs::*;

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        CFG: CSConfig,
        GC: GateConfigurationHolder<F>,
        T: StaticToolboxHolder,
        CR: CircuitResolver<F, CFG::ResolverConfig>,
    > ConstraintSystem<F> for CSReferenceImplementation<F, P, CFG, GC, T, CR>
{
    type Config = CFG;
    type WitnessSource = CR;
    type GatesConfig = GC;
    type StaticToolbox = T;

    #[inline(always)]
    fn get_gates_config(&self) -> &Self::GatesConfig {
        &self.gates_configuration
    }

    #[inline(always)]
    fn get_gates_config_mut(&mut self) -> &mut Self::GatesConfig {
        &mut self.gates_configuration
    }

    #[inline(always)]
    fn get_static_toolbox(&self) -> &Self::StaticToolbox {
        &self.static_toolbox
    }

    #[inline(always)]
    fn get_static_toolbox_mut(&mut self) -> &mut Self::StaticToolbox {
        &mut self.static_toolbox
    }

    // for 1 variable
    #[inline]
    fn alloc_variable_without_value(&mut self) -> Variable {
        let var = Variable::from_variable_index(self.next_available_place_idx);
        self.next_available_place_idx += 1;

        var
    }
    #[inline]
    fn alloc_multiple_variables_without_values<const N: usize>(&mut self) -> [Variable; N] {
        debug_assert!(N < u32::MAX as usize);
        let current_idx = self.next_available_place_idx;
        self.next_available_place_idx += N as u64;

        let result: [Variable; N] =
            std::array::from_fn(|i| Variable::from_variable_index(current_idx + (i as u64)));

        result
    }
    #[inline]
    fn alloc_witness_without_value(&mut self) -> Witness {
        let wit = Witness::from_witness_index(self.next_available_place_idx);
        self.next_available_place_idx += 1;

        wit
    }
    #[inline]
    fn alloc_multiple_witnesses_without_values<const N: usize>(&mut self) -> [Witness; N] {
        let current_idx = self.next_available_place_idx;
        self.next_available_place_idx += N as u64;

        let result: [Witness; N] =
            std::array::from_fn(|i| Witness::from_witness_index(current_idx + (i as u64)));

        result
    }

    #[inline]
    fn set_values<const N: usize>(&mut self, places: &[Place; N], values: [F; N]) {
        if CFG::WitnessConfig::EVALUATE_WITNESS == true {
            // places.iter().zip(values).for_each(|(a, b)| {
            //     self.storage_debug_trace_file.get_mut().unwrap().write(format!("set {:?} <- {}\n", a, b.as_raw_u64()).as_bytes()).unwrap();
            // });

            places.iter().zip(values).for_each(|(a, b)| {
                self.variables_storage.get_mut().unwrap().set_value(*a, b);
            });
        }
    }

    #[inline]
    fn set_values_with_dependencies<
        const INS: usize,
        const OUTS: usize,
        FN: FnOnce([F; INS]) -> [F; OUTS] + 'static + Send + Sync,
    >(
        &mut self,
        dependencies: &[Place; INS],
        outputs: &[Place; OUTS],
        value_fn: FN,
    ) {
        if CFG::WitnessConfig::EVALUATE_WITNESS == true {
            let value_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
                std::array::from_fn::<_, INS, _>(|i| ins[i])
                    .to(value_fn)
                    .into_iter()
                    .for_each(|x| outs.push(x));
            };

            self.set_values_with_dependencies_vararg(dependencies, outputs, value_fn);
        }
    }

    #[track_caller]
    #[inline]
    fn set_values_with_dependencies_vararg<
        FN: FnOnce(&[F], &mut DstBuffer<'_, '_, F>) + 'static + Send + Sync,
    >(
        &mut self,
        dependencies: &[Place],
        outputs: &[Place],
        value_fn: FN,
    ) {
        if CFG::WitnessConfig::EVALUATE_WITNESS == true {
            self.variables_storage.get_mut().unwrap().add_resolution(
                dependencies,
                outputs,
                value_fn,
            );
        }
    }

    // Getters
    #[inline]
    fn get_value(&self, place: Place) -> CSWitnessValues<F, 1, Self::WitnessSource> {
        debug_assert!(place.is_placeholder() == false);
        if CFG::WitnessConfig::EVALUATE_WITNESS == false {
            return CSWitnessValues::Placeholder;
        }

        use crate::dag::Awaiter;

        let r = {
            let storage = self.variables_storage.read().unwrap();

            // happy path
            if let Some(value) = storage.try_get_value(place) {
                value
            } else {
                drop(storage);
                let mut storage = self.variables_storage.write().unwrap();

                storage.get_awaiter([place]).wait();

                storage.get_value_unchecked(place)
            }
        };

        // self.storage_debug_trace_file.write().unwrap().write(
        //     format!(
        //         "get {:?} -> {}\n",
        //         place,
        //         r.as_raw_u64())
        //     .as_bytes()).unwrap();

        CSWitnessValues::Ready([r])
    }

    #[inline]
    fn get_value_for_multiple<const N: usize>(
        &self,
        for_places: [Place; N],
    ) -> CSWitnessValues<F, N, Self::WitnessSource> {
        assert_no_placeholders(&for_places);

        if CFG::WitnessConfig::EVALUATE_WITNESS == false {
            return CSWitnessValues::Placeholder;
        }

        use crate::dag::Awaiter;

        let r = {
            let mut storage = self.variables_storage.write().unwrap();

            storage.get_awaiter(for_places).wait();

            let arr = std::array::from_fn(|x| storage.get_value_unchecked(for_places[x]));

            arr
        };

        // self.storage_debug_trace_file.write().unwrap().write(
        //     format!(
        //         "get {:?} -> {:?}\n",
        //         for_places,
        //         r.map(|x| x.as_raw_u64()))
        //     .as_bytes()).unwrap();

        CSWitnessValues::Ready(r)
    }

    // Public input
    #[inline]
    fn set_public(&mut self, column: usize, row: usize) {
        log!("Adding row {} column {} as public input", row, column);
        debug_assert!(self.public_inputs.contains(&(column, row)) == false);
        self.public_inputs.push((column, row));
    }

    // Gate tooling
    #[inline]
    fn add_dynamic_tool<M: 'static + Send + Sync, TT: GateTool>(&mut self, tool: TT) {
        let marker_id = std::any::TypeId::of::<M>();
        let type_id = std::any::TypeId::of::<TT>();
        let as_box_any = Box::new(tool) as Box<dyn std::any::Any + Send + Sync + 'static>;
        let existing = self.dynamic_tools.insert(marker_id, (type_id, as_box_any));
        assert!(existing.is_none());
    }
    #[inline]
    fn get_dynamic_tool<M: 'static + Send + Sync, TT: GateTool>(&self) -> Option<&TT> {
        let marker_id = std::any::TypeId::of::<M>();
        let type_id = std::any::TypeId::of::<TT>();
        let (expected_type_id, as_any_ref) = self
            .dynamic_tools
            .get(&marker_id)
            .map(|el| (&el.0, &el.1))
            .unzip();
        if let Some(expected_type_id) = expected_type_id {
            if expected_type_id != &type_id {
                panic!(
                    "Trying to get tooling for marker {} with mismathing type",
                    std::any::type_name::<M>()
                );
            }
        }
        as_any_ref.map(|el| {
            el.downcast_ref().expect(&format!(
                "must downcast to proper tool type for type ID {:?} and marker {}",
                type_id,
                std::any::type_name::<M>(),
            ))
        })
    }
    #[inline]
    fn get_dynamic_tool_mut<M: 'static + Send + Sync, TT: GateTool>(&mut self) -> Option<&mut TT> {
        let marker_id = std::any::TypeId::of::<M>();
        let type_id = std::any::TypeId::of::<TT>();
        let (expected_type_id, as_any_ref) = self
            .dynamic_tools
            .get_mut(&marker_id)
            .map(|el| (&mut el.0, &mut el.1))
            .unzip();
        if let Some(expected_type_id) = expected_type_id {
            if expected_type_id != &type_id {
                panic!(
                    "Trying to get tooling for marker {} with mismathing type",
                    std::any::type_name::<M>()
                );
            }
        }
        as_any_ref.map(|el| {
            el.downcast_mut().expect(&format!(
                "must downcast to proper tool type for type ID {:?} and marker {}",
                type_id,
                std::any::type_name::<M>(),
            ))
        })
    }
    #[inline]
    fn take_dynamic_tool<M: 'static + Send + Sync, TT: GateTool>(&mut self) -> Option<TT> {
        let marker_id = std::any::TypeId::of::<M>();
        let type_id = std::any::TypeId::of::<TT>();
        let (expected_type_id, as_any) = self.dynamic_tools.remove(&marker_id).unzip();
        if let Some(expected_type_id) = expected_type_id {
            if expected_type_id != type_id {
                panic!(
                    "Trying to get tooling for marker {} with mismathing type",
                    std::any::type_name::<M>()
                );
            }
        }
        as_any
            .map(|el| {
                el.downcast().expect(&format!(
                    "must downcast to proper tool type for type ID {:?} and marker {}",
                    type_id,
                    std::any::type_name::<M>(),
                ))
            })
            .map(|el| *el)
    }
    #[inline]
    fn get_params(&self) -> CSGeometry {
        self.parameters
    }
    #[inline]
    fn get_lookup_params(&self) -> LookupParameters {
        self.lookup_parameters
    }

    #[inline]
    fn gate_is_allowed<G: Gate<F>>(&self) -> bool {
        self.gates_configuration.is_gate_allowed::<G>()
    }

    #[inline]
    fn get_gate_params<G: Gate<F>>(
        &self,
    ) -> <G::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams {
        self.gates_configuration
            .get_params::<G>()
            .expect("gate must be allowed")
    }

    #[inline]
    fn next_available_row(&self) -> usize {
        self.next_available_row
    }
    #[inline]
    fn place_variable(&mut self, var: Variable, row: usize, column: usize) {
        debug_assert!(
            row < self.next_available_row,
            "gate allocation must come before variable to actually \"take\" a row"
        );
        // so we do not have to resize and take care of padding with extra placeholders
        debug_assert!(self.next_available_row <= self.max_trace_len);

        assert_not_placeholder_variable(var);

        if <Self::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            // we do not care about placement
            return;
        }

        self.copy_permutation_data[column][row] = var;
    }
    #[inline]
    fn place_constants<const N: usize>(
        &mut self,
        gate_constants: &[F; N],
        row: usize,
        offset: usize,
    ) {
        debug_assert!(
            row < self.next_available_row,
            "gate allocation must come before variable to actually \"take\" a row"
        );
        debug_assert!(
            gate_constants.len() <= self.parameters.num_constant_columns,
            "too many constants for CS geometry"
        );

        if <Self::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            // we do not care about placement
            return;
        }

        if offset == 0 {
            if row < self.constants_requested_per_row.len() {
                // some gates may reuse constants
                debug_assert!(self.constants_requested_per_row[row][..] == gate_constants[..]);
            } else {
                // use new row
                debug_assert!(self.constants_requested_per_row.len() <= row);
                // some gates may skip requesting constants, so we will resize
                if row != 0 {
                    let resize_to = row;
                    if self.constants_requested_per_row.len() < resize_to {
                        self.constants_requested_per_row
                            .resize(resize_to, SmallVec::new());
                    }
                }
                let mut constants = SmallVec::new();
                constants.extend_from_slice(gate_constants);
                self.constants_requested_per_row.push(constants);
            }
        } else {
            let placement = self
                .constants_requested_per_row
                .get_mut(row)
                .expect("trying to place constants into non-existing row at non-zero offset");
            debug_assert_eq!(
                placement.len(),
                offset,
                "placement of constants must be continuous"
            );
            placement.extend_from_slice(gate_constants);
        }
    }
    #[inline]
    fn place_witness(&mut self, witness: Witness, row: usize, column: usize) {
        debug_assert!(
            row < self.next_available_row,
            "gate allocation must come before variable to actually \"take\" a row"
        );
        // so we do not have to resize and take care of padding with extra placeholders
        debug_assert!(self.next_available_row <= self.max_trace_len);

        if <Self::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            // we do not care about placement
            return;
        }

        self.witness_placement_data[column][row] = witness;
    }
    #[inline]
    fn place_gate<G: Gate<F>>(&mut self, gate: &G, row: usize) {
        debug_assert!(
            self.gate_is_allowed::<G>(),
            "gate {} is not configured for CS",
            std::any::type_name::<G>()
        );

        if <Self::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            // we do not care about placement
            return;
        }
        // NOTE: we do not use the type or value of the "gate" itself too much,
        // other than to create the evaluator itself. In the happy path we do not even
        // create an evaluator

        debug_assert!(
            gate.check_compatible_with_cs(&*self),
            "Gate {:?} is not compatible with CS configured as {:?}",
            gate,
            self.parameters
        );

        let idx = self
            .evaluation_data_over_general_purpose_columns
            .evaluator_type_id_into_evaluator_index_over_general_purpose_columns
            .get(&TypeId::of::<G::Evaluator>())
            .copied()
            .expect("gate must be allowed");
        if row == self.next_available_row {
            // use new row
            self.next_available_row += 1;
            debug_assert!(self.gates_application_sets.len() == row);
            self.gates_application_sets.push(idx);
        } else {
            debug_assert!(matches!(
                gate.placement_type(),
                GatePlacementType::MultipleOnRow { .. }
            ));
            debug_assert!(self.gates_application_sets[row] == idx);
        }

        debug_assert!(row < self.next_available_row);
        assert!(
            self.next_available_row <= self.max_trace_len,
            "exhausted general purpose columns capacity trying to add gate {}",
            std::any::type_name::<G>()
        );
    }

    #[inline]
    fn place_variable_specialized<G: Gate<F>>(
        &mut self,
        var: Variable,
        repetition: usize,
        row: usize,
        column: usize,
    ) {
        debug_assert!(
            self.gate_is_allowed::<G>(),
            "gate {} is not configured for CS",
            std::any::type_name::<G>()
        );

        assert_not_placeholder_variable(var);

        if <Self::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            // we do not care about placement
            return;
        }

        assert!(row < self.max_trace_len);

        // we are already given a repetition number, so we just need to get the offset
        let placement_strategy = self
            .gates_configuration
            .placement_strategy::<G>()
            .expect("gate must be allowed");
        let GatePlacementStrategy::UseSpecializedColumns {
            num_repetitions, ..
        } = placement_strategy
        else {
            unreachable!();
        };

        let idx = self
            .evaluation_data_over_specialized_columns
            .gate_type_id_into_evaluator_index_over_specialized_columns
            .get(&TypeId::of::<G>())
            .copied()
            .expect("gate must be allowed");
        let (mut initial_offset, offset_per_repetition, _) = self
            .evaluation_data_over_specialized_columns
            .offsets_for_specialized_evaluators[idx];
        assert!(repetition < num_repetitions, "gate is configured to have at most {} repetitions, but trying to place when {} already exist", num_repetitions, repetition);
        for _ in 0..repetition {
            initial_offset.add_offset(&offset_per_repetition);
        }

        let offset = initial_offset.variables_offset + column;
        // depending on parametrization we can have rows filled or not,
        // so we branch
        if self.copy_permutation_data[offset].len() > row {
            // there may be another copy with different parameter here,
            // so we have to assign
            debug_assert!(
                self.copy_permutation_data[offset][row].is_placeholder(),
                "Failed to place for gate {} at repetition {} for offset {}",
                std::any::type_name::<G>(),
                repetition,
                offset,
            );
            self.copy_permutation_data[offset][row] = var;
        } else {
            self.copy_permutation_data[offset].resize(row, Variable::placeholder());
            self.copy_permutation_data[offset].push(var);
            debug_assert_eq!(self.copy_permutation_data[offset].len(), row + 1);
        }
    }
    #[inline]
    fn place_witness_specialized<G: Gate<F>>(
        &mut self,
        witness: Witness,
        repetition: usize,
        row: usize,
        column: usize,
    ) {
        debug_assert!(
            self.gate_is_allowed::<G>(),
            "gate {} is not configured for CS",
            std::any::type_name::<G>()
        );

        if <Self::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            // we do not care about placement
            return;
        }

        assert!(
            row < self.max_trace_len,
            "can not place more instances of gate {}",
            std::any::type_name::<G>()
        );

        // we are already given a repetition number, so we just need to get the offset
        let placement_strategy = self
            .gates_configuration
            .placement_strategy::<G>()
            .expect("gate must be allowed");
        let GatePlacementStrategy::UseSpecializedColumns {
            num_repetitions, ..
        } = placement_strategy
        else {
            unreachable!();
        };

        let idx = self
            .evaluation_data_over_specialized_columns
            .gate_type_id_into_evaluator_index_over_specialized_columns
            .get(&TypeId::of::<G>())
            .copied()
            .expect("gate must be allowed");
        let (mut initial_offset, offset_per_repetition, _) = self
            .evaluation_data_over_specialized_columns
            .offsets_for_specialized_evaluators[idx];
        assert!(repetition < num_repetitions, "gate is configured to have at most {} repetitions, but trying to place when {} already exist", num_repetitions, repetition);
        for _ in 0..repetition {
            initial_offset.add_offset(&offset_per_repetition);
        }

        let offset = initial_offset.witnesses_offset + column;
        debug_assert_eq!(
            self.witness_placement_data[offset].len(),
            row,
            "rows must be continuous for specialized gates"
        );
        self.witness_placement_data[offset].push(witness);
    }
    #[inline(always)]
    fn place_gate_specialized<G: Gate<F>>(&mut self, _gate: &G, _repetition: usize, row: usize) {
        debug_assert!(
            self.gate_is_allowed::<G>(),
            "gate {} is not configured for CS",
            std::any::type_name::<G>()
        );

        if <Self::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            // we do not care about placement
            return;
        }

        assert!(row < self.max_trace_len,
            "can not place more specialized instances of gate {}: max trace length is {}, but trying to use row {}",
            std::any::type_name::<G>(),
            self.max_trace_len,
            row,
        );

        let entry = self
            .specialized_gates_rough_stats
            .entry(std::any::TypeId::of::<G>())
            .or_default();
        *entry = std::cmp::max(row, *entry);
        // actually we do not need to "do" anything here, let the gate handle it's placement itself.
        // May be later on we will intoduce counters for self-checks
    }
    #[inline]
    fn place_constants_specialized<G: Gate<F>, const N: usize>(
        &mut self,
        constants: &[F; N],
        repetition: usize,
        row: usize,
        offset: usize,
    ) {
        debug_assert!(
            self.gate_is_allowed::<G>(),
            "gate {} is not configured for CS",
            std::any::type_name::<G>()
        );

        if <Self::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            // we do not care about placement
            return;
        }

        assert!(
            row < self.max_trace_len,
            "can not place more instances of gate {}",
            std::any::type_name::<G>()
        );

        // we are already given a repetition number, so we just need to get the offset
        let placement_strategy = self
            .gates_configuration
            .placement_strategy::<G>()
            .expect("gate must be allowed");
        let GatePlacementStrategy::UseSpecializedColumns {
            num_repetitions,
            share_constants,
        } = placement_strategy
        else {
            unreachable!();
        };

        let idx = self
            .evaluation_data_over_specialized_columns
            .gate_type_id_into_evaluator_index_over_specialized_columns
            .get(&TypeId::of::<G>())
            .copied()
            .expect("gate must be allowed");
        let (initial_offsets, offset_per_repetition, total_constants_available) = self
            .evaluation_data_over_specialized_columns
            .offsets_for_specialized_evaluators[idx];
        assert!(repetition < num_repetitions, "gate is configured to have at most {} repetitions, but trying to place when {} already exist", num_repetitions, repetition);
        let mut constants_offset = initial_offsets.constants_offset;
        if share_constants == false {
            for _ in 0..repetition {
                constants_offset += offset_per_repetition.constants_offset;
            }
        }

        debug_assert!(offset + N <= total_constants_available);

        // for specialized gates placement is always continuous
        let range = (constants_offset + offset)..(constants_offset + offset + N);

        if offset > 0 {
            // sanity check that all previous were filled it
            for dst in self.constants_for_gates_in_specialized_mode
                [constants_offset..(constants_offset + offset)]
                .iter()
            {
                debug_assert!(
                    dst.len() > row,
                    "should not place at offset > 0 before placing at offset 0"
                );
            }
        }

        if share_constants == true && repetition > 0 {
            // self-check that it's the same constants
            let dst = &self.constants_for_gates_in_specialized_mode[range];
            let src = constants.iter();
            for (dst, src) in dst.iter().zip(src) {
                debug_assert_eq!(
                    &dst[row],
                    src,
                    "different constant is placed in shared constant mode for gate {}, repetition {}, offset {}, row {}",
                    std::any::type_name::<G>(),
                    repetition,
                    offset,
                    row
                );
            }

            return;
        }

        let dst = &mut self.constants_for_gates_in_specialized_mode[range];
        let src = constants.iter();
        for (dst, src) in dst.iter_mut().zip(src) {
            debug_assert_eq!(dst.len(), row);
            dst.push(*src);
        }
    }
    #[inline]
    fn place_multiple_variables_into_row_specialized<G: Gate<F>, const N: usize>(
        &mut self,
        vars: &[Variable; N],
        repetition: usize,
        row: usize,
        starting_column: usize,
    ) {
        debug_assert!(
            self.gate_is_allowed::<G>(),
            "gate {} is not configured for CS",
            std::any::type_name::<G>()
        );

        assert_no_placeholder_variables(vars);

        if <Self::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            // we do not care about placement
            return;
        }

        assert!(
            row < self.max_trace_len,
            "can not place more instances of gate {}",
            std::any::type_name::<G>()
        );

        // we are already given a repetition number, so we just need to get the offset
        let placement_strategy = self
            .gates_configuration
            .placement_strategy::<G>()
            .expect("gate must be allowed");
        let GatePlacementStrategy::UseSpecializedColumns {
            num_repetitions, ..
        } = placement_strategy
        else {
            unreachable!();
        };

        let idx = self
            .evaluation_data_over_specialized_columns
            .gate_type_id_into_evaluator_index_over_specialized_columns
            .get(&TypeId::of::<G>())
            .copied()
            .expect("gate must be allowed");
        let (mut initial_offset, offset_per_repetition, _) = self
            .evaluation_data_over_specialized_columns
            .offsets_for_specialized_evaluators[idx];
        assert!(repetition < num_repetitions);
        for _ in 0..repetition {
            initial_offset.add_offset(&offset_per_repetition);
        }

        let mut offset = initial_offset.variables_offset + starting_column;
        for var in vars.iter() {
            // depending on parametrization we can have rows filled or not,
            // so we branch
            if self.copy_permutation_data[offset].len() > row {
                // there may be another copy with different parameter here,
                // so we have to assign
                debug_assert!(
                    self.copy_permutation_data[offset][row].is_placeholder(),
                    "Failed to place for gate {} at repetition {} for offset {}: trying to place into absolute columns number {}",
                    std::any::type_name::<G>(),
                    repetition,
                    starting_column,
                    offset,
                );
                self.copy_permutation_data[offset][row] = *var;
            } else {
                self.copy_permutation_data[offset].resize(row, Variable::placeholder());
                self.copy_permutation_data[offset].push(*var);
                debug_assert_eq!(self.copy_permutation_data[offset].len(), row + 1);
            }
            offset += 1;
        }
    }

    fn perform_lookup<const KEYS: usize, const VALUES: usize>(
        &mut self,
        table_id: u32,
        keys: &[Variable; KEYS],
    ) -> [Variable; VALUES]
    where
        [(); KEYS + VALUES]:,
    {
        // here we only find an output value,
        // and use "enforce" later on to count multiplicity

        let output = match self.lookup_parameters {
            LookupParameters::NoLookup => {
                panic!("Lookup is not allowed for that CS");
            }
            LookupParameters::TableIdAsVariable { width, .. }
            | LookupParameters::TableIdAsConstant { width, .. }
            | LookupParameters::UseSpecializedColumnsWithTableIdAsConstant { width, .. }
            | LookupParameters::UseSpecializedColumnsWithTableIdAsVariable { width, .. } => {
                debug_assert_eq!(width as usize, KEYS + VALUES);

                let output_variables = self.alloc_multiple_variables_without_values::<VALUES>();

                let table_id = table_id - INITIAL_LOOKUP_TABLE_ID_VALUE;
                let table = std::sync::Arc::clone(&self.lookup_tables[table_id as usize]);

                let value_fn = move |inputs: [F; KEYS]| {
                    let (_, values) = table.lookup_value::<VALUES>(&inputs);

                    values.into_inner().expect("length must match")
                };

                self.set_values_with_dependencies(
                    &Place::from_variables(*keys),
                    &Place::from_variables(output_variables),
                    value_fn,
                );

                output_variables
            }
        };

        let mut keys_and_values = [Variable::placeholder(); KEYS + VALUES];
        keys_and_values[..KEYS].copy_from_slice(keys);
        keys_and_values[KEYS..].copy_from_slice(&output);

        self.enforce_lookup::<{ KEYS + VALUES }>(table_id, &keys_and_values);

        output
    }

    fn enforce_lookup<const N: usize>(&mut self, table_id: u32, keys_and_values: &[Variable; N]) {
        match self.lookup_parameters {
            LookupParameters::NoLookup => {
                panic!("Lookup is not allowed for that CS");
            }
            LookupParameters::TableIdAsVariable { width, .. } => {
                debug_assert_eq!(width as usize, N);

                self.enforce_lookup_over_general_purpose_columns(
                    table_id,
                    keys_and_values,
                    width as usize,
                    false,
                );
            }
            LookupParameters::TableIdAsConstant { width, .. } => {
                debug_assert_eq!(width as usize, N);

                self.enforce_lookup_over_general_purpose_columns(
                    table_id,
                    keys_and_values,
                    width as usize,
                    true,
                );
            }
            LookupParameters::UseSpecializedColumnsWithTableIdAsVariable {
                width,
                num_repetitions,
                ..
            } => {
                debug_assert_eq!(width as usize, N);

                self.enforce_lookup_over_specialized_columns(
                    table_id,
                    keys_and_values,
                    num_repetitions,
                    false,
                );
            }
            LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                width,
                num_repetitions,
                ..
            } => {
                debug_assert_eq!(width as usize, N);

                self.enforce_lookup_over_specialized_columns(
                    table_id,
                    keys_and_values,
                    num_repetitions,
                    true,
                );
            }
        }
    }

    fn place_multiple_variables_into_row<const N: usize>(
        &mut self,
        var: &[Variable; N],
        row: usize,
        starting_column: usize,
    ) {
        debug_assert!(
            row < self.next_available_row,
            "gate allocation must come before variable to actually \"take\" a row"
        );
        // so we do not have to resize and take care of padding with extra placeholders
        debug_assert!(self.next_available_row <= self.max_trace_len);

        assert_no_placeholder_variables(var);

        if <Self::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            // we do not care about placement
            return;
        }

        for (offset, var) in var.iter().enumerate() {
            self.copy_permutation_data[starting_column + offset][row] = *var;
        }
    }

    // Lookup table related things
    fn add_lookup_table<M: 'static + Send + Sync, const N: usize>(
        &mut self,
        table: LookupTable<F, N>,
    ) -> u32
    where
        LookupTable<F, N>: Wrappable<F>,
    {
        assert!(self.lookup_parameters.lookup_is_allowed());

        let table_width = table.num_keys() + table.num_values();
        assert_eq!(table_width, self.lookup_parameters.lookup_width());

        let id = self.next_lookup_table_index;
        self.next_lookup_table_index += 1;

        let table_size = table.table_size();

        if self.lookups_tables_total_len() > self.max_trace_len {
            unimplemented!("breaking encoding of lookup tables into multiple subcolumns is not yet implemented");
        }

        self.lookup_table_marker_into_id
            .insert(std::any::TypeId::of::<M>(), id);

        let wrapped = table.into_wrapper();
        let wrapped_arc = std::sync::Arc::new(wrapped);
        self.lookup_tables.push(wrapped_arc);

        match self.lookup_parameters {
            LookupParameters::NoLookup => {
                unreachable!()
            }
            LookupParameters::TableIdAsVariable { .. }
            | LookupParameters::UseSpecializedColumnsWithTableIdAsVariable { .. } => {
                // we need to create a formal ID
                let table_id_variable = self.allocate_constant(F::from_u64_unchecked(id as u64));
                self.table_ids_as_variables.push(table_id_variable);

                // we need to update the tooling in a limited way
                let tooling = self
                    .get_gates_config_mut()
                    .get_aux_data_mut::<LookupFormalGate, LookupTooling>()
                    .expect("tooling must exist");

                tooling.0.resize(1, None);
                assert!(
                    tooling.1 == 0,
                    "must declare tables before placing anything"
                );

                // we need to resize multiplicities
                let mut column = Vec::with_capacity(table_size);
                if CFG::WitnessConfig::EVALUATE_WITNESS {
                    column.resize_with(table_size, || AtomicU32::new(0));
                }
                self.lookup_multiplicities.push(std::sync::Arc::new(column));
            }
            LookupParameters::TableIdAsConstant { .. }
            | LookupParameters::UseSpecializedColumnsWithTableIdAsConstant { .. } => {
                // we need to update the tooling
                let tooling = self
                    .get_gates_config_mut()
                    .get_aux_data_mut::<LookupFormalGate, LookupTooling>()
                    .expect("tooling must exist");

                tooling.0.resize(id as usize, None);
                assert!(
                    tooling.1 == 0,
                    "must declare tables before placing anything"
                );

                // we need to resize multiplicities
                let mut column = Vec::with_capacity(table_size);
                if CFG::WitnessConfig::EVALUATE_WITNESS == true {
                    column.resize_with(table_size, || AtomicU32::new(0));
                }

                self.lookup_multiplicities.push(std::sync::Arc::new(column));
            }
        }

        assert!(self.lookups_tables_total_len() <= self.max_trace_len,
            "max trace is not large enough to fit all the tables for setup: max length is {} and tables require {} rows",
            self.max_trace_len,
            self.lookups_tables_total_len(),
        );

        id
    }
    #[inline]
    fn get_table_id_for_marker<M: 'static + Send + Sync>(&self) -> Option<u32> {
        self.lookup_table_marker_into_id
            .get(&std::any::TypeId::of::<M>())
            .copied()
    }
    #[inline]
    fn get_table(&self, table_num: u32) -> std::sync::Arc<LookupTableWrapper<F>> {
        let table_id = table_num - INITIAL_LOOKUP_TABLE_ID_VALUE;
        std::sync::Arc::clone(
            self.lookup_tables
                .get(table_id as usize)
                .expect("table must exist when queried"),
        )
    }
}

#[cfg(test)]
mod test {

    use std::alloc::Global;

    use super::*;
    use crate::algebraic_props::round_function::AbsorptionModeOverwrite;
    use crate::algebraic_props::sponge::GoldilocksPoseidonSponge;
    use crate::cs::cs_builder::*;
    use crate::cs::cs_builder_reference::CsReferenceImplementationBuilder;
    use crate::cs::cs_builder_verifier::CsVerifierBuilder;
    use crate::cs::gates::{fma_gate_without_constant::*, NopGate, ReductionGate, ZeroCheckGate};

    use crate::cs::implementations::pow::NoPow;
    use crate::cs::implementations::prover::ProofConfig;
    use crate::cs::implementations::transcript::GoldilocksPoisedonTranscript;

    use crate::dag::CircuitResolverOpts;
    use crate::field::goldilocks::GoldilocksExt2;

    use crate::{
        cs::gates::boolean_allocator::BooleanConstraintGate,
        field::{goldilocks::GoldilocksField, Field, U64Representable},
    };

    type F = GoldilocksField;

    #[test]
    fn prove_simple() {
        type P = GoldilocksField;
        type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;
        // type P = MixedGL;

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 8,
            num_witness_columns: 0,
            num_constant_columns: 2,
            max_allowed_constraint_degree: 8,
        };

        let max_variables = 512;
        let max_trace_len = 128;

        fn configure<
            T: CsBuilderImpl<F, T>,
            GC: GateConfigurationHolder<F>,
            TB: StaticToolboxHolder,
        >(
            builder: CsBuilder<T, F, GC, TB>,
        ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
            let builder = ConstantsAllocatorGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ZeroCheckGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
                false,
            );
            let builder = NopGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            builder
        }

        let builder_impl =
            CsReferenceImplementationBuilder::<F, P, DevCSConfig>::new(geometry, max_trace_len);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut cs = builder.build(CircuitResolverOpts::new(max_variables));

        let mut previous = None;

        for _ in 0..100 {
            let a = if let Some(previous) = previous.take() {
                previous
            } else {
                cs.alloc_single_variable_from_witness(GoldilocksField::from_u64_unchecked(1))
            };
            let b = cs.alloc_single_variable_from_witness(GoldilocksField::from_u64_unchecked(2));
            let c = cs.alloc_single_variable_from_witness(GoldilocksField::from_u64_unchecked(3));

            let d = FmaGateInBaseFieldWithoutConstant::compute_fma(
                &mut cs,
                GoldilocksField::TWO,
                (a, b),
                GoldilocksField::MINUS_ONE,
                c,
            );
            // previous = Some(d);

            let e = ZeroCheckGate::check_if_zero(&mut cs, d);
            previous = Some(e);
            // let e = FmaGateInBaseFieldWithoutConstant::compute_fma(
            //     &mut cs,
            //     GoldilocksField::TWO,
            //     (d, d),
            //     GoldilocksField::MINUS_ONE,
            //     a,
            // );
        }

        use super::gates::constant_allocator::*;

        // make few constants
        cs.allocate_constant(GoldilocksField::from_u64_unchecked(3));
        cs.allocate_constant(GoldilocksField::from_u64_unchecked(4));

        cs.pad_and_shrink();

        // let worker = Worker::new();

        let worker = Worker::new_with_num_threads(1);
        let cs = cs.into_assembly::<Global>();

        let lde_factor_to_use = 16;
        let proof_config = ProofConfig {
            fri_lde_factor: lde_factor_to_use,
            pow_bits: 0,
            ..Default::default()
        };

        let (proof, vk) = cs.prove_one_shot::<
            GoldilocksExt2,
            GoldilocksPoisedonTranscript,
            GoldilocksPoseidonSponge<AbsorptionModeOverwrite>,
            NoPow,
        >(&worker, proof_config, ());

        let builder_impl = CsVerifierBuilder::<F, GoldilocksExt2>::new_from_parameters(geometry);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let verifier = builder.build(());

        let is_valid = verifier.verify::<
            GoldilocksPoseidonSponge<AbsorptionModeOverwrite>,
            GoldilocksPoisedonTranscript,
            NoPow
        >(
            (),
            &vk,
            &proof,
        );

        assert!(is_valid);
    }

    #[test]
    #[ignore = "Computation of poly pairs for lookups unimplemented"]
    fn prove_simple_with_lookups() {
        pub const TEST_TABLE_NAME: &str = "Test table";

        #[derive(Derivative)]
        #[derivative(Clone, Copy, Debug)]
        pub struct TestTableMarker;

        type P = GoldilocksField;
        // type P = MixedGL;
        type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;

        pub fn create_test_table<F: SmallField>() -> LookupTable<F, 3> {
            let mut all_keys = Vec::with_capacity(64);
            for a in 0..8 {
                for b in 0..8 {
                    let key = smallvec::smallvec![
                        F::from_u64_unchecked(a as u64),
                        F::from_u64_unchecked(b as u64)
                    ];
                    all_keys.push(key);
                }
            }
            LookupTable::new_from_keys_and_generation_function(
                &all_keys,
                TEST_TABLE_NAME.to_string(),
                2,
                |keys| {
                    let a = keys[0].as_u64_reduced() as u8;
                    let b = keys[1].as_u64_reduced() as u8;

                    let xor_result = a ^ b;
                    let or_result = a | b;
                    let and_result = a & b;
                    let value =
                        (xor_result as u64) << 32 | (or_result as u64) << 16 | (and_result as u64);

                    smallvec::smallvec![F::from_u64_unchecked(value)]
                },
            )
        }

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 8,
            num_witness_columns: 0,
            num_constant_columns: 2,
            max_allowed_constraint_degree: 8,
        };

        // let cs = CSReferenceImplementation::<
        //     GoldilocksField,
        //     P,
        //     DevCSConfig,
        //     _,
        //     _,
        // >::new_for_geometry(geometry, 512, 128);

        fn configure<
            T: CsBuilderImpl<F, T>,
            GC: GateConfigurationHolder<F>,
            TB: StaticToolboxHolder,
        >(
            builder: CsBuilder<T, F, GC, TB>,
        ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
            // allow lookup
            let builder = builder.allow_lookup(LookupParameters::TableIdAsVariable {
                width: 3,
                share_table_id: false,
            });

            let builder = ConstantsAllocatorGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            // we pad with NOP gates, so we should formally allow it
            let builder = NopGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            builder
        }

        let builder = new_builder(CsReferenceImplementationBuilder::<
            GoldilocksField,
            P,
            DevCSConfig,
        >::new(geometry, 128));
        let builder = configure(builder);
        let mut cs = builder.build(CircuitResolverOpts::new(512));

        let table = create_test_table();
        let table_id = cs.add_lookup_table::<TestTableMarker, 3>(table);

        for _ in 0..100 {
            let a = cs.alloc_single_variable_from_witness(GoldilocksField::from_u64_unchecked(1));
            let b = cs.alloc_single_variable_from_witness(GoldilocksField::from_u64_unchecked(2));
            let c = cs.alloc_single_variable_from_witness(GoldilocksField::from_u64_unchecked(3));

            let d = FmaGateInBaseFieldWithoutConstant::compute_fma(
                &mut cs,
                GoldilocksField::TWO,
                (a, b),
                GoldilocksField::MINUS_ONE,
                c,
            );

            let [_e] = cs.perform_lookup(table_id, &[a, d]);
        }

        use super::gates::constant_allocator::*;

        // make few constants
        cs.allocate_constant(GoldilocksField::from_u64_unchecked(3));

        cs.pad_and_shrink();

        dbg!(&cs.max_trace_len);

        let worker = Worker::new();
        let cs = cs.into_assembly::<Global>();

        let lde_factor_to_use = 16;
        let proof_config = ProofConfig {
            fri_lde_factor: lde_factor_to_use,
            pow_bits: 0,
            ..Default::default()
        };

        let (proof, vk) = cs.prove_one_shot::<
            GoldilocksExt2,
            GoldilocksPoisedonTranscript,
            GoldilocksPoseidonSponge<AbsorptionModeOverwrite>,
            NoPow,
        >(&worker, proof_config, ());

        let builder_impl = CsVerifierBuilder::<F, GoldilocksExt2>::new_from_parameters(geometry);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let verifier = builder.build(());

        let is_valid = verifier.verify::<
            GoldilocksPoseidonSponge<AbsorptionModeOverwrite>,
            GoldilocksPoisedonTranscript,
            NoPow
        >(
            (),
            &vk,
            &proof,
        );

        assert!(is_valid);
    }

    #[test]
    #[ignore = "Unimplemented part of prover is called"]
    fn prove_simple_specialized() {
        type P = GoldilocksField;
        // type P = MixedGL;
        type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 0,
            num_witness_columns: 0,
            num_constant_columns: 0,
            max_allowed_constraint_degree: 8,
        };

        let max_variables = 1 << 16;
        let max_trace_len = 64;

        fn configure<
            T: CsBuilderImpl<F, T>,
            GC: GateConfigurationHolder<F>,
            TB: StaticToolboxHolder,
        >(
            builder: CsBuilder<T, F, GC, TB>,
        ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
            let builder = BooleanConstraintGate::configure_builder(
                builder,
                GatePlacementStrategy::UseSpecializedColumns {
                    num_repetitions: 2,
                    share_constants: false,
                },
            );
            let builder = NopGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            builder
        }

        let builder_impl =
            CsReferenceImplementationBuilder::<F, P, DevCSConfig>::new(geometry, max_trace_len);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut cs = builder.build(CircuitResolverOpts::new(max_variables));

        for _i in 0..50 {
            let a = cs.alloc_single_variable_from_witness(GoldilocksField::from_u64_unchecked(1));
            let b = cs.alloc_single_variable_from_witness(GoldilocksField::from_u64_unchecked(0));

            if _i % 2 == 0 {
                let _ = BooleanConstraintGate::enforce_boolean(&mut cs, a);
                let _ = BooleanConstraintGate::enforce_boolean(&mut cs, b);
            } else {
                let _ = BooleanConstraintGate::enforce_boolean(&mut cs, b);
                let _ = BooleanConstraintGate::enforce_boolean(&mut cs, a);
            }
        }

        cs.pad_and_shrink();

        dbg!(&cs.max_trace_len);

        let worker = Worker::new_with_num_threads(1);

        let cs = cs.into_assembly::<Global>();

        // assert!(cs.check_if_satisfied(&worker));

        let lde_factor_to_use = 16;
        let proof_config = ProofConfig {
            fri_lde_factor: lde_factor_to_use,
            pow_bits: 0,
            ..Default::default()
        };

        let (proof, vk) = cs.prove_one_shot::<
            GoldilocksExt2,
            GoldilocksPoisedonTranscript,
            GoldilocksPoseidonSponge<AbsorptionModeOverwrite>,
            NoPow,
        >(&worker, proof_config, ());

        let builder_impl = CsVerifierBuilder::<F, GoldilocksExt2>::new_from_parameters(geometry);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let verifier = builder.build(());

        let is_valid = verifier.verify::<
            GoldilocksPoseidonSponge<AbsorptionModeOverwrite>,
            GoldilocksPoisedonTranscript,
            NoPow
        >(
            (),
            &vk,
            &proof,
        );

        assert!(is_valid);
    }

    #[test]
    fn prove_simple_specialized_with_lookups() {
        pub const TEST_TABLE_NAME: &str = "Test table";
        pub const TEST_TABLE_NAME2: &str = "Test table 2";

        #[derive(Derivative)]
        #[derivative(Clone, Copy, Debug)]
        pub struct TestTableMarker;

        #[derive(Derivative)]
        #[derivative(Clone, Copy, Debug)]
        pub struct TestTableMarker2;

        type P = GoldilocksField;
        // type P = MixedGL;
        type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;

        fn create_test_table<F: SmallField>() -> LookupTable<F, 3> {
            let mut all_keys = Vec::with_capacity(64);
            for a in 0..8 {
                for b in 0..8 {
                    let key = smallvec::smallvec![
                        F::from_u64_unchecked(a as u64),
                        F::from_u64_unchecked(b as u64)
                    ];
                    all_keys.push(key);
                }
            }
            LookupTable::new_from_keys_and_generation_function(
                &all_keys,
                TEST_TABLE_NAME.to_string(),
                2,
                |keys| {
                    let a = keys[0].as_u64_reduced() as u8;
                    let b = keys[1].as_u64_reduced() as u8;

                    let xor_result = a ^ b;
                    let or_result = a | b;
                    let and_result = a & b;
                    let value =
                        (xor_result as u64) << 32 | (or_result as u64) << 16 | (and_result as u64);

                    smallvec::smallvec![F::from_u64_unchecked(value)]
                },
            )
        }

        fn create_test_table_2<F: SmallField>() -> LookupTable<F, 3> {
            let mut all_keys = Vec::with_capacity(64);
            for a in 0..8 {
                for b in 0..8 {
                    let key = smallvec::smallvec![
                        F::from_u64_unchecked(a as u64),
                        F::from_u64_unchecked(b as u64)
                    ];
                    all_keys.push(key);
                }
            }
            LookupTable::new_from_keys_and_generation_function(
                &all_keys,
                TEST_TABLE_NAME2.to_string(),
                2,
                |keys| {
                    let a = keys[0].as_u64_reduced() as u8;
                    let b = keys[1].as_u64_reduced() as u8;

                    let xor_result = a ^ b;
                    let or_result = a | b;
                    let and_result = a & b;
                    let value =
                        (xor_result as u64) << 16 | (or_result as u64) << 8 | (and_result as u64);

                    smallvec::smallvec![F::from_u64_unchecked(value)]
                },
            )
        }

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 8,
            num_witness_columns: 0,
            num_constant_columns: 2,
            max_allowed_constraint_degree: 8,
        };

        let max_variables = 1 << 16;
        let max_trace_len = 128;

        // allow lookup

        fn configure<
            T: CsBuilderImpl<F, T>,
            GC: GateConfigurationHolder<F>,
            TB: StaticToolboxHolder,
        >(
            builder: CsBuilder<T, F, GC, TB>,
        ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
            let builder = builder.allow_lookup(
                LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                    width: 3,
                    num_repetitions: 2,
                    share_table_id: true,
                },
            );
            let builder = ConstantsAllocatorGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ZeroCheckGate::configure_builder(
                builder,
                GatePlacementStrategy::UseSpecializedColumns {
                    num_repetitions: 2,
                    share_constants: false,
                },
                true,
            );
            // we pad with NOP gates, so we should formally allow it
            let builder = NopGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            builder
        }

        let builder_impl =
            CsReferenceImplementationBuilder::<F, P, DevCSConfig>::new(geometry, max_trace_len);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut cs = builder.build(CircuitResolverOpts::new(max_variables));

        let table = create_test_table();
        let table_id = cs.add_lookup_table::<TestTableMarker, 3>(table);

        let table2 = create_test_table_2();
        let table_id2 = cs.add_lookup_table::<TestTableMarker2, 3>(table2);

        for i in 0..101 {
            let a = cs.alloc_single_variable_from_witness(GoldilocksField::from_u64_unchecked(1));
            let b = cs.alloc_single_variable_from_witness(GoldilocksField::from_u64_unchecked(2));
            let c = cs.alloc_single_variable_from_witness(GoldilocksField::from_u64_unchecked(3));

            let d = FmaGateInBaseFieldWithoutConstant::compute_fma(
                &mut cs,
                GoldilocksField::TWO,
                (a, b),
                GoldilocksField::MINUS_ONE,
                c,
            );

            // let [e] = cs.perform_lookup(table_id, &[a, d]);

            // create some imbalance
            let e = if i % 2 == 0 {
                let [e] = cs.perform_lookup(table_id, &[a, d]);
                e
            } else {
                let [e] = cs.perform_lookup(table_id2, &[a, d]);
                e
            };

            let _f = ZeroCheckGate::check_if_zero(&mut cs, e);

            let [_i] = cs.perform_lookup(table_id2, &[a, d]);
            // let [_i] = cs.perform_lookup(table_id2, &[b, a]);
        }

        use super::gates::constant_allocator::*;

        // make few constants
        cs.allocate_constant(GoldilocksField::from_u64_unchecked(3));

        cs.pad_and_shrink();

        dbg!(&cs.max_trace_len);

        // NOTE: it's here only to check constant propagation
        let must_be_allowed = cs.gate_is_allowed::<ConstantsAllocatorGate<F>>();
        assert!(must_be_allowed);

        let may_be_in_config = cs.gate_is_allowed::<ReductionGate<F, 4>>();
        assert!(may_be_in_config == false);

        let worker = Worker::new_with_num_threads(8);

        let mut cs = cs.into_assembly::<Global>();

        assert!(cs.check_if_satisfied(&worker));

        let lde_factor_to_use = 16;
        let proof_config = ProofConfig {
            fri_lde_factor: lde_factor_to_use,
            pow_bits: 0,
            ..Default::default()
        };

        // let witness = cs.take_witness(&worker);
        // dbg!(&witness.multiplicities[0].storage);
        // panic!();

        let (proof, vk) = cs.prove_one_shot::<
            GoldilocksExt2,
            GoldilocksPoisedonTranscript,
            GoldilocksPoseidonSponge<AbsorptionModeOverwrite>,
            NoPow,
        >(&worker, proof_config, ());

        let builder_impl = CsVerifierBuilder::<F, GoldilocksExt2>::new_from_parameters(geometry);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let verifier = builder.build(());
        let is_valid = verifier.verify::<
            GoldilocksPoseidonSponge<AbsorptionModeOverwrite>,
            GoldilocksPoisedonTranscript,
            NoPow
        >(
            (),
            &vk,
            &proof,
        );

        assert!(is_valid);
    }

    // #[test]
    // fn prove_benchmark_simple() {
    //     use crate::cs::traits::destination_view::GateEvaluationReducingDestinationChunk;

    //     let limit = 1 << 20;

    //     let geometry = CSGeometry {
    //         num_columns_under_copy_permutation: 8,
    //         num_witness_columns: 0,
    //         num_constant_columns: 3,
    //         max_allowed_constraint_degree: 4,
    //         lookup_parameters: LookupParameters::NoLookup,
    //     };
    //     let mut cs = CSReferenceImplementation::<
    //         GoldilocksField,
    //         GoldilocksField,
    //         DevCSConfig,
    //         ProverTraceView<GoldilocksField, GoldilocksField>,
    //         GateEvaluationReducingDestinationChunk<GoldilocksField, GoldilocksField>
    //     >::new_for_geometry(geometry, limit*2, limit);

    //     let now = std::time::Instant::now();

    //     for _ in 0..limit {
    //         let a = cs.alloc_variable(ready(GoldilocksField::from_u64_unchecked(1)));
    //         let b = cs.alloc_variable(ready(GoldilocksField::from_u64_unchecked(2)));
    //         let c = cs.alloc_variable(ready(GoldilocksField::from_u64_unchecked(3)));

    //         let gate = FmaGateInBaseFieldWithConstant::new(
    //             GoldilocksField::TWO,
    //             (a, b),
    //             c,
    //             GoldilocksField::MINUS_ONE,
    //         );
    //         let (d, _) = gate.add(&mut cs);
    //         let gate = FmaGateInBaseFieldWithConstant::new(
    //             GoldilocksField::TWO,
    //             (d, d),
    //             a,
    //             GoldilocksField::MINUS_ONE,
    //         );
    //         let (_d, _) = gate.add(&mut cs);
    //     }

    //     assert_eq!(cs.next_available_row(), limit);

    //     log!("Synthesis taken {:?}", now.elapsed());

    //     cs.pad_and_shrink();

    //     cs.wait_for_witness();

    //     let worker = Worker::new_with_num_threads(8);

    //     let now = std::time::Instant::now();
    //     let base_setup = cs.create_base_setup(&worker, ());
    //     let (setup, _placement, _) = cs.materialize_setup_storage(8, &worker, ());
    //     log!("Setup taken {:?}", now.elapsed());

    //     let now = std::time::Instant::now();
    //     let _ = cs.prove_cpu_basic::<
    //         GoldilocksExt2,
    //         GoldilocksPoisedonTranscript,
    //         GoldilocksPoseidonSponge<AbsorptionModeOverwrite>
    //     >(
    //         &worker,
    //         &base_setup,
    //         &setup,
    //         8,
    //         ()
    //     );
    //     log!("Proof taken {:?}", now.elapsed());
    // }

    // #[test]
    // fn benchmark_synthesize_witness_only() {
    //     use crate::cs::traits::destination_view::GateEvaluationReducingDestinationChunk;

    //     let limit = 1 << 25;

    //     let geometry = CSGeometry {
    //         num_columns_under_copy_permutation: 8,
    //         num_witness_columns: 0,
    //         num_constant_columns: 3,
    //         max_allowed_constraint_degree: 4,
    //         lookup_parameters: LookupParameters::NoLookup,
    //     };
    //     let mut cs = CSReferenceImplementation::<
    //         GoldilocksField,
    //         GoldilocksField,
    //         ProvingCSConfig,
    //         ProverTraceView<GoldilocksField, GoldilocksField>,
    //         GateEvaluationReducingDestinationChunk<GoldilocksField, GoldilocksField>
    //     >::new_for_geometry(geometry, limit * 5 + 2, limit);

    //     let now = std::time::Instant::now();

    //     for _ in 0..limit {
    //         let a = cs.alloc_variable(ready(GoldilocksField::from_u64_unchecked(1)));
    //         let b = cs.alloc_variable(ready(GoldilocksField::from_u64_unchecked(2)));
    //         let c = cs.alloc_variable(ready(GoldilocksField::from_u64_unchecked(3)));

    //         let gate = FmaGateInBaseFieldWithConstant::new(
    //             GoldilocksField::TWO,
    //             (a, b),
    //             c,
    //             GoldilocksField::MINUS_ONE,
    //         );
    //         let (d, _) = gate.add(&mut cs);
    //         let gate = FmaGateInBaseFieldWithConstant::new(
    //             GoldilocksField::TWO,
    //             (d, d),
    //             a,
    //             GoldilocksField::MINUS_ONE,
    //         );
    //         let (_d, _) = gate.add(&mut cs);
    //     }

    //     log!("Synthesis taken {:?}", now.elapsed());

    //     cs.wait_for_witness();
    // }
}
