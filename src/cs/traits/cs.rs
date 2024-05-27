use super::evaluator::GateConstraintEvaluator;
use super::gate::{Gate, GatePlacementStrategy};
use super::*;
use crate::config::CSWitnessEvaluationConfig;
use crate::cs::toolboxes::gate_config::GateConfigurationHolder;
use crate::cs::toolboxes::static_toolbox::StaticToolboxHolder;
use crate::dag::{CSWitnessValues, WitnessSource};

pub enum DstBuffer<'set, 'tgt: 'set, T> {
    MutSlice(&'set mut [T], usize),
    MutSliceIndirect(&'set mut [&'tgt mut T], bool, usize),
    Vector(&'set mut Vec<T>),
}

impl<'set, 'tgt: 'set, T: SmallField> DstBuffer<'set, 'tgt, T> {
    pub fn push(&mut self, value: T) {
        match self {
            DstBuffer::MutSlice(dst, offset) => {
                dst[*offset] = value;
                *offset += 1;
            }
            DstBuffer::MutSliceIndirect(dst, debug_track, offset) => {
                if cfg!(feature = "debug_track") && *debug_track {
                    log!("   set out {} <- {}", *offset, value.as_raw_u64())
                }

                *dst[*offset] = T::from_u64_unchecked(value.as_u64_reduced());
                *offset += 1;
            }
            DstBuffer::Vector(dst) => {
                dst.push(value);
            }
        }
    }

    pub fn extend<S: IntoIterator<Item = T>>(&mut self, source: S) {
        match self {
            DstBuffer::MutSlice(dst, offset) => {
                for (dst, src) in dst[*offset..].iter_mut().zip(source.into_iter()) {
                    *dst = src;
                    *offset += 1;
                }
            }
            DstBuffer::MutSliceIndirect(dst, _debug_track, offset) => {
                for (dst, src) in dst[*offset..].iter_mut().zip(source.into_iter()) {
                    **dst = T::from_raw_u64_unchecked(src.as_u64_reduced());
                    *offset += 1;
                }
            }
            DstBuffer::Vector(dst) => {
                dst.extend(source);
            }
        }
    }
}

// Read-only proxy
pub trait CSWitnessSource<F: SmallField>: WitnessSource<F> + 'static {}

// Note that we use newtype mechanics to have markers

pub trait ConstraintSystem<F: SmallField>: Send + Sync {
    type Config: CSConfig;
    type WitnessSource: CSWitnessSource<F>;
    type GatesConfig: GateConfigurationHolder<F>;
    type StaticToolbox: StaticToolboxHolder;

    fn get_gates_config(&self) -> &Self::GatesConfig;
    fn get_gates_config_mut(&mut self) -> &mut Self::GatesConfig;

    fn get_static_toolbox(&self) -> &Self::StaticToolbox;
    fn get_static_toolbox_mut(&mut self) -> &mut Self::StaticToolbox;

    // A small note about the logic of CS: witness generation is tough to parallelize, so
    // let's at least boil down the most sequential part into nothing more complex
    // than doing += 1 on some sequential counter

    // we can declare some number of witnesses or variables (here we differentiate
    // by logical meaning), and later on set values
    fn alloc_variable_without_value(&mut self) -> Variable;
    fn alloc_multiple_variables_without_values<const N: usize>(&mut self) -> [Variable; N];
    fn alloc_witness_without_value(&mut self) -> Witness;
    fn alloc_multiple_witnesses_without_values<const N: usize>(&mut self) -> [Witness; N];

    // then in the most generic cases we can declare a values dependency

    fn set_values<const N: usize>(&mut self, places: &[Place; N], values: [F; N]);

    fn set_values_with_dependencies<
        const INS: usize,
        const OUTS: usize,
        FN: FnOnce([F; INS]) -> [F; OUTS] + 'static + Send + Sync,
    >(
        &mut self,
        dependencies: &[Place; INS],
        outputs: &[Place; OUTS],
        value_fn: FN,
    );

    fn set_values_with_dependencies_vararg<
        FN: FnOnce(&[F], &mut DstBuffer<'_, '_, F>) + 'static + Send + Sync,
    >(
        &mut self,
        dependencies: &[Place],
        outputs: &[Place],
        value_fn: FN,
    );

    // all other convenience functions can be expressed through the machinery above

    #[inline]
    fn alloc_single_variable_from_witness(&mut self, witness: F) -> Variable {
        let new_var = self.alloc_variable_without_value();
        if <Self::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
            self.set_values(&[new_var.into()], [witness]);
        }

        new_var
    }

    #[inline]
    fn alloc_multiple_variables_from_witnesses<const N: usize>(
        &mut self,
        witnesses: [F; N],
    ) -> [Variable; N] {
        let new_vars = self.alloc_multiple_variables_without_values::<N>();
        if <Self::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
            self.set_values(&Place::from_variables(new_vars), witnesses);
        }

        new_vars
    }

    // single method to set some location in the trace as publicly exposed
    fn set_public(&mut self, column: usize, row: usize); // instead of allocating it we can name any variable

    fn get_value(&self, place: Place) -> CSWitnessValues<F, 1, Self::WitnessSource>;
    fn get_value_for_multiple<const N: usize>(
        &self,
        for_places: [Place; N],
    ) -> CSWitnessValues<F, N, Self::WitnessSource>;

    // same logic we try to apply for witness variables (non-copiable). During setup phase in the same way we can maintain
    // a map of where each particular witness number W will go in the trace table, but for the hot path in circuit witness generation
    // we want to also degrade it down to just bumping a counter

    #[inline]
    fn alloc_single_witness(&mut self, witness: F) -> Witness {
        let new_var = self.alloc_witness_without_value();
        if <Self::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
            self.set_values(&Place::from_witnesses([new_var]), [witness]);
        }

        new_var
    }

    #[inline]
    fn alloc_multiple_witnesses<const N: usize>(&mut self, witnesses: [F; N]) -> [Witness; N] {
        let new_vars = self.alloc_multiple_witnesses_without_values::<N>();
        if <Self::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == true {
            self.set_values(&Place::from_witnesses(new_vars), witnesses);
        }

        new_vars
    }

    // "Dynamic tooling" relies on type-casting and doesn't product new type of CS when added
    fn add_dynamic_tool<M: 'static + Send + Sync, T: GateTool>(&mut self, tool: T);
    fn get_dynamic_tool<M: 'static + Send + Sync, T: GateTool>(&self) -> Option<&T>;
    fn get_dynamic_tool_mut<M: 'static + Send + Sync, T: GateTool>(&mut self) -> Option<&mut T>;
    fn get_or_create_dynamic_tool<M: 'static + Send + Sync, T: GateTool>(&mut self) -> &T {
        let is_some = self.get_dynamic_tool::<M, T>().is_some();
        if is_some == false {
            let new_tool = T::create();
            self.add_dynamic_tool::<M, T>(new_tool);
        }

        self.get_dynamic_tool::<M, T>().unwrap()
    }
    fn get_or_create_dynamic_tool_mut<M: 'static + Send + Sync, T: GateTool>(&mut self) -> &mut T {
        let is_some = self.get_dynamic_tool::<M, T>().is_some();
        if is_some == false {
            let new_tool = T::create();
            self.add_dynamic_tool::<M, T>(new_tool);
        }

        self.get_dynamic_tool_mut::<M, T>().unwrap()
    }
    // and if we cleanup we can take tool completely
    fn take_dynamic_tool<M: 'static + Send + Sync, T: GateTool>(&mut self) -> Option<T>;

    // provide unified paramters for gates
    fn get_params(&self) -> CSGeometry;
    // and for lookups
    fn get_lookup_params(&self) -> LookupParameters;

    #[inline(always)]
    fn gate_is_allowed<G: Gate<F>>(&self) -> bool {
        self.get_gates_config().is_gate_allowed::<G>()
    }
    #[inline(always)]
    fn get_gate_params<G: Gate<F>>(
        &self,
    ) -> <G::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams {
        self.get_gates_config()
            .get_params::<G>()
            .unwrap_or_else(|| panic!("gate {} must be allowed", std::any::type_name::<G>()))
    }
    #[inline(always)]
    fn get_gate_placement_strategy<G: Gate<F>>(&self) -> GatePlacementStrategy {
        self.get_gates_config()
            .placement_strategy::<G>()
            .unwrap_or_else(|| panic!("gate {} must be allowed", std::any::type_name::<G>()))
    }

    // When we declare a circuit (not just variables, but their concrete locations)
    // we need few things to
    fn next_available_row(&self) -> usize;

    // internal methods to actually place variables in particular places, usable by the gate. Should not be called by user
    // unless you know what you are doing

    // There are for case of "general purpose columns" that may have different gates placed on different rows
    fn place_variable(&mut self, var: Variable, row: usize, column: usize);
    fn place_witness(&mut self, witness: Witness, row: usize, column: usize);
    fn place_gate<G: Gate<F>>(&mut self, gate: &G, row: usize);
    fn place_constants<const N: usize>(&mut self, constants: &[F; N], row: usize, offset: usize);
    fn place_multiple_variables_into_row<const N: usize>(
        &mut self,
        vars: &[Variable; N],
        row: usize,
        starting_column: usize,
    );

    // Also we have the case to place variables into "specialized" columns,
    // where the same gate is applied at every row. Note that we expect the gate itself
    // to maintain a tooling logic to place itself
    fn place_variable_specialized<G: Gate<F>>(
        &mut self,
        var: Variable,
        repetition: usize,
        row: usize,
        column: usize,
    );
    fn place_witness_specialized<G: Gate<F>>(
        &mut self,
        witness: Witness,
        repetition: usize,
        row: usize,
        column: usize,
    );
    fn place_gate_specialized<G: Gate<F>>(&mut self, gate: &G, repetition: usize, row: usize);
    fn place_constants_specialized<G: Gate<F>, const N: usize>(
        &mut self,
        constants: &[F; N],
        repetition: usize,
        row: usize,
        offset: usize,
    );
    fn place_multiple_variables_into_row_specialized<G: Gate<F>, const N: usize>(
        &mut self,
        vars: &[Variable; N],
        repetition: usize,
        row: usize,
        starting_column: usize,
    );

    fn perform_lookup<const KEYS: usize, const VALUES: usize>(
        &mut self,
        table_id: u32,
        keys: &[Variable; KEYS],
    ) -> [Variable; VALUES]
    where
        [(); KEYS + VALUES]:;

    fn enforce_lookup<const N: usize>(&mut self, table_id: u32, keys_and_values: &[Variable; N]);

    // Lookup table related things. We also use newtype markers
    fn add_lookup_table<M: 'static + Send + Sync, const N: usize>(
        &mut self,
        table: LookupTable<F, N>,
    ) -> u32
    where
        LookupTable<F, N>: Wrappable<F>;
    fn get_table_id_for_marker<M: 'static + Send + Sync>(&self) -> Option<u32>;
    fn get_table(&self, table_id: u32) -> std::sync::Arc<LookupTableWrapper<F>>;
}
