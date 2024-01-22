use super::*;
use crate::config::*;
use crate::cs::implementations::evaluator_data::*;
use crate::cs::implementations::setup::FinalizationHintsForProver;
use crate::cs::traits::gate::GateColumnsCleanupFunction;
use crate::cs::traits::gate::GatePlacementStrategy;
use crate::cs::traits::gate::GateRowCleanupFunction;
use crate::dag::CircuitResolver;
use crate::dag::DefaultCircuitResolver;
use crate::dag::NullCircuitResolver;
use std::any::TypeId;
use std::marker::PhantomData;
use std::sync::atomic::AtomicU32;
use std::sync::RwLock;

pub type CSDevelopmentAssembly<F, GC, T, CR> =
    CSReferenceImplementation<F, F, DevCSConfig, GC, T, CR>;
pub type CSSetupAssembly<F, GC, T, CR> = CSReferenceImplementation<F, F, SetupCSConfig, GC, T, CR>;

pub const PADDING_LOOKUP_TABLE_ID_VALUE: u32 = 0;
pub const INITIAL_LOOKUP_TABLE_ID_VALUE: u32 = 1;

pub struct CSReferenceImplementation<
    F: SmallField, // over which we define a circuit
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>, // over whatever we evaluate gates. It can be vectorized type, or circuit variables
    CFG: CSConfig,
    GC: GateConfigurationHolder<F>,
    T: StaticToolboxHolder,
    CR: CircuitResolver<F, CFG::ResolverConfig> = DefaultCircuitResolver<
        F,
        <CFG as CSConfig>::ResolverConfig,
    >,
> {
    pub(crate) parameters: CSGeometry,
    pub(crate) lookup_parameters: LookupParameters,

    pub(crate) next_available_row: usize,
    pub(crate) next_available_place_idx: u64,
    pub(crate) next_lookup_table_index: u32,

    pub(crate) max_trace_len: usize,

    pub(crate) gates_application_sets: Vec<usize>, // index into gates_ordered_set for general-purpose columns

    pub(crate) copy_permutation_data: Vec<Vec<Variable>>, // store column-major order
    pub(crate) witness_placement_data: Vec<Vec<Witness>>, // store column-major order
    pub(crate) constants_requested_per_row: Vec<SmallVec<[F; 8]>>, // for general purpose gates
    pub(crate) constants_for_gates_in_specialized_mode: Vec<Vec<F>>, // for specialized gates we use another mode of placement
    pub(crate) lookup_table_marker_into_id: HashMap<TypeId, u32>,
    pub(crate) lookup_tables: Vec<std::sync::Arc<LookupTableWrapper<F>>>,
    pub(crate) lookup_multiplicities: Vec<std::sync::Arc<Vec<AtomicU32>>>, // per each subarbument (index 0) we have vector of multiplicities for every table

    // NOTE: it's a storage, it knows nothing about GateTool trait to avoid code to go from Box<dyn GateTool> into Box<dyn Any>
    pub(crate) dynamic_tools:
        HashMap<TypeId, (TypeId, Box<dyn std::any::Any + Send + Sync + 'static>)>,
    // pub(crate) variables_storage: RwLock<CircuitResolver<F, dag::sorter_runtime::RuntimeResolverSorter<F, CFG::ResolverConfig>>>,
    pub(crate) variables_storage: RwLock<CR>,

    /// Gate layout hints - we create our CS with only "general purpose" columns,
    /// and then if the gate is added in the specialized columns we should extend our
    /// holders for copy permutation and witness data, as well as know what the offsets are
    /// for the first copy of the evaluator
    pub(crate) evaluation_data_over_general_purpose_columns:
        EvaluationDataOverGeneralPurposeColumns<F, P>,
    pub(crate) evaluation_data_over_specialized_columns: EvaluationDataOverSpecializedColumns<F, P>,

    pub(crate) lookup_marker_gate_idx: Option<u32>,
    pub(crate) table_ids_as_variables: Vec<Variable>,
    pub(crate) public_inputs: Vec<(usize, usize)>,

    pub(crate) specialized_gates_rough_stats: HashMap<TypeId, usize>,

    pub(crate) static_toolbox: T,
    pub(crate) gates_configuration: GC,

    pub(crate) row_cleanups: Vec<GateRowCleanupFunction<Self>>,
    pub(crate) columns_cleanups: Vec<GateColumnsCleanupFunction<Self>>,
}

pub struct CSReferenceAssembly<
    F: SmallField, // over which we define a circuit
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>, // over whatever we evaluate gates. It can be vectorized type, or circuit variables
    CFG: CSConfig,
    CR: CircuitResolver<F, CFG::ResolverConfig> = DefaultCircuitResolver<
        F,
        <CFG as CSConfig>::ResolverConfig,
    >,
> {
    phantom: PhantomData<CFG>,
    pub parameters: CSGeometry,
    pub lookup_parameters: LookupParameters,

    pub(crate) next_available_place_idx: u64,

    pub max_trace_len: usize,

    pub gates_application_sets: Vec<usize>, // index into gates_ordered_set for general-purpose columns

    pub copy_permutation_data: Vec<Vec<Variable>>, // store column-major order
    pub witness_placement_data: Vec<Vec<Witness>>, // store column-major order
    pub constants_requested_per_row: Vec<SmallVec<[F; 8]>>, // for general purpose gates
    pub constants_for_gates_in_specialized_mode: Vec<Vec<F>>, // for specialized gates we use another mode of placement
    pub lookup_tables: Vec<std::sync::Arc<LookupTableWrapper<F>>>,
    pub lookup_multiplicities: Vec<std::sync::Arc<Vec<AtomicU32>>>, // per each subarbument (index 0) we have vector of multiplicities for every table

    pub variables_storage: RwLock<CR>,

    pub evaluation_data_over_general_purpose_columns: EvaluationDataOverGeneralPurposeColumns<F, P>,
    pub evaluation_data_over_specialized_columns: EvaluationDataOverSpecializedColumns<F, P>,

    pub specialized_gates_rough_stats: HashMap<TypeId, usize>,

    pub public_inputs: Vec<(usize, usize)>,

    pub placement_strategies: HashMap<TypeId, GatePlacementStrategy>,
}

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        CFG: CSConfig,
        GC: GateConfigurationHolder<F>,
        T: StaticToolboxHolder,
        CR: CircuitResolver<F, CFG::ResolverConfig>,
    > CSReferenceImplementation<F, P, CFG, GC, T, CR>
{
    pub(crate) fn lookups_tables_total_len(&self) -> usize {
        self.lookup_tables.iter().map(|el| el.table_size()).sum()
    }

    #[inline]
    pub fn num_sublookup_arguments(&self) -> usize {
        self.lookup_parameters
            .num_sublookup_arguments_for_geometry(&self.parameters)
    }

    #[inline]
    pub fn num_multipicities_polys(&self) -> usize {
        self.lookup_parameters
            .num_multipicities_polys(self.lookups_tables_total_len(), self.max_trace_len)
    }

    pub fn into_assembly(self) -> CSReferenceAssembly<F, P, CFG, CR> {
        let Self {
            parameters,
            lookup_parameters,
            next_available_place_idx,
            max_trace_len,
            gates_application_sets,
            copy_permutation_data,
            witness_placement_data,
            constants_requested_per_row,
            constants_for_gates_in_specialized_mode,
            lookup_tables,
            lookup_multiplicities,
            variables_storage,
            specialized_gates_rough_stats,
            public_inputs,
            gates_configuration,
            evaluation_data_over_general_purpose_columns,
            evaluation_data_over_specialized_columns,
            ..
        } = self;

        let capacity = evaluation_data_over_specialized_columns
            .evaluators_over_specialized_columns
            .len();
        let mut placement_strategies = HashMap::with_capacity(capacity);

        for gate_type_id in evaluation_data_over_specialized_columns
            .gate_type_ids_for_specialized_columns
            .iter()
        {
            let placement_strategy = gates_configuration
                .placement_strategy_for_type_id(*gate_type_id)
                .expect("gate must be allowed");
            placement_strategies.insert(*gate_type_id, placement_strategy);
        }

        CSReferenceAssembly::<F, P, CFG, CR> {
            phantom: PhantomData,
            parameters,
            lookup_parameters,
            next_available_place_idx,
            max_trace_len,
            gates_application_sets,
            copy_permutation_data,
            witness_placement_data,
            constants_requested_per_row,
            constants_for_gates_in_specialized_mode,
            lookup_tables,
            lookup_multiplicities,
            variables_storage,
            specialized_gates_rough_stats,
            evaluation_data_over_general_purpose_columns,
            evaluation_data_over_specialized_columns,
            public_inputs,
            placement_strategies,
        }
    }

    /// Uses finalization hint to set max trace length mainly, and public input locations,
    /// so we only create assembly, put NO witness into it, and use external witness source
    /// to prove the same circuit over and over
    pub fn into_assembly_for_repeated_proving(
        mut self,
        hint: &FinalizationHintsForProver,
    ) -> CSReferenceAssembly<F, P, CFG, NullCircuitResolver<F, CFG::ResolverConfig>> {
        assert_eq!(
            self.next_available_place_idx, 0,
            "it's not necessary to synthesize a circuit into this CS for proving"
        );

        self.public_inputs = hint.public_inputs.clone();
        self.max_trace_len = hint.final_trace_len;

        let Self {
            parameters,
            lookup_parameters,
            next_available_place_idx,
            max_trace_len,
            gates_application_sets,
            copy_permutation_data,
            witness_placement_data,
            constants_requested_per_row,
            constants_for_gates_in_specialized_mode,
            lookup_tables,
            lookup_multiplicities,
            specialized_gates_rough_stats,
            public_inputs,
            gates_configuration,
            evaluation_data_over_general_purpose_columns,
            evaluation_data_over_specialized_columns,
            ..
        } = self;

        let capacity = evaluation_data_over_specialized_columns
            .evaluators_over_specialized_columns
            .len();
        let mut placement_strategies = HashMap::with_capacity(capacity);

        for gate_type_id in evaluation_data_over_specialized_columns
            .gate_type_ids_for_specialized_columns
            .iter()
        {
            let placement_strategy = gates_configuration
                .placement_strategy_for_type_id(*gate_type_id)
                .expect("gate must be allowed");
            placement_strategies.insert(*gate_type_id, placement_strategy);
        }

        let variables_storage = std::sync::RwLock::new(NullCircuitResolver::new(()));

        CSReferenceAssembly::<F, P, CFG, NullCircuitResolver<F, CFG::ResolverConfig>> {
            phantom: PhantomData,
            parameters,
            lookup_parameters,
            next_available_place_idx,
            max_trace_len,
            gates_application_sets,
            copy_permutation_data,
            witness_placement_data,
            constants_requested_per_row,
            constants_for_gates_in_specialized_mode,
            lookup_tables,
            lookup_multiplicities,
            variables_storage,
            specialized_gates_rough_stats,
            evaluation_data_over_general_purpose_columns,
            evaluation_data_over_specialized_columns,
            public_inputs,
            placement_strategies,
        }
    }
}

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        CFG: CSConfig,
        CR: CircuitResolver<F, CFG::ResolverConfig>,
    > CSReferenceAssembly<F, P, CFG, CR>
{
    pub(crate) fn lookups_tables_total_len(&self) -> usize {
        self.lookup_tables.iter().map(|el| el.table_size()).sum()
    }

    #[inline]
    pub fn num_sublookup_arguments(&self) -> usize {
        self.lookup_parameters
            .num_sublookup_arguments_for_geometry(&self.parameters)
    }

    #[inline]
    pub fn num_multipicities_polys(&self) -> usize {
        self.lookup_parameters
            .num_multipicities_polys(self.lookups_tables_total_len(), self.max_trace_len)
    }

    #[inline]
    pub fn next_available_place_idx(&self) -> u64 {
        self.next_available_place_idx
    }
}
