use super::proof::Proof;
use super::transcript::Transcript;
use super::*;

use crate::cs::oracle::merkle_tree::MerkleTreeWithCap;
use crate::cs::oracle::TreeHasher;

use crate::cs::toolboxes::gate_config::GateConfigurationHolder;
use crate::cs::toolboxes::static_toolbox::StaticToolboxHolder;
use crate::cs::traits::evaluator::GatePlacementType;
use crate::cs::traits::evaluator::GatePurpose;
use crate::cs::traits::evaluator::PerChunkOffset;
use crate::cs::traits::evaluator::*;
use crate::cs::traits::gate::GatePlacementStrategy;
use crate::cs::traits::trace_source::TraceSourceDerivable;
use crate::field::Field;
use crate::field::PrimeField;
use std::any::TypeId;

use crate::cs::gates::lookup_marker::*;
use crate::cs::implementations::setup::TreeNode;
use std::alloc::Global;
use std::ops::Range;

use crate::cs::implementations::pow::PoWRunner;
use crate::field::ExtensionField;
use crate::field::FieldExtension;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Hash, PartialEq, Eq)]
pub struct VerificationKey<F: SmallField, H: TreeHasher<F>> {
    // fixed parameters of the circuit
    pub fixed_parameters: VerificationKeyCircuitGeometry,
    #[serde(bound(serialize = "H::Output: serde::Serialize"))]
    #[serde(bound(deserialize = "H::Output: serde::de::DeserializeOwned"))]
    pub setup_merkle_tree_cap: Vec<H::Output>,
}

impl<F: SmallField, H: TreeHasher<F>> Default for VerificationKey<F, H> {
    fn default() -> Self {
        Self {
            fixed_parameters: VerificationKeyCircuitGeometry::placeholder(),
            setup_merkle_tree_cap: vec![],
        }
    }
}

impl<F: SmallField, H: TreeHasher<F>> VerificationKey<F, H> {
    pub fn transmute_to_another_formal_hasher<HH: TreeHasher<F, Output = H::Output>>(
        self,
    ) -> VerificationKey<F, HH> {
        let Self {
            fixed_parameters,
            setup_merkle_tree_cap,
        } = self;

        VerificationKey::<F, HH> {
            fixed_parameters,
            setup_merkle_tree_cap: setup_merkle_tree_cap as Vec<HH::Output>,
        }
    }
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Hash, PartialEq, Eq)]
pub struct VerificationKeyCircuitGeometry {
    // fixed parameters of the circuit
    pub parameters: CSGeometry,
    pub lookup_parameters: LookupParameters,
    pub domain_size: u64,
    pub total_tables_len: u64,
    pub public_inputs_locations: Vec<(usize, usize)>,
    pub extra_constant_polys_for_selectors: usize,
    pub table_ids_column_idxes: Vec<usize>,
    pub quotient_degree: usize,
    pub selectors_placement: TreeNode,
    pub fri_lde_factor: usize,
    pub cap_size: usize,
}

impl VerificationKeyCircuitGeometry {
    pub(crate) fn placeholder() -> Self {
        Self {
            parameters: CSGeometry {
                num_columns_under_copy_permutation: 0,
                num_witness_columns: 0,
                num_constant_columns: 0,
                max_allowed_constraint_degree: 0,
            },
            lookup_parameters: LookupParameters::NoLookup,
            domain_size: 0,
            total_tables_len: 0,
            public_inputs_locations: Vec::new(),
            extra_constant_polys_for_selectors: 0,
            table_ids_column_idxes: Vec::new(),
            quotient_degree: 0,
            selectors_placement: TreeNode::Empty,
            fri_lde_factor: 0,
            cap_size: 0,
        }
    }

    pub fn num_public_inputs(&self) -> usize {
        self.public_inputs_locations.len()
    }

    pub fn public_inputs_locations_batched_by_opening(&self) -> Vec<(u32, Vec<usize>)> {
        let mut result = vec![];
        for (column, row) in self.public_inputs_locations.iter().copied() {
            assert!(row <= u32::MAX as usize);

            let pos = result
                .iter()
                .position(|el: &(u32, Vec<usize>)| el.0 == row as u32);
            if let Some(pos) = pos {
                result[pos].1.push(column);
            } else {
                result.push((row as u32, vec![column]));
            }
        }

        result
    }

    pub fn base_oracles_depth(&self) -> usize {
        assert!(self.cap_size.is_power_of_two());
        let lde_domain_size = self.domain_size * (self.fri_lde_factor as u64);
        let full_depth = lde_domain_size.trailing_zeros();
        // reduce by cap size
        let cut_depth = full_depth - self.cap_size.trailing_zeros();

        cut_depth as usize
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct VerifierPolyStorage<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
> {
    pub variables: Vec<P>,
    pub witnesses: Vec<P>,
    pub constants: Vec<P>,
    pub constants_offset: usize,
    pub chunk_offset: PerChunkOffset,
    pub _marker: std::marker::PhantomData<F>,
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLike<Base = F>>
    VerifierPolyStorage<F, P>
{
    pub const fn new(variables: Vec<P>, witnesses: Vec<P>, constants: Vec<P>) -> Self {
        Self {
            variables,
            witnesses,
            constants,
            constants_offset: 0,
            chunk_offset: PerChunkOffset::zero(),
            _marker: std::marker::PhantomData,
        }
    }

    pub fn subset(
        &self,
        variables_range: Range<usize>,
        witness_range: Range<usize>,
        constants_range: Range<usize>,
    ) -> Self {
        let variables = self.variables[variables_range].to_vec();
        let witnesses = self.witnesses[witness_range].to_vec();
        let constants = self.constants[constants_range].to_vec();

        Self {
            variables,
            witnesses,
            constants,
            constants_offset: 0,
            chunk_offset: PerChunkOffset::zero(),
            _marker: std::marker::PhantomData,
        }
    }
}

use crate::cs::traits::GoodAllocator;

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLike<Base = F>> TraceSource<F, P>
    for VerifierPolyStorage<F, P>
{
    fn get_constant_value(&self, constant_idx: usize) -> P {
        self.constants[self.constants_offset + self.chunk_offset.constants_offset + constant_idx]
    }

    fn get_variable_value(&self, variable_idx: usize) -> P {
        self.variables[self.chunk_offset.variables_offset + variable_idx]
    }

    fn get_witness_value(&self, witness_idx: usize) -> P {
        self.witnesses[self.chunk_offset.witnesses_offset + witness_idx]
    }

    fn dump_current_row<C: GoodAllocator>(&self, dst: &mut Vec<P, C>) {
        dst.extend_from_slice(&self.variables);
        dst.extend_from_slice(&self.witnesses);
        dst.extend_from_slice(&self.constants);
    }
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLike<Base = F>>
    TraceSourceDerivable<F, P> for VerifierPolyStorage<F, P>
{
    fn num_iterations(&self) -> usize {
        1
    }
    fn advance(&mut self) {}
    fn reset_gate_chunk_offset(&mut self) {
        self.chunk_offset = PerChunkOffset::zero();
    }
    fn offset_for_next_chunk(&mut self, chunk_offset: &PerChunkOffset) {
        self.chunk_offset.add_offset(chunk_offset);
    }
    fn set_constants_offset(&mut self, offset: usize) {
        self.constants_offset = offset;
    }
}

use crate::cs::traits::destination_view::{EvaluationDestination, EvaluationDestinationDrivable};
use crate::gpu_synthesizer::get_evaluator_name;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct VerifierRelationDestination<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
> {
    pub accumulator: P,
    pub selector_value: P,
    pub challenges: Vec<P>,
    pub current_challenge_offset: usize,
    pub _marker: std::marker::PhantomData<F>,
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLike<Base = F>>
    EvaluationDestination<F, P> for VerifierRelationDestination<F, P>
{
    #[inline(always)]
    fn push_evaluation_result(&mut self, value: P, ctx: &mut P::Context) {
        P::mul_and_accumulate_into(
            &mut self.accumulator,
            &value,
            &self.challenges[self.current_challenge_offset],
            ctx,
        );

        // let mut value = value;
        // value.mul_assign(&self.challenges[self.current_challenge_offset], ctx);
        // self.accumulator.add_assign(&value, ctx);

        self.current_challenge_offset += 1;
    }
}

impl<F: PrimeField, P: field::traits::field_like::PrimeFieldLike<Base = F>>
    EvaluationDestinationDrivable<F, P> for VerifierRelationDestination<F, P>
{
    #[inline]
    fn expected_num_iterations(&self) -> usize {
        1
    }
    #[inline(always)]
    fn advance(&mut self, ctx: &mut P::Context) {
        self.accumulator.mul_assign(&self.selector_value, ctx);
    }
}

// our path is a set of booleans true/false, and encode from the root,
// so when we even encounter a path, we can check for all it's ascendants
pub fn compute_selector_subpath_at_z<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
>(
    path: Vec<bool>,
    buffer: &mut HashMap<Vec<bool>, P>,
    constant_polys_evaluations: &[P],
    ctx: &mut P::Context,
) {
    if buffer.contains_key(&path) {
        return;
    }
    if path.len() == 0 {
        return;
    }

    let constant_poly_idx = path.len() - 1;

    if path.len() == 1 {
        // we need to read from setup and just place it,
        // as we are somewhat "root" node
        let poly = &constant_polys_evaluations[constant_poly_idx];
        if path[0] == false {
            // we have to compute (1 - poly)
            let mut result = P::one(ctx);
            result.sub_assign(poly, ctx);

            let existing = buffer.insert(path, result);
            debug_assert!(existing.is_none());
        } else {
            // we can use just an existing poly
            let existing = buffer.insert(path, *poly);
            debug_assert!(existing.is_none());
        }

        // since we are at the root we do not need to continue
        return;
    }

    // now we are in "child" only mode

    let mut parent_prefix = path.clone();
    let final_element = parent_prefix.pop().unwrap();
    if parent_prefix.is_empty() == false {
        // compute it's parents first
        compute_selector_subpath_at_z(
            parent_prefix.clone(),
            buffer,
            constant_polys_evaluations,
            ctx,
        );
    }

    // now we evaluated all prefixes and can add one here on top
    let prefix_poly = buffer.get(&parent_prefix).expect("must be computed");
    let other_poly = &constant_polys_evaluations[constant_poly_idx];

    let result = if final_element == false {
        // we need prefix * (1 - this)
        let mut result = P::one(ctx);
        result.sub_assign(other_poly, ctx);
        result.mul_assign(prefix_poly, ctx);

        result
    } else {
        // we need prefix * this
        let mut result = *other_poly;
        result.mul_assign(prefix_poly, ctx);

        result
    };

    let existing = buffer.insert(path, result);
    debug_assert!(existing.is_none());
}

pub struct VerifierProxy<
    F: SmallField,
    EXT: FieldExtension<2, BaseField = F>,
    GC: GateConfigurationHolder<F>,
    T: StaticToolboxHolder,
> {
    // when we init we get the following from VK
    pub parameters: CSGeometry,
    pub lookup_parameters: LookupParameters,

    pub gates_configuration: GC,
    pub(crate) gate_type_ids_for_specialized_columns: Vec<TypeId>,
    pub(crate) evaluators_over_specialized_columns:
        Vec<TypeErasedGateEvaluationVerificationFunction<F, EXT>>,
    pub(crate) offsets_for_specialized_evaluators: Vec<(PerChunkOffset, PerChunkOffset, usize)>,

    // pub(crate) gate_type_ids_for_general_purpose_columns: Vec<TypeId>,
    pub(crate) evaluators_over_general_purpose_columns:
        Vec<TypeErasedGateEvaluationVerificationFunction<F, EXT>>,
    pub(crate) general_purpose_evaluators_comparison_functions:
        HashMap<TypeId, Vec<(GateBatchEvaluationComparisonFunction, usize)>>,

    pub(crate) total_num_variables_for_specialized_columns: usize,
    pub(crate) total_num_witnesses_for_specialized_columns: usize,
    pub(crate) total_num_constants_for_specialized_columns: usize,

    pub(crate) _marker: std::marker::PhantomData<T>,
}

impl<
        F: SmallField,
        EXT: FieldExtension<2, BaseField = F>,
        GC: GateConfigurationHolder<F>,
        T: StaticToolboxHolder,
    > VerifierProxy<F, EXT, GC, T>
{
    pub fn into_verifier(self) -> Verifier<F, EXT> {
        let Self {
            parameters,
            lookup_parameters,
            gates_configuration,
            gate_type_ids_for_specialized_columns,
            evaluators_over_specialized_columns,
            offsets_for_specialized_evaluators,
            evaluators_over_general_purpose_columns,
            total_num_variables_for_specialized_columns,
            total_num_witnesses_for_specialized_columns,
            total_num_constants_for_specialized_columns,
            ..
        } = self;

        // capture small pieces of information from the gate configuration
        assert_eq!(
            evaluators_over_specialized_columns.len(),
            gate_type_ids_for_specialized_columns.len()
        );

        let capacity = evaluators_over_specialized_columns.len();
        let mut placement_strategies = HashMap::with_capacity(capacity);

        for gate_type_id in gate_type_ids_for_specialized_columns.iter() {
            let placement_strategy = gates_configuration
                .placement_strategy_for_type_id(*gate_type_id)
                .expect("gate must be allowed");
            placement_strategies.insert(*gate_type_id, placement_strategy);
        }

        Verifier::<F, EXT> {
            parameters,
            lookup_parameters,
            gate_type_ids_for_specialized_columns,
            evaluators_over_specialized_columns,
            offsets_for_specialized_evaluators,
            evaluators_over_general_purpose_columns,
            total_num_variables_for_specialized_columns,
            total_num_witnesses_for_specialized_columns,
            total_num_constants_for_specialized_columns,
            placement_strategies,
        }
    }
}

pub struct Verifier<F: SmallField, EXT: FieldExtension<2, BaseField = F>> {
    // when we init we get the following from VK
    pub parameters: CSGeometry,
    pub lookup_parameters: LookupParameters,

    pub gate_type_ids_for_specialized_columns: Vec<TypeId>,
    pub evaluators_over_specialized_columns:
        Vec<TypeErasedGateEvaluationVerificationFunction<F, EXT>>,
    pub offsets_for_specialized_evaluators: Vec<(PerChunkOffset, PerChunkOffset, usize)>,

    // pub(crate) gate_type_ids_for_general_purpose_columns: Vec<TypeId>,
    pub evaluators_over_general_purpose_columns:
        Vec<TypeErasedGateEvaluationVerificationFunction<F, EXT>>,

    pub total_num_variables_for_specialized_columns: usize,
    pub total_num_witnesses_for_specialized_columns: usize,
    pub total_num_constants_for_specialized_columns: usize,

    pub placement_strategies: HashMap<TypeId, GatePlacementStrategy>,
}

// we can implement a verifier that drives the procedure itself as a CS, so we can easily add gates
// to it, that contains all the information we need

#[derive(Derivative)]
#[derivative(Debug)]
pub struct TypeErasedGateEvaluationVerificationFunction<
    F: SmallField,
    EXT: FieldExtension<2, BaseField = F>,
> {
    pub debug_name: String,
    pub unique_name: String,
    pub evaluator_type_id: TypeId,
    pub gate_purpose: GatePurpose,
    pub max_constraint_degree: usize,
    pub num_quotient_terms: usize,
    pub num_required_constants: usize,
    pub total_quotient_terms_over_all_repetitions: usize,
    pub num_repetitions_on_row: usize,
    pub placement_type: GatePlacementType,
    #[derivative(Debug = "ignore")]
    pub(crate) columnwise_satisfiability_function: Option<
        Box<
            dyn GenericDynamicEvaluatorOverSpecializedColumns<
                    F,
                    ExtensionField<F, 2, EXT>,
                    VerifierPolyStorage<F, ExtensionField<F, 2, EXT>>,
                    VerifierRelationDestination<F, ExtensionField<F, 2, EXT>>,
                >
                + 'static
                + Send
                + Sync,
        >,
    >,
    #[derivative(Debug = "ignore")]
    pub(crate) rowwise_satisfiability_function: Option<
        Box<
            dyn GenericDynamicEvaluatorOverGeneralPurposeColumns<
                    F,
                    ExtensionField<F, 2, EXT>,
                    VerifierPolyStorage<F, ExtensionField<F, 2, EXT>>,
                    VerifierRelationDestination<F, ExtensionField<F, 2, EXT>>,
                >
                + 'static
                + Send
                + Sync,
        >,
    >,
}

impl<F: SmallField, EXT: FieldExtension<2, BaseField = F>>
    TypeErasedGateEvaluationVerificationFunction<F, EXT>
{
    pub fn from_evaluator<E: GateConstraintEvaluator<F>>(
        evaluator: E,
        geometry: &CSGeometry,
        placement_strategy: GatePlacementStrategy,
    ) -> (Self, GateBatchEvaluationComparisonFunction) {
        let debug_name = evaluator.instance_name();
        let unique_name = get_evaluator_name(&evaluator);
        let evaluator_type_id = std::any::TypeId::of::<E>();
        let gate_purpose = E::gate_purpose();
        let max_constraint_degree = E::max_constraint_degree();
        let num_quotient_terms = E::num_quotient_terms();
        let num_required_constants = evaluator.num_required_constants_in_geometry(geometry);
        let placement_type = evaluator.placement_type();
        let mut final_per_chunk_offset = PerChunkOffset::zero();
        let (num_repetitions_on_row, total_quotient_terms_over_all_repetitions) =
            match placement_strategy {
                GatePlacementStrategy::UseGeneralPurposeColumns => {
                    let num_repetitions_on_row = evaluator.num_repetitions_in_geometry(geometry);
                    if let GatePlacementType::MultipleOnRow { per_chunk_offset } = &placement_type {
                        debug_assert!(
                            num_repetitions_on_row > 0,
                            "invalid for evaluator {}",
                            std::any::type_name::<E>()
                        );
                        final_per_chunk_offset = *per_chunk_offset;
                    } else {
                        debug_assert_eq!(num_repetitions_on_row, 1);
                    }

                    let total_quotient_terms_in_geometry =
                        evaluator.total_quotient_terms_in_geometry(geometry);

                    (num_repetitions_on_row, total_quotient_terms_in_geometry)
                }
                GatePlacementStrategy::UseSpecializedColumns {
                    num_repetitions,
                    share_constants,
                } => {
                    let principal_width = evaluator.instance_width();
                    final_per_chunk_offset = PerChunkOffset {
                        variables_offset: principal_width.num_variables,
                        witnesses_offset: principal_width.num_witnesses,
                        constants_offset: principal_width.num_constants,
                    };
                    if share_constants {
                        final_per_chunk_offset.constants_offset = 0;
                    }

                    (num_repetitions, num_repetitions * num_quotient_terms)
                }
            };

        let (specialized_satisfiability_evaluator, general_purpose_satisfiability_evaluator) =
            match placement_strategy {
                GatePlacementStrategy::UseSpecializedColumns { .. } => {
                    let specialized_evaluator = GenericColumnwiseEvaluator {
                        evaluator: evaluator.clone(),
                        global_constants: evaluator.create_global_constants(&mut ()),
                        num_repetitions: num_repetitions_on_row,
                        per_chunk_offset: final_per_chunk_offset,
                    };

                    // dbg!(&specialized_evaluator);

                    (
                        Some(Box::new(specialized_evaluator)
                            as Box<
                                dyn GenericDynamicEvaluatorOverSpecializedColumns<
                                        F,
                                        ExtensionField<F, 2, EXT>,
                                        VerifierPolyStorage<F, ExtensionField<F, 2, EXT>>,
                                        VerifierRelationDestination<F, ExtensionField<F, 2, EXT>>,
                                    >
                                    + 'static
                                    + Send
                                    + Sync,
                            >),
                        None,
                    )
                }
                GatePlacementStrategy::UseGeneralPurposeColumns => {
                    let general_purpose_evaluator = GenericRowwiseEvaluator {
                        evaluator: evaluator.clone(),
                        global_constants: evaluator.create_global_constants(&mut ()),
                        num_repetitions: num_repetitions_on_row,
                        per_chunk_offset: final_per_chunk_offset,
                    };

                    // dbg!(&general_purpose_evaluator);

                    (
                        None,
                        Some(Box::new(general_purpose_evaluator)
                            as Box<
                                dyn GenericDynamicEvaluatorOverGeneralPurposeColumns<
                                        F,
                                        ExtensionField<F, 2, EXT>,
                                        VerifierPolyStorage<F, ExtensionField<F, 2, EXT>>,
                                        VerifierRelationDestination<F, ExtensionField<F, 2, EXT>>,
                                    >
                                    + 'static
                                    + Send
                                    + Sync,
                            >),
                    )
                }
            };

        let this_params = evaluator.unique_params();

        let comparison_fn = move |other_evaluator: &dyn std::any::Any| -> bool {
            assert_eq!(other_evaluator.type_id(), evaluator_type_id);
            let other_evaluator: &E = other_evaluator.downcast_ref().expect("must downcast");

            this_params == other_evaluator.unique_params()
        };

        let comparator = GateBatchEvaluationComparisonFunction {
            type_id: evaluator_type_id,
            evaluator_dyn: Box::new(evaluator),
            equality_fn: Box::new(comparison_fn),
        };

        let new = Self {
            debug_name,
            unique_name,
            evaluator_type_id,
            gate_purpose,
            max_constraint_degree,
            num_quotient_terms,
            num_required_constants,
            total_quotient_terms_over_all_repetitions,
            num_repetitions_on_row,
            placement_type,
            columnwise_satisfiability_function: specialized_satisfiability_evaluator,
            rowwise_satisfiability_function: general_purpose_satisfiability_evaluator,
        };

        (new, comparator)
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Default(bound = ""))]
pub struct SizeCalculator<F: SmallField, const N: usize, EXT: FieldExtension<N, BaseField = F>> {
    _marker: std::marker::PhantomData<(F, EXT)>,
}

impl<F: SmallField, const N: usize, EXT: FieldExtension<N, BaseField = F>>
    SizeCalculator<F, N, EXT>
{
    #[inline]
    pub fn num_sublookup_arguments(
        geometry: &CSGeometry,
        lookup_parameters: &LookupParameters,
    ) -> usize {
        match lookup_parameters {
            LookupParameters::NoLookup => 0,
            LookupParameters::TableIdAsVariable { width, .. } => {
                let principal_width = (*width as usize) + 1;
                geometry.num_columns_under_copy_permutation / principal_width
            }
            LookupParameters::TableIdAsConstant { width, .. } => {
                let principal_width = *width as usize;
                geometry.num_columns_under_copy_permutation / principal_width
            }
            LookupParameters::UseSpecializedColumnsWithTableIdAsVariable {
                num_repetitions,
                ..
            } => *num_repetitions,
            LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                num_repetitions,
                ..
            } => *num_repetitions,
        }
    }

    #[inline]
    pub fn num_multipicities_polys(
        lookup_parameters: &LookupParameters,
        total_tables_len: usize,
        domain_size: u64,
    ) -> usize {
        lookup_parameters.num_multipicities_polys(total_tables_len, domain_size as usize)
    }

    pub fn num_variable_polys(
        geometry: &CSGeometry,
        total_num_variables_for_specialized_columns: usize,
    ) -> usize {
        geometry.num_columns_under_copy_permutation + total_num_variables_for_specialized_columns
    }

    pub fn num_witness_polys(
        geometry: &CSGeometry,
        total_num_witnesses_for_specialized_columns: usize,
    ) -> usize {
        geometry.num_witness_columns + total_num_witnesses_for_specialized_columns
    }

    pub fn num_constant_polys(
        geometry: &CSGeometry,
        vk_fixed_params: &VerificationKeyCircuitGeometry,
        total_num_constants_for_specialized_columns: usize,
    ) -> usize {
        geometry.num_constant_columns
            + vk_fixed_params.extra_constant_polys_for_selectors
            + total_num_constants_for_specialized_columns
    }

    pub fn quotient_degree(vk_fixed_params: &VerificationKeyCircuitGeometry) -> usize {
        vk_fixed_params.quotient_degree
    }

    pub fn num_copy_permutation_polys(
        geometry: &CSGeometry,
        total_num_variables_for_specialized_columns: usize,
    ) -> usize {
        Self::num_variable_polys(geometry, total_num_variables_for_specialized_columns)
    }

    pub fn num_lookup_table_setup_polys(lookup_parameters: &LookupParameters) -> usize {
        if lookup_parameters.lookup_is_allowed() {
            lookup_parameters.lookup_width() + 1
        } else {
            0
        }
    }

    pub fn witness_leaf_size(
        geometry: &CSGeometry,
        lookup_parameters: &LookupParameters,
        vk_fixed_params: &VerificationKeyCircuitGeometry,
        total_num_variables_for_specialized_columns: usize,
        total_num_witnesses_for_specialized_columns: usize,
    ) -> usize {
        Self::num_variable_polys(geometry, total_num_variables_for_specialized_columns)
            + Self::num_witness_polys(geometry, total_num_witnesses_for_specialized_columns)
            + Self::num_multipicities_polys(
                lookup_parameters,
                vk_fixed_params.total_tables_len as usize,
                vk_fixed_params.domain_size,
            )
    }

    pub fn stage_2_leaf_size(
        geometry: &CSGeometry,
        lookup_parameters: &LookupParameters,
        vk_fixed_params: &VerificationKeyCircuitGeometry,
        total_num_variables_for_specialized_columns: usize,
    ) -> usize {
        use crate::cs::implementations::copy_permutation::num_intermediate_partial_product_relations;
        let num_copy_permutation_polys =
            Self::num_variable_polys(geometry, total_num_variables_for_specialized_columns);
        let quotient_degree = Self::quotient_degree(vk_fixed_params);
        let num_intermediate_partial_product_relations =
            num_intermediate_partial_product_relations(num_copy_permutation_polys, quotient_degree);

        let num_polys = 1
            + num_intermediate_partial_product_relations
            + Self::num_sublookup_arguments(geometry, lookup_parameters)
            + Self::num_multipicities_polys(
                lookup_parameters,
                vk_fixed_params.total_tables_len as usize,
                vk_fixed_params.domain_size,
            );

        num_polys * N // in extension
    }

    pub fn quotient_leaf_size(vk_fixed_params: &VerificationKeyCircuitGeometry) -> usize {
        Self::quotient_degree(vk_fixed_params) * N // we are in extension
    }

    pub fn setup_leaf_size(
        geometry: &CSGeometry,
        lookup_parameters: &LookupParameters,
        vk_fixed_params: &VerificationKeyCircuitGeometry,
        total_num_variables_for_specialized_columns: usize,
        total_num_constants_for_specialized_columns: usize,
    ) -> usize {
        let num_copy_permutation_polys =
            Self::num_variable_polys(geometry, total_num_variables_for_specialized_columns);

        num_copy_permutation_polys
            + Self::num_constant_polys(
                geometry,
                vk_fixed_params,
                total_num_constants_for_specialized_columns,
            )
            + Self::num_lookup_table_setup_polys(lookup_parameters)
    }
}

impl<F: SmallField, EXT: FieldExtension<2, BaseField = F>> Verifier<F, EXT> {
    #[inline]
    pub fn num_sublookup_arguments(&self) -> usize {
        SizeCalculator::<F, 2, EXT>::num_sublookup_arguments(
            &self.parameters,
            &self.lookup_parameters,
        )
    }

    #[inline]
    pub fn num_multipicities_polys(&self, total_tables_len: usize, domain_size: u64) -> usize {
        SizeCalculator::<F, 2, EXT>::num_multipicities_polys(
            &self.lookup_parameters,
            total_tables_len,
            domain_size,
        )
    }

    pub fn num_variable_polys(&self) -> usize {
        SizeCalculator::<F, 2, EXT>::num_variable_polys(
            &self.parameters,
            self.total_num_variables_for_specialized_columns,
        )
    }

    pub fn num_witness_polys(&self) -> usize {
        SizeCalculator::<F, 2, EXT>::num_witness_polys(
            &self.parameters,
            self.total_num_witnesses_for_specialized_columns,
        )
    }

    pub fn num_constant_polys(&self, vk_fixed_params: &VerificationKeyCircuitGeometry) -> usize {
        SizeCalculator::<F, 2, EXT>::num_constant_polys(
            &self.parameters,
            vk_fixed_params,
            self.total_num_constants_for_specialized_columns,
        )
    }

    pub fn quotient_degree(&self, vk_fixed_params: &VerificationKeyCircuitGeometry) -> usize {
        SizeCalculator::<F, 2, EXT>::quotient_degree(vk_fixed_params)
    }

    pub fn num_copy_permutation_polys(&self) -> usize {
        self.num_variable_polys()
    }

    pub fn num_lookup_table_setup_polys(&self) -> usize {
        SizeCalculator::<F, 2, EXT>::num_lookup_table_setup_polys(&self.lookup_parameters)
    }

    pub fn witness_leaf_size(&self, vk_fixed_params: &VerificationKeyCircuitGeometry) -> usize {
        SizeCalculator::<F, 2, EXT>::witness_leaf_size(
            &self.parameters,
            &self.lookup_parameters,
            vk_fixed_params,
            self.total_num_variables_for_specialized_columns,
            self.total_num_witnesses_for_specialized_columns,
        )
    }

    pub fn stage_2_leaf_size(&self, vk_fixed_params: &VerificationKeyCircuitGeometry) -> usize {
        SizeCalculator::<F, 2, EXT>::stage_2_leaf_size(
            &self.parameters,
            &self.lookup_parameters,
            vk_fixed_params,
            self.total_num_variables_for_specialized_columns,
        )
    }

    pub fn quotient_leaf_size(&self, vk_fixed_params: &VerificationKeyCircuitGeometry) -> usize {
        SizeCalculator::<F, 2, EXT>::quotient_leaf_size(vk_fixed_params)
    }

    pub fn setup_leaf_size(&self, vk_fixed_params: &VerificationKeyCircuitGeometry) -> usize {
        SizeCalculator::<F, 2, EXT>::setup_leaf_size(
            &self.parameters,
            &self.lookup_parameters,
            vk_fixed_params,
            self.total_num_variables_for_specialized_columns,
            self.total_num_constants_for_specialized_columns,
        )
    }

    pub fn verify<
        H: TreeHasher<F>,
        TR: Transcript<F, CompatibleCap = H::Output>,
        POW: PoWRunner,
    >(
        &self,
        transcript_params: TR::TransciptParameters,
        vk: &VerificationKey<F, H>,
        proof: &Proof<F, H, EXT>,
    ) -> bool {
        let mut transcript = TR::new(transcript_params);

        if self.parameters != vk.fixed_parameters.parameters {
            log!("Different circuit parameters in verifier and VK");
            return false;
        }

        if self.lookup_parameters != vk.fixed_parameters.lookup_parameters {
            log!("Different lookup parameters in verifier and VK");
            return false;
        }

        if vk.fixed_parameters.cap_size != proof.proof_config.merkle_tree_cap_size {
            log!("Different cap sized in proof as VK");
            return false;
        }

        if vk.fixed_parameters.fri_lde_factor != proof.proof_config.fri_lde_factor {
            log!("Different FRI LDE factor in proof as VK");
            return false;
        }

        if vk.fixed_parameters.cap_size != vk.setup_merkle_tree_cap.len() {
            log!("Cap is malformed");
            return false;
        }
        transcript.witness_merkle_tree_cap(&vk.setup_merkle_tree_cap);

        if proof.public_inputs.len() != vk.fixed_parameters.public_inputs_locations.len() {
            // VK mismatch
            log!("Invalid number of public inputs");
            return false;
        }

        let num_public_inputs = proof.public_inputs.len();
        let mut public_inputs_with_values = Vec::with_capacity(num_public_inputs);

        // commit public inputs
        for ((column, row), value) in vk
            .fixed_parameters
            .public_inputs_locations
            .iter()
            .copied()
            .zip(proof.public_inputs.iter().copied())
        {
            public_inputs_with_values.push((column, row, value));
            transcript.witness_field_elements(&[value]);
        }

        // commit witness
        if vk.fixed_parameters.cap_size != proof.witness_oracle_cap.len() {
            log!("Cap is malformed");
            return false;
        }
        transcript.witness_merkle_tree_cap(&proof.witness_oracle_cap);

        // draw challenges for stage 2
        let beta = transcript.get_multiple_challenges_fixed::<2>();
        let beta = ExtensionField::<F, 2, EXT>::from_coeff_in_base(beta);
        let gamma = transcript.get_multiple_challenges_fixed::<2>();
        let gamma = ExtensionField::<F, 2, EXT>::from_coeff_in_base(gamma);

        let (lookup_beta, lookup_gamma) = if self.lookup_parameters != LookupParameters::NoLookup {
            // lookup argument related parts
            let lookup_beta = transcript.get_multiple_challenges_fixed::<2>();
            let lookup_beta = ExtensionField::<F, 2, EXT>::from_coeff_in_base(lookup_beta);
            let lookup_gamma = transcript.get_multiple_challenges_fixed::<2>();
            let lookup_gamma = ExtensionField::<F, 2, EXT>::from_coeff_in_base(lookup_gamma);

            (lookup_beta, lookup_gamma)
        } else {
            let zero = ExtensionField::<F, 2, EXT>::ZERO;

            (zero, zero)
        };

        if vk.fixed_parameters.cap_size != proof.stage_2_oracle_cap.len() {
            log!("Cap is malformed");
            return false;
        }
        transcript.witness_merkle_tree_cap(&proof.stage_2_oracle_cap);

        // draw challenges for quotient
        let alpha = transcript.get_multiple_challenges_fixed::<2>();
        let alpha = ExtensionField::<F, 2, EXT>::from_coeff_in_base(alpha);

        // two extra relations per lookup subargument - for A and B polys
        let num_lookup_subarguments = self.num_sublookup_arguments();
        let num_multiplicities_polys = self.num_multipicities_polys(
            vk.fixed_parameters.total_tables_len as usize,
            vk.fixed_parameters.domain_size,
        );
        let total_num_lookup_argument_terms = num_lookup_subarguments + num_multiplicities_polys;

        // now we need to compute number of intermediate products for copy-permutation

        let num_variable_polys = self.num_variable_polys();
        let num_witness_polys = self.num_witness_polys();
        let num_constant_polys = self.num_constant_polys(&vk.fixed_parameters);
        let quotient_degree = self.quotient_degree(&vk.fixed_parameters);
        let num_copy_permutation_polys = num_variable_polys;

        use crate::cs::implementations::copy_permutation::num_intermediate_partial_product_relations;
        let num_intermediate_partial_product_relations =
            num_intermediate_partial_product_relations(num_copy_permutation_polys, quotient_degree);

        let total_num_gate_terms_for_specialized_columns = self
            .evaluators_over_specialized_columns
            .iter()
            .zip(self.gate_type_ids_for_specialized_columns.iter())
            .map(|(evaluator, gate_type_id)| {
                let placement_strategy = self
                    .placement_strategies
                    .get(gate_type_id)
                    .copied()
                    .expect("gate must be allowed");
                let num_repetitions = match placement_strategy {
                    GatePlacementStrategy::UseSpecializedColumns {
                        num_repetitions, ..
                    } => num_repetitions,
                    _ => unreachable!(),
                };
                assert_eq!(evaluator.num_repetitions_on_row, num_repetitions);
                let terms_per_repetition = evaluator.num_quotient_terms;

                terms_per_repetition * num_repetitions
            })
            .sum();

        let total_num_gate_terms_for_general_purpose_columns: usize = self
            .evaluators_over_general_purpose_columns
            .iter()
            .map(|evaluator| evaluator.total_quotient_terms_over_all_repetitions)
            .sum();

        let total_num_terms =
            total_num_lookup_argument_terms // and lookup is first
            + total_num_gate_terms_for_specialized_columns // then gates over specialized columns
            + total_num_gate_terms_for_general_purpose_columns // all getes terms over general purpose columns 
            + 1 // z(1) == 1 copy permutation
            + 1 // z(x * omega) = ...
            + num_intermediate_partial_product_relations // chunking copy permutation part
        ;

        use crate::cs::implementations::utils::materialize_powers_serial;

        let powers: Vec<_, Global> = materialize_powers_serial(alpha, total_num_terms);
        let rest = &powers[..];
        let (take, rest) = rest.split_at(total_num_lookup_argument_terms);
        let pregenerated_challenges_for_lookup = take.to_vec();
        let (take, rest) = rest.split_at(total_num_gate_terms_for_specialized_columns);
        let pregenerated_challenges_for_gates_over_specialized_columns = take.to_vec();
        let (take, rest) = rest.split_at(total_num_gate_terms_for_general_purpose_columns);
        let pregenerated_challenges_for_gates_over_general_purpose_columns = take.to_vec();
        let remaining_challenges = rest.to_vec();

        // commit quotient
        if vk.fixed_parameters.cap_size != proof.quotient_oracle_cap.len() {
            log!("Cap is malformed");
            return false;
        }
        transcript.witness_merkle_tree_cap(&proof.quotient_oracle_cap);

        // get z

        let z = transcript.get_multiple_challenges_fixed::<2>();
        let z = ExtensionField::<F, 2, EXT>::from_coeff_in_base(z);

        // commit claimed values at z, and form our poly storage
        for set in proof.values_at_z.iter() {
            transcript.witness_field_elements(set.as_coeffs_in_base());
        }

        for set in proof.values_at_z_omega.iter() {
            transcript.witness_field_elements(set.as_coeffs_in_base());
        }

        for set in proof.values_at_0.iter() {
            transcript.witness_field_elements(set.as_coeffs_in_base());
        }

        use crate::cs::implementations::utils::domain_generator_for_size;
        // and public inputs should also go into quotient
        let mut public_input_opening_tuples: Vec<(F, Vec<(usize, F)>)> = vec![];
        {
            let omega = domain_generator_for_size::<F>(vk.fixed_parameters.domain_size);

            for (column, row, value) in public_inputs_with_values.into_iter() {
                let open_at = omega.pow_u64(row as u64);
                let pos = public_input_opening_tuples
                    .iter()
                    .position(|el| el.0 == open_at);
                if let Some(pos) = pos {
                    public_input_opening_tuples[pos].1.push((column, value));
                } else {
                    public_input_opening_tuples.push((open_at, vec![(column, value)]));
                }
            }

            let public_inputs_sorted_locations = vk
                .fixed_parameters
                .public_inputs_locations_batched_by_opening();
            assert_eq!(
                public_inputs_sorted_locations.len(),
                public_input_opening_tuples.len()
            );

            for (a, b) in public_input_opening_tuples
                .iter()
                .zip(public_inputs_sorted_locations.into_iter())
            {
                assert_eq!(a.1.len(), b.1.len());
            }
        }

        let expected_lookup_polys_total = if self.lookup_parameters.lookup_is_allowed() {
            num_lookup_subarguments + // lookup witness encoding polys
            num_multiplicities_polys * 2 + // multiplicity and multiplicity encoding
            self.lookup_parameters.lookup_width() + // encode tables itself
            1 // encode table IDs
        } else {
            0
        };

        let num_poly_values_at_z = num_variable_polys + num_witness_polys +
            num_constant_polys + num_copy_permutation_polys +
            1 + // z_poly
            num_intermediate_partial_product_relations + // partial products in copy-permutation
            expected_lookup_polys_total + // everything from lookup
            quotient_degree; // chunks of quotient poly

        if proof.values_at_z.len() != num_poly_values_at_z {
            log!("Number of openings at Z is unexpected");
            return false;
        }

        if proof.values_at_z_omega.len() != 1 {
            log!("Number of openings at Z*omega is unexpected");
            return false;
        }

        if proof.values_at_0.len() != total_num_lookup_argument_terms {
            log!("Number of openings at 0 is unexpected");
            return false;
        }

        // run verifier at z
        {
            use crate::cs::implementations::copy_permutation::non_residues_for_copy_permutation;
            use crate::cs::implementations::verifier::*;

            let non_residues_for_copy_permutation = non_residues_for_copy_permutation::<F, Global>(
                vk.fixed_parameters.domain_size as usize,
                num_variable_polys,
            );

            let all_values_at_z = &proof.values_at_z;
            let all_values_at_z_omega = &proof.values_at_z_omega;
            let all_values_at_0 = &proof.values_at_0;

            let lookup_challenges = &pregenerated_challenges_for_lookup;
            let specialized_evaluators_challenges =
                &pregenerated_challenges_for_gates_over_specialized_columns;
            let general_purpose_challenges =
                &pregenerated_challenges_for_gates_over_general_purpose_columns;
            let remaining_challenges = &remaining_challenges;

            let mut source_it = all_values_at_z.iter();
            // witness
            let variables_polys_values: Vec<_> =
                (&mut source_it).take(num_variable_polys).copied().collect();
            let witness_polys_values: Vec<_> =
                (&mut source_it).take(num_witness_polys).copied().collect();
            // normal setup
            let constant_poly_values: Vec<_> =
                (&mut source_it).take(num_constant_polys).copied().collect();
            let sigmas_values: Vec<_> = (&mut source_it)
                .take(num_copy_permutation_polys)
                .copied()
                .collect();
            let copy_permutation_z_at_z = *source_it.next().unwrap();
            let grand_product_intermediate_polys: Vec<_> = (&mut source_it)
                .take(num_intermediate_partial_product_relations)
                .copied()
                .collect();
            // lookup if exists
            let multiplicities_polys_values: Vec<_> = (&mut source_it)
                .take(num_multiplicities_polys)
                .copied()
                .collect();
            let lookup_witness_encoding_polys_values: Vec<_> = (&mut source_it)
                .take(num_lookup_subarguments)
                .copied()
                .collect();
            let multiplicities_encoding_polys_values: Vec<_> = (&mut source_it)
                .take(num_multiplicities_polys)
                .copied()
                .collect();
            // lookup setup
            let num_lookup_table_setup_polys = self.num_lookup_table_setup_polys();
            let lookup_tables_columns: Vec<_> = (&mut source_it)
                .take(num_lookup_table_setup_polys)
                .copied()
                .collect();
            // quotient
            let quotient_chunks: Vec<_> = source_it.copied().collect();

            assert_eq!(quotient_chunks.len(), quotient_degree);

            let mut source_it = all_values_at_z_omega.iter();
            let copy_permutation_z_at_z_omega = *source_it.next().unwrap();

            let mut t_accumulator = ExtensionField::<F, 2, EXT>::ZERO;
            // precompute selectors at z

            let mut selectors_buffer = HashMap::new();
            for (gate_idx, evaluator) in self
                .evaluators_over_general_purpose_columns
                .iter()
                .enumerate()
            {
                if let Some(path) = vk
                    .fixed_parameters
                    .selectors_placement
                    .output_placement(gate_idx)
                {
                    if selectors_buffer.contains_key(&path) {
                        panic!("same selector for different gates");
                    }

                    compute_selector_subpath_at_z(
                        path,
                        &mut selectors_buffer,
                        &constant_poly_values,
                        &mut (),
                    );
                } else {
                    assert!(evaluator.num_quotient_terms == 0);
                }
            }

            // first we do the lookup
            if self.lookup_parameters != LookupParameters::NoLookup {
                // immediatelly do sumchecks
                let lookup_witness_encoding_polys_polys_at_0 =
                    &all_values_at_0[..num_lookup_subarguments];
                let multiplicities_encoding_polys_at_0 =
                    &all_values_at_0[num_lookup_subarguments..];

                let mut witness_subsum = ExtensionField::<F, 2, EXT>::ZERO;
                for a in lookup_witness_encoding_polys_polys_at_0.iter() {
                    witness_subsum.add_assign(a);
                }

                let mut multiplicities_subsum = ExtensionField::<F, 2, EXT>::ZERO;
                for b in multiplicities_encoding_polys_at_0.iter() {
                    multiplicities_subsum.add_assign(b);
                }
                if witness_subsum != multiplicities_subsum {
                    log!(
                        "Lookup sumcheck is invalid: a = {}, b = {}",
                        witness_subsum,
                        multiplicities_subsum
                    );
                    return false;
                }

                // lookup argument related parts
                match self.lookup_parameters {
                    LookupParameters::TableIdAsVariable {
                        width: _,
                        share_table_id: _,
                    }
                    | LookupParameters::TableIdAsConstant {
                        width: _,
                        share_table_id: _,
                    } => {
                        // exists by our setup
                        let lookup_evaluator_id = 0;
                        let selector_subpath = vk
                            .fixed_parameters
                            .selectors_placement
                            .output_placement(lookup_evaluator_id)
                            .expect("lookup gate must be placed");
                        let selector = selectors_buffer
                            .remove(&selector_subpath)
                            .expect("path must be unique and precomputed");

                        let column_elements_per_subargument =
                            self.lookup_parameters.columns_per_subargument() as usize;
                        assert!(
                            vk.fixed_parameters.table_ids_column_idxes.len() == 0
                                || vk.fixed_parameters.table_ids_column_idxes.len() == 1
                        );

                        // this is our lookup width, either counted by number of witness columns only, or if one includes setup
                        let num_lookup_columns = column_elements_per_subargument
                            + ((vk.fixed_parameters.table_ids_column_idxes.len() == 1) as usize);
                        assert_eq!(lookup_tables_columns.len(), num_lookup_columns);

                        let capacity = column_elements_per_subargument
                            + ((vk.fixed_parameters.table_ids_column_idxes.len() == 1) as usize);
                        let mut powers_of_gamma = Vec::with_capacity(capacity);
                        let mut tmp = ExtensionField::<F, 2, EXT>::ONE;
                        powers_of_gamma.push(tmp);
                        for _ in 1..capacity {
                            tmp.mul_assign(&lookup_gamma);
                            powers_of_gamma.push(tmp);
                        }

                        // precompute aggregation of lookup table polys
                        assert_eq!(powers_of_gamma.len(), capacity);
                        let mut lookup_table_columns_aggregated = lookup_beta;
                        for (gamma, column) in
                            powers_of_gamma.iter().zip(lookup_tables_columns.iter())
                        {
                            ExtensionField::<F, 2, EXT>::mul_and_accumulate_into(
                                &mut lookup_table_columns_aggregated,
                                gamma,
                                column,
                            );
                        }

                        let mut challenges_it = lookup_challenges.iter();

                        // first A polys
                        let variables_columns_for_lookup = &variables_polys_values
                            [..(column_elements_per_subargument * num_lookup_subarguments)];
                        assert_eq!(
                            lookup_witness_encoding_polys_values.len(),
                            variables_columns_for_lookup
                                .chunks_exact(column_elements_per_subargument)
                                .len()
                        );

                        for (a_poly, witness_columns) in
                            lookup_witness_encoding_polys_values.iter().zip(
                                variables_columns_for_lookup
                                    .chunks_exact(column_elements_per_subargument),
                            )
                        {
                            let alpha = *challenges_it
                                .next()
                                .expect("challenge for lookup A poly contribution");
                            let mut contribution = lookup_beta;

                            let table_id = if let Some(table_id_poly) =
                                vk.fixed_parameters.table_ids_column_idxes.first().copied()
                            {
                                vec![constant_poly_values[table_id_poly]]
                            } else {
                                vec![]
                            };

                            for (gamma, column) in powers_of_gamma
                                .iter()
                                .zip(witness_columns.iter().chain(table_id.iter()))
                            {
                                ExtensionField::<F, 2, EXT>::mul_and_accumulate_into(
                                    &mut contribution,
                                    gamma,
                                    column,
                                );
                            }

                            // mul by A(x)
                            contribution.mul_assign(a_poly);
                            // sub selector
                            contribution.sub_assign(&selector);

                            // mul by power of challenge
                            contribution.mul_assign(&alpha);

                            t_accumulator.add_assign(&contribution);
                        }

                        // then B polys
                        assert_eq!(
                            multiplicities_encoding_polys_values.len(),
                            multiplicities_polys_values.len()
                        );
                        for (b_poly, multiplicities_poly) in multiplicities_encoding_polys_values
                            .iter()
                            .zip(multiplicities_polys_values.iter())
                        {
                            let alpha = *challenges_it
                                .next()
                                .expect("challenge for lookup B poly contribution");
                            let mut contribution = lookup_table_columns_aggregated;
                            // mul by B(x)
                            contribution.mul_assign(b_poly);
                            // sub multiplicity
                            contribution.sub_assign(multiplicities_poly);
                            // mul by power of challenge
                            contribution.mul_assign(&alpha);

                            t_accumulator.add_assign(&contribution);
                        }
                    }
                    LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                        width: _,
                        num_repetitions: _,
                        share_table_id: _,
                    }
                    | LookupParameters::UseSpecializedColumnsWithTableIdAsVariable {
                        width: _,
                        num_repetitions: _,
                        share_table_id: _,
                    } => {
                        let column_elements_per_subargument =
                            self.lookup_parameters.specialized_columns_per_subargument() as usize;
                        assert!(
                            vk.fixed_parameters.table_ids_column_idxes.len() == 0
                                || vk.fixed_parameters.table_ids_column_idxes.len() == 1
                        );

                        // this is our lookup width, either counted by number of witness columns only, or if one includes setup
                        let num_lookup_columns = column_elements_per_subargument
                            + ((vk.fixed_parameters.table_ids_column_idxes.len() == 1) as usize);
                        assert_eq!(lookup_tables_columns.len(), num_lookup_columns);

                        let capacity = column_elements_per_subargument
                            + ((vk.fixed_parameters.table_ids_column_idxes.len() == 1) as usize);
                        let mut powers_of_gamma = Vec::with_capacity(capacity);
                        let mut tmp = ExtensionField::<F, 2, EXT>::ONE;
                        powers_of_gamma.push(tmp);
                        for _ in 1..capacity {
                            tmp.mul_assign(&lookup_gamma);
                            powers_of_gamma.push(tmp);
                        }

                        // precompute aggregation of lookup table polys
                        assert_eq!(powers_of_gamma.len(), capacity);
                        let mut lookup_table_columns_aggregated = lookup_beta;
                        for (gamma, column) in
                            powers_of_gamma.iter().zip(lookup_tables_columns.iter())
                        {
                            ExtensionField::<F, 2, EXT>::mul_and_accumulate_into(
                                &mut lookup_table_columns_aggregated,
                                gamma,
                                column,
                            );
                        }

                        let mut challenges_it = lookup_challenges.iter();

                        // first A polys
                        let variables_columns_for_lookup = &variables_polys_values[self
                            .parameters
                            .num_columns_under_copy_permutation
                            ..(self.parameters.num_columns_under_copy_permutation
                                + column_elements_per_subargument * num_lookup_subarguments)];
                        assert_eq!(
                            lookup_witness_encoding_polys_values.len(),
                            variables_columns_for_lookup
                                .chunks_exact(column_elements_per_subargument)
                                .len()
                        );

                        for (a_poly, witness_columns) in
                            lookup_witness_encoding_polys_values.iter().zip(
                                variables_columns_for_lookup
                                    .chunks_exact(column_elements_per_subargument),
                            )
                        {
                            let alpha = *challenges_it
                                .next()
                                .expect("challenge for lookup A poly contribution");
                            let mut contribution = lookup_beta;

                            let table_id = if let Some(table_id_poly) =
                                vk.fixed_parameters.table_ids_column_idxes.first().copied()
                            {
                                vec![constant_poly_values[table_id_poly]]
                            } else {
                                vec![]
                            };

                            for (gamma, column) in powers_of_gamma
                                .iter()
                                .zip(witness_columns.iter().chain(table_id.iter()))
                            {
                                ExtensionField::<F, 2, EXT>::mul_and_accumulate_into(
                                    &mut contribution,
                                    gamma,
                                    column,
                                );
                            }

                            // mul by A(x)
                            contribution.mul_assign(a_poly);
                            // sub numerator
                            contribution.sub_assign(&ExtensionField::<F, 2, EXT>::ONE);
                            // mul by power of challenge
                            contribution.mul_assign(&alpha);

                            t_accumulator.add_assign(&contribution);
                        }

                        // then B polys
                        assert_eq!(
                            multiplicities_encoding_polys_values.len(),
                            multiplicities_polys_values.len()
                        );
                        for (b_poly, multiplicities_poly) in multiplicities_encoding_polys_values
                            .iter()
                            .zip(multiplicities_polys_values.iter())
                        {
                            let alpha = *challenges_it
                                .next()
                                .expect("challenge for lookup B poly contribution");
                            let mut contribution = lookup_table_columns_aggregated;
                            // mul by B(x)
                            contribution.mul_assign(b_poly);
                            // sub multiplicity
                            contribution.sub_assign(multiplicities_poly);
                            // mul by power of challenge
                            contribution.mul_assign(&alpha);

                            t_accumulator.add_assign(&contribution);
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }

            let constants_for_gates_over_general_purpose_columns =
                vk.fixed_parameters.extra_constant_polys_for_selectors
                    + self.parameters.num_constant_columns;

            let src = VerifierPolyStorage::new(
                variables_polys_values.clone(),
                witness_polys_values,
                constant_poly_values,
            );

            // then specialized gates
            {
                let mut specialized_placement_data = vec![];
                let mut evaluation_functions = vec![];

                for (idx, (gate_type_id, evaluator)) in self
                    .gate_type_ids_for_specialized_columns
                    .iter()
                    .zip(self.evaluators_over_specialized_columns.iter())
                    .enumerate()
                {
                    if gate_type_id == &std::any::TypeId::of::<LookupFormalGate>() {
                        continue;
                    }

                    assert!(
                        evaluator.total_quotient_terms_over_all_repetitions != 0,
                        "evaluator {} has no contribution to quotient",
                        &evaluator.debug_name,
                    );
                    log!(
                        "Will be evaluating {} over specialized columns",
                        &evaluator.debug_name
                    );

                    let num_terms = evaluator.num_quotient_terms;
                    let placement_strategy = self
                        .placement_strategies
                        .get(gate_type_id)
                        .copied()
                        .expect("gate must be allowed");
                    let GatePlacementStrategy::UseSpecializedColumns {
                        num_repetitions,
                        share_constants,
                    } = placement_strategy
                    else {
                        unreachable!();
                    };

                    let total_terms = num_terms * num_repetitions;

                    let (initial_offset, per_repetition_offset, total_constants_available) =
                        self.offsets_for_specialized_evaluators[idx];

                    let placement_data = (
                        num_repetitions,
                        share_constants,
                        initial_offset,
                        per_repetition_offset,
                        total_constants_available,
                        total_terms,
                    );

                    specialized_placement_data.push(placement_data);
                    let t = &**evaluator
                        .columnwise_satisfiability_function
                        .as_ref()
                        .expect("must be properly configured");
                    evaluation_functions.push(t);
                }

                let mut challenges_offset = 0;

                for (placement_data, evaluation_fn) in specialized_placement_data
                    .iter()
                    .zip(evaluation_functions.iter())
                {
                    let (
                        num_repetitions,
                        share_constants,
                        initial_offset,
                        per_repetition_offset,
                        _total_constants_available,
                        total_terms,
                    ) = *placement_data;

                    // we self-check again
                    if share_constants {
                        assert_eq!(per_repetition_offset.constants_offset, 0);
                    }
                    let mut final_offset = initial_offset;
                    for _ in 0..num_repetitions {
                        final_offset.add_offset(&per_repetition_offset);
                    }

                    let mut dst = VerifierRelationDestination {
                        accumulator: ExtensionField::<F, 2, EXT>::ZERO,
                        selector_value: ExtensionField::<F, 2, EXT>::ONE,
                        challenges: specialized_evaluators_challenges.clone(),
                        current_challenge_offset: challenges_offset,
                        _marker: std::marker::PhantomData,
                    };

                    let mut src = src.subset(
                        initial_offset.variables_offset..final_offset.variables_offset,
                        initial_offset.witnesses_offset..final_offset.witnesses_offset,
                        (constants_for_gates_over_general_purpose_columns
                            + initial_offset.constants_offset)
                            ..(constants_for_gates_over_general_purpose_columns
                                + final_offset.constants_offset),
                    );

                    evaluation_fn.evaluate_over_columns(&mut src, &mut dst, &mut ());

                    t_accumulator.add_assign(&dst.accumulator);

                    challenges_offset += total_terms;
                }

                assert_eq!(
                    challenges_offset,
                    total_num_gate_terms_for_specialized_columns
                );
            }

            log!("Evaluating general purpose gates");
            // then general purpose gates
            {
                let src = src.subset(
                    0..self.parameters.num_columns_under_copy_permutation,
                    0..self.parameters.num_witness_columns,
                    0..constants_for_gates_over_general_purpose_columns,
                );

                let mut challenges_offset = 0;

                for (gate_idx, evaluator) in self
                    .evaluators_over_general_purpose_columns
                    .iter()
                    .enumerate()
                {
                    if evaluator.evaluator_type_id
                        == std::any::TypeId::of::<LookupGateMarkerFormalEvaluator>()
                    {
                        continue;
                    }

                    if evaluator.total_quotient_terms_over_all_repetitions == 0 {
                        // we MAY formally have NOP gate in the set here, but we should not evaluate it.
                        // NOP gate will affect selectors placement, but not the rest
                        continue;
                    }

                    if let Some(path) = vk
                        .fixed_parameters
                        .selectors_placement
                        .output_placement(gate_idx)
                    {
                        let selector = selectors_buffer
                            .remove(&path)
                            .expect("path must be unique and precomputed");
                        let constant_placement_offset = path.len();

                        let mut dst = VerifierRelationDestination {
                            accumulator: ExtensionField::<F, 2, EXT>::ZERO,
                            selector_value: selector,
                            challenges: general_purpose_challenges.clone(),
                            current_challenge_offset: challenges_offset,
                            _marker: std::marker::PhantomData,
                        };

                        let mut source = src.clone();

                        let evaluation_fn = &**evaluator
                            .rowwise_satisfiability_function
                            .as_ref()
                            .expect("gate must be allowed");

                        evaluation_fn.evaluate_over_general_purpose_columns(
                            &mut source,
                            &mut dst,
                            constant_placement_offset,
                            &mut (),
                        );

                        t_accumulator.add_assign(&dst.accumulator);
                        challenges_offset += evaluator.total_quotient_terms_over_all_repetitions;
                    } else {
                        assert!(evaluator.num_quotient_terms == 0);
                    }
                }

                assert_eq!(
                    challenges_offset,
                    total_num_gate_terms_for_general_purpose_columns
                );
            }

            // then copy_permutation algorithm

            let z_in_domain_size = z.pow_u64(vk.fixed_parameters.domain_size);

            let mut vanishing_at_z = z_in_domain_size;
            vanishing_at_z.sub_assign(&ExtensionField::<F, 2, EXT>::ONE);

            let mut challenges_it = remaining_challenges.iter();

            {
                // (x^n - 1) / (x - 1),
                let mut z_minus_one = z;
                z_minus_one.sub_assign(&ExtensionField::<F, 2, EXT>::ONE);

                let mut unnormalized_l1_inverse_at_z = vanishing_at_z;
                unnormalized_l1_inverse_at_z
                    .mul_assign(&z_minus_one.inverse().expect("Z is not in the domain"));

                let alpha = *challenges_it.next().expect("challenge for z(1) == 1");
                // (z(x) - 1) * l(1)
                let mut contribution = copy_permutation_z_at_z;
                contribution.sub_assign(&ExtensionField::<F, 2, EXT>::ONE);
                contribution.mul_assign(&unnormalized_l1_inverse_at_z);
                contribution.mul_assign(&alpha);

                t_accumulator.add_assign(&contribution);
            }

            // partial products

            let lhs = grand_product_intermediate_polys
                .iter()
                .chain(std::iter::once(&copy_permutation_z_at_z_omega));

            let rhs = std::iter::once(&copy_permutation_z_at_z)
                .chain(grand_product_intermediate_polys.iter());

            for (((((lhs, rhs), alpha), non_residues), variables), sigmas) in lhs
                .zip(rhs)
                .zip(&mut challenges_it)
                .zip(non_residues_for_copy_permutation.chunks(quotient_degree))
                .zip(variables_polys_values.chunks(quotient_degree))
                .zip(sigmas_values.chunks(quotient_degree))
            {
                let mut lhs = *lhs;
                for (variable, sigma) in variables.iter().zip(sigmas.iter()) {
                    // denominator is w + beta * sigma(x) + gamma
                    let mut subres = *sigma;
                    subres.mul_assign(&beta);
                    subres.add_assign(variable);
                    subres.add_assign(&gamma);
                    lhs.mul_assign(&subres);
                }

                let mut rhs = *rhs;
                let x_poly_value = z;
                for (non_res, variable) in non_residues.iter().zip(variables.iter()) {
                    // numerator is w + beta * non_res * x + gamma
                    let mut subres = x_poly_value;
                    subres.mul_assign_by_base(non_res);
                    subres.mul_assign(&beta);
                    subres.add_assign(variable);
                    subres.add_assign(&gamma);
                    rhs.mul_assign(&subres);
                }

                let mut contribution = lhs;
                contribution.sub_assign(&rhs);
                contribution.mul_assign(alpha);

                t_accumulator.add_assign(&contribution);
            }

            assert_eq!(challenges_it.len(), 0, "must exhaust all the challenges");

            let mut t_from_chunks = ExtensionField::<F, 2, EXT>::ZERO;
            let mut pow = ExtensionField::<F, 2, EXT>::ONE;
            for el in quotient_chunks.into_iter() {
                let mut tmp = el;
                tmp.mul_assign(&pow);
                pow.mul_assign(&z_in_domain_size);
                t_from_chunks.add_assign(&tmp);
            }

            t_from_chunks.mul_assign(&vanishing_at_z);

            // assert_eq!(t_accumulator, t_from_chunks, "unsatisfied at Z",);

            if t_accumulator != t_from_chunks {
                log!("Invalid quotient at Z");
                return false;
            }
        }

        // get challenges
        let c0 = transcript.get_challenge();
        let c1 = transcript.get_challenge();

        let mut total_num_challenges = 0;
        total_num_challenges += proof.values_at_z.len();
        total_num_challenges += proof.values_at_z_omega.len();
        total_num_challenges += proof.values_at_0.len();
        for (_, subset) in public_input_opening_tuples.iter() {
            total_num_challenges += subset.len();
        }

        let challenges_for_fri_quotiening =
            crate::cs::implementations::prover::materialize_ext_challenge_powers::<F, EXT>(
                (c0, c1),
                total_num_challenges,
            );

        let (
            new_pow_bits,                 // updated POW bits if needed
            num_queries,                  // num queries
            interpolation_log2s_schedule, // folding schedule
            final_expected_degree,
        ) = crate::cs::implementations::prover::compute_fri_schedule(
            proof.proof_config.security_level as u32,
            proof.proof_config.merkle_tree_cap_size,
            proof.proof_config.pow_bits,
            proof.proof_config.fri_lde_factor.trailing_zeros(),
            vk.fixed_parameters.domain_size.trailing_zeros(),
        );

        let mut expected_degree = vk.fixed_parameters.domain_size;

        if new_pow_bits != proof.proof_config.pow_bits {
            log!("PoW bits computation diverged");
            return false;
        }

        let mut fri_intermediate_challenges = vec![];

        {
            // now witness base FRI oracle
            if vk.fixed_parameters.cap_size != proof.fri_base_oracle_cap.len() {
                log!("Cap is malformed");
                return false;
            }
            transcript.witness_merkle_tree_cap(&proof.fri_base_oracle_cap);

            let reduction_degree_log_2 = interpolation_log2s_schedule[0];
            let c0 = transcript.get_challenge();
            let c1 = transcript.get_challenge();

            let mut challenge_powers = Vec::with_capacity(reduction_degree_log_2);
            challenge_powers.push((c0, c1));
            let as_extension = ExtensionField::<F, 2, EXT> {
                coeffs: [c0, c1],
                _marker: std::marker::PhantomData,
            };

            let mut current = as_extension;

            for _ in 1..reduction_degree_log_2 {
                current.square();
                let [c0, c1] = current.into_coeffs_in_base();
                challenge_powers.push((c0, c1));
            }
            expected_degree >>= reduction_degree_log_2;

            fri_intermediate_challenges.push(challenge_powers);
        }

        if interpolation_log2s_schedule[1..].len() != proof.fri_intermediate_oracles_caps.len() {
            log!("Unexpected number of intermediate FRI oracles");
            return false;
        }

        for (interpolation_degree_log2, cap) in interpolation_log2s_schedule[1..]
            .iter()
            .zip(proof.fri_intermediate_oracles_caps.iter())
        {
            // commit new oracle
            if vk.fixed_parameters.cap_size != cap.len() {
                log!("Cap is malformed");
                return false;
            }
            transcript.witness_merkle_tree_cap(cap);

            // get challenge
            let reduction_degree_log_2 = *interpolation_degree_log2;
            let c0 = transcript.get_challenge();
            let c1 = transcript.get_challenge();

            let mut challenge_powers = Vec::with_capacity(reduction_degree_log_2);
            challenge_powers.push((c0, c1));
            let as_extension = ExtensionField::<F, 2, EXT> {
                coeffs: [c0, c1],
                _marker: std::marker::PhantomData,
            };

            let mut current = as_extension;

            for _ in 1..reduction_degree_log_2 {
                current.square();
                let [c0, c1] = current.into_coeffs_in_base();
                challenge_powers.push((c0, c1));
            }

            fri_intermediate_challenges.push(challenge_powers);
            expected_degree >>= reduction_degree_log_2;
        }

        if final_expected_degree != expected_degree as usize {
            log!("Expected final degree diverged");
            return false;
        }

        if proof.final_fri_monomials[0].len() != proof.final_fri_monomials[1].len() {
            log!("Monomials coefficients length mismatch");
            return false;
        }

        if proof.final_fri_monomials[0].len() == 0 || proof.final_fri_monomials[1].len() == 0 {
            log!("Monomials coefficients length is zero");
            return false;
        }

        if expected_degree as usize != proof.final_fri_monomials[0].len() {
            log!("Unexpected number of monomials in FRI");
            return false;
        }
        if expected_degree as usize != proof.final_fri_monomials[1].len() {
            log!("Unexpected number of monomials in FRI");
            return false;
        }

        // witness monomial coeffs
        transcript.witness_field_elements(&proof.final_fri_monomials[0]);
        transcript.witness_field_elements(&proof.final_fri_monomials[1]);

        if new_pow_bits != 0 {
            log!("Doing PoW verification for {} bits", new_pow_bits);
            log!("Prover gave challenge 0x{:016x}", proof.pow_challenge);

            // pull enough challenges from the transcript
            let mut num_challenges = 256 / F::CHAR_BITS;
            if num_challenges % F::CHAR_BITS != 0 {
                num_challenges += 1;
            }
            let challenges = transcript.get_multiple_challenges(num_challenges);
            let pow_challenge = proof.pow_challenge;

            let pow_is_valid = POW::verify_from_field_elements(
                challenges,
                proof.proof_config.pow_bits,
                pow_challenge,
            );
            if pow_is_valid == false {
                log!("PoW is invalid");
                return false;
            }

            assert!(F::CAPACITY_BITS >= 32);
            let (low, high) = (pow_challenge as u32, (pow_challenge >> 32) as u32);
            let low = F::from_u64_unchecked(low as u64);
            let high = F::from_u64_unchecked(high as u64);
            transcript.witness_field_elements(&[low, high]);
        }

        use crate::cs::implementations::transcript::BoolsBuffer;

        let lde_domain_size: u64 =
            vk.fixed_parameters.domain_size * proof.proof_config.fri_lde_factor as u64;

        let max_needed_bits = lde_domain_size.trailing_zeros() as usize;
        let mut bools_buffer = BoolsBuffer {
            available: vec![],
            max_needed: max_needed_bits,
        };

        let num_bits_for_in_coset_index =
            max_needed_bits - proof.proof_config.fri_lde_factor.trailing_zeros() as usize;
        let base_tree_index_shift = vk.fixed_parameters.domain_size.trailing_zeros();
        assert_eq!(num_bits_for_in_coset_index, base_tree_index_shift as usize);

        // precompute once, will be handy later
        let mut precomputed_powers = vec![];
        let mut precomputed_powers_inversed = vec![];
        for i in 0..=lde_domain_size.trailing_zeros() {
            let omega = domain_generator_for_size::<F>(1u64 << i);
            precomputed_powers.push(omega);
            precomputed_powers_inversed.push(omega.inverse().unwrap());
        }

        let omega = precomputed_powers[vk.fixed_parameters.domain_size.trailing_zeros() as usize];

        // we also want to precompute "steps" for different interpolation degrees
        // e.g. if we interpolate 8 elements,
        // then those will be ordered as bitreverses of [0..=7], namely
        // [0, 4, 2, 6, 1, 5, 3, 7]

        // so we want to have exactly half of it, because separation by 4
        // is exactly -1, so we need [1, sqrt4(1), sqrt8(1), sqrt4(1)*sqrt8(1)]

        let mut interpolation_steps = [F::ONE; 4]; // max size
        for idx in [1, 3].into_iter() {
            interpolation_steps[idx].mul_assign(&precomputed_powers_inversed[2]);
        }
        for idx in [2, 3].into_iter() {
            interpolation_steps[idx].mul_assign(&precomputed_powers_inversed[3]);
        }

        assert_eq!(interpolation_steps[0], F::ONE);
        assert_eq!(interpolation_steps[1].pow_u64(4), F::ONE);
        assert_eq!(interpolation_steps[2].pow_u64(8), F::ONE);

        if num_queries != proof.queries_per_fri_repetition.len() {
            log!(
                "FRI queries number is invalid: expecting {}, prover provided {}",
                num_queries,
                proof.queries_per_fri_repetition.len(),
            );
        }

        let base_oracle_depth = vk.fixed_parameters.base_oracles_depth();

        let witness_leaf_size = self.witness_leaf_size(&vk.fixed_parameters);

        let stage_2_leaf_size = self.stage_2_leaf_size(&vk.fixed_parameters);
        let quotient_leaf_size = self.quotient_leaf_size(&vk.fixed_parameters);

        let setup_leaf_size = self.setup_leaf_size(&vk.fixed_parameters);

        for queries in proof.queries_per_fri_repetition.iter() {
            let query_index_lsb_first_bits =
                bools_buffer.get_bits(&mut transcript, max_needed_bits);
            // we consider it to be some convenient for us encoding of coset + inner index.

            // Small note on indexing: when we commit to elements we use bitreversal enumeration everywhere.
            // So index `i` in the tree corresponds to the element of `omega^bitreverse(i)`.
            // This gives us natural separation of LDE cosets, such that subtrees form independent cosets,
            // and if cosets are in the form of `{1, gamma, ...} x {1, omega, ...} where gamma^lde_factor == omega,
            // then subtrees are enumerated by bitreverse powers of gamma
            use crate::cs::implementations::prover::u64_from_lsb_first_bits;

            let inner_idx = u64_from_lsb_first_bits(
                &query_index_lsb_first_bits[0..num_bits_for_in_coset_index],
            ) as usize;
            let coset_idx =
                u64_from_lsb_first_bits(&query_index_lsb_first_bits[num_bits_for_in_coset_index..])
                    as usize;
            let base_tree_idx = (coset_idx << base_tree_index_shift) + inner_idx;
            // log!("Verifying inclusion at index {}", base_tree_idx);

            // first verify basic inclusion proofs
            if queries.witness_query.leaf_elements.len() != witness_leaf_size {
                log!("Invalid leaf size for witness oracle");
                return false;
            }
            let leaf_hash = H::hash_into_leaf(&queries.witness_query.leaf_elements);
            if queries.witness_query.proof.len() != base_oracle_depth {
                log!("Invalid Merkle proof length for witness oracle");
                return false;
            }
            let is_included = MerkleTreeWithCap::<F, H, Global, Global>::verify_proof_over_cap(
                &queries.witness_query.proof,
                &proof.witness_oracle_cap,
                leaf_hash,
                base_tree_idx as usize,
            );

            if is_included == false {
                log!("Witness query not in tree");
                return false;
            }

            if queries.stage_2_query.leaf_elements.len() != stage_2_leaf_size {
                log!("Invalid leaf size for stage 2 oracle");
                return false;
            }
            let leaf_hash = H::hash_into_leaf(&queries.stage_2_query.leaf_elements);
            if queries.stage_2_query.proof.len() != base_oracle_depth {
                log!("Invalid Merkle proof length for stage 2 oracle");
                return false;
            }
            let is_included = MerkleTreeWithCap::<F, H, Global, Global>::verify_proof_over_cap(
                &queries.stage_2_query.proof,
                &proof.stage_2_oracle_cap,
                leaf_hash,
                base_tree_idx as usize,
            );

            if is_included == false {
                log!("Stage 2 query not in tree");
                return false;
            }

            if queries.quotient_query.leaf_elements.len() != quotient_leaf_size {
                log!("Invalid leaf size for quotient oracle");
                return false;
            }
            let leaf_hash = H::hash_into_leaf(&queries.quotient_query.leaf_elements);
            if queries.quotient_query.proof.len() != base_oracle_depth {
                log!("Invalid Merkle proof length for quotient oracle");
                return false;
            }
            let is_included = MerkleTreeWithCap::<F, H, Global, Global>::verify_proof_over_cap(
                &queries.quotient_query.proof,
                &proof.quotient_oracle_cap,
                leaf_hash,
                base_tree_idx as usize,
            );

            if is_included == false {
                log!("Quotient query not in tree");
                return false;
            }

            if queries.setup_query.leaf_elements.len() != setup_leaf_size {
                log!("Invalid leaf size for setup oracle");
                return false;
            }
            let leaf_hash = H::hash_into_leaf(&queries.setup_query.leaf_elements);
            if queries.setup_query.proof.len() != base_oracle_depth {
                log!("Invalid Merkle proof length for setup oracle");
                return false;
            }
            let is_included = MerkleTreeWithCap::<F, H, Global, Global>::verify_proof_over_cap(
                &queries.setup_query.proof,
                &vk.setup_merkle_tree_cap,
                leaf_hash,
                base_tree_idx as usize,
            );

            if is_included == false {
                log!("Setup query not in tree");
                return false;
            }

            // now perform the quotiening operation
            let mut simulated_ext_element = ExtensionField::<F, 2, EXT>::ZERO;

            assert_eq!(
                query_index_lsb_first_bits.len(),
                precomputed_powers.len() - 1
            );
            let mut domain_element = F::ONE;
            for (a, b) in query_index_lsb_first_bits
                .iter()
                .zip(precomputed_powers[1..].iter())
            {
                if *a {
                    domain_element.mul_assign(b);
                }
            }

            // we will find it handy to have power of the generator with some bits masked to be zero
            let mut power_chunks = vec![];
            let mut skip_highest_powers = 0;
            // TODO: we may save here (in circuits case especially) if we compute recursively
            for interpolation_degree_log2 in interpolation_log2s_schedule.iter() {
                let mut domain_element = F::ONE;
                for (a, b) in query_index_lsb_first_bits
                    .iter()
                    .skip(skip_highest_powers)
                    .zip(precomputed_powers_inversed[1..].iter())
                    .skip(*interpolation_degree_log2)
                {
                    if *a {
                        domain_element.mul_assign(b);
                    }
                }
                skip_highest_powers += *interpolation_degree_log2;
                power_chunks.push(domain_element);
            }

            // don't forget that we are shifted
            let mut domain_element_for_quotiening = domain_element;
            domain_element_for_quotiening.mul_assign(&F::multiplicative_generator());

            let mut domain_element_for_interpolation = domain_element_for_quotiening;

            let mut challenge_offset = 0;

            let z_polys_offset = 0;
            let intermediate_polys_offset = 2;
            let lookup_witness_encoding_polys_offset =
                intermediate_polys_offset + num_intermediate_partial_product_relations * 2;
            let lookup_multiplicities_encoding_polys_offset =
                lookup_witness_encoding_polys_offset + num_lookup_subarguments * 2;
            let copy_permutation_polys_offset = 0;
            let constants_offset = 0 + num_copy_permutation_polys;
            let lookup_tables_values_offset = 0 + num_copy_permutation_polys + num_constant_polys;
            let variables_offset = 0;
            let witness_columns_offset = num_variable_polys;
            let lookup_multiplicities_offset = witness_columns_offset + num_witness_polys;
            let base_coset_inverse = F::multiplicative_generator().inverse().unwrap();

            {
                let mut z_omega = z;
                z_omega.mul_assign_by_base(&omega);

                let cast_from_base = move |el: &[F]| {
                    el.iter()
                        .map(|el| ExtensionField::<F, 2, EXT>::from_coeff_in_base([*el, F::ZERO]))
                        .collect::<Vec<_>>()
                };

                let cast_from_extension = move |el: &[F]| {
                    assert_eq!(el.len() % 2, 0);

                    el.array_chunks::<2>()
                        .map(|[a, b]| ExtensionField::<F, 2, EXT>::from_coeff_in_base([*a, *b]))
                        .collect::<Vec<_>>()
                };

                let mut sources = vec![];
                // witness
                sources.extend(cast_from_base(
                    &queries.witness_query.leaf_elements
                        [variables_offset..(variables_offset + num_variable_polys)],
                ));
                sources.extend(cast_from_base(
                    &queries.witness_query.leaf_elements
                        [witness_columns_offset..(witness_columns_offset + num_witness_polys)],
                ));
                // normal setup
                sources.extend(cast_from_base(
                    &queries.setup_query.leaf_elements
                        [constants_offset..(constants_offset + num_constant_polys)],
                ));
                sources.extend(cast_from_base(
                    &queries.setup_query.leaf_elements[copy_permutation_polys_offset
                        ..(copy_permutation_polys_offset + num_copy_permutation_polys)],
                ));
                // copy-permutation
                sources.extend(cast_from_extension(
                    &queries.stage_2_query.leaf_elements[z_polys_offset..intermediate_polys_offset],
                ));
                sources.extend(cast_from_extension(
                    &queries.stage_2_query.leaf_elements
                        [intermediate_polys_offset..lookup_witness_encoding_polys_offset],
                ));
                // lookup if exists
                sources.extend(cast_from_base(
                    &queries.witness_query.leaf_elements[lookup_multiplicities_offset
                        ..(lookup_multiplicities_offset + num_multiplicities_polys)],
                ));
                sources.extend(cast_from_extension(
                    &queries.stage_2_query.leaf_elements[lookup_witness_encoding_polys_offset
                        ..lookup_multiplicities_encoding_polys_offset],
                ));
                sources.extend(cast_from_extension(
                    &queries.stage_2_query.leaf_elements
                        [lookup_multiplicities_encoding_polys_offset..],
                ));
                // lookup setup
                if self.lookup_parameters.lookup_is_allowed() {
                    let num_lookup_setups = self.lookup_parameters.lookup_width() + 1;
                    sources.extend(cast_from_base(
                        &queries.setup_query.leaf_elements[lookup_tables_values_offset
                            ..(lookup_tables_values_offset + num_lookup_setups)],
                    ));
                }
                // quotient
                sources.extend(cast_from_extension(&queries.quotient_query.leaf_elements));

                let values_at_z = &proof.values_at_z;
                assert_eq!(sources.len(), values_at_z.len());
                // log!("Making quotiening at Z");
                quotening_operation(
                    &mut simulated_ext_element,
                    &sources,
                    values_at_z,
                    domain_element_for_quotiening,
                    z,
                    &challenges_for_fri_quotiening
                        [challenge_offset..(challenge_offset + sources.len())],
                );
                challenge_offset += sources.len();

                // now z*omega
                let mut sources = vec![];
                sources.extend(cast_from_extension(
                    &queries.stage_2_query.leaf_elements[z_polys_offset..intermediate_polys_offset],
                ));

                let values_at_z_omega = &proof.values_at_z_omega;
                assert_eq!(sources.len(), values_at_z_omega.len());
                // log!("Making quotiening at Z*omega");
                quotening_operation(
                    &mut simulated_ext_element,
                    &sources,
                    values_at_z_omega,
                    domain_element_for_quotiening,
                    z_omega,
                    &challenges_for_fri_quotiening
                        [challenge_offset..(challenge_offset + sources.len())],
                );

                challenge_offset += sources.len();
                // now at 0 if lookup is needed
                if self.lookup_parameters.lookup_is_allowed() {
                    let mut sources = vec![];
                    // witness encoding
                    sources.extend(cast_from_extension(
                        &queries.stage_2_query.leaf_elements[lookup_witness_encoding_polys_offset
                            ..lookup_multiplicities_encoding_polys_offset],
                    ));
                    // multiplicities encoding
                    sources.extend(cast_from_extension(
                        &queries.stage_2_query.leaf_elements
                            [lookup_multiplicities_encoding_polys_offset..],
                    ));

                    let values_at_0 = &proof.values_at_0;
                    assert_eq!(sources.len(), values_at_0.len());
                    // log!("Making quotiening at 0 for lookups sumchecks");
                    quotening_operation(
                        &mut simulated_ext_element,
                        &sources,
                        values_at_0,
                        domain_element_for_quotiening,
                        ExtensionField::<F, 2, EXT>::ZERO,
                        &challenges_for_fri_quotiening
                            [challenge_offset..(challenge_offset + sources.len())],
                    );

                    challenge_offset += sources.len();
                }
            }

            // and public inputs
            for (open_at, set) in public_input_opening_tuples.iter() {
                let mut sources = Vec::with_capacity(set.len());
                let mut values = Vec::with_capacity(set.len());
                for (column, expected_value) in set.iter() {
                    let el = ExtensionField::<F, 2, EXT>::from_coeff_in_base([
                        queries.witness_query.leaf_elements[*column],
                        F::ZERO,
                    ]);
                    sources.push(el);

                    let value =
                        ExtensionField::<F, 2, EXT>::from_coeff_in_base([*expected_value, F::ZERO]);
                    values.push(value);
                }
                let num_challenges_required = sources.len();
                assert_eq!(values.len(), num_challenges_required);

                // log!("Making quotiening at {} for public inputs", open_at);

                let open_at = ExtensionField::<F, 2, EXT>::from_coeff_in_base([*open_at, F::ZERO]);

                quotening_operation(
                    &mut simulated_ext_element,
                    &sources,
                    &values,
                    domain_element_for_quotiening,
                    open_at,
                    &challenges_for_fri_quotiening
                        [challenge_offset..(challenge_offset + sources.len())],
                );

                challenge_offset += num_challenges_required;
            }

            assert_eq!(challenge_offset, challenges_for_fri_quotiening.len());

            let mut current_folded_value = simulated_ext_element;
            let mut subidx = base_tree_idx;
            let mut coset_inverse = base_coset_inverse;

            if interpolation_log2s_schedule.len() != queries.fri_queries.len() {
                log!("Invalid number of FRI intermediate oracle queries per repetition");
                return false;
            }

            let mut expected_fri_query_len = base_oracle_depth;

            for (idx, (interpolation_degree_log2, fri_query)) in interpolation_log2s_schedule
                .iter()
                .zip(queries.fri_queries.iter())
                .enumerate()
            {
                expected_fri_query_len -= *interpolation_degree_log2;
                let interpolation_degree = 1 << *interpolation_degree_log2;
                let subidx_in_leaf = subidx % interpolation_degree;
                let tree_idx = subidx >> interpolation_degree_log2;

                let [c0, c1] = current_folded_value.into_coeffs_in_base();
                if c0 != fri_query.leaf_elements[subidx_in_leaf]
                    || c1 != fri_query.leaf_elements[interpolation_degree + subidx_in_leaf]
                {
                    log!("FRI element is not in the leaf for step {}", idx);
                    return false;
                }

                // verify query itself
                let cap = if idx == 0 {
                    &proof.fri_base_oracle_cap
                } else {
                    &proof.fri_intermediate_oracles_caps[idx - 1]
                };
                if fri_query.leaf_elements.len() != interpolation_degree * 2 {
                    // account for extension here
                    log!("Invalid leaf size for FRI oracle number {}", idx);
                    return false;
                }
                let leaf_hash = H::hash_into_leaf(&fri_query.leaf_elements);
                if fri_query.proof.len() != expected_fri_query_len {
                    log!("Invalid Merkle proof length for FRI oracle number {}", idx);
                    return false;
                }
                let is_included = MerkleTreeWithCap::<F, H, Global, Global>::verify_proof_over_cap(
                    &fri_query.proof,
                    cap,
                    leaf_hash,
                    tree_idx as usize,
                );
                if is_included == false {
                    log!("FRI leaf is not in the tree for step {}", idx);
                    return false;
                }

                // interpolate
                let mut elements_to_interpolate = Vec::with_capacity(interpolation_degree);
                for (c0, c1) in fri_query.leaf_elements[..interpolation_degree]
                    .iter()
                    .zip(fri_query.leaf_elements[interpolation_degree..].iter())
                {
                    let as_ext = ExtensionField::<F, 2, EXT> {
                        coeffs: [*c0, *c1],
                        _marker: std::marker::PhantomData,
                    };
                    elements_to_interpolate.push(as_ext);
                }

                let mut next = Vec::with_capacity(interpolation_degree / 2);
                let challenges = &fri_intermediate_challenges[idx];
                assert_eq!(challenges.len(), *interpolation_degree_log2);

                let mut base_pow = power_chunks[idx];

                for (c0, c1) in challenges.iter() {
                    let challenge = ExtensionField::<F, 2, EXT> {
                        coeffs: [*c0, *c1],
                        _marker: std::marker::PhantomData,
                    };
                    for (i, [a, b]) in elements_to_interpolate.array_chunks::<2>().enumerate() {
                        let mut result = *a;
                        result.add_assign(b);

                        let mut diff = *a;
                        diff.sub_assign(b);
                        diff.mul_assign(&challenge);
                        // divide by corresponding power
                        let mut pow = base_pow;
                        pow.mul_assign(&interpolation_steps[i]);
                        pow.mul_assign(&coset_inverse);
                        diff.mul_assign_by_base(&pow);

                        result.add_assign(&diff);
                        next.push(result);
                    }

                    std::mem::swap(&mut next, &mut elements_to_interpolate);
                    next.clear();
                    base_pow.square();
                    coset_inverse.square();
                }

                for _ in 0..*interpolation_degree_log2 {
                    domain_element_for_interpolation.square();
                }

                // recompute the index
                subidx = tree_idx;
                current_folded_value = elements_to_interpolate[0];
            }

            // and we should evaluate monomial form and compare

            let mut result_from_monomial = ExtensionField::<F, 2, EXT>::ZERO;
            // horner rule
            for (c0, c1) in proof.final_fri_monomials[0]
                .iter()
                .zip(proof.final_fri_monomials[1].iter())
                .rev()
            {
                let coeff = ExtensionField::<F, 2, EXT> {
                    coeffs: [*c0, *c1],
                    _marker: std::marker::PhantomData,
                };

                result_from_monomial.mul_assign_by_base(&domain_element_for_interpolation);
                result_from_monomial.add_assign(&coeff);
            }

            if result_from_monomial != current_folded_value {
                log!("Not equal to evaluation from monomials");
                return false;
            }
        }

        true
    }
}

fn quotening_operation<F: SmallField, EXT: FieldExtension<2, BaseField = F>>(
    dst: &mut ExtensionField<F, 2, EXT>,
    polynomial_values: &Vec<ExtensionField<F, 2, EXT>>,
    values_at: &Vec<ExtensionField<F, 2, EXT>>,
    domain_element: F,
    at: ExtensionField<F, 2, EXT>,
    challenge_coefficients: &[(F, F)],
) {
    // we precompute challenges outside to avoid any manual extension ops here
    assert_eq!(polynomial_values.len(), values_at.len());
    assert_eq!(polynomial_values.len(), challenge_coefficients.len());

    let mut denom = ExtensionField::<F, 2, EXT>::from_coeff_in_base([domain_element, F::ZERO]);
    denom.sub_assign(&at);
    denom = denom.inverse().expect("must exist");

    let mut acc = ExtensionField::<F, 2, EXT>::ZERO;

    for ((poly_value, value_at), (c0, c1)) in polynomial_values
        .iter()
        .zip(values_at.iter())
        .zip(challenge_coefficients.iter())
    {
        // (f(x) - f(z))/(x - z)
        let mut tmp = *poly_value;
        tmp.sub_assign(value_at);

        let mut as_ext = ExtensionField::<F, 2, EXT> {
            coeffs: [*c0, *c1],
            _marker: std::marker::PhantomData,
        };

        as_ext.mul_assign(&tmp);
        acc.add_assign(&as_ext);
    }

    acc.mul_assign(&denom);

    dst.add_assign(&acc);
}
