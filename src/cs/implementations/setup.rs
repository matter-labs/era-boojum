use self::traits::GoodAllocator;

use super::hints::{DenseVariablesCopyHint, DenseWitnessCopyHint};
use super::polynomial_storage::{SetupBaseStorage, SetupStorage};
use super::utils::*;
use super::verifier::VerificationKey;
use super::*;
use crate::config::*;
use crate::cs::gates::lookup_marker::*;
use crate::cs::gates::nop_gate::NopGate;
use crate::cs::implementations::polynomial::*;
use crate::cs::implementations::reference_cs::*;
use crate::cs::implementations::verifier::VerificationKeyCircuitGeometry;
use crate::cs::oracle::merkle_tree::MerkleTreeWithCap;
use crate::cs::oracle::TreeHasher;
use crate::cs::toolboxes::gate_config::GateConfigurationHolder;
use crate::cs::toolboxes::static_toolbox::StaticToolboxHolder;
use crate::dag::CircuitResolver;
use crate::utils::*;
use std::alloc::Global;
use std::collections::HashSet;
use std::sync::Arc;

fn materialize_x_by_non_residue_polys<
    F: SmallField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
>(
    num_polys: usize,
    size: usize,
    worker: &Worker,
    ctx: &mut P::Context,
) -> Vec<GenericPolynomial<F, LagrangeForm, F, Global>> {
    debug_assert!(size > 0);
    let x_poly = materialize_x_poly::<F, P, Global>(size, worker);
    log!("Basic X poly was made");
    let non_residues = make_non_residues::<F>(num_polys - 1, size);
    log!("Non-residues were made");
    let mut result = Vec::with_capacity(num_polys);
    for _el in 0..(num_polys - 1) {
        result.push(x_poly.clone());
    }
    result.push(x_poly);

    assert_eq!(result.len(), non_residues.len() + 1);

    log!("Copies were made");

    worker.scope(num_polys - 1, |scope, chunk_size| {
        for (non_residues, polys) in non_residues
            .chunks(chunk_size)
            .zip(result[1..].chunks_mut(chunk_size))
        {
            let mut ctx = *ctx;
            scope.spawn(move |_| {
                for (non_res, poly) in non_residues.iter().zip(polys.iter_mut()) {
                    let non_res = P::constant(*non_res, &mut ctx);
                    for el in poly.storage.iter_mut() {
                        el.mul_assign(&non_res, &mut ctx);
                    }
                }
            });
        }
    });

    log!("Individual colums were computed");

    result
        .into_iter()
        .map(|el| {
            let storage = el.into_storage();
            let storage = P::vec_into_base_vec(storage);

            Polynomial::from_storage(storage)
        })
        .collect()
}

use crate::cs::traits::gate::FinalizationHintSerialized;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Default, PartialEq, Eq)]
pub struct FinalizationHintsForProver {
    pub row_finalization_hints: Vec<FinalizationHintSerialized>,
    pub column_finalization_hints: Vec<FinalizationHintSerialized>,
    pub nop_gates_to_add: usize,
    pub final_trace_len: usize,
    pub public_inputs: Vec<(usize, usize)>,
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
    pub fn pad_and_shrink(&mut self) -> (usize, FinalizationHintsForProver) {
        // first we pad-cleanup all the gates
        assert!(
            CFG::SetupConfig::KEEP_SETUP == true,
            "must have setup available to compute finalization hints"
        );

        let mut finalization_hints = FinalizationHintsForProver {
            public_inputs: self.public_inputs.clone(),
            ..Default::default()
        };

        let row_cleanups = std::mem::take(&mut self.row_cleanups);

        for el in row_cleanups.into_iter() {
            let hint = el(self, &None);
            assert!(hint.is_some());
            finalization_hints
                .row_finalization_hints
                .push(hint.unwrap());
        }

        // we cleaned up general purpose rows, but columns are a little hardner, because we need to
        // know a limit at this point

        let num_used_rows = self.next_available_row;
        // we can not use the last row in fact due to copy-permutation argument,
        // and may be some rows to ensuze ZK, so we compute it here
        let required_rows = num_used_rows + 1;
        assert!(required_rows <= self.max_trace_len);

        log!("Required rows {:?}", required_rows);
        log!(
            "lookup_tables_total_len = {}",
            self.lookups_tables_total_len()
        );

        let required_rows = std::cmp::max(required_rows, self.lookups_tables_total_len());

        let required_size = if required_rows.is_power_of_two() {
            required_rows
        } else {
            required_rows.next_power_of_two()
        };

        // now we can become more precise, and if gates over specialized columns were more full

        // max rows taken from general purpsoe columns is already in "required size"

        // for specialized gates
        let max_copiable_in_specialized_columns = if self
            .evaluation_data_over_specialized_columns
            .evaluators_over_specialized_columns
            .len()
            > 0
        {
            self.copy_permutation_data[self.parameters.num_columns_under_copy_permutation..]
                .iter()
                .map(|el| el.len())
                .max()
                .unwrap_or(0)
        } else {
            0
        };
        let max_witnesses_in_general_purpose_columns = self.witness_placement_data
            [..self.parameters.num_witness_columns]
            .iter()
            .map(|el| el.len())
            .max()
            .unwrap_or(0);
        let max_witnesses_in_specialized_columns = if self
            .evaluation_data_over_specialized_columns
            .evaluators_over_specialized_columns
            .len()
            > 0
        {
            self.witness_placement_data[self.parameters.num_witness_columns..]
                .iter()
                .map(|el| el.len())
                .max()
                .unwrap_or(0)
        } else {
            0
        };
        let max_constants_for_general_purpose_gates = self.constants_requested_per_row.len();
        let max_in_column_for_specialized_gates = self
            .constants_for_gates_in_specialized_mode
            .iter()
            .map(|el| el.len())
            .max()
            .unwrap_or(0);

        log!("required size = {}", required_size);
        log!(
            "max_copiable_in_specialized_columns = {}",
            max_copiable_in_specialized_columns
        );
        log!(
            "max_witnesses_in_general_purpose_columns = {}",
            max_witnesses_in_general_purpose_columns
        );
        log!(
            "max_witnesses_in_specialized_columns = {}",
            max_witnesses_in_specialized_columns
        );
        log!(
            "max_constants_for_general_purpose_gates = {}",
            max_constants_for_general_purpose_gates
        );
        log!(
            "max_in_column_for_specialized_gates = {}",
            max_in_column_for_specialized_gates
        );

        assert!(max_constants_for_general_purpose_gates <= required_size);

        let mut preliminary_required_size = [
            required_size,
            max_copiable_in_specialized_columns,
            max_witnesses_in_general_purpose_columns,
            max_witnesses_in_specialized_columns,
            max_constants_for_general_purpose_gates,
            max_in_column_for_specialized_gates,
        ]
        .into_iter()
        .max()
        .unwrap_or(0);

        if preliminary_required_size.is_power_of_two() == false {
            preliminary_required_size = preliminary_required_size.next_power_of_two();
        }

        assert!(
            preliminary_required_size.is_power_of_two(),
            "size after columns padding is {} that is not power of two",
            preliminary_required_size,
        );

        let columns_cleanups = std::mem::take(&mut self.columns_cleanups);

        for el in columns_cleanups.into_iter() {
            let hint = el(self, preliminary_required_size, &None);
            assert!(hint.is_some());
            finalization_hints
                .column_finalization_hints
                .push(hint.unwrap());
        }

        // now self-check
        let max_copiable_in_specialized_columns = if self
            .evaluation_data_over_specialized_columns
            .evaluators_over_specialized_columns
            .len()
            > 0
        {
            self.copy_permutation_data[self.parameters.num_columns_under_copy_permutation..]
                .iter()
                .map(|el| el.len())
                .max()
                .unwrap_or(0)
        } else {
            0
        };
        let max_witnesses_in_general_purpose_columns = self.witness_placement_data
            [..self.parameters.num_witness_columns]
            .iter()
            .map(|el| el.len())
            .max()
            .unwrap_or(0);
        let max_witnesses_in_specialized_columns = if self
            .evaluation_data_over_specialized_columns
            .evaluators_over_specialized_columns
            .len()
            > 0
        {
            self.witness_placement_data[self.parameters.num_witness_columns..]
                .iter()
                .map(|el| el.len())
                .max()
                .unwrap_or(0)
        } else {
            0
        };
        let max_constants_for_general_purpose_gates = self.constants_requested_per_row.len();
        let max_in_column_for_specialized_gates = self
            .constants_for_gates_in_specialized_mode
            .iter()
            .map(|el| el.len())
            .max()
            .unwrap_or(0);

        let mut precise_required_size = [
            required_size,
            max_copiable_in_specialized_columns,
            max_witnesses_in_general_purpose_columns,
            max_witnesses_in_specialized_columns,
            max_constants_for_general_purpose_gates,
            max_in_column_for_specialized_gates,
        ]
        .into_iter()
        .max()
        .unwrap_or(0);

        // some gates may out-out from padding to full column for now
        assert!(preliminary_required_size >= precise_required_size);
        if precise_required_size.is_power_of_two() == false {
            precise_required_size = precise_required_size.next_power_of_two();
        }
        assert_eq!(preliminary_required_size, precise_required_size);

        // now we can shrink/cut polys to desired sizes

        for column in self.copy_permutation_data.iter_mut() {
            column.truncate(precise_required_size);
        }

        // TODO: we can use other types of gates here, to avoid extending selectors

        assert!(self.gates_application_sets.len() <= precise_required_size);
        let nop_gates_to_add = precise_required_size - self.gates_application_sets.len();
        finalization_hints.nop_gates_to_add = nop_gates_to_add;
        for _ in 0..nop_gates_to_add {
            let _ = NopGate::new().add_to_cs(self);
        }

        // dbg!(&self.gates_ordered_eval_functions_set);

        assert!(self.constants_requested_per_row.len() <= precise_required_size);
        self.constants_requested_per_row
            .resize(precise_required_size, SmallVec::new());
        for dst in self.constants_for_gates_in_specialized_mode.iter_mut() {
            dst.resize(precise_required_size, F::ZERO);
        }

        log!("precise_required_size = {}", precise_required_size);

        self.max_trace_len = precise_required_size;
        finalization_hints.final_trace_len = precise_required_size;

        // we should make sure that we do not have unfilled specialized columns
        for (column, els) in self.copy_permutation_data
            [self.parameters.num_columns_under_copy_permutation..]
            .iter()
            .enumerate()
        {
            for (row, el) in els.iter().enumerate() {
                debug_assert!(
                    el.is_placeholder() == false,
                    "not fully padded specialized columns {} at row {}",
                    column,
                    row
                );
            }
        }

        for (column, els) in self.witness_placement_data[self.parameters.num_witness_columns..]
            .iter()
            .enumerate()
        {
            for (row, el) in els.iter().enumerate() {
                debug_assert!(
                    el.is_placeholder() == false,
                    "not fully padded specialized columns {} at row {}",
                    column,
                    row
                );
            }
        }

        assert!(precise_required_size >= self.lookups_tables_total_len());

        (precise_required_size, finalization_hints)
    }

    pub fn pad_and_shrink_using_hint(&mut self, hint: &FinalizationHintsForProver) {
        // first we pad-cleanup all the gates

        self.public_inputs = hint.public_inputs.clone();

        let preliminary_required_size = hint.final_trace_len;

        let row_cleanups = std::mem::take(&mut self.row_cleanups);
        assert_eq!(row_cleanups.len(), hint.row_finalization_hints.len());

        for (el, hint) in row_cleanups
            .into_iter()
            .zip(hint.row_finalization_hints.iter())
        {
            let hint = Some(hint.clone());
            let _hint = el(self, &hint);
        }

        let columns_cleanups = std::mem::take(&mut self.columns_cleanups);
        assert_eq!(columns_cleanups.len(), hint.column_finalization_hints.len());

        for (el, hint) in columns_cleanups
            .into_iter()
            .zip(hint.column_finalization_hints.iter())
        {
            let hint = Some(hint.clone());
            let _hint = el(self, preliminary_required_size, &hint);
        }

        // TODO: we can use other types of gates here, to avoid extending selectors

        for _ in 0..hint.nop_gates_to_add {
            let _ = NopGate::new().add_to_cs(self);
        }

        self.max_trace_len = hint.final_trace_len;
    }
}

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        CFG: CSConfig,
        A: GoodAllocator,
    > CSReferenceAssembly<F, P, CFG, A>
{
    pub fn create_permutation_polys(
        &self,
        worker: &Worker,
        ctx: &mut P::Context,
    ) -> Vec<GenericPolynomial<F, LagrangeForm, P, Global>> {
        assert!(
            CFG::SetupConfig::KEEP_SETUP,
            "CS is not configured to have setup available"
        );

        log!("Creating placeholders");

        let capacity = self.parameters.num_columns_under_copy_permutation
            + self
                .evaluation_data_over_specialized_columns
                .total_num_variables_for_specialized_columns;

        let mut result =
            materialize_x_by_non_residue_polys::<F, P>(capacity, self.max_trace_len, worker, ctx);
        // now we should make cyclic permutations over all occurances of our variables

        log!("Making permutations");

        // even though it captures witness, we are ok with it being a scratch space for setup
        let mut scratch_space =
            vec![(F::ZERO, (0u32, 0u32)); self.next_available_place_idx as usize];

        for (column_idx, (column, poly)) in self
            .copy_permutation_data
            .iter()
            .zip(result.iter_mut())
            .enumerate()
        {
            for (row, var) in column.iter().enumerate() {
                if var.is_placeholder() {
                    // undefined value, so never copied
                    continue;
                }
                let var_idx = var.as_variable_index();
                let previous_occurance_data = &mut scratch_space[var_idx as usize];
                if previous_occurance_data.0 == F::ZERO {
                    debug_assert!(previous_occurance_data.1 .0 == 0);
                    debug_assert!(previous_occurance_data.1 .1 == 0);

                    // it can be zero IFF we never encountered it
                    // In addition we store a point of the first occurance
                    *previous_occurance_data = (poly.storage[row], (column_idx as u32, row as u32));
                } else {
                    // we encountered this var before and stored it's PREVIOUS occurance
                    // (read from poly) as field element, so we write previous occurance HERE,
                    // and store this occurance as previous one
                    std::mem::swap(&mut previous_occurance_data.0, &mut poly.storage[row]);
                }
            }
        }

        // final pass is to finish cycle

        for (value, (first_encountered_column, first_encountered_row)) in scratch_space.into_iter()
        {
            if value == F::ZERO {
                debug_assert!(first_encountered_column == 0);
                debug_assert!(first_encountered_row == 0);
                // never encountered
                continue;
            }

            // worst case it reassign same, otherwise we reassign LAST occurance into first
            result[first_encountered_column as usize].storage[first_encountered_row as usize] =
                value;
        }

        log!("Done creating permutation polys");

        result
            .into_iter()
            .map(|el| {
                let storage = el.into_storage();
                let storage = P::vec_from_base_vec(storage);

                GenericPolynomial::from_storage(storage)
            })
            .collect()
    }

    pub fn compute_selectors_and_constants_placement(&self) -> TreeNode {
        // every gate has a specific degree that it evaluates too,
        // and potentially non-trivial selector's path that
        // looks like unbalanced tree

        //             X
        //       sel0   (1-sel0)
        //   sel1  (1-sel1)  sel1   (1-sel1)
        //    G0     G1       G2    sel2   (1-sel2)
        //                           G3       G4

        // and our task is to find placements of gates and selectors
        // such that it leads to the minimal value of
        // degree(gate) * len(selectors path) from the root
        // There are 2 rules
        // - placing gate into node blocks it
        // - adding selector increases the degree by 1

        // Additional constraint is that gates require some number of constants
        // to evaluate themselves, and we should also to keep to the minimum a number of gate constants
        // along the path

        // We also know the worst case - dense selectors near the root and then gates,
        // but it would lead to potentiall suboptimal evaluation complexity.
        // Even though the full complexity of exhaustive search is small,
        // we can do better and deterministically by observing that
        // we do not have wide variability, and can iteratively simplify the construction
        // by moving nodes up

        log!("Computing placement");

        // we compute placement only for gates that span over general-purpose columns

        if self
            .evaluation_data_over_general_purpose_columns
            .evaluators_over_general_purpose_columns
            .len()
            == 0
        {
            unimplemented!("Not yet tested to have only specialized columns");
        }

        if self
            .evaluation_data_over_general_purpose_columns
            .evaluators_over_general_purpose_columns
            .len()
            == 1
        {
            let evaluator = &self
                .evaluation_data_over_general_purpose_columns
                .evaluators_over_general_purpose_columns[0];
            let needs_selector = evaluator.gate_purpose.needs_selector();

            assert!(matches!(self.lookup_parameters, LookupParameters::NoLookup));

            return TreeNode::GateOnly(GateDescription {
                gate_idx: 0,
                needs_selector,
                num_constants: evaluator.num_required_constants,
                degree: evaluator.max_constraint_degree,
                is_lookup: false,
            });
        }

        // longer path - work with a filtered set
        let mut all_gates: Vec<_> = self
            .evaluation_data_over_general_purpose_columns
            .evaluators_over_general_purpose_columns
            .iter()
            .enumerate()
            .map(|(i, evaluator)| {
                let mut is_lookup = false;
                let mut num_constants = evaluator.num_required_constants;
                match self.lookup_parameters {
                    LookupParameters::NoLookup => {}
                    LookupParameters::TableIdAsConstant { .. } => {
                        if i == 0 {
                            assert_eq!(
                                evaluator.evaluator_type_id,
                                std::any::TypeId::of::<LookupGateMarkerFormalEvaluator>(),
                                "lookup marker must be always first"
                            );
                            assert_eq!(evaluator.num_required_constants, 0);
                            is_lookup = true;
                            num_constants = 1;
                        }
                    },
                    LookupParameters::TableIdAsVariable { .. } => {
                        if i == 0 {
                            assert_eq!(
                                evaluator.evaluator_type_id,
                                std::any::TypeId::of::<LookupGateMarkerFormalEvaluator>(),
                                "lookup marker must be always first"
                            );
                            assert_eq!(evaluator.num_required_constants, 0);
                            is_lookup = true;
                        }
                    },
                    LookupParameters::UseSpecializedColumnsWithTableIdAsConstant { .. } | LookupParameters::UseSpecializedColumnsWithTableIdAsVariable { .. } => {
                        if i == 0 {
                            assert_ne!(
                                evaluator.evaluator_type_id,
                                std::any::TypeId::of::<LookupGateMarkerFormalEvaluator>(),
                                "lookup marker must not be present in general purpose gates in case of specialized lookup"
                            );
                        }
                    },
                }

                GateDescription {
                    gate_idx: i,
                    needs_selector: evaluator.gate_purpose.needs_selector(),
                    num_constants,
                    degree: evaluator.max_constraint_degree,
                    is_lookup,
                }
        })
            .map(|el| {
                if el.degree == 0 {
                    assert!(el.num_constants == 0 || el.is_lookup);
                }

                el
            })
            .filter(|a| {
                // NOP gate formally has no relations, but in this case we have to formally add extra selector
                a.degree > 0 || a.needs_selector || a.is_lookup
            })
            .collect();

        // if we support lookup then we should work with a gate marker
        match self.lookup_parameters {
            LookupParameters::NoLookup => {}
            LookupParameters::TableIdAsConstant { .. }
            | LookupParameters::TableIdAsVariable { .. } => {
                assert_eq!(
                    self.evaluation_data_over_general_purpose_columns
                        .evaluators_over_general_purpose_columns[0]
                        .evaluator_type_id,
                    std::any::TypeId::of::<LookupGateMarkerFormalEvaluator>(),
                    "lookup marker must be always first"
                );
            }
            LookupParameters::UseSpecializedColumnsWithTableIdAsConstant { .. }
            | LookupParameters::UseSpecializedColumnsWithTableIdAsVariable { .. } => {
                assert_eq!(
                    self.evaluation_data_over_specialized_columns
                        .evaluators_over_specialized_columns[0]
                        .evaluator_type_id,
                    std::any::TypeId::of::<LookupGateMarkerFormalEvaluator>(),
                    "lookup marker must be always first"
                );
            }
        }

        // after division, so -1
        let max_degree = all_gates
            .iter()
            .map(|el| el.degree_at_depth(0))
            .max()
            .unwrap()
            - 1;
        // max constants any of gates would require
        let max_num_constants = all_gates.iter().map(|el| el.num_constants).max().unwrap();

        // stable sort by composit key
        // of degree, and then break ties by num required constants
        // because no matter what happens we want to put gates with highest
        // degree and highest number of constants closer to the "root"
        all_gates.sort_by(|a, b| match b.degree.cmp(&a.degree) {
            std::cmp::Ordering::Equal => b.num_constants.cmp(&a.num_constants),
            a => a,
        });

        // we know that
        // - it will be at least 1 selector term in front of it, so it's +1 degree
        // - and then we will divide by vanishing poly, so it's -1 degree

        // now we can determine preliminary target - what will be our max degree to try to get
        let mut target_degree = if max_degree.is_power_of_two() {
            max_degree
        } else {
            max_degree.next_power_of_two()
        };

        assert!(
            self.parameters.num_constant_columns >= max_num_constants,
            "Circuit allows {} constant polynomials, but at least of the the gates requires {}",
            self.parameters.num_constant_columns,
            max_num_constants,
        );

        let starting_num_constants = max_num_constants;

        log!(
            "Computing placement for target degree {} and initially {} constant columns",
            target_degree,
            starting_num_constants
        );

        for _ in 0..4 {
            if let Some(found_strategy) = try_find_placement_for_degree(
                all_gates.clone(),
                target_degree,
                starting_num_constants,
            ) {
                let (degree, num_constants) = found_strategy.compute_stats();
                log!(
                    "Placement is found for quotient degree {} and {} constant columns",
                    degree,
                    num_constants
                );
                return found_strategy;
            } else {
                target_degree *= 2;
            }
        }

        panic!(
            "Can not find suited placement degree for target degree {}",
            target_degree
        );
    }

    pub fn create_constant_setup_polys(
        &self,
        worker: &Worker,
    ) -> (
        Vec<GenericPolynomial<F, LagrangeForm, P, Global>>,
        TreeNode,
        usize,
    ) {
        assert!(
            CFG::SetupConfig::KEEP_SETUP,
            "CS is not configured to have setup available"
        );

        let selectors_placement = self.compute_selectors_and_constants_placement();

        let (
            max_constraint_contribution_degree,
            number_of_constant_polys_for_general_purpose_gates,
        ) = selectors_placement.compute_stats();

        let extra_polys_for_selectors = number_of_constant_polys_for_general_purpose_gates
            - self.parameters.num_constant_columns;
        log!("extra_polys_for_selector = {}", extra_polys_for_selectors);

        let quotient_degree_from_constraits = if max_constraint_contribution_degree > 0 {
            max_constraint_contribution_degree - 1
        } else {
            0
        };

        assert!(self.max_trace_len.is_power_of_two());

        let storage = initialize_with_alignment_of::<_, P>(F::ZERO, self.max_trace_len);
        let poly = Polynomial::from_storage(storage);

        let total_constant_polys = number_of_constant_polys_for_general_purpose_gates
            + self
                .evaluation_data_over_specialized_columns
                .total_num_constants_for_specialized_columns;

        let mut result = Vec::with_capacity(total_constant_polys);
        if total_constant_polys > 0 {
            for _ in 0..(total_constant_polys - 1) {
                result.push(poly.clone_respecting_allignment::<P>());
            }
            result.push(poly);
        }

        // now we have to walk over our set of gates,
        // and perform placement of selectors

        let min_lde_degree = if quotient_degree_from_constraits.is_power_of_two() {
            quotient_degree_from_constraits
        } else {
            quotient_degree_from_constraits.next_power_of_two()
        };

        let mut paths_mappings = vec![];

        for (idx, evaluator) in self
            .evaluation_data_over_general_purpose_columns
            .evaluators_over_general_purpose_columns
            .iter()
            .enumerate()
        {
            use crate::cs::traits::evaluator::GatePurpose;
            if matches!(evaluator.gate_purpose, GatePurpose::MarkerWithoutSelector) {
                paths_mappings.push(vec![]);
                continue;
            }

            let path = selectors_placement
                .output_placement(idx)
                .expect("for non trivial gates we should have placement");
            paths_mappings.push(path);
        }

        debug_assert_eq!(
            self.gates_application_sets.len(),
            self.constants_requested_per_row.len()
        );
        if self.constants_for_gates_in_specialized_mode.len() > 0 {
            debug_assert_eq!(
                self.gates_application_sets.len(),
                self.constants_for_gates_in_specialized_mode[0].len()
            );
        }

        let chunk_size = if result.len() > 0 {
            worker.get_chunk_size(result[0].storage.len())
        } else if self.constants_for_gates_in_specialized_mode.len() > 0 {
            worker.get_chunk_size(self.constants_for_gates_in_specialized_mode[0].len())
        } else {
            let result = result
                .into_iter()
                .map(|el| {
                    let storage = el.into_storage();
                    let storage = P::vec_from_base_vec(storage);

                    GenericPolynomial::from_storage(storage)
                })
                .collect();

            return (result, selectors_placement, min_lde_degree);
        };

        let mut transposed_chunks: GenericPolynomialChunksMut<'_, F, LagrangeForm> =
            GenericPolynomialChunksMut::from_polys_with_chunk_size(&mut result, chunk_size);
        let transcposed_constants_chunks_for_specialized_gates: GenericPolynomialChunks<
            '_,
            F,
            LagrangeForm,
        > = GenericPolynomialChunks::from_columns_with_chunk_size(
            &self.constants_for_gates_in_specialized_mode,
            self.max_trace_len,
            chunk_size,
        );
        let paths_mappings = &paths_mappings;

        worker.scope(0, |scope, _| {
            for (((gates_chunk, constants_chunk), specialized_constants_chunk), rows_chunk) in
                self.gates_application_sets.chunks(chunk_size)
                .zip(self.constants_requested_per_row.chunks(chunk_size))
                .zip(transcposed_constants_chunks_for_specialized_gates.inner.iter())
                .zip(transposed_chunks.inner.iter_mut())
            {
                scope.spawn(move |_| {
                    for (subrow_idx, (evaluator_idx, constants)) in
                        gates_chunk.iter().zip(constants_chunk.iter()).enumerate()
                    {
                        let mut placement_constants_iter = paths_mappings[*evaluator_idx].iter();
                        debug_assert!(
                            constants.len() <= self.parameters.num_constant_columns,
                            "there were {} allowed constants for general purpose gates in the system, but there is a request for {}",
                            self.parameters.num_constant_columns,
                            constants.len(),
                        );
                        let mut constants_iter = constants.iter();

                        for column in rows_chunk.iter_mut() {
                            if let Some(selector) = placement_constants_iter.next() {
                                if *selector {
                                    column[subrow_idx] = F::ONE;
                                }
                            } else if let Some(constant) = constants_iter.next().copied() {
                                column[subrow_idx] = constant;
                            }
                        }

                        if specialized_constants_chunk.len() == 0 {
                            debug_assert!(placement_constants_iter.next().is_none());
                        }
                        debug_assert!(constants_iter.next().is_none());
                    }

                    // and then we need to copy at the proper offset

                    assert_eq!(
                        rows_chunk[number_of_constant_polys_for_general_purpose_gates..].len(),
                        specialized_constants_chunk.len()
                    );
                    for (dst, src) in rows_chunk[number_of_constant_polys_for_general_purpose_gates..].iter_mut()
                        .zip(specialized_constants_chunk.iter()) {
                            dst.copy_from_slice(src);
                        }
                });
            }
        });

        let result = result
            .into_iter()
            .map(|el| {
                let storage = el.into_storage();
                let storage = P::vec_from_base_vec(storage);

                GenericPolynomial::from_storage(storage)
            })
            .collect();

        (result, selectors_placement, min_lde_degree)
    }

    pub fn create_lookup_tables_columns_polys(
        &self,
        _worker: &Worker,
    ) -> Vec<GenericPolynomial<F, LagrangeForm, P, Global>> {
        assert!(
            CFG::SetupConfig::KEEP_SETUP,
            "CS is not configured to have setup available"
        );

        if self.lookup_parameters.lookup_is_allowed() == false {
            return vec![];
        }

        assert!(self.max_trace_len >= self.lookups_tables_total_len());

        let storage = initialize_with_alignment_of::<_, P>(F::ZERO, self.max_trace_len);
        let poly = Polynomial::<F, LagrangeForm, Global>::from_storage(storage);
        let total_lookup_columns = self.lookup_parameters.lookup_width() + 1; // + 1 for IDs
        let mut result = Vec::with_capacity(total_lookup_columns);
        for _ in 0..(total_lookup_columns - 1) {
            result.push(poly.clone_respecting_allignment::<P>());
        }
        result.push(poly);

        // just copy
        let mut idx = 0;
        for (table_id, table) in self.lookup_tables.iter().enumerate() {
            let table_id = table_id + INITIAL_LOOKUP_TABLE_ID_VALUE as usize;
            let table_id = F::from_u64_unchecked(table_id as u64);
            assert_eq!(result.len(), table.width() + 1);
            for row in 0..table.table_size() {
                let content = table.content_at_row(row);
                debug_assert_eq!(content.len() + 1, result.len());
                for (dst, src) in result[..content.len()].iter_mut().zip(content.iter()) {
                    dst.storage[idx] = *src;
                }
                let dst = &mut result[content.len()];
                dst.storage[idx] = table_id;
                idx += 1;
            }
        }

        result
            .into_iter()
            .map(|el| {
                let storage = el.into_storage();
                let storage = P::vec_from_base_vec(storage);

                GenericPolynomial::from_storage(storage)
            })
            .collect()
    }

    fn compute_table_ids_column_idxes(
        &self,
        selectors_placement: &TreeNode,
        offset_for_special_purpose_constants: usize,
    ) -> Vec<usize> {
        match self.lookup_parameters {
            LookupParameters::NoLookup => vec![],
            LookupParameters::TableIdAsVariable { .. }
            | LookupParameters::UseSpecializedColumnsWithTableIdAsVariable { .. } => vec![],
            LookupParameters::TableIdAsConstant { share_table_id, .. } => {
                assert!(share_table_id, "other option is not yet implemented");
                let lookup_table_evaluator_idx = 0;
                let path = selectors_placement
                    .output_placement(lookup_table_evaluator_idx)
                    .expect("selector path for lookup");
                let column_idx = path.len();

                vec![column_idx]
            }
            LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                share_table_id, ..
            } => {
                assert!(share_table_id, "other option is not yet implemented");
                assert_eq!(
                    self.evaluation_data_over_specialized_columns
                        .evaluators_over_specialized_columns[0]
                        .evaluator_type_id,
                    std::any::TypeId::of::<LookupGateMarkerFormalEvaluator>()
                );
                assert_eq!(
                    self.evaluation_data_over_specialized_columns
                        .gate_type_ids_for_specialized_columns[0],
                    std::any::TypeId::of::<LookupFormalGate>()
                );

                let mut result = vec![];
                for idx in
                    offset_for_special_purpose_constants..(offset_for_special_purpose_constants + 1)
                {
                    result.push(idx);
                }

                result
            }
        }
    }

    pub fn create_base_setup(
        &self,
        worker: &Worker,
        ctx: &mut P::Context,
    ) -> SetupBaseStorage<F, P, Global, Global> {
        assert!(
            CFG::SetupConfig::KEEP_SETUP,
            "CS is not configured to have setup available"
        );

        // first we need to ensure that all the general purpose gates
        // that were allowed actually were encountered in the system. Even though it's not strictly requried,
        // we still want to make some safety precautions

        // May be we can precompute such index during synthesis instead

        let mut evaluators_to_encounter = HashSet::new();
        for i in 0..self
            .evaluation_data_over_general_purpose_columns
            .evaluators_over_general_purpose_columns
            .len()
        {
            evaluators_to_encounter.insert(i);
        }

        for el in self.gates_application_sets.iter() {
            if evaluators_to_encounter.is_empty() {
                break;
            }

            evaluators_to_encounter.remove(el);
        }

        if evaluators_to_encounter.is_empty() == false {
            let mut not_encountered = vec![];
            for el in evaluators_to_encounter.into_iter() {
                let evaluator = &self
                    .evaluation_data_over_general_purpose_columns
                    .evaluators_over_general_purpose_columns[el];
                not_encountered.push(evaluator.debug_name.clone());
            }
            panic!("Some evaluators are claimed allowed, but not encountered for general purpose columns: {}", not_encountered.join(", "));
        }

        log!("Creating constant polys");
        let (constant_columns, selectors_placement, min_degree) =
            self.create_constant_setup_polys(worker);

        log!("min_degree = {}", min_degree);

        let (_, total_num_constants_for_gates_over_general_purpose_columns) =
            selectors_placement.compute_stats();

        log!("Creating permutation polys");
        let copy_permutataion_columns = self.create_permutation_polys(worker, ctx);

        log!("Creating lookup tables polys");

        let lookup_tables_columns = self.create_lookup_tables_columns_polys(worker);

        let table_ids_column_idxes = self.compute_table_ids_column_idxes(
            &selectors_placement,
            total_num_constants_for_gates_over_general_purpose_columns,
        );

        log!("Setup is made");

        let copy_permutataion_columns = copy_permutataion_columns
            .into_iter()
            .map(Arc::new)
            .collect();
        let constant_columns = constant_columns.into_iter().map(Arc::new).collect();
        let lookup_tables_columns = lookup_tables_columns.into_iter().map(Arc::new).collect();

        SetupBaseStorage {
            copy_permutation_polys: copy_permutataion_columns,
            constant_columns,
            lookup_tables_columns,
            table_ids_column_idxes,
            selectors_placement,
        }
    }

    pub fn materialize_setup_storage(
        &self,
        fri_lde_factor: usize,
        worker: &Worker,
        ctx: &mut P::Context,
    ) -> (SetupStorage<F, P, Global, Global>, TreeNode, usize, usize) {
        assert!(
            CFG::SetupConfig::KEEP_SETUP,
            "CS is not configured to have setup available"
        );

        let (constant_columns, gate_placement, min_degree) =
            self.create_constant_setup_polys(worker);

        // quotient degree is needed for chunking of quotient poly

        let quotient_degree_from_general_purpose_gate_terms = min_degree;

        let max_degree_from_specialized_gates = self
            .evaluation_data_over_specialized_columns
            .evaluators_over_specialized_columns
            .iter()
            .map(|el| el.max_constraint_degree - 1)
            .max()
            .unwrap_or(0);

        let quotient_degree_from_gate_terms = std::cmp::max(
            quotient_degree_from_general_purpose_gate_terms,
            max_degree_from_specialized_gates,
        );

        let min_lde_degree_for_gates = if quotient_degree_from_gate_terms.is_power_of_two() {
            quotient_degree_from_gate_terms
        } else {
            quotient_degree_from_gate_terms.next_power_of_two()
        };

        let quotient_degree = if min_lde_degree_for_gates.is_power_of_two() {
            min_lde_degree_for_gates
        } else {
            min_lde_degree_for_gates.next_power_of_two()
        };

        let precomputation_degree = std::cmp::max(quotient_degree, fri_lde_factor);

        log!(
            "Will use degree {} for precomputations",
            precomputation_degree
        );

        // now compute

        let copy_permutataion_columns = self.create_permutation_polys(worker, ctx);

        let lookup_tables_columns = self.create_lookup_tables_columns_polys(worker);

        let (_, total_num_constants_for_gates_over_general_purpose_columns) =
            gate_placement.compute_stats();
        let table_ids_column_idxes = self.compute_table_ids_column_idxes(
            &gate_placement,
            total_num_constants_for_gates_over_general_purpose_columns,
        );

        let copy_permutataion_columns = copy_permutataion_columns
            .into_iter()
            .map(Arc::new)
            .collect();
        let constant_columns = constant_columns.into_iter().map(Arc::new).collect();
        let lookup_tables_columns = lookup_tables_columns.into_iter().map(Arc::new).collect();

        (
            SetupStorage::from_base_trace(
                copy_permutataion_columns,
                constant_columns,
                lookup_tables_columns,
                table_ids_column_idxes,
                precomputation_degree,
                worker,
                ctx,
            ),
            gate_placement,
            min_degree,
            quotient_degree,
        )
    }

    pub fn materialize_setup_storage_and_vk<H: TreeHasher<F>>(
        &self,
        fri_lde_factor: usize,
        cap_size: usize,
        worker: &Worker,
        ctx: &mut P::Context,
    ) -> (
        SetupStorage<F, P, Global, Global>,
        VerificationKey<F, H>,
        MerkleTreeWithCap<F, H>,
    ) {
        assert!(
            CFG::SetupConfig::KEEP_SETUP,
            "CS is not configured to have setup available"
        );

        let (setup, gate_placement, _min_degree, quotient_degree) =
            self.materialize_setup_storage(fri_lde_factor, worker, ctx);

        log!("Will use LDE factor of {} for setup tree", fri_lde_factor);

        let mut source = vec![];
        source.extend(
            setup
                .copy_permutation_polys
                .iter()
                .map(|el| el.subset_for_degree(fri_lde_factor)),
        );
        source.extend(
            setup
                .constant_columns
                .iter()
                .map(|el| el.subset_for_degree(fri_lde_factor)),
        );
        source.extend(
            setup
                .lookup_tables_columns
                .iter()
                .map(|el| el.subset_for_degree(fri_lde_factor)),
        );

        let setup_tree = MerkleTreeWithCap::<F, H>::construct(source, cap_size, worker);

        let cap = setup_tree.get_cap();

        let (_, total_num_constants_for_gates_over_general_purpose_columns) =
            gate_placement.compute_stats();
        let table_ids_column_idxes = self.compute_table_ids_column_idxes(
            &gate_placement,
            total_num_constants_for_gates_over_general_purpose_columns,
        );
        let extra_constant_polys_for_selectors =
            total_num_constants_for_gates_over_general_purpose_columns
                - self.parameters.num_constant_columns;

        let fixed_parameters = VerificationKeyCircuitGeometry {
            parameters: self.parameters,
            lookup_parameters: self.lookup_parameters,
            domain_size: self.max_trace_len as u64,
            total_tables_len: self.lookups_tables_total_len() as u64,
            public_inputs_locations: self.public_inputs.clone(),
            extra_constant_polys_for_selectors,
            table_ids_column_idxes,
            quotient_degree,
            selectors_placement: gate_placement,
            fri_lde_factor,
            cap_size,
        };

        let vk = VerificationKey {
            fixed_parameters,
            setup_merkle_tree_cap: cap,
        };

        (setup, vk, setup_tree)
    }

    pub fn create_copy_hints(&self) -> (DenseVariablesCopyHint, DenseWitnessCopyHint) {
        assert!(
            CFG::SetupConfig::KEEP_SETUP,
            "CS is not configured to have setup available"
        );

        let vars_hint = DenseVariablesCopyHint {
            maps: self.copy_permutation_data.clone(),
        };

        let witness_hints = DenseWitnessCopyHint {
            maps: self.witness_placement_data.clone(),
        };

        (vars_hint, witness_hints)
    }

    pub fn get_full_setup<H: TreeHasher<F>>(
        &self,
        worker: &Worker,
        fri_lde_factor: usize,
        merkle_tree_cap_size: usize,
    ) -> (
        SetupBaseStorage<F, P, Global, Global>,
        SetupStorage<F, P, Global, Global>,
        VerificationKey<F, H>,
        MerkleTreeWithCap<F, H>,
        DenseVariablesCopyHint,
        DenseWitnessCopyHint,
    ) {
        let mut ctx = P::Context::placeholder();

        let setup_base = self.create_base_setup(worker, &mut ctx);
        let (setup, vk, setup_tree) = self.materialize_setup_storage_and_vk::<H>(
            fri_lde_factor,
            merkle_tree_cap_size,
            worker,
            &mut ctx,
        );
        let (vars_hint, witness_hints) = self.create_copy_hints();

        (setup_base, setup, vk, setup_tree, vars_hint, witness_hints)
    }

    pub fn print_gate_stats(&self) {
        let mut total_general_purpose = 0;
        for (idx, gate) in self
            .evaluation_data_over_general_purpose_columns
            .evaluators_over_general_purpose_columns
            .iter()
            .enumerate()
        {
            let num_applications = self
                .gates_application_sets
                .iter()
                .filter(|id| **id == idx)
                .count();

            let instances_per_row = gate.num_repetitions_on_row;
            log!(
                "Have {} instances of {} gate, with {} repetitions per row ({} instances total)",
                num_applications,
                &gate.debug_name,
                instances_per_row,
                num_applications * instances_per_row,
            );

            total_general_purpose += num_applications;
        }

        log!("In total {} general purpose rows", total_general_purpose);

        for (gate_type_id, evaluator_idx) in self
            .evaluation_data_over_specialized_columns
            .gate_type_id_into_evaluator_index_over_specialized_columns
            .iter()
        {
            let num_applications = self.specialized_gates_rough_stats[gate_type_id];
            let evaluator = &self
                .evaluation_data_over_specialized_columns
                .evaluators_over_specialized_columns[*evaluator_idx];
            log!(
                "Have {} rows of specialized {} gate",
                num_applications,
                &evaluator.debug_name
            );
        }
    }
}

fn try_find_placement_for_degree(
    gates_set: Vec<GateDescription>,
    degree_bound: usize,
    starting_num_constants: usize,
) -> Option<TreeNode> {
    let num_selectors_upper_bound = if gates_set.len().is_power_of_two() {
        gates_set.len().trailing_zeros()
    } else {
        gates_set.len().next_power_of_two().trailing_zeros()
    };

    for i in 0..=(num_selectors_upper_bound + 1) {
        let num_constants_bound = starting_num_constants + (i as usize);

        let mut tree = TreeNode::Empty;
        let mut made_placement = true;

        for gate in gates_set.iter().copied() {
            if let Some(new_tree) = tree.try_add_gate(gate, degree_bound, num_constants_bound, 0) {
                tree = new_tree;
            } else {
                made_placement = false;
                break;
            }
        }

        if made_placement {
            return Some(tree);
        }
    }

    None
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GateDescription {
    pub gate_idx: usize,
    pub num_constants: usize,
    pub degree: usize,
    pub needs_selector: bool,
    pub is_lookup: bool,
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TreeNode {
    Empty,
    GateOnly(GateDescription),
    Fork { left: Box<Self>, right: Box<Self> },
}

impl GateDescription {
    pub(crate) fn new_for_trivial_gate(
        gate_idx: usize,
        num_constants: usize,
        degree: usize,
        needs_selector: bool,
    ) -> Self {
        Self {
            gate_idx,
            num_constants,
            degree,
            needs_selector,
            is_lookup: false,
        }
    }

    pub(crate) fn degree_at_depth(&self, depth: usize) -> usize {
        if self.is_lookup == false {
            depth + self.degree
        } else {
            // lookup argument is of degree 2 in LHS of A(X) * (f(x) + beta),
            // or "depth" in RHS for selector product
            std::cmp::max(depth, 2)
        }
    }
}

impl TreeNode {
    pub fn compute_stats(&self) -> (usize, usize) {
        self.compute_stats_at_depth(0)
    }

    pub(crate) fn compute_stats_at_depth(&self, depth: usize) -> (usize, usize) {
        match self {
            TreeNode::Empty => {
                if depth != 0 {
                    unreachable!()
                } else {
                    (0, 0)
                }
            }
            TreeNode::GateOnly(description) => (
                description.degree_at_depth(depth),
                description.num_constants + depth,
            ),
            TreeNode::Fork { left, right } => {
                let (left_subtree_degree, left_subtree_constants) =
                    left.compute_stats_at_depth(depth + 1);
                let (right_subtree_degree, right_subtree_constants) =
                    right.compute_stats_at_depth(depth + 1);

                (
                    std::cmp::max(left_subtree_degree, right_subtree_degree),
                    std::cmp::max(left_subtree_constants, right_subtree_constants),
                )
            }
        }
    }

    pub fn output_placement(&self, gate_idx: usize) -> Option<Vec<bool>> {
        match self {
            Self::Empty => None,
            Self::GateOnly(existing_gate) => {
                if existing_gate.gate_idx == gate_idx {
                    Some(vec![])
                } else {
                    None
                }
            }
            Self::Fork { left, right } => {
                if let Some(path) = left.output_placement(gate_idx) {
                    let mut result = vec![true];
                    result.extend(path);

                    return Some(result);
                }

                if let Some(path) = right.output_placement(gate_idx) {
                    let mut result = vec![false];
                    result.extend(path);

                    return Some(result);
                }

                None
            }
        }
    }

    pub(crate) fn try_add_gate(
        &self,
        gate: GateDescription,
        max_resulting_degree: usize,
        max_num_constants: usize,
        current_depth: usize,
    ) -> Option<Self> {
        match self {
            Self::Empty => {
                if gate.degree_at_depth(current_depth) > max_resulting_degree
                    || gate.num_constants > max_num_constants
                {
                    None
                } else {
                    Some(Self::GateOnly(gate))
                }
            }
            Self::GateOnly(existing_gate) => {
                // we need to fork
                let node_0 = Self::GateOnly(*existing_gate);
                let node_1 = Self::GateOnly(gate);

                let new = Self::Fork {
                    left: Box::new(node_0.clone()),
                    right: Box::new(node_1.clone()),
                };

                let (resulting_degree, resulting_num_constants) =
                    new.compute_stats_at_depth(current_depth);

                if resulting_degree <= max_resulting_degree
                    && resulting_num_constants <= max_num_constants
                {
                    return Some(new);
                }

                let new = Self::Fork {
                    left: Box::new(node_1),
                    right: Box::new(node_0),
                };

                let (resulting_degree, resulting_num_constants) =
                    new.compute_stats_at_depth(current_depth);

                if resulting_degree <= max_resulting_degree
                    && resulting_num_constants <= max_num_constants
                {
                    return Some(new);
                }

                None
            }
            Self::Fork { left, right } => {
                if let Some(new_left_node) = left.try_add_gate(
                    gate,
                    max_resulting_degree,
                    max_num_constants,
                    current_depth + 1,
                ) {
                    let new = Self::Fork {
                        left: Box::new(new_left_node),
                        right: right.clone(),
                    };

                    return Some(new);
                }

                if let Some(new_right_node) = right.try_add_gate(
                    gate,
                    max_resulting_degree,
                    max_num_constants,
                    current_depth + 1,
                ) {
                    let new = Self::Fork {
                        left: left.clone(),
                        right: Box::new(new_right_node),
                    };

                    return Some(new);
                }

                None
            }
        }
    }
}
