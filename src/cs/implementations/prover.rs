//! Let's briefly describe how we want to prove things:
//! 1) We do not want to use a rate that leads to LDEs < minimal degree that is required to evaluate the quotient in full
//! 2) We HAVE TO run FRI over the extension field to be anywhere near the conditions where the conjecture is plausible, namely
//! field is much larger than code size. And 64 bits over 32 bits is not "large" IMHO
//! 3) We will use a repeated protocol to materialize all polynomials that depend on challenges, so
//! as soon as we commit to witness, we will have
//! - N grand-products
//! - N quotients
//! - N random points
//! - all of those are considered independent trials, so the protocol soundness is \epsion ^ N at this point
//! - now we have to do FRI. Here we can pull the challenges directly from the extension field, to be plausibly within the conjecture
//! 4) We modify the lookup argument, and instead of using aggregated sorted polynomials we use non-aggregated, and
//! skip the intermediate step
//! 5) We assume we're using quite a large number of columns, so we do NOT benefit from the trick of placing a full coset into
//! the leaves of the original oracles for witness and other round oracles, and instead we DO materialize the first FRI oracle,
//! where we actually place all coset values
use std::alloc::Global;

use super::hints::*;
use super::polynomial::lde::GenericLdeStorage;
use super::polynomial::BitreversedLagrangeForm;
use super::polynomial_storage::SetupStorage;
use super::proof::Proof;
use super::transcript::Transcript;
use super::verifier::VerificationKey;
use super::*;
use crate::cs::implementations::buffering_source::*;
use crate::cs::implementations::proof::SingleRoundQueries;
use crate::cs::implementations::transcript::BoolsBuffer;
use crate::cs::traits::gate::GatePlacementStrategy;
use crate::field::traits::field_like::mul_assign_vectorized_in_extension;
use std::sync::Arc;

use super::pow::*;
use crate::cs::gates::lookup_marker::LookupFormalGate;
use crate::cs::implementations::witness::WitnessSet;
use crate::utils::allocate_in_with_alignment_of;

use crate::cs::implementations::fri::do_fri;
use crate::cs::implementations::polynomial::MonomialForm;

use crate::cs::implementations::polynomial_storage::TraceHolder;
use crate::cs::implementations::polynomial_storage::*;
use crate::cs::implementations::reference_cs::*;
use crate::cs::implementations::utils::*;
use crate::cs::oracle::merkle_tree::MerkleTreeWithCap;
use crate::cs::oracle::TreeHasher;
use crate::cs::traits::destination_view::*;
use crate::cs::traits::evaluator::*;
use crate::cs::traits::trace_source::*;
use crate::cs::traits::GoodAllocator;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Hash, PartialEq, Eq)]
pub struct ProofConfig {
    pub fri_lde_factor: usize,
    pub merkle_tree_cap_size: usize,
    pub fri_folding_schedule: Option<Vec<usize>>,
    pub security_level: usize,
    pub pow_bits: u32,
}

impl std::default::Default for ProofConfig {
    fn default() -> Self {
        Self {
            fri_lde_factor: 4,
            merkle_tree_cap_size: 16,
            fri_folding_schedule: None,
            security_level: 100,
            pow_bits: 20,
        }
    }
}

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        CFG: CSConfig,
        A: GoodAllocator,
    > CSReferenceAssembly<F, P, CFG, A>
{
    pub fn take_witness(&mut self, worker: &Worker) -> WitnessSet<F> {
        // get our columns flattened out
        let variables_columns = self.materialize_variables_polynomials(worker);
        let witness_columns = self.materialize_witness_polynomials(worker);
        let mutliplicities_columns = self.materialize_multiplicities_polynomials(worker);

        // now we can commit to public inputs also before potentially moving computations to vectorized form

        let num_public_inputs = self.public_inputs.len();
        let mut public_inputs_only_values = Vec::with_capacity(num_public_inputs);
        let mut public_inputs_with_values = Vec::with_capacity(num_public_inputs);

        for (column, row) in self.public_inputs.iter().copied() {
            let value = variables_columns[column].storage[row];
            public_inputs_with_values.push((column, row, value));
            public_inputs_only_values.push(value);
        }

        WitnessSet {
            public_inputs_values: public_inputs_only_values,
            public_inputs_with_locations: public_inputs_with_values,
            variables: variables_columns,
            witness: witness_columns,
            multiplicities: mutliplicities_columns,
        }
    }

    pub fn dump_values_set(&mut self) -> Vec<F> {
        let max_idx = self.next_available_place_idx as usize;

        let mut values = Vec::with_capacity(max_idx);

        values.copy_from_slice(&self.witness.as_ref().unwrap().all_values);

        values
    }

    pub fn take_witness_using_hints(
        &mut self,
        worker: &Worker,
        vars_hint: &DenseVariablesCopyHint,
        wits_hint: &DenseWitnessCopyHint,
    ) -> WitnessSet<F> {
        // get our columns flattened out
        let variables_columns =
            self.materialize_variables_polynomials_from_dense_hint(worker, vars_hint);
        let witness_columns =
            self.materialize_witness_polynomials_from_dense_hint(worker, wits_hint);
        let mutliplicities_columns = self.materialize_multiplicities_polynomials(worker);

        // now we can commit to public inputs also before potentially moving computations to vectorized form

        let num_public_inputs = self.public_inputs.len();
        let mut public_inputs_only_values = Vec::with_capacity(num_public_inputs);
        let mut public_inputs_with_values = Vec::with_capacity(num_public_inputs);

        for (column, row) in self.public_inputs.iter().copied() {
            let value = variables_columns[column].storage[row];
            public_inputs_with_values.push((column, row, value));
            public_inputs_only_values.push(value);
        }

        WitnessSet {
            public_inputs_values: public_inputs_only_values,
            public_inputs_with_locations: public_inputs_with_values,
            variables: variables_columns,
            witness: witness_columns,
            multiplicities: mutliplicities_columns,
        }
    }

    pub fn prove_cpu_basic<
        EXT: FieldExtension<2, BaseField = F>,
        TR: Transcript<F>,
        H: TreeHasher<F, Output = TR::CompatibleCap>,
        POW: PoWRunner,
    >(
        &self,
        worker: &Worker,
        witness_set: WitnessSet<F>,
        setup_base: &SetupBaseStorage<F, P>,
        setup: &SetupStorage<F, P>,
        setup_tree: &MerkleTreeWithCap<F, H>,
        vk: &VerificationKey<F, H>,
        proof_config: ProofConfig,
        transcript_params: TR::TransciptParameters,
    ) -> Proof<F, H, EXT> {
        assert!(proof_config.fri_lde_factor.is_power_of_two());
        assert!(proof_config.fri_lde_factor > 1);

        profile_fn!(prove_cpu_basic);
        profile_section!(sect_1);

        let base_system_degree = self.max_trace_len;
        assert!(base_system_degree.is_power_of_two());

        let WitnessSet {
            public_inputs_values,
            public_inputs_with_locations,
            variables,
            witness,
            multiplicities,
        } = witness_set;

        let variables_columns = variables;
        let witness_columns = witness;
        let mutliplicities_columns = multiplicities;
        let public_inputs_only_values = public_inputs_values;
        let public_inputs_with_values = public_inputs_with_locations;

        assert_eq!(
            public_inputs_only_values.len(),
            public_inputs_with_values.len()
        );

        let interactive_soundness =
            (F::CAPACITY_BITS * 2) - base_system_degree.trailing_zeros() as usize;
        dbg!(interactive_soundness);

        let cap_size = proof_config.merkle_tree_cap_size;
        assert!(cap_size > 0);

        let table_ids_column_idxes = setup.table_ids_column_idxes.clone();

        let now = std::time::Instant::now();

        let mut transcript = TR::new(transcript_params);

        // Commit to verification key, that should be small
        transcript.witness_merkle_tree_cap(&vk.setup_merkle_tree_cap);

        let mut owned_ctx = P::Context::placeholder();
        let ctx = &mut owned_ctx;

        let selectors_placement = setup_base.selectors_placement.clone();
        let sigmas = setup_base.copy_permutation_polys.clone();

        let domain_size = sigmas[0].domain_size(); // counted in elements of P
        assert_eq!(base_system_degree, domain_size);
        assert!(domain_size.is_power_of_two());

        let x_poly = materialize_x_poly(domain_size, worker);

        let x_poly = std::sync::Arc::new(x_poly);

        let (max_constraint_contribution_degree, _number_of_constant_polys) =
            selectors_placement.compute_stats();

        let quotient_degree_from_general_purpose_gate_terms =
            if max_constraint_contribution_degree > 0 {
                max_constraint_contribution_degree - 1
            } else {
                0
            };

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

        // In our proof system RS code rate (we usually use "lde factor" that is an inverse of the rate)
        // is decoupled from the minimal LDE factor we need to compute quotient degree at the end,
        // so we propagate the parameters to the corresponding places
        let quotient_degree = min_lde_degree_for_gates;

        dbg!(quotient_degree);

        // now we can commit to public inputs also before potentially moving computations to vectorized form
        for value in public_inputs_only_values.iter().copied() {
            transcript.witness_field_elements(&[value]);
        }

        // all set, we can proceed with witness

        let variables_columns: Vec<_> = variables_columns
            .into_iter()
            .map(|el| {
                let el = el.into_storage();
                let el = P::vec_from_base_vec(el);
                let el = GenericPolynomial::from_storage(el);

                std::sync::Arc::new(el)
            })
            .collect();

        let num_variable_polys = variables_columns.len();

        let witness_columns: Vec<_> = witness_columns
            .into_iter()
            .map(|el| {
                let el = el.into_storage();
                let el = P::vec_from_base_vec(el);
                let el = GenericPolynomial::from_storage(el);

                std::sync::Arc::new(el)
            })
            .collect();

        let num_witness_polys = witness_columns.len();

        let mutliplicities_columns: Vec<_> = mutliplicities_columns
            .into_iter()
            .map(|el| {
                let el = el.into_storage();
                let el = P::vec_from_base_vec(el);
                let el = GenericPolynomial::from_storage(el);

                std::sync::Arc::new(el)
            })
            .collect();

        let num_multiplicities_polys = mutliplicities_columns.len();
        assert_eq!(num_multiplicities_polys, self.num_multipicities_polys());

        let num_constant_polys = setup.constant_columns.len();
        let num_copy_permutation_polys = setup.copy_permutation_polys.len();

        let used_lde_degree = std::cmp::max(proof_config.fri_lde_factor, quotient_degree);
        log!("Will operate with LDEs of factor {}", used_lde_degree);

        let witness_storage = WitnessStorage::<F, P, Global, Global>::from_base_trace_ext(
            variables_columns.clone(),
            witness_columns,
            mutliplicities_columns.clone(),
            used_lde_degree,
            worker,
            ctx,
        );

        let mut source = vec![];
        source.extend(
            witness_storage
                .variables_columns
                .iter()
                .map(|el| el.subset_for_degree(proof_config.fri_lde_factor)),
        );
        source.extend(
            witness_storage
                .witness_columns
                .iter()
                .map(|el| el.subset_for_degree(proof_config.fri_lde_factor)),
        );
        source.extend(
            witness_storage
                .lookup_multiplicities_polys
                .iter()
                .map(|el| el.subset_for_degree(proof_config.fri_lde_factor)),
        );

        log!("Witness LDE taken {:?}", now.elapsed());

        let witness_tree = MerkleTreeWithCap::<F, H>::construct(source, cap_size, worker);

        let witness_tree_cap = witness_tree.get_cap();

        profile_section!(mt_cap);

        transcript.witness_merkle_tree_cap(witness_tree_cap.as_ref());

        drop(mt_cap);

        // here we commit to our original witness,
        // potentially including lookup related one

        let beta_coeffs = transcript.get_multiple_challenges_fixed::<2>();
        let beta = ExtensionField::<F, 2, EXT>::from_coeff_in_base(beta_coeffs);

        let gamma_coeffs = transcript.get_multiple_challenges_fixed::<2>();
        let gamma = ExtensionField::<F, 2, EXT>::from_coeff_in_base(gamma_coeffs);

        let copy_permutation_chunking_degree = quotient_degree;

        let now = std::time::Instant::now();

        let (z_poly, intermediate_products) =
            super::copy_permutation::compute_partial_products_in_extension::<
                F,
                P,
                EXT,
                Global,
                Global,
            >(
                variables_columns.clone(),
                x_poly,
                sigmas,
                beta,
                gamma,
                worker,
                copy_permutation_chunking_degree,
                ctx,
            );

        // now we need to construct one more oracle,
        // but now over copy-permutation and lookup grand products,
        // as well as auxilary polys for lookup argument

        let num_intermediate_partial_product_relations = intermediate_products.len();

        let (
            (lookup_witness_encoding_polys, lookup_multiplicities_encoding_polys),
            lookup_beta,
            lookup_gamma,
        ) = if self.lookup_parameters != LookupParameters::NoLookup {
            profile_section!(get_lookups);

            // lookup argument related parts
            let lookup_beta = transcript.get_multiple_challenges_fixed::<2>();
            let lookup_beta = ExtensionField::<F, 2, EXT>::from_coeff_in_base(lookup_beta);

            let lookup_gamma = transcript.get_multiple_challenges_fixed::<2>();
            let lookup_gamma = ExtensionField::<F, 2, EXT>::from_coeff_in_base(lookup_gamma);

            let contributions = match self.lookup_parameters {
                LookupParameters::NoLookup => {
                    unreachable!()
                }
                LookupParameters::TableIdAsConstant { .. }
                | LookupParameters::TableIdAsVariable { .. } => {
                    // exists by our setup
                    let lookup_evaluator_id = 0;
                    let _selector_subpath = setup_base
                        .selectors_placement
                        .output_placement(lookup_evaluator_id)
                        .expect("lookup gate must be placed");

                    let _columns_per_subargument = self.lookup_parameters.columns_per_subargument();

                    todo!()

                    // super::lookup_argument::compute_lookup_poly_pairs_over_general_purpose_columns(
                    //     variables_columns.clone(),
                    //     mutliplicities_columns.clone(),
                    //     setup_base.constant_columns.clone(),
                    //     setup_base.lookup_tables_columns.clone(),
                    //     table_ids_column_idxes.clone(),
                    //     lookup_betas.clone(),
                    //     lookup_gammas.clone(),
                    //     columns_per_subargument as usize,
                    //     selector_subpath,
                    //     worker,
                    //     ctx,
                    // )
                }
                a @ LookupParameters::UseSpecializedColumnsWithTableIdAsVariable { .. }
                | a @ LookupParameters::UseSpecializedColumnsWithTableIdAsConstant { .. } => {
                    // ensure proper setup
                    assert_eq!(
                        self.evaluation_data_over_specialized_columns
                            .gate_type_ids_for_specialized_columns[0],
                        std::any::TypeId::of::<LookupFormalGate>(),
                        "we expect first specialized gate to be the lookup gate"
                    );
                    let (initial_offset, offset_per_repetition, _) = self
                        .evaluation_data_over_specialized_columns
                        .offsets_for_specialized_evaluators[0];
                    assert_eq!(initial_offset.constants_offset, 0);

                    if let LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                        share_table_id,
                        ..
                    } = a
                    {
                        if share_table_id {
                            assert_eq!(offset_per_repetition.constants_offset, 0);
                        }
                    }
                    super::lookup_argument_in_ext::compute_lookup_poly_pairs_specialized(
                        variables_columns.clone(),
                        mutliplicities_columns.clone(),
                        setup_base.constant_columns.clone(),
                        setup_base.lookup_tables_columns.clone(),
                        setup_base.table_ids_column_idxes.clone(),
                        lookup_beta,
                        lookup_gamma,
                        self.parameters.num_columns_under_copy_permutation,
                        a,
                        worker,
                        ctx,
                    )
                }
            };

            (contributions, lookup_beta, lookup_gamma)
        } else {
            let zero = ExtensionField::<F, 2, EXT>::ZERO;

            ((vec![], vec![]), zero, zero)
        };

        // LDE them
        profile_section!(lde_lookups);

        let z_poly = z_poly.map(Arc::new);
        let intermediate_products: Vec<_> = intermediate_products
            .into_iter()
            .map(|el| el.map(Arc::new))
            .collect();
        let lookup_witness_encoding_polys: Vec<_> = lookup_witness_encoding_polys
            .into_iter()
            .map(|el| el.map(Arc::new))
            .collect();
        let lookup_multiplicities_encoding_polys: Vec<_> = lookup_multiplicities_encoding_polys
            .into_iter()
            .map(|el| el.map(Arc::new))
            .collect();

        drop(lde_lookups);
        drop(sect_1);

        let second_stage_polys_storage = SecondStageProductsStorage::from_base_trace_ext(
            z_poly.clone(),
            intermediate_products,
            lookup_witness_encoding_polys,
            lookup_multiplicities_encoding_polys,
            used_lde_degree,
            worker,
            ctx,
        );

        log!("Second stage LDE taken {:?}", now.elapsed());

        // and commit
        profile_section!(commit_comething);

        let mut source = vec![];
        source.extend(
            second_stage_polys_storage
                .z_poly
                .iter()
                .map(|el| el.subset_for_degree(proof_config.fri_lde_factor)),
        );
        source.extend(
            second_stage_polys_storage
                .intermediate_polys
                .iter()
                .flatten()
                .map(|el| el.subset_for_degree(proof_config.fri_lde_factor)),
        );
        source.extend(
            second_stage_polys_storage
                .lookup_witness_encoding_polys
                .iter()
                .flatten()
                .map(|el| el.subset_for_degree(proof_config.fri_lde_factor)),
        );
        source.extend(
            second_stage_polys_storage
                .lookup_multiplicities_encoding_polys
                .iter()
                .flatten()
                .map(|el| el.subset_for_degree(proof_config.fri_lde_factor)),
        );

        let second_stage_tree = MerkleTreeWithCap::<F, H>::construct(source, cap_size, worker);

        // now we can commit to grand products and get new challenges
        let second_stage_tree_cap = second_stage_tree.get_cap();

        transcript.witness_merkle_tree_cap(second_stage_tree_cap.as_ref());

        drop(commit_comething);

        let now = std::time::Instant::now();

        let alpha = transcript.get_multiple_challenges_fixed::<2>();
        let alpha = ExtensionField::<F, 2, EXT>::from_coeff_in_base(alpha);

        // two extra relations per lookup subargument - for A and B polys
        let num_lookup_subarguments = self.num_sublookup_arguments();
        let num_multiplicities_polys = self.num_multipicities_polys();
        let total_num_lookup_argument_terms = num_lookup_subarguments + num_multiplicities_polys;

        let total_num_gate_terms_for_specialized_columns = self
            .evaluation_data_over_specialized_columns
            .evaluators_over_specialized_columns
            .iter()
            .zip(
                self.evaluation_data_over_specialized_columns
                    .gate_type_ids_for_specialized_columns
                    .iter(),
            )
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
            .evaluation_data_over_general_purpose_columns
            .evaluators_over_general_purpose_columns
            .iter()
            .map(|evaluator| evaluator.total_quotient_terms_over_all_repetitions)
            .sum();

        dbg!(total_num_lookup_argument_terms);
        dbg!(total_num_gate_terms_for_specialized_columns);
        dbg!(total_num_gate_terms_for_general_purpose_columns);
        dbg!(num_intermediate_partial_product_relations);

        let total_num_terms =
            total_num_lookup_argument_terms // and lookup is first
            + total_num_gate_terms_for_specialized_columns // then gates over specialized columns
            + total_num_gate_terms_for_general_purpose_columns // all getes terms over general purpose columns 
            + 1 // z(1) == 1 copy permutation
            + 1 // z(x * omega) = ...
            + num_intermediate_partial_product_relations // chunking copy permutation part
        ;

        let powers: Vec<_, Global> = materialize_powers_serial(alpha, total_num_terms);
        let rest = &powers[..];
        let (take, rest) = rest.split_at(total_num_lookup_argument_terms);
        let pregenerated_challenges_for_lookup = take.to_vec();
        let (take, rest) = rest.split_at(total_num_gate_terms_for_specialized_columns);
        let pregenerated_challenges_for_gates_over_specialized_columns = take.to_vec();
        let (take, rest) = rest.split_at(total_num_gate_terms_for_general_purpose_columns);
        let pregenerated_challenges_for_gates_over_general_purpose_columns = take.to_vec();
        let remaining_challenges = rest.to_vec();
        // now we can evaluate the constraints

        let inner_size = variables_columns[0].storage.len(); // counted in elements of P

        let trace_holder = TraceHolder {
            variables: witness_storage,
            setup: setup.clone(),
        };

        let sources = ProverTraceView::chunks_from_trace_for_degree(
            &trace_holder,
            quotient_degree,
            worker.num_cores,
        );

        let mut destination = GateEvaluationReducingDestination::<F, P>::new(
            inner_size,
            quotient_degree,
            vec![], // we will reassign later on
            ctx,
        );

        let (_deg, constants_for_gates_over_general_purpose_columns) =
            selectors_placement.compute_stats();

        // first we proceed over evaluators that are over special purpose columns
        // For now we tradeoff simplicity for some extra memory bandwidth
        {
            profile_section!(evaluate_over_specialized_columns);
            log!("Evaluating over specialized columns");
            // we expect our gates to be narrow, so we do not need to buffer row, and instead
            // we can evaluate over limited set of columns
            let mut specialized_placement_data = vec![];
            let mut evaluation_functions: Vec<&dyn DynamicEvaluatorOverSpecializedColumns<F, P>> =
                vec![];

            for (idx, (gate_type_id, evaluator)) in self
                .evaluation_data_over_specialized_columns
                .gate_type_ids_for_specialized_columns
                .iter()
                .zip(
                    self.evaluation_data_over_specialized_columns
                        .evaluators_over_specialized_columns
                        .iter(),
                )
                .enumerate()
            {
                if gate_type_id == &std::any::TypeId::of::<LookupFormalGate>() {
                    continue;
                }
                assert!(
                    evaluator.total_quotient_terms_over_all_repetitions != 0,
                    "evaluator {} has not contribution to quotient",
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

                let (initial_offset, per_repetition_offset, total_constants_available) = self
                    .evaluation_data_over_specialized_columns
                    .offsets_for_specialized_evaluators[idx];

                let placement_data = (
                    num_repetitions,
                    share_constants,
                    initial_offset,
                    per_repetition_offset,
                    total_constants_available,
                    total_terms,
                );

                specialized_placement_data.push(placement_data);
                let t = evaluator
                    .columnwise_evaluation_function
                    .as_ref()
                    .expect("must be properly configured");
                let tt: &dyn DynamicEvaluatorOverSpecializedColumns<F, P> = &(**t);
                evaluation_functions.push(tt);
            }

            let pregenerated_challenges_for_gates_over_specialized_columns: Vec<_> =
                pregenerated_challenges_for_gates_over_specialized_columns
                    .into_iter()
                    .map(|el| el.into_coeffs_in_base())
                    .collect();
            destination.challenges_powers =
                std::sync::Arc::new(pregenerated_challenges_for_gates_over_specialized_columns);

            let now = std::time::Instant::now();

            let mut challenge_offset = 0;

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

                let destination_chunks =
                    destination.into_buffering_chunks_without_selector(worker.num_cores);

                worker.scope(0, |scope, _| {
                    for (source, destination) in
                        sources.iter().cloned().zip(destination_chunks.into_iter())
                    {
                        let source = source.subset(
                            initial_offset.variables_offset..final_offset.variables_offset,
                            initial_offset.witnesses_offset..final_offset.witnesses_offset,
                            (constants_for_gates_over_general_purpose_columns
                                + initial_offset.constants_offset)
                                ..(constants_for_gates_over_general_purpose_columns
                                    + final_offset.constants_offset),
                        );

                        scope.spawn(|_| {
                            let mut source = source;

                            let mut ctx = *ctx;
                            let mut destination = destination;
                            destination.set_challenge_offset(challenge_offset);
                            evaluation_fn.evaluate_over_columns(
                                &mut source,
                                &mut destination,
                                &mut ctx,
                            );
                        });
                    }
                });

                challenge_offset += total_terms;
            }

            assert_eq!(
                challenge_offset,
                total_num_gate_terms_for_specialized_columns
            );

            log!(
                "Specialized gates contribution to quotient evaluation taken {:?}",
                now.elapsed()
            );
        }

        profile_section!(sect_5);

        let pregenerated_challenges_for_gates_over_general_purpose_columns: Vec<_> =
            pregenerated_challenges_for_gates_over_general_purpose_columns
                .into_iter()
                .map(|el| el.into_coeffs_in_base())
                .collect();
        destination.challenges_powers =
            std::sync::Arc::new(pregenerated_challenges_for_gates_over_general_purpose_columns);

        // now we need to precompute tree of selectors, then create chunks,
        // and then for every gate do the evaluation over general purpose columns

        let mut selectors_buffer = HashMap::new();
        {
            profile_section!(evaluator_iter);
            for (evaluator_idx, evaluator) in self
                .evaluation_data_over_general_purpose_columns
                .evaluators_over_general_purpose_columns
                .iter()
                .enumerate()
            {
                if let Some(path) = selectors_placement.output_placement(evaluator_idx) {
                    if selectors_buffer.contains_key(&path) {
                        panic!("same selector for different gates");
                    }

                    compute_selector_subpath(
                        path.clone(),
                        &mut selectors_buffer,
                        quotient_degree,
                        setup,
                        worker,
                        ctx,
                    );

                    if crate::config::DEBUG_SATISFIABLE {
                        let selector = selectors_buffer
                            // .remove(&path)
                            .get(&path)
                            .cloned()
                            .expect("path must be unique and precomputed");
                        let constant_placement_offset = path.len();

                        // check that our selectors are well placed
                        for (outer_idx, selector_value) in
                            selector.storage[0].storage.iter().enumerate()
                        {
                            let selector_value = [*selector_value];
                            let as_base_slice = P::slice_into_base_slice(&selector_value);
                            for (inner_idx, selector_value) in as_base_slice.iter().enumerate() {
                                let idx = outer_idx * P::SIZE_FACTOR + inner_idx;
                                let mut normal_enumeration = idx.reverse_bits();
                                normal_enumeration >>= usize::BITS - domain_size.trailing_zeros();
                                if *selector_value == F::ONE {
                                    assert_eq!(evaluator_idx, self.gates_application_sets[normal_enumeration], "divergence at row {}: evaluator idx is {}, but in setup it's evaluator number {}", normal_enumeration, evaluator_idx, self.gates_application_sets[normal_enumeration]);
                                } else if *selector_value == F::ZERO {
                                    assert_ne!(evaluator_idx, self.gates_application_sets[normal_enumeration], "divergence at row {}: evaluator idx is {}, but in setup it's evaluator number {}", normal_enumeration, evaluator_idx, self.gates_application_sets[normal_enumeration]);
                                } else {
                                    panic!("Selector value is undefined {:?} at row {} for gate idx {}", selector_value, normal_enumeration, evaluator_idx);
                                }
                            }
                        }

                        for subterms in destination.quotient_buffers.iter() {
                            for (idx, el) in subterms[0].iter().enumerate() {
                                if el.is_zero() == false {
                                    let selector_value = selector.storage[0].storage[idx];
                                    // now idx has to be bitreversed
                                    let mut normal_enumeration = idx.reverse_bits();
                                    normal_enumeration >>=
                                        usize::BITS - domain_size.trailing_zeros();
                                    let (vars, wits, constants) =
                                        trace_holder.dump_row_in_main_domain(idx);
                                    dbg!(&vars);
                                    dbg!(&wits);
                                    dbg!(&constants[constant_placement_offset..]);
                                    panic!(
                                        "Unsatisfied at row {}, gate {}. Selector value = {}",
                                        normal_enumeration, &evaluator.debug_name, selector_value
                                    );
                                }
                            }
                        }
                    }
                } else {
                    debug_assert!(evaluator.num_quotient_terms == 0);
                }
            }
            drop(evaluator_iter);
            {
                if self
                    .evaluation_data_over_general_purpose_columns
                    .evaluators_over_general_purpose_columns
                    .len()
                    == 1
                {
                    // for now do nothing

                    unimplemented!();
                } else {
                    // first prepare sequence of selectors
                    profile_section!(evaluator_iter_2);
                    let num_evaluators = self
                        .evaluation_data_over_general_purpose_columns
                        .evaluators_over_general_purpose_columns
                        .len();
                    let mut selectors = Vec::with_capacity(num_evaluators);
                    let mut placement_offsets = Vec::with_capacity(num_evaluators);
                    let mut evaluation_functions: Vec<
                        &dyn DynamicEvaluatorOverGeneralPurposeColumns<F, P>,
                    > = Vec::with_capacity(num_evaluators);

                    for (evaluator_idx, evaluator) in self
                        .evaluation_data_over_general_purpose_columns
                        .evaluators_over_general_purpose_columns
                        .iter()
                        .enumerate()
                    {
                        if evaluator.total_quotient_terms_over_all_repetitions == 0 {
                            // we MAY formally have NOP gate in the set here, but we should not evaluate it.
                            // NOP gate will affect selectors placement, but not the rest

                            match evaluator.gate_purpose {
                                GatePurpose::MarkerNeedsSelector => {
                                    let path = selectors_placement
                                        .output_placement(evaluator_idx)
                                        .expect("selector must exist");

                                    // dbg!(&evaluator.debug_name);
                                    // dbg!(&path);

                                    if crate::config::DEBUG_SATISFIABLE {
                                        let selector = selectors_buffer
                                            // .remove(&path)
                                            .get(&path)
                                            .cloned()
                                            .expect("path must be unique and precomputed");
                                        let constant_placement_offset = path.len();

                                        // check that our selectors are well placed
                                        for (outer_idx, selector_value) in
                                            selector.storage[0].storage.iter().enumerate()
                                        {
                                            let selector_value = [*selector_value];
                                            let as_base_slice =
                                                P::slice_into_base_slice(&selector_value);
                                            for (inner_idx, selector_value) in
                                                as_base_slice.iter().enumerate()
                                            {
                                                let idx = outer_idx * P::SIZE_FACTOR + inner_idx;
                                                let mut normal_enumeration = idx.reverse_bits();
                                                normal_enumeration >>=
                                                    usize::BITS - domain_size.trailing_zeros();
                                                if *selector_value == F::ONE {
                                                    assert_eq!(evaluator_idx, self.gates_application_sets[normal_enumeration], "divergence at row {}: evaluator idx is {}, but in setup it's evaluator number {}", normal_enumeration, evaluator_idx, self.gates_application_sets[normal_enumeration]);
                                                } else if *selector_value == F::ZERO {
                                                    assert_ne!(evaluator_idx, self.gates_application_sets[normal_enumeration], "divergence at row {}: evaluator idx is {}, but in setup it's evaluator number {}", normal_enumeration, evaluator_idx, self.gates_application_sets[normal_enumeration]);
                                                } else {
                                                    panic!("Selector value is undefined {:?} at row {} for gate idx {}", selector_value, normal_enumeration, evaluator_idx);
                                                }
                                            }
                                        }

                                        for subterms in destination.quotient_buffers.iter() {
                                            for (idx, el) in subterms[0].iter().enumerate() {
                                                if el.is_zero() == false {
                                                    dbg!(&evaluator.debug_name);
                                                    let selector_value =
                                                        selector.storage[0].storage[idx];
                                                    // now idx has to be bitreversed
                                                    let mut normal_enumeration = idx.reverse_bits();
                                                    normal_enumeration >>=
                                                        usize::BITS - domain_size.trailing_zeros();
                                                    let (vars, wits, constants) =
                                                        trace_holder.dump_row_in_main_domain(idx);
                                                    dbg!(&vars);
                                                    dbg!(&wits);
                                                    dbg!(&constants[constant_placement_offset..]);
                                                    panic!("Unsatisfied at row {}, gate {}. Selector value = {}", normal_enumeration, &evaluator.debug_name, selector_value);
                                                }
                                            }
                                        }
                                    }
                                }
                                GatePurpose::Evaluatable { .. } => {
                                    unreachable!()
                                }
                                GatePurpose::MarkerWithoutSelector => {
                                    unreachable!()
                                }
                            }
                        } else {
                            let path = selectors_placement
                                .output_placement(evaluator_idx)
                                .expect("selector must exist");
                            let selector = selectors_buffer
                                .remove(&path)
                                .expect("path must be unique and precomputed");
                            let constant_placement_offset = path.len();

                            // dbg!(&evaluator.debug_name);
                            // dbg!(&path);

                            selectors.push(selector);
                            placement_offsets.push(constant_placement_offset);
                            let t = evaluator
                                .rowwise_evaluation_function
                                .as_ref()
                                .expect("must be properly configured");
                            let tt: &dyn DynamicEvaluatorOverGeneralPurposeColumns<F, P> = &(**t);
                            evaluation_functions.push(tt);
                        }
                    }

                    assert_eq!(selectors.len(), placement_offsets.len());
                    assert_eq!(selectors.len(), evaluation_functions.len());

                    drop(evaluator_iter_2);
                    profile_section!(gates_contribution);

                    // now walk over chunks and compute by buffering rows

                    let destination_chunks =
                        destination.into_buffering_chunks(worker.num_cores, selectors);

                    let now = std::time::Instant::now();

                    worker.scope(0, |scope, _| {
                        for (source, destination) in
                            sources.iter().cloned().zip(destination_chunks.into_iter())
                        {
                            let source = source.subset(
                                0..self.parameters.num_columns_under_copy_permutation,
                                0..self.parameters.num_witness_columns,
                                0..constants_for_gates_over_general_purpose_columns,
                            );
                            scope.spawn(|_| {
                                let mut source = source;
                                let mut ctx = *ctx;
                                let mut destination = destination;
                                // we manually drive row by row
                                let num_iterations = source.num_iterations();
                                debug_assert_eq!(
                                    num_iterations,
                                    destination.expected_num_iterations()
                                );

                                let mut buffering_source = BufferingPolyStorage::new_with_capacity(
                                    self.parameters.num_columns_under_copy_permutation,
                                    self.parameters.num_witness_columns,
                                    self.parameters.num_columns_under_copy_permutation
                                        + self.parameters.num_witness_columns
                                        + self.parameters.num_constant_columns
                                        + 16,
                                );

                                for _ in 0..num_iterations {
                                    buffering_source.buffer.clear();
                                    source.dump_current_row(&mut buffering_source.buffer);
                                    for (constant_placement_offset, evaluation_fn) in
                                        placement_offsets.iter().zip(evaluation_functions.iter())
                                    {
                                        evaluation_fn.evaluate_over_general_purpose_columns(
                                            &mut buffering_source,
                                            &mut destination,
                                            *constant_placement_offset,
                                            &mut ctx,
                                        );
                                        destination.proceed_to_next_gate();
                                    }

                                    source.advance();
                                    destination.advance(&mut ctx);
                                }
                            });
                        }
                    });

                    log!("Gates over general purposes columns contribution to quotient evaluation taken {:?}", now.elapsed());
                }
            }
        }

        drop(sect_5);
        profile_section!(sect_6);

        let [quotient_c0s, quotient_c1s] =
            Arc::try_unwrap(destination.quotient_buffers).expect("must be exclusively owned");

        if crate::config::DEBUG_SATISFIABLE {
            for (idx, el) in quotient_c0s[0].iter().enumerate() {
                if el.is_zero() == false {
                    let mut normal_enumeration = idx.reverse_bits();
                    normal_enumeration >>= usize::BITS - domain_size.trailing_zeros();
                    let evaluator_idx = self.gates_application_sets[normal_enumeration];
                    let gate_name = &self
                        .evaluation_data_over_general_purpose_columns
                        .evaluators_over_general_purpose_columns[evaluator_idx]
                        .debug_name;
                    panic!(
                        "Unsatisfied at row {}, gate {}",
                        normal_enumeration, gate_name
                    );
                }
            }
        }

        let inner_size = domain_size / P::SIZE_FACTOR;
        let outer_size = quotient_c0s.len();
        let quotient_domain_size = outer_size * domain_size;
        let inverse_twiddles =
            P::precompute_inverse_twiddles_for_fft::<Global>(quotient_domain_size, worker, ctx);

        let coset = if crate::config::DEBUG_SATISFIABLE == false {
            F::multiplicative_generator()
        } else {
            F::ONE
        };

        let x_poly_lde = materialize_x_poly_as_arc_lde::<F, P, Global, Global>(
            domain_size,
            used_lde_degree,
            coset,
            worker,
            ctx,
        );

        let coset = if crate::config::DEBUG_SATISFIABLE == false {
            F::multiplicative_generator()
        } else {
            F::ONE
        };

        let unnormalized_l1_inverse = unnormalized_l1_inverse::<F, P, Global, Global>(
            domain_size,
            quotient_degree, // we do not need full degree
            F::multiplicative_generator(),
            worker,
            ctx,
        );

        let quotient_monomials = {
            // we will need to add the corresponding contribution from copy permutation

            // z(1) == 1 => (z(x) - 1) * L_1(x) == 0
            // that is equivalent to divisibility check that
            // (z(x) - 1) is divisible by (x - 1)

            // But in order to batch division by x^n - 1 below we will compute an (unnormalized)
            // (z(x) - 1) * L_1(x) term anyway

            // later on we will need terms like
            // partial_product_i = partial_product_{i-1} * rational_function, but we have everything precomputed
            // for it already

            // the last part is z(x * omega) = partial_product_{n-1} * rational_function

            let mut q_c0_as_lde =
                ArcGenericLdeStorage::empty_with_capacity_in(quotient_c0s.len(), Global);
            let mut q_c1_as_lde =
                ArcGenericLdeStorage::empty_with_capacity_in(quotient_c0s.len(), Global);
            for el in quotient_c0s.into_iter() {
                q_c0_as_lde
                    .storage
                    .push(Arc::new(GenericPolynomial::from_storage(el)));
            }
            for el in quotient_c1s.into_iter() {
                q_c1_as_lde
                    .storage
                    .push(Arc::new(GenericPolynomial::from_storage(el)));
            }

            let mut challenges_it = remaining_challenges.iter();
            let mut lookup_challenges_it = pregenerated_challenges_for_lookup.iter();

            let one = P::one(ctx);
            let alpha_power = challenges_it.next().expect("must have enough challenges");
            let alpha_power_c0 = P::constant(alpha_power.coeffs[0], ctx);
            let alpha_power_c1 = P::constant(alpha_power.coeffs[1], ctx);

            let z_poly_c0 = second_stage_polys_storage.z_poly[0].subset_for_degree(quotient_degree);
            let z_poly_c1 = second_stage_polys_storage.z_poly[1].subset_for_degree(quotient_degree);

            let mut dst = [q_c0_as_lde, q_c1_as_lde];

            if crate::config::DEBUG_SATISFIABLE == false {
                let src = [
                    z_poly_c0.clone(),
                    z_poly_c1.clone(),
                    unnormalized_l1_inverse,
                ];

                let op = #[inline(always)]
                move |dst: &mut [ArcGenericLdeStorage<F, P, Global, Global>; 2],
                               src: &[ArcGenericLdeStorage<F, P, Global, Global>; 3],
                               outer: usize,
                               inner: usize,
                               ctx: &mut P::Context| {
                    let mut z_c0 = src[0].storage[outer].storage[inner];
                    // sub 1
                    z_c0.sub_assign(&one, ctx);
                    let mut z_c1 = src[1].storage[outer].storage[inner];
                    let l1_inv = &src[2].storage[outer].storage[inner];
                    z_c0.mul_assign(l1_inv, ctx);
                    z_c1.mul_assign(l1_inv, ctx);
                    // mul by alpha
                    mul_assign_vectorized_in_extension::<F, P, EXT>(
                        &mut z_c0,
                        &mut z_c1,
                        &alpha_power_c0,
                        &alpha_power_c1,
                        ctx,
                    );

                    unsafe {
                        Arc::get_mut_unchecked(&mut dst[0].storage[outer]).storage[inner]
                            .add_assign(&z_c0, ctx);

                        Arc::get_mut_unchecked(&mut dst[1].storage[outer]).storage[inner]
                            .add_assign(&z_c1, ctx);
                    }
                };

                apply_multiop(&mut dst, &src, &op, worker, ctx)
            } else {
                debug_assert_eq!(
                    P::slice_into_base_slice(&z_poly_c0.storage[0].storage)[0],
                    F::ONE
                );
                debug_assert_eq!(
                    P::slice_into_base_slice(&z_poly_c1.storage[0].storage)[0],
                    F::ZERO
                );
            }

            let [mut q_c0_as_lde, mut q_c1_as_lde] = dst;

            let num_challenges = num_intermediate_partial_product_relations + 1;
            let mut alphas = Vec::with_capacity(num_challenges);
            for _ in 0..num_challenges {
                alphas.push(
                    challenges_it
                        .next()
                        .copied()
                        .expect("challenge for copy-permutation part"),
                );
            }

            crate::cs::implementations::copy_permutation::compute_quotient_terms_in_extension(
                domain_size,
                quotient_degree,
                &trace_holder.variables,
                &second_stage_polys_storage,
                &trace_holder.setup,
                num_intermediate_partial_product_relations,
                beta,
                gamma,
                alphas,
                &x_poly_lde,
                &mut q_c0_as_lde,
                &mut q_c1_as_lde,
                worker,
                ctx,
            );

            // now we add contribution from lookups - that at the domain

            // A(x) * (gamma^0 * column_0 + ... + gamma^n * column_n) == lookup_selector
            // B(x) * (gamma^0 * column_0 + ... + gamma^n * column_n) == multiplicity column

            // each of those is 1 term per lookup subargument

            match self.lookup_parameters {
                LookupParameters::NoLookup => {}
                LookupParameters::TableIdAsConstant { .. }
                | LookupParameters::TableIdAsVariable { .. } => {
                    // lookup argument related parts

                    // exists by our setup
                    let lookup_evaluator_id = 0;
                    let selector_subpath = setup_base
                        .selectors_placement
                        .output_placement(lookup_evaluator_id)
                        .expect("lookup gate must be placed");
                    let _columns_per_subargument = self.lookup_parameters.columns_per_subargument();

                    let _selector = selectors_buffer
                        .get(&selector_subpath)
                        .cloned()
                        .expect("path must be unique and precomputed");
                    let mut lookup_terms_challenges =
                        Vec::with_capacity(total_num_lookup_argument_terms);
                    for _ in 0..total_num_lookup_argument_terms {
                        lookup_terms_challenges.push(
                            lookup_challenges_it
                                .next()
                                .copied()
                                .expect("challenge for lookup argument A/B polys"),
                        );
                    }

                    todo!()

                    // super::lookup_argument::compute_quotient_terms_for_lookup_over_general_purpose_gates(
                    //     &trace_holder.variables,
                    //     &second_stage_polys_storage,
                    //     &trace_holder.setup,
                    //     selector,
                    //     lookup_beta,
                    //     lookup_gamma,
                    //     lookup_terms_challenges,
                    //     table_ids_column_idxes.clone(),
                    //     columns_per_subargument as usize,
                    //     num_lookup_subarguments,
                    //     set_idx,
                    //     quotient_degree,
                    //     &mut q_as_lde,
                    //     worker,
                    //     ctx,
                    // );
                }
                LookupParameters::UseSpecializedColumnsWithTableIdAsConstant { .. }
                | LookupParameters::UseSpecializedColumnsWithTableIdAsVariable { .. } => {
                    // lookup argument related parts

                    let mut lookup_terms_challenges =
                        Vec::with_capacity(total_num_lookup_argument_terms);
                    for _ in 0..total_num_lookup_argument_terms {
                        lookup_terms_challenges.push(
                            lookup_challenges_it
                                .next()
                                .copied()
                                .expect("challenge for lookup argument A/B polys"),
                        );
                    }

                    let columns_per_subargument =
                        self.lookup_parameters.specialized_columns_per_subargument();

                    super::lookup_argument_in_ext::compute_quotient_terms_for_lookup_specialized(
                        &trace_holder.variables,
                        &second_stage_polys_storage,
                        &trace_holder.setup,
                        lookup_beta,
                        lookup_gamma,
                        lookup_terms_challenges,
                        table_ids_column_idxes.clone(),
                        columns_per_subargument as usize,
                        num_lookup_subarguments,
                        num_multiplicities_polys,
                        self.parameters.num_columns_under_copy_permutation,
                        quotient_degree,
                        &mut q_c0_as_lde,
                        &mut q_c1_as_lde,
                        worker,
                        ctx,
                    );
                }
            }

            assert_eq!(challenges_it.len(), 0, "must exhaust all the challenges");

            let mut q_c0_as_vectors: Vec<Vec<P>> = q_c0_as_lde
                .storage
                .into_iter()
                .map(|el| {
                    Arc::try_unwrap(el)
                        .expect("must be exclusively owned")
                        .into_storage()
                })
                .collect();

            let mut q_c1_as_vectors: Vec<Vec<P>> = q_c1_as_lde
                .storage
                .into_iter()
                .map(|el| {
                    Arc::try_unwrap(el)
                        .expect("must be exclusively owned")
                        .into_storage()
                })
                .collect();

            if crate::config::DEBUG_SATISFIABLE == false {
                divide_by_vanishing_for_bitreversed_coset_enumeration(
                    &mut q_c0_as_vectors,
                    worker,
                    ctx,
                );
                divide_by_vanishing_for_bitreversed_coset_enumeration(
                    &mut q_c1_as_vectors,
                    worker,
                    ctx,
                );
            }

            let q_c0: Vec<Vec<F>> = q_c0_as_vectors
                .into_iter()
                .map(|el| P::vec_into_base_vec(el))
                .collect();

            let q_c1: Vec<Vec<F>> = q_c1_as_vectors
                .into_iter()
                .map(|el| P::vec_into_base_vec(el))
                .collect();

            let flattened_c0 = flatten_presumably_bitreversed::<_, P, _, _>(q_c0, worker);
            let flattened_c1 = flatten_presumably_bitreversed::<_, P, _, _>(q_c1, worker);
            let mut monomial_form_c0 = P::vec_from_base_vec(flattened_c0);
            let mut monomial_form_c1 = P::vec_from_base_vec(flattened_c1);

            if crate::config::DEBUG_SATISFIABLE {
                let as_slice = P::slice_into_base_slice(&monomial_form_c0);
                for (idx, el) in as_slice.iter().step_by(quotient_degree).enumerate() {
                    assert_eq!(*el, F::ZERO, "poly is not divisible at row {}", idx);
                }
            }

            P::ifft_natural_to_natural(&mut monomial_form_c0, coset, &inverse_twiddles, ctx);
            P::ifft_natural_to_natural(&mut monomial_form_c1, coset, &inverse_twiddles, ctx);

            if crate::config::DEBUG_SATISFIABLE == false {
                assert!(
                    P::slice_into_base_slice(&monomial_form_c0)
                        .last()
                        .unwrap()
                        .is_zero(),
                    "unsatisfied",
                );
                assert!(
                    P::slice_into_base_slice(&monomial_form_c1)
                        .last()
                        .unwrap()
                        .is_zero(),
                    "unsatisfied",
                );
            }

            [
                GenericPolynomial::<F, MonomialForm, P, _>::from_storage(monomial_form_c0),
                GenericPolynomial::<F, MonomialForm, P, _>::from_storage(monomial_form_c1),
            ]
        };

        // now we can chunk every polynomial and LDE them

        // NOTE: for all the polynomials below we will have an option to perform evaluation at random
        // point by using barycentric formula, while for quotient we could potentially save monomial form
        // for some time and use horner rule. We neglect small change of proof time in favor of simplicity
        // and memory consumption

        let mut quotient_chunks = vec![];
        let [q_c0, q_c1] = quotient_monomials;
        // we layout [c0, c1] in every chunk

        for (c0, c1) in q_c0
            .chunk_into_subpolys_of_degree::<Global>(base_system_degree)
            .into_iter()
            .zip(q_c1.chunk_into_subpolys_of_degree::<Global>(base_system_degree))
        {
            let c0 = c0.into_storage();
            let c1 = c1.into_storage();
            quotient_chunks.push(c0);
            quotient_chunks.push(c1);
        }

        // how we should LDE quotients and form another oracle

        let forward_twiddles =
            P::precompute_forward_twiddles_for_fft::<Global>(domain_size, worker, ctx);

        // we do not need full quotient LDE degree here, only large enough for FRI
        let quotient_chunks_ldes = transform_monomials_to_lde(
            quotient_chunks,
            domain_size,
            proof_config.fri_lde_factor,
            &forward_twiddles,
            worker,
            ctx,
        );

        drop(sect_6);
        profile_section!(sect_7);

        log!("Quotient work and LDE taken {:?}", now.elapsed());

        let source = quotient_chunks_ldes.clone();
        let quotients_tree = MerkleTreeWithCap::<F, H>::construct(source, cap_size, worker);

        // now we can commit to grand products and get new challenges
        let quotients_tree_cap = quotients_tree.get_cap();

        transcript.witness_merkle_tree_cap(quotients_tree_cap.as_ref());

        // now evaluate corresponding polynomials at corresponding z-s, and check equality

        let now = std::time::Instant::now();

        let z = transcript.get_multiple_challenges_fixed::<2>();
        let z = ExtensionField::<F, 2, EXT>::from_coeff_in_base(z);

        // we have to evaluate all sets at the corresponding point

        // let mut naive = ExtensionField::<F, 2, EXT>::ZERO;
        // let mut current = ExtensionField::<F, 2, EXT>::ONE;
        // for (c0, c1) in P::slice_into_base_slice(&quotient_chunks_tmp[0]).iter()
        //     .zip(P::slice_into_base_slice(&quotient_chunks_tmp[1]).iter()) {
        //     let mut tmp = ExtensionField::from_coeff_in_base([*c0, *c1]);
        //     tmp.mul_assign(&current);
        //     naive.add_assign(&tmp);

        //     current.mul_assign(&z);
        // }

        // dbg!(&naive);

        let [precomputed_lagranges_c0, precomputed_lagranges_c1] =
            precompute_for_barycentric_evaluation_in_extension::<F, EXT, P, Global>(
                domain_size,
                F::multiplicative_generator(),
                z,
                worker,
                ctx,
            );

        let mut all_polys_at_zs = vec![];

        let evaluate_from_base = |coeffs: &[P]| {
            barycentric_evaluate_base_at_extension_for_bitreversed_parallel(
                P::slice_into_base_slice(coeffs),
                P::slice_into_base_slice(&precomputed_lagranges_c0),
                P::slice_into_base_slice(&precomputed_lagranges_c1),
                worker,
            )
        };

        let evaluate_from_extension = |coeffs_c0: &[P], coeffs_c1: &[P]| {
            barycentric_evaluate_extension_at_extension_for_bitreversed_parallel::<F, EXT>(
                P::slice_into_base_slice(coeffs_c0),
                P::slice_into_base_slice(coeffs_c1),
                P::slice_into_base_slice(&precomputed_lagranges_c0),
                P::slice_into_base_slice(&precomputed_lagranges_c1),
                worker,
            )
        };

        // witness
        all_polys_at_zs.extend(
            trace_holder
                .variables
                .variables_columns
                .iter()
                .map(|el| &el.storage[0].as_ref().storage)
                .map(|el| evaluate_from_base(el))
                .map(|el| ExtensionField::<F, 2, EXT>::from_coeff_in_base(el)),
        );
        all_polys_at_zs.extend(
            trace_holder
                .variables
                .witness_columns
                .iter()
                .map(|el| &el.storage[0].as_ref().storage)
                .map(|el| evaluate_from_base(el))
                .map(|el| ExtensionField::<F, 2, EXT>::from_coeff_in_base(el)),
        );
        // "normal" setup
        all_polys_at_zs.extend(
            trace_holder
                .setup
                .constant_columns
                .iter()
                .map(|el| &el.storage[0].as_ref().storage)
                .map(|el| evaluate_from_base(el))
                .map(|el| ExtensionField::<F, 2, EXT>::from_coeff_in_base(el)),
        );
        all_polys_at_zs.extend(
            trace_holder
                .setup
                .copy_permutation_polys
                .iter()
                .map(|el| &el.storage[0].as_ref().storage)
                .map(|el| evaluate_from_base(el))
                .map(|el| ExtensionField::<F, 2, EXT>::from_coeff_in_base(el)),
        );
        // copy-permutation
        all_polys_at_zs.push(ExtensionField::<F, 2, EXT>::from_coeff_in_base(
            evaluate_from_extension(
                &second_stage_polys_storage.z_poly[0].storage[0]
                    .as_ref()
                    .storage,
                &second_stage_polys_storage.z_poly[1].storage[0]
                    .as_ref()
                    .storage,
            ),
        ));
        all_polys_at_zs.extend(
            second_stage_polys_storage
                .intermediate_polys
                .iter()
                .map(|[a, b]| {
                    [
                        &a.storage[0].as_ref().storage,
                        &b.storage[0].as_ref().storage,
                    ]
                })
                .map(|[a, b]| evaluate_from_extension(a, b))
                .map(|el| ExtensionField::<F, 2, EXT>::from_coeff_in_base(el)),
        );

        assert_eq!(
            all_polys_at_zs.len(),
            num_variable_polys
                + num_witness_polys
                + num_constant_polys
                + num_copy_permutation_polys
                + 1
                + num_intermediate_partial_product_relations
        );
        // lookup part if exists
        // lookup multiplicities
        all_polys_at_zs.extend(
            trace_holder
                .variables
                .lookup_multiplicities_polys
                .iter()
                .map(|el| &el.storage[0].as_ref().storage)
                .map(|el| evaluate_from_base(el))
                .map(|el| ExtensionField::<F, 2, EXT>::from_coeff_in_base(el)),
        );
        // lookup witness and multiplicities
        all_polys_at_zs.extend(
            second_stage_polys_storage
                .lookup_witness_encoding_polys
                .iter()
                .map(|[a, b]| {
                    [
                        &a.storage[0].as_ref().storage,
                        &b.storage[0].as_ref().storage,
                    ]
                })
                .map(|[a, b]| evaluate_from_extension(a, b))
                .map(|el| ExtensionField::<F, 2, EXT>::from_coeff_in_base(el)),
        );
        all_polys_at_zs.extend(
            second_stage_polys_storage
                .lookup_multiplicities_encoding_polys
                .iter()
                .map(|[a, b]| {
                    [
                        &a.storage[0].as_ref().storage,
                        &b.storage[0].as_ref().storage,
                    ]
                })
                .map(|[a, b]| evaluate_from_extension(a, b))
                .map(|el| ExtensionField::<F, 2, EXT>::from_coeff_in_base(el)),
        );
        // lookup setup
        // tables columns
        all_polys_at_zs.extend(
            trace_holder
                .setup
                .lookup_tables_columns
                .iter()
                .map(|el| &el.storage[0].as_ref().storage)
                .map(|el| evaluate_from_base(el))
                .map(|el| ExtensionField::<F, 2, EXT>::from_coeff_in_base(el)),
        );
        // table ids are not needed as those come from constatns in general
        // quotient
        all_polys_at_zs.extend(
            quotient_chunks_ldes
                .array_chunks::<2>()
                .map(|[a, b]| {
                    [
                        &a.storage[0].as_ref().storage,
                        &b.storage[0].as_ref().storage,
                    ]
                })
                .map(|[a, b]| evaluate_from_extension(a, b))
                .map(|el| ExtensionField::<F, 2, EXT>::from_coeff_in_base(el)),
        );

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

        assert_eq!(all_polys_at_zs.len(), num_poly_values_at_z);

        for set in all_polys_at_zs.iter() {
            transcript.witness_field_elements(set.as_coeffs_in_base());
        }

        let mut z_omega = z;
        z_omega.mul_assign_by_base(&domain_generator_for_size::<F>(domain_size as u64));

        let [precomputed_lagranges_c0, precomputed_lagranges_c1] =
            precompute_for_barycentric_evaluation_in_extension::<F, EXT, P, Global>(
                domain_size,
                F::multiplicative_generator(),
                z_omega,
                worker,
                ctx,
            );

        let evaluate_from_extension = |coeffs_c0: &[P], coeffs_c1: &[P]| {
            barycentric_evaluate_extension_at_extension_for_bitreversed_parallel::<F, EXT>(
                P::slice_into_base_slice(coeffs_c0),
                P::slice_into_base_slice(coeffs_c1),
                P::slice_into_base_slice(&precomputed_lagranges_c0),
                P::slice_into_base_slice(&precomputed_lagranges_c1),
                worker,
            )
        };

        let all_polys_at_zomegas = vec![ExtensionField::<F, 2, EXT>::from_coeff_in_base(
            evaluate_from_extension(
                &second_stage_polys_storage.z_poly[0].storage[0]
                    .as_ref()
                    .storage,
                &second_stage_polys_storage.z_poly[1].storage[0]
                    .as_ref()
                    .storage,
            ),
        )];
        assert_eq!(all_polys_at_zomegas.len(), 1);

        for set in all_polys_at_zomegas.iter() {
            transcript.witness_field_elements(set.as_coeffs_in_base());
        }

        let mut all_polys_at_zero = vec![];

        drop(sect_7);
        profile_section!(sect_8);

        if self.lookup_parameters != LookupParameters::NoLookup {
            let [precomputed_lagranges_c0, precomputed_lagranges_c1] =
                precompute_for_barycentric_evaluation_in_extension::<F, EXT, P, Global>(
                    domain_size,
                    F::multiplicative_generator(),
                    ExtensionField::<F, 2, EXT>::ZERO,
                    worker,
                    ctx,
                );

            let evaluate_from_extension = |coeffs_c0: &[P], coeffs_c1: &[P]| {
                barycentric_evaluate_extension_at_extension_for_bitreversed_parallel::<F, EXT>(
                    P::slice_into_base_slice(coeffs_c0),
                    P::slice_into_base_slice(coeffs_c1),
                    P::slice_into_base_slice(&precomputed_lagranges_c0),
                    P::slice_into_base_slice(&precomputed_lagranges_c1),
                    worker,
                )
            };

            all_polys_at_zero.extend(
                second_stage_polys_storage
                    .lookup_witness_encoding_polys
                    .iter()
                    .map(|[a, b]| {
                        [
                            &a.storage[0].as_ref().storage,
                            &b.storage[0].as_ref().storage,
                        ]
                    })
                    .map(|[a, b]| evaluate_from_extension(a, b))
                    .map(|el| ExtensionField::<F, 2, EXT>::from_coeff_in_base(el)),
            );
            all_polys_at_zero.extend(
                second_stage_polys_storage
                    .lookup_multiplicities_encoding_polys
                    .iter()
                    .map(|[a, b]| {
                        [
                            &a.storage[0].as_ref().storage,
                            &b.storage[0].as_ref().storage,
                        ]
                    })
                    .map(|[a, b]| evaluate_from_extension(a, b))
                    .map(|el| ExtensionField::<F, 2, EXT>::from_coeff_in_base(el)),
            );
        }

        assert_eq!(all_polys_at_zero.len(), total_num_lookup_argument_terms);

        for set in all_polys_at_zero.iter() {
            transcript.witness_field_elements(set.as_coeffs_in_base());
        }

        // and public inputs should also go into quotient
        let mut public_input_opening_tuples: Vec<(F, Vec<(usize, F)>)> = vec![];
        {
            let omega = domain_generator_for_size::<F>(domain_size as u64);

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
        }

        // We have committed to all the polynomials and evaluated them at random point.
        // Now we should perform quotening operation to compute terms of the form (f(x) - f(z))/(x - z)
        // and simultaneously form a (presumably) RS code word

        // Since it will be the last step before FRI, we will use challenges from extension

        let c0 = transcript.get_challenge();
        let c1 = transcript.get_challenge();

        let mut total_num_challenges = 0;
        total_num_challenges += num_poly_values_at_z;
        total_num_challenges += 1;
        total_num_challenges += total_num_lookup_argument_terms;
        for (_, subset) in public_input_opening_tuples.iter() {
            total_num_challenges += subset.len();
        }

        let challenges = materialize_ext_challenge_powers::<F, EXT>((c0, c1), total_num_challenges);
        // we may use lower factor LDE for FRI if we want
        let lde_factor_for_fri = proof_config.fri_lde_factor;

        let mut outer_c0 = Vec::with_capacity(lde_factor_for_fri);
        let mut outer_c1 = Vec::with_capacity(lde_factor_for_fri);
        for _ in 0..lde_factor_for_fri {
            let buff = vec![P::zero(ctx); inner_size];
            outer_c0.push(buff);
            let buff = vec![P::zero(ctx); inner_size];
            outer_c1.push(buff);
        }

        let x_poly_lde_subset = x_poly_lde.subset_for_degree(lde_factor_for_fri);

        let mut challenges_offset = 0;

        let map_base_for_quotening =
            move |input: &[ArcGenericLdeStorage<F, P, Global, Global>]| {
                input
                    .iter()
                    .map(|el| {
                        let c0 = el.subset_for_degree(lde_factor_for_fri);

                        [Some(c0), None]
                    })
                    .collect::<Vec<_>>()
            };

        let map_extension_for_quotening =
            move |input: &[[ArcGenericLdeStorage<F, P, Global, Global>; 2]]| {
                input
                    .iter()
                    .map(|[a, b]| {
                        let c0 = a.subset_for_degree(lde_factor_for_fri);
                        let c1 = b.subset_for_degree(lde_factor_for_fri);

                        [Some(c0), Some(c1)]
                    })
                    .collect::<Vec<_>>()
            };

        let mut sources = vec![];
        // witness
        sources.extend(map_base_for_quotening(
            &trace_holder.variables.variables_columns,
        ));
        sources.extend(map_base_for_quotening(
            &trace_holder.variables.witness_columns,
        ));
        // normal setup
        sources.extend(map_base_for_quotening(&trace_holder.setup.constant_columns));
        sources.extend(map_base_for_quotening(
            &trace_holder.setup.copy_permutation_polys,
        ));
        // copy permutation
        sources.extend(map_extension_for_quotening(&[second_stage_polys_storage
            .z_poly
            .clone()]));
        sources.extend(map_extension_for_quotening(
            &second_stage_polys_storage.intermediate_polys,
        ));
        // lookup if exists
        sources.extend(map_base_for_quotening(
            &trace_holder.variables.lookup_multiplicities_polys,
        ));
        sources.extend(map_extension_for_quotening(
            &second_stage_polys_storage.lookup_witness_encoding_polys,
        ));
        sources.extend(map_extension_for_quotening(
            &second_stage_polys_storage.lookup_multiplicities_encoding_polys,
        ));
        // lookup setup
        if self.lookup_parameters.lookup_is_allowed() {
            sources.extend(map_base_for_quotening(
                &trace_holder.setup.lookup_tables_columns,
            ));
        }
        // quotient
        let quotinents: Vec<_> = quotient_chunks_ldes.array_chunks::<2>().cloned().collect();
        sources.extend(map_extension_for_quotening(&quotinents));

        let num_challenges_required = sources.len();

        let values_at_z = all_polys_at_zs.clone();

        assert_eq!(values_at_z.len(), num_challenges_required);

        log!("Making quotiening at Z");

        quotening_operation_in_extension(
            &mut outer_c0,
            &mut outer_c1,
            sources,
            values_at_z,
            &x_poly_lde_subset,
            z,
            &challenges[challenges_offset..(challenges_offset + num_challenges_required)],
            worker,
            ctx,
        );

        challenges_offset += num_challenges_required;

        // now at z_omega

        let mut sources = vec![];
        sources.extend(map_extension_for_quotening(&[second_stage_polys_storage
            .z_poly
            .clone()]));

        let num_challenges_required = sources.len();

        let values_at_z_omega = all_polys_at_zomegas.clone();

        assert_eq!(values_at_z_omega.len(), num_challenges_required);

        log!("Making quotiening at Z*omega");

        quotening_operation_in_extension(
            &mut outer_c0,
            &mut outer_c1,
            sources,
            values_at_z_omega,
            &x_poly_lde_subset,
            z_omega,
            &challenges[challenges_offset..(challenges_offset + num_challenges_required)],
            worker,
            ctx,
        );

        drop(sect_8);
        profile_section!(sect_9);

        challenges_offset += num_challenges_required;

        // and now at 0 for sumcheck for lookup argument
        if self.lookup_parameters != LookupParameters::NoLookup {
            let mut sources = vec![];
            sources.extend(map_extension_for_quotening(
                &second_stage_polys_storage.lookup_witness_encoding_polys,
            ));
            sources.extend(map_extension_for_quotening(
                &second_stage_polys_storage.lookup_multiplicities_encoding_polys,
            ));

            let num_challenges_required = sources.len();

            let values_at_zero = all_polys_at_zero.clone();

            assert_eq!(values_at_zero.len(), num_challenges_required);

            log!("Making quotiening at 0 for lookups sumchecks");

            quotening_operation_in_extension(
                &mut outer_c0,
                &mut outer_c1,
                sources,
                values_at_zero,
                &x_poly_lde_subset,
                ExtensionField::<F, 2, EXT>::ZERO,
                &challenges[challenges_offset..(challenges_offset + num_challenges_required)],
                worker,
                ctx,
            );

            challenges_offset += num_challenges_required;
        }

        // add public inputs by quotening
        {
            for (open_at, set) in public_input_opening_tuples.into_iter() {
                let mut sources = Vec::with_capacity(set.len());
                let mut values = Vec::with_capacity(set.len());
                for (column, expected_value) in set.into_iter() {
                    sources.extend(map_base_for_quotening(&[trace_holder
                        .variables
                        .variables_columns[column]
                        .clone()]));
                    let expected_value =
                        ExtensionField::<F, 2, EXT>::from_coeff_in_base([expected_value, F::ZERO]);
                    values.push(expected_value);
                }
                let num_challenges_required = sources.len();
                assert_eq!(values.len(), num_challenges_required);

                log!("Making quotiening at {} for public inputs", open_at);

                let open_at = ExtensionField::<F, 2, EXT>::from_coeff_in_base([open_at, F::ZERO]);

                quotening_operation_in_extension(
                    &mut outer_c0,
                    &mut outer_c1,
                    sources,
                    values,
                    &x_poly_lde_subset,
                    open_at,
                    &challenges[challenges_offset..(challenges_offset + num_challenges_required)],
                    worker,
                    ctx,
                );

                challenges_offset += num_challenges_required;
            }
        }

        assert_eq!(challenges_offset, challenges.len());

        // for simplicity we transform c0 and c1 into ArcGenericPoly

        let c0_as_poly = GenericLdeStorage {
            storage: outer_c0
                .into_iter()
                .map(|el| GenericPolynomial::<F, BitreversedLagrangeForm, P, _>::from_storage(el))
                .collect(),
        };

        let c0_as_poly = ArcGenericLdeStorage::from_owned(c0_as_poly);

        let c1_as_poly = GenericLdeStorage {
            storage: outer_c1
                .into_iter()
                .map(|el| GenericPolynomial::<F, BitreversedLagrangeForm, P, _>::from_storage(el))
                .collect(),
        };

        let c1_as_poly = ArcGenericLdeStorage::from_owned(c1_as_poly);

        log!("Batched FRI opening computation taken {:?}", now.elapsed());

        // now we just have to do FRI. In general our strategy is:
        // - access oracles at single evaluation point (path), and get wide leafs
        // - simulate single element of RS code word by doing quotiening operation. It will be our first
        // FRI oracle. We may want to have 8 or 4 elements per leaf, so we can have smaller
        // number of FRI intermediate oracles

        let basic_pow_bits = proof_config.pow_bits;

        let (
            new_pow_bits,                 // updated POW bits if needed
            num_queries,                  // num queries
            interpolation_log2s_schedule, // folding schedule
            final_expected_degree,
        ) = compute_fri_schedule(
            proof_config.security_level as u32,
            cap_size,
            basic_pow_bits,
            lde_factor_for_fri.trailing_zeros(),
            domain_size.trailing_zeros(),
        );

        dbg!(&interpolation_log2s_schedule);
        dbg!(cap_size);

        let fri_data = do_fri::<F, P, EXT, TR, H, Global, Global>(
            c0_as_poly.clone(),
            c1_as_poly.clone(),
            &mut transcript,
            interpolation_log2s_schedule.clone(),
            lde_factor_for_fri,
            cap_size,
            worker,
            ctx,
        );

        assert_eq!(fri_data.monomial_forms[0].len(), final_expected_degree);
        assert_eq!(fri_data.monomial_forms[1].len(), final_expected_degree);

        // now we can do PoW if we want

        let pow_challenge = if new_pow_bits != 0 {
            log!("Doing PoW");

            let now = std::time::Instant::now();

            // pull enough challenges from the transcript
            let mut num_challenges = 256 / F::CHAR_BITS;
            if num_challenges % F::CHAR_BITS != 0 {
                num_challenges += 1;
            }
            let challenges = transcript.get_multiple_challenges(num_challenges);
            let pow_challenge = POW::run_from_field_elements(challenges, new_pow_bits, worker);

            assert!(F::CAPACITY_BITS >= 32);
            let (low, high) = (pow_challenge as u32, (pow_challenge >> 32) as u32);
            let low = F::from_u64_unchecked(low as u64);
            let high = F::from_u64_unchecked(high as u64);
            transcript.witness_field_elements(&[low, high]);

            log!("PoW for {} bits taken {:?}", new_pow_bits, now.elapsed());

            pow_challenge
        } else {
            0
        };

        assert!(
            proof_config.fri_folding_schedule.is_none(),
            "we do not yet support externally provided FRI schedule"
        );

        let mut proof = Proof::<F, H, EXT> {
            proof_config,
            public_inputs: public_inputs_only_values,
            witness_oracle_cap: witness_tree_cap.clone(),
            stage_2_oracle_cap: second_stage_tree_cap.clone(),
            quotient_oracle_cap: quotients_tree_cap.clone(),
            final_fri_monomials: fri_data.monomial_forms.clone(),
            values_at_z: all_polys_at_zs.clone(),
            values_at_z_omega: all_polys_at_zomegas.clone(),
            values_at_0: all_polys_at_zero.clone(),
            pow_challenge,
            fri_base_oracle_cap: fri_data.base_oracle.get_cap(),
            fri_intermediate_oracles_caps: fri_data
                .intermediate_oracles
                .iter()
                .map(|el| el.get_cap())
                .collect(),
            queries_per_fri_repetition: vec![],
            _marker: std::marker::PhantomData,
        };

        let max_needed_bits = (domain_size * lde_factor_for_fri).trailing_zeros() as usize;
        let mut bools_buffer = BoolsBuffer {
            available: vec![],
            max_needed: max_needed_bits,
        };

        let base_fri_source = (c0_as_poly, c1_as_poly);

        let num_bits_for_in_coset_index =
            max_needed_bits - lde_factor_for_fri.trailing_zeros() as usize;

        for _query_idx in 0..num_queries {
            let query_index_lsb_first_bits =
                bools_buffer.get_bits(&mut transcript, max_needed_bits);
            // we consider it to be some convenient for us encoding of coset + inner index.

            let inner_idx = u64_from_lsb_first_bits(
                &query_index_lsb_first_bits[0..num_bits_for_in_coset_index],
            ) as usize;
            let coset_idx =
                u64_from_lsb_first_bits(&query_index_lsb_first_bits[num_bits_for_in_coset_index..])
                    as usize;

            use crate::cs::implementations::proof::OracleQuery;

            let witness_query = OracleQuery::construct(
                &witness_tree,
                &trace_holder.variables,
                lde_factor_for_fri,
                coset_idx,
                domain_size,
                inner_idx,
                1,
            );

            let second_stage_query = OracleQuery::construct(
                &second_stage_tree,
                &second_stage_polys_storage,
                lde_factor_for_fri,
                coset_idx,
                domain_size,
                inner_idx,
                1,
            );

            let quotient_query = OracleQuery::construct(
                &quotients_tree,
                &quotient_chunks_ldes,
                lde_factor_for_fri,
                coset_idx,
                domain_size,
                inner_idx,
                1,
            );

            let setup_query = OracleQuery::construct(
                setup_tree,
                setup,
                lde_factor_for_fri,
                coset_idx,
                domain_size,
                inner_idx,
                1,
            );

            let mut domain_size = domain_size;
            let mut fri_queries = Vec::with_capacity(interpolation_log2s_schedule.len());
            let mut inner_idx = inner_idx;
            for (idx, interpolation_degree_log2) in interpolation_log2s_schedule.iter().enumerate()
            {
                let fri_oracle_query = if idx == 0 {
                    OracleQuery::construct(
                        &fri_data.base_oracle,
                        &base_fri_source,
                        lde_factor_for_fri,
                        coset_idx,
                        domain_size,
                        inner_idx,
                        1 << *interpolation_degree_log2,
                    )
                } else {
                    OracleQuery::construct(
                        &fri_data.intermediate_oracles[idx - 1],
                        &&fri_data.leaf_sources_for_intermediate_oracles[idx - 1],
                        lde_factor_for_fri,
                        coset_idx,
                        domain_size,
                        inner_idx,
                        1 << *interpolation_degree_log2,
                    )
                };
                inner_idx >>= *interpolation_degree_log2;
                domain_size >>= *interpolation_degree_log2;
                fri_queries.push(fri_oracle_query)
            }

            let queries = SingleRoundQueries {
                witness_query,
                stage_2_query: second_stage_query,
                quotient_query,
                setup_query,
                fri_queries,
            };

            proof.queries_per_fri_repetition.push(queries);
        }

        proof
    }
}

pub(crate) fn u64_from_lsb_first_bits(bits: &[bool]) -> u64 {
    let mut result = 0u64;
    for (shift, bit) in bits.iter().enumerate() {
        result |= (*bit as u64) << shift;
    }

    result
}

pub fn compute_fri_schedule(
    security_bits: u32,
    cap_size: usize,
    pow_bits: u32,
    rate_log_two: u32,
    initial_degree_log_two: u32,
) -> (
    u32,        // updated POW bits if needed
    usize,      // num queries
    Vec<usize>, // folding schedule,
    usize,      // final poly degree to expect
) {
    assert!(security_bits > pow_bits);
    let mut raw_security_bits = security_bits - pow_bits;

    let mut new_pow_bits = pow_bits;
    if raw_security_bits % rate_log_two != 0 {
        // there is no point to do so much PoW
        if new_pow_bits >= rate_log_two - (raw_security_bits % rate_log_two) {
            new_pow_bits -= rate_log_two - (raw_security_bits % rate_log_two);
        }
    }

    raw_security_bits = security_bits - new_pow_bits;

    let mut num_queries = raw_security_bits / rate_log_two;
    if raw_security_bits % rate_log_two != 0 {
        num_queries += 1;
    }

    // we assume that cap size should be such that we win on queries

    // let optimal_cap_size = if num_queries.is_power_of_two() {
    //     // so it's unique on average
    //     num_queries
    // } else {
    //     num_queries.next_power_of_two() / 2
    // };

    // if optimal_cap_size as usize != cap_size {
    //     log!(
    //         "Cap size is not optimal: suggested to have {}, configuration has {}",
    //         optimal_cap_size, cap_size
    //     );
    // }

    // we can stop FRI as soon as we got into plausibly low enough degree
    // or we should stop based on our optimal cap size
    let candidate_degree_from_cap_size = cap_size >> rate_log_two;
    let folding_stop_degree = std::cmp::max(1, candidate_degree_from_cap_size);
    assert!(folding_stop_degree.is_power_of_two());
    let folding_stop_degree_log_two = folding_stop_degree.trailing_zeros();

    // but also we have some cap size, and it's no point to make a FRI
    // folding step if our tree is smaller than cap size

    let mut degree_after_folding = initial_degree_log_two;
    let cap_size_log_two = cap_size.trailing_zeros();

    let mut schedule = vec![];
    while degree_after_folding > folding_stop_degree_log_two {
        let current_tree_size_log_two = degree_after_folding + rate_log_two;
        if current_tree_size_log_two <= cap_size_log_two {
            break;
        }
        if degree_after_folding - folding_stop_degree_log_two >= 3 {
            degree_after_folding -= 3;
            schedule.push(3);
        } else if degree_after_folding - folding_stop_degree_log_two == 2 {
            degree_after_folding -= 2;
            schedule.push(2);
        } else {
            assert_eq!(degree_after_folding - folding_stop_degree_log_two, 1);
            degree_after_folding -= 1;
            schedule.push(1);
            break;
        }

        let next_tree_size_log_two = degree_after_folding + rate_log_two;
        if next_tree_size_log_two <= cap_size_log_two {
            break;
        }
    }
    assert!(degree_after_folding + rate_log_two >= cap_size_log_two);

    (
        new_pow_bits,         // updated POW bits if needed
        num_queries as usize, // num queries
        schedule,             // folding schedule
        1 << degree_after_folding,
    )
}

pub fn materialize_ext_challenge_powers<F: SmallField, EXT: FieldExtension<2, BaseField = F>>(
    (c0, c1): (F, F),
    num_challenges: usize,
) -> Vec<(F, F)> {
    debug_assert!(num_challenges >= 2);
    let mut result = Vec::with_capacity(num_challenges);
    result.push((F::ONE, F::ZERO));
    result.push((c0, c1));
    let as_extension = ExtensionField::<F, 2, EXT> {
        coeffs: [c0, c1],
        _marker: std::marker::PhantomData,
    };

    let mut current = as_extension;
    for _ in 2..num_challenges {
        current.mul_assign(&as_extension);
        let [c0, c1] = current.into_coeffs_in_base();
        result.push((c0, c1));
    }

    result
}

fn quotening_operation<
    F: SmallField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    destination_c0: &mut Vec<Vec<P, A>, B>,
    destination_c1: &mut Vec<Vec<P, A>, B>,
    polynomial_ldes: Vec<ArcGenericLdeStorage<F, P, A, B>>,
    values_at_z: Vec<F>,
    precomputed_cosets: &ArcGenericLdeStorage<F, P, A, B>,
    at: F,
    challenge_coefficients: &[(F, F)],
    worker: &Worker,
    ctx: &mut P::Context,
) {
    // we precompute challenges outside to avoid any manual extension ops here

    assert_eq!(destination_c0.len(), destination_c1.len());
    assert_eq!(destination_c0.len(), precomputed_cosets.outer_len());
    assert_eq!(polynomial_ldes.len(), values_at_z.len());
    assert_eq!(polynomial_ldes.len(), challenge_coefficients.len());
    assert_eq!(destination_c0[0].len(), precomputed_cosets.inner_len());
    let polynomial_ldes_ref = &polynomial_ldes;
    let values_at_z_ref = &values_at_z;
    let challenge_coefficients_ref = challenge_coefficients;

    // we will work over every coset independently for simplicity
    for (coset_idx, (c0, c1)) in destination_c0
        .iter_mut()
        .zip(destination_c1.iter_mut())
        .enumerate()
    {
        debug_assert_eq!(c0.len(), c1.len());
        let work_size = c0.len();
        worker.scope(work_size, |scope, chunk_size| {
            for (chunk_idx, (c0, c1)) in c0
                .chunks_mut(chunk_size)
                .zip(c1.chunks_mut(chunk_size))
                .enumerate()
            {
                let mut ctx = *ctx;
                scope.spawn(move |_| {
                    let start = chunk_idx * chunk_size;
                    let mut end = start + chunk_size;
                    if end > work_size {
                        end = work_size;
                    }
                    // denominator is shared between everything, and we can compute it once here
                    let roots = &precomputed_cosets.storage[coset_idx].storage[start..end];
                    let at = P::constant(at, &mut ctx);
                    let mut roots_minus_z = roots.to_vec_in(A::default());

                    for el in roots_minus_z.iter_mut() {
                        el.sub_assign(&at, &mut ctx);
                    }
                    let mut denoms = P::vec_into_base_vec(roots_minus_z);
                    batch_inverse_inplace::<_, A>(&mut denoms);
                    let denoms = P::vec_from_base_vec(denoms);

                    // buffers to compute c0 and c1 coefficients before placing them into destination
                    let mut buffer_c0 = Vec::with_capacity_in(end - start, A::default());
                    buffer_c0.resize(end - start, P::zero(&mut ctx));

                    let mut buffer_c1 = Vec::with_capacity_in(end - start, A::default());
                    buffer_c1.resize(end - start, P::zero(&mut ctx));

                    for ((src_poly, value_at_z), challenge_coefficients) in polynomial_ldes_ref
                        .iter()
                        .zip(values_at_z_ref.iter())
                        .zip(challenge_coefficients_ref.iter())
                    {
                        let src_coset = &src_poly.storage[coset_idx];
                        let src_chunk = &src_coset.storage[start..end];

                        let (challenge_c0, challenge_c1) = challenge_coefficients;
                        let challenge_c0 = P::constant(*challenge_c0, &mut ctx);
                        let challenge_c1 = P::constant(*challenge_c1, &mut ctx);
                        debug_assert_eq!(src_chunk.len(), buffer_c0.len());
                        let value_at_z = P::constant(*value_at_z, &mut ctx);

                        for ((src, dst_c0), dst_c1) in src_chunk
                            .iter()
                            .zip(buffer_c0.iter_mut())
                            .zip(buffer_c1.iter_mut())
                        {
                            // src is in the base field, so in fact we do two independent operations
                            let mut tmp = *src;
                            tmp.sub_assign(&value_at_z, &mut ctx);

                            let mut c0 = tmp;
                            c0.mul_assign(&challenge_c0, &mut ctx);

                            let mut c1 = tmp;
                            c1.mul_assign(&challenge_c1, &mut ctx);

                            dst_c0.add_assign(&c0, &mut ctx);
                            dst_c1.add_assign(&c1, &mut ctx);
                        }
                    }

                    // numerators were aggregated, now "divide" once
                    for ((dst_c0, dst_c1), denom) in buffer_c0
                        .iter_mut()
                        .zip(buffer_c1.iter_mut())
                        .zip(denoms.into_iter())
                    {
                        dst_c0.mul_assign(&denom, &mut ctx);
                        dst_c1.mul_assign(&denom, &mut ctx);
                    }

                    for (((dst_c0, dst_c1), src_c0), src_c1) in c0
                        .iter_mut()
                        .zip(c1.iter_mut())
                        .zip(buffer_c0.into_iter())
                        .zip(buffer_c1.into_iter())
                    {
                        dst_c0.add_assign(&src_c0, &mut ctx);
                        dst_c1.add_assign(&src_c1, &mut ctx);
                    }
                })
            }
        });
    }
}

fn quotening_operation_in_extension<
    F: SmallField,
    EXT: FieldExtension<2, BaseField = F>,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    destination_c0: &mut Vec<Vec<P, A>, B>,
    destination_c1: &mut Vec<Vec<P, A>, B>,
    polynomial_ldes: Vec<[Option<ArcGenericLdeStorage<F, P, A, B>>; 2]>,
    values_at_z: Vec<ExtensionField<F, 2, EXT>>,
    precomputed_cosets: &ArcGenericLdeStorage<F, P, A, B>,
    at: ExtensionField<F, 2, EXT>,
    challenge_coefficients: &[(F, F)],
    worker: &Worker,
    ctx: &mut P::Context,
) {
    // we precompute challenges outside to avoid any manual extension ops here

    assert_eq!(destination_c0.len(), destination_c1.len());
    assert_eq!(destination_c0.len(), precomputed_cosets.outer_len());
    assert_eq!(polynomial_ldes.len(), values_at_z.len());
    assert_eq!(polynomial_ldes.len(), challenge_coefficients.len());
    assert_eq!(destination_c0[0].len(), precomputed_cosets.inner_len());
    let polynomial_ldes_ref = &polynomial_ldes;
    let values_at_z_ref = &values_at_z;
    let challenge_coefficients_ref = challenge_coefficients;

    // we will work over every coset independently for simplicity
    for (coset_idx, (c0, c1)) in destination_c0
        .iter_mut()
        .zip(destination_c1.iter_mut())
        .enumerate()
    {
        debug_assert_eq!(c0.len(), c1.len());
        let work_size = c0.len();
        worker.scope(work_size, |scope, chunk_size| {
            for (chunk_idx, (c0, c1)) in c0
                .chunks_mut(chunk_size)
                .zip(c1.chunks_mut(chunk_size))
                .enumerate()
            {
                let mut ctx = *ctx;
                scope.spawn(move |_| {
                    let start = chunk_idx * chunk_size;
                    let mut end = start + chunk_size;
                    if end > work_size {
                        end = work_size;
                    }
                    // denominator is shared between everything, and we can compute it once here
                    let roots = &precomputed_cosets.storage[coset_idx].storage[start..end];
                    let at_c0 = P::constant(at.coeffs[0], &mut ctx);
                    let at_c1 = P::constant(at.coeffs[1], &mut ctx);
                    let mut roots_minus_z_c0 = roots.to_vec_in(A::default());
                    let mut at_c1_negated = at_c1;
                    at_c1_negated.negate(&mut ctx);
                    let mut at_c1_negated_vec =
                        Vec::with_capacity_in(roots_minus_z_c0.len(), A::default());
                    at_c1_negated_vec.resize(roots_minus_z_c0.len(), at_c1_negated);

                    // denominator for (x - z), but roots are in base, so only one subtraction is needed
                    for el in roots_minus_z_c0.iter_mut() {
                        el.sub_assign(&at_c0, &mut ctx);
                    }

                    let mut denoms_c0 = P::vec_into_base_vec(roots_minus_z_c0);
                    let mut denoms_c1 = P::vec_into_base_vec(at_c1_negated_vec);
                    batch_inverse_inplace_in_extension::<F, EXT, A>(&mut denoms_c0, &mut denoms_c1);
                    let denoms_c0 = P::vec_from_base_vec(denoms_c0);
                    let denoms_c1 = P::vec_from_base_vec(denoms_c1);

                    let zero = P::zero(&mut ctx);

                    // buffers to compute c0 and c1 coefficients before placing them into destination
                    let mut buffer_c0 = Vec::with_capacity_in(end - start, A::default());
                    buffer_c0.resize(end - start, zero);

                    let mut buffer_c1 = Vec::with_capacity_in(end - start, A::default());
                    buffer_c1.resize(end - start, zero);

                    for (([src_poly_c0, src_poly_c1], value_at_z), challenge_coefficients) in
                        polynomial_ldes_ref
                            .iter()
                            .zip(values_at_z_ref.iter())
                            .zip(challenge_coefficients_ref.iter())
                    {
                        let src_coset_c0 = &src_poly_c0
                            .as_ref()
                            .expect("c0 must never be empty")
                            .storage[coset_idx];
                        let src_coset_c1 = src_poly_c1.as_ref().map(|el| &el.storage[coset_idx]);
                        let src_chunk_c0 = &src_coset_c0.storage[start..end];
                        let src_chunk_c1 = src_coset_c1.map(|el| &el.storage[start..end]);

                        let (challenge_c0, challenge_c1) = challenge_coefficients;
                        let challenge_c0 = P::constant(*challenge_c0, &mut ctx);
                        let challenge_c1 = P::constant(*challenge_c1, &mut ctx);
                        debug_assert_eq!(src_chunk_c0.len(), buffer_c0.len());
                        let value_at_z_c0 = P::constant(value_at_z.coeffs[0], &mut ctx);
                        let value_at_z_c1 = P::constant(value_at_z.coeffs[1], &mut ctx);
                        let mut value_at_z_c1_negated = value_at_z_c1;
                        value_at_z_c1_negated.negate(&mut ctx);

                        // we branch based on what we have

                        if let Some(src_chunk_c1) = src_chunk_c1 {
                            debug_assert_eq!(src_chunk_c1.len(), buffer_c1.len());

                            for (((src_c0, src_c1), dst_c0), dst_c1) in src_chunk_c0
                                .iter()
                                .zip(src_chunk_c1.iter())
                                .zip(buffer_c0.iter_mut())
                                .zip(buffer_c1.iter_mut())
                            {
                                // src is in the base field, so in fact we do two independent operations
                                let mut tmp_c0 = *src_c0;
                                tmp_c0.sub_assign(&value_at_z_c0, &mut ctx);

                                let mut tmp_c1 = *src_c1;
                                tmp_c1.sub_assign(&value_at_z_c1, &mut ctx);

                                mul_assign_vectorized_in_extension::<F, P, EXT>(
                                    &mut tmp_c0,
                                    &mut tmp_c1,
                                    &challenge_c0,
                                    &challenge_c1,
                                    &mut ctx,
                                );

                                dst_c0.add_assign(&tmp_c0, &mut ctx);
                                dst_c1.add_assign(&tmp_c1, &mut ctx);
                            }
                        } else {
                            for ((src, dst_c0), dst_c1) in src_chunk_c0
                                .iter()
                                .zip(buffer_c0.iter_mut())
                                .zip(buffer_c1.iter_mut())
                            {
                                // src is in the base field, so in fact we do two independent operations
                                let mut tmp_c0 = *src;
                                tmp_c0.sub_assign(&value_at_z_c0, &mut ctx);

                                let mut tmp_c1 = value_at_z_c1_negated;

                                mul_assign_vectorized_in_extension::<F, P, EXT>(
                                    &mut tmp_c0,
                                    &mut tmp_c1,
                                    &challenge_c0,
                                    &challenge_c1,
                                    &mut ctx,
                                );

                                dst_c0.add_assign(&tmp_c0, &mut ctx);
                                dst_c1.add_assign(&tmp_c1, &mut ctx);
                            }
                        }
                    }

                    // numerators were aggregated, now "divide" once
                    for (((dst_c0, dst_c1), denom_c0), denom_c1) in buffer_c0
                        .iter_mut()
                        .zip(buffer_c1.iter_mut())
                        .zip(denoms_c0.into_iter())
                        .zip(denoms_c1.into_iter())
                    {
                        mul_assign_vectorized_in_extension::<F, P, EXT>(
                            dst_c0, dst_c1, &denom_c0, &denom_c1, &mut ctx,
                        );
                    }

                    for (((dst_c0, dst_c1), src_c0), src_c1) in c0
                        .iter_mut()
                        .zip(c1.iter_mut())
                        .zip(buffer_c0.into_iter())
                        .zip(buffer_c1.into_iter())
                    {
                        dst_c0.add_assign(&src_c0, &mut ctx);
                        dst_c1.add_assign(&src_c1, &mut ctx);
                    }
                })
            }
        });
    }
}

fn flatten_presumably_bitreversed<T: Copy + Send + Sync, U, A: GoodAllocator, B: GoodAllocator>(
    input: Vec<Vec<T, A>, B>,
    worker: &Worker,
) -> Vec<T, A> {
    let mut input = input;
    let outer_size = input.len();
    let inner_size = input[0].len();
    let result_size = outer_size * inner_size;

    bitreverse_enumeration_inplace(&mut input); // bitreverse cosets to normal ordering

    // bitreverse inside every coset, so we can easier interleave
    worker.scope(outer_size, |scope, chunk_size| {
        for dst in input.chunks_mut(chunk_size) {
            scope.spawn(move |_| {
                for dst in dst.iter_mut() {
                    bitreverse_enumeration_inplace(dst);
                }
            })
        }
    });

    let mut flattened = allocate_in_with_alignment_of::<T, U, A>(result_size, A::default());

    // now it's actually interleaving
    let input_ref = &input;
    worker.scope(inner_size, |scope, chunk_size| {
        for (chunk_idx, dst) in flattened.spare_capacity_mut()[..result_size]
            .chunks_mut(chunk_size * outer_size)
            .enumerate()
        {
            scope.spawn(move |_| {
                let start = chunk_size * chunk_idx;
                let mut end = start + chunk_size;
                if end > inner_size {
                    end = inner_size;
                }

                debug_assert_eq!(dst.len(), (end - start) * outer_size);
                let buffers: Vec<_> = input_ref.iter().map(|el| &el[start..end]).collect();
                let mut it = dst.iter_mut();
                assert!(it.len() == (end - start) * outer_size);

                for i in 0..(end - start) {
                    for el in buffers.iter() {
                        it.next().unwrap().write(el[i]);
                    }
                }
            });
        }
    });

    unsafe { flattened.set_len(result_size) };

    flattened
}

use crate::cs::implementations::polynomial::lde::ArcGenericLdeStorage;
use crate::cs::implementations::polynomial::GenericPolynomial;
use crate::fft::bitreverse_enumeration_inplace;
use crate::field::Field;

use crate::field::ExtensionField;
use crate::field::FieldExtension;

// our path is a set of booleans true/false, and encode from the root,
// so when we even encounter a path, we can check for all it's ascendants
pub fn compute_selector_subpath<
    F: SmallField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
>(
    path: Vec<bool>,
    buffer: &mut HashMap<Vec<bool>, ArcGenericLdeStorage<F, P>>,
    degree: usize,
    setup: &SetupStorage<F, P>,
    worker: &Worker,
    ctx: &mut P::Context,
) {
    debug_assert!(degree.is_power_of_two());
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
        let poly = &setup.constant_columns[constant_poly_idx];
        if path[0] == false {
            // we have to compute (1 - poly)

            // we need to create a NEW poly that will be our result to not overwrite setup
            let subset = poly.owned_subset_for_degree(degree);
            let chunks = subset.compute_chunks_for_num_workers(worker.num_cores);
            worker.scope(0, |scope, _| {
                for chunk in chunks.into_iter() {
                    let mut dst = subset.clone();
                    let mut ctx = *ctx;
                    scope.spawn(move |_| {
                        let mut chunk = chunk;
                        let one = P::one(&mut ctx);
                        let num_iterations = chunk.num_iterations();
                        for _ in 0..num_iterations {
                            let (outer, inner) = chunk.current();
                            let mut tmp = one;
                            tmp.sub_assign(&dst.storage[outer].storage[inner], &mut ctx);
                            unsafe {
                                Arc::get_mut_unchecked(&mut dst.storage[outer]).storage[inner] = tmp
                            };
                            chunk.advance();
                        }
                    })
                }
            });

            let existing = buffer.insert(path, subset);
            debug_assert!(existing.is_none());
        } else {
            // we can use just an existing poly
            let subset = poly.subset_for_degree(degree);
            let existing = buffer.insert(path, subset);
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
        compute_selector_subpath(parent_prefix.clone(), buffer, degree, setup, worker, ctx);
    }

    // now we evaluated all prefixes and can add one here on top
    let prefix_poly = buffer.get(&parent_prefix).expect("must be computed");
    let other_poly = &setup.constant_columns[constant_poly_idx];

    // we know that prefix is of proper subset, so we need only subset of other

    // we need to create a NEW poly that will be our result to not overwrite setup
    let subset = other_poly.owned_subset_for_degree(degree);
    let chunks = subset.compute_chunks_for_num_workers(worker.num_cores);

    worker.scope(0, |scope, _| {
        for chunk in chunks.into_iter() {
            let mut dst = subset.clone();
            let mut ctx = *ctx;
            scope.spawn(move |_| {
                let mut chunk = chunk;
                let one = P::one(&mut ctx);
                let num_iterations = chunk.num_iterations();
                for _ in 0..num_iterations {
                    let (outer, inner) = chunk.current();
                    if final_element == false {
                        // we need prefix * (1 - this)
                        let mut result = one;
                        result.sub_assign(&dst.storage[outer].storage[inner], &mut ctx);
                        result.mul_assign(&prefix_poly.storage[outer].storage[inner], &mut ctx);
                        unsafe {
                            Arc::get_mut_unchecked(&mut dst.storage[outer]).storage[inner] = result
                        };
                    } else {
                        // we need prefix * this
                        let mut result = dst.storage[outer].storage[inner];
                        result.mul_assign(&prefix_poly.storage[outer].storage[inner], &mut ctx);
                        unsafe {
                            Arc::get_mut_unchecked(&mut dst.storage[outer]).storage[inner] = result
                        };
                    }

                    chunk.advance();
                }
            })
        }
    });

    if crate::config::DEBUG_SATISFIABLE == true {
        let mut at_least_one_used = false;
        for (idx, el) in subset.storage[0].storage.iter().enumerate() {
            let selector = [*el];
            let selector = P::slice_into_base_slice(&selector);
            for (j, el) in selector.iter().copied().enumerate() {
                let idx = idx * P::SIZE_FACTOR + j;
                if el != F::ZERO && el != F::ONE {
                    panic!(
                        "Lookup selector is non-binary at index {} with value {:?}",
                        idx, el
                    );
                }
                if el == F::ONE {
                    at_least_one_used = true;
                }
            }
        }

        assert!(at_least_one_used, "at least one selector must be non-zero");
    }

    let existing = buffer.insert(path, subset);
    debug_assert!(existing.is_none());
}
