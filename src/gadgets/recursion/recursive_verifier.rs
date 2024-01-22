use crate::log;
use std::{any::TypeId, collections::HashMap};

use crate::cs::traits::gate::GatePlacementStrategy;
use crate::{
    cs::{
        implementations::{prover::ProofConfig, verifier::VerificationKeyCircuitGeometry},
        traits::{cs::ConstraintSystem, evaluator::PerChunkOffset},
    },
    field::{FieldExtension, SmallField},
    gadgets::{boolean::Boolean, traits::selectable::Selectable},
};

use crate::cs::{
    gates::lookup_marker::LookupFormalGate,
    LookupParameters,
    {oracle::TreeHasher, CSGeometry, GateConfigurationHolder, StaticToolboxHolder},
};

use crate::cs::gates::lookup_marker::LookupGateMarkerFormalEvaluator;
use crate::cs::implementations::transcript::Transcript;
use crate::cs::implementations::verifier::SizeCalculator;
use crate::field::traits::field_like::PrimeFieldLike;
use crate::gadgets::num::prime_field_like::*;
use crate::gadgets::num::Num;
use crate::gadgets::recursion::allocated_proof::AllocatedProof;
use crate::gadgets::recursion::allocated_vk::AllocatedVerificationKey;
use crate::gadgets::recursion::recursive_transcript::*;
use crate::gadgets::recursion::recursive_tree_hasher::*;
use crate::gadgets::recursion::recursive_verifier_builder::TypeErasedGateEvaluationRecursiveVerificationFunction;
use std::alloc::Global;

use crate::gadgets::recursion::circuit_pow::RecursivePoWRunner;

fn materialize_powers_serial<
    F: SmallField,
    EXT: FieldExtension<2, BaseField = F>,
    CS: ConstraintSystem<F> + 'static,
>(
    cs: &mut CS,
    base: NumExtAsFieldWrapper<F, EXT, CS>,
    size: usize,
) -> Vec<NumExtAsFieldWrapper<F, EXT, CS>> {
    if size == 0 {
        return Vec::new();
    }
    let mut storage = Vec::with_capacity(size);
    let mut current = NumExtAsFieldWrapper::<F, EXT, CS>::one(cs);
    storage.push(current);
    for idx in 1..size {
        if idx == 1 {
            current = base;
        } else {
            current.mul_assign(&base, cs);
        }
        storage.push(current);
    }

    storage
}

pub struct RecursiveVerifierProxy<
    F: SmallField,
    EXT: FieldExtension<2, BaseField = F>,
    CS: ConstraintSystem<F> + 'static,
    GC: GateConfigurationHolder<F>,
    T: StaticToolboxHolder,
> {
    // when we init we get the following from VK
    pub parameters: CSGeometry,
    pub lookup_parameters: LookupParameters,

    pub gates_configuration: GC,
    pub(crate) gate_type_ids_for_specialized_columns: Vec<TypeId>,
    pub(crate) evaluators_over_specialized_columns:
        Vec<TypeErasedGateEvaluationRecursiveVerificationFunction<F, EXT, CS>>,
    pub(crate) offsets_for_specialized_evaluators: Vec<(PerChunkOffset, PerChunkOffset, usize)>,

    pub(crate) evaluators_over_general_purpose_columns:
        Vec<TypeErasedGateEvaluationRecursiveVerificationFunction<F, EXT, CS>>,

    pub(crate) total_num_variables_for_specialized_columns: usize,
    pub(crate) total_num_witnesses_for_specialized_columns: usize,
    pub(crate) total_num_constants_for_specialized_columns: usize,

    pub(crate) _marker: std::marker::PhantomData<T>,
}

impl<
        F: SmallField,
        EXT: FieldExtension<2, BaseField = F>,
        CS: ConstraintSystem<F> + 'static,
        GC: GateConfigurationHolder<F>,
        T: StaticToolboxHolder,
    > RecursiveVerifierProxy<F, EXT, CS, GC, T>
{
    pub fn into_verifier(self) -> RecursiveVerifier<F, EXT, CS> {
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

        RecursiveVerifier::<F, EXT, CS> {
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

pub struct RecursiveVerifier<
    F: SmallField,
    EXT: FieldExtension<2, BaseField = F>,
    CS: ConstraintSystem<F> + 'static,
> {
    // when we init we get the following from VK
    pub parameters: CSGeometry,
    pub lookup_parameters: LookupParameters,

    pub(crate) gate_type_ids_for_specialized_columns: Vec<TypeId>,
    pub(crate) evaluators_over_specialized_columns:
        Vec<TypeErasedGateEvaluationRecursiveVerificationFunction<F, EXT, CS>>,
    pub(crate) offsets_for_specialized_evaluators: Vec<(PerChunkOffset, PerChunkOffset, usize)>,

    pub(crate) evaluators_over_general_purpose_columns:
        Vec<TypeErasedGateEvaluationRecursiveVerificationFunction<F, EXT, CS>>,

    pub(crate) total_num_variables_for_specialized_columns: usize,
    pub(crate) total_num_witnesses_for_specialized_columns: usize,
    pub(crate) total_num_constants_for_specialized_columns: usize,

    pub(crate) placement_strategies: HashMap<TypeId, GatePlacementStrategy>,
}

impl<F: SmallField, EXT: FieldExtension<2, BaseField = F>, CS: ConstraintSystem<F> + 'static>
    RecursiveVerifier<F, EXT, CS>
{
    #[inline]
    fn num_sublookup_arguments(&self) -> usize {
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

    pub fn fri_folding_schedule(
        &self,
        fixed_parameters: &VerificationKeyCircuitGeometry,
        proof_config: &ProofConfig,
    ) -> Vec<usize> {
        let (
            _new_pow_bits,                // updated POW bits if needed
            _num_queries,                 // num queries
            interpolation_log2s_schedule, // folding schedule
            _final_expected_degree,
        ) = crate::cs::implementations::prover::compute_fri_schedule(
            proof_config.security_level as u32,
            proof_config.merkle_tree_cap_size,
            proof_config.pow_bits,
            fixed_parameters.fri_lde_factor.trailing_zeros(),
            fixed_parameters.domain_size.trailing_zeros(),
        );

        interpolation_log2s_schedule
    }

    pub fn final_expected_degree(
        &self,
        fixed_parameters: &VerificationKeyCircuitGeometry,
        proof_config: &ProofConfig,
    ) -> usize {
        let (
            _new_pow_bits,                // updated POW bits if needed
            _num_queries,                 // num queries
            interpolation_log2s_schedule, // folding schedule
            final_expected_degree,
        ) = crate::cs::implementations::prover::compute_fri_schedule(
            proof_config.security_level as u32,
            proof_config.merkle_tree_cap_size,
            proof_config.pow_bits,
            fixed_parameters.fri_lde_factor.trailing_zeros(),
            fixed_parameters.domain_size.trailing_zeros(),
        );

        let mut expected_degree = fixed_parameters.domain_size;

        for interpolation_degree_log2 in interpolation_log2s_schedule.into_iter() {
            expected_degree >>= interpolation_degree_log2;
        }

        assert_eq!(final_expected_degree, expected_degree as usize);

        expected_degree as usize
    }

    pub fn num_fri_repetitions(
        &self,
        fixed_parameters: &VerificationKeyCircuitGeometry,
        proof_config: &ProofConfig,
    ) -> usize {
        let (
            _new_pow_bits,                 // updated POW bits if needed
            num_queries,                   // num queries
            _interpolation_log2s_schedule, // folding schedule
            _final_expected_degree,
        ) = crate::cs::implementations::prover::compute_fri_schedule(
            proof_config.security_level as u32,
            proof_config.merkle_tree_cap_size,
            proof_config.pow_bits,
            fixed_parameters.fri_lde_factor.trailing_zeros(),
            fixed_parameters.domain_size.trailing_zeros(),
        );

        num_queries
    }

    pub fn num_poly_values_at_z(&self, fixed_parameters: &VerificationKeyCircuitGeometry) -> usize {
        let num_lookup_subarguments = self.num_sublookup_arguments();
        let num_multiplicities_polys = self.num_multipicities_polys(
            fixed_parameters.total_tables_len as usize,
            fixed_parameters.domain_size,
        );

        let expected_lookup_polys_total = if fixed_parameters.lookup_parameters.lookup_is_allowed()
        {
            num_lookup_subarguments + // lookup witness encoding polys
            num_multiplicities_polys * 2 + // multiplicity and multiplicity encoding
            fixed_parameters.lookup_parameters.lookup_width() + // encode tables itself
            1 // encode table IDs
        } else {
            0
        };

        let num_variable_polys = self.num_variable_polys();
        let num_witness_polys = self.num_witness_polys();
        let num_constant_polys = self.num_constant_polys(fixed_parameters);
        let num_copy_permutation_polys = num_variable_polys;

        let quotient_degree = self.quotient_degree(fixed_parameters);

        use crate::cs::implementations::copy_permutation::num_intermediate_partial_product_relations;
        let num_intermediate_partial_product_relations =
            num_intermediate_partial_product_relations(num_copy_permutation_polys, quotient_degree);

        let num_poly_values_at_z = num_variable_polys + num_witness_polys +
            num_constant_polys + num_copy_permutation_polys +
            1 + // z_poly
            num_intermediate_partial_product_relations + // partial products in copy-permutation
            expected_lookup_polys_total + // everything from lookup
            quotient_degree; // chunks of quotient poly

        num_poly_values_at_z
    }

    pub fn num_poly_values_at_z_omega(&self) -> usize {
        1
    }

    pub fn num_poly_values_at_zero(
        &self,
        fixed_parameters: &VerificationKeyCircuitGeometry,
    ) -> usize {
        let num_lookup_subarguments = self.num_sublookup_arguments();
        let num_multiplicities_polys = self.num_multipicities_polys(
            fixed_parameters.total_tables_len as usize,
            fixed_parameters.domain_size,
        );
        let total_num_lookup_argument_terms = num_lookup_subarguments + num_multiplicities_polys;

        total_num_lookup_argument_terms
    }

    pub fn verify<
        H: RecursiveTreeHasher<F, Num<F>>, // Doesn't work, and this is strange by, because RecursiveTreeHasher<F, Num<F>> is TreeHasher<Num<F>::Witness> == TreeHasher<F>
        // H: RecursiveTreeHasher<F, Num<F>> + TreeHasher<F>,
        TR: RecursiveTranscript<
            F,
            CompatibleCap = <H::NonCircuitSimulator as TreeHasher<F>>::Output,
            CircuitReflection = CTR,
        >,
        CTR: CircuitTranscript<
            F,
            CircuitCompatibleCap = <H as CircuitTreeHasher<F, Num<F>>>::CircuitOutput,
            TransciptParameters = TR::TransciptParameters,
        >,
        POW: RecursivePoWRunner<F>,
    >(
        &self,
        cs: &mut CS,
        transcript_params: <TR as Transcript<F>>::TransciptParameters,
        proof: &AllocatedProof<F, H, EXT>,
        fixed_parameters: &VerificationKeyCircuitGeometry,
        proof_config: &ProofConfig,
        vk: &AllocatedVerificationKey<F, H>,
    ) -> (Boolean<F>, Vec<Num<F>>) {
        assert_eq!(self.parameters, fixed_parameters.parameters);
        assert_eq!(self.lookup_parameters, fixed_parameters.lookup_parameters);
        assert!(proof_config.fri_folding_schedule.is_none());
        assert_eq!(fixed_parameters.cap_size, proof_config.merkle_tree_cap_size);
        assert_eq!(fixed_parameters.fri_lde_factor, proof_config.fri_lde_factor,);
        assert_eq!(fixed_parameters.cap_size, vk.setup_merkle_tree_cap.len());

        let mut validity_flags = Vec::with_capacity(256);

        let zero_num = Num::<F>::zero(cs);

        let zero_base = NumAsFieldWrapper::<F, CS>::zero(cs);

        let zero_ext = NumExtAsFieldWrapper::<F, EXT, CS>::zero(cs);
        let one_ext = NumExtAsFieldWrapper::<F, EXT, CS>::one(cs);

        let multiplicative_generator =
            NumAsFieldWrapper::constant(F::multiplicative_generator(), cs);

        // allocate everything
        let mut transcript = CTR::new(cs, transcript_params);
        let setup_tree_cap = &vk.setup_merkle_tree_cap;
        assert_eq!(fixed_parameters.cap_size, setup_tree_cap.len());
        <TR::CircuitReflection as CircuitTranscript<F>>::witness_merkle_tree_cap(
            &mut transcript,
            cs,
            setup_tree_cap,
        );

        if proof.public_inputs.len() != fixed_parameters.public_inputs_locations.len() {
            panic!("Invalid number of public inputs");
        }

        let num_public_inputs = proof.public_inputs.len();
        let mut public_inputs_with_values = Vec::with_capacity(num_public_inputs);
        let mut public_input_allocated = Vec::with_capacity(num_public_inputs);

        // commit public inputs
        for ((column, row), value) in fixed_parameters
            .public_inputs_locations
            .iter()
            .copied()
            .zip(proof.public_inputs.iter().copied())
        {
            transcript.witness_field_elements(cs, &[value]);
            public_input_allocated.push(value);
            let value = value.into();
            public_inputs_with_values.push((column, row, value));
        }

        // commit witness
        assert_eq!(fixed_parameters.cap_size, proof.witness_oracle_cap.len());
        transcript.witness_merkle_tree_cap(cs, &proof.witness_oracle_cap);

        // draw challenges for stage 2

        let beta = transcript.get_multiple_challenges_fixed::<_, 2>(cs);
        let beta = NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base(beta);

        let gamma = transcript.get_multiple_challenges_fixed::<_, 2>(cs);
        let gamma = NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base(gamma);

        let (lookup_beta, lookup_gamma) = if self.lookup_parameters != LookupParameters::NoLookup {
            // lookup argument related parts
            let lookup_beta = transcript.get_multiple_challenges_fixed::<_, 2>(cs);
            let lookup_beta =
                NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base(lookup_beta);
            let lookup_gamma = transcript.get_multiple_challenges_fixed::<_, 2>(cs);
            let lookup_gamma =
                NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base(lookup_gamma);

            (lookup_beta, lookup_gamma)
        } else {
            (zero_ext, zero_ext)
        };

        assert_eq!(fixed_parameters.cap_size, proof.stage_2_oracle_cap.len());
        transcript.witness_merkle_tree_cap(cs, &proof.stage_2_oracle_cap);

        // draw challenges for quotient
        let alpha = transcript.get_multiple_challenges_fixed::<_, 2>(cs);
        let alpha = NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base(alpha);

        // two extra relations per lookup subargument - for A and B polys
        let num_lookup_subarguments = self.num_sublookup_arguments();
        let num_multiplicities_polys = self.num_multipicities_polys(
            fixed_parameters.total_tables_len as usize,
            fixed_parameters.domain_size,
        );
        let total_num_lookup_argument_terms = num_lookup_subarguments + num_multiplicities_polys;

        let num_variable_polys = self.num_variable_polys();
        let num_witness_polys = self.num_witness_polys();
        let num_constant_polys = self.num_constant_polys(fixed_parameters);
        let quotient_degree = self.quotient_degree(fixed_parameters);
        let num_copy_permutation_polys = num_variable_polys;

        use crate::cs::implementations::copy_permutation::num_intermediate_partial_product_relations;
        let num_intermediate_partial_product_relations =
            num_intermediate_partial_product_relations(num_copy_permutation_polys, quotient_degree);

        assert_eq!(
            self.evaluators_over_specialized_columns.len(),
            self.gate_type_ids_for_specialized_columns.len()
        );

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

        let powers: Vec<_> = materialize_powers_serial(cs, alpha, total_num_terms);
        let rest = &powers[..];
        let (take, rest) = rest.split_at(total_num_lookup_argument_terms);
        let pregenerated_challenges_for_lookup = take.to_vec();
        let (take, rest) = rest.split_at(total_num_gate_terms_for_specialized_columns);
        let pregenerated_challenges_for_gates_over_specialized_columns = take.to_vec();
        let (take, rest) = rest.split_at(total_num_gate_terms_for_general_purpose_columns);
        let pregenerated_challenges_for_gates_over_general_purpose_columns = take.to_vec();
        let remaining_challenges = rest.to_vec();

        // commit quotient
        assert_eq!(fixed_parameters.cap_size, proof.quotient_oracle_cap.len());
        transcript.witness_merkle_tree_cap(cs, &proof.quotient_oracle_cap);

        // get z
        let z = transcript.get_multiple_challenges_fixed::<_, 2>(cs);
        let z = NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base(z);

        let all_values_at_z: Vec<_> = proof
            .values_at_z
            .iter()
            .map(|el| NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base(*el))
            .collect();
        let all_values_at_z_omega: Vec<_> = proof
            .values_at_z_omega
            .iter()
            .map(|el| NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base(*el))
            .collect();
        let all_values_at_0: Vec<_> = proof
            .values_at_0
            .iter()
            .map(|el| NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base(*el))
            .collect();

        // commit claimed values at z, and form our poly storage
        for set in proof.values_at_z.iter() {
            transcript.witness_field_elements(cs, set);
        }

        for set in proof.values_at_z_omega.iter() {
            transcript.witness_field_elements(cs, set);
        }

        for set in proof.values_at_0.iter() {
            transcript.witness_field_elements(cs, set);
        }

        use crate::cs::implementations::utils::domain_generator_for_size;
        // and public inputs should also go into quotient
        let mut public_input_opening_tuples: Vec<(F, Vec<(usize, NumAsFieldWrapper<F, CS>)>)> =
            vec![];
        {
            let omega = domain_generator_for_size::<F>(fixed_parameters.domain_size);

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

        let num_poly_values_at_z = self.num_poly_values_at_z(fixed_parameters);
        let num_poly_values_at_z_omega = self.num_poly_values_at_z_omega();
        let num_poly_values_at_zero = self.num_poly_values_at_zero(fixed_parameters);

        assert_eq!(proof.values_at_z.len(), num_poly_values_at_z);
        assert_eq!(proof.values_at_z_omega.len(), num_poly_values_at_z_omega);
        assert_eq!(proof.values_at_0.len(), num_poly_values_at_zero);

        // run verifier at z
        {
            use crate::cs::implementations::copy_permutation::non_residues_for_copy_permutation;
            use crate::cs::implementations::verifier::*;

            let non_residues_for_copy_permutation = non_residues_for_copy_permutation::<F, Global>(
                fixed_parameters.domain_size as usize,
                num_variable_polys,
            );

            let non_residues_for_copy_permutation: Vec<_> = non_residues_for_copy_permutation
                .into_iter()
                .map(|el| NumAsFieldWrapper::constant(el, cs))
                .collect();

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

            let mut t_accumulator = NumExtAsFieldWrapper::<F, EXT, CS>::zero(cs);
            // precompute selectors at z

            let mut selectors_buffer = HashMap::new();
            for (gate_idx, evaluator) in self
                .evaluators_over_general_purpose_columns
                .iter()
                .enumerate()
            {
                if let Some(path) = fixed_parameters
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
                        cs,
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

                let mut witness_subsum = NumExtAsFieldWrapper::<F, EXT, CS>::zero(cs);
                for a in lookup_witness_encoding_polys_polys_at_0.iter() {
                    witness_subsum.add_assign(a, cs);
                }

                let mut multiplicities_subsum = NumExtAsFieldWrapper::<F, EXT, CS>::zero(cs);
                for b in multiplicities_encoding_polys_at_0.iter() {
                    multiplicities_subsum.add_assign(b, cs);
                }

                let witness_subsum = witness_subsum.into_num_coeffs_in_base();
                let multiplicities_subsum = multiplicities_subsum.into_num_coeffs_in_base();

                let c0_is_valid = Num::equals(cs, &witness_subsum[0], &multiplicities_subsum[0]);
                let c1_is_valid = Num::equals(cs, &witness_subsum[1], &multiplicities_subsum[1]);

                validity_flags.push(c0_is_valid);
                validity_flags.push(c1_is_valid);

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
                        let selector_subpath = fixed_parameters
                            .selectors_placement
                            .output_placement(lookup_evaluator_id)
                            .expect("lookup gate must be placed");
                        let selector = selectors_buffer
                            .remove(&selector_subpath)
                            .expect("path must be unique and precomputed");

                        let column_elements_per_subargument =
                            self.lookup_parameters.columns_per_subargument() as usize;
                        assert!(
                            fixed_parameters.table_ids_column_idxes.len() == 0
                                || fixed_parameters.table_ids_column_idxes.len() == 1
                        );

                        // this is our lookup width, either counted by number of witness columns only, or if one includes setup
                        let num_lookup_columns = column_elements_per_subargument
                            + ((fixed_parameters.table_ids_column_idxes.len() == 1) as usize);
                        assert_eq!(lookup_tables_columns.len(), num_lookup_columns);

                        let capacity = column_elements_per_subargument
                            + ((fixed_parameters.table_ids_column_idxes.len() == 1) as usize);
                        let mut powers_of_gamma = Vec::with_capacity(capacity);
                        let mut tmp = NumExtAsFieldWrapper::<F, EXT, CS>::one(cs);
                        powers_of_gamma.push(tmp);
                        for _idx in 1..capacity {
                            if _idx == 1 {
                                tmp = lookup_gamma;
                            } else {
                                tmp.mul_assign(&lookup_gamma, cs);
                            }

                            powers_of_gamma.push(tmp);
                        }

                        // precompute aggregation of lookup table polys
                        assert_eq!(powers_of_gamma.len(), capacity);
                        let mut lookup_table_columns_aggregated = lookup_beta;
                        for (gamma, column) in
                            powers_of_gamma.iter().zip(lookup_tables_columns.iter())
                        {
                            NumExtAsFieldWrapper::<F, EXT, CS>::mul_and_accumulate_into(
                                &mut lookup_table_columns_aggregated,
                                gamma,
                                column,
                                cs,
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
                                fixed_parameters.table_ids_column_idxes.first().copied()
                            {
                                vec![constant_poly_values[table_id_poly]]
                            } else {
                                vec![]
                            };

                            for (gamma, column) in powers_of_gamma
                                .iter()
                                .zip(witness_columns.iter().chain(table_id.iter()))
                            {
                                NumExtAsFieldWrapper::<F, EXT, CS>::mul_and_accumulate_into(
                                    &mut contribution,
                                    gamma,
                                    column,
                                    cs,
                                );
                            }

                            // mul by A(x)
                            contribution.mul_assign(a_poly, cs);
                            // sub selector
                            contribution.sub_assign(&selector, cs);

                            // mul by power of challenge and accumulate
                            NumExtAsFieldWrapper::<F, EXT, CS>::mul_and_accumulate_into(
                                &mut t_accumulator,
                                &alpha,
                                &contribution,
                                cs,
                            );

                            // contribution.mul_assign(&alpha, cs);
                            // t_accumulator.add_assign(&contribution, cs);
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
                            contribution.mul_assign(b_poly, cs);
                            // sub multiplicity
                            contribution.sub_assign(multiplicities_poly, cs);

                            // mul by power of challenge and accumulate
                            NumExtAsFieldWrapper::<F, EXT, CS>::mul_and_accumulate_into(
                                &mut t_accumulator,
                                &alpha,
                                &contribution,
                                cs,
                            );

                            // contribution.mul_assign(&alpha, cs);
                            // t_accumulator.add_assign(&contribution, cs);
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
                            fixed_parameters.table_ids_column_idxes.len() == 0
                                || fixed_parameters.table_ids_column_idxes.len() == 1
                        );

                        // this is our lookup width, either counted by number of witness columns only, or if one includes setup
                        let num_lookup_columns = column_elements_per_subargument
                            + ((fixed_parameters.table_ids_column_idxes.len() == 1) as usize);
                        assert_eq!(lookup_tables_columns.len(), num_lookup_columns);

                        let capacity = column_elements_per_subargument
                            + ((fixed_parameters.table_ids_column_idxes.len() == 1) as usize);
                        let mut powers_of_gamma = Vec::with_capacity(capacity);
                        let mut tmp = NumExtAsFieldWrapper::<F, EXT, CS>::one(cs);
                        powers_of_gamma.push(tmp);
                        for _idx in 1..capacity {
                            if _idx == 1 {
                                tmp = lookup_gamma;
                            } else {
                                tmp.mul_assign(&lookup_gamma, cs);
                            }

                            powers_of_gamma.push(tmp);
                        }

                        // precompute aggregation of lookup table polys
                        assert_eq!(powers_of_gamma.len(), capacity);
                        let mut lookup_table_columns_aggregated = lookup_beta;
                        for (gamma, column) in
                            powers_of_gamma.iter().zip(lookup_tables_columns.iter())
                        {
                            NumExtAsFieldWrapper::<F, EXT, CS>::mul_and_accumulate_into(
                                &mut lookup_table_columns_aggregated,
                                gamma,
                                column,
                                cs,
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
                                fixed_parameters.table_ids_column_idxes.first().copied()
                            {
                                vec![constant_poly_values[table_id_poly]]
                            } else {
                                vec![]
                            };

                            for (gamma, column) in powers_of_gamma
                                .iter()
                                .zip(witness_columns.iter().chain(table_id.iter()))
                            {
                                NumExtAsFieldWrapper::<F, EXT, CS>::mul_and_accumulate_into(
                                    &mut contribution,
                                    gamma,
                                    column,
                                    cs,
                                );
                            }

                            // mul by A(x)
                            contribution.mul_assign(a_poly, cs);
                            // sub numerator
                            contribution.sub_assign(&one_ext, cs);

                            // mul by power of challenge and accumulate
                            NumExtAsFieldWrapper::<F, EXT, CS>::mul_and_accumulate_into(
                                &mut t_accumulator,
                                &alpha,
                                &contribution,
                                cs,
                            );

                            // contribution.mul_assign(&alpha, cs);
                            // t_accumulator.add_assign(&contribution, cs);
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
                            contribution.mul_assign(b_poly, cs);
                            // sub multiplicity
                            contribution.sub_assign(multiplicities_poly, cs);

                            // mul by power of challenge and accumulate
                            NumExtAsFieldWrapper::<F, EXT, CS>::mul_and_accumulate_into(
                                &mut t_accumulator,
                                &alpha,
                                &contribution,
                                cs,
                            );

                            // contribution.mul_assign(&alpha, cs);
                            // t_accumulator.add_assign(&contribution, cs);
                        }
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }

            let constants_for_gates_over_general_purpose_columns = fixed_parameters
                .extra_constant_polys_for_selectors
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
                    // log!(
                    //     "Will be evaluating {} over specialized columns",
                    //     &evaluator.debug_name
                    // );

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
                        accumulator: zero_ext,
                        selector_value: one_ext,
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

                    evaluation_fn.evaluate_over_columns(&mut src, &mut dst, cs);

                    t_accumulator.add_assign(&dst.accumulator, cs);

                    challenges_offset += total_terms;
                }

                assert_eq!(
                    challenges_offset,
                    total_num_gate_terms_for_specialized_columns
                );
            }

            // log!("Evaluating general purpose gates");

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

                    if let Some(path) = fixed_parameters
                        .selectors_placement
                        .output_placement(gate_idx)
                    {
                        let selector = selectors_buffer
                            .remove(&path)
                            .expect("path must be unique and precomputed");
                        let constant_placement_offset = path.len();

                        let mut dst = VerifierRelationDestination {
                            accumulator: zero_ext,
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
                            cs,
                        );

                        t_accumulator.add_assign(&dst.accumulator, cs);
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

            let z_in_domain_size = z.pow_u64(fixed_parameters.domain_size, cs);

            let mut vanishing_at_z = z_in_domain_size;
            vanishing_at_z.sub_assign(&one_ext, cs);

            let mut challenges_it = remaining_challenges.iter();

            {
                // (x^n - 1) / (x - 1),
                let mut z_minus_one = z;
                z_minus_one.sub_assign(&one_ext, cs);

                let mut unnormalized_l1_inverse_at_z = vanishing_at_z;
                let z_minus_one_inversed = z_minus_one.inverse(cs);
                unnormalized_l1_inverse_at_z.mul_assign(&z_minus_one_inversed, cs);

                let alpha = *challenges_it.next().expect("challenge for z(1) == 1");
                // (z(x) - 1) * l(1)
                let mut contribution = copy_permutation_z_at_z;
                contribution.sub_assign(&one_ext, cs);
                contribution.mul_assign(&unnormalized_l1_inverse_at_z, cs);

                // mul by power of challenge and accumulate
                NumExtAsFieldWrapper::<F, EXT, CS>::mul_and_accumulate_into(
                    &mut t_accumulator,
                    &alpha,
                    &contribution,
                    cs,
                );

                // contribution.mul_assign(&alpha, cs);
                // t_accumulator.add_assign(&contribution, cs);
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
                    subres.mul_assign(&beta, cs);
                    subres.add_assign(variable, cs);
                    subres.add_assign(&gamma, cs);
                    lhs.mul_assign(&subres, cs);
                }

                let mut rhs = *rhs;
                let x_poly_value = z;
                for (non_res, variable) in non_residues.iter().zip(variables.iter()) {
                    // numerator is w + beta * non_res * x + gamma
                    let mut subres = x_poly_value;
                    subres.mul_assign_by_base(non_res, cs);
                    subres.mul_assign(&beta, cs);
                    subres.add_assign(variable, cs);
                    subres.add_assign(&gamma, cs);
                    rhs.mul_assign(&subres, cs);
                }

                let mut contribution = lhs;
                contribution.sub_assign(&rhs, cs);

                // mul by power of challenge and accumulate
                NumExtAsFieldWrapper::<F, EXT, CS>::mul_and_accumulate_into(
                    &mut t_accumulator,
                    alpha,
                    &contribution,
                    cs,
                );

                // contribution.mul_assign(&alpha, cs);
                // t_accumulator.add_assign(&contribution, cs);
            }

            assert_eq!(challenges_it.len(), 0, "must exhaust all the challenges");

            let mut t_from_chunks = zero_ext;
            let mut pow = one_ext;
            for el in quotient_chunks.into_iter() {
                NumExtAsFieldWrapper::<F, EXT, CS>::mul_and_accumulate_into(
                    &mut t_from_chunks,
                    &el,
                    &pow,
                    cs,
                );

                // let mut tmp = el;
                // tmp.mul_assign(&pow, cs);
                // t_from_chunks.add_assign(&tmp, cs);

                pow.mul_assign(&z_in_domain_size, cs);
            }

            t_from_chunks.mul_assign(&vanishing_at_z, cs);

            let t_accumulator = t_accumulator.into_num_coeffs_in_base();
            let t_from_chunks = t_from_chunks.into_num_coeffs_in_base();

            let c0_is_valid = Num::equals(cs, &t_accumulator[0], &t_from_chunks[0]);
            let c1_is_valid = Num::equals(cs, &t_accumulator[1], &t_from_chunks[1]);

            validity_flags.push(c0_is_valid);
            validity_flags.push(c1_is_valid);
        }

        // get challenges
        let c0 = transcript.get_challenge(cs);
        let c1 = transcript.get_challenge(cs);

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

        let mut total_num_challenges = 0;
        total_num_challenges += num_poly_values_at_z;
        total_num_challenges += 1;
        total_num_challenges += total_num_lookup_argument_terms;
        for (_, subset) in public_input_opening_tuples.iter() {
            total_num_challenges += subset.len();
        }

        assert_eq!(all_values_at_z.len(), num_poly_values_at_z);
        assert_eq!(all_values_at_z_omega.len(), 1);
        assert_eq!(all_values_at_0.len(), total_num_lookup_argument_terms);

        let challenge = NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base([c0, c1]);
        let challenges_for_fri_quotiening =
            materialize_powers_serial::<F, EXT, CS>(cs, challenge, total_num_challenges);

        let (
            new_pow_bits,                 // updated POW bits if needed
            num_queries,                  // num queries
            interpolation_log2s_schedule, // folding schedule
            final_expected_degree,
        ) = crate::cs::implementations::prover::compute_fri_schedule(
            proof_config.security_level as u32,
            proof_config.merkle_tree_cap_size,
            proof_config.pow_bits,
            fixed_parameters.fri_lde_factor.trailing_zeros(),
            fixed_parameters.domain_size.trailing_zeros(),
        );

        let mut expected_degree = fixed_parameters.domain_size;

        assert_eq!(new_pow_bits, proof_config.pow_bits);

        let mut fri_intermediate_challenges = vec![];

        {
            // now witness base FRI oracle
            assert_eq!(fixed_parameters.cap_size, proof.fri_base_oracle_cap.len());
            transcript.witness_merkle_tree_cap(cs, &proof.fri_base_oracle_cap);

            let reduction_degree_log_2 = interpolation_log2s_schedule[0];

            let c0 = transcript.get_challenge(cs);
            let c1 = transcript.get_challenge(cs);

            let mut challenge_powers = Vec::with_capacity(reduction_degree_log_2);
            let as_extension =
                NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base([c0, c1]);
            challenge_powers.push(as_extension);

            let mut current = as_extension;

            for _ in 1..reduction_degree_log_2 {
                current.square(cs);
                challenge_powers.push(current);
            }
            expected_degree >>= reduction_degree_log_2;

            fri_intermediate_challenges.push(challenge_powers);
        }

        assert_eq!(
            interpolation_log2s_schedule[1..].len(),
            proof.fri_intermediate_oracles_caps.len()
        );

        for (interpolation_degree_log2, cap) in interpolation_log2s_schedule[1..]
            .iter()
            .zip(proof.fri_intermediate_oracles_caps.iter())
        {
            // commit new oracle
            assert_eq!(fixed_parameters.cap_size, cap.len());
            transcript.witness_merkle_tree_cap(cs, cap);

            // get challenge
            let reduction_degree_log_2 = *interpolation_degree_log2;
            let c0 = transcript.get_challenge(cs);
            let c1 = transcript.get_challenge(cs);

            let mut challenge_powers = Vec::with_capacity(reduction_degree_log_2);
            let as_extension =
                NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base([c0, c1]);
            challenge_powers.push(as_extension);

            let mut current = as_extension;

            for _ in 1..reduction_degree_log_2 {
                current.square(cs);
                challenge_powers.push(current);
            }

            fri_intermediate_challenges.push(challenge_powers);
            expected_degree >>= reduction_degree_log_2;
        }

        assert_eq!(final_expected_degree, expected_degree as usize);
        assert_eq!(
            proof.final_fri_monomials[0].len(),
            proof.final_fri_monomials[1].len()
        );
        assert_eq!(expected_degree as usize, proof.final_fri_monomials[0].len());
        assert_eq!(expected_degree as usize, proof.final_fri_monomials[1].len());
        assert!(proof.final_fri_monomials[0].len() > 0);

        // witness monomial coeffs
        transcript.witness_field_elements(cs, &proof.final_fri_monomials[0]);
        transcript.witness_field_elements(cs, &proof.final_fri_monomials[1]);

        if new_pow_bits != 0 {
            log!("Doing PoW verification for {} bits", new_pow_bits);
            // log!("Prover gave challenge 0x{:016x}", proof.pow_challenge);

            // pull enough challenges from the transcript
            let mut num_challenges = 256 / F::CHAR_BITS;
            if num_challenges % F::CHAR_BITS != 0 {
                num_challenges += 1;
            }
            let _challenges: Vec<_> = transcript.get_multiple_challenges(cs, num_challenges);

            todo!()
        }

        let max_needed_bits = (fixed_parameters.domain_size
            * fixed_parameters.fri_lde_factor as u64)
            .trailing_zeros() as usize;
        let mut bools_buffer = BoolsBuffer::<F> {
            available: vec![],
            max_needed: max_needed_bits,
        };

        let num_bits_for_in_coset_index =
            max_needed_bits - fixed_parameters.fri_lde_factor.trailing_zeros() as usize;
        let base_tree_index_shift = fixed_parameters.domain_size.trailing_zeros();
        assert_eq!(num_bits_for_in_coset_index, base_tree_index_shift as usize);

        // precompute once, will be handy later
        let mut precomputed_powers = vec![];
        let mut precomputed_powers_inversed = vec![];
        for i in 0..=(fixed_parameters.domain_size * fixed_parameters.fri_lde_factor as u64)
            .trailing_zeros()
        {
            let omega = domain_generator_for_size::<F>(1u64 << i);
            precomputed_powers.push(omega);
            precomputed_powers_inversed.push(omega.inverse().unwrap());
        }

        let omega = precomputed_powers[fixed_parameters.domain_size.trailing_zeros() as usize];
        let omega_cs_constant = NumAsFieldWrapper::constant(omega, cs);

        // we also want to precompute "steps" for different interpolation degrees
        // e.g. if we interpolate 8 elements,
        // then those will be ordered as bitreverses of [0..=7], namely
        // [0, 4, 2, 6, 1, 5, 3, 7]

        // so we want to have exactly half of it, because separation by 4
        // is exactly -1, so we need [1, sqrt4(1), sqrt8(1), sqrt4(1)*sqrt8(1)]

        let mut interpolation_steps = vec![F::ONE; 4]; // max size

        for idx in [1, 3].into_iter() {
            interpolation_steps[idx].mul_assign(&precomputed_powers_inversed[2]);
        }
        for idx in [2, 3].into_iter() {
            interpolation_steps[idx].mul_assign(&precomputed_powers_inversed[3]);
        }

        assert_eq!(interpolation_steps[0], F::ONE);
        assert_eq!(interpolation_steps[1].pow_u64(4), F::ONE);
        assert_eq!(interpolation_steps[2].pow_u64(8), F::ONE);

        let precomputed_powers: Vec<_> = precomputed_powers
            .into_iter()
            .map(|el| NumAsFieldWrapper::constant(el, cs))
            .collect();
        let precomputed_powers_inversed: Vec<_> = precomputed_powers_inversed
            .into_iter()
            .map(|el| NumAsFieldWrapper::constant(el, cs))
            .collect();
        let interpolation_steps: Vec<_> = interpolation_steps
            .into_iter()
            .map(|el| NumAsFieldWrapper::constant(el, cs))
            .collect();

        assert_eq!(num_queries, proof.queries_per_fri_repetition.len());

        let base_oracle_depth = fixed_parameters.base_oracles_depth();

        let witness_leaf_size = self.witness_leaf_size(fixed_parameters);

        let stage_2_leaf_size = self.stage_2_leaf_size(fixed_parameters);
        let quotient_leaf_size = self.quotient_leaf_size(fixed_parameters);

        let setup_leaf_size = self.setup_leaf_size(fixed_parameters);

        for queries in proof.queries_per_fri_repetition.iter() {
            let query_index_lsb_first_bits =
                bools_buffer.get_bits(cs, &mut transcript, max_needed_bits);

            // we consider it to be some convenient for us encoding of coset + inner index.

            // Small note on indexing: when we commit to elements we use bitreversal enumeration everywhere.
            // So index `i` in the tree corresponds to the element of `omega^bitreverse(i)`.
            // This gives us natural separation of LDE cosets, such that subtrees form independent cosets,
            // and if cosets are in the form of `{1, gamma, ...} x {1, omega, ...} where gamma^lde_factor == omega,
            // then subtrees are enumerated by bitreverse powers of gamma

            // let inner_idx = &query_index_lsb_first_bits[0..num_bits_for_in_coset_index];
            // let coset_idx = &query_index_lsb_first_bits[num_bits_for_in_coset_index..];
            let base_tree_idx = query_index_lsb_first_bits.clone();

            // first verify basic inclusion proofs
            assert_eq!(witness_leaf_size, queries.witness_query.leaf_elements.len());
            let leaf_hash = <H as CircuitTreeHasher<F, Num<F>>>::hash_into_leaf(
                cs,
                &queries.witness_query.leaf_elements,
            );
            assert_eq!(base_oracle_depth, queries.witness_query.proof.len());
            let is_included = verify_proof_over_cap::<F, H, CS>(
                cs,
                &queries.witness_query.proof,
                &proof.witness_oracle_cap,
                &leaf_hash,
                &base_tree_idx,
            );
            validity_flags.push(is_included);

            assert_eq!(stage_2_leaf_size, queries.stage_2_query.leaf_elements.len());
            let leaf_hash = <H as CircuitTreeHasher<F, Num<F>>>::hash_into_leaf(
                cs,
                &queries.stage_2_query.leaf_elements,
            );
            assert_eq!(base_oracle_depth, queries.stage_2_query.proof.len());
            let is_included = verify_proof_over_cap::<F, H, CS>(
                cs,
                &queries.stage_2_query.proof,
                &proof.stage_2_oracle_cap,
                &leaf_hash,
                &base_tree_idx,
            );
            validity_flags.push(is_included);

            assert_eq!(
                quotient_leaf_size,
                queries.quotient_query.leaf_elements.len()
            );
            let leaf_hash = <H as CircuitTreeHasher<F, Num<F>>>::hash_into_leaf(
                cs,
                &queries.quotient_query.leaf_elements,
            );
            assert_eq!(base_oracle_depth, queries.quotient_query.proof.len());
            let is_included = verify_proof_over_cap::<F, H, CS>(
                cs,
                &queries.quotient_query.proof,
                &proof.quotient_oracle_cap,
                &leaf_hash,
                &base_tree_idx,
            );
            validity_flags.push(is_included);

            assert_eq!(setup_leaf_size, queries.setup_query.leaf_elements.len());
            let leaf_hash = <H as CircuitTreeHasher<F, Num<F>>>::hash_into_leaf(
                cs,
                &queries.setup_query.leaf_elements,
            );
            assert_eq!(base_oracle_depth, queries.setup_query.proof.len());
            let is_included = verify_proof_over_cap::<F, H, CS>(
                cs,
                &queries.setup_query.proof,
                &vk.setup_merkle_tree_cap,
                &leaf_hash,
                &base_tree_idx,
            );
            validity_flags.push(is_included);

            // now perform the quotiening operation
            let mut simulated_ext_element = zero_ext;

            assert_eq!(
                query_index_lsb_first_bits.len(),
                precomputed_powers.len() - 1
            );

            let domain_element =
                pow_from_precomputations(cs, &precomputed_powers[1..], &query_index_lsb_first_bits);

            // we will find it handy to have power of the generator with some bits masked to be zero
            let mut power_chunks = vec![];
            let mut skip_highest_powers = 0;
            // TODO: we may save here (in circuits case especially) if we compute recursively
            for interpolation_degree_log2 in interpolation_log2s_schedule.iter() {
                let domain_element = pow_from_precomputations(
                    cs,
                    &precomputed_powers_inversed[(1 + interpolation_degree_log2)..],
                    &query_index_lsb_first_bits
                        [(skip_highest_powers + interpolation_degree_log2)..],
                );

                skip_highest_powers += *interpolation_degree_log2;
                power_chunks.push(domain_element);
            }

            // don't forget that we are shifted
            let mut domain_element_for_quotiening = domain_element;
            domain_element_for_quotiening.mul_assign(&multiplicative_generator, cs);

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
                z_omega.mul_assign_by_base(&omega_cs_constant, cs);

                let cast_from_base = move |el: &[Num<F>]| {
                    el.iter()
                        .map(|el| {
                            NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base([
                                *el, zero_num,
                            ])
                        })
                        .collect::<Vec<_>>()
                };

                let cast_from_extension = move |el: &[Num<F>]| {
                    assert_eq!(el.len() % 2, 0);

                    el.array_chunks::<2>()
                        .map(|[c0, c1]| {
                            NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base([*c0, *c1])
                        })
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

                let values_at_z = &all_values_at_z;
                assert_eq!(sources.len(), values_at_z.len());
                // log!("Making quotiening at Z");
                quotening_operation(
                    cs,
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

                let values_at_z_omega = &all_values_at_z_omega;
                assert_eq!(sources.len(), values_at_z_omega.len());
                // log!("Making quotiening at Z*omega");
                quotening_operation(
                    cs,
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

                    let values_at_0 = &all_values_at_0;
                    assert_eq!(sources.len(), values_at_0.len());
                    // log!("Making quotiening at 0 for lookups sumchecks");
                    quotening_operation(
                        cs,
                        &mut simulated_ext_element,
                        &sources,
                        values_at_0,
                        domain_element_for_quotiening,
                        zero_ext,
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
                for (column, expected_value) in set {
                    let c0 = queries.witness_query.leaf_elements[*column];
                    let el =
                        NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base([c0, zero_num]);
                    sources.push(el);

                    let value = NumExtAsFieldWrapper::<F, EXT, CS>::from_coeffs_in_base([
                        *expected_value,
                        zero_base,
                    ]);
                    values.push(value);
                }
                let num_challenges_required = sources.len();
                assert_eq!(values.len(), num_challenges_required);

                // log!("Making quotiening at {} for public inputs", open_at);

                let open_at = NumAsFieldWrapper::constant(*open_at, cs);
                let open_at =
                    NumExtAsFieldWrapper::<F, EXT, CS>::from_coeffs_in_base([open_at, zero_base]);

                quotening_operation(
                    cs,
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

            let mut expected_fri_query_len = base_oracle_depth;

            for (idx, (interpolation_degree_log2, fri_query)) in interpolation_log2s_schedule
                .iter()
                .zip(queries.fri_queries.iter())
                .enumerate()
            {
                expected_fri_query_len -= *interpolation_degree_log2;
                let interpolation_degree = 1 << *interpolation_degree_log2;
                let subidx_in_leaf = &subidx[..*interpolation_degree_log2];
                let tree_idx = &subidx[*interpolation_degree_log2..];

                assert_eq!(fri_query.leaf_elements.len(), interpolation_degree * 2);

                let [c0, c1] = current_folded_value.into_num_coeffs_in_base();

                let c0_from_leaf = binary_select(
                    cs,
                    &fri_query.leaf_elements[..interpolation_degree],
                    subidx_in_leaf,
                );
                let c1_from_leaf = binary_select(
                    cs,
                    &fri_query.leaf_elements[interpolation_degree..],
                    subidx_in_leaf,
                );

                let c0_is_valid = Num::equals(cs, &c0, &c0_from_leaf);
                let c1_is_valid = Num::equals(cs, &c1, &c1_from_leaf);

                validity_flags.push(c0_is_valid);
                validity_flags.push(c1_is_valid);

                // verify query itself
                let cap = if idx == 0 {
                    &proof.fri_base_oracle_cap
                } else {
                    &proof.fri_intermediate_oracles_caps[idx - 1]
                };
                let leaf_hash = <H as CircuitTreeHasher<F, Num<F>>>::hash_into_leaf(
                    cs,
                    &fri_query.leaf_elements,
                );
                assert_eq!(fri_query.proof.len(), expected_fri_query_len);
                let is_included = verify_proof_over_cap::<F, H, CS>(
                    cs,
                    &fri_query.proof,
                    cap,
                    &leaf_hash,
                    tree_idx,
                );
                validity_flags.push(is_included);

                // interpolate
                let mut elements_to_interpolate = Vec::with_capacity(interpolation_degree);
                for (c0, c1) in fri_query.leaf_elements[..interpolation_degree]
                    .iter()
                    .zip(fri_query.leaf_elements[interpolation_degree..].iter())
                {
                    let as_ext =
                        NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base([*c0, *c1]);
                    elements_to_interpolate.push(as_ext);
                }

                let mut next = Vec::with_capacity(interpolation_degree / 2);
                let challenges = &fri_intermediate_challenges[idx];
                assert_eq!(challenges.len(), *interpolation_degree_log2);

                let mut base_pow = power_chunks[idx];

                for challenge in challenges.iter() {
                    for (i, [a, b]) in elements_to_interpolate.array_chunks::<2>().enumerate() {
                        let mut result = *a;
                        result.add_assign(b, cs);

                        let mut diff = *a;
                        diff.sub_assign(b, cs);
                        diff.mul_assign(challenge, cs);
                        // divide by corresponding power
                        let mut pow = base_pow;
                        pow.mul_assign(&interpolation_steps[i], cs);
                        let coset_inverse = NumAsFieldWrapper::constant(coset_inverse, cs);
                        pow.mul_assign(&coset_inverse, cs);

                        NumExtAsFieldWrapper::<F, EXT, CS>::mul_by_base_and_accumulate_into(
                            &mut result,
                            &pow,
                            &diff,
                            cs,
                        );

                        // diff.mul_assign_by_base(&pow, cs);
                        // result.add_assign(&diff, cs);

                        next.push(result);
                    }

                    std::mem::swap(&mut next, &mut elements_to_interpolate);
                    next.clear();
                    base_pow.square(cs);
                    coset_inverse.square();
                }

                for _ in 0..*interpolation_degree_log2 {
                    domain_element_for_interpolation.square(cs);
                }

                // recompute the index
                subidx = tree_idx.to_vec();
                current_folded_value = elements_to_interpolate[0];
            }

            // and we should evaluate monomial form and compare

            let mut result_from_monomial = zero_ext;
            // horner rule
            for (c0, c1) in proof.final_fri_monomials[0]
                .iter()
                .zip(proof.final_fri_monomials[1].iter())
                .rev()
            {
                let coeff = NumExtAsFieldWrapper::<F, EXT, CS>::from_num_coeffs_in_base([*c0, *c1]);

                // result_from_monomial = result_from_monomial * z + coeff

                let mut tmp = coeff;
                NumExtAsFieldWrapper::<F, EXT, CS>::mul_by_base_and_accumulate_into(
                    &mut tmp,
                    &domain_element_for_interpolation,
                    &result_from_monomial,
                    cs,
                );

                result_from_monomial = tmp;

                // result_from_monomial.mul_assign_by_base(&domain_element_for_interpolation, cs);
                // result_from_monomial.add_assign(&coeff, cs);
            }

            let result_from_monomial = result_from_monomial.into_num_coeffs_in_base();
            let current_folded_value = current_folded_value.into_num_coeffs_in_base();

            let c0_is_valid = Num::equals(cs, &result_from_monomial[0], &current_folded_value[0]);
            let c1_is_valid = Num::equals(cs, &result_from_monomial[1], &current_folded_value[1]);

            validity_flags.push(c0_is_valid);
            validity_flags.push(c1_is_valid);
        }

        let is_valid = Boolean::multi_and(cs, &validity_flags);

        (is_valid, public_input_allocated)
    }
}

fn quotening_operation<
    F: SmallField,
    EXT: FieldExtension<2, BaseField = F>,
    CS: ConstraintSystem<F> + 'static,
>(
    cs: &mut CS,
    dst: &mut NumExtAsFieldWrapper<F, EXT, CS>,
    polynomial_values: &Vec<NumExtAsFieldWrapper<F, EXT, CS>>,
    values_at: &Vec<NumExtAsFieldWrapper<F, EXT, CS>>,
    domain_element: NumAsFieldWrapper<F, CS>,
    at: NumExtAsFieldWrapper<F, EXT, CS>,
    challenges: &[NumExtAsFieldWrapper<F, EXT, CS>],
) {
    // we precompute challenges outside to avoid any manual extension ops here
    assert_eq!(polynomial_values.len(), values_at.len());
    assert_eq!(polynomial_values.len(), challenges.len());

    let zero_base = NumAsFieldWrapper::zero(cs);

    let mut denom =
        NumExtAsFieldWrapper::<F, EXT, CS>::from_coeffs_in_base([domain_element, zero_base]);
    denom.sub_assign(&at, cs);
    denom = denom.inverse(cs);

    let mut acc = NumExtAsFieldWrapper::<F, EXT, CS>::zero(cs);

    for ((poly_value, value_at), challenge) in polynomial_values
        .iter()
        .zip(values_at.iter())
        .zip(challenges.iter())
    {
        // (f(x) - f(z))/(x - z)
        let mut tmp = *poly_value;
        tmp.sub_assign(value_at, cs);

        NumExtAsFieldWrapper::<F, EXT, CS>::mul_and_accumulate_into(&mut acc, &tmp, challenge, cs);

        // let mut as_ext = *challenge;
        // as_ext.mul_assign(&tmp, cs);
        // acc.add_assign(&as_ext, cs);
    }

    NumExtAsFieldWrapper::<F, EXT, CS>::mul_and_accumulate_into(dst, &acc, &denom, cs);

    // acc.mul_assign(&denom, cs);
    // dst.add_assign(&acc, cs);
}

fn pow<F: SmallField, CS: ConstraintSystem<F> + 'static>(
    cs: &mut CS,
    base: &NumAsFieldWrapper<F, CS>,
    pow_bits_from_lsb: &[Boolean<F>],
) -> NumAsFieldWrapper<F, CS> {
    let mut result = NumAsFieldWrapper::<F, CS>::one(cs);
    assert!(pow_bits_from_lsb.len() > 0);

    let mut it = pow_bits_from_lsb.iter().rev();
    let b = *it.next().unwrap();
    result = NumAsFieldWrapper::conditionally_select(cs, b, base, &result);
    for b in it {
        result.double(cs);
        let mut tmp = result;
        tmp.mul_assign(base, cs);
        result = NumAsFieldWrapper::conditionally_select(cs, *b, &tmp, &result);
    }

    result
}

fn pow_from_precomputations<F: SmallField, CS: ConstraintSystem<F> + 'static>(
    cs: &mut CS,
    bases: &[NumAsFieldWrapper<F, CS>],
    bits: &[Boolean<F>],
) -> NumAsFieldWrapper<F, CS> {
    let mut result = NumAsFieldWrapper::<F, CS>::one(cs);

    for (base, bit) in bases.iter().zip(bits.iter()) {
        let mut tmp = result;
        tmp.mul_assign(base, cs);
        result = NumAsFieldWrapper::conditionally_select(cs, *bit, &tmp, &result);
    }

    result
}

pub fn verify_proof_over_cap<
    F: SmallField,
    H: RecursiveTreeHasher<F, Num<F>>,
    CS: ConstraintSystem<F>,
>(
    cs: &mut CS,
    proof: &[H::CircuitOutput],
    cap: &[H::CircuitOutput],
    leaf_hash: &H::CircuitOutput,
    path: &[Boolean<F>],
) -> Boolean<F> {
    assert!(path.len() >= proof.len());

    let mut current = *leaf_hash;
    let path_bits = &path[..proof.len()];
    let cap_bits = &path[proof.len()..];

    for (proof_el, path_bit) in proof.iter().zip(path_bits.iter()) {
        let (left, right) = H::swap_nodes(cs, *path_bit, &current, proof_el, 0);
        current = <H as CircuitTreeHasher<F, Num<F>>>::hash_into_node(cs, &left, &right, 0);
    }

    let selected_cap_el = H::select_cap_node(cs, cap_bits, cap);

    H::compare_output(cs, &current, &selected_cap_el)
}

pub(crate) fn binary_select<F: SmallField, T: Selectable<F>, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    elements: &[T],
    bits: &[Boolean<F>],
) -> T {
    assert_eq!(elements.len(), 1 << bits.len());
    assert!(bits.len() > 0);

    let mut input_space = Vec::with_capacity(elements.len() / 2);
    let mut dst_space = Vec::with_capacity(elements.len() / 2);

    for (idx, bit) in bits.iter().enumerate() {
        let src = if idx == 0 { elements } else { &input_space };

        debug_assert_eq!(elements.len() % 2, 0);
        dst_space.clear();

        for src in src.array_chunks::<2>() {
            let [a, b] = src;
            // NOTE order here
            let selected = T::conditionally_select(cs, *bit, b, a);
            dst_space.push(selected);
        }

        std::mem::swap(&mut dst_space, &mut input_space);
    }

    assert_eq!(input_space.len(), 1);

    input_space.pop().unwrap()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::algebraic_props::round_function::AbsorptionModeOverwrite;
    use crate::algebraic_props::sponge::GoldilocksPoseidon2Sponge;
    use crate::config::{CSConfig, DevCSConfig};
    use crate::cs::cs_builder::new_builder;
    use crate::cs::cs_builder_reference::CsReferenceImplementationBuilder;
    use crate::cs::cs_builder_verifier::CsVerifierBuilder;
    use crate::cs::gates::Poseidon2FlattenedGate;
    use crate::cs::gates::*;
    use crate::cs::implementations::pow::NoPow;
    use crate::cs::implementations::transcript::*;
    use crate::dag::CircuitResolverOpts;
    use crate::field::goldilocks::{GoldilocksExt2, GoldilocksField};
    use crate::gadgets::recursion::recursive_verifier_builder::CsRecursiveVerifierBuilder;
    use crate::gadgets::traits::witnessable::WitnessHookable;
    use crate::implementations::poseidon2::Poseidon2Goldilocks;

    #[test]
    fn test_recursive_verification() {
        type F = GoldilocksField;
        type P = GoldilocksField;
        type TR = GoldilocksPoisedon2Transcript;
        type R = Poseidon2Goldilocks;
        type Ctr = CircuitAlgebraicSpongeBasedTranscript<GoldilocksField, 8, 12, 4, R>;
        type Ext = GoldilocksExt2;
        type H = GoldilocksPoseidon2Sponge<AbsorptionModeOverwrite>;
        type RH = CircuitGoldilocksPoseidon2Sponge;
        // type P = MixedGL;
        type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 132,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 8,
        };
        let max_trace_len = 1 << 16;
        let num_vars = 1 << 22;

        let builder_impl = CsReferenceImplementationBuilder::<GoldilocksField, P, DevCSConfig>::new(
            geometry,
            max_trace_len,
        );
        let builder = new_builder::<_, GoldilocksField>(builder_impl);

        type Poseidon2Gate = Poseidon2FlattenedGate<GoldilocksField, 8, 12, 4, Poseidon2Goldilocks>;

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = BooleanConstraintGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = Poseidon2Gate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = SelectionGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ReductionGate::<F, 4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ZeroCheckGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
            false,
        );
        let builder = PublicInputGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut cs = builder.build(CircuitResolverOpts::new(num_vars));

        let mut vk_file = std::fs::File::open("vk.json").unwrap();
        let mut proof_file = std::fs::File::open("proof.json").unwrap();

        use crate::cs::implementations::proof::*;
        use crate::cs::implementations::verifier::VerificationKey;

        let vk: VerificationKey<F, H> = serde_json::from_reader(&mut vk_file).unwrap();
        let proof: Proof<F, H, Ext> = serde_json::from_reader(&mut proof_file).unwrap();

        let builder_impl =
            CsVerifierBuilder::<F, Ext>::new_from_parameters(vk.fixed_parameters.parameters);
        let builder = new_builder::<_, GoldilocksField>(builder_impl);
        // copy parameters from actual circuit
        let builder = builder.allow_lookup(
            LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                width: 3,
                num_repetitions: 8,
                share_table_id: true,
            },
        );

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = BooleanConstraintGate::configure_builder(
            builder,
            GatePlacementStrategy::UseSpecializedColumns {
                num_repetitions: 1,
                share_constants: false,
            },
        );
        let builder = U8x4FMAGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = Poseidon2Gate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = DotProductGate::<4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ZeroCheckGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
            false,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = UIntXAddGate::<32>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = UIntXAddGate::<16>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = UIntXAddGate::<8>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = SelectionGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ParallelSelectionGate::<4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = PublicInputGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ReductionGate::<_, 4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let verifier = builder.build(());

        let is_valid_proof = verifier.verify::<H, TR, NoPow>((), &vk, &proof);
        assert!(is_valid_proof);

        let builder_impl = CsRecursiveVerifierBuilder::<'_, F, Ext, _>::new_from_parameters(
            &mut cs,
            vk.fixed_parameters.parameters,
        );
        let builder = new_builder::<_, GoldilocksField>(builder_impl);
        // copy parameters from actual circuit
        let builder = builder.allow_lookup(
            LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                width: 3,
                num_repetitions: 8,
                share_table_id: true,
            },
        );

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = BooleanConstraintGate::configure_builder(
            builder,
            GatePlacementStrategy::UseSpecializedColumns {
                num_repetitions: 1,
                share_constants: false,
            },
        );
        let builder = U8x4FMAGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = Poseidon2Gate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = DotProductGate::<4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ZeroCheckGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
            false,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = UIntXAddGate::<32>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = UIntXAddGate::<16>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = UIntXAddGate::<8>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = SelectionGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ParallelSelectionGate::<4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = PublicInputGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ReductionGate::<_, 4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let verifier = builder.build(());

        use crate::gadgets::traits::allocatable::CSAllocatable;

        let allocated_vk = AllocatedVerificationKey::<F, RH>::allocate(&mut cs, vk.clone());
        let allocated_proof = AllocatedProof::<F, RH, Ext>::allocate_from_witness(
            &mut cs,
            Some(proof.clone()),
            &verifier,
            &vk.fixed_parameters,
            &proof.proof_config,
        );

        let (is_valid, public_inputs) = verifier.verify::<RH, TR, Ctr, NoPow>(
            &mut cs,
            (),
            &allocated_proof,
            &vk.fixed_parameters,
            &proof.proof_config,
            &allocated_vk,
        );

        assert!(is_valid.witness_hook(&cs)().unwrap());
        for el in public_inputs.into_iter() {
            dbg!(el.witness_hook(&cs)().unwrap());
        }

        dbg!(cs.next_available_row());
    }
}
