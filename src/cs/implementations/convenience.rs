//! Contains convenience functions that collate all the proving/verifying algorithms together
//! under a single function umbrella.
use std::alloc::Global;

use super::polynomial_storage::{SetupBaseStorage, SetupStorage};
use super::proof::Proof;
use super::verifier::VerificationKey;
use super::witness::WitnessVec;
use crate::cs::cs_builder_verifier::CsVerifierBuilder;
use crate::cs::oracle::merkle_tree::MerkleTreeWithCap;
use crate::cs::traits::GoodAllocator;

use super::transcript::Transcript;
use crate::cs::traits::circuit::Circuit;

use super::*;

use super::pow::*;

use crate::config::*;
use crate::cs::implementations::hints::*;
use crate::cs::implementations::prover::ProofConfig;
use crate::cs::implementations::reference_cs::*;
use crate::cs::oracle::TreeHasher;
use crate::field::FieldExtension;

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        CFG: CSConfig,
        A: GoodAllocator,
    > CSReferenceAssembly<F, P, CFG, A>
{
    pub fn prove_one_shot<
        EXT: FieldExtension<2, BaseField = F>,
        TR: Transcript<F>,
        H: TreeHasher<F, Output = TR::CompatibleCap>,
        POW: PoWRunner,
    >(
        mut self,
        worker: &Worker,
        proof_config: ProofConfig,
        transcript_params: TR::TransciptParameters,
    ) -> (Proof<F, H, EXT>, VerificationKey<F, H>) {
        assert!(
            CFG::SetupConfig::KEEP_SETUP,
            "CS is not configured to keep setup to know variables placement"
        );

        assert!(
            CFG::WitnessConfig::EVALUATE_WITNESS,
            "CS is not configured to have witness available"
        );

        assert!(proof_config.fri_lde_factor.is_power_of_two());

        let mut ctx = P::Context::placeholder();

        let setup_base = self.create_base_setup(worker, &mut ctx);
        let (setup, vk, setup_tree) = self.materialize_setup_storage_and_vk::<H>(
            proof_config.fri_lde_factor,
            proof_config.merkle_tree_cap_size,
            worker,
            &mut ctx,
        );
        let witness_set = self.take_witness(worker);

        let proof = self.prove_cpu_basic::<EXT, TR, H, POW>(
            worker,
            witness_set,
            &setup_base,
            &setup,
            &setup_tree,
            &vk,
            proof_config,
            transcript_params,
        );

        (proof, vk)
    }

    pub fn prepare_base_setup_with_precomputations_and_vk<
        TR: Transcript<F>,
        H: TreeHasher<F, Output = TR::CompatibleCap>,
    >(
        self,
        proof_config: ProofConfig,
        worker: &Worker,
    ) -> (
        SetupBaseStorage<F, P>,
        SetupStorage<F, P>,
        MerkleTreeWithCap<F, H, Global, Global>,
        DenseVariablesCopyHint,
        DenseWitnessCopyHint,
        VerificationKey<F, H>,
    ) {
        assert!(
            CFG::SetupConfig::KEEP_SETUP,
            "CS is not configured to keep setup to know variables placement"
        );

        assert!(proof_config.fri_lde_factor.is_power_of_two());

        let mut ctx = P::Context::placeholder();

        let (vars_hint, wits_hint) = self.create_copy_hints();

        let setup_base = self.create_base_setup(worker, &mut ctx);
        let (setup, vk, setup_tree) = self.materialize_setup_storage_and_vk::<H>(
            proof_config.fri_lde_factor,
            proof_config.merkle_tree_cap_size,
            worker,
            &mut ctx,
        );

        (setup_base, setup, setup_tree, vars_hint, wits_hint, vk)
    }

    pub fn prove_from_precomputations<
        EXT: FieldExtension<2, BaseField = F>,
        TR: Transcript<F>,
        H: TreeHasher<F, Output = TR::CompatibleCap>,
        POW: PoWRunner,
    >(
        mut self,
        proof_config: ProofConfig,
        setup_base: &SetupBaseStorage<F, P>,
        setup: &SetupStorage<F, P>,
        setup_tree: &MerkleTreeWithCap<F, H, Global, Global>,
        vk: &VerificationKey<F, H>,
        vars_hint: &DenseVariablesCopyHint,
        wits_hint: &DenseWitnessCopyHint,
        transcript_params: TR::TransciptParameters,
        worker: &Worker,
    ) -> Proof<F, H, EXT> {
        assert!(
            CFG::WitnessConfig::EVALUATE_WITNESS,
            "CS is not configured to have witness available"
        );

        assert!(proof_config.fri_lde_factor.is_power_of_two());

        let witness_set = self.take_witness_using_hints(worker, vars_hint, wits_hint);

        let proof = self.prove_cpu_basic::<EXT, TR, H, POW>(
            worker,
            witness_set,
            setup_base,
            setup,
            setup_tree,
            vk,
            proof_config,
            transcript_params,
        );

        proof
    }

    /// Intended to be used mainly with assembly produced by `into_assembly_for_repeated_proving`
    pub fn prove_from_witness_vec_and_precomputations<
        EXT: FieldExtension<2, BaseField = F>,
        TR: Transcript<F>,
        H: TreeHasher<F, Output = TR::CompatibleCap>,
        POW: PoWRunner,
    >(
        &self,
        witness_vector: &WitnessVec<F, A>,
        proof_config: ProofConfig,
        setup_base: &SetupBaseStorage<F, P>,
        setup: &SetupStorage<F, P>,
        setup_tree: &MerkleTreeWithCap<F, H, Global, Global>,
        vk: &VerificationKey<F, H>,
        vars_hint: &DenseVariablesCopyHint,
        wits_hint: &DenseWitnessCopyHint,
        transcript_params: TR::TransciptParameters,
        worker: &Worker,
    ) -> Proof<F, H, EXT> {
        assert!(proof_config.fri_lde_factor.is_power_of_two());

        let witness_set =
            self.witness_set_from_witness_vec(witness_vector, vars_hint, wits_hint, worker);

        let proof = self.prove_cpu_basic::<EXT, TR, H, POW>(
            worker,
            witness_set,
            setup_base,
            setup,
            setup_tree,
            vk,
            proof_config,
            transcript_params,
        );

        proof
    }
}

pub fn verify_circuit<
    F: SmallField,
    C: Circuit<F>,
    EXT: FieldExtension<2, BaseField = F>,
    TR: Transcript<F>,
    H: TreeHasher<F, Output = TR::CompatibleCap>,
    POW: PoWRunner,
>(
    circuit: &C,
    proof: &Proof<F, H, EXT>,
    vk: &VerificationKey<F, H>,
    transcript_params: TR::TransciptParameters,
) -> bool {
    let builder_impl =
        CsVerifierBuilder::<F, EXT>::new_from_parameters(vk.fixed_parameters.parameters);
    use crate::cs::cs_builder::new_builder;

    let builder = new_builder::<_, F>(builder_impl);
    let builder = circuit.configure_builder(builder);

    let verifier = builder.build(());
    verifier.verify::<H, TR, POW>(transcript_params, vk, proof)
}
