use crate::cs::{
    oracle::{merkle_tree::MerkleTreeWithCap, TreeHasher},
    traits::GoodAllocator,
};

use super::{fri::QuerySource, prover::ProofConfig, *};

#[derive(derivative::Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone(bound = ""), Debug(bound = ""), Hash(bound = ""))]
#[serde(bound = "H::Output: serde::Serialize + serde::de::DeserializeOwned")]
pub struct SingleRoundQueries<F: SmallField, H: TreeHasher<F>> {
    // we need query for witness, setup, stage 2 and quotient
    pub witness_query: OracleQuery<F, H>,
    pub stage_2_query: OracleQuery<F, H>,
    pub quotient_query: OracleQuery<F, H>,
    pub setup_query: OracleQuery<F, H>,

    pub fri_queries: Vec<OracleQuery<F, H>>,
}

impl<F: SmallField, H: TreeHasher<F>> SingleRoundQueries<F, H> {
    #[inline]
    pub fn transmute_to_another_formal_hasher<HH: TreeHasher<F, Output = H::Output>>(
        self,
    ) -> SingleRoundQueries<F, HH> {
        let Self {
            witness_query,
            stage_2_query,
            quotient_query,
            setup_query,
            fri_queries,
        } = self;

        SingleRoundQueries::<F, HH> {
            witness_query: witness_query.transmute_to_another_formal_hasher(),
            stage_2_query: stage_2_query.transmute_to_another_formal_hasher(),
            quotient_query: quotient_query.transmute_to_another_formal_hasher(),
            setup_query: setup_query.transmute_to_another_formal_hasher(),

            fri_queries: fri_queries
                .into_iter()
                .map(|el| el.transmute_to_another_formal_hasher())
                .collect(),
        }
    }
}

#[derive(derivative::Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    Hash(bound = ""),
    PartialEq(bound = ""),
    Eq(bound = "")
)]
#[serde(bound = "")]
pub struct OracleQuery<F: SmallField, H: TreeHasher<F>> {
    pub leaf_elements: Vec<F>,
    #[serde(bound(serialize = "H::Output: serde::Serialize"))]
    #[serde(bound(deserialize = "H::Output: serde::de::DeserializeOwned"))]
    pub proof: Vec<H::Output>,
}

impl<F: SmallField, H: TreeHasher<F>> OracleQuery<F, H> {
    pub fn construct<S: QuerySource<F>, A: GoodAllocator, B: GoodAllocator>(
        tree: &MerkleTreeWithCap<F, H, A, B>,
        source: &S,
        lde_factor: usize,
        coset_idx: usize,
        domain_size: usize,
        inner_idx: usize,
        num_elements: usize,
    ) -> Self {
        let mut new = Self {
            leaf_elements: vec![],
            proof: vec![],
        };

        source.get_elements(
            lde_factor,
            coset_idx,
            domain_size,
            inner_idx,
            num_elements,
            &mut new.leaf_elements,
        );
        assert!(domain_size.is_power_of_two());
        assert!(num_elements.is_power_of_two());
        let (inner_idx, _) = crate::cs::implementations::fri::split_inner(inner_idx, num_elements);
        let shift = domain_size.trailing_zeros() - num_elements.trailing_zeros();
        let tree_idx = (coset_idx << shift) + inner_idx;
        let (_leaf_hash, proof) = tree.get_proof(tree_idx);

        new.proof = proof;

        new
    }

    #[inline]
    pub fn transmute_to_another_formal_hasher<HH: TreeHasher<F, Output = H::Output>>(
        self,
    ) -> OracleQuery<F, HH> {
        let Self {
            leaf_elements,
            proof,
        } = self;

        OracleQuery::<F, HH> {
            leaf_elements,
            proof: proof as Vec<HH::Output>,
        }
    }
}

use crate::field::ExtensionField;
use crate::field::FieldExtension;

#[derive(derivative::Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone(bound = ""), Debug(bound = ""), Hash(bound = ""))]
#[serde(bound = "H::Output: serde::Serialize + serde::de::DeserializeOwned")]
pub struct Proof<F: SmallField, H: TreeHasher<F>, EXT: FieldExtension<2, BaseField = F>> {
    pub proof_config: ProofConfig,

    pub public_inputs: Vec<F>,

    pub witness_oracle_cap: Vec<H::Output>,
    pub stage_2_oracle_cap: Vec<H::Output>,
    pub quotient_oracle_cap: Vec<H::Output>,
    pub final_fri_monomials: [Vec<F>; 2],

    pub values_at_z: Vec<ExtensionField<F, 2, EXT>>,
    pub values_at_z_omega: Vec<ExtensionField<F, 2, EXT>>,
    pub values_at_0: Vec<ExtensionField<F, 2, EXT>>,

    pub fri_base_oracle_cap: Vec<H::Output>,
    pub fri_intermediate_oracles_caps: Vec<Vec<H::Output>>,

    pub queries_per_fri_repetition: Vec<SingleRoundQueries<F, H>>,

    pub pow_challenge: u64,

    pub _marker: std::marker::PhantomData<EXT>,
}

impl<F: SmallField, H: TreeHasher<F>, EXT: FieldExtension<2, BaseField = F>> Proof<F, H, EXT> {
    pub fn is_same_geometry(a: &Self, b: &Self) -> bool {
        if a.proof_config != b.proof_config {
            return false;
        }

        if a.public_inputs.len() != b.public_inputs.len() {
            return false;
        }

        if a.witness_oracle_cap.len() != b.witness_oracle_cap.len() {
            return false;
        }
        if a.stage_2_oracle_cap.len() != b.stage_2_oracle_cap.len() {
            return false;
        }
        if a.quotient_oracle_cap.len() != b.quotient_oracle_cap.len() {
            return false;
        }

        if a.final_fri_monomials.len() != b.final_fri_monomials.len() {
            return false;
        }
        if a.values_at_z.len() != b.values_at_z.len() {
            return false;
        }
        if a.values_at_z_omega.len() != b.values_at_z_omega.len() {
            return false;
        }
        if a.values_at_0.len() != b.values_at_0.len() {
            return false;
        }

        if a.fri_base_oracle_cap.len() != b.fri_base_oracle_cap.len() {
            return false;
        }
        if a.fri_intermediate_oracles_caps.len() != b.fri_intermediate_oracles_caps.len() {
            return false;
        }

        for (a, b) in a
            .fri_intermediate_oracles_caps
            .iter()
            .zip(b.fri_intermediate_oracles_caps.iter())
        {
            if a.len() != b.len() {
                return false;
            }
        }

        if a.queries_per_fri_repetition.len() != b.queries_per_fri_repetition.len() {
            return false;
        }

        true
    }

    pub fn transmute_to_another_formal_hasher<HH: TreeHasher<F, Output = H::Output>>(
        self,
    ) -> Proof<F, HH, EXT> {
        let Proof {
            proof_config,
            public_inputs,
            witness_oracle_cap,
            stage_2_oracle_cap,
            quotient_oracle_cap,
            final_fri_monomials,
            values_at_z,
            values_at_z_omega,
            values_at_0,
            fri_base_oracle_cap,
            fri_intermediate_oracles_caps,
            queries_per_fri_repetition,
            pow_challenge,
            ..
        } = self;

        Proof {
            proof_config,
            public_inputs,
            witness_oracle_cap: witness_oracle_cap as Vec<HH::Output>,
            stage_2_oracle_cap: stage_2_oracle_cap as Vec<HH::Output>,
            quotient_oracle_cap: quotient_oracle_cap as Vec<HH::Output>,
            final_fri_monomials,
            values_at_z,
            values_at_z_omega,
            values_at_0,
            fri_base_oracle_cap: fri_base_oracle_cap as Vec<HH::Output>,
            fri_intermediate_oracles_caps: fri_intermediate_oracles_caps as Vec<Vec<HH::Output>>,
            queries_per_fri_repetition: queries_per_fri_repetition
                .into_iter()
                .map(|el| el.transmute_to_another_formal_hasher())
                .collect(),
            pow_challenge,
            _marker: std::marker::PhantomData,
        }
    }
}
