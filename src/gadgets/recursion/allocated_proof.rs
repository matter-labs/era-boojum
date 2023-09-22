use crate::cs::implementations::proof::OracleQuery;
use crate::cs::implementations::prover::ProofConfig;
use crate::cs::implementations::verifier::VerificationKeyCircuitGeometry;
use crate::cs::traits::cs::ConstraintSystem;
use crate::gadgets::boolean::Boolean;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::utils::LSBIterator;

use super::recursive_verifier::RecursiveVerifier;
use super::*;
use crate::cs::implementations::proof::Proof;
use crate::cs::implementations::proof::SingleRoundQueries;
use crate::field::FieldExtension;
use crate::gadgets::num::Num;
use crate::gadgets::recursion::recursive_tree_hasher::RecursiveTreeHasher;
use crate::gadgets::traits::allocatable::allocate_num_elements;

#[derive(derivative::Derivative)]
#[derivative(Clone(bound = ""))]
pub struct AllocatedOracleQuery<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>> {
    pub leaf_elements: Vec<Num<F>>,
    pub proof: Vec<H::CircuitOutput>,
}

impl<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>> AllocatedOracleQuery<F, H> {
    pub fn allocate_from_witness<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        witness: Option<OracleQuery<F, H::NonCircuitSimulator>>,
        leaf_size: usize,
        proof_depth: usize,
    ) -> Self {
        let num_elements = leaf_size;
        let leaf_elements = witness.as_ref().map(|el| el.leaf_elements.iter().copied());
        let leaf_elements = allocate_num_elements::<F, CS, Num<F>>(cs, num_elements, leaf_elements);

        let num_elements = proof_depth;
        let proof = witness.as_ref().map(|el| el.proof.iter().cloned());
        let proof = allocate_num_elements::<F, CS, H::CircuitOutput>(cs, num_elements, proof);

        Self {
            leaf_elements,
            proof,
        }
    }
}

// impl<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>> CSAllocatable<F>
//     for AllocatedOracleQuery<F, H>
// {
//     type Witness = OracleQuery<F, H::NonCircuitSimulator>;

//     fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
//         let OracleQuery {
//             leaf_elements,
//             proof,
//         } = witness;

//         let leaf_elements = leaf_elements
//             .into_iter()
//             .map(|el| Num::allocate(cs, el))
//             .collect();

//         let proof = proof
//             .into_iter()
//             .map(|el| H::CircuitOutput::allocate(cs, el))
//             .collect();

//         Self {
//             leaf_elements,
//             proof,
//         }
//     }

//     fn allocate_without_value<CS: ConstraintSystem<F>>(_cs: &mut CS) -> Self {
//         unimplemented!("can not be implemented for such type")
//     }

//     fn placeholder_witness() -> Self::Witness {
//         unimplemented!("should not be implemented for such type")
//     }
// }

// impl<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>> WitnessHookable<F>
//     for AllocatedOracleQuery<F, H>
// where
//     H::CircuitOutput: WitnessHookable<F>,
// {
//     fn witness_hook<CS: ConstraintSystem<F>>(
//         &self,
//         cs: &CS,
//     ) -> Box<dyn FnOnce() -> Option<Self::Witness> + 'static> {
//         let leaf_elements: Vec<_> = self
//             .leaf_elements
//             .iter()
//             .map(|el| el.witness_hook(cs))
//             .collect();
//         let proof: Vec<_> = self.proof.iter().map(|el| el.witness_hook(cs)).collect();

//         let hook_fn = move || {
//             let mut leaf_elements_wits = Vec::with_capacity(leaf_elements.len());
//             for el in leaf_elements.into_iter() {
//                 let el = el()?;
//                 leaf_elements_wits.push(el);
//             }

//             let mut proof_wits = Vec::with_capacity(proof.len());
//             for el in proof.into_iter() {
//                 let el = el()?;
//                 proof_wits.push(el);
//             }

//             let wit = Self::Witness {
//                 leaf_elements: leaf_elements_wits,
//                 proof: proof_wits,
//             };

//             Some(wit)
//         };

//         Box::new(hook_fn)
//     }
// }

#[derive(derivative::Derivative)]
#[derivative(Clone(bound = ""))]
pub struct AllocatedSingleRoundQueries<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>> {
    // we need query for witness, setup, stage 2 and quotient
    pub witness_query: AllocatedOracleQuery<F, H>,
    pub stage_2_query: AllocatedOracleQuery<F, H>,
    pub quotient_query: AllocatedOracleQuery<F, H>,
    pub setup_query: AllocatedOracleQuery<F, H>,

    pub fri_queries: Vec<AllocatedOracleQuery<F, H>>,
}

impl<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>> AllocatedSingleRoundQueries<F, H> {
    pub fn allocate_from_witness<CS: ConstraintSystem<F>, EXT: FieldExtension<2, BaseField = F>>(
        cs: &mut CS,
        witness: Option<SingleRoundQueries<F, H::NonCircuitSimulator>>,
        verifier: &RecursiveVerifier<F, EXT, CS>,
        fixed_parameters: &VerificationKeyCircuitGeometry,
        proof_config: &ProofConfig,
    ) -> Self {
        let base_oracle_depth = fixed_parameters.base_oracles_depth();

        let witness_leaf_size = verifier.witness_leaf_size(fixed_parameters);
        let witness_query = AllocatedOracleQuery::allocate_from_witness(
            cs,
            witness.as_ref().map(|el| el.witness_query.clone()),
            witness_leaf_size,
            base_oracle_depth,
        );

        let stage_2_leaf_size = verifier.stage_2_leaf_size(fixed_parameters);
        let stage_2_query = AllocatedOracleQuery::allocate_from_witness(
            cs,
            witness.as_ref().map(|el| el.stage_2_query.clone()),
            stage_2_leaf_size,
            base_oracle_depth,
        );

        let quotient_leaf_size = verifier.quotient_leaf_size(fixed_parameters);
        let quotient_query = AllocatedOracleQuery::allocate_from_witness(
            cs,
            witness.as_ref().map(|el| el.quotient_query.clone()),
            quotient_leaf_size,
            base_oracle_depth,
        );

        let setup_leaf_size = verifier.setup_leaf_size(fixed_parameters);
        let setup_query = AllocatedOracleQuery::allocate_from_witness(
            cs,
            witness.as_ref().map(|el| el.setup_query.clone()),
            setup_leaf_size,
            base_oracle_depth,
        );

        // fri is a little bit more involved
        let mut expected_fri_query_len = base_oracle_depth;
        let interpolation_schedule = verifier.fri_folding_schedule(fixed_parameters, proof_config);
        let mut fri_queries = Vec::with_capacity(interpolation_schedule.len());
        for (idx, interpolation_log_2) in interpolation_schedule.into_iter().enumerate() {
            expected_fri_query_len -= interpolation_log_2;
            let leaf_size = (1 << interpolation_log_2) * 2; // in extension
            let wit = witness.as_ref().map(|el| el.fri_queries[idx].clone());
            let query = AllocatedOracleQuery::allocate_from_witness(
                cs,
                wit,
                leaf_size,
                expected_fri_query_len,
            );
            fri_queries.push(query);
        }

        Self {
            witness_query,
            stage_2_query,
            quotient_query,
            setup_query,
            fri_queries,
        }
    }
}

// impl<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>> CSAllocatable<F>
//     for AllocatedSingleRoundQueries<F, H>
// {
//     type Witness = SingleRoundQueries<F, H::NonCircuitSimulator>;

//     fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
//         let SingleRoundQueries {
//             witness_query,
//             stage_2_query,
//             quotient_query,
//             setup_query,

//             fri_queries,
//         } = witness;

//         let witness_query = AllocatedOracleQuery::allocate(cs, witness_query);
//         let stage_2_query = AllocatedOracleQuery::allocate(cs, stage_2_query);
//         let quotient_query = AllocatedOracleQuery::allocate(cs, quotient_query);
//         let setup_query = AllocatedOracleQuery::allocate(cs, setup_query);

//         let fri_queries = fri_queries
//             .into_iter()
//             .map(|el| AllocatedOracleQuery::allocate(cs, el))
//             .collect();

//         Self {
//             witness_query,
//             stage_2_query,
//             quotient_query,
//             setup_query,

//             fri_queries,
//         }
//     }

//     fn allocate_without_value<CS: ConstraintSystem<F>>(_cs: &mut CS) -> Self {
//         unimplemented!("can not be implemented for such type")
//     }

//     fn placeholder_witness() -> Self::Witness {
//         unimplemented!("should not be implemented for such type")
//     }
// }

#[derive(derivative::Derivative)]
#[derivative(Clone(bound = ""))]
pub struct AllocatedProof<
    F: SmallField,
    H: RecursiveTreeHasher<F, Num<F>>,
    EXT: FieldExtension<2, BaseField = F>,
> {
    pub public_inputs: Vec<Num<F>>,

    pub witness_oracle_cap: Vec<H::CircuitOutput>,
    pub stage_2_oracle_cap: Vec<H::CircuitOutput>,
    pub quotient_oracle_cap: Vec<H::CircuitOutput>,
    pub final_fri_monomials: [Vec<Num<F>>; 2],

    pub values_at_z: Vec<[Num<F>; 2]>,
    pub values_at_z_omega: Vec<[Num<F>; 2]>,
    pub values_at_0: Vec<[Num<F>; 2]>,

    pub fri_base_oracle_cap: Vec<H::CircuitOutput>,
    pub fri_intermediate_oracles_caps: Vec<Vec<H::CircuitOutput>>,

    pub queries_per_fri_repetition: Vec<AllocatedSingleRoundQueries<F, H>>,

    pub pow_challenge: [Boolean<F>; 64],

    _marker: std::marker::PhantomData<EXT>,
}

impl<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>, EXT: FieldExtension<2, BaseField = F>>
    AllocatedProof<F, H, EXT>
{
    pub fn allocate_from_witness<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        witness: Option<Proof<F, H::NonCircuitSimulator, EXT>>,
        verifier: &RecursiveVerifier<F, EXT, CS>,
        fixed_parameters: &VerificationKeyCircuitGeometry,
        proof_config: &ProofConfig,
    ) -> Self {
        if let Some(config) = witness.as_ref().map(|el| &el.proof_config) {
            assert_eq!(config, proof_config);
        }

        let num_elements = fixed_parameters.num_public_inputs();
        let public_inputs = witness.as_ref().map(|el| el.public_inputs.iter().copied());
        let public_inputs = allocate_num_elements::<F, CS, Num<F>>(cs, num_elements, public_inputs);

        let num_elements = fixed_parameters.cap_size;
        let witness_oracle_cap = witness
            .as_ref()
            .map(|el| el.witness_oracle_cap.iter().cloned());
        let witness_oracle_cap =
            allocate_num_elements::<F, CS, H::CircuitOutput>(cs, num_elements, witness_oracle_cap);

        let num_elements = fixed_parameters.cap_size;
        let stage_2_oracle_cap = witness
            .as_ref()
            .map(|el| el.stage_2_oracle_cap.iter().cloned());
        let stage_2_oracle_cap =
            allocate_num_elements::<F, CS, H::CircuitOutput>(cs, num_elements, stage_2_oracle_cap);

        let num_elements = fixed_parameters.cap_size;
        let quotient_oracle_cap = witness
            .as_ref()
            .map(|el| el.quotient_oracle_cap.iter().cloned());
        let quotient_oracle_cap =
            allocate_num_elements::<F, CS, H::CircuitOutput>(cs, num_elements, quotient_oracle_cap);

        let num_elements = verifier.final_expected_degree(fixed_parameters, proof_config);
        let final_fri_monomials_c0 = witness
            .as_ref()
            .map(|el| el.final_fri_monomials[0].iter().cloned());
        let final_fri_monomials_c0 =
            allocate_num_elements::<F, CS, Num<F>>(cs, num_elements, final_fri_monomials_c0);

        let num_elements = verifier.final_expected_degree(fixed_parameters, proof_config);
        let final_fri_monomials_c1 = witness
            .as_ref()
            .map(|el| el.final_fri_monomials[1].iter().cloned());
        let final_fri_monomials_c1 =
            allocate_num_elements::<F, CS, Num<F>>(cs, num_elements, final_fri_monomials_c1);

        let num_elements = verifier.num_poly_values_at_z(fixed_parameters);
        let values_at_z = witness
            .as_ref()
            .map(|el| el.values_at_z.iter().map(|el| el.into_coeffs_in_base()));
        let values_at_z =
            allocate_num_elements::<F, CS, [Num<F>; 2]>(cs, num_elements, values_at_z);

        let num_elements = verifier.num_poly_values_at_z_omega();
        let values_at_z_omega = witness.as_ref().map(|el| {
            el.values_at_z_omega
                .iter()
                .map(|el| el.into_coeffs_in_base())
        });
        let values_at_z_omega =
            allocate_num_elements::<F, CS, [Num<F>; 2]>(cs, num_elements, values_at_z_omega);

        let num_elements = verifier.num_poly_values_at_zero(fixed_parameters);
        let values_at_0 = witness
            .as_ref()
            .map(|el| el.values_at_0.iter().map(|el| el.into_coeffs_in_base()));
        let values_at_0 =
            allocate_num_elements::<F, CS, [Num<F>; 2]>(cs, num_elements, values_at_0);

        let num_elements = fixed_parameters.cap_size;
        let fri_base_oracle_cap = witness
            .as_ref()
            .map(|el| el.fri_base_oracle_cap.iter().cloned());
        let fri_base_oracle_cap =
            allocate_num_elements::<F, CS, H::CircuitOutput>(cs, num_elements, fri_base_oracle_cap);

        let fri_folding_schedule = verifier.fri_folding_schedule(fixed_parameters, proof_config);
        assert!(fri_folding_schedule.len() > 0);
        let mut fri_intermediate_oracles_caps = Vec::with_capacity(fri_folding_schedule.len() - 1);
        for idx in 0..(fri_folding_schedule.len() - 1) {
            let num_elements = fixed_parameters.cap_size;
            let fri_intermediate_cap = witness
                .as_ref()
                .map(|el| el.fri_intermediate_oracles_caps[idx].iter().cloned());
            let fri_intermediate_cap = allocate_num_elements::<F, CS, H::CircuitOutput>(
                cs,
                num_elements,
                fri_intermediate_cap,
            );
            fri_intermediate_oracles_caps.push(fri_intermediate_cap);
        }

        let num_items = verifier.num_fri_repetitions(fixed_parameters, proof_config);
        let mut queries_per_fri_repetition = Vec::with_capacity(num_items);
        for idx in 0..num_items {
            let wit = witness
                .as_ref()
                .map(|el| el.queries_per_fri_repetition[idx].clone());
            let queries = AllocatedSingleRoundQueries::allocate_from_witness(
                cs,
                wit,
                verifier,
                fixed_parameters,
                proof_config,
            );
            queries_per_fri_repetition.push(queries);
        }

        let pow_challenge = witness.as_ref().map(|el| el.pow_challenge).unwrap_or(0u64);
        let pow_challenge = [pow_challenge];
        let mut lsb_iter = LSBIterator::new(&pow_challenge);
        let pow_challenge: [_; 64] = std::array::from_fn(|_| {
            let witness = lsb_iter.next().unwrap();
            Boolean::allocate(cs, witness)
        });

        let final_fri_monomials = [final_fri_monomials_c0, final_fri_monomials_c1];

        Self {
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

            _marker: std::marker::PhantomData,
        }
    }
}

// impl<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>, EXT: FieldExtension<2, BaseField = F>>
//     CSAllocatable<F> for AllocatedProof<F, H, EXT>
// {
//     type Witness = Proof<F, H::NonCircuitSimulator, EXT>;

//     fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
//         let Proof {
//             proof_config: _,
//             public_inputs,
//             witness_oracle_cap,
//             stage_2_oracle_cap,
//             quotient_oracle_cap,
//             final_fri_monomials,
//             values_at_z,
//             values_at_z_omega,
//             values_at_0,
//             fri_base_oracle_cap,
//             fri_intermediate_oracles_caps,
//             queries_per_fri_repetition,
//             pow_challenge,
//             _marker: _,
//         } = witness;

//         let public_inputs = public_inputs
//             .into_iter()
//             .map(|el| Num::allocate(cs, el))
//             .collect();

//         let witness_oracle_cap = witness_oracle_cap
//             .into_iter()
//             .map(|el| H::CircuitOutput::allocate(cs, el))
//             .collect();
//         let stage_2_oracle_cap = stage_2_oracle_cap
//             .into_iter()
//             .map(|el| H::CircuitOutput::allocate(cs, el))
//             .collect();
//         let quotient_oracle_cap = quotient_oracle_cap
//             .into_iter()
//             .map(|el| H::CircuitOutput::allocate(cs, el))
//             .collect();

//         let final_fri_monomials =
//             final_fri_monomials.map(|el| el.into_iter().map(|el| Num::allocate(cs, el)).collect());

//         let values_at_z = values_at_z
//             .into_iter()
//             .map(|el| <[Num<F>; 2]>::allocate(cs, el.into_coeffs_in_base()))
//             .collect();
//         let values_at_z_omega = values_at_z_omega
//             .into_iter()
//             .map(|el| <[Num<F>; 2]>::allocate(cs, el.into_coeffs_in_base()))
//             .collect();
//         let values_at_0 = values_at_0
//             .into_iter()
//             .map(|el| <[Num<F>; 2]>::allocate(cs, el.into_coeffs_in_base()))
//             .collect();

//         let fri_base_oracle_cap = fri_base_oracle_cap
//             .into_iter()
//             .map(|el| H::CircuitOutput::allocate(cs, el))
//             .collect();
//         let fri_intermediate_oracles_caps = fri_intermediate_oracles_caps
//             .into_iter()
//             .map(|el| {
//                 el.into_iter()
//                     .map(|el| H::CircuitOutput::allocate(cs, el))
//                     .collect::<Vec<_>>()
//             })
//             .collect();

//         let queries_per_fri_repetition = queries_per_fri_repetition
//             .into_iter()
//             .map(|el| AllocatedSingleRoundQueries::allocate(cs, el))
//             .collect();

//         let pow_challenge = [pow_challenge];
//         let mut lsb_iter = LSBIterator::new(&pow_challenge);
//         let pow_challenge: [_; 64] = std::array::from_fn(|_| {
//             let witness = lsb_iter.next().unwrap();
//             Boolean::allocate(cs, witness)
//         });

//         Self {
//             public_inputs,

//             witness_oracle_cap,
//             stage_2_oracle_cap,
//             quotient_oracle_cap,
//             final_fri_monomials,

//             values_at_z,
//             values_at_z_omega,
//             values_at_0,

//             fri_base_oracle_cap,
//             fri_intermediate_oracles_caps,

//             queries_per_fri_repetition,

//             pow_challenge: pow_challenge,

//             _marker: std::marker::PhantomData,
//         }
//     }

//     fn allocate_without_value<CS: ConstraintSystem<F>>(_cs: &mut CS) -> Self {
//         unimplemented!("can not be implemented for such type")
//     }

//     fn placeholder_witness() -> Self::Witness {
//         unimplemented!("should not be implemented for such type")
//     }
// }
