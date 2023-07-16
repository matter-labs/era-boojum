use super::*;
use crate::gadgets::num::Num;
use crate::gadgets::traits::allocatable::allocate_num_elements;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::traits::witnessable::WitnessHookable;
use crate::{
    cs::{
        implementations::verifier::{VerificationKey, VerificationKeyCircuitGeometry},
        traits::cs::ConstraintSystem,
    },
    gadgets::recursion::recursive_tree_hasher::RecursiveTreeHasher,
};

pub struct AllocatedVerificationKey<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>> {
    pub setup_merkle_tree_cap: Vec<H::CircuitOutput>,
}

impl<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>> CSAllocatable<F>
    for AllocatedVerificationKey<F, H>
{
    type Witness = VerificationKey<F, H::NonCircuitSimulator>;

    fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let VerificationKey {
            setup_merkle_tree_cap,
            fixed_parameters,
        } = witness;

        // allocate fixed length
        assert!(fixed_parameters.cap_size > 0);
        let cap = allocate_num_elements::<F, CS, H::CircuitOutput>(
            cs,
            fixed_parameters.cap_size,
            Some(setup_merkle_tree_cap.into_iter()),
        );

        Self {
            setup_merkle_tree_cap: cap,
        }
    }

    fn allocate_without_value<CS: ConstraintSystem<F>>(_cs: &mut CS) -> Self {
        unimplemented!("can not be implemented for such type")
    }

    fn placeholder_witness() -> Self::Witness {
        unimplemented!("should not be implemented for such type")
    }

    fn allocate_constant<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let VerificationKey {
            setup_merkle_tree_cap,
            fixed_parameters,
        } = witness;

        let cap: Vec<_> = setup_merkle_tree_cap
            .into_iter()
            .map(|el| H::CircuitOutput::allocate_constant(cs, el))
            .collect();

        assert!(cap.len() > 0);
        assert_eq!(cap.len(), fixed_parameters.cap_size);

        Self {
            setup_merkle_tree_cap: cap,
        }
    }
}

impl<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>> WitnessHookable<F>
    for AllocatedVerificationKey<F, H>
where
    H::CircuitOutput: WitnessHookable<F>,
{
    fn witness_hook<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
    ) -> Box<dyn FnOnce() -> Option<Self::Witness> + 'static> {
        let setup_merkle_tree_cap: Vec<_> = self
            .setup_merkle_tree_cap
            .iter()
            .map(|el| el.witness_hook(cs))
            .collect();

        let hook_fn = move || {
            let mut setup_merkle_tree_cap_wits = Vec::with_capacity(setup_merkle_tree_cap.len());
            for el in setup_merkle_tree_cap.into_iter() {
                let el = el()?;
                setup_merkle_tree_cap_wits.push(el);
            }

            let wit = Self::Witness {
                setup_merkle_tree_cap: setup_merkle_tree_cap_wits,
                fixed_parameters: VerificationKeyCircuitGeometry::placeholder(),
            };

            Some(wit)
        };

        Box::new(hook_fn)
    }
}

use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;

impl<F: SmallField, H: RecursiveTreeHasher<F, Num<F>>> CircuitVarLengthEncodable<F>
    for AllocatedVerificationKey<F, H>
{
    fn encoding_length(&self) -> usize {
        let cap_size = self.setup_merkle_tree_cap.len();
        assert!(cap_size > 0);
        let el_size = self.setup_merkle_tree_cap[0].encoding_length();

        el_size * cap_size
    }

    fn encode_to_buffer<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        dst: &mut Vec<crate::cs::Variable>,
    ) {
        for el in self.setup_merkle_tree_cap.iter() {
            el.encode_to_buffer(cs, dst);
        }
    }
}
