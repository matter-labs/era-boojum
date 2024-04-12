use pairing::ff::PrimeField;

use crate::{
    cs::traits::cs::ConstraintSystem,
    field::SmallField,
    gadgets::{boolean::Boolean, non_native_field::traits::NonNativeField},
};

use super::{fq12::Fq12, fq6::Fq6, params::Extension12Params};

/// `TorusWrapper` is an algebraic compression of the `Fq12` element via underlying encoding of `Fq6`.
/// In compressed form operations over Fq12 are less expensive.
#[derive(Clone, Debug, Copy)]
pub struct TorusWrapper<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension12Params<T>,
{
    pub encoding: Fq6<F, T, NN, P::Ex6>,
}

impl<F: SmallField, T: PrimeField, NN: NonNativeField<F, T>, P: Extension12Params<T>>
    TorusWrapper<F, T, NN, P>
{
    pub fn new(encoding: Fq6<F, T, NN, P::Ex6>) -> Self {
        todo!()
    }

    pub fn mask<CS>(&mut self, cs: &mut CS, flag: &Boolean<F>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    pub fn compress<CS>(cs: &mut CS, e: Fq12<F, T, NN, P>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    pub fn decompress<CS>(&self, cs: &mut CS) -> Fq12<F, T, NN, P>
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    pub fn frobenius_map<CS>(&mut self, cs: &mut CS, power: usize) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    pub fn mul<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    pub fn pow<CS>(&mut self, cs: &mut CS, exp: T) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    pub fn inverse<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    pub fn square<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }

    pub fn replace_by_constant_if_trivial<CS>(
        &mut self,
        cs: &mut CS,
        value: P::Witness,
    ) -> (Self, Boolean<F>)
    where
        CS: ConstraintSystem<F>,
    {
        todo!()
    }
}
