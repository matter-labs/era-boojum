use super::*;
use crate::cs::implementations::pow::{NoPow, PoWRunner};

pub trait CircuitPowRunner<F: SmallField> {}

pub trait RecursivePoWRunner<F: SmallField>: PoWRunner {
    type CircuitReflection: CircuitPowRunner<F>;
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Default(bound = ""))]
pub struct CircuitNoPow<F: SmallField> {
    _marker: std::marker::PhantomData<F>,
}

impl<F: SmallField> CircuitPowRunner<F> for CircuitNoPow<F> {}

impl<F: SmallField> RecursivePoWRunner<F> for NoPow {
    type CircuitReflection = CircuitNoPow<F>;
}
