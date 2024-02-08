use std::marker::PhantomData;

use crate::{
    config::CSResolverConfig,
    cs::traits::cs::CSWitnessSource,
    dag::{
        awaiters::Awaiter, primitives::OrderIx, CircuitResolver, WitnessSource,
        WitnessSourceAwaitable,
    },
    field::SmallField,
};

pub struct NullCircuitResolver<F, CFG> {
    phantom: PhantomData<(F, CFG)>,
}

impl<F: SmallField, CFG: CSResolverConfig> WitnessSource<F> for NullCircuitResolver<F, CFG> {
    const PRODUCES_VALUES: bool = false;

    fn try_get_value(&self, _variable: crate::cs::Place) -> Option<F> {
        panic!("Null resolver.");
    }

    fn get_value_unchecked(&self, _variable: crate::cs::Place) -> F {
        panic!("Null resolver.");
    }
}

impl<F: SmallField, CFG: CSResolverConfig> WitnessSourceAwaitable<F>
    for NullCircuitResolver<F, CFG>
{
    type Awaiter<'a> = Awaiter<'a, OrderIx>;

    fn get_awaiter<const N: usize>(&mut self, _vars: [crate::cs::Place; N]) -> Self::Awaiter<'_> {
        panic!("Null resolver.");
    }
}

impl<F: SmallField, CFG: CSResolverConfig> CSWitnessSource<F> for NullCircuitResolver<F, CFG> {}

impl<F: SmallField, CFG: CSResolverConfig> CircuitResolver<F, CFG> for NullCircuitResolver<F, CFG> {
    type Arg = ();

    fn new(_args: Self::Arg) -> Self {
        panic!("Null resolver.");
    }

    fn set_value(&mut self, _key: crate::cs::Place, _value: F) {
        panic!("Null resolver.");
    }

    fn add_resolution<Fn>(
        &mut self,
        _inputs: &[crate::cs::Place],
        _outputs: &[crate::cs::Place],
        _f: Fn,
    ) where
        Fn: FnOnce(&[F], &mut crate::cs::traits::cs::DstBuffer<'_, '_, F>) + Send + Sync,
    {
        panic!("Null resolver");
    }

    fn clear(&mut self) {
        panic!("Null resolver");
    }

    fn wait_till_resolved(&mut self) {
        panic!("Null resolver");
    }
}
