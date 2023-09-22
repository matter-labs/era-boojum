use crate::cs::traits::gate::GatePlacementStrategy;
use crate::cs::*;
use crate::gadgets::traits::configuration::cs_builder::*;

use super::*;

pub trait ConfigurationFunction<F: SmallField>: 'static + Sized + std::fmt::Debug {
    fn configure<TImpl: CsBuilderImpl<F, TImpl>>(
        builder: CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder>,
        placement_strategy: GatePlacementStrategy,
    ) -> CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder>;

    fn configure_proxy<TImpl: CsBuilderImpl<F, TImpl>>(
        self,
        builder: CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder>,
        placement_strategy: GatePlacementStrategy,
    ) -> CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
        <Self as ConfigurationFunction<F>>::configure::<TImpl>(builder, placement_strategy)
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct IdentityConfiguration<F: SmallField> {
    _marker: std::marker::PhantomData<F>,
}

impl<F: SmallField> IdentityConfiguration<F> {
    pub fn new() -> Self {
        Self {
            _marker: std::marker::PhantomData,
        }
    }

    pub fn add_confituration_step<A: ConfigurationFunction<F>>(
        self,
    ) -> ConfigurationComposition<F, Self, A> {
        ConfigurationComposition {
            _marker: std::marker::PhantomData,
        }
    }
}

impl<F: SmallField> ConfigurationFunction<F> for IdentityConfiguration<F> {
    fn configure<TImpl: CsBuilderImpl<F, TImpl>>(
        builder: CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder>,
        _placement_strategy: GatePlacementStrategy,
    ) -> CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
        builder
    }
}

// B follows after A
#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct ConfigurationComposition<
    F: SmallField,
    A: ConfigurationFunction<F>,
    B: ConfigurationFunction<F>,
> {
    _marker: std::marker::PhantomData<(F, A, B)>,
}

impl<F: SmallField, A: ConfigurationFunction<F>, B: ConfigurationFunction<F>>
    ConfigurationFunction<F> for ConfigurationComposition<F, A, B>
{
    fn configure<TImpl: CsBuilderImpl<F, TImpl>>(
        builder: CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder>,
        placement_strategy: GatePlacementStrategy,
    ) -> CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
        let builder = A::configure(builder, placement_strategy);
        B::configure(builder, placement_strategy)
    }
}

impl<F: SmallField, A: ConfigurationFunction<F>, B: ConfigurationFunction<F>>
    ConfigurationComposition<F, A, B>
{
    pub fn add_confituration_step<C: ConfigurationFunction<F>>(
        self,
    ) -> ConfigurationComposition<F, Self, C> {
        ConfigurationComposition {
            _marker: std::marker::PhantomData,
        }
    }
}
