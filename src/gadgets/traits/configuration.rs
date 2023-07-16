use crate::cs::traits::gate::GatePlacementStrategy;
use crate::cs::*;
use crate::gadgets::traits::configuration::cs_builder::*;

use super::*;

pub trait ConfigurationFunction<F: SmallField, TImpl: CsBuilderImpl<F, TImpl>>:
    std::fmt::Debug
{
    fn configure(
        builder: CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder>,
        placement_strategy: GatePlacementStrategy,
    ) -> CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder>;

    fn configure_proxy(
        &self,
        builder: CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder>,
        placement_strategy: GatePlacementStrategy,
    ) -> CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
        <Self as ConfigurationFunction<F, TImpl>>::configure(builder, placement_strategy)
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct IdentityConfiguration;

impl<F: SmallField, TImpl: CsBuilderImpl<F, TImpl>> ConfigurationFunction<F, TImpl>
    for IdentityConfiguration
{
    fn configure(
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
    TImpl: CsBuilderImpl<F, TImpl>,
    A: ConfigurationFunction<F, TImpl>,
    B: ConfigurationFunction<F, TImpl>,
> {
    _marker: std::marker::PhantomData<(F, TImpl, A, B)>,
}

impl<
        F: SmallField,
        TImpl: CsBuilderImpl<F, TImpl>,
        A: ConfigurationFunction<F, TImpl>,
        B: ConfigurationFunction<F, TImpl>,
    > ConfigurationFunction<F, TImpl> for ConfigurationComposition<F, TImpl, A, B>
{
    fn configure(
        builder: CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder>,
        placement_strategy: GatePlacementStrategy,
    ) -> CsBuilder<TImpl, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
        let builder = A::configure(builder, placement_strategy);
        B::configure(builder, placement_strategy)
    }
}

impl IdentityConfiguration {
    pub fn add_confituration_step<
        F: SmallField,
        TImpl: CsBuilderImpl<F, TImpl>,
        A: ConfigurationFunction<F, TImpl>,
    >(
        self,
    ) -> ConfigurationComposition<F, TImpl, Self, A> {
        ConfigurationComposition {
            _marker: std::marker::PhantomData,
        }
    }
}

impl<
        F: SmallField,
        TImpl: CsBuilderImpl<F, TImpl>,
        A: ConfigurationFunction<F, TImpl>,
        B: ConfigurationFunction<F, TImpl>,
    > ConfigurationComposition<F, TImpl, A, B>
{
    pub fn add_confituration_step<C: ConfigurationFunction<F, TImpl>>(
        self,
    ) -> ConfigurationComposition<F, TImpl, Self, C> {
        ConfigurationComposition {
            _marker: std::marker::PhantomData,
        }
    }
}
