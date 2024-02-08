use super::{
    traits::{evaluator::GateConstraintEvaluator, gate::Gate},
    CSGeometry, GateConfigurationHolder, GateTypeEntry, LookupParameters, StaticToolboxHolder,
    Tool,
};
use crate::cs::traits::gate::GatePlacementStrategy;
use crate::field::SmallField;

pub trait CsBuilderImpl<F: SmallField, TImpl> {
    type Final<GC: GateConfigurationHolder<F>, TB: StaticToolboxHolder>;
    type BuildParams<'a>;

    fn parameters<GC: GateConfigurationHolder<F>, TB: StaticToolboxHolder>(
        builder: &CsBuilder<TImpl, F, GC, TB>,
    ) -> CSGeometry;

    fn allow_gate<
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        G: Gate<F>,
        TAux: 'static + Send + Sync + Clone,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
        params: <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
        aux_data: TAux,
        // ) -> CsBuilder<TImpl, F, GC::DescendantHolder<G, TAux>, TB>;
    ) -> CsBuilder<TImpl, F, (GateTypeEntry<F, G, TAux>, GC), TB>;

    fn add_tool<
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        M: 'static + Send + Sync + Clone,
        T: 'static + Send + Sync,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        tool: T,
        // ) -> CsBuilder<TImpl, F, GC, TB::DescendantHolder<M, T>>;
    ) -> CsBuilder<TImpl, F, GC, (Tool<M, T>, TB)>;

    type GcWithLookup<GC: GateConfigurationHolder<F>>: GateConfigurationHolder<F>;

    fn allow_lookup<GC: GateConfigurationHolder<F>, TB: StaticToolboxHolder>(
        builder: CsBuilder<TImpl, F, GC, TB>,
        lookup_parameters: LookupParameters,
    ) -> CsBuilder<TImpl, F, Self::GcWithLookup<GC>, TB>;

    fn build<
        'a,
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        ARG: Into<Self::BuildParams<'a>>,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        params: ARG,
    ) -> Self::Final<GC, TB>;
}

pub struct CsBuilder<TImpl, F: SmallField, GC: GateConfigurationHolder<F>, TB: StaticToolboxHolder>
{
    pub phantom: std::marker::PhantomData<F>,

    pub implementation: TImpl,
    pub gates_config: GC,
    pub toolbox: TB,
}

pub fn new_builder<TImpl: CsBuilderImpl<F, TImpl>, F: SmallField>(
    implementation: TImpl,
) -> CsBuilder<TImpl, F, (), ()> {
    CsBuilder {
        phantom: std::marker::PhantomData,
        implementation,
        gates_config: (),
        toolbox: (),
    }
}

// pub fn new_builder<TImpl: CsBuilderImpl<F, TImpl>, F: SmallField>(
//     implementation: TImpl,
// ) -> CsBuilder<TImpl, F, NoGates, EmptyToolbox> {
//     CsBuilder {
//         phantom: std::marker::PhantomData,
//         implementation,
//         gates_config: NoGates,
//         toolbox: EmptyToolbox,
//     }
// }

impl<
        TImpl: CsBuilderImpl<F, TImpl>,
        F: SmallField,
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
    > CsBuilder<TImpl, F, GC, TB>
{
    pub fn get_params(&self) -> CSGeometry {
        TImpl::parameters::<GC, TB>(self)
    }

    pub fn allow_gate<G: Gate<F>, TAux: 'static + Send + Sync + Clone>(
        self,
        placement_strategy: GatePlacementStrategy,
        params: <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
        aux_data: TAux,
        // ) -> CsBuilder<TImpl, F, GC::DescendantHolder<G, TAux>, TB> {
    ) -> CsBuilder<TImpl, F, (GateTypeEntry<F, G, TAux>, GC), TB> {
        TImpl::allow_gate::<GC, TB, _, _>(self, placement_strategy, params, aux_data)
    }

    pub fn add_tool<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(
        self,
        tool: T,
        // ) -> CsBuilder<TImpl, F, GC, TB::DescendantHolder<M, T>> {
    ) -> CsBuilder<TImpl, F, GC, (Tool<M, T>, TB)> {
        TImpl::add_tool::<GC, TB, _, _>(self, tool)
    }

    pub fn allow_lookup(
        self,
        lookup_parameters: LookupParameters,
    ) -> CsBuilder<TImpl, F, TImpl::GcWithLookup<GC>, TB> {
        TImpl::allow_lookup::<GC, TB>(self, lookup_parameters)
    }

    /// Build
    pub fn build<'a, ARG: Into<TImpl::BuildParams<'a>>>(self, params: ARG) -> TImpl::Final<GC, TB> {
        TImpl::build::<GC, TB, _>(self, params)
    }
}
