use std::any::{Any, TypeId};
use std::collections::HashSet;

use super::*;

// To configure the CS we will need to allow some gates to be used,
// as well as specify extra parameters, such as whether gates are evaluated as specialized
// columns, or placed into general purpose columns

// We can implement parameters chain here, and using inline(always) trick and const bounds
// we can have those optimized down to loading of the constants

use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::evaluator::GateConstraintEvaluator;
use crate::cs::traits::gate::Gate;
use crate::cs::traits::gate::{GateColumnsCleanupFunction, GateRowCleanupFunction};

use crate::cs::implementations::evaluator_data::*;

pub trait GateConfigurationHolder<F: SmallField>: Sized + Send + Sync {
    // we can walk over and get the next one
    type DescendantHolder<G: Gate<F>, T: 'static + Send + Sync + Clone>: GateConfigurationHolder<F>;

    const CAN_POSTPONE_DATA_CAPTURE: bool = false;

    fn is_gate_allowed<G: Gate<F>>(&self) -> bool;

    #[inline(always)]
    fn placement_strategy<G: Gate<F>>(&self) -> Option<GatePlacementStrategy> {
        self.placement_strategy_for_type_id(TypeId::of::<G>())
    }
    fn placement_strategy_for_type_id(&self, type_id: TypeId) -> Option<GatePlacementStrategy>;

    fn get_tooling<G: Gate<F>>(&self) -> Option<&G::Tools>;
    fn get_tooling_mut<G: Gate<F>>(&mut self) -> Option<&mut G::Tools>;

    fn get_aux_data<G: Gate<F>, T: 'static + Send + Sync + Clone>(&self) -> Option<&T>;
    fn get_aux_data_mut<G: Gate<F>, T: 'static + Send + Sync + Clone>(&mut self) -> Option<&mut T>;

    fn get_params<G: Gate<F>>(
        &self,
    ) -> Option<
        <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
    >;

    fn add_gate<G: Gate<F>, T: 'static + Send + Sync + Clone>(
        self,
        placement_strategy: GatePlacementStrategy,
        params: <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
        aux_data: T,
    ) -> Self::DescendantHolder<G, T>;

    fn gather_row_finalization_functions<CS: ConstraintSystem<F>>(
        &self,
        dst: &mut Vec<GateRowCleanupFunction<CS>>,
    );
    fn gather_columns_finalization_functions<CS: ConstraintSystem<F>>(
        &self,
        dst: &mut Vec<GateColumnsCleanupFunction<CS>>,
    );
    fn gather_unique_evaluator_ids(
        &self,
        placement_strategy: &GatePlacementStrategy,
        dst: &mut HashSet<std::any::TypeId>,
    );
    fn capture_general_purpose_gate_evaluator_data<
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    >(
        &self,
        _geometry: &CSGeometry,
        _dst: &mut EvaluationDataOverGeneralPurposeColumns<F, P>,
        _ctx: &mut P::Context,
    ) {
        if Self::CAN_POSTPONE_DATA_CAPTURE == false {
            unreachable!()
        } else {
            panic!("should implement it manually")
        }
    }
    fn capture_specialized_gate_evaluator_data<
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    >(
        &self,
        _geometry: &CSGeometry,
        _dst: &mut EvaluationDataOverSpecializedColumns<F, P>,
        _ctx: &mut P::Context,
    ) {
        if Self::CAN_POSTPONE_DATA_CAPTURE == false {
            unreachable!()
        } else {
            panic!("should implement it manually")
        }
    }
}

#[derive(Clone)]
pub struct NoGates;

impl<F: SmallField> GateConfigurationHolder<F> for NoGates {
    type DescendantHolder<G: Gate<F>, T: 'static + Send + Sync + Clone> = GatesTuple<F, G, T, Self>;
    #[inline(always)]
    fn is_gate_allowed<G: Gate<F>>(&self) -> bool {
        false
    }
    #[inline(always)]
    fn placement_strategy_for_type_id(&self, _type_id: TypeId) -> Option<GatePlacementStrategy> {
        None
    }
    #[inline(always)]
    fn get_tooling<G: Gate<F>>(&self) -> Option<&G::Tools> {
        None
    }
    #[inline(always)]
    fn get_tooling_mut<G: Gate<F>>(&mut self) -> Option<&mut G::Tools> {
        None
    }
    #[inline(always)]
    fn get_aux_data<G: Gate<F>, T: 'static + Send + Sync + Clone>(&self) -> Option<&T> {
        None
    }
    #[inline(always)]
    fn get_aux_data_mut<G: Gate<F>, T: 'static + Send + Sync + Clone>(&mut self) -> Option<&mut T> {
        None
    }
    #[inline(always)]
    fn get_params<G: Gate<F>>(
        &self,
    ) -> Option<
        <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
    > {
        None
    }
    #[inline(always)]
    fn add_gate<G: Gate<F>, T: 'static + Send + Sync + Clone>(
        self,
        placement_strategy: GatePlacementStrategy,
        params: <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
        aux_data: T,
    ) -> Self::DescendantHolder<G, T> {
        GatesTuple {
            placement_strategy,
            parameters: params,
            tools: G::Tools::create(),
            aux_data,
            other: self,
        }
    }
    #[inline(always)]
    fn gather_row_finalization_functions<CS: ConstraintSystem<F>>(
        &self,
        _dst: &mut Vec<GateRowCleanupFunction<CS>>,
    ) {
    }
    #[inline(always)]
    fn gather_columns_finalization_functions<CS: ConstraintSystem<F>>(
        &self,
        _dst: &mut Vec<GateColumnsCleanupFunction<CS>>,
    ) {
    }
    #[inline(always)]
    fn gather_unique_evaluator_ids(
        &self,
        _placement_strategy: &GatePlacementStrategy,
        _dst: &mut HashSet<std::any::TypeId>,
    ) {
    }
    fn capture_general_purpose_gate_evaluator_data<
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    >(
        &self,
        _geometry: &CSGeometry,
        _dst: &mut EvaluationDataOverGeneralPurposeColumns<F, P>,
        _ctx: &mut P::Context,
    ) {
    }
    fn capture_specialized_gate_evaluator_data<
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    >(
        &self,
        _geometry: &CSGeometry,
        _dst: &mut EvaluationDataOverSpecializedColumns<F, P>,
        _ctx: &mut P::Context,
    ) {
    }
}

// We assume that any type ID can have only one parameter
pub struct GatesTuple<
    F: SmallField,
    G: Gate<F>,
    T: 'static + Send + Sync + Clone,
    U: GateConfigurationHolder<F>,
> {
    placement_strategy: GatePlacementStrategy,
    parameters:
        <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
    tools: G::Tools,
    aux_data: T,
    other: U,
}

impl<
        F: SmallField,
        GG: Gate<F>,
        TT: 'static + Send + Sync + Clone,
        U: GateConfigurationHolder<F>,
    > GateConfigurationHolder<F> for GatesTuple<F, GG, TT, U>
{
    type DescendantHolder<G: Gate<F>, T: 'static + Send + Sync + Clone> = GatesTuple<F, G, T, Self>;

    #[inline(always)]
    fn is_gate_allowed<G: Gate<F>>(&self) -> bool {
        if std::any::TypeId::of::<G>() == std::any::TypeId::of::<GG>() {
            true
        } else {
            self.other.is_gate_allowed::<G>()
        }
    }
    #[inline(always)]
    fn placement_strategy_for_type_id(&self, type_id: TypeId) -> Option<GatePlacementStrategy> {
        if type_id == std::any::TypeId::of::<GG>() {
            Some(self.placement_strategy)
        } else {
            self.other.placement_strategy_for_type_id(type_id)
        }
    }
    #[inline(always)]
    fn get_tooling<G: Gate<F>>(&self) -> Option<&G::Tools> {
        if std::any::TypeId::of::<G>() == std::any::TypeId::of::<GG>() {
            unsafe {
                let casted: &G::Tools = &*(&self.tools as *const GG::Tools).cast() as &G::Tools;

                Some(casted)
            }
        } else {
            self.other.get_tooling::<G>()
        }
    }
    #[inline(always)]
    fn get_tooling_mut<G: Gate<F>>(&mut self) -> Option<&mut G::Tools> {
        if std::any::TypeId::of::<G>() == std::any::TypeId::of::<GG>() {
            unsafe {
                let casted: &mut G::Tools =
                    &mut *(&mut self.tools as *mut GG::Tools).cast() as &mut G::Tools;

                Some(casted)
            }
        } else {
            self.other.get_tooling_mut::<G>()
        }
    }
    #[inline(always)]
    fn get_aux_data<G: Gate<F>, T: 'static + Send + Sync + Clone>(&self) -> Option<&T> {
        if std::any::TypeId::of::<G>() == std::any::TypeId::of::<GG>() {
            if std::any::TypeId::of::<T>() == std::any::TypeId::of::<TT>() {
                unsafe {
                    let casted: &T = &*(&self.aux_data as *const TT).cast() as &T;

                    Some(casted)
                }
            } else {
                panic!(
                    "Trying to get aux data of type {} for gate {}, but it was named to be of type {}",
                    std::any::type_name::<T>(),
                    std::any::type_name::<G>(),
                    std::any::type_name::<TT>(),
                );
            }
        } else {
            self.other.get_aux_data::<G, T>()
        }
    }
    #[inline(always)]
    fn get_aux_data_mut<G: Gate<F>, T: 'static + Send + Sync + Clone>(&mut self) -> Option<&mut T> {
        if std::any::TypeId::of::<G>() == std::any::TypeId::of::<GG>() {
            if std::any::TypeId::of::<T>() == std::any::TypeId::of::<TT>() {
                unsafe {
                    let casted: &mut T = &mut *(&mut self.aux_data as *mut TT).cast() as &mut T;

                    Some(casted)
                }
            } else {
                panic!(
                    "Trying to get aux data of type {} for gate {}, but it was named to be of type {}",
                    std::any::type_name::<T>(),
                    std::any::type_name::<G>(),
                    std::any::type_name::<TT>(),
                );
            }
        } else {
            self.other.get_aux_data_mut::<G, T>()
        }
    }
    #[inline(always)]
    fn get_params<G: Gate<F>>(
        &self,
    ) -> Option<
        <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
    > {
        if std::any::TypeId::of::<G>() == std::any::TypeId::of::<GG>() {
            unsafe {
                let casted: &<<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams =
                    &*(&self.parameters as *const <<GG as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams).cast() as &<<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams;

                Some(casted.clone())
            }
        } else {
            self.other.get_params::<G>()
        }
    }
    #[inline(always)]
    fn add_gate<G: Gate<F>, T: 'static + Send + Sync + Clone>(
        self,
        placement_strategy: GatePlacementStrategy,
        params: <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
        aux_data: T,
    ) -> Self::DescendantHolder<G, T> {
        if self.is_gate_allowed::<G>() {
            panic!(
                "Gate type {} is already in the system",
                std::any::type_name::<G>()
            );
        }

        GatesTuple {
            parameters: params,
            placement_strategy,
            tools: G::Tools::create(),
            aux_data,
            other: self,
        }
    }
    fn gather_row_finalization_functions<CS: ConstraintSystem<F>>(
        &self,
        dst: &mut Vec<GateRowCleanupFunction<CS>>,
    ) {
        if matches!(
            self.placement_strategy,
            GatePlacementStrategy::UseGeneralPurposeColumns
        ) {
            if let Some(cleanup_fn) = GG::row_finalization_function::<CS>() {
                dst.push(cleanup_fn);
            }
        }
        self.other.gather_row_finalization_functions::<CS>(dst);
    }
    fn gather_columns_finalization_functions<CS: ConstraintSystem<F>>(
        &self,
        dst: &mut Vec<GateColumnsCleanupFunction<CS>>,
    ) {
        if matches!(
            self.placement_strategy,
            GatePlacementStrategy::UseSpecializedColumns { .. }
        ) {
            if let Some(cleanup_fn) = GG::columns_finalization_function::<CS>() {
                dst.push(cleanup_fn);
            }
        }
        self.other.gather_columns_finalization_functions::<CS>(dst);
    }
    fn gather_unique_evaluator_ids(
        &self,
        placement_strategy: &GatePlacementStrategy,
        dst: &mut HashSet<std::any::TypeId>,
    ) {
        if &self.placement_strategy == placement_strategy {
            dst.insert(std::any::TypeId::of::<GG::Evaluator>());
        }
        self.other
            .gather_unique_evaluator_ids(placement_strategy, dst);
    }
    // Note on this two methods: they should be kind-of in reverse order
    fn capture_general_purpose_gate_evaluator_data<
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    >(
        &self,
        geometry: &CSGeometry,
        dst: &mut EvaluationDataOverGeneralPurposeColumns<F, P>,
        ctx: &mut P::Context,
    ) {
        assert!(Self::CAN_POSTPONE_DATA_CAPTURE == true);
        self.other
            .capture_general_purpose_gate_evaluator_data::<P>(geometry, dst, ctx);
        if matches!(
            self.placement_strategy,
            GatePlacementStrategy::UseGeneralPurposeColumns
        ) {
            let evaluator = GG::Evaluator::new_from_parameters(self.parameters.clone());
            dst.capture_gate_data::<GG>(evaluator, geometry, ctx);
        }
    }
    fn capture_specialized_gate_evaluator_data<
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    >(
        &self,
        geometry: &CSGeometry,
        dst: &mut EvaluationDataOverSpecializedColumns<F, P>,
        ctx: &mut P::Context,
    ) {
        assert!(Self::CAN_POSTPONE_DATA_CAPTURE == true);
        self.other
            .capture_specialized_gate_evaluator_data::<P>(geometry, dst, ctx);
        if matches!(
            self.placement_strategy,
            GatePlacementStrategy::UseSpecializedColumns { .. }
        ) {
            let evaluator = GG::Evaluator::new_from_parameters(self.parameters.clone());
            dst.capture_gate_data::<GG>(evaluator, self.placement_strategy, geometry, ctx);
        }
    }
}

// We can also have a dynamic gate config, that boxes individual entries, but looks like the same type from
// compiler perspective and speeds up compilation if needed for testing

// We assume that any type ID can have only one parameter
pub struct DynGatesConfig<F: SmallField> {
    is_placeholder: bool,
    gate_type_id: TypeId,
    evaluator_type_id: TypeId,
    placement_strategy: GatePlacementStrategy,
    parameters_type_id: TypeId,
    parameters: Box<dyn Any + 'static + Send + Sync>,
    tools_type_id: TypeId,
    tools: Box<dyn Any + 'static + Send + Sync>,
    aux_data_type_id: TypeId,
    aux_data: Box<dyn Any + 'static + Send + Sync>,
    other: Option<Box<Self>>,
    _marker: std::marker::PhantomData<&'static F>,
}

impl<F: SmallField> DynGatesConfig<F> {
    pub fn empty() -> Self {
        let dummy_id = TypeId::of::<()>();
        Self {
            is_placeholder: true,
            gate_type_id: dummy_id,
            evaluator_type_id: dummy_id,
            placement_strategy: GatePlacementStrategy::UseGeneralPurposeColumns,
            parameters_type_id: dummy_id,
            parameters: Box::new(()),
            tools_type_id: dummy_id,
            tools: Box::new(()),
            aux_data_type_id: dummy_id,
            aux_data: Box::new(()),
            other: None,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<F: SmallField> GateConfigurationHolder<F> for DynGatesConfig<F> {
    type DescendantHolder<G: Gate<F>, T: 'static + Send + Sync + Clone> = Self;

    const CAN_POSTPONE_DATA_CAPTURE: bool = false;

    #[inline(always)]
    fn is_gate_allowed<G: Gate<F>>(&self) -> bool {
        if self.is_placeholder {
            return false;
        }
        if std::any::TypeId::of::<G>() == self.gate_type_id {
            true
        } else {
            if let Some(other) = self.other.as_ref() {
                other.is_gate_allowed::<G>()
            } else {
                false
            }
        }
    }
    #[inline(always)]
    fn placement_strategy_for_type_id(&self, type_id: TypeId) -> Option<GatePlacementStrategy> {
        if self.is_placeholder {
            return None;
        }
        if type_id == self.gate_type_id {
            Some(self.placement_strategy)
        } else {
            if let Some(other) = self.other.as_ref() {
                other.placement_strategy_for_type_id(type_id)
            } else {
                None
            }
        }
    }
    #[inline(always)]
    fn get_tooling<G: Gate<F>>(&self) -> Option<&G::Tools> {
        if self.is_placeholder {
            return None;
        }
        if std::any::TypeId::of::<G>() == self.gate_type_id {
            let casted = self
                .tools
                .downcast_ref::<G::Tools>()
                .expect("must be same type");

            Some(casted)
        } else {
            if let Some(other) = self.other.as_ref() {
                other.get_tooling::<G>()
            } else {
                None
            }
        }
    }
    #[inline(always)]
    fn get_tooling_mut<G: Gate<F>>(&mut self) -> Option<&mut G::Tools> {
        if self.is_placeholder {
            return None;
        }
        if std::any::TypeId::of::<G>() == self.gate_type_id {
            let casted = self
                .tools
                .downcast_mut::<G::Tools>()
                .expect("must be same type");

            Some(casted)
        } else {
            if let Some(other) = self.other.as_mut() {
                other.get_tooling_mut::<G>()
            } else {
                None
            }
        }
    }
    #[inline(always)]
    fn get_aux_data<G: Gate<F>, T: 'static + Send + Sync + Clone>(&self) -> Option<&T> {
        if self.is_placeholder {
            return None;
        }
        if std::any::TypeId::of::<G>() == self.gate_type_id {
            if std::any::TypeId::of::<T>() == self.tools_type_id {
                let casted = self
                    .aux_data
                    .downcast_ref::<T>()
                    .expect("must be same type");

                Some(casted)
            } else {
                panic!(
                    "Mismatch in types when trying to get aux data of type {} for gate {}",
                    std::any::type_name::<T>(),
                    std::any::type_name::<G>(),
                );
            }
        } else {
            if let Some(other) = self.other.as_ref() {
                other.get_aux_data::<G, T>()
            } else {
                None
            }
        }
    }
    #[inline(always)]
    fn get_aux_data_mut<G: Gate<F>, T: 'static + Send + Sync + Clone>(&mut self) -> Option<&mut T> {
        if self.is_placeholder {
            return None;
        }
        if std::any::TypeId::of::<G>() == self.gate_type_id {
            if std::any::TypeId::of::<T>() == self.tools_type_id {
                let casted = self
                    .aux_data
                    .downcast_mut::<T>()
                    .expect("must be same type");

                Some(casted)
            } else {
                panic!(
                    "Mismatch in types when trying to get aux data of type {} for gate {}",
                    std::any::type_name::<T>(),
                    std::any::type_name::<G>(),
                );
            }
        } else {
            if let Some(other) = self.other.as_mut() {
                other.get_aux_data_mut::<G, T>()
            } else {
                None
            }
        }
    }
    #[inline(always)]
    fn get_params<G: Gate<F>>(
        &self,
    ) -> Option<
        <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
    > {
        if self.is_placeholder {
            return None;
        }
        if std::any::TypeId::of::<G>() == self.gate_type_id {
            let casted = self.parameters.downcast_ref::<<<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams>().expect("must be same type");

            Some(casted.clone())
        } else {
            if let Some(other) = self.other.as_ref() {
                other.get_params::<G>()
            } else {
                None
            }
        }
    }
    #[inline(always)]
    fn add_gate<G: Gate<F>, T: 'static + Send + Sync + Clone>(
        self,
        placement_strategy: GatePlacementStrategy,
        params: <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
        aux_data: T,
    ) -> Self::DescendantHolder<G, T> {
        if self.is_gate_allowed::<G>() {
            panic!(
                "Gate type {} is already in the system",
                std::any::type_name::<G>()
            );
        }

        Self {
            is_placeholder: false,
            gate_type_id: TypeId::of::<G>(),
            evaluator_type_id: TypeId::of::<G::Evaluator>(),
            placement_strategy,
            parameters_type_id: TypeId::of::<<<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams>(),
            parameters: Box::new(params),
            tools_type_id: TypeId::of::<G::Tools>(),
            tools: Box::new(G::Tools::create()),
            aux_data_type_id: TypeId::of::<T>(),
            aux_data: Box::new(aux_data),
            other: Some(Box::new(self)),
            _marker: std::marker::PhantomData,
        }
    }
    fn gather_row_finalization_functions<CS: ConstraintSystem<F>>(
        &self,
        _dst: &mut Vec<GateRowCleanupFunction<CS>>,
    ) {
        unreachable!("this type of config should only appear after building");
    }
    fn gather_columns_finalization_functions<CS: ConstraintSystem<F>>(
        &self,
        _dst: &mut Vec<GateColumnsCleanupFunction<CS>>,
    ) {
        unreachable!("this type of config should only appear after building");
    }
    fn gather_unique_evaluator_ids(
        &self,
        _placement_strategy: &GatePlacementStrategy,
        _dst: &mut HashSet<std::any::TypeId>,
    ) {
        unreachable!("this type of config should only appear after building");
    }
}
