use crate::cs::implementations::evaluator_data::*;
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::evaluator::*;
use crate::cs::traits::gate::*;
use crate::cs::CSGeometry;
use crate::cs::GateTool;
use crate::field::SmallField;
use std::any::TypeId;

pub struct GateTypeEntry<F: SmallField, G: Gate<F>, T: 'static + Send + Sync + Clone> {
    pub placement_strategy: GatePlacementStrategy,
    pub params:
        <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
    pub tools: G::Tools,
    pub aux: T,
    pub _marker: std::marker::PhantomData<(&'static F, &'static G)>,
}

impl<F: SmallField> GateConfigurationHolder<F> for () {
    #[inline(always)]
    fn is_gate_allowed<G: Gate<F>>(&self) -> bool {
        false
    }
    fn is_type_id_included(&self, _type_id: TypeId) -> bool {
        false
    }
    #[inline(always)]
    fn add_gate<G: Gate<F>, T: 'static + Send + Sync + Clone>(
        self,
        placement_strategy: GatePlacementStrategy,
        params: <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
        aux: T,
    ) -> (GateTypeEntry<F, G, T>, Self) {
        (
            GateTypeEntry {
                placement_strategy,
                params,
                tools: G::Tools::create(),
                aux,
                _marker: std::marker::PhantomData,
            },
            (),
        )
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
    fn placement_strategy_for_type_id(&self, _type_id: TypeId) -> Option<GatePlacementStrategy> {
        None
    }
    fn gather_row_finalization_functions<CS: ConstraintSystem<F>>(
        &self,
        _dst: &mut Vec<GateRowCleanupFunction<CS>>,
    ) {
    }
    fn gather_columns_finalization_functions<CS: ConstraintSystem<F>>(
        &self,
        _dst: &mut Vec<GateColumnsCleanupFunction<CS>>,
    ) {
    }
    fn get_tooling<G: Gate<F>>(&self) -> Option<&G::Tools> {
        None
    }
    fn get_tooling_mut<G: Gate<F>>(&mut self) -> Option<&mut G::Tools> {
        None
    }
    fn get_aux_data<G: Gate<F>, T: 'static + Send + Sync + Clone>(&self) -> Option<&T> {
        None
    }
    fn get_aux_data_mut<G: Gate<F>, T: 'static + Send + Sync + Clone>(&mut self) -> Option<&mut T> {
        None
    }
}

impl<
        F: SmallField,
        GG: Gate<F>,
        TT: 'static + Send + Sync + Clone,
        U: GateConfigurationHolder<F>,
    > GateConfigurationHolder<F> for (GateTypeEntry<F, GG, TT>, U)
{
    #[inline(always)]
    fn is_gate_allowed<G: Gate<F>>(&self) -> bool {
        if TypeId::of::<GG>() == TypeId::of::<G>() {
            true
        } else {
            self.1.is_gate_allowed::<G>()
        }
    }
    fn is_type_id_included(&self, type_id: TypeId) -> bool {
        if TypeId::of::<GG>() == type_id {
            true
        } else {
            self.1.is_type_id_included(type_id)
        }
    }
    #[inline(always)]
    fn add_gate<G: Gate<F>, T: 'static + Send + Sync + Clone>(
        self,
        placement_strategy: GatePlacementStrategy,
        params: <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
        aux: T,
    ) -> (GateTypeEntry<F, G, T>, Self) {
        (
            GateTypeEntry {
                placement_strategy,
                params,
                tools: G::Tools::create(),
                aux,
                _marker: std::marker::PhantomData,
            },
            self,
        )
    }
    #[inline(always)]
    fn get_params<G: Gate<F>>(
        &self,
    ) -> Option<
        <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
    > {
        if TypeId::of::<GG>() == TypeId::of::<G>() {
            unsafe {
                let casted: &<<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams = &*(
                    &self.0.params as *const <<GG as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams
                ).cast() as &<<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams;

                Some(casted.clone())
            }
        } else {
            self.1.get_params::<G>()
        }
    }
    #[inline(always)]
    fn placement_strategy_for_type_id(&self, type_id: TypeId) -> Option<GatePlacementStrategy> {
        if TypeId::of::<GG>() == type_id {
            Some(self.0.placement_strategy)
        } else {
            self.1.placement_strategy_for_type_id(type_id)
        }
    }
    fn gather_row_finalization_functions<CS: ConstraintSystem<F>>(
        &self,
        dst: &mut Vec<GateRowCleanupFunction<CS>>,
    ) {
        if matches!(
            self.0.placement_strategy,
            GatePlacementStrategy::UseGeneralPurposeColumns
        ) {
            if let Some(cleanup_fn) = GG::row_finalization_function::<CS>() {
                dst.push(cleanup_fn);
            }
        }
        self.1.gather_row_finalization_functions::<CS>(dst);
    }
    fn gather_columns_finalization_functions<CS: ConstraintSystem<F>>(
        &self,
        dst: &mut Vec<GateColumnsCleanupFunction<CS>>,
    ) {
        if matches!(
            self.0.placement_strategy,
            GatePlacementStrategy::UseSpecializedColumns { .. }
        ) {
            if let Some(cleanup_fn) = GG::columns_finalization_function::<CS>() {
                dst.push(cleanup_fn);
            }
        }
        self.1.gather_columns_finalization_functions::<CS>(dst);
    }
    fn get_tooling<G: Gate<F>>(&self) -> Option<&G::Tools> {
        if TypeId::of::<GG>() == TypeId::of::<G>() {
            unsafe {
                let casted: &G::Tools = &*(&self.0.tools as *const GG::Tools).cast() as &G::Tools;

                Some(casted)
            }
        } else {
            self.1.get_tooling::<G>()
        }
    }
    fn get_tooling_mut<G: Gate<F>>(&mut self) -> Option<&mut G::Tools> {
        if TypeId::of::<GG>() == TypeId::of::<G>() {
            unsafe {
                let casted: &mut G::Tools =
                    &mut *(&mut self.0.tools as *mut GG::Tools).cast() as &mut G::Tools;

                Some(casted)
            }
        } else {
            self.1.get_tooling_mut::<G>()
        }
    }
    fn get_aux_data<G: Gate<F>, T: 'static + Send + Sync + Clone>(&self) -> Option<&T> {
        if TypeId::of::<GG>() == TypeId::of::<G>() {
            debug_assert!(TypeId::of::<TT>() == TypeId::of::<T>());
            unsafe {
                let casted: &T = &*(&self.0.aux as *const TT).cast() as &T;

                Some(casted)
            }
        } else {
            self.1.get_aux_data::<G, T>()
        }
    }
    fn get_aux_data_mut<G: Gate<F>, T: 'static + Send + Sync + Clone>(&mut self) -> Option<&mut T> {
        if TypeId::of::<GG>() == TypeId::of::<G>() {
            debug_assert!(TypeId::of::<TT>() == TypeId::of::<T>());
            unsafe {
                let casted: &mut T = &mut *(&mut self.0.aux as *mut TT).cast() as &mut T;

                Some(casted)
            }
        } else {
            self.1.get_aux_data_mut::<G, T>()
        }
    }
}

pub trait GateConfigurationHolder<F: SmallField>: 'static + Send + Sync {
    const CAN_POSTPONE_DATA_CAPTURE: bool = false;

    fn is_gate_allowed<G: Gate<F>>(&self) -> bool;
    fn is_type_id_included(&self, type_id: TypeId) -> bool;
    fn add_gate<G: Gate<F>, T: 'static + Send + Sync + Clone>(
        self,
        placement_strategy: GatePlacementStrategy,
        params: <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
        aux: T,
    ) -> (GateTypeEntry<F, G, T>, Self);

    fn get_params<G: Gate<F>>(
        &self,
    ) -> Option<
        <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
    >;

    #[inline(always)]
    fn placement_strategy<G: Gate<F>>(&self) -> Option<GatePlacementStrategy> {
        self.placement_strategy_for_type_id(TypeId::of::<G>())
    }
    fn placement_strategy_for_type_id(&self, type_id: TypeId) -> Option<GatePlacementStrategy>;
    fn gather_row_finalization_functions<CS: ConstraintSystem<F>>(
        &self,
        dst: &mut Vec<GateRowCleanupFunction<CS>>,
    );
    fn gather_columns_finalization_functions<CS: ConstraintSystem<F>>(
        &self,
        dst: &mut Vec<GateColumnsCleanupFunction<CS>>,
    );
    fn get_tooling<G: Gate<F>>(&self) -> Option<&G::Tools>;
    fn get_tooling_mut<G: Gate<F>>(&mut self) -> Option<&mut G::Tools>;
    fn get_aux_data<G: Gate<F>, T: 'static + Send + Sync + Clone>(&self) -> Option<&T>;
    fn get_aux_data_mut<G: Gate<F>, T: 'static + Send + Sync + Clone>(&mut self) -> Option<&mut T>;
    fn capture_general_purpose_gate_evaluator_data<
        P: crate::field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
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
        P: crate::field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
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
