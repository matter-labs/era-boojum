// This is zero-sized structure, that records types

use std::any::TypeId;
use std::collections::HashSet;

pub trait TypeSet: 'static + Send + Sync {
    type ExtendedSet<T: 'static + Send + Sync>: TypeSet;
    fn is_type_included<T: 'static + Send + Sync>(&self) -> bool;
    fn is_type_id_included(&self, type_id: TypeId) -> bool;
    fn extend<T: 'static + Send + Sync>(self) -> Self::ExtendedSet<T>;
}

#[derive(Clone, Copy, Debug)]
pub struct EmptySet;

impl TypeSet for EmptySet {
    type ExtendedSet<T: 'static + Send + Sync> = SetEntry<T, Self>;
    #[inline(always)]
    fn is_type_included<T: 'static + Send + Sync>(&self) -> bool {
        false
    }
    #[inline(always)]
    fn is_type_id_included(&self, _type_id: TypeId) -> bool {
        false
    }
    #[inline(always)]
    fn extend<T: 'static + Send + Sync>(self) -> Self::ExtendedSet<T> {
        SetEntry {
            next: self,
            _marker: std::marker::PhantomData,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct SetEntry<T: 'static + Send + Sync, NEXT: TypeSet> {
    pub next: NEXT,
    pub _marker: std::marker::PhantomData<&'static T>,
}

impl<TT: 'static + Send + Sync, NEXT: TypeSet> TypeSet for SetEntry<TT, NEXT> {
    type ExtendedSet<T: 'static + Send + Sync> = SetEntry<T, Self>;
    #[inline(always)]
    fn is_type_included<T: 'static + Send + Sync>(&self) -> bool {
        if TypeId::of::<TT>() == TypeId::of::<T>() {
            true
        } else {
            self.next.is_type_included::<T>()
        }
    }
    #[inline(always)]
    fn is_type_id_included(&self, type_id: TypeId) -> bool {
        if TypeId::of::<TT>() == type_id {
            true
        } else {
            self.next.is_type_id_included(type_id)
        }
    }
    #[inline(always)]
    fn extend<T: 'static + Send + Sync>(self) -> Self::ExtendedSet<T> {
        SetEntry {
            next: self,
            _marker: std::marker::PhantomData,
        }
    }
}

// Unfortunately it's not easy to express something like a set of object that implement some trait,
// and which can only add objects that implement this trait too, so we make a special one for gates

use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::evaluator::GateConstraintEvaluator;
use crate::cs::traits::gate::*;
use crate::field::SmallField;

use super::kv_set::KVSet;
use super::markers::*;

pub trait GateTypeSet<F: SmallField>: 'static + Send + Sync {
    type ExtendedSet<G: Gate<F>>: GateTypeSet<F>;
    fn is_gate_included<G: Gate<F>>(&self) -> bool;
    fn is_type_id_included(&self, type_id: TypeId) -> bool;
    fn extend<G: Gate<F>>(
        self,
        placement_strategy: GatePlacementStrategy,
        params: <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
    ) -> Self::ExtendedSet<G>;

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
    fn gather_unique_evaluator_ids(
        &self,
        placement_strategy: &GatePlacementStrategy,
        dst: &mut HashSet<std::any::TypeId>,
    );

    // default implementations for tooling
    #[inline(always)]
    fn get_tooling<'a, G: Gate<F>, KV: KVSet>(&self, storage: &'a KV) -> Option<&'a G::Tools> {
        storage.get::<MarkerProxy<(GateToolingMarker, G)>, G::Tools>()
    }
    #[inline(always)]
    fn get_tooling_mut<'a, G: Gate<F>, KV: KVSet>(
        &self,
        storage: &'a mut KV,
    ) -> Option<&'a mut G::Tools> {
        storage.get_mut::<MarkerProxy<(GateToolingMarker, G)>, G::Tools>()
    }
}

impl<F: SmallField> GateTypeSet<F> for EmptySet {
    type ExtendedSet<G: Gate<F>> = GateSetEntry<F, G, Self>;
    #[inline(always)]
    fn is_gate_included<G: Gate<F>>(&self) -> bool {
        false
    }
    #[inline(always)]
    fn is_type_id_included(&self, _type_id: TypeId) -> bool {
        false
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
    #[inline(always)]
    fn extend<G: Gate<F>>(
        self,
        placement_strategy: GatePlacementStrategy,
        params: <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
    ) -> Self::ExtendedSet<G> {
        GateSetEntry {
            placement_strategy,
            params,
            next: self,
            _marker: std::marker::PhantomData,
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
}

pub struct GateSetEntry<F: SmallField, G: Gate<F>, NEXT: GateTypeSet<F>> {
    pub placement_strategy: GatePlacementStrategy,
    pub params:
        <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
    pub next: NEXT,
    pub _marker: std::marker::PhantomData<(&'static F, &'static G)>,
}

impl<F: SmallField, GG: Gate<F>, NEXT: GateTypeSet<F>> GateTypeSet<F>
    for GateSetEntry<F, GG, NEXT>
{
    type ExtendedSet<G: Gate<F>> = GateSetEntry<F, G, Self>;
    #[inline(always)]
    fn is_gate_included<G: Gate<F>>(&self) -> bool {
        if TypeId::of::<GG>() == TypeId::of::<G>() {
            true
        } else {
            self.next.is_gate_included::<G>()
        }
    }
    #[inline(always)]
    fn is_type_id_included(&self, type_id: TypeId) -> bool {
        if TypeId::of::<GG>() == type_id {
            true
        } else {
            self.next.is_type_id_included(type_id)
        }
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
                    &self.params as *const <<GG as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams
                ).cast() as &<<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams;

                Some(casted.clone())
            }
        } else {
            self.next.get_params::<G>()
        }
    }
    #[inline(always)]
    fn placement_strategy_for_type_id(&self, type_id: TypeId) -> Option<GatePlacementStrategy> {
        if TypeId::of::<GG>() == type_id {
            Some(self.placement_strategy)
        } else {
            self.next.placement_strategy_for_type_id(type_id)
        }
    }
    #[inline(always)]
    fn extend<G: Gate<F>>(
        self,
        placement_strategy: GatePlacementStrategy,
        params: <<G as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::UniqueParameterizationParams,
    ) -> Self::ExtendedSet<G> {
        GateSetEntry {
            placement_strategy,
            params,
            next: self,
            _marker: std::marker::PhantomData,
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
        self.next.gather_row_finalization_functions::<CS>(dst);
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
        self.next.gather_columns_finalization_functions::<CS>(dst);
    }
    fn gather_unique_evaluator_ids(
        &self,
        placement_strategy: &GatePlacementStrategy,
        dst: &mut HashSet<std::any::TypeId>,
    ) {
        if &self.placement_strategy == placement_strategy {
            dst.insert(std::any::TypeId::of::<GG::Evaluator>());
        }
        self.next
            .gather_unique_evaluator_ids(placement_strategy, dst);
    }
}
