use super::cs::ConstraintSystem;
use super::*;
use crate::cs::traits::evaluator::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GatePlacementStrategy {
    UseSpecializedColumns {
        num_repetitions: usize,
        share_constants: bool,
    },
    UseGeneralPurposeColumns,
}

impl GatePlacementStrategy {
    pub fn specialized_num_repetitions(&self) -> Option<usize> {
        match self {
            Self::UseSpecializedColumns {
                num_repetitions, ..
            } => Some(*num_repetitions),
            Self::UseGeneralPurposeColumns => None,
        }
    }
}

// // helper trait
// pub trait GateCleanupFunctionGenerator<F: SmallField>:
//     Sized + 'static + Send + Sync + Clone + std::fmt::Debug + std::any::Any
// {
//     fn row_finalization_function<CS: ConstraintSystem<F>>(
//         _cs: &CS,
//     ) -> Option<GateCleanupFunction<CS>> {
//         // assume by default that we do not need to cleanup
//         None
//     }
// }

// #[derive(Derivative)]
// #[derivative(Clone, Copy, Debug)]
// pub struct NoCleanupFunction;

// impl<F: SmallField> GateCleanupFunctionGenerator<F> for NoCleanupFunction {}

pub(crate) struct CleanupFunctionGenerator<F: SmallField, CS: ConstraintSystem<F>> {
    pub(crate) rowwise_generator:
        Box<dyn Fn() -> Option<GateRowCleanupFunction<CS>> + 'static + Send + Sync>,
    pub(crate) columnwise_generator:
        Box<dyn Fn() -> Option<GateColumnsCleanupFunction<CS>> + 'static + Send + Sync>,
    pub(crate) _marker: std::marker::PhantomData<(F, CS)>,
}

impl<F: SmallField, CS: ConstraintSystem<F>> CleanupFunctionGenerator<F, CS> {
    pub fn new_for_gate_in_cs<G: Gate<F>>() -> Self {
        let rowwise_generator = || G::row_finalization_function();
        let columnwise_generator = || G::columns_finalization_function();
        Self {
            rowwise_generator: Box::new(rowwise_generator),
            columnwise_generator: Box::new(columnwise_generator),
            _marker: std::marker::PhantomData,
        }
    }
    pub fn row_finalization_function(&self) -> Option<GateRowCleanupFunction<CS>> {
        (self.rowwise_generator)()
    }

    pub fn columns_finalization_function(&self) -> Option<GateColumnsCleanupFunction<CS>> {
        (self.columnwise_generator)()
    }
}

// Not object-safe part that known what to do with itself
pub trait Gate<F: SmallField>:
    Sized + 'static + Send + Sync + Clone + std::fmt::Debug + std::any::Any
{
    type Tools: GateTool = ();
    // type CleanupFunction: GateCleanupFunctionGenerator<F> = NoCleanupFunction;

    #[inline]
    fn placement_type(&self) -> GatePlacementType {
        self.evaluator().placement_type()
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, geometry: &CSGeometry) -> usize {
        self.evaluator().num_repetitions_in_geometry(geometry)
    }

    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool;

    type Evaluator: GateConstraintEvaluator<F>;
    fn evaluator(&self) -> Self::Evaluator;

    #[inline]
    fn num_required_constants(&self, geometry: &CSGeometry) -> usize {
        self.evaluator()
            .num_required_constants_in_geometry(geometry)
    }

    #[inline]
    fn capacity_per_row<CS: ConstraintSystem<F>>(&self, cs: &CS) -> usize {
        match cs.get_gate_placement_strategy::<Self>() {
            GatePlacementStrategy::UseGeneralPurposeColumns => {
                <<Self as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::num_repetitions_in_geometry(
                    &<Self as Gate<F>>::evaluator(self),
                    &cs.get_params()
                )
            },
            GatePlacementStrategy::UseSpecializedColumns { num_repetitions, .. } => {
                num_repetitions
            }
        }
    }
    // if gate is placed over general purpose columns then it should be able to fill the row(!)
    // witness to the end
    fn row_finalization_function<CS: ConstraintSystem<F>>() -> Option<GateRowCleanupFunction<CS>> {
        // assume by default that we do not need to cleanup
        None
    }
    // if gate is placed over specialized columns then it should be able to fill
    // the corresponding columns, and potentially few sets of them, with proper witness
    fn columns_finalization_function<CS: ConstraintSystem<F>>(
    ) -> Option<GateColumnsCleanupFunction<CS>> {
        // assume by default that we do not need to cleanup
        None
    }
}

pub type GateRowCleanupFunction<CS> = Box<
    dyn FnOnce(&mut CS, &Option<FinalizationHintSerialized>) -> Option<FinalizationHintSerialized>
        + Send
        + Sync
        + 'static,
>;
pub type GateColumnsCleanupFunction<CS> = Box<
    dyn FnOnce(
            &mut CS,
            usize,
            &Option<FinalizationHintSerialized>,
        ) -> Option<FinalizationHintSerialized>
        + Send
        + Sync
        + 'static,
>;
pub type FinalizationHintSerialized = Vec<u8>;
