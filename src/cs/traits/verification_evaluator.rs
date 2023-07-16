use std::borrow::Cow;

use serde::Deserializer;

use crate::field::PrimeField;

use super::*;

use super::destination_view::*;
use super::evaluator::*;
use super::trace_source::*;
// We need a type to save a set of gate evaluators
// into verification keys. We need some dynamic progamming (without type IDs!) for it,
// and we also need to somehow construct it in a fully dynamic environment where
// the only thing provided from outside would be some "factory" of all known gate deserializers

// so we need two things:
// - first is an "in-verifier" evaluator, the same way as we did before
// - second is a special constuctor, that can dynamically construct such an evaluator by having access
// only to it's `dyn` wrapper

// To avoid too much pain with manual serde layers, we just decide to use bincode here

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
pub struct EvaluatorBinaryData<F: PrimeField> {
    pub(crate) type_name: Cow<'static, str>,
    #[derivative(Debug = "ignore")]
    pub(crate) parameters_data: Vec<u8>,
    #[serde(skip)]
    _marker: std::marker::PhantomData<F>,
}

impl<F: PrimeField> EvaluatorBinaryData<F> {
    pub fn from_evaluator<E: GateConstraintEvaluator<F>>(evaluator: &E) -> Self {
        let params = evaluator.unique_params();
        let encoding = bincode::serialize(&params).expect("must serialize");
        Self {
            type_name: E::type_name(),
            parameters_data: encoding,
            _marker: std::marker::PhantomData,
        }
    }
}

/// This is a type to try to construct parametric gate instance
#[derive(Derivative)]
#[derivative(Debug, Hash, PartialEq, Eq)]
pub struct GateDeserializationFunction<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
    S: TraceSourceDerivable<F, P>,
    D: EvaluationDestinationDrivable<F, P>,
> {
    pub type_name: String,
    #[derivative(Debug = "ignore")]
    #[derivative(Hash = "ignore")]
    #[derivative(PartialEq = "ignore")]
    pub construction_function: Box<
        dyn Fn(&[u8], &CSGeometry) -> Option<VerifierGateEvaluationFunction<F, P, S, D>>
            + 'static
            + Send
            + Sync,
    >,
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSourceDerivable<F, P>,
        D: EvaluationDestinationDrivable<F, P>,
    > GateDeserializationFunction<F, P, S, D>
{
    pub fn construct_for_evaluator<E: GateConstraintEvaluator<F>>() -> Self {
        let type_name = E::type_name().to_string();

        let construction_function = move |params_data: &[u8], geometry: &CSGeometry| {
            let evaluator_params =
                bincode::deserialize::<E::UniqueParameterizationParams>(params_data);
            if evaluator_params.is_err() {
                return None;
            }

            let evaluator_params = evaluator_params.unwrap();
            let evaluator = VerifierGateEvaluationFunction::new::<E>(geometry, evaluator_params);

            Some(evaluator)
        };

        let new = Self {
            type_name,
            construction_function: Box::new(construction_function),
        };

        new
    }
}

// Now we can define a structure that will do type erasure,
// so we can construct it from some serialized verifier
#[derive(Derivative)]
#[derivative(Debug)]
pub struct VerifierGateEvaluationFunction<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
    S: TraceSourceDerivable<F, P>,
    D: EvaluationDestinationDrivable<F, P>,
> {
    pub debug_name: String,
    pub gate_purpose: GatePurpose,
    pub max_constraint_degree: usize,
    pub num_quotient_terms: usize,
    pub total_quotient_terms_in_geometry: usize,
    num_repetitions_on_row: usize,
    pub placement_type: GatePlacementType,

    #[derivative(Debug = "ignore")]
    pub evaluation_fn: Box<dyn Fn(S, &mut D, usize, &mut P::Context) -> () + 'static + Send + Sync>,
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSourceDerivable<F, P>,
        D: EvaluationDestinationDrivable<F, P>,
    > VerifierGateEvaluationFunction<F, P, S, D>
{
    pub(crate) fn new<E: GateConstraintEvaluator<F>>(
        geometry: &CSGeometry,
        evaluator_params: E::UniqueParameterizationParams,
    ) -> Self {
        let evaluator = E::new_from_parameters(evaluator_params);
        let debug_name = evaluator.instance_name();
        let gate_purpose = E::gate_purpose();
        let max_constraint_degree = E::max_constraint_degree();
        let num_quotient_terms = E::num_quotient_terms();
        let total_quotient_terms_in_geometry = evaluator.total_quotient_terms_in_geometry(geometry);
        let num_repetitions_on_row = evaluator.num_repetitions_in_geometry(geometry);
        let placement_type = evaluator.placement_type();
        if let GatePlacementType::MultipleOnRow { .. } = &placement_type {
            debug_assert!(num_repetitions_on_row > 0);
        } else {
            debug_assert_eq!(num_repetitions_on_row, 1);
        }

        let eval_fn = move |evaluation_view: S,
                            destination: &mut D,
                            constant_placement_offset: usize,
                            ctx: &mut P::Context|
              -> () {
            let global_constants = evaluator.create_global_constants(ctx);

            let mut evaluation_view = evaluation_view;
            evaluation_view.set_constants_offset(constant_placement_offset); // renumerate constants
            let shared_constants = evaluator.load_row_shared_constants(&evaluation_view, ctx);

            evaluator.evaluate_once(
                &evaluation_view,
                destination,
                &shared_constants,
                &global_constants,
                ctx,
            );
        };

        let new = Self {
            debug_name,
            gate_purpose,
            max_constraint_degree,
            num_quotient_terms,
            total_quotient_terms_in_geometry,
            num_repetitions_on_row,
            placement_type,
            evaluation_fn: Box::new(eval_fn),
        };

        new
    }
}

pub struct EvaluatorsFactory<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLike<Base = F>,
    S: TraceSourceDerivable<F, P>,
    D: EvaluationDestinationDrivable<F, P>,
> {
    pub(crate) constructor_functions: Vec<GateDeserializationFunction<F, P, S, D>>,
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSourceDerivable<F, P>,
        D: EvaluationDestinationDrivable<F, P>,
    > EvaluatorsFactory<F, P, S, D>
{
    pub fn add_constructor(&mut self, constructor: GateDeserializationFunction<F, P, S, D>) {
        if self
            .constructor_functions
            .iter()
            .position(|el| &constructor.type_name == &el.type_name)
            .is_some()
        {
            panic!("Duplicate constructor for type {}", constructor.type_name);
        }

        self.constructor_functions.push(constructor);
    }

    pub fn try_construct<'de, DE: Deserializer<'de>>(
        &self,
        deserializer: DE,
        geometry: &CSGeometry,
    ) -> Option<VerifierGateEvaluationFunction<F, P, S, D>> {
        use serde::Deserialize;

        let binary_data = EvaluatorBinaryData::<F>::deserialize(deserializer);
        if binary_data.is_err() {
            return None;
        }

        let binary_data = binary_data.unwrap();

        let mut found = None;
        for el in self.constructor_functions.iter() {
            if el.type_name == binary_data.type_name {
                found = Some(el);
                break;
            }
        }

        let found = found?;

        let constructed = (found.construction_function)(&binary_data.parameters_data, geometry);

        constructed
    }

    pub fn new() -> Self {
        Self {
            constructor_functions: vec![],
        }
    }
}

// now we need macro (or a few) to construct `EvaluatorsFactory` from the list of type names

#[macro_export]
macro_rules! declare_gates {
    ($( $target:ident ),+) => {
        {
            let mut factory = EvaluatorsFactory::new();
            $(
                {
                    let _e = GateDeserializationFunction::construct_for_evaluator::<$target>();
                    factory.add_constructor(_e);
                }
            )+

            factory
        }
    };
}

// #[allow(dead_code)]
// fn test_fn<
//     F: PrimeField,
//     P: field::traits::field_like::PrimeFieldLike<Base = F>,
//     S: TraceSourceDerivable<F, P>,
//     D: EvaluationDestinationDrivable<F, P>,
// >() -> EvaluatorsFactory<F, P, S, D> {
//     use crate::cs::gates::boolean_allocator::BooleanAllocatorConstraitEvaluator;
//     use crate::cs::gates::unbounded_constant_allocator::UnboundedConstantAllocatorConstraintEvaluator;

//     let factory: EvaluatorsFactory<_, _, _, _> = declare_gates!(
//         BooleanAllocatorConstraitEvaluator,
//         UnboundedConstantAllocatorConstraintEvaluator
//     );

//     factory
// }

// #[cfg(test)]
// mod test {
//     use super::*;
//     use crate::cs::gates::boolean_allocator::*;
//     use crate::cs::gates::unbounded_constant_allocator::*;

//     use crate::cs::implementations::verifier::VerifierPolyStorage;
//     use crate::cs::implementations::verifier::VerifierRelationDestination;
//     use crate::field::goldilocks::GoldilocksField;

//     type F = GoldilocksField;

//     #[test]
//     fn check_serialize() {
//         let evaluator = BooleanAllocatorConstraitEvaluator;
//         let evaluator_data = EvaluatorBinaryData::<F>::from_evaluator(&evaluator);
//         let as_string = serde_json::to_string(&evaluator_data).unwrap();

//         dbg!(&as_string);

//         let string_bytes = as_string.as_bytes();

//         let geometry = CSGeometry {
//             num_columns_under_copy_permutation: 8,
//             num_witness_columns: 0,
//             num_constant_columns: 3,
//             max_allowed_constraint_degree: 4,
//             lookup_parameters: LookupParameters::NoLookup,
//         };

//         // let data = EvaluatorData::<F, BooleanAllocatorConstraitEvaluator>::deserialize(&mut deserializer);
//         // dbg!(&data);

//         let mut deserializer = serde_json::Deserializer::from_reader(string_bytes);

//         let factory: EvaluatorsFactory<F, F, VerifierPolyStorage<F>, VerifierRelationDestination<F>> = declare_gates!(
//             BooleanAllocatorConstraitEvaluator,
//             UnboundedConstantAllocatorConstraintEvaluator
//         );

//         let evaluator = factory.try_construct(
//             &mut deserializer,
//             &geometry
//         );
//         dbg!(&evaluator);
//     }
// }
