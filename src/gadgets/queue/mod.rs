use std::collections::VecDeque;
use std::sync::Arc;
use std::sync::RwLock;

use super::boolean::Boolean;
use super::num::Num;
use super::traits::allocatable::*;
use super::u32::UInt32;
use super::{traits::encodable::CircuitEncodable, traits::encodable::WitnessVarLengthEncodable, *};
use crate::algebraic_props::round_function::AbsorptionModeOverwrite;
use crate::algebraic_props::round_function::AlgebraicRoundFunction;
use crate::config::CSConfig;
use crate::cs::gates::ConstantAllocatableCS;
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::traits::cs::DstBuffer;
use crate::cs::Variable;
use crate::field::SmallField;
use crate::gadgets::traits::castable::WitnessCastable;
use crate::gadgets::traits::encodable::CircuitEncodableExt;
use crate::gadgets::traits::round_function::CircuitRoundFunction;
use crate::gadgets::traits::selectable::Selectable;
use crate::gadgets::traits::witnessable::WitnessHookable;
use cs_derive::*;

pub mod full_state_queue;
pub mod queue_optimizer;
use queue_optimizer::*;

pub struct CircuitQueue<
    F: SmallField,
    EL: CircuitEncodable<F, N>,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    const T: usize,
    const N: usize,
    R: CircuitRoundFunction<F, AW, SW, CW>,
> {
    pub head: [Num<F>; T],
    pub tail: [Num<F>; T],
    pub length: UInt32<F>,
    pub witness: Arc<CircuitQueueWitness<F, EL, T, N>>,
    _marker: std::marker::PhantomData<(F, EL, R)>,
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, Default)]
#[serde(bound = "")]
pub struct CircuitQueueRawWitness<
    F: SmallField,
    EL: CircuitEncodable<F, N>,
    const T: usize,
    const N: usize,
> {
    #[serde(bound(
        serialize = "<EL as CSAllocatable<F>>::Witness: serde::Serialize, [F; T]: serde::Serialize"
    ))]
    #[serde(bound(
        deserialize = "<EL as CSAllocatable<F>>::Witness: serde::de::DeserializeOwned, [F; T]: serde::de::DeserializeOwned"
    ))]
    pub elements: VecDeque<(EL::Witness, [F; T])>,
}

pub struct CircuitQueueWitness<
    F: SmallField,
    EL: CircuitEncodable<F, N>,
    const T: usize,
    const N: usize,
> {
    // elements and previous tails when we push
    pub elements: RwLock<VecDeque<(EL::Witness, [F; T])>>,
}

impl<F: SmallField, EL: CircuitEncodable<F, N>, const T: usize, const N: usize>
    CircuitQueueWitness<F, EL, T, N>
{
    pub fn from_inner_witness(inner: CircuitQueueRawWitness<F, EL, T, N>) -> Self {
        Self {
            elements: RwLock::new(inner.elements),
        }
    }
}

impl<F: SmallField, EL: CircuitEncodable<F, N>, const T: usize, const N: usize> Clone
    for CircuitQueueWitness<F, EL, T, N>
{
    fn clone(&self) -> Self {
        if let Ok(elements) = self.elements.read() {
            let elements = (*elements).clone();

            Self {
                elements: RwLock::new(elements),
            }
        } else {
            unreachable!()
        }
    }
}

impl<
        F: SmallField,
        EL: CircuitEncodable<F, N>,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        const T: usize,
        const N: usize,
        R: CircuitRoundFunction<F, AW, SW, CW>,
    > Clone for CircuitQueue<F, EL, AW, SW, CW, T, N, R>
{
    fn clone(&self) -> Self {
        Self {
            head: self.head,
            tail: self.tail,
            length: self.length,
            witness: Arc::clone(&self.witness),
            _marker: std::marker::PhantomData,
        }
    }
}

impl<F: SmallField, EL: CircuitEncodable<F, N>, const T: usize, const N: usize>
    CircuitQueueWitness<F, EL, T, N>
{
    pub fn empty() -> Self {
        Self {
            elements: RwLock::new(VecDeque::new()),
        }
    }

    pub fn pop_front(&self) -> (EL::Witness, [F; T]) {
        if let Ok(mut elements) = self.elements.write() {
            let el = (*elements).pop_front().expect("must not be empty");

            el
        } else {
            unreachable!()
        }
    }

    pub fn push(&self, element_witness: EL::Witness, previous_tail: [F; T]) {
        if let Ok(mut elements) = self.elements.write() {
            (*elements).push_back((element_witness, previous_tail));
        } else {
            unreachable!()
        }
    }
}

impl<
        F: SmallField,
        EL: CircuitEncodable<F, N>,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        const T: usize,
        const N: usize,
        R: CircuitRoundFunction<F, AW, SW, CW>,
    > CircuitQueue<F, EL, AW, SW, CW, T, N, R>
{
    pub fn empty<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let zero_el = Num::allocated_constant(cs, F::ZERO);
        let length = UInt32::allocated_constant(cs, 0u32);
        Self {
            head: [zero_el; T],
            tail: [zero_el; T],
            length,
            witness: Arc::new(CircuitQueueWitness::empty()),
            _marker: std::marker::PhantomData,
        }
    }

    fn push_evaluate_witness<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        encoding: [Variable; N],
        flattened_vars: [Variable; <EL as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN],
        execute: Boolean<F>,
    ) where
        EL: CircuitEncodableExt<F, N>,
    {
        // now the trick - we add values in another thread, by using "execute" and self-state values as a barrier
        use crate::config::*;
        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let mut dependencies = Vec::with_capacity(
                N + 1 + T * 2 + 1 + <EL as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN,
            );
            dependencies.extend(Place::from_variables(encoding));
            dependencies.push(execute.get_variable().into());
            dependencies.extend(Place::from_variables(self.head.map(|el| el.variable)));
            dependencies.extend(Place::from_variables(self.tail.map(|el| el.variable)));
            dependencies.push(self.length.get_variable().into());
            dependencies.extend(Place::from_variables(flattened_vars));

            let witness_storage = Arc::clone(&self.witness);

            cs.set_values_with_dependencies_vararg(
                &dependencies,
                &[],
                move |ins: &[F], _outs: &mut DstBuffer<'_, '_, F>| {
                    let offset = N + 1 + T * 2 + 1;
                    let raw_values = ins[offset..]
                        .array_chunks::<{ <EL as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN }>()
                        .next()
                        .copied()
                        .expect("must exist");
                    let witness = CSAllocatableExt::<F>::witness_from_set_of_values(raw_values);

                    let should_push: bool = WitnessCastable::cast_from_source([ins[N]]);

                    let previous_tail = ins[(N + 1)..]
                        .array_chunks::<T>()
                        .next()
                        .copied()
                        .expect("must exist");

                    if should_push {
                        CircuitQueueWitness::push(&*witness_storage, witness, previous_tail);
                    }
                },
            );
        }
    }

    pub fn push<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        element: EL,
        execute: Boolean<F>,
    ) -> [Variable; N]
    where
        EL: CircuitEncodableExt<F, N>,
        [(); <EL as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    {
        // first we need an encoding
        let encoding = element.encode(cs);
        let flattened_vars = element.flatten_as_variables();
        self.push_evaluate_witness(cs, encoding, flattened_vars, execute);

        let total_elements_to_absorb = N + T;
        let num_rounds = (total_elements_to_absorb + AW - 1) / AW;
        let mut elements_source = encoding.into_iter().chain(self.tail.map(|el| el.variable));

        let zero_element = cs.allocate_constant(F::ZERO);

        let mut capacity_elements = [zero_element; CW];

        let mut new_tail = self.tail.map(|el| el.variable);

        for _ in 0..num_rounds {
            let mut to_absorb = [zero_element; AW];
            for (dst, src) in to_absorb.iter_mut().zip(&mut elements_source) {
                *dst = src;
            }

            let result_state = R::absorb_with_replacement(cs, to_absorb, capacity_elements);
            let result_state = R::compute_round_function(cs, result_state);
            capacity_elements.copy_from_slice(&result_state[AW..]);
            new_tail.copy_from_slice(&result_state[..T]);
        }

        // update tail and length

        let one_uint32 = UInt32::allocated_constant(cs, 1u32);
        let incremented_length = self.length.add_no_overflow(cs, one_uint32);
        self.length =
            Selectable::conditionally_select(cs, execute, &incremented_length, &self.length);

        let new_tail = new_tail.map(|el| Num::from_variable(el));
        self.tail = Selectable::conditionally_select(cs, execute, &new_tail, &self.tail);

        // self.enforce_consistency(cs);

        encoding
    }

    pub fn push_with_optimizer<CS: ConstraintSystem<F>, const M: usize>(
        &mut self,
        cs: &mut CS,
        element: EL,
        execute: Boolean<F>,
        id: usize,
        optimizer: &mut SpongeOptimizer<F, R, AW, SW, CW, M>,
    ) -> [Variable; N]
    where
        R: AlgebraicRoundFunction<F, AW, SW, CW>,
        EL: CircuitEncodableExt<F, N>,
        [(); <EL as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
        [(); AW + SW + 1]:,
        [(); N + T]:,
    {
        // first we need an encoding
        let encoding = element.encode(cs);
        let flattened_vars = element.flatten_as_variables();
        self.push_evaluate_witness(cs, encoding, flattened_vars, execute);

        let mut input = smallvec::SmallVec::<[_; N + T]>::new();
        input.extend_from_slice(&encoding.map(|x| Num::from_variable(x)));
        input.extend_from_slice(&self.tail);

        let commitment = variable_length_hash_using_optimizer::<_, _, R, AW, SW, CW, M, T>(
            cs,
            &input[..],
            id,
            execute,
            optimizer,
        );

        // update tail and length

        let one_uint32 = UInt32::allocated_constant(cs, 1u32);
        let incremented_length = self.length.add_no_overflow(cs, one_uint32);
        self.length =
            Selectable::conditionally_select(cs, execute, &incremented_length, &self.length);
        self.tail = <[Num<F>; T]>::conditionally_select(cs, execute, &commitment, &self.tail);

        // self.enforce_consistency(cs);

        encoding
    }

    fn pop_evaluate_witness<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        execute: Boolean<F>,
    ) -> EL
    where
        EL: CircuitEncodableExt<F, N>,
        [(); <EL as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    {
        // allocate in some raw form
        let popped_element = EL::create_without_value(cs);

        // now we use the same trick
        use crate::config::*;
        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let internal_structure = popped_element.flatten_as_variables();
            let mut dependencies = Vec::with_capacity(1 + T * 2 + 1);
            dependencies.push(execute.get_variable().into());
            dependencies.extend(Place::from_variables(self.head.map(|el| el.variable)));
            dependencies.extend(Place::from_variables(self.tail.map(|el| el.variable)));
            dependencies.push(self.length.get_variable().into());

            let witness_storage = Arc::clone(&self.witness);

            cs.set_values_with_dependencies_vararg(
                &dependencies,
                &Place::from_variables(internal_structure),
                move |ins: &[F], outs: &mut DstBuffer<'_, '_, F>| {
                    let should_pop: bool = WitnessCastable::cast_from_source([ins[0]]);
                    let witness_element = if should_pop {
                        CircuitQueueWitness::pop_front(&*witness_storage).0
                    } else {
                        EL::placeholder_witness()
                    };

                    EL::set_internal_variables_values(witness_element, outs);
                },
            );
        }

        popped_element
    }

    pub fn pop_front<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
        execute: Boolean<F>,
    ) -> (EL, [Variable; N])
    where
        EL: CircuitEncodableExt<F, N>,
        [(); <EL as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
    {
        let popped_element = self.pop_evaluate_witness(cs, execute);

        // then continue as we push, but modify head

        let encoding = popped_element.encode(cs);

        let total_elements_to_absorb = N + T;
        let num_rounds = (total_elements_to_absorb + AW - 1) / AW;
        let mut elements_source = encoding.into_iter().chain(self.head.map(|el| el.variable));

        let zero_element = cs.allocate_constant(F::ZERO);

        let mut capacity_elements = [zero_element; CW];

        let mut new_head = self.head.map(|el| el.variable);

        for _ in 0..num_rounds {
            let mut to_absorb = [zero_element; AW];
            for (dst, src) in to_absorb.iter_mut().zip(&mut elements_source) {
                *dst = src;
            }

            let result_state = R::absorb_with_replacement(cs, to_absorb, capacity_elements);
            let result_state = R::compute_round_function(cs, result_state);
            capacity_elements.copy_from_slice(&result_state[AW..]);
            new_head.copy_from_slice(&result_state[..T]);
        }

        // update tail and length

        let one_uint32 = UInt32::allocated_constant(cs, 1u32);
        let (decremented_len, uf) = self.length.overflowing_sub(cs, one_uint32);
        uf.conditionally_enforce_false(cs, execute);

        self.length = Selectable::conditionally_select(cs, execute, &decremented_len, &self.length);

        // if we indeed pop then we need to know that there is no underflow

        let new_head = new_head.map(|el| Num::from_variable(el));
        self.head = Selectable::conditionally_select(cs, execute, &new_head, &self.head);

        // self.enforce_consistency(cs);

        (popped_element, encoding)
    }

    pub fn pop_with_optimizer<CS: ConstraintSystem<F>, const M: usize>(
        &mut self,
        cs: &mut CS,
        execute: Boolean<F>,
        id: usize,
        optimizer: &mut SpongeOptimizer<F, R, AW, SW, CW, M>,
    ) -> (EL, [Variable; N])
    where
        R: AlgebraicRoundFunction<F, AW, SW, CW>,
        EL: CircuitEncodableExt<F, N>,
        [(); <EL as CSAllocatableExt<F>>::INTERNAL_STRUCT_LEN]:,
        [(); AW + SW + 1]:,
        [(); N + T]:,
    {
        // first we need an encoding
        let popped_element = self.pop_evaluate_witness(cs, execute);
        let encoding = popped_element.encode(cs);

        let mut input = smallvec::SmallVec::<[_; N + T]>::new();
        input.extend_from_slice(&encoding.map(|x| Num::from_variable(x)));
        input.extend_from_slice(&self.head);

        let commitment = variable_length_hash_using_optimizer::<_, _, R, AW, SW, CW, M, T>(
            cs,
            &input[..],
            id,
            execute,
            optimizer,
        );

        // update tail and length

        let one_uint32 = UInt32::allocated_constant(cs, 1u32);
        let (decremented_len, uf) = self.length.overflowing_sub(cs, one_uint32);
        uf.conditionally_enforce_false(cs, execute);

        self.length = Selectable::conditionally_select(cs, execute, &decremented_len, &self.length);

        // if we indeed pop then we need to know that there is no underflow

        self.head = Selectable::conditionally_select(cs, execute, &commitment, &self.head);

        // self.enforce_consistency(cs);

        (popped_element, encoding)
    }

    pub fn from_state<CS: ConstraintSystem<F>>(cs: &mut CS, state: QueueState<F, T>) -> Self {
        Self::from_raw_parts(cs, state.head, state.tail.tail, state.tail.length)
    }

    pub fn from_raw_parts<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        head: [Num<F>; T],
        tail: [Num<F>; T],
        length: UInt32<F>,
    ) -> Self {
        let length_is_zero: Boolean<F> = length.is_zero(cs);
        let tmp_bools: [_; T] = std::array::from_fn(|i| Num::equals(cs, &head[i], &tail[i]));
        let head_is_equal_to_tail = Boolean::multi_and(cs, &tmp_bools);
        Boolean::enforce_equal(cs, &length_is_zero, &head_is_equal_to_tail);
        let new = Self {
            head,
            tail,
            length,
            witness: Arc::new(CircuitQueueWitness::empty()),
            _marker: std::marker::PhantomData,
        };

        new
    }

    pub fn is_empty<CS: ConstraintSystem<F>>(&self, cs: &mut CS) -> Boolean<F> {
        self.length.is_zero(cs)
    }

    pub fn into_state(&self) -> QueueState<F, T> {
        QueueState {
            head: self.head,
            tail: QueueTailState {
                tail: self.tail,
                length: self.length,
            },
        }
    }

    pub fn enforce_consistency<CS: ConstraintSystem<F>>(&self, cs: &mut CS) {
        let is_empty = self.length.is_zero(cs);
        for (a, b) in self.head.iter().zip(self.tail.iter()) {
            Num::conditionally_enforce_equal(cs, is_empty, a, b);
        }
    }

    pub fn enforce_trivial_head<CS: ConstraintSystem<F>>(&self, cs: &mut CS) {
        let zero_num = Num::zero(cs);
        for el in self.head.iter() {
            Num::enforce_equal(cs, el, &zero_num);
        }
    }
}

pub fn simulate_new_tail<
    F: SmallField,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    const T: usize,
    const N: usize,
    R: CircuitRoundFunction<F, AW, SW, CW> + AlgebraicRoundFunction<F, AW, SW, CW>,
    CS: ConstraintSystem<F>,
>(
    cs: &mut CS,
    element_encoding: [Variable; N],
    tail: [Variable; T],
    execute: Boolean<F>,
) -> [Variable; T] {
    // create result
    let result = cs.alloc_multiple_variables_without_values::<T>();

    use crate::config::CSWitnessEvaluationConfig;
    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
        let mut dependencies = Vec::with_capacity(N + T + 1);
        dependencies.push(execute.get_variable().into());
        dependencies.extend(Place::from_variables(tail));
        dependencies.extend(Place::from_variables(element_encoding));

        cs.set_values_with_dependencies_vararg(
            &dependencies,
            &Place::from_variables(result),
            move |ins: &[F], outs: &mut DstBuffer<'_, '_, F>| {
                let should_push: bool = WitnessCastable::cast_from_source([ins[0]]);

                if should_push == false {
                    outs.extend([F::ZERO; T]);
                    return;
                }

                let num_rounds = (N + T + AW - 1) / AW;
                let mut elements_source = ins[1..].iter();

                let mut current_state = [F::ZERO; SW];

                for _ in 0..num_rounds {
                    let mut to_absorb = [F::ZERO; AW];
                    for (dst, src) in to_absorb.iter_mut().zip(&mut elements_source) {
                        *dst = *src;
                    }

                    R::absorb_into_state::<AbsorptionModeOverwrite>(&mut current_state, &to_absorb);
                    R::round_function(&mut current_state);
                }

                let new_tail = <R as AlgebraicRoundFunction<F, AW, SW, CW>>::state_into_commitment::<T>(&current_state);
                // push new tail
                outs.extend(new_tail);
            },
        );
    }

    result
}

use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;
use crate::serde_utils::BigArraySerde;

#[derive(
    Derivative,
    CSAllocatable,
    CSSelectable,
    CSVarLengthEncodable,
    WitVarLengthEncodable,
    WitnessHookable,
)]
#[derivative(Clone, Copy, Debug)]
pub struct QueueState<F: SmallField, const N: usize> {
    pub head: [Num<F>; N],
    pub tail: QueueTailState<F, N>,
}

#[derive(
    Derivative,
    CSAllocatable,
    CSSelectable,
    CSVarLengthEncodable,
    WitVarLengthEncodable,
    WitnessHookable,
)]
#[derivative(Clone, Copy, Debug)]
pub struct QueueTailState<F: SmallField, const N: usize> {
    pub tail: [Num<F>; N],
    pub length: UInt32<F>,
}

impl<F: SmallField, const N: usize> CSPlaceholder<F> for QueueTailState<F, N> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::empty(cs)
    }
}

impl<F: SmallField, const N: usize> QueueTailState<F, N> {
    pub fn empty<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let zero_u32 = UInt32::zero(cs);
        let zero_num = Num::zero(cs);
        Self {
            tail: [zero_num; N],
            length: zero_u32,
        }
    }
}

impl<F: SmallField, const N: usize> CSPlaceholder<F> for QueueState<F, N> {
    fn placeholder<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        Self::empty(cs)
    }
}

impl<F: SmallField, const N: usize> QueueState<F, N> {
    pub fn empty<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let zero_num = Num::zero(cs);
        let empty_tail = QueueTailState::empty(cs);
        Self {
            head: [zero_num; N],
            tail: empty_tail,
        }
    }

    pub fn enforce_trivial_head<CS: ConstraintSystem<F>>(&self, cs: &mut CS) {
        let zero_num = Num::zero(cs);
        for el in self.head.iter() {
            Num::enforce_equal(cs, el, &zero_num);
        }
    }

    pub fn enforce_consistency<CS: ConstraintSystem<F>>(&self, cs: &mut CS) {
        let is_empty = self.tail.length.is_zero(cs);
        for (a, b) in self.head.iter().zip(self.tail.tail.iter()) {
            Num::conditionally_enforce_equal(cs, is_empty, a, b);
        }
    }
}

impl<
        F: SmallField,
        EL: CircuitEncodable<F, N>,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        const T: usize,
        const N: usize,
        R: CircuitRoundFunction<F, AW, SW, CW>,
    > PartialEq for CircuitQueue<F, EL, AW, SW, CW, T, N, R>
{
    fn eq(&self, other: &Self) -> bool {
        self.length.eq(&other.length) && self.head.eq(&other.head) && self.tail.eq(&other.tail)
    }
}
