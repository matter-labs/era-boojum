use crate::algebraic_props::round_function::AbsorptionModeOverwrite;
use crate::algebraic_props::sponge::GenericAlgebraicSpongeState;
use crate::algebraic_props::sponge::GoldilocksPoseidon2Sponge;
use crate::cs::oracle::TreeHasher;
use crate::cs::traits::cs::ConstraintSystem;
use crate::field::goldilocks::GoldilocksField;
use crate::field::SmallField;
use crate::gadgets::boolean::Boolean;
use crate::gadgets::num::Num;
use crate::gadgets::traits::allocatable::CSAllocatable;
use crate::gadgets::traits::encodable::CircuitVarLengthEncodable;
use crate::gadgets::traits::round_function::CircuitRoundFunction;
use crate::implementations::poseidon2::Poseidon2Goldilocks;

pub trait CircuitTreeHasher<F: SmallField, B: Sized + CSAllocatable<F>>:
    'static + Clone + Send + Sync
{
    type CircuitOutput: Sized
        + 'static
        + Clone
        + Copy
        + Sync
        + Send
        + PartialEq
        + Eq
        + std::fmt::Debug
        + CSAllocatable<F>
        + CircuitVarLengthEncodable<F>;

    fn new<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self;
    fn placeholder_output<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self::CircuitOutput;
    fn accumulate_into_leaf<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, value: &B);
    fn finalize_into_leaf_hash_and_reset<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
    ) -> Self::CircuitOutput;
    fn hash_into_leaf<'a, S: IntoIterator<Item = &'a B>, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        source: S,
    ) -> Self::CircuitOutput
    where
        B: 'a;
    fn hash_into_leaf_owned<S: IntoIterator<Item = B>, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        source: S,
    ) -> Self::CircuitOutput;
    fn swap_nodes<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        should_swap: Boolean<F>,
        left: &Self::CircuitOutput,
        right: &Self::CircuitOutput,
        depth: usize,
    ) -> (Self::CircuitOutput, Self::CircuitOutput);
    fn hash_into_node<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        left: &Self::CircuitOutput,
        right: &Self::CircuitOutput,
        depth: usize,
    ) -> Self::CircuitOutput;
    fn select_cap_node<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        cap_bits: &[Boolean<F>],
        cap: &[Self::CircuitOutput],
    ) -> Self::CircuitOutput;
    fn compare_output<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: &Self::CircuitOutput,
        b: &Self::CircuitOutput,
    ) -> Boolean<F>;
}

// pub trait RecursiveTreeHasher<
//     F: SmallField,
//     B: Sized + CSAllocatable<F>,
// >: TreeHasher<B::Witness> {
//     type CircuitReflection: CircuitTreeHasher<F, B, CircuitOutput::Witness = Self::Output>;
// }

pub trait RecursiveTreeHasher<F: SmallField, B: Sized + CSAllocatable<F>>:
    CircuitTreeHasher<F, B>
{
    type NonCircuitSimulator: TreeHasher<
        <B as CSAllocatable<F>>::Witness,
        Output = <<Self as CircuitTreeHasher<F, B>>::CircuitOutput as CSAllocatable<F>>::Witness,
    >;
}

use crate::gadgets::round_function::CircuitSimpleAlgebraicSponge;

impl<
        F: SmallField,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        R: CircuitRoundFunction<F, AW, SW, CW>,
        const ABSORB_BY_REPLACEMENT: bool,
    > CircuitTreeHasher<F, Num<F>>
    for CircuitSimpleAlgebraicSponge<F, AW, SW, CW, R, ABSORB_BY_REPLACEMENT>
{
    type CircuitOutput = [Num<F>; 4];

    fn new<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let filler = Num::zero(cs);
        let buffer = GenericAlgebraicSpongeState::empty_from_filler(filler);

        Self {
            buffer,
            _marker: std::marker::PhantomData,
        }
    }
    fn placeholder_output<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self::CircuitOutput {
        let zero_num = Num::zero(cs);

        [zero_num; 4]
    }
    fn accumulate_into_leaf<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS, value: &Num<F>) {
        assert!(
            ABSORB_BY_REPLACEMENT == true,
            "unimplemented for other absorbtion modes"
        );
        self.buffer.buffer[self.buffer.filled] = *value;
        self.buffer.filled += 1;
        if self.buffer.filled == AW {
            for (dst, src) in self.buffer.state[..AW]
                .iter_mut()
                .zip(self.buffer.buffer[..self.buffer.filled].iter())
            {
                *dst = *src;
            }

            self.buffer.state = R::compute_round_function_over_nums(cs, self.buffer.state);
            self.buffer.filled = 0;
        }
    }
    fn finalize_into_leaf_hash_and_reset<CS: ConstraintSystem<F>>(
        &mut self,
        cs: &mut CS,
    ) -> Self::CircuitOutput {
        // reset
        let zero_num = Num::zero(cs);
        let mut state = std::mem::replace(&mut self.buffer.state, [zero_num; SW]);
        let filled = self.buffer.filled;
        self.buffer.filled = 0;

        // run round function if necessary
        if filled > 0 {
            for (dst, src) in state[..filled]
                .iter_mut()
                .zip(self.buffer.buffer[..filled].iter())
            {
                *dst = *src;
            }

            for dst in state[filled..AW].iter_mut() {
                *dst = zero_num;
            }

            state = R::compute_round_function_over_nums(cs, state);
        }

        R::state_into_commitment::<4>(&state.map(|el| el.get_variable()))
            .map(|el| Num::from_variable(el))
    }
    fn hash_into_leaf<'a, S: IntoIterator<Item = &'a Num<F>>, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        source: S,
    ) -> Self::CircuitOutput
    where
        Num<F>: 'a,
    {
        let mut hasher = Self::new(cs);

        for el in source.into_iter() {
            <Self as CircuitTreeHasher<F, Num<F>>>::accumulate_into_leaf(&mut hasher, cs, el);
        }

        let leaf_hash = <Self as CircuitTreeHasher<F, Num<F>>>::finalize_into_leaf_hash_and_reset(
            &mut hasher,
            cs,
        );

        leaf_hash
    }
    fn hash_into_leaf_owned<S: IntoIterator<Item = Num<F>>, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        source: S,
    ) -> Self::CircuitOutput {
        let mut hasher = Self::new(cs);

        for el in source.into_iter() {
            <Self as CircuitTreeHasher<F, Num<F>>>::accumulate_into_leaf(&mut hasher, cs, &el);
        }

        <Self as CircuitTreeHasher<F, Num<F>>>::finalize_into_leaf_hash_and_reset(&mut hasher, cs)
    }
    fn swap_nodes<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        should_swap: Boolean<F>,
        left: &Self::CircuitOutput,
        right: &Self::CircuitOutput,
        _depth: usize,
    ) -> (Self::CircuitOutput, Self::CircuitOutput) {
        let (new_left, new_right) = Num::conditionally_swap_multiple(cs, should_swap, left, right);

        (new_left, new_right)
    }
    fn hash_into_node<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        left: &Self::CircuitOutput,
        right: &Self::CircuitOutput,
        _depth: usize,
    ) -> Self::CircuitOutput {
        let mut hasher = Self::new(cs);

        for el in left {
            <Self as CircuitTreeHasher<F, Num<F>>>::accumulate_into_leaf(&mut hasher, cs, el);
        }
        for el in right {
            <Self as CircuitTreeHasher<F, Num<F>>>::accumulate_into_leaf(&mut hasher, cs, el);
        }

        let node_hash = <Self as CircuitTreeHasher<F, Num<F>>>::finalize_into_leaf_hash_and_reset(
            &mut hasher,
            cs,
        );

        node_hash
    }
    fn select_cap_node<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        cap_bits: &[Boolean<F>],
        cap: &[Self::CircuitOutput],
    ) -> Self::CircuitOutput {
        use crate::gadgets::recursion::recursive_verifier::binary_select;

        binary_select(cs, cap, cap_bits)
    }
    fn compare_output<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a: &Self::CircuitOutput,
        b: &Self::CircuitOutput,
    ) -> Boolean<F> {
        let equalities: [_; 4] = std::array::from_fn(|idx| Num::equals(cs, &a[idx], &b[idx]));

        Boolean::multi_and(cs, &equalities)
    }
}

pub type CircuitGoldilocksPoseidon2Sponge =
    CircuitSimpleAlgebraicSponge<GoldilocksField, 8, 12, 4, Poseidon2Goldilocks, true>;

impl RecursiveTreeHasher<GoldilocksField, Num<GoldilocksField>>
    for CircuitGoldilocksPoseidon2Sponge
{
    type NonCircuitSimulator = GoldilocksPoseidon2Sponge<AbsorptionModeOverwrite>;
}
