use super::*;
use crate::algebraic_props::round_function::AlgebraicRoundFunction;
use crate::algebraic_props::sponge::GenericAlgebraicSpongeState;
use crate::config::*;
use crate::cs::traits::cs::*;
use crate::cs::Variable;
use crate::gadgets::boolean::Boolean;
use crate::gadgets::num::Num;
use crate::gadgets::traits::round_function::CircuitRoundFunction;

pub fn simulate_round_function<
    F: SmallField,
    CS: ConstraintSystem<F>,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    R: CircuitRoundFunction<F, AW, SW, CW> + AlgebraicRoundFunction<F, AW, SW, CW>,
>(
    cs: &mut CS,
    state: [Variable; SW],
    execute: Boolean<F>,
) -> [Variable; SW] {
    // create result
    let result = cs.alloc_multiple_variables_without_values::<SW>();

    if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
        let mut dependencies = Vec::with_capacity(SW + 1);
        dependencies.push(execute.get_variable().into());
        dependencies.extend(Place::from_variables(state));

        cs.set_values_with_dependencies_vararg(
            &dependencies,
            &Place::from_variables(result),
            move |ins: &[F], outs: &mut DstBuffer<'_, '_, F>| {
                use crate::gadgets::traits::castable::WitnessCastable;
                let should_run: bool = WitnessCastable::cast_from_source([ins[0]]);

                if should_run == false {
                    outs.extend([F::ZERO; SW]);
                    return;
                }

                let mut state = [F::ZERO; SW];
                state.copy_from_slice(&ins[1..]);
                R::round_function(&mut state);

                outs.extend(state);
            },
        );
    }

    result
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CircuitSimpleAlgebraicSponge<
    F: SmallField,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    R: CircuitRoundFunction<F, AW, SW, CW>,
    const ABSORB_BY_REPLACEMENT: bool,
> {
    pub buffer: GenericAlgebraicSpongeState<Num<F>, AW, SW, CW>,
    pub _marker: std::marker::PhantomData<R>,
}
