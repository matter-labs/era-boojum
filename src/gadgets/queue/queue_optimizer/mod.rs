use super::*;
use crate::config::CSWitnessEvaluationConfig;
pub mod sponge_optimizer;
pub use sponge_optimizer::*;

pub fn variable_length_hash_using_optimizer<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, AW, SW, CW> + AlgebraicRoundFunction<F, AW, SW, CW>,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    const N: usize,
    const COM_LEN: usize,
>(
    cs: &mut CS,
    input: &[Num<F>],
    id: usize,
    execute: Boolean<F>,
    optimizer: &mut SpongeOptimizer<F, R, AW, SW, CW, N>,
) -> [Num<F>; COM_LEN]
where
    [(); AW + SW + 1]:,
{
    let state =
        variable_length_hash_into_empty_state_using_optimizer(cs, input, id, execute, optimizer)
            .map(|x| x.get_variable());

    <R as CircuitRoundFunction<F, AW, SW, CW>>::state_into_commitment(&state)
        .map(|x| Num::from_variable(x))
}

pub fn variable_length_hash_into_empty_state_using_optimizer<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, AW, SW, CW> + AlgebraicRoundFunction<F, AW, SW, CW>,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    const N: usize,
>(
    cs: &mut CS,
    input: &[Num<F>],
    id: usize,
    execute: Boolean<F>,
    optimizer: &mut SpongeOptimizer<F, R, AW, SW, CW, N>,
) -> [Num<F>; SW]
where
    [(); AW + SW + 1]:,
{
    let state = R::create_empty_state(cs).map(|x| Num::from_variable(x));

    variable_length_absorb_into_state_using_optimizer(cs, input, &state, id, execute, optimizer)
}

pub fn variable_length_absorb_into_state_using_optimizer<
    F: SmallField,
    CS: ConstraintSystem<F>,
    R: CircuitRoundFunction<F, AW, SW, CW> + AlgebraicRoundFunction<F, AW, SW, CW>,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    const N: usize,
>(
    cs: &mut CS,
    input: &[Num<F>],
    into_state: &[Num<F>; SW],
    id: usize,
    execute: Boolean<F>,
    optimizer: &mut SpongeOptimizer<F, R, AW, SW, CW, N>,
) -> [Num<F>; SW]
where
    [(); AW + SW + 1]:,
{
    let len = input.len();
    let num_rounds = (len + AW - 1) / AW;

    let input_chunks = {
        let mut result = Vec::with_capacity(num_rounds);

        let it = input.array_chunks::<AW>();
        let remainder = it.remainder();

        for input_chunk in it {
            result.push(*input_chunk);
        }

        if !remainder.is_empty() {
            let num_zero = Num::zero(cs);
            let mut chunk = [num_zero; AW];

            chunk.copy_from_slice(remainder);
            result.push(chunk);
        }

        result
    };

    let mut last_state = *into_state;
    assert_eq!(input_chunks.len(), num_rounds);

    for round_id in 0..num_rounds {
        let intermediate = cs.alloc_multiple_variables_without_values::<SW>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; AW + SW + 1]| {
                if inputs[AW + SW] == F::ONE {
                    let mut state = *inputs[..SW].array_chunks::<SW>().next().unwrap();
                    let to_absorb = inputs[SW..AW + SW].array_chunks::<AW>().next().unwrap();
                    R::absorb_into_state::<AbsorptionModeOverwrite>(&mut state, to_absorb);
                    R::round_function(&mut state);
                    state
                } else {
                    [F::ZERO; SW]
                }
            };

            let mut dependencies = [Place::placeholder(); AW + SW + 1];
            dependencies[..SW]
                .copy_from_slice(&Place::from_variables(last_state.map(|x| x.get_variable()))[..]);
            dependencies[SW..AW + SW].copy_from_slice(
                &Place::from_variables(input_chunks[round_id].map(|x| x.get_variable()))[..],
            );
            dependencies[AW + SW] = Place::from_variable(execute.get_variable());

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables(intermediate),
                value_fn,
            );
        }

        let intermediate = intermediate.map(|x| Num::from_variable(x));

        let mut provably_absorbed = last_state;

        // absorb by overwriting
        for (dst, src) in provably_absorbed[..AW]
            .iter_mut()
            .zip(input_chunks[round_id].iter())
        {
            *dst = *src;
        }

        let request = SpongeRoundRequest {
            initial_state: provably_absorbed,
            claimed_final_state: intermediate,
        };

        optimizer.add_request(request, execute, id);

        last_state = intermediate;
    }

    last_state
}
