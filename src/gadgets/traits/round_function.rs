use super::*;
use crate::cs::traits::cs::*;
use crate::cs::traits::gate::GatePlacementStrategy;
use crate::gadgets::num::Num;
use crate::gadgets::traits::round_function::gates::*;

pub trait CircuitRoundFunction<F: SmallField, const AW: usize, const SW: usize, const CW: usize>:
    'static + Send + Sync + Clone
{
    fn create_empty_state<CS: ConstraintSystem<F>>(cs: &mut CS) -> [Variable; SW] {
        let zero = cs.allocate_constant(F::ZERO);

        [zero; SW]
    }

    fn split_capacity_elements(state: &[Variable; SW]) -> [Variable; CW] {
        let mut tmp = [Variable::placeholder(); CW];
        tmp.copy_from_slice(&state[AW..]);

        assert_no_placeholder_variables(&tmp);

        tmp
    }

    fn apply_length_specialization<CS: ConstraintSystem<F>>(
        _cs: &mut CS,
        state: &mut [Variable; SW],
        length: Variable,
    ) {
        state[SW - 1] = length;
    }

    fn compute_round_function<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        state: [Variable; SW],
    ) -> [Variable; SW];

    /// Absorb elements into state and DOES NOT run round function (prepare for it)
    fn absorb_with_replacement<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        elements_to_absorb: [Variable; AW],
        state_elements_to_keep: [Variable; CW],
    ) -> [Variable; SW];

    #[inline]
    fn compute_round_function_over_nums<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        state: [Num<F>; SW],
    ) -> [Num<F>; SW] {
        Self::compute_round_function(cs, state.map(|el| el.variable))
            .map(|el| Num::from_variable(el))
    }

    #[inline]
    fn absorb_with_replacement_over_nums<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        elements_to_absorb: [Num<F>; AW],
        state_elements_to_keep: [Num<F>; CW],
    ) -> [Num<F>; SW] {
        Self::absorb_with_replacement(
            cs,
            elements_to_absorb.map(|el| el.variable),
            state_elements_to_keep.map(|el| el.variable),
        )
        .map(|el| Num::from_variable(el))
    }

    fn enforce_round_function<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        initial_state: [Variable; SW],
        final_state: [Variable; SW],
    );

    fn state_into_commitment<const N: usize>(state: &[Variable; SW]) -> [Variable; N] {
        assert!(N <= AW);
        assert!(N > 0);

        state[..N].try_into().expect("length must match")
    }
}

use crate::cs::cs_builder::*;
use crate::cs::*;

use crate::gadgets::traits::configuration::ConfigurationFunction;
use crate::gadgets::traits::configuration::IdentityConfiguration;

pub trait BuildableCircuitRoundFunction<
    F: SmallField,
    const AW: usize,
    const SW: usize,
    const CW: usize,
>: CircuitRoundFunction<F, AW, SW, CW>
{
    type GateConfiguration<GC: GateConfigurationHolder<F>>: GateConfigurationHolder<F>;
    type Toolbox<TB: StaticToolboxHolder>: StaticToolboxHolder;

    fn configure_builder<
        T: CsBuilderImpl<F, T>,
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
    >(
        builder: CsBuilder<T, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
    ) -> CsBuilder<T, F, Self::GateConfiguration<GC>, Self::Toolbox<TB>>;

    fn make_specialization_function_0() -> impl ConfigurationFunction<F> {
        IdentityConfiguration::new()
    }

    fn make_specialization_function_1() -> impl ConfigurationFunction<F> {
        IdentityConfiguration::new()
    }

    fn make_specialization_function_2() -> impl ConfigurationFunction<F> {
        IdentityConfiguration::new()
    }
}
