use super::*;
use crate::{
    algebraic_props::poseidon_parameters::{MatrixParameters, PoseidonParameters},
    cs::{
        cs_builder::{CsBuilder, CsBuilderImpl},
        toolboxes::gate_config::GatePlacementStrategy,
    },
};

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PoseidonRoundFunctionFlattenedEvaluator<
    F: SmallField,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    PAR: PoseidonParameters<F, AW, SW, CW>,
> {
    num_copiable_columns_used: usize,
    num_witness_columns_used: usize,
    _marker: std::marker::PhantomData<(F, PAR)>,
}

impl<
        F: SmallField,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        PAR: PoseidonParameters<F, AW, SW, CW>,
    > GateConstraintEvaluator<F> for PoseidonRoundFunctionFlattenedEvaluator<F, AW, SW, CW, PAR>
where
    [(); SW - 1]:,
    [(); PAR::NUM_ROUNDS]:,
    [(); PAR::NUM_PARTIAL_ROUNDS]:,
{
    type UniqueParameterizationParams = (usize, usize);

    #[inline(always)]
    fn new_from_parameters(params: Self::UniqueParameterizationParams) -> Self {
        Self {
            num_copiable_columns_used: params.0,
            num_witness_columns_used: params.1,
            _marker: std::marker::PhantomData,
        }
    }

    #[inline(always)]
    fn unique_params(&self) -> Self::UniqueParameterizationParams {
        (
            self.num_copiable_columns_used,
            self.num_witness_columns_used,
        )
    }

    #[inline]
    fn type_name() -> std::borrow::Cow<'static, str> {
        Cow::Borrowed(std::any::type_name::<Self>())
    }

    #[inline]
    fn instance_width(&self) -> GatePrincipalInstanceWidth {
        GatePrincipalInstanceWidth {
            num_variables: self.num_copiable_columns_used,
            num_witnesses: self.num_witness_columns_used,
            num_constants: 0,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: PAR::NONLINEARITY_DEGREE,
            num_quotient_terms: Self::num_terms(),
        }
    }

    #[inline]
    fn placement_type(&self) -> GatePlacementType {
        GatePlacementType::MultipleOnRow {
            per_chunk_offset: PerChunkOffset {
                variables_offset: self.num_copiable_columns_used,
                witnesses_offset: self.num_witness_columns_used,
                constants_offset: 0,
            },
        }
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, geometry: &CSGeometry) -> usize {
        debug_assert!(
            geometry.num_columns_under_copy_permutation
                >= Self::min_num_required_copiable_variables()
        );

        debug_assert!(
            geometry.num_columns_under_copy_permutation >= self.num_copiable_columns_used
        );
        debug_assert!(geometry.num_witness_columns >= self.num_witness_columns_used);

        let limit_by_copiable =
            geometry.num_columns_under_copy_permutation / self.num_copiable_columns_used;
        let limit_by_witness = if self.num_witness_columns_used == 0 {
            usize::MAX
        } else {
            geometry.num_witness_columns / self.num_witness_columns_used
        };

        std::cmp::min(limit_by_copiable, limit_by_witness)
    }

    #[inline]
    fn num_required_constants_in_geometry(&self, _geometry: &CSGeometry) -> usize {
        0
    }

    // we load MDS and round constants
    type GlobalConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = (
        [[P; SW]; SW],
        [[P; SW]; PAR::NUM_ROUNDS],
        [P; SW],
        [[P; SW]; SW],
        [P; PAR::NUM_PARTIAL_ROUNDS],
        [[P; SW - 1]; PAR::NUM_PARTIAL_ROUNDS],
        [[P; SW - 1]; PAR::NUM_PARTIAL_ROUNDS],
    );

    #[inline(always)]
    fn create_global_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>>(
        &self,
        ctx: &mut P::Context,
    ) -> Self::GlobalConstants<P> {
        let mds_matrix = PAR::MdsMatrixParams::COEFFS.map(|row| row.map(|el| P::constant(el, ctx)));
        let mut round_constants = [[P::zero(ctx); SW]; PAR::NUM_ROUNDS];
        for (src, dst) in PAR::all_round_constants()
            .iter()
            .zip(round_constants.iter_mut())
        {
            *dst = (*src).map(|el| P::constant(el, ctx));
        }

        let last_full_first_partial_rounds_merged_constants =
            PAR::ROUND_CONSTANTS_FUZED_LAST_FULL_AND_FIRST_PARTIAL.map(|el| P::constant(el, ctx));
        let last_full_first_partial_dense_matrix =
            PAR::FUZED_DENSE_MATRIX_LAST_FULL_AND_FIRST_PARTIAL
                .map(|row| row.map(|el| P::constant(el, ctx)));
        let mut fuzed_round_constants_for_partial_rounds = [P::zero(ctx); PAR::NUM_PARTIAL_ROUNDS];
        for (src, dst) in PAR::fuzed_round_constants_for_partial_rounds()
            .iter()
            .zip(fuzed_round_constants_for_partial_rounds.iter_mut())
        {
            *dst = P::constant(*src, ctx);
        }

        let mut vs_for_partial_rounds = [[P::zero(ctx); SW - 1]; PAR::NUM_PARTIAL_ROUNDS];
        for (src, dst) in PAR::vs_for_partial_rounds()
            .iter()
            .zip(vs_for_partial_rounds.iter_mut())
        {
            for (src, dst) in src[1..].iter().zip(dst.iter_mut()) {
                *dst = P::constant(*src, ctx);
            }
        }

        let mut w_hats_for_partial_rounds = [[P::zero(ctx); SW - 1]; PAR::NUM_PARTIAL_ROUNDS];
        for (src, dst) in PAR::w_hats_for_partial_rounds()
            .iter()
            .zip(w_hats_for_partial_rounds.iter_mut())
        {
            for (src, dst) in src[1..].iter().zip(dst.iter_mut()) {
                *dst = P::constant(*src, ctx);
            }
        }

        (
            mds_matrix,
            round_constants,
            last_full_first_partial_rounds_merged_constants,
            last_full_first_partial_dense_matrix,
            fuzed_round_constants_for_partial_rounds,
            vs_for_partial_rounds,
            w_hats_for_partial_rounds,
        )
    }

    type RowSharedConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = ();

    #[inline(always)]
    fn load_row_shared_constants<
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSource<F, P>,
    >(
        &self,
        _trace_source: &S,
        _ctx: &mut P::Context,
    ) -> Self::RowSharedConstants<P> {
    }

    #[inline(always)]
    fn evaluate_once<
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSource<F, P>,
        D: EvaluationDestination<F, P>,
    >(
        &self,
        trace_source: &S,
        destination: &mut D,
        _shared_constants: &Self::RowSharedConstants<P>,
        global_constants: &Self::GlobalConstants<P>,
        ctx: &mut P::Context,
    ) {
        let (
            mds_matrix,
            round_constants,
            last_full_first_partial_rounds_merged_constants,
            last_full_first_partial_dense_matrix,
            fuzed_round_constants_for_partial_rounds,
            vs_for_partial_rounds,
            w_hats_for_partial_rounds,
        ) = global_constants;

        let mut state: [P; SW] = std::array::from_fn(|idx| trace_source.get_variable_value(idx));

        // full rounds are like
        // apply_round_constants(state, *round_counter);
        // for i in 0..12 {
        //     apply_non_linearity(&mut state[i]);
        // }
        // mds_mul_naive(state);

        // and we merge multiplication by MDS with addition of round constants everywhere, but on the last full round

        let mut copiable_var_offset = SW;
        // we place output early

        let output: [P; SW] =
            std::array::from_fn(|idx| trace_source.get_variable_value(copiable_var_offset + idx));
        copiable_var_offset += SW;

        let mut witness_offset = 0;

        // we try to first use witness columns, and then use copiable. Limits are determined by the gate
        // that creates this evaluator

        for round in 0..(PAR::HALF_NUM_FULL_ROUNDS - 1) {
            // we try to first use witness columns, and then use copiable. Limits are determined by the gate
            // that creates this evaluator

            if round != 0 {
                // we "reset" the degree
                for (_idx, dst) in state.iter_mut().enumerate() {
                    let sbox_out_var = if witness_offset < self.num_witness_columns_used {
                        let var = trace_source.get_witness_value(witness_offset);
                        witness_offset += 1;

                        var
                    } else {
                        debug_assert!(copiable_var_offset < self.num_copiable_columns_used);
                        let var = trace_source.get_variable_value(copiable_var_offset);
                        copiable_var_offset += 1;

                        var
                    };

                    let mut contribution = *dst;
                    contribution.sub_assign(&sbox_out_var, ctx);

                    destination.push_evaluation_result(contribution, ctx);

                    *dst = sbox_out_var;
                }
            }

            for (idx, dst) in state.iter_mut().enumerate() {
                // add constants and do s_box
                dst.add_assign(&round_constants[round][idx], ctx);
                dst.small_pow(PAR::NONLINEARITY_DEGREE, ctx);
            }

            // do MDS

            let old_state = state;
            for (i, dst) in state.iter_mut().enumerate() {
                let mut tmp = P::zero(ctx);
                for (src, coeff) in old_state.iter().zip(mds_matrix[i].iter()) {
                    P::mul_and_accumulate_into(&mut tmp, src, coeff, ctx);
                }

                *dst = tmp;
            }
        }

        // still S-box
        {
            let round = PAR::HALF_NUM_FULL_ROUNDS - 1;
            // we "reset" the degree
            for (_idx, dst) in state.iter_mut().enumerate() {
                let sbox_out_var = if witness_offset < self.num_witness_columns_used {
                    let var = trace_source.get_witness_value(witness_offset);
                    witness_offset += 1;

                    var
                } else {
                    debug_assert!(copiable_var_offset < self.num_copiable_columns_used);
                    let var = trace_source.get_variable_value(copiable_var_offset);
                    copiable_var_offset += 1;

                    var
                };

                let mut contribution = *dst;
                contribution.sub_assign(&sbox_out_var, ctx);

                destination.push_evaluation_result(contribution, ctx);

                *dst = sbox_out_var;
            }

            for (idx, dst) in state.iter_mut().enumerate() {
                // add constants and do s_box
                dst.add_assign(&round_constants[round][idx], ctx);
                dst.small_pow(PAR::NONLINEARITY_DEGREE, ctx);
            }
        }

        // last partial round is special, because we can utilize another multiplication after s-box
        for (dst, src) in state
            .iter_mut()
            .zip(last_full_first_partial_rounds_merged_constants.iter())
        {
            dst.add_assign(src, ctx);
        }
        let old_state = state;
        for (i, dst) in state.iter_mut().enumerate() {
            let mut tmp = P::zero(ctx);
            for (src, coeff) in old_state
                .iter()
                .zip(last_full_first_partial_dense_matrix[i].iter())
            {
                P::mul_and_accumulate_into(&mut tmp, src, coeff, ctx);
            }

            *dst = tmp;
        }

        // partial rounds
        for round in 0..PAR::NUM_PARTIAL_ROUNDS {
            // partial s-box reset degree
            {
                let sbox_out_var = if witness_offset < self.num_witness_columns_used {
                    let var = trace_source.get_witness_value(witness_offset);
                    witness_offset += 1;

                    var
                } else {
                    debug_assert!(copiable_var_offset < self.num_copiable_columns_used);
                    let var = trace_source.get_variable_value(copiable_var_offset);
                    copiable_var_offset += 1;

                    var
                };

                let mut contribution = state[0];
                contribution.sub_assign(&sbox_out_var, ctx);

                destination.push_evaluation_result(contribution, ctx);

                // partial s-box itself, with constant
                let mut tmp = sbox_out_var;
                tmp.small_pow(PAR::NONLINEARITY_DEGREE, ctx);
                tmp.add_assign(&fuzed_round_constants_for_partial_rounds[round], ctx);

                state[0] = tmp;
            }

            // optimized MDS

            let original_s0 = state[0];

            let mut new_state0 = original_s0;

            for (src, coeff) in state[1..].iter().zip(vs_for_partial_rounds[round].iter()) {
                P::mul_and_accumulate_into(&mut new_state0, src, coeff, ctx);
            }

            state[0] = new_state0;

            for (dst, coeff) in state[1..]
                .iter_mut()
                .zip(w_hats_for_partial_rounds[round].iter())
            {
                P::mul_and_accumulate_into(dst, &original_s0, coeff, ctx);
            }
        }

        // finish with full rounds

        let round_counter = PAR::HALF_NUM_FULL_ROUNDS + PAR::NUM_PARTIAL_ROUNDS;

        for round_idx in 0..PAR::HALF_NUM_FULL_ROUNDS {
            // we try to first use witness columns, and then use copiable. Limits are determined by the gate
            // that creates this evaluator

            let round = round_counter + round_idx;

            {
                // we "reset" the degree for all elements because MDS had mixed high-degree
                // state[0] into all other elements
                for (_idx, dst) in state.iter_mut().enumerate() {
                    let sbox_out_var = if witness_offset < self.num_witness_columns_used {
                        let var = trace_source.get_witness_value(witness_offset);
                        witness_offset += 1;

                        var
                    } else {
                        debug_assert!(copiable_var_offset < self.num_copiable_columns_used);
                        let var = trace_source.get_variable_value(copiable_var_offset);
                        copiable_var_offset += 1;

                        var
                    };

                    let mut contribution = *dst;
                    contribution.sub_assign(&sbox_out_var, ctx);

                    destination.push_evaluation_result(contribution, ctx);

                    *dst = sbox_out_var;
                }
            }

            // add constatnts

            if round_idx != 0 {
                for (idx, dst) in state.iter_mut().enumerate() {
                    // add constants and do s_box
                    dst.add_assign(&round_constants[round][idx], ctx);
                    dst.small_pow(PAR::NONLINEARITY_DEGREE, ctx);
                }
            } else {
                for dst in state.iter_mut() {
                    // no constant here
                    dst.small_pow(PAR::NONLINEARITY_DEGREE, ctx);
                }
            }

            // do MDS, and it'll be collapsed into the outputs
            let old_state = state;
            for (i, dst) in state.iter_mut().enumerate() {
                let mut tmp = P::zero(ctx);
                for (src, coeff) in old_state.iter().zip(mds_matrix[i].iter()) {
                    P::mul_and_accumulate_into(&mut tmp, src, coeff, ctx);
                }

                *dst = tmp;
            }
        }

        for (src, dst) in state.into_iter().zip(output.into_iter()) {
            let mut contribution = dst;
            contribution.sub_assign(&src, ctx);

            destination.push_evaluation_result(contribution, ctx);
        }
    }
}

impl<
        F: SmallField,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        PAR: PoseidonParameters<F, AW, SW, CW>,
    > PoseidonRoundFunctionFlattenedEvaluator<F, AW, SW, CW, PAR>
{
    const fn min_num_required_copiable_variables() -> usize {
        2 * SW
    }

    const fn total_num_required_columns() -> usize {
        2 * SW + PAR::NUM_PARTIAL_ROUNDS + (PAR::HALF_NUM_FULL_ROUNDS - 1) * SW * 2
    }

    const fn num_terms() -> usize {
        (PAR::HALF_NUM_FULL_ROUNDS - 1) * SW
            + PAR::NUM_PARTIAL_ROUNDS
            + (PAR::HALF_NUM_FULL_ROUNDS - 1) * SW
            + SW
            + SW
    }

    const fn total_num_variables() -> usize {
        // we count in-outs + whatever we create in betwee
        SW + // in
        SW + // out
        SW * (PAR::HALF_NUM_FULL_ROUNDS-1) + // s-boxes for first half of partial rounds
        PAR::NUM_PARTIAL_ROUNDS + // s-boxes for partial rounds for first element of state only
        SW * PAR::HALF_NUM_FULL_ROUNDS // s-boxes for second half of partial rounds
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PoseidonFlattenedGate<
    F: SmallField,
    const AW: usize,
    const SW: usize,
    const CW: usize,
    PAR: PoseidonParameters<F, AW, SW, CW>,
> {
    pub absorbed_elements: [Variable; AW],
    pub kept_elements: [Variable; CW],
    pub new_state: [Variable; SW],
    num_copiable_columns_used: usize,
    num_witness_columns_used: usize,
    _marker: std::marker::PhantomData<(F, PAR)>,
}

impl<
        F: SmallField,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        PAR: PoseidonParameters<F, AW, SW, CW>,
    > Gate<F> for PoseidonFlattenedGate<F, AW, SW, CW, PAR>
where
    [(); SW - 1]:,
    [(); PAR::NUM_ROUNDS]:,
    [(); PAR::NUM_PARTIAL_ROUNDS]:,
{
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= PAR::NONLINEARITY_DEGREE
            && geometry.num_columns_under_copy_permutation
                >= Self::Evaluator::min_num_required_copiable_variables()
            && (geometry.num_columns_under_copy_permutation + geometry.num_witness_columns)
                >= Self::Evaluator::total_num_required_columns()
    }

    type Evaluator = PoseidonRoundFunctionFlattenedEvaluator<F, AW, SW, CW, PAR>;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        PoseidonRoundFunctionFlattenedEvaluator {
            num_copiable_columns_used: self.num_copiable_columns_used,
            num_witness_columns_used: self.num_witness_columns_used,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<
        F: SmallField,
        const AW: usize,
        const SW: usize,
        const CW: usize,
        PAR: PoseidonParameters<F, AW, SW, CW>,
    > PoseidonFlattenedGate<F, AW, SW, CW, PAR>
where
    [(); SW - 1]:,
    [(); PAR::NUM_ROUNDS]:,
    [(); PAR::NUM_PARTIAL_ROUNDS]:,
{
    #[inline]
    pub fn compute_strategy(geometry: &CSGeometry) -> (usize, (usize, usize)) {
        let num_copiable = geometry.num_columns_under_copy_permutation;
        let num_witnesses = geometry.num_witness_columns;

        let min_copiable_required =
            <Self as Gate<F>>::Evaluator::min_num_required_copiable_variables();
        let total_vars_required = <Self as Gate<F>>::Evaluator::total_num_variables();

        let max_by_copiable_in_state = num_copiable / min_copiable_required;
        let max_by_total_width = (num_copiable + num_witnesses) / total_vars_required;

        let max_instances = std::cmp::min(max_by_copiable_in_state, max_by_total_width);

        let in_witness_per_copy = num_witnesses / max_instances;

        let copiable_vars_per_copy = total_vars_required - in_witness_per_copy;

        // we do not handle endge cases when num_witnesses % max_instances != 0

        (max_instances, (copiable_vars_per_copy, in_witness_per_copy))
    }

    pub fn add_to_cs<CS: ConstraintSystem<F>>(self, cs: &mut CS, temporary_places: Vec<Place>) {
        debug_assert!(cs.gate_is_allowed::<Self>());

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            return;
        }

        match cs.get_gate_placement_strategy::<Self>() {
            GatePlacementStrategy::UseGeneralPurposeColumns => {
                let offered_row_idx = cs.next_available_row();
                let geometry = cs.get_params();
                // let capacity_per_row = self.capacity_per_row(&*cs);
                let (capacity_per_row, (num_new_variables, num_new_witnesses)) =
                    Self::compute_strategy(&geometry);
                let total_variables =
                    <Self as Gate<F>>::Evaluator::min_num_required_copiable_variables()
                        + num_new_variables;
                let tooling: &mut NextGateCounterWithoutParams = cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, _>()
                    .expect("gate must be allowed");
                let (row, num_instances_already_placed) =
                    find_next_gate_without_params(tooling, capacity_per_row, offered_row_idx);
                drop(tooling);

                // now we can use methods of CS to inform it of low level operations
                let mut variables_offset = num_instances_already_placed * total_variables;
                let mut witnesses_offset = num_instances_already_placed * num_new_witnesses;
                if offered_row_idx == row {
                    cs.place_gate(&self, row);
                }
                // place logical inputs
                cs.place_multiple_variables_into_row(
                    &self.absorbed_elements,
                    row,
                    variables_offset,
                );
                variables_offset += AW;

                cs.place_multiple_variables_into_row(&self.kept_elements, row, variables_offset);
                variables_offset += CW;

                cs.place_multiple_variables_into_row(&self.new_state, row, variables_offset);
                variables_offset += SW;

                for el in temporary_places.into_iter() {
                    debug_assert!(el.is_placeholder() == false);
                    if el.is_copiable_variable() {
                        let var = el.as_variable();
                        cs.place_variable(var, row, variables_offset);
                        variables_offset += 1;
                    } else {
                        let var = el.as_witness();
                        cs.place_witness(var, row, witnesses_offset);
                        witnesses_offset += 1;
                    }
                }
            }
            GatePlacementStrategy::UseSpecializedColumns {
                num_repetitions,
                share_constants,
            } => {
                unimplemented!()
            }
        }
    }

    pub fn configure_builder<
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        TImpl: CsBuilderImpl<F, TImpl>,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
    ) -> CsBuilder<TImpl, F, GC::DescendantHolder<Self, NextGateCounterWithoutParams>, TB> {
        let geometry = builder.get_params();
        let (_, (total_num_variables, num_new_witnesses)) = Self::compute_strategy(&geometry);

        builder.allow_gate(
            placement_strategy,
            (total_num_variables, num_new_witnesses),
            None,
        )
    }

    pub fn configure_builder<CS: ConfigurableCS<F>>(
        cs: CS,
        placement_strategy: GatePlacementStrategy,
    ) -> CS::DescendantCSWithNewGate<Self, NextGateCounterWithoutParams> {
        let geometry = cs.get_params();
        let (_, (total_num_variables, num_new_witnesses)) = Self::compute_strategy(&geometry);

        cs.allow_gate(
            placement_strategy,
            (total_num_variables, num_new_witnesses),
            None,
        )
    }

    pub fn compute_round_function<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        elements_to_absorb: [Variable; AW],
        state_elements_to_keep: [Variable; CW],
    ) -> [Variable; SW] {
        debug_assert!(cs.gate_is_allowed::<Self>());
        debug_assert_eq!(AW + CW, SW);

        let output_variables = cs.alloc_multiple_variables_without_values::<SW>();

        // and we need to formally allocate all intermediate values

        let reserved_for_in_out =
            <Self as Gate<F>>::Evaluator::min_num_required_copiable_variables();

        // we need to get it from parameters
        let (total_num_variables, num_new_witnesses) = cs.get_gate_params::<Self>();

        let num_new_variables = total_num_variables - reserved_for_in_out;

        let mut new_places = Vec::with_capacity(num_new_variables + num_new_witnesses);
        // first allocate witnesses
        for _ in 0..num_new_witnesses {
            let wit = cs.alloc_witness_without_value();
            new_places.push(wit.into());
        }

        for _ in 0..num_new_variables {
            let wit = cs.alloc_variable_without_value();
            new_places.push(wit.into());
        }

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let mut all_dependencies = Vec::with_capacity(AW + CW);
            all_dependencies.extend(&Place::from_variables(elements_to_absorb));
            all_dependencies.extend(&Place::from_variables(state_elements_to_keep));

            let mut all_outputs = Vec::with_capacity(num_new_variables + num_new_witnesses + SW);
            all_outputs.extend_from_slice(&new_places);
            all_outputs.extend(Place::from_variables(output_variables));

            let value_fn = move |inputs: &[F], output_buffer: &mut DstBuffer<'_, '_, F>| {
                // we follow the same logic as in the constraints below

                let mut state: [F; SW] = std::array::from_fn(|idx| inputs[idx]);

                let round_constants = PAR::all_round_constants();
                let mds_matrix = &PAR::MdsMatrixParams::COEFFS;
                let last_full_first_partial_rounds_merged_constants =
                    &PAR::ROUND_CONSTANTS_FUZED_LAST_FULL_AND_FIRST_PARTIAL;
                let last_full_first_partial_dense_matrix =
                    &PAR::FUZED_DENSE_MATRIX_LAST_FULL_AND_FIRST_PARTIAL;
                let fuzed_round_constants_for_partial_rounds =
                    PAR::fuzed_round_constants_for_partial_rounds();
                let vs_for_partial_rounds = PAR::vs_for_partial_rounds();
                let w_hats_for_partial_rounds = PAR::w_hats_for_partial_rounds();

                for round in 0..(PAR::HALF_NUM_FULL_ROUNDS - 1) {
                    if round != 0 {
                        // when we "reset" the degree
                        for (_idx, dst) in state.iter().enumerate() {
                            let output_value = *dst;
                            output_buffer.push(output_value);
                        }
                    }

                    // otherwise - normal poseidon
                    for (dst, src) in state.iter_mut().zip(round_constants[round].iter()) {
                        // add constants and do s_box
                        dst.add_assign(src);
                        dst.small_pow(PAR::NONLINEARITY_DEGREE);
                    }

                    // do MDS

                    let old_state = state;
                    for (i, dst) in state.iter_mut().enumerate() {
                        let mut tmp = F::ZERO;
                        for (src, coeff) in old_state.iter().zip(mds_matrix[i].iter()) {
                            F::mul_and_accumulate_into(&mut tmp, src, coeff);
                        }

                        *dst = tmp;
                    }
                }

                // we still need S-box
                for (_idx, dst) in state.iter().enumerate() {
                    let output_value = *dst;
                    output_buffer.push(output_value);
                }

                let round = PAR::HALF_NUM_FULL_ROUNDS - 1;
                for (dst, src) in state.iter_mut().zip(round_constants[round].iter()) {
                    // add constants and do s_box
                    dst.add_assign(src);
                    dst.small_pow(PAR::NONLINEARITY_DEGREE);
                }

                // last partial round is special, because we can utilize another multiplication after s-box
                for (dst, src) in state
                    .iter_mut()
                    .zip(last_full_first_partial_rounds_merged_constants.iter())
                {
                    dst.add_assign(src);
                }
                let old_state = state;
                for (i, dst) in state.iter_mut().enumerate() {
                    let mut tmp = F::ZERO;
                    for (src, coeff) in old_state
                        .iter()
                        .zip(last_full_first_partial_dense_matrix[i].iter())
                    {
                        F::mul_and_accumulate_into(&mut tmp, src, coeff);
                    }

                    *dst = tmp;
                }

                // partial rounds
                for round in 0..PAR::NUM_PARTIAL_ROUNDS {
                    // partial s-box reset degree

                    {
                        let output_value = state[0];
                        output_buffer.push(output_value);

                        // partial s-box itself

                        // NOTE change of s-box and constant addition
                        state[0].small_pow(PAR::NONLINEARITY_DEGREE);
                        state[0].add_assign(&fuzed_round_constants_for_partial_rounds[round]);
                    }

                    // optimized MDS

                    let original_s0 = state[0];

                    let mut new_state0 = original_s0;

                    for (src, coeff) in state[1..]
                        .iter()
                        .zip(vs_for_partial_rounds[round][1..].iter())
                    {
                        F::mul_and_accumulate_into(&mut new_state0, src, coeff);
                    }

                    state[0] = new_state0;

                    for (dst, coeff) in state[1..]
                        .iter_mut()
                        .zip(w_hats_for_partial_rounds[round][1..].iter())
                    {
                        F::mul_and_accumulate_into(dst, &original_s0, coeff);
                    }
                }

                // finish with full rounds

                let round_counter = PAR::HALF_NUM_FULL_ROUNDS + PAR::NUM_PARTIAL_ROUNDS;

                for round_idx in 0..PAR::HALF_NUM_FULL_ROUNDS {
                    // we try to first use witness columns, and then use copiable. Limits are determined by the gate
                    // that creates this evaluator

                    let round = round_counter + round_idx;

                    {
                        // we "reset" the degree. We have to reset it for all because MDS matrix mixed high-degree
                        // state[0] into all other elements
                        for (_idx, dst) in state.iter().enumerate() {
                            let output_value = *dst;
                            output_buffer.push(output_value);
                        }
                    }

                    // add constants and apply S-box
                    // first round doesn't need to add counstans

                    for (dst, src) in state.iter_mut().zip(round_constants[round].iter()) {
                        // add constants and do s_box
                        dst.add_assign(src);
                        dst.small_pow(PAR::NONLINEARITY_DEGREE);
                    }

                    // do MDS

                    let old_state = state;
                    for (i, dst) in state.iter_mut().enumerate() {
                        let mut tmp = F::ZERO;
                        for (src, coeff) in old_state.iter().zip(mds_matrix[i].iter()) {
                            F::mul_and_accumulate_into(&mut tmp, src, coeff);
                        }

                        *dst = tmp;
                    }
                }

                output_buffer.extend(state);
            };

            cs.set_values_with_dependencies_vararg(&all_dependencies, &all_outputs, value_fn);
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let gate = Self {
                absorbed_elements: elements_to_absorb,
                kept_elements: state_elements_to_keep,
                new_state: output_variables,
                num_copiable_columns_used: total_num_variables,
                num_witness_columns_used: num_new_witnesses,
                _marker: std::marker::PhantomData,
            };

            gate.add_to_cs(cs, new_places);
        }

        output_variables
    }

    pub fn enforce_round_function<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        initial_state: [Variable; SW],
        final_state: [Variable; SW],
    ) {
        debug_assert!(cs.gate_is_allowed::<Self>());
        debug_assert_eq!(AW + CW, SW);

        // and we need to formally allocate all intermediate values

        let reserved_for_in_out =
            <Self as Gate<F>>::Evaluator::min_num_required_copiable_variables();

        // we need to get it from parameters
        let (total_num_variables, num_new_witnesses) = cs.get_gate_params::<Self>();

        let num_new_variables = total_num_variables - reserved_for_in_out;

        let mut new_places = Vec::with_capacity(num_new_variables + num_new_witnesses);
        // first allocate witnesses
        for _ in 0..num_new_witnesses {
            let wit = cs.alloc_witness_without_value();
            new_places.push(wit.into());
        }

        for _ in 0..num_new_variables {
            let wit = cs.alloc_variable_without_value();
            new_places.push(wit.into());
        }

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let mut all_dependencies = Vec::with_capacity(SW);
            all_dependencies.extend(&Place::from_variables(initial_state));

            let mut all_outputs = Vec::with_capacity(num_new_variables + num_new_witnesses);
            all_outputs.extend_from_slice(&new_places);

            let value_fn = move |inputs: &[F], output_buffer: &mut DstBuffer<'_, '_, F>| {
                // we follow the same logic as in the constraints below

                let mut state: [F; SW] = std::array::from_fn(|idx| inputs[idx]);

                let round_constants = PAR::all_round_constants();
                let mds_matrix = &PAR::MdsMatrixParams::COEFFS;
                let last_full_first_partial_rounds_merged_constants =
                    &PAR::ROUND_CONSTANTS_FUZED_LAST_FULL_AND_FIRST_PARTIAL;
                let last_full_first_partial_dense_matrix =
                    &PAR::FUZED_DENSE_MATRIX_LAST_FULL_AND_FIRST_PARTIAL;
                let fuzed_round_constants_for_partial_rounds =
                    PAR::fuzed_round_constants_for_partial_rounds();
                let vs_for_partial_rounds = PAR::vs_for_partial_rounds();
                let w_hats_for_partial_rounds = PAR::w_hats_for_partial_rounds();

                for round in 0..(PAR::HALF_NUM_FULL_ROUNDS - 1) {
                    if round != 0 {
                        // when we "reset" the degree
                        for (_idx, dst) in state.iter().enumerate() {
                            let output_value = *dst;
                            output_buffer.push(output_value);
                        }
                    }

                    // otherwise - normal poseidon
                    for (dst, src) in state.iter_mut().zip(round_constants[round].iter()) {
                        // add constants and do s_box
                        dst.add_assign(src);
                        dst.small_pow(PAR::NONLINEARITY_DEGREE);
                    }

                    // do MDS

                    let old_state = state;
                    for (i, dst) in state.iter_mut().enumerate() {
                        let mut tmp = F::ZERO;
                        for (src, coeff) in old_state.iter().zip(mds_matrix[i].iter()) {
                            F::mul_and_accumulate_into(&mut tmp, src, coeff);
                        }

                        *dst = tmp;
                    }
                }

                // we still need S-box
                for (_idx, dst) in state.iter().enumerate() {
                    let output_value = *dst;
                    output_buffer.push(output_value);
                }

                let round = PAR::HALF_NUM_FULL_ROUNDS - 1;
                for (dst, src) in state.iter_mut().zip(round_constants[round].iter()) {
                    // add constants and do s_box
                    dst.add_assign(src);
                    dst.small_pow(PAR::NONLINEARITY_DEGREE);
                }

                // last partial round is special, because we can utilize another multiplication after s-box
                for (dst, src) in state
                    .iter_mut()
                    .zip(last_full_first_partial_rounds_merged_constants.iter())
                {
                    dst.add_assign(src);
                }
                let old_state = state;
                for (i, dst) in state.iter_mut().enumerate() {
                    let mut tmp = F::ZERO;
                    for (src, coeff) in old_state
                        .iter()
                        .zip(last_full_first_partial_dense_matrix[i].iter())
                    {
                        F::mul_and_accumulate_into(&mut tmp, src, coeff);
                    }

                    *dst = tmp;
                }

                // partial rounds
                for round in 0..PAR::NUM_PARTIAL_ROUNDS {
                    // partial s-box reset degree

                    {
                        let output_value = state[0];
                        output_buffer.push(output_value);

                        // partial s-box itself

                        // NOTE change of s-box and constant addition
                        state[0].small_pow(PAR::NONLINEARITY_DEGREE);
                        state[0].add_assign(&fuzed_round_constants_for_partial_rounds[round]);
                    }

                    // optimized MDS

                    let original_s0 = state[0];

                    let mut new_state0 = original_s0;

                    for (src, coeff) in state[1..]
                        .iter()
                        .zip(vs_for_partial_rounds[round][1..].iter())
                    {
                        F::mul_and_accumulate_into(&mut new_state0, src, coeff);
                    }

                    state[0] = new_state0;

                    for (dst, coeff) in state[1..]
                        .iter_mut()
                        .zip(w_hats_for_partial_rounds[round][1..].iter())
                    {
                        F::mul_and_accumulate_into(dst, &original_s0, coeff);
                    }
                }

                // finish with full rounds

                let round_counter = PAR::HALF_NUM_FULL_ROUNDS + PAR::NUM_PARTIAL_ROUNDS;

                for round_idx in 0..PAR::HALF_NUM_FULL_ROUNDS {
                    // we try to first use witness columns, and then use copiable. Limits are determined by the gate
                    // that creates this evaluator

                    let round = round_counter + round_idx;

                    {
                        // we "reset" the degree. We have to reset it for all because MDS matrix mixed high-degree
                        // state[0] into all other elements
                        for (_idx, dst) in state.iter().enumerate() {
                            let output_value = *dst;
                            output_buffer.push(output_value);
                        }
                    }

                    // add constants and apply S-box
                    // first round doesn't need to add counstans

                    for (dst, src) in state.iter_mut().zip(round_constants[round].iter()) {
                        // add constants and do s_box
                        dst.add_assign(src);
                        dst.small_pow(PAR::NONLINEARITY_DEGREE);
                    }

                    // do MDS

                    let old_state = state;
                    for (i, dst) in state.iter_mut().enumerate() {
                        let mut tmp = F::ZERO;
                        for (src, coeff) in old_state.iter().zip(mds_matrix[i].iter()) {
                            F::mul_and_accumulate_into(&mut tmp, src, coeff);
                        }

                        *dst = tmp;
                    }
                }
            };

            cs.set_values_with_dependencies_vararg(&all_dependencies, &all_outputs, value_fn);
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let mut elements_to_absorb = [Variable::placeholder(); AW];
            elements_to_absorb.copy_from_slice(&initial_state[..AW]);

            let mut state_elements_to_keep = [Variable::placeholder(); CW];
            state_elements_to_keep.copy_from_slice(&initial_state[AW..]);

            let gate = Self {
                absorbed_elements: elements_to_absorb,
                kept_elements: state_elements_to_keep,
                new_state: final_state,
                num_copiable_columns_used: total_num_variables,
                num_witness_columns_used: num_new_witnesses,
                _marker: std::marker::PhantomData,
            };

            gate.add_to_cs(cs, new_places);
        }
    }
}

#[cfg(test)]
mod test {
    use crate::cs::gates::testing_tools::test_evaluator;
    use crate::field::Field;

    use super::*;
    use crate::worker::Worker;
    type F = crate::field::goldilocks::GoldilocksField;
    use crate::cs::gates::*;
    use crate::implementations::poseidon_goldilocks::PoseidonGoldilocks;

    type PoseidonGate = PoseidonFlattenedGate<F, 8, 12, 4, PoseidonGoldilocks>;
    use crate::cs::implementations::reference_cs::CSReferenceImplementation;

    #[test]
    fn test_simple_poseidon() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 80,
            num_witness_columns: 80,
            num_constant_columns: 10,
            max_allowed_constraint_degree: 8,
        };

        let owned_cs = CSReferenceImplementation::<F, F, DevCSConfig, _, _>::new_for_geometry(
            geometry, 128, 8,
        );

        let owned_cs = PoseidonGate::configure_builder(
            owned_cs,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let owned_cs = ConstantsAllocatorGate::configure_builder(
            owned_cs,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let owned_cs =
            NopGate::configure_builder(owned_cs, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = owned_cs.freeze();

        let cs = &mut owned_cs;

        let mut inputs = [Variable::placeholder(); 8];
        let mut state = [F::ZERO; 12];
        for (idx, dst) in inputs.iter_mut().enumerate() {
            let value = F::from_u64_with_reduction(idx as u64);
            let var = cs.alloc_single_variable_from_witness(value);
            state[idx] = value;
            *dst = var;
        }

        let capacity_var = cs.allocate_constant(F::ZERO);

        let outputs = [capacity_var; 4];

        let round_function_result = PoseidonGate::compute_round_function(cs, inputs, outputs);

        use crate::implementations::poseidon_goldilocks::poseidon_permutation;
        poseidon_permutation(&mut state);

        log!("Out of circuit result = {:?}", state);

        let circuit_result = cs
            .get_value_for_multiple(Place::from_variables(round_function_result))
            .wait()
            .unwrap();

        log!("Circuit result = {:?}", circuit_result);

        assert_eq!(circuit_result, state);

        drop(cs);
        owned_cs.pad_and_shrink();

        let worker = Worker::new();

        log!("Checking if satisfied");

        assert!(owned_cs.check_if_satisfied(&worker));
    }

    #[test]
    fn test_properties() {
        type PoseidonGate = PoseidonFlattenedGate<F, 8, 12, 4, PoseidonGoldilocks>;

        // particular geometry is not important
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 80,
            num_witness_columns: 80,
            num_constant_columns: 10,
            max_allowed_constraint_degree: 8,
        };

        let (_, (total_num_variables, num_new_witnesses)) =
            PoseidonGate::compute_strategy(&geometry);

        let evaluator = PoseidonRoundFunctionFlattenedEvaluator::<F, 8, 12, 4, PoseidonGoldilocks>::new_from_parameters(
            (total_num_variables, num_new_witnesses)
        );

        test_evaluator(evaluator);
    }

    #[test]
    fn test_properties_2() {
        type PoseidonGate = PoseidonFlattenedGate<F, 8, 12, 4, PoseidonGoldilocks>;

        // particular geometry is not important
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 140,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 8,
        };

        let (_, (total_num_variables, num_new_witnesses)) =
            PoseidonGate::compute_strategy(&geometry);

        let evaluator = PoseidonRoundFunctionFlattenedEvaluator::<F, 8, 12, 4, PoseidonGoldilocks>::new_from_parameters(
            (total_num_variables, num_new_witnesses)
        );

        test_evaluator(evaluator);
    }
}
