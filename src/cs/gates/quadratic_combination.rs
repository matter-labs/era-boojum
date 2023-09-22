use super::*;

// Allocate constants by a batch of constraints like (a - constant) == 0

// In this file the allocator uses (type) bounded number of constant columns for its work

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct QuadraticCombinationGate<const N: usize> {
    pub pairs: [(Variable, Variable); N],
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct QuadraticCombinationConstraintEvaluator<const N: usize>;

impl<F: PrimeField, const N: usize> GateConstraintEvaluator<F>
    for QuadraticCombinationConstraintEvaluator<N>
{
    type UniqueParameterizationParams = ();

    #[inline(always)]
    fn new_from_parameters(_params: Self::UniqueParameterizationParams) -> Self {
        Self
    }

    #[inline(always)]
    fn unique_params(&self) -> Self::UniqueParameterizationParams {}

    #[inline]
    fn type_name() -> std::borrow::Cow<'static, str> {
        Cow::Borrowed(std::any::type_name::<Self>())
    }

    #[inline]
    fn instance_width(&self) -> GatePrincipalInstanceWidth {
        GatePrincipalInstanceWidth {
            num_variables: 2 * N,
            num_witnesses: 0,
            num_constants: 0,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: 2,
            num_quotient_terms: 1,
        }
    }

    #[inline]
    fn placement_type(&self) -> GatePlacementType {
        GatePlacementType::MultipleOnRow {
            per_chunk_offset: PerChunkOffset {
                variables_offset: 2 * N,
                witnesses_offset: 0,
                constants_offset: 0,
            },
        }
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, geometry: &CSGeometry) -> usize {
        debug_assert!(geometry.num_columns_under_copy_permutation >= (2 * N));

        geometry.num_columns_under_copy_permutation / (2 * N)
    }
    #[inline]
    fn num_required_constants_in_geometry(&self, _geometry: &CSGeometry) -> usize {
        0
    }

    type GlobalConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = ();

    #[inline(always)]
    fn create_global_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>>(
        &self,
        _ctx: &mut P::Context,
    ) -> Self::GlobalConstants<P> {
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
        _global_constants: &Self::GlobalConstants<P>,
        ctx: &mut P::Context,
    ) {
        let (a, b) = (
            trace_source.get_variable_value(0),
            trace_source.get_variable_value(1),
        );

        let mut contribution = a;
        contribution.mul_assign(&b, ctx);

        for i in 1..N {
            let (a, b) = (
                trace_source.get_variable_value(2 * i),
                trace_source.get_variable_value(2 * i + 1),
            );
            let mut tmp = a;
            tmp.mul_assign(&b, ctx);

            contribution.add_assign(&tmp, ctx);
        }

        destination.push_evaluation_result(contribution, ctx);
    }
}

impl<F: SmallField, const N: usize> Gate<F> for QuadraticCombinationGate<N> {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 2
            && geometry.num_columns_under_copy_permutation >= N
    }

    type Evaluator = QuadraticCombinationConstraintEvaluator<N>;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        QuadraticCombinationConstraintEvaluator
    }
}

impl<const N: usize> QuadraticCombinationGate<N> {
    const fn principal_width() -> usize {
        2 * N
    }

    // evaluation of witness must be done by the caller
    pub fn add_to_cs<F: SmallField, CS: ConstraintSystem<F>>(self, cs: &mut CS) {
        debug_assert!(cs.gate_is_allowed::<Self>());

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP == false {
            return;
        }

        match cs.get_gate_placement_strategy::<Self>() {
            GatePlacementStrategy::UseGeneralPurposeColumns => {
                let offered_row_idx = cs.next_available_row();
                let capacity_per_row = self.capacity_per_row(&*cs);
                let tooling: &mut NextGateCounterWithoutParams = cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, _>()
                    .expect("gate must be allowed");
                let (row, num_instances_already_placed) =
                    find_next_gate_without_params(tooling, capacity_per_row, offered_row_idx);
                drop(tooling);

                // now we can use methods of CS to inform it of low level operations
                let mut offset = num_instances_already_placed * Self::principal_width();
                if offered_row_idx == row {
                    cs.place_gate(&self, row);
                }
                for (a, b) in self.pairs.into_iter() {
                    cs.place_multiple_variables_into_row(&[a, b], row, offset);
                    offset += 2;
                }
            }
            GatePlacementStrategy::UseSpecializedColumns {
                num_repetitions,
                share_constants: _,
            } => {
                // gate knows how to place itself
                let capacity_per_row = num_repetitions;
                let tooling: &mut NextGateCounterWithoutParams = cs
                    .get_gates_config_mut()
                    .get_aux_data_mut::<Self, _>()
                    .expect("gate must be allowed");
                let (row, num_instances_already_placed) =
                    find_next_specialized_gate_without_params(tooling, capacity_per_row);
                cs.place_gate_specialized(&self, num_instances_already_placed, row);
                let mut offset = 0;
                for (a, b) in self.pairs.into_iter() {
                    cs.place_multiple_variables_into_row_specialized::<Self, 2>(
                        &[a, b],
                        num_instances_already_placed,
                        row,
                        offset,
                    );
                    offset += 2;
                }
            }
        }
    }
}
