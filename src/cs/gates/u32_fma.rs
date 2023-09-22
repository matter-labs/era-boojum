use crate::cs::cs_builder::{CsBuilder, CsBuilderImpl};

use super::*;

// u8x4 * u8x4 + u8x4 + u8x4 = u8x4 + 2^32 * u8x4, for purposes for long math

const UNIQUE_IDENTIFIER: &str = "u8x4 * u8x4 + u8x4 + u8x4 = u8x4 + 2^32 * u8x4";
const PRINCIPAL_WIDTH: usize = 26;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct U8x4ConstraintEvaluator;

impl<F: SmallField> GateConstraintEvaluator<F> for U8x4ConstraintEvaluator {
    type UniqueParameterizationParams = ();

    #[inline(always)]
    fn new_from_parameters(_params: Self::UniqueParameterizationParams) -> Self {
        Self
    }

    #[inline(always)]
    fn unique_params(&self) -> Self::UniqueParameterizationParams {}

    #[inline]
    fn type_name() -> std::borrow::Cow<'static, str> {
        Cow::Borrowed(UNIQUE_IDENTIFIER)
    }

    #[inline]
    fn instance_width(&self) -> GatePrincipalInstanceWidth {
        GatePrincipalInstanceWidth {
            num_variables: PRINCIPAL_WIDTH,
            num_witnesses: 0,
            num_constants: 0,
        }
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        GatePurpose::Evaluatable {
            max_constraint_degree: 2,
            num_quotient_terms: 2,
        }
    }

    #[inline]
    fn placement_type(&self) -> GatePlacementType {
        GatePlacementType::MultipleOnRow {
            per_chunk_offset: PerChunkOffset {
                variables_offset: PRINCIPAL_WIDTH,
                witnesses_offset: 0,
                constants_offset: 0,
            },
        }
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, geometry: &CSGeometry) -> usize {
        debug_assert!(geometry.num_columns_under_copy_permutation >= PRINCIPAL_WIDTH);

        geometry.num_columns_under_copy_permutation / PRINCIPAL_WIDTH
    }

    #[inline]
    fn num_required_constants_in_geometry(&self, _geometry: &CSGeometry) -> usize {
        0
    }

    type GlobalConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> = [P; 12];

    #[inline(always)]
    fn create_global_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>>(
        &self,
        ctx: &mut P::Context,
    ) -> Self::GlobalConstants<P> {
        debug_assert!(F::CAPACITY_BITS >= 48);

        let shift_8 = F::from_u64_unchecked(1u64 << 8);
        let shift_16 = F::from_u64_unchecked(1u64 << 16);
        let shift_24 = F::from_u64_unchecked(1u64 << 24);
        let shift_32 = F::from_u64_unchecked(1u64 << 32);
        let shift_40 = F::from_u64_unchecked(1u64 << 40);

        let mut minus_shift_8 = shift_8;
        minus_shift_8.negate();
        let mut minus_shift_16 = shift_16;
        minus_shift_16.negate();
        let mut minus_shift_24 = shift_24;
        minus_shift_24.negate();
        let mut minus_shift_32 = shift_32;
        minus_shift_32.negate();
        let mut minus_shift_40 = shift_40;
        minus_shift_40.negate();

        let one = P::constant(F::ONE, ctx);
        let minus_one = P::constant(F::MINUS_ONE, ctx);

        let shift_8 = P::constant(shift_8, ctx);
        let shift_16 = P::constant(shift_16, ctx);
        let shift_24 = P::constant(shift_24, ctx);
        let shift_32 = P::constant(shift_32, ctx);
        let shift_40 = P::constant(shift_40, ctx);

        let minus_shift_8 = P::constant(minus_shift_8, ctx);
        let minus_shift_16 = P::constant(minus_shift_16, ctx);
        let minus_shift_24 = P::constant(minus_shift_24, ctx);
        let minus_shift_32 = P::constant(minus_shift_32, ctx);
        let minus_shift_40 = P::constant(minus_shift_40, ctx);

        [
            one,
            shift_8,
            shift_16,
            shift_24,
            shift_32,
            shift_40,
            minus_one,
            minus_shift_8,
            minus_shift_16,
            minus_shift_24,
            minus_shift_32,
            minus_shift_40,
        ]
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
        let [_one, shift_8, shift_16, shift_24, _shift_32, _shift_40, minus_one, minus_shift_8, minus_shift_16, minus_shift_24, minus_shift_32, minus_shift_40] =
            global_constants;

        let [a0, a1, a2, a3] = [
            trace_source.get_variable_value(0),
            trace_source.get_variable_value(1),
            trace_source.get_variable_value(2),
            trace_source.get_variable_value(3),
        ];

        let [b0, b1, b2, b3] = [
            trace_source.get_variable_value(4 + 0),
            trace_source.get_variable_value(4 + 1),
            trace_source.get_variable_value(4 + 2),
            trace_source.get_variable_value(4 + 3),
        ];

        let [c0, c1, c2, c3] = [
            trace_source.get_variable_value(8 + 0),
            trace_source.get_variable_value(8 + 1),
            trace_source.get_variable_value(8 + 2),
            trace_source.get_variable_value(8 + 3),
        ];

        let [carry0, carry1, carry2, carry3] = [
            trace_source.get_variable_value(12 + 0),
            trace_source.get_variable_value(12 + 1),
            trace_source.get_variable_value(12 + 2),
            trace_source.get_variable_value(12 + 3),
        ];

        let [low0, low1, low2, low3] = [
            trace_source.get_variable_value(16 + 0),
            trace_source.get_variable_value(16 + 1),
            trace_source.get_variable_value(16 + 2),
            trace_source.get_variable_value(16 + 3),
        ];

        let [high0, high1, high2, high3] = [
            trace_source.get_variable_value(20 + 0),
            trace_source.get_variable_value(20 + 1),
            trace_source.get_variable_value(20 + 2),
            trace_source.get_variable_value(20 + 3),
        ];

        let [product_carry0, product_carry1] = [
            trace_source.get_variable_value(24 + 0),
            trace_source.get_variable_value(24 + 1),
        ];

        // we do the usual long math, assuming that long enough combination fits into
        // field element without overflow

        // arbitrary decision is to use low 16 bit subwords from multiplication,
        // and partial 16 bit words from addition

        // we create a combination such that lowest 0..32 bits will be zeroes,
        // and we carry the rest to the next piece

        // in general we should consider range of such "carry".
        // In this case it fits into 8 bits

        // + c
        let mut contribution = c0;
        P::mul_and_accumulate_into(&mut contribution, &c1, shift_8, ctx);
        P::mul_and_accumulate_into(&mut contribution, &c2, shift_16, ctx);
        P::mul_and_accumulate_into(&mut contribution, &c3, shift_24, ctx);

        // + carry_in
        contribution.add_assign(&carry0, ctx);
        P::mul_and_accumulate_into(&mut contribution, &carry1, shift_8, ctx);
        P::mul_and_accumulate_into(&mut contribution, &carry2, shift_16, ctx);
        P::mul_and_accumulate_into(&mut contribution, &carry3, shift_24, ctx);

        // - low
        P::mul_and_accumulate_into(&mut contribution, &low0, minus_one, ctx);
        P::mul_and_accumulate_into(&mut contribution, &low1, minus_shift_8, ctx);
        P::mul_and_accumulate_into(&mut contribution, &low2, minus_shift_16, ctx);
        P::mul_and_accumulate_into(&mut contribution, &low3, minus_shift_24, ctx);

        // multiplication, basically everything that contributes into 0..32 bits

        // 0..
        P::mul_and_accumulate_into(&mut contribution, &a0, &b0, ctx);

        // 8..
        let mut tmp = a1;
        tmp.mul_assign(&b0, ctx);
        P::mul_and_accumulate_into(&mut tmp, &a0, &b1, ctx);
        P::mul_and_accumulate_into(&mut contribution, &tmp, shift_8, ctx);

        // 16..
        let mut tmp = a2;
        tmp.mul_assign(&b0, ctx);
        P::mul_and_accumulate_into(&mut tmp, &a1, &b1, ctx);
        P::mul_and_accumulate_into(&mut tmp, &a0, &b2, ctx);
        P::mul_and_accumulate_into(&mut contribution, &tmp, shift_16, ctx);

        // 24..
        let mut tmp = a3;
        tmp.mul_assign(&b0, ctx);
        P::mul_and_accumulate_into(&mut tmp, &a2, &b1, ctx);
        P::mul_and_accumulate_into(&mut tmp, &a1, &b2, ctx);
        P::mul_and_accumulate_into(&mut tmp, &a0, &b3, ctx);
        P::mul_and_accumulate_into(&mut contribution, &tmp, shift_24, ctx);

        // and we need to subtract carries, that are range checked
        P::mul_and_accumulate_into(&mut contribution, &product_carry0, minus_shift_32, ctx);
        P::mul_and_accumulate_into(&mut contribution, &product_carry1, minus_shift_40, ctx);

        destination.push_evaluation_result(contribution, ctx);

        // continue in the same manner, enforce everything for range 32..64

        let mut contribution = product_carry0;
        P::mul_and_accumulate_into(&mut contribution, &product_carry1, shift_8, ctx);

        // - high
        P::mul_and_accumulate_into(&mut contribution, &high0, minus_one, ctx);
        P::mul_and_accumulate_into(&mut contribution, &high1, minus_shift_8, ctx);
        P::mul_and_accumulate_into(&mut contribution, &high2, minus_shift_16, ctx);
        P::mul_and_accumulate_into(&mut contribution, &high3, minus_shift_24, ctx);

        // multiplication
        // 32..
        let mut tmp = a3;
        tmp.mul_assign(&b1, ctx);
        P::mul_and_accumulate_into(&mut tmp, &a2, &b2, ctx);
        P::mul_and_accumulate_into(&mut tmp, &a1, &b3, ctx);

        contribution.add_assign(&tmp, ctx);

        // 40..
        let mut tmp = a3;
        tmp.mul_assign(&b2, ctx);
        P::mul_and_accumulate_into(&mut tmp, &a2, &b3, ctx);

        P::mul_and_accumulate_into(&mut contribution, &tmp, shift_8, ctx);

        // 48..
        let mut tmp = a3;
        tmp.mul_assign(&b3, ctx);

        P::mul_and_accumulate_into(&mut contribution, &tmp, shift_16, ctx);

        destination.push_evaluation_result(contribution, ctx);
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct U8x4FMAGate {
    pub a: [Variable; 4],
    pub b: [Variable; 4],
    pub c: [Variable; 4],
    pub carry_in: [Variable; 4],
    pub low: [Variable; 4],
    pub high: [Variable; 4],

    pub internal_carries: [Variable; 2],
}

impl<F: SmallField> Gate<F> for U8x4FMAGate {
    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        let geometry = cs.get_params();
        geometry.max_allowed_constraint_degree >= 2
            && geometry.num_columns_under_copy_permutation >= PRINCIPAL_WIDTH
    }

    type Evaluator = U8x4ConstraintEvaluator;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        U8x4ConstraintEvaluator
    }
}

impl U8x4FMAGate {
    pub fn configure_builder<
        F: SmallField,
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
        TImpl: CsBuilderImpl<F, TImpl>,
    >(
        builder: CsBuilder<TImpl, F, GC, TB>,
        placement_strategy: GatePlacementStrategy,
        // ) -> CsBuilder<TImpl, F, GC::DescendantHolder<Self, NextGateCounterWithoutParams>, TB> {
    ) -> CsBuilder<TImpl, F, (GateTypeEntry<F, Self, NextGateCounterWithoutParams>, GC), TB> {
        builder.allow_gate(placement_strategy, (), None)
    }

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
                let mut offset = num_instances_already_placed * PRINCIPAL_WIDTH;
                if offered_row_idx == row {
                    cs.place_gate(&self, row);
                }
                cs.place_multiple_variables_into_row(&self.a, row, offset);
                offset += 4;
                cs.place_multiple_variables_into_row(&self.b, row, offset);
                offset += 4;
                cs.place_multiple_variables_into_row(&self.c, row, offset);
                offset += 4;
                cs.place_multiple_variables_into_row(&self.carry_in, row, offset);
                offset += 4;
                cs.place_multiple_variables_into_row(&self.low, row, offset);
                offset += 4;
                cs.place_multiple_variables_into_row(&self.high, row, offset);
                offset += 4;
                cs.place_multiple_variables_into_row(&self.internal_carries, row, offset);
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
                cs.place_multiple_variables_into_row_specialized::<Self, 4>(
                    &self.a,
                    num_instances_already_placed,
                    row,
                    offset,
                );
                offset += 4;
                cs.place_multiple_variables_into_row_specialized::<Self, 4>(
                    &self.b,
                    num_instances_already_placed,
                    row,
                    offset,
                );
                offset += 4;
                cs.place_multiple_variables_into_row_specialized::<Self, 4>(
                    &self.c,
                    num_instances_already_placed,
                    row,
                    offset,
                );
                offset += 4;
                cs.place_multiple_variables_into_row_specialized::<Self, 4>(
                    &self.carry_in,
                    num_instances_already_placed,
                    row,
                    offset,
                );
                offset += 4;
                cs.place_multiple_variables_into_row_specialized::<Self, 4>(
                    &self.low,
                    num_instances_already_placed,
                    row,
                    offset,
                );
                offset += 4;
                cs.place_multiple_variables_into_row_specialized::<Self, 4>(
                    &self.high,
                    num_instances_already_placed,
                    row,
                    offset,
                );
                offset += 4;
                cs.place_multiple_variables_into_row_specialized::<Self, 2>(
                    &self.internal_carries,
                    num_instances_already_placed,
                    row,
                    offset,
                );
            }
        }
    }

    pub fn perform_fma<F: SmallField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        a_decomposition: [Variable; 4],
        b_decomposition: [Variable; 4],
        c_decomposition: [Variable; 4],
        carry_in_decomposition: [Variable; 4],
    ) -> ([Variable; 4], [Variable; 4], [Variable; 2]) {
        debug_assert!(cs.gate_is_allowed::<Self>());

        let output_variables = cs.alloc_multiple_variables_without_values::<10>();

        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS {
            let value_fn = move |inputs: [F; 16]| {
                let [a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3, carry_in0, carry_in1, carry_in2, carry_in3] =
                    inputs.map(|el| el.as_u64() as u8);

                // reassemble
                let a = [a0, a1, a2, a3];

                let a = u32::from_le_bytes(a);

                let b = [b0, b1, b2, b3];

                let b = u32::from_le_bytes(b);

                let c = [c0, c1, c2, c3];

                let c = u32::from_le_bytes(c);

                let carry_in = [carry_in0, carry_in1, carry_in2, carry_in3];

                let carry_in = u32::from_le_bytes(carry_in);

                // the most unpleasant part is getting partial carries
                let mut tmp = (a0 as u64) * (b0 as u64)
                    + ((a1 as u64 * b0 as u64 + a0 as u64 * b1 as u64) << 8)
                    + ((a2 as u64 * b0 as u64 + a1 as u64 * b1 as u64 + a0 as u64 * b2 as u64)
                        << 16)
                    + ((a3 as u64 * b0 as u64
                        + a2 as u64 * b1 as u64
                        + a1 as u64 * b2 as u64
                        + a0 as u64 * b3 as u64)
                        << 24);

                tmp += c as u64;
                tmp += carry_in as u64;

                debug_assert!(tmp < 1u64 << 48);

                let carry = tmp >> 32;
                let product_carry0 = carry as u8;
                let product_carry1 = (carry >> 8) as u8;

                let result = a as u64 * b as u64 + c as u64 + carry_in as u64;
                let low = result as u32;
                let high = (result >> 32) as u32;

                let [low0, low1, low2, low3] = low.to_le_bytes();

                let [high0, high1, high2, high3] = high.to_le_bytes();

                [
                    low0,
                    low1,
                    low2,
                    low3,
                    high0,
                    high1,
                    high2,
                    high3,
                    product_carry0,
                    product_carry1,
                ]
                .map(|el| F::from_u64_unchecked(el as u64))
            };

            let dependencies = Place::from_variables([
                a_decomposition[0],
                a_decomposition[1],
                a_decomposition[2],
                a_decomposition[3],
                b_decomposition[0],
                b_decomposition[1],
                b_decomposition[2],
                b_decomposition[3],
                c_decomposition[0],
                c_decomposition[1],
                c_decomposition[2],
                c_decomposition[3],
                carry_in_decomposition[0],
                carry_in_decomposition[1],
                carry_in_decomposition[2],
                carry_in_decomposition[3],
            ]);

            cs.set_values_with_dependencies(
                &dependencies,
                &Place::from_variables(output_variables),
                value_fn,
            );
        }

        if <CS::Config as CSConfig>::SetupConfig::KEEP_SETUP {
            let [low0, low1, low2, low3, high0, high1, high2, high3, product_carry0, product_carry_1] =
                output_variables;

            let gate = Self {
                a: a_decomposition,
                b: b_decomposition,
                c: c_decomposition,
                carry_in: carry_in_decomposition,
                low: [low0, low1, low2, low3],
                high: [high0, high1, high2, high3],
                internal_carries: [product_carry0, product_carry_1],
            };

            gate.add_to_cs(cs);
        }

        (
            [
                output_variables[0],
                output_variables[1],
                output_variables[2],
                output_variables[3],
            ],
            [
                output_variables[4],
                output_variables[5],
                output_variables[6],
                output_variables[7],
            ],
            [output_variables[8], output_variables[9]],
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cs::gates::testing_tools::test_evaluator;
    use crate::field::goldilocks::GoldilocksField;
    type F = GoldilocksField;

    #[test]
    fn test_properties() {
        // particular geometry is not important
        let _geometry = CSGeometry {
            num_columns_under_copy_permutation: 80,
            num_witness_columns: 80,
            num_constant_columns: 10,
            max_allowed_constraint_degree: 8,
        };

        let evaluator =
            <U8x4ConstraintEvaluator as GateConstraintEvaluator<F>>::new_from_parameters(());

        test_evaluator::<F, _>(evaluator);
    }
}
