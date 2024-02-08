use super::*;
use crate::cs::gates::{
    assert_no_placeholder_variables, ConstantAllocatableCS, FmaGateInBaseFieldWithoutConstant,
};
use crate::cs::traits::cs::ConstraintSystem;
use crate::cs::Variable;
use crate::gadgets::u32::UInt32;
use crate::gadgets::u8::UInt8;

pub mod round_function;

pub const SHA256_ROUNDS: usize = 64;
pub const SHA256_BLOCK_SIZE: usize = 64;
pub const SHA256_DIGEST_SIZE: usize = 32;

pub const INITIAL_STATE: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

pub const ROUND_CONSTANTS: [u32; SHA256_ROUNDS] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

pub fn ivs_as_uint32<F: SmallField, CS: ConstraintSystem<F>>(cs: &mut CS) -> [UInt32<F>; 8] {
    INITIAL_STATE.map(|el| UInt32::allocated_constant(cs, el))
}

pub fn sha256<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: &[UInt8<F>],
) -> [UInt8<F>; SHA256_DIGEST_SIZE] {
    // pad first
    let last_block_size = input.len() % SHA256_BLOCK_SIZE;
    let num_zeroes_to_add = if last_block_size <= (64 - 1 - 8) {
        64 - 1 - 8 - last_block_size
    } else {
        128 - 1 - 8 - last_block_size
    };

    let mut full_message = Vec::with_capacity(input.len() + 1 + 8 + num_zeroes_to_add);
    full_message.extend_from_slice(input);
    full_message.push(UInt8::allocated_constant(cs, 0x80));
    if num_zeroes_to_add > 0 {
        let zero = UInt8::allocated_constant(cs, 0x00);
        full_message.extend(std::iter::repeat(zero).take(num_zeroes_to_add));
    }
    let bit_length_be = (input.len() as u64 * 8u64).to_be_bytes();
    for el in bit_length_be {
        let el = UInt8::allocated_constant(cs, el);
        full_message.push(el);
    }
    assert_eq!(full_message.len() % SHA256_BLOCK_SIZE, 0);
    let num_rounds = full_message.len() / SHA256_BLOCK_SIZE;

    let mut final_4bit_chunks = None;

    let mut state = INITIAL_STATE.map(|el| cs.allocate_constant(F::from_u64_unchecked(el as u64)));

    for (round, input_bytes) in full_message.array_chunks::<SHA256_BLOCK_SIZE>().enumerate() {
        let last_round = round == num_rounds - 1;

        let mut message_block = [Variable::placeholder(); 16];
        for (dst, src) in message_block
            .iter_mut()
            .zip(input_bytes.array_chunks::<4>())
        {
            *dst = UInt32::from_be_bytes(cs, *src).variable;
        }
        assert_no_placeholder_variables(&message_block);

        final_4bit_chunks =
            self::round_function::round_function(cs, &mut state, &message_block, last_round);
    }

    let final_4bit_chunks = final_4bit_chunks.expect("must create decompositions");
    let mut output = [Variable::placeholder(); SHA256_DIGEST_SIZE];
    let shift_4 = F::from_u64_unchecked(1u64 << 4);
    let one = cs.allocate_constant(F::ONE);
    for (le_4bit_chunks, dst) in final_4bit_chunks
        .array_chunks::<8>()
        .zip(output.array_chunks_mut::<4>())
    {
        for (dst, [low, high]) in dst.iter_mut().zip(le_4bit_chunks.array_chunks::<2>()) {
            *dst = FmaGateInBaseFieldWithoutConstant::compute_fma(
                cs,
                shift_4,
                (one, *high),
                F::ONE,
                *low,
            );
        }

        dst.reverse();
    }
    assert_no_placeholder_variables(&output);

    unsafe { output.map(|el| UInt8::from_variable_unchecked(el)) }
}

#[cfg(test)]
mod test {
    use std::alloc::Global;

    use super::*;
    use crate::{
        config::CSConfig,
        cs::{
            gates::{ConstantsAllocatorGate, NopGate, ReductionGate},
            implementations::{
                pow::NoPow,
                transcript::{Blake2sTranscript, Transcript},
            },
            oracle::TreeHasher,
            CSGeometry,
        },
        dag::CircuitResolverOpts,
        field::goldilocks::GoldilocksField,
        gadgets::tables::{
            ch4::{create_ch4_table, Ch4Table},
            chunk4bits::{create_4bit_chunk_split_table, Split4BitChunkTable},
            maj4::{create_maj4_table, Maj4Table},
            trixor4::{create_tri_xor_table, TriXor4Table},
        },
        log,
    };
    use blake2::Digest;
    type F = GoldilocksField;
    use crate::cs::traits::gate::GatePlacementStrategy;
    use crate::gadgets::traits::witnessable::WitnessHookable;

    #[test]
    fn test_single_round() {
        test_sha256(42);
    }
    #[test]
    fn test_single_round_exact() {
        test_sha256(64 - 9);
    }
    #[test]
    fn test_two_rounds() {
        test_sha256(64 + 42);
    }
    #[test]
    fn test_two_rounds_exact() {
        test_sha256(64 + 64 - 9);
    }
    #[test]
    fn test_many_rounds() {
        test_sha256(10 * 64 + 42);
    }
    #[test]
    fn test_many_rounds_exact() {
        test_sha256(10 * 64 + 64 - 9);
    }

    fn test_sha256(len: usize) {
        use rand::{Rng, SeedableRng};
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);

        let mut input = vec![];
        for _ in 0..len {
            let byte: u8 = rng.gen();
            input.push(byte);
        }

        let mut hasher = sha2::Sha256::new();
        hasher.update(&input);
        let reference_output = hasher.finalize();

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 20,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 4,
        };

        use crate::config::DevCSConfig;
        type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, 1 << 18);
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = builder.allow_lookup(
            crate::cs::LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                width: 4,
                num_repetitions: 5,
                share_table_id: true,
            },
        );

        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = ReductionGate::<F, 4>::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder =
            NopGate::configure_builder(builder, GatePlacementStrategy::UseGeneralPurposeColumns);

        let mut owned_cs = builder.build(CircuitResolverOpts::new(1 << 20));

        // add tables
        let table = create_tri_xor_table();
        owned_cs.add_lookup_table::<TriXor4Table, 4>(table);

        let table = create_ch4_table();
        owned_cs.add_lookup_table::<Ch4Table, 4>(table);

        let table = create_maj4_table();
        owned_cs.add_lookup_table::<Maj4Table, 4>(table);

        let table = create_4bit_chunk_split_table::<F, 1>();
        owned_cs.add_lookup_table::<Split4BitChunkTable<1>, 4>(table);

        let table = create_4bit_chunk_split_table::<F, 2>();
        owned_cs.add_lookup_table::<Split4BitChunkTable<2>, 4>(table);

        let mut circuit_input = vec![];

        let cs = &mut owned_cs;

        for el in input.iter() {
            let el = UInt8::allocate_checked(cs, *el);
            circuit_input.push(el);
        }

        let output = sha256(cs, &circuit_input);
        let output = hex::encode((output.witness_hook(&*cs))().unwrap());
        let reference_output = hex::encode(reference_output.as_slice());
        assert_eq!(output, reference_output);

        drop(cs);
        owned_cs.pad_and_shrink();
        let mut owned_cs = owned_cs.into_assembly::<Global>();
        use crate::worker::Worker;
        let worker = Worker::new_with_num_threads(8);
        assert!(owned_cs.check_if_satisfied(&worker));
    }

    type P = crate::field::goldilocks::MixedGL;

    // Notes on benches:
    // - we ignore equality asserts because we are lazy, but those are negligible contribution compared to sha256 itself
    // - we use random input (not zeroes), because constant propagation would not help much anyway, and it's more realistic case
    // - allocation (8-bit constraints on bytes) are included in the proof, but why not?
    // - PoW is turned off, because 2^20 bits for blake2s PoW is 30 ms anyway, negligible

    #[test]
    #[ignore]
    fn run_sha256_prover_non_recursive() {
        use crate::blake2::Blake2s256;
        type TreeHash = Blake2s256;
        type Transcript = Blake2sTranscript;
        prove_sha256::<TreeHash, Transcript>(8 * (1 << 10));
    }

    #[test]
    #[ignore]
    fn run_sha256_prover_recursive_mode() {
        use crate::algebraic_props::round_function::AbsorptionModeOverwrite;
        use crate::algebraic_props::sponge::GoldilocksPoseidonSponge;
        use crate::cs::implementations::transcript::GoldilocksPoisedonTranscript;

        type TreeHash = GoldilocksPoseidonSponge<AbsorptionModeOverwrite>;
        type Transcript = GoldilocksPoisedonTranscript;
        prove_sha256::<TreeHash, Transcript>(8 * (1 << 10));
    }

    #[test]
    #[ignore]
    fn run_sha256_prover_recursive_mode_poseidon2() {
        use crate::algebraic_props::round_function::AbsorptionModeOverwrite;
        use crate::algebraic_props::sponge::GoldilocksPoseidon2Sponge;
        use crate::cs::implementations::transcript::GoldilocksPoisedonTranscript;

        type TreeHash = GoldilocksPoseidon2Sponge<AbsorptionModeOverwrite>;
        type Transcript = GoldilocksPoisedonTranscript;
        prove_sha256::<TreeHash, Transcript>(8 * (1 << 10));
    }

    fn prove_sha256<
        T: TreeHasher<GoldilocksField, Output = TR::CompatibleCap>,
        TR: Transcript<GoldilocksField, TransciptParameters = ()>,
    >(
        len: usize,
    ) {
        use crate::config::SetupCSConfig;
        use crate::cs::implementations::prover::ProofConfig;
        use crate::field::goldilocks::GoldilocksExt2;
        use crate::worker::Worker;

        let worker = Worker::new_with_num_threads(8);

        let quotient_lde_degree = 8; // Setup params are not split yet, so it's should be equal to max(FRI lde degree, quotient degree)
        let fri_lde_degree = 8;
        let cap_size = 16;
        let prover_config = ProofConfig {
            fri_lde_factor: fri_lde_degree,
            pow_bits: 0, // not important in practice for anything. 2^20 Blake2s POW uses 30ms
            ..Default::default()
        };

        use rand::{Rng, SeedableRng};
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);

        let mut input = vec![];
        for _ in 0..len {
            let byte: u8 = rng.gen();
            input.push(byte);
        }

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 60,
            num_witness_columns: 0,
            num_constant_columns: 4,
            max_allowed_constraint_degree: 4,
        };

        let max_variables = 1 << 25;
        let max_trace_len = 1 << 19;

        use crate::cs::cs_builder::*;
        use crate::cs::GateConfigurationHolder;
        use crate::cs::StaticToolboxHolder;

        fn configure<
            T: CsBuilderImpl<F, T>,
            GC: GateConfigurationHolder<F>,
            TB: StaticToolboxHolder,
        >(
            builder: CsBuilder<T, F, GC, TB>,
        ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder> {
            let num_lookups = 8;
            let builder = builder.allow_lookup(
                crate::cs::LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                    width: 4,
                    num_repetitions: num_lookups,
                    share_table_id: true,
                },
            );
            let builder = ConstantsAllocatorGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = FmaGateInBaseFieldWithoutConstant::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = ReductionGate::<F, 4>::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );
            let builder = NopGate::configure_builder(
                builder,
                GatePlacementStrategy::UseGeneralPurposeColumns,
            );

            builder
        }

        {
            // satisfiability check
            use crate::config::DevCSConfig;
            type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;

            let builder_impl =
                CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, max_trace_len);
            let builder = new_builder::<_, F>(builder_impl);

            let builder = configure(builder);
            let mut owned_cs = builder.build(CircuitResolverOpts::new(max_variables));

            // add tables
            let table = create_tri_xor_table();
            owned_cs.add_lookup_table::<TriXor4Table, 4>(table);

            let table = create_ch4_table();
            owned_cs.add_lookup_table::<Ch4Table, 4>(table);

            let table = create_maj4_table();
            owned_cs.add_lookup_table::<Maj4Table, 4>(table);

            let table = create_4bit_chunk_split_table::<F, 1>();
            owned_cs.add_lookup_table::<Split4BitChunkTable<1>, 4>(table);

            let table = create_4bit_chunk_split_table::<F, 2>();
            owned_cs.add_lookup_table::<Split4BitChunkTable<2>, 4>(table);

            let mut circuit_input = vec![];

            let cs = &mut owned_cs;

            for el in input.iter() {
                let el = UInt8::allocate_checked(cs, *el);
                circuit_input.push(el);
            }

            let _output = sha256(cs, &circuit_input);
            drop(cs);
            let (_, _padding_hint) = owned_cs.pad_and_shrink();
            let mut owned_cs = owned_cs.into_assembly::<Global>();
            assert!(owned_cs.check_if_satisfied(&worker));
        }

        use crate::cs::cs_builder_reference::*;
        use crate::cs::cs_builder_verifier::*;

        type RCfgS = <SetupCSConfig as CSConfig>::ResolverConfig;

        let builder_impl =
            CsReferenceImplementationBuilder::<F, P, SetupCSConfig>::new(geometry, max_trace_len);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut owned_cs = builder.build(CircuitResolverOpts::new(max_variables));

        // add tables
        let table = create_tri_xor_table();
        owned_cs.add_lookup_table::<TriXor4Table, 4>(table);

        let table = create_ch4_table();
        owned_cs.add_lookup_table::<Ch4Table, 4>(table);

        let table = create_maj4_table();
        owned_cs.add_lookup_table::<Maj4Table, 4>(table);

        let table = create_4bit_chunk_split_table::<F, 1>();
        owned_cs.add_lookup_table::<Split4BitChunkTable<1>, 4>(table);

        let table = create_4bit_chunk_split_table::<F, 2>();
        owned_cs.add_lookup_table::<Split4BitChunkTable<2>, 4>(table);

        let mut circuit_input = vec![];

        let cs = &mut owned_cs;

        for el in input.iter() {
            let el = UInt8::allocate_checked(cs, *el);
            circuit_input.push(el);
        }

        let _output = sha256(cs, &circuit_input);
        drop(cs);
        let (_, padding_hint) = owned_cs.pad_and_shrink();
        let owned_cs = owned_cs.into_assembly::<Global>();
        owned_cs.print_gate_stats();

        let (base_setup, setup, vk, setup_tree, vars_hint, wits_hint) =
            owned_cs.get_full_setup::<T>(&worker, quotient_lde_degree, cap_size);

        use crate::config::ProvingCSConfig;
        type RCfgP = <ProvingCSConfig as CSConfig>::ResolverConfig;

        let builder_impl =
            CsReferenceImplementationBuilder::<F, P, ProvingCSConfig>::new(geometry, max_trace_len);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let mut owned_cs = builder.build(CircuitResolverOpts::new(max_variables));

        // add tables
        let table = create_tri_xor_table();
        owned_cs.add_lookup_table::<TriXor4Table, 4>(table);

        let table = create_ch4_table();
        owned_cs.add_lookup_table::<Ch4Table, 4>(table);

        let table = create_maj4_table();
        owned_cs.add_lookup_table::<Maj4Table, 4>(table);

        let table = create_4bit_chunk_split_table::<F, 1>();
        owned_cs.add_lookup_table::<Split4BitChunkTable<1>, 4>(table);

        let table = create_4bit_chunk_split_table::<F, 2>();
        owned_cs.add_lookup_table::<Split4BitChunkTable<2>, 4>(table);

        // create setup
        let now = std::time::Instant::now();
        log!("Start synthesis for proving");
        let mut circuit_input = vec![];

        let cs = &mut owned_cs;

        for el in input.iter() {
            let el = UInt8::allocate_checked(cs, *el);
            circuit_input.push(el);
        }

        let _output = sha256(cs, &circuit_input);
        dbg!(now.elapsed());
        log!("Synthesis for proving is done");
        owned_cs.pad_and_shrink_using_hint(&padding_hint);
        let mut owned_cs = owned_cs.into_assembly::<Global>();

        log!("Proving");
        let witness_set = owned_cs.take_witness_using_hints(&worker, &vars_hint, &wits_hint);
        log!("Witness is resolved");

        let now = std::time::Instant::now();

        let proof = owned_cs.prove_cpu_basic::<GoldilocksExt2, TR, T, NoPow>(
            &worker,
            witness_set,
            &base_setup,
            &setup,
            &setup_tree,
            &vk,
            prover_config,
            (),
        );

        log!("Proving is done, taken {:?}", now.elapsed());

        let builder_impl = CsVerifierBuilder::<F, GoldilocksExt2>::new_from_parameters(geometry);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = configure(builder);
        let verifier = builder.build(());

        let is_valid = verifier.verify::<T, TR, NoPow>((), &vk, &proof);

        assert!(is_valid);
    }
}
