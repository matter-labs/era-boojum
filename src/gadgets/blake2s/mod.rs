use super::*;
use crate::cs::traits::cs::ConstraintSystem;
use crate::gadgets::u8::UInt8;
use std::mem::MaybeUninit;

pub const BLAKE2S_ROUNDS: usize = 10;
pub const BLAKE2S_BLOCK_SIZE: usize = 64;
pub const BLAKE2S_DIGEST_SIZE: usize = 32;

pub const STATE_WIDTH_IN_U32_WORDS: usize = 8;
pub const BLOCK_WIDTH_IN_U32_WORDS: usize = 16;

pub const IV: [u32; 8] = [
    0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
];

pub const IV_0_TWIST: u32 = 0x6A09E667 ^ 0x01010000 ^ 32;

pub const SIGMAS: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

pub mod mixing_function;
pub mod round_function;

pub fn blake2s<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: &[UInt8<F>],
) -> [UInt8<F>; BLAKE2S_DIGEST_SIZE] {
    // create an initial state
    use crate::cs::gates::ConstantAllocatableCS;
    use crate::gadgets::blake2s::mixing_function::Word;

    assert!(input.len() <= u32::MAX as usize);

    let input_len = input.len();

    let mut state: [_; 8] = std::array::from_fn(|idx| {
        let word = if idx == 0 { IV_0_TWIST } else { IV[idx] };

        let le_bytes = word.to_le_bytes();
        let le_bytes = le_bytes.map(|el| cs.allocate_constant(F::from_u64_unchecked(el as u64)));

        let state_word = unsafe {
            Word {
                inner: le_bytes.map(|el| UInt8::from_variable_unchecked(el)),
            }
        };

        state_word
    });

    let mut num_rounds = input.len() / BLAKE2S_BLOCK_SIZE;
    if input.len() % BLAKE2S_BLOCK_SIZE != 0 {
        num_rounds += 1;
    }

    use self::round_function::*;

    let mut input_chunks = input.array_chunks::<BLAKE2S_BLOCK_SIZE>();
    let mut offset = 0;
    if num_rounds > 1 {
        for _round in 0..(num_rounds - 1) {
            offset += BLAKE2S_BLOCK_SIZE as u32;

            let chunk = input_chunks.next().unwrap();
            let mut block = [MaybeUninit::<Word<F>>::uninit(); 16];
            for (dst, src) in block.iter_mut().zip(chunk.array_chunks::<4>()) {
                let word = Word { inner: *src };
                dst.write(word);
            }

            let block = unsafe { block.map(|el| el.assume_init()) };

            let control = Blake2sControl::FixedLength {
                offset,
                is_last_block: false,
            };

            blake2s_round_function(cs, &mut state, &block, control);
        }
    }

    // final block
    let last_block = if let Some(full_chunk) = input_chunks.next() {
        assert!(input_chunks.remainder().is_empty());

        *full_chunk
    } else {
        let zero = UInt8::<F>::allocated_constant(cs, 0u8);
        let mut full_buffer = [zero; BLAKE2S_BLOCK_SIZE];
        let remainder = input_chunks.remainder();
        let len = remainder.len();
        assert!(len > 0);
        assert!(len < BLAKE2S_BLOCK_SIZE);
        full_buffer[..len].copy_from_slice(remainder);

        full_buffer
    };

    let mut block = [MaybeUninit::<Word<F>>::uninit(); 16];
    for (dst, src) in block.iter_mut().zip(last_block.array_chunks::<4>()) {
        let word = Word { inner: *src };
        dst.write(word);
    }

    let block = unsafe { block.map(|el| el.assume_init()) };

    let control = Blake2sControl::FixedLength {
        offset: input_len as u32,
        is_last_block: true,
    };

    blake2s_round_function(cs, &mut state, &block, control);

    // copy back

    let mut result = [MaybeUninit::<UInt8<F>>::uninit(); BLAKE2S_DIGEST_SIZE];
    for (dst, src) in result.array_chunks_mut::<4>().zip(state[..8].iter()) {
        for i in 0..4 {
            dst[i].write(src.inner[i]);
        }
    }

    unsafe { result.map(|el| el.assume_init()) }
}

#[cfg(test)]
mod test {
    use std::alloc::Global;

    use super::*;
    use crate::{
        config::CSConfig,
        cs::{gates::ConstantsAllocatorGate, CSGeometry},
        dag::CircuitResolverOpts,
        field::goldilocks::GoldilocksField,
        gadgets::tables::{
            byte_split::{create_byte_split_table, ByteSplitTable},
            xor8::{create_xor8_table, Xor8Table},
        },
    };
    use blake2::Digest;
    type F = GoldilocksField;
    use crate::cs::gates::u32_tri_add_carry_as_chunk::U32TriAddCarryAsChunkGate;
    use crate::cs::traits::gate::GatePlacementStrategy;
    use crate::gadgets::traits::witnessable::WitnessHookable;

    #[test]
    fn test_single_round() {
        test_blake2s(42);
    }
    #[test]
    fn test_single_round_exact() {
        test_blake2s(64);
    }
    #[test]
    fn test_two_rounds() {
        test_blake2s(64 + 42);
    }
    #[test]
    fn test_two_rounds_exact() {
        test_blake2s(64 + 64);
    }
    #[test]
    fn test_many_rounds() {
        test_blake2s(10 * 64 + 42);
    }
    #[test]
    fn test_many_rounds_exact() {
        test_blake2s(10 * 64 + 64);
    }

    fn test_blake2s(len: usize) {
        use rand::{Rng, SeedableRng};
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);

        let mut input = vec![];
        for _ in 0..len {
            let byte: u8 = rng.gen();
            input.push(byte);
        }

        let mut hasher = blake2::Blake2s256::new();
        hasher.update(&input);
        let reference_output = hasher.finalize();

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 20,
            num_witness_columns: 0,
            num_constant_columns: 2,
            max_allowed_constraint_degree: 2,
        };

        use crate::config::DevCSConfig;
        type RCfg = <DevCSConfig as CSConfig>::ResolverConfig;
        use crate::cs::cs_builder_reference::*;
        let builder_impl =
            CsReferenceImplementationBuilder::<F, F, DevCSConfig>::new(geometry, 1 << 17);
        use crate::cs::cs_builder::new_builder;
        let builder = new_builder::<_, F>(builder_impl);

        let builder = builder.allow_lookup(
            crate::cs::LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                width: 3,
                num_repetitions: 5,
                share_table_id: true,
            },
        );
        let builder = ConstantsAllocatorGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );
        let builder = U32TriAddCarryAsChunkGate::configure_builder(
            builder,
            GatePlacementStrategy::UseGeneralPurposeColumns,
        );

        let mut owned_cs = builder.build(CircuitResolverOpts::new(1 << 20));

        // add tables
        let table = create_xor8_table();
        owned_cs.add_lookup_table::<Xor8Table, 3>(table);

        let table = create_byte_split_table::<F, 4>();
        owned_cs.add_lookup_table::<ByteSplitTable<4>, 3>(table);

        let table = create_byte_split_table::<F, 7>();
        owned_cs.add_lookup_table::<ByteSplitTable<7>, 3>(table);

        let table = create_byte_split_table::<F, 1>();
        owned_cs.add_lookup_table::<ByteSplitTable<1>, 3>(table);

        let mut circuit_input = vec![];

        let cs = &mut owned_cs;

        for pair in input.array_chunks::<2>() {
            let pair = UInt8::allocate_pair(cs, *pair);
            circuit_input.extend(pair);
        }

        let output = blake2s(cs, &circuit_input);
        let output = hex::encode((output.witness_hook(cs))().unwrap());
        let reference_output = hex::encode(reference_output.as_slice());
        assert_eq!(output, reference_output);

        drop(cs);
        let _owned_cs = owned_cs.into_assembly::<Global>();
    }
}
