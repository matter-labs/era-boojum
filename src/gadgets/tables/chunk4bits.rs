use super::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Split4BitChunkTable<const SPLIT_AT: usize>;

pub fn create_4bit_chunk_split_table<F: SmallField, const SPLIT_AT: usize>() -> LookupTable<F, 4> {
    assert!(SPLIT_AT > 0);
    assert!(SPLIT_AT <= 2); // it's a symmetric table
    let mut all_keys = Vec::with_capacity(1 << 4);
    for a in 0..(1u8 << 4) {
        let key = smallvec::smallvec![F::from_u64_unchecked(a as u64),];
        all_keys.push(key);
    }

    let mask = (1u8 << SPLIT_AT) - 1;

    LookupTable::new_from_keys_and_generation_function(
        &all_keys,
        format!("4-bit chunk split at {}", SPLIT_AT),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced() as u8;

            let low = a & mask;
            let high = a >> SPLIT_AT;

            let reversed = (low << (4 - SPLIT_AT)) | high;

            smallvec::smallvec![
                F::from_u64_unchecked(low as u64),
                F::from_u64_unchecked(high as u64),
                F::from_u64_unchecked(reversed as u64),
            ]
        },
    )
}
