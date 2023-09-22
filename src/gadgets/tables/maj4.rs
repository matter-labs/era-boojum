use super::*;

const TABLE_NAME: &str = "Maj4 table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Maj4Table;

pub fn create_maj4_table<F: SmallField>() -> LookupTable<F, 4> {
    const MASK: u8 = (1u8 << 4) - 1;

    let mut all_keys = Vec::with_capacity(16 * 16 * 16);
    let upper_bound = 1u8 << 4;
    for a in 0..upper_bound {
        for b in 0..upper_bound {
            for c in 0..upper_bound {
                let key = smallvec::smallvec![
                    F::from_u64_unchecked(a as u64),
                    F::from_u64_unchecked(b as u64),
                    F::from_u64_unchecked(c as u64)
                ];
                all_keys.push(key);
            }
        }
    }
    LookupTable::new_from_keys_and_generation_function(
        &all_keys,
        TABLE_NAME.to_string(),
        3,
        |keys| {
            let a = keys[0].as_u64_reduced() as u8;
            let b = keys[1].as_u64_reduced() as u8;
            let c = keys[2].as_u64_reduced() as u8;

            let maj_result = (a & b) ^ (a & c) ^ (b & c);
            let value = (maj_result & MASK) as u64;

            smallvec::smallvec![F::from_u64_unchecked(value)]
        },
    )
}
