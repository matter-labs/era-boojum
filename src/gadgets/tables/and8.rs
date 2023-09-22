use super::*;

const TABLE_NAME: &str = "AND8 table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct And8Table;

pub fn create_and8_table<F: SmallField>() -> LookupTable<F, 3> {
    let mut all_keys = Vec::with_capacity(1 << 16);
    for a in 0..=u8::MAX {
        for b in 0..=u8::MAX {
            let key = smallvec::smallvec![
                F::from_u64_unchecked(a as u64),
                F::from_u64_unchecked(b as u64)
            ];
            all_keys.push(key);
        }
    }
    LookupTable::new_from_keys_and_generation_function(
        &all_keys,
        TABLE_NAME.to_string(),
        2,
        |keys| {
            let a = keys[0].as_u64_reduced() as u8;
            let b = keys[1].as_u64_reduced() as u8;

            let and_result = a & b;
            let value = and_result as u64;

            smallvec::smallvec![F::from_u64_unchecked(value)]
        },
    )
}
