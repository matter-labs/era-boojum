use super::*;

const TABLE_NAME: &str = "Range check 16 bits table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RangeCheck16BitsTable;

pub fn create_range_check_16_bits_table<F: SmallField>() -> LookupTable<F, 1> {
    let mut all_keys = Vec::with_capacity(1 << 16);
    for a in 0..=u16::MAX {
        let key = smallvec::smallvec![F::from_u64_unchecked(a as u64),];
        all_keys.push(key);
    }
    LookupTable::new_from_keys_and_generation_function(
        &all_keys,
        TABLE_NAME.to_string(),
        1,
        |_keys| smallvec::smallvec![],
    )
}
