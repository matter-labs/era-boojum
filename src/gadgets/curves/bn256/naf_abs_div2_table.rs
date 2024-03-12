use crate::cs::implementations::lookup_table::LookupTable;
use crate::field::SmallField;
use derivative::*;

const TABLE_NAME: &'static str = "NAFABSDIV2 table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NafAbsDiv2Table;

// Quick table lookups in wNAF circuit
pub fn create_naf_abs_div2_table<F: SmallField>() -> LookupTable<F, 3> {
    let mut all_keys = Vec::with_capacity(1 << 8);
    for a in 0..=u8::MAX {
        let key = smallvec::smallvec![F::from_u64_unchecked(a as u64)];
        all_keys.push(key);
    }
    LookupTable::new_from_keys_and_generation_function(
        &all_keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let a = keys[0].as_u64_reduced() as i8;
            // we need unsigned abs, to handle i8::MIN
            let v = a.unsigned_abs() >> 1;

            smallvec::smallvec![F::from_u64_unchecked(v as u64), F::from_u64_unchecked(0u64)]
        },
    )
}
