use super::*;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RangeCheckTable<const N: usize>;

pub fn create_range_check_table<F: SmallField, const N: usize>() -> LookupTable<F, 1> {
    assert!(N > 0);
    let mut all_keys = Vec::with_capacity(1 << N);
    for a in 0..(1 << N) {
        let key = smallvec::smallvec![F::from_u64_unchecked(a as u64),];
        all_keys.push(key);
    }
    LookupTable::new_from_keys_and_generation_function(
        &all_keys,
        format!("Range check {} bits table", N),
        1,
        |_keys| smallvec::smallvec![],
    )
}
