use std::collections::BTreeMap;

use crate::cs::traits::cs::ConstraintSystem;

use super::*;
use arrayvec::ArrayVec;

#[derive(Derivative)]
#[derivative(Clone, PartialEq, Eq)]
pub enum LookupTableWrapper<F: SmallField> {
    W1(LookupTable<F, 1>),
    W2(LookupTable<F, 2>),
    W3(LookupTable<F, 3>),
    W4(LookupTable<F, 4>),
    W5(LookupTable<F, 5>),
    W6(LookupTable<F, 6>),
    W7(LookupTable<F, 7>),
    W8(LookupTable<F, 8>),
}

impl<F: SmallField> LookupTableWrapper<F> {
    pub fn width(&self) -> usize {
        match self {
            Self::W1(..) => 1,
            Self::W2(..) => 2,
            Self::W3(..) => 3,
            Self::W4(..) => 4,
            Self::W5(..) => 5,
            Self::W6(..) => 6,
            Self::W7(..) => 7,
            Self::W8(..) => 8,
        }
    }

    pub fn content_at_row(&self, row: usize) -> &[F] {
        match self {
            Self::W1(inner) => inner.content_at_row(row),
            Self::W2(inner) => inner.content_at_row(row),
            Self::W3(inner) => inner.content_at_row(row),
            Self::W4(inner) => inner.content_at_row(row),
            Self::W5(inner) => inner.content_at_row(row),
            Self::W6(inner) => inner.content_at_row(row),
            Self::W7(inner) => inner.content_at_row(row),
            Self::W8(inner) => inner.content_at_row(row),
        }
    }

    pub fn pad_into_cs<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        num_repetitions: usize,
        as_table_id: u32,
    ) {
        match self {
            Self::W1(inner) => inner.pad_into_cs(cs, num_repetitions, as_table_id),
            Self::W2(inner) => inner.pad_into_cs(cs, num_repetitions, as_table_id),
            Self::W3(inner) => inner.pad_into_cs(cs, num_repetitions, as_table_id),
            Self::W4(inner) => inner.pad_into_cs(cs, num_repetitions, as_table_id),
            Self::W5(inner) => inner.pad_into_cs(cs, num_repetitions, as_table_id),
            Self::W6(inner) => inner.pad_into_cs(cs, num_repetitions, as_table_id),
            Self::W7(inner) => inner.pad_into_cs(cs, num_repetitions, as_table_id),
            Self::W8(inner) => inner.pad_into_cs(cs, num_repetitions, as_table_id),
        }
    }

    pub fn table_size(&self) -> usize {
        match self {
            Self::W1(inner) => inner.table_size(),
            Self::W2(inner) => inner.table_size(),
            Self::W3(inner) => inner.table_size(),
            Self::W4(inner) => inner.table_size(),
            Self::W5(inner) => inner.table_size(),
            Self::W6(inner) => inner.table_size(),
            Self::W7(inner) => inner.table_size(),
            Self::W8(inner) => inner.table_size(),
        }
    }

    pub fn lookup_value<const VALUES: usize>(&self, keys: &[F]) -> (u32, ArrayVec<F, VALUES>) {
        match self {
            Self::W1(inner) => inner.lookup_value(keys),
            Self::W2(inner) => inner.lookup_value(keys),
            Self::W3(inner) => inner.lookup_value(keys),
            Self::W4(inner) => inner.lookup_value(keys),
            Self::W5(inner) => inner.lookup_value(keys),
            Self::W6(inner) => inner.lookup_value(keys),
            Self::W7(inner) => inner.lookup_value(keys),
            Self::W8(inner) => inner.lookup_value(keys),
        }
    }

    pub fn lookup_row(&self, keys: &[F]) -> u32 {
        match self {
            Self::W1(inner) => inner.lookup_row(keys),
            Self::W2(inner) => inner.lookup_row(keys),
            Self::W3(inner) => inner.lookup_row(keys),
            Self::W4(inner) => inner.lookup_row(keys),
            Self::W5(inner) => inner.lookup_row(keys),
            Self::W6(inner) => inner.lookup_row(keys),
            Self::W7(inner) => inner.lookup_row(keys),
            Self::W8(inner) => inner.lookup_row(keys),
        }
    }

    pub fn num_keys(&self) -> usize {
        match self {
            Self::W1(inner) => inner.num_keys(),
            Self::W2(inner) => inner.num_keys(),
            Self::W3(inner) => inner.num_keys(),
            Self::W4(inner) => inner.num_keys(),
            Self::W5(inner) => inner.num_keys(),
            Self::W6(inner) => inner.num_keys(),
            Self::W7(inner) => inner.num_keys(),
            Self::W8(inner) => inner.num_keys(),
        }
    }

    pub fn num_values(&self) -> usize {
        match self {
            Self::W1(inner) => inner.num_values(),
            Self::W2(inner) => inner.num_values(),
            Self::W3(inner) => inner.num_values(),
            Self::W4(inner) => inner.num_values(),
            Self::W5(inner) => inner.num_values(),
            Self::W6(inner) => inner.num_values(),
            Self::W7(inner) => inner.num_values(),
            Self::W8(inner) => inner.num_values(),
        }
    }
}

pub trait Wrappable<F: SmallField>: 'static {
    fn into_wrapper(self) -> LookupTableWrapper<F>;
}

impl<F: SmallField> Wrappable<F> for LookupTable<F, 1> {
    fn into_wrapper(self) -> LookupTableWrapper<F> {
        LookupTableWrapper::W1(self)
    }
}

impl<F: SmallField> Wrappable<F> for LookupTable<F, 2> {
    fn into_wrapper(self) -> LookupTableWrapper<F> {
        LookupTableWrapper::W2(self)
    }
}

impl<F: SmallField> Wrappable<F> for LookupTable<F, 3> {
    fn into_wrapper(self) -> LookupTableWrapper<F> {
        LookupTableWrapper::W3(self)
    }
}

impl<F: SmallField> Wrappable<F> for LookupTable<F, 4> {
    fn into_wrapper(self) -> LookupTableWrapper<F> {
        LookupTableWrapper::W4(self)
    }
}

impl<F: SmallField> Wrappable<F> for LookupTable<F, 5> {
    fn into_wrapper(self) -> LookupTableWrapper<F> {
        LookupTableWrapper::W5(self)
    }
}

impl<F: SmallField> Wrappable<F> for LookupTable<F, 6> {
    fn into_wrapper(self) -> LookupTableWrapper<F> {
        LookupTableWrapper::W6(self)
    }
}

impl<F: SmallField> Wrappable<F> for LookupTable<F, 7> {
    fn into_wrapper(self) -> LookupTableWrapper<F> {
        LookupTableWrapper::W7(self)
    }
}

impl<F: SmallField> Wrappable<F> for LookupTable<F, 8> {
    fn into_wrapper(self) -> LookupTableWrapper<F> {
        LookupTableWrapper::W8(self)
    }
}

// Lookup table of width N, where N only includes "content"
// and not the table type marker
#[derive(Derivative)]
#[derivative(Clone, Eq)]
pub struct LookupTable<F: SmallField, const N: usize> {
    lookup_cache: BTreeMap<LookupKey<F, N>, usize>, // lookup from keys into row index
    content_cache: BTreeMap<ContentLookupKey<F, N>, usize>, // lookup from keys into row index
    name: String,
    num_key_columns: usize,
    num_value_columns: usize,
    content: Vec<[F; N]>,
}

#[derive(Derivative)]
#[derivative(Clone, PartialEq, Eq, Debug)]
struct LookupKey<F: SmallField, const N: usize>(ArrayVec<F, N>);

impl<F: SmallField, const N: usize> LookupKey<F, N> {
    fn from_keys(keys: &[F]) -> Self {
        let mut new = ArrayVec::new_const();
        for el in keys.iter().copied() {
            new.push(el);
        }

        Self(new)
    }
}

impl<F: SmallField, const N: usize> PartialOrd for LookupKey<F, N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: SmallField, const N: usize> Ord for LookupKey<F, N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        debug_assert_eq!(self.0.len(), other.0.len());
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            match a.as_u64_reduced().cmp(&b.as_u64_reduced()) {
                std::cmp::Ordering::Equal => {
                    continue;
                }
                ordering => {
                    return ordering;
                }
            }
        }

        std::cmp::Ordering::Equal
    }
}

#[derive(Derivative)]
#[derivative(Clone, PartialEq, Eq, Debug)]
struct ContentLookupKey<F: SmallField, const N: usize>([F; N]);

impl<F: SmallField, const N: usize> PartialOrd for ContentLookupKey<F, N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: SmallField, const N: usize> Ord for ContentLookupKey<F, N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        debug_assert_eq!(self.0.len(), other.0.len());
        for (a, b) in self.0.iter().zip(other.0.iter()) {
            match a.as_u64_reduced().cmp(&b.as_u64_reduced()) {
                std::cmp::Ordering::Equal => {
                    continue;
                }
                ordering => {
                    return ordering;
                }
            }
        }

        std::cmp::Ordering::Equal
    }
}

impl<F: SmallField, const N: usize> PartialEq<LookupTable<F, N>> for LookupTable<F, N> {
    fn eq(&self, other: &LookupTable<F, N>) -> bool {
        // we only need to compare content, that is canonical
        self.content.eq(&other.content)
    }
}

impl<F: SmallField, const N: usize> LookupTable<F, N> {
    fn sort_content(content: &mut [[F; N]]) {
        content.sort_by(|a, b| {
            for i in 0..N {
                match a[i].as_u64_reduced().cmp(&b[i].as_u64_reduced()) {
                    std::cmp::Ordering::Equal => {
                        continue;
                    }
                    a => {
                        return a;
                    }
                }
            }

            panic!("most likely duplicate entries in the table");
        });
    }

    fn compute_cache(
        content: &[[F; N]],
        num_key_columns: usize,
    ) -> BTreeMap<LookupKey<F, N>, usize> {
        assert!(num_key_columns <= N);
        let mut result = BTreeMap::new();
        for (idx, row) in content.iter().enumerate() {
            let mut key = ArrayVec::<F, N>::new();
            for idx in 0..num_key_columns {
                key.push(row[idx]);
            }
            let key = LookupKey(key);
            let existing = result.insert(key, idx);
            assert!(existing.is_none(), "can not compute lookup cache if using only {} first columns out of {} as logical key", num_key_columns, N);
        }

        result
    }

    pub fn new_from_content(content: Vec<[F; N]>, name: String, num_key_columns: usize) -> Self {
        assert!(num_key_columns <= N);
        let num_value_columns = N - num_key_columns;

        // sort content
        let mut content = content;
        Self::sort_content(&mut content);

        let lookup_cache = Self::compute_cache(&content, num_key_columns);
        let mut content_cache = BTreeMap::new();
        for (idx, el) in content.iter().enumerate() {
            content_cache.insert(ContentLookupKey(*el), idx);
        }

        Self {
            content,
            content_cache,
            name,
            num_key_columns,
            num_value_columns,
            lookup_cache,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn table_size(&self) -> usize {
        self.content.len()
    }

    pub fn new_from_keys_and_generation_function<G: Fn(&[F]) -> SmallVec<[F; N]>>(
        all_keys: &Vec<SmallVec<[F; N]>>,
        name: String,
        num_key_columns: usize,
        generation_function: G,
    ) -> Self {
        let mut content = Vec::with_capacity(all_keys.len());
        for key in all_keys.iter() {
            let values = generation_function(&key[..]);
            let mut row = [F::ZERO; N];
            row[..num_key_columns].copy_from_slice(&key[..]);
            row[num_key_columns..].copy_from_slice(&values[..]);
            content.push(row);
        }

        Self::new_from_content(content, name, num_key_columns)
    }

    pub fn lookup_value<const VALUES: usize>(&self, keys: &[F]) -> (u32, ArrayVec<F, VALUES>) {
        debug_assert!(VALUES < N);
        debug_assert_eq!(keys.len(), self.num_key_columns);
        let key = LookupKey::from_keys(keys);
        let Some(row_idx) = self.lookup_cache.get(&key).copied() else {
            panic!("There is no value for key {:?}", keys);
        };

        let mut result = ArrayVec::new();
        result
            .try_extend_from_slice(&self.content[row_idx][self.num_key_columns..])
            .expect("must have enough capacity");

        (row_idx as u32, result)
    }

    pub fn lookup_row(&self, entry: &[F]) -> u32 {
        debug_assert_eq!(entry.len(), N);
        let mut key = [F::ZERO; N];
        key.copy_from_slice(entry);
        let key = ContentLookupKey(key);
        let Some(row_idx) = self.content_cache.get(&key).copied() else {
            panic!(
                "There is no entry for key+value {:?} in table {}",
                key, &self.name
            );
        };

        row_idx as u32
    }

    pub fn num_values(&self) -> usize {
        self.num_value_columns
    }

    pub fn num_keys(&self) -> usize {
        self.num_key_columns
    }

    pub fn content_at_row(&self, row: usize) -> &[F] {
        &self.content[row][..]
    }

    pub(crate) fn pad_into_cs<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        num_repetitions: usize,
        as_table_id: u32,
    ) {
        let padding_entry = self.content[1];
        let entries = cs.alloc_multiple_variables_from_witnesses(padding_entry);
        for _ in 0..num_repetitions {
            cs.enforce_lookup(as_table_id, &entries);
        }
    }
}
