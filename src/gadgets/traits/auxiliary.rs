use super::allocatable::CSAllocatable;
use super::*;

pub trait PrettyComparison<F: SmallField>: CSAllocatable<F> {
    fn find_diffs(a: &Self::Witness, b: &Self::Witness) -> Vec<String>;
}

impl<F: SmallField> PrettyComparison<F> for () {
    fn find_diffs(_a: &Self::Witness, _b: &Self::Witness) -> Vec<String> {
        vec![]
    }
}
