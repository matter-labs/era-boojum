use super::*;

use std::fmt::Debug;
use ethereum_types::*;

pub trait RangeTracker: 'static + Send + Sync + Clone + Debug {
    type DoubleWidthResult: 'static + Send + Sync + Clone + Debug;

    fn add_range(&self, other: &Self) -> Self::DoubleWidthResult;
    fn from_u64_words(words: &[u64]) -> Self;
    fn mul_with_range(&self, other: &Self) -> Self::DoubleWidthResult;
    fn as_u64_words_into(&self, dst: &mut [u64]);
    fn double_width_result_as_u64_words_into(src: &Self::DoubleWidthResult, dst: &mut [u64]);
    fn double_width_into_single_width(src: Self::DoubleWidthResult) -> Result<Self, Self::DoubleWidthResult>;
}

impl RangeTracker for U256 {
    type DoubleWidthResult = U512;

    fn add_range(&self, other: &Self) -> Self::DoubleWidthResult {
        let (low, of) = self.overflowing_add(*other);
        U512([low.0[0], low.0[1], low.0[2], low.0[3], of as u64, 0, 0, 0])
    }
    fn from_u64_words(words: &[u64]) -> Self {
        todo!()
    }
    fn mul_with_range(&self, other: &Self) -> Self::DoubleWidthResult {
        todo!()
    }
    fn as_u64_words_into(&self, dst: &mut [u64]) {
        todo!()
    }
    fn double_width_result_as_u64_words_into(src: &Self::DoubleWidthResult, dst: &mut [u64]) {
        todo!()
    }
    fn double_width_into_single_width(src: Self::DoubleWidthResult) -> Result<Self, Self::DoubleWidthResult> {
        todo!()
    }
}