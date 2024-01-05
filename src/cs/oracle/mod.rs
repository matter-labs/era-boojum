use super::*;
pub mod merkle_tree;

pub trait FlattenIntoBase<T: Sized, const N: usize> {
    fn into_base(self) -> [T; N];
}

impl<F: SmallField> FlattenIntoBase<F, 1> for &F {
    #[inline(always)]
    fn into_base(self) -> [F; 1] {
        [*self]
    }
}

impl<F: SmallField> FlattenIntoBase<F, 1> for F {
    #[inline(always)]
    fn into_base(self) -> [F; 1] {
        [self]
    }
}

// NOTE: we need to take care over reduction when representing as bytes

impl<F: SmallField> FlattenIntoBase<u8, 8> for &F {
    #[inline(always)]
    fn into_base(self) -> [u8; 8] {
        self.as_u64_reduced().to_le_bytes()
    }
}

use crate::algebraic_props::round_function::AbsorptionModeTrait;
use crate::algebraic_props::round_function::AlgebraicRoundFunction;
use crate::algebraic_props::sponge::SimpleAlgebraicSponge;
use crate::field::ExtensionField;
use crate::field::FieldExtension;
use crate::field::PrimeField;

impl<F: SmallField, E: FieldExtension<2, BaseField = F>> FlattenIntoBase<F, 2>
    for &ExtensionField<F, 2, E>
{
    #[inline(always)]
    fn into_base(self) -> [F; 2] {
        self.into_coeffs_in_base()
    }
}

impl<F: SmallField, E: FieldExtension<2, BaseField = F>> FlattenIntoBase<F, 2>
    for ExtensionField<F, 2, E>
{
    #[inline(always)]
    fn into_base(self) -> [F; 2] {
        self.into_coeffs_in_base()
    }
}

impl<F: SmallField, E: FieldExtension<2, BaseField = F>> FlattenIntoBase<u8, 16>
    for &ExtensionField<F, 2, E>
{
    #[inline]
    fn into_base(self) -> [u8; 16] {
        let [a, b] = self.into_coeffs_in_base();
        let mut result = [0u8; 16];
        result[0..8].copy_from_slice(&a.as_u64_reduced().to_le_bytes());
        result[8..16].copy_from_slice(&b.as_u64_reduced().to_le_bytes());

        result
    }
}

impl<F: SmallField, E: FieldExtension<2, BaseField = F>> FlattenIntoBase<u8, 16>
    for ExtensionField<F, 2, E>
{
    #[inline]
    fn into_base(self) -> [u8; 16] {
        let [a, b] = self.into_coeffs_in_base();
        let mut result = [0u8; 16];
        result[0..8].copy_from_slice(&a.as_u64_reduced().to_le_bytes());
        result[8..16].copy_from_slice(&b.as_u64_reduced().to_le_bytes());

        result
    }
}

pub trait TreeHasher<B: Sized>: 'static + Clone + Send + Sync {
    type Output: Sized
        + 'static
        + Clone
        + Copy
        + Sync
        + Send
        + PartialEq
        + Eq
        + std::fmt::Debug
        + std::hash::Hash;
    fn new() -> Self;
    fn placeholder_output() -> Self::Output;
    fn accumulate_into_leaf(&mut self, value: &B);
    fn finalize_into_leaf_hash_and_reset(&mut self) -> Self::Output;
    fn hash_into_leaf<'a, S: IntoIterator<Item = &'a B>>(source: S) -> Self::Output
    where
        B: 'a;
    fn hash_into_leaf_owned<S: IntoIterator<Item = B>>(source: S) -> Self::Output;
    fn hash_into_node(left: &Self::Output, right: &Self::Output, depth: usize) -> Self::Output;
    fn normalize_output(_dst: &mut Self::Output) {
        // empty in general case
    }
    fn batch_normalize_outputs(dst: &mut [Self::Output]) {
        for el in dst.iter_mut() {
            Self::normalize_output(el);
        }
    }
}

impl<
        F: SmallField,
        R: AlgebraicRoundFunction<F, AW, SW, CW>,
        M: AbsorptionModeTrait<F>,
        const AW: usize,
        const SW: usize,
        const CW: usize,
    > TreeHasher<F> for SimpleAlgebraicSponge<F, AW, SW, CW, R, M>
{
    type Output = [F; CW];
    #[inline]
    fn placeholder_output() -> Self::Output {
        [F::ZERO; CW]
    }
    #[inline]
    fn new() -> Self {
        Self::default()
    }
    #[inline]
    fn accumulate_into_leaf(&mut self, value: &F) {
        self.absorb_single(value);
    }
    #[inline]
    fn finalize_into_leaf_hash_and_reset(&mut self) -> Self::Output {
        self.finalize_reset()
    }
    #[inline]
    fn hash_into_leaf<'a, S: IntoIterator<Item = &'a F>>(source: S) -> Self::Output
    where
        F: 'a,
    {
        let mut hasher = Self::default();

        for el in source.into_iter() {
            hasher.absorb_single(el);
        }
        hasher.finalize()
    }
    #[inline]
    fn hash_into_leaf_owned<S: IntoIterator<Item = F>>(source: S) -> Self::Output {
        let mut hasher = Self::default();

        for el in source.into_iter() {
            hasher.absorb_single(&el);
        }
        hasher.finalize()
    }
    #[inline]
    fn hash_into_node(left: &Self::Output, right: &Self::Output, _depth: usize) -> Self::Output {
        let mut hasher = Self::default();
        hasher.absorb(&left[..]);
        hasher.absorb(&right[..]);

        hasher.finalize()
    }
    #[inline]
    fn normalize_output(dst: &mut Self::Output) {
        for el in dst.iter_mut() {
            el.normalize();
        }
    }
}

use blake2::Digest;

impl<F: SmallField> TreeHasher<F> for blake2::Blake2s256 {
    type Output = [u8; 32];
    #[inline]
    fn placeholder_output() -> Self::Output {
        [0u8; 32]
    }
    #[inline]
    fn new() -> Self {
        Self::default()
    }
    #[inline]
    fn accumulate_into_leaf(&mut self, value: &F) {
        let as_u64 = value.as_u64_reduced().to_le_bytes();
        self.update(as_u64);
    }
    #[inline]
    fn finalize_into_leaf_hash_and_reset(&mut self) -> Self::Output {
        let mut output = [0u8; 32];
        let raw_output = self.finalize_reset();
        output[..].copy_from_slice(raw_output.as_slice());

        output
    }
    #[inline]
    fn hash_into_leaf<'a, S: IntoIterator<Item = &'a F>>(source: S) -> Self::Output
    where
        F: 'a,
    {
        let mut hasher = Self::default();

        for el in source.into_iter() {
            hasher.accumulate_into_leaf(el);
        }

        let mut output = [0u8; 32];
        let raw_output = hasher.finalize();
        output[..].copy_from_slice(raw_output.as_slice());

        output
    }
    #[inline]
    fn hash_into_leaf_owned<S: IntoIterator<Item = F>>(source: S) -> Self::Output {
        let mut hasher = Self::default();

        for el in source.into_iter() {
            hasher.accumulate_into_leaf(&el);
        }

        let mut output = [0u8; 32];
        let raw_output = hasher.finalize();
        output[..].copy_from_slice(raw_output.as_slice());

        output
    }
    #[inline]
    fn hash_into_node(left: &Self::Output, right: &Self::Output, _depth: usize) -> Self::Output {
        let mut hasher = Self::default();
        hasher.update(&left[..]);
        hasher.update(&right[..]);

        let mut output = [0u8; 32];
        let raw_output = hasher.finalize();
        output[..].copy_from_slice(raw_output.as_slice());

        output
    }
}

impl<F: SmallField> TreeHasher<F> for sha3::Keccak256 {
    type Output = [u8; 32];
    #[inline]
    fn placeholder_output() -> Self::Output {
        [0u8; 32]
    }
    #[inline]
    fn new() -> Self {
        Self::default()
    }
    #[inline]
    fn accumulate_into_leaf(&mut self, value: &F) {
        let as_u64 = value.as_u64_reduced().to_le_bytes();
        self.update(as_u64);
    }
    #[inline]
    fn finalize_into_leaf_hash_and_reset(&mut self) -> Self::Output {
        let mut output = [0u8; 32];
        let raw_output = self.finalize_reset();
        output[..].copy_from_slice(raw_output.as_slice());

        output
    }
    #[inline]
    fn hash_into_leaf<'a, S: IntoIterator<Item = &'a F>>(source: S) -> Self::Output
    where
        F: 'a,
    {
        let mut hasher = Self::default();

        for el in source.into_iter() {
            hasher.accumulate_into_leaf(el);
        }

        let mut output = [0u8; 32];
        let raw_output = hasher.finalize();
        output[..].copy_from_slice(raw_output.as_slice());

        output
    }
    #[inline]
    fn hash_into_leaf_owned<S: IntoIterator<Item = F>>(source: S) -> Self::Output {
        let mut hasher = Self::default();

        for el in source.into_iter() {
            hasher.accumulate_into_leaf(&el);
        }

        let mut output = [0u8; 32];
        let raw_output = hasher.finalize();
        output[..].copy_from_slice(raw_output.as_slice());

        output
    }
    #[inline]
    fn hash_into_node(left: &Self::Output, right: &Self::Output, _depth: usize) -> Self::Output {
        let mut hasher = Self::default();
        hasher.update(&left[..]);
        hasher.update(&right[..]);

        let mut output = [0u8; 32];
        let raw_output = hasher.finalize();
        output[..].copy_from_slice(raw_output.as_slice());

        output
    }
}
