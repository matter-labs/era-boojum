use std::sync::Arc;

use self::utils::u16_words_to_u1024;

use super::*;
use crate::config::*;
use crate::cs::gates::ConstantAllocatableCS;
use crate::cs::traits::cs::ConstraintSystem;
use crate::gadgets::u16::UInt16;
use crate::{cs::Variable, gadgets::u8::get_8_by_8_range_check_table};
use crypto_bigint::{CheckedMul, NonZero, Zero, U1024};

pub mod impl_traits;
pub mod implementation_u16;
pub mod utils;

// Small note on the strategy - because we are quite flexible in what range check tables we use we have a few options:
// - if we only need field ops we can create many lookup arguments that are basically 16 bit range checks
// - if we need something else (like hash functions too), we can use almost always use 8x8 tables
// Previously we used RNS with quite diverse strategy on lazy reduction, but in practice we can ignore additions almost always,
// and insert manual reduction where necessary by N/2N/3N/4N depending on the capacity, and only focus on efficiency of multiplication.
// For multiplications there is not too much we can do: so far looks like enforcing the constraint
// that for range-checked and properly decomposed `a` and `b` we can just enforce the relation
// a * b = q * P + r, and depending on what we need afterwards to ensure range of `q` and `r` in certain bounds.
// Note that we rarely need `r` to be strictly `< P` and usually are fine to have it `< 2^log2(P)` or even `< 2^next_range_check_multiple(log2(P))`

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct OverflowTracker {
    pub max_moduluses: u32,
}

impl OverflowTracker {
    pub fn add(&self, other: &Self) -> Self {
        Self {
            max_moduluses: self.max_moduluses + other.max_moduluses,
        }
    }

    pub fn overflow_over_representation(&self, modulus: &U1024, repr_bits: u32) -> u32 {
        let total = modulus.saturating_mul(&U1024::from_word(self.max_moduluses as u64));
        let total_bits = total.bits() as u32;
        if total_bits <= repr_bits {
            0
        } else {
            total_bits - repr_bits
        }
    }

    pub fn into_max_value(&self, modulus: &U1024) -> U1024 {
        let mut other = U1024::ZERO;
        other.as_words_mut()[0] = self.max_moduluses as u64;

        other.wrapping_mul(modulus)
    }

    pub fn used_words_if_normalized(&self, modulus: &U1024) -> usize {
        let mut other = U1024::ZERO;
        other.as_words_mut()[0] = self.max_moduluses as u64;
        let upper_bound = other.wrapping_mul(modulus);

        let mut words = upper_bound.bits() / 16;
        if upper_bound.bits() % 16 != 0 {
            words += 1;
        }

        words
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct NonNativeFieldOverU16Params<T: pairing::ff::PrimeField, const N: usize> {
    pub modulus: [u16; N], // modulus padded with zeroes to number of representation words if necessary
    pub modulus_bits: u32, // number of bits in modulus
    pub modulus_limbs: usize, // number of u16 limbs required to represent a modulus
    pub modulus_u1024: crypto_bigint::NonZero<U1024>,
    pub max_product_before_reduction: U1024,
    pub max_mods_to_fit: u32, // how many moduluses fit into 2^{16 * N}
    pub max_mods_in_allocation: u32, // how many moduluses fit into 2^{16 * modulus_limbs}
    pub max_mods_before_multiplication: usize,
    pub _marker: std::marker::PhantomData<T>,
}

impl<T: pairing::ff::PrimeField, const N: usize> NonNativeFieldOverU16Params<T, N> {
    pub const fn repr_bits(&self) -> u32 {
        (N as u32) * 16
    }

    pub const fn modulus_is_word_aligned(&self) -> bool {
        self.modulus_bits % 16 == 0
    }

    pub fn create() -> Self
    where
        [(); N + 1]:,
    {
        let modulus_bits = T::NUM_BITS;
        let mut modulus_limbs = modulus_bits / 16;
        if modulus_bits % 16 != 0 {
            modulus_limbs += 1;
        }

        let mut modulus_u1024 = U1024::ZERO;
        for (dst, src) in modulus_u1024
            .as_words_mut()
            .iter_mut()
            .zip(T::char().as_ref())
        {
            *dst = *src;
        }

        let modulus_non_zero = NonZero::new(modulus_u1024).unwrap();

        let tmp = [u16::MAX; N];
        let max_in_allocation = u16_words_to_u1024(&tmp[..(modulus_limbs as usize)]);
        let (q, r) = max_in_allocation.div_rem(&modulus_non_zero);
        for el in q.as_words().iter().skip(1) {
            assert_eq!(*el, 0);
        }
        let mut max_mods_in_allocation = q.as_words()[0];
        assert!(max_mods_in_allocation <= u32::MAX as u64);
        if r.is_zero().unwrap_u8() == 0 {
            max_mods_in_allocation += 1;
        }
        assert!(max_mods_in_allocation <= u32::MAX as u64);

        let max_mods_in_allocation = max_mods_in_allocation as u32;

        let max_representable = u16_words_to_u1024(&[u16::MAX; N]);
        let q = max_representable.checked_div(&modulus_u1024).unwrap();
        for el in q.as_words().iter().skip(1) {
            assert_eq!(*el, 0);
        }

        let max_mods_to_fit = q.as_words()[0];
        assert!(max_mods_to_fit <= u32::MAX as u64);
        let max_mods_to_fit = max_mods_to_fit as u32;

        let mut modulus = [0u16; N];
        let mut tmp = modulus_u1024;
        for dst in modulus.iter_mut() {
            let low = tmp.as_words()[0];
            *dst = low as u16;

            tmp = tmp.shr_vartime(16);
        }
        assert!(tmp.is_zero().unwrap_u8() == 1);

        let max_q = u16_words_to_u1024(&[u16::MAX; N + 1]);
        let max_input = max_q.checked_mul(&modulus_u1024).unwrap(); // actually + P - 1, but we take lower
        let max_product_before_reduction = max_input;
        let max_mods_before_multiplication_u1024 = max_product_before_reduction
            .checked_div(&modulus_u1024)
            .unwrap();

        let mut max_mods_before_multiplication =
            max_mods_before_multiplication_u1024.as_words()[0] as usize;

        for word in max_mods_before_multiplication_u1024.as_words()[1..].iter() {
            if *word != 0 {
                max_mods_before_multiplication = usize::MAX;
            }
        }

        Self {
            modulus,
            modulus_bits,
            modulus_limbs: modulus_limbs as usize,
            modulus_u1024: modulus_non_zero,
            max_product_before_reduction,
            max_mods_to_fit,
            max_mods_in_allocation,
            max_mods_before_multiplication,
            _marker: std::marker::PhantomData,
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RepresentationForm {
    Normalized,
    Lazy,
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct NonNativeFieldOverU16<F: SmallField, T: pairing::ff::PrimeField, const N: usize> {
    pub limbs: [Variable; N],
    pub non_zero_limbs: usize,
    pub tracker: OverflowTracker,
    pub form: RepresentationForm,
    pub params: Arc<NonNativeFieldOverU16Params<T, N>>,
    pub _marker: std::marker::PhantomData<F>,
}

pub fn get_16_bits_range_check_table<F: SmallField, CS: ConstraintSystem<F>>(
    cs: &CS,
) -> Option<u32> {
    use crate::gadgets::tables::range_check_16_bits::RangeCheck16BitsTable;
    cs.get_table_id_for_marker::<RangeCheck16BitsTable>()
}

pub fn range_check_u16<F: SmallField, CS: ConstraintSystem<F>>(cs: &mut CS, variable: Variable) {
    if let Some(table_id) = get_16_bits_range_check_table(&*cs) {
        cs.enforce_lookup::<1>(table_id, &[variable]);
    } else if let Some(_table_id) = get_8_by_8_range_check_table(&*cs) {
        let _ = UInt16::from_variable_checked(cs, variable);
    } else {
        unimplemented!()
    }
}
