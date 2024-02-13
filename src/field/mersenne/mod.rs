

mod extension;

#[cfg(not(target_feature = "avx512f"))]
pub mod generic_impl;
#[cfg(not(target_feature = "avx512f"))]
pub use generic_impl::*;

// #[cfg(target_feature = "avx512f")]
pub mod avx512_impl;
// #[cfg(target_feature = "avx512f")]
pub use avx512_impl::*;

/// The prime field `F_p` where `p = 2^31 - 1`.

use core::hash::Hash;
use core::fmt::Display;
use core::fmt::Formatter;
use core::fmt::Debug;
use core::hash::Hasher;
use std::ops::BitXorAssign;

use crate::field::{
    Field, PrimeField, SmallField, SmallFieldRepresentable, U64RawRepresentable, U64Representable,
};
use super::SqrtField;


#[derive(Clone, Copy, serde::Deserialize)]
#[repr(transparent)]
pub struct MersenneField(pub u32);

// To allow wire format equality, we normalize on serialization
impl serde::Serialize for MersenneField {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_u64(self.as_u64_reduced())
    }
}

impl MersenneField{
    pub const ORDER: u32 = (1 << 31) - 1;
    pub const MULTIPLICATIVE_GROUP_GENERATOR: Self = Self(7);
    pub const ORDER_BITS: usize = 31;
    pub const RADIX_2_SUBGROUP_GENERATOR: Self = Self(2147483643);
    pub const TWO_ADICITY: usize = 32; // should it be 32?

    pub fn new(value: u32) -> Self{
        debug_assert!((value >> 31) == 0);
        
        Self(value)
    }
    #[inline(always)]
    const fn to_reduced_u32(&self) -> u32 {
        let mut c = self.0;
        if c >= Self::ORDER {
            c -= Self::ORDER;
        }
        c
    }
    fn mul_2exp_u64(&self, exp: u64) -> Self {
        // In a Mersenne field, multiplication by 2^k is just a left rotation by k bits.
        let exp = (exp % 31) as u8;
        let left = (self.0 << exp) & ((1 << 31) - 1);
        let right = self.0 >> (31 - exp);
        let rotated = left | right;
        Self::new(rotated)
    }
    fn exp_power_of_2(&self, power_log: usize, count: usize) -> Self {
        let mut res = *self;
        let mut count = count;
        for _ in 0..power_log {
            count += count;
            println!("{}", count);
            res.square();
        }
        res
    }
    fn mod_pow(&self, mut exp: u32) -> Self {
        let mut base = *self;
        let mut result = &mut MersenneField::new(1);
        while exp > 0 {
            if exp % 2 == 1 {
                result = result.mul_assign(&base.clone());
            }
    
            exp >>= 1;
            base.mul_assign(&base.clone());
        }
    
        *result
    }
    #[inline(always)]
    pub fn from_u64_with_reduction(x: u64) -> Self {
        let x_low = (x as u32) & ((1 << 31) - 1);
        let x_high = (x >> 31) as u32;
        let mut res = Self(x_low);
        res.add_assign(&Self(x_high));
        res
    }

    #[inline(always)]
    pub fn from_negative_u64_with_reduction(x: u64) -> Self {
        let x_low = (x as u32) & ((1 << 31) - 1);
        let x_high = ((x >> 31) as u32) & ((1 << 31) - 1);
        let x_sign = (x >> 63) as u32;
        let res_wrapped = x_low.wrapping_add(x_high);
        let res_wrapped = res_wrapped - x_sign;
        let msb = res_wrapped & (1 << 31);
        let mut sum = res_wrapped;
        sum.bitxor_assign(msb);
        let mut res = sum + u32::from(msb != 0);
        if res >= MersenneField::ORDER {
            res -= MersenneField::ORDER;
        }
        MersenneField(res)
    }

    #[inline(always)]
    pub fn as_u64(self) -> u64 {
        self.0 as u64
    }

    #[inline(always)]
    pub fn from_u64_unchecked(value: u64) -> Self{
        Self::new(
            value.try_into()
                .expect("Too large"),
        )
    }
    #[inline(always)]
    fn from_u64(value: u64) -> Option<Self> {
        if value as u32 >= Self::ORDER {
            None
        } else {
            Some(Self(value as u32))
        }
    }

    #[inline(always)]
    pub const fn from_nonreduced_u32(c: u32) -> Self {
        let mut c = c;
        // We only need one condition subtraction, since 2 * ORDER would not fit in a u64.
        if c >= Self::ORDER {
            c -= Self::ORDER;
        }

        Self(c)
    }
    #[inline(always)]
    fn as_u64_array<const N: usize>(input: [Self; N]) -> [u64; N] {
        unsafe { *(&input as *const _ as *const [u64; N]) }
    }

    #[inline(always)]
    fn as_u64_reduced(&self) -> u64 {
        self.to_reduced_u32() as u64
    }

    fn as_boolean(&self) -> bool{
        let as_uint = self.to_reduced_u32();
        assert!(as_uint == 0 || as_uint == 1);
        as_uint != 0
    }

    fn inverse(&self) -> Option<Self>{
        //Since the nonzero elements of GF(pn) form a finite group with respect to multiplication,
        // a^p^n−1 = 1 (for a ≠ 0), thus the inverse of a is a^p^n−2.
        if self.is_zero() {
            return None;
        }
        Some(self.mod_pow(MersenneField::ORDER - 2))
    }

    const fn compute_shifts() -> [Self; Self::CHAR_BITS] {
        let mut result = [Self::ZERO; Self::CHAR_BITS];
        let mut i = 0;
        while i < Self::CHAR_BITS {
            result[i] = Self::from_nonreduced_u32(1u32 << i);
            i += 1;
        }

        result
    }

}
impl Default for MersenneField {
    fn default() -> Self {
        Self(0u32)
    }
}
impl PartialEq for MersenneField {
    fn eq(&self, other: &Self) -> bool {
        self.to_reduced_u32() == other.to_reduced_u32()
    }
}
impl Eq for MersenneField {}

impl Hash for MersenneField {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u32(self.to_reduced_u32())
    }
}

impl Ord for MersenneField {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.to_reduced_u32().cmp(&other.to_reduced_u32())
    }
}

impl PartialOrd for MersenneField {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Display for MersenneField {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl Debug for MersenneField {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl Field for MersenneField {
    const ZERO: Self = Self(0);
    const ONE: Self = Self(1);
    const TWO: Self = Self(2);
    const MINUS_ONE: Self = Self(Self::ORDER - 1);

    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.to_reduced_u32() == 0
    }

    #[inline(always)]
    fn from_u64_with_reduction(value: u64) -> Self {
        Self::from_u64_with_reduction(value)
    }

    fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self{
        let mut sum = self.0.wrapping_add(other.0);
        let msb = sum & (1 << 31);
        sum.bitxor_assign(msb);
        sum += u32::from(msb != 0);
        if sum >= Self::ORDER {
            sum -= Self::ORDER;
        }
        self.0 = sum;

        self
    }
    // sub
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self{
        let mut sum = self.0.wrapping_sub(other.0);
        let msb = sum & (1 << 31);
        sum.bitxor_assign(msb);
        sum -= u32::from(msb != 0);
        self.0 = sum;

        self

    }
    // mul
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self{
        let product = u64::from(self.0) * u64::from(other.0);
        let product_low = (product as u32) & ((1 << 31) - 1);
        let product_high = (product >> 31) as u32;
        *self = Self(product_low);
        self.add_assign(&Self(product_high));
        self
    }
    // square
    fn square(&'_ mut self) -> &'_ mut Self{
        self.mul_assign(&self.clone())

    }
    // negate
    #[inline(always)]
    fn negate(&'_ mut self) -> &'_ mut Self{
        if self.is_zero() == false {
            *self = Self(Self::ORDER - self.to_reduced_u32());
        }
    
        self
    }
    // double
    fn double(&'_ mut self) -> &'_ mut Self{
        let t = *self;
        self.add_assign(&t);

        self
    }

}

impl SqrtField for MersenneField {
    fn sqrt(&self) -> Option<Self> {
        if self.is_zero() {
            return Some(*self);
        }

        let mut a1 = self.pow_u64(536870911u64);
        let mut a0 = a1;
        a0.square();
        a0.mul_assign(self);
        if a0.0 == 2147483643 {
            None
        } else {
            a1.mul_assign(self);
            Some(a1)
        }
    }
}

impl PrimeField for MersenneField {
    const CHAR_BITS: usize = Self::ORDER_BITS;
    const CAPACITY_BITS: usize = Self::ORDER_BITS - 1;
    const TWO_ADICITY: usize = Self::TWO_ADICITY;
    const SHIFTS: &'static [Self] = &Self::compute_shifts();

    #[inline(always)]
    fn multiplicative_generator() -> Self {
        Self::MULTIPLICATIVE_GROUP_GENERATOR
    }

    #[inline(always)]
    fn radix_2_subgroup_generator() -> Self {
        Self::RADIX_2_SUBGROUP_GENERATOR
    }

    #[inline(always)]
    fn frobenius(&self, _power: usize) -> Self {
        *self
    }

    fn inverse(&self) -> Option<Self> {
        Self::inverse(self)
    }

    fn legendre(&self) -> super::LegendreSymbol {
        // s = self^((modulus - 1) // 2)
        let s = self.pow_u64((Self::CHAR - 1) / 2);
        if s == Self::ZERO {
            super::LegendreSymbol::Zero
        } else if s == Self::ONE {
            super::LegendreSymbol::QuadraticResidue
        } else {
            super::LegendreSymbol::QuadraticNonResidue
        }
    }
}

impl U64RawRepresentable for MersenneField {
    #[inline(always)]
    fn as_raw_u64(self) -> u64 {
        Self::as_u64(self)
    }

    #[inline(always)]
    fn from_raw_u64_unchecked(value: u64) -> Self {
        Self::from_u64_unchecked(value)
    }

    #[inline(always)]
    fn from_raw_u64_checked(value: u64) -> Option<Self> {
        Self::from_u64(value)
    }

    #[inline(always)]
    fn as_raw_u64_array<const N: usize>(input: [Self; N]) -> [u64; N] {
        Self::as_u64_array(input)
    }
}

impl U64Representable for MersenneField {
    #[inline(always)]
    fn as_u64(self) -> u64 {
        Self::as_u64(self)
    }

    #[inline(always)]
    fn from_u64_unchecked(value: u64) -> Self {
        Self::from_u64_unchecked(value)
    }

    #[inline(always)]
    fn from_u64(value: u64) -> Option<Self> {
        Self::from_u64(value)
    }

    #[inline(always)]
    fn as_u64_array<const N: usize>(input: [Self; N]) -> [u64; N] {
        Self::as_u64_array(input)
    }

    #[inline(always)]
    fn as_u64_reduced(&self) -> u64 {
        Self::as_u64_reduced(self)
    }
}

impl SmallFieldRepresentable for MersenneField {
    #[inline(always)]
    fn from_u128_reduced(value: u128) -> Self {
        Self::from_u64_with_reduction(value as u64)
    }
}

impl SmallField for MersenneField {
    const CHAR: u64 = Self::ORDER as u64;
    // a * b + c
    #[inline(always)]
    fn fma(a: Self, b: Self, c: Self) -> Self {
        Self::from_u64_with_reduction(
            (a.0 as u64)
                .wrapping_mul(b.0 as u64)
                .wrapping_add(c.0 as u64),
        )
    }

    const CAN_CAST_VECTOR_TO_U64_LE_VECTOR: bool = true;
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn basic_properties() {
        assert_eq!(MersenneField::ZERO, MersenneField(0));
        assert_eq!(MersenneField::ONE, MersenneField(1));
        assert_eq!(MersenneField::TWO, MersenneField(2));
        assert_eq!(MersenneField::MINUS_ONE, MersenneField(MersenneField::ORDER - 1));
    }

    #[test]
    fn test_multiplication() {
        let a = MersenneField::from_u64(5).unwrap();
        let b = MersenneField::from_u64(4).unwrap();
        let mut res = a;
        res.mul_assign(&b);
        assert_eq!(res.to_reduced_u32(), 20);

        let a = MersenneField::from_u64(MersenneField::ORDER as u64 - 1).unwrap();
        let b = MersenneField::from_u64(2).unwrap();
        let mut result = a;
        result.mul_assign(&b);
        assert_eq!(result, MersenneField::from_u64(MersenneField::ORDER as u64 - 2).unwrap());

        let a = MersenneField::from_u64(12345).unwrap();
        let b = MersenneField::ONE;
        let mut result = a;
        result.mul_assign(&b);
        assert_eq!(result, MersenneField::from_u64(12345).unwrap());

        let a = MersenneField::from_u64(12345).unwrap();
        let b = MersenneField::ZERO;
        let mut result = a;
        result.mul_assign(&b);
        assert_eq!(result, MersenneField::ZERO);

        let a = MersenneField::from_u64(17).unwrap();
        let b = MersenneField::from_u64(19).unwrap();
        let mut result1 = a;
        let mut result2 = b;
        result1.mul_assign(&b);
        result2.mul_assign(&a);
        assert_eq!(result1, result2);

        let a = MersenneField::from_u64(123).unwrap();
        let b = MersenneField::from_u64(456).unwrap();
        let mut result = a;
        result.mul_assign(&b);
        assert_eq!(result, MersenneField::from_u64(56088 % MersenneField::ORDER as u64).unwrap());

    }

    #[test]
    fn test_square() {
        let mut a = MersenneField::from_u64(7).unwrap();
        a.square();
        assert_eq!(a.to_reduced_u32(), 49);
        let a = MersenneField::from_u64(2).unwrap();
        let mut result = a.clone();
        result.square();
        assert_eq!(result, MersenneField::from_u64(4).unwrap());

        let a = MersenneField::from_u64(3).unwrap();
        let mut result = a.clone();
        result.square();
        assert_eq!(result, MersenneField::from_u64(9).unwrap());

        let a = MersenneField::ZERO;
        let mut result = a.clone();
        result.square();
        assert_eq!(result, MersenneField::ZERO);

        let a = MersenneField::ONE;
        let mut result = a.clone();
        result.square();
        assert_eq!(result, MersenneField::ONE);

    }

    #[test]
    fn test_negate() {
        let mut a = MersenneField::from_u64(5).unwrap();
        a.negate();
        assert_eq!(a.to_reduced_u32(), MersenneField::ORDER - 5);

        let a = MersenneField::from_u64(2).unwrap();
        let mut result = a.clone();
        result.negate();
        assert_eq!(result, MersenneField::from_u64(MersenneField::ORDER as u64 - 2).unwrap());

        let a = MersenneField::from_u64(3).unwrap();
        let mut result = a.clone();
        result.negate();
        assert_eq!(result, MersenneField::from_u64(MersenneField::ORDER as u64 - 3).unwrap());

        let a = MersenneField::from_u64(MersenneField::ORDER as u64 - 1).unwrap();
        let mut result = a.clone();
        result.negate();
        assert_eq!(result, MersenneField::ONE);

        let a = MersenneField::ZERO;
        let mut result = a.clone();
        result.negate();
        assert_eq!(result, MersenneField::ZERO);

        let a = MersenneField::from_u64(12345).unwrap();
        let mut result = a.clone();
        result.negate().negate();
        assert_eq!(result, a);

        let a = MersenneField::from_u64(123456).unwrap();
        let mut result = a.clone();
        result.negate();
        assert_eq!(result, MersenneField::from_u64(MersenneField::ORDER as u64 - 123456).unwrap());
    }

    #[test]
    fn test_double() {
        let mut a = MersenneField::from_u64(12345).unwrap();
        a.double();
        assert_eq!(a.to_reduced_u32(), 24690);

        let a = MersenneField::from_u64(2).unwrap();
        let mut result = a.clone();
        result.double();
        assert_eq!(result, MersenneField::from_u64(4).unwrap());

        let a = MersenneField::from_u64(3).unwrap();
        let mut result = a.clone();
        result.double();
        assert_eq!(result, MersenneField::from_u64(6).unwrap());

        let a = MersenneField::from_u64(MersenneField::ORDER as u64 - 2).unwrap();
        let mut result = a.clone();
        result.double();
        assert_eq!(result, MersenneField::from_u64(MersenneField::ORDER as u64 - 4).unwrap());

        let a = MersenneField::from_u64(MersenneField::ORDER as u64 - 1).unwrap();
        let mut result = a.clone();
        result.double();
        assert_eq!(result, MersenneField::from_u64(MersenneField::ORDER as u64 - 2).unwrap());

        let a = MersenneField::ZERO;
        let mut result = a.clone();
        result.double();
        assert_eq!(result, MersenneField::ZERO);

        let a = MersenneField::ONE;
        let mut result = a.clone();
        result.double();
        assert_eq!(result, MersenneField::TWO);

        let a = MersenneField::from_u64(123456).unwrap();
        let mut result = a.clone();
        result.double();
        assert_eq!(result, MersenneField::from_u64(246912).unwrap());
    }

    #[test]
    fn test_inverse() {
        let a = MersenneField::from_u64(4).unwrap();
        let inv_a = a.inverse().unwrap();
        let mut res = a;
        res.mul_assign(&inv_a);
        // a * a^-1 should be 1
        assert_eq!(res.to_reduced_u32(), 1);

        let a = MersenneField::from_u64(2).unwrap();
        let inv_a = a.inverse().unwrap();
        let mut res = a;
        res.mul_assign(&inv_a);
        assert_eq!(res, MersenneField::ONE);

        let a = MersenneField::from_u64(3).unwrap();
        let inv_a = a.inverse().unwrap();
        let mut res = a;
        res.mul_assign(&inv_a);
        assert_eq!(res.to_reduced_u32(), 1);

        let a = MersenneField::ONE;
        let inv_a = a.inverse().unwrap();
        assert_eq!(inv_a, MersenneField::ONE);

        let a = MersenneField::ZERO;
        assert!(a.inverse().is_none());

        let a = MersenneField::from_u64(MersenneField::ORDER as u64 - 2).unwrap();
        let inv_a = a.inverse().unwrap();
        let mut res = a;
        res.mul_assign(&inv_a);
        assert_eq!(res, MersenneField::ONE);

        let a = MersenneField::from_u64(4).unwrap();
        let inv_a = a.inverse().unwrap();
        let double_inv_a = inv_a.inverse().unwrap();
        assert_eq!(a, double_inv_a);

        let a = MersenneField::from_u64(123456).unwrap();
        let inv_a = a.inverse().unwrap();
        let mut res = a;
        res.mul_assign(&inv_a);
        assert_eq!(res, MersenneField::ONE);

    }

    #[test]
    fn test_add() {
        let a = MersenneField::from_u64(MersenneField::ORDER as u64 - 2).unwrap();
        let b = MersenneField::from_u64(10).unwrap();
        let mut res = a;
        res.add_assign(&b);
        assert_eq!(res.to_reduced_u32(), 8);  
        let a = MersenneField::from_u64(MersenneField::ORDER as u64 - 2).unwrap();
        let b = MersenneField::from_u64(4).unwrap();
        let mut sum = a;
        sum.add_assign(&b);
        assert_eq!(sum, MersenneField::from_u64(2).unwrap());

        let a = MersenneField::from_u64(MersenneField::ORDER as u64 - 1).unwrap();
        let b = MersenneField::ONE;
        let mut sum = a;
        sum.add_assign(&b);
        assert_eq!(sum, MersenneField::ZERO);

        let a = MersenneField::from_u64(10).unwrap();
        let b = MersenneField::from_u64(MersenneField::ORDER as u64 - 8).unwrap();
        let mut sum = a;
        sum.add_assign(&b);
        assert_eq!(sum, MersenneField::from_u64(2).unwrap());

        let a = MersenneField::from_u64(10).unwrap();
        let b = MersenneField::from_u64(20).unwrap();
        let mut sum = a;
        sum.add_assign(&b);
        assert_eq!(sum, MersenneField::from_u64(30).unwrap());
    }

    #[test]
    fn test_sub() {
        let a = MersenneField::from_u64(2).unwrap();
        let b = MersenneField::from_u64(10).unwrap();
        let mut res = a;
        res.sub_assign(&b);
        assert_eq!(res.to_reduced_u32(), MersenneField::ORDER - 8);

        let a = MersenneField::from_u64(3).unwrap();
        let b = MersenneField::from_u64(MersenneField::ORDER as u64 - 2).unwrap();
        let mut result = a;
        result.sub_assign(&b);
        assert_eq!(result, MersenneField::from_u64(5).unwrap());

        let min_val = 0; 
        let a = MersenneField::from_u64(min_val as u64).unwrap();
        let b = MersenneField::from_u64(MersenneField::ORDER as u64 - 1).unwrap();
        let mut result = a;
        result.sub_assign(&b);
        assert_eq!(result, MersenneField::ONE);

        let a = MersenneField::from_u64(10).unwrap();
        let b = MersenneField::from_u64(15).unwrap();
        let mut result = a;
        result.sub_assign(&b);
        assert_eq!(result, MersenneField::from_u64(MersenneField::ORDER as u64 - 5).unwrap());
    }
    #[test]
    fn test_count(){
        let num = MersenneField::from_u64(5).unwrap();
        let a = num.exp_power_of_2(2, 357913941);
    }
}