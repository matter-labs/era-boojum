// NOTE: we use the Plonky2 (https://github.com/mir-protocol/plonky2) implementation of non-vectorized field as the baseline,
// with extra modifications for compile-time evaluations. Even though we can not use "const trait"
// for now, one can use "_impl" const fn methods in non-generic contexts

use crate::field::{
    Field, PrimeField, SmallField, SmallFieldRepresentable, U64RawRepresentable, U64Representable,
};
use crate::utils::{assume, branch_hint, split};
use std::hash::{Hash, Hasher};

mod extension;
mod inversion;

#[cfg(all(
    not(feature = "include_packed_simd"),
    any(target_feature = "neon", target_feature = "avx2"),
    not(all(target_feature = "avx512f", target_feature = "avx512vl"))
))]
pub mod arm_asm_impl;

#[cfg(all(
    feature = "include_packed_simd",
    any(target_feature = "neon", target_feature = "avx2"),
    not(all(target_feature = "avx512f", target_feature = "avx512vl"))
))]
pub mod arm_asm_packed_impl;
#[cfg(not(any(
    all(target_feature = "avx512f", target_feature = "avx512vl"),
    target_feature = "neon",
    target_feature = "avx2"
)))]
pub mod generic_impl;
#[cfg(all(
    target_feature = "avx512f",
    target_feature = "avx512vl",
    not(any(
        target_feature = "avx512bw",
        target_feature = "avx512cd",
        target_feature = "avx512dq"
    ))
))]
pub mod x86_64_asm_impl;

#[cfg(all(
    target_feature = "avx512bw",
    target_feature = "avx512cd",
    target_feature = "avx512dq",
    target_feature = "avx512f",
    target_feature = "avx512vl"
))]
pub mod avx512_impl;

#[cfg(all(
    not(feature = "include_packed_simd"),
    any(target_feature = "neon", target_feature = "avx2"),
    not(all(target_feature = "avx512f", target_feature = "avx512vl"))
))]
pub use arm_asm_impl::*;

#[cfg(all(
    feature = "include_packed_simd",
    any(target_feature = "neon", target_feature = "avx2"),
    not(all(target_feature = "avx512f", target_feature = "avx512vl"))
))]
pub use arm_asm_packed_impl::*;

#[cfg(not(any(
    all(target_feature = "avx512f", target_feature = "avx512vl"),
    target_feature = "neon",
    target_feature = "avx2"
)))]
pub use generic_impl::*;

#[cfg(all(
    target_feature = "avx512f",
    target_feature = "avx512vl",
    not(any(
        target_feature = "avx512bw",
        target_feature = "avx512cd",
        target_feature = "avx512dq"
    ))
))]
pub use x86_64_asm_impl::*;

#[cfg(all(
    target_feature = "avx512bw",
    target_feature = "avx512cd",
    target_feature = "avx512dq",
    target_feature = "avx512f",
    target_feature = "avx512vl"
))]
pub use avx512_impl::*;

pub use self::extension::GoldilocksExt2;
use self::inversion::try_inverse_u64;

use super::SqrtField;

const EPSILON: u64 = (1 << 32) - 1;

/// A field selected to have fast reduction.
///
/// Its order is 2^64 - 2^32 + 1.
/// ```ignore
/// P = 2**64 - EPSILON
///   = 2**64 - 2**32 + 1
///   = 2**32 * (2**32 - 1) + 1
/// ```
#[derive(Clone, Copy, Default, serde::Deserialize)]
#[repr(transparent)]
pub struct GoldilocksField(pub u64);

// To allow wire format equality, we normalize on serialization
impl serde::Serialize for GoldilocksField {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_u64(self.as_u64_reduced())
    }
}

impl GoldilocksField {
    pub const MULTIPLICATIVE_GROUP_GENERATOR: Self = Self(7);
    pub const RADIX_2_SUBGROUP_GENERATOR: Self = Self(0x185629dcda58878c);
    pub const ORDER_BITS: usize = 64;
    pub const ORDER: u64 = 0xFFFFFFFF00000001;
    pub const TWO_ADICITY: usize = 32;
    pub const T: u64 = (Self::ORDER - 1) >> Self::TWO_ADICITY;
    pub const BARRETT: u128 = 18446744078004518912; // 0x10000000100000000

    #[inline(always)]
    pub fn mul_assign_long(&'_ mut self, other: &Self) -> u128 {
        let c = (self.0 as u128) * (other.0 as u128);

        c
    }

    // for poseidon hash we will have dot products of vectors of length 11,
    // where vectors are quasi-random in field,
    // so we need roughly 11 + 64 + 64 bits
    #[inline(always)]
    pub const fn accumulate_extended(acc: (u128, u32), value: u128) -> (u128, u32) {
        let (acc_low, acc_high) = acc;
        let (res_lo, of) = acc_low.overflowing_add(value);
        let res_hi = acc_high.wrapping_add(of as u32);
        (res_lo, res_hi)
    }

    #[inline(always)]
    pub const fn reduce_from_extended_accumulator(acc: (u128, u32)) -> Self {
        let (acc_low, acc_high) = acc;
        let (acc_low, acc_mid) = (acc_low as u64, (acc_low >> 64) as u64);
        let high = (acc_mid as u128) | ((acc_high as u128) << 64);
        let reduced_high: u64 = Self::from_u128_with_reduction(high).to_reduced_u64();
        let low: u128 = (acc_low as u128) | ((reduced_high as u128) << 64);

        Self::from_u128_with_reduction(low)
    }

    #[inline(always)]
    pub const fn to_reduced_u64(&self) -> u64 {
        let mut c = self.0;
        // We only need one condition subtraction, since 2 * ORDER would not fit in a u64.
        if c >= Self::ORDER {
            c -= Self::ORDER;
        }
        c
    }

    #[inline(always)]
    pub const fn to_nonreduced_u64(&self) -> u64 {
        self.0
    }

    #[inline(always)]
    pub const fn from_nonreduced_u64(c: u64) -> Self {
        let mut c = c;
        // We only need one condition subtraction, since 2 * ORDER would not fit in a u64.
        if c >= Self::ORDER {
            c -= Self::ORDER;
        }

        Self(c)
    }

    #[inline(always)]
    pub const fn add_reduced_u64(&self, rhs: u64) -> Self {
        let (res_wrapped, carry) = self.0.overflowing_add(rhs);
        // Add EPSILON * carry cannot overflow unless rhs is not in canonical form.
        Self(res_wrapped + EPSILON * (carry as u64))
    }

    #[inline(always)]
    pub const fn sub_reduced_u64(&self, rhs: u64) -> Self {
        let (res_wrapped, borrow) = self.0.overflowing_sub(rhs);
        // Sub EPSILON * carry cannot underflow unless rhs is not in canonical form.
        Self(res_wrapped - EPSILON * (borrow as u64))
    }

    #[inline(always)]
    pub const fn from_u128_with_reduction(x: u128) -> Self {
        let (x_lo, x_hi) = split(x); // This is a no-op
        let x_hi_hi = x_hi >> 32;
        let x_hi_lo = x_hi as u32; // get high and low parts

        let (mut t0, borrow) = x_lo.overflowing_sub(x_hi_hi);
        if borrow {
            branch_hint(); // A borrow is exceedingly rare. It is faster to branch.
            t0 -= EPSILON; // Cannot underflow.
        }
        let t1 = (x_hi_lo as u64) * EPSILON;
        let t2 = unsafe { add_no_canonicalize_trashing_input(t0, t1) };
        GoldilocksField(t2)
    }

    const fn compute_shifts() -> [Self; Self::CHAR_BITS] {
        let mut result = [Self::ZERO; Self::CHAR_BITS];
        let mut i = 0;
        while i < Self::CHAR_BITS {
            result[i] = Self::from_nonreduced_u64(1u64 << i);
            i += 1;
        }

        result
    }

    #[inline(always)]
    pub(crate) const fn add_assign_impl(&'_ mut self, other: &Self) -> &'_ mut Self {
        let (sum, over) = self.0.overflowing_add(other.0);
        let (mut sum, over) = sum.overflowing_add((over as u64) * EPSILON);
        if over {
            // NB: self.0 > Self::ORDER && rhs.0 > Self::ORDER is necessary but not sufficient for
            // double-overflow.
            // This assume does two things:
            //  1. If compiler knows that either self.0 or rhs.0 <= ORDER, then it can skip this
            //     check.
            //  2. Hints to the compiler how rare this double-overflow is (thus handled better with
            //     a branch).
            assume(self.0 > Self::ORDER && other.0 > Self::ORDER);
            branch_hint();
            sum += EPSILON; // Cannot overflow.
        }
        self.0 = sum;

        self
    }

    #[inline(always)]
    pub(crate) const fn double_impl(&mut self) -> &mut Self {
        // unfortunately canonical form overflows anyway, so we should just add
        let t = *self;
        self.add_assign_impl(&t);

        self
    }

    #[inline(always)]
    pub(crate) const fn mul_assign_impl(&'_ mut self, other: &Self) -> &'_ mut Self {
        *self = Self::from_u128_with_reduction((self.0 as u128) * (other.0 as u128));

        self
    }

    #[inline(always)]
    pub(crate) const fn square_impl(&mut self) -> &mut Self {
        *self = Self::from_u128_with_reduction((self.0 as u128) * (self.0 as u128));

        self
    }
}

impl PartialEq for GoldilocksField {
    fn eq(&self, other: &Self) -> bool {
        self.to_reduced_u64() == other.to_reduced_u64()
    }
}

impl PartialEq<u64> for GoldilocksField {
    fn eq(&self, other: &u64) -> bool {
        self.to_reduced_u64() == *other
    }
}

impl Eq for GoldilocksField {}

impl Hash for GoldilocksField {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.to_reduced_u64())
    }
}

impl std::fmt::Display for GoldilocksField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "0x{:016x}", self.to_reduced_u64())
    }
}

impl std::fmt::Debug for GoldilocksField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "0x{:016x}", self.to_reduced_u64())
        // write!(f, "0x{:016x}", self.0)
    }
}

impl Field for GoldilocksField {
    const ZERO: Self = Self(0);
    const ONE: Self = Self(1);
    const TWO: Self = Self(2);
    const MINUS_ONE: Self = Self(Self::ORDER - 1);

    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.to_reduced_u64() == 0
    }

    #[inline(always)]
    fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.add_assign_impl(other)
    }

    #[inline]
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        let (diff, under) = self.0.overflowing_sub(other.0);
        let (mut diff, under) = diff.overflowing_sub((under as u64) * EPSILON);
        if under {
            // NB: self.0 < EPSILON - 1 && rhs.0 > Self::ORDER is necessary but not sufficient for
            // double-underflow.
            // This assume does two things:
            //  1. If compiler knows that either self.0 >= EPSILON - 1 or rhs.0 <= ORDER, then it
            //     can skip this check.
            //  2. Hints to the compiler how rare this double-underflow is (thus handled better
            //     with a branch).
            assume(self.0 < EPSILON - 1 && other.0 > Self::ORDER);
            branch_hint();
            diff -= EPSILON; // Cannot underflow.
        }
        self.0 = diff;

        self
    }

    #[inline(always)]
    fn negate(&mut self) -> &mut Self {
        if self.is_zero() == false {
            *self = Self(Self::ORDER - self.to_reduced_u64());
        }

        self
    }

    #[inline(always)]
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.mul_assign_impl(other)
    }

    #[inline(always)]
    fn square(&mut self) -> &mut Self {
        self.square_impl()
    }

    #[inline(always)]
    fn double(&mut self) -> &mut Self {
        self.double_impl()
    }

    #[inline(always)]
    fn from_u64_with_reduction(value: u64) -> Self {
        Self::from_nonreduced_u64(value)
    }
}

impl SqrtField for GoldilocksField {
    fn sqrt(&self) -> Option<Self> {
        if self.is_zero() {
            return Some(*self);
        }

        // "Square root computation over even extension fields"

        const TONELLI_SHANKS_Z: GoldilocksField = GoldilocksField(1753635133440165772);

        let mut omega = self.pow_u64(GoldilocksField::T >> 1);
        let mut a_omega = omega;
        a_omega.mul_assign(self);
        let mut b = a_omega;
        b.mul_assign(&omega);

        let mut i = 0;
        let mut a0 = b;
        while i < GoldilocksField::TWO_ADICITY - 1 {
            a0.square();
            i += 1;
        }

        if a0 == GoldilocksField::MINUS_ONE {
            return None;
        }

        let mut v = GoldilocksField::TWO_ADICITY;
        let mut x = a_omega;
        let mut z = TONELLI_SHANKS_Z;

        while b != GoldilocksField::ONE {
            let mut k = 0;
            let mut tmp = b;
            while tmp != GoldilocksField::ONE {
                tmp.square();
                k += 1;
            }

            omega = z;

            let mut i = 0;
            while i < v - k - 1 {
                omega.square();
                i += 1;
            }

            z = omega;
            z.square();

            b.mul_assign(&z);
            x.mul_assign(&omega);
            v = k;
        }

        debug_assert!({
            let mut tmp = x;
            tmp.square();

            tmp == *self
        });

        Some(x)
    }
}

impl PrimeField for GoldilocksField {
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
        try_inverse_u64(self)
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

impl U64RawRepresentable for GoldilocksField {
    #[inline(always)]
    fn as_raw_u64(self) -> u64 {
        self.0
    }

    #[inline(always)]
    fn from_raw_u64_unchecked(value: u64) -> Self {
        Self(value)
    }

    #[inline(always)]
    fn from_raw_u64_checked(value: u64) -> Option<Self> {
        if value >= Self::ORDER {
            None
        } else {
            Some(Self(value))
        }
    }

    #[inline(always)]
    fn as_raw_u64_array<const N: usize>(input: [Self; N]) -> [u64; N] {
        // unsafe {std::mem::transmute::<[Self; N], [u64; N]>(input)} // well, compiler is stupid here
        unsafe { *(&input as *const _ as *const [u64; N]) }
    }
}

impl U64Representable for GoldilocksField {
    #[inline(always)]
    fn as_u64(self) -> u64 {
        self.0
    }

    #[inline(always)]
    fn from_u64_unchecked(value: u64) -> Self {
        Self(value)
    }

    #[inline(always)]
    fn from_u64(value: u64) -> Option<Self> {
        if value >= Self::ORDER {
            None
        } else {
            Some(Self(value))
        }
    }

    #[inline(always)]
    fn as_u64_array<const N: usize>(input: [Self; N]) -> [u64; N] {
        // unsafe {std::mem::transmute::<[Self; N], [u64; N]>(input)} // It would be true after monomorphization only
        unsafe { *(&input as *const _ as *const [u64; N]) }
    }

    #[inline(always)]
    fn as_u64_reduced(&self) -> u64 {
        self.to_reduced_u64()
    }
}

impl SmallFieldRepresentable for GoldilocksField {
    #[inline(always)]
    fn from_u128_reduced(value: u128) -> Self {
        Self::from_u128_with_reduction(value)
    }
}

impl SmallField for GoldilocksField {
    const CHAR: u64 = Self::ORDER;
    // a * b + c
    #[inline(always)]
    fn fma(a: Self, b: Self, c: Self) -> Self {
        Self::from_u128_with_reduction(
            (a.0 as u128)
                .wrapping_mul(b.0 as u128)
                .wrapping_add(c.0 as u128),
        )
    }

    const CAN_CAST_VECTOR_TO_U64_LE_VECTOR: bool = true;
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
const unsafe fn add_no_canonicalize_trashing_input(x: u64, y: u64) -> u64 {
    use std::intrinsics::const_eval_select;

    const_eval_select::<_, _, _, u64>(
        (x, y),
        add_no_canonicalize_trashing_input_ct,
        add_no_canonicalize_trashing_input_asm,
    )
}

/// Fast addition modulo ORDER for x86-64.
/// This function is marked unsafe for the following reasons:
///   - It is only correct if x + y < 2**64 + ORDER = 0x1ffffffff00000001.
///   - It is only faster in some circumstances. In particular, on x86 it overwrites both inputs in
///     the registers, so its use is not recommended when either input will be used again.
#[inline(always)]
#[cfg(target_arch = "x86_64")]
fn add_no_canonicalize_trashing_input_asm(x: u64, y: u64) -> u64 {
    unsafe {
        use std::arch::asm;
        let res_wrapped: u64;
        let adjustment: u64;
        asm!(
            "add {0}, {1}",
            // Trick. The carry flag is set iff the addition overflowed.
            // sbb x, y does x := x - y - CF. In our case, x and y are both {1:e}, so it simply does
            // {1:e} := 0xffffffff on overflow and {1:e} := 0 otherwise. {1:e} is the low 32 bits of
            // {1}; the high 32-bits are zeroed on write. In the end, we end up with 0xffffffff in {1}
            // on overflow; this happens be EPSILON.
            // Note that the CPU does not realize that the result of sbb x, x does not actually depend
            // on x. We must write the result to a register that we know to be ready. We have a
            // dependency on {1} anyway, so let's use it.
            "sbb {1:e}, {1:e}",
            inlateout(reg) x => res_wrapped,
            inlateout(reg) y => adjustment,
            options(pure, nomem, nostack),
        );
        assume(x != 0 || (res_wrapped == y && adjustment == 0));
        assume(y != 0 || (res_wrapped == x && adjustment == 0));
        // Add EPSILON == subtract ORDER.
        // Cannot overflow unless the assumption if x + y < 2**64 + ORDER is incorrect.
        res_wrapped + adjustment
    }
}

#[inline(always)]
#[cfg(target_arch = "x86_64")]
const fn add_no_canonicalize_trashing_input_ct(x: u64, y: u64) -> u64 {
    let (res_wrapped, carry) = x.overflowing_add(y);
    // Below cannot overflow unless the assumption if x + y < 2**64 + ORDER is incorrect.
    res_wrapped + EPSILON * (carry as u64)
}

#[inline(always)]
#[cfg(not(target_arch = "x86_64"))]
const unsafe fn add_no_canonicalize_trashing_input(x: u64, y: u64) -> u64 {
    let (res_wrapped, carry) = x.overflowing_add(y);
    // Below cannot overflow unless the assumption if x + y < 2**64 + ORDER is incorrect.
    res_wrapped + EPSILON * (carry as u64)
}

crate::impl_std_ops_for_field!(GoldilocksField);

#[cfg(test)]
mod test {

    use super::*;

    #[test]
    fn test_generators() {
        let multiplicative_generator = GoldilocksField::multiplicative_generator();
        let pow = (GoldilocksField::CHAR - 1) >> GoldilocksField::TWO_ADICITY;
        let pow = multiplicative_generator.pow_u64(pow);
        assert_eq!(pow, GoldilocksField::radix_2_subgroup_generator());
        let pow = GoldilocksField::radix_2_subgroup_generator()
            .pow_u64(1u64 << GoldilocksField::TWO_ADICITY);
        assert_eq!(pow, GoldilocksField::ONE);
        // let pow = GoldilocksField::power2_subgroup_generator()
        //     .pow_u64(1u64 << GoldilocksField::TWO_ADICITY);
        assert_eq!(pow, GoldilocksField::ONE);

        // let mut x = GoldilocksField(1 << 10);
        // dbg!(x);
        // x = x.pow_u64(GoldilocksField::CHAR - 1);
        // dbg!(x);

        // for i in 1..10 {
        //     let x: u64 = 1 << i;
        //     dbg!(x);
        //     dbg!(x.trailing_zeros());
        // }

        let x = GoldilocksField(1 << 48);
        for i in 0..25 {
            let fft_size = 1 << i;
            dbg!(x.pow_u64(fft_size));
        }

        let fft_size = 1 << 10;
        // let omega = domain_generator_for_size::<GoldilocksField>(fft_size as u64);
        let omega = GoldilocksField(1 << 48);
        let num_powers = fft_size / 2;
        let mut current = GoldilocksField::ONE;
        for _i in 1..num_powers {
            current.mul_assign(&omega);
            dbg!(current);
        }
    }

    #[test]
    fn find_tonelli_shanks_param() {
        let mut z;
        let mut c = GoldilocksField::TWO;
        loop {
            z = c.pow_u64(GoldilocksField::T);
            let c0 = z.pow_u64(1u64 << (GoldilocksField::TWO_ADICITY - 1));

            if c0 != GoldilocksField::ONE {
                break;
            }
            c.add_assign(&GoldilocksField::ONE);
        }

        dbg!(z.as_u64_reduced());
    }

    #[test]
    fn some_square_root() {
        let x = GoldilocksField::MINUS_ONE.sqrt();
        dbg!(&x);

        let x = GoldilocksField::TWO.sqrt();
        dbg!(&x);
    }
}
