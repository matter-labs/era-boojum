// #[cfg(target_arch = "aarch64")]
// use std::arch::aarch64::*;
use std::ops::Shl;
use std::ops::Shr;
use std::ops::Sub;

use std::simd::num::*;
use std::simd::cmp::*;
use packed_simd::FromCast;

use crate::field::{goldilocks::GoldilocksField, Field};

/// # Safety
///
/// `a`, `b`, and `c` must have the same length.
pub unsafe fn naive(a: &[u64], b: &[u64], dst: &mut Vec<u64>) {
    let mut i = 0;
    while i < a.len() {
        let c = a.get_unchecked(i).wrapping_add(*b.get_unchecked(i));
        dst.push(c);
        i += 1;
    }
}

const EPSILON: u64 = (1 << 32) - 1;
const CHAR: u64 = 0xFFFFFFFF00000001;

pub struct GLN(pub [GoldilocksField; 32]);

impl GLN {
    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub fn add_assign_impl(&mut self, other: &Self) -> &mut Self {
        for i in 0..32 {
            self.0[i].add_assign(&other.0[i]);
        }

        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub fn mul_assign_impl(&mut self, other: &Self) -> &mut Self {
        for i in 0..32 {
            self.0[i].mul_assign(&other.0[i]);
        }

        self
    }
}

pub fn vec_add_native(a: &mut [GoldilocksField], b: &[GoldilocksField]) {
    for (a, b) in a.iter_mut().zip(b.iter()) {
        a.add_assign(b);
    }
}

pub fn vec_mul_native(a: &mut [GoldilocksField], b: &[GoldilocksField]) {
    for (a, b) in a.iter_mut().zip(b.iter()) {
        a.mul_assign(b);
    }
}

pub fn vec_add_vectorized(a: &mut [GLN], b: &[GLN]) {
    for (a, b) in a.iter_mut().zip(b.iter()) {
        a.add_assign_impl(b);
    }
}

pub fn vec_mul_vectorized(a: &mut [GLN], b: &[GLN]) {
    for (a, b) in a.iter_mut().zip(b.iter()) {
        a.mul_assign_impl(b);
    }
}

pub fn vec_add_simd(a: &mut [GLV], b: &[GLV]) {
    for (a, b) in a.iter_mut().zip(b.iter()) {
        a.add_assign_impl(b);
    }
}

pub fn vec_mul_simd(a: &mut [GLV], b: &[GLV]) {
    for (a, b) in a.iter_mut().zip(b.iter()) {
        a.mul_assign_impl(b);
    }
}

pub fn vec_add_portable_simd(a: &mut [GLPS], b: &[GLPS]) {
    for (a, b) in a.iter_mut().zip(b.iter()) {
        a.add_assign_impl(b);
    }
}

pub fn vec_mul_portable_simd_long(a: &mut [GLPSL], b: &[GLPSL]) {
    for (a, b) in a.iter_mut().zip(b.iter()) {
        a.mul_assign_impl(b);
    }
}

use crate::utils::*;
pub fn vec_mul_mixed(a: &mut [LN], b: &[LN]) {
    for (a, b) in a.iter_mut().zip(b.iter()) {
        a.mul_assign_nonred_impl(b);
    }

    let mut a: Vec<GLPSL> = cast_check_alignment(a.to_vec());
    // let b: Vec<GLPSL> = cast_check_alignment(b.to_vec());

    for a in a.iter_mut() {
        a.from_u128_with_reduction();
    }
}

pub fn vec_mul_portable_simd(a: &mut [GLPS], b: &[GLPS]) {
    for (a, b) in a.iter_mut().zip(b.iter()) {
        a.mul_assign_impl(b);
    }
}

use std::simd::*;

pub struct GLV(pub Simd<u64, N>);

const N: usize = 16;
const N2: usize = N * 2;

impl GLV {
    #[inline(always)]
    pub fn add_assign_impl(&mut self, other: &Self) -> &mut Self {
        // a + b mod 2^64
        // then reduce modulo 2^64 - 2^32 + 1. Substracting a modulus is
        // the same as adding it's complement, so add 2^32 - 1

        // Note that 2^64 = 2^32 - 1 mod P, so whenever we over flow 2^64,
        // we can immediatelly add 2^32 - 1 insteal

        let modulus_mask = Simd::<u64, N>::splat(EPSILON);
        let zero = Simd::<u64, N>::splat(0);
        let sum = self.0.saturating_add(other.0);
        let of_mask = Simd::simd_lt(sum, other.0);
        // conditionally add modulus
        let modulus_spread = of_mask.select(modulus_mask, zero);
        let sum = sum.saturating_add(modulus_spread);
        let of_mask = Simd::simd_lt(sum, modulus_spread);
        // conditionally add modulus
        let modulus_spread = of_mask.select(modulus_mask, zero);
        let sum = sum.saturating_add(modulus_spread);

        self.0 = sum;

        self
    }

    #[inline(always)]
    pub fn mul_assign_impl(&mut self, other: &Self) -> &mut Self {
        // a * b mod P

        // reduce modulo 2^64 - 2^32 + 1. Substracting a modulus is
        // the same as adding it's complement, so add 2^32 - 1

        // Note that 2^64 = 2^32 - 1 mod P, so whenever we over flow 2^64,
        // we can immediatelly add 2^32 - 1 insteal

        // we try to do the following steps:
        // - get lowest 64 bits, we can not get around it
        // - for every next 32 bit chunk we can use relation 2^64 = 2^32 - 1

        let self_as_u32_chunks: Simd<u32, N2> = unsafe { std::mem::transmute(self.0) };
        let other_as_u32_chunks: Simd<u32, N2> = unsafe { std::mem::transmute(other.0) };

        let self_hi = self_as_u32_chunks;
        let other_hi = other_as_u32_chunks;

        // let self_hi = simd_swizzle!(self_as_u32_chunks, [
        //     1, 0, 3, 2,
        //     5, 4, 7, 6,
        //     8, 8, 11, 10,
        //     13, 12, 15, 14,
        //     17, 16, 19, 18,
        //     21, 20, 23, 22,
        //     25, 24, 27, 26,
        //     29, 28, 31, 30,
        // ]);

        // let other_hi = simd_swizzle!(other_as_u32_chunks, [
        //     1, 0, 3, 2,
        //     5, 4, 7, 6,
        //     8, 8, 11, 10,
        //     13, 12, 15, 14,
        //     17, 16, 19, 18,
        //     21, 20, 23, 22,
        //     25, 24, 27, 26,
        //     29, 28, 31, 30,
        // ]);

        let self_hi: Simd<u64, N> = unsafe { std::mem::transmute(self_hi) };
        let other_hi: Simd<u64, N> = unsafe { std::mem::transmute(other_hi) };

        let z_lo_lo = self.0 * other.0; // doesn't need any reduction yet, and is < P
                                        // because it's range is 2^64 - 2 * 2^32 + 1
        let z_lo_hi = self.0 * other_hi; // range of 2^64 - 2 * 2^32 + 1
        let z_hi_lo = self_hi * other.0; // range of 2^64 - 2 * 2^32 + 1
        let z_hi_hi = self_hi * other_hi; // range of 2^64 - 2 * 2^32 + 1

        let shift_32 = Simd::<u64, N>::splat(32);
        let zero = Simd::<u64, N>::splat(0);

        let z_lo_lo_shifted = z_lo_lo >> shift_32; // highest 32 bits of z_lo_lo
        let sum_tmp = z_lo_hi.saturating_add(z_lo_lo_shifted); // can not overflow, now in range 2^64 - 2^32 + 1
        let lo_mask = Simd::<u64, N>::splat(0x00000000ffffffff);
        let sum_lo = sum_tmp & lo_mask; // bits 32-64, not yet completed

        let sum_mid = sum_tmp >> shift_32; // bits 64-96
        let sum_mid_2 = z_hi_lo.saturating_add(sum_lo); // can not overflow. Bit 32-64 now completed
        let lo = z_lo_lo & lo_mask;
        let lo = lo ^ (sum_mid_2 >> shift_32);
        let sum_mid_2_hi = sum_mid_2 >> shift_32;
        let sum_hi = z_hi_hi.saturating_add(sum_mid);

        let hi = sum_hi.saturating_add(sum_mid_2_hi);

        // now reduce

        let epsilon_mask = Simd::<u64, N>::splat(EPSILON);

        let hi_hi = hi >> shift_32;
        let hi_lo = hi & lo_mask;

        let t0 = lo.saturating_sub(hi_hi);
        let uf_mask = Simd::simd_gt(t0, hi_hi);
        let modulus_spread = uf_mask.select(epsilon_mask, zero);
        let t0 = t0.saturating_add(modulus_spread);

        let t1 = hi_lo * epsilon_mask;
        let t2 = t0.saturating_add(t1);
        let of_mask = Simd::simd_gt(t2, t1);
        let modulus_spread = of_mask.select(epsilon_mask, zero);
        let res = t2.saturating_add(modulus_spread);

        self.0 = res;

        self
    }
}

use std::ops::Add;
use std::ops::BitOr;
use std::ops::Mul;
// use std::ops::MulAssign;

pub struct GLPS(pub packed_simd::u64x4);

impl GLPS {
    #[inline(always)]
    pub fn add_assign_impl(&mut self, other: &Self) -> &mut Self {
        let modulus_mask = packed_simd::u64x4::splat(EPSILON);

        let sum = self.0.add(other.0);
        let sum_reduced = sum.add(modulus_mask);
        let cmp0 = sum_reduced.lt(sum);
        let cmp1 = sum.lt(self.0);
        let reduce_flag = cmp0.bitor(cmp1);
        let res = reduce_flag.select(sum_reduced, sum);

        self.0 = res;

        self
    }

    #[inline(always)]
    pub fn sub_assign_impl(&mut self, other: &Self) -> &mut Self {
        let modulus_mask = packed_simd::u64x4::splat(EPSILON);

        let diff = self.0.sub(other.0);
        let diff_reduced = diff.sub(modulus_mask);
        let cmp = self.0.lt(other.0);
        let res = cmp.select(diff_reduced, diff);

        self.0 = res;

        self
    }

    #[inline(always)]
    pub fn mul_assign_impl(&mut self, other: &Self) -> &mut Self {
        let a: packed_simd::u128x4 = From::from(self.0);
        let b: packed_simd::u128x4 = From::from(other.0);
        let c = a.mul(b);
        let q1 = c.add(c.shr(32));
        // let q2 = q1.shr(64);
        let q2: packed_simd::u64x4 = FromCast::from_cast(q1.shr(64));
        let r1 = q2.mul(CHAR);
        let c: packed_simd::u64x4 = FromCast::from_cast(c);
        let r = c.sub(r1);

        let reduce_flag = r.eq(packed_simd::u64x4::splat(0xffffffffffffffff));
        let res = reduce_flag.select(packed_simd::u64x4::splat(0xffffffff00000000), r);

        self.0 = res;

        self
    }
}

pub struct GLPSL(pub packed_simd::u128x4);

impl GLPSL {
    #[inline(always)]
    pub fn mul_assign_impl(&mut self, other: &Self) -> &mut Self {
        // let mut c = a.mul(b);
        // let q1 = c + (c >> 32);
        // let q2 = q1 >> 64;
        // let r1 = (q2 - (q2 << 32) + (q2 << 64));
        // // let r1 = q2 * modulus;
        // let r = c - r1;

        // let modulus_mask = packed_simd::u128x4::splat(CHAR as u128);
        let shift_32 = packed_simd::u128x4::splat(32);
        let shift_64 = packed_simd::u128x4::splat(64);

        let c = self.0.mul(other.0);
        let q1 = c.add(c.shr(shift_32));
        let q2 = q1.shr(shift_64);
        let r1 = q2.shl(shift_64) - q2.shl(shift_32) + q2;
        let r = c.sub(r1);

        let reduce_flag = r.eq(packed_simd::u128x4::splat(
            0xffffffffffffffffffffffffffffffff,
        ));
        let r = reduce_flag.select(packed_simd::u128x4::splat(0xffffffff00000000), r);

        self.0 = r;

        self
    }

    #[inline(always)]
    pub fn from_u128_with_reduction(&mut self) -> &mut Self {
        let shift_32 = packed_simd::u128x4::splat(32);
        let shift_64 = packed_simd::u128x4::splat(64);

        let c = self.0;
        let q1 = c.add(c.shr(shift_32));
        let q2 = q1.shr(shift_64);
        let r1 = q2.shl(shift_64) - q2.shl(shift_32) + q2;
        let r = c.sub(r1);

        self.0 = r;

        self
    }
}

#[derive(Clone)]
pub struct LN(pub [u128; 32]);

impl LN {
    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub fn mul_assign_nonred_impl(&mut self, other: &Self) -> &mut Self {
        for i in 0..32 {
            self.0[i] *= other.0[i];
            // self.0[i].mul_assign(&other.0[i]);
        }

        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    pub fn from_u128_with_reduction(&mut self) -> &mut Self {
        for i in 0..32 {
            let q1 = self.0[i] + (self.0[i] >> 32);
            let q2 = q1 >> 64;
            let r1 = (q2 << 64) - (q2 << 32) + q2;
            let r = self.0[i] - r1;

            self.0[i] = r;
        }

        self
    }
}

#[cfg(test)]
mod test {

    // #[test]
    // fn calc() {
    //     let mut a = GLx2::from_pair([1, 2]);
    //     let b = GLx2::from_pair([3, 4]);

    //     let c = a.add_assign_impl(&b);
    //     dbg!(&c.0);

    //     let mut a = GLx2::from_pair([CHAR - 2, CHAR - 4]);
    //     let b = GLx2::from_pair([CHAR - 2, CHAR - 4]);

    //     let c = a.add_assign_impl(&b);
    //     dbg!(&c.0);
    // }
}
