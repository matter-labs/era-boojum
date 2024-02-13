use crate::field::mersenne::MersenneField;
use crate::field::traits::field_like::PrimeFieldLike;
use crate::field::traits::field::{Field, PrimeField};
use std::arch::x86_64::{self, __m512i, __m512d};
use std::mem::transmute;

#[derive(Hash, Clone, Copy)]
#[repr(C, align(64))]
pub struct MersenneFieldVec(pub [u64; 8]);

impl MersenneFieldVec{
    const MULTIPLICATIVE_GROUP_GENERATOR: __m512i = unsafe { transmute(Self([7u64; 8])) };
    const FIELD_ORDER: __m512i = unsafe { transmute(Self([MersenneField::ORDER as u64; 8])) };
    const MSB_BITMASK: __m512i = unsafe { transmute(Self([(1 << 31); 8])) };
    const FIELD_BITMASK: __m512i = unsafe { transmute(Self([(1 << 31) - 1; 8])) };

    #[inline(always)]
    pub fn as_u64_ptr(&self) -> *const i64 {
        self.0.as_ptr() as *const _
    }

    #[inline(always)]
    pub const fn from_v(x: __m512i) -> Self {
        unsafe { transmute(x) }
    }

    #[inline(always)]
    pub const fn to_v_pd(&self) -> __m512d {
        unsafe { transmute(*self) }
    }

    #[inline(always)]
    pub const fn to_v(&self) -> __m512i {
        unsafe { transmute(*self) }
    }

    pub const fn new(values: [u64; 8]) -> Self{
        let mut i = 0;
        while i < 8 {
            debug_assert!((values[i] >> 31) == 0);
            i += 1;
        }
        Self(values)
    }

    pub const fn new_from_i64(values: [i64; 8]) -> Self{
        let mut i = 0;
        let mut res = [0u64; 8];
        while i < 8 {
            res[i] = values[i] as u64;
            i += 1;
        }
        Self(res)
    }

    pub fn from_partial(elements_in: &[MersenneField]) -> Self {
        let mut elements = [MersenneField::ZERO; 8];
        elements[0..elements_in.len()].copy_from_slice(elements_in);
        let res = elements.map(|x| x.as_u64());
        Self(res)
    }

    #[inline(always)]
    pub(crate) unsafe fn add_no_double_overflow_32_32(x: __m512i, y: __m512i) -> __m512i {
        let res_wrapped = x86_64::_mm512_add_epi64(x, y);
        let msb = x86_64::_mm512_srli_epi64::<31>(res_wrapped);
        let msb = x86_64::_mm512_and_epi64(msb, x86_64::_mm512_set1_epi64(1 as i64));

        // let sum = x86_64::_mm512_xor_epi64(res_wrapped, Self::MSB_BITMASK);
        let sum = x86_64::_mm512_and_epi64(res_wrapped, Self::FIELD_BITMASK);
        let res = x86_64::_mm512_add_epi64(sum, msb);
        res
    }

    #[inline(always)]
    pub(crate) unsafe fn sub_no_double_overflow_32_32(x: __m512i, y: __m512i) -> __m512i {
        let res_wrapped = x86_64::_mm512_sub_epi64(x, y);
        let msb = x86_64::_mm512_srli_epi64::<31>(res_wrapped);
        // let sum = x86_64::_mm512_xor_epi64(res_wrapped, Self::MSB_BITMASK);
        let sum = x86_64::_mm512_and_epi64(res_wrapped, Self::FIELD_BITMASK);
        let res = x86_64::_mm512_sub_epi64(sum, msb);
        res
    }

    #[inline(always)]
    pub(crate) unsafe fn canonicalize(x: __m512i) -> __m512i {
        let mask = x86_64::_mm512_cmpge_epu64_mask(x, Self::FIELD_ORDER);
        x86_64::_mm512_mask_sub_epi64(x, mask, x, Self::FIELD_ORDER)
    }

    #[inline(always)]
    pub(crate) unsafe fn mul32_32(x: __m512i, y: __m512i) -> __m512i {
        let mul = x86_64::_mm512_mul_epu32(x, y);
        mul
    }

    #[inline(always)]
    pub(crate) unsafe fn reduce64(x: __m512i) -> __m512i {
        let hi = x86_64::_mm512_srli_epi64::<31>(x);
        let lo = x86_64::_mm512_and_epi64(x, Self::FIELD_BITMASK);
        let res = Self::add_no_double_overflow_32_32(hi, lo);
        res
    }

    #[inline(always)]
    pub(crate) unsafe fn reduce_negative64(x: __m512i) -> __m512i {
        let hi = x86_64::_mm512_srli_epi64::<31>(x);
        let hi = x86_64::_mm512_and_epi64(hi, Self::FIELD_BITMASK);
        let lo = x86_64::_mm512_and_epi64(x, Self::FIELD_BITMASK);
        let sign = x86_64::_mm512_srli_epi64::<63>(x);

        let res_wrapped = x86_64::_mm512_add_epi64(hi, lo);
        let res_wrapped = x86_64::_mm512_sub_epi64(res_wrapped, sign);
        let msb = x86_64::_mm512_srli_epi64::<31>(res_wrapped);
        let msb = x86_64::_mm512_and_epi64(msb, x86_64::_mm512_set1_epi64(1 as i64));

        let sum = x86_64::_mm512_and_epi64(res_wrapped, Self::FIELD_BITMASK);
        let res = x86_64::_mm512_add_epi64(sum, msb);
        res
    }

    #[inline]
    unsafe fn negate_impl(y: __m512i) -> __m512i {
        x86_64::_mm512_sub_epi64(Self::FIELD_ORDER, Self::canonicalize(y))
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn to_reduced(&mut self) -> &mut Self {
        let r = unsafe { Self::canonicalize(self.to_v()) };
        *self = Self::from_v(r);
        self
    }

    // fn mul_2exp_u64(&self, exp: u64) -> Self {
    //     // In a Mersenne field, multiplication by 2^k is just a left rotation by k bits.
    //     let exp = (exp % 31) as u8;
    //     let left = (self.0 << exp) & ((1 << 31) - 1);
    //     let right = self.0 >> (31 - exp);
    //     let rotated = left | right;
    //     Self::new(rotated)
    // }
    // fn exp_power_of_2(&self, power_log: usize, count: usize) -> Self {
    //     let mut res = *self;
    //     let mut count = count;
    //     for _ in 0..power_log {
    //         count += count;
    //         println!("{}", count);
    //         res.square();
    //     }
    //     res
    // }
    // fn mod_pow(&self, mut exp: u32) -> Self {
    //     let mut base = *self;
    //     let mut result = &mut MersenneFieldVec::new(1);
    //     while exp > 0 {
    //         if exp % 2 == 1 {
    //             result = result.mul_assign(&base.clone());
    //         }
    
    //         exp >>= 1;
    //         base.mul_assign(&base.clone());
    //     }
    
    //     *result
    // }
    // #[inline(always)]
    // pub fn from_u64_with_reduction(x: u64) -> Self {
    //     let x_low = (x as u32) & ((1 << 31) - 1);
    //     let x_high = (x >> 31) as u32;
    //     let mut res = Self(x_low);
    //     res.add_assign(&Self(x_high));
    //     res
    // }
}

impl Default for MersenneFieldVec {
    fn default() -> Self {
        Self([0u64; 8])
    }
}

impl PartialEq for MersenneFieldVec {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for MersenneFieldVec {}

// impl Hash for MersenneFieldVec {
//     fn hash<H: Hasher>(&self, state: &mut H) {
//         state.write_u32(self.to_reduced_u32())
//     }
// }

// impl Ord for MersenneFieldVec {
//     fn cmp(&self, other: &Self) -> core::cmp::Ordering {
//         self.to_reduced().cmp(&other.to_reduced())
//     }
// }

// impl PartialOrd for MersenneFieldVec {
//     fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
//         Some(self.cmp(other))
//     }
// }

impl std::fmt::Debug for MersenneFieldVec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl std::fmt::Display for MersenneFieldVec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl PrimeFieldLike for MersenneFieldVec {
    type Base = MersenneField;
    type Context = ();

    #[inline(always)]
    fn zero(_ctx: &mut Self::Context) -> Self {
        Self([MersenneField::ZERO.as_u64(); 8])
    }
    #[inline(always)]
    fn one(_ctx: &mut Self::Context) -> Self {
        Self([MersenneField::ONE.as_u64(); 8])
    }
    #[inline(always)]
    fn minus_one(_ctx: &mut Self::Context) -> Self {
        Self([MersenneField::MINUS_ONE.as_u64(); 8])
    }

    #[inline(always)]
    fn add_assign(&mut self, other: &Self, _ctx: &mut Self::Context) -> &mut Self {
        let x = self.to_v();
        let y = other.to_v();
        let r = unsafe { Self::add_no_double_overflow_32_32(x, y) };

        *self = Self::from_v(r);

        self
    }

    #[inline(always)]
    fn sub_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &mut Self {
        let x = self.to_v();
        let y = other.to_v();
        let r = unsafe { Self::sub_no_double_overflow_32_32(x, y) };

        *self = Self::from_v(r);

        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn mul_assign(&'_ mut self, other: &Self, _ctx: &mut Self::Context) -> &mut Self {
        let r = unsafe { Self::reduce64(Self::mul32_32(self.to_v(), other.to_v())) };
        *self = Self::from_v(r);
        self
    }

    #[inline(always)]
    fn square(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        let t = *self;
        self.mul_assign(&t, _ctx);

        self
    }

    #[inline(always)]
    fn negate(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        unsafe {
            let x = self.to_v();
            let r = Self::negate_impl(x);

            *self = Self::from_v(r);
            self
        }
    }

    #[inline(always)]
    fn double(&'_ mut self, _ctx: &mut Self::Context) -> &'_ mut Self {
        let t = *self;
        self.add_assign(&t, _ctx);

        self
    }

    #[inline(always)]
    #[unroll::unroll_for_loops]
    fn inverse(&self, _ctx: &mut Self::Context) -> Self {
        let mut result = *self;
        for i in 0..8 {
            result.0[i] = PrimeField::inverse(&MersenneField::new(result.0[i] as u32)).expect("inverse must exist").as_u64();
        }

        result
    }

    #[inline(always)]
    fn constant(value: Self::Base, _ctx: &mut Self::Context) -> Self {
        Self([value.0 as u64; 8])
    }
}

// impl Field for MersenneFieldVec {
//     const ZERO: Self = Self([0u64; 8]);
//     const ONE: Self = Self([0u64; 8]);
//     const TWO: Self = Self([0u64; 8]);
//     const MINUS_ONE: Self = Self([MersenneField::ORDER as u64 - 1; 8]);

//     #[inline(always)]
//     fn is_zero(&self) -> bool {
//         self.to_reduced().0 == Self::ZERO.0
//     }


//     #[inline(always)]
//     fn as_u64(self) -> u64 {
//         self.0 as u64
//     }

//     #[inline(always)]
//     fn from_u64_unchecked(value: u64) -> Self{
//         Self::new(
//             value.try_into()
//                 .expect("Too large"),
//         )
//     }
//     #[inline(always)]
//     fn from_u64(value: u64) -> Option<Self> {
//         if value as u32 >= Self::ORDER {
//             None
//         } else {
//             Some(Self(value as u32))
//         }
//     }
    
//     #[inline(always)]
//     fn from_u64_with_reduction(value: u64) -> Self {
//         Self::from_u64_with_reduction(value)
//     }

//     #[inline(always)]
//     fn as_u64_array<const N: usize>(input: [Self; N]) -> [u64; N] {
//         unsafe { *(&input as *const _ as *const [u64; N]) }
//     }

//     #[inline(always)]
//     fn as_u64_reduced(&self) -> u64 {
//         self.to_reduced_u32() as u64
//     }

//     fn as_boolean(&self) -> bool{
//         let as_uint = self.to_reduced_u32();
//         assert!(as_uint == 0 || as_uint == 1);
//         as_uint != 0
//     }

//     fn inverse(&self) -> Option<Self>{
//         //Since the nonzero elements of GF(pn) form a finite group with respect to multiplication,
//         // a^p^n−1 = 1 (for a ≠ 0), thus the inverse of a is a^p^n−2.
//         if self.is_zero() {
//             return None;
//         }
//         Some(self.mod_pow(MersenneFieldVec::ORDER - 2))
//     }
    
//     fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self{
//         let mut sum = self.0.wrapping_add(other.0);
//         let msb = sum & (1 << 31);
//         sum.bitxor_assign(msb);
//         sum += u32::from(msb != 0);
//         if sum >= Self::ORDER {
//             sum -= Self::ORDER;
//         }
//         self.0 = sum;

//         self
//     }
//     // sub
//     fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self{
//         let mut sum = self.0.wrapping_sub(other.0);
//         let msb = sum & (1 << 31);
//         sum.bitxor_assign(msb);
//         sum -= u32::from(msb != 0);
//         self.0 = sum;

//         self

//     }
//     // mul
//     fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self{
//         let product = u64::from(self.0) * u64::from(other.0);
//         let product_low = (product as u32) & ((1 << 31) - 1);
//         let product_high = (product >> 31) as u32;
//         *self = Self(product_low);
//         self.add_assign(&Self(product_high));
//         self
//     }
//     // square
//     fn square(&'_ mut self) -> &'_ mut Self{
//         self.mul_assign(&self.clone())

//     }
//     // negate
//     #[inline(always)]
//     fn negate(&'_ mut self) -> &'_ mut Self{
//         if self.is_zero() == false {
//             *self = Self(Self::ORDER - self.to_reduced_u32());
//         }
    
//         self
//     }
//     // double
//     fn double(&'_ mut self) -> &'_ mut Self{
//         let t = *self;
//         self.add_assign(&t);

//         self
//     }

// }

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;




    #[test]
    fn test_vec_addition() {
        let mut ctx = ();
        let mut rng = rand::thread_rng();
        let length = 1 << 10;
        let mut input_0 = vec![];
        let mut input_1 = vec![];
        for i in 0..length {
            input_0.push(MersenneField::from_u64_with_reduction(rng.gen()));
            input_1.push(MersenneField::from_u64_with_reduction(rng.gen()));
        }

        // ref
        let mut res_ref = input_0.clone();
        for i in 0..length {
            Field::add_assign(&mut res_ref[i], &input_1[i]);
        }

        // test
        let mut res_test = Vec::with_capacity(length);
        for (chunk0, chunk1) in input_0.chunks(8).zip(input_1.chunks(8)) {
            let mut in0 = MersenneFieldVec::from_partial(chunk0);
            let in1 = MersenneFieldVec::from_partial(chunk1);
            in0.add_assign(&in1, &mut ctx);
            res_test.extend_from_slice(&in0.0.map(|x| MersenneField::from_u64_with_reduction(x))[..]);
        }

        assert_eq!(res_ref, res_test);

    }


    #[test]
    fn test_vec_multiplication() {
        let mut ctx = ();
        let mut rng = rand::thread_rng();
        let length = 1 << 10;
        let mut input_0 = vec![];
        let mut input_1 = vec![];
        for i in 0..length {
            input_0.push(MersenneField::from_u64_with_reduction(rng.gen()));
            input_1.push(MersenneField::from_u64_with_reduction(rng.gen()));
        }

        // ref
        let mut res_ref = input_0.clone();
        for i in 0..length {
            Field::mul_assign(&mut res_ref[i], &input_1[i]);
        }

        // test
        let mut res_test = Vec::with_capacity(length);
        for (chunk0, chunk1) in input_0.chunks(8).zip(input_1.chunks(8)) {
            let mut in0 = MersenneFieldVec::from_partial(chunk0);
            let in1 = MersenneFieldVec::from_partial(chunk1);
            in0.mul_assign(&in1, &mut ctx);
            res_test.extend_from_slice(&in0.0.map(|x| MersenneField::from_u64_with_reduction(x))[..]);
        }

        assert_eq!(res_ref, res_test);

    }

    #[test]
    fn test_vec_reduce() {
        use std::ops::BitXorAssign;
        
        let input: u64 = 18446663704134054963;// 18446661344049526910;// 98251671809866;// 18446661344049526910;

        // ref
        let res_ref = MersenneField::from_negative_u64_with_reduction(input as u64);
        dbg!(res_ref);
        
        let x = input;// & ((1 << 62) - 1);
        let x_low = (x as u32) & ((1 << 31) - 1);
        let x_high = ((x >> 31) as u32) & ((1 << 31) - 1);
        let x_high_high = (x >> 63) as u32;
        let res_wrapped = x_low.wrapping_add(x_high);
        let res_wrapped = res_wrapped - x_high_high;
        let msb = res_wrapped & (1 << 31);
        let mut sum = res_wrapped;
        sum.bitxor_assign(msb);
        let mut res = sum + u32::from(msb != 0);
        // res -= u32::from(x_high_high != 0);
        if res >= MersenneField::ORDER {
            res -= MersenneField::ORDER;
        }
        dbg!(x_high);
        dbg!(x_low);
        // dbg!(x_high_high);
        dbg!(res_wrapped);
        dbg!(msb);
        dbg!(sum);
        dbg!(res);


        // test
        let res_test = unsafe {
            let input_vec = x86_64::_mm512_set1_epi64(input as i64);
            let res_test = MersenneFieldVec::reduce_negative64(input_vec);
            let res_test = MersenneFieldVec::from_v(res_test);

            let x = input_vec;
            // let mask = x86_64::_mm512_set1_epi64(0x7fffffffffffffff as i64);
            // let x = x86_64::_mm512_and_epi64(x, mask);
            let hi = x86_64::_mm512_srli_epi64::<31>(x);
            let lo = x86_64::_mm512_and_epi64(x, MersenneFieldVec::FIELD_BITMASK);
            let res_wrapped = x86_64::_mm512_add_epi64(hi, lo);
            let msb = x86_64::_mm512_srli_epi64::<31>(res_wrapped);
            let msb = x86_64::_mm512_and_epi64(msb, x86_64::_mm512_set1_epi64(1 as i64));
            let sum = x86_64::_mm512_and_epi64(res_wrapped, MersenneFieldVec::FIELD_BITMASK);
            let res = x86_64::_mm512_add_epi64(sum, msb);
            // dbg!(hi);
            // dbg!(lo);
            // dbg!(res_wrapped);
            // dbg!(msb);
            // dbg!(sum);
            // dbg!(res);

            res_test.0[0]
        };

        assert_eq!(res_ref.0, res_test as u32);

    }
}
