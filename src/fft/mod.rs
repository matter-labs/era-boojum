use crate::field::goldilocks::GoldilocksField;
use crate::field::traits::field::{Field, PrimeField};
use crate::field::SmallField;

pub mod transpose;
use crate::field::goldilocks::MixedGL;

// swap via lookup table that itself fits into cache line
const SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE: usize = 6;
const SMALL_BITREVERSE_LOOKUP_TABLE: [u8; 1 << SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE] = const {
    let mut result = [0u8; 1 << SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE];
    let mut i = 0u64;
    let shift_right = 64 - SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE;
    while i < (1 << SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE) {
        let reversed = i.reverse_bits() >> shift_right;
        debug_assert!(reversed <= u8::MAX as u64);
        result[i as usize] = reversed as u8;
        i += 1;
    }

    result
};

// in this case we can easily swap bytes, and then swap bits in bytes
const MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE: usize = 8;
const MEDIUM_BITREVERSE_LOOKUP_TABLE: [u8; 1 << MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE] = const {
    let mut result = [0u8; 1 << MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE];
    let mut i = 0u64;
    let shift_right = 64 - MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE;
    while i < (1 << MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE) {
        let reversed = i.reverse_bits() >> shift_right;
        debug_assert!(reversed <= u8::MAX as u64);
        result[i as usize] = reversed as u8;
        i += 1;
    }

    result
};

// This operation is so cache-unfriendly, that parallelism is not used here
pub const fn bitreverse_enumeration_inplace<T>(input: &mut [T]) {
    if input.len() == 0 {
        return;
    }
    assert!(input.len().is_power_of_two());

    if input.len() <= SMALL_BITREVERSE_LOOKUP_TABLE.len() {
        bitreverse_enumeration_inplace_via_small_lookup(input);
    } else if input.len() <= MEDIUM_BITREVERSE_LOOKUP_TABLE.len() {
        bitreverse_enumeration_inplace_via_medium_lookup(input);
    } else {
        bitreverse_enumeration_inplace_hybrid(input);
    }
}

const fn bitreverse_enumeration_inplace_via_small_lookup<T>(input: &mut [T]) {
    assert!(input.len().is_power_of_two());
    assert!(input.len() <= SMALL_BITREVERSE_LOOKUP_TABLE.len());

    let shift_to_cleanup =
        (SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE as u32) - input.len().trailing_zeros();

    let mut i = 0;
    let work_size = input.len();
    while i < work_size {
        let mut j = SMALL_BITREVERSE_LOOKUP_TABLE[i] as usize;
        j >>= shift_to_cleanup; // if our table size is larger than work size
        if i < j {
            unsafe { input.swap_unchecked(i, j) };
        }

        i += 1;
    }
}

const fn bitreverse_enumeration_inplace_via_medium_lookup<T>(input: &mut [T]) {
    assert!(input.len().is_power_of_two());
    assert!(input.len() <= MEDIUM_BITREVERSE_LOOKUP_TABLE.len());

    let shift_to_cleanup =
        (MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE as u32) - input.len().trailing_zeros();

    let mut i = 0;
    let work_size = input.len();
    while i < work_size {
        let mut j = MEDIUM_BITREVERSE_LOOKUP_TABLE[i] as usize;
        j >>= shift_to_cleanup; // if our table size is larger than work size
        if i < j {
            unsafe { input.swap_unchecked(i, j) };
        }

        i += 1;
    }
}

const fn bitreverse_enumeration_inplace_hybrid<T>(input: &mut [T]) {
    assert!(input.len().is_power_of_two());
    assert!(input.len() > MEDIUM_BITREVERSE_LOOKUP_TABLE.len());
    assert!(input.len() <= 1usize << 31); // a reasonable upper bound to use u32 internally

    // there is a function usize::reverse_bits(), but if one looks into the compiler then
    // will see that it's something like (sorry for C code)
    // ```
    //     uint32_t bit_reverse32(uint32_t x)
    // {
    //     x = (x >> 16) | (x << 16);
    //     x = ((x & 0xFF00FF00) >> 8) | ((x & 0x00FF00FF) << 8);
    //     x = ((x & 0xF0F0F0F0) >> 4) | ((x & 0x0F0F0F0F) << 4);
    //     x = ((x & 0xCCCCCCCC) >> 2) | ((x & 0x33333333) << 2);
    //     return ((x & 0xAAAAAAAA) >> 1) | ((x & 0x55555555) << 1);
    // }
    // ```

    // since we bitreverse a continuous set of indexes, we can save a little by
    // doing two loops, such that one bitreverses (naively) some common bits,
    // and one that bitreversed uncommon via lookup

    let log_n = input.len().trailing_zeros();
    let common_part_log_n = log_n - (MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE as u32);

    // double loop. Note the swapping approach:
    // - lowest bits become highest bits and change every time
    // - highest bits change become lowest bits and change rarely
    // so our "i" counter is a counter over highest bits, and our source is in the form (i << 8) + j
    // and our dst is (reversed_j << common_part_log_n) + reversed_i
    // and since our source and destination are symmetrical we can formally swap them
    // and have our writes cache-friendly
    let mut i = 0;
    let work_size = 1u32 << common_part_log_n;
    while i < work_size {
        // bitreversing byte by byte
        let mut bytes = i.swap_bytes().to_le_bytes();
        bytes[0] = 0;
        bytes[1] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[1] as usize];
        bytes[2] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[2] as usize];
        bytes[3] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[3] as usize];
        let reversed_i = u32::from_le_bytes(bytes) >> (32 - common_part_log_n);

        debug_assert!(reversed_i == i.reverse_bits() >> (32 - common_part_log_n));

        let mut j = 0;
        while j < MEDIUM_BITREVERSE_LOOKUP_TABLE.len() {
            let reversed_j = MEDIUM_BITREVERSE_LOOKUP_TABLE[j];
            let dst = ((i as usize) << MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE) | j;
            let src = ((reversed_j as usize) << common_part_log_n) | (reversed_i as usize);
            if dst < src {
                unsafe { input.swap_unchecked(src, dst) };
            }

            j += 1;
        }

        i += 1;
    }
}

// // This operation is so cache-unfriendly, that parallelism is not used here
// pub const fn bitreverse_enumeration_into<T: Copy>(input: &[T], dst: &mut [T]) {
//     if input.len() == 0 {
//         return;
//     }
//     assert_eq!(input.len(), dst.len());
//     assert!(input.len().is_power_of_two());

//     if input.len() <= SMALL_BITREVERSE_LOOKUP_TABLE.len() {
//         bitreverse_enumeration_inplace_via_small_lookup_into(input, dst);
//     } else if input.len() <= MEDIUM_BITREVERSE_LOOKUP_TABLE.len() {
//         bitreverse_enumeration_inplace_via_medium_lookup_into(input, dst);
//     } else {
//         bitreverse_enumeration_inplace_hybrid_into(input, dst);
//     }
// }

// const fn bitreverse_enumeration_inplace_via_small_lookup_into<T: Copy>(input: &[T], dst: &mut [T]) {
//     assert!(input.len().is_power_of_two());
//     assert!(input.len() <= SMALL_BITREVERSE_LOOKUP_TABLE.len());

//     let shift_to_cleanup =
//         (SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE as u32) - input.len().trailing_zeros();

//     // copy over and swap
//     dst.copy_from_slice(input);

//     let mut i = 0;
//     let work_size = dst.len();
//     while i < work_size {
//         let mut j = SMALL_BITREVERSE_LOOKUP_TABLE[i] as usize;
//         j >>= shift_to_cleanup; // if our table size is larger than work size
//         if i < j {
//             unsafe { dst.swap_unchecked(i, j) };
//         }

//         i += 1;
//     }
// }

// const fn bitreverse_enumeration_inplace_via_medium_lookup_into<T: Copy>(input: &[T], dst: &mut [T]) {
//     assert!(input.len().is_power_of_two());
//     assert!(input.len() <= MEDIUM_BITREVERSE_LOOKUP_TABLE.len());

//     let shift_to_cleanup =
//         (MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE as u32) - input.len().trailing_zeros();

//     // copy over and swap
//     dst.copy_from_slice(input);

//     let mut i = 0;
//     let work_size = dst.len();
//     while i < work_size {
//         let mut j = MEDIUM_BITREVERSE_LOOKUP_TABLE[i] as usize;
//         j >>= shift_to_cleanup; // if our table size is larger than work size
//         if i < j {
//             unsafe { dst.swap_unchecked(i, j) };
//         }

//         i += 1;
//     }
// }

// const fn bitreverse_enumeration_inplace_hybrid_into<T: Copy>(input: &[T], dst: &mut [T]) {
//     assert!(input.len().is_power_of_two());
//     assert!(input.len() > MEDIUM_BITREVERSE_LOOKUP_TABLE.len());
//     assert!(input.len() <= 1usize << 31); // a reasonable upper bound to use u32 internally

//     // there is a function usize::reverse_bits(), but if one looks into the compiler then
//     // will see that it's something like (sorry for C code)
//     // ```
//     //     uint32_t bit_reverse32(uint32_t x)
//     // {
//     //     x = (x >> 16) | (x << 16);
//     //     x = ((x & 0xFF00FF00) >> 8) | ((x & 0x00FF00FF) << 8);
//     //     x = ((x & 0xF0F0F0F0) >> 4) | ((x & 0x0F0F0F0F) << 4);
//     //     x = ((x & 0xCCCCCCCC) >> 2) | ((x & 0x33333333) << 2);
//     //     return ((x & 0xAAAAAAAA) >> 1) | ((x & 0x55555555) << 1);
//     // }
//     // ```

//     // since we bitreverse a continuous set of indexes, we can save a little by
//     // doing two loops, such that one bitreverses (naively) some common bits,
//     // and one that bitreversed uncommon via lookup

//     let log_n = input.len().trailing_zeros();
//     let common_part_log_n = log_n - (MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE as u32);

//     // copy over and swap
//     dst.copy_from_slice(input);

//     // double loop. Note the swapping approach:
//     // - lowest bits become highest bits and change every time
//     // - highest bits change become lowest bits and change rarely
//     // so our "i" counter is a counter over highest bits, and our source is in the form (i << 8) + j
//     // and our dst is (reversed_j << common_part_log_n) + reversed_i
//     // and since our source and destination are symmetrical we can formally swap them
//     // and have our writes cache-friendly
//     let mut i = 0;
//     let work_size = 1u32 << common_part_log_n;
//     while i < work_size {
//         // bitreversing byte by byte
//         let mut bytes = i.swap_bytes().to_le_bytes();
//         bytes[0] = 0;
//         bytes[1] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[1] as usize];
//         bytes[2] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[2] as usize];
//         bytes[3] = MEDIUM_BITREVERSE_LOOKUP_TABLE[bytes[3] as usize];
//         let reversed_i = u32::from_le_bytes(bytes) >> (32 - common_part_log_n);

//         debug_assert!(reversed_i == i.reverse_bits() >> (32 - common_part_log_n));

//         let mut j = 0;
//         while j < MEDIUM_BITREVERSE_LOOKUP_TABLE.len() {
//             let reversed_j = MEDIUM_BITREVERSE_LOOKUP_TABLE[j];
//             let dst = ((i as usize) << MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE) | (j as usize);
//             let src = ((reversed_j as usize) << common_part_log_n) | (reversed_i as usize);
//             if dst < src {
//                 unsafe { input.swap_unchecked(src, dst) };
//             }

//             j += 1;
//         }

//         i += 1;
//     }
// }

// Some basic words on FFT
// Assuming that traces will be quite wide (tens of polys) we agree that parallelism strategy
// for all LDE or FFT operations will be separate polys -> separate cores, instead of trying to parallelise
// internal FFT/LDE subtask

// We also will eventually want to implement a pool of preallocated vectors as we may want to have scratch space
// or partial out-of-place operations, but it's second order optimization

// Some functions below allow us to estimate some machine-specific(!) cache-friendly strategies
// Later on we can update those based on compiler flags / CPU detection, but at the moment
// it's assumed that:
// - L1 cache is 32 Kb and thus fits 2^12 of 8 byte elements
// - L2 cache is 1Mb and fits 2^17 of 8 byte elements
// - cache line is 64 bytes (valid for x86-64. Apple M1 has 128)

// One of the most commonly used strategies for FFT is to divide an original problem of size M into
// n1 * n2 problems where n1 == n2 or n1 == 2*n2. We restrict ourselves to problem sized up to
// 2^24, so splitting will always be L1 cache friendly

// Notes on higher-radix FFTs in prime fields: for complex numbers higher-radix FFTs reduced number of multiplications,
// but for prime field it does not. Nevertheless for small fields where we can read large cache lines
// it's beneficial to use both larger-radix FFT to reduce bandwidth requriements (keep more in registers),
// and also to utilize the fact that cache line fits 8 or 16 field elements

pub fn distribute_powers<F: PrimeField>(input: &mut [F], element: F) {
    let work_size = input.len();
    let mut scale_by = F::ONE;
    let mut idx = 0;
    while idx < work_size {
        input[idx].mul_assign(&scale_by);
        scale_by.mul_assign(&element);
        idx += 1;
    }
}

fn distribute_powers_mixedgl(input: &mut [MixedGL], element: GoldilocksField) {
    let work_size = input.len();
    let mut current = GoldilocksField::ONE;
    let mut scale_by = MixedGL::from_constant(current);

    use crate::field::traits::field_like::PrimeFieldLikeVectorized;
    for i in 0..MixedGL::SIZE_FACTOR {
        scale_by.0[i] = current;
        current.mul_assign(&element);
    }

    let large_step = current;

    let mut idx = 0;
    while idx < work_size {
        use crate::field::traits::field_like::PrimeFieldLike;
        input[idx].mul_assign(&scale_by, &mut ());
        scale_by.mul_constant_assign(&large_step);
        idx += 1;
    }
}

fn distribute_powers_normalized_mixedgl(input: &mut [MixedGL], element: GoldilocksField) {
    use crate::field::traits::field_like::PrimeFieldLikeVectorized;
    let work_size = input.len();
    let mut current = GoldilocksField::ONE;
    let mut scale_by = MixedGL::from_constant(current);
    for i in 0..MixedGL::SIZE_FACTOR {
        scale_by.0[i] = current;
        current.mul_assign(&element);
    }

    let large_step = current;
    let n_inv =
        GoldilocksField::from_u64_with_reduction((input.len() * MixedGL::SIZE_FACTOR) as u64)
            .inverse()
            .unwrap();
    scale_by.mul_constant_assign(&n_inv);

    let mut idx = 0;
    while idx < work_size {
        use crate::field::traits::field_like::PrimeFieldLike;
        input[idx].mul_assign(&scale_by, &mut ());
        scale_by.mul_constant_assign(&large_step);
        idx += 1;
    }
}

// 1Mb
const AVERAGE_L2_CACHE_SIZE_BYTES: usize = 1 << 20;
const AVERAGE_CACHE_BLOCK_SIZE_BYTES: usize = 64;

const fn small_field_cache_friendly_problem_size_for_stride(stride: usize) -> usize {
    // we assume "small field" of 8 bytes per element, so as per
    // "Dynamic data layouts for cache-conscious factorization of DFT"

    // const BLOCK_SIZE_IN_ELEMENTS: usize = AVERAGE_CACHE_BLOCK_SIZE_BYTES / 8;

    AVERAGE_L2_CACHE_SIZE_BYTES / 8 / stride
}

const fn max_stride_for_problem_size(size: usize) -> usize {
    // we assume "small field" of 8 bytes per element, so as per
    // "Dynamic data layouts for cache-conscious factorization of DFT"

    let max = AVERAGE_L2_CACHE_SIZE_BYTES / 8 / size;
    if max == 0 {
        1
    } else if max >= size / 2 {
        if size / 2 > 0 {
            size / 2
        } else {
            1
        }
    } else {
        max
    }
}

pub fn fft_natural_to_bitreversed<F: BaseField>(input: &mut [F], coset: F, twiddles: &[F]) {
    debug_assert!(input.len().is_power_of_two());
    if input.len() > 16 {
        debug_assert!(input.len() == twiddles.len() * 2);
    }

    if coset != F::ONE {
        distribute_powers(input, coset);
    }

    let log_n = input.len().trailing_zeros();

    serial_ct_ntt_natural_to_bitreversed(input, log_n, twiddles);
}

pub fn fft_natural_to_bitreversed_cache_friendly<F: BaseField>(
    input: &mut [F],
    coset: F,
    twiddles: &[F],
) {
    debug_assert!(input.len().is_power_of_two());
    if input.len() > 16 {
        debug_assert!(input.len() == twiddles.len() * 2);
    }

    if coset != F::ONE {
        distribute_powers(input, coset);
    }

    let log_n = input.len().trailing_zeros();

    cache_friendly_ntt_natural_to_bitreversed(input, log_n, twiddles);
}

pub fn ifft_natural_to_natural_cache_friendly<F: BaseField>(
    input: &mut [F],
    coset: F,
    twiddles: &[F],
) {
    debug_assert!(input.len().is_power_of_two());
    if input.len() > 16 {
        debug_assert!(input.len() == twiddles.len() * 2);
    }

    // trick with coset being trivial to supress distributing powers
    fft_natural_to_bitreversed_cache_friendly(input, F::ONE, twiddles);
    bitreverse_enumeration_inplace(input);

    if coset != F::ONE {
        let coset = coset.inverse().expect("inverse of coset must exist");
        distribute_powers(input, coset);
    }

    if input.len() > 1 {
        let n_inv = F::from_u64_with_reduction(input.len() as u64)
            .inverse()
            .unwrap();
        let mut i = 0;
        let work_size = input.len();
        while i < work_size {
            input[i].mul_assign(&n_inv);
            i += 1;
        }
    }
}

pub fn ifft_natural_to_natural<F: BaseField>(input: &mut [F], coset: F, twiddles: &[F]) {
    debug_assert!(input.len().is_power_of_two());
    if input.len() > 16 {
        debug_assert!(input.len() == twiddles.len() * 2);
    }

    let log_n = input.len().trailing_zeros();

    serial_ct_ntt_natural_to_bitreversed(input, log_n, twiddles);
    bitreverse_enumeration_inplace(input);

    if coset != F::ONE {
        let coset = coset.inverse().expect("inverse of coset must exist");
        distribute_powers(input, coset);
    }

    if input.len() > 1 {
        let n_inv = F::from_u64_with_reduction(input.len() as u64)
            .inverse()
            .unwrap();
        let mut i = 0;
        let work_size = input.len();
        while i < work_size {
            input[i].mul_assign(&n_inv);
            i += 1;
        }
    }
}

pub fn fft_natural_to_bitreversed_mixedgl(
    input: &mut [MixedGL],
    coset: GoldilocksField,
    twiddles: &[GoldilocksField],
) {
    debug_assert!(input.len().is_power_of_two());
    if input.len() > 2 {
        debug_assert!(input.len() * 16 == twiddles.len() * 2);
    } else {
        debug_assert!(twiddles.len() == 16)
    }

    if coset != GoldilocksField::ONE {
        distribute_powers_mixedgl(input, coset);
    }

    let log_n = (input.len() * 16).trailing_zeros();

    mixedgl_cache_friendly_ntt_natural_to_bitreversed(input, log_n, twiddles);
}

#[cfg(all(
    target_feature = "avx512bw",
    target_feature = "avx512cd",
    target_feature = "avx512dq",
    target_feature = "avx512f",
    target_feature = "avx512vl"
))]
pub fn fft_natural_to_bitreversed_mixedgl_interleaving(
    input: &mut [MixedGL],
    coset: GoldilocksField,
    twiddles: &[GoldilocksField],
) {
    debug_assert!(input.len().is_power_of_two());
    if input.len() != 1 {
        debug_assert!(input.len() * 8 == twiddles.len() * 2);
    }

    if coset != GoldilocksField::ONE {
        distribute_powers_mixedgl(input, coset);
    }

    let log_n = (input.len() * 8).trailing_zeros();

    mixedgl_cache_friendly_ntt_natural_to_bitreversed_interlieving(input, log_n, twiddles);
}

pub fn ifft_natural_to_natural_mixedgl(
    input: &mut [MixedGL],
    coset: GoldilocksField,
    twiddles: &[GoldilocksField],
) {
    debug_assert!(input.len().is_power_of_two());
    if input.len() > 2 {
        debug_assert!(input.len() * 16 == twiddles.len() * 2);
    } else {
        debug_assert!(twiddles.len() == 16)
    }

    let log_n = (input.len() * 16).trailing_zeros();

    mixedgl_cache_friendly_ntt_natural_to_bitreversed(input, log_n, twiddles);

    let input =
        crate::utils::cast_check_alignment_ref_mut_unpack::<MixedGL, GoldilocksField>(input);
    bitreverse_enumeration_inplace(input);
    let input = crate::utils::cast_check_alignment_ref_mut_pack::<GoldilocksField, MixedGL>(input);

    if coset != GoldilocksField::ONE {
        let coset = coset.inverse().expect("coset must be non-trivial");
        distribute_powers_normalized_mixedgl(input, coset);
    } else if input.len() > 1 {
        let n_inv = GoldilocksField::from_u64_with_reduction((input.len() * 16) as u64)
            .inverse()
            .unwrap();
        let mut i = 0;
        let work_size = input.len();
        while i < work_size {
            input[i].mul_constant_assign(&n_inv);
            i += 1;
        }
    }
}

#[cfg(all(
    target_feature = "avx512bw",
    target_feature = "avx512cd",
    target_feature = "avx512dq",
    target_feature = "avx512f",
    target_feature = "avx512vl"
))]
pub fn ifft_natural_to_natural_mixedgl_interleaving(
    input: &mut [MixedGL],
    coset: GoldilocksField,
    twiddles: &[GoldilocksField],
) {
    debug_assert!(input.len().is_power_of_two());
    if input.len() != 1 {
        debug_assert!(input.len() * 8 == twiddles.len() * 2);
    }

    let log_n = (input.len() * 8).trailing_zeros();

    mixedgl_cache_friendly_ntt_natural_to_bitreversed_interlieving(input, log_n, twiddles);

    let input =
        crate::utils::cast_check_alignment_ref_mut_unpack::<MixedGL, GoldilocksField>(input);
    bitreverse_enumeration_inplace(input);
    let input = crate::utils::cast_check_alignment_ref_mut_pack::<GoldilocksField, MixedGL>(input);

    if coset != GoldilocksField::ONE {
        let coset = coset.inverse().expect("coset must be non-trivial");
        distribute_powers_normalized_mixedgl(input, coset);
    } else {
        if input.len() > 1 {
            let n_inv = GoldilocksField::from_u64_with_reduction((input.len() * 8) as u64)
                .inverse()
                .unwrap();
            let mut i = 0;
            let work_size = input.len();
            while i < work_size {
                input[i].mul_constant_assign(&n_inv);
                i += 1;
            }
        }
    }
}

use crate::cs::traits::GoodAllocator;
use crate::field::traits::field_like::BaseField;
use crate::worker::Worker;

pub fn precompute_twiddles_for_fft_wrapper<F: BaseField, A: GoodAllocator, const INVERSED: bool>(
    fft_size: usize,
    worker: &Worker,
    // _ctx: F::Context,
) -> Vec<F, A> {
    let forward_twiddles = crate::cs::implementations::utils::precompute_twiddles_for_fft::<
        F,
        F,
        A,
        INVERSED,
    >(fft_size, worker, &mut ());

    forward_twiddles
}

pub fn precompute_twiddles_for_fft_natural_wrapper<
    F: BaseField,
    A: GoodAllocator,
    const INVERSED: bool,
>(
    fft_size: usize,
    worker: &Worker,
    // _ctx: F::Context,
) -> Vec<F, A> {
    let forward_twiddles = crate::cs::implementations::utils::precompute_twiddles_for_fft_natural::<
        F,
        F,
        A,
        INVERSED,
    >(fft_size, worker, ());

    forward_twiddles
}

pub(crate) fn serial_ct_ntt_natural_to_bitreversed<F: BaseField>(
    a: &mut [F],
    log_n: u32,
    omegas_bit_reversed: &[F],
) {
    let n = a.len();
    if n == 1 {
        return;
    }

    if a.len() > 16 {
        debug_assert!(n == omegas_bit_reversed.len() * 2);
    }
    debug_assert!(n == (1 << log_n) as usize);

    let mut pairs_per_group = n / 2;
    let mut num_groups = 1;
    let mut distance = n / 2;

    {
        // special case for omega = 1
        debug_assert!(num_groups == 1);
        let idx_1 = 0;
        let idx_2 = pairs_per_group;

        let mut j = idx_1;

        while j < idx_2 {
            let u = a[j];
            let v = a[j + distance];

            let mut tmp = u;
            tmp.sub_assign(&v);

            a[j + distance] = tmp;
            a[j].add_assign(&v);

            j += 1;
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
    }

    while num_groups < n {
        debug_assert!(num_groups > 1);
        let mut k = 0;
        while k < num_groups {
            let idx_1 = k * pairs_per_group * 2;
            let idx_2 = idx_1 + pairs_per_group;
            let s = omegas_bit_reversed[k];

            let mut j = idx_1;
            while j < idx_2 {
                let u = a[j];
                let mut v = a[j + distance];
                v.mul_assign(&s);

                let mut tmp = u;
                tmp.sub_assign(&v);

                a[j + distance] = tmp;
                a[j].add_assign(&v);

                j += 1;
            }

            k += 1;
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
    }
}

pub(crate) fn cache_friendly_ntt_natural_to_bitreversed<F: PrimeField>(
    a: &mut [F],
    log_n: u32,
    omegas_bit_reversed: &[F],
) {
    let n = a.len();
    if n == 1 {
        return;
    }

    // const CACHE_SIZE_LOG: u32 = 20; // 1 MB
    const CACHE_SIZE_LOG: u32 = 20; // 1 MB

    const WORD_SIZE_LOG: u32 = 3; // 8 B
    const CACHE_BUNCH_LOG: u32 = CACHE_SIZE_LOG - WORD_SIZE_LOG; // 2^17 B
    let cache_friendly_round = log_n.saturating_sub(CACHE_BUNCH_LOG); // 7 round

    if a.len() > 16 {
        debug_assert!(n == omegas_bit_reversed.len() * 2);
    }
    debug_assert!(n == (1 << log_n) as usize);

    let mut pairs_per_group = n / 2;
    let mut num_groups = 1;
    let mut distance = n / 2;
    let mut round = 0;

    {
        // special case for omega = 1
        debug_assert!(num_groups == 1);
        let idx_1 = 0;
        let idx_2 = pairs_per_group;

        let mut j = idx_1;
        while j < idx_2 {
            let mut u = a[j];
            let v = a[j + distance];
            u.sub_assign(&v);
            a[j + distance] = u;
            a[j].add_assign(&v);
            j += 1;
        }
        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
        round += 1;
    }

    while round < cache_friendly_round {
        debug_assert!(num_groups > 1);
        let mut k = 0;
        while k < num_groups {
            let idx_1 = k * pairs_per_group * 2;
            let idx_2 = idx_1 + pairs_per_group;
            let s = omegas_bit_reversed[k];

            let mut j = idx_1;
            while j < idx_2 {
                let mut u = a[j];
                let mut v = a[j + distance];
                v.mul_assign(&s);
                u.sub_assign(&v);
                a[j + distance] = u;
                a[j].add_assign(&v);
                j += 1;
            }
            k += 1;
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
        round += 1;
    }
    let mut cache_bunch = 0;
    while cache_bunch < num_groups {
        // num_groups=128 // round loop
        let mut pairs_per_group_in_cache = pairs_per_group;
        let mut distance_in_cache = distance;
        let mut num_groups_in_cache = 1;
        let num_rounds_in_cache = log_n - round; // 17

        let mut round = 0;
        while round < num_rounds_in_cache {
            // experiment

            let mut k = 0;
            while k < num_groups_in_cache {
                // group loop
                let idx_1 = cache_bunch * pairs_per_group * 2 + k * pairs_per_group_in_cache * 2;
                let idx_2 = idx_1 + pairs_per_group_in_cache;
                let s = omegas_bit_reversed[cache_bunch * num_groups_in_cache + k];

                let mut j = idx_1;
                while j < idx_2 {
                    let mut u = a[j];
                    let mut v = a[j + distance_in_cache];
                    v.mul_assign(&s);
                    u.sub_assign(&v);
                    a[j + distance_in_cache] = u;
                    a[j].add_assign(&v);

                    j += 1;
                }
                k += 1;
            }
            pairs_per_group_in_cache /= 2;
            num_groups_in_cache *= 2;
            distance_in_cache /= 2;
            round += 1;
        }
        cache_bunch += 1;
    }
}

#[inline(always)]
pub(crate) fn mixedgl_cache_friendly_ntt_natural_to_bitreversed(
    a: &mut [MixedGL],
    log_n: u32,
    omegas_bit_reversed: &[GoldilocksField],
) {
    let n = a.len() * 16;
    debug_assert!(a.len() > 0);

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    const CACHE_SIZE_LOG: u32 = 22; // 4 MB
    #[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
    const CACHE_SIZE_LOG: u32 = 20; // 1 MB

    const WORD_SIZE_LOG: u32 = 3; // 8 B
    const CACHE_BUNCH_LOG: u32 = CACHE_SIZE_LOG - WORD_SIZE_LOG; // 2^17 B
    let cache_friendly_round = log_n.saturating_sub(CACHE_BUNCH_LOG); // 7 round

    debug_assert!(n == omegas_bit_reversed.len() * 2);
    debug_assert!(n == (1 << log_n) as usize);

    let mut pairs_per_group = a.len() / 2;
    let mut num_groups = 1;
    let mut distance = a.len() / 2;
    let mut round = 0;

    if round < cache_friendly_round {
        // special case for omega = 1
        debug_assert!(num_groups == 1);
        let idx_1 = 0;
        let idx_2 = pairs_per_group;

        let mut j = idx_1;
        while j < idx_2 {
            unsafe {
                MixedGL::butterfly_16x16_impl(
                    a[j].0.as_ptr() as *mut u64,
                    a[j + distance].0.as_ptr() as *mut u64,
                );
            }

            j += 1;
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
        round += 1;
    }

    while round < cache_friendly_round {
        debug_assert!(num_groups > 1);
        let mut k = 0;
        while k < num_groups {
            let idx_1 = k * pairs_per_group * 2;
            let idx_2 = idx_1 + pairs_per_group;
            let s = omegas_bit_reversed[k];

            let mut j = idx_1;
            while j < idx_2 {
                a[j + distance].mul_constant_assign(&s);
                unsafe {
                    MixedGL::butterfly_16x16_impl(
                        a[j].0.as_ptr() as *mut u64,
                        a[j + distance].0.as_ptr() as *mut u64,
                    );
                }

                j += 1;
            }
            k += 1;
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
        round += 1;
    }
    let mut cache_bunch = 0;
    while cache_bunch < num_groups {
        // num_groups=128 // round loop
        let mut pairs_per_group_in_cache = pairs_per_group;
        let mut distance_in_cache = distance;
        let mut num_groups_in_cache = 1;
        let num_rounds_in_cache = log_n - round; // 17
        let mut round_in_cache = 0;

        if (round == 0) & (a.len() > 1) {
            // special case for omega = 1
            debug_assert!(num_groups == 1);
            let idx_1 = 0;
            let idx_2 = pairs_per_group;

            let mut j = idx_1;
            while j < idx_2 {
                unsafe {
                    MixedGL::butterfly_16x16_impl(
                        a[j].0.as_ptr() as *mut u64,
                        a[j + distance].0.as_ptr() as *mut u64,
                    );
                }

                j += 1;
            }

            pairs_per_group_in_cache /= 2;
            num_groups_in_cache *= 2;
            distance_in_cache /= 2;
            round_in_cache += 1;
        }

        while round_in_cache < (num_rounds_in_cache - 4) {
            //attempt to subtract with overflow
            let mut k = 0;
            while k < num_groups_in_cache {
                // group loop
                let idx_1 = cache_bunch * pairs_per_group * 2 + k * pairs_per_group_in_cache * 2;
                let idx_2 = idx_1 + pairs_per_group_in_cache;
                let s = omegas_bit_reversed[cache_bunch * num_groups_in_cache + k];

                let mut j = idx_1;
                while j < idx_2 {
                    a[j + distance_in_cache].mul_constant_assign(&s);
                    unsafe {
                        MixedGL::butterfly_16x16_impl(
                            a[j].0.as_ptr() as *mut u64,
                            a[j + distance_in_cache].0.as_ptr() as *mut u64,
                        );
                    }

                    j += 1;
                }
                k += 1;
            }

            pairs_per_group_in_cache /= 2;
            num_groups_in_cache *= 2;
            distance_in_cache /= 2;
            round_in_cache += 1;
        }

        // ROUND = num_groups_in_cache - 4
        let mut parts = 1;
        let mut k = 0;
        let mut k_idx = 0;
        while k < num_groups_in_cache {
            // group loop
            let idx_1 = cache_bunch * pairs_per_group * 2 + k_idx;
            let s = omegas_bit_reversed[cache_bunch * num_groups_in_cache + k];
            let mut i = 0;
            while i < 8 {
                a[idx_1].0[8 + i].mul_assign(&s);
                i += 1;
            }
            unsafe {
                let ptr1 = a[idx_1].0.as_ptr() as *mut u64;
                let ptr2 = ptr1.offset(8);
                MixedGL::butterfly_8x8_impl(ptr1, ptr2);
            }
            k += parts;
            k_idx += 1;
        }
        num_groups_in_cache *= 2;
        parts *= 2;

        // ROUND = num_groups_in_cache - 3
        let mut k = 0;
        let mut k_idx = 0;
        while k < num_groups_in_cache {
            // group loop
            let idx_1 = cache_bunch * pairs_per_group * 2 + k_idx;
            let mut i = 0;
            while i < 2 {
                let s = omegas_bit_reversed[cache_bunch * num_groups_in_cache + k + i];
                a[idx_1].0[8 * i + 4].mul_assign(&s);
                a[idx_1].0[8 * i + 5].mul_assign(&s);
                a[idx_1].0[8 * i + 6].mul_assign(&s);
                a[idx_1].0[8 * i + 7].mul_assign(&s);
                i += 1;
            }
            unsafe { a[idx_1].butterfly_4x4_impl() };
            k += parts;
            k_idx += 1;
        }
        num_groups_in_cache *= 2;
        parts *= 2;

        // ROUND = num_groups_in_cache - 2
        let mut k = 0;
        let mut k_idx = 0;
        while k < num_groups_in_cache {
            // group loop
            let idx_1 = cache_bunch * pairs_per_group * 2 + k_idx;
            let mut i = 0;
            while i < 4 {
                let s = omegas_bit_reversed[cache_bunch * num_groups_in_cache + k + i];
                a[idx_1].0[4 * i + 2].mul_assign(&s);
                a[idx_1].0[4 * i + 3].mul_assign(&s);
                i += 1;
            }
            unsafe { a[idx_1].butterfly_2x2_impl() };
            k += parts;
            k_idx += 1;
        }
        num_groups_in_cache *= 2;
        parts *= 2;

        // ROUND = num_groups_in_cache - 1
        let mut k = 0;
        let mut k_idx = 0;
        while k < num_groups_in_cache {
            // group loop
            let idx_1 = cache_bunch * pairs_per_group * 2 + k_idx;
            let mut i = 0;
            while i < 8 {
                let s = omegas_bit_reversed[cache_bunch * num_groups_in_cache + k + i];
                a[idx_1].0[2 * i + 1].mul_assign(&s);
                i += 1;
            }
            unsafe { a[idx_1].butterfly_1x1_impl() };
            k += parts;
            k_idx += 1;
        }

        cache_bunch += 1;
    }
}

#[inline(always)]
#[cfg(all(
    target_feature = "avx512bw",
    target_feature = "avx512cd",
    target_feature = "avx512dq",
    target_feature = "avx512f",
    target_feature = "avx512vl"
))]
#[unroll::unroll_for_loops]
pub(crate) fn mixedgl_cache_friendly_ntt_natural_to_bitreversed_interlieving(
    a: &mut [MixedGL],
    log_n: u32,
    omegas_bit_reversed: &[GoldilocksField],
) {
    use std::arch::x86_64::_mm512_loadu_epi64;

    use crate::field::traits::field_like::PrimeFieldLike;
    use crate::field::traits::field_like::PrimeFieldLikeVectorized;
    let n = a.len() * MixedGL::SIZE_FACTOR;
    debug_assert!(a.len() > 0);

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    const CACHE_SIZE_LOG: u32 = 22; // 4 MB
    #[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
    const CACHE_SIZE_LOG: u32 = 20; // 1 MB

    const WORD_SIZE_LOG: u32 = 3; // 8 B
    const CACHE_BUNCH_LOG: u32 = CACHE_SIZE_LOG - WORD_SIZE_LOG; // 2^17 B
    let cache_friendly_round = log_n.saturating_sub(CACHE_BUNCH_LOG); // 7 round

    debug_assert!(n == omegas_bit_reversed.len() * 2);
    debug_assert!(n == (1 << log_n) as usize);

    let mut pairs_per_group = a.len() / 2;
    let mut num_groups = 1;
    let mut distance = a.len() / 2;
    let mut round = 0;

    if round < cache_friendly_round {
        // special case for omega = 1
        debug_assert!(num_groups == 1);
        let idx_1 = 0;
        let idx_2 = pairs_per_group;

        let mut j = idx_1;
        while j < idx_2 {
            unsafe {
                MixedGL::butterfly_8x8_impl(
                    a[j].0.as_ptr() as *mut u64,
                    a[j + distance].0.as_ptr() as *mut u64,
                );
            }

            j += 1;
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
        round += 1;
    }

    while round < cache_friendly_round {
        debug_assert!(num_groups > 1);
        let mut k = 0;
        while k < num_groups {
            let idx_1 = k * pairs_per_group * 2;
            let idx_2 = idx_1 + pairs_per_group;
            let s = omegas_bit_reversed[k];

            let mut j = idx_1;
            while j < idx_2 {
                a[j + distance].mul_constant_assign(&s);
                unsafe {
                    MixedGL::butterfly_8x8_impl(
                        a[j].0.as_ptr() as *mut u64,
                        a[j + distance].0.as_ptr() as *mut u64,
                    );
                }

                j += 1;
            }
            k += 1;
        }

        pairs_per_group /= 2;
        num_groups *= 2;
        distance /= 2;
        round += 1;
    }
    let mut cache_bunch = 0;
    while cache_bunch < num_groups {
        // num_groups=128 // round loop
        let mut pairs_per_group_in_cache = pairs_per_group;
        let mut distance_in_cache = distance;
        let mut num_groups_in_cache = 1;
        let num_rounds_in_cache = log_n - round; // 17
        let mut round_in_cache = 0;

        if (round == 0) & (a.len() > 1) {
            // special case for omega = 1
            debug_assert!(num_groups == 1);
            let idx_1 = 0;
            let idx_2 = pairs_per_group;

            let mut j = idx_1;
            while j < idx_2 {
                let mut u_p = a[j];
                let mut u_n = u_p;
                let mut v = a[j + distance_in_cache];
                u_p.add_assign(&v, &mut ());
                u_n.sub_assign(&v, &mut ());
                a[j] = u_p;
                a[j + distance_in_cache] = u_n;

                j += 1;
            }

            pairs_per_group_in_cache /= 2;
            num_groups_in_cache *= 2;
            distance_in_cache /= 2;
            round_in_cache += 1;
        }

        while round_in_cache < (num_rounds_in_cache - 4) {
            //attempt to subtract with overflow
            let mut k = 0;
            while k < num_groups_in_cache {
                // group loop
                let idx_1 = cache_bunch * pairs_per_group * 2 + k * pairs_per_group_in_cache * 2;
                let idx_2 = idx_1 + pairs_per_group_in_cache;
                let s = omegas_bit_reversed[cache_bunch * num_groups_in_cache + k];

                let mut j = idx_1;
                while j < idx_2 {
                    let mut u_p = a[j];
                    let mut u_n = u_p;
                    let mut v = a[j + distance_in_cache];
                    v.mul_constant_assign(&s);
                    u_p.add_assign(&v, &mut ());
                    u_n.sub_assign(&v, &mut ());
                    a[j] = u_p;
                    a[j + distance_in_cache] = u_n;

                    let mut u_p = a[j + 1];
                    let mut u_n = u_p;
                    let mut v = a[j + 1 + distance_in_cache];
                    v.mul_constant_assign(&s);
                    u_p.add_assign(&v, &mut ());
                    u_n.sub_assign(&v, &mut ());
                    a[j + 1] = u_p;
                    a[j + 1 + distance_in_cache] = u_n;

                    j += 2;
                }
                k += 1;
            }

            pairs_per_group_in_cache /= 2;
            num_groups_in_cache *= 2;
            distance_in_cache /= 2;
            round_in_cache += 1;
        }

        for static_round in 0..4 {
            let (step_size, butterfly_width, omega_permutation) = match static_round {
                // TODO: 0 and 3 cases can be nop.
                // TODO: works with size 8 MixedGL only.
                0 => (1, 8, [0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64]),
                1 => (2, 4, [0u64, 0u64, 0u64, 0u64, 1u64, 1u64, 1u64, 1u64]),
                2 => (4, 2, [0u64, 0u64, 2u64, 2u64, 1u64, 1u64, 3u64, 3u64]),
                3 => (8, 1, [0u64, 4u64, 1u64, 5u64, 2u64, 6u64, 3u64, 7u64]),
                _ => unreachable!(),
            };

            let mut k = 0;
            let mut k_idx = 0;

            while k < num_groups_in_cache {
                // group loop
                let idx_1 = cache_bunch * pairs_per_group * 2 + k_idx;
                let s = &omegas_bit_reversed[cache_bunch * num_groups_in_cache + k
                    ..cache_bunch * num_groups_in_cache + k + MixedGL::SIZE_FACTOR];
                let s_v = unsafe {
                    _mm512_loadu_epi64(
                        &omegas_bit_reversed[cache_bunch * num_groups_in_cache + k] as *const _
                            as *const i64,
                    )
                };
                // let mut s_as_mgl: MixedGL = unsafe { &*(s as *const _ as *const MixedGL) }.clone();
                let mut s_mgl = MixedGL::from_v(s_v);
                s_mgl.permute(&omega_permutation);
                let mut i = 0;

                let (mut u_p, mut v) = a[idx_1].interleave(a[idx_1 + 1], butterfly_width);
                let mut u_n = u_p;
                v.mul_assign(&s_mgl, &mut ());
                u_p.add_assign(&v, &mut ());
                u_n.sub_assign(&v, &mut ());
                (a[idx_1], a[idx_1 + 1]) = u_p.interleave(u_n, butterfly_width);

                k += step_size;
                k_idx += 2;
            }
            num_groups_in_cache *= 2;
        }

        cache_bunch += 1;
    }
}

#[cfg(test)]
mod test {
    use std::alloc::Global;

    use super::*;
    use crate::log;

    #[test]
    fn test_bitreverse() {
        let mut small: Vec<usize> = (0..(1 << SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE)).collect();
        bitreverse_enumeration_inplace(&mut small);
        for (i, value) in small.into_iter().enumerate() {
            let expected = i.reverse_bits()
                >> ((std::mem::size_of::<usize>() * 8) - SMALL_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE);
            assert_eq!(value, expected, "failed for index {}", i);
        }

        let mut medium: Vec<usize> =
            (0..(1 << MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE)).collect();
        bitreverse_enumeration_inplace(&mut medium);
        for (i, value) in medium.into_iter().enumerate() {
            let expected = i.reverse_bits()
                >> ((std::mem::size_of::<usize>() * 8) - MEDIUM_BITREVERSE_LOOKUP_TABLE_LOG_2_SIZE);
            assert_eq!(value, expected, "failed for index {}", i);
        }

        let mut large: Vec<usize> = (0..(1 << 20)).collect();
        bitreverse_enumeration_inplace(&mut large);
        for (i, value) in large.into_iter().enumerate() {
            let expected = i.reverse_bits() >> ((std::mem::size_of::<usize>() * 8) - 20);
            assert_eq!(value, expected, "failed for index {}", i);
        }
    }

    #[test]
    fn strides() {
        for log_2_problem_size in 1..12 {
            log!(
                "Max stride = {} for problem size 2^{}",
                max_stride_for_problem_size(1 << log_2_problem_size),
                log_2_problem_size
            );
        }
    }

    use crate::cs::implementations::utils::{
        domain_generator_for_size, precompute_twiddles_for_fft,
    };
    use crate::field::goldilocks::GoldilocksField;
    use crate::field::traits::field_like::PrimeFieldLikeVectorized;
    use crate::field::{rand_from_rng, Field, PrimeField};
    use crate::utils::{allocate_in_with_alignment_of, clone_respecting_allignment};
    use crate::worker::Worker;

    #[test]
    fn test_over_goldilocks_valid_naive() {
        let worker = Worker::new();
        let mut rng = rand::thread_rng();
        for poly_size_log in 1..10 {
            let poly_size = 1 << poly_size_log;

            let original: Vec<GoldilocksField> =
                (0..poly_size).map(|_| rand_from_rng(&mut rng)).collect();
            let forward_twiddles = precompute_twiddles_for_fft::<
                GoldilocksField,
                GoldilocksField,
                Global,
                false,
            >(poly_size, &worker, &mut ());

            // dbg!(&forward_twiddles);
            let mut forward = original.clone();
            fft_natural_to_bitreversed(&mut forward, GoldilocksField::ONE, &forward_twiddles[..]);
            // fft_natural_to_bitreversed_cache_friendly(&mut forward, GoldilocksField::ONE, &forward_twiddles[..]);
            bitreverse_enumeration_inplace(&mut forward);

            let omega = domain_generator_for_size::<GoldilocksField>(poly_size as u64);
            let mut reference = vec![];
            for i in 0..poly_size {
                let x = Field::pow_u64(&omega, i as u64); //omega.pow_u64(i as u64);
                let mut tmp = GoldilocksField::ZERO;
                let mut current = GoldilocksField::ONE;
                for coeff in original.iter() {
                    let mut c = *coeff;
                    Field::mul_assign(&mut c, &current); //c.mul_assign(&current);
                    Field::add_assign(&mut tmp, &c); //tmp.add_assign(&c);
                    Field::mul_assign(&mut current, &x); //current.mul_assign(&x);
                }

                reference.push(tmp);
            }

            assert_eq!(reference, forward, "failed for size 2^{}", poly_size_log);
        }
    }

    #[test]
    fn test_over_goldilocks_valid_cache_friendly() {
        let worker = Worker::new();
        let mut rng = rand::thread_rng();
        let poly_size_log = 24;

        let poly_size = 1 << poly_size_log;

        let original: Vec<GoldilocksField> =
            (0..poly_size).map(|_| rand_from_rng(&mut rng)).collect();
        // let forward_twiddles = precompute_twiddles_for_fft::<GoldilocksField, GoldilocksField, Global, false>(poly_size, &worker, ());
        let forward_twiddles = precompute_twiddles_for_fft_wrapper::<GoldilocksField, Global, false>(
            poly_size, &worker,
        );

        // dbg!(&forward_twiddles);
        let mut forward = original.clone();
        fft_natural_to_bitreversed_cache_friendly(
            &mut forward,
            GoldilocksField::ONE,
            &forward_twiddles[..],
        );

        let mut reference = original.clone();
        fft_natural_to_bitreversed(&mut reference, GoldilocksField::ONE, &forward_twiddles[..]);

        // assert_eq!(reference, forward, "failed for size 2^{}", poly_size_log);
        assert!(reference.eq(&forward));
    }

    #[test]
    fn test_over_goldilocks_valid_mixedgl() {
        let worker = Worker::new();
        let mut ctx = ();
        let mut rng = rand::thread_rng();
        // for poly_size_log_2 in 5..20 {
        for poly_size_log_2 in 5..21 {
            println!("Running log {}", poly_size_log_2);

            let poly_size: usize = 1 << poly_size_log_2;

            let mut original = allocate_in_with_alignment_of::<GoldilocksField, MixedGL, Global>(
                poly_size, Global,
            );
            // (0..poly_size).map(|_| rand_from_rng::<_, GoldilocksField>(&mut rng)).collect_into(&mut original);
            use rand::Rng;
            (0..poly_size)
                .map(|_| GoldilocksField(rng.gen_range(0..2)))
                .collect_into(&mut original);
            // dbg!(&original);

            let forward_twiddles_gl = GoldilocksField::precompute_forward_twiddles_for_fft::<Global>(
                poly_size, &worker, &mut ctx,
            );
            let forward_twiddles_mixedgl = MixedGL::precompute_forward_twiddles_for_fft::<Global>(
                poly_size, &worker, &mut ctx,
            );

            let coset = GoldilocksField(7);
            // let coset = GoldilocksField::ONE;

            let mut forward: Vec<MixedGL> =
                MixedGL::vec_from_base_vec(clone_respecting_allignment::<
                    GoldilocksField,
                    MixedGL,
                    Global,
                >(&original));

            MixedGL::fft_natural_to_bitreversed(
                &mut forward,
                coset,
                &forward_twiddles_mixedgl,
                &mut ctx,
            );

            let mut reference = original;
            GoldilocksField::fft_natural_to_bitreversed(
                &mut reference,
                coset,
                &forward_twiddles_gl,
                &mut ctx,
            );

            assert_eq!(
                reference,
                MixedGL::vec_into_base_vec(forward),
                "invalid for log2 size {}",
                poly_size_log_2
            );
        }
    }

    #[test]
    fn test_ifft_mixedgl() {
        let worker = Worker::new();
        // let worker = Worker::new_with_num_threads(1);
        let mut ctx = ();
        let mut rng = rand::thread_rng();
        // for poly_size_log_2 in 6..20 {
        for poly_size_log_2 in 5..21 {
            let poly_size: usize = 1 << poly_size_log_2;
            use rand::Rng;
            let mut original = allocate_in_with_alignment_of::<GoldilocksField, MixedGL, Global>(
                poly_size, Global,
            );
            // (0..poly_size).map(|_| rand_from_rng::<_, GoldilocksField>(&mut rng)).collect_into(&mut original);
            (0..poly_size)
                .map(|_| GoldilocksField(rng.gen_range(0..2)))
                .collect_into(&mut original);
            // dbg!(&original);

            let inverse_twiddles_gl = GoldilocksField::precompute_inverse_twiddles_for_fft::<Global>(
                poly_size, &worker, &mut ctx,
            );
            let inverse_twiddles_mixedgl = MixedGL::precompute_inverse_twiddles_for_fft::<Global>(
                poly_size, &worker, &mut ctx,
            );

            let coset = GoldilocksField(7);
            let mut forward: Vec<MixedGL> =
                MixedGL::vec_from_base_vec(clone_respecting_allignment::<
                    GoldilocksField,
                    MixedGL,
                    Global,
                >(&original));
            // ifft_natural_to_natural_mixedgl(&mut forward, coset_vec, &inverse_twiddles[..]);
            MixedGL::ifft_natural_to_natural(
                &mut forward,
                coset,
                &inverse_twiddles_mixedgl,
                &mut ctx,
            );

            let mut reference = original;
            // ifft_natural_to_natural(&mut reference, coset, &inverse_twiddles[..]);
            GoldilocksField::ifft_natural_to_natural(
                &mut reference,
                coset,
                &inverse_twiddles_gl,
                &mut ctx,
            );

            assert_eq!(
                reference,
                MixedGL::vec_into_base_vec(forward.clone()),
                "invalid for log2 size {}",
                poly_size_log_2
            );
            // dbg!(MixedGL::vec_from_base_vec(reference));
            // dbg!(forward);
        }
    }

    #[test]
    fn test_fft_roundtrip_mixedgl() {
        let worker = Worker::new();
        let mut ctx = ();
        let mut rng = rand::thread_rng();

        for poly_size_log_2 in 5..20 {
            let poly_size: usize = 1 << poly_size_log_2;

            let mut original = allocate_in_with_alignment_of::<GoldilocksField, MixedGL, Global>(
                poly_size, Global,
            );
            (0..poly_size)
                .map(|_| rand_from_rng::<_, GoldilocksField>(&mut rng))
                .collect_into(&mut original);

            let forward_twiddles_mixedgl = MixedGL::precompute_forward_twiddles_for_fft::<Global>(
                poly_size, &worker, &mut ctx,
            );
            let inverse_twiddles_mixedgl = MixedGL::precompute_inverse_twiddles_for_fft::<Global>(
                poly_size, &worker, &mut ctx,
            );

            let coset = GoldilocksField(7);
            // let coset = GoldilocksField::ONE;

            let mut forward: Vec<MixedGL> =
                MixedGL::vec_from_base_vec(clone_respecting_allignment::<
                    GoldilocksField,
                    MixedGL,
                    Global,
                >(&original));
            MixedGL::fft_natural_to_bitreversed(
                &mut forward,
                coset,
                &forward_twiddles_mixedgl,
                &mut ctx,
            );
            let mut forward = MixedGL::vec_into_base_vec(forward);
            bitreverse_enumeration_inplace(&mut forward);
            let mut forward = MixedGL::vec_from_base_vec(forward);
            MixedGL::ifft_natural_to_natural(
                &mut forward,
                coset,
                &inverse_twiddles_mixedgl,
                &mut ctx,
            );

            assert_eq!(original, MixedGL::vec_into_base_vec(forward));
        }
    }

    #[test]
    fn test_over_goldilocks_valid_naive_in_coset() {
        let worker = Worker::new();
        let mut rng = rand::thread_rng();
        for poly_size_log in 1..10 {
            let poly_size = 1 << poly_size_log;

            let original: Vec<GoldilocksField> =
                (0..poly_size).map(|_| rand_from_rng(&mut rng)).collect();
            let forward_twiddles = precompute_twiddles_for_fft::<
                GoldilocksField,
                GoldilocksField,
                Global,
                false,
            >(poly_size, &worker, &mut ());

            let mut forward = original.clone();
            fft_natural_to_bitreversed(
                &mut forward,
                GoldilocksField::multiplicative_generator(),
                &forward_twiddles[..],
            );
            bitreverse_enumeration_inplace(&mut forward);

            let omega = domain_generator_for_size::<GoldilocksField>(poly_size as u64);
            let mut reference = vec![];
            for i in 0..poly_size {
                let mut x = Field::pow_u64(&omega, i as u64); //omega.pow_u64(i as u64);
                x.mul_assign(&GoldilocksField::multiplicative_generator());
                let mut tmp = GoldilocksField::ZERO;
                let mut current = GoldilocksField::ONE;
                for coeff in original.iter() {
                    let mut c = *coeff;
                    Field::mul_assign(&mut c, &current); //c.mul_assign(&current);
                    Field::add_assign(&mut tmp, &c); //tmp.add_assign(&c);
                    Field::mul_assign(&mut current, &x); //current.mul_assign(&x);
                }

                reference.push(tmp);
            }

            assert_eq!(reference, forward, "failed for size 2^{}", poly_size_log);
        }
    }

    #[test]
    fn test_over_goldilocks() {
        let worker = Worker::new();
        let mut rng = rand::thread_rng();
        for poly_size_log in 1..20 {
            let poly_size = 1 << poly_size_log;

            let original: Vec<GoldilocksField> =
                (0..poly_size).map(|_| rand_from_rng(&mut rng)).collect();
            let inverse_twiddles = precompute_twiddles_for_fft::<
                GoldilocksField,
                GoldilocksField,
                Global,
                true,
            >(poly_size, &worker, &mut ());
            let forward_twiddles = precompute_twiddles_for_fft::<
                GoldilocksField,
                GoldilocksField,
                Global,
                false,
            >(poly_size, &worker, &mut ());

            let mut forward = original.clone();
            fft_natural_to_bitreversed(&mut forward, GoldilocksField::ONE, &forward_twiddles[..]);
            bitreverse_enumeration_inplace(&mut forward);

            let mut back = forward.clone();
            ifft_natural_to_natural(&mut back, GoldilocksField::ONE, &inverse_twiddles[..]);

            assert_eq!(original, back, "failed for size 2^{}", poly_size_log);
        }
    }

    #[test]
    fn test_over_goldilocks_coset() {
        let mut rng = rand::thread_rng();
        let worker = Worker::new();

        for poly_size_log in 1..20 {
            let poly_size = 1 << poly_size_log;

            let original: Vec<GoldilocksField> =
                (0..poly_size).map(|_| rand_from_rng(&mut rng)).collect();
            let inverse_twiddles = precompute_twiddles_for_fft::<
                GoldilocksField,
                GoldilocksField,
                Global,
                true,
            >(poly_size, &worker, &mut ());
            let forward_twiddles = precompute_twiddles_for_fft::<
                GoldilocksField,
                GoldilocksField,
                Global,
                false,
            >(poly_size, &worker, &mut ());

            let mut forward = original.clone();
            fft_natural_to_bitreversed(
                &mut forward,
                GoldilocksField::multiplicative_generator(),
                &forward_twiddles[..],
            );
            bitreverse_enumeration_inplace(&mut forward);

            let mut back = forward.clone();
            ifft_natural_to_natural(
                &mut back,
                GoldilocksField::multiplicative_generator(),
                &inverse_twiddles[..],
            );

            assert_eq!(original, back, "failed for size 2^{}", poly_size_log);
        }
    }

    #[test]
    fn calculator() {
        use crate::field::traits::representation::U64Representable;

        let mut t = GoldilocksField::from_u64_unchecked(0xc3bbb4c7a16f4463);
        t.mul_assign(&GoldilocksField::from_u64_unchecked(0x64bda2929d4ab026));
        dbg!(t);
    }
}
