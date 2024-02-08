#![allow(
    dead_code, // OK for benches
    clippy::let_unit_value, // False positives
    clippy::needless_range_loop, // Suggests less readable code
)]
#![feature(iter_collect_into)]
#![feature(allocator_api)]

use boojum::fft::precompute_twiddles_for_fft_wrapper;
use boojum::field::goldilocks::GoldilocksField;
use boojum::field::Field;
use boojum::implementations::poseidon2::State;
// use boojum::implementations::state_vectorized_double::StateVecD;

use boojum::field::goldilocks::MixedGL;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use sha3::{Digest, Keccak256};

const MUL_UPPER_BOUND: usize = 1024;

fn criterion_benchmark_multiplication(c: &mut Criterion) {
    let aa: [GoldilocksField; MUL_UPPER_BOUND] = (0..MUL_UPPER_BOUND)
        .map(|x| x as u64 + 1)
        .map(GoldilocksField::from_u64_with_reduction)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let bb: [GoldilocksField; MUL_UPPER_BOUND] = (0..MUL_UPPER_BOUND)
        .map(|x| x as u64 + MUL_UPPER_BOUND as u64)
        .map(GoldilocksField::from_u64_with_reduction)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    c.bench_function("Goldilocks baseline", |b| {
        b.iter(|| {
            let mut aa = black_box(aa);
            let bb = black_box(bb);
            for (dst, src) in aa.iter_mut().zip(bb.iter()) {
                GoldilocksField::mul_assign(dst, src);
            }
        })
    });
}

// fn criterion_benchmark_poseidon_naive(c: &mut Criterion) {
//     let state = [GoldilocksField::ONE; 12];
//     c.bench_function("Poseidon naive", |b| {
//         b.iter(|| poseidon_goldilocks::poseidon_permutation_naive(&mut black_box(state)))
//     });
// }

// fn criterion_benchmark_poseidon_optimized(c: &mut Criterion) {
//     let state = [GoldilocksField::ONE; 12];
//     c.bench_function("Poseidon optimized", |b| {
//         b.iter(|| poseidon_goldilocks::poseidon_permutation_optimized(&mut black_box(state)))
//     });
// }

// fn criterion_benchmark_poseidon_vectorized(c: &mut Criterion) {
//     let state = [GoldilocksField::ONE; 12];
//     c.bench_function("Poseidon vectorized", |b| {
//         b.iter(|| poseidon_goldilocks::poseidon_permutation_vectorized(&mut black_box(state)))
//     });
// }

// fn criterion_benchmark_poseidon_naive_statevec(c: &mut Criterion) {
//     let state = State([GoldilocksField::ONE; 12]);
//     c.bench_function("Poseidon naive State", |b| {
//         b.iter(|| State::poseidon_permutation_naive(&mut black_box(state)))
//     });
// }

fn criterion_benchmark_poseidon2_statevec(c: &mut Criterion) {
    let state = State::from_field_array([GoldilocksField::ONE; 12]);
    c.bench_function("Poseidon2 State general impl", |b| {
        b.iter(|| State::poseidon2_permutation(&mut black_box(state)))
    });
}

// fn criterion_benchmark_poseidon2_statevecd(c: &mut Criterion) {
//     let state = StateVecD::from_array([GoldilocksField::ONE; 12]);
//     c.bench_function("Poseidon2 StateVecD", |b| {
//         b.iter(|| StateVecD::poseidon2_permutation(&mut black_box(state)))
//     });
// }

fn criterion_benchmark_keccak(c: &mut Criterion) {
    let input = [0u8; 64];
    c.bench_function("Keccak256", |b| {
        b.iter(|| Keccak256::digest(black_box(input)))
    });
}

// fn criterion_benchmark_poseidon_mds_mul_naive(c: &mut Criterion) {
//     let state = [GoldilocksField::ONE; 12];
//     c.bench_function("Poseidon MDS naive", |b| {
//         b.iter(|| poseidon_goldilocks::maive_mds_mul_ext(&mut black_box(state)))
//     });
// }

fn criterion_benchmark_poseidon2_mds_mul(c: &mut Criterion) {
    use boojum::implementations::suggested_mds::suggested_mds_mul_ext;
    let state = [GoldilocksField::ONE; 12];
    c.bench_function("Poseidon2 MDS multiplication", |b| {
        b.iter(|| suggested_mds_mul_ext(&mut black_box(state)))
    });
}

fn criterion_benchmark_poseidon2_mds_split_mul(c: &mut Criterion) {
    use boojum::implementations::experimental::poseidon2_matrixes_repr::poseidon2_mds_split_mul_ext;
    let state = [GoldilocksField::ONE; 12];
    c.bench_function("Poseidon2 MDS multiplication by u32 split", |b| {
        b.iter(|| poseidon2_mds_split_mul_ext(&mut black_box(state)))
    });
}

fn criterion_benchmark_circulant_mds_mul_by_fft(c: &mut Criterion) {
    use boojum::implementations::experimental::circulat_matmul_by_fft::goldilocks_mds_matmul_by_fft_ext;
    let state = [GoldilocksField::ONE; 12];
    c.bench_function("Poseidon2 MDS multiplication by FFT", |b| {
        b.iter(|| goldilocks_mds_matmul_by_fft_ext(&mut black_box(state)))
    });
}

fn criterion_benchmark_poseidon2_mds_mul_vectorized(c: &mut Criterion) {
    let state = [GoldilocksField::ONE; 12];
    let state = State::from_field_array(state);
    let mut state = black_box(state);
    c.bench_function("Vectorized Poseidon2 MDS multiplication", |b| {
        b.iter(|| state.suggested_mds_mul())
    });
}

fn criterion_benchmark_poseidon2_inner_matrix_mul(c: &mut Criterion) {
    use boojum::implementations::poseidon2::state_generic_impl::poseidon2_inner_mul_ext;
    let state = [GoldilocksField::ONE; 12];
    c.bench_function("Poseidon2 inner matrix multiplication", |b| {
        b.iter(|| poseidon2_inner_mul_ext(&mut black_box(state)))
    });
}

fn criterion_benchmark_poseidon2_inner_matrix_split_mul(c: &mut Criterion) {
    use boojum::implementations::experimental::poseidon2_matrixes_repr::poseidon2_inner_split_mul_ext;
    let state = [GoldilocksField::ONE; 12];
    c.bench_function("Poseidon2 inner matrix multiplication by u32 split", |b| {
        b.iter(|| poseidon2_inner_split_mul_ext(&mut black_box(state)))
    });
}

// fn criterion_benchmark_poseidon_apply_round_constants(c: &mut Criterion) {
//     let state = [GoldilocksField::ONE; 12];
//     let round = 1;
//     c.bench_function("Poseidon apply_round_constants", |b| {
//         b.iter(|| poseidon_goldilocks::apply_round_constants(&mut black_box(state), black_box(round)))
//     });
// }

fn criterion_benchmark_poseidon_apply_round_constants_statevec(c: &mut Criterion) {
    let state = State::from_field_array([GoldilocksField::ONE; 12]);
    let round = 1;
    c.bench_function("Poseidon apply_round_constants State", |b| {
        b.iter(|| State::apply_round_constants(&mut black_box(state), black_box(round)))
    });
}

// fn criterion_benchmark_poseidon_partial(c: &mut Criterion) {
//     let state = [GoldilocksField::ONE; 12];
//     c.bench_function("Poseidon partial round optimized multiplication", |b| {
//         b.iter(|| poseidon_goldilocks::partial_round_optimized_ext(&mut black_box(state)))
//     });
// }

fn criterion_benchmark_poseidon2_inner_statevec(c: &mut Criterion) {
    // let state = State([GoldilocksField::ONE; 12]);

    let mut rng = rand::thread_rng();
    let mut state = [GoldilocksField::ONE; 12];
    for i in 0..state.len() {
        state[i] = rand_from_rng(&mut rng);
    }
    let state = State::from_field_array(state);

    c.bench_function("Poseidon2 inner multiplication State", |b| {
        // b.iter(|| State::m_i_mul(&mut black_box(state)))
    });
}

// fn criterion_benchmark_poseidon2_inner_opt_statevec(c: &mut Criterion) {
//     let state = State([GoldilocksField::ONE; 12]);
//     c.bench_function("Poseidon2 inner multiplication opt State", |b| {
//         b.iter(|| State::m_i_mul_opt(&mut black_box(state)))
//     });
// }

// fn criterion_benchmark_add_naive(c: &mut Criterion) {
//     let degree: usize = 1 << 24;

//     let aa: Vec<u64> = (0..(degree * 2)).map(|x| x as u64 + 1).collect();
//     let bb: Vec<u64> = (0..(degree * 2)).map(|x| x as u64 + 2).collect();
//     let mut cc: Vec<u64> = Vec::with_capacity(degree * 2);

//     c.bench_function("Naive", |b| {
//         b.iter(|| unsafe {
//             boojum::experiments::naive(black_box(&aa), black_box(&bb), black_box(&mut cc))
//         })
//     });
// }

// fn criterion_benchmark_add_vectors_naive(c: &mut Criterion) {
//     let degree: usize = 1 << 24;

//     let mut aa: Vec<GoldilocksField> = (0..(degree * 2))
//         .map(|x| x as u64 + 1)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect();
//     let bb: Vec<GoldilocksField> = (0..(degree * 2))
//         .map(|x| x as u64 + 2)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect();

//     c.bench_function("Naive Vec add", |b| {
//         b.iter(|| boojum::experiments::vec_add_native(black_box(&mut aa), black_box(&bb)))
//     });
// }

// fn criterion_benchmark_add_vectors_vectorized(c: &mut Criterion) {
//     let degree: usize = 1 << 24;

//     let aa: Vec<GoldilocksField> = (0..(degree * 2))
//         .map(|x| x as u64 + 1)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect();
//     let bb: Vec<GoldilocksField> = (0..(degree * 2))
//         .map(|x| x as u64 + 2)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect();

//     let mut aa = boojum::utils::cast_check_alignment(aa);
//     let bb = boojum::utils::cast_check_alignment(bb);

//     c.bench_function("Unrolled Vec add", |b| {
//         b.iter(|| boojum::experiments::vec_add_vectorized(black_box(&mut aa), black_box(&bb)))
//     });
// }

// fn criterion_benchmark_add_vectors_simd(c: &mut Criterion) {
//     let degree: usize = 1 << 24;

//     use boojum::experiments::GLV;
//     let mut aa = boojum::utils::allocate_with_alignment_of::<GoldilocksField, GLV>(degree * 2);
//     let mut bb = boojum::utils::allocate_with_alignment_of::<GoldilocksField, GLV>(degree * 2);

//     (0..(degree * 2))
//         .map(|x| x as u64 + 1)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect_into(&mut aa);
//     (0..(degree * 2))
//         .map(|x| x as u64 + 2)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect_into(&mut bb);

//     let mut aa = boojum::utils::cast_check_alignment(aa);
//     let bb = boojum::utils::cast_check_alignment(bb);

//     c.bench_function("SIMD Vec add", |b| {
//         b.iter(|| boojum::experiments::vec_add_simd(black_box(&mut aa), black_box(&bb)))
//     });
// }

// fn criterion_benchmark_add_vectors_portable_simd(c: &mut Criterion) {
//     let degree: usize = 1 << 24;

//     use boojum::experiments::GLV;
//     let mut aa = boojum::utils::allocate_with_alignment_of::<GoldilocksField, GLV>(degree * 2);
//     let mut bb = boojum::utils::allocate_with_alignment_of::<GoldilocksField, GLV>(degree * 2);

//     (0..(degree * 2))
//         .map(|x| x as u64 + 1)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect_into(&mut aa);
//     (0..(degree * 2))
//         .map(|x| x as u64 + 2)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect_into(&mut bb);

//     let mut aa = boojum::utils::cast_check_alignment(aa);
//     let bb = boojum::utils::cast_check_alignment(bb);

//     c.bench_function("Portable SIMD Vec add", |b| {
//         b.iter(|| boojum::experiments::vec_add_portable_simd(black_box(&mut aa), black_box(&bb)))
//     });
// }

use boojum::utils::clone_respecting_allignment;

fn criterion_benchmark_add_vectors_mixedgl(c: &mut Criterion) {
    let degree: usize = 1 << 24;

    let aa: Vec<GoldilocksField> = (0..(degree * 2))
        .map(|x| x as u64 + 1)
        .map(GoldilocksField::from_u64_with_reduction)
        .collect();
    let bb: Vec<GoldilocksField> = (0..(degree * 2))
        .map(|x| x as u64 + 2)
        .map(GoldilocksField::from_u64_with_reduction)
        .collect();

    // let mut aa: Vec<MixedGL> = boojum::utils::cast_check_alignment(aa);
    // let bb: Vec<MixedGL> = boojum::utils::cast_check_alignment(bb);

    let mut aa: Vec<MixedGL> =
        MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
            &aa,
        ));
    let bb: Vec<MixedGL> =
        MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
            &bb,
        ));

    c.bench_function("MixedGL Vec add", |b| {
        // b.iter(|| boojum::experiments::vec_add_portable_simd(black_box(&mut aa), black_box(&bb)))
        b.iter(|| MixedGL::vec_add_assign(black_box(&mut aa), black_box(&bb)))
    });
}

fn criterion_benchmark_mul_vectors_naive(c: &mut Criterion) {
    let degree: usize = 1 << 24;

    let aa: Vec<GoldilocksField> = (0..(degree * 2))
        .map(|x| x as u64 + 1)
        .map(GoldilocksField::from_u64_with_reduction)
        .collect();
    let bb: Vec<GoldilocksField> = (0..(degree * 2))
        .map(|x| x as u64 + 2)
        .map(GoldilocksField::from_u64_with_reduction)
        .collect();

    let mut aa: Vec<MixedGL> =
        MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
            &aa,
        ));
    let bb: Vec<MixedGL> =
        MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
            &bb,
        ));

    c.bench_function("MixedGL Vec add", |b| {
        // b.iter(|| boojum::experiments::vec_add_portable_simd(black_box(&mut aa), black_box(&bb)))
        b.iter(|| MixedGL::vec_add_assign(black_box(&mut aa), black_box(&bb)))
    });
}

// fn criterion_benchmark_mul_vectors_vectorized(c: &mut Criterion) {
//     let degree: usize = 1 << 24;

//     let aa: Vec<GoldilocksField> = (0..(degree * 2))
//         .map(|x| x as u64 + 1)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect();
//     let bb: Vec<GoldilocksField> = (0..(degree * 2))
//         .map(|x| x as u64 + 2)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect();

//     let mut aa = boojum::utils::cast_check_alignment(aa);
//     let bb = boojum::utils::cast_check_alignment(bb);

//     c.bench_function("Unrolled Vec mul", |b| {
//         b.iter(|| boojum::experiments::vec_mul_vectorized(black_box(&mut aa), black_box(&bb)))
//     });
// }

// fn criterion_benchmark_mul_vectors_simd(c: &mut Criterion) {
//     let degree: usize = 1 << 24;

//     use boojum::experiments::GLV;
//     let mut aa = boojum::utils::allocate_with_alignment_of::<GoldilocksField, GLV>(degree * 2);
//     let mut bb = boojum::utils::allocate_with_alignment_of::<GoldilocksField, GLV>(degree * 2);

//     (0..(degree * 2))
//         .map(|x| x as u64 + 1)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect_into(&mut aa);
//     (0..(degree * 2))
//         .map(|x| x as u64 + 2)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect_into(&mut bb);

//     let mut aa = boojum::utils::cast_check_alignment(aa);
//     let bb = boojum::utils::cast_check_alignment(bb);

//     c.bench_function("SIMD Vec mul", |b| {
//         b.iter(|| boojum::experiments::vec_mul_simd(black_box(&mut aa), black_box(&bb)))
//     });
// }

// fn criterion_benchmark_mul_vectors_portable_simd_long(c: &mut Criterion) {
//     let degree: usize = 1 << 24;

//     use boojum::experiments::GLV;
//     let mut aa = boojum::utils::allocate_with_alignment_of::<GoldilocksField, GLV>(degree * 2);
//     let mut bb = boojum::utils::allocate_with_alignment_of::<GoldilocksField, GLV>(degree * 2);

//     (0..(degree * 2))
//         .map(|x| x as u64 + 1)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect_into(&mut aa);
//     (0..(degree * 2))
//         .map(|x| x as u64 + 2)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect_into(&mut bb);

//     let mut aa = boojum::utils::cast_check_alignment(aa);
//     let bb = boojum::utils::cast_check_alignment(bb);

//     c.bench_function("Portable SIMD long Vec mul", |b| {
//         b.iter(|| {
//             boojum::experiments::vec_mul_portable_simd_long(black_box(&mut aa), black_box(&bb))
//         })
//     });
// }

// fn criterion_benchmark_mul_vectors_portable_simd(c: &mut Criterion) {
//     let degree: usize = 1 << 24;

//     use boojum::experiments::GLV;
//     let mut aa = boojum::utils::allocate_with_alignment_of::<GoldilocksField, GLV>(degree * 2);
//     let mut bb = boojum::utils::allocate_with_alignment_of::<GoldilocksField, GLV>(degree * 2);

//     (0..(degree * 2))
//         .map(|x| x as u64 + 1)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect_into(&mut aa);
//     (0..(degree * 2))
//         .map(|x| x as u64 + 2)
//         .map(GoldilocksField::from_u64_with_reduction)
//         .collect_into(&mut bb);

//     let mut aa = boojum::utils::cast_check_alignment(aa);
//     let bb = boojum::utils::cast_check_alignment(bb);

//     c.bench_function("Portable SIMD Vec mul", |b| {
//         b.iter(|| boojum::experiments::vec_mul_portable_simd(black_box(&mut aa), black_box(&bb)))
//     });
// }

fn criterion_benchmark_mul_vectors_mixedgl(c: &mut Criterion) {
    let degree: usize = 1 << 24;

    let aa: Vec<GoldilocksField> = (0..(degree * 2))
        .map(|x| x as u64 + 1)
        .map(GoldilocksField::from_u64_with_reduction)
        .collect();
    let bb: Vec<GoldilocksField> = (0..(degree * 2))
        .map(|x| x as u64 + 2)
        .map(GoldilocksField::from_u64_with_reduction)
        .collect();

    let mut aa: Vec<MixedGL> =
        MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
            &aa,
        ));
    let bb: Vec<MixedGL> =
        MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
            &bb,
        ));

    c.bench_function("MixedGL Vec mul", |b| {
        // b.iter(|| boojum::experiments::vec_add_portable_simd(black_box(&mut aa), black_box(&bb)))
        b.iter(|| MixedGL::vec_mul_assign(black_box(&mut aa), black_box(&bb)))
    });
}

use boojum::field::rand_from_rng;
use boojum::field::traits::field_like::PrimeFieldLikeVectorized;
use boojum::worker::Worker;
use std::alloc::Global;

fn criterion_benchmark_fft_naive(c: &mut Criterion) {
    let worker = Worker::new();
    let mut ctx = ();
    let mut rng = rand::thread_rng();
    let poly_size_log = 24;
    let poly_size = 1 << poly_size_log;

    let original: Vec<GoldilocksField> = (0..poly_size).map(|_| rand_from_rng(&mut rng)).collect();
    let mut reference = original.clone();
    let coset = GoldilocksField(7);
    let forward_twiddles =
        precompute_twiddles_for_fft_wrapper::<GoldilocksField, Global, false>(poly_size, &worker);

    c.bench_function("FFT Naive", |b| {
        b.iter(|| {
            GoldilocksField::fft_natural_to_bitreversed(
                black_box(&mut reference),
                black_box(coset),
                black_box(&forward_twiddles),
                &mut ctx,
            )
        })
    });
}

fn criterion_benchmark_fft_cache_friendly(c: &mut Criterion) {
    let worker = Worker::new();
    let mut rng = rand::thread_rng();
    let poly_size_log = 24;
    let poly_size = 1 << poly_size_log;

    let original: Vec<GoldilocksField> = (0..poly_size).map(|_| rand_from_rng(&mut rng)).collect();
    let forward_twiddles =
        precompute_twiddles_for_fft_wrapper::<GoldilocksField, Global, false>(poly_size, &worker);
    let mut reference = original.clone();
    let coset = GoldilocksField(7);

    c.bench_function("FFT Cache Friendly", |b| {
        b.iter(|| {
            boojum::fft::fft_natural_to_bitreversed_cache_friendly(
                black_box(&mut reference),
                black_box(coset),
                black_box(&forward_twiddles[..]),
            )
        })
    });
}

fn criterion_benchmark_fft_mixedgl(c: &mut Criterion) {
    let worker = Worker::new();
    let mut ctx = ();
    let mut rng = rand::thread_rng();
    let poly_size_log = 24;
    let poly_size = 1 << poly_size_log;

    #[cfg(all(
        any(target_feature = "neon", target_feature = "avx2"),
        not(all(target_feature = "avx512f", target_feature = "avx512vl"))
    ))]
    println!("Using packed_simd");
    #[cfg(all(target_feature = "avx512f", target_feature = "avx512vl"))]
    println!("Using avx512f, avx512vl");
    #[cfg(not(any(
        all(target_feature = "avx512f", target_feature = "avx512vl"),
        target_feature = "neon",
        target_feature = "avx2"
    )))]
    println!("Using unknown");

    let original: Vec<GoldilocksField> = (0..poly_size).map(|_| rand_from_rng(&mut rng)).collect();
    let forward_twiddles =
        MixedGL::precompute_forward_twiddles_for_fft::<Global>(poly_size, &worker, &mut ctx);
    let mut reference: Vec<MixedGL> =
        MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
            &original,
        ));
    let coset = GoldilocksField(7);

    c.bench_function("FFT MixedGL", |b| {
        b.iter(|| {
            MixedGL::fft_natural_to_bitreversed(
                black_box(&mut reference),
                black_box(coset),
                black_box(&forward_twiddles),
                &mut ctx,
            )
        })
    });
}

fn criterion_benchmark_ifft_naive(c: &mut Criterion) {
    let worker = Worker::new();
    let mut ctx = ();
    let mut rng = rand::thread_rng();
    let poly_size_log = 24;
    let poly_size = 1 << poly_size_log;

    let original: Vec<GoldilocksField> = (0..poly_size).map(|_| rand_from_rng(&mut rng)).collect();
    let mut reference = original.clone();
    let coset = GoldilocksField(7);
    let inverse_twiddles =
        precompute_twiddles_for_fft_wrapper::<GoldilocksField, Global, true>(poly_size, &worker);

    c.bench_function("IFFT Naive", |b| {
        b.iter(|| {
            GoldilocksField::ifft_natural_to_natural(
                black_box(&mut reference),
                black_box(coset),
                black_box(&inverse_twiddles),
                &mut ctx,
            )
        })
    });
}

fn criterion_benchmark_ifft_cache_friendly(c: &mut Criterion) {
    let worker = Worker::new();
    let mut rng = rand::thread_rng();
    let poly_size_log = 24;
    let poly_size = 1 << poly_size_log;

    let original: Vec<GoldilocksField> = (0..poly_size).map(|_| rand_from_rng(&mut rng)).collect();
    let inverse_twiddles =
        precompute_twiddles_for_fft_wrapper::<GoldilocksField, Global, true>(poly_size, &worker);
    let mut reference = original.clone();
    let coset = GoldilocksField(7);

    c.bench_function("IFFT Cache Friendly", |b| {
        b.iter(|| {
            boojum::fft::ifft_natural_to_natural_cache_friendly(
                black_box(&mut reference),
                black_box(coset),
                black_box(&inverse_twiddles[..]),
            )
        })
    });
}

fn criterion_benchmark_ifft_mixedgl(c: &mut Criterion) {
    let worker = Worker::new();
    let mut ctx = ();
    let mut rng = rand::thread_rng();
    let poly_size_log = 24;
    let poly_size = 1 << poly_size_log;

    let original: Vec<GoldilocksField> = (0..poly_size).map(|_| rand_from_rng(&mut rng)).collect();
    let inverse_twiddles =
        MixedGL::precompute_inverse_twiddles_for_fft::<Global>(poly_size, &worker, &mut ctx);
    let mut reference: Vec<MixedGL> =
        MixedGL::vec_from_base_vec(clone_respecting_allignment::<GoldilocksField, MixedGL, _>(
            &original,
        ));
    let coset = GoldilocksField(7);

    c.bench_function("IFFT MixedGL", |b| {
        b.iter(|| {
            MixedGL::ifft_natural_to_natural(
                black_box(&mut reference),
                black_box(coset),
                black_box(&inverse_twiddles),
                &mut ctx,
            )
        })
    });
}

fn criterion_benchmark_bitreverse_naive(c: &mut Criterion) {
    let mut rng = rand::thread_rng();
    let poly_size_log = 24;
    let poly_size = 1 << poly_size_log;

    let original: Vec<GoldilocksField> = (0..poly_size).map(|_| rand_from_rng(&mut rng)).collect();
    let mut reference = original.clone();

    c.bench_function("Bitreverse Naive", |b| {
        b.iter(|| boojum::fft::bitreverse_enumeration_inplace(black_box(&mut reference)))
    });
}

criterion_group!(multiplication, criterion_benchmark_multiplication,);

criterion_group!(
    poseidon,
    criterion_benchmark_poseidon2_mds_mul,
    criterion_benchmark_poseidon2_mds_split_mul,
    criterion_benchmark_circulant_mds_mul_by_fft,
    criterion_benchmark_poseidon2_mds_mul_vectorized,
    criterion_benchmark_poseidon2_inner_matrix_mul,
    criterion_benchmark_poseidon2_inner_matrix_split_mul,
    // criterion_benchmark_poseidon_naive,
    // criterion_benchmark_poseidon_optimized,
    // criterion_benchmark_poseidon_vectorized,
    // criterion_benchmark_poseidon_naive_statevec,
    // criterion_benchmark_poseidon2_statevec,
    // criterion_benchmark_keccak,
    // criterion_benchmark_poseidon_mds_mul_naive,
    // criterion_benchmark_poseidon_mds_mul_suggested,
    // criterion_benchmark_poseidon_mds_mul_suggested_vectorized,
    // criterion_benchmark_poseidon_mds_mul_suggested_vectorized_perm,
    // criterion_benchmark_poseidon_apply_round_constants,
    // criterion_benchmark_poseidon_apply_round_constants_statevec,
    // criterion_benchmark_poseidon_partial,
    // criterion_benchmark_poseidon2_inner,
    // criterion_benchmark_poseidon2_inner_with_shifts,
    // criterion_benchmark_poseidon2_inner_statevec,
    // criterion_benchmark_poseidon2_inner_opt_statevec,
);
criterion_group!(
    vectorized,
    // // criterion_benchmark_add_naive,
    // // criterion_benchmark_add_vectorized,
    // // criterion_benchmark_add_vectors_naive,
    // criterion_benchmark_add_vectors_vectorized, //candidate #1
    // // criterion_benchmark_add_vectors_simd,
    // // criterion_benchmark_add_vectors_portable_simd,
    // // criterion_benchmark_add_vectors_glps,
    criterion_benchmark_add_vectors_mixedgl, //candidate #3
                                             // criterion_benchmark_add_vectors_x86, //candidate #2
                                             // criterion_benchmark_mul_vectors_naive,
                                             // criterion_benchmark_mul_vectors_vectorized,
                                             // // criterion_benchmark_mul_vectors_simd,
                                             // // criterion_benchmark_mul_vectors_portable_simd_long,
                                             // // criterion_benchmark_mul_vectors_vectorized_experimental,
                                             // // criterion_benchmark_mul_vectors_portable_simd,
                                             // // criterion_benchmark_mul_vectors_glps,
                                             // criterion_benchmark_mul_vectors_mixedgl,
                                             // // criterion_benchmark_mul_vectors_mixedgl_x86,
);

criterion_group!(
    fft,
    // criterion_benchmark_fft_naive,
    // criterion_benchmark_fft_cache_friendly,
    criterion_benchmark_fft_mixedgl,
);

criterion_group!(
    ifft,
    // criterion_benchmark_ifft_naive,
    // criterion_benchmark_ifft_cache_friendly,
    criterion_benchmark_ifft_mixedgl,
);

// criterion_group!(
//     split_concat,
//     criterion_benchmark_split_concat_mixedgl8,
//     criterion_benchmark_split_concat,
// );

criterion_group!(
    bitreverse,
    criterion_benchmark_bitreverse_naive,
    // criterion_benchmark_bitreverse_mixedgl,
);

// criterion_main!(multiplication);
// criterion_main!(poseidon);
// criterion_main!(multiplication);
criterion_main!(poseidon);
// criterion_main!(vectorized);
// criterion_main!(fft);
// criterion_main!(bitreverse);
