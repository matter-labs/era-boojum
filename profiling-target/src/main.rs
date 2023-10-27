#![feature(allocator_api)]

use std::{env, collections::HashMap, time::Instant};

use boojum::{field::{traits::field_like::{PrimeFieldLike, PrimeFieldLikeVectorized}, goldilocks::{MixedGL, GoldilocksField}}, worker::Worker};

mod init;
mod poseidon2;

const REPETITIONS_ADD: u64 = 4000;
const REPETITIONS_FFT: u64 = 100;

fn main() {
    
    let args: Vec<_> = env::args().collect();

    let map: HashMap<&str, fn()> = [
        ("op_vec_vec", op_vec_vec as fn()),
        ("op_vec_vec_scalar", op_vec_vec_scalar as fn()),
        ("op_vec_vec_packed", op_vec_vec_packed as fn()),
        ("add_vec_vec_scalar", add_vec_vec_scalar as fn()),
        ("sub_vec_vec_scalar", sub_vec_vec_scalar as fn()),
        ("mul_vec_vec_scalar", mul_vec_vec_scalar as fn()),
        ("add_vec_vec_packed", add_vec_vec_packed as fn()),
        ("sub_vec_vec_packed", sub_vec_vec_packed as fn()),
        ("mul_vec_vec_packed", mul_vec_vec_packed as fn()),
        ("fft", fft as fn()),
        ("fft_scalar", fft_scalar as fn()),
        ("fft_packed", fft_packed as fn()),
        ("pos2_mds_mul_scalar", poseidon2::pos2_mds_mul_scalar as fn()),
        ("pos2_mds_mul_packed", poseidon2::pos2_mds_mul_packed as fn()),
        ("poseidon2_scalar", poseidon2::poseidon2_scalar as fn()),
        ("poseidon2_packed", poseidon2::poseidon2_packed as fn()),
    ].into_iter().collect();
    
    println!("features:");
    let mut features = Vec::new();
    if cfg!(target_feature = "avx2") { features.push("Using avx2"); }
    if cfg!(target_feature = "avx512bw") { features.push("Using avx512bw"); }
    if cfg!(target_feature = "avx512cd") { features.push("Using avx512cd"); }
    if cfg!(target_feature = "avx512dq") { features.push("Using avx512dq"); }
    if cfg!(target_feature = "avx512f") { features.push("Using avx512f"); }
    if cfg!(target_feature = "avx512vl") { features.push("Using avx512vl"); }
    for s in features {
        println!("{s}");
    }
    println!("---");

    match args.len() {
        0 | 1 => {
            let mut keys: Vec<_> = map.keys().collect();
            keys.sort_unstable();
            for key in keys {
                println!("{}", key);
            }
        },
        _ => {
            map[args[1].as_str()]();
        }
    }
}

fn op_vec_vec() {
    op_vec_vec_scalar();
    op_vec_vec_packed();
}

fn op_vec_vec_scalar() {
    add_vec_vec_scalar();
    sub_vec_vec_scalar();
    mul_vec_vec_scalar();
}

fn op_vec_vec_packed() {
    add_vec_vec_packed();
    sub_vec_vec_packed();
    mul_vec_vec_packed();
}

fn fft() {
    fft_scalar();
    fft_packed();
}

fn add_vec_vec_scalar() {
    let mut v1 = init::generate_gl(init::VECTOR_SIZE, 1);
    let v2 = init::generate_gl(init::VECTOR_SIZE, 2);

    let now = Instant::now();
    for _ in 0..REPETITIONS_ADD {
        for (a, b) in v1.iter_mut().zip(v2.iter()) {
            a.add_assign(b, &mut ());
        }
    }
    
    println!("add_vec_vec_scalar taken {:?}", now.elapsed());
}

fn sub_vec_vec_scalar() {
    let mut v1 = init::generate_gl(init::VECTOR_SIZE, 1);
    let v2 = init::generate_gl(init::VECTOR_SIZE, 2);

    let now = Instant::now();
    for _ in 0..REPETITIONS_ADD {
        for (a, b) in v1.iter_mut().zip(v2.iter()) {
            a.sub_assign(b, &mut ());
        }
    }
    
    println!("sub_vec_vec_scalar taken {:?}", now.elapsed());
}

fn mul_vec_vec_scalar() {
    let mut v1 = init::generate_gl(init::VECTOR_SIZE, 1);
    let v2 = init::generate_gl(init::VECTOR_SIZE, 2);

    let now = Instant::now();
    for _ in 0..REPETITIONS_ADD {
        for (a, b) in v1.iter_mut().zip(v2.iter()) {
            a.mul_assign(b, &mut ());
        }
    }
    
    println!("mul_vec_vec_scalar taken {:?}", now.elapsed());
}

fn add_vec_vec_packed() {
    let mut v1 = init::generate_mixedgl(init::VECTOR_SIZE, 1);
    let v2 = init::generate_mixedgl(init::VECTOR_SIZE, 2);

    let now = Instant::now();
    for _ in 0..REPETITIONS_ADD {
        for (a, b) in v1.iter_mut().zip(v2.iter()) {
            a.add_assign(b, &mut ());
        }
    }
    
    println!("add_vec_vec_packed taken {:?}", now.elapsed());
}

fn sub_vec_vec_packed() {
    let mut v1 = init::generate_mixedgl(init::VECTOR_SIZE, 1);
    let v2 = init::generate_mixedgl(init::VECTOR_SIZE, 2);

    let now = Instant::now();
    for _ in 0..REPETITIONS_ADD {
        for (a, b) in v1.iter_mut().zip(v2.iter()) {
            a.sub_assign(b, &mut ());
        }
    }
    
    println!("sub_vec_vec_packed taken {:?}", now.elapsed());
}

fn mul_vec_vec_packed() {
    let mut v1 = init::generate_mixedgl(init::VECTOR_SIZE, 1);
    let v2 = init::generate_mixedgl(init::VECTOR_SIZE, 2);

    let now = Instant::now();
    for _ in 0..REPETITIONS_ADD {
        for (a, b) in v1.iter_mut().zip(v2.iter()) {
            a.mul_assign(b, &mut ());
        }
    }
    
    println!("mul_vec_vec_packed taken {:?}", now.elapsed());
}

fn fft_scalar() {
    let mut v = init::generate_gl(init::VECTOR_SIZE, 1);
    let mut vs = vec![v; REPETITIONS_FFT as usize];
    let twiddles = GoldilocksField::precompute_forward_twiddles_for_fft::<std::alloc::Global>(
                init::VECTOR_SIZE as usize, 
                &Worker::new(), 
                &mut ());
    let coset = GoldilocksField(2);

    let now = Instant::now();
    vs.iter_mut().for_each(|x| GoldilocksField::fft_natural_to_bitreversed(x, coset, &twiddles, &mut ()));

    println!("fft_scalar taken {:?}", now.elapsed());
}


fn fft_packed() {
    let mut v = init::generate_mixedgl(init::VECTOR_SIZE, 1);
    let mut vs = vec![v; REPETITIONS_FFT as usize];
    let twiddles = MixedGL::precompute_forward_twiddles_for_fft::<std::alloc::Global>(
        init::VECTOR_SIZE as usize, 
        &Worker::new(), 
        &mut ());
    let coset = GoldilocksField(2);

    let now = Instant::now();
    vs.iter_mut().for_each(|x| MixedGL::fft_natural_to_bitreversed(x, coset, &twiddles, &mut ()));

    println!("fft_packed taken {:?}", now.elapsed());
}


#[cfg(test)]
mod test {
    use crate::add_vec_vec_packed;

    #[test]
    fn playground() {
        add_vec_vec_packed();
    }
}
