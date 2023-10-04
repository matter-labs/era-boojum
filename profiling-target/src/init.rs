use boojum::field::Field;
use boojum::field::goldilocks::{GoldilocksField, MixedGL};
use boojum::field::traits::field_like::*;

pub const VECTOR_SIZE: u64 = 1 << 20;

fn prng(x: u64) -> u64 {
    (x * 110923) % 10000
}

pub fn generate_gl(size: u64, seed: u64) -> Vec<GoldilocksField> {
    let mut vec = boojum::utils::allocate_with_alignment_of::<GoldilocksField, MixedGL>(size as usize);

    for i in 1..=size {
        vec.push(GoldilocksField::from_nonreduced_u64(prng(i * seed)))
    }
    
    vec
}

pub fn generate_mixedgl(size: u64, seed: u64) -> Vec<MixedGL> {
    let v = generate_gl(size, seed);

    MixedGL::vec_from_base_vec(v)
}

pub fn generate_gl_arr<const N: usize>() -> [GoldilocksField; N] {
    let seed = 1;
    let mut arr = [GoldilocksField::ZERO; N];

    for i in 0..N {
        arr[i] = GoldilocksField::from_u64_with_reduction(prng(i as u64 * seed));
    }

    arr
}
