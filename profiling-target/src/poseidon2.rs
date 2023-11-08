use crate::init;
use boojum::implementations::poseidon2;

const MDS_ITERS: usize = 1_000_000;

pub fn pos2_mds_mul_scalar() {
    let mut state = init::generate_gl_arr::<12>();

    let now = std::time::Instant::now();
    for _ in 0..MDS_ITERS {
        boojum::implementations::suggested_mds::suggested_mds_mul_ext(&mut state);
    }
    println!("pos2_mds_mul_scalar taken {:?}", now.elapsed());
}

pub fn pos2_mds_mul_packed() {
    let mut state = poseidon2::State::from_field_array(init::generate_gl_arr::<12>());

    let now = std::time::Instant::now();
    for _ in 0..MDS_ITERS {
        // state.suggested_mds_mul();
    }
    println!("pos2_mds_mul_packed taken {:?}", now.elapsed());
}

pub fn poseidon2_scalar() {
    let mut state = init::generate_gl_arr::<12>();
    let mut state = boojum::implementations::poseidon2::state_generic_impl::State::from_field_array(state);

    let now = std::time::Instant::now();
    for _ in 0..MDS_ITERS {
        state.poseidon2_permutation();
    }
    println!("pos2_mds_mul_scalar taken {:?}", now.elapsed());
}

pub fn poseidon2_packed() {
    let mut state = init::generate_gl_arr::<12>();
    let mut state = poseidon2::State::from_field_array(state);

    let now = std::time::Instant::now();
    for _ in 0..MDS_ITERS {
        std::hint::black_box(state.poseidon2_permutation());
    }
    println!("pos2_mds_mul_scalar taken {:?}", now.elapsed());
}
