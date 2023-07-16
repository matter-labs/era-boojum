use super::*;

pub const TRANSPOSE_SCRATCH_SPACE_ELEMENTS: usize = 64;

// this is Fraser's transposition. It's out of place (not a big deal), and uses scratch space
// See https://nas.nasa.gov/assets/pdf/techreports/1989/rnr-89-012.pdf
pub fn transpose<F: SmallField>(
    _input: &[F],
    _output: &mut [F],
    scratch: &mut [[F; TRANSPOSE_SCRATCH_SPACE_ELEMENTS]; 2],
    dims: (usize, usize),
) {
    // We do not benefit from multicore here, as usual

    // we transpose from input as dim_0 x dim_1 in row-major order into
    // dim_1 x dim_0 in row major order
    let (_dim_0, _dim_1) = dims;

    let [_buffer_0, _buffer_1] = scratch;
}
