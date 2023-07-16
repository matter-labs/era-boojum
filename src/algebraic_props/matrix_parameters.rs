use super::*;

/// A trait which exposes matrix coefficients for algebraic hash functions.
pub trait MatrixParameters<F: PrimeField, const N: usize>: 'static + Clone + Send + Sync {
    const COEFFS: [[F; N]; N];
}
