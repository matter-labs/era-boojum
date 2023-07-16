pub mod goldilocks;
pub mod traits;

pub use self::traits::field::*;
pub use self::traits::representation::*;

pub fn rand_from_rng<R: rand::Rng, F: SmallField>(rng: &mut R) -> F {
    F::from_u64_unchecked(rng.gen_range(0..F::CHAR))
}

pub trait SmallField:
    SmallFieldRepresentable + Field + PrimeField + serde::Serialize + serde::de::DeserializeOwned
{
    const CHAR: u64;
    // computes a*b + c, handy in small fields where a * b + c doesn't overflow u128::MAX
    fn fma(a: Self, b: Self, c: Self) -> Self;

    // We really want to cast to vector sometimes
    const CAN_CAST_VECTOR_TO_U64_LE_VECTOR: bool;
}
