use crate::cs::traits::cs::ConstraintSystem;

use super::SmallField;

/// This trait is used to define the requirements for an element to be compatible
/// with the hard exponentiation step
pub trait HardexpCompatible<F>: Clone
where
    F: SmallField,
{
    fn mul<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>;

    fn square<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>;

    fn conjugate<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>;

    fn inverse<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>;

    fn frobenius_map<CS>(&mut self, cs: &mut CS, power: usize) -> Self
    where
        CS: ConstraintSystem<F>;

    fn pow_u32<CS, S: AsRef<[u64]>>(&mut self, cs: &mut CS, exponent: S) -> Self
    where
        CS: ConstraintSystem<F>;

    fn normalize<CS>(&mut self, cs: &mut CS)
    where
        CS: ConstraintSystem<F>;
}
