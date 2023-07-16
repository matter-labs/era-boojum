use super::*;
use derivative::*;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Copy, Debug, Hash)]
pub struct GoldilocksExt2;

impl std::fmt::Display for GoldilocksExt2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "GoldilocksExt2")
    }
}

impl GoldilocksExt2 {
    const NON_RESIDUE: GoldilocksField = GoldilocksField(7u64);
}

impl crate::field::FieldExtension<2> for GoldilocksExt2 {
    const TWO_ADICITY: usize = 1;

    type BaseField = GoldilocksField;

    #[inline(always)]
    fn non_residue() -> Self::BaseField {
        Self::NON_RESIDUE
    }

    fn compute_norm(_el: &[Self::BaseField; 2]) -> Self::BaseField {
        todo!()
    }

    fn multiplicative_generator_coeffs() -> [Self::BaseField; 2] {
        todo!()
    }

    #[inline(always)]
    fn mul_by_non_residue(el: &mut Self::BaseField) {
        el.mul_assign(&Self::NON_RESIDUE);
    }
}

impl crate::field::traits::field_like::PrimeFieldLikeExtension<2> for GoldilocksExt2 {
    const TWO_ADICITY: usize = 1;

    type BaseField = GoldilocksField;

    fn compute_norm(
        _el: &[Self::BaseField; 2],
        _ctx: &mut <Self::BaseField as crate::field::traits::field_like::PrimeFieldLike>::Context,
    ) -> Self::BaseField {
        todo!()
    }

    fn multiplicative_generator_coeffs(
        _ctx: &mut <Self::BaseField as crate::field::traits::field_like::PrimeFieldLike>::Context,
    ) -> [Self::BaseField; 2] {
        todo!()
    }

    fn mul_by_non_residue(
        el: &mut Self::BaseField,
        _ctx: &mut <Self::BaseField as crate::field::traits::field_like::PrimeFieldLike>::Context,
    ) {
        el.mul_assign(&Self::NON_RESIDUE);
    }
}
