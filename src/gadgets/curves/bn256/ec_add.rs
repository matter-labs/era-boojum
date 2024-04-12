use crate::{cs::traits::cs::ConstraintSystem, gadgets::curves::SmallField};

use super::*;

/// Adds two points in the plain SW projective coordinates.
pub fn projective_add<F, CS>(
    cs: &mut CS,
    point_1: &mut BN256SWProjectivePoint<F>,
    point_2: BN256SWProjectivePoint<F>,
) -> BN256SWProjectivePoint<F>
where
    F: SmallField,
    CS: ConstraintSystem<F>,
{
    let point_2_x = point_2.x.clone();
    let point_2_y = point_2.y.clone();
    point_1.add_mixed(cs, &mut (point_2_x, point_2_y))
}
