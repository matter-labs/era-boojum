use crate::cs::gates::{ReductionByPowersGate, ReductionGate};
use crate::cs::Variable;
use crate::{cs::traits::cs::ConstraintSystem, field::SmallField};

pub fn decompose_into_limbs<F: SmallField, CS: ConstraintSystem<F>, const N: usize>(
    cs: &mut CS,
    limb_size: F,
    input: Variable,
) -> [Variable; N] {
    if cs.gate_is_allowed::<ReductionGate<F, N>>() {
        ReductionGate::<F, N>::decompose_into_limbs(cs, limb_size, input)
    } else if cs.gate_is_allowed::<ReductionByPowersGate<F, N>>() {
        ReductionByPowersGate::<F, N>::decompose_into_limbs(cs, limb_size, input)
    } else {
        unimplemented!()
    }
}

pub fn decompose_into_limbs_limited<F: SmallField, CS: ConstraintSystem<F>, const N: usize>(
    cs: &mut CS,
    limb_size: F,
    input: Variable,
    limit: usize,
    zero_var: Variable,
) -> [Variable; N] {
    if cs.gate_is_allowed::<ReductionGate<F, N>>() {
        ReductionGate::<F, N>::decompose_into_limbs_limited(cs, limb_size, input, limit, zero_var)
    } else if cs.gate_is_allowed::<ReductionByPowersGate<F, N>>() {
        ReductionByPowersGate::<F, N>::decompose_into_limbs_limited(
            cs, limb_size, input, limit, zero_var,
        )
    } else {
        unimplemented!()
    }
}

pub fn reduce_terms<F: SmallField, CS: ConstraintSystem<F>, const N: usize>(
    cs: &mut CS,
    reduction_constant: F,
    terms: [Variable; N],
) -> Variable {
    if cs.gate_is_allowed::<ReductionGate<F, N>>() {
        let mut reduction_constants = [F::ZERO; N];
        reduction_constants[0] = F::ONE;
        let mut current = F::ONE;
        for dst in reduction_constants[1..].iter_mut() {
            current.mul_assign(&reduction_constant);
            *dst = current;
        }
        ReductionGate::<F, N>::reduce_terms(cs, reduction_constants, terms)
    } else if cs.gate_is_allowed::<ReductionByPowersGate<F, N>>() {
        ReductionByPowersGate::<F, N>::reduce_terms(cs, reduction_constant, terms)
    } else {
        unimplemented!()
    }
}
