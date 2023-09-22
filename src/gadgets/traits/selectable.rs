use std::mem::MaybeUninit;

use crate::cs::gates::{ConstantAllocatableCS, ParallelSelectionGate};
use crate::cs::traits::cs::ConstraintSystem;
use crate::field::SmallField;
use crate::gadgets::boolean::Boolean;

pub trait Selectable<F: SmallField>: Sized {
    /// Selects `a` if `flag` is `true`, and `b` otherwise
    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self;

    const SUPPORTS_PARALLEL_SELECT: bool = false;

    /// Selects `a` if `flag` is `true`, and `b` otherwise
    fn parallel_select<CS: ConstraintSystem<F>, const N: usize>(
        _cs: &mut CS,
        _flag: Boolean<F>,
        _a: &[Self; N],
        _b: &[Self; N],
    ) -> [Self; N] {
        unimplemented!(
            "not implemented by default for type {}",
            std::any::type_name::<Self>()
        );
    }

    fn select_from_chain<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        baseline: &Self,
        mut candidates: impl Iterator<Item = (Boolean<F>, Self)>,
        mut length: usize,
    ) -> Self {
        // default implementation performs sequential select,
        // that is ok for some types (large types)
        assert!(length > 0);

        let (flag, candidate) = candidates.next().expect("is some");
        length -= 1;

        let mut tmp = Self::conditionally_select(cs, flag, &candidate, baseline);

        for (flag, candidate) in candidates {
            tmp = Self::conditionally_select(cs, flag, &candidate, &tmp);
            length -= 1;
        }

        assert_eq!(length, 0);

        tmp
    }
}

impl<F: SmallField> Selectable<F> for () {
    fn conditionally_select<CS: ConstraintSystem<F>>(
        _cs: &mut CS,
        _flag: Boolean<F>,
        _a: &Self,
        _b: &Self,
    ) -> Self {
    }
}

impl<F: SmallField, T: Sized> Selectable<F> for std::marker::PhantomData<T> {
    fn conditionally_select<CS: ConstraintSystem<F>>(
        _cs: &mut CS,
        _flag: Boolean<F>,
        _a: &Self,
        _b: &Self,
    ) -> Self {
        std::marker::PhantomData
    }
}

impl<F: SmallField, T: Selectable<F>, const N: usize> Selectable<F> for [T; N] {
    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self {
        // well, not the prettiest, but fine

        if T::SUPPORTS_PARALLEL_SELECT {
            // happy path for not too deeply recursive types
            return T::parallel_select::<CS, N>(cs, flag, a, b);
        }

        let mut buffer: [MaybeUninit<T>; N] = std::array::from_fn(|_| MaybeUninit::uninit());
        for ((a, b), dst) in a.iter().zip(b.iter()).zip(buffer.iter_mut()) {
            let t = Selectable::conditionally_select(cs, flag, a, b);
            dst.write(t);
        }

        unsafe { buffer.map(|el| el.assume_init()) }
    }
}

// we can select by boolean masks
pub trait MultiSelectable<F: SmallField>: Selectable<F> {}

use crate::cs::Variable;

pub fn parallel_select_variables<'a, F: SmallField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    flag: Boolean<F>,
    it: impl Iterator<Item = ((Variable, Variable), &'a mut Variable)>,
) {
    if cs.gate_is_allowed::<ParallelSelectionGate<4>>() {
        let mut it = it.array_chunks::<4>();
        for chunk in &mut it {
            let a = [chunk[0].0 .0, chunk[1].0 .0, chunk[2].0 .0, chunk[3].0 .0];
            let b = [chunk[0].0 .1, chunk[1].0 .1, chunk[2].0 .1, chunk[3].0 .1];
            let result = ParallelSelectionGate::select(cs, &a, &b, flag.variable);
            *chunk[0].1 = result[0];
            *chunk[1].1 = result[1];
            *chunk[2].1 = result[2];
            *chunk[3].1 = result[3];
        }

        if let Some(rest) = it.into_remainder() {
            let zero = cs.allocate_constant(F::ZERO);
            let num_items = rest.len();

            let mut a_buffer = [zero; 4];
            let mut b_buffer = [zero; 4];
            let mut result_buffer: [MaybeUninit<&'a mut Variable>; 4] =
                std::array::from_fn(|_| MaybeUninit::uninit());

            for (idx, ((a, b), dst)) in rest.into_iter().enumerate() {
                a_buffer[idx] = a;
                b_buffer[idx] = b;
                result_buffer[idx].write(dst);
            }

            let result = ParallelSelectionGate::select(cs, &a_buffer, &b_buffer, flag.variable);
            for (dst, res) in result_buffer
                .into_iter()
                .zip(result.into_iter())
                .take(num_items)
            {
                let dst = unsafe { dst.assume_init() };
                *dst = res;
            }
        }
    } else {
        unimplemented!()
    }
}
