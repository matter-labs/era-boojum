use crate::cs::{Place, Variable};
use crate::dag::WitnessSource;
use crate::field::SmallField;
use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

// we need some "get value" thing, kind of the callback, and this will be a property of the gadget itself,
// and will use some lowest level primitive from the CS

// NOTE: witness is not "serde" by default because it still doesn't work nicely with const generics

// #[derive(Derivative, serde::Serialize, serde::Deserialize)]
// #[derivative(Clone, Debug, Hash)]
// #[serde(bound(serialize = "T: serde::Serialize"))]
// #[serde(bound(deserialize = "T: serde::de::DeserializeOwned"))]
// pub enum Witness<T: 'static + Send + Sync + Clone + std::fmt::Debug> {
//     Placeholder,
//     Value(T)
// }

// impl<T: 'static + Send + Sync + Clone + std::fmt::Debug> Witness<T> {
//     #[inline(always)]
//     pub const fn placeholder() -> Self {
//         Self::Placeholder
//     }

//     #[inline(always)]
//     pub const fn from_value(value: T) -> Self {
//         Self::Value(value)
//     }

//     #[inline(always)]
//     pub const fn get_value(self) -> Option<T> where T:  std::marker::Destruct {
//         match self {
//             Witness::Placeholder => None,
//             Witness::Value(value) => Some(value)
//         }
//     }

//     #[inline(always)]
//     pub const fn is_placeholder(&self) -> bool {
//         match self {
//             Witness::Placeholder => true,
//             Witness::Value(..) => false,
//         }
//     }
// }

pub enum WitnessValue<
    F: SmallField,
    T: 'static + Clone + Send + Sync + std::fmt::Debug,
    const N: usize,
    S: WitnessSource<F>,
    FN: FnOnce([F; N]) -> T + 'static + Send + Sync,
> {
    Placeholder,
    Ready(T),
    Waiting {
        barrier: Arc<AtomicBool>,
        witness_source: Arc<S>,
        sources: [Place; N],
        cast_fn: FN,
        _marker: std::marker::PhantomData<F>,
    },
}

impl<
        F: SmallField,
        T: 'static + Clone + Send + Sync + std::fmt::Debug,
        const N: usize,
        S: WitnessSource<F>,
        FN: FnOnce([F; N]) -> T + 'static + Send + Sync,
    > WitnessValue<F, T, N, S, FN>
{
    const NUM_SPINS: usize = 16;
    const SLEEP_DURATION: std::time::Duration = std::time::Duration::from_millis(1);

    pub fn wait(self) -> Option<T> {
        match self {
            Self::Placeholder => None,
            Self::Ready(value) => Some(value.clone()),
            Self::Waiting {
                barrier,
                witness_source,
                sources,
                cast_fn,
                ..
            } => {
                let mut ready = false;
                for _ in 0..Self::NUM_SPINS {
                    if barrier.load(Ordering::Relaxed) == false {
                        std::hint::spin_loop();
                    } else {
                        ready = true;
                        break;
                    }
                }

                while !ready {
                    std::thread::sleep(Self::SLEEP_DURATION);
                    ready = barrier.load(Ordering::Relaxed);
                }

                let mut witnesses = [F::ZERO; N];
                for (var, dst) in sources.iter().zip(witnesses.iter_mut()) {
                    *dst = witness_source.get_value_unchecked(*var);
                }

                let as_final_type = (cast_fn)(witnesses);

                Some(as_final_type)
            }
        }
    }
}

use crate::cs::traits::cs::ConstraintSystem;
use crate::gadgets::traits::allocatable::CSAllocatable;

pub trait CSWitnessable<F: SmallField, const N: usize>: CSAllocatable<F> {
    type ConversionFunction: FnOnce([F; N]) -> Self::Witness + Send + Sync + Default;

    fn witness_from_set_of_values(values: [F; N]) -> Self::Witness;

    fn as_variables_set(&self) -> [Variable; N];

    fn get_witness<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
    ) -> WitnessValue<F, Self::Witness, N, CS::WitnessSource, Self::ConversionFunction> {
        use crate::config::*;
        if <CS::Config as CSConfig>::WitnessConfig::EVALUATE_WITNESS == false {
            return WitnessValue::Placeholder;
        }

        let cs_witness = cs.get_value_for_multiple(Place::from_variables(self.as_variables_set()));

        use crate::dag::CSWitnessValues;

        match cs_witness {
            CSWitnessValues::Placeholder => WitnessValue::Placeholder,
            CSWitnessValues::Ready(values) => {
                let as_witness = Self::witness_from_set_of_values(values);
                WitnessValue::Ready(as_witness)
            }
            CSWitnessValues::Waiting {
                barrier,
                witness_source,
                sources,
                _marker,
            } => WitnessValue::Waiting {
                barrier,
                witness_source,
                sources,
                cast_fn: Self::ConversionFunction::default(),
                _marker: std::marker::PhantomData,
            },
        }
    }
}

pub trait WitnessHookable<F: SmallField>: CSAllocatable<F> {
    fn witness_hook<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
    ) -> Box<dyn FnOnce() -> Option<Self::Witness> + 'static>;
}

impl<F: SmallField> WitnessHookable<F> for () {
    fn witness_hook<CS: ConstraintSystem<F>>(
        &self,
        _cs: &CS,
    ) -> Box<dyn FnOnce() -> Option<Self::Witness> + 'static> {
        Box::new(|| Some(()))
    }
}

// But we can still extend for case of arrays
impl<F: SmallField, const N: usize, T: WitnessHookable<F>> WitnessHookable<F> for [T; N] {
    fn witness_hook<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
    ) -> Box<dyn FnOnce() -> Option<Self::Witness> + 'static> {
        let hooks: [Box<dyn FnOnce() -> std::option::Option<<T as CSAllocatable<F>>::Witness>>; N] =
            std::array::from_fn(|idx| self[idx].witness_hook(cs));

        let hook_fn = move || {
            let mut results: [MaybeUninit<T::Witness>; N] =
                std::array::from_fn(|_| MaybeUninit::uninit());
            for (dst, hook) in results.iter_mut().zip(hooks.into_iter()) {
                let value = (hook)()?;
                dst.write(value);
            }

            // all are init
            let results = unsafe { results.map(|el| el.assume_init()) };

            Some(results)
        };

        Box::new(hook_fn)
    }
}
