use std::hint::spin_loop;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use crate::field::SmallField;

mod awaiters;
mod guide;
mod registrar;
pub(crate) mod resolution_window;
pub(crate) mod resolver;
mod resolver_box;

pub trait TrivialWitnessCastable<F: SmallField, const N: usize>:
    'static + Clone + std::fmt::Debug + Send + Sync
{
    fn cast_from_field_elements(parts: [F; N]) -> Self;
    fn cast_into_field_elements(self) -> [F; N];
}

pub enum CSWitnessValues<F: SmallField, const N: usize, S: WitnessSource<F>> {
    Placeholder,
    Ready([F; N]),
    Waiting {
        barrier: Arc<AtomicBool>,
        witness_source: Arc<S>,
        sources: [Place; N],
        _marker: std::marker::PhantomData<F>,
    },
}

impl<F: SmallField, const N: usize, S: WitnessSource<F>> CSWitnessValues<F, N, S> {
    const NUM_SPINS: usize = 16;
    const SLEEP_DURATION: std::time::Duration = std::time::Duration::from_millis(10);

    // TODO: do we still need this with the new witness source wait interface?

    pub fn wait(&mut self) -> Option<[F; N]> {
        match self {
            Self::Placeholder => None,
            Self::Ready(value) => Some(*value),
            Self::Waiting {
                barrier,
                witness_source,
                sources,
                ..
            } => {
                let mut ready = false;
                for _ in 0..Self::NUM_SPINS {
                    if barrier.load(Ordering::Relaxed) == false {
                        spin_loop();
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

                *self = CSWitnessValues::Ready(witnesses);

                self.wait()
            }
        }
    }
}

use crate::cs::Place;

// we use Arc and interior mutability, so we want Send + Sync just in case
pub trait WitnessSource<F: SmallField>: 'static + Send + Sync {
    const PRODUCES_VALUES: bool;

    fn try_get_value(&self, variable: Place) -> Option<F>;
    fn get_value_unchecked(&self, variable: Place) -> F;
}

pub trait WitnessSourceAwaitable<F: SmallField>: WitnessSource<F> {
    type Awaiter<'a>: Awaiter<'a>;

    fn get_awaiter<const N: usize>(&mut self, vars: [Place; N]) -> Self::Awaiter<'_>;
}

pub trait Awaiter<'a> {
    fn wait(&self);
}
