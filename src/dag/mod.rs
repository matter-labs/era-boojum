use self::resolvers::mt::sorters::sorter_live::LiveResolverSorter;
use std::fmt::Debug;
use std::hint::spin_loop;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use crate::config::CSResolverConfig;
use crate::cs::traits::cs::{CSWitnessSource, DstBuffer};
use crate::cs::Place;
use crate::field::SmallField;

mod awaiters;
mod guide;
mod primitives;
mod resolver_box;
pub mod resolvers;

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

#[derive(Clone, Copy, Debug)]
pub struct CircuitResolverOpts {
    pub max_variables: usize,
    pub desired_parallelism: u32,
}

impl CircuitResolverOpts {
    pub fn new(max_variables: usize) -> Self {
        Self {
            max_variables,
            desired_parallelism: 1 << 12,
        }
    }
}

impl From<usize> for CircuitResolverOpts {
    fn from(value: usize) -> Self {
        Self {
            max_variables: value,
            desired_parallelism: 1 << 12,
        }
    }
}

pub trait TrackId:
    From<u64> + Into<u64> + Into<usize> + Eq + Ord + Debug + Default + Clone + Copy
{
}

pub trait CircuitResolver<F: SmallField, Cfg: CSResolverConfig>:
    WitnessSource<F> + WitnessSourceAwaitable<F> + CSWitnessSource<F> + Send + Sync
{
    type Arg;

    fn new(args: Self::Arg) -> Self;
    fn set_value(&mut self, key: Place, value: F);
    fn add_resolution<Fn>(&mut self, inputs: &[Place], outputs: &[Place], f: Fn)
    where
        Fn: FnOnce(&[F], &mut DstBuffer<'_, '_, F>) + Send + Sync;
    fn wait_till_resolved(&mut self);
    fn clear(&mut self);
}

pub type NullCircuitResolver<F, CFG> = resolvers::NullCircuitResolver<F, CFG>;

pub type StCircuitResolver<F, CFG> = resolvers::StCircuitResolver<F, CFG>;
pub type MtCircuitResolver<F, CFG> =
    resolvers::MtCircuitResolver<F, LiveResolverSorter<F, CFG>, CFG>;

pub type DefaultCircuitResolver<F, CFG> = MtCircuitResolver<F, CFG>;
