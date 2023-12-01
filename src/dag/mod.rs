use std::cell::UnsafeCell;
use std::fmt::Debug;
use std::hint::spin_loop;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;

use bincode::Config;

use crate::config::CSResolverConfig;
use crate::cs::traits::cs::DstBuffer;
use crate::field::SmallField;

mod awaiters;
mod guide;
mod registrar;
pub(crate) mod resolution_window;
pub(crate) mod resolver;
mod resolver_box;
pub(crate) mod sorter_runtime;
pub(crate) mod sorter_playback;

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
use crate::utils::PipeOp;

use self::guide::{GuideOrder, OrderInfo, RegistrationNum};
use self::resolver::{CircuitResolverOpts, ResolverIx, ResolverCommonData};
use self::resolver_box::ResolverBox;
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

pub trait ResolutionRecordStorage {
    type Id;
    fn store(&mut self, id: Self::Id, record: &ResolutionRecord);
    fn get(&self, id: Self::Id) -> Rc<ResolutionRecord>;
}

#[derive(Default, Clone)]
pub struct ResolutionRecordItem { 
    added_at: RegistrationNum,
    accepted_at: RegistrationNum,
    /// The size of the order list when this registration was processed.
    order_len: usize,
    order_ix: resolver::OrderIx,
    parallelism: u16,
}

#[derive(Clone)]
pub struct ResolutionRecord {
    pub items: Vec<ResolutionRecordItem>,
    pub registrations_count: usize,
    pub values_count: usize
}

impl ResolutionRecord {
    fn new(registrations_count: usize, values_count: usize, size: usize) -> Self {
        Self {
            registrations_count,
            values_count,
            items:
                Vec::with_capacity(size)
                .op(|x| x.resize_with(size, ResolutionRecordItem::default))
        }
    }
}

pub trait TrackId: From<u64> + Into<u64> + Into<usize> + Eq + Ord + Debug + Default + Clone + Copy {}

pub trait ResolverSorter<F: SmallField>: Sized
{
    type Arg;
    type Config: resolution_window::RWConfig<Self::TrackId> + 'static;
    type TrackId: TrackId + 'static;
    

    fn new(opts: Self::Arg, debug_track: &Vec<Place>) -> (Self, Arc<ResolverCommonData<F, Self::TrackId>>);
    fn set_value(&mut self, key: Place, value: F);
    fn add_resolution<Fn>(&mut self, inputs: &[Place], outputs: &[Place], f: Fn)
    where
        Fn: FnOnce(&[F], &mut DstBuffer<'_, '_, F>) + Send + Sync;

    unsafe fn internalize(
        &mut self, 
        resolver_ix: ResolverIx,
        inputs: &[Place], 
        outputs: &[Place],
        added_at: RegistrationNum);
    fn internalize_one(
        &mut self,
        resolver_ix: ResolverIx,
        inputs: &[Place],
        outputs: &[Place],
        added_at: RegistrationNum
    ) -> Vec<ResolverIx>;

    fn flush(&mut self);
    fn final_flush(&mut self);

    fn retrieve_sequence(&mut self) -> &ResolutionRecord;
}
