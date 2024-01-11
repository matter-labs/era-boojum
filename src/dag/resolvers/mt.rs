use std::{sync::{Arc, atomic::{AtomicIsize, AtomicBool, fence}}, thread::JoinHandle, marker::PhantomData, cell::Cell, any::Any, panic::resume_unwind};

use crate::{field::SmallField, dag::{ResolverSortingMode, resolver::{ResolverCommonData}, CircuitResolver, resolution_window::ResolutionWindow, ResolutionRecord, WitnessSource, WitnessSourceAwaitable, awaiters}, config::CSResolverConfig, cs::{Place, traits::cs::{DstBuffer, CSWitnessSource}}, log, utils::{PipeOp, UnsafeCellEx as _}};

pub(crate) const PARANOIA: bool = false;

/// Used to send notifications and data between the resolver, resolution window
/// and the awaiters.
pub struct ResolverComms {
    pub exec_order_buffer_hint: AtomicIsize,
    pub registration_complete: AtomicBool,
    pub rw_panicked: AtomicBool,
    pub rw_panic: Cell<Option<Box<dyn Any + Send + 'static>>>,
}

#[derive(Debug)]
struct Stats {
    values_added: u64,
    witnesses_added: u64,
    registrations_added: u64,
    started_at: std::time::Instant,
    registration_time: std::time::Duration,
    total_resolution_time: std::time::Duration,
}

impl Stats {
    fn new() -> Self {
        Self {
            values_added: 0,
            witnesses_added: 0,
            registrations_added: 0,
            started_at: std::time::Instant::now(),
            registration_time: std::time::Duration::from_secs(0),
            total_resolution_time: std::time::Duration::from_secs(0),
        }
    }
}

/// The data is tracked in the following manner:
///
/// `key ---> [values.variables/witnesses] ---> [resolvers_order] ---> [resolvers]`
///
/// Given a key, one can find a value and the metadata in `variables/witnesses`.
/// The metadata contains the resolver order index which will produce a value for that item.
/// The order index contains the index at which the resolver data is placed.
///    Those indicies are not monotonic and act akin to pointers, and thus are
///    Unsafe to work with.

pub struct MtCircuitResolver<V: SmallField, RS: ResolverSortingMode<V>, CFG: CSResolverConfig> {
    // registrar: Registrar,

    sorter: RS,

    pub(crate) common: Arc<ResolverCommonData<V, RS::TrackId>>,
    // pub(crate) options: CircuitResolverOpts,
    
    comms: Arc<ResolverComms>,
    // pub(crate) guide: BufferGuide<ResolverIx, Cfg>,

    resolution_window_handle: Option<JoinHandle<()>>,

    stats: Stats,
    call_count: u32,
    debug_track: Vec<Place>,
    phantom: PhantomData<CFG>,
}

unsafe impl<V, RS, CFG> Send for MtCircuitResolver<V, RS, CFG> 
where 
    V: SmallField,
    RS: ResolverSortingMode<V>,
    CFG: CSResolverConfig {}

unsafe impl<V, RS, CFG> Sync for MtCircuitResolver<V, RS, CFG> 
where 
    V: SmallField,
    RS: ResolverSortingMode<V>,
    CFG: CSResolverConfig {}

impl< F, RS, CFG> CircuitResolver<F, CFG> for MtCircuitResolver<F, RS, CFG> 
where 
    F: SmallField,
    RS: ResolverSortingMode<F> + 'static,
    CFG: CSResolverConfig 
{
    type Arg = RS::Arg;

    fn new(args: Self::Arg) -> Self {
        Self::new(args)
    }

    fn set_value(&mut self, key: Place, value: F) {
        self.set_value(key, value)
    }

    fn add_resolution<Fn>(&mut self, inputs: &[Place], outputs: &[Place], f: Fn)
    where
        Fn: FnOnce(&[F], &mut DstBuffer<'_, '_, F>) + Send + Sync {
        self.add_resolution(inputs, outputs, f)
    }

    fn wait_till_resolved(&mut self) {
        self.wait_till_resolved()
    }

    fn clear(&mut self) {
        self.clear()
    }
}

impl<V: SmallField, RS: ResolverSortingMode<V>, CFG: CSResolverConfig> MtCircuitResolver<V, RS, CFG> {
    pub fn new(opts: RS::Arg) -> Self {
        let threads =
            match 
            
                std::env::var("BOOJUM_CR_THREADS")
                .map_err(|_| "")
                .and_then(|x| x.parse().map_err(|_| ""))
            {
                Ok(x) => x,
                Err(_) => 3
            };

        let debug_track = vec![];

        if cfg!(cr_paranoia_mode) || PARANOIA {
            log!("Contains tracked keys {:?} ", debug_track);
        }

        let comms = ResolverComms {
            exec_order_buffer_hint: AtomicIsize::new(0),
            registration_complete: AtomicBool::new(false),
            rw_panicked: AtomicBool::new(false),
            rw_panic: Cell::new(None),
        }.to(Arc::new);

        let (sorter, common) = RS::new(opts, comms.clone(), &debug_track);

        Self {
            // options: opts,
            call_count: 0,
            sorter,
            // guide: BufferGuide::new(opts.desired_parallelism),
            // registrar: Registrar::new(),
            comms: comms.clone(),

            resolution_window_handle: ResolutionWindow::<V, RS::TrackId, RS::Config>::run(
                comms.clone(),
                common.clone(),
                &debug_track,
                threads,
            )
            .to(Some),

            common,
            stats: Stats::new(),
            debug_track,
            phantom: PhantomData,
        }
    }

    pub fn set_value(&mut self, key: Place, value: V) {
        self.sorter.set_value(key, value)
    }

    pub fn add_resolution<F>(&mut self, inputs: &[Place], outputs: &[Place], f: F)
    where
        F: FnOnce(&[V], &mut DstBuffer<'_, '_, V>) + Send + Sync,
    {
        self.sorter.add_resolution(inputs, outputs, f)
    }

    pub fn wait_till_resolved(&mut self) {
        self.wait_till_resolved_impl(true);
    }

    pub fn wait_till_resolved_impl(&mut self, report: bool) {
        if self
            .comms
            .registration_complete
            .load(std::sync::atomic::Ordering::Relaxed)
        {
            return;
        }

        self.sorter.final_flush();

        self.stats.registration_time = self.stats.started_at.elapsed();

        self
            .comms
            .registration_complete
            .store(true, std::sync::atomic::Ordering::Relaxed);

        self.resolution_window_handle
            .take()
            .expect("Attempting to join resolution window handler for second time.")
            .join()
            .unwrap(); // Just propagate panics. Those are unhandled, unlike the ones from `rw_panic`.

        self.stats.total_resolution_time = self.stats.started_at.elapsed();

        // Propage panic from the resolution window handler.
        if self
            .comms
            .rw_panicked
            .load(std::sync::atomic::Ordering::Relaxed)
        {
            if let Some(e) = self.comms.rw_panic.take() {
                resume_unwind(e);
            } else {
                log!("Resolution window panicked, but no panic payload stored.");
                return;
            }
        }

        match report {
            true => {
                log!("CR stats {:#?}", self.stats);
            }
            false if cfg!(test) || cfg!(debug_assertions) => {
                print!(" resolution time {:?}...", self.stats.total_resolution_time);
            }
            _ => {}
        }
        
        self.sorter.write_sequence();

        if cfg!(cr_paranoia_mode) || PARANOIA {
            log!("CR {:?}", unsafe {
                self.common.awaiters_broker.stats.u_deref()
            });
        }
    }

    pub fn retrieve_sequence(&mut self) -> &ResolutionRecord {
        assert!(self.comms.registration_complete.load(std::sync::atomic::Ordering::Relaxed));
        self.sorter.retrieve_sequence()
    }

    pub fn clear(&mut self) {
        // TODO: implement
    }
}

impl<V: SmallField, RS: ResolverSortingMode<V> + 'static, CFG: CSResolverConfig> 
    WitnessSource<V> for MtCircuitResolver<V, RS, CFG> {
    const PRODUCES_VALUES: bool = true;

    fn try_get_value(&self, variable: Place) -> Option<V> {

        let (v, md) = unsafe { self.common.values.u_deref().get_item_ref(variable) };

        match md.is_resolved() {
            true => {
                fence(std::sync::atomic::Ordering::Acquire);
                Some(*v)
            }
            false => None,
        }
    }

    fn get_value_unchecked(&self, variable: Place) -> V {
        // TODO: Should this fn be marked as unsafe?

        // Safety: Dereferencing as & in &self context.
        let (r, md) = unsafe { self.common.values.u_deref().get_item_ref(variable) };
        // log!("gvu: {:0>8} -> {}", variable.0, r);

        debug_assert!(
            md.is_resolved(),
            "Attempted to get value of unresolved variable."
        );

        *r
    }
}

impl<V: SmallField, RS: ResolverSortingMode<V> + 'static, CFG: CSResolverConfig> 
    CSWitnessSource<V> for MtCircuitResolver<V, RS, CFG> {}

impl<V: SmallField, RS: ResolverSortingMode<V> + 'static, CFG: CSResolverConfig> 
    WitnessSourceAwaitable<V> for MtCircuitResolver<V, RS, CFG> {
    type Awaiter<'a> = awaiters::Awaiter<'a, RS::TrackId>;

    fn get_awaiter<const N: usize>(&mut self, vars: [Place; N]) -> awaiters::Awaiter<RS::TrackId> {
        // Safety: We're only getting the metadata address for an item, which is
        // immutable and the max_tracked value, which isn't but read only once
        // for the duration of the reference.
        let values = unsafe { self.common.values.u_deref() };

        if values.max_tracked < vars.iter().map(|x| x.as_any_index()).max().unwrap() as i64 {
            panic!("The awaiter will never resolve since the awaited variable can't be computed based on currently available registrations. You have holes!!!");
        }

        // We're picking the item that will be resolved last among other inputs.
        let md = vars
            .into_iter()
            .map(|x| &values.get_item_ref(x).1)
            .max_by_key(|x| x.tracker)
            .unwrap();

        let r = awaiters::AwaitersBroker::register(
            &self.common.awaiters_broker,
            &self.comms,
            md,
        );

        self.sorter.flush();

        r
    }
}

// impl Drop for CircuitResolver

impl<V: SmallField, RS: ResolverSortingMode<V>, CFG: CSResolverConfig> 
    Drop for MtCircuitResolver<V, RS, CFG> {
    fn drop(&mut self) {
        if cfg!(test) || cfg!(debug_assertions) {
            print!("Starting drop of CircuitResolver (If this hangs, it's bad)...");
        }
        self.wait_till_resolved_impl(false);

        if cfg!(test) || cfg!(debug_assertions) {
            log!("ok");
        }
    }
}
