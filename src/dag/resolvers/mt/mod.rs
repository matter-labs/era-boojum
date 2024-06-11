mod registrar;
mod resolution_window;
pub mod sorters;

use std::{
    any::Any,
    cell::{Cell, UnsafeCell},
    marker::PhantomData,
    panic::resume_unwind,
    sync::{
        atomic::{fence, AtomicBool, AtomicIsize},
        Arc, Mutex,
    },
    thread::JoinHandle,
};

use crate::{
    config::CSResolverConfig,
    cs::{
        traits::cs::{CSWitnessSource, DstBuffer},
        Place,
    },
    dag::{
        awaiters::{self, AwaitersBroker},
        primitives::{ExecOrder, Values},
        resolver_box::ResolverBox,
        CircuitResolver, WitnessSource, WitnessSourceAwaitable,
    },
    field::SmallField,
    log,
    utils::{PipeOp as _, UnsafeCellEx},
};

use self::{
    resolution_window::ResolutionWindow,
    sorters::{ResolutionRecord, ResolverSortingMode},
};

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

/// Shared between the resolver, awaiters and the resolution window.
pub struct ResolverCommonData<V, T: Default> {
    // The following two are meant to have an asynchronized access. The access
    // correctness is provided by the `exec_order` mutex. Once an item is
    // added to the `exec_order`, it's guaranteed that the corresponding
    // values are present in resolvers and values.
    pub resolvers: UnsafeCell<ResolverBox<V>>,
    pub values: UnsafeCell<Values<V, T>>,

    /// Resolutions happen in this order. Holds index of the resolver in `resolver`.
    /// This index follows pointer semantics and is unsafe to operate on.
    /// The order can have gaps, so it's size should be somewhat larger than the total
    /// amount of resolvers.
    pub exec_order: Mutex<ExecOrder>,
    pub awaiters_broker: AwaitersBroker<T>,
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
    sorter: RS,

    pub(crate) common: Arc<ResolverCommonData<V, RS::TrackId>>,
    comms: Arc<ResolverComms>,
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
    CFG: CSResolverConfig,
{
}

unsafe impl<V, RS, CFG> Sync for MtCircuitResolver<V, RS, CFG>
where
    V: SmallField,
    RS: ResolverSortingMode<V>,
    CFG: CSResolverConfig,
{
}

impl<F, RS, CFG> CircuitResolver<F, CFG> for MtCircuitResolver<F, RS, CFG>
where
    F: SmallField,
    RS: ResolverSortingMode<F> + 'static,
    CFG: CSResolverConfig,
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
        Fn: FnOnce(&[F], &mut DstBuffer<'_, '_, F>) + Send + Sync,
    {
        self.add_resolution(inputs, outputs, f)
    }

    fn wait_till_resolved(&mut self) {
        self.wait_till_resolved()
    }

    fn clear(&mut self) {
        self.clear()
    }
}

impl<V: SmallField, RS: ResolverSortingMode<V>, CFG: CSResolverConfig>
    MtCircuitResolver<V, RS, CFG>
{
    pub fn new(opts: RS::Arg) -> Self {
        let threads = std::env::var("BOOJUM_CR_THREADS")
            .map_err(|_| "")
            .and_then(|x| x.parse().map_err(|_| ""))
            .unwrap_or(3);

        let debug_track = vec![];

        if cfg!(feature = "cr_paranoia_mode") || PARANOIA {
            log!("Contains tracked keys {:?} ", debug_track);
        }

        let comms = ResolverComms {
            exec_order_buffer_hint: AtomicIsize::new(0),
            registration_complete: AtomicBool::new(false),
            rw_panicked: AtomicBool::new(false),
            rw_panic: Cell::new(None),
        }
        .to(Arc::new);

        let (sorter, common) = RS::new(opts, comms.clone(), &debug_track);

        Self {
            call_count: 0,
            sorter,
            comms: comms.clone(),

            resolution_window_handle: ResolutionWindow::<V, RS::TrackId, RS::Config>::run(
                comms,
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

        self.comms
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

        if cfg!(feature = "cr_paranoia_mode") || PARANOIA {
            log!("CR {:?}", unsafe {
                self.common.awaiters_broker.stats.u_deref()
            });
        }
    }

    pub fn retrieve_sequence(&mut self) -> &ResolutionRecord {
        assert!(self
            .comms
            .registration_complete
            .load(std::sync::atomic::Ordering::Relaxed));
        self.sorter.retrieve_sequence()
    }

    pub fn clear(&mut self) {
        // TODO: implement
    }
}

impl<V: SmallField, RS: ResolverSortingMode<V> + 'static, CFG: CSResolverConfig> WitnessSource<V>
    for MtCircuitResolver<V, RS, CFG>
{
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

impl<V: SmallField, RS: ResolverSortingMode<V> + 'static, CFG: CSResolverConfig> CSWitnessSource<V>
    for MtCircuitResolver<V, RS, CFG>
{
}

impl<V: SmallField, RS: ResolverSortingMode<V> + 'static, CFG: CSResolverConfig>
    WitnessSourceAwaitable<V> for MtCircuitResolver<V, RS, CFG>
{
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

        let r = awaiters::AwaitersBroker::register(&self.common.awaiters_broker, &self.comms, md);

        self.sorter.flush();

        r
    }
}

// impl Drop for CircuitResolver

impl<V: SmallField, RS: ResolverSortingMode<V>, CFG: CSResolverConfig> Drop
    for MtCircuitResolver<V, RS, CFG>
{
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

#[cfg(test)]
mod test {
    use std::collections::VecDeque;
    use std::hint::spin_loop;
    use std::rc::Rc;
    use std::sync::Mutex;

    use itertools::Itertools as _;

    use crate::config::Resolver;
    use crate::cs::traits::cs::DstBuffer;
    use crate::cs::Place;
    use crate::dag::resolvers::mt::sorters::sorter_live::*;
    use crate::dag::resolvers::mt::sorters::sorter_playback::PlaybackResolverSorter;
    use crate::dag::resolvers::mt::sorters::ResolverSortingMode;
    use crate::dag::resolvers::MtCircuitResolver;
    use crate::dag::{
        Awaiter, CircuitResolverOpts, WitnessSource as _, WitnessSourceAwaitable as _,
    };

    use crate::field::SmallField;
    use crate::log;
    use crate::utils::PipeOp as _;
    use crate::{
        config::DoPerformRuntimeAsserts,
        cs::Variable,
        field::{goldilocks::GoldilocksField, Field},
    };

    use super::sorters::{ResolutionRecordSource, ResolutionRecordWriter};
    use super::*;

    type F = GoldilocksField;
    type Cfg = Resolver<DoPerformRuntimeAsserts>;

    pub struct TestRecordStorage {
        record: std::rc::Rc<ResolutionRecord>,
    }

    impl ResolutionRecordWriter for TestRecordStorage {
        fn store(&mut self, _record: &ResolutionRecord) {}
    }

    impl ResolutionRecordSource for TestRecordStorage {
        fn get(&self) -> &ResolutionRecord {
            &self.record
        }
    }

    #[test]
    fn playground() {
        let mut v = VecDeque::with_capacity(4);

        v.push_front(1);
        v.push_front(2);
        v.push_front(3);
        v.push_front(4);

        log!("{:#?}", v.iter().take(5).collect_vec());

        assert_eq!(4, v.len());
    }

    fn tracks_values_populate<F: SmallField, RS: ResolverSortingMode<F>>(
        resolver: &mut MtCircuitResolver<F, RS, Cfg>,
        limit: u64,
    ) {
        for i in 0..limit {
            let a = Place::from_variable(Variable::from_variable_index(i));

            resolver.set_value(a, F::from_u64_with_reduction(i));
        }
    }

    #[test]
    fn tracks_values_record_mode() {
        let limit = 10;
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 10,
                desired_parallelism: 16,
            });

        log!("Storage is ready");

        tracks_values_populate(&mut storage, limit);

        for i in 0..limit {
            let a = Place::from_variable(Variable::from_variable_index(i));
            let v = storage.get_value_unchecked(a);

            assert_eq!(F::from_u64_with_reduction(i), v);
        }
    }

    #[test]
    fn tracks_values_playback_mode() {
        let limit = 10;
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 10,
                desired_parallelism: 16,
            });

        tracks_values_populate(&mut storage, limit);
        storage.wait_till_resolved();

        let rs = TestRecordStorage {
            record: Rc::new(storage.retrieve_sequence().clone()),
        };

        let mut storage =
            MtCircuitResolver::<F, PlaybackResolverSorter<F, TestRecordStorage, Cfg>, Cfg>::new(rs);

        tracks_values_populate(&mut storage, limit);

        for i in 0..limit {
            let a = Place::from_variable(Variable::from_variable_index(i));
            let v = storage.get_value_unchecked(a);

            assert_eq!(F::from_u64_with_reduction(i), v);
        }
    }

    fn resolves_populate<F: SmallField, RS: ResolverSortingMode<F>>(
        resolver: &mut MtCircuitResolver<F, RS, Cfg>,
    ) -> (Place, Place) {
        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var = Place::from_variable(Variable::from_variable_index(1));

        resolver.set_value(init_var, F::from_u64_with_reduction(123));

        resolver.add_resolution(&[init_var], &[dep_var], res_fn);

        (init_var, dep_var)
    }

    #[test]
    fn resolves_record_mode() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let (init_var, dep_var) = resolves_populate(&mut storage);

        storage.wait_till_resolved();

        assert_eq!(
            storage.get_value_unchecked(init_var),
            storage.get_value_unchecked(dep_var)
        );
    }

    #[test]
    fn resolves_empty() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });
        storage.wait_till_resolved();
    }

    #[test]
    fn resolves_playback_mode() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let (_, _) = resolves_populate(&mut storage);

        storage.wait_till_resolved();

        let rs = TestRecordStorage {
            record: Rc::new(storage.retrieve_sequence().clone()),
        };

        println!("\n----- Recording finished -----\n");

        let mut storage =
            MtCircuitResolver::<F, PlaybackResolverSorter<F, TestRecordStorage, Cfg>, Cfg>::new(rs);

        let (init_var, dep_var) = resolves_populate(&mut storage);

        storage.wait_till_resolved();

        assert_eq!(
            storage.get_value_unchecked(init_var),
            storage.get_value_unchecked(dep_var)
        );
    }

    fn resolves_siblings_populate<F: SmallField, RS: ResolverSortingMode<F>>(
        resolver: &mut MtCircuitResolver<F, RS, Cfg>,
    ) -> ((Place, Place), (Place, Place)) {
        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            let mut x = ins[0];

            outs.push(*x.double());
        };

        let init_var1 = Place::from_variable(Variable::from_variable_index(0));
        let dep_var1 = Place::from_variable(Variable::from_variable_index(1));
        let init_var2 = Place::from_variable(Variable::from_variable_index(2));
        let dep_var2 = Place::from_variable(Variable::from_variable_index(3));

        resolver.set_value(init_var1, F::from_u64_with_reduction(123));
        resolver.set_value(init_var2, F::from_u64_with_reduction(321));

        resolver.add_resolution(&[init_var1], &[dep_var1], res_fn);
        resolver.add_resolution(&[init_var2], &[dep_var2], res_fn);

        ((init_var1, dep_var1), (init_var2, dep_var2))
    }

    #[test]
    fn resolves_siblings_record_mode() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let ((init_var1, dep_var1), (init_var2, dep_var2)) =
            resolves_siblings_populate(&mut storage);

        storage.wait_till_resolved();

        assert_eq!(
            *storage.get_value_unchecked(init_var1).clone().double(),
            storage.get_value_unchecked(dep_var1)
        );
        assert_eq!(
            *storage.get_value_unchecked(init_var2).clone().double(),
            storage.get_value_unchecked(dep_var2)
        );
    }

    #[test]
    fn resolves_siblings_playback_mode() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        resolves_siblings_populate(&mut storage);

        storage.wait_till_resolved();

        let rs = TestRecordStorage {
            record: Rc::new(storage.retrieve_sequence().clone()),
        };

        let mut storage =
            MtCircuitResolver::<F, PlaybackResolverSorter<F, TestRecordStorage, Cfg>, Cfg>::new(rs);

        let ((init_var1, dep_var1), (init_var2, dep_var2)) =
            resolves_siblings_populate(&mut storage);

        storage.wait_till_resolved();

        assert_eq!(
            *storage.get_value_unchecked(init_var1).clone().double(),
            storage.get_value_unchecked(dep_var1)
        );
        assert_eq!(
            *storage.get_value_unchecked(init_var2).clone().double(),
            storage.get_value_unchecked(dep_var2)
        );
    }

    fn resolves_descendants_populate<F: SmallField, RS: ResolverSortingMode<F>>(
        resolver: &mut MtCircuitResolver<F, RS, Cfg>,
    ) -> Place {
        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            let mut x = ins[0];

            outs.push(*x.double());
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var1 = Place::from_variable(Variable::from_variable_index(1));
        let dep_var2 = Place::from_variable(Variable::from_variable_index(2));
        let dep_var3 = Place::from_variable(Variable::from_variable_index(3));

        resolver.set_value(init_var, F::from_u64_with_reduction(2));

        resolver.add_resolution(&[init_var], &[dep_var1], res_fn);
        resolver.add_resolution(&[dep_var1], &[dep_var2], res_fn);
        resolver.add_resolution(&[dep_var2], &[dep_var3], res_fn);

        dep_var3
    }

    #[test]
    fn resolves_descendants_record_mode() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 2,
            });

        let dep_var3 = resolves_descendants_populate(&mut storage);

        storage.wait_till_resolved();

        assert_eq!(
            F::from_u64_with_reduction(16),
            storage.get_value_unchecked(dep_var3)
        );
    }

    #[test]
    fn resolves_descendants_playback_mode() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 2,
            });

        resolves_descendants_populate(&mut storage);

        storage.wait_till_resolved();

        let rs = TestRecordStorage {
            record: Rc::new(storage.retrieve_sequence().clone()),
        };

        let mut storage =
            MtCircuitResolver::<F, PlaybackResolverSorter<F, TestRecordStorage, Cfg>, Cfg>::new(rs);

        let dep_var3 = resolves_descendants_populate(&mut storage);

        storage.wait_till_resolved();

        assert_eq!(
            F::from_u64_with_reduction(16),
            storage.get_value_unchecked(dep_var3)
        );
    }

    #[test]
    fn resolves_with_context() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var = Place::from_variable(Variable::from_variable_index(1));

        storage.set_value(init_var, F::from_u64_with_reduction(123));

        let ctx_var = F::from_u64_with_reduction(321);

        storage.add_resolution(
            &[init_var],
            &[dep_var],
            move |ins: &[F], outs: &mut DstBuffer<F>| {
                let mut result = ins[0];

                Field::add_assign(&mut result, &ctx_var);

                outs.push(result);
            },
        );

        storage.wait_till_resolved();

        assert_eq!(
            F::from_u64_with_reduction(444),
            storage.get_value_unchecked(dep_var)
        );
    }

    #[test]
    fn resolves_and_drops_context_after() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var = Place::from_variable(Variable::from_variable_index(1));

        storage.set_value(init_var, F::from_u64_with_reduction(123));

        struct DroppedContext {
            times_invoked: Arc<Mutex<u32>>,
            value: u64,
        }

        impl Drop for DroppedContext {
            fn drop(&mut self) {
                let mut g = self.times_invoked.lock().unwrap();
                *g += 1;
            }
        }

        let times_invoked = Mutex::new(0).to(Arc::new);

        let ctx = DroppedContext {
            times_invoked: times_invoked.clone(),
            value: 1,
        };

        storage.add_resolution(
            &[init_var],
            &[dep_var],
            move |ins: &[F], outs: &mut DstBuffer<F>| {
                let ctx = ctx;
                let mut r = ins[0];
                Field::add_assign(&mut r, &F::from_u64_with_reduction(ctx.value));
                outs.push(r);
            },
        );

        assert_eq!(0, *times_invoked.lock().unwrap());
        storage.wait_till_resolved();
        assert_eq!(1, *times_invoked.lock().unwrap());
    }

    #[test]
    fn awaiter_returns_for_resolved_value_record_mode() {
        let limit = 1 << 13;
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: limit * 5,
                desired_parallelism: 2048,
            });

        populate(&mut storage, limit);

        // Ensure 4'th element is done.
        while storage
            .try_get_value(Place::from_variable(Variable::from_variable_index(4)))
            .is_none()
        {
            spin_loop();
        }

        storage
            .get_awaiter([Place::from_variable(Variable::from_variable_index(4))])
            .wait();

        assert_eq!(
            F::from_u64_with_reduction(0x12),
            storage.get_value_unchecked(Place::from_variable(Variable::from_variable_index(4)))
        );
    }

    #[test]
    fn awaiter_returns_for_resolved_value_playback_mode() {
        awaiter_returns_for_resolved_value_playback_mode_impl(15, 2);
        awaiter_returns_for_resolved_value_playback_mode_impl(15, 20);
        awaiter_returns_for_resolved_value_playback_mode_impl(15, 2048);
    }

    fn awaiter_returns_for_resolved_value_playback_mode_impl(
        limit: usize,
        desired_parallelism: u32,
    ) {
        let limit = 1 << limit;
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: limit * 5,
                desired_parallelism,
            });

        populate(&mut storage, limit);

        storage.wait_till_resolved();

        let rs = TestRecordStorage {
            record: Rc::new(storage.retrieve_sequence().clone()),
        };

        let mut storage =
            MtCircuitResolver::<F, PlaybackResolverSorter<F, TestRecordStorage, Cfg>, Cfg>::new(rs);

        populate(&mut storage, limit);

        // Ensure 4'th element is done.
        while storage
            .try_get_value(Place::from_variable(Variable::from_variable_index(4)))
            .is_none()
        {
            spin_loop();
        }

        storage
            .get_awaiter([Place::from_variable(Variable::from_variable_index(4))])
            .wait();

        assert_eq!(
            F::from_u64_with_reduction(0x12),
            storage.get_value_unchecked(Place::from_variable(Variable::from_variable_index(4)))
        );
    }

    #[test]
    fn awaiter_returns_after_finish_record_mode() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var = Place::from_variable(Variable::from_variable_index(1));

        storage.set_value(init_var, F::from_u64_with_reduction(123));

        storage.add_resolution(&[init_var], &[dep_var], res_fn);

        storage.wait_till_resolved();

        storage.get_awaiter([dep_var]).wait();

        assert_eq!(
            F::from_u64_with_reduction(123),
            storage.get_value_unchecked(dep_var)
        );
    }

    #[test]
    fn awaiter_returns_after_finish_playback_mode() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var_1 = Place::from_variable(Variable::from_variable_index(1));
        let dep_var_2 = Place::from_variable(Variable::from_variable_index(2));

        storage.set_value(init_var, F::from_u64_with_reduction(123));

        storage.add_resolution(&[init_var], &[dep_var_1], res_fn);
        storage.add_resolution(&[dep_var_1], &[dep_var_2], res_fn);

        storage.wait_till_resolved();

        let rs = TestRecordStorage {
            record: Rc::new(storage.retrieve_sequence().clone()),
        };

        let mut storage =
            MtCircuitResolver::<F, PlaybackResolverSorter<F, TestRecordStorage, Cfg>, Cfg>::new(rs);

        storage.set_value(init_var, F::from_u64_with_reduction(123));

        storage.add_resolution(&[init_var], &[dep_var_1], res_fn);
        storage.add_resolution(&[dep_var_1], &[dep_var_2], res_fn);

        storage.wait_till_resolved();

        storage.get_awaiter([dep_var_2]).wait();

        assert_eq!(
            F::from_u64_with_reduction(123),
            storage.get_value_unchecked(dep_var_2)
        );
    }

    #[test]
    fn awaiter_returns_for_unexpropriated() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let awaited_var = Place::from_variable(Variable::from_variable_index(1));

        storage.set_value(init_var, F::from_u64_with_reduction(123));

        storage.add_resolution(&[init_var], &[awaited_var], res_fn);

        storage.get_awaiter([awaited_var]).wait();

        let v = storage.get_value_unchecked(awaited_var);

        assert_eq!(F::from_u64_with_reduction(123), v);
    }

    #[test]
    fn awaiter_blocks_before_resolved() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let mut notch = std::time::Instant::now();

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            std::thread::sleep(std::time::Duration::from_secs(1));
            notch = std::time::Instant::now();
            outs.push(ins[0]);
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var = Place::from_variable(Variable::from_variable_index(1));

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var], res_fn);

        storage.get_awaiter([dep_var]).wait();
        // We should arrive here at the same time or after the `notch` has been
        // set.
        let now = std::time::Instant::now();

        assert!(now >= notch);
    }

    #[test]
    fn resolution_after_awaiter_is_supported_record_mode() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var_1 = Place::from_variable(Variable::from_variable_index(1));
        let dep_var_2 = Place::from_variable(Variable::from_variable_index(2));

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var_1], res_fn);

        storage.get_awaiter([dep_var_1]).wait();

        storage.add_resolution(&[dep_var_1], &[dep_var_2], res_fn);

        storage.wait_till_resolved();

        let v = storage.get_value_unchecked(dep_var_2);

        assert_eq!(F::from_u64_with_reduction(123), v);
    }

    #[test]
    fn resolution_after_awaiter_is_supported_playback_mode() {
        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var_1 = Place::from_variable(Variable::from_variable_index(1));
        let dep_var_2 = Place::from_variable(Variable::from_variable_index(2));
        let dep_var_3 = Place::from_variable(Variable::from_variable_index(3));

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var_1], res_fn);
        storage.add_resolution(&[dep_var_1], &[dep_var_2], res_fn);
        storage.get_awaiter([dep_var_2]).wait();
        storage.add_resolution(&[dep_var_2], &[dep_var_3], res_fn);

        storage.wait_till_resolved();

        let rs = TestRecordStorage {
            record: Rc::new(storage.retrieve_sequence().clone()),
        };

        let mut storage =
            MtCircuitResolver::<F, PlaybackResolverSorter<F, TestRecordStorage, Cfg>, Cfg>::new(rs);

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var_1], res_fn);
        storage.add_resolution(&[dep_var_1], &[dep_var_2], res_fn);

        storage.get_awaiter([dep_var_2]).wait();

        storage.add_resolution(&[dep_var_2], &[dep_var_3], res_fn);

        storage.wait_till_resolved();

        let v = storage.get_value_unchecked(dep_var_3);

        assert_eq!(F::from_u64_with_reduction(123), v);
    }

    #[test]
    fn try_get_value_returns_none_before_resolve_record_mode() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var = Place::from_variable(Variable::from_variable_index(1));

        storage.set_value(init_var, F::from_u64_with_reduction(123));

        storage.add_resolution(&[init_var], &[dep_var], res_fn);

        let result = storage.try_get_value(dep_var);

        assert_eq!(None, result);
    }

    #[test]
    fn try_get_value_returns_none_before_resolve_playback_mode() {
        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var = Place::from_variable(Variable::from_variable_index(1));

        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var], res_fn);
        storage.try_get_value(dep_var);
        storage.wait_till_resolved();

        let rs = TestRecordStorage {
            record: Rc::new(storage.retrieve_sequence().clone()),
        };

        let mut storage =
            MtCircuitResolver::<F, PlaybackResolverSorter<F, TestRecordStorage, Cfg>, Cfg>::new(rs);

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var], res_fn);
        let result = storage.try_get_value(dep_var);

        assert_eq!(None, result);
    }

    #[test]
    fn try_get_value_returns_some_after_resolve_record_mode() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var = Place::from_variable(Variable::from_variable_index(1));

        storage.set_value(init_var, F::from_u64_with_reduction(123));

        storage.add_resolution(&[init_var], &[dep_var], res_fn);

        storage.wait_till_resolved();

        let result = storage.try_get_value(dep_var);

        assert_eq!(Some(F::from_u64_with_reduction(123)), result);
    }

    #[test]
    fn try_get_value_returns_some_after_resolve_playback_mode() {
        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var = Place::from_variable(Variable::from_variable_index(1));

        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var], res_fn);
        storage.wait_till_resolved();

        let rs = TestRecordStorage {
            record: Rc::new(storage.retrieve_sequence().clone()),
        };

        let mut storage =
            MtCircuitResolver::<F, PlaybackResolverSorter<F, TestRecordStorage, Cfg>, Cfg>::new(rs);

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var], res_fn);
        storage.wait_till_resolved();

        let result = storage.try_get_value(dep_var);

        assert_eq!(Some(F::from_u64_with_reduction(123)), result);
    }

    #[test]
    fn try_get_value_returns_some_after_wait_record_mode() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var = Place::from_variable(Variable::from_variable_index(1));

        storage.set_value(init_var, F::from_u64_with_reduction(123));

        storage.add_resolution(&[init_var], &[dep_var], res_fn);

        storage.get_awaiter([dep_var]).wait();

        let result = storage.try_get_value(dep_var);

        assert_eq!(Some(F::from_u64_with_reduction(123)), result);
    }

    #[test]
    fn try_get_value_returns_some_after_wait_playback_mode() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var_1 = Place::from_variable(Variable::from_variable_index(1));
        let dep_var_2 = Place::from_variable(Variable::from_variable_index(2));

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var_1], res_fn);
        storage.add_resolution(&[dep_var_1], &[dep_var_2], res_fn);
        storage.get_awaiter([dep_var_2]).wait();
        storage.wait_till_resolved();

        let rs = TestRecordStorage {
            record: Rc::new(storage.retrieve_sequence().clone()),
        };

        let mut storage =
            MtCircuitResolver::<F, PlaybackResolverSorter<F, TestRecordStorage, Cfg>, Cfg>::new(rs);

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var_1], res_fn);
        storage.add_resolution(&[dep_var_1], &[dep_var_2], res_fn);
        storage.get_awaiter([dep_var_2]).wait();

        let result = storage.try_get_value(dep_var_2);

        assert_eq!(Some(F::from_u64_with_reduction(123)), result);
    }

    #[test]
    fn try_get_value_returns_none_on_untracked() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var = Place::from_variable(Variable::from_variable_index(1));

        storage.set_value(init_var, F::from_u64_with_reduction(123));

        storage.add_resolution(&[init_var], &[dep_var], res_fn);

        let result = storage.try_get_value(Place::from_variable(Variable::from_variable_index(2)));

        assert_eq!(None, result);
    }

    // Test that panics in resolution functions are caught and propagated
    // to the caller.
    #[test]
    #[should_panic]
    fn panic_in_resolution_function_is_propagated_through_cr_waiting() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let res_fn = |_: &[F], _: &mut DstBuffer<F>| {
            panic!("This is a test panic");
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var = Place::from_variable(Variable::from_variable_index(1));

        storage.set_value(init_var, F::from_u64_with_reduction(123));

        storage.add_resolution(&[init_var], &[dep_var], res_fn);

        storage.wait_till_resolved();
    }

    // Test that panics in resolution functions are caught and propagated
    // when using awaiter.
    #[test]
    #[should_panic]
    fn panic_in_resolution_function_is_propagated_through_awaiter() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let res_fn = |_: &[F], _: &mut DstBuffer<F>| {
            panic!("This is a test panic");
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var = Place::from_variable(Variable::from_variable_index(1));

        storage.set_value(init_var, F::from_u64_with_reduction(123));

        storage.add_resolution(&[init_var], &[dep_var], res_fn);

        storage.get_awaiter([dep_var]).wait();
    }

    #[test]
    fn non_chronological_resolution_record_mode() {
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            let mut r = ins[0];
            r.mul_assign(&ins[1]);

            outs.push(r);
        };

        let var_1 = Place::from_variable(Variable::from_variable_index(0));
        let var_2 = Place::from_variable(Variable::from_variable_index(1));
        let var_3 = Place::from_variable(Variable::from_variable_index(2));
        let var_4 = Place::from_variable(Variable::from_variable_index(3));
        let var_5 = Place::from_variable(Variable::from_variable_index(4));

        storage.set_value(var_4, F::from_u64_with_reduction(7));
        storage.add_resolution(&[var_3, var_4], &[var_5], res_fn);
        storage.add_resolution(&[var_1, var_2], &[var_3], res_fn);
        storage.set_value(var_2, F::from_u64_with_reduction(5));
        storage.set_value(var_1, F::from_u64_with_reduction(3));

        storage.wait_till_resolved();

        let result = storage.try_get_value(var_5);

        assert_eq!(Some(F::from_u64_with_reduction(105)), result);
    }

    #[test]
    fn non_chronological_resolution_playback_mode() {
        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            let mut r = ins[0];
            r.mul_assign(&ins[1]);

            outs.push(r);
        };

        let var_1 = Place::from_variable(Variable::from_variable_index(0));
        let var_2 = Place::from_variable(Variable::from_variable_index(1));
        let var_3 = Place::from_variable(Variable::from_variable_index(2));
        let var_4 = Place::from_variable(Variable::from_variable_index(3));
        let var_5 = Place::from_variable(Variable::from_variable_index(4));

        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        storage.set_value(var_4, F::from_u64_with_reduction(7));
        storage.add_resolution(&[var_3, var_4], &[var_5], res_fn);
        storage.add_resolution(&[var_1, var_2], &[var_3], res_fn);
        storage.set_value(var_2, F::from_u64_with_reduction(5));
        storage.set_value(var_1, F::from_u64_with_reduction(3));

        storage.wait_till_resolved();

        let rs = TestRecordStorage {
            record: Rc::new(storage.retrieve_sequence().clone()),
        };

        let mut storage =
            MtCircuitResolver::<F, PlaybackResolverSorter<F, TestRecordStorage, Cfg>, Cfg>::new(rs);

        storage.set_value(var_4, F::from_u64_with_reduction(7));
        storage.add_resolution(&[var_3, var_4], &[var_5], res_fn);
        storage.add_resolution(&[var_1, var_2], &[var_3], res_fn);
        storage.set_value(var_2, F::from_u64_with_reduction(5));
        storage.set_value(var_1, F::from_u64_with_reduction(3));

        storage.wait_till_resolved();

        let result = storage.try_get_value(var_5);

        assert_eq!(Some(F::from_u64_with_reduction(105)), result);
    }

    fn correctness_simple_linear_populate<F: SmallField, RS: ResolverSortingMode<F>>(
        resolver: &mut MtCircuitResolver<F, RS, Cfg>,
        limit: usize,
    ) {
        let mut var_idx = 0;

        let mut pa = Place::from_variable(Variable::from_variable_index(var_idx));
        var_idx += 1;
        let mut pb = Place::from_variable(Variable::from_variable_index(var_idx));
        var_idx += 1;

        resolver.set_value(pa, F::from_u64_with_reduction(1));
        resolver.set_value(pb, F::from_u64_with_reduction(2));

        for _ in 1..limit {
            let a = Place::from_variable(Variable::from_variable_index(var_idx));
            var_idx += 1;
            let b = Place::from_variable(Variable::from_variable_index(var_idx));
            var_idx += 1;

            // We increment each of the 4 variables by one so each could be
            // corellated to their position.
            let f = |ins: &[F], out: &mut DstBuffer<F>| {
                if let [p] = *ins {
                    let mut result = p;
                    Field::add_assign(&mut result, &F::from_u64_with_reduction(1));

                    out.push(result);
                } else {
                    unreachable!();
                }
            };

            resolver.add_resolution(&[pa], &[a], f);
            pa = a;
            resolver.add_resolution(&[pb], &[b], f);
            pb = b;
        }
    }

    #[test]
    fn correctness_simple_linear_record_mode() {
        let limit = 1 << 10;

        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: limit * 5,
                desired_parallelism: 32,
            });

        correctness_simple_linear_populate(&mut storage, limit);

        storage.wait_till_resolved();

        if cfg!(feature = "cr_paranoia_mode") {
            log!("Test: total value result: \n   - {}", unsafe {
                (*storage.common.values.get())
                    .variables
                    .iter()
                    .take(limit * 2 + 2)
                    .enumerate()
                    .map(|(i, x)| format!("[{}] - {}", i, (*x.get()).0))
                    .collect::<Vec<_>>()
                    .join("\n   - ")
            });
        }

        for i in 0..limit {
            for j in 0..2 {
                let ix = i * 2 + j;
                let val = i + j + 1;

                let exp = F::from_u64_with_reduction(val as u64);
                let act = Place::from_variable(Variable::from_variable_index(ix as u64))
                    .to(|x| storage.get_value_unchecked(x));

                if cfg!(feature = "cr_paranoia_mode") {
                    log!("Test: per item value: ix {}, value {}", ix, act);
                }

                assert_eq!(exp, act, "Ix {}", ix);
            }
        }
    }

    #[test]
    fn correctness_simple_linear_playback_mode() {
        let limit = 1 << 10;

        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: limit * 5,
                desired_parallelism: 32,
            });

        correctness_simple_linear_populate(&mut storage, limit);
        storage.wait_till_resolved();

        let rs = TestRecordStorage {
            record: Rc::new(storage.retrieve_sequence().clone()),
        };

        let mut storage =
            MtCircuitResolver::<F, PlaybackResolverSorter<F, TestRecordStorage, Cfg>, Cfg>::new(rs);

        correctness_simple_linear_populate(&mut storage, limit);

        storage.wait_till_resolved();

        if cfg!(feature = "cr_paranoia_mode") {
            log!("Test: total value result: \n   - {}", unsafe {
                (*storage.common.values.get())
                    .variables
                    .iter()
                    .take(limit * 2 + 2)
                    .enumerate()
                    .map(|(i, x)| format!("[{}] - {}", i, (*x.get()).0))
                    .collect::<Vec<_>>()
                    .join("\n   - ")
            });
        }

        for i in 0..limit {
            for j in 0..2 {
                let ix = i * 2 + j;
                let val = i + j + 1;

                let exp = F::from_u64_with_reduction(val as u64);
                let act = Place::from_variable(Variable::from_variable_index(ix as u64))
                    .to(|x| storage.get_value_unchecked(x));

                if cfg!(feature = "cr_paranoia_mode") {
                    log!("Test: per item value: ix {}, value {}", ix, act);
                }

                assert_eq!(exp, act, "Ix {}", ix);
            }
        }
    }

    fn populate<RS: ResolverSortingMode<F>>(
        storage: &mut MtCircuitResolver<F, RS, Cfg>,
        limit: usize,
    ) {
        let mut var_idx = 0u64;
        for _ in 0..limit {
            let a = Place::from_variable(Variable::from_variable_index(var_idx));
            var_idx += 1;
            let b = Place::from_variable(Variable::from_variable_index(var_idx));
            var_idx += 1;
            let c = Place::from_variable(Variable::from_variable_index(var_idx));
            var_idx += 1;
            let d = Place::from_variable(Variable::from_variable_index(var_idx));
            var_idx += 1;
            let e = Place::from_variable(Variable::from_variable_index(var_idx));
            var_idx += 1;

            storage.set_value(a, F::from_u64_with_reduction(1));
            storage.set_value(b, F::from_u64_with_reduction(2));
            storage.set_value(c, F::from_u64_with_reduction(3));

            let f1 = |ins: &[F], out: &mut DstBuffer<F>| {
                if let [a, b, c] = *ins {
                    let mut result = a;
                    Field::add_assign(&mut result, &b);
                    Field::add_assign(&mut result, &c);

                    out.push(result);
                } else {
                    unreachable!();
                }
            };

            storage.add_resolution(&[a, b, c], &[d], f1);

            let f2 = |ins: &[F], out: &mut DstBuffer<F>| {
                if let [c, d] = *ins {
                    let mut result = c;
                    Field::mul_assign(&mut result, &d);

                    out.push(result);
                } else {
                    unreachable!()
                }
            };

            storage.add_resolution(&[c, d], &[e], f2)
        }
    }
}

#[cfg(test)]
mod benches {

    use super::*;
    use crate::{
        config::{DoPerformRuntimeAsserts, Resolver},
        cs::{traits::cs::DstBuffer, Place, Variable},
        dag::{
            resolvers::mt::sorters::sorter_live::LiveResolverSorter, Awaiter as _,
            CircuitResolverOpts,
        },
        field::{goldilocks::GoldilocksField, Field},
        log,
    };
    type F = GoldilocksField;
    type Cfg = Resolver<DoPerformRuntimeAsserts>;

    #[test]
    #[ignore = ""]
    fn synth_bench_m_1() {
        // Warmup.
        for _ in 0..2 {
            synth_bench_1()
        }

        let now = std::time::Instant::now();
        for _ in 0..15 {
            synth_bench_1()
        }
        log!("15 resolutions in {:?}", now.elapsed());
    }

    #[test]
    fn synth_bench_1() {
        let limit = 1 << 25;
        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: limit * 5,
                desired_parallelism: 2048,
            });

        log!("Storage is ready");

        let now = std::time::Instant::now();

        let mut var_idx = 0u64;
        for _ in 0..limit {
            let a = Place::from_variable(Variable::from_variable_index(var_idx));
            var_idx += 1;
            let b = Place::from_variable(Variable::from_variable_index(var_idx));
            var_idx += 1;
            let c = Place::from_variable(Variable::from_variable_index(var_idx));
            var_idx += 1;
            let d = Place::from_variable(Variable::from_variable_index(var_idx));
            var_idx += 1;
            let e = Place::from_variable(Variable::from_variable_index(var_idx));
            var_idx += 1;

            storage.set_value(a, F::from_u64_with_reduction(1));
            storage.set_value(b, F::from_u64_with_reduction(2));
            storage.set_value(c, F::from_u64_with_reduction(3));

            let f1 = |ins: &[F], out: &mut DstBuffer<F>| {
                if let [a, b, c] = *ins {
                    let mut result = a;
                    Field::add_assign(&mut result, &b);
                    Field::add_assign(&mut result, &c);

                    out.push(result);
                } else {
                    unreachable!();
                }
            };

            storage.add_resolution(&[a, b, c], &[d], f1);

            let f2 = |ins: &[F], out: &mut DstBuffer<F>| {
                if let [c, d] = *ins {
                    let mut result = c;
                    Field::mul_assign(&mut result, &d);

                    out.push(result);
                } else {
                    unreachable!()
                }
            };

            storage.add_resolution(&[c, d], &[e], f2)
        }

        log!("[{:?}] Waiting.", std::time::Instant::now());

        storage.wait_till_resolved();

        log!("Resolution took {:?}", now.elapsed());

        log!(
            "Ensure not optimized away {}",
            storage.get_value_unchecked(Place::from_variable(Variable::from_variable_index(0)))
        );
    }

    #[test]
    fn awaiter_performance_bench() {
        let now = std::time::Instant::now();

        let limit = 1 << 4;

        let mut storage =
            MtCircuitResolver::<F, LiveResolverSorter<F, Cfg>, Cfg>::new(CircuitResolverOpts {
                max_variables: limit + 1,
                desired_parallelism: 16,
            });

        let init_var = Place::from_variable(Variable::from_variable_index(0));

        storage.set_value(init_var, F::from_u64_with_reduction(123));

        for i in 1..limit {
            println!("{}", i);
            let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
                outs.push(ins[0]);
            };

            let out_var = Place::from_variable(Variable::from_variable_index(i as u64));

            storage.add_resolution(&[init_var], &[out_var], res_fn);

            let awaiter = storage.get_awaiter([out_var]);

            awaiter.wait()
        }

        storage.wait_till_resolved();

        log!("Awaiter performance took {:?}", now.elapsed());
    }
}
