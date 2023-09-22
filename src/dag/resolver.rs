// Interferes with paranioa mode.
#![allow(clippy::overly_complex_bool_expr)]
#![allow(clippy::nonminimal_bool)]

use crate::log;
use std::any::Any;
use std::cell::{Cell, UnsafeCell};

use super::resolution_window::ResolutionWindow;
use super::{registrar::Registrar, WitnessSource, WitnessSourceAwaitable};
use crate::config::*;
use crate::cs::traits::cs::{CSWitnessSource, DstBuffer};
use crate::cs::{Place, Variable, VariableType};
use crate::dag::awaiters::AwaitersBroker;
use crate::dag::resolution_window::invocation_binder;
use crate::dag::resolver_box::ResolverBox;
use crate::dag::{awaiters, guide::*};
use crate::field::SmallField;
use crate::utils::{PipeOp, UnsafeCellEx};
use itertools::Itertools;
use std::ops::{AddAssign, Sub};
use std::panic::resume_unwind;
use std::sync::atomic::{fence, AtomicBool};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;

pub type OrderIx = u32;
pub(crate) type Mutarc<T> = Arc<Mutex<T>>;

pub const PARANOIA: bool = false;

#[derive(Clone, Copy, Debug)]
pub struct CircuitResolverOpts {
    pub max_variables: usize,
    //pub witness_columns: usize,
    //pub max_trace_len: usize,
    pub desired_parallelism: u32,
}

/// Shared between the resolver, awaiters and the resolution window.
pub(crate) struct ResolverCommonData<V> {
    // The following two are meant to have an asynchronized access. The access
    // correctness is provided by the `exec_order` mutex. Once an iter is
    // added to the `exec_order`, it's guaranteed that the corresponding
    // values are present in resolvers and values.
    pub resolvers: UnsafeCell<ResolverBox<V>>,
    pub values: UnsafeCell<Values<V>>,

    /// Resolutions happen in this order. Holds index of the resolver in `resolver`.
    /// This index follows pointer semantics and is unsafe to operate on.
    /// The order can have gaps, so it's size should be somewhat larger than the total
    /// amount of resolvers.
    pub exec_order: Mutex<Vec<OrderInfo<ResolverIx>>>,
    pub awaiters_broker: AwaitersBroker,
    pub comms: ResolverComms,
}

/// Used to send notifications and data between the resolver, resolution window
/// and the awaiters.
pub(crate) struct ResolverComms {
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

pub struct CircuitResolver<V: SmallField, Cfg: CSResolverConfig> {
    registrar: Registrar,

    pub(crate) common: Arc<ResolverCommonData<V>>,
    pub(crate) options: CircuitResolverOpts,
    pub(crate) guide: BufferGuide<ResolverIx, Cfg>,

    resolution_window_handle: Option<JoinHandle<()>>,

    stats: Stats,
    debug_track: Vec<Place>,
}

unsafe impl<V: SmallField, Cfg: CSResolverConfig> Send for CircuitResolver<V, Cfg> where V: Send {}
unsafe impl<V: SmallField, Cfg: CSResolverConfig> Sync for CircuitResolver<V, Cfg> where V: Send {}

// TODO: try to eliminate this constraint to something more general, preferably defatult.
impl<'cr, V: SmallField, Cfg: CSResolverConfig> CircuitResolver<V, Cfg> {
    pub fn new(opts: CircuitResolverOpts) -> Self {
        fn new_values<V>(size: usize, default: fn() -> V) -> Box<[V]> {
            // TODO: ensure mem-page multiple capacity.
            let mut values = Vec::with_capacity(size);
            // TODO: If this isn't reused extend should be switched to unsafe resize
            values.resize_with(size, default);
            values.into_boxed_slice()
        }

        let values = Values {
            variables: new_values(opts.max_variables, || {
                UnsafeCell::new((V::from_u64_unchecked(0), Metadata::default()))
            }),
            max_tracked: -1,
        };

        let exec_order = Vec::with_capacity(opts.max_variables);

        let debug_track = vec![];

        if cfg!(cr_paranoia_mode) || PARANOIA {
            log!("Contains tracked keys {:?} ", debug_track);
        }

        let common = ResolverCommonData {
            resolvers: UnsafeCell::new(ResolverBox::new()),
            values: UnsafeCell::new(values),
            exec_order: Mutex::new(exec_order),
            awaiters_broker: AwaitersBroker::new(),
            comms: ResolverComms {
                registration_complete: AtomicBool::new(false),
                rw_panicked: AtomicBool::new(false),
                rw_panic: Cell::new(None),
            },
        }
        .to(Arc::new);

        let threads = 3;

        Self {
            options: opts,
            guide: BufferGuide::new(opts.desired_parallelism),
            registrar: Registrar::new(),

            resolution_window_handle: ResolutionWindow::<V>::run(
                Arc::clone(&common),
                &debug_track,
                threads,
            )
            .to(Some),

            common,
            stats: Stats::new(),
            debug_track,
        }
    }

    pub fn set_value(&mut self, key: Place, value: V) {
        if (cfg!(cr_paranoia_mode) || PARANOIA) && self.debug_track.contains(&key) && false {
            log!("CR: setting {:?} -> {:?}", key, value);
        }

        match key.get_type() {
            VariableType::CopyableVariable => self.stats.values_added += 1,
            VariableType::Witness => self.stats.witnesses_added += 1,
        }

        // Safety: Dereferencing as &mut in mutable context. This thread doesn't hold any
        // references to `self.resolvers`. Other thread may hold shared references, but
        // are guaranteed to not access the same underlying data.
        let values = unsafe { self.common.values.u_deref_mut() };

        values.set_value(key, value);

        // Safety: using as shared, assuming no &mut references to
        // `self.resolvers` (Only this thread requires mut, and we're not
        // currently doing that).

        let delayed_resolvers =
            if values.max_tracked >= 0 {
                self.registrar.advance(values.max_tracked.to(|x| {
                    Place::from_variable(Variable::from_variable_index(x.try_into().unwrap()))
                }))
            } else {
                vec![]
            };

        unsafe {
            // Safety: Dereferencing as shared, not accessing `resolve_fn`.
            let rb = self.common.resolvers.u_deref();

            delayed_resolvers
                .into_iter()
                .map(|x| (x, rb.get(x).inputs(), rb.get(x).outputs()))
                // Safety: No &mut references to `self.common.resolvers`.
                .for_each(|(r, i, o)| self.internalize(r, i, o));
        }
    }

    pub fn add_resolution<F>(&mut self, inputs: &[Place], outputs: &[Place], f: F)
    where
        F: FnOnce(&[V], &mut DstBuffer<'_, '_, V>) + Send + Sync + 'cr,
    {
        debug_assert!(inputs
            .iter()
            .all(|x| x.0 < self.options.max_variables as u64));

        // Safety: This thread is the only one to use `push` on the resolvers
        // and is the only thread to do so. `push` is the only mutable function
        // on that struct.
        let resolver_ix = unsafe {
            self.common
                .resolvers
                .u_deref_mut()
                .push(inputs, outputs, f, invocation_binder::<F, V>)
        };

        if PARANOIA && resolver_ix.0 == 0 {
            println!(
                "CR: Resolvers push returned ix 0, on resolution {}",
                self.stats.registrations_added
            );
        }

        let mut hit = false;

        if (cfg!(cr_paranoia_mode) || PARANOIA) && true {
            if let Some(x) = self.debug_track.iter().find(|x| inputs.contains(x)) {
                log!("CR: added resolution with tracked input {:?}", x);

                hit = true;
            }

            if let Some(x) = self.debug_track.iter().find(|x| outputs.contains(x)) {
                log!("CR: added resolution with tracked output {:?}", x);

                hit = true;
            }

            if hit {
                log!("   {:?}", resolver_ix);
                log!(
                    "   Ins:\n   - {}{}\n   Outs:\n   - {}{}",
                    inputs
                        .iter()
                        .take(10)
                        .map(|x| format!("{:?}", x))
                        .collect_vec()
                        .join("\n   - "),
                    if inputs.len() > 10 {
                        format!("\n   - ... {} total", inputs.len())
                    } else {
                        "".to_owned()
                    },
                    outputs
                        .iter()
                        .take(10)
                        .map(|x| format!("{:?}", x))
                        .collect_vec()
                        .join("\n   - "),
                    if outputs.len() > 10 {
                        format!("\n   - ... {} total", outputs.len())
                    } else {
                        "".to_owned()
                    },
                );
            }
        }

        let registrar_answer = self.registrar.accept(inputs, resolver_ix);

        if hit {
            match registrar_answer {
                Err(x) => log!("   Registration delayed due to {:?}", x),
                Ok(_) => log!("   Registration accepted."),
            }
        }

        if let Ok(resolver_ix) = registrar_answer {
            // Safety: `self.resolvers` is dropped as a temp value a few lines above.
            unsafe { self.internalize(resolver_ix, inputs, outputs) };
        }

        self.stats.registrations_added += 1;
    }

    /// Safety: `self.common.resolvers` must not have a &mut reference to it.
    unsafe fn internalize(&mut self, resolver_ix: ResolverIx, inputs: &[Place], outputs: &[Place]) {
        let mut resolvers = vec![(resolver_ix, inputs, outputs)];

        if PARANOIA && resolver_ix == ResolverIx::new_resolver(0) {
            println!("CR: Internalize called with resolver_ix 0");
        }

        // Safety: using as shared, assuming no &mut references to
        // `self.resolvers` that access the same underlying data. This is
        // guaranteed by the fact that inputs and outputs for any given resolver
        // is written only once by this thread, and safety requires that no &mut
        // references to `self.resolvers` exist.
        let rb = self.common.resolvers.u_deref();

        while resolvers.len() > 0 {
            let (resolver_ix, inputs, outputs) = resolvers.pop().unwrap();

            let new_resolvers = self.internalize_one(resolver_ix, inputs, outputs);

            if PARANOIA {
                if new_resolvers.iter().any(|x| x.0 == 0) {
                    println!("CR: internalize_one returned resolver with ix 0");
                }
            }

            self.registrar.stats.secondary_resolutions += new_resolvers.len();

            // Safety: calling to immutable functions (`get`, `inputs`, `outputs`).
            // The resolver is not yet pushed to the resolution window.
            new_resolvers
                .into_iter()
                .map(|x| (x, rb.get(x).inputs(), rb.get(x).outputs()))
                .to(|x| resolvers.extend(x));
        }
    }

    fn internalize_one(
        &mut self,
        resolver_ix: ResolverIx,
        inputs: &[Place],
        outputs: &[Place],
    ) -> Vec<ResolverIx> {
        if cfg!(cr_paranoia_mode) {
            if let Some(x) = self.debug_track.iter().find(|x| inputs.contains(x)) {
                log!("CR: internalized resolution with tracked input {:?}", x);
            }

            if let Some(x) = self.debug_track.iter().find(|x| outputs.contains(x)) {
                log!("CR: internalized resolution with tracked output {:?}", x);
            }
        }

        // Safety: The values created by this function are not yet tracked, thus
        // are not referenced by anyone. All dependencies have already been
        // written.
        // It is safe to borrow as mut because the only mutable function that is
        // being called on it is `track_values` and thus no one can have a
        // reference to that location.
        // The rest of the calls are immutable.
        let values = unsafe { self.common.values.u_deref_mut() };

        let deps = inputs.iter().map(|x| &values.get_item_ref(*x).1);

        if cfg!(cr_paranoia_mode) {
            debug_assert!(
                deps.clone().all(|x| { x.is_tracked() }),
                "Attempting to internalize a resolution with an untracked input. All inputs must be tracked."
            );
        }

        if PARANOIA && resolver_ix == ResolverIx::new_resolver(0) && false {
            self.guide.tracing = true;
        }

        if PARANOIA && resolver_ix == ResolverIx::new_resolver(0) {
            println!("CR: resolver_ix {} pushed to guide.", resolver_ix.0);
        }

        let (guide_loc, order) = self
            .guide
            .push(resolver_ix, deps.map(|x| x.guide_loc).reduce(std::cmp::max));

        Self::write_order(&self.common.exec_order, &self.common.resolvers, &order);

        values.track_values(outputs, guide_loc);

        // This values starts from -1, which is illegal.
        if values.max_tracked >= 0 {
            let delayed_resolvers = self.registrar.advance(values.max_tracked.to(|x| {
                Place::from_variable(Variable::from_variable_index(x.try_into().unwrap()))
            }));

            delayed_resolvers
        } else {
            Vec::new()
        }
    }

    fn write_order<'a, T: GuideOrder<'a, ResolverIx>>(
        tgt: &Mutex<Vec<OrderInfo<ResolverIx>>>,
        resolvers: &UnsafeCell<ResolverBox<V>>,
        order: &T,
    ) {
        if order.size() > 0 {
            let mut tgt = tgt.lock().unwrap();
            let len = tgt.len();
            tgt.resize(
                len + order.size(),
                OrderInfo::new(ResolverIx::default(), GuideMetadata::new(0)),
            );

            order.write(&mut tgt[..]);

            if PARANOIA {
                for i in len..len + order.size() {
                    if tgt[i].value == ResolverIx(0) {
                        log!(
                            "CR: resolver {} added to order at ix {}, during write {}..{}.",
                            tgt[i].value.0,
                            i,
                            len,
                            len + order.size()
                        );
                    }
                }
            }

            if cfg!(cr_paranoia_mode) {
                // This ugly block checks that the calculated parallelism is
                // correct. It's a bit slower than O(n^2). Also note, that it
                // checks only the last 1050 items, so it's not a full check,
                // 'twas when the desired parallelism was set to 1024, but it's
                // not anymore.
                unsafe {
                    for r_ix in std::cmp::max(0, len as i32 - 1050) as usize..tgt.len() {
                        let r = resolvers.u_deref().get(tgt[r_ix].value);

                        for derivative in
                            r_ix..std::cmp::min(r_ix + tgt[r_ix].metadata.parallelism(), tgt.len())
                        {
                            let r_d = resolvers.u_deref().get(tgt[derivative].value);

                            assert!(r.outputs().iter().all(|x| r_d.inputs().contains(x) == false),
                                "Parallelism violation at ix {}, val {:#?}, derivative ix {} , val {:#?}: {:#?}",
                                r_ix,
                                tgt[r_ix],
                                derivative,
                                tgt[derivative],
                                (std::cmp::max(0, len as i32 - 1050) as usize..tgt.len())
                                    .map(|x| (x, resolvers.u_deref().get(tgt[x].value)))
                                    .map(|(i, r)| (i, tgt[i], r.inputs().to_vec(), r.outputs().to_vec()))
                                    .collect_vec()
                            );
                        }
                    }
                }
            }
        }
    }

    pub fn wait_till_resolved(&mut self) {
        self.wait_till_resolved_impl(true);
    }

    pub fn wait_till_resolved_impl(&mut self, report: bool) {
        if self
            .common
            .comms
            .registration_complete
            .load(std::sync::atomic::Ordering::Relaxed)
        {
            return;
        }

        assert!(self.registrar.is_empty());
        // assert!(self.registrar.is_empty(), "Registrar is not empty: has {:?}", self.registrar.peek_vars());

        let order = self.guide.flush();

        Self::write_order(&self.common.exec_order, &self.common.resolvers, &order);

        drop(order);

        if cfg!(cr_paranoia_mode) || PARANOIA {
            log!(
                "CR: Final order written. Order len {}",
                self.common.exec_order.lock().unwrap().len()
            );
        }

        self.stats.registration_time = self.stats.started_at.elapsed();

        self.common
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
            .common
            .comms
            .rw_panicked
            .load(std::sync::atomic::Ordering::Relaxed)
        {
            if let Some(e) = self.common.comms.rw_panic.take() {
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

        if cfg!(cr_paranoia_mode) || PARANOIA {
            self.guide.stats.finalize();

            log!("CR {:?}", self.guide.stats);
            log!("CRR stats {:#?}", self.registrar.stats);
            log!("CR {:?}", unsafe {
                self.common.awaiters_broker.stats.u_deref()
            });
        }
    }

    pub fn clear(&mut self) {
        // TODO: implement
    }
}

impl<V: SmallField, Cfg: CSResolverConfig> WitnessSource<V> for CircuitResolver<V, Cfg> {
    const PRODUCES_VALUES: bool = true;

    fn try_get_value(&self, variable: Place) -> Option<V> {
        // TODO: UB on subsequent calls?

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

impl<V: SmallField, Cfg: CSResolverConfig> CSWitnessSource<V> for CircuitResolver<V, Cfg> {}

impl<V: SmallField, Cfg: CSResolverConfig> WitnessSourceAwaitable<V> for CircuitResolver<V, Cfg> {
    type Awaiter<'a> = awaiters::Awaiter<'a>;

    fn get_awaiter<const N: usize>(&mut self, vars: [Place; N]) -> awaiters::Awaiter {
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
            .max_by_key(|x| x.guide_loc)
            .unwrap();

        let r = awaiters::AwaitersBroker::register(
            &self.common.awaiters_broker,
            &self.common.comms,
            md,
        );

        let order = self.guide.flush();

        Self::write_order(&self.common.exec_order, &self.common.resolvers, &order);

        drop(order);

        r
    }
}

// impl Drop for CircuitResolver

impl<V: SmallField, Cfg: CSResolverConfig> Drop for CircuitResolver<V, Cfg> {
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

// region: ResolverIx

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) struct ResolverIx(pub u32);

pub(crate) enum ResolverIxType {
    Jump,
    Resolver,
}

impl ResolverIx {
    // Resolver box uses `sizeof` to determine the size of the allocations,
    // and operates on pointers or _size primitives, which always have lsb == 0
    // in their sizes, thus we can use the lsb to store type info.
    const TYPE_MASK: u32 = 1;

    pub fn get_type(self) -> ResolverIxType {
        match self.0 & Self::TYPE_MASK == 0 {
            true => ResolverIxType::Resolver,
            false => ResolverIxType::Jump,
        }
    }

    fn new_jump(value: u32) -> Self {
        Self(value | Self::TYPE_MASK)
    }

    pub fn new_resolver(value: u32) -> Self {
        Self(value)
    }

    pub fn normalized(&self) -> usize {
        (!Self::TYPE_MASK & self.0) as usize
    }
}

impl AddAssign for ResolverIx {
    fn add_assign(&mut self, rhs: Self) {
        self.0 = rhs.0;
    }
}

impl Sub for ResolverIx {
    type Output = u32;

    fn sub(self, origin: Self) -> Self::Output {
        self.0 - origin.0
    }
}

impl AddAssign<u32> for ResolverIx {
    fn add_assign(&mut self, rhs: u32) {
        self.0 = rhs;
    }
}

// endregion

// region: Values

pub struct Values<V> {
    pub(crate) variables: Box<[UnsafeCell<(V, Metadata)>]>,
    pub(crate) max_tracked: i64, // Be sure to not overflow.
}

impl<V> Values<V> {
    pub(crate) fn resolve_type(&self, _key: Place) -> &[UnsafeCell<(V, Metadata)>] {
        &self.variables
    }

    pub(crate) fn get_item_ref(&self, key: Place) -> &(V, Metadata) {
        let vs = self.resolve_type(key);
        unsafe { &(*vs[key.raw_ix()].get()) }

        // TODO: spec unprocessed/untracked items
    }

    // Safety: No other mutable references to the same item are allowed.
    pub(crate) unsafe fn get_item_ref_mut(&self, key: Place) -> &mut (V, Metadata) {
        let vs = self.resolve_type(key);
        &mut (*vs[key.raw_ix()].get())

        // TODO: spec unprocessed/untracked items
    }

    /// Marks values as tracked and stores the resolution order that those values
    /// are resolved in.
    fn track_values(&mut self, keys: &[Place], loc: GuideLoc) {
        for key in keys {
            let nmd = Metadata::new(loc);

            // Safety: tracking is only done on untracked values, and only once, so the
            // item at key is guaranteed to not be used. If the item was already tracked,
            // we panic in the next line.
            let (_, md) = unsafe { self.get_item_ref_mut(*key) };

            if md.is_tracked() {
                panic!("Value with index {} is already tracked", key.as_any_index())
            }

            *md = nmd;
        }

        self.advance_track();
    }

    fn set_value(&mut self, key: Place, value: V) {
        // Safety: we're setting the value, so we're sure that the item at key is not used.
        // If the item was already set, we panic in the next line.
        let (v, md) = unsafe { self.get_item_ref_mut(key) };

        if md.is_tracked() {
            panic!("Value with index {} is already set", key.as_any_index())
        }

        (*v, *md) = (value, Metadata::new_resolved());

        self.advance_track();
    }

    fn advance_track(&mut self) {
        for i in (self.max_tracked + 1)..self.variables.len() as i64 {
            // TODO: switch to the following on next dev iteration.
            // if  i
            //     .to(std::convert::TryInto::<u64>::try_into)
            //     .unwrap()
            //     .to(Variable::from_variable_index)
            //     .to(Place::from_variable)
            //     .to(|x| self.get_item_ref(x))
            //     .1.is_tracked() == false {

            if self
                .get_item_ref(Place::from_variable(Variable::from_variable_index(
                    i.try_into().unwrap(),
                )))
                .1
                .is_tracked()
                == false
            {
                self.max_tracked = i - 1;
                break;
            }
        }
    }
}

// endregion

// region: metadata

type Mdi = u16;

#[derive(Default)]
// Used by the resolver for internal tracking purposes.
pub(crate) struct Metadata {
    data: Mdi,
    pub guide_loc: GuideLoc,
}

impl Metadata {
    // Means this element was introduced to the resolver
    const TRACKED_MASK: Mdi = 0b1000_0000_0000_0000;
    // Means this element was resolved and it's value is set.
    const RESOLVED_MASK: Mdi = 0b0100_0000_0000_0000;

    fn new(loc: GuideLoc) -> Self {
        Self {
            data: Self::TRACKED_MASK,
            guide_loc: loc,
        }
    }

    fn new_resolved() -> Self {
        Self {
            data: Self::TRACKED_MASK | Self::RESOLVED_MASK,
            guide_loc: GuideLoc::default(),
        }
    }

    pub fn is_tracked(&self) -> bool {
        self.data & Self::TRACKED_MASK != 0
    }

    pub fn is_resolved(&self) -> bool {
        self.data & Self::RESOLVED_MASK != 0
    }

    pub fn mark_resolved(&mut self) {
        self.data |= Self::RESOLVED_MASK;
    }
}

// endregion

#[cfg(test)]
mod test {
    use crate::{dag::Awaiter, utils::PipeOp};
    use std::{collections::VecDeque, hint::spin_loop, time::Duration};

    use crate::{
        config::DoPerformRuntimeAsserts,
        cs::Variable,
        field::{goldilocks::GoldilocksField, Field},
    };

    use super::*;

    type F = GoldilocksField;

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

    #[test]
    fn init_tracks_values() {
        let limit = 10;
        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
                max_variables: 10,
                desired_parallelism: 16,
            });

        log!("Storage is ready");

        for i in 0..limit {
            let a = Place::from_variable(Variable::from_variable_index(i));

            storage.set_value(a, F::from_u64_with_reduction(i));
        }

        for i in 0..limit {
            let a = Place::from_variable(Variable::from_variable_index(i));
            let v = storage.get_value_unchecked(a);

            assert_eq!(F::from_u64_with_reduction(i), v);
        }
    }

    #[test]
    fn resolves() {
        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
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

        assert_eq!(
            storage.get_value_unchecked(init_var),
            storage.get_value_unchecked(dep_var)
        );
    }

    #[test]
    fn resolves_siblings() {
        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            let mut x = ins[0];

            outs.push(*x.double());
        };

        let init_var1 = Place::from_variable(Variable::from_variable_index(0));
        let dep_var1 = Place::from_variable(Variable::from_variable_index(1));
        let init_var2 = Place::from_variable(Variable::from_variable_index(2));
        let dep_var2 = Place::from_variable(Variable::from_variable_index(3));

        storage.set_value(init_var1, F::from_u64_with_reduction(123));
        storage.set_value(init_var2, F::from_u64_with_reduction(321));

        storage.add_resolution(&[init_var1], &[dep_var1], res_fn);
        storage.add_resolution(&[init_var2], &[dep_var2], res_fn);

        storage.wait_till_resolved();

        // let a = *storage.get_value_unchecked(init_var2).clone().double();
        // let b = storage.get_value_unchecked(dep_var2);

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
    fn resolves_descendants() {
        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            let mut x = ins[0];

            outs.push(*x.double());
        };

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var1 = Place::from_variable(Variable::from_variable_index(1));
        let dep_var2 = Place::from_variable(Variable::from_variable_index(2));
        let dep_var3 = Place::from_variable(Variable::from_variable_index(3));

        storage.set_value(init_var, F::from_u64_with_reduction(2));

        storage.add_resolution(&[init_var], &[dep_var1], res_fn);
        storage.add_resolution(&[dep_var1], &[dep_var2], res_fn);
        storage.add_resolution(&[dep_var2], &[dep_var3], res_fn);

        storage.wait_till_resolved();

        assert_eq!(
            F::from_u64_with_reduction(16),
            storage.get_value_unchecked(dep_var3)
        );
    }

    #[test]
    fn resolves_with_context() {
        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
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
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let init_var = Place::from_variable(Variable::from_variable_index(0));
        let dep_var = Place::from_variable(Variable::from_variable_index(1));

        storage.set_value(init_var, F::from_u64_with_reduction(123));

        struct DroppedContext {
            times_invoked: Mutarc<u32>,
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
    fn awaiter_returns_for_resolved_value() {
        let limit = 1 << 13;
        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
                max_variables: limit * 5,
                desired_parallelism: 2048,
            });

        // let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
        //     outs.push(ins[0]);
        // };

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
    fn awaiter_returns_after_finish() {
        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
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
    fn awaiter_returns_for_unexpropriated() {
        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
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
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let mut notch = std::time::Instant::now();

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            std::thread::sleep(Duration::from_secs(1));
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
    fn resolution_after_awaiter_is_supported() {
        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
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
    fn try_get_value_returns_none_before_resolve() {
        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
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
    fn try_get_value_returns_some_after_resolve() {
        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
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
    fn try_get_value_returns_some_after_wait() {
        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
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
    fn try_get_value_returns_none_on_untracked() {
        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
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
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
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
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
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
    fn non_chronological_resolution() {
        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
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
    fn correctness_simple_linear() {
        let limit = 1 << 10;

        let mut storage =
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
                max_variables: limit * 5,
                desired_parallelism: 32,
            });

        let mut var_idx = 0;

        let mut pa = Place::from_variable(Variable::from_variable_index(var_idx));
        var_idx += 1;
        let mut pb = Place::from_variable(Variable::from_variable_index(var_idx));
        var_idx += 1;

        storage.set_value(pa, F::from_u64_with_reduction(1));
        storage.set_value(pb, F::from_u64_with_reduction(2));

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

            storage.add_resolution(&[pa], &[a], f);
            pa = a;
            storage.add_resolution(&[pb], &[b], f);
            pb = b;
        }

        storage.wait_till_resolved();

        if cfg!(cr_paranoia_mode) {
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

                if cfg!(cr_paranoia_mode) {
                    log!("Test: per item value: ix {}, value {}", ix, act);
                }

                assert_eq!(exp, act, "Ix {}", ix);
            }
        }
    }

    fn populate(storage: &mut CircuitResolver<F, Resolver<DoPerformRuntimeAsserts>>, limit: usize) {
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
        cs::Variable,
        dag::Awaiter,
        field::{goldilocks::GoldilocksField, Field},
    };
    type F = GoldilocksField;

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
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
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
            CircuitResolver::<F, Resolver<DoPerformRuntimeAsserts>>::new(CircuitResolverOpts {
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
