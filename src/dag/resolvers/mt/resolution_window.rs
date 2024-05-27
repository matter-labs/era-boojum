// Interferes with paranioa mode.
#![allow(clippy::overly_complex_bool_expr)]
#![allow(clippy::nonminimal_bool)]
// Allow inspection.
#![allow(clippy::let_and_return)]

use std::{
    any::Any,
    cell::{Cell, UnsafeCell},
    cmp,
    collections::VecDeque,
    hint::spin_loop,
    io::Write,
    marker::PhantomData,
    ops::Range,
    panic::AssertUnwindSafe,
    path::PathBuf,
    sync::{
        atomic::{fence, AtomicBool, AtomicUsize},
        Arc, Mutex,
    },
    thread::{park, yield_now, JoinHandle, Thread},
    time::Duration,
};

use itertools::Itertools;
use smallvec::SmallVec;

use crate::{
    cs::Place,
    dag::{
        guide::{GuideLoc, OrderInfo},
        primitives::{OrderIx, ResolverIx},
        resolver_box::Resolver,
        TrackId,
    },
    field::SmallField,
    log,
    utils::{DilatoryPrinter, PipeOp, UnsafeCellEx},
};

use super::{ResolverCommonData, ResolverComms};

#[derive(PartialEq, Eq, Debug)]
enum ResolverState {
    Pending,
    Enqueued,
    Done,
}

#[derive(Debug)]
struct OrderBufferItem {
    order_info: OrderInfo<ResolverIx>,
    state: ResolverState,
}

#[derive(Default, Debug)]
struct ResolutionWindowStats {
    total_control_iterations: u64,
    total_consumption: u64,
    total_time: Duration,
}

const CHANNEL_SIZE: usize = 2048;

pub trait RWConfig<T: TrackId> {
    type TrackId: TrackId = T;
    const ASSERT_TRACKED_VALUES: bool;
}

pub struct RWConfigPlayback<T>(PhantomData<T>);
impl RWConfig<OrderIx> for RWConfigPlayback<OrderIx> {
    type TrackId = OrderIx;
    const ASSERT_TRACKED_VALUES: bool = false;
}

pub struct RWConfigRecord<T>(PhantomData<T>);
impl RWConfig<GuideLoc> for RWConfigRecord<GuideLoc> {
    type TrackId = GuideLoc;
    const ASSERT_TRACKED_VALUES: bool = true;
}

pub(crate) struct ResolutionWindow<V, T: TrackId, Cfg: RWConfig<T>> {
    /// Represents a sliding window over the execution order.
    range: Range<usize>,
    exec_order_buffer: VecDeque<OrderBufferItem>,
    channel: Arc<LockStepChannel>,
    pool: Vec<JoinHandle<()>>,
    stats: ResolutionWindowStats,

    comms: Arc<ResolverComms>,
    common: Arc<ResolverCommonData<V, T>>,

    // Debugging
    /// Tracks tasks being sent and received by the control thread. Those are
    /// synchronized, so it splits any bugs into data race or logic error
    /// categories.
    track_list: Vec<(&'static str, Vec<Place>, Vec<Place>)>,

    /// Tracks the number of times each task is executed.
    /// This is used to detect tasks that are executed more than once or not at all.
    execution_list: Vec<u8>,
    phantom: PhantomData<Cfg>,
}

unsafe impl<V, T: TrackId, Cfg: RWConfig<T>> Send for ResolutionWindow<V, T, Cfg> {}

impl<V: SmallField + 'static, T: TrackId + 'static, Cfg: RWConfig<T> + 'static>
    ResolutionWindow<V, T, Cfg>
{
    pub(crate) fn run(
        comms: Arc<ResolverComms>,
        common: Arc<ResolverCommonData<V, T>>,
        debug_track: &[Place],
        threads: u32,
    ) -> JoinHandle<()> {
        assert!(threads <= 128, "Not enough primes for that, add additional primes to the channel. Don't forget to update this assert.");

        use rand::distributions::Alphanumeric;
        use rand::{thread_rng, Rng};

        let discriminant_affix: String = thread_rng()
            .sample_iter(&Alphanumeric)
            .take(4)
            .map(|x| x as char)
            .collect();

        let channel = Arc::new(LockStepChannel::new(threads as usize));

        let pool = (0..threads)
            .map(|i| {
                let receiver = LockStepWorker::new(i, channel.clone());

                let mut worker = Worker::<V, T, Cfg, CHANNEL_SIZE> {
                    receiver,
                    common: Arc::clone(&common),
                    debug_track: debug_track.to_vec(),
                    phantom: PhantomData,
                };

                let handle = std::thread::Builder::new()
                    .name(format!(
                        "CircuitResolver-{}-worker-{}",
                        discriminant_affix, i
                    ))
                    .spawn(move || worker.run())
                    .expect("Couldn't spawn resolver worker thread.");

                handle
            })
            .collect::<Vec<_>>();

        unsafe { (*channel.pool.get()) = pool.iter().map(|x| x.thread().clone()).collect_vec() };

        let this = Self {
            range: 0..0,
            exec_order_buffer: VecDeque::with_capacity(1 << 19),
            channel,
            pool,
            stats: ResolutionWindowStats::default(),

            common,
            comms,

            track_list: Vec::new(),
            execution_list: if cfg!(feature = "cr_paranoia_mode") {
                1 << 26
            } else {
                0
            }
            .to(|x| Vec::with_capacity(x).op(|v| v.resize(x, 0))),
            phantom: PhantomData,
        };

        std::thread::Builder::new()
            .name(format!("CircuitResolver-{}-broker", discriminant_affix))
            .spawn(move || unsafe {
                this.resolve();
            })
            .expect("Couldn't spawn resolution window broker thread.")
    }

    /// Processes all items currently in the buffer.
    fn process_buffer(&mut self) {
        while self.exec_order_buffer.len() > 0 {
            // Safety: the worker threads are parked, so we can safely access
            // the data.
            let data = unsafe { self.channel.data.u_deref_mut() };

            // We're limited by:
            let count =
                // Parallelism of the first task
                self.exec_order_buffer[0].order_info.metadata.parallelism()
                // Size of the channel
                .min(data.len() * LOCK_STEP_ELEM_SIZE)
                // Number of tasks in the buffer
                .min(self.exec_order_buffer.len());

            assert!(count > 0, "At least one task must be sent.");

            for (buffer_ix, data_ix) in (0..count).zip((0..data.len()).cycle()) {
                let task = &mut self.exec_order_buffer[buffer_ix];
                let order_ix = buffer_ix + self.range.start; // Absolute order index

                assert!(
                    task.state == ResolverState::Pending,
                    "Selected task to be executed is not pending."
                );

                task.state = ResolverState::Enqueued;

                data[data_ix].push(order_ix.into(), task.order_info.value);

                if cfg!(feature = "cr_paranoia_mode") {
                    self.execution_list[order_ix] += 1;

                    if self.execution_list[order_ix] > 1 {
                        let path = PathBuf::from("./crash.txt");
                        let mut file = std::fs::File::create(&path).unwrap();

                        for (state, inputs, outputs) in self.track_list.iter() {
                            writeln!(
                                file,
                                "{} inputs: {:?} outputs: {:?}",
                                state, inputs, outputs
                            )
                            .unwrap();
                        }

                        file.flush().unwrap();

                        panic!(
                            "Task {} is executed more than once. Details are in {:?}",
                            order_ix, path
                        );
                    }

                    let r = unsafe { self.common.resolvers.u_deref().get(task.order_info.value) };

                    self.track_list
                        .push(("in", r.inputs().to_vec(), r.outputs().to_vec()));
                }
            }

            if (cfg!(feature = "cr_paranoia_mode") || crate::dag::resolvers::mt::PARANOIA) && true {
                log!("RW: Batch! {} tasks.", count);
            }

            self.channel.execute();

            // Check if worker has paniced, mark the window as panicked and
            // end the resolution.
            if let Some(panic) = self.channel.get_panic() {
                self.comms.rw_panic.set(Some(panic));
                self.comms
                    .rw_panicked
                    .store(true, std::sync::atomic::Ordering::Relaxed);
                return;
            }

            // Mark the tasks as done. Items are processed in order, so we can
            // just those that are marked as enqueued.
            // Other option is to use count. Idk which one is faster and it's
            // not a big enough difference to benchmark it.
            self.exec_order_buffer
                .iter_mut()
                .take_while(|x| x.state == ResolverState::Enqueued)
                .for_each(|x| {
                    x.state = ResolverState::Done;

                    if cfg!(feature = "cr_paranoia_mode") || crate::dag::resolvers::mt::PARANOIA {
                        unsafe {
                            let r = self.common.resolvers.u_deref().get(x.order_info.value);

                            self.track_list.push((
                                "out",
                                r.inputs().to_vec(),
                                r.outputs().to_vec(),
                            ));

                            // Note that perhaps there's something missing in this assert as it has
                            // failed before while the resolution worked fine.
                            r.outputs().iter().for_each(|p| {
                                assert!(
                                    self.common
                                        .values
                                        .u_deref()
                                        .get_item_ref(*p)
                                        .1
                                        .is_resolved(),
                                    "Not seeing as resolved (Data race?)."
                                );
                            })
                        }
                    }
                });

            if cfg!(feature = "cr_paranoia_mode") || crate::dag::resolvers::mt::PARANOIA {
                if self
                    .exec_order_buffer
                    .iter()
                    .enumerate()
                    .take_while(|(_, x)| x.state == ResolverState::Done)
                    .any(|(i, _)| self.execution_list[i + self.range.start] < 1)
                {
                    panic!("Task was executed less than once.");
                }

                if self
                    .exec_order_buffer
                    .iter()
                    .enumerate()
                    .take_while(|(_, x)| x.state == ResolverState::Done)
                    .any(|(i, _)| self.execution_list[i + self.range.start] > 1)
                {
                    panic!("Task was executed more than once.");
                }
            }

            // Notify the awaiters.
            self.exec_order_buffer
                .iter()
                .take_while(|x| x.state == ResolverState::Done)
                .count()
                .to(|count| {
                    self.range = self.range.start + count..self.range.end;

                    let drained = self.exec_order_buffer.drain(..count);

                    let awaiters = &self.common.awaiters_broker;

                    drained
                        // WARNING: We're not allowed to touch the `resolve_fn` of
                        // the resolver, as it was already dropped. It is ok to
                        // instanciate the resolver itself, as the resolve_fn is not
                        // a field but a data written in the unsized tail of the
                        // resolver.
                        .flat_map(|x| unsafe {
                            self.common
                                .resolvers
                                .u_deref()
                                .get(x.order_info.value)
                                .outputs()
                        })
                        .map(|x| unsafe { self.common.values.u_deref().get_item_ref(*x).1.tracker })
                        .for_each(|x| awaiters.notify(x));

                    drop(awaiters);

                    if cfg!(feature = "cr_paranoia_mode") && count > 0 {
                        log!(
                            "RW: Shifted by {}, new range is: {}..{}, buffer len: {}",
                            count,
                            self.range.start,
                            self.range.end,
                            self.exec_order_buffer.len()
                        );
                    }
                });
        }
    }

    /// The function requires that `exec_order` is populated only by values from the
    /// `resolvers`.
    /// Also, the provided resolution functions must not ever confuse inputs with outputs.
    /// An output can't have the same key as any input to that function.
    pub unsafe fn resolve(mut self) {
        let start_instant = std::time::Instant::now();

        let mut transient_buffer = Vec::with_capacity(self.exec_order_buffer.capacity());
        let mut dp = DilatoryPrinter::new(); // Hehe

        loop {
            self.stats.total_control_iterations += 1;

            let registration_complete = self
                .comms
                .registration_complete
                .load(std::sync::atomic::Ordering::Relaxed);

            use std::sync::atomic::Ordering::Relaxed;

            let exec_order = self.common.exec_order.lock().unwrap();
            let limit = exec_order.size;

            if limit - self.range.end > 0 || registration_complete {
                // New resolvers were added since.

                let space_left = self.exec_order_buffer.capacity() - self.exec_order_buffer.len();
                let extend_to = cmp::min(limit, self.range.end + space_left);

                if extend_to > 0 {
                    dp.print(format!("Buffering resolvers, {} taken.", extend_to));
                }

                transient_buffer.extend_from_slice(&exec_order.items[self.range.end..extend_to]);

                drop(exec_order); // Release ASAP.

                debug_assert!(
                    transient_buffer.capacity() == self.exec_order_buffer.capacity(),
                    "Took more tasks than anticipated."
                );

                transient_buffer
                    .drain(..)
                    .map(|x| OrderBufferItem {
                        order_info: x,
                        state: ResolverState::Pending,
                    })
                    .to(|x| self.exec_order_buffer.extend(x));

                debug_assert!(transient_buffer.is_empty());

                self.range = self.range.start..extend_to;

                self.stats.total_consumption = extend_to as u64;

                if crate::dag::resolvers::mt::PARANOIA || cfg!(feature = "cr_paranoia_mode") {
                    log!(
                        "RW: Extended range by {}, new range {}..{}",
                        extend_to,
                        self.range.start,
                        self.range.end
                    );
                }
            } else {
                drop(exec_order);

                let mut iters = 0;
                loop {
                    let hint = self
                        .comms
                        .exec_order_buffer_hint
                        .compare_exchange(1, 0, Relaxed, Relaxed);

                    match hint {
                        Ok(_) => {
                            break;
                        }
                        _ => {
                            iters += 1;

                            if iters > (1 << 10) {
                                if self.comms.registration_complete.load(Relaxed) {
                                    break;
                                }

                                iters = 0;
                            }

                            yield_now();
                            continue;
                        }
                    }
                }
                continue;
            }

            let exec_order_len = self.exec_order_buffer.len();

            if registration_complete && exec_order_len == 0 && limit == self.range.end {
                break;
            }

            self.process_buffer();

            // This must happen strictly after the processing of the buffer, as
            // otherwise we may get into deadlock when new resolvers aren't
            // added cause the registration thread waits for some future or
            // already failed resolution.
            if self
                .comms
                .rw_panicked
                .load(std::sync::atomic::Ordering::Relaxed)
            {
                break;
            }
        }

        if crate::dag::resolvers::mt::PARANOIA || cfg!(feature = "cr_paranoia_mode") {
            log!("[{:?}] RW: Exit conditions met.", std::time::Instant::now())
        }

        self.channel.kill();

        self.pool.into_iter().for_each(|h| h.join().unwrap());

        self.stats.total_time = start_instant.elapsed();

        if cfg!(feature = "cr_paranoia_mode") || crate::dag::resolvers::mt::PARANOIA {
            log!("CR {:#?}", self.stats);
            log!("CR {:#?}", unsafe { &*self.channel.stats.get() });

            log!(
                "CR RW execution anomalies: over {}, under {}",
                self.execution_list.iter().filter(|x| **x > 1).count(),
                self.execution_list.iter().filter(|x| **x < 1).count()
            );
        }
    }
}

#[derive(Default, Debug)]
struct WorkerStats {
    total_tasks: u32,
    total_iterations: u32,
    active_iterations: u32,
    starving_iterations: u32,
}

struct Worker<V: Copy, T: TrackId, Cfg: RWConfig<T>, const SIZE: usize> {
    receiver: LockStepWorker,
    common: Arc<ResolverCommonData<V, T>>,
    debug_track: Vec<Place>,
    phantom: PhantomData<Cfg>,
}

unsafe impl<V: Copy, T: TrackId, Cfg: RWConfig<T>, const SIZE: usize> Send
    for Worker<V, T, Cfg, SIZE>
{
}
unsafe impl<V: Copy, T: TrackId, Cfg: RWConfig<T>, const SIZE: usize> Sync
    for Worker<V, T, Cfg, SIZE>
{
}

impl<V: SmallField, T: TrackId + 'static, Cfg: RWConfig<T>, const SIZE: usize>
    Worker<V, T, Cfg, SIZE>
{
    fn run(&mut self) {
        let mut stats = WorkerStats::default();

        {
            let mut stats = AssertUnwindSafe(&mut stats);
            let this = AssertUnwindSafe(&self);

            std::panic::catch_unwind(move || {
                loop {
                    stats.total_iterations += 1;

                    let tasks = this.receiver.wait_for_tasks();

                    if this.receiver.die_order() { break; }

                    if tasks.is_empty() == false {
                        stats.active_iterations += 1;
                        stats.total_tasks += tasks.len() as u32;
                    } else {
                        stats.starving_iterations += 1;
                    }

                    for (order_ix, resolver_ix) in tasks {

                        unsafe {
                            // Safety: This is the only call to the `get` function.  
                            // Warning: Don't ever change this access to mutable
                            // here, as this is an unsynchronizd access.
                            let resolver = this.common.resolvers.u_deref().get(*resolver_ix);

                            if cfg!(feature="cr_paranoia_mode") || crate::dag::resolvers::mt::PARANOIA {
                                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                    this.invoke(resolver, *order_ix);

                                })).unwrap_or_else(|_| {
                                    this.receiver.channel.panicked.store(true, std::sync::atomic::Ordering::Relaxed);

                                    let inputs = resolver.inputs();

                                    panic!(
                                        "Panic in resolution invocation. Order {:?}, resolver index {:?}', \
                                         input count {}, input ixs {:?}\nWorker stats:\n{:?}\n", 
                                        order_ix,
                                        resolver_ix,
                                        inputs.len(),
                                        inputs.iter().map(|x| format!("{:?}", x)).collect_vec(),
                                        stats)
                                })
                            }
                            else {
                                // Safety: The `resolve_fn()` wasn't called on the resolver.
                                this.invoke(resolver, *order_ix);
                            }
                        }

                    }

                    this.receiver.done();
                }

            })
            .unwrap_or_else(|panic| {
                self.receiver.panic(panic);
            });
        }

        if cfg!(feature = "cr_paranoia_mode") || crate::dag::resolvers::mt::PARANOIA {
            log!(
                "{}\n{:#?}\n{:#?}",
                std::thread::current().name().unwrap_or_default(),
                self.receiver.channel.stats,
                stats
            );
        }
    }

    /// Safety: `resolve_fn()` mustn't've been called on the resolver.
    unsafe fn invoke(&self, resolver: &Resolver, order_ix: OrderIx) {
        fence(std::sync::atomic::Ordering::Acquire);

        // Safety: Using `values` in an unsynchronized manner is safe, since we are
        // only getting items that are guaranteed to be already written and remain
        // immutable for entire execution except this very function.
        // Any out of order exection would not occur because the resolution window
        // thread mutex'es with the main thread and is synched with this worker.

        let ins_ixs = resolver.inputs();
        let out_ixs = resolver.outputs();

        if crate::dag::resolvers::mt::PARANOIA && false {
            let vs = self.common.values.u_deref();

            println!("RW: input ixs: {:#?}", ins_ixs);
            println!("RW: variables resolved");
            vs.variables
                .iter()
                .enumerate()
                .for_each(|(i, x)| println!("[{}] => r: {}", i, x.u_deref().1.is_resolved()));
        }

        let ins_vs: SmallVec<[_; 8]> = ins_ixs
            .iter()
            .map(|x| {
                let (vs, md) = self.common.values.u_deref().get_item_ref(*x);

                if cfg!(feature = "cr_paranoia_mode") || true {
                    if Cfg::ASSERT_TRACKED_VALUES {
                        assert!(md.is_tracked());
                    }
                    assert!(
                        md.is_resolved(),
                        "Not resolved at ix {:?}, order ix {:?}, thread {:?}",
                        x,
                        order_ix,
                        std::thread::current().name()
                    );
                }

                // Safety:
                // 1. Rust infers this clouse as FnMut, thus we can't return the
                // reference from the closure as it consumes `values`.
                //
                // 2. We also need to cast the references to consts as the
                // resolution function expects constant inputs. The cast is safe
                // since the items we pick up are guaranteed to be distinct between
                // all active resolvers. All resolvers that write to those items
                // have already done so, due to the exection ordering.
                *(vs as *const V)
            })
            .collect();

        let (mut out_vs, mut mds): (SmallVec<[_; 8]>, SmallVec<[_; 8]>) = out_ixs
            .iter()
            .map(|x| {
                // Safety: getting mutable refs here is ok because they are puller
                // for a globally unique `x`.
                let (vs, md) = self.common.values.u_deref().get_item_ref_mut(*x);

                assert!(
                    md.is_resolved() == false,
                    "Already resolved at ix {:?}, thread {:?}",
                    x,
                    std::thread::current().name()
                );

                // Safety:
                // 1. Same as inputs.
                // 2. Must not point to any input.
                (&mut *(vs as *mut _), md)
            })
            .unzip();

        let mut track = false;

        if cfg!(feature = "cr_paranoia_mode") || crate::dag::resolvers::mt::PARANOIA {
            if let Some(x) = self
                .debug_track
                .iter()
                .find(|x| resolver.inputs().contains(x))
            {
                log!(
                    "RW: invoking at ix {:?} with tracked input {:?}",
                    order_ix,
                    x
                );

                track = true;
            }

            if let Some(x) = self
                .debug_track
                .iter()
                .find(|x| resolver.outputs().contains(x))
            {
                log!(
                    "RW: invoking at ix {:?} with with tracked output {:?}",
                    order_ix,
                    x
                );

                track = true;
            }

            if track {
                log!(
                    "   Ins:\n   - {}\n   Outs:\n   - {}",
                    resolver
                        .inputs()
                        .iter()
                        .map(|x| format!(
                            "{:?} : {:?}",
                            x,
                            self.common.values.u_deref().get_item_ref(*x).0.as_raw_u64()
                        ))
                        .collect_vec()
                        .join("\n   - "),
                    resolver
                        .outputs()
                        .iter()
                        .map(|x| format!("{:?}", x))
                        .collect_vec()
                        .join("\n   - ")
                );
            }
        }

        let bind_fn = std::mem::transmute::<_, fn(&Resolver, &[V], &mut [&mut V], bool)>(
            resolver.bind_fn_ptr(),
        );
        bind_fn(resolver, ins_vs.as_slice(), out_vs.as_mut_slice(), track);

        fence(std::sync::atomic::Ordering::Release);

        mds.iter_mut().for_each(|x| x.mark_resolved());
    }
}

const LOCK_STEP_ELEM_SIZE: usize = 8;

#[derive(Debug, Clone)]
struct LockStepElement {
    count: usize,
    items: [(OrderIx, ResolverIx); LOCK_STEP_ELEM_SIZE],
    done: bool,
}

impl LockStepElement {
    fn new() -> Self {
        Self {
            count: 0,
            items: [(0u32.into(), ResolverIx::new_resolver(0)); LOCK_STEP_ELEM_SIZE],
            done: false,
        }
    }

    fn push(&mut self, order_ix: OrderIx, resolver_ix: ResolverIx) {
        self.items[self.count] = (order_ix, resolver_ix);
        self.count += 1;
    }

    fn clear(&mut self) {
        self.count = 0;
        self.done = false;
    }
}

#[derive(Debug, Clone)]
struct LockStepChannelStats {
    total_iterations: usize,
    execute_wait_loops: usize,
}

const LOCK_STEP_STATE_WRITING: usize = 0;
const LOCK_STEP_STATE_FREE: usize = 1;
const PRIMES: [usize; 128] = [
    // 128 cores sounds large enough.
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
    197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
    311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
    431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547,
    557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
    661, 673, 677, 683, 691, 701, 709, 719,
];

struct LockStepChannel {
    lock_state: AtomicUsize,
    lock_correlation: AtomicUsize,
    park_workers: AtomicBool,
    data: UnsafeCell<Vec<LockStepElement>>,
    die_order: AtomicBool,
    pool: UnsafeCell<Vec<Thread>>,
    stats: UnsafeCell<LockStepChannelStats>,
    panicked: AtomicBool,
    panic: Mutex<Option<Box<dyn Any + Send>>>,
}

impl LockStepChannel {
    fn new(worker_cnt: usize) -> Self {
        Self {
            lock_state: AtomicUsize::new(LOCK_STEP_STATE_WRITING),
            lock_correlation: AtomicUsize::new(0),
            park_workers: AtomicBool::new(true),

            data: Vec::with_capacity(worker_cnt)
                .op(|x| x.resize(worker_cnt, LockStepElement::new()))
                .to(UnsafeCell::new),

            die_order: AtomicBool::new(false),
            pool: UnsafeCell::new(Vec::new()),

            stats: LockStepChannelStats {
                total_iterations: 0,
                execute_wait_loops: 0,
            }
            .to(UnsafeCell::new),

            panicked: AtomicBool::new(false),
            panic: Mutex::new(None),
        }
    }

    /// Releases the batch of tasks that is already written to the channel and
    /// waits for the workers to complete it.
    fn execute(&self) {
        use std::sync::atomic::Ordering::*;

        if (cfg!(feature = "cr_paranoia_mode") || crate::dag::resolvers::mt::PARANOIA) && false {
            log!("RW: batch sent {:#?}", unsafe { self.data.u_deref() });
        }

        unsafe { self.stats.u_deref_mut().total_iterations += 1 };

        self.lock_correlation.fetch_add(1, Relaxed);
        self.lock_state.store(LOCK_STEP_STATE_FREE, Relaxed);
        self.park_workers.store(false, Release);

        unsafe { self.pool.u_deref().iter().for_each(|x| x.unpark()) }

        unsafe {
            for i in (0..self.data.u_deref().len()).rev() {
                while self.data.u_deref()[i].done == false {
                    spin_loop();
                }
            }
        }

        self.lock_state.store(LOCK_STEP_STATE_WRITING, Relaxed);
        fence(Acquire); // TODO: Do we need this? `data` is only written in this thread.

        // self.batch_done_res.store(1, Relaxed);
        unsafe { self.data.u_deref_mut().iter_mut().for_each(|x| x.clear()) };
    }

    /// Gets the panic value if any.
    fn get_panic(&self) -> Option<Box<dyn Any + Send>> {
        use std::sync::atomic::Ordering::*;

        // It is theoretically possible to not use atomic here, which will save
        // us total operation order for the CPU, but it can be hard to
        // implement. It can be beneficial, since this function is called 1m+
        // times per circuit (7-9 secs on M1, but can and will be faster).
        // Isn't it only an issue on ARM?
        // TODO: see asm for x86_64.
        if self.panicked.load(Relaxed) {
            Some(self.panic.lock().unwrap().take().unwrap())
        } else {
            None
        }
    }

    /// Sends kill order to all workers.
    fn kill(&self) {
        use std::sync::atomic::Ordering::*;

        self.die_order.store(true, Relaxed);
        self.park_workers.store(false, Relaxed);

        unsafe { self.pool.u_deref().iter().for_each(|x| x.unpark()) }
    }
}

#[derive(Debug, Clone)]
struct LockStepWorkerStats {
    lock_loops: usize,
    correlation_loops: usize,
    park_loops: usize,
    tasks_received: usize,
    tasks_done: usize,
}

struct LockStepWorker {
    id: u32,
    channel: Arc<LockStepChannel>,
    lock_correlation: Cell<usize>,
    stats: UnsafeCell<LockStepWorkerStats>,
}

impl LockStepWorker {
    fn new(id: u32, channel: Arc<LockStepChannel>) -> Self {
        Self {
            id,
            channel,
            lock_correlation: Cell::new(0),
            stats: LockStepWorkerStats {
                lock_loops: 0,
                correlation_loops: 0,
                park_loops: 0,
                tasks_received: 0,
                tasks_done: 0,
            }
            .to(UnsafeCell::new),
        }
    }

    /// Waits for the next batch of tasks to be released, and returns
    /// a reference to its assigned tasks.
    fn wait_for_tasks(&self) -> &[(OrderIx, ResolverIx)] {
        use std::sync::atomic::Ordering::*;

        loop {
            if self.channel.park_workers.load(Relaxed) {
                unsafe { self.stats.u_deref_mut().park_loops += 1 };
                park();

                // In case of phantom unpark we don't want to
                // attempt/check any state transitions.
                continue;
            }

            if self.channel.die_order.load(Relaxed) {
                return unsafe { &self.channel.data.u_deref()[self.id as usize].items[0..0] };
            }

            if self.lock_correlation.get() == self.channel.lock_correlation.load(Relaxed) {
                unsafe { self.stats.u_deref_mut().correlation_loops += 1 };
                spin_loop();
                continue;
            }

            if self.channel.lock_state.load(Relaxed) != LOCK_STEP_STATE_FREE {
                unsafe { self.stats.u_deref_mut().lock_loops += 1 };
                spin_loop();
                continue;
            }

            break;
        }

        fence(Acquire);

        let new_lock_correlation = self.channel.lock_correlation.load(Relaxed);

        assert_eq!(
            self.lock_correlation.get(),
            new_lock_correlation - 1,
            "Correlation mismatch: current {}, new {}, in worker {}.\n{:#?}",
            self.lock_correlation.get(),
            new_lock_correlation,
            self.id,
            unsafe { self.stats.u_deref() }
        );

        self.lock_correlation.set(new_lock_correlation);

        let data = unsafe { &*self.channel.data.get() };
        let elem = &data[self.id as usize];

        unsafe { self.stats.u_deref_mut() }.tasks_received += elem.count;

        let r = elem.items[..elem.count].as_ref();

        r
    }

    /// Marks the current batch of tasks as completed.
    fn done(&self) {
        use std::sync::atomic::Ordering::*;

        unsafe {
            self.stats.u_deref_mut().tasks_done +=
                self.channel.data.u_deref()[self.id as usize].count
        };

        fence(Release);
        unsafe { self.channel.data.u_deref_mut()[self.id as usize].done = true };
    }

    /// Notifies the channel that this worker has panicked.
    fn panic(&mut self, panic: Box<dyn Any + Send>) {
        use std::sync::atomic::Ordering::*;

        let mut channel_panic = self.channel.panic.lock().unwrap();

        if channel_panic.is_none() {
            *channel_panic = Some(panic);
            self.channel.panicked.store(true, Relaxed);
        }

        // Dropping cause we're notifying the controller on the next line
        // and I don't want to think how the channel will behave if we
        // notify while holding the lock.
        drop(channel_panic);

        // We need to notify the controller that we're done, otherwise
        // it will wait forever.
        self.done();
    }

    fn die_order(&self) -> bool {
        use std::sync::atomic::Ordering::*;

        self.channel.die_order.load(Relaxed)
    }
}
