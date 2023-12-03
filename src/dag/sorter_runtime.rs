use std::{marker::PhantomData, sync::{Arc, Mutex, atomic::AtomicBool}, cell::{UnsafeCell, Cell}, thread::JoinHandle, panic::resume_unwind};

use itertools::Itertools;

use crate::{config::CSResolverConfig, field::SmallField, cs::{VariableType, Variable, Place, traits::cs::DstBuffer}, log, dag::{resolver::Metadata, resolution_window::invocation_binder, ResolutionRecordItem}, utils::{PipeOp, UnsafeCellEx}};

use super::{ResolverSorter, registrar::Registrar, guide::{BufferGuide, GuideOrder, OrderInfo, GuideMetadata, RegistrationNum, GuideLoc}, resolver::{ResolverIx, CircuitResolverOpts, PARANOIA, ResolverCommonData, Values, OrderIx, ExecOrder}, awaiters::AwaitersBroker, resolver_box::ResolverBox, ResolutionRecord};

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


pub(crate) struct Source;

// impl ResolverSorterSource for Source {
//     fn new<F: SmallField, Cfg: CSResolverConfig>(opts: CircuitResolverOpts) -> impl ResolverSorter<F> {
//         RuntimeResolverSorter::<F, Cfg>::new(opts)
//     }
// }

pub struct RuntimeResolverSorter<F:SmallField, Cfg: CSResolverConfig> {
    stats: Stats,
    options: CircuitResolverOpts,
    debug_track: Vec<Place>,
    pub(crate) common: Arc<ResolverCommonData<F, GuideLoc>>,
    pub(crate) registrar: Registrar,
    pub(crate) guide: BufferGuide<ResolverIx, F, Cfg>,
    record: ResolutionRecord,
    /// Tracks the size of the execution order written.
    order_len: usize,
    field: PhantomData<F>
}

impl<F: SmallField, Cfg: CSResolverConfig> RuntimeResolverSorter<F, Cfg> {

    fn write_order<'a, GO: GuideOrder<'a, ResolverIx>>(
        tgt: &Mutex<ExecOrder>,
        record: &mut ResolutionRecord,
        tgt_len: &mut usize,
        resolvers: &UnsafeCell<ResolverBox<F>>,
        order: &GO,
    ) {
        if order.size() > 0 {
            let mut exec_order = tgt.lock().unwrap();
            let mut tgt = &mut exec_order.items;
            let len = tgt.len();
            tgt.resize(
                len + order.size(),
                OrderInfo::new(ResolverIx::default(), GuideMetadata::new(0, 0, 0)),
            );

            order.write(&mut tgt[..]);

            for (i, nfo) in (&tgt[len..]).iter().enumerate() {
                let ri = &mut record.items[nfo.metadata.added_at() as usize];

                ri.added_at = nfo.metadata.added_at();
                ri.accepted_at = nfo.metadata.accepted_at();
                ri.order_ix = (i + len).into();
                ri.parallelism = nfo.metadata.parallelism() as u16;
            }

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
            
            // This value is an optimization, it is not behind a mutex and used on each
            // registration for record purposes.
            *tgt_len = tgt.len();

            exec_order.size = *tgt_len;
        }
    }
}

impl<F: SmallField, Cfg: CSResolverConfig> ResolverSorter<F> for RuntimeResolverSorter<F, Cfg> {
    type Arg = CircuitResolverOpts;
    type Config = super::resolution_window::RWConfigRecord<GuideLoc>;
    type TrackId = GuideLoc;

    fn new(opts: CircuitResolverOpts, debug_track: &Vec<Place>) -> (Self, Arc<ResolverCommonData<F, Self::TrackId>>) {

        fn new_values<V>(size: usize, default: fn() -> V) -> Box<[V]> {
            // TODO: ensure mem-page multiple capacity.
            let mut values = Vec::with_capacity(size);
            // TODO: If this isn't reused extend should be switched to unsafe resize
            values.resize_with(size, default);
            values.into_boxed_slice()
        }

        let values = Values {
            variables: new_values(opts.max_variables, || {
                UnsafeCell::new((F::from_u64_unchecked(0), Metadata::default()))
            }),
            max_tracked: -1,
        };

        let exec_order = ExecOrder { 
            size: 0, 
            items: Vec::with_capacity(opts.max_variables)
        };

        let common = ResolverCommonData {
            resolvers: UnsafeCell::new(ResolverBox::new()),
            values: UnsafeCell::new(values),
            exec_order: Mutex::new(exec_order),
            awaiters_broker: AwaitersBroker::new(),
        }
       .to(Arc::new);


        let s = Self {
            stats: Stats::new(),
            options: opts,
            debug_track: debug_track.clone(),
            common,
            record: ResolutionRecord::new(0, 0, opts.max_variables),
            guide: BufferGuide::new(opts.desired_parallelism),
            registrar: Registrar::new(),
            field: PhantomData,
            order_len: 0,
        };

        let c = Arc::clone(&s.common);

        (s, c)
    }

    fn set_value(&mut self, key: crate::cs::Place, value: F) {
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
                .map(|x| (x, rb.get(x).inputs(), rb.get(x).outputs(), rb.get(x).added_at()))
                // Safety: No &mut references to `self.common.resolvers`.
                .for_each(|(r, i, o, a)| self.internalize(r, i, o, a));
        }
    }

    fn add_resolution<Fn>(&mut self, inputs: &[Place], outputs: &[Place], f: Fn)
    where
        Fn: FnOnce(&[F], &mut DstBuffer<'_, '_, F>) + Send + Sync,
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
                .push(
                    inputs,
                    outputs,
                    self.stats.registrations_added as RegistrationNum,
                    f,
                    invocation_binder::<Fn, F>)
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
            unsafe {
                self.internalize(
                    resolver_ix, 
                    inputs, 
                    outputs, 
                    self.stats.registrations_added as RegistrationNum) 
            };
        }

        self.record.items[self.stats.registrations_added as usize].order_len = self.order_len;
        self.stats.registrations_added += 1;
    }

    unsafe fn internalize(
        &mut self,
        resolver_ix: ResolverIx,
        inputs: &[Place],
        outputs: &[Place],
        added_at: RegistrationNum) 
    {
        let mut resolvers = vec![(resolver_ix, inputs, outputs, added_at)];

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
            let (resolver_ix, inputs, outputs, added_at) = resolvers.pop().unwrap();

            let new_resolvers = self.internalize_one(resolver_ix, inputs, outputs, added_at);

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
                .map(|x| (x, rb.get(x).inputs(), rb.get(x).outputs(), rb.get(x).added_at()))
                .to(|x| resolvers.extend(x));
        }
    }

    fn internalize_one(
        &mut self,
        resolver_ix: ResolverIx,
        inputs: &[Place],
        outputs: &[Place],
        added_at: RegistrationNum,
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
            .push(
                resolver_ix,
                deps.map(|x| x.tracker).reduce(std::cmp::max),
                // This stat represents the registration in which this registration
                // had all its dependencies tracked and safe to use. Thus, once we
                // reach this registration in playback, the resolution window can
                // consume this resolver.
                // In recording mode we don't yet know what is the actual order index
                // the registration will have at this point.
                added_at,
                self.stats.registrations_added as RegistrationNum);

        Self::write_order(&self.common.exec_order, &mut self.record, &mut self.order_len, &self.common.resolvers, &order);

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


    fn flush(&mut self) {

        let order = self.guide.flush();

        Self::write_order(&self.common.exec_order, &mut self.record, &mut self.order_len, &self.common.resolvers, &order);

        drop(order);

        self.record.items[std::cmp::max(1, self.stats.registrations_added) as usize - 1].order_len = self.order_len;
    }

    fn final_flush(&mut self) {

        assert!(self.registrar.is_empty());
        // assert!(self.registrar.is_empty(), "Registrar is not empty: has {:?}", self.registrar.peek_vars());

        self.flush();

        self.record.items.resize_with(self.stats.registrations_added as usize, ResolutionRecordItem::default);

        for (i, item) in self.record.items[..].iter_mut().enumerate() {
            debug_assert_eq!(i, item.added_at as usize);

            // When the resolver is accepted at the same registration as it is being added, that
            // means that it has all dependencies tracked and will be placed in the exec order to
            // the left of it. If the resolver is accepted at later registration, the order size
            // for it will be covered by the immediately accepted resolver that it depends on.
            // if item.added_at == item.accepted_at {
            //     item.order_len = i + 1;
            // }
        }

        if cfg!(cr_paranoia_mode) || PARANOIA {
            log!(
                "CR: Final order written. Order len {}",
                self.common.exec_order.lock().unwrap().items.len()
            );
        }

        if cfg!(cr_paranoia_mode) || PARANOIA {
            self.guide.stats.finalize();

            log!("CR {:?}", self.guide.stats);
            log!("CRR stats {:#?}", self.registrar.stats);
        }
    }

    fn retrieve_sequence(&mut self) -> &ResolutionRecord {
        self.record.values_count = 1 + unsafe { self.common.values.u_deref().max_tracked } as usize;
        self.record.registrations_count = self.stats.registrations_added as usize;
        &self.record
    }
}
