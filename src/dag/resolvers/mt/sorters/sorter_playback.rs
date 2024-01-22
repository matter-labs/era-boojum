use std::{
    cell::UnsafeCell,
    marker::PhantomData,
    sync::{Arc, Mutex},
};

use crate::{
    config::CSResolverConfig,
    cs::Place,
    dag::{
        awaiters::AwaitersBroker,
        guide::{GuideMetadata, OrderInfo, RegistrationNum},
        primitives::{ExecOrder, Metadata, OrderIx, ResolverIx, Values},
        resolver_box::{invocation_binder, ResolverBox},
        resolvers::mt::{ResolverCommonData, ResolverComms},
    },
    field::SmallField,
    utils::{PipeOp, UnsafeCellEx},
};

use super::{ResolutionRecord, ResolutionRecordItem, ResolutionRecordSource, ResolverSortingMode};

struct OrderBufferItem {
    resolver_ix: ResolverIx,
    record_item: ResolutionRecordItem,
}

pub struct PlaybackResolverSorter<F, Rrs: ResolutionRecordSource, Cfg> {
    common: Arc<ResolverCommonData<F, OrderIx>>,
    comms: Arc<ResolverComms>,
    exec_order_buffer: Vec<OrderBufferItem>,
    record: Rrs,
    registrations_added: usize,
    phantom: PhantomData<Cfg>,
}

impl<F: SmallField, Rrs: ResolutionRecordSource, Cfg: CSResolverConfig>
    PlaybackResolverSorter<F, Rrs, Cfg>
{
    #[inline(always)]
    fn write_buffer(&mut self, size_override: Option<usize>) {
        let mut exec_order = self.common.exec_order.lock().unwrap();

        for i in &self.exec_order_buffer {
            exec_order.items[usize::from(i.record_item.order_ix)] = OrderInfo::new(
                i.resolver_ix,
                GuideMetadata::new(i.record_item.parallelism, 0, 0),
            )
        }

        exec_order.size = match size_override {
            None => match self.registrations_added == self.record.get().registrations_count {
                false => self.record.get().items[self.registrations_added - 1].order_len,
                true => self.record.get().registrations_count,
            },
            Some(x) => x,
        };

        self.comms
            .exec_order_buffer_hint
            .store(1, std::sync::atomic::Ordering::Relaxed);

        if crate::dag::resolvers::mt::PARANOIA {
            println!(
                "RS_P: buffer written, {} item, size: {}",
                self.exec_order_buffer.len(),
                exec_order.size
            );
        }

        self.exec_order_buffer.clear();
    }
}

impl<F: SmallField, Rrs: ResolutionRecordSource, Cfg: CSResolverConfig> ResolverSortingMode<F>
    for PlaybackResolverSorter<F, Rrs, Cfg>
{
    type Arg = Rrs;
    type Config = crate::dag::resolvers::mt::resolution_window::RWConfigPlayback<OrderIx>;
    type TrackId = OrderIx;

    fn new(
        arg: Self::Arg,
        comms: Arc<ResolverComms>,
        _debug_track: &[Place],
    ) -> (Self, Arc<ResolverCommonData<F, OrderIx>>) {
        fn new_values<V>(size: usize, default: fn() -> V) -> Box<[V]> {
            // TODO: ensure mem-page multiple capacity.
            let mut values = Vec::with_capacity(size);
            // TODO: If this isn't reused extend should be switched to unsafe resize
            values.resize_with(size, default);
            values.into_boxed_slice()
        }

        let rrs = arg;

        let record = rrs.get();

        let values = Values {
            variables: new_values(record.values_count, || {
                UnsafeCell::new((F::from_u64_unchecked(0), Metadata::default()))
            }),
            // We know that all values are ultimately tracked, since otherwise
            // the record wouldn't've been created.
            // max_tracked: record.values_count as i64 - 1,
            max_tracked: -1,
        };

        let exec_order = ExecOrder {
            size: 0,
            items: Vec::with_capacity(record.registrations_count).op(|x| {
                x.resize(
                    record.items.len(),
                    OrderInfo::new(ResolverIx::default(), GuideMetadata::default()),
                )
            }),
        };

        let common = ResolverCommonData {
            resolvers: UnsafeCell::new(ResolverBox::new()),
            values: UnsafeCell::new(values),
            exec_order: Mutex::new(exec_order),
            awaiters_broker: AwaitersBroker::new(),
        }
        .to(Arc::new);

        let buf_size = std::env::var("BOOJUM_PRS_BUF_SIZE")
            .map_err(|_| "")
            .and_then(|x| x.parse().map_err(|_| ""))
            .unwrap_or(1 << 10);

        let s = Self {
            common,
            comms,
            record: rrs,
            exec_order_buffer: Vec::with_capacity(buf_size),
            registrations_added: 0,
            phantom: PhantomData,
        };

        let c = Arc::clone(&s.common);

        (s, c)
    }

    fn set_value(&mut self, key: Place, value: F) {
        // NOTE: Common with other sorter
        // Safety: Dereferencing as &mut in mutable context. This thread doesn't hold any
        // references to `self.resolvers`. Other thread may hold shared references, but
        // are guaranteed to not access the same underlying data.
        let values = unsafe { self.common.values.u_deref_mut() };

        values.set_value(key, value);
    }

    fn add_resolution<Fn>(
        &mut self,
        inputs: &[crate::cs::Place],
        outputs: &[crate::cs::Place],
        f: Fn,
    ) where
        Fn: FnOnce(&[F], &mut crate::cs::traits::cs::DstBuffer<'_, '_, F>) + Send + Sync,
    {
        let record = &self.record.get().items[self.registrations_added];

        let values = unsafe { self.common.values.u_deref_mut() };

        // Safety: This thread is the only one to use `push` on the resolvers
        // and is the only thread to do so. `push` is the only mutable function
        // on that struct.
        let resolver_ix = unsafe {
            self.common.resolvers.u_deref_mut().push(
                inputs,
                outputs,
                self.registrations_added as RegistrationNum,
                f,
                invocation_binder::<Fn, F>,
            )
        };

        // TODO: Change OrderInfo such that unrelated data is not stored along.
        self.exec_order_buffer.push(OrderBufferItem {
            resolver_ix,
            record_item: record.clone(),
        });

        // Without the additions, awaiters for 0th resolver would resolve immediately.
        values.track_values(outputs, record.order_ix + 1);

        self.registrations_added += 1;

        // TODO: Check if branch hints are needed.
        if self.exec_order_buffer.len() == self.exec_order_buffer.capacity() {
            self.write_buffer(None);
        }
    }

    fn internalize(
        &mut self,
        _resolver_ix: ResolverIx,
        _inputs: &[crate::cs::Place],
        _outputs: &[crate::cs::Place],
        _added_at: RegistrationNum,
    ) {
        todo!()
    }

    fn internalize_one(
        &mut self,
        _resolver_ix: ResolverIx,
        _inputs: &[crate::cs::Place],
        _outputs: &[crate::cs::Place],
        _added_at: RegistrationNum,
    ) -> Vec<ResolverIx> {
        todo!()
    }

    fn flush(&mut self) {
        self.write_buffer(None);
    }

    fn final_flush(&mut self) {
        self.write_buffer(Some(self.record.get().registrations_count));
    }

    fn retrieve_sequence(&mut self) -> &ResolutionRecord {
        self.record.get()
    }

    fn write_sequence(&mut self) {}
}
