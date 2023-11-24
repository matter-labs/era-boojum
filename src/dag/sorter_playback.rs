use std::{marker::PhantomData, sync::{Arc, Mutex}, cell::UnsafeCell, rc::Rc };

use crate::{field::SmallField, config::CSResolverConfig, cs::Place, dag::{resolver::{Values, Metadata, ExecOrder, OrderIx, ResolverIx}, resolver_box::ResolverBox, awaiters::AwaitersBroker, ResolutionRecordItem, guide::{OrderInfo, GuideMetadata}}, utils::{PipeOp, UnsafeCellEx}};

use super::{sorter_runtime::RuntimeResolverSorter, ResolverSorter, ResolutionRecordStorage, resolver::{CircuitResolverOpts, ResolverCommonData}, ResolutionRecord, resolution_window::invocation_binder, guide::RegistrationNum};

pub struct PlaybackResolverSorter<F, Rrs: ResolutionRecordStorage, Cfg> {
    common: Arc<ResolverCommonData<F>>,
    exec_order_buffer: Vec<OrderInfo<ResolverIx>>,
    record: Rc<ResolutionRecord>,
    registrations_added: usize,
    phantom: PhantomData<(Cfg, Rrs)>,
}

impl<F: SmallField, Rrs: ResolutionRecordStorage, Cfg: CSResolverConfig> PlaybackResolverSorter<F, Rrs, Cfg> {
    #[inline(always)]
    fn write_buffer(&mut self, size_override: Option<usize>) {
        let mut exec_order = self.common.exec_order.lock().unwrap();

        let order_len = exec_order.size;

        exec_order.items[order_len .. order_len + self.exec_order_buffer.len()]
            .copy_from_slice(&self.exec_order_buffer);

        match size_override {
            None => exec_order.size = self.record.items[self.registrations_added - 1].order_len,
            Some(x) => exec_order.size = x
        };

        self.exec_order_buffer.clear();
    }
}

impl<F: SmallField, Rrs: ResolutionRecordStorage, Cfg: CSResolverConfig> ResolverSorter<F> 
    for PlaybackResolverSorter<F, Rrs, Cfg> 
{
    type Arg = (Rrs, Rrs::Id);
    type Config = super::resolution_window::RWConfigPlayback;

    fn new(arg: Self::Arg, debug_track: &Vec<Place>) -> (Self, Arc<ResolverCommonData<F>>) {
        fn new_values<V>(size: usize, default: fn() -> V) -> Box<[V]> {
            // TODO: ensure mem-page multiple capacity.
            let mut values = Vec::with_capacity(size);
            // TODO: If this isn't reused extend should be switched to unsafe resize
            values.resize_with(size, default);
            values.into_boxed_slice()
        }

        let (rrs, id) = arg;

        let record = rrs.get(id);

        let values = Values {
            variables: new_values(record.values_count, || {
                UnsafeCell::new((F::from_u64_unchecked(0), Metadata::default()))
            }),
            max_tracked: -1,
        };

        let exec_order = ExecOrder {
            size: 0,
            items:
                Vec::with_capacity(record.registrations_count) 
                .op(|x| x.resize(
                    record.items.len(),
                    OrderInfo::new(
                        ResolverIx::default(),
                        GuideMetadata::default())))
        };

        let common = ResolverCommonData {
            resolvers: UnsafeCell::new(ResolverBox::new()),
            values: UnsafeCell::new(values),
            exec_order: Mutex::new(exec_order),
            awaiters_broker: AwaitersBroker::new(),
        }
        .to(Arc::new);

        let s = Self {
            common,
            record,
            exec_order_buffer: Vec::with_capacity(1 << 12),
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

    fn add_resolution<Fn>(&mut self, inputs: &[crate::cs::Place], outputs: &[crate::cs::Place], f: Fn)
    where
        Fn: FnOnce(&[F], &mut crate::cs::traits::cs::DstBuffer<'_, '_, F>) + Send + Sync {

        let record = &self.record.items[self.registrations_added];

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
                    self.registrations_added as RegistrationNum,
                    f,
                    invocation_binder::<Fn, F>)
        };

        // TODO: Change OrderInfo such that unrelated data is not stored along.
        self.exec_order_buffer.push(OrderInfo::new(resolver_ix, GuideMetadata::new(record.parallelism, 0, 0)));

        // TODO: Check if branch hints are needed.
        if self.exec_order_buffer.len() == self.exec_order_buffer.capacity() {
            self.write_buffer(None);
        }

        self.registrations_added += 1;
    }

    unsafe fn internalize(
        &mut self, 
        resolver_ix: super::resolver::ResolverIx,
        inputs: &[crate::cs::Place], 
        outputs: &[crate::cs::Place],
        added_at: super::guide::RegistrationNum) {
        todo!()
    }

    fn internalize_one(
        &mut self,
        resolver_ix: super::resolver::ResolverIx,
        inputs: &[crate::cs::Place],
        outputs: &[crate::cs::Place],
        added_at: super::guide::RegistrationNum
    ) -> Vec<super::resolver::ResolverIx> {
        todo!()
    }


    fn flush(&mut self) {
        self.write_buffer(None);
    }

    fn final_flush(&mut self) {
        self.write_buffer(Some(self.record.registrations_count));
    }

    fn retrieve_sequence(&mut self) -> &crate::dag::ResolutionRecord {
        &self.record
    }
}
