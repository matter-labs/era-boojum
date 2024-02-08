use std::{cell::UnsafeCell, collections::VecDeque, marker::PhantomData};

use smallvec::SmallVec;

use crate::{
    config::{CSDebugConfig, CSResolverConfig},
    cs::{
        traits::cs::{CSWitnessSource, DstBuffer},
        Place,
    },
    dag::{
        awaiters::ImmediateAwaiter,
        primitives::{Metadata, OrderIx, ResolverIx, Values},
        resolver_box::{invocation_binder, Resolver, ResolverBox},
        CircuitResolver, WitnessSource, WitnessSourceAwaitable,
    },
    field::SmallField,
    utils::PipeOp as _,
};

pub struct StCircuitResolverParams {
    pub max_variables: usize,
}

impl From<usize> for StCircuitResolverParams {
    fn from(value: usize) -> Self {
        Self::new(value)
    }
}

impl StCircuitResolverParams {
    pub fn new(max_variables: usize) -> Self {
        Self { max_variables }
    }
}

#[derive(Default)]
struct Stats {
    resolvers_added: u32,
}

pub struct StCircuitResolver<F, CFG: CSResolverConfig> {
    values: Values<F, OrderIx>,
    deferrer: Deferrer,
    resolver_box: ResolverBox<F>,
    options: StCircuitResolverParams,
    stats: Stats,
    phantom: PhantomData<CFG>,
}

unsafe impl<F: SmallField, CFG: CSResolverConfig> Send for StCircuitResolver<F, CFG> {}
unsafe impl<F: SmallField, CFG: CSResolverConfig> Sync for StCircuitResolver<F, CFG> {}

impl<F, CFG> WitnessSource<F> for StCircuitResolver<F, CFG>
where
    F: SmallField,
    CFG: CSResolverConfig,
{
    const PRODUCES_VALUES: bool = true;

    fn try_get_value(&self, variable: crate::cs::Place) -> Option<F> {
        let (v, md) = self.values.get_item_ref(variable);

        match md.is_resolved() {
            true => Some(*v),
            false => None,
        }
    }

    fn get_value_unchecked(&self, variable: crate::cs::Place) -> F {
        let (r, md) = self.values.get_item_ref(variable);

        if CFG::DebugConfig::PERFORM_RUNTIME_ASSERTS {
            debug_assert!(
                md.is_resolved(),
                "Attempted to get value of unresolved variable."
            );
        }

        *r
    }
}

impl<F, CFG> WitnessSourceAwaitable<F> for StCircuitResolver<F, CFG>
where
    F: SmallField,
    CFG: CSResolverConfig,
{
    type Awaiter<'a> = ImmediateAwaiter;

    fn get_awaiter<const N: usize>(&mut self, vars: [crate::cs::Place; N]) -> Self::Awaiter<'_> {
        if CFG::DebugConfig::PERFORM_RUNTIME_ASSERTS {
            assert!(vars
                .iter()
                .all(|x| self.values.get_item_ref(*x).1.is_resolved()));
        }

        // TODO: check registrar is empty

        ImmediateAwaiter {}
    }
}

impl<F, CFG> CSWitnessSource<F> for StCircuitResolver<F, CFG>
where
    F: SmallField,
    CFG: CSResolverConfig,
{
}

impl<F: SmallField, CFG: CSResolverConfig> StCircuitResolver<F, CFG> {
    fn defer<Fn>(
        &mut self,
        inputs: &[crate::cs::Place],
        outputs: &[crate::cs::Place],
        f: Fn,
    ) -> Place
    where
        Fn: FnOnce(&[F], &mut crate::cs::traits::cs::DstBuffer<'_, '_, F>) + Send + Sync,
    {
        let resolver_ix = self.resolver_box.push(
            inputs,
            outputs,
            self.stats.resolvers_added,
            f,
            invocation_binder::<Fn, F>,
        );

        let place = inputs.iter().max_by_key(|x| x.0).unwrap();

        self.deferrer.defer(resolver_ix, *place);

        *place
    }

    fn invoke_closure<Fn>(
        &mut self,
        inputs: &[crate::cs::Place],
        outputs: &[crate::cs::Place],
        f: Fn,
    ) where
        Fn: FnOnce(&[F], &mut crate::cs::traits::cs::DstBuffer<'_, '_, F>) + Send + Sync,
    {
        let ins_vs: SmallVec<[_; 8]> = inputs
            .iter()
            .map(|x| self.values.get_item_ref(*x).0)
            .collect();

        let (mut out_vs, out_mds): (SmallVec<[_; 8]>, SmallVec<[_; 8]>) = outputs
            .iter()
            .map(|x| unsafe { self.values.get_item_ref_mut(*x) })
            .map(|(v, md)| (v, md))
            .unzip();

        f(
            ins_vs.as_slice(),
            &mut DstBuffer::MutSliceIndirect(out_vs.as_mut_slice(), false, 0),
        );

        out_mds
            .into_iter()
            .for_each(|x| *x = Metadata::new_resolved());
        drop(out_vs);
        self.values.advance_track();
    }

    /// **Safety:** resolver must have never had its bind_fn referenced.
    unsafe fn invoke_boxed(&mut self, resolver: &Resolver) {
        let ins_ixs = resolver.inputs();
        let out_ixs = resolver.outputs();

        let ins_vs: SmallVec<[_; 8]> = ins_ixs
            .iter()
            .map(|x| {
                let (v, md) = self.values.get_item_ref(*x);

                if CFG::DebugConfig::PERFORM_RUNTIME_ASSERTS {
                    assert!(md.is_resolved());
                }

                *v
            })
            .collect();

        let (mut out_vs, out_mds): (SmallVec<[_; 8]>, SmallVec<[_; 8]>) = out_ixs
            .iter()
            .map(|x| {
                let (v, md) = self.values.get_item_ref_mut(*x);

                if CFG::DebugConfig::PERFORM_RUNTIME_ASSERTS {
                    assert!(md.is_resolved() == false);
                }

                (v, md)
            })
            .unzip();

        let bind_fn = std::mem::transmute::<_, fn(&Resolver, &[F], &mut [&mut F], bool)>(
            resolver.bind_fn_ptr(),
        );
        bind_fn(resolver, ins_vs.as_slice(), out_vs.as_mut_slice(), false);

        out_mds
            .into_iter()
            .for_each(|x| *x = Metadata::new_resolved());
        drop(out_vs);
        self.values.advance_track();
    }

    fn advance(&mut self) {
        while let Some(resolver_ix) = self
            .deferrer
            .try_take(Place(self.values.max_tracked as u64))
        {
            // Safety: `resolver_ix` is provided from the deferrer which got it in the from the
            // resolver_box in the `defer` function.
            let resolver = unsafe { self.resolver_box.get(resolver_ix) };

            // Unbind `resolver` lifetime from `self` so it could be reborrowed.
            // Safety: `resolver` is going to be dropped at the end of this iteration. This
            // reference is the only existing reference to it. `invoke_boxed` doesn't use the
            // `resolver_box`.
            let resolver = unsafe { &*(resolver as *const _) };

            // Safety: This resolver hasn't yet been invoked and it's `bind_fn_ptr` hasn't been
            // called.
            unsafe { self.invoke_boxed(resolver) };
        }
    }

    fn resolve<Fn>(&mut self, inputs: &[crate::cs::Place], outputs: &[crate::cs::Place], f: Fn)
    where
        Fn: FnOnce(&[F], &mut crate::cs::traits::cs::DstBuffer<'_, '_, F>) + Send + Sync,
    {
        self.invoke_closure(inputs, outputs, f);

        self.advance();
    }
}

impl<F: SmallField, CFG: CSResolverConfig> CircuitResolver<F, CFG> for StCircuitResolver<F, CFG> {
    type Arg = StCircuitResolverParams;

    fn new(opts: Self::Arg) -> Self {
        let values = Values {
            variables: Vec::with_capacity(opts.max_variables)
                .op(|x| {
                    x.resize_with(opts.max_variables, || {
                        UnsafeCell::new((F::from_u64_unchecked(0), Metadata::default()))
                    })
                })
                .to(|x| x.into_boxed_slice()),
            max_tracked: -1,
        };

        Self {
            values,
            deferrer: Deferrer::new(),
            resolver_box: ResolverBox::new(),
            options: opts,
            stats: Stats::default(),
            phantom: PhantomData,
        }
    }

    fn set_value(&mut self, key: crate::cs::Place, value: F) {
        self.values.set_value(key, value);
        self.advance();
    }

    fn add_resolution<Fn>(
        &mut self,
        inputs: &[crate::cs::Place],
        outputs: &[crate::cs::Place],
        f: Fn,
    ) where
        Fn: FnOnce(&[F], &mut crate::cs::traits::cs::DstBuffer<'_, '_, F>) + Send + Sync,
    {
        let mut input_packs = inputs.iter().map(|x| self.values.get_item_ref(*x));

        if CFG::DebugConfig::PERFORM_RUNTIME_ASSERTS {
            assert!(outputs
                .iter()
                .all(|x| x.as_any_index() < self.options.max_variables as u64));

            assert!(inputs.iter().all(|i| outputs.contains(i) == false));
        }

        if input_packs.any(|(_, md)| md.is_resolved() == false) {
            self.defer(inputs, outputs, f);
        } else {
            self.resolve(inputs, outputs, f);
        }
    }

    fn wait_till_resolved(&mut self) {
        // No out of thread resolutions - nothing to do.

        // TODO: check registrar is empty
    }

    fn clear(&mut self) {}
}

struct Deferrer {
    resolvers: VecDeque<(Place, ResolverIx)>,
}

impl Deferrer {
    fn new() -> Self {
        Self {
            resolvers: VecDeque::new(),
        }
    }

    fn defer(&mut self, resolver_ix: ResolverIx, place: Place) {
        self.resolvers.push_back((place, resolver_ix));
    }

    fn try_take(&mut self, max_place: Place) -> Option<ResolverIx> {
        match self.resolvers.front() {
            Some((place, _)) if *place <= max_place => Some(self.resolvers.pop_front().unwrap().1),
            _ => None,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::dag::resolvers::StCircuitResolverParams;
    use crate::dag::*;
    use crate::{
        config::{CSConfig, DevCSConfig},
        cs::{traits::cs::DstBuffer, Place},
        dag::CircuitResolver,
        field::{goldilocks::GoldilocksField, U64Representable},
    };

    use super::StCircuitResolver;

    type F = GoldilocksField;
    type Cfg = <DevCSConfig as CSConfig>::ResolverConfig;

    fn new_f(x: u64) -> F {
        F::from_u64_unchecked(x)
    }

    #[test]
    fn resolves_init() {
        let mut resolver = StCircuitResolver::<F, Cfg>::new(StCircuitResolverParams::new(111));

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        resolver.set_value(Place(0), new_f(123));

        resolver.add_resolution(&[Place(0)], &[Place(1)], res_fn);

        assert!(resolver.try_get_value(Place(1)).is_some());
        assert!(resolver.get_value_unchecked(Place(1)) == new_f(123));
    }

    #[test]
    fn resolves_chain() {
        let mut resolver = StCircuitResolver::<F, Cfg>::new(StCircuitResolverParams::new(111));

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        resolver.set_value(Place(0), new_f(123));

        resolver.add_resolution(&[Place(0)], &[Place(1)], res_fn);
        resolver.add_resolution(&[Place(1)], &[Place(2)], res_fn);

        assert!(resolver.try_get_value(Place(2)).is_some());
        assert!(resolver.get_value_unchecked(Place(2)) == new_f(123));
    }

    #[test]
    fn resolves_delayed_set() {
        let mut resolver = StCircuitResolver::<F, Cfg>::new(StCircuitResolverParams::new(111));

        let res_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            outs.push(ins[0]);
        };

        resolver.add_resolution(&[Place(0)], &[Place(1)], res_fn);
        resolver.add_resolution(&[Place(1)], &[Place(2)], res_fn);
        resolver.set_value(Place(0), new_f(123));

        assert!(resolver.try_get_value(Place(2)).is_some());
        assert!(resolver.get_value_unchecked(Place(2)) == new_f(123));
    }
}
