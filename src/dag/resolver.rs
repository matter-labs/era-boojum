// Interferes with paranioa mode.
#![allow(clippy::overly_complex_bool_expr)]
#![allow(clippy::nonminimal_bool)]

use super::primitives::Values;
use super::{ResolverSortingMode, ResolutionRecord, TrackId, CircuitResolver, CircuitResolverOpts};
use crate::log;
use std::any::Any;
use std::cell::{Cell, UnsafeCell};
use std::fmt::{Display, Debug};
use std::marker::PhantomData;

use super::resolution_window::ResolutionWindow;
use super::{registrar::Registrar, WitnessSource, WitnessSourceAwaitable};
use crate::config::*;
use crate::cs::traits::cs::{CSWitnessSource, DstBuffer};
use crate::cs::{Place, Variable, VariableType};
use crate::dag::awaiters::AwaitersBroker;
use crate::dag::resolver_box::ResolverBox;
use crate::dag::{awaiters, guide::*};
use crate::field::SmallField;
use crate::utils::{PipeOp, UnsafeCellEx};
use itertools::Itertools;
use std::ops::{Add, Sub, AddAssign};
use std::panic::resume_unwind;
use std::sync::atomic::{fence, AtomicBool, AtomicIsize};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;


pub(crate) type Mutarc<T> = Arc<Mutex<T>>;





#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Default, Clone, Copy)]
pub struct OrderIx(u32);


impl From<u32> for OrderIx {
    fn from(value: u32) -> Self {
        Self(value)
    }
}

impl From<u64> for OrderIx {
    fn from(value: u64) -> Self {
        // This trait will not fail under normal circumstances.
        debug_assert!(value < u32::MAX as u64);
        Self(value as u32)
    }
}

impl From<usize> for OrderIx {
    fn from(value: usize) -> Self {
        // This trait will not fail under normal circumstances.
        debug_assert!(value < u32::MAX as usize);
        Self(value as u32)
    }
}

impl From<OrderIx> for u32 {
    fn from(value: OrderIx) -> Self {
        value.0
    }
}

impl From<OrderIx> for u64 {
    fn from(value: OrderIx) -> Self {
        value.0 as u64
    }
}

impl From<OrderIx> for usize {
    fn from(value: OrderIx) -> Self {
        value.0 as usize
    }
}

impl From<OrderIx> for isize {
    fn from(value: OrderIx) -> Self {
        value.0 as isize
    }
}

impl TrackId for OrderIx { }

impl Add<i32> for OrderIx {
    type Output = Self;

    fn add(self, rhs: i32) -> Self::Output {
        debug_assert!(rhs >= 0);
        OrderIx(self.0 + rhs as u32)
    }
}

impl AddAssign<i32> for OrderIx {
    fn add_assign(&mut self, rhs: i32) {
        *self = *self + rhs;
    }
}

impl Add<u32> for OrderIx {
    type Output = Self;

    fn add(self, rhs: u32) -> Self::Output {
        OrderIx(self.0 + rhs as u32)
    }
}

impl AddAssign<u32> for OrderIx {
        fn add_assign(&mut self, rhs: u32) {
        *self = *self + rhs;
    }
}


impl Add<usize> for OrderIx {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        debug_assert!(rhs < u32::MAX as usize);
        OrderIx(self.0 + rhs as u32)
    }
}

impl Sub for OrderIx {
    type Output = u32;

    fn sub(self, rhs: Self) -> Self::Output {
        self.0 - rhs.0
    }
}

pub struct ExecOrder {
    /// Represents the current size of the execution order. It is safe to execute the order up to
    /// this value.
    pub size: usize,
    /// The order itself. The `len` of the vector behaves differently in record and playback mode.
    /// Code agnostic to the mode can't rely on it.
    pub items: Vec<OrderInfo<ResolverIx>>
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



// region: ResolverIx

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct ResolverIx(pub u32);

pub enum ResolverIxType {
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



// endregion

#[cfg(test)]
mod test {
    use crate::{dag::{Awaiter, sorter_runtime::RuntimeResolverSorter, sorter_playback::PlaybackResolverSorter, ResolutionRecordStorage, CircuitResolverOpts, TestRecordStorage, resolvers::MtCircuitResolver}, utils::PipeOp};
    use std::{collections::VecDeque, hint::spin_loop, time::Duration, rc::Rc};

    use crate::{
        config::DoPerformRuntimeAsserts,
        cs::Variable,
        field::{goldilocks::GoldilocksField, Field},
    };

    use super::*;
    use super::super::sorter_runtime::*;

    type F = GoldilocksField;
    type CFG = Resolver<DoPerformRuntimeAsserts>;

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
        resolver: &mut MtCircuitResolver<F, RS, CFG>, limit: u64)
    {
        for i in 0..limit {
            let a = Place::from_variable(Variable::from_variable_index(i));

            resolver.set_value(a, F::from_u64_with_reduction(i));
        }
    }

    #[test]
    fn tracks_values_record_mode() {
        let limit = 10;
        let mut storage =
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(
                CircuitResolverOpts {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(
                CircuitResolverOpts {
                    max_variables: 10,
                    desired_parallelism: 16,
                });

        tracks_values_populate(&mut storage, limit);
        storage.wait_till_resolved();

        let rs = TestRecordStorage { record: Rc::new(storage.retrieve_sequence().clone()) };

        let mut storage =
            MtCircuitResolver::<
                F, 
                PlaybackResolverSorter<F, TestRecordStorage, CFG>, CFG>
            ::new(rs);

        tracks_values_populate(&mut storage, limit);

        for i in 0..limit {
            let a = Place::from_variable(Variable::from_variable_index(i));
            let v = storage.get_value_unchecked(a);

            assert_eq!(F::from_u64_with_reduction(i), v);
        }
    }

    fn resolves_populate<F: SmallField, RS: ResolverSortingMode<F>>(
        resolver: &mut MtCircuitResolver<F, RS, CFG>) -> (Place, Place)
    {

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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
    fn resolves_playback_mode() {
        let mut storage =
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let (_, _) = resolves_populate(&mut storage);

        storage.wait_till_resolved();

        let rs = TestRecordStorage { record: Rc::new(storage.retrieve_sequence().clone()) };

        println!("\n----- Recording finished -----\n");

        let mut storage =
            MtCircuitResolver::<
                F, 
                PlaybackResolverSorter<F, TestRecordStorage, CFG>, CFG>
            ::new(rs);

        let (init_var, dep_var) = resolves_populate(&mut storage);

        storage.wait_till_resolved();

        assert_eq!(
            storage.get_value_unchecked(init_var),
            storage.get_value_unchecked(dep_var)
        );
    }

    fn resolves_siblings_populate<F: SmallField, RS: ResolverSortingMode<F>>(
        resolver: &mut MtCircuitResolver<F, RS, CFG>) -> ((Place, Place), (Place, Place))
    {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        let ((init_var1, dep_var1), (init_var2, dep_var2)) 
            = resolves_siblings_populate(&mut storage);

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
        MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
            max_variables: 100,
            desired_parallelism: 16,
        });

        resolves_siblings_populate(&mut storage);

        storage.wait_till_resolved();

        let rs = TestRecordStorage { record: Rc::new(storage.retrieve_sequence().clone()) };

        let mut storage =
            MtCircuitResolver::<
                F, 
                PlaybackResolverSorter<F, TestRecordStorage, CFG>, CFG>
            ::new(rs);

        let ((init_var1, dep_var1), (init_var2, dep_var2)) 
            = resolves_siblings_populate(&mut storage);

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
        resolver: &mut MtCircuitResolver<F, RS, CFG>) -> Place
    {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
    // #[ignore = "temp"]
    fn resolves_descendants_playback_mode() {
        let mut storage =
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 2,
            });

        resolves_descendants_populate(&mut storage);

        storage.wait_till_resolved();

        let rs = TestRecordStorage { record: Rc::new(storage.retrieve_sequence().clone()) };

        let mut storage =
            MtCircuitResolver::<
                F, 
                PlaybackResolverSorter<F, TestRecordStorage, CFG>, CFG>
            ::new(rs);

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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
    fn awaiter_returns_for_resolved_value_record_mode() {
        let limit = 1 << 13;
        let mut storage =
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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

        // awaiter_returns_for_resolved_value_playback_mode_impl(2, 2);
        // awaiter_returns_for_resolved_value_playback_mode_impl(2, 20);
        // awaiter_returns_for_resolved_value_playback_mode_impl(2, 2048);
        awaiter_returns_for_resolved_value_playback_mode_impl(15, 2);
        awaiter_returns_for_resolved_value_playback_mode_impl(15, 20);
        awaiter_returns_for_resolved_value_playback_mode_impl(15, 2048);
    }

    fn awaiter_returns_for_resolved_value_playback_mode_impl(limit: usize, desired_parallelism: u32) {
        let limit = 1 << limit;
        let mut storage =
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
                max_variables: limit * 5,
                desired_parallelism,
            });

        populate(&mut storage, limit);

        storage.wait_till_resolved();

        let rs = TestRecordStorage { record: Rc::new(storage.retrieve_sequence().clone()) };

        let mut storage =
            MtCircuitResolver::<
                F, 
                PlaybackResolverSorter<F, TestRecordStorage, CFG>, CFG>
            ::new(rs);

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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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

        let rs = TestRecordStorage { record: Rc::new(storage.retrieve_sequence().clone()) };

        let mut storage =
            MtCircuitResolver::<
                F, 
                PlaybackResolverSorter<F, TestRecordStorage, CFG>, CFG>
            ::new(rs);

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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
    fn resolution_after_awaiter_is_supported_record_mode() {
        let mut storage =
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
        });

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var_1], res_fn);
        storage.add_resolution(&[dep_var_1], &[dep_var_2], res_fn);
        storage.get_awaiter([dep_var_2]).wait();
        storage.add_resolution(&[dep_var_2], &[dep_var_3], res_fn);

        storage.wait_till_resolved();

        let rs = TestRecordStorage { record: Rc::new(storage.retrieve_sequence().clone()) };

        let mut storage =
            MtCircuitResolver::<
                F, 
                PlaybackResolverSorter<F, TestRecordStorage, CFG>, CFG>
            ::new(rs);

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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var], res_fn);
        storage.try_get_value(dep_var);
        storage.wait_till_resolved();

        let rs = TestRecordStorage { record: Rc::new(storage.retrieve_sequence().clone()) };

        let mut storage =
            MtCircuitResolver::<
                F, 
                PlaybackResolverSorter<F, TestRecordStorage, CFG>, CFG>
            ::new(rs);

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var], res_fn);
        let result = storage.try_get_value(dep_var);

        assert_eq!(None, result);
    }

    #[test]
    fn try_get_value_returns_some_after_resolve_record_mode() {
        let mut storage =
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
        });

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var], res_fn);
        storage.wait_till_resolved();

        let rs = TestRecordStorage { record: Rc::new(storage.retrieve_sequence().clone()) };

        let mut storage =
            MtCircuitResolver::<
                F, 
                PlaybackResolverSorter<F, TestRecordStorage, CFG>, CFG>
            ::new(rs);

        storage.set_value(init_var, F::from_u64_with_reduction(123));
        storage.add_resolution(&[init_var], &[dep_var], res_fn);
        storage.wait_till_resolved();

        let result = storage.try_get_value(dep_var);

        assert_eq!(Some(F::from_u64_with_reduction(123)), result);
    }

    #[test]
    fn try_get_value_returns_some_after_wait_record_mode() {
        let mut storage =
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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

        let rs = TestRecordStorage { record: Rc::new(storage.retrieve_sequence().clone()) };

        let mut storage =
            MtCircuitResolver::<
                F, 
                PlaybackResolverSorter<F, TestRecordStorage, CFG>, CFG>
            ::new(rs);

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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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

        let record = storage.retrieve_sequence();

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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
                max_variables: 100,
                desired_parallelism: 16,
            });

        storage.set_value(var_4, F::from_u64_with_reduction(7));
        storage.add_resolution(&[var_3, var_4], &[var_5], res_fn);
        storage.add_resolution(&[var_1, var_2], &[var_3], res_fn);
        storage.set_value(var_2, F::from_u64_with_reduction(5));
        storage.set_value(var_1, F::from_u64_with_reduction(3));

        storage.wait_till_resolved();

        let rs = TestRecordStorage { record: Rc::new(storage.retrieve_sequence().clone()) };

        let mut storage =
            MtCircuitResolver::<
                F, 
                PlaybackResolverSorter<F, TestRecordStorage, CFG>, CFG>
            ::new(rs);

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
        resolver: &mut MtCircuitResolver<F, RS, CFG>, limit: usize)
    {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
                max_variables: limit * 5,
                desired_parallelism: 32,
            });

        correctness_simple_linear_populate(&mut storage, limit);

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

    #[test]
    fn correctness_simple_linear_playback_mode() {
        let limit = 1 << 10;

        let mut storage =
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
                max_variables: limit * 5,
                desired_parallelism: 32,
            });

        correctness_simple_linear_populate(&mut storage, limit);
        storage.wait_till_resolved();

        let rs = TestRecordStorage { record: Rc::new(storage.retrieve_sequence().clone()) };

        let mut storage =
            MtCircuitResolver::<
                F, 
                PlaybackResolverSorter<F, TestRecordStorage, CFG>, CFG>
            ::new(rs);

        correctness_simple_linear_populate(&mut storage, limit);

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


    fn populate<RS: ResolverSortingMode<F>>(storage: &mut MtCircuitResolver<F, RS, CFG>, limit: usize) {

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
        dag::{Awaiter, sorter_runtime::RuntimeResolverSorter, CircuitResolverOpts, resolvers::MtCircuitResolver},
        field::{goldilocks::GoldilocksField, Field},
    };
    type F = GoldilocksField;
    type CFG = Resolver<DoPerformRuntimeAsserts>;

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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
            MtCircuitResolver::<F, RuntimeResolverSorter<F, CFG>, CFG>::new(CircuitResolverOpts {
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
