use std::cell::UnsafeCell;
use std::ops::{Add, AddAssign, Sub};

use crate::cs::{Place, Variable};
use crate::utils::PipeOp as _;

use super::guide::OrderInfo;
use super::TrackId;

pub struct Values<V, T: Default> {
    pub(crate) variables: Box<[UnsafeCell<(V, Metadata<T>)>]>,
    pub(crate) max_tracked: i64, // Be sure to not overflow.
}

impl<V, T: Default + Copy> Values<V, T> {
    pub(crate) fn resolve_type(&self, _key: Place) -> &[UnsafeCell<(V, Metadata<T>)>] {
        &self.variables
    }

    pub(crate) fn get_item_ref(&self, key: Place) -> &(V, Metadata<T>) {
        let vs = self.resolve_type(key);
        unsafe { &(*vs[key.raw_ix()].get()) }
    }

    // Safety: No other mutable references to the same item are allowed.
    pub(crate) unsafe fn get_item_ref_mut(&self, key: Place) -> &mut (V, Metadata<T>) {
        let vs = self.resolve_type(key);
        &mut (*vs[key.raw_ix()].get())
    }

    /// Marks values as tracked and stores the resolution order that those values
    /// are resolved in.
    pub(crate) fn track_values(&mut self, keys: &[Place], loc: T) {
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

    pub(crate) fn set_value(&mut self, key: Place, value: V) {
        // Safety: we're setting the value, so we're sure that the item at key is not used.
        // If the item was already set, we panic in the next line.
        let (v, md) = unsafe { self.get_item_ref_mut(key) };

        if md.is_tracked() {
            panic!("Value with index {} is already set", key.as_any_index())
        }

        (*v, *md) = (value, Metadata::new_resolved());

        self.advance_track();
    }

    pub(crate) fn advance_track(&mut self) {
        for i in (self.max_tracked + 1)..self.variables.len() as i64 {
            if i.to(std::convert::TryInto::<u64>::try_into)
                .unwrap()
                .to(Variable::from_variable_index)
                .to(Place::from_variable)
                .to(|x| self.get_item_ref(x))
                .1
                .is_tracked()
            {
                self.max_tracked = i;
            } else {
                break;
            }
        }
    }
}

type Mdd = u16;

#[derive(Default)]
// Used by the resolver for internal tracking purposes.
pub(crate) struct Metadata<T: Default> {
    data: Mdd,
    pub tracker: T,
}

impl<T: Default> Metadata<T> {
    // Means this element was introduced to the resolver
    const TRACKED_MASK: Mdd = 0b1000_0000_0000_0000;
    // Means this element was resolved and it's value is set.
    const RESOLVED_MASK: Mdd = 0b0100_0000_0000_0000;

    pub(crate) fn new(tracker: T) -> Self {
        Self {
            data: Self::TRACKED_MASK,
            tracker,
        }
    }

    pub(crate) fn new_resolved() -> Self {
        Self {
            data: Self::TRACKED_MASK | Self::RESOLVED_MASK,
            tracker: T::default(),
        }
    }

    pub fn is_tracked(&self) -> bool {
        self.data & Self::TRACKED_MASK != 0
    }

    pub fn is_resolved(&self) -> bool {
        self.data & Self::RESOLVED_MASK != 0
    }

    pub fn mark_resolved(&mut self) {
        // This is a workaround for single threaded resolver, that doesn't mark `tracked` in some
        // cases, but requires for some asserts in common code.
        // TODO: separate the resolver implementations.
        self.data |= Self::RESOLVED_MASK | Self::TRACKED_MASK;
    }
}

#[derive(Debug)]
struct MetadataDebugHelper {
    is_tracked: bool,
    is_resolved: bool,
}

impl<T: Default> std::fmt::Debug for Metadata<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::mem::size_of;
        use std::mem::transmute_copy;

        let mdh = MetadataDebugHelper {
            is_resolved: self.is_resolved(),
            is_tracked: self.is_tracked(),
        };
        let tracker: u64;
        unsafe {
            if size_of::<T>() == size_of::<u64>() {
                tracker = transmute_copy::<_, u64>(&self.tracker)
            } else if size_of::<T>() == size_of::<u32>() {
                tracker = transmute_copy::<_, u32>(&self.tracker) as u64
            } else {
                tracker = 0
            }
        };
        f.debug_struct("Metadata")
            .field("data", &mdh)
            .field("tracker", &tracker)
            .finish()
    }
}

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

impl TrackId for OrderIx {}

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
        OrderIx(self.0 + rhs)
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
    pub items: Vec<OrderInfo<ResolverIx>>,
}

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct ResolverIx(pub usize);

pub enum ResolverIxType {
    Jump,
    Resolver,
}

impl ResolverIx {
    // Resolver box uses `sizeof` to determine the size of the allocations,
    // and operates on pointers or _size primitives, which always have lsb == 0
    // in their sizes, thus we can use the lsb to store type info.
    const TYPE_MASK: usize = 1;

    pub fn get_type(self) -> ResolverIxType {
        match self.0 & Self::TYPE_MASK == 0 {
            true => ResolverIxType::Resolver,
            false => ResolverIxType::Jump,
        }
    }

    fn new_jump(value: usize) -> Self {
        Self(value | Self::TYPE_MASK)
    }

    pub fn new_resolver(value: usize) -> Self {
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
    type Output = usize;

    fn sub(self, origin: Self) -> Self::Output {
        self.0 - origin.0
    }
}

impl AddAssign<u32> for ResolverIx {
    fn add_assign(&mut self, rhs: u32) {
        self.0 = rhs as usize;
    }
}
