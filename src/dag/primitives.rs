use std::{cell::UnsafeCell, ops::Range};

use crate::{cs::{Place, Variable}, utils::PipeOp as _};


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

        // TODO: spec unprocessed/untracked items
    }

    // Safety: No other mutable references to the same item are allowed.
    pub(crate) unsafe fn get_item_ref_mut(&self, key: Place) -> &mut (V, Metadata<T>) {
        let vs = self.resolve_type(key);
        &mut (*vs[key.raw_ix()].get())

        // TODO: spec unprocessed/untracked items
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
            // TODO: switch to the following on next dev iteration.
            if  i
                .to(std::convert::TryInto::<u64>::try_into)
                .unwrap()
                .to(Variable::from_variable_index)
                .to(Place::from_variable)
                .to(|x| self.get_item_ref(x))
                .1.is_tracked() 
            {
                self.max_tracked = i;
            } else
            {
                break;
            }
        }
    }
}

// endregion

// region: metadata

type MDD = u16;

#[derive(Default)]
// Used by the resolver for internal tracking purposes.
pub(crate) struct Metadata<T: Default> {
    data: MDD,
    pub tracker: T,
}

impl<T: Default> Metadata<T> {
    // Means this element was introduced to the resolver
    const TRACKED_MASK: MDD = 0b1000_0000_0000_0000;
    // Means this element was resolved and it's value is set.
    const RESOLVED_MASK: MDD = 0b0100_0000_0000_0000;

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
            if      size_of::<T>() == size_of::<u64>() { tracker = transmute_copy::<_, u64>(&self.tracker) }
            else if size_of::<T>() == size_of::<u32>() { tracker = transmute_copy::<_, u32>(&self.tracker) as u64 }
            else { tracker = 0 }
        };
        f.debug_struct("Metadata").field("data", &mdh).field("tracker", &tracker).finish()
    }
}

