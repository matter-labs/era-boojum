use std::cell::UnsafeCell;
use std::hint::spin_loop;
use std::marker::PhantomData;
use std::panic::resume_unwind;
use std::sync::atomic::{fence, AtomicU64, Ordering};
use std::thread::yield_now;

use crate::log;
use crate::utils::{PipeOp, UnsafeCellEx};

use super::primitives::Metadata;
use super::resolvers::mt::ResolverComms;
use super::TrackId;

#[derive(Debug)]
pub(crate) struct AwaiterStats {
    total_registered: u64,
}

/// The broker provides awaiters, which are used to wait for a particular resolution.
pub struct AwaitersBroker<T> {
    /// Tracks the maximum resolved location.
    max_resolved: AtomicU64,
    pub(crate) stats: UnsafeCell<AwaiterStats>,
    phantom: PhantomData<T>,
}

impl<T: TrackId> AwaitersBroker<T> {
    pub(crate) fn new() -> Self {
        Self {
            // It's ok to compare to 0, because this value represents 0'th span
            // which doesn't contain any resolvers due to giude implementation.
            max_resolved: AtomicU64::new(0),
            stats: UnsafeCell::new(AwaiterStats {
                total_registered: 0,
            }),
            phantom: PhantomData,
        }
    }

    pub(crate) fn notify(&self, resolved: T) {
        // TODO: Remove once the system is stable.
        let max_resolved = self.max_resolved.load(Ordering::Relaxed).to(T::from);
        assert!(
            resolved >= max_resolved,
            "Resolved location less than the maximum resolved location: {:?} > {:?}",
            resolved,
            max_resolved
        );

        self.max_resolved.store(resolved.into(), Ordering::Relaxed);
    }

    pub(crate) fn register<'a>(&'a self, comms: &'a ResolverComms, md: &Metadata<T>) -> Awaiter<T> {
        unsafe { self.stats.u_deref_mut().total_registered += 1 };

        Awaiter::new(self, comms, md.tracker)
    }
}

/// The Awaiter attempts to resolve a (set of) variables in its own thread.  
/// Waits based on the `track_id`. Once an id is resolved, all items with lower id are considered
/// resolved.
pub struct Awaiter<'a, T> {
    pub(crate) broker: &'a AwaitersBroker<T>,
    comms: &'a ResolverComms,
    track_id: T,
}

impl<'a, T> Awaiter<'a, T> {
    pub(crate) fn new(
        broker: &'a AwaitersBroker<T>,
        comms: &'a ResolverComms,
        track_id: T,
    ) -> Self {
        Self {
            broker,
            comms,
            track_id,
        }
    }
}

impl<'a, T: TrackId> crate::dag::Awaiter<'a> for Awaiter<'a, T> {
    fn wait(&self) {
        let iterations = 0;

        loop {
            if self.broker.max_resolved.load(Ordering::Relaxed).to(T::from) >= self.track_id {
                break;
            }

            if self.comms.rw_panicked.load(Ordering::Relaxed) {
                if let Some(e) = self.comms.rw_panic.take() {
                    resume_unwind(e);
                } else {
                    log!("Resolution window panicked, but no panic payload stored.");
                    return;
                }
            }

            // TODO: This threshold is arbitrary. It should be tuned.
            if iterations > 1000 {
                yield_now();
            } else {
                spin_loop();
            }
        }

        // After waiting the client code will want to access the value, which
        // is written in another thread.
        fence(Ordering::Acquire);
    }
}

/// An awaiter that is always considered resolved. Used by the single threaded resolver.
pub struct ImmediateAwaiter {}

impl<'a> crate::dag::Awaiter<'a> for ImmediateAwaiter {
    fn wait(&self) {}
}
