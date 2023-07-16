use std::cell::UnsafeCell;
use std::hint::spin_loop;
use std::panic::resume_unwind;
use std::sync::atomic::{fence, AtomicU64, Ordering};
use std::thread::yield_now;

use crate::log;
use crate::utils::{PipeOp, UnsafeCellEx};

use super::guide::GuideLoc;
use super::resolver::{Metadata, ResolverComms};

#[derive(Debug)]
pub(crate) struct AwaiterStats {
    total_registered: u64,
}

/// The broker provides awaiters, which are used to wait for a particular resolution.
pub(crate) struct AwaitersBroker {
    /// Tracks the maximum resolved location.
    max_resolved: AtomicU64,
    pub(crate) stats: UnsafeCell<AwaiterStats>,
}

impl AwaitersBroker {
    pub(crate) fn new() -> Self {
        Self {
            // It's ok to compare to 0, because this value represents 0'th span
            // which doesn't contain any resolvers due to giude implementation.
            max_resolved: AtomicU64::new(0),
            stats: UnsafeCell::new(AwaiterStats {
                total_registered: 0,
            }),
        }
    }

    pub(crate) fn notify(&self, resolved: GuideLoc) {
        // TODO: Remove once the system is stable.
        let max_resolved = self
            .max_resolved
            .load(Ordering::Relaxed)
            .to(GuideLoc::from_u64);
        assert!(
            resolved >= max_resolved,
            "Resolved location less than the maximum resolved location: {:?} > {:?}",
            resolved,
            max_resolved
        );

        self.max_resolved
            .store(resolved.to_u64(), Ordering::Relaxed);
    }

    pub(crate) fn register<'a>(&'a self, comms: &'a ResolverComms, md: &Metadata) -> Awaiter {
        unsafe { self.stats.u_deref_mut().total_registered += 1 };

        Awaiter::new(self, comms, md.guide_loc)
    }
}

/// The Awaiter attempts to resolve a (set of) variables in its own thread.
pub struct Awaiter<'a> {
    pub(crate) broker: &'a AwaitersBroker,
    comms: &'a ResolverComms,
    guide_loc: GuideLoc,
}

impl<'a> Awaiter<'a> {
    pub(crate) fn new(
        broker: &'a AwaitersBroker,
        comms: &'a ResolverComms,
        guide_loc: GuideLoc,
    ) -> Self {
        Self {
            broker,
            comms,
            guide_loc,
        }
    }
}

impl<'a> crate::dag::Awaiter<'a> for Awaiter<'a> {
    fn wait(&self) {
        let iterations = 0;

        loop {
            if self
                .broker
                .max_resolved
                .load(Ordering::Relaxed)
                .to(GuideLoc::from_u64)
                >= self.guide_loc
            {
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
