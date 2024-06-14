use super::primitives::OrderIx;
use super::TrackId;
use crate::{config::*, utils::PipeOp};
use crate::{field::SmallField, log};
use smallvec::SmallVec;
use std::{fmt::Debug, marker::PhantomData, ops::Range};

// TODO: Move to a more fitting location.
pub(crate) type RegistrationNum = u32;
pub const GUIDE_SIZE: usize = 32;

#[derive(Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct SpanId(u32);

// TODO: Measure max values on real data, perhaps we can make it smaller.
/// Marks the location of a resolver within the guide. Resolvers spend only a
/// limited time within the guide, so it is not possible to retrieve a resolver
/// from the guide with this in general case. It's main purpose is to provide
/// the guide with the information about a resolver. The guide doesn't care if
/// the specific resolver is currently in it or not, it handles both cases.
///
/// The `GuideLoc` can be used to compare relative order of two resolvers, but
/// it will not allow to find the resolver within the `resolvers_order`. This is
/// used to notify any awaiters that are waiting for a particular resolver.
#[derive(PartialEq, Eq, Debug, Copy, Clone, Default, PartialOrd, Ord)]
pub struct GuideLoc {
    id: SpanId,
    pos: u32,
}

impl GuideLoc {
    pub fn from_u64(v: u64) -> Self {
        Self {
            id: SpanId((v >> 32) as u32),
            pos: (v & 0xFFFF_FFFF) as u32,
        }
    }

    pub fn to_u64(self) -> u64 {
        (self.id.0 as u64) << 32 | (self.pos as u64)
    }
}

impl From<u64> for GuideLoc {
    fn from(value: u64) -> Self {
        GuideLoc::from_u64(value)
    }
}

impl From<GuideLoc> for u64 {
    fn from(value: GuideLoc) -> Self {
        value.to_u64()
    }
}

impl From<GuideLoc> for usize {
    fn from(value: GuideLoc) -> Self {
        value.to_u64() as usize
    }
}

impl TrackId for GuideLoc {}

// region: guide trait

pub(crate) trait Guide<T, F: SmallField, Cfg: CSResolverConfig> {
    type PushOrder<'a>: GuideOrder<'a, T>
    where
        T: 'a,
        Self: 'a;
    type FinalizationOrder<'a>: GuideOrder<'a, T>
    where
        T: 'a,
        Self: 'a;

    fn push(
        &mut self,
        value: T,
        after: Option<GuideLoc>,
        added_at: RegistrationNum,
        accepted_at: RegistrationNum,
    ) -> (GuideLoc, Self::PushOrder<'_>);

    fn flush(&mut self) -> Self::FinalizationOrder<'_>;
}

#[derive(PartialEq, Eq, Debug)]
enum GuideRecord {
    Index(OrderIx),
    Jump((OrderIx, OrderIx)),
}

// TODO: remove on next dev iteration.
/// First guide implementation, tries to write in place, thus wasting space (can have long gaps).
/// This creates a problem that graphs with linear nature will take an obsenely large vec.
///
/// This guide will work faster on a wider shaped graphs.
///
/// It doesn't implement the Guide trait cause the trait was created later along with buffer guide.
/// It also wasn't tested with mutlithreaded resolution.
pub(crate) struct SpansGuide<F: SmallField, Cfg> {
    /// Desired parallelism. It can be lower, but the guide will try to keep it somewhat above.
    parallelism: usize,
    /// Points to the end of the acqiusition. This is last acquision +1, not the acquisition itself.
    pub end: OrderIx,
    /// Only public for support of the sync resolution. The 0'th span's pointer is used as the only
    /// pointer in the guide.
    pub spans: [Span; GUIDE_SIZE],

    phantom: PhantomData<F>,
}

pub(crate) struct Span {
    origin: Pointer,
    // Points to the next slot to be used.
    pub(crate) next: Pointer,
}

impl Span {
    fn new(origin: Pointer) -> Self {
        Self {
            next: Pointer::new_at(origin.index),
            origin,
        }
    }
}

impl<F: SmallField, Cfg: CSResolverConfig> SpansGuide<F, Cfg> {
    pub fn new(parallelism: usize) -> Self {
        Self {
            parallelism,
            spans: std::array::from_fn(|x| Span::new(Pointer::new_at((x * parallelism).into()))),
            end: 0u64.into(),
            phantom: PhantomData,
        }
    }

    pub fn acquire_position(
        &mut self,
        after: Option<OrderIx>,
    ) -> (OrderIx, Option<(OrderIx, OrderIx)>) {
        let r = match after {
            Some(after) => {
                // Affects the way the filled pointer is chosen.
                fn select_pointer(p: &Pointer, after: OrderIx, parallelism: usize) -> bool {
                    p.distance(after) >= parallelism as isize
                }

                let span = self
                    .spans
                    .iter_mut()
                    .enumerate()
                    .find(|(_, x)| select_pointer(&x.next, after, self.parallelism));

                match span {
                    Some((i, _)) => (advance(self, i), None),
                    None => {
                        // This happens when `after` is in the last span. This means that
                        // when we shift once, the parallelism for the dependency drops to
                        // 0 < x < parallelism.
                        // TODO: handle cases for x << parallelism.

                        // Remove the oldest span. This one should be less probable to get
                        // added to. This may not be the case, stat analysis should be
                        // applied once the new system is complete. We want to have as little
                        // gaps as possible.
                        drop(span);

                        let short_circuit_from = self.spans[0].next.index;
                        let short_circuit_to = self.spans[1].origin.index;

                        unsafe { shift(self, 0) };

                        let ix = advance(self, GUIDE_SIZE - 1);

                        (ix, Some((short_circuit_from, short_circuit_to)))
                    }
                }
            }
            // Pushing to the earlies possible slot.
            None => (advance(self, 0), None),
        };

        fn advance<F: SmallField, Cfg>(guide: &mut SpansGuide<F, Cfg>, span_ix: usize) -> OrderIx {
            let span = &mut guide.spans[span_ix];

            // TODO: advance should return the ix.
            let ix = span.next.index;
            span.next.advance();

            // TODO: Normalize types.
            if (span.next.index - span.origin.index) as usize >= guide.parallelism {
                // Otherwise, `span` will point to different memory after memmove.
                drop(span);

                unsafe { shift(guide, span_ix) };
            }

            guide.end = std::cmp::max(guide.end, ix + 1 /* `end` points to last el +1 */);

            ix
        }

        /// Removes a span and shifts all spans to the right one position left.
        /// A new span is created at the end of the list.
        ///
        /// Safety: All indices and references to spans in the guide need to be
        /// dropped before use.
        unsafe fn shift<F: SmallField, Cfg>(guide: &mut SpansGuide<F, Cfg>, span_ix: usize) {
            assert!(span_ix < GUIDE_SIZE);

            // We're shifting all items right to the current element
            // one position to the right, removing the filled span.
            let src = span_ix + 1;
            let dst = span_ix;
            let count = guide.spans.len() - span_ix - 1;

            // Safety:
            // Pointer and span types should not implement Copy, which
            // is required by the `copy_within` function. This code
            // is an expempt from there. It is safe to copy spans because
            // the span index is only used transitively when acquiring
            // a new position.
            // The `span` in use is dropped above.
            unsafe {
                let ptr = guide.spans.as_mut_ptr();
                let src_ptr = ptr.add(src); // Check out of bounds.
                let dst_ptr = ptr.add(dst);
                std::ptr::copy(src_ptr, dst_ptr, count);
            }

            // Zero out the last span as new.
            let span_loc = &mut guide.spans[GUIDE_SIZE - 1];
            let new_origin =
                // The last element still contains a residual copy of the last span.
                span_loc.origin.index + guide.parallelism;
            *span_loc = Span::new(Pointer::new_at(new_origin));
        }

        r
    }

    pub fn finalize(&mut self) -> SmallVec<[(OrderIx, OrderIx); GUIDE_SIZE]> {
        let mut vec = SmallVec::new();

        for i in 0..GUIDE_SIZE - 1 {
            let cur = &self.spans[i];
            let next = &self.spans[i + 1];

            if next.origin.index > self.end {
                // No point going over the end.
                break;
            }

            vec.push((cur.next.index, next.origin.index));
        }

        vec
    }
}

// endregion

// region: buffer guide

struct BufferSpan<T, F: SmallField, Cfg: CSResolverConfig> {
    id: SpanId,
    buffer: Vec<OrderInfo<T>>,
    phantom: PhantomData<(F, Cfg)>,
    size: u32,
}

impl<T: Debug, F: SmallField, Cfg: CSResolverConfig> BufferSpan<T, F, Cfg> {
    fn new(id: SpanId, size: u32) -> Self {
        Self {
            id,
            buffer: Vec::with_capacity(size as usize),
            phantom: PhantomData,
            size,
        }
    }

    fn push(&mut self, value: OrderInfo<T>) -> u32 {
        let pos = self.buffer.len();
        self.buffer.push(value);

        debug_assert_eq!(self.size as usize, self.buffer.capacity());

        pos as u32
    }

    fn repurpose(&mut self, id: SpanId) {
        self.id = id;
        self.buffer.clear();
    }
}

#[derive(Clone, Copy, Debug)]
pub struct OrderInfo<T> {
    pub value: T,
    pub metadata: GuideMetadata,
}

impl<T> OrderInfo<T> {
    pub fn new(value: T, metadata: GuideMetadata) -> Self {
        Self { value, metadata }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct GuideMetadata {
    parallelism: u16,
    /// Represents the **moment** at which the resolver's order
    /// could be determined, **not** the registration at which
    /// it was added.
    added_at: RegistrationNum,
    accepted_at: RegistrationNum,
}

impl GuideMetadata {
    pub fn new(parallelism: u16, added_at: RegistrationNum, accepted_at: RegistrationNum) -> Self {
        Self {
            parallelism,
            added_at,
            accepted_at,
        }
    }

    pub fn with_parallelism(&self, parallelism: u16) -> Self {
        Self {
            parallelism,
            ..*self
        }
    }

    pub fn parallelism(&self) -> usize {
        self.parallelism as usize
    }

    pub fn added_at(&self) -> RegistrationNum {
        self.added_at
    }
    pub fn accepted_at(&self) -> RegistrationNum {
        self.accepted_at
    }
}

pub trait GuideOrder<'a, T>
where
    T: 'a,
{
    fn size(&self) -> usize;
    fn write(&self, target: &mut [OrderInfo<T>]) -> Range<OrderIx>;
}

pub(crate) struct BufferGuideOrder<'a, T: Debug, F: SmallField, Cfg: CSResolverConfig> {
    guide: &'a mut BufferGuide<T, F, Cfg>,
    /// Amount of released spans.
    released_spans: u32,
}

impl<'a, T: Copy + Debug, F: SmallField, Cfg: CSResolverConfig> GuideOrder<'a, T>
    for BufferGuideOrder<'a, T, F, Cfg>
{
    fn size(&self) -> usize {
        // TODO: bench if explicitly handling case with 0 and 1 span is faster.
        self.guide.spans[0..self.released_spans as usize]
            .iter()
            .map(|x| x.buffer.len())
            .sum::<usize>()
    }

    fn write(&self, target: &mut [OrderInfo<T>]) -> Range<OrderIx> {
        if self.released_spans == 0 {
            return self.guide.next_target.index..self.guide.next_target.index;
        }

        let start = self.guide.next_target.index;
        let mut pos = self.guide.next_target.index.into();

        for span in &self.guide.spans[0..self.released_spans as usize] {
            target[pos..pos + span.buffer.len()].copy_from_slice(&span.buffer);

            pos += span.buffer.len();
        }

        if cfg!(feature = "cr_paranoia_mode") && self.guide.tracing {
            log!(
                "Released span {}: {:?}",
                self.guide.spans[0].id.0,
                self.guide.spans[0].buffer
            );
        }

        start..pos.into()
    }
}

impl<'a, T: Debug, F: SmallField, Cfg: CSResolverConfig> Drop for BufferGuideOrder<'a, T, F, Cfg> {
    fn drop(&mut self) {
        for _ in 0..self.released_spans {
            self.guide.expropriate_span();
        }

        if let Some(item) = self.guide.carrying_over.take() {
            // Always carried to the last span, the decision where to put it is
            // made at the order construction site.
            self.guide.spans[GUIDE_SIZE - 1].push(item);
        }
    }
}

pub(crate) struct BufferGuideFinalization<'a, T: Debug, F: SmallField, Cfg: CSResolverConfig> {
    guide: &'a mut BufferGuide<T, F, Cfg>,
}

impl<'a, T: Copy + Debug, F: SmallField, Cfg: CSResolverConfig> GuideOrder<'a, T>
    for BufferGuideFinalization<'a, T, F, Cfg>
{
    fn size(&self) -> usize {
        self.guide
            .spans
            .iter()
            .map(|x| x.buffer.len())
            .sum::<usize>()
    }

    fn write(&self, target: &mut [OrderInfo<T>]) -> Range<OrderIx> {
        // Not using the pointer cause after this no modifications are
        // allowed anyway, so we don't care about preserving invariants.
        let start = self.guide.next_target.index;
        let mut pos = start.into();

        for span in &self.guide.spans {
            target[pos..pos + span.buffer.len()].copy_from_slice(&span.buffer);

            pos += span.buffer.len();
        }

        start..pos.into()
    }
}

impl<'a, T: Debug, F: SmallField, Cfg: CSResolverConfig> Drop
    for BufferGuideFinalization<'a, T, F, Cfg>
{
    fn drop(&mut self) {
        for _ in 0..GUIDE_SIZE {
            self.guide.expropriate_span();
        }
    }
}

#[derive(Debug)]
pub(crate) struct GuideStats {
    pub(crate) parallelism: Vec<u32>,
    parallelism_low: Vec<u32>,

    avg_parallelism: f32,
    median_parallelism: usize,
}

impl GuideStats {
    pub fn new() -> Self {
        Self {
            parallelism: Vec::with_capacity(65000).op(|x| x.resize(65000, 0)),
            parallelism_low: Vec::new(),
            avg_parallelism: 0.0,
            median_parallelism: 0,
        }
    }

    pub fn finalize(&mut self) {
        let sum: u32 = self.parallelism.iter().sum();
        let len = self.parallelism.len() as f32;

        self.avg_parallelism = sum as f32 / len;

        // Calculate median.
        let mut aggr = 0.0;

        for i in 0..self.parallelism.len() {
            aggr += self.parallelism[i] as f32;
            if aggr >= sum as f32 / 2.0 {
                self.median_parallelism = i;
                break;
            }
        }

        self.parallelism_low = self.parallelism[0..128].to_vec();

        // compress parallelism vector by a factor of 1000.
        let mut new_vec = Vec::with_capacity(self.parallelism.len() / 1000);

        self.parallelism.chunks(1000).for_each(|x| {
            new_vec.push(x.iter().sum());
        });

        self.parallelism = new_vec;
    }
}

/// Thid guide uses buffers to fill out the order. It is slower than the
/// `SpansGuide`, but leaves no gaps.
pub(crate) struct BufferGuide<T, F: SmallField, Cfg: CSResolverConfig> {
    /// Desired parallelism. It can be lower, but the guide will try to keep it somewhat above.
    parallelism: u32,

    /// Represent the sorting front of the graph. The algorithm attempts to
    /// optmistically populate the spans in such a way, that if all spans are
    /// completely filled, the distance between any dependant items equals or is
    /// greater than `parallelism`.  
    /// If the algorithm fails to do so, it will modify the `parallelism` value
    /// of each affected item upon release.
    spans: [BufferSpan<T, F, Cfg>; GUIDE_SIZE],

    /// Points to one element after the last element in the target span. When a
    /// guide order is written it is using this pointer to find the location
    /// where the data should be written.
    next_target: Pointer,

    /// Holds the order info that should be written to the new span. When this
    /// value is created there is still no span to write to, so it is stored
    /// here.
    carrying_over: Option<OrderInfo<T>>,

    /// Enables tracing. Requires `cr_paranoia_mode` to be enabled.
    pub tracing: bool,

    pub stats: GuideStats,
}

enum MatchedSpan<T> {
    Existing(T),
    New(u32),
}

impl<T: Debug, F: SmallField, Cfg: CSResolverConfig> BufferGuide<T, F, Cfg> {
    pub fn new(parallelism: u32) -> Self {
        Self {
            parallelism,
            spans: std::array::from_fn(|x| {
                BufferSpan::new(
                    SpanId(x as u32),
                    // When a non edge buffer is full and moves to the edge
                    // position, it can be pushed into one more time. So we
                    // set the capacity to +1.
                    parallelism + 1,
                )
            }),
            next_target: Pointer::new_at(0u32.into()),
            carrying_over: None,
            tracing: false,
            stats: GuideStats::new(),
        }
    }

    pub(crate) fn push(
        &mut self,
        value: T,
        after: Option<GuideLoc>,
        added_at: RegistrationNum,
        accepted_at: RegistrationNum,
    ) -> (GuideLoc, BufferGuideOrder<'_, T, F, Cfg>) {
        let origin = after;
        let span = match origin {
            // WARNING: Span with id 0 may not be written to, as the awaiter relies on this
            // fact for performance reasons.
            Some(origin) => {
                match origin.id.0 as isize - self.spans[0].id.0 as isize {
                    // Origin is before 0'th span. We don't really know how far,
                    // (though it can be estimated, if required).
                    // Dropping into the 1'st span, on average should yield big
                    // enough distances.
                    // TODO: statistics for the average distance on real cases.
                    d if d < 0 => MatchedSpan::Existing((&mut self.spans[1], 1)),
                    // Origin is the last span, this means there is no span we
                    // can push this into. We can't put the value into the the
                    // span immediately following the origin, as it depends on
                    // an item within it, so we create 2 new spans.
                    d if d == GUIDE_SIZE as isize - 1 => MatchedSpan::New(2),
                    // Origin is any except last span.
                    d => {
                        let d = d as usize;

                        let i = match origin.pos as usize > self.spans[d + 1].buffer.len() {
                            // The value is too close to the next span's push
                            // position, so we're puting it in the one after it.
                            // The next span will continue to be filled,
                            // increasing the distance.
                            true => d + 2,
                            false => d + 1,
                        };

                        // If an existing span will not be found, this new span
                        // will never be immediately following the origin, thus
                        // the items will be separated by one span.
                        let mut r = MatchedSpan::New(1);

                        for i in i..GUIDE_SIZE {
                            if self.spans[i].buffer.len() < self.parallelism as usize {
                                r = MatchedSpan::Existing((&mut self.spans[i], i));
                                break;
                            }
                        }

                        r
                    }
                }
            }
            // Non-depending item. Since we allow overfill of +1, this is safe.
            None => MatchedSpan::Existing((&mut self.spans[1], 1)),
        };

        let order_info = OrderInfo::new(
            value,
            // We optimistically assume that the span will be completely filled.
            GuideMetadata::new(self.parallelism as u16, added_at, accepted_at),
        );

        match span {
            MatchedSpan::Existing((span, _)) => match span.push(order_info) {
                // Span is full. It can be of size `parallelism + 1` due to
                // already being completely full when moved to the edge
                // position and an independent item is being pushed.
                // This will never occur for second or further buffers as
                // they are never chosen if full.
                // TODO: Bug. Seems like `&& i == 1` is missing. Or perhaps it should be `pos + 1 > self.parallelism`?
                pos if pos + 1 >= self.parallelism => {
                    // The 1'st span is full, so 0'th span can't gain any
                    // more parallelism. Release it.
                    // The order is holding an exclusive guide reference, so
                    // it will have to be dropped to add next item.
                    let id = span.id;

                    self.calculate_parallelism(0);

                    let order = BufferGuideOrder {
                        guide: self,
                        released_spans: 1,
                    };

                    (GuideLoc { id, pos }, order)
                }
                pos => {
                    let loc = GuideLoc { id: span.id, pos };

                    // Empty.
                    (
                        loc,
                        BufferGuideOrder {
                            guide: self,
                            released_spans: 0,
                        },
                    )
                }
            },
            MatchedSpan::New(n) => {
                // This happens when `after` is in the last span.

                // This one is going to be added to a yet non-existing span. It
                // will be created after the order is dropped.
                let id = SpanId(self.spans[GUIDE_SIZE - 1].id.0 + n);
                // Naturally the first value in a new span will take 0'th position.
                let pos = 0;
                let loc = GuideLoc { id, pos };

                // This value is going to be written after the span is released,
                // during the order drop.
                self.carrying_over = Some(order_info);

                (0..n).for_each(|x| self.calculate_parallelism(x as usize));

                // The presentation is the same, it's just going to have less items.
                // This is going to be handled in the order drop.
                let order = BufferGuideOrder {
                    guide: self,
                    released_spans: n,
                };

                (loc, order)
            }
        }
    }

    pub(crate) fn flush(&mut self) -> BufferGuideFinalization<'_, T, F, Cfg> {
        if cfg!(feature = "cr_paranoia_mode") && self.tracing {
            log!("CRG: flush.");
        }

        for i in 0..GUIDE_SIZE {
            self.calculate_parallelism(i)
        }

        BufferGuideFinalization { guide: self }
    }

    #[allow(non_snake_case)] // reason = "The names are used in the comments."
    fn calculate_parallelism(&mut self, i: usize) {
        // For each buffer pair (A, B) there are four options:
        // 1. A - full, B - full
        // 2. A - full, B - not full
        // 3. A - not full, B - full
        // 4. A - not full, B - not full
        //
        // We're only interested in the parallelism rate of A.

        // In case of a last span, we assume that in the future the next span
        // will be depending on all items in this one, thus we limit the
        // parallelism to this span only.
        if i == GUIDE_SIZE - 1 {
            let A = &mut self.spans[i].buffer;
            let N = A.len();

            for x in 0..N {
                let p: usize = N - x;
                debug_assert_ne!(0, p);

                A[x].metadata = A[x].metadata.with_parallelism((p) as u16);
                self.stats.parallelism[p] += 1;
            }

            return;
        }

        // Not using capacity, cause the capacity is p + 1.
        // The cast is sound cause spans' size is a derivative of a parallelism
        // and its values are generally small.
        match (
            self.parallelism as isize - self.spans[i].buffer.len() as isize,
            self.parallelism as isize - self.spans[i + 1].buffer.len() as isize,
        ) {
            (a, b) if a <= 0 && b <= 0 => {
                // Case 1:
                // Each item in B is guaranteed to be at least `parallelism`
                // away from it's dependency in A. Hence no actions are
                // required, all items in A have full parallelism (default).

                self.stats.parallelism[self.parallelism as usize] +=
                    self.spans[i].buffer.len() as u32;
            }
            (a, b) if a <= 0 && b > 0 => {
                // Case 2:
                // Where B filled with N items:
                // Up until N the dependency distance guarantees are upheld.
                // Beyond N items in A are less than `parallelism` away from
                // theoretical C. There are no guarantees made for C, so we
                // consider that all A[N + x] are dependant by C[0].
                // So the distance between A[N + x] from C[0] is the total B and
                // the tail from `x` to end of A.

                // N doesn't include the possible overfill item, due to case.
                let n = self.spans[i + 1].buffer.len();
                let mut t = self.parallelism as u16 - n as u16; // tail

                let B_len = self.spans[i + 1].buffer.len();
                let A = &mut self.spans[i].buffer;

                self.stats.parallelism[self.parallelism as usize] += n as u32;

                for n in n..A.len() {
                    let p = std::cmp::max(t + B_len as u16, 1);
                    A[n].metadata = A[n].metadata.with_parallelism(p);
                    self.stats.parallelism[p as usize] += 1;

                    // If A has an overfill item, t will go into negative and
                    // additionaly reduce parallelism for that item.
                    (t, _) = t.overflowing_sub(1);
                }
            }
            (a, b) if a > 0 && b <= 0 => {
                // Case 3:
                // Where A is filled with N items:
                // A[x] and B[x] distance is size of A. With B completely
                // filled, the distance to C[0] is larger than parallelism. Then
                // the parallelism of all A items is trimmed to size of A.

                let len = self.spans[i].buffer.len();

                for e in &mut self.spans[i].buffer {
                    debug_assert_ne!(0, len);
                    e.metadata = e.metadata.with_parallelism(len as u16);

                    self.stats.parallelism[len] += 1;
                }
            }

            (a, b) if a > 0 && b > 0 => {
                // Case 4:
                // Where A is filled with N items and B is filled with M items:
                // A combination of cases 2 and 3.
                // For x when:
                // - x < N, x < M:
                //   B[x] - A[x] = size of A (N) (similar to case 3).
                // - M < x < N:
                //   A is more filled than B. In this case, last N - M items of
                //   A are affected by the fill ratio of B, as in case 2: size
                //   of B + tail in A.
                // Those are only two possibilities, as x must be smaller than
                // N. We consider both cases and take the smaller constraint.
                //
                // This can be the only case, but the idea is to tweak the
                // parallelism so that it mainly falls into case 1 (nop).

                let B = &self.spans[i + 1].buffer;
                let M = B.len() as u16;

                let A = &mut self.spans[i].buffer;
                let N = A.len() as u16;

                for x in 0..N {
                    let c1 = N;
                    let c2 = M + (N - x);

                    let p = std::cmp::min(c1, c2);

                    debug_assert_ne!(0, p);
                    A[x as usize].metadata = A[x as usize].metadata.with_parallelism(p);

                    self.stats.parallelism[p as usize] += 1;
                }
            }
            (_, _) => unreachable!(),
        }
    }

    // TODO: Optimization: can rotate n times, not just 1.
    fn expropriate_span(&mut self) {
        self.next_target.jump(
            self.spans[0].buffer.len() as u32, /* Never larger than `parallelism` */
        );

        // Using last span as a refernce point.
        let last_span = &self.spans[GUIDE_SIZE - 1];
        // It's going to be the new last span.
        self.spans[0].repurpose(SpanId(last_span.id.0 + 1));

        // then moved to the end of the span list as a fresh new span.
        self.spans.rotate_left(1)
    }
}

impl<T: Copy + Debug, F: SmallField, Cfg: CSResolverConfig> Guide<T, F, Cfg>
    for BufferGuide<T, F, Cfg>
{
    type PushOrder<'a>         = BufferGuideOrder       <'a, T, F, Cfg> where T: 'a;
    type FinalizationOrder<'a> = BufferGuideFinalization<'a, T, F, Cfg> where T: 'a;

    fn push(
        &mut self,
        value: T,
        after: Option<GuideLoc>,
        added_at: RegistrationNum,
        accepted_at: RegistrationNum,
    ) -> (GuideLoc, BufferGuideOrder<'_, T, F, Cfg>) {
        self.push(value, after, added_at, accepted_at)
    }

    fn flush(&mut self) -> BufferGuideFinalization<'_, T, F, Cfg> {
        self.flush()
    }
}

// TODO: is it used?
// Note, this is not related to *ptr, but this thing points to stuff
// hence the name. Instances of this will always be called `pointers`,
// instances of system pointers will always be `ptrs`, to remove ambiguity.
#[derive(PartialEq, PartialOrd, Eq, Ord)]
pub(crate) struct Pointer {
    // TODO: use generic integer type.
    pub index: OrderIx,
}

impl Pointer {
    pub fn new_at(at: OrderIx) -> Self {
        Self { index: at }
    }

    pub fn advance(&mut self) {
        self.index += 1;
    }

    pub(crate) fn jump(&mut self, distance: u32) {
        self.index += distance;
    }

    pub(crate) fn jump_to(&mut self, ix: u32) {
        assert!(self.index <= ix.into());
        self.index = ix.into();
    }

    fn distance(&self, from: OrderIx) -> isize {
        let (a, b): (isize, isize) = (self.index.into(), from.into());
        a - b
    }
}

impl std::ops::Add<u32> for &Pointer {
    type Output = Pointer;

    fn add(self, rhs: u32) -> Self::Output {
        Pointer::new_at(self.index + rhs)
    }
}

#[cfg(test)]
mod general_tests {
    use crate::dag::guide::SpanId;

    use super::GuideLoc;

    #[test]
    fn guide_loc_ordering() {
        use std::cmp::Ordering;

        assert_eq!(
            Ordering::Equal,
            GuideLoc::default().cmp(&GuideLoc::default())
        );
        assert_eq!(
            Ordering::Greater,
            GuideLoc {
                id: SpanId(1),
                pos: 0
            }
            .cmp(&GuideLoc {
                id: SpanId(0),
                pos: 1
            })
        );
        assert_eq!(
            Ordering::Greater,
            GuideLoc {
                id: SpanId(1),
                pos: 2
            }
            .cmp(&GuideLoc {
                id: SpanId(0),
                pos: 1
            })
        );
    }
}

#[cfg(test)]
mod spans_guide_tests {
    use super::SpansGuide;
    use crate::{
        config::{DoPerformRuntimeAsserts, Resolver},
        field::goldilocks::GoldilocksField,
        utils::PipeOp,
    };

    #[test]
    fn acquire_after_none_gives_incremented_indicies() {
        let mut guide = SpansGuide::<GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (i1, _) = guide.acquire_position(None);
        let (i2, _) = guide.acquire_position(None);
        let (i3, _) = guide.acquire_position(None);
        let (i4, _) = guide.acquire_position(None); // Up to parallelism.

        assert_eq!(0, u32::from(i1));
        assert_eq!(1, u32::from(i2));
        assert_eq!(2, u32::from(i3));
        assert_eq!(3, u32::from(i4));
    }

    #[test]
    fn acquire_after_none_gives_incremented_indicies_after_fill() {
        let mut guide = SpansGuide::<GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let _ = guide.acquire_position(None);
        let _ = guide.acquire_position(None);
        let _ = guide.acquire_position(None);
        let _ = guide.acquire_position(None);
        let (i1, _) = guide.acquire_position(None);
        let (i2, _) = guide.acquire_position(None);
        let (i3, _) = guide.acquire_position(None);
        let (i4, _) = guide.acquire_position(None); // Up to parallelism.

        assert_eq!(4, u32::from(i1));
        assert_eq!(5, u32::from(i2));
        assert_eq!(6, u32::from(i3));
        assert_eq!(7, u32::from(i4));
    }

    #[test]
    fn acquire_after_some_gaps_over_required_parallelism() {
        let p = 4;

        let mut guide =
            SpansGuide::<GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(p as usize);

        let (i1, _) = guide.acquire_position(None);
        let (i2, _) = guide.acquire_position(Some(i1));
        let (i3, _) = guide.acquire_position(Some(i2));

        assert_eq!(0, u32::from(i1));
        assert_eq!(i1 + p, i2);
        assert_eq!(i2 + p, i3);
    }

    #[test]
    fn acquire_after_none_gives_incremented_indicies_after_dependencies_added() {
        let mut guide = SpansGuide::<GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (i1, _) = guide.acquire_position(None);
        let (i2, _) = guide.acquire_position(Some(i1));
        let (_, _) = guide.acquire_position(Some(i2));
        let (i4, _) = guide.acquire_position(None);
        let (i5, _) = guide.acquire_position(None);
        let (i6, _) = guide.acquire_position(None); // Until span fill.

        assert_eq!(1, u32::from(i4));
        assert_eq!(2, u32::from(i5));
        assert_eq!(3, u32::from(i6));
    }

    #[test]
    fn acquire_after_none_steps_over_added_dependencies() {
        let mut guide = SpansGuide::<GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (i1, _) = guide.acquire_position(None);
        let (i2, _) = guide.acquire_position(Some(i1));
        let (_, _) = guide.acquire_position(Some(i2));
        let _ = guide.acquire_position(None);
        let _ = guide.acquire_position(None);
        let _ = guide.acquire_position(None); // Span filled.
        let (i4, _) = guide.acquire_position(None);
        let (i5, _) = guide.acquire_position(None);
        let (i6, _) = guide.acquire_position(None); // Second span filled.
        let (i7, _) = guide.acquire_position(None);

        assert_eq!(5, u32::from(i4));
        assert_eq!(6, u32::from(i5));
        assert_eq!(7, u32::from(i6));
        assert_eq!(9, u32::from(i7));
    }

    #[test]
    fn short_circuits_correct_on_partially_filled_span() {
        let mut guide = SpansGuide::<GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (i1, _) = guide.acquire_position(None);
        let (_, _) = guide.acquire_position(Some(i1));

        let scs = guide.finalize();

        assert_eq!((1, 4), scs[0].to(|(a, b)| (u32::from(a), u32::from(b))));
        assert_eq!(1, scs.len());
        assert_eq!(5, u32::from(guide.end));
    }

    #[test]
    fn short_curcuits_correct_on_filled_span() {
        let mut guide = SpansGuide::<GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (i1, _) = guide.acquire_position(None);
        let _ = guide.acquire_position(Some(i1));
        let _ = guide.acquire_position(None);
        let _ = guide.acquire_position(None);
        let _ = guide.acquire_position(None);

        let scs = guide.finalize();

        assert_eq!(0, scs.len());
        assert_eq!(5, u32::from(guide.end));
    }
}

#[cfg(test)]
mod buffer_guide_tests {
    use itertools::Itertools;

    use crate::{
        config::{DoPerformRuntimeAsserts, Resolver},
        dag::guide::{GuideLoc, GuideMetadata, GuideOrder, OrderInfo},
        field::goldilocks::GoldilocksField,
        log,
    };

    use super::{BufferGuide, GUIDE_SIZE};

    #[test]
    fn independent_pushes_are_sequentional() {
        const P: usize = 4;

        let mut guide =
            BufferGuide::<u32, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(P as u32);

        let results: [GuideLoc; P * 2] = std::array::from_fn(|_| guide.push(0, None, 0, 0).0);

        assert!(
            results[0..P].windows(2).all(|x| { x[0].id == x[1].id }),
            "Should be placed in the same span."
        );
        assert!(
            results[P..P * 2].windows(2).all(|x| { x[0].id == x[1].id }),
            "Should be placed in the same span."
        );
        assert_eq!(
            results[0].id.0 + 1,
            results[P].id.0,
            "Span ids are not sequential."
        );

        assert_eq!(
            [0, 1, 2, 3],
            &results[0..P].iter().map(|x| x.pos).collect::<Vec<_>>()[..],
            "Should come one after another."
        );
        assert_eq!(
            [0, 1, 2, 3],
            &results[P..P * 2].iter().map(|x| x.pos).collect::<Vec<_>>()[..],
            "Should come one after another."
        );
    }

    #[test]
    fn filling_0th_span_expropriates_outstanding_span() {
        let mut guide =
            BufferGuide::<u32, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let _ = guide.push(0, None, 0, 0);
        let _ = guide.push(1, None, 0, 0);
        let _ = guide.push(2, None, 0, 0);
        let _ = guide.push(3, None, 0, 0); // first fill

        let _ = guide.push(4, None, 0, 0);
        let _ = guide.push(5, None, 0, 0);
        let _ = guide.push(6, None, 0, 0);
        let (_, order) = guide.push(7, None, 0, 0); // second fill

        let mut vec = [OrderInfo::new(0, GuideMetadata::new(4, 0, 0)); 8];

        order.write(&mut vec[..]);

        assert_eq!(
            [0, 1, 2, 3, 0, 0, 0, 0],
            vec[..]
                .iter()
                .map(|x| x.value)
                .collect::<Vec<_>>()
                .as_slice()
        );
    }

    #[test]
    fn filling_non_0th_span_expropriates_outstanding_span() {
        let mut guide =
            BufferGuide::<u32, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let _ = guide.push(0, None, 0, 0);
        let _ = guide.push(1, None, 0, 0);
        let _ = guide.push(2, None, 0, 0);
        let _ = guide.push(3, None, 0, 0); // first fill

        let _ = guide.push(4, None, 0, 0);
        let _ = guide.push(5, None, 0, 0);
        let _ = guide.push(6, None, 0, 0);
        let _ = guide.push(7, None, 0, 0); // second fill

        let _ = guide.push(8, None, 0, 0);
        let _ = guide.push(9, None, 0, 0);
        let _ = guide.push(10, None, 0, 0);
        let (_, order) = guide.push(11, None, 0, 0); // third fill

        let mut vec = [OrderInfo::new(0, GuideMetadata::new(4, 0, 0)); 8];

        order.write(&mut vec[..]);

        assert_eq!(
            [4, 5, 6, 7],
            vec[4..8]
                .iter()
                .map(|x| x.value)
                .collect::<Vec<_>>()
                .as_slice()
        );
    }

    #[test]
    fn push_after_last_depending_on_last_skips_id() {
        let mut guide =
            BufferGuide::<usize, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (mut loc, _) = guide.push(0, None, 0, 0);

        // With 32 pushes in total and one nop span, we'll have 31 regular
        // pushes and one forcing release.
        for i in 1..GUIDE_SIZE {
            (loc, _) = guide.push(i, Some(loc), 0, 0);
        }

        assert_eq!(33, loc.id.0);
    }

    #[test]
    fn forced_expropriation_carries_value_over() {
        let mut guide =
            BufferGuide::<usize, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (mut pos, _) = guide.push(0, None, 0, 0);

        // Fill all existing buffers and than continue for half the size, since
        // when new spans are created, the items are dependent immediately on
        // the last one, thus the guide will put it one span away.
        for i in 1..GUIDE_SIZE + GUIDE_SIZE / 2 {
            (pos, _) = guide.push(i, Some(pos), 0, 0);
        }

        let (_, order) = guide.push(0, Some(pos), 0, 0);

        let mut vec = vec![OrderInfo::new(0, GuideMetadata::new(4, 0, 0)); GUIDE_SIZE * 2 * 4];

        order.write(&mut vec[..]);

        // Also tests that values are written tightly, since we're looking for a
        // specific value at specific location. It's not really possible to test
        // that separately, due to how the interface behaves.
        assert_eq!(
            [32],
            vec[32..33]
                .iter()
                .map(|x| x.value)
                .collect::<Vec<_>>()
                .as_slice()
        );
    }

    #[test]
    fn dependent_pushes_are_dropped_at_least_parallelism_away() {
        let p = 4;

        let mut guide =
            BufferGuide::<u32, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(p);

        let (i1, _) = guide.push(0, None, 0, 0);
        let (i2, _) = guide.push(0, None, 0, 0);

        // [i1, i2,  _,  _] [ _,  _,  _,  _] [i3,  _,  _,  _]
        let (i3, _) = guide.push(0, Some(i2), 0, 0);
        // [i1, i2,  _,  _] [i4,  _,  _,  _] [i3,  _,  _,  _]
        let (i4, _) = guide.push(0, Some(i1), 0, 0);
        // [i1, i2,  _,  _] [i4, i5,  _,  _] [i3,  _,  _,  _]
        let (i5, _) = guide.push(0, Some(i2), 0, 0);

        assert_eq!(i2.id.0 + 2, i3.id.0);
        assert_eq!(i1.id.0 + 1, i4.id.0);
        assert_eq!(i2.id.0 + 1, i5.id.0);

        assert!(i4.pos >= i1.pos);
        assert!(i5.pos >= i2.pos);
    }

    #[test]
    fn initial_order_is_nop() {
        let mut guide =
            BufferGuide::<u32, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let _ = guide.push(0, None, 0, 0);
        let _ = guide.push(1, None, 0, 0);
        let _ = guide.push(2, None, 0, 0);
        let (_, order) = guide.push(3, None, 0, 0); // first fill

        let mut vec = [OrderInfo::new(0, GuideMetadata::new(4, 0, 0)); 0];

        order.write(&mut vec[..]);

        assert_eq!(0, vec.len());
    }

    #[test]
    fn empty_orders_are_empty() {
        let mut guide =
            BufferGuide::<u32, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (_, order) = guide.push(0, None, 0, 0);

        let mut vec = [OrderInfo::new(0, GuideMetadata::new(4, 0, 0)); 0];

        order.write(&mut vec[..]);

        assert_eq!(0, order.released_spans);
        assert_eq!(0, order.size());
        assert_eq!(0, vec.len());
    }

    #[test]
    fn flush_returns_all_items() {
        let mut guide =
            BufferGuide::<u32, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (i1, _) = guide.push(1, None, 0, 0);
        let (_, _) = guide.push(2, Some(i1), 0, 0);

        let mut vec = [OrderInfo::new(0, GuideMetadata::new(4, 0, 0)); 4];

        let order = guide.flush();

        order.write(&mut vec[..]);

        assert_eq!(
            [1, 2, 0, 0],
            vec[..]
                .iter()
                .map(|x| x.value)
                .collect::<Vec<_>>()
                .as_slice()
        );
    }

    #[test]
    fn flush_after_flush_returns_new_items() {
        let mut guide =
            BufferGuide::<u32, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (i1, _) = guide.push(1, None, 0, 0);
        let (i2, _) = guide.push(2, Some(i1), 0, 0);

        let mut vec = [OrderInfo::new(0, GuideMetadata::new(4, 0, 0)); 4];

        guide.flush();

        let (i3, _) = guide.push(3, Some(i2), 0, 0);
        let (_, _) = guide.push(4, Some(i3), 0, 0);

        let order = guide.flush();

        order.write(&mut vec[..]);

        assert_eq!(
            [0, 0, 3, 4],
            vec[..]
                .iter()
                .map(|x| x.value)
                .collect::<Vec<_>>()
                .as_slice()
        );
    }

    #[test]
    fn release_with_full_full_spans_returns_correct_parallelizm() {
        let mut guide =
            BufferGuide::<u32, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (_, _) = guide.push(1, None, 0, 0);
        let (_, _) = guide.push(2, None, 0, 0);
        let (_, _) = guide.push(3, None, 0, 0);
        let (_, order) = guide.push(4, None, 0, 0);

        assert_eq!(0, order.size());
        drop(order);

        let (_, _) = guide.push(5, None, 0, 0);
        let (_, _) = guide.push(6, None, 0, 0);
        let (_, _) = guide.push(7, None, 0, 0);
        let (_, order) = guide.push(8, None, 0, 0);

        let mut vec = [OrderInfo::new(0, GuideMetadata::new(0, 0, 0)); 4];

        order.write(&mut vec[..]);

        assert_eq!(
            [4, 4, 4, 4],
            vec[..]
                .iter()
                .map(|x| x.metadata.parallelism())
                .collect_vec()
                .as_slice()
        )
    }

    #[track_caller]
    fn assert_parallelism(expected: &[usize], actual: &[OrderInfo<u32>]) {
        // Map `actual` to a slice of `parallelism` values.
        let actual = actual
            .iter()
            .map(|x| x.metadata.parallelism())
            .collect_vec();

        // Assert that both slices have the same length. On failure, print the actual slices.
        assert_eq!(
            expected.len(),
            actual.len(),
            "Unexpected length: expected: {:?}, actual: {:?}",
            expected,
            actual
        );

        // Assert that the parallelism of each element is not greater than the expected value. On failure, print the actual slices.
        for (i, (e, a)) in expected.iter().zip(actual.iter()).enumerate() {
            assert!(
                a <= e,
                "Unexpected parallelism at index {}: expected: {:?}, actual: {:?}",
                i,
                expected,
                actual
            );
        }

        let location = std::panic::Location::caller();

        // Raise a warning if the actual parallelism is less than the expected value.
        for (i, (e, a)) in expected.iter().zip(actual.iter()).enumerate() {
            if a < e {
                log!(
                    "\x1b[33mWarning: unexpected parallelism at index {}: expected: {:?}, actual: {:?}, in{:?}\x1b[0m",
                    i,
                    expected,
                    actual,
                    location
                );
            }
        }
    }

    #[test]
    fn flush_release_with_full_part_spans_returns_correct_parallelism() {
        let mut guide =
            BufferGuide::<u32, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (_i1, _) = guide.push(1, None, 0, 0);
        let (_i2, _) = guide.push(2, None, 0, 0);
        let (_i3, _) = guide.push(3, None, 0, 0);
        let (_i4, order) = guide.push(4, None, 0, 0);

        assert_eq!(0, order.size());
        drop(order);

        let (_i5, _) = guide.push(5, None, 0, 0);
        let (_i6, _) = guide.push(6, None, 0, 0);

        // [i1, i2, i3, i4] [i5, i6, _, _]
        // [ 4,  4,  4,  3] [ x,  x, _, _]

        let order = guide.flush();

        let mut vec = [OrderInfo::new(0, GuideMetadata::new(0, 0, 0)); 6];

        order.write(&mut vec[..]);

        assert_parallelism(&[4, 4, 4, 3], &vec[0..4]);

        assert_eq!(
            [4, 4, 4, 3],
            vec[0..4]
                .iter()
                .map(|x| x.metadata.parallelism())
                .collect_vec()
                .as_slice()
        )
    }

    #[test]
    fn flush_release_with_part_full_spans_returns_correct_parallelism() {
        let mut guide =
            BufferGuide::<u32, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);
        let mut vec = [OrderInfo::new(0, GuideMetadata::new(0, 0, 0)); 9];

        let (_i1, _) = guide.push(1, None, 0, 0);
        let (_i2, _) = guide.push(2, None, 0, 0);
        let (_i3, _) = guide.push(3, None, 0, 0);
        let (_i4, order) = guide.push(4, None, 0, 0);

        assert_eq!(0, order.size());
        drop(order);

        // Goes to second span
        let (_i5, _) = guide.push(5, None, 0, 0);

        // goes to third span
        let (_i7, _) = guide.push(7, Some(_i3), 0, 0);
        let (_i8, _) = guide.push(8, Some(_i4), 0, 0);
        let (_i9, _) = guide.push(9, Some(_i4), 0, 0);
        let (_i10, order) = guide.push(10, Some(_i4), 0, 0);

        order.write(&mut vec[..]);
        drop(order);

        // [i1, i2, i3, i4] [i5, _, _, _] [i7, i8, i9, i10]
        // [ 4,  4,  3,  2] [ 4, _, _, _] [ 4,  3,  2,   1]

        let order = guide.flush();

        order.write(&mut vec[..]);

        assert_parallelism(&[4, 4, 3, 2, 4, 4, 3, 2, 1], &vec[..]);
    }

    #[test]
    fn flush_release_with_part_part_lt_spans_returns_correct_parallelism() {
        let mut guide =
            BufferGuide::<u32, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (_i1, _) = guide.push(1, None, 0, 0);
        let (_i2, _) = guide.push(2, None, 0, 0);
        let (_i3, _) = guide.push(3, None, 0, 0);
        let (_i4, order) = guide.push(4, None, 0, 0);

        assert_eq!(0, order.size());
        drop(order);

        // Goes to second span
        let (_i5, _) = guide.push(5, None, 0, 0);

        // goes to third span
        let (_i7, _) = guide.push(7, Some(_i3), 0, 0);
        let (_i8, _) = guide.push(8, Some(_i4), 0, 0);

        // [i1, i2, i3, i4] [i5, _, _, _] [i7, i8, _, _]
        // [ 4,  4,  3,  2] [ 2, _, _, _] [ 2,  1, _, _]

        let order = guide.flush();

        let mut vec = [OrderInfo::new(0, GuideMetadata::new(0, 0, 0)); 7];

        order.write(&mut vec[..]);

        assert_parallelism(&[4, 4, 3, 2, 2, 2, 1], &vec[..]);
    }

    #[test]
    fn flush_release_with_part_part_gt_spans_returns_correct_parallelism() {
        let mut guide =
            BufferGuide::<u32, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (_i1, _) = guide.push(1, None, 0, 0);
        let (_i2, _) = guide.push(2, None, 0, 0);
        let (_i3, _) = guide.push(3, None, 0, 0);
        let (_i4, order) = guide.push(4, None, 0, 0);

        assert_eq!(0, order.size());
        drop(order);

        // Goes to second span
        let (_i5, _) = guide.push(5, None, 0, 0);
        let (_i6, _) = guide.push(6, None, 0, 0);
        let (_i7, _) = guide.push(7, None, 0, 0);

        // goes to third span
        let (_i8, _) = guide.push(8, Some(_i5), 0, 0);

        // [i1, i2, i3, i4] [i5, i6, i7, _] [i8, _, _, _]
        // [ 4,  4,  4,  4] [ 3,  3,  2, _] [ 1, _, _, _]

        let order = guide.flush();

        let mut vec = [OrderInfo::new(0, GuideMetadata::new(0, 0, 0)); 8];

        order.write(&mut vec[..]);

        assert_parallelism(&[4, 4, 4, 4, 3, 3, 2, 1], &vec[..]);
    }

    #[test]
    fn flush_release_with_part_part_eq_spans_returns_correct_parallelism() {
        let mut guide =
            BufferGuide::<u32, GoldilocksField, Resolver<DoPerformRuntimeAsserts>>::new(4);

        let (_i1, _) = guide.push(1, None, 0, 0);
        let (_i2, _) = guide.push(2, None, 0, 0);
        let (_i3, _) = guide.push(3, None, 0, 0);
        let (_i4, order) = guide.push(4, None, 0, 0);

        assert_eq!(0, order.size());
        drop(order);

        // Goes to second span
        let (_i5, _) = guide.push(5, None, 0, 0);
        let (_i6, _) = guide.push(6, None, 0, 0);

        // goes to third span
        let (_i7, _) = guide.push(7, Some(_i5), 0, 0);
        let (_i8, _) = guide.push(8, Some(_i5), 0, 0);

        // [i1, i2, i3, i4] [i5, i6, _, _] [i7, i8, _, _]
        // [ 4,  4,  4,  3] [ 2,  2, _, _] [ 2,  1, _, _]

        let order = guide.flush();

        let mut vec = [OrderInfo::new(0, GuideMetadata::new(0, 0, 0)); 8];

        order.write(&mut vec[..]);

        assert_parallelism(&[4, 4, 4, 3, 2, 2, 2, 1], &vec[..]);
    }

    // TODO: test part full after flush (when the origin is to the left of the outstanding span)
}
