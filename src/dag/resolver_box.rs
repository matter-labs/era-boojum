#![allow(clippy::overly_complex_bool_expr)]
#![allow(clippy::nonminimal_bool)]

use itertools::Itertools;

use crate::field::SmallField;
use crate::log;
use std::marker::PhantomData;
use std::mem::size_of;

use crate::{
    cs::{traits::cs::DstBuffer, Place},
    utils::PipeOp,
};

use super::{guide::RegistrationNum, primitives::ResolverIx};

pub trait ResolutionFn<V> = FnOnce(&[V], &mut DstBuffer<V>) + Send + Sync;

pub struct ResolverBox<V> {
    // I assume that reallocations should not matter that much, in comparison
    // to increased complexity of enabling non reallocated growth. Even with
    // 1Gb copy we're talking about hundreds of milliseconds. As the size is
    // page multiple, the allocator should be able to efficiently take entire
    // pages to use and return them to the system when freed, although this
    // needs to be tested.
    container: Container,
    allocations: usize,
    phantom: PhantomData<V>,
}

impl<V> ResolverBox<V> {
    pub fn new() -> Self {
        Self::new_with_capacity(None)
    }

    pub fn new_with_capacity(size_power: Option<usize>) -> Self {
        let size_power = size_power.unwrap_or(26 /* 128MB */);

        ResolverBox {
            container: Container::new(size_power),
            allocations: 0,
            phantom: PhantomData,
        }
    }

    pub fn push<F>(
        &mut self,
        inputs: &[Place],
        outputs: &[Place],
        registration_num: RegistrationNum,
        resolve_fn: F,
        bind_fn_ref: fn(&Resolver, &[V], &mut [&mut V], bool),
    ) -> ResolverIx
    where
        F: ResolutionFn<V>,
    {
        // Nothing special about this size, just want to keep that resolver type
        // smaller.
        debug_assert!(size_of::<F>() < u16::MAX as usize);

        let ctor = ResolverDstCtor {
            inputs,
            outputs,
            registration_num,
            resolve_fn,
            bind_fn_ref,
        };
        let (loc, ptr) = self.container.reserve(ctor.size());

        unsafe { ctor.write(ptr as *mut _) };

        self.allocations += 1;

        debug_assert!(
            loc < u32::MAX as usize,
            "Allocated more than 4GB or resolvers. Signifies a faulty circuit."
        );

        ResolverIx::new_resolver(loc)
    }

    /// Retrives the resolution from the box.
    ///
    /// Safety: The index must be one of the provided values from `push` calls.
    pub unsafe fn get(&self, ix: ResolverIx) -> &Resolver {
        // TODO: `ix.normalized()` is unrelated to this domain, create `OrderValue` and clear `ResolverIx`.
        let ptr = (self.container.get_ptr(ix.normalized())) as *const ResolverHeader;

        Resolver::from(&*ptr)
    }
}

struct Container {
    pages: Vec<ContainerPage>,
    cur_page_ix: usize,
    // Using thins instead of relying on <Vec>::len() is a bit faster.
    page_size: usize,
    page_size_power: usize,
    page_ix_mask: usize,
    byte_ix_mask: usize,
}

impl Container {
    fn new(size_power: usize) -> Self {
        let byte_ix_mask = (1 << size_power) - 1;
        let page_ix_mask = !byte_ix_mask;

        let page_size = 1 << size_power;

        Self {
            pages: Vec::with_capacity(2048) // Can map 262GB with 128MB pages.
                .op(|x| x.push(ContainerPage::new(page_size))),
            cur_page_ix: 0,
            page_size,
            page_size_power: size_power,
            page_ix_mask,
            byte_ix_mask,
        }
    }

    /// Reserves a size amount of bytes and returns the index and the pointer
    /// for the reservation.
    //#[inline(always)]
    fn reserve(&mut self, size: usize) -> (usize, *mut u8) {
        let page = &mut self.pages[self.cur_page_ix];

        let page = match page.fits(size) {
            true => page,
            false => {
                // Since access to this location is not synched, we must not
                // reallocate the `pages` vector.
                self.pages
                    .push_within_capacity(ContainerPage::new(self.page_size))
                    .expect("Resolver Box: allocating more pages than expected.");
                self.cur_page_ix += 1;
                &mut self.pages[self.cur_page_ix]
            }
        };

        // Safety: Called `fits()` on existing page. New page is guaranteed to
        // be large enough.
        let (loc, ptr) = unsafe { page.reserve(size) };

        ((self.cur_page_ix << self.page_size_power) + loc, ptr)
    }

    fn get_ptr(&self, i: usize) -> *const u8 {
        let page_ix = (i & self.page_ix_mask) >> self.page_size_power;
        let byte_ix = i & self.byte_ix_mask;

        debug_assert_eq!(i / self.page_size, page_ix);
        debug_assert_eq!(i % self.page_size, byte_ix);

        &self.pages[page_ix].allocation[byte_ix] as *const _
    }
}

#[derive(Debug)]
struct ContainerPage {
    allocation: Box<[u8]>,
    commited: usize,
}

impl ContainerPage {
    fn new(size: usize) -> Self {
        let allocation = vec![0u8; size].into_boxed_slice();
        let commited = if cfg!(miri) {
            8 - allocation.as_ptr() as usize % std::mem::align_of::<ResolverHeader>()
        } else {
            0
        };

        if cfg!(miri) {
            log!(
                "Allocated page at {} aligned by {}",
                allocation.as_ptr() as usize,
                allocation.as_ptr() as usize % 8
            );
        }

        Self {
            allocation,
            commited,
        }
    }

    #[inline(always)]
    fn fits(&self, size: usize) -> bool {
        self.allocation.len() - self.commited >= size
    }

    unsafe fn reserve(&mut self, size: usize) -> (usize, *mut u8) {
        let loc = self.commited;
        self.commited += size;
        let ptr = self.allocation.as_mut_ptr().add(loc);

        if cfg!(not(miri)) {
            debug_assert!(loc % 4 == 0);
        }

        (loc, ptr)
    }
}

/// A constructor for a `Resolver`. Exists because `Resolver` is a DST.
struct ResolverDstCtor<'a, F, V>
where
    F: ResolutionFn<V>,
{
    inputs: &'a [Place],
    outputs: &'a [Place],
    registration_num: RegistrationNum,
    resolve_fn: F,
    bind_fn_ref: fn(&Resolver, &[V], &mut [&mut V], bool),
}

impl<F, V> ResolverDstCtor<'_, F, V>
where
    F: ResolutionFn<V>,
{
    fn size(&self) -> usize {
        assert!(
            size_of::<F>() % 4 == 0,
            "Only handling multiples of 4 sizes. Got: {}",
            size_of::<F>()
        );

        debug_assert!(self.inputs.len() <= u16::MAX as usize);
        debug_assert!(self.outputs.len() <= u16::MAX as usize);
        // Otherwise the size will be `x % 8 != 0` and the next allocation will
        // be aligned to 4 bytes.
        // This is a fix for a closure that was found in nature. I haven't been
        // able to reproduce it, but it was a 4 byte closure that was aligned to
        // 4 bytes.
        let closure_size = if size_of::<F>() == 4 {
            8
        } else {
            size_of::<F>()
        };

        let r = ((self.inputs.len() + self.outputs.len()) * size_of::<Place>())
            + size_of::<ResolverHeader>()
            + closure_size;

        assert!(
            r % 8 == 0,
            "Inputs: {:?}, Outputs: {:?}, size_of place: {}, size_of header: {}, size_of fn: {}, size_of ptr {}, total: {}",
            self.inputs,
            self.outputs,
            size_of::<Place>(),
            size_of::<ResolverHeader>(),
            size_of::<F>(),
            size_of::<*const ()>(),
            r
        );

        r
    }

    fn mk_header(&self) -> ResolverHeader {
        assert!(
            self.inputs.len() < u16::MAX as usize,
            "Too many inputs: {}",
            self.inputs.len()
        );
        assert!(
            self.outputs.len() < u16::MAX as usize,
            "Too many outputs: {}",
            self.outputs.len()
        );
        assert!(
            size_of::<F>() < u16::MAX as usize,
            "Closure is too large: {}",
            size_of::<F>()
        );

        ResolverHeader {
            input_count: self.inputs.len() as u16,
            output_count: self.outputs.len() as u16,
            registration_num: self.registration_num,
            resolve_fn_size: size_of::<F>() as u16,
            bind_fn_ref: self.bind_fn_ref as *const (),
        }
    }

    /// Safety: Requires that [`ptr` .. `ptr` + size()] is a an allocated unuzed
    /// memory.
    unsafe fn write(self, ptr: *mut ()) {
        let header = self.mk_header();

        // header
        let head_ptr = ptr as *mut ResolverHeader;
        if cfg!(not(miri)) {
            debug_assert_eq!(
                0,
                head_ptr as usize % std::mem::align_of_val(&header),
                "\n  Wrong alignment.\n   Align of header: {}\n   Ptr value: {}",
                std::mem::align_of_val(&header),
                head_ptr as usize
            );
        }

        head_ptr.write(header);

        // inputs
        let mut plc_ptr = head_ptr.add(1) as *mut Place;
        std::ptr::copy_nonoverlapping(self.inputs.as_ptr(), plc_ptr, self.inputs.len());

        // outputs
        plc_ptr = plc_ptr.add(self.inputs.len());
        std::ptr::copy_nonoverlapping(self.outputs.as_ptr(), plc_ptr, self.outputs.len());

        // resolver closure
        let f_ptr = plc_ptr.add(self.outputs.len()) as *mut F;
        debug_assert_eq!(0, f_ptr as usize % std::mem::align_of_val(&f_ptr));

        let closure_size = if size_of::<F>() == 4 {
            8
        } else {
            size_of::<F>()
        };

        debug_assert_eq!(
            self.size(),
            f_ptr as usize - ptr as usize + closure_size,
            "Unexpected amount of bytes written."
        );

        // Note: sometimes the alignment of the closure is 4. If you add any fields
        // after the closure, you need to make sure to offsset the pointer by 8 bytes.
        std::ptr::write(f_ptr, self.resolve_fn);
    }
}

struct ResolverHeader {
    input_count: u16,
    output_count: u16,
    resolve_fn_size: u16,
    /// This is the registration at which the resolver was added. This is going to be used in
    /// replay mode to map to the order index.
    registration_num: RegistrationNum,
    bind_fn_ref: *const (),
}

/// Payload layout:
/// ```ignore
/// [ inputs(Place) ][ outputs(Place) ][ resolve_fn(*) ]
/// ```
pub struct Resolver {
    header: ResolverHeader,
    payload: [u8],
}

impl Resolver {
    /// Safety: The header provided to this function must come from the location
    /// that has also stored the payload right after the header. Creating a header
    /// and calling this with it is UB.
    unsafe fn from(header: &ResolverHeader) -> &Self {
        let payload_size = header.input_count as usize * size_of::<Place>()
            + header.output_count as usize * size_of::<Place>()
            + header.resolve_fn_size as usize;

        let head_ptr = header as *const ResolverHeader as *const ();

        let ptr = std::ptr::from_raw_parts(head_ptr, payload_size);

        &*ptr
    }

    pub fn added_at(&self) -> RegistrationNum {
        self.header.registration_num
    }

    pub fn inputs(&self) -> &[Place] {
        // Safety: Ensured by ctor.
        unsafe {
            std::slice::from_raw_parts(
                self.payload.as_ptr() as *const Place,
                self.header.input_count as usize,
            )
        }
    }

    pub fn outputs(&self) -> &[Place] {
        // Safety: Ensured by ctor.
        unsafe {
            std::slice::from_raw_parts(
                (self.payload.as_ptr() as *const Place).add(self.header.input_count as usize),
                self.header.output_count as usize,
            )
        }
    }

    /// Safety:
    ///  - `T` must be of the actual data type stored in this resolver.
    ///  - Must never be called twice.
    pub unsafe fn resolve_fn<T>(&self) -> T {
        let ptr = self
            .payload
            .as_ptr()
            .cast::<Place>()
            .add(self.header.input_count as usize + self.header.output_count as usize)
            .cast::<T>();

        ptr.read()
    }

    pub fn bind_fn_ptr(&self) -> *const () /* TODO: we know the type here, should we use ref instead? */
    {
        self.header.bind_fn_ref
    }
}

pub(crate) fn invocation_binder<Fn, F: SmallField>(
    resolver: &Resolver,
    ins: &[F],
    out: &mut [&mut F],
    debug_track: bool,
) where
    Fn: FnOnce(&[F], &mut DstBuffer<F>) + Send + Sync,
{
    unsafe {
        // Safety: This is the actual type of the provided function.
        let bound = resolver.resolve_fn::<Fn>();

        if (cfg!(feature = "cr_paranoia_mode") || crate::dag::resolvers::mt::PARANOIA) && false {
            log!(
                "Ivk: Ins [{}], Out [{}], Out-addr [{}], Thread [{}]",
                resolver
                    .inputs()
                    .iter()
                    .map(|x| x.0.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                resolver
                    .outputs()
                    .iter()
                    .map(|x| x.0.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                out.iter()
                    .map(|x| *x as *const _ as usize)
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                std::thread::current().name().unwrap_or("unnamed")
            )
        }

        if (cfg!(feature = "cr_paranoia_mode") || crate::dag::resolvers::mt::PARANOIA)
            && debug_track
            && false
        {
            log!(
                "Ivk: provided inputs:\n   - {:?}",
                ins.iter().map(|x| x.as_raw_u64()).collect_vec()
            );
        }

        bound(ins, &mut DstBuffer::MutSliceIndirect(out, debug_track, 0));

        if (cfg!(feature = "cr_paranoia_mode") || crate::dag::resolvers::mt::PARANOIA)
            && debug_track
            && true
        {
            log!(
                "Ivk: calculated outputs:\n   - {:?}",
                out.iter().map(|x| x.as_raw_u64()).collect_vec()
            );
        }
    }
}

#[cfg(test)]
mod test {
    use std::{
        intrinsics::size_of,
        mem::{align_of, size_of_val},
    };

    use rand::random;

    use crate::{
        cs::{traits::cs::DstBuffer, Place, Variable},
        dag::{guide::RegistrationNum, resolver_box::ResolverHeader},
        field::{goldilocks::GoldilocksField, Field},
        log,
    };

    use super::{invocation_binder, Resolver, ResolverBox};

    type F = GoldilocksField;

    #[derive(Copy, Clone)]
    struct Context {
        _one: u32,
        _two: u64,
    }

    #[test]
    fn header_size_alignment() {
        let resolution_fn = |_: &[F], _: &mut DstBuffer<F>| {};

        let binder = get_binder(&resolution_fn);

        let header = ResolverHeader {
            input_count: 0,
            output_count: 0,
            registration_num: 0,
            resolve_fn_size: 0,
            bind_fn_ref: binder as *const (),
        };

        let base_addr = &header as *const _ as usize;

        log!(
            "input_count offset: {}",
            &header.input_count as *const _ as usize - base_addr
        );
        log!(
            "output_count offset: {}",
            &header.output_count as *const _ as usize - base_addr
        );
        log!(
            "resolve_fn_size offset: {}",
            &header.resolve_fn_size as *const _ as usize - base_addr
        );
        log!(
            "bind_fn_ref offset: {}",
            &header.bind_fn_ref as *const _ as usize - base_addr
        );

        assert_eq!(size_of::<ResolverHeader>(), 24);
        assert_eq!(align_of::<ResolverHeader>(), 8);
    }

    fn run_invariant_asserts<Fn>(
        ins: &[Place],
        out: &[Place],
        registration_num: RegistrationNum,
        res_fn: &Fn,
        bind_fn: fn(&Resolver, &[F], &mut [&mut F], bool),
        value: &Resolver,
    ) where
        Fn: FnOnce(&[F], &mut DstBuffer<F>) + Send + Sync,
    {
        let fn_bytes_exp = unsafe {
            std::slice::from_raw_parts(res_fn as *const _ as *const u8, std::mem::size_of::<Fn>())
        };
        let fn_bytes_act = unsafe {
            std::slice::from_raw_parts(
                &value.resolve_fn::<Fn>() as *const _ as *const u8,
                std::mem::size_of::<Fn>(),
            )
        };
        assert_eq!(fn_bytes_exp, fn_bytes_act);

        assert_eq!(ins.len(), value.header.input_count as usize);
        assert_eq!(out.len(), value.header.output_count as usize);

        assert_eq!(ins.len(), { value.inputs().len() });
        assert_eq!(out.len(), { value.outputs().len() });

        assert_eq!(registration_num, value.header.registration_num);

        assert!(ins.iter().zip(value.inputs()).all(|(x, y)| { x == y }));
        assert!(out.iter().zip(value.outputs()).all(|(x, y)| { x == y }));

        assert!(value.bind_fn_ptr() as *const _ as usize % 4 == 0);

        let bind_fn_exp_addr = bind_fn as *const u8 as usize;
        let bind_fn_act_addr = value.header.bind_fn_ref as *const u8 as usize;

        assert_eq!(bind_fn_exp_addr, bind_fn_act_addr);
    }

    fn get_binder<Fn: FnOnce(&[F], &mut DstBuffer<F>) + Send + Sync>(
        _: &Fn,
    ) -> fn(&Resolver, &[F], &mut [&mut F], bool) {
        invocation_binder::<Fn, F>
    }

    #[test]
    fn storing_retreiving_upholds_invariant() {
        let mut rbox = ResolverBox::new();

        let resolution_fn = |_: &[F], _: &mut DstBuffer<F>| {};

        let ins = [
            Place::from_variable(Variable::from_variable_index(0)),
            Place::from_variable(Variable::from_variable_index(1)),
        ];

        let out = [
            Place::from_variable(Variable::from_variable_index(2)),
            Place::from_variable(Variable::from_variable_index(3)),
            Place::from_variable(Variable::from_variable_index(3)),
        ];

        let binder = get_binder(&resolution_fn);

        let ix = rbox.push(&ins, &out, 1 << 7, resolution_fn, binder);

        let value = unsafe { rbox.get(ix) };

        run_invariant_asserts(&ins, &out, 1 << 7, &resolution_fn, binder, value);
    }

    #[test]
    #[ignore = "Need to force alignment of closure to be 4 bytes."]
    fn storing_retrieving_unaligned_closure_upholds_invariant() {
        let mut rbox = ResolverBox::new();

        let n: u8 = 1 + random::<u8>() % 100;

        let resolution_fn = |ins: &[F], outs: &mut DstBuffer<F>| {
            let mut r = ins[0];

            r.add_assign(&F::from_u64_with_reduction(n as u64));

            outs.push(r);
        };

        assert_eq!(4, size_of_val(&resolution_fn));

        let ins = [
            Place::from_variable(Variable::from_variable_index(0)),
            Place::from_variable(Variable::from_variable_index(1)),
        ];

        let out = [
            Place::from_variable(Variable::from_variable_index(2)),
            Place::from_variable(Variable::from_variable_index(3)),
            Place::from_variable(Variable::from_variable_index(3)),
        ];

        let binder = get_binder(&resolution_fn);

        let ix = rbox.push(&ins, &out, 1 << 7, resolution_fn, binder);

        let value = unsafe { rbox.get(ix) };

        run_invariant_asserts(&ins, &out, 1 << 7, &resolution_fn, binder, value);
    }

    #[test]
    fn subsequent_stores_increment_location_according_to_size() {
        let mut rbox = ResolverBox::new();

        let item1 = 1;
        let item2 = 2;

        let resolution_fn = |_: &[F], outs: &mut DstBuffer<F>| {
            outs.push(F::from_nonreduced_u64(item1));
            outs.push(F::from_nonreduced_u64(item2));
        };

        let ins = [
            Place::from_variable(Variable::from_variable_index(0)),
            Place::from_variable(Variable::from_variable_index(1)),
        ];

        let out = [
            Place::from_variable(Variable::from_variable_index(2)),
            Place::from_variable(Variable::from_variable_index(3)),
            Place::from_variable(Variable::from_variable_index(3)),
        ];

        let expected_move = size_of::<ResolverHeader>() + size_of_val(&resolution_fn) + 5 * 8;

        let binder = get_binder(&resolution_fn);

        let _ = rbox.push(&ins, &out, 1 << 7, resolution_fn, binder);
        let ix = rbox.push(&ins, &out, 1 << 7, resolution_fn, binder);

        assert_eq!(expected_move, ix.normalized());

        let value = unsafe { rbox.get(ix) };

        run_invariant_asserts(&ins, &out, 1 << 7, &resolution_fn, binder, value)
    }

    #[test]
    fn subsequent_stores_uphold_previous_invariant() {
        let mut rbox = ResolverBox::new();

        let item1 = 1;
        let item2 = 2;

        let resolution_fn = |_: &[F], outs: &mut DstBuffer<F>| {
            outs.push(F::from_nonreduced_u64(item1));
            outs.push(F::from_nonreduced_u64(item2));
        };

        let ins = [
            Place::from_variable(Variable::from_variable_index(0)),
            Place::from_variable(Variable::from_variable_index(1)),
        ];

        let out = [
            Place::from_variable(Variable::from_variable_index(2)),
            Place::from_variable(Variable::from_variable_index(3)),
            Place::from_variable(Variable::from_variable_index(3)),
        ];

        let binder = get_binder(&resolution_fn);

        let ix = rbox.push(&ins, &out, 1 << 7, resolution_fn, binder);
        let _ = rbox.push(&ins, &out, 1 << 7, resolution_fn, binder);

        let value = unsafe { rbox.get(ix) };

        run_invariant_asserts(&ins, &out, 1 << 7, &resolution_fn, binder, value)
    }

    #[test]
    fn store_grows() {
        let mut rbox = ResolverBox::new_with_capacity(Some(6));

        let resolution_fn = |_: &[F], _: &mut DstBuffer<F>| {};

        let ins = [
            Place::from_variable(Variable::from_variable_index(0)),
            Place::from_variable(Variable::from_variable_index(1)),
        ];

        let out = [
            Place::from_variable(Variable::from_variable_index(2)),
            Place::from_variable(Variable::from_variable_index(3)),
            Place::from_variable(Variable::from_variable_index(3)),
        ];

        let binder = get_binder(&resolution_fn);

        let _ = rbox.push(&ins, &out, 1 << 7, resolution_fn, binder);
        let _ = rbox.push(&ins, &out, 1 << 7, resolution_fn, binder);
    }

    #[test]
    fn store_upholds_invariant_on_grow() {
        let mut rbox = ResolverBox::new_with_capacity(Some(6));

        let resolution_fn = |_: &[F], _: &mut DstBuffer<F>| {};

        let ins = [
            Place::from_variable(Variable::from_variable_index(0)),
            Place::from_variable(Variable::from_variable_index(1)),
        ];

        let out = [
            Place::from_variable(Variable::from_variable_index(2)),
            Place::from_variable(Variable::from_variable_index(3)),
            Place::from_variable(Variable::from_variable_index(3)),
        ];

        let binder = get_binder(&resolution_fn);

        let ix1 = rbox.push(&ins, &out, 1 << 7, resolution_fn, binder);
        let ix2 = rbox.push(&ins, &out, 1 << 7, resolution_fn, binder);

        let value = unsafe { rbox.get(ix1) };
        run_invariant_asserts(&ins, &out, 1 << 7, &resolution_fn, binder, value);

        let value = unsafe { rbox.get(ix2) };
        run_invariant_asserts(&ins, &out, 1 << 7, &resolution_fn, binder, value);
    }

    #[test]
    fn store_doesnt_drop_fn() {
        struct DroppedContext<'a> {
            times_invoked: &'a mut u32,
            value: u64,
        }

        impl<'a> Drop for DroppedContext<'a> {
            fn drop(&mut self) {
                *self.times_invoked += 1;
            }
        }

        let mut rbox = ResolverBox::new();

        let mut drop_invoked = 0;

        let ctx = DroppedContext {
            times_invoked: &mut drop_invoked,
            value: 1,
        };

        let resolution_fn = move |_: &[F], outs: &mut DstBuffer<F>| {
            let ctx = ctx;
            outs.push(F::from_nonreduced_u64(ctx.value));
        };

        let ins = [
            Place::from_variable(Variable::from_variable_index(0)),
            Place::from_variable(Variable::from_variable_index(1)),
        ];

        let out = [
            Place::from_variable(Variable::from_variable_index(2)),
            Place::from_variable(Variable::from_variable_index(3)),
            Place::from_variable(Variable::from_variable_index(3)),
        ];

        let binder = get_binder(&resolution_fn);

        let _ = rbox.push(&ins, &out, 1 << 7, resolution_fn, binder);

        assert_eq!(0, drop_invoked);
    }
}
