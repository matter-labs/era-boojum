use crate::log;
use std::{
    arch::asm,
    intrinsics::const_eval_select,
    time::{Duration, Instant},
};

use derivative::Derivative;

use crate::cs::traits::GoodAllocator;

#[inline(always)]
pub const fn branch_hint() {
    unsafe { const_eval_select((), branch_hint_ct, branch_hint_rt) };
}

#[inline(always)]
fn branch_hint_rt() {
    unsafe {
        asm!("", options(nomem, nostack, preserves_flags));
    }
}

#[inline(always)]
const fn branch_hint_ct() {}

#[inline(always)]
pub const fn assume(p: bool) {
    debug_assert!(p);
    if !p {
        unsafe {
            std::hint::unreachable_unchecked();
        }
    }
}

#[inline(always)]
pub const fn split(x: u128) -> (u64, u64) {
    (x as u64, (x >> 64) as u64)
}

#[inline]
pub const fn num_bits_u64(n: u64) -> usize {
    (64 - n.leading_zeros()) as usize
}

/// Allocate a vector of type T, but with extra restriction that it has an alignment
/// of type U. Capacity should be divisible by size_of::<U>/size_of::<T>
#[inline]
pub fn allocate_in_with_alignment_of<T: Sized, U: Sized, A: GoodAllocator>(
    capacity: usize,
    allocator: A,
) -> Vec<T, A> {
    debug_assert!(std::mem::size_of::<T>() > 0);
    debug_assert!(std::mem::size_of::<U>() > 0);
    debug_assert!(std::mem::size_of::<U>() % std::mem::size_of::<T>() == 0);
    let size_factor = std::mem::size_of::<U>() / std::mem::size_of::<T>();
    if size_factor == 0 {
        return Vec::with_capacity_in(capacity, allocator);
    }
    debug_assert!(capacity % size_factor == 0);
    let modified_capacity = capacity / size_factor;
    let (ptr, len, _, allocator) =
        Vec::<U, A>::with_capacity_in(modified_capacity, allocator).into_raw_parts_with_alloc();
    debug_assert_eq!(len, 0);
    unsafe { Vec::<T, A>::from_raw_parts_in(ptr as *mut T, len, capacity, allocator) }
}

// Allocate a vector of type T, but with extra restriction that it has an alignment
// of type U. Capacity should be divisible by size_of::<U>/size_of::<T>
#[inline]
pub fn allocate_with_alignment_of<T: Sized, U: Sized>(capacity: usize) -> Vec<T> {
    allocate_in_with_alignment_of::<T, U, std::alloc::Global>(capacity, std::alloc::Global)
}

#[inline]
pub fn initialize_in_with_alignment_of<T: Sized + Copy, U: Sized, A: GoodAllocator>(
    value: T,
    length: usize,
    allocator: A,
) -> Vec<T, A> {
    let mut new = allocate_in_with_alignment_of::<T, U, A>(length, allocator);
    new.resize(length, value);

    new
}

#[inline]
pub fn initialize_with_alignment_of<T: Sized + Copy, U: Sized>(value: T, length: usize) -> Vec<T> {
    let mut new = allocate_with_alignment_of::<T, U>(length);
    new.resize(length, value);

    new
}

#[inline]
pub fn clone_respecting_allignment<T: Sized + Clone, U: Sized, A: GoodAllocator>(
    input: &Vec<T, A>,
) -> Vec<T, A> {
    // we can not just use alignment of pointer in the input because it can be larger
    let mut result = allocate_in_with_alignment_of::<T, U, _>(input.len(), A::default());
    result.extend_from_slice(&input[..]);

    result
}

// Allocate a vector of type T, but with extra restriction that it has an alignment
// of type U. Capacity should be divisible by size_of::<U>/size_of::<T>
#[inline]
pub fn cast_check_alignment<T: Sized, U: Sized, A: GoodAllocator>(a: Vec<T, A>) -> Vec<U, A> {
    debug_assert!(std::mem::size_of::<T>() > 0);
    debug_assert!(std::mem::size_of::<U>() > 0);
    debug_assert!(std::mem::size_of::<U>() % std::mem::size_of::<T>() == 0);
    let size_factor = std::mem::size_of::<U>() / std::mem::size_of::<T>();
    debug_assert!(size_factor > 0);
    let (ptr, len, capacity, allocator) = a.into_raw_parts_with_alloc();
    debug_assert!(len % size_factor == 0);
    debug_assert!(capacity % size_factor == 0);
    debug_assert!(ptr.addr() % std::mem::align_of::<U>() == 0);
    let modified_len = len / size_factor;
    let modified_capacity = capacity / size_factor;
    unsafe {
        Vec::<U, A>::from_raw_parts_in(ptr as *mut U, modified_len, modified_capacity, allocator)
    }
}

// Allocate a vector of type T, but with extra restriction that it has an alignment
// of type U. Capacity should be divisible by size_of::<U>/size_of::<T>
#[inline]
pub fn cast_check_alignment_ref_mut_pack<T: Sized, U: Sized>(a: &mut [T]) -> &mut [U] {
    debug_assert!(std::mem::size_of::<T>() > 0);
    debug_assert!(std::mem::size_of::<U>() > 0);
    debug_assert!(std::mem::size_of::<U>() % std::mem::size_of::<T>() == 0);
    let size_factor = std::mem::size_of::<U>() / std::mem::size_of::<T>();
    debug_assert!(size_factor > 0);
    let len = a.len();
    let ptr = a.as_mut_ptr();
    debug_assert!(len % size_factor == 0);
    debug_assert!(ptr.addr() % std::mem::align_of::<U>() == 0);
    let modified_len = len / size_factor;
    unsafe { std::slice::from_raw_parts_mut(ptr as *mut U, modified_len) }
}

// Allocate a vector of type T, but with extra restriction that it has an alignment
// of type U. Capacity should be divisible by size_of::<U>/size_of::<T>
#[inline]
pub fn cast_check_alignment_ref_mut_unpack<T: Sized, U: Sized>(a: &mut [T]) -> &mut [U] {
    debug_assert!(std::mem::size_of::<T>() > 0);
    debug_assert!(std::mem::size_of::<U>() > 0);
    debug_assert!(std::mem::size_of::<T>() % std::mem::size_of::<U>() == 0);
    let size_factor = std::mem::size_of::<T>() / std::mem::size_of::<U>();
    debug_assert!(size_factor > 0);
    let len = a.len();
    let ptr = a.as_mut_ptr();
    debug_assert!(ptr.addr() % std::mem::align_of::<U>() == 0);
    let modified_len = len * size_factor;
    unsafe { std::slice::from_raw_parts_mut(ptr as *mut U, modified_len) }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct LSBIterator<'a> {
    over: &'a [u64],
    n: usize,
}

impl<'a> LSBIterator<'a> {
    pub const fn new(source: &'a [u64]) -> Self {
        Self { over: source, n: 0 }
    }
}

impl<'a> Iterator for LSBIterator<'a> {
    type Item = bool;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.n >= self.over.len() * 64 {
            return None;
        }

        let word_idx = self.n / 64;
        let bit_idx = self.n % 64;

        self.n += 1;

        Some(self.over[word_idx] & (1u64 << bit_idx) != 0)
    }
}

impl<'a> ExactSizeIterator for LSBIterator<'a> {
    fn len(&self) -> usize {
        self.over.len() * 64 - self.n
    }
}

pub fn wait_to_attach() {
    log!("Can attach now");

    loop {
        match std::fs::read_to_string(std::env::var("DEBUG_ATTACH_FILE").unwrap()) {
            Ok(contents) if contents.trim() == "go" => {
                let _ = std::fs::write(std::env::var("DEBUG_ATTACH_FILE").unwrap(), "nogo"); // Cause keep forgetting
                break;
            }
            _ => (),
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

pub struct DilatoryPrinter {
    last_print_time: Instant,
}

impl DilatoryPrinter {
    pub fn new() -> Self {
        Self {
            last_print_time: Instant::now(),
        }
    }

    pub fn print(&mut self, s: String) {
        let elapsed = self.last_print_time.elapsed();
        if elapsed >= Duration::from_secs(1) {
            log!("{}", s);
            self.last_print_time = Instant::now();
        }
    }
}

use std::cell::UnsafeCell;

pub trait UnsafeCellEx<T> {
    /// Dereferences the contained value. Synonym for `&*self.get()`.
    ///
    /// # Safety
    ///
    /// The value must not be referenced outside of the actual lifetime of the UnsafeCell.
    ///
    /// Violating this condition is undefined behavior.
    unsafe fn u_deref(&self) -> &'static T;

    /// Mutably dereferences the contained value. Synonym for `&mut *self.get()`.
    ///
    /// # Safety
    ///
    /// 1. The value must not be referenced outside of the actual lifetime of the UnsafeCell.
    /// 2. The caller must ensure that no other references to the value exist at the same time.
    ///
    /// Violating either of these conditions is undefined behavior.
    unsafe fn u_deref_mut(&self) -> &'static mut T;
}

impl<T> UnsafeCellEx<T> for UnsafeCell<T> {
    /// Dereferences the contained value. Synonym for `&*self.get()`.
    unsafe fn u_deref(&self) -> &'static T {
        std::mem::transmute::<&T, &'static T>(&*self.get())
    }

    /// Mutably dereferences the contained value. Synonym for `&mut *self.get()`.
    unsafe fn u_deref_mut(&self) -> &'static mut T {
        std::mem::transmute::<&mut T, &'static mut T>(&mut *self.get())
    }
}

pub trait PipeOp<T> {
    fn to<F, U>(self, f: F) -> U
    where
        F: FnOnce(T) -> U;

    fn op<F>(self, f: F) -> T
    where
        F: FnOnce(&mut T);
}

impl<T> PipeOp<T> for T {
    fn to<F, U>(self, f: F) -> U
    where
        F: FnOnce(T) -> U,
    {
        f(self)
    }

    fn op<F>(mut self, f: F) -> T
    where
        F: FnOnce(&mut T),
    {
        f(&mut self);
        self
    }
}

pub(crate) fn serialize_arc<T: serde::Serialize, S>(
    t: &std::sync::Arc<T>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    (*t).serialize(serializer)
}

pub(crate) fn deserialize_arc<'de, D, T: serde::Deserialize<'de>>(
    deserializer: D,
) -> Result<std::sync::Arc<T>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let res = T::deserialize(deserializer)?;
    let arc = std::sync::Arc::new(res);

    Ok(arc)
}

pub fn serialize_vec_with_allocator<T: serde::Serialize, S, A: GoodAllocator>(
    t: &Vec<T, A>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    let mut seq = serializer.serialize_seq(Some(t.len()))?;
    use serde::ser::SerializeSeq;

    for el in t.iter() {
        seq.serialize_element(el)?;
    }
    seq.end()
}

struct VecVisitor<T, A> {
    element: std::marker::PhantomData<(T, A)>,
}

impl<'de, T, A: GoodAllocator> serde::de::Visitor<'de> for VecVisitor<T, A>
where
    T: serde::Deserialize<'de>,
{
    type Value = Vec<T, A>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a vector")
    }

    fn visit_seq<B>(self, mut seq: B) -> Result<Self::Value, B::Error>
    where
        B: serde::de::SeqAccess<'de>,
    {
        let expected_len = seq.size_hint().unwrap_or(0);
        let mut vector = Vec::with_capacity_in(expected_len, A::default());
        for i in 0..expected_len {
            let el = seq
                .next_element()?
                .ok_or_else(|| serde::de::Error::invalid_length(i, &self))?;
            vector.push(el);
        }

        Ok(vector)
    }
}

pub fn deserialize_vec_with_allocator<'de, D, T: serde::Deserialize<'de>, A: GoodAllocator>(
    deserializer: D,
) -> Result<Vec<T, A>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let visitor = VecVisitor::<T, A> {
        element: std::marker::PhantomData,
    };
    deserializer.deserialize_seq(visitor)
}

pub(crate) fn serialize_vec_arc<T: serde::Serialize, S, A: GoodAllocator>(
    t: &Vec<std::sync::Arc<T>, A>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    let mut seq = serializer.serialize_seq(Some(t.len()))?;
    use serde::ser::SerializeSeq;

    for el in t.iter() {
        let inner = &**el;
        seq.serialize_element(inner)?;
    }
    seq.end()
}

struct VecArcVisitor<T, A> {
    element: std::marker::PhantomData<(T, A)>,
}

impl<'de, T, A: GoodAllocator> serde::de::Visitor<'de> for VecArcVisitor<T, A>
where
    T: serde::Deserialize<'de>,
{
    type Value = Vec<std::sync::Arc<T>, A>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a vector")
    }

    fn visit_seq<B>(self, mut seq: B) -> Result<Self::Value, B::Error>
    where
        B: serde::de::SeqAccess<'de>,
    {
        let expected_len = seq.size_hint().unwrap_or(0);
        let mut vector = Vec::with_capacity_in(expected_len, A::default());
        for i in 0..expected_len {
            let el = seq
                .next_element()?
                .ok_or_else(|| serde::de::Error::invalid_length(i, &self))?;
            vector.push(std::sync::Arc::new(el));
        }

        Ok(vector)
    }
}

pub(crate) fn deserialize_vec_arc<'de, D, T: serde::Deserialize<'de>, A: GoodAllocator>(
    deserializer: D,
) -> Result<Vec<std::sync::Arc<T>, A>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let visitor = VecArcVisitor::<T, A> {
        element: std::marker::PhantomData,
    };
    deserializer.deserialize_seq(visitor)
}

#[derive(serde::Serialize)]
struct VecProxySer<'a, T: serde::Serialize, A: GoodAllocator> {
    #[serde(serialize_with = "crate::utils::serialize_vec_with_allocator")]
    inner: &'a Vec<T, A>,
}

pub fn serialize_vec_vec_with_allocators<
    T: serde::Serialize,
    S,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    t: &Vec<Vec<T, A>, B>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    let mut seq = serializer.serialize_seq(Some(t.len()))?;
    use serde::ser::SerializeSeq;

    for el in t.iter() {
        let proxy = VecProxySer { inner: el };
        seq.serialize_element(&proxy)?;
    }
    seq.end()
}

#[derive(serde::Deserialize)]
#[serde(bound = "T: serde::Deserialize<'de>")]
struct VecProxyDeser<T, A: GoodAllocator> {
    #[serde(deserialize_with = "crate::utils::deserialize_vec_with_allocator")]
    inner: Vec<T, A>,
}

struct VecVecVisitor<T, A, B> {
    element: std::marker::PhantomData<(T, A, B)>,
}

impl<'de, T, A: GoodAllocator, B: GoodAllocator> serde::de::Visitor<'de> for VecVecVisitor<T, A, B>
where
    T: serde::Deserialize<'de>,
{
    type Value = Vec<Vec<T, A>, B>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a vector")
    }

    fn visit_seq<C>(self, mut seq: C) -> Result<Self::Value, C::Error>
    where
        C: serde::de::SeqAccess<'de>,
    {
        let expected_len = seq.size_hint().unwrap_or(0);
        let mut vector: Vec<Vec<T, A>, B> = Vec::with_capacity_in(expected_len, B::default());
        for i in 0..expected_len {
            let el: VecProxyDeser<T, A> = seq
                .next_element()?
                .ok_or_else(|| serde::de::Error::invalid_length(i, &self))?;
            vector.push(el.inner);
        }

        Ok(vector)
    }
}

pub fn deserialize_vec_vec_with_allocators<
    'de,
    D,
    T: serde::Deserialize<'de>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    deserializer: D,
) -> Result<Vec<Vec<T, A>, B>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let visitor = VecVecVisitor::<T, A, B> {
        element: std::marker::PhantomData,
    };
    deserializer.deserialize_seq(visitor)
}
