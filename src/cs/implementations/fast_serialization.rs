use core::slice;
use std::{
    alloc::Allocator,
    error::Error,
    io::{Read, Write},
};

use crate::{cs::traits::GoodAllocator, field::SmallField, utils::allocate_in_with_alignment_of};

// We expect many primitives to allow memcopy-like serialization/deserialization
// (we need copy to preserve alignment!)
pub trait MemcopySerializable: 'static + Sized {
    fn write_into_buffer<W: Write>(&self, dst: W) -> Result<(), Box<dyn Error>>;
    fn read_from_buffer<R: Read>(src: R) -> Result<Self, Box<dyn Error>>;
}

pub fn read_vec_from_buffer<T: MemcopySerializable, A: GoodAllocator, R: Read>(
    mut src: R,
) -> Result<Vec<T, A>, Box<dyn Error>> {
    let mut len_le_bytes = [0u8; 8];
    src.read_exact(&mut len_le_bytes).map_err(Box::new)?;
    let length: u64 = u64::from_le_bytes(len_le_bytes);
    let length = length as usize;

    let mut result = Vec::with_capacity_in(length, A::default());
    for _ in 0..length {
        let el: T = MemcopySerializable::read_from_buffer(&mut src)?;
        result.push(el);
    }

    Ok(result)
}

pub fn write_vec_into_buffer<T: MemcopySerializable, W: Write, A: Allocator>(
    src: &Vec<T, A>,
    mut dst: W,
) -> Result<(), Box<dyn Error>> {
    let len_le_bytes = (src.len() as u64).to_le_bytes();
    dst.write_all(&len_le_bytes).map_err(Box::new)?;

    for el in src.iter() {
        MemcopySerializable::write_into_buffer(el, &mut dst)?;
    }

    Ok(())
}

// we provide only non-field related base implementations, that can be used with vector functions above
impl MemcopySerializable for u32 {
    fn read_from_buffer<R: Read>(mut src: R) -> Result<Self, Box<dyn Error>> {
        let mut le_bytes = [0u8; 4];
        src.read_exact(&mut le_bytes).map_err(Box::new)?;
        let el: u32 = u32::from_le_bytes(le_bytes);

        Ok(el)
    }

    fn write_into_buffer<W: Write>(&self, mut dst: W) -> Result<(), Box<dyn Error>> {
        let le_bytes = self.to_le_bytes();
        dst.write_all(&le_bytes).map_err(Box::new)?;

        Ok(())
    }
}

impl MemcopySerializable for u64 {
    fn read_from_buffer<R: Read>(mut src: R) -> Result<Self, Box<dyn Error>> {
        let mut le_bytes = [0u8; 8];
        src.read_exact(&mut le_bytes).map_err(Box::new)?;
        let el: u64 = u64::from_le_bytes(le_bytes);

        Ok(el)
    }

    fn write_into_buffer<W: Write>(&self, mut dst: W) -> Result<(), Box<dyn Error>> {
        let le_bytes = self.to_le_bytes();
        dst.write_all(&le_bytes).map_err(Box::new)?;

        Ok(())
    }
}

impl MemcopySerializable for usize {
    fn read_from_buffer<R: Read>(mut src: R) -> Result<Self, Box<dyn Error>> {
        let mut le_bytes = [0u8; 8];
        src.read_exact(&mut le_bytes).map_err(Box::new)?;
        let el: u64 = u64::from_le_bytes(le_bytes);
        let this = el
            .try_into()
            .map_err(|_| Box::<dyn Error>::from(format!("0x{:016x} doesn't fit into usize", el)))?;

        Ok(this)
    }

    fn write_into_buffer<W: Write>(&self, mut dst: W) -> Result<(), Box<dyn Error>> {
        let as_u64: u64 = (*self)
            .try_into()
            .map_err(|_| Box::<dyn Error>::from(format!("0x{:x} doesn't fit into u64", self)))?;
        let le_bytes = as_u64.to_le_bytes();
        dst.write_all(&le_bytes).map_err(Box::new)?;

        Ok(())
    }
}

// and trivial case for tuples
impl<A: MemcopySerializable, B: MemcopySerializable> MemcopySerializable for (A, B) {
    fn read_from_buffer<R: Read>(mut src: R) -> Result<Self, Box<dyn Error>> {
        let a = <A as MemcopySerializable>::read_from_buffer(&mut src)?;
        let b = <B as MemcopySerializable>::read_from_buffer(&mut src)?;

        Ok((a, b))
    }

    fn write_into_buffer<W: Write>(&self, mut dst: W) -> Result<(), Box<dyn Error>> {
        <A as MemcopySerializable>::write_into_buffer(&self.0, &mut dst)?;
        <B as MemcopySerializable>::write_into_buffer(&self.1, &mut dst)?;

        Ok(())
    }
}

impl<T: MemcopySerializable> MemcopySerializable for std::sync::Arc<T> {
    fn write_into_buffer<W: Write>(&self, dst: W) -> Result<(), Box<dyn Error>> {
        let inner: &T = self;
        MemcopySerializable::write_into_buffer(inner, dst)?;

        Ok(())
    }

    fn read_from_buffer<R: Read>(src: R) -> Result<Self, Box<dyn Error>> {
        let inner: T = MemcopySerializable::read_from_buffer(src)?;

        Ok(std::sync::Arc::new(inner))
    }
}

// Prime field like vectors are the special case, and it's only implemented for vector!

impl<
        F: SmallField,
        A: GoodAllocator,
        P: crate::field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    > MemcopySerializable for Vec<P, A>
where
    Self: 'static,
{
    fn write_into_buffer<W: Write>(&self, mut dst: W) -> Result<(), Box<dyn Error>> {
        let len_as_base = self.len() * P::SIZE_FACTOR;
        let len_le_bytes = (len_as_base as u64).to_le_bytes();
        dst.write_all(&len_le_bytes).map_err(Box::new)?;

        if F::CAN_CAST_VECTOR_TO_U64_LE_VECTOR {
            // do some magic
            let len = len_as_base * 8;
            let ptr: *const u8 = self.as_ptr().cast();
            let src = unsafe { slice::from_raw_parts(ptr, len) };

            dst.write_all(src).map_err(Box::new)?;
        } else {
            // slow path
            let self_as_base = P::slice_into_base_slice(self);
            for el in self_as_base.iter() {
                let el_le = el.as_u64_reduced().to_le_bytes();
                dst.write_all(&el_le).map_err(Box::new)?;
            }
        }

        Ok(())
    }

    fn read_from_buffer<R: Read>(mut src: R) -> Result<Self, Box<dyn Error>> {
        let mut len_le_bytes = [0u8; 8];
        src.read_exact(&mut len_le_bytes).map_err(Box::new)?;
        let length: u64 = u64::from_le_bytes(len_le_bytes);
        let length_as_base = length as usize;

        assert_eq!(length_as_base % P::SIZE_FACTOR, 0);

        let mut result = allocate_in_with_alignment_of::<F, P, A>(length_as_base, A::default());

        if F::CAN_CAST_VECTOR_TO_U64_LE_VECTOR {
            let dst_buffer = &mut result.spare_capacity_mut()[..length_as_base];
            let len = length_as_base * 8;
            let ptr: *mut u8 = dst_buffer.as_mut_ptr().cast();
            // do some magic
            let dst = unsafe { slice::from_raw_parts_mut(ptr, len) };
            src.read_exact(dst).map_err(Box::new)?;
            drop(dst);
            drop(dst_buffer);
            unsafe { result.set_len(length_as_base) };
        } else {
            // slow path
            let mut buffer = [0u8; 8];
            for _ in 0..length_as_base {
                src.read_exact(&mut buffer).map_err(Box::new)?;
                let el = F::from_u64_unchecked(u64::from_le_bytes(buffer));
                result.push(el);
            }
        }

        assert_eq!(result.len(), length_as_base);

        let result = P::vec_from_base_vec(result);

        Ok(result)
    }
}

impl<A: GoodAllocator> MemcopySerializable for Vec<u32, A>
where
    Self: 'static,
{
    fn write_into_buffer<W: Write>(&self, mut dst: W) -> Result<(), Box<dyn Error>> {
        let len_le_bytes = (self.len() as u64).to_le_bytes();
        dst.write_all(&len_le_bytes).map_err(Box::new)?;

        let num_bytes = self.len() * std::mem::size_of::<u32>();
        let src = unsafe { slice::from_raw_parts(self.as_ptr().cast(), num_bytes) };
        dst.write_all(src).map_err(Box::new)?;

        Ok(())
    }

    fn read_from_buffer<R: Read>(mut src: R) -> Result<Self, Box<dyn Error>> {
        let mut len_le_bytes = [0u8; 8];
        src.read_exact(&mut len_le_bytes).map_err(Box::new)?;
        let capacity = u64::from_le_bytes(len_le_bytes) as usize;

        let num_bytes = capacity * std::mem::size_of::<u32>();
        let mut result: Vec<u32, A> = Vec::with_capacity_in(capacity, A::default());
        let tmp = unsafe { std::slice::from_raw_parts_mut(result.as_mut_ptr().cast(), num_bytes) };
        src.read_exact(tmp).map_err(Box::new)?;
        unsafe { result.set_len(capacity) };
        Ok(result)
    }
}

impl<A: GoodAllocator> MemcopySerializable for Vec<u64, A>
where
    Self: 'static,
{
    fn write_into_buffer<W: Write>(&self, mut dst: W) -> Result<(), Box<dyn Error>> {
        let len_le_bytes = (self.len() as u64).to_le_bytes();
        dst.write_all(&len_le_bytes).map_err(Box::new)?;

        let num_bytes = self.len() * std::mem::size_of::<u64>();
        let src = unsafe { slice::from_raw_parts(self.as_ptr().cast(), num_bytes) };
        dst.write_all(src).map_err(Box::new)?;

        Ok(())
    }

    fn read_from_buffer<R: Read>(mut src: R) -> Result<Self, Box<dyn Error>> {
        let mut len_le_bytes = [0u8; 8];
        src.read_exact(&mut len_le_bytes).map_err(Box::new)?;
        let capacity = u64::from_le_bytes(len_le_bytes) as usize;

        let num_bytes = capacity * std::mem::size_of::<u64>();
        let mut result: Vec<u64, A> = Vec::with_capacity_in(capacity, A::default());
        let tmp = unsafe { std::slice::from_raw_parts_mut(result.as_mut_ptr().cast(), num_bytes) };
        src.read_exact(tmp).map_err(Box::new)?;
        unsafe { result.set_len(capacity) };

        Ok(result)
    }
}

impl<F: SmallField, const N: usize, A: GoodAllocator> MemcopySerializable for Vec<[F; N], A>
where
    Self: 'static,
{
    fn write_into_buffer<W: Write>(&self, mut dst: W) -> Result<(), Box<dyn Error>> {
        // we avoid transmute here
        let flattened_self = self[..].flatten();

        let len_as_base = flattened_self.len();
        let len_le_bytes = (len_as_base as u64).to_le_bytes();
        dst.write_all(&len_le_bytes).map_err(Box::new)?;

        if F::CAN_CAST_VECTOR_TO_U64_LE_VECTOR {
            // do some magic
            let len = len_as_base * 8;
            let ptr: *const u8 = flattened_self.as_ptr().cast();
            let src = unsafe { slice::from_raw_parts(ptr, len) };

            dst.write_all(src).map_err(Box::new)?;
        } else {
            // slow path
            for el in flattened_self.iter() {
                let el_le = el.as_u64_reduced().to_le_bytes();
                dst.write_all(&el_le).map_err(Box::new)?;
            }
        }

        Ok(())
    }

    fn read_from_buffer<R: Read>(mut src: R) -> Result<Self, Box<dyn Error>> {
        let mut len_le_bytes = [0u8; 8];
        src.read_exact(&mut len_le_bytes).map_err(Box::new)?;
        let length: u64 = u64::from_le_bytes(len_le_bytes);
        let length = length as usize;

        assert_eq!(length % N, 0);

        let mut result = Vec::with_capacity_in(length, A::default());

        if F::CAN_CAST_VECTOR_TO_U64_LE_VECTOR {
            let dst_buffer = &mut result.spare_capacity_mut()[..length];
            let len = length * 8;
            let ptr: *mut u8 = dst_buffer.as_mut_ptr().cast();
            // do some magic
            let dst = unsafe { slice::from_raw_parts_mut(ptr, len) };
            src.read_exact(dst).map_err(Box::new)?;
            drop(dst);
            drop(dst_buffer);
            unsafe { result.set_len(length) };
        } else {
            // slow path
            let mut buffer = [0u8; 8];
            for _ in 0..length {
                src.read_exact(&mut buffer).map_err(Box::new)?;
                let el = F::from_u64_unchecked(u64::from_le_bytes(buffer));
                result.push(el);
            }
        }

        assert_eq!(result.len(), length);

        let (ptr, len, capacity, allocator) = result.into_raw_parts_with_alloc();

        assert_eq!(len % N, 0);
        assert_eq!(capacity % N, 0);

        let result =
            unsafe { Vec::from_raw_parts_in(ptr.cast(), len / N, capacity / N, allocator) };

        Ok(result)
    }
}

impl<const N: usize, A: GoodAllocator> MemcopySerializable for Vec<[u8; N], A>
where
    Self: 'static,
{
    fn write_into_buffer<W: Write>(&self, mut dst: W) -> Result<(), Box<dyn Error>> {
        // we avoid transmute here
        let flattened_self = self[..].flatten();

        let len_as_base = flattened_self.len();
        let len_le_bytes = (len_as_base as u64).to_le_bytes();
        dst.write_all(&len_le_bytes).map_err(Box::new)?;

        dst.write_all(flattened_self).map_err(Box::new)?;

        Ok(())
    }

    fn read_from_buffer<R: Read>(mut src: R) -> Result<Self, Box<dyn Error>> {
        let mut len_le_bytes = [0u8; 8];
        src.read_exact(&mut len_le_bytes).map_err(Box::new)?;
        let length: u64 = u64::from_le_bytes(len_le_bytes);
        let length = length as usize;

        assert_eq!(length % N, 0);

        let mut result: Vec<u8, A> = Vec::with_capacity_in(length, A::default());
        let dst_buffer = &mut result.spare_capacity_mut()[..length];
        let ptr: *mut u8 = dst_buffer.as_mut_ptr().cast();
        // do some magic
        let dst = unsafe { slice::from_raw_parts_mut(ptr, length) };
        src.read_exact(dst).map_err(Box::new)?;

        unsafe { result.set_len(length) };

        assert_eq!(result.len(), length);

        let (ptr, len, capacity, allocator) = result.into_raw_parts_with_alloc();

        assert_eq!(len % N, 0);
        assert_eq!(capacity % N, 0);

        let result =
            unsafe { Vec::from_raw_parts_in(ptr.cast(), len / N, capacity / N, allocator) };

        Ok(result)
    }
}
