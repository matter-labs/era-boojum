use super::{fast_serialization::MemcopySerializable, *};

// Hints are some handly artifacts that allow us to speedup the proofs and synthesis
// For now such hints would be how to copy variable values (where variable index is just an integer)
// into the places in the trace columns. Another one is how to place witness values into corresponding
// columns, but those are sparse

// Dense hint spans every column in full and says which variable to use to put there

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, PartialEq, Eq)]
pub struct DenseVariablesCopyHint {
    pub maps: Vec<Vec<Variable>>,
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, PartialEq, Eq)]
pub struct DenseWitnessCopyHint {
    pub maps: Vec<Vec<Witness>>,
}

impl MemcopySerializable for Vec<Variable> {
    fn read_from_buffer<R: std::io::Read>(mut src: R) -> Result<Self, Box<dyn std::error::Error>> {
        let mut len_le_bytes = [0u8; 8];
        src.read_exact(&mut len_le_bytes).map_err(Box::new)?;
        let length: u64 = u64::from_le_bytes(len_le_bytes);
        let length = length as usize;

        let mut result = Vec::with_capacity(length);

        let dst_buffer = &mut result.spare_capacity_mut()[..length];
        let ptr: *mut u8 = dst_buffer.as_mut_ptr().cast();
        // do some magic
        assert_eq!(std::mem::size_of::<Variable>(), 8);
        let len = length * 8;
        let dst = unsafe { std::slice::from_raw_parts_mut(ptr, len) };
        src.read_exact(dst).map_err(Box::new)?;
        drop(dst);
        drop(dst_buffer);
        unsafe { result.set_len(length) };

        Ok(result)
    }

    fn write_into_buffer<W: std::io::Write>(
        &self,
        mut dst: W,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let len = self.len();
        let len_le_bytes = (len as u64).to_le_bytes();
        dst.write_all(&len_le_bytes).map_err(Box::new)?;

        let num_bytes = len * std::mem::size_of::<Variable>();
        let ptr: *const u8 = self.as_ptr().cast();
        let src = unsafe { std::slice::from_raw_parts(ptr, num_bytes) };

        dst.write_all(src).map_err(Box::new)?;

        Ok(())
    }
}

impl MemcopySerializable for Vec<Witness> {
    fn read_from_buffer<R: std::io::Read>(mut src: R) -> Result<Self, Box<dyn std::error::Error>> {
        let mut len_le_bytes = [0u8; 8];
        src.read_exact(&mut len_le_bytes).map_err(Box::new)?;
        let length: u64 = u64::from_le_bytes(len_le_bytes);
        let length = length as usize;

        let mut result = Vec::with_capacity(length);

        let dst_buffer = &mut result.spare_capacity_mut()[..length];
        let ptr: *mut u8 = dst_buffer.as_mut_ptr().cast();
        // do some magic
        assert_eq!(std::mem::size_of::<Witness>(), 8);
        let len = length * 8;
        let dst = unsafe { std::slice::from_raw_parts_mut(ptr, len) };
        src.read_exact(dst).map_err(Box::new)?;
        drop(dst);
        drop(dst_buffer);
        unsafe { result.set_len(length) };

        Ok(result)
    }

    fn write_into_buffer<W: std::io::Write>(
        &self,
        mut dst: W,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let len = self.len();
        let len_le_bytes = (len as u64).to_le_bytes();
        dst.write_all(&len_le_bytes).map_err(Box::new)?;

        let num_bytes = len * std::mem::size_of::<Variable>();
        let ptr: *const u8 = self.as_ptr().cast();
        let src = unsafe { std::slice::from_raw_parts(ptr, num_bytes) };

        dst.write_all(src).map_err(Box::new)?;

        Ok(())
    }
}

impl MemcopySerializable for DenseVariablesCopyHint {
    fn read_from_buffer<R: std::io::Read>(src: R) -> Result<Self, Box<dyn std::error::Error>> {
        let maps = super::fast_serialization::read_vec_from_buffer(src)?;

        Ok(Self { maps })
    }

    fn write_into_buffer<W: std::io::Write>(
        &self,
        dst: W,
    ) -> Result<(), Box<dyn std::error::Error>> {
        super::fast_serialization::write_vec_into_buffer(&self.maps, dst)?;

        Ok(())
    }
}

impl MemcopySerializable for DenseWitnessCopyHint {
    fn read_from_buffer<R: std::io::Read>(src: R) -> Result<Self, Box<dyn std::error::Error>> {
        let maps = super::fast_serialization::read_vec_from_buffer(src)?;

        Ok(Self { maps })
    }

    fn write_into_buffer<W: std::io::Write>(
        &self,
        dst: W,
    ) -> Result<(), Box<dyn std::error::Error>> {
        super::fast_serialization::write_vec_into_buffer(&self.maps, dst)?;

        Ok(())
    }
}

// we can also have "sparse" cases in general if those are beneficial,
// where instead of spanning over every columns we specify places of each
// variable to be copied. We expect a number of places where every variable
// used to be "small" and even smaller for witness
#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, PartialEq, Eq)]
pub struct SparseVariablesCopyHint {
    pub maps: Vec<smallvec::SmallVec<[(u32, u32); 8]>>,
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, PartialEq, Eq)]
pub struct SparseWitnessCopyHint {
    pub maps: Vec<smallvec::SmallVec<[(u32, u32); 2]>>,
}
