pub trait U64Representable: U64RawRepresentable {
    fn as_u64(self) -> u64;
    fn from_u64_unchecked(value: u64) -> Self;
    fn from_u64(value: u64) -> Option<Self>;
    fn as_u64_array<const N: usize>(input: [Self; N]) -> [u64; N];
    fn as_u64_reduced(&self) -> u64;
    #[inline(always)]
    fn normalize(&mut self) {
        *self = Self::from_raw_u64_unchecked(self.as_u64_reduced());
    }
    fn batch_normalize(dst: &mut [Self]) {
        for el in dst.iter_mut() {
            el.normalize();
        }
    }
}

pub trait U64RawRepresentable:
    'static
    + Clone
    + Copy
    + std::fmt::Display
    + std::fmt::Debug
    + std::hash::Hash
    + std::marker::Send
    + std::marker::Sync
{
    fn as_raw_u64(self) -> u64;
    fn from_raw_u64_unchecked(value: u64) -> Self;
    fn from_raw_u64_checked(value: u64) -> Option<Self>;
    fn as_raw_u64_array<const N: usize>(input: [Self; N]) -> [u64; N];
}

pub trait SmallFieldRepresentable: U64Representable {
    fn from_u128_reduced(value: u128) -> Self;
}
