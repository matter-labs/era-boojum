use crate::cs::toolboxes::simplified::type_map::EmptySet;
use std::any::TypeId;

pub trait KVSet: 'static + Send + Sync {
    // we can walk over and get the next one
    type ExtendedSet<K: 'static + Send + Sync, T: 'static + Send + Sync>: KVSet;

    fn get<K: 'static + Send + Sync, T: 'static + Send + Sync>(&self) -> Option<&T>;
    fn get_mut<K: 'static + Send + Sync, T: 'static + Send + Sync>(&mut self) -> Option<&mut T>;

    fn extend<K: 'static + Send + Sync, T: 'static + Send + Sync>(
        self,
        value: T,
    ) -> Self::ExtendedSet<K, T>;
}

impl KVSet for EmptySet {
    type ExtendedSet<K: 'static + Send + Sync, T: 'static + Send + Sync> = KVSetEntry<K, T, Self>;

    #[inline(always)]
    fn get<K: 'static + Send + Sync, T: 'static + Send + Sync>(&self) -> Option<&T> {
        None
    }
    #[inline(always)]
    fn get_mut<K: 'static + Send + Sync, T: 'static + Send + Sync>(&mut self) -> Option<&mut T> {
        None
    }
    #[inline(always)]
    fn extend<K: 'static + Send + Sync, T: 'static + Send + Sync>(
        self,
        value: T,
    ) -> Self::ExtendedSet<K, T> {
        KVSetEntry {
            value,
            next: self,
            _marker: std::marker::PhantomData,
        }
    }
}

pub struct KVSetEntry<K: 'static + Send + Sync, T: 'static + Send + Sync, NEXT: KVSet> {
    pub value: T,
    pub next: NEXT,
    pub _marker: std::marker::PhantomData<&'static K>,
}

impl<KK: 'static + Send + Sync, TT: 'static + Send + Sync, NEXT: KVSet> KVSet
    for KVSetEntry<KK, TT, NEXT>
{
    type ExtendedSet<K: 'static + Send + Sync, T: 'static + Send + Sync> = KVSetEntry<K, T, Self>;

    #[inline(always)]
    fn get<K: 'static + Send + Sync, T: 'static + Send + Sync>(&self) -> Option<&T> {
        if TypeId::of::<K>() == TypeId::of::<KK>() {
            debug_assert!(TypeId::of::<T>() == TypeId::of::<TT>());
            unsafe {
                let casted: &T = &*(&self.value as *const TT).cast() as &T;

                Some(casted)
            }
        } else {
            self.next.get::<K, T>()
        }
    }
    #[inline(always)]
    fn get_mut<K: 'static + Send + Sync, T: 'static + Send + Sync>(&mut self) -> Option<&mut T> {
        if TypeId::of::<K>() == TypeId::of::<KK>() {
            debug_assert!(TypeId::of::<T>() == TypeId::of::<TT>());
            unsafe {
                let casted: &mut T = &mut *(&mut self.value as *mut TT).cast() as &mut T;

                Some(casted)
            }
        } else {
            self.next.get_mut::<K, T>()
        }
    }
    #[inline(always)]
    fn extend<K: 'static + Send + Sync, T: 'static + Send + Sync>(
        self,
        value: T,
    ) -> Self::ExtendedSet<K, T> {
        KVSetEntry {
            value,
            next: self,
            _marker: std::marker::PhantomData,
        }
    }
}
