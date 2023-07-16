use derivative::*;

pub trait TypeMarker: 'static + Send + Sync + Clone + Copy + std::fmt::Debug {}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct PlacementStrategyMarker;

impl TypeMarker for PlacementStrategyMarker {}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct GateParametersMarker;

impl TypeMarker for GateParametersMarker {}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct GateToolingMarker;

impl TypeMarker for GateToolingMarker {}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug)]
pub struct MarkerProxy<T: 'static + Send + Sync> {
    _marker: std::marker::PhantomData<&'static T>,
}

impl<T: 'static + Send + Sync> MarkerProxy<T> {
    pub const fn new() -> Self {
        Self {
            _marker: std::marker::PhantomData,
        }
    }

    pub const fn wrap_marker<M: TypeMarker>(_other: M) -> MarkerProxy<(T, M)> {
        MarkerProxy::<(T, M)> {
            _marker: std::marker::PhantomData,
        }
    }
}

impl<T: 'static + Send + Sync> TypeMarker for MarkerProxy<T> {}

pub struct KVQueryMarker<K: TypeMarker, V: 'static + Send + Sync> {
    _marker: std::marker::PhantomData<(&'static K, &'static V)>,
}

impl<K: TypeMarker, V: 'static + Send + Sync> KVQueryMarker<K, V> {
    pub const fn new() -> Self {
        Self {
            _marker: std::marker::PhantomData,
        }
    }
}
