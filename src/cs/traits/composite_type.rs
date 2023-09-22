use super::*;

use crate::dag::WitnessSource;

use crate::gadgets::traits::castable::WitnessCastable;

pub trait Resolvable<T: 'static + Clone>: 'static {
    fn wait_for_value(self) -> Option<T>;
}

pub enum CompositeWitnessValue<
    F: SmallField,
    SRC: 'static + Send + Sync + Clone + std::fmt::Debug,
    T: WitnessCastable<F, SRC>,
    R: Resolvable<SRC>,
    S: WitnessSource<F>,
> {
    Placeholder,
    Ready(T),
    Waiting {
        resolvable: R,
        _marker: std::marker::PhantomData<(F, SRC, S)>,
    },
}

impl<
        F: SmallField,
        SRC: 'static + Send + Sync + Clone + std::fmt::Debug,
        T: WitnessCastable<F, SRC>,
        R: Resolvable<SRC>,
        S: WitnessSource<F>,
    > CompositeWitnessValue<F, SRC, T, R, S>
{
    pub fn wait(&mut self) -> Option<T> {
        match self {
            Self::Placeholder => None,
            Self::Ready(value) => Some(value.clone()),
            a => {
                let this = std::mem::replace(a, Self::Placeholder);

                let Self::Waiting { resolvable, .. } = this else {
                    unreachable!()
                };
                let resolved = resolvable.wait_for_value();
                if let Some(resolved) = resolved {
                    let as_final_type = T::cast_from_source(resolved);
                    let _ = std::mem::replace(a, Self::Ready(as_final_type.clone()));

                    Some(as_final_type)
                } else {
                    None
                }
            }
        }
    }
}

impl<
        F: SmallField,
        SRC: 'static + Send + Sync + Clone + std::fmt::Debug,
        T: WitnessCastable<F, SRC>,
        R: Resolvable<SRC>,
        S: WitnessSource<F>,
    > Resolvable<T> for CompositeWitnessValue<F, SRC, T, R, S>
{
    fn wait_for_value(mut self) -> Option<T> {
        self.wait()
    }
}
