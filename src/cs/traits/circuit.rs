use super::{cs::ConstraintSystem, *};
use crate::cs::cs_builder::*;

pub trait Circuit<F: SmallField> {
    fn geometry(&self) -> CSGeometry;
    fn lookup_parameters(&self) -> LookupParameters;
    fn size_hint(&self) -> (Option<usize>, Option<usize>) {
        // We will be able to handle the case even without hints on average
        (None, None)
    }
    fn configure_builder<
        T: CsBuilderImpl<F, T>,
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
    >(
        &self,
        builder: CsBuilder<T, F, GC, TB>,
    ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder>;
    fn add_tables<CS: ConstraintSystem<F>>(&self, _cs: &mut CS) {
        // by default there are no tables
    }
    fn synthesize_into_cs<CS: ConstraintSystem<F>>(self, cs: &mut CS);
}

pub trait CircuitBuilder<F: SmallField> {
    fn geometry() -> CSGeometry;
    fn lookup_parameters() -> LookupParameters;
    fn configure_builder<
        T: CsBuilderImpl<F, T>,
        GC: GateConfigurationHolder<F>,
        TB: StaticToolboxHolder,
    >(
        builder: CsBuilder<T, F, GC, TB>,
    ) -> CsBuilder<T, F, impl GateConfigurationHolder<F>, impl StaticToolboxHolder>;
}

use crate::cs::cs_builder_verifier::CsVerifierBuilder;
use crate::cs::implementations::verifier::Verifier;
use crate::field::FieldExtension;
use crate::gadgets::recursion::recursive_verifier::RecursiveVerifier;
use crate::gadgets::recursion::recursive_verifier_builder::CsRecursiveVerifierBuilder;

// Done object-safe traits for convenience, as well as holders

pub trait ErasedBuilderForVerifier<F: SmallField, EXT: FieldExtension<2, BaseField = F>> {
    fn geometry(&self) -> CSGeometry;
    fn lookup_parameters(&self) -> LookupParameters;
    fn create_verifier(&self) -> Verifier<F, EXT>;
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash, Default(bound = ""))]
pub struct CircuitBuilderProxy<F: SmallField, C: CircuitBuilder<F>> {
    #[derivative(Debug = "ignore", Hash = "ignore")]
    pub _marker: std::marker::PhantomData<(&'static F, fn() -> C)>,
}

impl<F: SmallField, T: CircuitBuilder<F> + 'static> CircuitBuilderProxy<F, T> {
    // Create a boxed builder
    pub fn dyn_verifier_builder<EXT: FieldExtension<2, BaseField = F>>(
    ) -> Box<dyn ErasedBuilderForVerifier<F, EXT>> {
        Box::<Self>::default()
    }

    // Create a boxed builder
    pub fn dyn_recursive_verifier_builder<
        EXT: FieldExtension<2, BaseField = F>,
        CS: ConstraintSystem<F> + 'static,
    >() -> Box<dyn ErasedBuilderForRecursiveVerifier<F, EXT, CS>> {
        Box::<Self>::default()
    }
}

// we do not provide default implementation for CircuitBuilder, because those would require non-trivial construction,
// and instead we provide it for proxy

impl<F: SmallField, EXT: FieldExtension<2, BaseField = F>, T: CircuitBuilder<F>>
    ErasedBuilderForVerifier<F, EXT> for CircuitBuilderProxy<F, T>
{
    fn geometry(&self) -> CSGeometry {
        T::geometry()
    }
    fn lookup_parameters(&self) -> LookupParameters {
        T::lookup_parameters()
    }
    fn create_verifier(&self) -> Verifier<F, EXT> {
        let geometry = T::geometry();
        let builder_impl = CsVerifierBuilder::<F, EXT>::new_from_parameters(geometry);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = T::configure_builder(builder);
        let verifier = builder.build(());

        verifier
    }
}

pub trait ErasedBuilderForRecursiveVerifier<
    F: SmallField,
    EXT: FieldExtension<2, BaseField = F>,
    CS: ConstraintSystem<F> + 'static,
>
{
    fn geometry(&self) -> CSGeometry;
    fn lookup_parameters(&self) -> LookupParameters;
    fn create_recursive_verifier(&self, cs: &mut CS) -> RecursiveVerifier<F, EXT, CS>;
}

impl<
        F: SmallField,
        CS: ConstraintSystem<F> + 'static,
        EXT: FieldExtension<2, BaseField = F>,
        T: CircuitBuilder<F>,
    > ErasedBuilderForRecursiveVerifier<F, EXT, CS> for CircuitBuilderProxy<F, T>
{
    fn geometry(&self) -> CSGeometry {
        T::geometry()
    }
    fn lookup_parameters(&self) -> LookupParameters {
        T::lookup_parameters()
    }
    fn create_recursive_verifier(&self, cs: &mut CS) -> RecursiveVerifier<F, EXT, CS> {
        let geometry = T::geometry();
        let builder_impl =
            CsRecursiveVerifierBuilder::<'_, F, EXT, CS>::new_from_parameters(cs, geometry);
        let builder = new_builder::<_, F>(builder_impl);

        let builder = T::configure_builder(builder);
        let verifier = builder.build(());

        verifier
    }
}
