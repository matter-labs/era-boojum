use crate::field::PrimeField;

use super::*;

// This is a wrapper over any gate, that allows us to limit number of applications from above,
// compared to the "default" automatically computed capacity

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BoundedEvaluatorWrapper<F: PrimeField, W: GateConstraintEvaluator<F>> {
    pub max_on_row: usize,
    pub inner: W,
    pub _marker: std::marker::PhantomData<F>,
}

impl<F: PrimeField, W: GateConstraintEvaluator<F>> GateConstraintEvaluator<F>
    for BoundedEvaluatorWrapper<F, W>
{
    type UniqueParameterizationParams = (usize, W::UniqueParameterizationParams);

    #[inline(always)]
    fn new_from_parameters(params: Self::UniqueParameterizationParams) -> Self {
        let (max_on_row, inner_params) = params;
        let inner = W::new_from_parameters(inner_params);

        Self {
            max_on_row,
            inner,
            _marker: std::marker::PhantomData,
        }
    }

    #[inline(always)]
    fn unique_params(&self) -> Self::UniqueParameterizationParams {
        let inner_params = self.inner.unique_params();
        (self.max_on_row, inner_params)
    }

    #[inline]
    fn type_name() -> std::borrow::Cow<'static, str> {
        Cow::Borrowed(std::any::type_name::<Self>())
    }

    #[inline]
    fn instance_width(&self) -> GatePrincipalInstanceWidth {
        self.inner.instance_width()
    }

    #[inline]
    fn gate_purpose() -> GatePurpose {
        W::gate_purpose()
    }

    #[inline]
    fn placement_type(&self) -> GatePlacementType {
        self.inner.placement_type()
    }

    #[inline]
    fn num_repetitions_in_geometry(&self, geometry: &CSGeometry) -> usize {
        let max_inner = self.inner.num_repetitions_in_geometry(geometry);
        std::cmp::min(max_inner, self.max_on_row)
    }
    #[inline]
    fn num_required_constants_in_geometry(&self, geometry: &CSGeometry) -> usize {
        self.inner.num_repetitions_in_geometry(geometry)
    }

    type GlobalConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> =
        W::GlobalConstants<P>;

    #[inline(always)]
    fn create_global_constants<P: field::traits::field_like::PrimeFieldLike<Base = F>>(
        &self,
        ctx: &mut P::Context,
    ) -> Self::GlobalConstants<P> {
        self.inner.create_global_constants(ctx)
    }

    type RowSharedConstants<P: field::traits::field_like::PrimeFieldLike<Base = F>> =
        W::RowSharedConstants<P>;

    #[inline(always)]
    fn load_row_shared_constants<
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSource<F, P>,
    >(
        &self,
        trace_source: &S,
        ctx: &mut P::Context,
    ) -> Self::RowSharedConstants<P> {
        self.inner.load_row_shared_constants(trace_source, ctx)
    }

    #[inline(always)]
    fn evaluate_once<
        P: field::traits::field_like::PrimeFieldLike<Base = F>,
        S: TraceSource<F, P>,
        D: EvaluationDestination<F, P>,
    >(
        &self,
        trace_source: &S,
        destination: &mut D,
        shared_constants: &Self::RowSharedConstants<P>,
        global_constants: &Self::GlobalConstants<P>,
        ctx: &mut P::Context,
    ) {
        self.inner.evaluate_once(
            trace_source,
            destination,
            shared_constants,
            global_constants,
            ctx,
        )
    }
}

// Just keep a position that we can use next
#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BoundedGateWrapper<F: SmallField, W: Gate<F>> {
    pub max_on_row: usize,
    pub inner: W,
    pub _marker: std::marker::PhantomData<F>,
}

impl<F: SmallField, W: Gate<F>> Gate<F> for BoundedGateWrapper<F, W> {
    type Tools = W::Tools;

    #[inline(always)]
    fn check_compatible_with_cs<CS: ConstraintSystem<F>>(&self, cs: &CS) -> bool {
        self.inner.check_compatible_with_cs(cs)
    }

    type Evaluator = BoundedEvaluatorWrapper<F, W::Evaluator>;

    #[inline]
    fn evaluator(&self) -> Self::Evaluator {
        BoundedEvaluatorWrapper {
            max_on_row: self.max_on_row,
            inner: self.inner.evaluator(),
            _marker: std::marker::PhantomData,
        }
    }
}
