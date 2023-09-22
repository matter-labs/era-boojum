use std::sync::atomic::AtomicUsize;

use crate::field::traits::field_like::PrimeFieldLikeVectorized;

use super::*;

#[derive(Derivative)]
#[derivative(Default)]
pub struct TestSource<F: SmallField, P: PrimeFieldLikeVectorized<Base = F> = F> {
    pub max_accessed_variable: AtomicUsize,
    pub max_accessed_witness: AtomicUsize,
    pub max_accessed_constant: AtomicUsize,
    _marker: std::marker::PhantomData<(F, P)>,
}

impl<F: SmallField, P: PrimeFieldLikeVectorized<Base = F>> TraceSource<F, P> for TestSource<F, P> {
    fn get_variable_value(&self, variable_offset: usize) -> P {
        self.max_accessed_variable
            .fetch_max(variable_offset, std::sync::atomic::Ordering::AcqRel);
        P::zero(&mut P::Context::placeholder())
    }

    fn get_constant_value(&self, constant_offset: usize) -> P {
        self.max_accessed_witness
            .fetch_max(constant_offset, std::sync::atomic::Ordering::AcqRel);
        P::zero(&mut P::Context::placeholder())
    }

    fn get_witness_value(&self, witness_offset: usize) -> P {
        self.max_accessed_witness
            .fetch_max(witness_offset, std::sync::atomic::Ordering::AcqRel);
        P::zero(&mut P::Context::placeholder())
    }

    fn dump_current_row<A: traits::GoodAllocator>(&self, _dst: &mut Vec<P, A>) {
        unimplemented!()
    }
}

#[derive(Derivative)]
#[derivative(Clone, Default, Debug)]
pub struct TestDestination<F: SmallField, P: PrimeFieldLikeVectorized<Base = F> = F> {
    pub num_terms: usize,
    _marker: std::marker::PhantomData<(F, P)>,
}

impl<F: SmallField, P: PrimeFieldLikeVectorized<Base = F>> EvaluationDestination<F, P>
    for TestDestination<F, P>
{
    fn push_evaluation_result(&mut self, _value: P, _ctx: &mut P::Context) {
        self.num_terms += 1;
    }
}

pub fn test_evaluator<F: SmallField, E: GateConstraintEvaluator<F>>(evaluator: E) {
    // we mainly check that number of terms claimed is one that is pushed,
    // and that whatever "column" gate requires it uses

    let expected_num_terms = match E::gate_purpose() {
        GatePurpose::Evaluatable {
            max_constraint_degree: _,
            num_quotient_terms,
        } => num_quotient_terms,
        a => {
            unreachable!("testing is not usable for evaluator with purpose {:?}", a);
        }
    };

    let source = TestSource::<F, F>::default();
    let row_constants = evaluator.load_row_shared_constants(&source, &mut ());

    let global_constants = evaluator.create_global_constants(&mut ());

    let source = TestSource::<F, F>::default();
    let mut destination = TestDestination::<F, F>::default();

    evaluator.evaluate_once(
        &source,
        &mut destination,
        &row_constants,
        &global_constants,
        &mut (),
    );

    assert!(
        expected_num_terms == destination.num_terms,
        "gate claims to have {} terms, but pushed {} into evaluator",
        expected_num_terms,
        destination.num_terms,
    );
}
