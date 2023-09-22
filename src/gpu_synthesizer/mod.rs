use crate::field::traits::field_like::BaseField;
use crate::{cs::traits::evaluator::PerChunkOffset, field::SmallField};

use convert_case::{Case, Casing};
use derivative::Derivative;
use itertools::Itertools;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Mutex,
};

use crate::cs::traits::evaluator::*;

use super::*;

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GPUPolyStorage<F: SmallField> {
    chunk_offset: PerChunkOffset,
    _marker: std::marker::PhantomData<F>,
}

impl<F: SmallField> GPUPolyStorage<F> {
    pub const fn new() -> Self {
        Self {
            chunk_offset: PerChunkOffset::zero(),
            _marker: std::marker::PhantomData,
        }
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GPUPolyDestination<F: SmallField> {
    num_evaluations: usize,
    writes: Vec<Index<F>>,
}

impl<F: SmallField> GPUPolyDestination<F> {
    pub const fn new(num_evaluations: usize) -> Self {
        Self {
            num_evaluations,
            writes: vec![],
        }
    }
}

use crate::cs::traits::destination_view::*;
use crate::cs::traits::trace_source::*;
use crate::cs::traits::GoodAllocator;

impl<F: SmallField> TraceSource<F, GpuSynthesizerFieldLike<F>> for GPUPolyStorage<F> {
    fn get_constant_value(&self, constant_idx: usize) -> GpuSynthesizerFieldLike<F> {
        GpuSynthesizerFieldLike {
            idx: Index::ConstantPoly(self.chunk_offset.constants_offset + constant_idx),
        }
    }

    fn get_variable_value(&self, variable_idx: usize) -> GpuSynthesizerFieldLike<F> {
        GpuSynthesizerFieldLike {
            idx: Index::VariablePoly(self.chunk_offset.variables_offset + variable_idx),
        }
    }

    fn get_witness_value(&self, witness_idx: usize) -> GpuSynthesizerFieldLike<F> {
        GpuSynthesizerFieldLike {
            idx: Index::WitnessPoly(self.chunk_offset.witnesses_offset + witness_idx),
        }
    }

    fn dump_current_row<C: GoodAllocator>(&self, _dst: &mut Vec<GpuSynthesizerFieldLike<F>, C>) {
        unimplemented!("GPU context doesn't use row-wise access");
    }
}

impl<F: SmallField> TraceSourceDerivable<F, GpuSynthesizerFieldLike<F>> for GPUPolyStorage<F> {
    fn num_iterations(&self) -> usize {
        1
    }
    fn advance(&mut self) {}
    fn reset_gate_chunk_offset(&mut self) {
        self.chunk_offset = PerChunkOffset::zero();
    }
    fn offset_for_next_chunk(&mut self, chunk_offset: &PerChunkOffset) {
        self.chunk_offset.add_offset(chunk_offset);
    }
    fn set_constants_offset(&mut self, _offset: usize) {}
}

impl<F: SmallField> EvaluationDestination<F, GpuSynthesizerFieldLike<F>> for GPUPolyDestination<F> {
    #[inline(always)]
    fn push_evaluation_result(
        &mut self,
        value: GpuSynthesizerFieldLike<F>,
        _ctx: &mut GPUVariablesContext<F>,
    ) {
        self.writes.push(value.idx);
    }
}

impl<F: SmallField> EvaluationDestinationDrivable<F, GpuSynthesizerFieldLike<F>>
    for GPUPolyDestination<F>
{
    fn advance(&mut self, _ctx: &mut GPUVariablesContext<F>) {}
    fn expected_num_iterations(&self) -> usize {
        1
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Index<F: SmallField> {
    VariablePoly(usize),
    WitnessPoly(usize),
    ConstantPoly(usize),
    TemporaryValue(usize),
    ConstantValue(F),
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Relation<F: SmallField> {
    Add(Index<F>, Index<F>),
    Double(Index<F>),
    Sub(Index<F>, Index<F>),
    Negate(Index<F>),
    Mul(Index<F>, Index<F>),
    Square(Index<F>),
    Inverse(Index<F>),
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct GPUVariablesGlobalContext<F: SmallField> {
    counter: Arc<AtomicUsize>,
    relations: Arc<Mutex<Vec<(GpuSynthesizerFieldLike<F>, Relation<F>)>>>,
}

impl<F: SmallField> GPUVariablesGlobalContext<F> {
    pub fn new() -> Self {
        Self {
            counter: Arc::new(AtomicUsize::new(0)),
            relations: Arc::new(Mutex::new(vec![])),
        }
    }

    pub fn reset(&self) {
        self.counter.store(0, Ordering::Release);
        self.relations
            .lock()
            .expect("should reset only synchronously")
            .truncate(0);
    }

    fn advance(&self) -> usize {
        let this = self.counter.fetch_add(1, Ordering::AcqRel);

        this
    }
}

// we need a trick for "copy"

#[derive(Derivative)]
#[derivative(Debug)]
pub struct GPUVariablesContext<F: SmallField> {
    inner: &'static GPUVariablesGlobalContext<F>,
}

impl<F: SmallField> Clone for GPUVariablesContext<F> {
    fn clone(&self) -> Self {
        Self { inner: self.inner }
    }
}

impl<F: SmallField> Copy for GPUVariablesContext<F> {}

impl<F: SmallField> GPUVariablesContext<F> {
    pub fn push_relation(&self, for_var: GpuSynthesizerFieldLike<F>, rel: Relation<F>) {
        self.inner
            .relations
            .lock()
            .expect("GPU synthesis procedure is essentially synchronous")
            .push((for_var, rel));
    }

    pub fn get_relations(&self) -> Vec<(GpuSynthesizerFieldLike<F>, Relation<F>)> {
        self.inner
            .relations
            .lock()
            .expect("GPU synthesis procedure is essentially synchronous")
            .clone()
    }
}

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GpuSynthesizerFieldLike<F: SmallField> {
    pub idx: Index<F>,
}

impl<F: SmallField> std::fmt::Display for GpuSynthesizerFieldLike<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<F: SmallField> crate::field::traits::field_like::PrimeFieldLike
    for GpuSynthesizerFieldLike<F>
{
    type Base = F;
    type Context = GPUVariablesContext<F>;

    fn zero(_ctx: &mut Self::Context) -> Self {
        Self {
            idx: Index::ConstantValue(F::ZERO),
        }
    }

    fn one(_ctx: &mut Self::Context) -> Self {
        Self {
            idx: Index::ConstantValue(F::ONE),
        }
    }
    fn minus_one(_ctx: &mut Self::Context) -> Self {
        Self {
            idx: Index::ConstantValue(F::MINUS_ONE),
        }
    }
    // Arithmetics. Expressed in mutable way. It would not matter in after inlining
    fn add_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        let next_idx = ctx.inner.advance();
        let clean_var = Self {
            idx: Index::TemporaryValue(next_idx),
        };
        let rel = Relation::Add(self.idx, other.idx);
        ctx.push_relation(clean_var, rel);

        *self = clean_var;

        self
    }
    fn sub_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        let next_idx = ctx.inner.advance();
        let clean_var = Self {
            idx: Index::TemporaryValue(next_idx),
        };
        let rel = Relation::Sub(self.idx, other.idx);
        ctx.push_relation(clean_var, rel);

        *self = clean_var;

        self
    }
    fn mul_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        let next_idx = ctx.inner.advance();
        let clean_var = Self {
            idx: Index::TemporaryValue(next_idx),
        };
        let rel = Relation::Mul(self.idx, other.idx);
        ctx.push_relation(clean_var, rel);

        *self = clean_var;

        self
    }
    fn square(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        let next_idx = ctx.inner.advance();
        let clean_var = Self {
            idx: Index::TemporaryValue(next_idx),
        };
        let rel = Relation::Square(self.idx);
        ctx.push_relation(clean_var, rel);

        *self = clean_var;

        self
    }
    fn negate(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        let next_idx = ctx.inner.advance();
        let clean_var = Self {
            idx: Index::TemporaryValue(next_idx),
        };
        let rel = Relation::Negate(self.idx);
        ctx.push_relation(clean_var, rel);

        *self = clean_var;

        self
    }
    fn double(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        let next_idx = ctx.inner.advance();
        let clean_var = Self {
            idx: Index::TemporaryValue(next_idx),
        };
        let rel = Relation::Double(self.idx);
        ctx.push_relation(clean_var, rel);

        *self = clean_var;

        self
    }
    // infallible inverse
    fn inverse(&self, ctx: &mut Self::Context) -> Self {
        let next_idx = ctx.inner.advance();
        let clean_var = Self {
            idx: Index::TemporaryValue(next_idx),
        };
        let rel = Relation::Inverse(self.idx);
        ctx.push_relation(clean_var, rel);

        clean_var
    }
    // constant creation
    fn constant(value: F, _ctx: &mut Self::Context) -> Self {
        let clean_var = Self {
            idx: Index::ConstantValue(value),
        };

        clean_var
    }
    // fn mul_by_base(&'_ mut self, other: &F, ctx: &mut Self::Context) -> &'_ mut Self {
    //     let next_idx = ctx.inner.advance();
    //     let other = Index::ConstantValue(*other);
    //     let clean_var = Self {
    //         idx: Index::TemporaryValue(next_idx),
    //     };
    //     let rel = Relation::Mul(self.idx, other);
    //     ctx.push_relation(clean_var, rel);

    //     *self = clean_var;

    //     self
    // }
}

use field::goldilocks::GoldilocksField;
use lazy_static::lazy_static;

lazy_static! {
    pub static ref GPU_CONTEXT: GPUVariablesGlobalContext<GoldilocksField> =
        GPUVariablesGlobalContext::new();
}

fn get_context() -> &'static GPUVariablesGlobalContext<GoldilocksField> {
    &GPU_CONTEXT
}

#[derive(Derivative)]
#[derivative(Debug)]
pub struct GPUDataCapture {
    pub evaluator_name: String,
    pub gate_purpose: GatePurpose,
    pub max_constraint_degree: usize,
    pub num_quotient_terms: usize,
    pub placement_type: GatePlacementType,
    pub row_shared_constants_set: Vec<GpuSynthesizerFieldLike<GoldilocksField>>,
    pub writes_per_repetition: Vec<Index<GoldilocksField>>,
    pub relations: Vec<(
        GpuSynthesizerFieldLike<GoldilocksField>,
        Relation<GoldilocksField>,
    )>,
    #[derivative(Debug = "ignore")]
    pub(crate) equality_fn: Box<dyn Fn(&dyn std::any::Any) -> bool + 'static + Send + Sync>,
}

pub fn get_evaluator_name<F: BaseField, E: GateConstraintEvaluator<F>>(evaluator: &E) -> String {
    let name = std::any::type_name::<E>()
        .split_terminator(['<', '>', ','].as_ref())
        .map(str::trim)
        .map(|s| s.split("::").last().unwrap().to_case(Case::Snake))
        .join("_");
    if std::any::TypeId::of::<E::UniqueParameterizationParams>() == std::any::TypeId::of::<()>() {
        name
    } else {
        let mut hasher = DefaultHasher::new();
        evaluator.unique_params().hash(&mut hasher);
        let hash = hasher.finish();
        format!("{}_{:016x}", name, hash)
    }
}

impl GPUDataCapture {
    pub fn from_evaluator<E: GateConstraintEvaluator<GoldilocksField>>(evaluator: E) -> Self {
        // as we may not have a luxury of having single compilation unit here,
        // we can not rely on TypeId, so we compare by evaluator name,
        // and it's initialization parameters always

        let evaluator_name = get_evaluator_name(&evaluator);
        let gate_purpose = E::gate_purpose();
        let max_constraint_degree = E::max_constraint_degree();
        let num_quotient_terms = E::num_quotient_terms();
        let placement_type = evaluator.placement_type();

        let mut ctx = GPUVariablesContext {
            inner: get_context(),
        };

        let source = GPUPolyStorage::<GoldilocksField>::new();
        let mut destination = GPUPolyDestination::<GoldilocksField>::new(num_quotient_terms);

        let global_constants = evaluator.create_global_constants(&mut ctx);

        // stateless anyway
        let shared_constants = evaluator.load_row_shared_constants(&source, &mut ctx);
        let shared_constants_descr = shared_constants.external_description();

        let another_clone = evaluator.clone();
        let equality_fn = move |other: &dyn std::any::Any| -> bool {
            if let Some(same_type_gate) = other.downcast_ref::<E>() {
                same_type_gate == &another_clone
            } else {
                false
            }
        };

        let equality_fn = Box::new(equality_fn);

        evaluator.evaluate_once(
            &source,
            &mut destination,
            &shared_constants,
            &global_constants,
            &mut ctx,
        );

        let new = Self {
            evaluator_name,
            gate_purpose,
            max_constraint_degree,
            num_quotient_terms,
            placement_type,
            row_shared_constants_set: shared_constants_descr,
            writes_per_repetition: destination.writes,
            relations: ctx.get_relations(),
            equality_fn,
        };

        new
    }
}

pub struct GatesSetForGPU {
    pub descriptions: Vec<GPUDataCapture>,
}

use crate::cs::traits::gate::*;

impl GatesSetForGPU {
    pub fn new() -> Self {
        Self {
            descriptions: vec![],
        }
    }

    pub fn add_gate<G: Gate<GoldilocksField>>(
        &mut self,
        params: <<G as Gate<GoldilocksField>>::Evaluator as GateConstraintEvaluator<
            GoldilocksField,
        >>::UniqueParameterizationParams,
    ) {
        let evaluator = <<G as Gate<GoldilocksField>>::Evaluator as GateConstraintEvaluator<
            GoldilocksField,
        >>::new_from_parameters(params);
        let capture = GPUDataCapture::from_evaluator(evaluator);
        self.descriptions.push(capture);
    }

    pub fn find_evaluator<E: GateConstraintEvaluator<GoldilocksField>>(
        &self,
        evaluator: &E,
    ) -> Option<(usize, &GPUDataCapture)> {
        if self.descriptions.is_empty() {
            return None;
        }

        let mut found = None;

        for (idx, description) in self.descriptions.iter().enumerate() {
            let other_name = evaluator.instance_name();
            let gate_purpose = E::gate_purpose();
            let max_constraint_degree = E::max_constraint_degree();
            let num_quotient_terms = E::num_quotient_terms();
            let placement_type = evaluator.placement_type();
            if description.evaluator_name != other_name {
                continue;
            }
            if (description.equality_fn)(evaluator) == true {
                assert!(found.is_none(), "only one should match");
                assert_eq!(gate_purpose, description.gate_purpose);
                assert_eq!(max_constraint_degree, description.max_constraint_degree);
                assert_eq!(num_quotient_terms, description.num_quotient_terms);
                assert_eq!(placement_type, description.placement_type);

                found = Some(idx);
            }
        }

        found.map(|found| (found, &self.descriptions[found]))
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct TestSource<F: SmallField> {
    pub variables: Vec<Vec<F>>,
    pub witness: Vec<Vec<F>>,
    pub constants: Vec<Vec<F>>,
    constants_offset: usize,
    gate_chunks_offset: PerChunkOffset,
    index: usize,
}

impl<F: SmallField> TestSource<F> {
    #[inline]
    pub fn from_storages(
        variables: Vec<Vec<F>>,
        witness: Vec<Vec<F>>,
        constants: Vec<Vec<F>>,
    ) -> Self {
        Self {
            variables,
            witness,
            constants,
            constants_offset: 0,
            gate_chunks_offset: PerChunkOffset::zero(),
            index: 0,
        }
    }

    pub fn advance_manually(&mut self) {
        self.index += 1;
    }

    pub fn subset(
        &self,
        variables_range: std::ops::Range<usize>,
        witness_range: std::ops::Range<usize>,
        constants_range: std::ops::Range<usize>,
    ) -> Self {
        Self {
            variables: self.variables[variables_range].to_vec(),
            witness: self.witness[witness_range].to_vec(),
            constants: self.constants[constants_range].to_vec(),
            constants_offset: 0,
            gate_chunks_offset: PerChunkOffset::zero(),
            index: 0,
        }
    }

    pub fn random_source(
        num_vars: usize,
        num_wits: usize,
        num_constants: usize,
        size: usize,
    ) -> Self {
        use rayon::iter::IntoParallelIterator;
        use rayon::iter::ParallelIterator;
        let mut start = 0;
        let vars: Vec<_> = (start..(start + num_vars))
            .into_par_iter()
            .map(|el| {
                use crate::field::rand_from_rng;
                use rand::SeedableRng;
                let mut rng = rand::rngs::StdRng::seed_from_u64(el as u64);

                let mut result = Vec::with_capacity(size);
                for _ in 0..size {
                    let value = rand_from_rng::<_, F>(&mut rng);
                    result.push(value);
                }

                result
            })
            .collect();
        start += num_vars;

        let wits: Vec<_> = (start..(start + num_wits))
            .into_par_iter()
            .map(|el| {
                use crate::field::rand_from_rng;
                use rand::SeedableRng;
                let mut rng = rand::rngs::StdRng::seed_from_u64(el as u64);

                let mut result = Vec::with_capacity(size);
                for _ in 0..size {
                    let value = rand_from_rng::<_, F>(&mut rng);
                    result.push(value);
                }

                result
            })
            .collect();
        start += num_wits;

        let consts: Vec<_> = (start..(start + num_constants))
            .into_par_iter()
            .map(|el| {
                use crate::field::rand_from_rng;
                use rand::SeedableRng;
                let mut rng = rand::rngs::StdRng::seed_from_u64(el as u64);

                let mut result = Vec::with_capacity(size);
                for _ in 0..size {
                    let value = rand_from_rng::<_, F>(&mut rng);
                    result.push(value);
                }

                result
            })
            .collect();

        Self {
            variables: vars,
            witness: wits,
            constants: consts,
            constants_offset: 0,
            gate_chunks_offset: PerChunkOffset::zero(),
            index: 0,
        }
    }
}

impl<F: SmallField> TraceSource<F, F> for TestSource<F> {
    #[inline(always)]
    fn get_variable_value(&self, variable_idx: usize) -> F {
        self.variables[self.gate_chunks_offset.variables_offset + variable_idx][self.index]
    }

    #[inline(always)]
    fn get_constant_value(&self, constant_idx: usize) -> F {
        self.constants
            [self.constants_offset + self.gate_chunks_offset.constants_offset + constant_idx]
            [self.index]
    }

    #[inline(always)]
    fn get_witness_value(&self, witness_idx: usize) -> F {
        self.witness[self.gate_chunks_offset.witnesses_offset + witness_idx][self.index]
    }

    #[inline(always)]
    fn dump_current_row<C: GoodAllocator>(&self, _dst: &mut Vec<F, C>) {
        unimplemented!("Test source doesn't use per-row access");
    }
}

impl<F: SmallField> TraceSourceDerivable<F, F> for TestSource<F> {
    #[inline]
    fn num_iterations(&self) -> usize {
        self.variables[0].len()
    }
    #[inline(always)]
    fn reset_gate_chunk_offset(&mut self) {
        self.gate_chunks_offset = PerChunkOffset::zero();
    }
    #[inline]
    fn offset_for_next_chunk(&mut self, gate_chunks_offset: &PerChunkOffset) {
        self.gate_chunks_offset.add_offset(gate_chunks_offset);
    }
    #[inline(always)]
    fn advance(&mut self) {
        self.index += 1;
    }
    #[inline]
    fn set_constants_offset(&mut self, offset: usize) {
        debug_assert!(offset < self.constants.len());
        self.constants_offset = offset;
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct TestDestination<F: SmallField> {
    pub terms: Vec<Vec<F>>,
    term_index: usize,
    index: usize,
}

impl<F: SmallField> TestDestination<F> {
    pub fn new(size: usize, num_terms: usize) -> Self {
        Self {
            terms: vec![vec![F::ZERO; size]; num_terms],
            term_index: 0,
            index: 0,
        }
    }
}

impl<F: SmallField> EvaluationDestination<F, F> for TestDestination<F> {
    fn push_evaluation_result(&mut self, value: F, _ctx: &mut ()) {
        self.terms[self.term_index][self.index] = value;
        self.term_index += 1;
    }
}

impl<F: SmallField> EvaluationDestinationDrivable<F, F> for TestDestination<F> {
    fn expected_num_iterations(&self) -> usize {
        self.terms[0].len()
    }
    fn advance(&mut self, _ctx: &mut ()) {
        self.index += 1;
        self.term_index = 0;
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::cs::CSGeometry;
    use crate::{
        cs::traits::evaluator::GateConstraintEvaluator, field::goldilocks::GoldilocksField,
    };

    use crate::cs::gates::Poseidon2FlattenedGate;
    use crate::implementations::poseidon2::Poseidon2Goldilocks;
    type F = GoldilocksField;
    use crate::cs::gates::*;

    #[test]
    fn try_evaluator() {
        let num_vars = 4;
        let num_wits = 0;
        let num_constants = 2;

        let geometry = CSGeometry {
            num_columns_under_copy_permutation: num_vars,
            num_witness_columns: num_wits,
            num_constant_columns: num_constants,
            max_allowed_constraint_degree: 1000,
        };

        let domain_size = 1 << 10;
        let mut source =
            TestSource::<F>::random_source(num_vars, num_wits, num_constants, domain_size);
        let num_terms = 2;
        let mut destination = TestDestination::<F>::new(domain_size, num_terms);

        let evaluator = <<FmaGateInBaseFieldWithoutConstant<F> as Gate<F>>::Evaluator as GateConstraintEvaluator<F>>::new_from_parameters(());
        let ctx = &mut ();
        let num_repetitions_on_row =
            GateConstraintEvaluator::<F>::num_repetitions_in_geometry(&evaluator, &geometry);
        // we test as non-specialized one for now
        let final_per_chunk_offset = GateConstraintEvaluator::<F>::per_chunk_offset_for_repetition_over_general_purpose_columns(&evaluator);
        let evaluator = GenericRowwiseEvaluator::<F, F, _> {
            evaluator,
            global_constants: evaluator.create_global_constants::<F>(ctx),
            num_repetitions: num_repetitions_on_row,
            per_chunk_offset: final_per_chunk_offset,
        };

        for _ in 0..domain_size {
            evaluator.evaluate_over_general_purpose_columns(&mut source, &mut destination, 0, ctx);

            // it advances internally
        }
        // should be something
        dbg!(&destination.terms[0][0]);
        // should be 0 because we only have 1 term from FMA gate
        dbg!(&destination.terms[1][0]);
    }

    // #[test]
    // fn test_demo_gpu_basic_derivation() {
    //     let geometry = CSGeometry {
    //         num_columns_under_copy_permutation: 8,
    //         num_witness_columns: 0,
    //         num_constant_columns: 2,
    //         max_allowed_constraint_degree: 8,
    //     };

    //     use crate::cs::gates::fma_gate_without_constant::FmaGateInBaseWithoutConstantConstraintEvaluator;
    //     use crate::cs::traits::evaluator::GateConstraintEvaluator;

    //     let evaluator = FmaGateInBaseWithoutConstantConstraintEvaluator;
    //     let num_terms =
    //         <FmaGateInBaseWithoutConstantConstraintEvaluator as GateConstraintEvaluator<
    //             GoldilocksField,
    //         >>::total_quotient_terms_in_geometry(&evaluator, &geometry);

    //     let global_ctx = get_context();
    //     global_ctx.reset();
    //     let mut ctx = GPUVariablesContext {
    //         inner: global_ctx
    //     };

    //     let mut source = GPUPolyStorage::<GoldilocksField>::new();
    //     let mut destination = GPUPolyDestination::<GoldilocksField>::new(num_terms);

    //     // stateless anyway
    //     let shared_constants = evaluator.load_row_shared_constants(&source, &mut ctx);
    //     dbg!(&shared_constants);

    //     // evaluator.evaluate_once(&source, &mut destination, &[], &shared_constants, ctx);

    //     let constants_offset = 0;

    //     let (batch_evaluator, _) =
    //         GenericGateEvaluationFunction::from_evaluator(evaluator, &geometry, None);

    //     (batch_evaluator.evaluation_fn)(&mut source, &mut destination, constants_offset, &mut ctx);

    //     dbg!(&destination.writes);
    //     dbg!(&ctx.get_relations());
    // }

    #[test]
    fn test_gpu_data_capture() {
        let geometry = CSGeometry {
            num_columns_under_copy_permutation: 140,
            num_witness_columns: 0,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 8,
        };

        type Poseidon2Gate = Poseidon2FlattenedGate<F, 8, 12, 4, Poseidon2Goldilocks>;

        let mut descriptions = GatesSetForGPU::new();

        let (_, (total_num_variables, num_new_witnesses)) =
            Poseidon2Gate::compute_strategy(&geometry);
        descriptions.add_gate::<Poseidon2Gate>((total_num_variables, num_new_witnesses));
        descriptions.add_gate::<DotProductGate<4>>(());
        descriptions.add_gate::<BooleanConstraintGate>(());
        descriptions.add_gate::<QuadraticCombinationGate<4>>(());
        descriptions.add_gate::<ZeroCheckGate>(false);
        descriptions.add_gate::<FmaGateInBaseFieldWithoutConstant<F>>(());
        descriptions.add_gate::<UIntXAddGate<32>>(());
        descriptions.add_gate::<UIntXAddGate<16>>(());
        descriptions.add_gate::<UIntXAddGate<8>>(());
        descriptions.add_gate::<ReductionByPowersGate<F, 4>>(());
        descriptions.add_gate::<SelectionGate>(());
        descriptions.add_gate::<ParallelSelectionGate<4>>(());
        descriptions.add_gate::<ReductionGate<F, 4>>(());

        let other_geometry = CSGeometry {
            num_columns_under_copy_permutation: 96,
            num_witness_columns: 40,
            num_constant_columns: 8,
            max_allowed_constraint_degree: 8,
        };

        let (_, (total_num_variables, num_new_witnesses)) =
            Poseidon2Gate::compute_strategy(&other_geometry);
        let evaluator = <Poseidon2Gate as Gate<GoldilocksField>>::Evaluator::new_from_parameters((
            total_num_variables,
            num_new_witnesses,
        ));

        assert!(descriptions.find_evaluator(&evaluator).is_none());
    }
}
