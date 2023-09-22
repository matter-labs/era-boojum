use crate::{cs::traits::GoodAllocator, field::traits::field_like::BaseField};
use std::alloc::Global;

use crate::cs::traits::evaluator::PerChunkOffset;

use super::{fast_serialization::MemcopySerializable, *};

use super::polynomial::lde::*;
use super::polynomial::*;
use crate::cs::implementations::polynomial::Polynomial;
use crate::cs::implementations::setup::TreeNode;
use crate::field::PrimeField;
use std::ops::Range;
use std::sync::Arc;

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct WitnessStorage<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F> = F,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    // We store full LDEs of the original polynomials.
    // For those we can produce adapters to properly iterate over
    // future leafs of the oracles
    pub variables_columns: Vec<ArcGenericLdeStorage<F, P, A, B>, B>,
    pub witness_columns: Vec<ArcGenericLdeStorage<F, P, A, B>, B>,
    pub lookup_multiplicities_polys: Vec<ArcGenericLdeStorage<F, P, A, B>, B>,
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct SecondStageProductsStorage<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F> = F,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    // We store full LDEs of the original polynomials.
    // For those we can produce adapters to properly iterate over
    // future leafs of the oracles
    pub z_poly: [ArcGenericLdeStorage<F, P, A, B>; 2],
    pub intermediate_polys: Vec<[ArcGenericLdeStorage<F, P, A, B>; 2], B>,
    pub lookup_witness_encoding_polys: Vec<[ArcGenericLdeStorage<F, P, A, B>; 2], B>,
    pub lookup_multiplicities_encoding_polys: Vec<[ArcGenericLdeStorage<F, P, A, B>; 2], B>,
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, PartialEq(bound = ""), Eq)]
#[serde(
    bound = "F: serde::Serialize + serde::de::DeserializeOwned, P: serde::Serialize + serde::de::DeserializeOwned"
)]
pub struct SetupBaseStorage<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F> = F,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    // We store full LDEs of the original polynomials.
    // For those we can produce adapters to properly iterate over
    // future leafs of the oracles
    #[serde(serialize_with = "crate::utils::serialize_vec_arc")]
    #[serde(deserialize_with = "crate::utils::deserialize_vec_arc")]
    pub copy_permutation_polys: Vec<Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    #[serde(serialize_with = "crate::utils::serialize_vec_arc")]
    #[serde(deserialize_with = "crate::utils::deserialize_vec_arc")]
    pub constant_columns: Vec<Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    #[serde(serialize_with = "crate::utils::serialize_vec_arc")]
    #[serde(deserialize_with = "crate::utils::deserialize_vec_arc")]
    pub lookup_tables_columns: Vec<Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    pub table_ids_column_idxes: Vec<usize>,
    pub selectors_placement: TreeNode,
}

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > MemcopySerializable for SetupBaseStorage<F, P, A, B>
where
    Self: 'static,
{
    fn read_from_buffer<R: std::io::Read>(mut src: R) -> Result<Self, Box<dyn std::error::Error>> {
        use crate::cs::implementations::fast_serialization::*;
        let copy_permutation_polys = read_vec_from_buffer(&mut src)?;
        let constant_columns = read_vec_from_buffer(&mut src)?;
        let lookup_tables_columns = read_vec_from_buffer(&mut src)?;

        // now we just use bincode for small structures
        let table_ids_column_idxes: Vec<usize> = bincode::deserialize_from(&mut src)?;
        let selectors_placement: TreeNode = bincode::deserialize_from(&mut src)?;

        let new = Self {
            copy_permutation_polys,
            constant_columns,
            lookup_tables_columns,
            table_ids_column_idxes,
            selectors_placement,
        };

        Ok(new)
    }

    fn write_into_buffer<W: std::io::Write>(
        &self,
        mut dst: W,
    ) -> Result<(), Box<dyn std::error::Error>> {
        use crate::cs::implementations::fast_serialization::*;

        write_vec_into_buffer(&self.copy_permutation_polys, &mut dst)?;
        write_vec_into_buffer(&self.constant_columns, &mut dst)?;
        write_vec_into_buffer(&self.lookup_tables_columns, &mut dst)?;

        bincode::serialize_into(&mut dst, &self.table_ids_column_idxes)?;
        bincode::serialize_into(&mut dst, &self.selectors_placement)?;

        Ok(())
    }
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug, PartialEq(bound = ""), Eq)]
#[serde(
    bound = "F: serde::Serialize + serde::de::DeserializeOwned, P: serde::Serialize + serde::de::DeserializeOwned"
)]
pub struct SetupStorage<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F> = F,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    // We store full LDEs of the original polynomials.
    // For those we can produce adapters to properly iterate over
    // future leafs of the oracles
    #[serde(serialize_with = "crate::utils::serialize_vec_with_allocator")]
    #[serde(deserialize_with = "crate::utils::deserialize_vec_with_allocator")]
    pub copy_permutation_polys: Vec<ArcGenericLdeStorage<F, P, A, B>, B>,
    #[serde(serialize_with = "crate::utils::serialize_vec_with_allocator")]
    #[serde(deserialize_with = "crate::utils::deserialize_vec_with_allocator")]
    pub constant_columns: Vec<ArcGenericLdeStorage<F, P, A, B>, B>,
    #[serde(serialize_with = "crate::utils::serialize_vec_with_allocator")]
    #[serde(deserialize_with = "crate::utils::deserialize_vec_with_allocator")]
    pub lookup_tables_columns: Vec<ArcGenericLdeStorage<F, P, A, B>, B>, // include the ID of the TABLE itself
    pub table_ids_column_idxes: Vec<usize>,
    pub used_lde_degree: usize,
}

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > MemcopySerializable for SetupStorage<F, P, A, B>
where
    Self: 'static,
{
    fn read_from_buffer<R: std::io::Read>(mut src: R) -> Result<Self, Box<dyn std::error::Error>> {
        use crate::cs::implementations::fast_serialization::*;
        let copy_permutation_polys = read_vec_from_buffer(&mut src)?;
        let constant_columns = read_vec_from_buffer(&mut src)?;
        let lookup_tables_columns = read_vec_from_buffer(&mut src)?;

        // now we just use bincode for small structures
        let table_ids_column_idxes: Vec<usize> = bincode::deserialize_from(&mut src)?;

        let mut buffer = [0u8; 8];
        src.read_exact(&mut buffer).map_err(Box::new)?;
        let used_lde_degree = u64::from_le_bytes(buffer) as usize;

        assert!(used_lde_degree.is_power_of_two());

        let new = Self {
            copy_permutation_polys,
            constant_columns,
            lookup_tables_columns,
            table_ids_column_idxes,
            used_lde_degree,
        };

        Ok(new)
    }

    fn write_into_buffer<W: std::io::Write>(
        &self,
        mut dst: W,
    ) -> Result<(), Box<dyn std::error::Error>> {
        use crate::cs::implementations::fast_serialization::*;

        write_vec_into_buffer(&self.copy_permutation_polys, &mut dst)?;
        write_vec_into_buffer(&self.constant_columns, &mut dst)?;
        write_vec_into_buffer(&self.lookup_tables_columns, &mut dst)?;

        bincode::serialize_into(&mut dst, &self.table_ids_column_idxes)?;

        dst.write_all(&(self.used_lde_degree as u64).to_le_bytes())
            .map_err(Box::new)?;

        Ok(())
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct LookupSetupStorage<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F> = F,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    // We store full LDEs of the original polynomials.
    // For those we can produce adapters to properly iterate over
    // future leafs of the oracles
    pub table_polynomials: Vec<ArcGenericLdeStorage<F, P, A, B>, B>,
}

#[derive(Derivative)]
#[derivative(Clone, Copy, PartialEq, Eq, Hash)]
pub struct AuxTraceInformation<F: PrimeField, P: field::traits::field_like::PrimeFieldLike = F> {
    domain_size: usize,
    main_domain_generator: P,
    lde_generator: P,
    additional_coset: P,
    _marker: std::marker::PhantomData<F>,
}

// This is a capture over the full trace: copiable variabless,
// witness and constant columns, but no lookup because an argument about lookups is separate
#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct TraceHolder<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F> = F,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    pub variables: WitnessStorage<F, P, A, B>,
    pub setup: SetupStorage<F, P, A, B>,
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > TraceHolder<F, P, A, B>
{
    pub(crate) fn dump_row_in_main_domain(&self, row: usize) -> (Vec<P>, Vec<P>, Vec<P>) {
        assert!(crate::config::DEBUG_SATISFIABLE);

        let mut vars = vec![];
        let mut wits = vec![];
        let mut constants = vec![];

        for column in self.variables.variables_columns.iter() {
            vars.push(column.storage[0].storage[row]);
        }
        for column in self.variables.witness_columns.iter() {
            wits.push(column.storage[0].storage[row]);
        }
        for column in self.setup.constant_columns.iter() {
            constants.push(column.storage[0].storage[row]);
        }

        (vars, wits, constants)
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct ProverTraceView<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F> = F,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    variables: Vec<ArcGenericLdeStorage<F, P, A, B>, B>,
    witness: Vec<ArcGenericLdeStorage<F, P, A, B>, B>,
    constants: Vec<ArcGenericLdeStorage<F, P, A, B>, B>,
    constants_offset: usize,
    gate_chunks_offset: PerChunkOffset,
    iterator: LdeIterator,
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > ProverTraceView<F, P, A, B>
{
    #[inline]
    pub(crate) fn from_full_trace(trace: &TraceHolder<F, P, A, B>) -> Self {
        let typical_len = trace.variables.variables_columns[0].inner_len();
        let outer_len = trace.variables.variables_columns[0].outer_len();
        let iterator = LdeIterator::full_iterator(outer_len, typical_len);
        debug_assert!(trace.variables.variables_columns[0].outer_len() > 0);

        let variables = trace.variables.variables_columns.clone();
        let witness = trace.variables.witness_columns.clone();
        let constants = trace.setup.constant_columns.clone();

        Self {
            variables,
            witness,
            constants,
            constants_offset: 0,
            gate_chunks_offset: PerChunkOffset::zero(),
            iterator,
        }
    }

    pub(crate) fn subset(
        &self,
        variables_range: Range<usize>,
        witness_range: Range<usize>,
        constants_range: Range<usize>,
    ) -> Self {
        let iterator = self.iterator.clone();

        let variables = self.variables[variables_range].to_vec_in(B::default());
        let witness = self.witness[witness_range].to_vec_in(B::default());
        let constants = self.constants[constants_range].to_vec_in(B::default());

        Self {
            variables,
            witness,
            constants,
            constants_offset: 0,
            gate_chunks_offset: PerChunkOffset::zero(),
            iterator,
        }
    }

    #[inline]
    pub(crate) fn from_trace_for_degree(trace: &TraceHolder<F, P, A, B>, degree: usize) -> Self {
        let typical_len = trace.variables.variables_columns[0].inner_len();
        debug_assert!(trace.variables.variables_columns[0].outer_len() > 0);

        // we can not collect due to allocator here, but fine
        let mut variables =
            Vec::with_capacity_in(trace.variables.variables_columns.len(), B::default());
        for el in trace.variables.variables_columns.iter() {
            variables.push(el.subset_for_degree(degree));
        }

        let mut witness =
            Vec::with_capacity_in(trace.variables.witness_columns.len(), B::default());
        for el in trace.variables.witness_columns.iter() {
            witness.push(el.subset_for_degree(degree));
        }

        let mut constants = Vec::with_capacity_in(trace.setup.constant_columns.len(), B::default());
        for el in trace.setup.constant_columns.iter() {
            constants.push(el.subset_for_degree(degree));
        }

        let iterator = LdeIterator::full_iterator(degree, typical_len);

        Self {
            variables,
            witness,
            constants,
            constants_offset: 0,
            gate_chunks_offset: PerChunkOffset::zero(),
            iterator,
        }
    }

    #[inline]
    pub(crate) fn chunks_from_trace_for_degree(
        trace: &TraceHolder<F, P, A, B>,
        degree: usize,
        num_workers: usize,
    ) -> Vec<Self> {
        let typical_len = trace.variables.variables_columns[0].inner_len();
        debug_assert!(trace.variables.variables_columns[0].outer_len() > 0);

        // we can not collect due to allocator here, but fine
        let mut variables =
            Vec::with_capacity_in(trace.variables.variables_columns.len(), B::default());
        for el in trace.variables.variables_columns.iter() {
            variables.push(el.subset_for_degree(degree));
        }

        let mut witness =
            Vec::with_capacity_in(trace.variables.witness_columns.len(), B::default());
        for el in trace.variables.witness_columns.iter() {
            witness.push(el.subset_for_degree(degree));
        }

        let mut constants = Vec::with_capacity_in(trace.setup.constant_columns.len(), B::default());
        for el in trace.setup.constant_columns.iter() {
            constants.push(el.subset_for_degree(degree));
        }

        let iterators =
            LdeIterator::chunk_lde_storage_for_num_workers(degree, typical_len, num_workers);

        let mut result = Vec::with_capacity(num_workers);
        for iterator in iterators.into_iter() {
            let chunk = Self {
                variables: variables.clone(),
                witness: witness.clone(),
                constants: constants.clone(),
                constants_offset: 0,
                gate_chunks_offset: PerChunkOffset::zero(),
                iterator,
            };

            result.push(chunk);
        }

        result
    }
}

use crate::cs::traits::trace_source::{TraceSource, TraceSourceDerivable};

// TODO: here we can use unchecked methods later on because driving iterations will
// me "trusted", so getting "current" value can be without range checks

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > TraceSource<F, P> for ProverTraceView<F, P, A, B>
{
    #[inline(always)]
    fn get_variable_value(&self, variable_idx: usize) -> P {
        let (outer, inner) = self.iterator.current();
        debug_assert!(
            self.gate_chunks_offset.variables_offset + variable_idx < self.variables.len(),
            "trying to access a variables column number {} (zero enumerated) at chunk offset {}, but there are only {} columns in the system",
            variable_idx,
            self.gate_chunks_offset.variables_offset,
            self.variables.len()
        );

        // unsafe {
        //     *self.variables.get_unchecked(self.gate_chunks_offset.variables_offset + variable_idx)
        //         .storage.get_unchecked(outer)
        //         .storage.get_unchecked(inner)
        // }
        self.variables[self.gate_chunks_offset.variables_offset + variable_idx].storage[outer]
            .storage[inner]
    }

    #[inline(always)]
    fn get_constant_value(&self, constant_idx: usize) -> P {
        let (outer, inner) = self.iterator.current();
        debug_assert!(
            self.constants_offset + self.gate_chunks_offset.constants_offset + constant_idx < self.constants.len(),
            "trying to access a constants column number {} (zero enumerated) at chunk offset {} and gate offset {}, but there are only {} columns in the system",
            constant_idx,
            self.gate_chunks_offset.constants_offset,
            self.constants_offset,
            self.constants.len()
        );
        // unsafe {
        //     *self.constants.get_unchecked(self.gate_chunks_offset.constants_offset + constant_idx)
        //         .storage.get_unchecked(outer)
        //         .storage.get_unchecked(inner)
        // }
        self.constants
            [self.constants_offset + self.gate_chunks_offset.constants_offset + constant_idx]
            .storage[outer]
            .storage[inner]
    }

    #[inline(always)]
    fn get_witness_value(&self, witness_idx: usize) -> P {
        debug_assert!(
            self.gate_chunks_offset.witnesses_offset + witness_idx < self.witness.len(),
            "trying to access a witness column number {} (zero enumerated) at chunk offset {}, but there are only {} columns in the system",
            witness_idx,
            self.gate_chunks_offset.witnesses_offset,
            self.witness.len()
        );
        let (outer, inner) = self.iterator.current();
        // unsafe {
        //     *self.witness.get_unchecked(self.gate_chunks_offset.witnesses_offset + witness_idx)
        //         .storage.get_unchecked(outer)
        //         .storage.get_unchecked(inner)
        // }
        self.witness[self.gate_chunks_offset.witnesses_offset + witness_idx].storage[outer].storage
            [inner]
    }

    #[inline(always)]
    fn dump_current_row<C: GoodAllocator>(&self, dst: &mut Vec<P, C>) {
        let (outer, inner) = self.iterator.current();
        // we just write down variables, witnesses and constants without offsets
        for var in self.variables.iter() {
            dst.push(var.storage[outer].storage[inner]);
        }
        for var in self.witness.iter() {
            dst.push(var.storage[outer].storage[inner]);
        }
        for var in self.constants.iter() {
            dst.push(var.storage[outer].storage[inner]);
        }
    }
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > TraceSourceDerivable<F, P> for ProverTraceView<F, P, A, B>
{
    #[inline]
    fn num_iterations(&self) -> usize {
        self.iterator.num_iterations()
    }
    #[inline(always)]
    fn reset_gate_chunk_offset(&mut self) {
        self.gate_chunks_offset = PerChunkOffset::zero();
    }
    #[inline(always)]
    fn offset_for_next_chunk(&mut self, gate_chunks_offset: &PerChunkOffset) {
        self.gate_chunks_offset.add_offset(gate_chunks_offset);
    }
    #[inline(always)]
    fn advance(&mut self) {
        self.iterator.advance();
    }
    #[inline(always)]
    fn set_constants_offset(&mut self, offset: usize) {
        debug_assert!(offset < self.constants.len());
        self.constants_offset = offset;
    }
}

#[derive(Derivative)]
#[derivative(Clone, Debug)]
pub struct SatisfiabilityCheckRowView<
    F: BaseField,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    pub variables: Vec<Arc<Polynomial<F, LagrangeForm, A>>, B>,
    pub witness: Vec<Arc<Polynomial<F, LagrangeForm, A>>, B>,
    pub constants: Vec<Arc<Polynomial<F, LagrangeForm, A>>, B>,
    pub constants_offset: usize,
    pub gate_chunks_offset: PerChunkOffset,
    pub index: usize,
}

impl<F: BaseField, A: GoodAllocator, B: GoodAllocator> SatisfiabilityCheckRowView<F, A, B> {
    #[inline]
    pub fn from_storages(
        variables: Vec<Polynomial<F, LagrangeForm, A>, B>,
        witness: Vec<Polynomial<F, LagrangeForm, A>, B>,
        constants: Vec<Polynomial<F, LagrangeForm, A>, B>,
    ) -> Self {
        let mut vars = Vec::with_capacity_in(variables.len(), B::default());
        variables.into_iter().map(Arc::new).collect_into(&mut vars);

        let mut wits = Vec::with_capacity_in(witness.len(), B::default());
        witness.into_iter().map(Arc::new).collect_into(&mut wits);

        let mut consts = Vec::with_capacity_in(constants.len(), B::default());
        constants
            .into_iter()
            .map(Arc::new)
            .collect_into(&mut consts);

        Self {
            variables: vars,
            witness: wits,
            constants: consts,
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
        variables_range: Range<usize>,
        witness_range: Range<usize>,
        constants_range: Range<usize>,
    ) -> Self {
        Self {
            variables: self.variables[variables_range].to_vec_in(B::default()),
            witness: self.witness[witness_range].to_vec_in(B::default()),
            constants: self.constants[constants_range].to_vec_in(B::default()),
            constants_offset: 0,
            gate_chunks_offset: PerChunkOffset::zero(),
            index: 0,
        }
    }
}

impl<F: BaseField, A: GoodAllocator, B: GoodAllocator> TraceSource<F, F>
    for SatisfiabilityCheckRowView<F, A, B>
{
    #[inline(always)]
    fn get_variable_value(&self, variable_idx: usize) -> F {
        self.variables[self.gate_chunks_offset.variables_offset + variable_idx].storage[self.index]
    }

    #[inline(always)]
    fn get_constant_value(&self, constant_idx: usize) -> F {
        self.constants
            [self.constants_offset + self.gate_chunks_offset.constants_offset + constant_idx]
            .storage[self.index]
    }

    #[inline(always)]
    fn get_witness_value(&self, witness_idx: usize) -> F {
        self.witness[self.gate_chunks_offset.witnesses_offset + witness_idx].storage[self.index]
    }

    #[inline(always)]
    fn dump_current_row<C: GoodAllocator>(&self, _dst: &mut Vec<F, C>) {
        unimplemented!("Satisfiability checker doesn't use per-row access");
    }
}

impl<F: BaseField, A: GoodAllocator, B: GoodAllocator> TraceSourceDerivable<F, F>
    for SatisfiabilityCheckRowView<F, A, B>
{
    #[inline]
    fn num_iterations(&self) -> usize {
        1
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
        // do nothing, we drive it manually
    }
    #[inline]
    fn set_constants_offset(&mut self, offset: usize) {
        debug_assert!(
            offset <= self.constants.len(),
            "there are only {} constants in the row in storage when trying to set offset {}",
            self.constants.len(),
            offset
        );
        self.constants_offset = offset;
    }
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > SetupStorage<F, P, A, B>
{
    pub(crate) fn flattened_source(
        &self,
    ) -> impl Iterator<Item = &ArcGenericLdeStorage<F, P, A, B>> + Clone {
        self.copy_permutation_polys
            .iter()
            .chain(self.constant_columns.iter())
            .chain(self.lookup_tables_columns.iter())
    }
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > WitnessStorage<F, P, A, B>
{
    pub(crate) fn flattened_source(
        &self,
    ) -> impl Iterator<Item = &ArcGenericLdeStorage<F, P, A, B>> + Clone {
        self.variables_columns
            .iter()
            .chain(self.witness_columns.iter())
            .chain(self.lookup_multiplicities_polys.iter())
    }
}

impl<
        F: PrimeField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > SecondStageProductsStorage<F, P, A, B>
{
    pub(crate) fn flattened_source(
        &self,
    ) -> impl Iterator<Item = &ArcGenericLdeStorage<F, P, A, B>> + Clone {
        self.z_poly
            .iter()
            .chain(self.intermediate_polys.iter().flatten())
            .chain(self.lookup_witness_encoding_polys.iter().flatten())
            .chain(self.lookup_multiplicities_encoding_polys.iter().flatten())
    }
}

#[cfg(test)]
mod test {
    use crate::field::Field;

    use super::*;
    type F = crate::field::goldilocks::GoldilocksField;

    #[test]
    fn baseline_evaluation() {
        let size = 1 << 23;
        let a = vec![F::ONE; size];
        let b = vec![F::TWO; size];
        let c = vec![F::MINUS_ONE; size];
        let mut d = vec![F::ZERO; size];
        let c0 = vec![F::ONE; size];
        let c1 = vec![F::MINUS_ONE; size];

        let worker = Worker::new_with_num_threads(8);

        let now = std::time::Instant::now();
        worker.scope(size, |scope, chunk_size| {
            for (((((a, b), c), d), c0), c1) in a
                .chunks(chunk_size)
                .zip(b.chunks(chunk_size))
                .zip(c.chunks(chunk_size))
                .zip(d.chunks_mut(chunk_size))
                .zip(c0.chunks(chunk_size))
                .zip(c1.chunks(chunk_size))
            {
                scope.spawn(move |_| {
                    for (((((a, b), c), d), c0), c1) in a
                        .iter()
                        .zip(b.iter())
                        .zip(c.iter())
                        .zip(d.iter_mut())
                        .zip(c0.iter())
                        .zip(c1.iter())
                    {
                        let mut tmp = *a;
                        tmp.mul_assign(b).mul_assign(c0);

                        let mut t = *c;
                        t.mul_assign(c1);

                        tmp.add_assign(&t);

                        *d = tmp;
                    }
                });
            }
        });

        log!("Single FMA gate evaluation takes {:?}", now.elapsed());
    }
}
