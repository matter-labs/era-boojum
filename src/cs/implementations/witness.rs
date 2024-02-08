use crate::cs::implementations::fast_serialization::MemcopySerializable;
use crate::cs::traits::GoodAllocator;
use std::alloc::Global;
use std::sync::atomic::AtomicU32;

use super::fast_serialization::read_vec_from_buffer;
use super::fast_serialization::write_vec_into_buffer;
use super::*;
use crate::cs::implementations::hints::*;
use crate::cs::implementations::polynomial::*;
use crate::cs::implementations::reference_cs::*;

use crate::config::*;
use crate::utils::*;

// even though it's public, it has internal requirements over alignment and
// can only be constructed by implementations
#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "F: serde::Serialize + serde::de::DeserializeOwned")]
pub struct WitnessSet<F: SmallField> {
    pub public_inputs_values: Vec<F>,
    pub public_inputs_with_locations: Vec<(usize, usize, F)>,
    pub variables: Vec<Polynomial<F, LagrangeForm, Global>>,
    pub witness: Vec<Polynomial<F, LagrangeForm, Global>>,
    pub multiplicities: Vec<Polynomial<F, LagrangeForm, Global>>,
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Debug)]
#[serde(bound = "F: serde::Serialize + serde::de::DeserializeOwned")]
pub struct WitnessVec<F: SmallField, A: GoodAllocator = Global> {
    pub public_inputs_locations: Vec<(usize, usize)>,
    #[serde(serialize_with = "crate::utils::serialize_vec_with_allocator")]
    #[serde(deserialize_with = "crate::utils::deserialize_vec_with_allocator")]
    pub all_values: Vec<F, A>,
    #[serde(serialize_with = "crate::utils::serialize_vec_with_allocator")]
    #[serde(deserialize_with = "crate::utils::deserialize_vec_with_allocator")]
    pub multiplicities: Vec<u32, A>,
}

impl<F: SmallField, A: GoodAllocator> MemcopySerializable for WitnessVec<F, A>
where
    A: 'static,
{
    fn read_from_buffer<R: std::io::Read>(mut src: R) -> Result<Self, Box<dyn std::error::Error>> {
        let public_inputs_locations = read_vec_from_buffer(&mut src)?;
        let all_values = MemcopySerializable::read_from_buffer(&mut src)?;
        let multiplicities = read_vec_from_buffer(&mut src)?;

        let new = Self {
            public_inputs_locations,
            all_values,
            multiplicities,
        };

        Ok(new)
    }

    fn write_into_buffer<W: std::io::Write>(
        &self,
        mut dst: W,
    ) -> Result<(), Box<dyn std::error::Error>> {
        write_vec_into_buffer(&self.public_inputs_locations, &mut dst)?;
        MemcopySerializable::write_into_buffer(&self.all_values, &mut dst)?;
        write_vec_into_buffer(&self.multiplicities, &mut dst)?;

        Ok(())
    }
}

impl<F: SmallField> WitnessSet<F> {
    pub fn pretty_compare(&self, other: &Self) {
        // assert_eq!(self.public_inputs_values, other.public_inputs_values);
        // assert_eq!(self.public_inputs_with_locations, other.public_inputs_with_locations);
        log!("Comparing variables");
        for (_idx, (a, b)) in self
            .variables
            .iter()
            .zip(other.variables.iter())
            .enumerate()
        {
            a.pretty_compare(b);
        }
        log!("Comparing witnesses");
        for (_idx, (a, b)) in self.witness.iter().zip(other.witness.iter()).enumerate() {
            a.pretty_compare(b);
        }
        log!("Comparing multiplicities");
        for (_idx, (a, b)) in self
            .multiplicities
            .iter()
            .zip(other.multiplicities.iter())
            .enumerate()
        {
            a.pretty_compare(b);
        }
    }
}

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        CFG: CSConfig,
        A: GoodAllocator,
    > CSReferenceAssembly<F, P, CFG, A>
{
    pub(crate) fn materialize_witness_polynomials(
        &mut self,
        worker: &Worker,
    ) -> Vec<Polynomial<F, LagrangeForm, Global>> {
        assert!(
            CFG::SetupConfig::KEEP_SETUP,
            "CS is not configured to keep setup to know variables placement"
        );

        assert!(
            CFG::WitnessConfig::EVALUATE_WITNESS,
            "CS is not configured to have witness available"
        );

        let capacity = self.parameters.num_witness_columns
            + self
                .evaluation_data_over_specialized_columns
                .total_num_witnesses_for_specialized_columns;

        if capacity == 0 {
            return vec![];
        }

        let storage = initialize_with_alignment_of::<_, P>(F::ZERO, self.max_trace_len);
        let poly = Polynomial::from_storage(storage);

        let mut polies = Vec::with_capacity(capacity);
        for _ in 0..(capacity - 1) {
            polies.push(poly.clone_respecting_allignment::<P>());
        }
        polies.push(poly);

        let witness_ref = &self.witness.as_ref().unwrap().all_values;

        worker.scope(polies.len(), |scope, chunk_size| {
            for (dst, src) in polies
                .chunks_mut(chunk_size)
                .zip(self.witness_placement_data.chunks(chunk_size))
            {
                scope.spawn(move |_| {
                    for (dst, src) in dst.iter_mut().zip(src.iter()) {
                        for (dst, src) in dst.storage.iter_mut().zip(src.iter()) {
                            if src.is_placeholder() == false {
                                *dst = witness_ref[src.0 as usize];
                            }
                        }
                    }
                });
            }
        });

        polies
    }

    pub(crate) fn materialize_variables_polynomials(
        &mut self,
        worker: &Worker,
    ) -> Vec<Polynomial<F, LagrangeForm, Global>> {
        assert!(
            CFG::SetupConfig::KEEP_SETUP,
            "CS is not configured to keep setup to know variables placement"
        );

        assert!(
            CFG::WitnessConfig::EVALUATE_WITNESS,
            "CS is not configured to have witness available"
        );
        if self.parameters.num_columns_under_copy_permutation
            + self
                .evaluation_data_over_specialized_columns
                .total_num_variables_for_specialized_columns
            == 0
        {
            return vec![];
        }

        let storage = initialize_with_alignment_of::<_, P>(F::ZERO, self.max_trace_len);
        let poly = Polynomial::from_storage(storage);

        let capacity = self.parameters.num_columns_under_copy_permutation
            + self
                .evaluation_data_over_specialized_columns
                .total_num_variables_for_specialized_columns;
        let mut result = Vec::with_capacity(capacity);
        for _ in 0..(capacity - 1) {
            result.push(poly.clone_respecting_allignment::<P>());
        }
        result.push(poly);

        let witness_ref = &self.witness.as_ref().unwrap().all_values;

        // we copy column-wise
        worker.scope(result.len(), |scope, chunk_size| {
            for (vars_chunk, polys_chunk) in self
                .copy_permutation_data
                .chunks(chunk_size)
                .zip(result.chunks_mut(chunk_size))
            {
                scope.spawn(move |_| {
                    debug_assert_eq!(vars_chunk.len(), polys_chunk.len());
                    for (vars_column, poly) in vars_chunk.iter().zip(polys_chunk.iter_mut()) {
                        for (var, dst) in vars_column.iter().zip(poly.storage.iter_mut()) {
                            if var.is_placeholder() == false {
                                *dst = witness_ref[var.0 as usize];
                            } else {
                                // we can use 0 as a substitue for all undefined variables,
                                // or add ZK into them
                            }
                        }
                    }
                });
            }
        });

        result
    }

    pub fn materialize_multiplicities_polynomials(
        &mut self,
        worker: &Worker,
    ) -> Vec<Polynomial<F, LagrangeForm, Global>> {
        assert!(
            CFG::WitnessConfig::EVALUATE_WITNESS,
            "CS is not configured to have witness available"
        );
        if self.lookup_parameters == LookupParameters::NoLookup {
            return vec![];
        }

        // we just need to flatten then multiplicities
        let storage = initialize_with_alignment_of::<_, P>(F::ZERO, self.max_trace_len);
        let poly = Polynomial::from_storage(storage);

        let num_subpolys = self.num_multipicities_polys();
        assert_eq!(num_subpolys, 1);

        let mut result = Vec::with_capacity(num_subpolys);
        for _ in 0..(num_subpolys - 1) {
            result.push(poly.clone_respecting_allignment::<P>());
        }
        result.push(poly);

        let flattening_iter = self.lookup_multiplicities.iter().flat_map(|el| el.iter());

        for (idx, dst) in result.iter_mut().enumerate() {
            let num_to_skip = idx * self.max_trace_len;
            let src_it = flattening_iter.clone().skip(num_to_skip);

            worker.scope(dst.storage.len(), |scope, chunk_size| {
                for (idx, dst) in dst.storage.chunks_mut(chunk_size).enumerate() {
                    let src = src_it.clone().skip(idx * chunk_size);
                    scope.spawn(move |_| {
                        for (dst, src) in dst.iter_mut().zip(src) {
                            *dst = F::from_u64_unchecked(AtomicU32::load(
                                src,
                                std::sync::atomic::Ordering::SeqCst,
                            ) as u64);
                        }
                    });
                }
            });
        }

        result
    }

    pub fn materialize_witness_polynomials_from_dense_hint(
        &mut self,
        worker: &Worker,
        hint: &DenseWitnessCopyHint,
    ) -> Vec<Polynomial<F, LagrangeForm, Global>> {
        assert!(
            CFG::WitnessConfig::EVALUATE_WITNESS,
            "CS is not configured to have witness available"
        );

        let capacity = self.parameters.num_witness_columns
            + self
                .evaluation_data_over_specialized_columns
                .total_num_witnesses_for_specialized_columns;

        if capacity == 0 {
            return vec![];
        }

        let storage = initialize_with_alignment_of::<_, P>(F::ZERO, self.max_trace_len);
        let poly = Polynomial::from_storage(storage);
        assert_eq!(capacity, hint.maps.len());

        let mut result = Vec::with_capacity(capacity);
        for _ in 0..(capacity - 1) {
            result.push(poly.clone_respecting_allignment::<P>());
        }
        result.push(poly);

        let witness_ref = &self.witness.as_ref().unwrap().all_values;

        worker.scope(result.len(), |scope, chunk_size| {
            for (dst, src) in result
                .chunks_mut(chunk_size)
                .zip(hint.maps.chunks(chunk_size))
            {
                scope.spawn(move |_| {
                    for (dst, src) in dst.iter_mut().zip(src.iter()) {
                        for (dst, src) in dst.storage.iter_mut().zip(src.iter()) {
                            if src.is_placeholder() == false {
                                *dst = witness_ref[src.0 as usize];
                            }
                        }
                    }
                });
            }
        });

        result
    }

    pub fn materialize_variables_polynomials_from_dense_hint(
        &mut self,
        worker: &Worker,
        hint: &DenseVariablesCopyHint,
    ) -> Vec<Polynomial<F, LagrangeForm, Global>> {
        assert!(
            CFG::WitnessConfig::EVALUATE_WITNESS,
            "CS is not configured to have witness available"
        );

        if self.parameters.num_columns_under_copy_permutation
            + self
                .evaluation_data_over_specialized_columns
                .total_num_variables_for_specialized_columns
            == 0
        {
            return vec![];
        }

        let storage = initialize_with_alignment_of::<_, P>(F::ZERO, self.max_trace_len);
        let poly = Polynomial::from_storage(storage);

        let capacity = self.parameters.num_columns_under_copy_permutation
            + self
                .evaluation_data_over_specialized_columns
                .total_num_variables_for_specialized_columns;
        assert_eq!(capacity, hint.maps.len());

        let mut result = Vec::with_capacity(capacity);
        for _ in 0..(capacity - 1) {
            result.push(poly.clone_respecting_allignment::<P>());
        }
        result.push(poly);

        let witness_ref = &self.witness.as_ref().unwrap().all_values;

        // we copy column-wise (each worker to it's independent set of columns)
        worker.scope(result.len(), |scope, chunk_size| {
            for (vars_chunk, polys_chunk) in hint
                .maps
                .chunks(chunk_size)
                .zip(result.chunks_mut(chunk_size))
            {
                scope.spawn(move |_| {
                    debug_assert_eq!(vars_chunk.len(), polys_chunk.len());
                    for (vars_column, poly) in vars_chunk.iter().zip(polys_chunk.iter_mut()) {
                        for (var, dst) in vars_column.iter().zip(poly.storage.iter_mut()) {
                            if var.is_placeholder() == false {
                                *dst = witness_ref[var.0 as usize];
                            } else {
                                // we can use 0 as a substitue for all undefined variables,
                                // or add ZK into them
                            }
                        }
                    }
                });
            }
        });

        result
    }

    pub fn witness_set_from_witness_vec(
        &self,
        witness_set: &WitnessVec<F, A>,
        vars_hint: &DenseVariablesCopyHint,
        wits_hint: &DenseWitnessCopyHint,
        worker: &Worker,
    ) -> WitnessSet<F> {
        let variables_columns = if self.parameters.num_columns_under_copy_permutation
            + self
                .evaluation_data_over_specialized_columns
                .total_num_variables_for_specialized_columns
            == 0
        {
            vec![]
        } else {
            let storage = initialize_with_alignment_of::<_, P>(F::ZERO, self.max_trace_len);
            let poly = Polynomial::from_storage(storage);

            let capacity = self.parameters.num_columns_under_copy_permutation
                + self
                    .evaluation_data_over_specialized_columns
                    .total_num_variables_for_specialized_columns;
            assert_eq!(capacity, vars_hint.maps.len());

            let mut result = Vec::with_capacity(capacity);
            for _ in 0..(capacity - 1) {
                result.push(poly.clone_respecting_allignment::<P>());
            }
            result.push(poly);
            // copy

            // we copy column-wise (each worker to it's independent set of columns)
            worker.scope(result.len(), |scope, chunk_size| {
                for (vars_chunk, polys_chunk) in vars_hint
                    .maps
                    .chunks(chunk_size)
                    .zip(result.chunks_mut(chunk_size))
                {
                    scope.spawn(move |_| {
                        debug_assert_eq!(vars_chunk.len(), polys_chunk.len());
                        for (vars_column, poly) in vars_chunk.iter().zip(polys_chunk.iter_mut()) {
                            for (var, dst) in vars_column.iter().zip(poly.storage.iter_mut()) {
                                if var.is_placeholder() == false {
                                    // our index is just the index of the variable
                                    let as_usize = var.as_variable_index() as usize;
                                    *dst = witness_set.all_values[as_usize];
                                } else {
                                    // we can use 0 as a substitue for all undefined variables,
                                    // or add ZK into them
                                }
                            }
                        }
                    });
                }
            });

            result
        };

        let capacity = self.parameters.num_witness_columns
            + self
                .evaluation_data_over_specialized_columns
                .total_num_witnesses_for_specialized_columns;

        let witness_columns = if capacity == 0 {
            vec![]
        } else {
            let storage = initialize_with_alignment_of::<_, P>(F::ZERO, self.max_trace_len);
            let poly = Polynomial::from_storage(storage);
            assert_eq!(capacity, wits_hint.maps.len());

            let mut result = Vec::with_capacity(capacity);
            for _ in 0..(capacity - 1) {
                result.push(poly.clone_respecting_allignment::<P>());
            }
            result.push(poly);
            // copy

            // we copy column-wise (each worker to it's independent set of columns)
            worker.scope(result.len(), |scope, chunk_size| {
                for (vars_chunk, polys_chunk) in wits_hint
                    .maps
                    .chunks(chunk_size)
                    .zip(result.chunks_mut(chunk_size))
                {
                    scope.spawn(move |_| {
                        debug_assert_eq!(vars_chunk.len(), polys_chunk.len());
                        for (vars_column, poly) in vars_chunk.iter().zip(polys_chunk.iter_mut()) {
                            for (var, dst) in vars_column.iter().zip(poly.storage.iter_mut()) {
                                if var.is_placeholder() == false {
                                    // our index is just the index of the variable
                                    let as_usize = var.as_witness_index() as usize;
                                    *dst = witness_set.all_values[as_usize];
                                } else {
                                    // we can use 0 as a substitue for all undefined variables,
                                    // or add ZK into them
                                }
                            }
                        }
                    });
                }
            });

            result
        };

        let mutliplicities_columns = if self.lookup_parameters == LookupParameters::NoLookup {
            vec![]
        } else {
            // we just need to flatten then multiplicities
            let storage = initialize_with_alignment_of::<_, P>(F::ZERO, self.max_trace_len);
            let poly = Polynomial::from_storage(storage);

            let num_subpolys = self.num_multipicities_polys();
            assert_eq!(num_subpolys, 1);

            let mut result = Vec::with_capacity(num_subpolys);
            for _ in 0..(num_subpolys - 1) {
                result.push(poly.clone_respecting_allignment::<P>());
            }
            result.push(poly);

            // we know it's only 1
            for (dst, src) in result[0]
                .storage
                .iter_mut()
                .zip(witness_set.multiplicities.iter().copied())
            {
                *dst = F::from_u64_unchecked(src as u64);
            }

            result
        };

        let num_public_inputs = witness_set.public_inputs_locations.len();
        let mut public_inputs_only_values = Vec::with_capacity(num_public_inputs);
        let mut public_inputs_with_values = Vec::with_capacity(num_public_inputs);

        for (column, row) in witness_set.public_inputs_locations.iter().copied() {
            let value = variables_columns[column].storage[row];
            public_inputs_with_values.push((column, row, value));
            public_inputs_only_values.push(value);
        }

        WitnessSet {
            public_inputs_values: public_inputs_only_values,
            public_inputs_with_locations: public_inputs_with_values,
            variables: variables_columns,
            witness: witness_columns,
            multiplicities: mutliplicities_columns,
        }
    }
}
