use std::alloc::Global;

use crate::cs::{
    implementations::{
        fast_serialization::MemcopySerializable,
        polynomial::{lde::ArcGenericLdeStorage, GenericPolynomial},
    },
    traits::GoodAllocator,
};

use super::*;

use crate::field::traits::field_like::Flattener;

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Debug, PartialEq(bound = ""), Eq)]
pub struct MerkleTreeWithCap<
    F: PrimeField,
    H: TreeHasher<F>,
    A: GoodAllocator = Global,
    B: GoodAllocator = Global,
> {
    pub cap_size: usize,
    #[serde(bound(serialize = "H::Output: serde::Serialize"))]
    #[serde(bound(deserialize = "H::Output: serde::de::DeserializeOwned"))]
    #[serde(serialize_with = "crate::utils::serialize_vec_with_allocator")]
    #[serde(deserialize_with = "crate::utils::deserialize_vec_with_allocator")]
    pub leaf_hashes: Vec<H::Output, A>,
    #[serde(bound(serialize = "H::Output: serde::Serialize"))]
    #[serde(bound(deserialize = "H::Output: serde::de::DeserializeOwned"))]
    #[serde(serialize_with = "crate::utils::serialize_vec_vec_with_allocators")]
    #[serde(deserialize_with = "crate::utils::deserialize_vec_vec_with_allocators")]
    pub node_hashes_enumerated_from_leafs: Vec<Vec<H::Output, A>, B>,
}

impl<F: PrimeField, H: TreeHasher<F>, A: GoodAllocator, B: GoodAllocator> MemcopySerializable
    for MerkleTreeWithCap<F, H, A, B>
where
    Self: 'static,
    Vec<H::Output, A>: MemcopySerializable,
{
    fn write_into_buffer<W: std::io::Write>(
        &self,
        mut dst: W,
    ) -> Result<(), Box<dyn std::error::Error>> {
        dst.write_all(&(self.cap_size as u64).to_le_bytes())
            .map_err(Box::new)?;

        MemcopySerializable::write_into_buffer(&self.leaf_hashes, &mut dst)?;
        use crate::cs::implementations::fast_serialization::*;
        write_vec_into_buffer(&self.node_hashes_enumerated_from_leafs, &mut dst)?;

        Ok(())
    }

    fn read_from_buffer<R: std::io::Read>(mut src: R) -> Result<Self, Box<dyn std::error::Error>> {
        let mut buffer = [0u8; 8];
        src.read_exact(&mut buffer).map_err(Box::new)?;
        let cap_size = u64::from_le_bytes(buffer) as usize;

        let leaf_hashes = MemcopySerializable::read_from_buffer(&mut src)?;
        use crate::cs::implementations::fast_serialization::*;
        let node_hashes_enumerated_from_leafs = read_vec_from_buffer(&mut src)?;

        let new = Self {
            cap_size,
            leaf_hashes,
            node_hashes_enumerated_from_leafs,
        };

        Ok(new)
    }
}

impl<F: PrimeField, H: TreeHasher<F>, A: GoodAllocator, B: GoodAllocator>
    MerkleTreeWithCap<F, H, A, B>
{
    pub fn construct<P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>>(
        leafs_sources: Vec<ArcGenericLdeStorage<F, P, A, B>, B>,
        cap_size: usize,
        worker: &Worker,
    ) -> Self {
        debug_assert!(cap_size > 0);
        debug_assert!(cap_size.is_power_of_two());

        profile_fn!(merkle_tree_construct);

        let now = std::time::Instant::now();

        let tree_size =
            leafs_sources[0].inner_len() * leafs_sources[0].outer_len() * P::SIZE_FACTOR;
        debug_assert!(tree_size.is_power_of_two());
        let tree_depth = tree_size.trailing_zeros();
        let layers_to_skip = cap_size.trailing_zeros();

        debug_assert!(tree_size > cap_size);
        let elements_per_leaf = leafs_sources.len();

        // simplest job ever - compute by layers with parallelism
        // To prevent to complex parallelism we will work over each individual coset

        let mut leaf_hashes = Vec::with_capacity_in(tree_size, A::default());

        let chunk_size = leafs_sources[0].inner_len() * P::SIZE_FACTOR;
        let inner_len = leafs_sources[0].inner_len(); // in units of P

        // for each coset we need to pick place elements from each individual poly

        let mut sources_flattened = Vec::new_in(B::default());

        profile_section!(work_loop);
        for (coset_idx, dst) in leaf_hashes.spare_capacity_mut()[..tree_size]
            .chunks_mut(chunk_size)
            .enumerate()
        {
            sources_flattened.truncate(0);
            worker.scope_with_num_chunks(inner_len, |scope, subchunk_size, num_subchunks| {
                // we have to make chunks for every source

                let mut sources = Vec::with_capacity_in(leafs_sources.len(), B::default());
                for source in leafs_sources.iter() {
                    let coset = &source.storage[coset_idx];
                    let subchunks = GenericPolynomial::chunks::<B>(coset, subchunk_size);
                    sources.push(subchunks);
                }

                // now transpose and flatten

                for _ in 0..num_subchunks {
                    for s in sources.iter_mut() {
                        sources_flattened.push(s.drain(..1).next().expect("chunk must exist"));
                    }
                }

                let mut flatteners = Vec::with_capacity_in(num_subchunks, B::default());

                for c in sources_flattened.chunks(leafs_sources.len()) {
                    let leaf_flattener = Flattener::new(c.iter().map(|el| el.as_ref()), 1);
                    flatteners.push(leaf_flattener);
                }

                let chunk_in_units_of_base = subchunk_size * P::SIZE_FACTOR;
                // done with a transposition and potential de-vectorization. Now spawn
                for (dst, flattener) in dst
                    .chunks_mut(chunk_in_units_of_base)
                    .zip(flatteners.into_iter())
                {
                    scope.spawn(move |_| {
                        let mut flattener = flattener;
                        debug_assert_eq!(dst.len(), flattener.num_iterations());
                        for dst in dst.iter_mut() {
                            dst.write(H::hash_into_leaf(flattener.next()));
                        }
                    });
                }
            })
        }
        drop(work_loop);

        unsafe { leaf_hashes.set_len(tree_size) };

        log!(
            "Merkle tree of size 2^{} leaf hashes taken {:?} for {} elements per leaf",
            tree_size.trailing_zeros(),
            now.elapsed(),
            elements_per_leaf,
        );

        let num_layers_to_construct = tree_depth - layers_to_skip;

        Self::continue_from_leaf_hashes(leaf_hashes, num_layers_to_construct, cap_size, worker)
    }

    // used for first of FRI oracles, where inputs are results of arithmetic operations,
    // and are not base vectors
    pub fn construct_by_chunking<
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    >(
        leafs_sources: Vec<ArcGenericLdeStorage<F, P, A, B>, B>,
        elements_to_take_per_leaf: usize,
        cap_size: usize,
        worker: &Worker,
    ) -> Self {
        assert!(cap_size > 0);
        assert!(cap_size.is_power_of_two());
        assert!(elements_to_take_per_leaf.is_power_of_two());

        let now = std::time::Instant::now();

        let inner_len = leafs_sources[0].inner_len();
        let outer_len = leafs_sources[0].outer_len();

        // we expect original polys to be large enough, so we can take
        // the full leaf-going coset from the single "inner" element

        assert!(inner_len * P::SIZE_FACTOR / elements_to_take_per_leaf >= 1);
        assert!(inner_len * P::SIZE_FACTOR % elements_to_take_per_leaf == 0);

        let tree_size = inner_len * outer_len * P::SIZE_FACTOR / elements_to_take_per_leaf;

        debug_assert!(tree_size.is_power_of_two());
        let tree_depth = tree_size.trailing_zeros();
        let layers_to_skip = cap_size.trailing_zeros();

        assert!(tree_size > cap_size);

        // simplest job ever - compute by layers with parallelism
        // To prevent to complex parallelism we will work over each individual coset

        let mut leaf_hashes = Vec::with_capacity_in(tree_size, A::default());

        // From every ArcGeneric... we will take elements_to_take_per_leaf elements
        // we will work over cosets independently for parallelism

        // each of the cosets from LDEs that we have as inputs will give this number of elements in the result
        let dst_chunk_size_per_coset = inner_len * P::SIZE_FACTOR / elements_to_take_per_leaf;

        assert!(tree_size % dst_chunk_size_per_coset == 0);

        // for each coset we need to pick place elements from each individual poly

        for (coset_idx, dst) in leaf_hashes.spare_capacity_mut()[..tree_size]
            .chunks_mut(dst_chunk_size_per_coset)
            .enumerate()
        {
            // each worker will create its subpart of leaf hashes, and for simplicity
            // we work over parts of the tree produced by individual cosets of sources
            // independently as they never overlap
            worker.scope_with_num_chunks(
                dst_chunk_size_per_coset,
                |scope, dst_subchunk_size, num_subchunks| {
                    // we have to make chunks for every source

                    assert_eq!(
                        dst_subchunk_size * elements_to_take_per_leaf % P::SIZE_FACTOR,
                        0
                    );
                    assert!(dst_subchunk_size * elements_to_take_per_leaf / P::SIZE_FACTOR > 0);

                    // this is in units of base field
                    let source_subchunk_size = dst_subchunk_size * elements_to_take_per_leaf;

                    let mut sources = Vec::with_capacity_in(num_subchunks, B::default());
                    sources.resize(
                        num_subchunks,
                        Vec::with_capacity_in(leafs_sources.len(), B::default()),
                    );
                    // we can playout more than one poly one after another
                    for source in leafs_sources.iter() {
                        let coset = &source.storage[coset_idx];
                        let as_base_slice = P::slice_into_base_slice(&coset.storage);
                        assert_eq!(
                            as_base_slice.chunks(source_subchunk_size).len(),
                            dst.chunks(dst_subchunk_size).len()
                        );
                        assert_eq!(
                            as_base_slice
                                .chunks_exact(source_subchunk_size)
                                .remainder()
                                .len(),
                            dst.chunks_exact(dst_subchunk_size).remainder().len()
                                * elements_to_take_per_leaf
                        );
                        for (chunk_idx, chunk_in_base) in
                            as_base_slice.chunks(source_subchunk_size).enumerate()
                        {
                            // and we additionally chunk them
                            assert_eq!(chunk_in_base.len() % elements_to_take_per_leaf, 0);
                            assert!(chunk_in_base.len() / elements_to_take_per_leaf > 0);
                            sources[chunk_idx]
                                .push(chunk_in_base.chunks(elements_to_take_per_leaf));
                        }
                    }

                    // done with a transposition and potential de-vectorization. Now spawn
                    for (dst, source) in dst.chunks_mut(dst_subchunk_size).zip(sources.into_iter())
                    {
                        let mut source = source;
                        scope.spawn(move |_| {
                            debug_assert_eq!(dst.len(), source[0].len());
                            let mut buffer = Vec::new_in(B::default());
                            for dst in dst.iter_mut() {
                                buffer.clear();
                                for subsource in source.iter_mut() {
                                    buffer.extend_from_slice(subsource.next().unwrap());
                                }
                                dst.write(H::hash_into_leaf(&buffer));
                            }
                        });
                    }
                },
            )
        }

        unsafe { leaf_hashes.set_len(tree_size) };

        log!(
            "Merkle tree of size 2^{} leaf hashes taken {:?}",
            tree_size.trailing_zeros(),
            now.elapsed()
        );

        let num_layers_to_construct = tree_depth - layers_to_skip;

        Self::continue_from_leaf_hashes(leaf_hashes, num_layers_to_construct, cap_size, worker)
    }

    pub fn construct_by_chunking_from_flat_sources(
        leafs_sources: &Vec<&Vec<F, A>, B>,
        elements_to_take_per_leaf: usize,
        cap_size: usize,
        worker: &Worker,
    ) -> Self {
        debug_assert!(cap_size > 0);
        debug_assert!(cap_size.is_power_of_two());
        debug_assert!(elements_to_take_per_leaf.is_power_of_two());

        let now = std::time::Instant::now();

        let num_sources = leafs_sources.len();
        let poly_size = leafs_sources[0].len();
        assert!(poly_size % elements_to_take_per_leaf == 0);
        let tree_size = poly_size / elements_to_take_per_leaf;

        debug_assert!(tree_size.is_power_of_two());
        let tree_depth = tree_size.trailing_zeros();
        let layers_to_skip = cap_size.trailing_zeros();

        assert!(
            tree_size >= cap_size,
            "trying to make tree of size {}, while requested cap size is {}",
            tree_size,
            cap_size
        );

        // simplest job ever - compute by layers with parallelism
        // To prevent to complex parallelism we will work over each individual coset

        let mut leaf_hashes = Vec::with_capacity_in(tree_size, A::default());

        worker.scope(tree_size, |scope, dst_chunk_size| {
            let src_chunk_size = dst_chunk_size * elements_to_take_per_leaf;
            for (dst_idx, dst) in leaf_hashes.spare_capacity_mut()[..tree_size]
                .chunks_mut(dst_chunk_size)
                .enumerate()
            {
                scope.spawn(move |_| {
                    let mut sources = Vec::with_capacity(num_sources);
                    let start = dst_idx * src_chunk_size;
                    let mut end = start + src_chunk_size;
                    if end > poly_size {
                        end = poly_size;
                    }
                    for src in leafs_sources.iter() {
                        sources.push(&src[start..end]);
                    }

                    let mut buffer = Vec::with_capacity(num_sources * elements_to_take_per_leaf);

                    let mut start = 0;
                    for dst in dst.iter_mut() {
                        buffer.clear();
                        let end = start + elements_to_take_per_leaf;
                        for src in sources.iter() {
                            buffer.extend_from_slice(&src[start..end]);
                        }
                        dst.write(H::hash_into_leaf(&buffer));

                        start = end;
                    }
                })
            }
        });

        unsafe { leaf_hashes.set_len(tree_size) };

        log!(
            "Merkle tree of size 2^{} leaf hashes taken {:?}",
            tree_size.trailing_zeros(),
            now.elapsed()
        );

        let num_layers_to_construct = tree_depth - layers_to_skip;

        Self::continue_from_leaf_hashes(leaf_hashes, num_layers_to_construct, cap_size, worker)
    }

    fn continue_from_leaf_hashes(
        leaf_hashes: Vec<H::Output, A>,
        num_layers_to_construct: u32,
        cap_size: usize,
        worker: &Worker,
    ) -> Self {
        if num_layers_to_construct == 0 {
            assert_eq!(cap_size, leaf_hashes.len());
            return Self {
                cap_size,
                leaf_hashes,
                node_hashes_enumerated_from_leafs: Vec::new_in(B::default()),
            };
        }

        let now = std::time::Instant::now();
        assert!(num_layers_to_construct > 0);

        let mut previous = &leaf_hashes[..];
        let mut node_hashes_enumerated_from_leafs =
            Vec::with_capacity_in(num_layers_to_construct as usize, B::default());
        for _ in 0..num_layers_to_construct {
            let next_layer_len = previous.len() / 2;
            debug_assert!(next_layer_len > 0);
            debug_assert!(next_layer_len.is_power_of_two());
            let mut new_layer_node_hashes: Vec<H::Output, A> =
                Vec::with_capacity_in(next_layer_len, A::default());

            worker.scope(next_layer_len, |scope, chunk_size| {
                for (dst, src) in new_layer_node_hashes.spare_capacity_mut()[..next_layer_len]
                    .chunks_mut(chunk_size)
                    .zip(previous.chunks(chunk_size * 2))
                {
                    scope.spawn(move |_| {
                        for (dst, src) in dst.iter_mut().zip(src.array_chunks::<2>()) {
                            let [left, right] = src;
                            dst.write(H::hash_into_node(left, right, 0));
                        }
                    });
                }
            });

            unsafe { new_layer_node_hashes.set_len(next_layer_len) };

            node_hashes_enumerated_from_leafs.push(new_layer_node_hashes);
            previous = node_hashes_enumerated_from_leafs.last().unwrap();
        }

        debug_assert_eq!(previous.len(), cap_size);

        log!(
            "Nodes construction of size 2^{} taken {:?}",
            leaf_hashes.len().trailing_zeros(),
            now.elapsed()
        );

        Self {
            cap_size,
            leaf_hashes,
            node_hashes_enumerated_from_leafs,
        }
    }

    pub fn get_cap(&self) -> Vec<H::Output, A> {
        let mut output = if let Some(cap) = self.node_hashes_enumerated_from_leafs.last().cloned() {
            cap
        } else {
            self.leaf_hashes.clone()
        };
        H::batch_normalize_outputs(&mut output);

        output
    }

    pub fn get_proof<C: GoodAllocator>(&self, idx: usize) -> (H::Output, Vec<H::Output, C>) {
        let depth = self.node_hashes_enumerated_from_leafs.len(); // we do not need the element of the cap
        let mut result = Vec::with_capacity_in(depth, C::default());
        let mut idx = idx;
        let this_el_leaf_hash = self.leaf_hashes[idx];
        for i in 0..depth {
            let pair_idx = idx ^ 1;
            let proof_element = if i == 0 {
                self.leaf_hashes[pair_idx]
            } else {
                self.node_hashes_enumerated_from_leafs[i - 1][pair_idx]
            };

            result.push(proof_element);
            idx >>= 1;
        }

        (this_el_leaf_hash, result)
    }

    pub fn verify_proof_over_cap(
        proof: &[H::Output],
        cap: &[H::Output],
        leaf_hash: H::Output,
        idx: usize,
    ) -> bool {
        let mut idx = idx;
        let mut current = leaf_hash;
        for proof_el in proof.iter() {
            if idx & 1 == 0 {
                current = H::hash_into_node(&current, proof_el, 0);
            } else {
                current = H::hash_into_node(proof_el, &current, 0);
            }

            idx >>= 1;
        }

        let cap_el = &cap[idx];
        H::normalize_output(&mut current);

        cap_el == &current
    }
}
