use super::*;

use super::polynomial_storage::{SecondStageProductsStorage, WitnessStorage};
use crate::cs::implementations::polynomial::*;
use crate::cs::traits::GoodAllocator;

use super::utils::*;
use std::sync::Arc;

// here we want trivial context bound to use equalities
impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > WitnessStorage<F, P, A, B>
{
    pub fn from_base_trace(
        variables: Vec<Arc<Polynomial<F, LagrangeForm, A>>, B>,
        witnesses: Vec<Arc<Polynomial<F, LagrangeForm, A>>, B>,
        lookup_multiplicities: Vec<Arc<Polynomial<F, LagrangeForm, A>>, B>,
        lde_degree: usize,
        worker: &Worker,
        ctx: &mut P::Context,
    ) -> Self {
        assert!(lde_degree.is_power_of_two());
        assert!(lde_degree > 1);

        let poly_size = variables[0].domain_size();

        let inverse_twiddles = P::precompute_inverse_twiddles_for_fft::<A>(poly_size, worker, ctx);
        let forward_twiddles = P::precompute_forward_twiddles_for_fft::<A>(poly_size, worker, ctx);

        let variables_columns = transform_from_arcs_to_lde(
            variables,
            lde_degree,
            &inverse_twiddles,
            &forward_twiddles,
            worker,
            ctx,
        );

        let witness_columns = transform_from_arcs_to_lde(
            witnesses,
            lde_degree,
            &inverse_twiddles,
            &forward_twiddles,
            worker,
            ctx,
        );

        let lookup_multiplicities_polys = transform_from_arcs_to_lde(
            lookup_multiplicities,
            lde_degree,
            &inverse_twiddles,
            &forward_twiddles,
            worker,
            ctx,
        );

        WitnessStorage {
            variables_columns,
            witness_columns,
            lookup_multiplicities_polys,
        }
    }

    pub fn from_base_trace_ext(
        variables: Vec<Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
        witnesses: Vec<Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
        lookup_multiplicities: Vec<Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
        lde_degree: usize,
        worker: &Worker,
        ctx: &mut P::Context,
    ) -> Self {
        assert!(lde_degree.is_power_of_two());
        assert!(lde_degree > 1);

        let poly_size = variables[0].domain_size();

        let inverse_twiddles = P::precompute_inverse_twiddles_for_fft::<A>(poly_size, worker, ctx);
        let forward_twiddles = P::precompute_forward_twiddles_for_fft::<A>(poly_size, worker, ctx);

        let variables_columns = transform_from_arcs_to_lde_ext(
            variables,
            lde_degree,
            &inverse_twiddles,
            &forward_twiddles,
            worker,
            ctx,
        );

        let witness_columns = transform_from_arcs_to_lde_ext(
            witnesses,
            lde_degree,
            &inverse_twiddles,
            &forward_twiddles,
            worker,
            ctx,
        );

        let lookup_multiplicities_polys = transform_from_arcs_to_lde_ext(
            lookup_multiplicities,
            lde_degree,
            &inverse_twiddles,
            &forward_twiddles,
            worker,
            ctx,
        );

        WitnessStorage {
            variables_columns,
            witness_columns,
            lookup_multiplicities_polys,
        }
    }
}

// here we want trivial context bound to use equalities
impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > SecondStageProductsStorage<F, P, A, B>
{
    pub fn from_base_trace_ext(
        z_poly: [Arc<GenericPolynomial<F, LagrangeForm, P, A>>; 2],
        intermediates: Vec<[Arc<GenericPolynomial<F, LagrangeForm, P, A>>; 2], B>,
        lookup_witness_encoding_polys: Vec<[Arc<GenericPolynomial<F, LagrangeForm, P, A>>; 2], B>,
        lookup_multiplicities_encoding_polys: Vec<
            [Arc<GenericPolynomial<F, LagrangeForm, P, A>>; 2],
            B,
        >,
        lde_degree: usize,
        worker: &Worker,
        ctx: &mut P::Context,
    ) -> Self {
        assert!(lde_degree.is_power_of_two());
        assert!(lde_degree > 1);

        let poly_size = z_poly[0].domain_size();

        let inverse_twiddles = P::precompute_inverse_twiddles_for_fft::<A>(poly_size, worker, ctx);
        let forward_twiddles = P::precompute_forward_twiddles_for_fft::<A>(poly_size, worker, ctx);

        let mut z_polys = Vec::with_capacity_in(2, B::default());
        z_polys.extend(z_poly);

        let z_polys = transform_from_arcs_to_lde_ext(
            z_polys,
            lde_degree,
            &inverse_twiddles,
            &forward_twiddles,
            worker,
            ctx,
        );

        let num_intermediate_polys = intermediates.len();
        let mut intermediate_polys =
            Vec::with_capacity_in(num_intermediate_polys * 2, B::default());
        intermediate_polys.extend(intermediates.into_iter().flatten());
        let intermediate_polys_flattened = transform_from_arcs_to_lde_ext(
            intermediate_polys,
            lde_degree,
            &inverse_twiddles,
            &forward_twiddles,
            worker,
            ctx,
        );

        let num_lookup_witness_encoding_polys = lookup_witness_encoding_polys.len();
        let mut lookup_witness_encoding =
            Vec::with_capacity_in(num_lookup_witness_encoding_polys * 2, B::default());
        lookup_witness_encoding.extend(lookup_witness_encoding_polys.into_iter().flatten());
        let lookup_witness_encoding_polys_flattened = transform_from_arcs_to_lde_ext(
            lookup_witness_encoding,
            lde_degree,
            &inverse_twiddles,
            &forward_twiddles,
            worker,
            ctx,
        );

        let num_lookup_multiplicities_encoding_polys = lookup_multiplicities_encoding_polys.len();
        let mut lookup_multiplicities_encoding =
            Vec::with_capacity_in(num_lookup_multiplicities_encoding_polys * 2, B::default());
        lookup_multiplicities_encoding
            .extend(lookup_multiplicities_encoding_polys.into_iter().flatten());
        let lookup_multiplicities_encoding_polys_flattened = transform_from_arcs_to_lde_ext(
            lookup_multiplicities_encoding,
            lde_degree,
            &inverse_twiddles,
            &forward_twiddles,
            worker,
            ctx,
        );

        let z_poly = z_polys.into_iter().array_chunks::<2>().next().unwrap();
        let mut intermediate_polys =
            Vec::with_capacity_in(num_intermediate_polys * 2, B::default());
        intermediate_polys_flattened
            .into_iter()
            .array_chunks::<2>()
            .collect_into(&mut intermediate_polys);

        let mut lookup_witness_encoding_polys =
            Vec::with_capacity_in(num_lookup_witness_encoding_polys * 2, B::default());
        lookup_witness_encoding_polys_flattened
            .into_iter()
            .array_chunks::<2>()
            .collect_into(&mut lookup_witness_encoding_polys);

        let mut lookup_multiplicities_encoding_polys =
            Vec::with_capacity_in(num_lookup_multiplicities_encoding_polys * 2, B::default());
        lookup_multiplicities_encoding_polys_flattened
            .into_iter()
            .array_chunks::<2>()
            .collect_into(&mut lookup_multiplicities_encoding_polys);

        SecondStageProductsStorage {
            z_poly,
            intermediate_polys,
            lookup_witness_encoding_polys,
            lookup_multiplicities_encoding_polys,
        }
    }
}
