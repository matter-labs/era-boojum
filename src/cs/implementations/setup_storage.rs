use super::*;

use crate::cs::implementations::polynomial::*;
use crate::cs::traits::GoodAllocator;

use super::utils::*;
use crate::cs::implementations::polynomial_storage::SetupStorage;
use std::sync::Arc;

// here we want trivial context bound to use equalities
impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > SetupStorage<F, P, A, B>
{
    pub fn from_base_trace(
        copy_permutation_columns: Vec<Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
        constant_columns: Vec<Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
        lookup_tables_columns: Vec<Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
        table_ids_column_idxes: Vec<usize>,
        lde_degree: usize,
        worker: &Worker,
        ctx: &mut P::Context,
    ) -> Self {
        assert!(lde_degree.is_power_of_two());
        assert!(lde_degree > 1);

        let poly_size = copy_permutation_columns[0].domain_size();

        let inverse_twiddles = P::precompute_inverse_twiddles_for_fft::<A>(poly_size, worker, ctx);
        let forward_twiddles = P::precompute_forward_twiddles_for_fft::<A>(poly_size, worker, ctx);

        let copy_permutation_polys = transform_from_arcs_to_lde_ext(
            copy_permutation_columns,
            lde_degree,
            &inverse_twiddles,
            &forward_twiddles,
            worker,
            ctx,
        );

        let constant_columns = transform_from_arcs_to_lde_ext(
            constant_columns,
            lde_degree,
            &inverse_twiddles,
            &forward_twiddles,
            worker,
            ctx,
        );

        let lookup_tables_columns = transform_from_arcs_to_lde_ext(
            lookup_tables_columns,
            lde_degree,
            &inverse_twiddles,
            &forward_twiddles,
            worker,
            ctx,
        );

        SetupStorage {
            copy_permutation_polys,
            constant_columns,
            lookup_tables_columns,
            table_ids_column_idxes,
            used_lde_degree: lde_degree,
        }
    }
}
