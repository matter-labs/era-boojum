use super::{
    polynomial::{lde::ArcGenericLdeStorage, GenericPolynomial, LagrangeForm},
    polynomial_storage::{SecondStageProductsStorage, SetupStorage, WitnessStorage},
    *,
};
use crate::cs::implementations::utils::*;
use crate::utils::*;
use crate::{
    cs::implementations::polynomial::lde::GenericLdeStorage,
    field::traits::field_like::mul_assign_vectorized_in_extension,
};
use crate::{cs::traits::GoodAllocator, field::PrimeField};

pub fn num_intermediate_partial_product_relations(
    num_copys_under_copy_permutation: usize,
    quotient_degree: usize,
) -> usize {
    if num_copys_under_copy_permutation <= quotient_degree {
        return 0;
    }
    let mut result = num_copys_under_copy_permutation / quotient_degree;
    if num_copys_under_copy_permutation % quotient_degree != 0 {
        result += 1;
    }
    result -= 1;

    result
}

pub(crate) fn pointwise_rational<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    copy_permutation_columns: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    precomputed_x_poly: std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>,
    sigma_polys: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    non_residues: Vec<F, B>,
    beta: F,
    gamma: F,
    basis: &mut GenericPolynomial<F, LagrangeForm, P, A>,
    worker: &Worker,
    ctx: &mut P::Context,
) {
    debug_assert!(precomputed_x_poly.storage.as_ptr().addr() % std::mem::align_of::<P>() == 0);
    assert!(copy_permutation_columns.len() > 0);
    assert_eq!(copy_permutation_columns.len(), sigma_polys.len());
    assert_eq!(copy_permutation_columns.len(), non_residues.len());
    let typical_size = copy_permutation_columns[0].storage.len();
    assert_eq!(basis.storage.len(), typical_size);

    let beta = P::constant(beta, ctx);
    let gamma = P::constant(gamma, ctx);

    for ((witness_poly, sigma_poly), non_residue) in copy_permutation_columns
        .iter()
        .zip(sigma_polys.iter())
        .zip(non_residues.iter())
    {
        let non_residue = P::constant(*non_residue, ctx);
        worker.scope(typical_size, |scope, chunk_size| {
            for (((w, sigma), x_poly), dst) in (witness_poly.storage.chunks(chunk_size))
                .zip(sigma_poly.storage.chunks(chunk_size))
                .zip(precomputed_x_poly.storage.chunks(chunk_size))
                .zip(basis.storage.chunks_mut(chunk_size))
            {
                let mut ctx = *ctx;
                scope.spawn(move |_| {
                    let mut buffer_den = Vec::with_capacity_in(chunk_size, A::default());
                    let buffer_for_inverses = Vec::with_capacity_in(chunk_size, A::default());
                    let mut buffer_for_inverses = P::vec_into_base_vec(buffer_for_inverses);

                    for (((w, sigma), x_poly), dst) in w
                        .iter()
                        .zip(sigma.iter())
                        .zip(x_poly.iter())
                        .zip(dst.iter_mut())
                    {
                        // numerator is w + beta * non_res * x + gamma
                        let mut numerator = beta;
                        numerator
                            .mul_assign(&non_residue, &mut ctx)
                            .mul_assign(x_poly, &mut ctx);
                        numerator
                            .add_assign(w, &mut ctx)
                            .add_assign(&gamma, &mut ctx);
                        dst.mul_assign(&numerator, &mut ctx);

                        // denominator is w + beta * sigma(x) + gamma
                        let mut denominator = beta;
                        denominator.mul_assign(sigma, &mut ctx);
                        denominator
                            .add_assign(w, &mut ctx)
                            .add_assign(&gamma, &mut ctx);

                        buffer_den.push(denominator);
                    }

                    let buffer_den = P::slice_into_base_slice(&buffer_den[..]);
                    batch_inverse(buffer_den, &mut buffer_for_inverses);
                    let buffer_for_inverses = P::vec_from_base_vec(buffer_for_inverses);
                    assert_eq!(dst.len(), buffer_for_inverses.len());

                    for (dst, src) in dst.iter_mut().zip(buffer_for_inverses.iter()) {
                        dst.mul_assign(src, &mut ctx);
                    }
                });
            }
        });
    }
}

pub(crate) fn pointwise_rational_in_extension<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    EXT: FieldExtension<2, BaseField = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    copy_permutation_columns: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    precomputed_x_poly: std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>,
    sigma_polys: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    non_residues: Vec<F, B>,
    beta: ExtensionField<F, 2, EXT>,
    gamma: ExtensionField<F, 2, EXT>,
    basis_c0: &mut GenericPolynomial<F, LagrangeForm, P, A>,
    basis_c1: &mut GenericPolynomial<F, LagrangeForm, P, A>,
    worker: &Worker,
    ctx: &mut P::Context,
) {
    debug_assert!(precomputed_x_poly.storage.as_ptr().addr() % std::mem::align_of::<P>() == 0);
    assert!(copy_permutation_columns.len() > 0);
    assert_eq!(copy_permutation_columns.len(), sigma_polys.len());
    assert_eq!(copy_permutation_columns.len(), non_residues.len());
    let typical_size = copy_permutation_columns[0].storage.len();
    assert_eq!(basis_c0.storage.len(), typical_size);
    assert_eq!(basis_c1.storage.len(), typical_size);

    let beta_c0 = P::constant(beta.coeffs[0], ctx);
    let beta_c1 = P::constant(beta.coeffs[1], ctx);
    let gamma_c0 = P::constant(gamma.coeffs[0], ctx);
    let gamma_c1 = P::constant(gamma.coeffs[1], ctx);

    for ((witness_poly, sigma_poly), non_residue) in copy_permutation_columns
        .iter()
        .zip(sigma_polys.iter())
        .zip(non_residues.iter())
    {
        let non_residue = P::constant(*non_residue, ctx);
        worker.scope(typical_size, |scope, chunk_size| {
            for ((((w, sigma), x_poly), dst_c0), dst_c1) in
                (witness_poly.storage.chunks(chunk_size))
                    .zip(sigma_poly.storage.chunks(chunk_size))
                    .zip(precomputed_x_poly.storage.chunks(chunk_size))
                    .zip(basis_c0.storage.chunks_mut(chunk_size))
                    .zip(basis_c1.storage.chunks_mut(chunk_size))
            {
                let mut ctx = *ctx;
                scope.spawn(move |_| {
                    let mut buffer_den =
                        Vec::with_capacity_in(chunk_size * P::SIZE_FACTOR, A::default());
                    let mut buffer_for_inverses =
                        Vec::with_capacity_in(chunk_size * P::SIZE_FACTOR, A::default());

                    for ((((w, sigma), x_poly), dst_c0), dst_c1) in w
                        .iter()
                        .zip(sigma.iter())
                        .zip(x_poly.iter())
                        .zip(dst_c0.iter_mut())
                        .zip(dst_c1.iter_mut())
                    {
                        // numerator is w + beta * non_res * x + gamma

                        // w, non_res and x are in base field,
                        // so we split the evaluation
                        let mut numerator_common = non_residue;
                        numerator_common.mul_assign(x_poly, &mut ctx);

                        // c0 and c1 parts
                        let mut numerator_c0 = numerator_common;
                        numerator_c0.mul_assign(&beta_c0, &mut ctx);
                        numerator_c0
                            .add_assign(w, &mut ctx)
                            .add_assign(&gamma_c0, &mut ctx);

                        let mut numerator_c1 = numerator_common;
                        numerator_c1.mul_assign(&beta_c1, &mut ctx);
                        numerator_c1.add_assign(&gamma_c1, &mut ctx);

                        mul_assign_vectorized_in_extension::<F, P, EXT>(
                            dst_c0,
                            dst_c1,
                            &numerator_c0,
                            &numerator_c1,
                            &mut ctx,
                        );

                        // denominator is w + beta * sigma(x) + gamma
                        // we do the same

                        // c0 and c1 parts
                        let mut denominator_c0 = *sigma;
                        denominator_c0.mul_assign(&beta_c0, &mut ctx);
                        denominator_c0
                            .add_assign(w, &mut ctx)
                            .add_assign(&gamma_c0, &mut ctx);

                        let mut denominator_c1 = *sigma;
                        denominator_c1.mul_assign(&beta_c1, &mut ctx);
                        denominator_c1.add_assign(&gamma_c1, &mut ctx);

                        for (c0, c1) in denominator_c0
                            .as_base_elements()
                            .iter()
                            .zip(denominator_c1.as_base_elements().iter())
                        {
                            let denominator =
                                ExtensionField::<F, 2, EXT>::from_coeff_in_base([*c0, *c1]);
                            buffer_den.push(denominator);
                        }
                    }

                    batch_inverse(&buffer_den, &mut buffer_for_inverses);
                    assert_eq!(dst_c0.len() * P::SIZE_FACTOR, buffer_for_inverses.len());
                    assert_eq!(dst_c1.len() * P::SIZE_FACTOR, buffer_for_inverses.len());

                    // mul as scalars
                    let dst_c0_base = P::slice_into_base_slice_mut(dst_c0);
                    let dst_c1_base = P::slice_into_base_slice_mut(dst_c1);

                    for ((dst_c0, dst_c1), src) in dst_c0_base
                        .iter_mut()
                        .zip(dst_c1_base.iter_mut())
                        .zip(buffer_for_inverses.drain(..))
                    {
                        let mut dst =
                            ExtensionField::<F, 2, EXT>::from_coeff_in_base([*dst_c0, *dst_c1]);
                        crate::field::Field::mul_assign(&mut dst, &src);
                        let [c0, c1] = dst.into_coeffs_in_base();
                        *dst_c0 = c0;
                        *dst_c1 = c1;
                    }
                });
            }
        });
    }
}

pub(crate) fn pointwise_product<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
>(
    inputs: &[GenericPolynomial<F, LagrangeForm, P, A>],
    worker: &Worker,
    ctx: &mut P::Context,
) -> GenericPolynomial<F, LagrangeForm, P, A> {
    if inputs.len() == 1 {
        return inputs[0].clone();
    }

    let mut result = inputs[0].clone();

    pointwise_product_into(&inputs[1..], &mut result, worker, ctx);

    result
}

pub(crate) fn pointwise_product_into<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
>(
    inputs: &[GenericPolynomial<F, LagrangeForm, P, A>],
    into: &mut GenericPolynomial<F, LagrangeForm, P, A>,
    worker: &Worker,
    ctx: &mut P::Context,
) {
    let typical_size = into.storage.len(); // we need raw length in counts of P

    for source in inputs.iter() {
        worker.scope(typical_size, |scope, chunk_size| {
            for (dst, src) in
                (into.storage.chunks_mut(chunk_size)).zip(source.storage.chunks(chunk_size))
            {
                let mut ctx = *ctx;
                scope.spawn(move |_| {
                    for (dst, src) in dst.iter_mut().zip(src.iter()) {
                        dst.mul_assign(src, &mut ctx);
                    }
                });
            }
        });
    }
}

pub(crate) fn pointwise_product_in_extension<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    EXT: FieldExtension<2, BaseField = F>,
    A: GoodAllocator,
>(
    inputs: &[[GenericPolynomial<F, LagrangeForm, P, A>; 2]],
    worker: &Worker,
    ctx: &mut P::Context,
) -> [GenericPolynomial<F, LagrangeForm, P, A>; 2] {
    if inputs.len() == 1 {
        return inputs[0].clone();
    }

    let [mut result_c0, mut result_c1] = inputs[0].clone();

    pointwise_product_in_extension_into::<F, P, EXT, A>(
        &inputs[1..],
        &mut result_c0,
        &mut result_c1,
        worker,
        ctx,
    );

    [result_c0, result_c1]
}

pub(crate) fn pointwise_product_in_extension_into<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    EXT: FieldExtension<2, BaseField = F>,
    A: GoodAllocator,
>(
    inputs: &[[GenericPolynomial<F, LagrangeForm, P, A>; 2]],
    into_c0: &mut GenericPolynomial<F, LagrangeForm, P, A>,
    into_c1: &mut GenericPolynomial<F, LagrangeForm, P, A>,
    worker: &Worker,
    ctx: &mut P::Context,
) {
    let typical_size = into_c0.storage.len(); // we need raw length in counts of P

    for source in inputs.iter() {
        let [src_c0, src_c1] = source;
        worker.scope(typical_size, |scope, chunk_size| {
            for (((dst_c0, dst_c1), src_c0), src_c1) in into_c0
                .storage
                .chunks_mut(chunk_size)
                .zip(into_c1.storage.chunks_mut(chunk_size))
                .zip(src_c0.storage.chunks(chunk_size))
                .zip(src_c1.storage.chunks(chunk_size))
            {
                let mut ctx = *ctx;
                scope.spawn(move |_| {
                    for (((dst_c0, dst_c1), src_c0), src_c1) in dst_c0
                        .iter_mut()
                        .zip(dst_c1.iter_mut())
                        .zip(src_c0.iter())
                        .zip(src_c1.iter())
                    {
                        mul_assign_vectorized_in_extension::<F, P, EXT>(
                            dst_c0, dst_c1, src_c0, src_c1, &mut ctx,
                        );
                    }
                });
            }
        });
    }
}

pub(crate) fn shifted_grand_product<F: PrimeField, A: GoodAllocator>(
    input: Vec<F, A>,
    worker: &Worker,
) -> Vec<F, A> {
    let mut input = input;
    let work_size = input.len();
    assert!(work_size.is_power_of_two());
    let chunk_size = worker.get_chunk_size(work_size);
    let num_chunks = Worker::compute_num_chunks(work_size, chunk_size);
    let mut partial_subproducts = vec![F::ZERO; num_chunks];

    worker.scope(work_size, |scope, chunk_size| {
        for (chunk, acc) in input
            .chunks_mut(chunk_size)
            .zip(partial_subproducts.iter_mut())
        {
            scope.spawn(move |_| {
                let mut product = F::ONE;
                for dst in chunk.iter_mut() {
                    let tmp = *dst;
                    *dst = product;
                    product.mul_assign(&tmp);
                }

                *acc = product;
            });
        }
    });

    // multiply partial products
    let mut current = F::ONE;
    for el in partial_subproducts.iter_mut() {
        let tmp = *el;
        el.mul_assign(&current);
        current.mul_assign(&tmp);
    }

    assert_eq!(current, F::ONE);

    // second pass
    worker.scope(work_size, |scope, chunk_size| {
        // no multiplication for 1st chunk
        for (chunk, acc) in input
            .chunks_mut(chunk_size)
            .skip(1)
            .zip(partial_subproducts.iter())
        {
            scope.spawn(move |_| {
                for dst in chunk.iter_mut() {
                    dst.mul_assign(acc);
                }
            });
        }
    });

    input
}

pub(crate) fn shifted_grand_product_in_extension<
    F: PrimeField,
    EXT: FieldExtension<2, BaseField = F>,
    A: GoodAllocator,
>(
    input_c0: Vec<F, A>,
    input_c1: Vec<F, A>,
    worker: &Worker,
) -> [Vec<F, A>; 2] {
    let mut input_c0 = input_c0;
    let mut input_c1 = input_c1;
    let work_size = input_c0.len();
    assert!(work_size.is_power_of_two());
    let chunk_size = worker.get_chunk_size(work_size);
    let num_chunks = Worker::compute_num_chunks(work_size, chunk_size);

    let mut partial_subproducts = {
        use crate::field::traits::field::Field;
        vec![ExtensionField::<F, 2, EXT>::ZERO; num_chunks]
    };

    worker.scope(work_size, |scope, chunk_size| {
        for ((chunk_c0, chunk_c1), acc) in input_c0
            .chunks_mut(chunk_size)
            .zip(input_c1.chunks_mut(chunk_size))
            .zip(partial_subproducts.iter_mut())
        {
            scope.spawn(move |_| {
                let mut product = {
                    use crate::field::Field;
                    ExtensionField::<F, 2, EXT>::ONE
                };
                for (dst_c0, dst_c1) in chunk_c0.iter_mut().zip(chunk_c1.iter_mut()) {
                    let tmp = ExtensionField::<F, 2, EXT>::from_coeff_in_base([*dst_c0, *dst_c1]);

                    *dst_c0 = product.coeffs[0];
                    *dst_c1 = product.coeffs[1];

                    crate::field::Field::mul_assign(&mut product, &tmp);
                }

                *acc = product;
            });
        }
    });

    // multiply partial products
    let one = {
        use crate::field::Field;
        ExtensionField::<F, 2, EXT>::ONE
    };
    let mut current = one;

    for el in partial_subproducts.iter_mut() {
        let tmp = *el;

        crate::field::Field::mul_assign(el, &current);
        crate::field::Field::mul_assign(&mut current, &tmp);
    }

    assert_eq!(current, one);

    // second pass
    worker.scope(work_size, |scope, chunk_size| {
        // no multiplication for 1st chunk
        for ((chunk_c0, chunk_c1), acc) in input_c0
            .chunks_mut(chunk_size)
            .skip(1)
            .zip(input_c1.chunks_mut(chunk_size).skip(1))
            .zip(partial_subproducts.iter())
        {
            scope.spawn(move |_| {
                for (dst_c0, dst_c1) in chunk_c0.iter_mut().zip(chunk_c1.iter_mut()) {
                    let mut dst =
                        ExtensionField::<F, 2, EXT>::from_coeff_in_base([*dst_c0, *dst_c1]);
                    crate::field::Field::mul_assign(&mut dst, acc);
                    let [c0, c1] = dst.into_coeffs_in_base();
                    *dst_c0 = c0;
                    *dst_c1 = c1;
                }
            });
        }
    });

    [input_c0, input_c1]
}

pub fn non_residues_for_copy_permutation<F: PrimeField, B: GoodAllocator>(
    domain_size: usize,
    num_columns: usize,
) -> Vec<F, B> {
    assert!(num_columns > 0);
    let mut non_residues = Vec::with_capacity_in(num_columns, B::default());
    non_residues.push(F::ONE);
    non_residues.extend(make_non_residues::<F>(num_columns - 1, domain_size));

    non_residues
}

// Evaluated over main domain (no coset, no LDE)
pub(crate) fn compute_partial_products<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    all_copy_permutation_columns: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    precomputed_x_poly: std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>,
    all_sigma_polys: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    betas: Vec<F, B>,
    gammas: Vec<F, B>,
    worker: &Worker,
    max_degree: usize,
    ctx: &mut P::Context,
) -> Vec<
    (
        GenericPolynomial<F, LagrangeForm, P, A>,         // Z(x)
        Vec<GenericPolynomial<F, LagrangeForm, P, A>, B>, // partial products
    ),
    B,
> {
    assert!(all_copy_permutation_columns.len() > 0);
    assert_eq!(all_copy_permutation_columns.len(), all_sigma_polys.len());
    assert!(max_degree >= 1);
    assert!(max_degree.is_power_of_two());
    assert_eq!(betas.len(), gammas.len());

    let domain_size = precomputed_x_poly.domain_size();
    let num_polys = all_copy_permutation_columns.len();
    let non_residues = non_residues_for_copy_permutation::<F, B>(domain_size, num_polys);

    // we repeat the argument over betas and gammas sets

    let mut subsets = Vec::with_capacity_in(betas.len(), B::default());

    for (beta, gamma) in betas.into_iter().zip(gammas.into_iter()) {
        // even though to compute z(x) we need to make full product starting from the fact that Z(1) == 1, and then making
        // Z(omega), Z(omega^1), etc, we can transpose into parallel computations over larger sizes and keep some partial products
        // along the way, and then make z(x) and intermediate values using it

        let mut partial_elementwise_products = Vec::new_in(B::default());

        for ((copy_permutation_columns_chunk, sigma_polys_chunk), non_residues_chunk) in
            all_copy_permutation_columns
                .chunks(max_degree)
                .zip(all_sigma_polys.chunks(max_degree))
                .zip(non_residues.chunks(max_degree))
        {
            let copy_permutation_columns_chunk =
                copy_permutation_columns_chunk.to_vec_in(B::default());
            let sigma_polys_chunk = sigma_polys_chunk.to_vec_in(B::default());
            let non_residues_chunk = non_residues_chunk.to_vec_in(B::default());

            let basis =
                initialize_in_with_alignment_of::<F, P, _>(F::ONE, domain_size, A::default());
            let basis = P::vec_from_base_vec(basis);
            let mut partial_elementwise_product = GenericPolynomial::from_storage(basis);

            pointwise_rational(
                copy_permutation_columns_chunk.clone(),
                precomputed_x_poly.clone(),
                sigma_polys_chunk.clone(),
                non_residues_chunk.clone(),
                beta,
                gamma,
                &mut partial_elementwise_product,
                worker,
                ctx,
            );

            partial_elementwise_products.push(partial_elementwise_product);
        }

        let almost_z_poly =
            pointwise_product::<F, P, A>(&partial_elementwise_products, worker, ctx);

        // now we can compute almost z poly, by performing elementwise multiplication
        // that should be completed in base field

        let almost_z_poly = P::vec_into_base_vec(almost_z_poly.into_storage());
        let z_poly = shifted_grand_product(almost_z_poly, worker);
        let z_poly = P::vec_from_base_vec(z_poly);
        let z_poly = GenericPolynomial::from_storage(z_poly);

        // and now we need to re-materialize partial elementwise products like
        // partial_0 = z(x) * partial_elementwise_products[0]
        // partial_1 = partial_0 * partial_elementwise_products[1]
        // ...
        // and by our construction we easily can see that
        // z(x * omega) = partial_{n-1} * partial_elementwise_products[n]

        if partial_elementwise_products.len() == 1 {
            // there are no intermediate products in practice, we can go directly from z(x) to z(x * omega)
            subsets.push((z_poly, Vec::new_in(B::default())))
        } else {
            // we have to compute intermediates
            let mut previous = [z_poly.clone()];
            let mut full_elementwise_products = Vec::new_in(B::default());

            let _ = partial_elementwise_products.pop().unwrap();

            // we have to apply pointwise products on top of Z(x)

            for el in partial_elementwise_products.into_iter() {
                let mut el = el;
                pointwise_product_into(&previous, &mut el, worker, ctx);

                // we have new pointwise in el, and untouched previous, so we can reuse the storage

                Clone::clone_from(&mut previous[0], &el);
                full_elementwise_products.push(el);
            }

            subsets.push((z_poly, full_elementwise_products))
        }
    }

    subsets
}

use crate::field::ExtensionField;
use crate::field::FieldExtension;

// Evaluated over main domain (no coset, no LDE)
pub(crate) fn compute_partial_products_in_extension<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    EXT: FieldExtension<2, BaseField = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    all_copy_permutation_columns: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    precomputed_x_poly: std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>,
    all_sigma_polys: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    beta: ExtensionField<F, 2, EXT>,
    gamma: ExtensionField<F, 2, EXT>,
    worker: &Worker,
    max_degree: usize,
    ctx: &mut P::Context,
) -> (
    [GenericPolynomial<F, LagrangeForm, P, A>; 2], // Z(x)
    Vec<[GenericPolynomial<F, LagrangeForm, P, A>; 2], B>, // partial products
) {
    assert!(all_copy_permutation_columns.len() > 0);
    assert_eq!(all_copy_permutation_columns.len(), all_sigma_polys.len());
    assert!(max_degree >= 1);
    assert!(max_degree.is_power_of_two());

    profile_fn!(compute_partial_products_in_extension);

    let domain_size = precomputed_x_poly.domain_size();
    let num_polys = all_copy_permutation_columns.len();
    let non_residues = non_residues_for_copy_permutation::<F, B>(domain_size, num_polys);

    // even though to compute z(x) we need to make full product starting from the fact that Z(1) == 1, and then making
    // Z(omega), Z(omega^1), etc, we can transpose into parallel computations over larger sizes and keep some partial products
    // along the way, and then make z(x) and intermediate values using it

    let mut partial_elementwise_products = Vec::new_in(B::default());

    for ((copy_permutation_columns_chunk, sigma_polys_chunk), non_residues_chunk) in
        all_copy_permutation_columns
            .chunks(max_degree)
            .zip(all_sigma_polys.chunks(max_degree))
            .zip(non_residues.chunks(max_degree))
    {
        let copy_permutation_columns_chunk = copy_permutation_columns_chunk.to_vec_in(B::default());
        let sigma_polys_chunk = sigma_polys_chunk.to_vec_in(B::default());
        let non_residues_chunk = non_residues_chunk.to_vec_in(B::default());

        let basis_c0 =
            initialize_in_with_alignment_of::<F, P, _>(F::ONE, domain_size, A::default());
        let basis_c1 =
            initialize_in_with_alignment_of::<F, P, _>(F::ZERO, domain_size, A::default());
        let basis_c0 = P::vec_from_base_vec(basis_c0);
        let basis_c1 = P::vec_from_base_vec(basis_c1);

        let mut partial_elementwise_product_c0 = GenericPolynomial::from_storage(basis_c0);
        let mut partial_elementwise_product_c1 = GenericPolynomial::from_storage(basis_c1);

        pointwise_rational_in_extension(
            copy_permutation_columns_chunk.clone(),
            precomputed_x_poly.clone(),
            sigma_polys_chunk.clone(),
            non_residues_chunk.clone(),
            beta,
            gamma,
            &mut partial_elementwise_product_c0,
            &mut partial_elementwise_product_c1,
            worker,
            ctx,
        );

        partial_elementwise_products.push([
            partial_elementwise_product_c0,
            partial_elementwise_product_c1,
        ]);
    }

    let [almost_z_poly_c0, almost_z_poly_c1] =
        pointwise_product_in_extension::<F, P, EXT, A>(&partial_elementwise_products, worker, ctx);

    // now we can compute almost z poly, by performing elementwise multiplication
    // that should be completed in base field

    let almost_z_poly_c0 = P::vec_into_base_vec(almost_z_poly_c0.into_storage());
    let almost_z_poly_c1 = P::vec_into_base_vec(almost_z_poly_c1.into_storage());
    let [z_poly_c0, z_poly_c1] =
        shifted_grand_product_in_extension::<F, EXT, A>(almost_z_poly_c0, almost_z_poly_c1, worker);
    let z_poly_c0 = P::vec_from_base_vec(z_poly_c0);
    let z_poly_c0 = GenericPolynomial::from_storage(z_poly_c0);

    let z_poly_c1 = P::vec_from_base_vec(z_poly_c1);
    let z_poly_c1 = GenericPolynomial::from_storage(z_poly_c1);

    // and now we need to re-materialize partial elementwise products like
    // partial_0 = z(x) * partial_elementwise_products[0]
    // partial_1 = partial_0 * partial_elementwise_products[1]
    // ...
    // and by our construction we easily can see that
    // z(x * omega) = partial_{n-1} * partial_elementwise_products[n]

    if partial_elementwise_products.len() == 1 {
        // there are no intermediate products in practice, we can go directly from z(x) to z(x * omega)
        ([z_poly_c0, z_poly_c1], partial_elementwise_products)
    } else {
        // we have to compute intermediates
        let mut previous = [[z_poly_c0.clone(), z_poly_c1.clone()]];
        let mut full_elementwise_products = Vec::new_in(B::default());

        let _ = partial_elementwise_products.pop().unwrap();

        // we have to apply pointwise products on top of Z(x)

        for el in partial_elementwise_products.into_iter() {
            let [mut el_c0, mut el_c1] = el;
            pointwise_product_in_extension_into::<F, P, EXT, A>(
                &previous, &mut el_c0, &mut el_c1, worker, ctx,
            );

            // we have new pointwise in el, and untouched previous, so we can reuse the storage

            Clone::clone_from(&mut previous[0][0], &el_c0);
            Clone::clone_from(&mut previous[0][1], &el_c1);
            full_elementwise_products.push([el_c0, el_c1]);
        }

        ([z_poly_c0, z_poly_c1], full_elementwise_products)
    }
}

// pub(crate) fn compute_quotient_terms<
//     F: PrimeField,
//     P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
//     A: GoodAllocator,
//     B: GoodAllocator,
// >(
//     domain_size: usize,
//     degree: usize,
//     witness: &WitnessStorage<F, P, A, B>,
//     grand_products: &SecondStageProductsStorage<F, P, A, B>,
//     setup: &SetupStorage<F, P, A, B>,
//     num_intermediate_products: usize,
//     set_idx: usize,
//     beta: F,
//     gamma: F,
//     alphas: Vec<F>,
//     x_poly: &ArcGenericLdeStorage<F, P, A, B>,
//     dst: &mut ArcGenericLdeStorage<F, P, A, B>,
//     worker: &Worker,
//     ctx: &mut P::Context,
// )  {
//     let mut non_residues = Vec::with_capacity_in(witness.variables_columns.len(), B::default());
//     non_residues_for_copy_permutation::<F, B>(domain_size, witness.variables_columns.len())
//         .into_iter()
//         .map(|el| P::constant(el, ctx))
//         .collect_into(&mut non_residues);
//     // numerator is w + beta * non_res * x + gamma
//     // denominator is w + beta * sigma(x) + gamma

//     // We have

//     // partial_product_{1} = Z(x) * num / denom
//     // partial_product_{i + 1} = partial_product_i * num / denom
//     // Z(x * omega) = partial_product_{last} * num / denom

//     // that are transformed into
//     // (LHS * denom - RHS * num) / Vanishing(x) = poly

//     assert_eq!(alphas.len(), num_intermediate_products + 1);

//     let z_poly_shifted = grand_products
//         .z_polys
//         .iter()
//         .skip(set_idx)
//         .take(1)
//         .map(|el| {
//             let subset = el.subset_for_degree(degree);
//             let subset_len = subset.storage.len();
//             let mut owned_set = Vec::with_capacity_in(subset_len, B::default());
//             worker.scope(subset_len, |scope, chunk_size| {
//                 for (src, dst) in subset
//                     .storage
//                     .chunks(chunk_size)
//                     .zip(owned_set.spare_capacity_mut()[..subset_len].chunks_mut(chunk_size))
//                 {
//                     scope.spawn(|_| {
//                         for (src, dst) in src.iter().zip(dst.iter_mut()) {
//                             let shifted_base = shift_by_omega_assuming_bitreversed::<F, P, A>(
//                                 &src.storage,
//                             );
//                             let as_poly =
//                                 GenericPolynomial::from_storage(shifted_base);
//                             dst.write(as_poly);
//                         }
//                     })
//                 }
//             });

//             unsafe { owned_set.set_len(subset_len) };

//             ArcGenericLdeStorage::from_owned(GenericLdeStorage { storage: owned_set })
//         })
//         .next()
//         .expect("must get z(x * omega)");

//     let lhs = grand_products
//         .intermediate_polys
//         .iter()
//         .skip(num_intermediate_products * set_idx)
//         .take(num_intermediate_products)
//         .map(|el| el.subset_for_degree(degree))
//         .chain([z_poly_shifted].into_iter());

//     let z_poly = grand_products
//         .z_polys
//         .iter()
//         .skip(set_idx)
//         .take(1)
//         .map(|el| el.owned_subset_for_degree(degree))
//         .next()
//         .expect("must get z(x)");

//     if crate::config::DEBUG_SATISFIABLE == true {
//         assert_eq!(
//             P::slice_into_base_slice(&[z_poly.storage[0].storage[0]])[0],
//             F::ONE
//         );
//     }

//     let rhs = [z_poly].into_iter().chain(
//         grand_products
//             .intermediate_polys
//             .iter()
//             .skip(num_intermediate_products * set_idx)
//             .take(num_intermediate_products)
//             .map(|el| el.subset_for_degree(degree)),
//     );

//     let mut columns_chunks = Vec::with_capacity_in(witness.variables_columns.len(), B::default());
//     witness
//         .variables_columns
//         .iter()
//         .map(|el| el.subset_for_degree(degree))
//         .collect_into(&mut columns_chunks);

//     let mut sigmas_chunks = Vec::with_capacity_in(setup.copy_permutation_polys.len(), B::default());
//     setup
//         .copy_permutation_polys
//         .iter()
//         .map(|el| el.subset_for_degree(degree))
//         .collect_into(&mut sigmas_chunks);

//     // lhs * denom - rhs * num == 0, and make it over coset

//     let beta = P::constant(beta, ctx);
//     let gamma = P::constant(gamma, ctx);

//     for (_relation_idx, (((((lhs, rhs), alpha), non_residues), variables), sigmas)) in lhs
//         .zip(rhs)
//         .zip(alphas.into_iter())
//         .zip(non_residues.chunks(degree))
//         .zip(columns_chunks.chunks(degree))
//         .zip(sigmas_chunks.chunks(degree))
//         .enumerate()
//     {
//         let alpha = P::constant(alpha, ctx);

//         assert_eq!(variables.len(), sigmas.len());
//         assert_eq!(variables.len(), non_residues.len());

//         // unfortunatery we have to open code it due to internal iterator
//         let iterators = lhs.compute_chunks_for_num_workers(worker.num_cores);

//         worker.scope(0, |scope, _| {
//             for iterator in iterators.into_iter() {
//                 let mut dst = dst.clone();
//                 let lhs = lhs.clone();
//                 let rhs = rhs.clone();
//                 let x_poly = x_poly.clone();
//                 let mut ctx = *ctx;
//                 scope.spawn(move |_| {
//                     let num_iterations = iterator.num_iterations();
//                     let mut iterator = iterator;
//                     for _ in 0..num_iterations {
//                         let (outer, inner) = iterator.current();

//                         let mut lhs_contribution = lhs.storage[outer].storage[inner];
//                         for (variables, sigma) in variables.iter().zip(sigmas.iter()) {
//                             // denominator is w + beta * sigma(x) + gamma
//                             let mut subres = sigma.storage[outer].storage[inner];
//                             subres.mul_assign(&beta, &mut ctx);
//                             subres.add_assign(&variables.storage[outer].storage[inner], &mut ctx);
//                             subres.add_assign(&gamma, &mut ctx);
//                             lhs_contribution.mul_assign(&subres, &mut ctx);
//                         }

//                         let mut rhs_contribution = rhs.storage[outer].storage[inner];
//                         let x_poly_value = x_poly.storage[outer].storage[inner];
//                         for (non_res, variables) in non_residues.iter().zip(variables.iter()) {
//                             // numerator is w + beta * non_res * x + gamma
//                             let mut subres = x_poly_value;
//                             subres.mul_assign(&non_res, &mut ctx);
//                             subres.mul_assign(&beta, &mut ctx);
//                             subres.add_assign(&variables.storage[outer].storage[inner], &mut ctx);
//                             subres.add_assign(&gamma, &mut ctx);
//                             rhs_contribution.mul_assign(&subres, &mut ctx);
//                         }

//                         let mut contribution = lhs_contribution;
//                         contribution.sub_assign(&rhs_contribution, &mut ctx);
//                         contribution.mul_assign(&alpha, &mut ctx);

//                         if crate::config::DEBUG_SATISFIABLE == true {
//                             if outer == 0 {
//                                 // only on base coset
//                                 let t = [contribution];
//                                 let as_base = P::slice_into_base_slice(&t);
//                                 for el in as_base.iter() {
//                                     if el.is_zero() == false {
//                                         dbg!(_relation_idx);
//                                         dbg!(lhs.storage[outer].storage[inner]);
//                                         dbg!(rhs.storage[outer].storage[inner]);
//                                         dbg!(variables[0].storage[outer].storage[inner]);
//                                         dbg!(variables[1].storage[outer].storage[inner]);
//                                         dbg!(variables[2].storage[outer].storage[inner]);
//                                         dbg!(variables[3].storage[outer].storage[inner]);
//                                         dbg!(sigmas[0].storage[outer].storage[inner]);
//                                         dbg!(sigmas[1].storage[outer].storage[inner]);
//                                         dbg!(sigmas[2].storage[outer].storage[inner]);
//                                         dbg!(sigmas[3].storage[outer].storage[inner]);
//                                     }
//                                     assert_eq!(
//                                         *el,
//                                         F::ZERO,
//                                         "failed at outer = {}, inner = {}",
//                                         outer,
//                                         inner
//                                     );
//                                 }
//                             }
//                         }

//                         unsafe { std::sync::Arc::get_mut_unchecked(&mut dst.storage[outer]) }
//                             .storage[inner]
//                             .add_assign(&contribution, &mut ctx);

//                         iterator.advance();
//                     }
//                 });
//             }
//         });
//     }
// }

pub(crate) fn compute_quotient_terms_in_extension<
    F: PrimeField,
    EXT: FieldExtension<2, BaseField = F>,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    domain_size: usize,
    degree: usize,
    witness: &WitnessStorage<F, P, A, B>,
    grand_products: &SecondStageProductsStorage<F, P, A, B>,
    setup: &SetupStorage<F, P, A, B>,
    num_intermediate_products: usize,
    beta: ExtensionField<F, 2, EXT>,
    gamma: ExtensionField<F, 2, EXT>,
    alphas: Vec<ExtensionField<F, 2, EXT>>,
    x_poly: &ArcGenericLdeStorage<F, P, A, B>,
    dst_c0: &mut ArcGenericLdeStorage<F, P, A, B>,
    dst_c1: &mut ArcGenericLdeStorage<F, P, A, B>,
    worker: &Worker,
    ctx: &mut P::Context,
) {
    let mut non_residues = Vec::with_capacity_in(witness.variables_columns.len(), B::default());
    non_residues_for_copy_permutation::<F, B>(domain_size, witness.variables_columns.len())
        .into_iter()
        .map(|el| P::constant(el, ctx))
        .collect_into(&mut non_residues);
    // numerator is w + beta * non_res * x + gamma
    // denominator is w + beta * sigma(x) + gamma

    // We have

    // partial_product_{1} = Z(x) * num / denom
    // partial_product_{i + 1} = partial_product_i * num / denom
    // Z(x * omega) = partial_product_{last} * num / denom

    // that are transformed into
    // (LHS * denom - RHS * num) / Vanishing(x) = poly

    assert_eq!(alphas.len(), num_intermediate_products + 1);

    let z_poly_shifted: [_; 2] = grand_products.z_poly.clone().map(|el| {
        let subset = el.subset_for_degree(degree);
        let subset_len = subset.storage.len();
        let mut owned_set = Vec::with_capacity_in(subset_len, B::default());
        worker.scope(subset_len, |scope, chunk_size| {
            for (src, dst) in subset
                .storage
                .chunks(chunk_size)
                .zip(owned_set.spare_capacity_mut()[..subset_len].chunks_mut(chunk_size))
            {
                scope.spawn(|_| {
                    for (src, dst) in src.iter().zip(dst.iter_mut()) {
                        let shifted_base =
                            shift_by_omega_assuming_bitreversed::<F, P, A>(&src.storage);
                        let as_poly = GenericPolynomial::from_storage(shifted_base);
                        dst.write(as_poly);
                    }
                })
            }
        });

        unsafe { owned_set.set_len(subset_len) };

        ArcGenericLdeStorage::from_owned(GenericLdeStorage { storage: owned_set })
    });

    let lhs = grand_products
        .intermediate_polys
        .iter()
        .map(|el| el.clone().map(|el| el.subset_for_degree(degree)))
        .chain([z_poly_shifted]);

    let z_poly = grand_products
        .z_poly
        .clone()
        .map(|el| el.owned_subset_for_degree(degree));

    if crate::config::DEBUG_SATISFIABLE == true {
        assert_eq!(
            P::slice_into_base_slice(&[z_poly[0].storage[0].storage[0]])[0],
            F::ONE
        );
    }

    let rhs = [z_poly].into_iter().chain(
        grand_products
            .intermediate_polys
            .iter()
            .map(|el| el.clone().map(|el| el.subset_for_degree(degree))),
    );

    let mut columns_chunks = Vec::with_capacity_in(witness.variables_columns.len(), B::default());
    witness
        .variables_columns
        .iter()
        .map(|el| el.subset_for_degree(degree))
        .collect_into(&mut columns_chunks);

    let mut sigmas_chunks = Vec::with_capacity_in(setup.copy_permutation_polys.len(), B::default());
    setup
        .copy_permutation_polys
        .iter()
        .map(|el| el.subset_for_degree(degree))
        .collect_into(&mut sigmas_chunks);

    // lhs * denom - rhs * num == 0, and make it over coset

    let beta_c0 = P::constant(beta.coeffs[0], ctx);
    let beta_c1 = P::constant(beta.coeffs[1], ctx);

    let gamma_c0 = P::constant(gamma.coeffs[0], ctx);
    let gamma_c1 = P::constant(gamma.coeffs[1], ctx);

    for (_relation_idx, (((((lhs, rhs), alpha), non_residues), variables), sigmas)) in lhs
        .zip(rhs)
        .zip(alphas.into_iter())
        .zip(non_residues.chunks(degree))
        .zip(columns_chunks.chunks(degree))
        .zip(sigmas_chunks.chunks(degree))
        .enumerate()
    {
        let alpha_c0 = P::constant(alpha.coeffs[0], ctx);
        let alpha_c1 = P::constant(alpha.coeffs[1], ctx);

        assert_eq!(variables.len(), sigmas.len());
        assert_eq!(variables.len(), non_residues.len());

        // unfortunatery we have to open code it due to internal iterator
        let iterators = lhs[0].compute_chunks_for_num_workers(worker.num_cores);

        worker.scope(0, |scope, _| {
            for iterator in iterators.into_iter() {
                let mut dst_c0 = dst_c0.clone();
                let mut dst_c1 = dst_c1.clone();
                let lhs = lhs.clone();
                let rhs = rhs.clone();
                let x_poly = x_poly.clone();
                let mut ctx = *ctx;
                scope.spawn(move |_| {
                    let num_iterations = iterator.num_iterations();
                    let mut iterator = iterator;
                    for _ in 0..num_iterations {
                        let (outer, inner) = iterator.current();

                        let mut lhs_contribution_c0 = lhs[0].storage[outer].storage[inner];
                        let mut lhs_contribution_c1 = lhs[1].storage[outer].storage[inner];
                        for (variables, sigma) in variables.iter().zip(sigmas.iter()) {
                            // denominator is w + beta * sigma(x) + gamma
                            let mut subres_c0 = sigma.storage[outer].storage[inner];
                            subres_c0.mul_assign(&beta_c0, &mut ctx);
                            subres_c0
                                .add_assign(&variables.storage[outer].storage[inner], &mut ctx);
                            subres_c0.add_assign(&gamma_c0, &mut ctx);

                            let mut subres_c1 = sigma.storage[outer].storage[inner];
                            subres_c1.mul_assign(&beta_c1, &mut ctx);
                            subres_c1.add_assign(&gamma_c1, &mut ctx);

                            mul_assign_vectorized_in_extension::<F, P, EXT>(
                                &mut lhs_contribution_c0,
                                &mut lhs_contribution_c1,
                                &subres_c0,
                                &subres_c1,
                                &mut ctx,
                            );
                        }

                        let mut rhs_contribution_c0 = rhs[0].storage[outer].storage[inner];
                        let mut rhs_contribution_c1 = rhs[1].storage[outer].storage[inner];
                        let x_poly_value = x_poly.storage[outer].storage[inner];
                        for (non_res, variables) in non_residues.iter().zip(variables.iter()) {
                            // numerator is w + beta * non_res * x + gamma
                            let mut subres_c0 = x_poly_value;
                            subres_c0.mul_assign(non_res, &mut ctx);
                            subres_c0.mul_assign(&beta_c0, &mut ctx);
                            subres_c0
                                .add_assign(&variables.storage[outer].storage[inner], &mut ctx);
                            subres_c0.add_assign(&gamma_c0, &mut ctx);

                            let mut subres_c1 = x_poly_value;
                            subres_c1.mul_assign(non_res, &mut ctx);
                            subres_c1.mul_assign(&beta_c1, &mut ctx);
                            subres_c1.add_assign(&gamma_c1, &mut ctx);

                            mul_assign_vectorized_in_extension::<F, P, EXT>(
                                &mut rhs_contribution_c0,
                                &mut rhs_contribution_c1,
                                &subres_c0,
                                &subres_c1,
                                &mut ctx,
                            );
                        }

                        let mut contribution_c0 = lhs_contribution_c0;
                        contribution_c0.sub_assign(&rhs_contribution_c0, &mut ctx);
                        let mut contribution_c1 = lhs_contribution_c1;
                        contribution_c1.sub_assign(&rhs_contribution_c1, &mut ctx);

                        mul_assign_vectorized_in_extension::<F, P, EXT>(
                            &mut contribution_c0,
                            &mut contribution_c1,
                            &alpha_c0,
                            &alpha_c1,
                            &mut ctx,
                        );

                        if crate::config::DEBUG_SATISFIABLE == true && outer == 0 {
                            // only on base coset
                            let t = [contribution_c0];
                            let as_base = P::slice_into_base_slice(&t);
                            for el in as_base.iter() {
                                if el.is_zero() == false {
                                    dbg!(_relation_idx);
                                    dbg!(lhs[0].storage[outer].storage[inner]);
                                    dbg!(rhs[0].storage[outer].storage[inner]);
                                    dbg!(variables[0].storage[outer].storage[inner]);
                                    dbg!(variables[1].storage[outer].storage[inner]);
                                    dbg!(variables[2].storage[outer].storage[inner]);
                                    dbg!(variables[3].storage[outer].storage[inner]);
                                    dbg!(sigmas[0].storage[outer].storage[inner]);
                                    dbg!(sigmas[1].storage[outer].storage[inner]);
                                    dbg!(sigmas[2].storage[outer].storage[inner]);
                                    dbg!(sigmas[3].storage[outer].storage[inner]);
                                }
                                assert_eq!(
                                    *el,
                                    F::ZERO,
                                    "failed at outer = {}, inner = {}",
                                    outer,
                                    inner
                                );
                            }
                        }

                        unsafe { std::sync::Arc::get_mut_unchecked(&mut dst_c0.storage[outer]) }
                            .storage[inner]
                            .add_assign(&contribution_c0, &mut ctx);

                        unsafe { std::sync::Arc::get_mut_unchecked(&mut dst_c1.storage[outer]) }
                            .storage[inner]
                            .add_assign(&contribution_c1, &mut ctx);

                        iterator.advance();
                    }
                });
            }
        });
    }
}
