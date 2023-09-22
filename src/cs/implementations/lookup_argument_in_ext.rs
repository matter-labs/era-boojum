use super::{
    polynomial::{lde::ArcGenericLdeStorage, GenericPolynomial, LagrangeForm},
    polynomial_storage::{SecondStageProductsStorage, SetupStorage, WitnessStorage},
    *,
};
use crate::cs::implementations::utils::*;
use crate::field::traits::field_like::mul_assign_vectorized_in_extension;

use crate::field::ExtensionField;
use crate::field::FieldExtension;
use crate::{cs::traits::GoodAllocator, field::PrimeField};

// Evaluated over the extension field

// we need polys for \sum (selector) / (value + beta) and \sum (multiplicity) / (lookup + beta),
// so we need polys that elementwise agree on (selector) / (value + beta) and (multiplicity) / (lookup + beta) respectively

// we also perform additional aggregation to batch together columns
// and produce poly per each

// we also should have few repetitions of the argument

// pub(crate) fn compute_lookup_poly_pairs_over_general_purpose_columns<
//     F: SmallField,
//     P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
//     A: GoodAllocator,
//     B: GoodAllocator,
// >(
//     variables_columns: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
//     multiplicities_columns: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
//     constant_polys: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
//     lookup_tables_columns: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
//     table_id_column_idxes: Vec<usize>,
//     betas: Vec<F, B>, // for denominator, it should be number of repetitions
//     gammas: Vec<F, B>, // to aggregate columns
//     column_elements_per_subargument: usize,
//     lookup_selector_path: Vec<bool>,
//     worker: &Worker,
//     ctx: &mut P::Context,
// ) -> Vec<
//     (
//         Vec<GenericPolynomial<F, LagrangeForm, P, A>, B>, // involves witness
//         Vec<GenericPolynomial<F, LagrangeForm, P, A>, B>, // involve multiplicities
//     ),
//     B,
// >  {
//     assert!(variables_columns.len() > 0);

//     let domain_size = variables_columns[0].domain_size();

//     let num_polys = variables_columns.len();

//     // we repeat the argument over betas and gammas sets

//     let num_subarguments = num_polys / column_elements_per_subargument;
//     assert_eq!(multiplicities_columns.len(), 1);

//     let mut result = Vec::with_capacity_in(betas.len(), B::default());

//     assert!(table_id_column_idxes.len() == 0 || table_id_column_idxes.len() == 1);

//     // this is our lookup width, either counted by number of witness columns only, or if one includes setup
//     let num_lookup_columns = column_elements_per_subargument + ((table_id_column_idxes.len() == 1) as usize);
//     assert_eq!(lookup_tables_columns.len(), num_lookup_columns);

//     // now we can work on every individual argument

//     // we should also precompute a selector
//     let mut selector: GenericPolynomial<F, LagrangeForm, P, A> = (&*constant_polys[0]).clone();
//     if lookup_selector_path[0] == false {
//         worker.scope(selector.storage.len(), |scope, chunk_size| {
//             for dst in selector.storage.chunks_mut(chunk_size) {
//                 let mut ctx = *ctx;
//                 scope.spawn(move |_| {
//                     // inverse
//                     let one = P::one(&mut ctx);
//                     for dst in dst.iter_mut() {
//                         let mut tmp = one;
//                         tmp.sub_assign(&*dst, &mut ctx);
//                         *dst = tmp;
//                     }
//                 });
//             }
//         });
//     }

//     for (path_element, src) in lookup_selector_path[1..].iter().zip(constant_polys[1..].iter()) {
//         worker.scope(selector.storage.len(), |scope, chunk_size| {
//             for (dst, src) in selector.storage.chunks_mut(chunk_size)
//                                                         .zip(src.storage.chunks(chunk_size))
//             {
//                 let mut ctx = *ctx;
//                 scope.spawn(move |_| {
//                     if *path_element == false {
//                         // inverse
//                         let one = P::one(&mut ctx);
//                         for (src, dst) in src.iter().zip(dst.iter_mut()) {
//                             let mut tmp = one;
//                             tmp.sub_assign(src, &mut ctx);
//                             dst.mul_assign(&tmp, &mut ctx);
//                         }
//                     } else {
//                         // just mul
//                         for (src, dst) in src.iter().zip(dst.iter_mut()) {
//                             dst.mul_assign(&src, &mut ctx);
//                         }
//                     }
//                 });
//             }
//         });
//     }

//     if crate::config::DEBUG_SATISFIABLE == true {
//         let mut at_least_one_used = false;
//         for (idx, el) in selector.storage.iter().enumerate() {
//             let selector = [*el];
//             let selector = P::slice_into_base_slice(&selector);
//             for (j, el) in selector.iter().copied().enumerate() {
//                 let idx = idx * P::SIZE_FACTOR + j;
//                 if el != F::ZERO && el != F::ONE {
//                     panic!("Lookup selector is non-binary at index {} with value {:?}", idx, el);
//                 }
//                 if el == F::ONE {
//                     at_least_one_used = true;
//                 }
//             }
//         }

//         assert!(at_least_one_used, "at least one selector must be non-zero");
//     }

//     // we have independent repetitions
//     for (beta, gamma) in betas.iter().zip(gammas.iter()) {
//         let beta = P::constant(*beta, ctx);
//         let gamma = P::constant(*gamma, ctx);

//         let mut subarguments_poly_a = Vec::with_capacity_in(num_subarguments, B::default());
//         let mut subarguments_poly_b = Vec::with_capacity_in(num_subarguments, B::default());

//         let mut powers_of_gamma = Vec::with_capacity_in(num_lookup_columns, B::default());
//         let mut tmp = P::one(ctx);
//         powers_of_gamma.push(tmp);
//         for _ in 1..num_lookup_columns {
//             tmp.mul_assign(&gamma, ctx);
//             powers_of_gamma.push(tmp);
//         }

//         // precomputed columns contribution

//         let mut aggregated_lookup_columns = Vec::with_capacity_in(domain_size / P::SIZE_FACTOR, A::default());
//         worker.scope(domain_size / P::SIZE_FACTOR, |scope, chunk_size| {
//             let mut subiterators = Vec::new_in(B::default());

//             for (idx, _) in aggregated_lookup_columns.spare_capacity_mut()[..domain_size / P::SIZE_FACTOR].chunks_mut(chunk_size).enumerate() {
//                 let mut tmp = Vec::with_capacity_in(lookup_tables_columns.len(), B::default());
//                 for src in lookup_tables_columns.iter() {
//                     let chunk = src.storage.chunks(chunk_size).skip(idx).next().expect("next chunk").iter();
//                     tmp.push(chunk);
//                 }
//                 assert_eq!(tmp.len(), powers_of_gamma.len());
//                 subiterators.push(tmp);
//             }

//             assert_eq!(
//                 aggregated_lookup_columns.spare_capacity_mut()[..domain_size / P::SIZE_FACTOR].chunks_mut(chunk_size).len(),
//                 subiterators.len()
//             );
//             for (dst, src) in
//                 aggregated_lookup_columns.spare_capacity_mut()[..domain_size / P::SIZE_FACTOR].chunks_mut(chunk_size)
//                 .zip(subiterators.into_iter())
//             {
//                 let mut ctx = *ctx;
//                 let powers_of_gamma = &powers_of_gamma;

//                 assert_eq!(src.len(), powers_of_gamma.len());
//                 scope.spawn(move |_| {
//                     let mut src = src;
//                     for dst in dst.iter_mut() {
//                         let mut acc = beta;
//                         for (src, gamma) in src.iter_mut().zip(powers_of_gamma.iter()) {
//                             P::mul_and_accumulate_into(&mut acc, src.next().expect("table column element"), gamma, &mut ctx);
//                         }

//                         dst.write(acc);
//                     }
//                 });
//             }
//         });

//         unsafe {aggregated_lookup_columns.set_len(domain_size / P::SIZE_FACTOR)};
//         let mut aggregated_lookup_columns_inversed = P::vec_into_base_vec(aggregated_lookup_columns);
//         batch_inverse_inplace_parallel::<F, A>(&mut aggregated_lookup_columns_inversed, worker);
//         let aggregated_lookup_columns_inversed = P::vec_from_base_vec(aggregated_lookup_columns_inversed);

//         // we follow the same aproach as above - first prepare chunks, and then work over them

//         assert_eq!(
//             variables_columns.chunks_exact(column_elements_per_subargument).len(),
//             num_subarguments
//         );

//         for (witness_columns, multiplicity_column)
//             in variables_columns.chunks_exact(column_elements_per_subargument)
//             .zip(multiplicities_columns.iter())
//         {
//             let mut a_poly = Vec::with_capacity_in(domain_size / P::SIZE_FACTOR, A::default());

//             worker.scope(domain_size / P::SIZE_FACTOR, |scope, chunk_size| {
//                 // prepare subiterators

//                 let mut subiterators = Vec::new_in(B::default());
//                 for (idx, _) in selector.storage.chunks(chunk_size).enumerate() {
//                     let mut tmp = Vec::with_capacity_in(num_lookup_columns, B::default());
//                     for src in witness_columns.iter() {
//                         let chunk = src.storage.chunks(chunk_size).skip(idx).next().expect("next chunk").iter();
//                         tmp.push(chunk);
//                     }
//                     if let Some(table_id_poly_idx) = table_id_column_idxes.get(0).copied() {
//                         let chunk = constant_polys[table_id_poly_idx].storage.chunks(chunk_size).skip(idx).next().expect("next chunk").iter();
//                         tmp.push(chunk);
//                     }
//                     assert_eq!(tmp.len(), powers_of_gamma.len());
//                     subiterators.push(tmp);
//                 }

//                 // work with A poly only, compute denominator

//                 assert_eq!(
//                     a_poly.spare_capacity_mut()[..domain_size / P::SIZE_FACTOR].chunks_mut(chunk_size).len(),
//                     subiterators.len()
//                 );

//                 for (dst_a, src)
//                         in a_poly.spare_capacity_mut()[..domain_size / P::SIZE_FACTOR].chunks_mut(chunk_size)
//                         .zip(subiterators.into_iter())
//                 {
//                     let powers_of_gamma = &powers_of_gamma[..];
//                     let mut ctx = *ctx;
//                     assert_eq!(src.len(), powers_of_gamma.len());

//                     scope.spawn(move |_| {
//                         let mut src = src;
//                         for dst_a in dst_a.iter_mut() {
//                             let mut acc = beta;
//                             for (src, gamma) in src.iter_mut().zip(powers_of_gamma.iter()) {
//                                 P::mul_and_accumulate_into(&mut acc, src.next().expect("witness column element"), gamma, &mut ctx);
//                             }

//                             dst_a.write(acc);
//                         }
//                     });
//                 }

//             });

//             unsafe {a_poly.set_len(domain_size / P::SIZE_FACTOR)};
//             let mut a_poly = P::vec_into_base_vec(a_poly);
//             batch_inverse_inplace_parallel::<F, A>(&mut a_poly, worker);
//             let mut a_poly = P::vec_from_base_vec(a_poly);

//             // A poly's denominator is ready, now we have simple elementwise pass

//             let mut b_poly = aggregated_lookup_columns_inversed.clone();

//             worker.scope(a_poly.len(), |scope, chunk_size| {
//                 for (((dst_a, dst_b), mults), selector)
//                                 in a_poly.chunks_mut(chunk_size)
//                                 .zip(b_poly.chunks_mut(chunk_size))
//                                 .zip(multiplicity_column.storage.chunks(chunk_size))
//                                 .zip(selector.storage.chunks(chunk_size))
//                 {
//                     let mut ctx = *ctx;
//                     scope.spawn(move |_| {
//                         for (dst_a, selector) in dst_a.iter_mut().zip(selector.iter()) {
//                             dst_a.mul_assign(selector, &mut ctx);
//                         }

//                         for (dst_b, mults) in dst_b.iter_mut().zip(mults.iter()) {
//                             dst_b.mul_assign(mults, &mut ctx);
//                         }
//                     });
//                 }
//             });

//             if crate::config::DEBUG_SATISFIABLE == true {
//                 let mut a_sum = F::ZERO;
//                 for a in P::slice_into_base_slice(&a_poly).iter() {
//                     a_sum.add_assign(a);
//                 }

//                 let mut b_sum = F::ZERO;
//                 for b in P::slice_into_base_slice(&b_poly).iter() {
//                     b_sum.add_assign(b);
//                 }

//                 if a_sum != b_sum {
//                     panic!("Sumcheck fails with a = {:?}, b = {:?}", a_sum, b_sum);
//                 }
//             }

//             // push the results
//             let a_poly = GenericPolynomial::from_storage(a_poly);
//             let b_poly = GenericPolynomial::from_storage(b_poly);

//             subarguments_poly_a.push(a_poly);
//             subarguments_poly_b.push(b_poly);
//         }

//         assert_eq!(subarguments_poly_a.len(), num_subarguments);
//         assert_eq!(subarguments_poly_b.len(), num_subarguments);

//         result.push((subarguments_poly_a, subarguments_poly_b));
//     }

//     assert_eq!(result.len(), betas.len());

//     result
// }

pub(crate) fn compute_lookup_poly_pairs_specialized<
    F: SmallField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    EXT: FieldExtension<2, BaseField = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    variables_columns: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    multiplicities_columns: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    constant_polys: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    lookup_tables_columns: Vec<std::sync::Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    table_id_column_idxes: Vec<usize>,
    beta: ExtensionField<F, 2, EXT>,  // for denominator
    gamma: ExtensionField<F, 2, EXT>, // to aggregate columns
    variables_offset: usize,
    lookup_parameters: LookupParameters,
    worker: &Worker,
    ctx: &mut P::Context,
) -> (
    Vec<[GenericPolynomial<F, LagrangeForm, P, A>; 2], B>, // involves witness
    Vec<[GenericPolynomial<F, LagrangeForm, P, A>; 2], B>, // involve multiplicities
) {
    assert!(variables_columns.len() > 0);

    let domain_size = variables_columns[0].domain_size();

    let (
        use_constant_for_table_id,
        _share_table_id,
        _width,
        num_variable_columns_per_argument,
        total_num_columns_per_subargument,
        num_subarguments,
    ) = match lookup_parameters {
        LookupParameters::UseSpecializedColumnsWithTableIdAsVariable {
            width,
            num_repetitions,
            share_table_id: _,
        } => (
            false,
            false,
            width as usize,
            width as usize + 1,
            width as usize + 1,
            num_repetitions,
        ),
        LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
            width,
            num_repetitions,
            share_table_id,
        } => {
            assert!(share_table_id);

            (
                true,
                true,
                width as usize,
                width as usize,
                width as usize + 1,
                num_repetitions,
            )
        }
        _ => unreachable!(),
    };

    // we repeat the argument over betas and gammas sets
    let variables_columns_for_lookup = variables_columns[variables_offset
        ..(variables_offset + num_variable_columns_per_argument * num_subarguments)]
        .to_vec_in(B::default());

    // we no longer need full witness
    drop(variables_columns);

    let beta_c0 = P::constant(beta.coeffs[0], ctx);
    let beta_c1 = P::constant(beta.coeffs[1], ctx);
    let _gamma_c0 = P::constant(gamma.coeffs[0], ctx);
    let _gamma_c1 = P::constant(gamma.coeffs[1], ctx);

    let mut subarguments_witness_encoding_polys =
        Vec::with_capacity_in(num_subarguments, B::default());
    let mut subarguments_multiplicities_encoding_polys = Vec::with_capacity_in(1, B::default());

    let mut powers_of_gamma_c0 =
        Vec::with_capacity_in(total_num_columns_per_subargument, B::default());
    let mut powers_of_gamma_c1 =
        Vec::with_capacity_in(total_num_columns_per_subargument, B::default());
    let mut tmp = {
        use crate::field::traits::field::Field;

        ExtensionField::<F, 2, EXT>::ONE
    };
    powers_of_gamma_c0.push(P::constant(tmp.coeffs[0], ctx));
    powers_of_gamma_c1.push(P::constant(tmp.coeffs[1], ctx));
    for _ in 1..total_num_columns_per_subargument {
        crate::field::Field::mul_assign(&mut tmp, &gamma);

        powers_of_gamma_c0.push(P::constant(tmp.coeffs[0], ctx));
        powers_of_gamma_c1.push(P::constant(tmp.coeffs[1], ctx));
    }

    // precomputed columns contribution

    // form denominator's part of t_0 + gamma * t_1 + ... + beta
    let mut aggregated_lookup_columns_c0 =
        Vec::with_capacity_in(domain_size / P::SIZE_FACTOR, A::default());
    let mut aggregated_lookup_columns_c1 =
        Vec::with_capacity_in(domain_size / P::SIZE_FACTOR, A::default());

    worker.scope(domain_size / P::SIZE_FACTOR, |scope, chunk_size| {
        let mut subiterators = Vec::new_in(B::default());

        for (idx, _) in aggregated_lookup_columns_c0.spare_capacity_mut()
            [..domain_size / P::SIZE_FACTOR]
            .chunks_mut(chunk_size)
            .enumerate()
        {
            let mut tmp = Vec::with_capacity_in(lookup_tables_columns.len(), B::default());
            for src in lookup_tables_columns.iter() {
                let chunk = src
                    .storage
                    .chunks(chunk_size)
                    .nth(idx)
                    .expect("next chunk")
                    .iter();
                tmp.push(chunk);
            }
            assert_eq!(tmp.len(), powers_of_gamma_c0.len());
            assert_eq!(tmp.len(), powers_of_gamma_c1.len());
            subiterators.push(tmp);
        }

        assert_eq!(
            aggregated_lookup_columns_c0.spare_capacity_mut()[..domain_size / P::SIZE_FACTOR]
                .chunks_mut(chunk_size)
                .len(),
            subiterators.len()
        );
        assert_eq!(
            aggregated_lookup_columns_c1.spare_capacity_mut()[..domain_size / P::SIZE_FACTOR]
                .chunks_mut(chunk_size)
                .len(),
            subiterators.len()
        );

        for ((dst_c0, dst_c1), src) in aggregated_lookup_columns_c0.spare_capacity_mut()
            [..domain_size / P::SIZE_FACTOR]
            .chunks_mut(chunk_size)
            .zip(
                aggregated_lookup_columns_c1.spare_capacity_mut()[..domain_size / P::SIZE_FACTOR]
                    .chunks_mut(chunk_size),
            )
            .zip(subiterators.into_iter())
        {
            let mut ctx = *ctx;
            let powers_of_gamma_c0 = &powers_of_gamma_c0;
            let powers_of_gamma_c1 = &powers_of_gamma_c1;

            assert_eq!(src.len(), powers_of_gamma_c0.len());
            assert_eq!(src.len(), powers_of_gamma_c1.len());

            scope.spawn(move |_| {
                let mut src = src;
                for (dst_c0, dst_c1) in dst_c0.iter_mut().zip(dst_c1.iter_mut()) {
                    let mut acc_c0 = beta_c0;
                    let mut acc_c1 = beta_c1;
                    for ((src, gamma_c0), gamma_c1) in src
                        .iter_mut()
                        .zip(powers_of_gamma_c0.iter())
                        .zip(powers_of_gamma_c1.iter())
                    {
                        let src = src.next().expect("table column element");
                        P::mul_and_accumulate_into(&mut acc_c0, src, gamma_c0, &mut ctx);
                        P::mul_and_accumulate_into(&mut acc_c1, src, gamma_c1, &mut ctx);
                    }

                    dst_c0.write(acc_c0);
                    dst_c1.write(acc_c1);
                }
            });
        }
    });

    unsafe { aggregated_lookup_columns_c0.set_len(domain_size / P::SIZE_FACTOR) };
    unsafe { aggregated_lookup_columns_c1.set_len(domain_size / P::SIZE_FACTOR) };

    let mut aggregated_lookup_columns_inversed_c0 =
        P::vec_into_base_vec(aggregated_lookup_columns_c0);
    let mut aggregated_lookup_columns_inversed_c1 =
        P::vec_into_base_vec(aggregated_lookup_columns_c1);

    batch_inverse_inplace_parallel_in_extension::<F, EXT, A>(
        &mut aggregated_lookup_columns_inversed_c0,
        &mut aggregated_lookup_columns_inversed_c1,
        worker,
    );
    let aggregated_lookup_columns_inversed_c0 =
        P::vec_from_base_vec(aggregated_lookup_columns_inversed_c0);
    let aggregated_lookup_columns_inversed_c1 =
        P::vec_from_base_vec(aggregated_lookup_columns_inversed_c1);

    // we follow the same aproach as above - first prepare chunks, and then work over them
    for witness_columns in
        variables_columns_for_lookup.chunks_exact(num_variable_columns_per_argument)
    {
        let mut witness_encoding_poly_c0 =
            Vec::with_capacity_in(domain_size / P::SIZE_FACTOR, A::default());
        let mut witness_encoding_poly_c1 =
            Vec::with_capacity_in(domain_size / P::SIZE_FACTOR, A::default());

        worker.scope(domain_size / P::SIZE_FACTOR, |scope, chunk_size| {
            // prepare subiterators

            let mut subiterators = Vec::new_in(B::default());
            for idx in 0..witness_columns[0].storage.chunks(chunk_size).len() {
                let mut tmp =
                    Vec::with_capacity_in(total_num_columns_per_subargument, B::default());
                for src in witness_columns.iter() {
                    let chunk = src
                        .storage
                        .chunks(chunk_size)
                        .nth(idx)
                        .expect("next chunk")
                        .iter();
                    tmp.push(chunk);
                }
                if let Some(table_id_poly) = table_id_column_idxes.first().copied() {
                    assert!(use_constant_for_table_id);
                    let chunk = constant_polys[table_id_poly]
                        .storage
                        .chunks(chunk_size)
                        .nth(idx)
                        .expect("next chunk")
                        .iter();
                    tmp.push(chunk);
                }
                assert_eq!(tmp.len(), powers_of_gamma_c0.len());
                assert_eq!(tmp.len(), powers_of_gamma_c1.len());
                subiterators.push(tmp);
            }

            // work with A poly only, compute denominator

            assert_eq!(
                witness_encoding_poly_c0.spare_capacity_mut()[..domain_size / P::SIZE_FACTOR]
                    .chunks_mut(chunk_size)
                    .len(),
                subiterators.len()
            );
            assert_eq!(
                witness_encoding_poly_c1.spare_capacity_mut()[..domain_size / P::SIZE_FACTOR]
                    .chunks_mut(chunk_size)
                    .len(),
                subiterators.len()
            );

            for ((dst_c0, dst_c1), src) in witness_encoding_poly_c0.spare_capacity_mut()
                [..domain_size / P::SIZE_FACTOR]
                .chunks_mut(chunk_size)
                .zip(
                    witness_encoding_poly_c1.spare_capacity_mut()[..domain_size / P::SIZE_FACTOR]
                        .chunks_mut(chunk_size),
                )
                .zip(subiterators.into_iter())
            {
                let powers_of_gamma_c0 = &powers_of_gamma_c0[..];
                let powers_of_gamma_c1 = &powers_of_gamma_c1[..];
                let mut ctx = *ctx;
                assert_eq!(src.len(), powers_of_gamma_c0.len());
                assert_eq!(src.len(), powers_of_gamma_c1.len());

                scope.spawn(move |_| {
                    let mut src = src;
                    for (dst_c0, dst_c1) in dst_c0.iter_mut().zip(dst_c1.iter_mut()) {
                        let mut acc_c0 = beta_c0;
                        let mut acc_c1 = beta_c1;
                        for ((src, gamma_c0), gamma_c1) in src
                            .iter_mut()
                            .zip(powers_of_gamma_c0.iter())
                            .zip(powers_of_gamma_c1.iter())
                        {
                            let src = src.next().expect("witness column element");
                            P::mul_and_accumulate_into(&mut acc_c0, src, gamma_c0, &mut ctx);
                            P::mul_and_accumulate_into(&mut acc_c1, src, gamma_c1, &mut ctx);
                        }

                        dst_c0.write(acc_c0);
                        dst_c1.write(acc_c1);
                    }
                });
            }
        });

        unsafe { witness_encoding_poly_c0.set_len(domain_size / P::SIZE_FACTOR) };
        unsafe { witness_encoding_poly_c1.set_len(domain_size / P::SIZE_FACTOR) };

        let mut witness_encoding_poly_c0 = P::vec_into_base_vec(witness_encoding_poly_c0);
        let mut witness_encoding_poly_c1 = P::vec_into_base_vec(witness_encoding_poly_c1);

        batch_inverse_inplace_parallel_in_extension::<F, EXT, A>(
            &mut witness_encoding_poly_c0,
            &mut witness_encoding_poly_c1,
            worker,
        );
        let witness_encoding_poly_c0 = P::vec_from_base_vec(witness_encoding_poly_c0);
        let witness_encoding_poly_c1 = P::vec_from_base_vec(witness_encoding_poly_c1);

        // push the results
        let witness_encoding_poly_c0 = GenericPolynomial::from_storage(witness_encoding_poly_c0);
        let witness_encoding_poly_c1 = GenericPolynomial::from_storage(witness_encoding_poly_c1);

        subarguments_witness_encoding_polys
            .push([witness_encoding_poly_c0, witness_encoding_poly_c1]);
    }

    // now multiplicities
    for multiplicity_column in multiplicities_columns.iter() {
        // A poly's denominator is ready, now we have simple elementwise pass

        let mut multiplicities_encoding_poly_c0 = aggregated_lookup_columns_inversed_c0.clone();
        let mut multiplicities_encoding_poly_c1 = aggregated_lookup_columns_inversed_c1.clone();

        worker.scope(
            multiplicities_encoding_poly_c0.len(),
            |scope, chunk_size| {
                for ((dst_c0, dst_c1), mults) in multiplicities_encoding_poly_c0
                    .chunks_mut(chunk_size)
                    .zip(multiplicities_encoding_poly_c1.chunks_mut(chunk_size))
                    .zip(multiplicity_column.storage.chunks(chunk_size))
                {
                    let mut ctx = *ctx;
                    scope.spawn(move |_| {
                        for ((dst_c0, dst_c1), mults) in
                            dst_c0.iter_mut().zip(dst_c1.iter_mut()).zip(mults.iter())
                        {
                            dst_c0.mul_assign(mults, &mut ctx);
                            dst_c1.mul_assign(mults, &mut ctx);
                        }
                    });
                }
            },
        );

        // push the results
        let multiplicities_encoding_poly_c0 =
            GenericPolynomial::from_storage(multiplicities_encoding_poly_c0);
        let multiplicities_encoding_poly_c1 =
            GenericPolynomial::from_storage(multiplicities_encoding_poly_c1);

        subarguments_multiplicities_encoding_polys.push([
            multiplicities_encoding_poly_c0,
            multiplicities_encoding_poly_c1,
        ]);
    }

    assert_eq!(subarguments_witness_encoding_polys.len(), num_subarguments);
    assert_eq!(subarguments_multiplicities_encoding_polys.len(), 1);

    if crate::config::DEBUG_SATISFIABLE == true {
        // {
        let mut a_sum_c0 = F::ZERO;
        let mut a_sum_c1 = F::ZERO;
        for a_poly in subarguments_witness_encoding_polys.iter() {
            for a in P::slice_into_base_slice(&a_poly[0].storage).iter() {
                a_sum_c0.add_assign(a);
            }
            for a in P::slice_into_base_slice(&a_poly[1].storage).iter() {
                a_sum_c1.add_assign(a);
            }
        }

        let mut b_sum_c0 = F::ZERO;
        let mut b_sum_c1 = F::ZERO;
        for b_poly in subarguments_multiplicities_encoding_polys.iter() {
            for b in P::slice_into_base_slice(&b_poly[0].storage).iter() {
                b_sum_c0.add_assign(b);
            }
            for b in P::slice_into_base_slice(&b_poly[1].storage).iter() {
                b_sum_c1.add_assign(b);
            }
        }

        if a_sum_c0 != b_sum_c0 || a_sum_c1 != b_sum_c1 {
            panic!(
                "Sumcheck fails with a = [{:?}, {:?}], b = [{:?}, {:?}]",
                a_sum_c0, a_sum_c1, b_sum_c0, b_sum_c1,
            );
        }
    }

    (
        subarguments_witness_encoding_polys,
        subarguments_multiplicities_encoding_polys,
    )
}

// pub(crate) fn compute_quotient_terms_for_lookup_over_general_purpose_gates<
//     F: PrimeField,
//     P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
//     A: GoodAllocator,
//     B: GoodAllocator,
// >(
//     witness: &WitnessStorage<F, P, A, B>,
//     second_stage: &SecondStageProductsStorage<F, P, A, B>,
//     setup: &SetupStorage<F, P, A, B>,
//     selector_precomputed: ArcGenericLdeStorage<F, P, A, B>,
//     beta: F,
//     gamma: F,
//     alphas: Vec<F>,
//     table_id_column_idxes: Vec<usize>,
//     column_elements_per_subargument: usize,
//     num_subarguments: usize,
//     set_idx: usize,
//     quotient_degree: usize,
//     dst: &mut ArcGenericLdeStorage<F, P, A, B>,
//     worker: &Worker,
//     ctx: &mut P::Context,
// )  {
//     assert_eq!(alphas.len(), num_subarguments * 2);
//     // A(x) * (gamma^0 * column_0 + ... + gamma^n * column_n + beta) == lookup_selector

//     // B(x) * (gamma^0 * column_0 + ... + gamma^n * column_n + beta) == multiplicity column

//     let gamma = P::constant(gamma, ctx);
//     let beta = P::constant(beta, ctx);

//     let domain_size = dst.storage[0].domain_size();

//     assert!(table_id_column_idxes.len() == 0 || table_id_column_idxes.len() == 1);

//     // this is our lookup width, either counted by number of witness columns only, or if one includes setup
//     let capacity = column_elements_per_subargument + ((table_id_column_idxes.len() == 1) as usize);

//     let mut powers_of_gamma = Vec::with_capacity_in(capacity, B::default());
//     let mut tmp = P::one(ctx);
//     powers_of_gamma.push(tmp);
//     for _ in 1..capacity {
//         tmp.mul_assign(&gamma, ctx);
//         powers_of_gamma.push(tmp);
//     }

//     // for each term we form inputs, and then parallelize over them

//     assert_eq!(dst.outer_len(), quotient_degree);
//     let iterators = dst.compute_chunks_for_num_workers(worker.num_cores);
//     // first precompute table aggregations

//     let aggregated_lookup_columns = setup.lookup_tables_columns[0]
//         .owned_subset_for_degree(quotient_degree);

//     let mut other_lookup_columns = Vec::with_capacity_in(setup.lookup_tables_columns.len() - 1, B::default());
//         setup.lookup_tables_columns[1..].iter().map(|el| el.subset_for_degree(quotient_degree)).collect_into(&mut other_lookup_columns);

//     // we access the memory exactly once
//     let dst_chunks = aggregated_lookup_columns.compute_chunks_for_num_workers(worker.num_cores);
//     worker.scope(0, |scope, _| {
//         // transpose other chunks
//         for lde_iter in dst_chunks.into_iter() {
//             let mut lde_iter = lde_iter;
//             let powers_of_gamma = &powers_of_gamma[1..];
//             assert_eq!(powers_of_gamma.len(), other_lookup_columns.len());
//             let mut ctx = *ctx;
//             let mut aggregated_lookup_columns = aggregated_lookup_columns.clone();
//             let other_lookup_columns = &other_lookup_columns;
//             scope.spawn(move |_| {
//                 for _ in 0..lde_iter.num_iterations() {
//                     let (outer, inner) = lde_iter.current();
//                     let mut tmp = beta;

//                     for (gamma, other) in powers_of_gamma.iter().zip(other_lookup_columns.iter()) {
//                         P::mul_and_accumulate_into(
//                             &mut tmp,
//                             gamma,
//                             &other.storage[outer].storage[inner],
//                             &mut ctx
//                         );
//                     }

//                     // our "base" value for `aggregated_lookup_columns` already contains a term 1 * column_0,
//                     // so we just add

//                     unsafe {
//                         std::sync::Arc::get_mut_unchecked(
//                             &mut aggregated_lookup_columns.storage[outer])
//                             .storage[inner].add_assign(&tmp, &mut ctx);
//                     };

//                     lde_iter.advance();
//                 }
//             });
//         }
//     });

//     let selector_precomputed = &selector_precomputed;

//     // now we can compute each term the same way, but identifying contributions
//     let witness_encoding_poly_powers_of_alpha = &alphas[..num_subarguments];
//     assert_eq!(witness_encoding_poly_powers_of_alpha.len(), witness.variables_columns.chunks_exact(column_elements_per_subargument).len());

//     for (idx, (alpha, vars_chunk)) in witness_encoding_poly_powers_of_alpha.iter().zip(witness.variables_columns.chunks_exact(column_elements_per_subargument)).enumerate() {
//         let alpha = P::constant(*alpha, ctx);
//         // A(x) * (gamma^0 * column_0 + ... + gamma^n * column_n + beta) == lookup_selector

//         let flat_poly_idx_offset = num_subarguments * set_idx;
//         let a_poly = &second_stage.lookup_witness_encoding_polys[flat_poly_idx_offset + idx].subset_for_degree(quotient_degree);

//         assert_eq!(selector_precomputed.outer_len(), a_poly.outer_len());
//         assert_eq!(selector_precomputed.inner_len(), a_poly.inner_len());
//         let mut columns = Vec::with_capacity_in(capacity, B::default());
//         for wit_column in vars_chunk.iter() {
//             let subset = wit_column.subset_for_degree(quotient_degree);
//             columns.push(subset);
//         }

//         if let Some(table_id_poly) = table_id_column_idxes.get(0).copied() {
//             let subset = setup.constant_columns[table_id_poly].subset_for_degree(quotient_degree);
//             columns.push(subset);
//         }

//         worker.scope(0, |scope, _| {
//             // transpose other chunks
//             for lde_iter in iterators.iter().cloned() {
//                 let mut lde_iter = lde_iter;
//                 let powers_of_gamma = &powers_of_gamma[..];
//                 let mut ctx = *ctx;
//                 let columns = &columns;
//                 assert_eq!(powers_of_gamma.len(), columns.len());
//                 let mut dst = dst.clone(); // we use Arc, so it's the same instance
//                 scope.spawn(move |_| {
//                     for _ in 0..lde_iter.num_iterations() {
//                         let (outer, inner) = lde_iter.current();
//                         let mut tmp = beta;

//                         for (gamma, other) in powers_of_gamma.iter().zip(columns.iter()) {
//                             P::mul_and_accumulate_into(
//                                 &mut tmp,
//                                 gamma,
//                                 &other.storage[outer].storage[inner],
//                                 &mut ctx
//                             );
//                         }
//                         // mul by A(X)
//                         tmp.mul_assign(&a_poly.storage[outer].storage[inner], &mut ctx);
//                         // subtract selectors
//                         tmp.sub_assign(&selector_precomputed.storage[outer].storage[inner], &mut ctx);

//                         // mul by alpha
//                         tmp.mul_assign(&alpha, &mut ctx);

//                         if crate::config::DEBUG_SATISFIABLE == true {
//                             if outer == 0 {
//                                 if tmp.is_zero() == false {
//                                     let mut normal_enumeration = inner.reverse_bits();
//                                     normal_enumeration >>= usize::BITS - domain_size.trailing_zeros();
//                                     panic!("A(x) term is invalid for index {} for subargument {} in repetition {}", normal_enumeration, idx, set_idx);
//                                 }
//                             }
//                         }

//                         // add into accumulator
//                         unsafe {
//                             std::sync::Arc::get_mut_unchecked(
//                                 &mut dst.storage[outer]
//                             )
//                                 .storage[inner]
//                                 .add_assign(&tmp, &mut ctx);
//                         };

//                         lde_iter.advance();
//                     }
//                 });
//             }
//         });
//     }

//     // now B poly
//     let multiplicities_encoding_poly_powers_of_alpha = &alphas[num_subarguments..];
//     assert_eq!(multiplicities_encoding_poly_powers_of_alpha.len(), num_subarguments);
//     for (idx, alpha) in multiplicities_encoding_poly_powers_of_alpha.iter().enumerate() {
//         let alpha = P::constant(*alpha, ctx);
//         // B(x) * (gamma^0 * column_0 + ... + gamma^n * column_n + beta) == multiplicity column
//         let flat_poly_idx_offset = num_subarguments * set_idx;
//         let b_poly = &second_stage.lookup_multiplicities_encoding_polys[flat_poly_idx_offset + idx].subset_for_degree(quotient_degree);
//         // columns are precomputed, so we need multiplicity
//         let multiplicity =  witness.lookup_multiplicities_polys[idx].subset_for_degree(quotient_degree);
//         worker.scope(0, |scope, _| {
//             // transpose other chunks
//             for lde_iter in iterators.iter().cloned() {
//                 let mut lde_iter = lde_iter;
//                 let mut ctx = *ctx;
//                 let mut dst = dst.clone(); // we use Arc, so it's the same instance
//                 let multiplicity = &multiplicity;
//                 let aggregated_lookup_columns = &aggregated_lookup_columns;
//                 scope.spawn(move |_| {
//                     for _ in 0..lde_iter.num_iterations() {
//                         let (outer, inner) = lde_iter.current();
//                         let mut tmp = aggregated_lookup_columns.storage[outer].storage[inner];
//                         // mul by B(X)
//                         tmp.mul_assign(&b_poly.storage[outer].storage[inner], &mut ctx);
//                         // subtract multiplicity
//                         tmp.sub_assign(&multiplicity.storage[outer].storage[inner], &mut ctx);
//                         // mul by alpha
//                         tmp.mul_assign(&alpha, &mut ctx);

//                         if crate::config::DEBUG_SATISFIABLE == true {
//                             if outer == 0 {
//                                 if tmp.is_zero() == false {
//                                     let mut normal_enumeration = inner.reverse_bits();
//                                     normal_enumeration >>= usize::BITS - domain_size.trailing_zeros();
//                                     panic!("B(x) term is invalid for index {} for subargument {} in repetition {}", normal_enumeration, idx, set_idx);
//                                 }
//                             }
//                         }

//                         // add into accumulator
//                         unsafe {
//                             std::sync::Arc::get_mut_unchecked(
//                                 &mut dst.storage[outer])
//                                 .storage[inner]
//                                 .add_assign(&tmp, &mut ctx);
//                         };

//                         lde_iter.advance();
//                     }
//                 });
//             }
//         });
//     }
// }

pub(crate) fn compute_quotient_terms_for_lookup_specialized<
    F: PrimeField,
    EXT: FieldExtension<2, BaseField = F>,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    witness: &WitnessStorage<F, P, A, B>,
    second_stage: &SecondStageProductsStorage<F, P, A, B>,
    setup: &SetupStorage<F, P, A, B>,
    beta: ExtensionField<F, 2, EXT>,
    gamma: ExtensionField<F, 2, EXT>,
    alphas: Vec<ExtensionField<F, 2, EXT>>,
    table_id_column_idxes: Vec<usize>,
    column_elements_per_subargument: usize,
    num_subarguments: usize,
    num_multiplicities_polys: usize,
    variables_offset: usize,
    quotient_degree: usize,
    dst_c0: &mut ArcGenericLdeStorage<F, P, A, B>,
    dst_c1: &mut ArcGenericLdeStorage<F, P, A, B>,
    worker: &Worker,
    ctx: &mut P::Context,
) {
    assert_eq!(alphas.len(), num_subarguments + num_multiplicities_polys);
    assert_eq!(num_multiplicities_polys, 1);
    // A(x) * (gamma^0 * column_0 + ... + gamma^n * column_n + beta) == lookup_selector

    // B(x) * (gamma^0 * column_0 + ... + gamma^n * column_n + beta) == multiplicity column

    let _gamma_c0 = P::constant(gamma.coeffs[0], ctx);
    let _gamma_c1 = P::constant(gamma.coeffs[1], ctx);

    let beta_c0 = P::constant(beta.coeffs[0], ctx);
    let beta_c1 = P::constant(beta.coeffs[1], ctx);

    let domain_size = dst_c0.storage[0].domain_size();

    assert!(
        table_id_column_idxes.len() == 0 || table_id_column_idxes.len() == 1,
        "only specialized lookup with shared table ID in constants in supported, or no sharing, but got {:?} as table idxes for IDs",
        &table_id_column_idxes,
    );

    let variables_columns_for_lookup = witness.variables_columns
        [variables_offset..(variables_offset + column_elements_per_subargument * num_subarguments)]
        .to_vec_in(B::default());

    // this is our lookup width, either counted by number of witness columns only, or if one includes setup
    let capacity = column_elements_per_subargument + ((table_id_column_idxes.len() == 1) as usize);

    let mut powers_of_gamma_c0 = Vec::with_capacity_in(capacity, B::default());
    let mut powers_of_gamma_c1 = Vec::with_capacity_in(capacity, B::default());
    let mut tmp = {
        use crate::field::traits::field::Field;

        ExtensionField::<F, 2, EXT>::ONE
    };
    powers_of_gamma_c0.push(P::constant(tmp.coeffs[0], ctx));
    powers_of_gamma_c1.push(P::constant(tmp.coeffs[1], ctx));
    for _ in 1..capacity {
        crate::field::Field::mul_assign(&mut tmp, &gamma);

        powers_of_gamma_c0.push(P::constant(tmp.coeffs[0], ctx));
        powers_of_gamma_c1.push(P::constant(tmp.coeffs[1], ctx));
    }

    // for each term we form inputs, and then parallelize over them

    assert_eq!(dst_c0.outer_len(), quotient_degree);
    assert_eq!(dst_c1.outer_len(), quotient_degree);
    let iterators = dst_c0.compute_chunks_for_num_workers(worker.num_cores);
    // first precompute table aggregations

    let aggregated_lookup_columns_c0 =
        setup.lookup_tables_columns[0].owned_subset_for_degree(quotient_degree);
    let aggregated_lookup_columns_c1 = ArcGenericLdeStorage::<F, P, A, B>::zeroed(
        aggregated_lookup_columns_c0.inner_len(),
        aggregated_lookup_columns_c0.outer_len(),
        A::default(),
        B::default(),
    );

    let mut other_lookup_columns =
        Vec::with_capacity_in(setup.lookup_tables_columns.len() - 1, B::default());
    setup.lookup_tables_columns[1..]
        .iter()
        .map(|el| el.subset_for_degree(quotient_degree))
        .collect_into(&mut other_lookup_columns);

    // we access the memory exactly once
    let dst_chunks = aggregated_lookup_columns_c0.compute_chunks_for_num_workers(worker.num_cores);
    worker.scope(0, |scope, _| {
        // transpose other chunks
        for lde_iter in dst_chunks.into_iter() {
            let mut lde_iter = lde_iter;
            let powers_of_gamma_c0 = &powers_of_gamma_c0[1..];
            let powers_of_gamma_c1 = &powers_of_gamma_c1[1..];
            assert_eq!(powers_of_gamma_c0.len(), other_lookup_columns.len());
            assert_eq!(powers_of_gamma_c1.len(), other_lookup_columns.len());

            let mut ctx = *ctx;
            let mut aggregated_lookup_columns_c0 = aggregated_lookup_columns_c0.clone();
            let mut aggregated_lookup_columns_c1 = aggregated_lookup_columns_c1.clone();

            let other_lookup_columns = &other_lookup_columns;
            scope.spawn(move |_| {
                for _ in 0..lde_iter.num_iterations() {
                    let (outer, inner) = lde_iter.current();
                    let mut tmp_c0 = beta_c0;
                    let mut tmp_c1 = beta_c1;

                    for ((gamma_c0, gamma_c1), other) in powers_of_gamma_c0
                        .iter()
                        .zip(powers_of_gamma_c1.iter())
                        .zip(other_lookup_columns.iter())
                    {
                        P::mul_and_accumulate_into(
                            &mut tmp_c0,
                            gamma_c0,
                            &other.storage[outer].storage[inner],
                            &mut ctx,
                        );

                        P::mul_and_accumulate_into(
                            &mut tmp_c1,
                            gamma_c1,
                            &other.storage[outer].storage[inner],
                            &mut ctx,
                        );
                    }

                    // our "base" value for `aggregated_lookup_columns` already contains a term 1 * column_0,
                    // so we just add

                    unsafe {
                        std::sync::Arc::get_mut_unchecked(
                            &mut aggregated_lookup_columns_c0.storage[outer],
                        )
                        .storage[inner]
                            .add_assign(&tmp_c0, &mut ctx);
                    };

                    unsafe {
                        std::sync::Arc::get_mut_unchecked(
                            &mut aggregated_lookup_columns_c1.storage[outer],
                        )
                        .storage[inner]
                            .add_assign(&tmp_c1, &mut ctx);
                    };

                    lde_iter.advance();
                }
            });
        }
    });

    // now we can compute each term the same way, but identifying contributions
    let witness_encoding_poly_powers_of_alpha = &alphas[..num_subarguments];
    assert_eq!(
        witness_encoding_poly_powers_of_alpha.len(),
        variables_columns_for_lookup
            .chunks_exact(column_elements_per_subargument)
            .len()
    );

    for (idx, (alpha, vars_chunk)) in witness_encoding_poly_powers_of_alpha
        .iter()
        .zip(variables_columns_for_lookup.chunks_exact(column_elements_per_subargument))
        .enumerate()
    {
        let alpha_c0 = P::constant(alpha.coeffs[0], ctx);
        let alpha_c1 = P::constant(alpha.coeffs[1], ctx);

        // A(x) * (gamma^0 * column_0 + ... + gamma^n * column_n + beta) == lookup_selector
        let witness_encoding_poly_c0 =
            &second_stage.lookup_witness_encoding_polys[idx][0].subset_for_degree(quotient_degree);
        let witness_encoding_poly_c1 =
            &second_stage.lookup_witness_encoding_polys[idx][1].subset_for_degree(quotient_degree);

        let mut columns = Vec::with_capacity_in(capacity, B::default());
        for wit_column in vars_chunk.iter() {
            let subset = wit_column.subset_for_degree(quotient_degree);
            columns.push(subset);
        }

        if let Some(table_id_poly) = table_id_column_idxes.first().copied() {
            let subset = setup.constant_columns[table_id_poly].subset_for_degree(quotient_degree);
            columns.push(subset);
        }

        worker.scope(0, |scope, _| {
            // transpose other chunks
            for lde_iter in iterators.iter().cloned() {
                let mut lde_iter = lde_iter;
                let powers_of_gamma_c0 = &powers_of_gamma_c0[..];
                let powers_of_gamma_c1 = &powers_of_gamma_c1[..];
                let mut ctx = *ctx;
                let columns = &columns;
                assert_eq!(powers_of_gamma_c0.len(), columns.len());
                assert_eq!(powers_of_gamma_c1.len(), columns.len());

                let mut dst_c0 = dst_c0.clone(); // we use Arc, so it's the same instance
                let mut dst_c1 = dst_c1.clone(); // we use Arc, so it's the same instance
                scope.spawn(move |_| {
                    let one = P::one(&mut ctx);
                    for _ in 0..lde_iter.num_iterations() {
                        let (outer, inner) = lde_iter.current();
                        let mut tmp_c0 = beta_c0;
                        let mut tmp_c1 = beta_c1;

                        for ((gamma_c0, gamma_c1), other) in powers_of_gamma_c0
                            .iter()
                            .zip(powers_of_gamma_c1.iter())
                            .zip(columns.iter())
                        {
                            P::mul_and_accumulate_into(
                                &mut tmp_c0,
                                gamma_c0,
                                &other.storage[outer].storage[inner],
                                &mut ctx,
                            );

                            P::mul_and_accumulate_into(
                                &mut tmp_c1,
                                gamma_c1,
                                &other.storage[outer].storage[inner],
                                &mut ctx,
                            );
                        }
                        // mul by A(X)
                        mul_assign_vectorized_in_extension::<F, P, EXT>(
                            &mut tmp_c0,
                            &mut tmp_c1,
                            &witness_encoding_poly_c0.storage[outer].storage[inner],
                            &witness_encoding_poly_c1.storage[outer].storage[inner],
                            &mut ctx,
                        );

                        // subtract 1
                        tmp_c0.sub_assign(&one, &mut ctx);

                        // mul by alpha
                        mul_assign_vectorized_in_extension::<F, P, EXT>(
                            &mut tmp_c0,
                            &mut tmp_c1,
                            &alpha_c0,
                            &alpha_c1,
                            &mut ctx,
                        );

                        if crate::config::DEBUG_SATISFIABLE == true
                            && outer == 0
                            && tmp_c0.is_zero() == false
                        {
                            let mut normal_enumeration = inner.reverse_bits();
                            normal_enumeration >>= usize::BITS - domain_size.trailing_zeros();
                            panic!(
                                "A(x) term is invalid for index {} for subargument {}",
                                normal_enumeration, idx
                            );
                        }

                        // add into accumulator
                        unsafe {
                            std::sync::Arc::get_mut_unchecked(&mut dst_c0.storage[outer]).storage
                                [inner]
                                .add_assign(&tmp_c0, &mut ctx);
                        };
                        unsafe {
                            std::sync::Arc::get_mut_unchecked(&mut dst_c1.storage[outer]).storage
                                [inner]
                                .add_assign(&tmp_c1, &mut ctx);
                        };

                        lde_iter.advance();
                    }
                });
            }
        });
    }

    // now B poly
    let multiplicities_encoding_poly_powers_of_alpha = &alphas[num_subarguments..];
    assert_eq!(
        multiplicities_encoding_poly_powers_of_alpha.len(),
        num_multiplicities_polys
    );
    for (idx, alpha) in multiplicities_encoding_poly_powers_of_alpha
        .iter()
        .enumerate()
    {
        let alpha_c0 = P::constant(alpha.coeffs[0], ctx);
        let alpha_c1 = P::constant(alpha.coeffs[1], ctx);
        // B(x) * (gamma^0 * column_0 + ... + gamma^n * column_n + beta) == multiplicity column
        let multiplicities_encoding_poly_c0 = &second_stage.lookup_multiplicities_encoding_polys
            [idx][0]
            .subset_for_degree(quotient_degree);
        let multiplicities_encoding_poly_c1 = &second_stage.lookup_multiplicities_encoding_polys
            [idx][1]
            .subset_for_degree(quotient_degree);
        // columns are precomputed, so we need multiplicity
        let multiplicity =
            witness.lookup_multiplicities_polys[idx].subset_for_degree(quotient_degree);
        worker.scope(0, |scope, _| {
            // transpose other chunks
            for lde_iter in iterators.iter().cloned() {
                let mut lde_iter = lde_iter;
                let mut ctx = *ctx;
                let mut dst_c0 = dst_c0.clone(); // we use Arc, so it's the same instance
                let mut dst_c1 = dst_c1.clone(); // we use Arc, so it's the same instance
                let multiplicity = &multiplicity;
                let aggregated_lookup_columns_c0 = &aggregated_lookup_columns_c0;
                let aggregated_lookup_columns_c1 = &aggregated_lookup_columns_c1;
                scope.spawn(move |_| {
                    for _ in 0..lde_iter.num_iterations() {
                        let (outer, inner) = lde_iter.current();
                        let mut tmp_c0 = aggregated_lookup_columns_c0.storage[outer].storage[inner];
                        let mut tmp_c1 = aggregated_lookup_columns_c1.storage[outer].storage[inner];
                        // mul by B(X)
                        mul_assign_vectorized_in_extension::<F, P, EXT>(
                            &mut tmp_c0,
                            &mut tmp_c1,
                            &multiplicities_encoding_poly_c0.storage[outer].storage[inner],
                            &multiplicities_encoding_poly_c1.storage[outer].storage[inner],
                            &mut ctx,
                        );

                        // subtract multiplicity
                        tmp_c0.sub_assign(&multiplicity.storage[outer].storage[inner], &mut ctx);

                        // mul by alpha
                        mul_assign_vectorized_in_extension::<F, P, EXT>(
                            &mut tmp_c0,
                            &mut tmp_c1,
                            &alpha_c0,
                            &alpha_c1,
                            &mut ctx,
                        );

                        if crate::config::DEBUG_SATISFIABLE == true
                            && outer == 0
                            && tmp_c0.is_zero() == false
                        {
                            let mut normal_enumeration = inner.reverse_bits();
                            normal_enumeration >>= usize::BITS - domain_size.trailing_zeros();
                            panic!(
                                "B(x) term is invalid for index {} for subargument {}",
                                normal_enumeration, idx
                            );
                        }

                        // add into accumulator
                        unsafe {
                            std::sync::Arc::get_mut_unchecked(&mut dst_c0.storage[outer]).storage
                                [inner]
                                .add_assign(&tmp_c0, &mut ctx);
                        };
                        unsafe {
                            std::sync::Arc::get_mut_unchecked(&mut dst_c1.storage[outer]).storage
                                [inner]
                                .add_assign(&tmp_c1, &mut ctx);
                        };

                        lde_iter.advance();
                    }
                });
            }
        });
    }
}
