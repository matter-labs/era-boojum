use super::*;

use crate::cs::implementations::polynomial::LagrangeForm;
use crate::cs::traits::GoodAllocator;
use crate::fft::bitreverse_enumeration_inplace;
use crate::field::traits::field_like::mul_assign_in_extension;
use crate::field::traits::field_like::PrimeFieldLikeVectorized;
use crate::field::ExtensionField;
use crate::field::{FieldExtension, PrimeField};
use crate::utils::*;
use std::sync::Arc;

pub fn domain_generator_for_size<F: PrimeField>(size: u64) -> F {
    debug_assert!(size.is_power_of_two());
    debug_assert!(size.trailing_zeros() as usize <= F::TWO_ADICITY);

    let mut omega = F::radix_2_subgroup_generator();
    for _ in size.trailing_zeros()..(F::TWO_ADICITY as u32) {
        omega.square();
        if size != 1 {
            assert_ne!(omega, F::ONE);
        }
    }

    assert_eq!(omega.pow_u64(size), F::ONE);

    omega
}

// Explicitly NOT vectorized!
pub fn materialize_powers_serial<F: PrimeField, A: GoodAllocator>(
    base: F,
    size: usize,
) -> Vec<F, A> {
    if size == 0 {
        return Vec::new_in(A::default());
    }
    let mut storage = Vec::with_capacity_in(size, A::default());
    let mut current = F::ONE;
    storage.push(current);
    for _ in 1..size {
        current.mul_assign(&base);
        storage.push(current);
    }

    storage
}

pub(crate) fn materialize_powers_parallel<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
>(
    base: F,
    size: usize,
    worker: &Worker,
) -> Vec<F, A> {
    if size == 0 {
        return Vec::new_in(A::default());
    }
    assert!(
        size.is_power_of_two(),
        "due to requirement on size and alignment we only allow powers of two sizes, but got {}",
        size
    );
    let size = std::cmp::max(size, P::SIZE_FACTOR);
    let mut storage = utils::allocate_in_with_alignment_of::<F, P, A>(size, A::default());
    worker.scope(size, |scope, chunk_size| {
        for (chunk_idx, chunk) in storage.spare_capacity_mut()[..size]
            .chunks_mut(chunk_size)
            .enumerate()
        {
            scope.spawn(move |_| {
                let mut current = base.pow_u64((chunk_idx * chunk_size) as u64);
                for el in chunk.iter_mut() {
                    el.write(current);
                    current.mul_assign(&base);
                }
            });
        }
    });

    unsafe { storage.set_len(size) }

    storage
}

pub fn precompute_twiddles_for_fft<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    const INVERSED: bool,
>(
    fft_size: usize,
    worker: &Worker,
    _ctx: &mut P::Context,
) -> Vec<P, A> {
    debug_assert!(fft_size.is_power_of_two());

    let mut omega = domain_generator_for_size::<F>(fft_size as u64);
    if INVERSED {
        omega = omega
            .inverse()
            .expect("must always exist for domain generator");
    }

    assert_eq!(omega.pow_u64(fft_size as u64), F::ONE);
    for i in 1..fft_size {
        assert_ne!(omega.pow_u64(i as u64), F::ONE);
    }

    let num_powers = fft_size / 2;
    // MixedGL can have up to 16 elements, depending on implementation, so we can't
    // have less than that.
    let mut powers = materialize_powers_parallel::<F, P, A>(
        omega,
        std::cmp::max(num_powers, P::SIZE_FACTOR),
        worker,
    );

    // Items beyond `num_powers` are dead weight.
    bitreverse_enumeration_inplace(&mut powers[0..num_powers]);

    P::vec_from_base_vec(powers)
}

pub fn precompute_twiddles_for_fft_natural<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    const INVERSED: bool,
>(
    fft_size: usize,
    worker: &Worker,
    _ctx: P::Context,
) -> Vec<P, A> {
    debug_assert!(fft_size.is_power_of_two());

    let mut omega = domain_generator_for_size::<F>(fft_size as u64);
    if INVERSED {
        omega = omega
            .inverse()
            .expect("must always exist for domain generator");
    }

    assert_eq!(omega.pow_u64(fft_size as u64), F::ONE);
    for i in 1..fft_size {
        assert_ne!(omega.pow_u64(i as u64), F::ONE);
    }

    let num_powers = fft_size / 2;
    let powers = materialize_powers_parallel::<F, P, A>(omega, num_powers, worker);

    P::vec_from_base_vec(powers)
}

use crate::cs::implementations::polynomial::lde::ArcGenericLdeStorage;
use crate::cs::implementations::polynomial::*;

pub(crate) fn transform_from_trace_to_lde<
    F: SmallField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    trace_columns: Vec<Polynomial<F, LagrangeForm, A>, B>,
    lde_degree: usize,
    inverse_twiddles: &P::InverseTwiddles<A>,
    forward_twiddles: &P::Twiddles<A>,
    worker: &Worker,
    ctx: &mut P::Context,
) -> Vec<ArcGenericLdeStorage<F, P, A, B>, B> {
    if trace_columns.len() == 0 {
        return Vec::new_in(B::default());
    }

    let domain_size = trace_columns[0].domain_size();

    let mut raw_storage = Vec::with_capacity_in(trace_columns.len(), B::default());
    for el in trace_columns.into_iter() {
        raw_storage.push(P::vec_from_base_vec(el.into_storage()));
    }

    transform_raw_storages_to_lde(
        raw_storage,
        domain_size,
        lde_degree,
        inverse_twiddles,
        forward_twiddles,
        worker,
        ctx,
    )
}

pub(crate) fn transform_from_arcs_to_lde<
    F: SmallField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    trace_columns: Vec<Arc<Polynomial<F, LagrangeForm, A>>, B>,
    lde_degree: usize,
    inverse_twiddles: &P::InverseTwiddles<A>,
    forward_twiddles: &P::Twiddles<A>,
    worker: &Worker,
    ctx: &mut P::Context,
) -> Vec<ArcGenericLdeStorage<F, P, A, B>, B> {
    if trace_columns.len() == 0 {
        return Vec::new_in(B::default());
    }

    let domain_size = trace_columns[0].domain_size();

    let mut raw_storage = Vec::with_capacity_in(trace_columns.len(), B::default());
    for el in trace_columns.into_iter() {
        raw_storage.push(P::vec_from_base_vec((*el).clone().into_storage()));
    }

    transform_raw_storages_to_lde(
        raw_storage,
        domain_size,
        lde_degree,
        inverse_twiddles,
        forward_twiddles,
        worker,
        ctx,
    )
}

pub(crate) fn transform_from_arcs_to_lde_ext<
    F: SmallField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    trace_columns: Vec<Arc<GenericPolynomial<F, LagrangeForm, P, A>>, B>,
    lde_degree: usize,
    inverse_twiddles: &P::InverseTwiddles<A>,
    forward_twiddles: &P::Twiddles<A>,
    worker: &Worker,
    ctx: &mut P::Context,
) -> Vec<ArcGenericLdeStorage<F, P, A, B>, B> {
    if trace_columns.len() == 0 {
        return Vec::new_in(B::default());
    }

    let domain_size = trace_columns[0].domain_size();

    let mut raw_storage = Vec::with_capacity_in(trace_columns.len(), B::default());
    for el in trace_columns.into_iter() {
        let owned_copy: GenericPolynomial<F, LagrangeForm, P, A> = Clone::clone(&*el);
        raw_storage.push(owned_copy.into_storage());
    }

    let result = transform_raw_storages_to_lde(
        raw_storage,
        domain_size,
        lde_degree,
        inverse_twiddles,
        forward_twiddles,
        worker,
        ctx,
    );

    result
}

// use crate::field::traits::field_like::PrimeFieldLikeVectorized;

pub(crate) fn transform_raw_storages_to_lde<
    F: SmallField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    trace_columns: Vec<Vec<P, A>, B>,
    domain_size: usize,
    lde_degree: usize,
    inverse_twiddles: &P::InverseTwiddles<A>,
    forward_twiddles: &P::Twiddles<A>,
    worker: &Worker,
    ctx: &mut P::Context,
) -> Vec<ArcGenericLdeStorage<F, P, A, B>, B> {
    assert!(lde_degree.is_power_of_two());
    assert!(lde_degree > 1);

    debug_assert_eq!(domain_size, trace_columns[0].len() * P::SIZE_FACTOR);

    let _num_polys = trace_columns.len();

    let _now = std::time::Instant::now();

    // IFFT to get monomial form
    let mut jobs: Vec<Vec<P, A>, B> = trace_columns;
    worker.scope(jobs.len(), |scope, chunk_size| {
        for chunk in jobs.chunks_mut(chunk_size) {
            let mut ctx = *ctx;
            scope.spawn(move |_| {
                for poly in chunk.iter_mut() {
                    P::ifft_natural_to_natural(poly, F::ONE, inverse_twiddles, &mut ctx);
                }
            });
        }
    });

    // log!("{} iFFTs taken {:?}", num_polys, now.elapsed());

    transform_monomials_to_lde(jobs, domain_size, lde_degree, forward_twiddles, worker, ctx)
}

pub(crate) fn transform_monomials_to_lde<
    F: SmallField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    trace_columns: Vec<Vec<P, A>, B>,
    domain_size: usize,
    lde_degree: usize,
    forward_twiddles: &P::Twiddles<A>,
    worker: &Worker,
    ctx: &mut P::Context,
) -> Vec<ArcGenericLdeStorage<F, P, A, B>, B> {
    assert!(lde_degree.is_power_of_two());
    assert!(lde_degree > 1);

    profile_fn!(transform_monomials_to_lde);
    profile_section!(determine_properties);
    let num_polys = trace_columns.len();

    debug_assert_eq!(domain_size, trace_columns[0].len() * P::SIZE_FACTOR);

    let lde_size = domain_size * lde_degree;
    let coset = domain_generator_for_size::<F>(lde_size as u64);
    debug_assert!({
        let outer_omega = domain_generator_for_size::<F>(domain_size as u64);
        let tmp = coset.pow_u64(lde_degree as u64);

        outer_omega == tmp
    });

    let multiplicative_generator = F::multiplicative_generator();

    // now all polys are in the Monomial form, so let's LDE them
    let mut powers_of_coset = materialize_powers_serial::<F, A>(coset, lde_degree);
    bitreverse_enumeration_inplace(&mut powers_of_coset);
    let powers_of_coset_ref = &powers_of_coset[..];

    drop(determine_properties);
    profile_section!(extend_vecs);
    let _now = std::time::Instant::now();

    let jobs_per_coset = trace_columns.len();
    // we will create a temporary placeholder of vectors for more even CPU load
    let mut all_ldes = Vec::with_capacity_in(trace_columns.len() * lde_degree, B::default());
    for _ in 0..(lde_degree - 1) {
        all_ldes.extend_from_slice(&trace_columns);
    }
    all_ldes.extend(trace_columns);

    drop(extend_vecs);
    profile_section!(do_work);
    worker.scope(all_ldes.len(), |scope, chunk_size| {
        for (chunk_idx, chunk) in all_ldes.chunks_mut(chunk_size).enumerate() {
            let mut ctx = *ctx;
            scope.spawn(move |_| {
                for (idx, poly) in chunk.iter_mut().enumerate() {
                    let poly_idx = chunk_idx * chunk_size + idx;
                    let coset_idx = poly_idx / jobs_per_coset;
                    let mut coset = powers_of_coset_ref[coset_idx];
                    if crate::config::DEBUG_SATISFIABLE == false {
                        coset.mul_assign(&multiplicative_generator);
                    }
                    debug_assert!(poly.as_ptr().addr() % std::mem::align_of::<P>() == 0);
                    P::fft_natural_to_bitreversed(poly, coset, forward_twiddles, &mut ctx);
                }
            });
        }
    });

    drop(do_work);
    profile_section!(finalize);
    // transpose them back. In "all_ldes" we have first coset for every poly, then next one for every, etc
    // and we need to place them into individual cosets for into poly

    let mut columns = Vec::with_capacity_in(num_polys, B::default());
    columns.resize(
        num_polys,
        ArcGenericLdeStorage::empty_with_capacity_in(lde_degree, B::default()),
    );

    for (idx, el) in all_ldes.into_iter().enumerate() {
        let dst_poly_idx = idx % num_polys;
        let as_polynomial = GenericPolynomial::from_storage(el);
        columns[dst_poly_idx]
            .storage
            .push(std::sync::Arc::new(as_polynomial));
    }

    // log!("{} LDEs of degree {} taken {:?}", num_polys, lde_degree, now.elapsed());

    columns
}

pub(crate) fn batch_inverse<F: PrimeField, A: GoodAllocator>(input: &[F], into: &mut Vec<F, A>) {
    debug_assert!(into.is_empty());

    if input.is_empty() {
        return;
    }

    // we do Montgomery batch inversion trick, and reuse a buffer
    let one = F::ONE;
    into.push(one);
    let mut accumulator = input[0];
    for el in input[1..].iter() {
        into.push(accumulator);
        accumulator.mul_assign(el);
    }

    // for a set of a, b, c, d we have
    // - input = [1, a, ab, abc],
    // - accumulator = abcd

    let mut grand_inverse = accumulator
        .inverse()
        .expect("batch inverse must be called on sets without zeroes");

    // grand_inverse = a^-1 b^-1 c^-1 d^-1

    for (dst, original) in into.iter_mut().rev().zip(input.iter().rev()) {
        dst.mul_assign(&grand_inverse); // e.g it's now d^-1
        grand_inverse.mul_assign(original); // e.g. it's now a^-1 b^-1 c^-1
    }

    debug_assert_eq!(into.len(), input.len());
}

pub(crate) fn batch_inverse_inplace<F: PrimeField, A: GoodAllocator>(input: &mut [F]) {
    if input.is_empty() {
        return;
    }

    let mut into = Vec::with_capacity_in(input.len(), A::default());

    // we do Montgomery batch inversion trick, and reuse a buffer
    let one = F::ONE;
    into.push(one);
    let mut accumulator = input[0];
    for el in input[1..].iter() {
        into.push(accumulator);
        accumulator.mul_assign(el);
    }

    // for a set of a, b, c, d we have
    // - input = [1, a, ab, abc],
    // - accumulator = abcd

    let mut grand_inverse = accumulator
        .inverse()
        .expect("batch inverse must be called on sets without zeroes");

    // grand_inverse = a^-1 b^-1 c^-1 d^-1

    for (tmp, original) in into.into_iter().rev().zip(input.iter_mut().rev()) {
        let mut tmp = tmp; // abc
        tmp.mul_assign(&grand_inverse); // d^-1
        grand_inverse.mul_assign(original); // e.g. it's now a^-1 b^-1 c^-1

        *original = tmp;
    }
}

pub(crate) fn batch_inverse_in_extension<
    F: PrimeField,
    EXT: FieldExtension<2, BaseField = F>,
    A: GoodAllocator,
>(
    input_c0: &[F],
    input_c1: &[F],
    into_c0: &mut Vec<F, A>,
    into_c1: &mut Vec<F, A>,
) {
    assert!(into_c0.is_empty());
    assert!(into_c1.is_empty());

    assert_eq!(input_c0.len(), input_c1.len());

    if input_c0.is_empty() {
        return;
    }

    // we do Montgomery batch inversion trick, and reuse a buffer
    let one = {
        use crate::field::traits::field::Field;

        ExtensionField::<F, 2, EXT>::ONE
    };
    into_c0.push(one.coeffs[0]);
    into_c1.push(one.coeffs[1]);
    let mut accumulator =
        ExtensionField::<F, 2, EXT>::from_coeff_in_base([input_c0[0], input_c1[0]]);
    for (el_c0, el_c1) in input_c0[1..].iter().zip(input_c1[1..].iter()) {
        into_c0.push(accumulator.coeffs[0]);
        into_c1.push(accumulator.coeffs[1]);

        let el = ExtensionField::<F, 2, EXT>::from_coeff_in_base([*el_c0, *el_c1]);
        crate::field::Field::mul_assign(&mut accumulator, &el);
    }

    // for a set of a, b, c, d we have
    // - input = [1, a, ab, abc],
    // - accumulator = abcd

    let mut grand_inverse = accumulator
        .inverse()
        .expect("batch inverse must be called on sets without zeroes");

    // grand_inverse = a^-1 b^-1 c^-1 d^-1

    for (((tmp_c0, tmp_c1), original_c0), original_c1) in into_c0
        .iter_mut()
        .rev()
        .zip(into_c1.iter_mut().rev())
        .zip(input_c0.iter().rev())
        .zip(input_c1.iter().rev())
    {
        let mut tmp = ExtensionField::<F, 2, EXT>::from_coeff_in_base([*tmp_c0, *tmp_c1]); // abc
        crate::field::Field::mul_assign(&mut tmp, &grand_inverse); // d^-1

        // write back
        *tmp_c0 = tmp.coeffs[0];
        *tmp_c1 = tmp.coeffs[1];

        let original =
            ExtensionField::<F, 2, EXT>::from_coeff_in_base([*original_c0, *original_c1]);
        crate::field::Field::mul_assign(&mut grand_inverse, &original); // e.g. it's now a^-1 b^-1 c^-1
    }

    assert_eq!(input_c0.len(), into_c0.len());
    assert_eq!(input_c1.len(), into_c1.len());
}

pub(crate) fn batch_inverse_inplace_in_extension<
    F: PrimeField,
    EXT: FieldExtension<2, BaseField = F>,
    A: GoodAllocator,
>(
    input_c0: &mut [F],
    input_c1: &mut [F],
) {
    assert_eq!(input_c0.len(), input_c1.len());

    if input_c0.is_empty() {
        return;
    }

    let mut into = Vec::with_capacity_in(input_c0.len(), A::default());

    // we do Montgomery batch inversion trick, and reuse a buffer
    let one = {
        use crate::field::traits::field::Field;

        ExtensionField::<F, 2, EXT>::ONE
    };
    into.push(one);
    let mut accumulator =
        ExtensionField::<F, 2, EXT>::from_coeff_in_base([input_c0[0], input_c1[0]]);
    for (el_c0, el_c1) in input_c0[1..].iter().zip(input_c1[1..].iter()) {
        into.push(accumulator);
        let el = ExtensionField::<F, 2, EXT>::from_coeff_in_base([*el_c0, *el_c1]);
        crate::field::Field::mul_assign(&mut accumulator, &el);
    }

    // for a set of a, b, c, d we have
    // - input = [1, a, ab, abc],
    // - accumulator = abcd

    let mut grand_inverse = accumulator
        .inverse()
        .expect("batch inverse must be called on sets without zeroes");

    // grand_inverse = a^-1 b^-1 c^-1 d^-1

    for ((tmp, original_c0), original_c1) in into
        .into_iter()
        .rev()
        .zip(input_c0.iter_mut().rev())
        .zip(input_c1.iter_mut().rev())
    {
        let mut tmp = tmp; // abc
        crate::field::Field::mul_assign(&mut tmp, &grand_inverse); // d^-1
        let original =
            ExtensionField::<F, 2, EXT>::from_coeff_in_base([*original_c0, *original_c1]);
        crate::field::Field::mul_assign(&mut grand_inverse, &original); // e.g. it's now a^-1 b^-1 c^-1

        *original_c0 = tmp.coeffs[0];
        *original_c1 = tmp.coeffs[1];
    }
}

pub(crate) fn batch_inverse_inplace_parallel<F: PrimeField, A: GoodAllocator>(
    input: &mut [F],
    worker: &Worker,
) {
    worker.scope(input.len(), |scope, chunk_size| {
        for dst in input.chunks_mut(chunk_size) {
            scope.spawn(move |_| {
                batch_inverse_inplace::<F, A>(dst);
            });
        }
    });
}

pub(crate) fn batch_inverse_inplace_parallel_in_extension<
    F: PrimeField,
    EXT: FieldExtension<2, BaseField = F>,
    A: GoodAllocator,
>(
    input_c0: &mut [F],
    input_c1: &mut [F],
    worker: &Worker,
) {
    worker.scope(input_c0.len(), |scope, chunk_size| {
        for (dst_c0, dst_c1) in input_c0
            .chunks_mut(chunk_size)
            .zip(input_c1.chunks_mut(chunk_size))
        {
            scope.spawn(move |_| {
                batch_inverse_inplace_in_extension::<F, EXT, A>(dst_c0, dst_c1);
            });
        }
    });
}

pub fn make_non_residues<F: PrimeField>(num: usize, domain_size: usize) -> Vec<F> {
    assert!(domain_size.is_power_of_two());
    assert!(domain_size <= u64::MAX as usize);
    use crate::field::LegendreSymbol;

    // we need to check that
    // - some k is not a residue
    // - it's NOT a part of coset formed as other_k * {1, omega^1, ...}

    // latter is just a * omega^i == b * omega^j, so a/b == omega^{j-i},
    // and then (a / b) ^ domain_size == 1

    let mut non_residues: Vec<F> = Vec::with_capacity(num);
    let mut current = F::ONE;
    let one = F::ONE;
    for _ in 0..num {
        'outer: loop {
            current.add_assign(&one);

            if current.legendre() != LegendreSymbol::QuadraticNonResidue {
                // try another one
            } else {
                // it's not a square, so let's
                let mut is_unique = true;
                {
                    // first pow into the domain size
                    let tmp = current.pow_u64(domain_size as u64);
                    if tmp == F::ONE {
                        // we hit the domain
                        continue;
                    }
                    // then check: if it's in some other coset, then
                    // X^N == other_k ^ N
                    for t in non_residues.iter() {
                        if !is_unique {
                            break;
                        }
                        let t_in_domain_size = t.pow_u64(domain_size as u64);
                        if tmp == t_in_domain_size {
                            is_unique = false;
                        }
                    }
                }
                if is_unique {
                    non_residues.push(current);
                    break 'outer;
                }
            }
        }
    }

    non_residues
}

pub(crate) fn materialize_x_poly<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
>(
    size: usize,
    worker: &Worker,
) -> GenericPolynomial<F, LagrangeForm, P, A> {
    debug_assert!(size.is_power_of_two());
    let mut storage = allocate_in_with_alignment_of::<F, P, A>(size, A::default());
    let omega = domain_generator_for_size::<F>(size as u64);
    worker.scope(size, |scope, chunk_size| {
        for (chunk_idx, chunk) in storage.spare_capacity_mut()[..size]
            .chunks_mut(chunk_size)
            .enumerate()
        {
            scope.spawn(move |_| {
                let mut current = omega.pow_u64((chunk_idx * chunk_size) as u64);
                for el in chunk.iter_mut() {
                    el.write(current);
                    current.mul_assign(&omega);
                }
            });
        }
    });

    unsafe { storage.set_len(size) };

    let storage = P::vec_from_base_vec(storage);

    GenericPolynomial::from_storage(storage)
}

pub(crate) fn materialize_x_poly_as_arc_lde<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    domain_size: usize,
    lde_degree: usize,
    coset: F,
    worker: &Worker,
    ctx: &mut P::Context,
) -> ArcGenericLdeStorage<F, P, A, B> {
    let x_poly = materialize_x_poly::<F, P, A>(domain_size, worker).into_storage();
    let mut x_poly = P::vec_into_base_vec(x_poly);
    bitreverse_enumeration_inplace(&mut x_poly);
    let x_poly = P::vec_from_base_vec(x_poly);

    let lde_generator = domain_generator_for_size::<F>((domain_size * lde_degree) as u64);
    let mut lde_generators = materialize_powers_serial::<F, B>(lde_generator, lde_degree);
    bitreverse_enumeration_inplace(&mut lde_generators);

    let mut result = ArcGenericLdeStorage::empty_with_capacity_in(lde_degree, B::default());

    for lde_generator in lde_generators.into_iter() {
        let mut dst = x_poly.clone();
        let mut ctx = *ctx;
        worker.scope(dst.len(), |scope, chunk_size| {
            for dst in dst.chunks_mut(chunk_size) {
                scope.spawn(move |_| {
                    let mut multiplier = lde_generator;
                    multiplier.mul_assign(&coset);
                    let multiplier = P::constant(multiplier, &mut ctx);
                    for dst in dst.iter_mut() {
                        dst.mul_assign(&multiplier, &mut ctx);
                    }
                });
            }
        });

        result
            .storage
            .push(std::sync::Arc::new(GenericPolynomial::from_storage(dst)));
    }

    result
}

pub(crate) fn divide_by_vanishing_for_bitreversed_coset_enumeration<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    presumably_bitreversed_lde_chunks: &mut Vec<Vec<P, A>, B>,
    worker: &Worker,
    ctx: &mut P::Context,
) {
    // we have a vanishing poly z^inner_domain_size - 1,
    // evaluated at mul_gen * gamma^i x {1, omega, omega^2, ...} where omega^inner_domain_size == 1,
    // so we only need mul_gen^n * gamma^{i * n} - 1

    let inner_domain_size = presumably_bitreversed_lde_chunks[0].len() * P::SIZE_FACTOR;
    let outer_size = presumably_bitreversed_lde_chunks.len();
    let full_domain_size = outer_size * inner_domain_size;

    let coset = domain_generator_for_size::<F>(full_domain_size as u64);
    let coset_in_n = coset.pow_u64(inner_domain_size as u64);
    debug_assert!({ coset_in_n.pow_u64(outer_size as u64) == F::ONE });
    let multiplicative_gen_in_n = F::multiplicative_generator().pow_u64(inner_domain_size as u64);
    let mut powers_of_coset = materialize_powers_serial::<F, B>(coset_in_n, outer_size);
    for el in powers_of_coset.iter_mut() {
        el.mul_assign(&multiplicative_gen_in_n);
        el.sub_assign(&F::ONE);
    }
    bitreverse_enumeration_inplace(&mut powers_of_coset);
    let mut inverses = Vec::with_capacity_in(outer_size, B::default());
    batch_inverse(&powers_of_coset, &mut inverses);

    for (dst, multiplier) in presumably_bitreversed_lde_chunks
        .iter_mut()
        .zip(inverses.into_iter())
    {
        let multiplier = P::constant(multiplier, ctx);
        worker.scope(dst.len(), |scope, chunk_size| {
            let mut ctx = *ctx;
            for dst in dst.chunks_mut(chunk_size) {
                scope.spawn(move |_| {
                    for dst in dst.iter_mut() {
                        dst.mul_assign(&multiplier, &mut ctx);
                    }
                })
            }
        });
    }
}

// precompute values useful for barycentric evaluation
pub fn precompute_for_barycentric_evaluation<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
>(
    n: usize,
    coset: F,
    at: F,
    worker: &Worker,
    ctx: &mut P::Context,
) -> Vec<P, A> {
    if n == 1 {
        let mut result = Vec::with_capacity_in(1, A::default());
        result.push(P::one(ctx));

        return result;
    }

    // L_i(X) = (omega^i / N) / (X - omega^i) * (X^N - 1)

    // if case of coset we can have (coset * omega^i / N) / (X - coset * omega^i) * (X^N - coset^N)

    // constant factor = coset * (X^N - coset^N) / n

    let t = coset.pow_u64(n as u64);
    let mut constant_factor = at.pow_u64(n as u64);
    constant_factor.sub_assign(&t);
    constant_factor.mul_assign(&coset);

    let mut t = t;
    t.mul_assign(&F::from_u64_with_reduction(n as u64));
    constant_factor.mul_assign(
        &t.inverse()
            .expect("inverse of domain size by mul generator must exist"),
    );

    // compute vector of (X - coset * omega^i)

    let mut storage = allocate_in_with_alignment_of::<F, P, A>(n, A::default());
    let omega = domain_generator_for_size::<F>(n as u64);
    worker.scope(n, |scope, chunk_size| {
        for (chunk_idx, chunk) in storage.spare_capacity_mut()[..n]
            .chunks_mut(chunk_size)
            .enumerate()
        {
            scope.spawn(move |_| {
                let mut current = omega.pow_u64((chunk_idx * chunk_size) as u64);
                current.mul_assign(&coset);
                for el in chunk.iter_mut() {
                    // X - coset * omega^i
                    let mut tmp = at;
                    tmp.sub_assign(&current);
                    el.write(tmp);
                    current.mul_assign(&omega);
                }
            });
        }
    });

    unsafe { storage.set_len(n) };

    let mut result = allocate_in_with_alignment_of::<F, P, A>(n, A::default());
    batch_inverse(&storage, &mut result);

    drop(storage);

    // * omega^i * constant_factor

    worker.scope(result.len(), |scope, chunk_size| {
        for (chunk_idx, chunk) in result.chunks_mut(chunk_size).enumerate() {
            scope.spawn(move |_| {
                let mut current = omega.pow_u64((chunk_idx * chunk_size) as u64);
                current.mul_assign(&constant_factor);
                for el in chunk.iter_mut() {
                    el.mul_assign(&current);
                    current.mul_assign(&omega);
                }
            });
        }
    });

    bitreverse_enumeration_inplace(&mut result);

    P::vec_from_base_vec(result)
}

// precompute values useful for barycentric evaluation
pub fn precompute_for_barycentric_evaluation_in_extension<
    F: PrimeField,
    EXT: FieldExtension<2, BaseField = F>,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
>(
    n: usize,
    coset: F,
    at: ExtensionField<F, 2, EXT>,
    worker: &Worker,
    ctx: &mut P::Context,
) -> [Vec<P, A>; 2] {
    if n == 1 {
        let mut result_c0 = Vec::with_capacity_in(1, A::default());
        result_c0.push(P::one(ctx));

        let mut result_c1 = Vec::with_capacity_in(1, A::default());
        result_c1.push(P::zero(ctx));

        return [result_c0, result_c1];
    }

    // L_i(X) = (omega^i / N) / (X - omega^i) * (X^N - 1)

    // if case of coset we can have (coset * omega^i / N) / (X - coset * omega^i) * (X^N - coset^N)

    // constant factor = coset * (X^N - coset^N) / N

    let t = coset.pow_u64(n as u64);
    let mut constant_factor = crate::field::Field::pow_u64(&at, n as u64);
    constant_factor.coeffs[0].sub_assign(&t);
    constant_factor.mul_assign_by_base(&coset);

    let mut t = t;
    t.mul_assign(&F::from_u64_with_reduction(n as u64));
    constant_factor.mul_assign_by_base(
        &t.inverse()
            .expect("inverse of domain size by mul generator must exist"),
    );

    // compute vector of (X - coset * omega^i)

    let mut storage_c0 = allocate_in_with_alignment_of::<F, P, A>(n, A::default());
    let mut storage_c1 = allocate_in_with_alignment_of::<F, P, A>(n, A::default());

    // because we only subtract c0, we can just fill it
    storage_c1.resize(n, at.coeffs[1]);

    let omega = domain_generator_for_size::<F>(n as u64);
    let at_c0 = at.coeffs[0];

    worker.scope(n, |scope, chunk_size| {
        for (chunk_idx, chunk_c0) in storage_c0.spare_capacity_mut()[..n]
            .chunks_mut(chunk_size)
            .enumerate()
        {
            scope.spawn(move |_| {
                let mut current = omega.pow_u64((chunk_idx * chunk_size) as u64);
                current.mul_assign(&coset);
                for el_c0 in chunk_c0.iter_mut() {
                    // X - coset * omega^i
                    let mut tmp_c0 = at_c0;
                    tmp_c0.sub_assign(&current);
                    el_c0.write(tmp_c0);
                    current.mul_assign(&omega);
                }
            });
        }
    });

    unsafe { storage_c0.set_len(n) };

    assert_eq!(storage_c0.len(), storage_c1.len());

    let mut result_c0 = storage_c0;
    let mut result_c1 = storage_c1;
    batch_inverse_inplace_parallel_in_extension::<F, EXT, A>(
        &mut result_c0,
        &mut result_c1,
        worker,
    );

    // * omega^i * constant_factor

    worker.scope(result_c0.len(), |scope, chunk_size| {
        for (chunk_idx, (chunk_c0, chunk_c1)) in result_c0
            .chunks_mut(chunk_size)
            .zip(result_c1.chunks_mut(chunk_size))
            .enumerate()
        {
            scope.spawn(move |_| {
                let mut current = constant_factor;
                current.mul_assign_by_base(&omega.pow_u64((chunk_idx * chunk_size) as u64));
                for (el_c0, el_c1) in chunk_c0.iter_mut().zip(chunk_c1.iter_mut()) {
                    mul_assign_in_extension::<F, EXT>(
                        el_c0,
                        el_c1,
                        &current.coeffs[0],
                        &current.coeffs[1],
                    );

                    current.mul_assign_by_base(&omega);
                }
            });
        }
    });

    bitreverse_enumeration_inplace(&mut result_c0);
    bitreverse_enumeration_inplace(&mut result_c1);

    [
        P::vec_from_base_vec(result_c0),
        P::vec_from_base_vec(result_c1),
    ]
}

// No parallelism here - we parallelize externally
// And we also don't use vectorized reduction yes
pub(crate) fn barycentric_evaluate_at_for_bitreversed<F: PrimeField>(
    values: &[F],
    precomputed_lagrange_poly_evals: &[F],
) -> F {
    debug_assert_eq!(values.len(), precomputed_lagrange_poly_evals.len());
    if values.len() == 1 {
        // evaluation is just a constant
        return values[0];
    };

    let mut result = F::ZERO;
    for (a, b) in values.iter().zip(precomputed_lagrange_poly_evals.iter()) {
        let mut tmp = *a;
        tmp.mul_assign(b);
        result.add_assign(&tmp);
    }

    result
}

pub(crate) fn barycentric_evaluate_at_for_bitreversed_parallel<F: PrimeField>(
    values: &[F],
    precomputed_lagrange_poly_evals: &[F],
    worker: &Worker,
) -> F {
    debug_assert_eq!(values.len(), precomputed_lagrange_poly_evals.len());
    if values.len() == 1 {
        // evaluation is just a constant
        return values[0];
    };

    let chunk_size = worker.get_chunk_size(values.len());
    let num_chunks = Worker::compute_num_chunks(values.len(), chunk_size);

    let mut chunk_evals = vec![F::ZERO; num_chunks];

    worker.scope(values.len(), |scope, chunk_size| {
        for ((a, b), dst) in values
            .chunks(chunk_size)
            .zip(precomputed_lagrange_poly_evals.chunks(chunk_size))
            .zip(chunk_evals.iter_mut())
        {
            scope.spawn(move |_| {
                for (a, b) in a.iter().zip(b.iter()) {
                    let mut tmp = *a;
                    tmp.mul_assign(b);
                    dst.add_assign(&tmp);
                }
            });
        }
    });

    let mut result = chunk_evals[0];
    for el in chunk_evals.into_iter().skip(1) {
        result.add_assign(&el);
    }

    result
}

pub(crate) fn barycentric_evaluate_base_at_extension_for_bitreversed_parallel<F: PrimeField>(
    values: &[F],
    precomputed_lagrange_poly_evals_c0: &[F],
    precomputed_lagrange_poly_evals_c1: &[F],
    worker: &Worker,
) -> [F; 2] {
    debug_assert_eq!(values.len(), precomputed_lagrange_poly_evals_c0.len());
    debug_assert_eq!(values.len(), precomputed_lagrange_poly_evals_c1.len());

    if values.len() == 1 {
        // evaluation is just a constant
        return [values[0], values[0]];
    };

    if values.len() < worker.num_cores {
        // do single thread
        let mut dst_c0 = F::ZERO;
        let mut dst_c1 = F::ZERO;
        for ((a, b_c0), b_c1) in values
            .iter()
            .zip(precomputed_lagrange_poly_evals_c0.iter())
            .zip(precomputed_lagrange_poly_evals_c1.iter())
        {
            let mut c0 = *b_c0;
            c0.mul_assign(a);
            let mut c1 = *b_c1;
            c1.mul_assign(a);

            dst_c0.add_assign(&c0);
            dst_c1.add_assign(&c1);
        }

        return [dst_c0, dst_c1];
    }

    let chunk_size = worker.get_chunk_size(values.len());
    let num_chunks = Worker::compute_num_chunks(values.len(), chunk_size);

    let mut chunk_evals_c0 = vec![F::ZERO; num_chunks];
    let mut chunk_evals_c1 = vec![F::ZERO; num_chunks];

    worker.scope(values.len(), |scope, chunk_size| {
        for ((((a, b_c0), b_c1), dst_c0), dst_c1) in values
            .chunks(chunk_size)
            .zip(precomputed_lagrange_poly_evals_c0.chunks(chunk_size))
            .zip(precomputed_lagrange_poly_evals_c1.chunks(chunk_size))
            .zip(chunk_evals_c0.iter_mut())
            .zip(chunk_evals_c1.iter_mut())
        {
            scope.spawn(move |_| {
                for ((a, b_c0), b_c1) in a.iter().zip(b_c0.iter()).zip(b_c1.iter()) {
                    let mut tmp = *a;
                    tmp.mul_assign(b_c0);
                    dst_c0.add_assign(&tmp);

                    let mut tmp = *a;
                    tmp.mul_assign(b_c1);
                    dst_c1.add_assign(&tmp);
                }
            });
        }
    });

    let mut result_c0 = chunk_evals_c0[0];
    let mut result_c1 = chunk_evals_c1[0];
    for el in chunk_evals_c0.into_iter().skip(1) {
        result_c0.add_assign(&el);
    }
    for el in chunk_evals_c1.into_iter().skip(1) {
        result_c1.add_assign(&el);
    }

    [result_c0, result_c1]
}

pub(crate) fn barycentric_evaluate_extension_at_extension_for_bitreversed_parallel<
    F: PrimeField,
    EXT: FieldExtension<2, BaseField = F>,
>(
    values_c0: &[F],
    values_c1: &[F],
    precomputed_lagrange_poly_evals_c0: &[F],
    precomputed_lagrange_poly_evals_c1: &[F],
    worker: &Worker,
) -> [F; 2] {
    debug_assert_eq!(values_c0.len(), precomputed_lagrange_poly_evals_c0.len());
    debug_assert_eq!(values_c0.len(), precomputed_lagrange_poly_evals_c1.len());
    debug_assert_eq!(values_c1.len(), precomputed_lagrange_poly_evals_c0.len());
    debug_assert_eq!(values_c1.len(), precomputed_lagrange_poly_evals_c1.len());

    if values_c0.len() == 1 {
        // evaluation is just a constant
        return [values_c0[0], values_c1[0]];
    };

    if values_c0.len() < worker.num_cores {
        // do single thread
        let mut dst_c0 = F::ZERO;
        let mut dst_c1 = F::ZERO;
        for (((a_c0, a_c1), b_c0), b_c1) in values_c0
            .iter()
            .zip(values_c1.iter())
            .zip(precomputed_lagrange_poly_evals_c0.iter())
            .zip(precomputed_lagrange_poly_evals_c1.iter())
        {
            let mut a_c0 = *a_c0;
            let mut a_c1 = *a_c1;
            mul_assign_in_extension::<F, EXT>(&mut a_c0, &mut a_c1, b_c0, b_c1);
            dst_c0.add_assign(&a_c0);
            dst_c1.add_assign(&a_c1);
        }

        return [dst_c0, dst_c1];
    }

    let chunk_size = worker.get_chunk_size(values_c0.len());
    let num_chunks = Worker::compute_num_chunks(values_c0.len(), chunk_size);

    let mut chunk_evals_c0 = vec![F::ZERO; num_chunks];
    let mut chunk_evals_c1 = vec![F::ZERO; num_chunks];

    worker.scope(values_c0.len(), |scope, chunk_size| {
        for (((((a_c0, a_c1), b_c0), b_c1), dst_c0), dst_c1) in values_c0
            .chunks(chunk_size)
            .zip(values_c1.chunks(chunk_size))
            .zip(precomputed_lagrange_poly_evals_c0.chunks(chunk_size))
            .zip(precomputed_lagrange_poly_evals_c1.chunks(chunk_size))
            .zip(chunk_evals_c0.iter_mut())
            .zip(chunk_evals_c1.iter_mut())
        {
            scope.spawn(move |_| {
                for (((a_c0, a_c1), b_c0), b_c1) in a_c0
                    .iter()
                    .zip(a_c1.iter())
                    .zip(b_c0.iter())
                    .zip(b_c1.iter())
                {
                    let mut a_c0 = *a_c0;
                    let mut a_c1 = *a_c1;
                    mul_assign_in_extension::<F, EXT>(&mut a_c0, &mut a_c1, b_c0, b_c1);
                    dst_c0.add_assign(&a_c0);
                    dst_c1.add_assign(&a_c1);
                }
            });
        }
    });

    let mut result_c0 = chunk_evals_c0[0];
    let mut result_c1 = chunk_evals_c1[0];
    for el in chunk_evals_c0.into_iter().skip(1) {
        result_c0.add_assign(&el);
    }
    for el in chunk_evals_c1.into_iter().skip(1) {
        result_c1.add_assign(&el);
    }

    [result_c0, result_c1]
}

// signature is over P to keep our alignment at bay
pub(crate) fn shift_by_omega_assuming_bitreversed<
    F: PrimeField,
    P: PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
>(
    input: &[P],
) -> Vec<P, A> {
    // brute force for now, but we carefully monitor the alignment
    let mut result = crate::utils::allocate_in_with_alignment_of::<F, P, A>(
        input.len() * P::SIZE_FACTOR,
        A::default(),
    );

    let mut tmp = Vec::with_capacity_in(input.len() * P::SIZE_FACTOR + 1, A::default());
    tmp.extend_from_slice(P::slice_into_base_slice(input));
    bitreverse_enumeration_inplace(&mut tmp);
    let first = tmp[0];
    tmp.push(first);

    result.extend_from_slice(&tmp[1..]);

    bitreverse_enumeration_inplace(&mut result);

    debug_assert_eq!(result.len(), input.len() * P::SIZE_FACTOR);

    P::vec_from_base_vec(result)
}

// a - b * c
pub(crate) fn fused_multiply_sub<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    a: ArcGenericLdeStorage<F, P, A, B>,
    b: ArcGenericLdeStorage<F, P, A, B>,
    c: ArcGenericLdeStorage<F, P, A, B>,
    worker: &Worker,
    ctx: &mut P::Context,
) -> ArcGenericLdeStorage<F, P, A, B> {
    debug_assert_eq!(a.inner_len(), b.inner_len());
    debug_assert_eq!(a.inner_len(), c.inner_len());

    debug_assert_eq!(a.outer_len(), b.outer_len());
    debug_assert_eq!(a.outer_len(), c.outer_len());

    let inner_size = a.inner_len();
    let outer_size = a.outer_len();
    let mut result =
        ArcGenericLdeStorage::uninit(inner_size, outer_size, A::default(), B::default());

    let iterators = a.compute_chunks_for_num_workers(worker.num_cores);

    worker.scope(0, |scope, _| {
        for iterator in iterators.into_iter() {
            let mut result = result.clone();
            let a = a.clone();
            let b = b.clone();
            let c = c.clone();
            let mut ctx = *ctx;
            scope.spawn(move |_| {
                let num_iterations = iterator.num_iterations();
                let mut iterator = iterator;
                for _ in 0..num_iterations {
                    let (outer, inner) = iterator.current();

                    let mut t = b.storage[outer].storage[inner];
                    t.mul_assign(&(&c.storage[outer].storage)[inner], &mut ctx);

                    let mut r = a.storage[outer].storage[inner];
                    r.sub_assign(&t, &mut ctx);

                    unsafe { Arc::get_mut_unchecked(&mut result.storage[outer]) }
                        .storage
                        .spare_capacity_mut()[inner]
                        .write(r);

                    iterator.advance();
                }
            });
        }
    });

    unsafe { result.assume_init(inner_size) };

    result
}

// DST must be initialized here
pub(crate) fn apply_binop_into<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    OP: Binop<P, P::Context>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    dst: &mut ArcGenericLdeStorage<F, P, A, B>,
    a: ArcGenericLdeStorage<F, P, A, B>,
    b: ArcGenericLdeStorage<F, P, A, B>,
    op: &OP,
    worker: &Worker,
    ctx: &mut P::Context,
) {
    debug_assert_eq!(a.inner_len(), b.inner_len());
    debug_assert_eq!(a.inner_len(), dst.inner_len());

    debug_assert_eq!(a.outer_len(), b.outer_len());
    debug_assert_eq!(a.outer_len(), dst.outer_len());

    let iterators = a.compute_chunks_for_num_workers(worker.num_cores);

    worker.scope(0, |scope, _| {
        for iterator in iterators.into_iter() {
            let mut dst = dst.clone();
            let a = a.clone();
            let b = b.clone();
            let mut ctx = *ctx;
            scope.spawn(move |_| {
                let num_iterations = iterator.num_iterations();
                let mut iterator = iterator;
                for _ in 0..num_iterations {
                    let (outer, inner) = iterator.current();

                    let a = &a.storage[outer].storage[inner];
                    let b = &b.storage[outer].storage[inner];

                    // inliner should take care of references here
                    op.apply(
                        &mut unsafe { Arc::get_mut_unchecked(&mut dst.storage[outer]) }.storage
                            [inner],
                        a,
                        b,
                        &mut ctx,
                    );

                    iterator.advance();
                }
            });
        }
    });
}

// DST must be initialized here
pub(crate) fn apply_multiop<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    FN: Fn(
            &mut [ArcGenericLdeStorage<F, P, A, B>; N],
            &[ArcGenericLdeStorage<F, P, A, B>; M],
            usize,
            usize,
            &mut P::Context,
        )
        + 'static
        + Send
        + Sync,
    const N: usize,
    const M: usize,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    dst: &mut [ArcGenericLdeStorage<F, P, A, B>; N],
    src: &[ArcGenericLdeStorage<F, P, A, B>; M],
    op: &FN,
    worker: &Worker,
    ctx: &mut P::Context,
) {
    assert!(dst.len() > 0);
    assert!(src.len() > 0);

    debug_assert!({
        let mut valid = true;
        let typical_inner = dst[0].inner_len();
        let typical_outer = dst[0].outer_len();

        for a in dst.iter() {
            if a.inner_len() != typical_inner || a.outer_len() != typical_outer {
                valid = false
            }
        }

        for a in src.iter() {
            if a.inner_len() != typical_inner || a.outer_len() != typical_outer {
                valid = false
            }
        }

        valid
    });

    let iterators = dst[0].compute_chunks_for_num_workers(worker.num_cores);

    worker.scope(0, |scope, _| {
        for iterator in iterators.into_iter() {
            let mut dst = dst.clone();
            let src = src.clone();
            let mut ctx = *ctx;
            scope.spawn(move |_| {
                let num_iterations = iterator.num_iterations();
                let mut iterator = iterator;
                for _ in 0..num_iterations {
                    let (outer, inner) = iterator.current();

                    (op)(&mut dst, &src, outer, inner, &mut ctx);

                    iterator.advance();
                }
            });
        }
    });
}

// DST must be initialized here
pub(crate) fn apply_ternop_into<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    OP: Ternop<P, P::Context>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    dst: &mut ArcGenericLdeStorage<F, P, A, B>,
    a: ArcGenericLdeStorage<F, P, A, B>,
    b: ArcGenericLdeStorage<F, P, A, B>,
    c: ArcGenericLdeStorage<F, P, A, B>,
    op: &OP,
    worker: &Worker,
    ctx: &mut P::Context,
) {
    debug_assert_eq!(a.inner_len(), b.inner_len());
    debug_assert_eq!(a.inner_len(), c.inner_len());
    debug_assert_eq!(a.inner_len(), dst.inner_len());

    debug_assert_eq!(a.outer_len(), b.outer_len());
    debug_assert_eq!(a.outer_len(), c.outer_len());
    debug_assert_eq!(a.outer_len(), dst.outer_len());

    let iterators = a.compute_chunks_for_num_workers(worker.num_cores);

    worker.scope(0, |scope, _| {
        for iterator in iterators.into_iter() {
            let mut dst = dst.clone();
            let a = a.clone();
            let b = b.clone();
            let c = c.clone();
            let mut ctx = *ctx;
            scope.spawn(move |_| {
                let num_iterations = iterator.num_iterations();
                let mut iterator = iterator;
                for _ in 0..num_iterations {
                    let (outer, inner) = iterator.current();

                    let a = &a.storage[outer].storage[inner];
                    let b = &b.storage[outer].storage[inner];
                    let c = &c.storage[outer].storage[inner];

                    // inliner should take care of references here
                    op.apply(
                        &mut unsafe { Arc::get_mut_unchecked(&mut dst.storage[outer]) }.storage
                            [inner],
                        a,
                        b,
                        c,
                        &mut ctx,
                    );

                    iterator.advance();
                }
            });
        }
    });
}

// DST must be initialized here
pub(crate) fn apply_quad_into<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    OP: Quadop<P, P::Context>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    dst: &mut ArcGenericLdeStorage<F, P, A, B>,
    a: ArcGenericLdeStorage<F, P, A, B>,
    b: ArcGenericLdeStorage<F, P, A, B>,
    c: ArcGenericLdeStorage<F, P, A, B>,
    d: ArcGenericLdeStorage<F, P, A, B>,
    op: &OP,
    worker: &Worker,
    ctx: &mut P::Context,
) {
    debug_assert_eq!(a.inner_len(), b.inner_len());
    debug_assert_eq!(a.inner_len(), c.inner_len());
    debug_assert_eq!(a.inner_len(), d.inner_len());
    debug_assert_eq!(a.inner_len(), dst.inner_len());

    debug_assert_eq!(a.outer_len(), b.outer_len());
    debug_assert_eq!(a.outer_len(), c.outer_len());
    debug_assert_eq!(a.outer_len(), d.outer_len());
    debug_assert_eq!(a.outer_len(), dst.outer_len());

    let iterators = a.compute_chunks_for_num_workers(worker.num_cores);

    worker.scope(0, |scope, _| {
        for iterator in iterators.into_iter() {
            let mut dst = dst.clone();
            let a = a.clone();
            let b = b.clone();
            let c = c.clone();
            let d = d.clone();
            let mut ctx = *ctx;
            scope.spawn(move |_| {
                let num_iterations = iterator.num_iterations();
                let mut iterator = iterator;
                for _ in 0..num_iterations {
                    let (outer, inner) = iterator.current();

                    let a = &a.storage[outer].storage[inner];
                    let b = &b.storage[outer].storage[inner];
                    let c = &c.storage[outer].storage[inner];
                    let d = &d.storage[outer].storage[inner];

                    // inliner should take care of references here
                    op.apply(
                        &mut unsafe { Arc::get_mut_unchecked(&mut dst.storage[outer]) }.storage
                            [inner],
                        a,
                        b,
                        c,
                        d,
                        &mut ctx,
                    );

                    iterator.advance();
                }
            });
        }
    });
}

// compute unnormalized L1(x) over our LDE superdomain and coset
pub(crate) fn unnormalized_l1_inverse<
    F: PrimeField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    domain_size: usize,
    lde_degree: usize,
    coset: F,
    worker: &Worker,
    ctx: &mut P::Context,
) -> ArcGenericLdeStorage<F, P, A, B> {
    // we need to compute unnormalized poly, that is zero everywhere,
    // but not at omega^0. So we compute (x^n - 1) / (x - 1),
    // where x = coset *{lde coset factor} * {1, omega, omega^2, etc}

    // out prefactor x^n - 1 is trivial on every coset,
    // so we mainly need to compute denominators

    let mut result = ArcGenericLdeStorage::empty_with_capacity_in(lde_degree, B::default());

    let omega = domain_generator_for_size::<F>(domain_size as u64);
    let lde_generator = domain_generator_for_size::<F>((domain_size * lde_degree) as u64);
    let mut lde_factors = materialize_powers_serial::<F, B>(lde_generator, lde_degree);
    bitreverse_enumeration_inplace(&mut lde_factors);

    for lde_factor in lde_factors.into_iter() {
        let mut r = allocate_in_with_alignment_of::<F, P, A>(domain_size, A::default());
        let mut numerator = coset;
        numerator.mul_assign(&lde_factor);
        numerator = numerator.pow_u64(domain_size as u64);
        numerator.sub_assign(&F::ONE);

        worker.scope(domain_size, |scope, chunk_size| {
            for (chunk_idx, dst) in r.spare_capacity_mut()[..domain_size]
                .chunks_mut(chunk_size)
                .enumerate()
            {
                scope.spawn(move |_| {
                    let mut current = omega.pow_u64((chunk_size * chunk_idx) as u64);
                    current.mul_assign(&lde_factor);
                    current.mul_assign(&coset);
                    for dst in dst.iter_mut() {
                        let mut tmp = current;
                        tmp.sub_assign(&F::ONE);
                        dst.write(tmp);
                        current.mul_assign(&omega);
                    }
                });
            }
        });

        unsafe { r.set_len(domain_size) };

        // we computed powers of elements in natural enumeration, but will need bitreversed
        bitreverse_enumeration_inplace(&mut r);

        // inverse to get denominators
        batch_inverse_inplace_parallel::<F, A>(&mut r, worker);

        let mut r = P::vec_from_base_vec(r);

        worker.scope(r.len(), |scope, chunk_size| {
            let mut ctx = *ctx;
            for dst in r.chunks_mut(chunk_size) {
                scope.spawn(move |_| {
                    let mul_by = P::constant(numerator, &mut ctx);
                    for dst in dst.iter_mut() {
                        dst.mul_assign(&mul_by, &mut ctx);
                    }
                });
            }
        });

        result
            .storage
            .push(Arc::new(GenericPolynomial::from_storage(r)));
    }

    result
}

pub trait Binop<T: 'static + Send + Sync, CTX: 'static + Send + Sync>:
    'static + Send + Sync
{
    fn apply(&self, into: &mut T, a: &T, b: &T, ctx: &mut CTX);
}

impl<
        T: 'static + Send + Sync,
        CTX: 'static + Send + Sync,
        F: Fn(&mut T, &T, &T, &mut CTX) + 'static + Send + Sync,
    > Binop<T, CTX> for F
{
    #[inline(always)]
    fn apply(&self, into: &mut T, a: &T, b: &T, ctx: &mut CTX) {
        (self)(into, a, b, ctx);
    }
}

pub trait Ternop<T: 'static + Send + Sync, CTX: 'static + Send + Sync>:
    'static + Send + Sync
{
    fn apply(&self, into: &mut T, a: &T, b: &T, c: &T, ctx: &mut CTX);
}

impl<
        T: 'static + Send + Sync,
        CTX: 'static + Send + Sync,
        F: Fn(&mut T, &T, &T, &T, &mut CTX) + 'static + Send + Sync,
    > Ternop<T, CTX> for F
{
    #[inline(always)]
    fn apply(&self, into: &mut T, a: &T, b: &T, c: &T, ctx: &mut CTX) {
        (self)(into, a, b, c, ctx);
    }
}

pub trait Quadop<T: 'static + Send + Sync, CTX: 'static + Send + Sync>:
    'static + Send + Sync
{
    fn apply(&self, into: &mut T, a: &T, b: &T, c: &T, d: &T, ctx: &mut CTX);
}

impl<
        T: 'static + Send + Sync,
        CTX: 'static + Send + Sync,
        F: Fn(&mut T, &T, &T, &T, &T, &mut CTX) + 'static + Send + Sync,
    > Quadop<T, CTX> for F
{
    #[inline(always)]
    fn apply(&self, into: &mut T, a: &T, b: &T, c: &T, d: &T, ctx: &mut CTX) {
        (self)(into, a, b, c, d, ctx);
    }
}

#[cfg(test)]
mod test {
    use std::alloc::Global;

    use rand::thread_rng;

    use crate::field::{
        goldilocks::{GoldilocksExt2, GoldilocksField},
        rand_from_rng, Field,
    };

    use super::*;

    type F = GoldilocksField;
    type Ext = GoldilocksExt2;

    #[test]
    fn test_materialize_powers() {
        let serial: Vec<_> = materialize_powers_serial(F::multiplicative_generator(), 512);
        let worker = Worker::new();
        let parallel: Vec<_> = materialize_powers_parallel::<F, F, Global>(
            F::multiplicative_generator(),
            512,
            &worker,
        );
        assert_eq!(serial, parallel);
    }

    #[test]
    fn test_batch_inverse() {
        use crate::field::traits::field::Field;

        let input = vec![
            F::ONE,
            F::from_u64_with_reduction(123),
            F::from_u64_with_reduction(456),
            F::from_u64_with_reduction(789),
            F::from_u64_with_reduction(123),
            F::from_u64_with_reduction(456),
            F::from_u64_with_reduction(789),
            F::from_u64_with_reduction(123),
            F::from_u64_with_reduction(456),
            F::from_u64_with_reduction(789),
            F::TWO,
        ];

        let mut inv_dst = vec![];
        batch_inverse(&input, &mut inv_dst);

        let reference: Vec<_> = input.into_iter().map(|el| el.inverse().unwrap()).collect();
        assert_eq!(inv_dst, reference);
    }

    #[test]
    fn test_batch_inverse_in_extension() {
        use crate::field::traits::field::Field;
        use std::alloc::Global;

        let input_c0 = vec![
            F::ONE,
            F::from_u64_with_reduction(123),
            F::from_u64_with_reduction(456),
            F::from_u64_with_reduction(789),
            F::from_u64_with_reduction(123),
            F::from_u64_with_reduction(456),
            F::from_u64_with_reduction(789),
            F::from_u64_with_reduction(123),
            F::from_u64_with_reduction(456),
            F::from_u64_with_reduction(789),
            F::TWO,
        ];

        let mut input_c1 = input_c0.clone();
        input_c1.reverse();

        let mut inv_dst_c0 = vec![];
        let mut inv_dst_c1 = vec![];
        batch_inverse_in_extension::<F, GoldilocksExt2, Global>(
            &input_c0,
            &input_c1,
            &mut inv_dst_c0,
            &mut inv_dst_c1,
        );

        let mut reference_c0 = vec![];
        let mut reference_c1 = vec![];

        for (c0, c1) in input_c0.into_iter().zip(input_c1.into_iter()) {
            let el = ExtensionField::<F, 2, GoldilocksExt2>::from_coeff_in_base([c0, c1]);
            let [c0, c1] = el.inverse().unwrap().coeffs;
            reference_c0.push(c0);
            reference_c1.push(c1);
        }

        assert_eq!(inv_dst_c0, reference_c0);
        assert_eq!(inv_dst_c1, reference_c1);
    }

    #[test]
    fn test_barycentric_eval() {
        for log_size in 0..20 {
            let size = 1usize << log_size;

            let mut rng = thread_rng();
            let coeffs: Vec<_> = (0..size).map(|_| rand_from_rng::<_, F>(&mut rng)).collect();

            let z = rand_from_rng::<_, F>(&mut rng);

            let mut naive = F::ZERO;
            let mut current = F::ONE;
            for el in coeffs.iter() {
                let mut tmp = *el;
                tmp.mul_assign(&current);
                naive.add_assign(&tmp);
                current.mul_assign(&z);
            }

            let worker = Worker::new();

            let precomps: Vec<F> = precompute_for_barycentric_evaluation(
                size,
                F::multiplicative_generator(),
                z,
                &worker,
                &mut (),
            );

            let forward_twiddles: Vec<_> =
                precompute_twiddles_for_fft::<F, F, _, false>(size, &worker, &mut ());
            let mut forward = coeffs.clone();
            {
                use crate::field::traits::field_like::PrimeFieldLikeVectorized;
                F::fft_natural_to_bitreversed(
                    &mut forward,
                    GoldilocksField::multiplicative_generator(),
                    &forward_twiddles,
                    &mut (),
                );
            }

            let barycentric_val = barycentric_evaluate_at_for_bitreversed(&forward, &precomps);

            assert_eq!(naive, barycentric_val);

            let barycentric_val_parallel =
                barycentric_evaluate_at_for_bitreversed_parallel(&forward, &precomps, &worker);

            assert_eq!(naive, barycentric_val_parallel);
        }
    }

    #[test]
    fn test_barycentric_eval_in_extension() {
        for log_size in 0..20 {
            let size = 1usize << log_size;

            let mut rng = thread_rng();
            let coeffs_c0: Vec<_> = (0..size).map(|_| rand_from_rng::<_, F>(&mut rng)).collect();
            let coeffs_c1: Vec<_> = (0..size).map(|_| rand_from_rng::<_, F>(&mut rng)).collect();

            let z_c0 = rand_from_rng::<_, F>(&mut rng);
            let z_c1 = rand_from_rng::<_, F>(&mut rng);

            let z = ExtensionField::from_coeff_in_base([z_c0, z_c1]);

            let mut naive = ExtensionField::<F, 2, Ext>::ZERO;
            let mut current = ExtensionField::<F, 2, Ext>::ONE;
            for (c0, c1) in coeffs_c0.iter().zip(coeffs_c1.iter()) {
                let mut tmp = ExtensionField::from_coeff_in_base([*c0, *c1]);
                tmp.mul_assign(&current);
                naive.add_assign(&tmp);

                current.mul_assign(&z);
            }

            let worker = Worker::new();

            let [precomps_c0, precomps_c1] =
                precompute_for_barycentric_evaluation_in_extension::<F, Ext, F, Global>(
                    size,
                    F::multiplicative_generator(),
                    z,
                    &worker,
                    &mut (),
                );

            let forward_twiddles: Vec<_> =
                precompute_twiddles_for_fft::<F, F, _, false>(size, &worker, &mut ());
            let mut forward_c0 = coeffs_c0.clone();
            let mut forward_c1 = coeffs_c1.clone();
            {
                use crate::field::traits::field_like::PrimeFieldLikeVectorized;
                F::fft_natural_to_bitreversed(
                    &mut forward_c0,
                    GoldilocksField::multiplicative_generator(),
                    &forward_twiddles,
                    &mut (),
                );
                F::fft_natural_to_bitreversed(
                    &mut forward_c1,
                    GoldilocksField::multiplicative_generator(),
                    &forward_twiddles,
                    &mut (),
                );
            }

            let barycentric_val =
                barycentric_evaluate_extension_at_extension_for_bitreversed_parallel::<F, Ext>(
                    &forward_c0,
                    &forward_c1,
                    &precomps_c0,
                    &precomps_c1,
                    &worker,
                );

            assert_eq!(
                naive,
                ExtensionField::from_coeff_in_base(barycentric_val),
                "failed for size 2^{}",
                log_size
            );
        }
    }
}
