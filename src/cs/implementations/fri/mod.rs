use super::polynomial_storage::{SecondStageProductsStorage, WitnessStorage};
use super::*;
use std::mem::MaybeUninit;

// Note: in this codebase we assume "small" modulus (64 bits), so we have a "problem" with FRI:
// - to achieve soundness from interactive part, we need to perform FRI twice or 3 times to get proper soundness
// error due to pulling the challenges from the small field
// - but for efficiency purposes we would want to still instantiate intermediate oracles in the join form, so both parallel
// FRIs would use the same tree with 2x or 3x elements placed into the leaf
// - and naively we would pull single index during query phase and do 2 or 3 "independent" interpolations for verification

// Unfortunately we can not do it (unless we prove the opposite later on) due to e.g. https://www.youtube.com/watch?v=0DHoxCAsick - parallel repetition

// So when we get presumably RS codes from quotening operation (f(x) - f(z))/(x - z) and linear combination of such terms,
// we immediatelly pull challenges for such linear combination from quadratic extension, so our initial oracle for FRI containes Fp2 elements in the leafs.
// Then on every step of interpolation we will take another challenge from Fp2 and continue

// Another things is FRI soundness bound. FRI (not DEEP-FRI) is sound up to Johnson bound IF code size is much smaller
// than field size. So we need n << |F|, that is not that prominent for |F| ~= 2^64

// Because we want to do some vectorization tricks, we manually implement operations in Fp2 over Vec<Fp2> as operations over
// (Vec<F>, Vec<F>)

use crate::cs::implementations::polynomial::lde::ArcGenericLdeStorage;
use crate::cs::implementations::transcript::Transcript;
use crate::cs::implementations::utils::precompute_twiddles_for_fft;
use crate::cs::oracle::merkle_tree::MerkleTreeWithCap;
use crate::cs::oracle::TreeHasher;
use crate::cs::traits::GoodAllocator;
use crate::fft::bitreverse_enumeration_inplace;

use crate::field::{Field, FieldExtension};

pub struct FriOracles<
    F: SmallField,
    H: TreeHasher<F>,
    A: GoodAllocator,
    B: GoodAllocator,
    const N: usize,
> {
    // we do not store "leaf" sources for the base oracle, but store all other oracles
    // and their leafs
    pub base_oracle: MerkleTreeWithCap<F, H, A, B>,
    pub leaf_sources_for_intermediate_oracles: Vec<(Vec<F, A>, Vec<F, A>), B>,
    pub intermediate_oracles: Vec<MerkleTreeWithCap<F, H, A, B>, B>,
    pub monomial_forms: [Vec<F, A>; 2],
}

pub fn do_fri<
    F: SmallField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    EXT: FieldExtension<2, BaseField = F>,
    T: Transcript<F>,
    H: TreeHasher<F, Output = T::CompatibleCap>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    rs_code_word_c0: ArcGenericLdeStorage<F, P, A, B>,
    rs_code_word_c1: ArcGenericLdeStorage<F, P, A, B>,
    transcript: &mut T,
    interpolation_log2s_schedule: Vec<usize>,
    lde_degree: usize,
    cap_size: usize,
    worker: &Worker,
    ctx: &mut P::Context,
) -> FriOracles<F, H, A, B, 2> {
    // first we have to construct our "base" oracle

    let now = std::time::Instant::now();

    debug_assert_eq!(rs_code_word_c0.outer_len(), rs_code_word_c1.outer_len());
    debug_assert_eq!(rs_code_word_c0.inner_len(), rs_code_word_c1.inner_len());

    let full_size = rs_code_word_c0.outer_len() * rs_code_word_c0.inner_len() * P::SIZE_FACTOR;
    let degree = full_size / lde_degree;
    let mut final_degree = degree;
    for interpolation_log2 in interpolation_log2s_schedule.iter() {
        let factor = 1usize << interpolation_log2;
        final_degree /= factor;
    }

    assert!(final_degree > 0);

    // now we can interpolate

    // usually FRI example is folding by 2, using quasi-FFT as
    // f(x) = f0(x^2) + x * f1(x^2)
    // and half degree interpolation is
    // f'(x^2) = f0(x^2) + alpha * f1(x^2), and it can be achieved by just adding up two adjustent
    // coefficients in the monomial form
    // if we would want to try to get the same result, one can observe that
    // f0(x^2) = (f(x) + f(-x)) / 2
    // f1(x^2) = (f(x) - f(-x)) / 2x

    // so f'(x^2) = (f(x) + f(-x)) / 2 + alpha * (f(x) - f(-x)) / 2x by value

    // note that those formulas are independent of whether we are at "omega" or "omega * coset",
    // because "coset" goes under the coefficients into f(x), and we can always few our work
    // as it happens directly at the roots of unity

    // now we have two options how to extend to higher interpolation degrees:
    // - express something like
    // f(x) = f0(x^4) + x * f1(x^4) + x^2 * f2(x^4) + x^3 * f3(x^4),
    // where similar interpolation via random challenge formula trivially applies,
    // or try to re-express it from by-value case

    // f(x) = f0(x^4) + x * f1(x^4) + x^2 * f2(x^4) + x^3 * f3(x^4),
    // f(-x) = f0(x^4) - x * f1(x^4) + x^2 * f2(x^4) - x^3 * f3(x^4),
    // f(x * sqrt(-1)) = f0(x^4) + sqrt(-1) * x * f(x^4) - x^2 * f2(x^4) - sqrt(-1) * x^3 * f3(x^4)
    // f(-x * sqrt(-1)) = f0(x^4) - sqrt(-1) * x * f(x^4) - x^2 * f2(x^4) + sqrt(-1) * x^3 * f3(x^4)

    // yes, we kind of abuse "x" notation there, and it may be a little confusing. Now we want to compute
    // f'(x^4) = f0(x^4) + alpha * f1(x^4) + alpha^2 * f2(x^4) + alpha^3 * f3(x^4)

    // note the symmetry below:

    // f(x) + f(-x) == 2 * f0(x^2) previously, and now
    // f(x) + f(-x) == 2 * f0(x^4) + 2 * x^2 * f3(x^4)

    // f(x) - f(-x) == 2 * x * f1(x^2) previously, and now
    // f(x) - f(-x) = 2 * x * f1(x^4) + 2 * x^3 * f3(x^4)

    // f(x * sqrt(-1)) + f(-x * sqrt(-1)) = 2 * f0(x^4) - 2 * x^2 * f2(x^4)
    // f(x * sqrt(-1)) - f(-x * sqrt(-1)) = 2 * sqrt(-1) * x * f1(x^4) - 2 * sqrt(-1) * x^3 * f3(x^4)

    // and each of those pairs [f(x), f(-x)], and [f(x * sqrt(-1)), f(-x * sqrt(-1))] would itself be pairs between
    // themselves if we would fold by 2

    // f0(x^4) = (f(x) + f(-x) + f(x * sqrt(-1)) + f(-x * sqrt(-1))) / 4
    // f1(x^4) = (f(x) - f(-x) + (f(x * sqrt(-1)) - f(-x * sqrt(-1))) / sqrt(-1) ) / 4x
    // f2(x^4) = (f(x) + f(-x) - (f(x * sqrt(-1)) + f(-x * sqrt(-1))) ) / 4x^2
    // f3(x^4) = (f(x) - f(-x) - (f(x * sqrt(-1)) - f(-x * sqrt(-1))) / sqrt(-1) ) / 4x^3

    // and our final interpolant value at x^4 can be computed as
    // 4 * f'(x^4) = f(x) * (1 + alpha/x + alpha^2/x^2 + alpha^3/x^3) +
    //               f(-x) * (1 - alpha/x + alpha^2/x^2 - alpha^3/x^3) +
    //               f(x * sqrt(-1)) * (1 + alpha/x/sqrt(-1) - alpha^2/x^2 - alpha^3/x^3/sqrt(-1))
    //               f(-x * sqrt(-1)) * (1 - alpha/x/sqrt(-1) - alpha^2/x^2 + alpha^3/x^3/sqrt(-1))

    // and if we would fold twice by 2 instead:

    // 2 * f'(x^2) = f(x) * (1 + alpha/x) + f(-x) * (1 - alpha/x)
    // 2 * f'(-x^2) = f(x * sqrt(-1)) * (1 + alpha/x/sqrt(-1)) + f(-x * sqrt(-1)) * (1 - alpha/x/sqrt(-1))

    // and NOW we interpolate the interpolants using alpha^2

    // 4 * f''(x^4) = f'(x^2) * (1 + alpha^2/x^2) + f'(-x^2) * (1 - alpha^2/x^2) =
    // = (f(x) * (1 + alpha/x) + f(-x) * (1 - alpha/x)) * (1 + alpha^2/x^2) +
    // + (f(x * sqrt(-1)) * (1 + alpha/x/sqrt(-1)) + f(-x * sqrt(-1)) * (1 - alpha/x/sqrt(-1))) * (1 - alpha^2/x^2) =
    // = f(x) * ( (1 + alpha/x) * (1 + alpha^2/x^2) ) +
    // + f(-x) * ( (1 - alpha/x) * (1 + alpha^2/x^2) ) +
    // + f(x * sqrt(-1)) * ( (1 + alpha/x/sqrt(-1)) * (1 - alpha^2/x^2) )
    // + f(-x * sqrt(-1)) * ( (1 - alpha/x/sqrt(-1)) * (1 - alpha^2/x^2) ) =
    // = f(x) * ( 1 + alpha/x + alpha^2/x^2 + alpha^3/x^3 ) +
    // + f(-x) * ( 1 - alpha/x + alpha^2/x^2 - alpha^3/x^3 ) +
    // + f(x * sqrt(-1)) * ( 1 + alpha/x/sqrt(-1) - alpha^2/x^2 - alpha^3/x^3/sqrt(-1) )
    // + f(-x * sqrt(-1)) * ( 1 - alpha/x/sqrt(-1) - alpha^2/x^2 + alpha^3/x^3/sqrt(-1) )

    // That is (wow, miracle!) the same expression that we would want to get if we would interpolate through
    // the coefficients

    // this formula works all the way, so we just recursively apply folding by 2, and raise the challenge powers
    // (square it) every time when necessary

    // one should also note that after LDE when we have cosets like [1, gamma, gamma^2, ...] * {1, omega, ...},
    // values of x, -x, x * sqrt(-1) and -x * sqrt(-1) are always in the same coset as long as it's size larger than 4.
    // same would apply if we would use higher roots of -1

    // create first oracle. It's special because
    // what we have have is two polynomials that represent c0 and c1 coefficients of the extension,
    // and we want to take X elements from every coset in there, and place into the leaf

    let mut base_sources = Vec::with_capacity_in(2, B::default());
    base_sources.push(rs_code_word_c0.clone());
    base_sources.push(rs_code_word_c1.clone());

    let base_oracle_elements_per_leaf = interpolation_log2s_schedule[0];

    let fri_base_oracle =
        oracle::merkle_tree::MerkleTreeWithCap::<F, H, A, B>::construct_by_chunking(
            base_sources,
            1 << base_oracle_elements_per_leaf,
            cap_size,
            worker,
        );

    transcript.witness_merkle_tree_cap(&fri_base_oracle.get_cap());

    let mut intermediate_oracles = Vec::new_in(B::default());
    let mut intermediate_sources = Vec::new_in(B::default());

    let roots = precompute_twiddles_for_fft::<F, P, A, true>(full_size, worker, ctx);
    let roots = P::vec_into_base_vec(roots);

    let mut coset_inverse = F::multiplicative_generator().inverse().unwrap();

    // we have to manually unroll 1st loop due to type dependency
    let mut it = interpolation_log2s_schedule.into_iter();

    let reduction_degree_log_2 = it.next().unwrap();

    let (c0_values, c1_values) = {
        log!("Fold degree by {}", 1 << reduction_degree_log_2);
        assert!(reduction_degree_log_2 > 0);
        assert!(reduction_degree_log_2 < 4);

        let c0 = transcript.get_challenge();
        let c1 = transcript.get_challenge();

        let mut challenge_powers = Vec::with_capacity(reduction_degree_log_2);
        challenge_powers.push((c0, c1));
        use crate::field::ExtensionField;
        let as_extension = ExtensionField::<F, 2, EXT> {
            coeffs: [c0, c1],
            _marker: std::marker::PhantomData,
        };

        let mut current = as_extension;

        for _ in 1..reduction_degree_log_2 {
            current.square();
            let [c0, c1] = current.into_coeffs_in_base();
            challenge_powers.push((c0, c1));
        }

        // now interpolate as described above

        let (c0, c1) = interpolate_independent_cosets::<F, P, EXT, A, B>(
            rs_code_word_c0.clone(),
            rs_code_word_c1.clone(),
            reduction_degree_log_2,
            &roots,
            challenge_powers,
            lde_degree,
            &mut coset_inverse,
            worker,
            ctx,
        );

        (c0, c1)
    };

    intermediate_sources.push((c0_values, c1_values));

    for reduction_degree_log_2 in it {
        log!("Fold degree by {}", 1 << reduction_degree_log_2);

        assert!(reduction_degree_log_2 > 0);
        assert!(reduction_degree_log_2 < 4);

        // make intermediate oracle for the next folding
        let mut sources = Vec::with_capacity_in(2, B::default());
        let (c0_values, c1_values) = intermediate_sources
            .last()
            .expect("previous folding result exists");
        sources.push(c0_values);
        sources.push(c1_values);
        let intermediate_oracle =
            MerkleTreeWithCap::<F, H, A, B>::construct_by_chunking_from_flat_sources(
                &sources,
                1 << reduction_degree_log_2,
                cap_size,
                worker,
            );

        transcript.witness_merkle_tree_cap(&intermediate_oracle.get_cap());

        intermediate_oracles.push(intermediate_oracle);
        // compute next folding

        let c0 = transcript.get_challenge();
        let c1 = transcript.get_challenge();

        let mut challenge_powers = Vec::with_capacity(reduction_degree_log_2);
        challenge_powers.push((c0, c1));
        use crate::field::ExtensionField;
        let as_extension = ExtensionField::<F, 2, EXT> {
            coeffs: [c0, c1],
            _marker: std::marker::PhantomData,
        };

        let mut current = as_extension;

        for _ in 1..reduction_degree_log_2 {
            current.square();
            let [c0, c1] = current.into_coeffs_in_base();
            challenge_powers.push((c0, c1));
        }

        // now interpolate as described above

        let (c0_source, c1_source) = intermediate_sources.last().cloned().unwrap();

        let (new_c0, new_c1) = interpolate_flattened_cosets::<F, EXT, A>(
            c0_source,
            c1_source,
            reduction_degree_log_2,
            &roots,
            challenge_powers,
            lde_degree,
            &mut coset_inverse,
            worker,
        );

        intermediate_sources.push((new_c0, new_c1));
    }

    // we can now interpolate the last sets to get monomial forms

    log!("Interpolating low degree poly");

    let (mut c0_source, mut c1_source) = intermediate_sources.last().cloned().unwrap();

    bitreverse_enumeration_inplace(&mut c0_source);
    bitreverse_enumeration_inplace(&mut c1_source);

    let coset = coset_inverse.inverse().unwrap();
    // IFFT our presumable LDE of some low degree poly
    let fft_size = c0_source.len();
    crate::fft::ifft_natural_to_natural(&mut c0_source, coset, &roots[..fft_size / 2]);
    crate::fft::ifft_natural_to_natural(&mut c1_source, coset, &roots[..fft_size / 2]);

    assert_eq!(final_degree, fft_size / lde_degree);

    // self-check
    if crate::config::DEBUG_SATISFIABLE == false {
        for el in c0_source[final_degree..].iter() {
            assert_eq!(*el, F::ZERO);
        }

        for el in c1_source[final_degree..].iter() {
            assert_eq!(*el, F::ZERO);
        }
    }

    // add to the transcript
    transcript.witness_field_elements(&c0_source[..final_degree]);
    transcript.witness_field_elements(&c1_source[..final_degree]);

    // now we should do some PoW and we are good to go

    let monomial_form_0 = c0_source[..(fft_size / lde_degree)].to_vec_in(A::default());
    let monomial_form_1 = c1_source[..(fft_size / lde_degree)].to_vec_in(A::default());

    log!(
        "FRI for base size 2^{} is done over {:?}",
        full_size.trailing_zeros(),
        now.elapsed()
    );

    FriOracles {
        base_oracle: fri_base_oracle,
        leaf_sources_for_intermediate_oracles: intermediate_sources,
        intermediate_oracles,
        monomial_forms: [monomial_form_0, monomial_form_1],
    }
}

// this is quasi-vectorization
#[inline(always)]
#[unroll::unroll_for_loops]
fn fold_multiple<F: SmallField, EXT: FieldExtension<2, BaseField = F>>(
    c0_chunk: &[F],
    c1_chunk: &[F],
    dst_c0: &mut [MaybeUninit<F>],
    dst_c1: &mut [MaybeUninit<F>],
    roots: &[F],
    coset_inverse: &F,
    (c0, c1): (F, F),
) {
    use crate::field::traits::field::Field;
    use crate::field::ExtensionField;

    // we compute f(x) + f(-x) + alpha * ((f(x) - f(-x))) / x,
    // where f(x), f(-x) and alpha are extension field elements,
    // and x is in the base field

    // So in practice we only do single multiplication of Fp2 by Fp2 here

    let mut src_c0_chunks = c0_chunk.array_chunks::<32>();
    let mut src_c1_chunks = c1_chunk.array_chunks::<32>();

    let mut dst_c0_chunks = dst_c0.array_chunks_mut::<16>();
    let mut dst_c1_chunks = dst_c1.array_chunks_mut::<16>();

    let mut roots_chunks = roots.array_chunks::<16>();

    let challenge_as_extension = ExtensionField::<F, 2, EXT> {
        coeffs: [c0, c1],
        _marker: std::marker::PhantomData,
    };

    for ((((c0_pairs, c1_pairs), dst_c0), dst_c1), roots) in (&mut src_c0_chunks)
        .zip(&mut src_c1_chunks)
        .zip(&mut dst_c0_chunks)
        .zip(&mut dst_c1_chunks)
        .zip(&mut roots_chunks)
    {
        for i in 0..16 {
            let f_at_x_c0 = c0_pairs[2 * i];
            let f_at_minus_x_c0 = c0_pairs[2 * i + 1];
            let mut diff_c0 = f_at_x_c0;
            diff_c0.sub_assign(&f_at_minus_x_c0);
            diff_c0.mul_assign(&roots[i]);
            diff_c0.mul_assign(coset_inverse);

            let f_at_x_c1 = c1_pairs[2 * i];
            let f_at_minus_x_c1 = c1_pairs[2 * i + 1];
            let mut diff_c1 = f_at_x_c1;
            diff_c1.sub_assign(&f_at_minus_x_c1);
            diff_c1.mul_assign(&roots[i]);
            diff_c1.mul_assign(coset_inverse);

            // now we multiply
            let mut diff_as_extension = ExtensionField::<F, 2, EXT> {
                coeffs: [diff_c0, diff_c1],
                _marker: std::marker::PhantomData,
            };

            diff_as_extension.mul_assign(&challenge_as_extension);

            let [mut other_c0, mut other_c1] = diff_as_extension.into_coeffs_in_base();

            other_c0.add_assign(&f_at_x_c0).add_assign(&f_at_minus_x_c0);
            other_c1.add_assign(&f_at_x_c1).add_assign(&f_at_minus_x_c1);

            dst_c0[i].write(other_c0);
            dst_c1[i].write(other_c1);
        }
    }

    // and now over remainders
    let c0_pairs = src_c0_chunks.remainder();
    let c1_pairs = src_c1_chunks.remainder();

    let dst_c0 = dst_c0_chunks.into_remainder();
    let dst_c1 = dst_c1_chunks.into_remainder();

    let roots = roots_chunks.remainder();

    let bound = dst_c0.len();

    for i in 0..bound {
        let f_at_x_c0 = c0_pairs[2 * i];
        let f_at_minus_x_c0 = c0_pairs[2 * i + 1];
        let mut diff_c0 = f_at_x_c0;
        diff_c0.sub_assign(&f_at_minus_x_c0);
        diff_c0.mul_assign(&roots[i]);
        diff_c0.mul_assign(coset_inverse);

        let f_at_x_c1 = c1_pairs[2 * i];
        let f_at_minus_x_c1 = c1_pairs[2 * i + 1];
        let mut diff_c1 = f_at_x_c1;
        diff_c1.sub_assign(&f_at_minus_x_c1);
        diff_c1.mul_assign(&roots[i]);
        diff_c1.mul_assign(coset_inverse);

        // now we multiply
        let mut diff_as_extension = ExtensionField::<F, 2, EXT> {
            coeffs: [diff_c0, diff_c1],
            _marker: std::marker::PhantomData,
        };

        diff_as_extension.mul_assign(&challenge_as_extension);

        let [mut other_c0, mut other_c1] = diff_as_extension.into_coeffs_in_base();

        other_c0.add_assign(&f_at_x_c0).add_assign(&f_at_minus_x_c0);
        other_c1.add_assign(&f_at_x_c1).add_assign(&f_at_minus_x_c1);

        dst_c0[i].write(other_c0);
        dst_c1[i].write(other_c1);
    }
}

fn interpolate_independent_cosets<
    F: SmallField,
    P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
    EXT: FieldExtension<2, BaseField = F>,
    A: GoodAllocator,
    B: GoodAllocator,
>(
    c0_source: ArcGenericLdeStorage<F, P, A, B>,
    c1_source: ArcGenericLdeStorage<F, P, A, B>,
    interpolation_degree_log2: usize,
    roots_precomputation: &[F],
    challenges: Vec<(F, F)>,
    original_lde_degree: usize,
    coset_inverse: &mut F,
    worker: &Worker,
    _ctx: &mut P::Context,
) -> (Vec<F, A>, Vec<F, A>) {
    let full_size = c0_source.outer_len() * c0_source.inner_len() * P::SIZE_FACTOR;
    debug_assert_eq!(roots_precomputation.len() * 2, full_size);
    let mut interpolation_degree_log2 = interpolation_degree_log2;
    let result_size = full_size >> 1;
    interpolation_degree_log2 -= 1;
    debug_assert!(result_size > 0);
    let mut result_c0 = Vec::with_capacity_in(result_size, A::default());
    let mut result_c1 = Vec::with_capacity_in(result_size, A::default());

    // we fold as many times as we need, but after first folding we should understand that our memory layout is not
    // beneficial for FRI, so in practice we work over independent field elements

    let (c0, c1) = challenges[0];

    // even though our cosets are continuous in memory, total placement is just bitreversed

    for (coset_idx, (c0_coset, c1_coset)) in c0_source
        .storage
        .iter()
        .zip(c1_source.storage.iter())
        .enumerate()
    {
        let work_size = c0_coset.domain_size() / 2;
        let roots = &roots_precomputation[coset_idx * work_size..(coset_idx + 1) * work_size];
        let dst_c0 =
            &mut result_c0.spare_capacity_mut()[coset_idx * work_size..(coset_idx + 1) * work_size];
        let dst_c1 =
            &mut result_c1.spare_capacity_mut()[coset_idx * work_size..(coset_idx + 1) * work_size];

        worker.scope(work_size, |scope, chunk_size| {
            let src_c0 = P::slice_into_base_slice(&c0_coset.storage);
            let src_c1 = P::slice_into_base_slice(&c1_coset.storage);
            debug_assert_eq!(dst_c0.len() * 2, src_c0.len());

            for ((((c0_chunk, c1_chunk), dst0_chunk), dst1_chunk), roots) in src_c0
                .chunks(chunk_size * 2)
                .zip(src_c1.chunks(chunk_size * 2))
                .zip(dst_c0.chunks_mut(chunk_size))
                .zip(dst_c1.chunks_mut(chunk_size))
                .zip(roots.chunks(chunk_size))
            {
                scope.spawn(|_| {
                    fold_multiple::<F, EXT>(
                        c0_chunk,
                        c1_chunk,
                        dst0_chunk,
                        dst1_chunk,
                        roots,
                        &*coset_inverse,
                        (c0, c1),
                    );
                })
            }
        });
    }

    unsafe {
        result_c0.set_len(result_size);
        result_c1.set_len(result_size);
    }

    coset_inverse.square();

    if crate::config::DEBUG_SATISFIABLE == false {
        let coset = coset_inverse.inverse().unwrap();
        let mut tmp = result_c0.clone();
        bitreverse_enumeration_inplace(&mut tmp);
        crate::field::traits::field_like::ifft_natural_to_natural(&mut tmp, coset);
        for el in tmp[(tmp.len() / original_lde_degree)..].iter() {
            debug_assert_eq!(*el, F::ZERO);
        }

        let mut tmp = result_c1.clone();
        bitreverse_enumeration_inplace(&mut tmp);
        crate::field::traits::field_like::ifft_natural_to_natural(&mut tmp, coset);
        for el in tmp[(tmp.len() / original_lde_degree)..].iter() {
            debug_assert_eq!(*el, F::ZERO);
        }
    }

    let challenges = challenges[1..].to_vec();

    interpolate_flattened_cosets::<F, EXT, A>(
        result_c0,
        result_c1,
        interpolation_degree_log2,
        roots_precomputation,
        challenges,
        original_lde_degree,
        coset_inverse,
        worker,
    )
}

fn interpolate_flattened_cosets<
    F: SmallField,
    EXT: FieldExtension<2, BaseField = F>,
    A: GoodAllocator,
>(
    c0_source: Vec<F, A>,
    c1_source: Vec<F, A>,
    interpolation_degree_log2: usize,
    roots_precomputation: &[F],
    challenges: Vec<(F, F)>,
    original_lde_degree: usize,
    coset_inverse: &mut F,
    worker: &Worker,
) -> (Vec<F, A>, Vec<F, A>) {
    let full_size = c0_source.len();
    debug_assert_eq!(interpolation_degree_log2, challenges.len());
    let max_result_size = full_size >> 1;
    debug_assert!(max_result_size > 0);

    let mut c0_source = c0_source;
    let mut c1_source = c1_source;

    let mut result_c0 = Vec::with_capacity_in(max_result_size, A::default());
    let mut result_c1 = Vec::with_capacity_in(max_result_size, A::default());

    for (c0, c1) in challenges.into_iter() {
        let work_size = c0_source.len() / 2;

        result_c0.clear();
        result_c1.clear();

        let roots = &roots_precomputation[0..work_size];
        let dst_c0 = &mut result_c0.spare_capacity_mut()[..work_size];
        let dst_c1 = &mut result_c1.spare_capacity_mut()[..work_size];

        worker.scope(work_size, |scope, chunk_size| {
            debug_assert_eq!(dst_c0.len() * 2, c0_source.len());

            for ((((c0_chunk, c1_chunk), dst0_chunk), dst1_chunk), roots) in c0_source
                .chunks(chunk_size * 2)
                .zip(c1_source.chunks(chunk_size * 2))
                .zip(dst_c0.chunks_mut(chunk_size))
                .zip(dst_c1.chunks_mut(chunk_size))
                .zip(roots.chunks(chunk_size))
            {
                scope.spawn(|_| {
                    fold_multiple::<F, EXT>(
                        c0_chunk,
                        c1_chunk,
                        dst0_chunk,
                        dst1_chunk,
                        roots,
                        &*coset_inverse,
                        (c0, c1),
                    );
                })
            }
        });

        unsafe {
            result_c0.set_len(work_size);
            result_c1.set_len(work_size);
        }

        coset_inverse.square();

        if crate::config::DEBUG_SATISFIABLE == false {
            let coset = coset_inverse.inverse().unwrap();

            let mut tmp = result_c0.clone();
            bitreverse_enumeration_inplace(&mut tmp);
            crate::field::traits::field_like::ifft_natural_to_natural(&mut tmp, coset);
            for el in tmp[(tmp.len() / original_lde_degree)..].iter() {
                debug_assert_eq!(*el, F::ZERO);
            }

            let mut tmp = result_c1.clone();
            bitreverse_enumeration_inplace(&mut tmp);
            crate::field::traits::field_like::ifft_natural_to_natural(&mut tmp, coset);
            for el in tmp[(tmp.len() / original_lde_degree)..].iter() {
                debug_assert_eq!(*el, F::ZERO);
            }
        }

        // swap source and result to reuse the buffer

        std::mem::swap(&mut c0_source, &mut result_c0);
        std::mem::swap(&mut c1_source, &mut result_c1);
    }

    (c0_source, c1_source)
}

// We will query oracles where leafs are made from different number of elements
// from potentially different subsources of non-trivial structure

pub trait QuerySource<T: 'static + Clone> {
    fn get_elements(
        &self,
        lde_factor: usize,
        coset_idx: usize,
        domain_size: usize,
        inner_idx: usize,
        num_elements: usize,
        dst: &mut Vec<T>,
    );
}

use crate::cs::implementations::polynomial_storage::SetupStorage;

// for vectorized types we need to know subelement's index.
#[inline(always)]
pub fn split_inner(idx: usize, size_factor: usize) -> (usize, usize) {
    debug_assert!(size_factor.is_power_of_two());
    let outer = idx >> size_factor.trailing_zeros();
    let inner = idx & (size_factor - 1);

    (outer, inner)
}

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > QuerySource<F> for SetupStorage<F, P, A, B>
{
    // setup storage is merklized as copy-permutation columns, then constants, then lookup tables setup
    fn get_elements(
        &self,
        lde_factor: usize,
        coset_idx: usize,
        domain_size: usize,
        inner_idx: usize,
        num_elements: usize,
        dst: &mut Vec<F>,
    ) {
        assert!(lde_factor > coset_idx);
        assert_eq!(
            num_elements, 1,
            "we query setup/witness oracles only by 1 element per leaf"
        );
        let (outer, inner) = split_inner(inner_idx, P::SIZE_FACTOR);
        let source = self.flattened_source();
        for subsource in source {
            assert_eq!(subsource.storage[coset_idx].domain_size(), domain_size);
            let el = subsource.storage[coset_idx].storage[outer].as_base_elements()[inner];
            dst.push(el);
        }
    }
}

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > QuerySource<F> for WitnessStorage<F, P, A, B>
{
    // witness is variables, then witness, then lookup multiplicities columns
    fn get_elements(
        &self,
        lde_factor: usize,
        coset_idx: usize,
        domain_size: usize,
        inner_idx: usize,
        num_elements: usize,
        dst: &mut Vec<F>,
    ) {
        assert!(lde_factor > coset_idx);
        assert_eq!(
            num_elements, 1,
            "we query setup/witness oracles only by 1 element per leaf"
        );
        let (outer, inner) = split_inner(inner_idx, P::SIZE_FACTOR);
        let source = self.flattened_source();
        for subsource in source {
            assert_eq!(subsource.storage[coset_idx].domain_size(), domain_size);
            let el = subsource.storage[coset_idx].storage[outer].as_base_elements()[inner];
            dst.push(el);
        }
    }
}

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > QuerySource<F> for SecondStageProductsStorage<F, P, A, B>
{
    // witness is copy_permutation z_polys, then intermediate products, then lookup's A and B polys
    fn get_elements(
        &self,
        lde_factor: usize,
        coset_idx: usize,
        domain_size: usize,
        inner_idx: usize,
        num_elements: usize,
        dst: &mut Vec<F>,
    ) {
        assert!(lde_factor > coset_idx);
        assert_eq!(
            num_elements, 1,
            "we query setup/witness oracles only by 1 element per leaf"
        );
        let (outer, inner) = split_inner(inner_idx, P::SIZE_FACTOR);
        let source = self.flattened_source();
        for subsource in source {
            assert_eq!(subsource.storage[coset_idx].domain_size(), domain_size);
            let el = subsource.storage[coset_idx].storage[outer].as_base_elements()[inner];
            dst.push(el);
        }
    }
}

// the only other case if when we made FRI specific oracles. It's either the "largest one",
// that we can form from fixed set of polys arc polys, or flattened vectors

impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
    > QuerySource<F>
    for (
        ArcGenericLdeStorage<F, P, A, B>,
        ArcGenericLdeStorage<F, P, A, B>,
    )
{
    fn get_elements(
        &self,
        lde_factor: usize,
        coset_idx: usize,
        domain_size: usize,
        inner_idx: usize,
        num_elements: usize,
        dst: &mut Vec<F>,
    ) {
        assert!(lde_factor > coset_idx);
        // we put num_elements from first, and then from second
        assert!(num_elements.is_power_of_two());
        let (inner_start_aligned, _) = split_inner(inner_idx, num_elements);
        let source = [&self.0, &self.1];
        let inner_start_aligned = inner_start_aligned * num_elements;
        for subsource in source.iter() {
            assert_eq!(subsource.storage[coset_idx].domain_size(), domain_size);
            let as_base = P::slice_into_base_slice(&subsource.storage[coset_idx].storage);
            dst.extend_from_slice(
                &as_base[inner_start_aligned..(inner_start_aligned + num_elements)],
            );
        }
    }
}

impl<'a, F: SmallField, A: GoodAllocator> QuerySource<F> for &'a (Vec<F, A>, Vec<F, A>) {
    fn get_elements(
        &self,
        lde_factor: usize,
        coset_idx: usize,
        domain_size: usize,
        inner_idx: usize,
        num_elements: usize,
        dst: &mut Vec<F>,
    ) {
        assert!(lde_factor > coset_idx);
        // we put num_elements from one, then another
        assert!(num_elements.is_power_of_two());
        let (inner_start_aligned, _) = split_inner(inner_idx, num_elements);
        let mut inner_start_aligned = inner_start_aligned * num_elements;
        // we did flatten the sources, so we should offset
        inner_start_aligned += domain_size * coset_idx;

        let subsource = &self.0;
        assert_eq!(subsource.len(), domain_size * lde_factor);
        dst.extend_from_slice(
            &subsource[inner_start_aligned..(inner_start_aligned + num_elements)],
        );

        let subsource = &self.1;
        assert_eq!(subsource.len(), domain_size * lde_factor);
        dst.extend_from_slice(
            &subsource[inner_start_aligned..(inner_start_aligned + num_elements)],
        );
    }
}

impl<'a, F: SmallField, const N: usize, A: GoodAllocator> QuerySource<F> for &'a [Vec<F, A>; N] {
    fn get_elements(
        &self,
        lde_factor: usize,
        coset_idx: usize,
        domain_size: usize,
        inner_idx: usize,
        num_elements: usize,
        dst: &mut Vec<F>,
    ) {
        assert!(lde_factor > coset_idx);
        // we put num_elements from one, then another
        assert!(num_elements.is_power_of_two());
        let (inner_start_aligned, _) = split_inner(inner_idx, num_elements);
        for subsource in self.iter() {
            assert_eq!(subsource.len(), domain_size * lde_factor);
            dst.extend_from_slice(
                &subsource[inner_start_aligned..(inner_start_aligned + num_elements)],
            );
        }
    }
}

// mainly for quotient
impl<
        F: SmallField,
        P: field::traits::field_like::PrimeFieldLikeVectorized<Base = F>,
        A: GoodAllocator,
        B: GoodAllocator,
        C: GoodAllocator,
    > QuerySource<F> for Vec<ArcGenericLdeStorage<F, P, A, B>, C>
{
    fn get_elements(
        &self,
        lde_factor: usize,
        coset_idx: usize,
        domain_size: usize,
        inner_idx: usize,
        num_elements: usize,
        dst: &mut Vec<F>,
    ) {
        assert!(lde_factor > coset_idx);
        assert_eq!(
            num_elements, 1,
            "we query setup/witness oracles only by 1 element per leaf"
        );
        let (outer, inner) = split_inner(inner_idx, P::SIZE_FACTOR);
        for subsource in self.iter() {
            assert_eq!(subsource.storage[coset_idx].domain_size(), domain_size);
            let el = subsource.storage[coset_idx].storage[outer].as_base_elements()[inner];
            dst.push(el);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::field::goldilocks::GoldilocksField;
    use crate::field::{rand_from_rng, PrimeField, U64Representable};
    use rand::thread_rng;
    use std::alloc::Global;

    // poly c0, c1, c2, c3
    // folded (c0 + alpha * c1) + (c2 + alpha * c3) * y

    // by values
    // t0 = c0 + c1 * g + c2 * g^2 + c3 * g^3
    // t1 = c0 + c1 * g * omega - c2 * g^2 - c3 * g^3 * omega // omega^2 == -1
    // t2 = c0 - c1 * g + c2 * g^2 - c3 * g^3
    // t3 = c0 - c1 * g * omega - c2 * g^2 + c3 * g^3 * omega

    // folded by values

    // tt0 = (t0 + t2) + alpha * (t0 - t2) / (g * omega^0) = 2c0 + 2 g^2 * c2 + alpha * 2 * (c1 + g^2 * c3)
    // tt1 = (t1 + t3) + alpha * (t1 - t3) / (g * omega^1) = 2c0 - 2 g^2 * c2 + alpha * 2 * (c1 - g^2 * c3)

    // evaluate folded at g^2 and - g^2

    // ttt0 = folded(g^2) = c0 + alpha c1 + g^2 * c2 + g^2 * c3 * alpha
    // ttt1 = folded(- g^2) = c0 + alpha c1 - g^2 * c2 - g^2 * c3 * alpha

    // that only differs from tt0 and tt1 by the factor of 2

    // so simplified procedure to fold by value pushes us from coset of form g * {1, omega, ..} into coset of g^2 * {1, omega^2, ...}

    #[test]
    fn test_fri_over_coset() {
        type F = GoldilocksField;

        let alpha = F::from_u64_unchecked(1234);
        let worker = Worker::new_with_num_threads(1);

        let domain_size = 1 << 10;
        let mut rng = thread_rng();
        let monomials: Vec<_> = (0..domain_size)
            .map(|_| rand_from_rng::<_, F>(&mut rng))
            .collect();
        let forward_twiddles = <F as crate::field::traits::field_like::PrimeFieldLikeVectorized>::precompute_forward_twiddles_for_fft::<Global>(domain_size, &worker, &mut ());
        let inverse_twiddles = <F as crate::field::traits::field_like::PrimeFieldLikeVectorized>::precompute_inverse_twiddles_for_fft::<Global>(domain_size, &worker, &mut ());

        let coset = F::multiplicative_generator();
        // let coset = F::ONE;

        let mut values_on_coset = monomials.clone();
        <F as crate::field::traits::field_like::PrimeFieldLikeVectorized>::fft_natural_to_bitreversed(&mut values_on_coset, coset, &forward_twiddles, &mut ());

        let mut folded_monomials = Vec::with_capacity(domain_size / 2);
        for [even, odd] in monomials.array_chunks::<2>() {
            let mut tmp = *odd;
            tmp.mul_assign(&alpha);
            tmp.add_assign(even);
            folded_monomials.push(tmp);
        }

        let mut next_coset = coset;
        next_coset.square();

        let mut folded_from_monomials = folded_monomials.clone();
        let forward_twiddles_next = <F as crate::field::traits::field_like::PrimeFieldLikeVectorized>::precompute_forward_twiddles_for_fft::<Global>(domain_size / 2, &worker, &mut ());
        <F as crate::field::traits::field_like::PrimeFieldLikeVectorized>::fft_natural_to_bitreversed(&mut folded_from_monomials, next_coset, &forward_twiddles_next, &mut ());

        // now do the same by value

        let two_inverse = F::TWO.inverse().unwrap();
        let gen_inverse = coset.inverse().unwrap();

        let mut folded_by_values = vec![];
        for (idx, [even, odd]) in values_on_coset.array_chunks::<2>().enumerate() {
            let mut diff = *even;
            diff.sub_assign(odd);
            diff.mul_assign(&alpha);
            diff.mul_assign(&inverse_twiddles[idx]);
            diff.mul_assign(&gen_inverse);

            let mut sum = *even;
            sum.add_assign(odd);
            sum.add_assign(&diff);

            sum.mul_assign(&two_inverse);

            folded_by_values.push(sum);
        }

        let inverse_twiddles_next = <F as crate::field::traits::field_like::PrimeFieldLikeVectorized>::precompute_inverse_twiddles_for_fft::<Global>(domain_size / 2, &worker, &mut ());
        let mut monomials_from_values = folded_by_values.clone();
        bitreverse_enumeration_inplace(&mut monomials_from_values);
        <F as crate::field::traits::field_like::PrimeFieldLikeVectorized>::ifft_natural_to_natural(
            &mut monomials_from_values,
            next_coset,
            &inverse_twiddles_next,
            &mut (),
        );

        assert_eq!(&monomials_from_values, &folded_monomials);

        assert_eq!(&folded_by_values, &folded_from_monomials);
    }
}
