use super::polynomial::foldable::GeneratorMatrix;
use crate::cs::implementations::transcript::Transcript;
use crate::field::SmallField;
use rand::Rng;

// Commit phase for basefold. From an input oracle, we proceed to fold down to an oracle of a
// single element.
//
// TODO(jules): needs to take in encodings in quadratic extension for soundness
pub fn do_basefold<F: SmallField, T: Transcript<F>>(
    transcript: &mut T,
    matrices: &GeneratorMatrix<F>,
    encoding: Vec<F>,
    degree: usize,
) -> (Vec<Vec<F>>, Vec<F>) {
    assert!(encoding.len().is_power_of_two());
    assert!(degree <= matrices.diagonal_matrices.len() - 1);

    let mut oracles = Vec::with_capacity(degree + 1);
    let mut challenges = Vec::with_capacity(degree);
    let mut current_oracle = encoding;
    oracles.push(current_oracle.clone());
    let mut size = current_oracle.len() >> 1;
    for i in 0..degree {
        let mut new_oracle = Vec::with_capacity(size);
        let alpha = transcript.get_challenge();
        challenges.push(alpha);
        let diag = &matrices.diagonal_matrices[degree - 1 - i];
        let diag_neg = &matrices.negated_diagonal_matrices[degree - 1 - i];
        // TODO(jules): this can be parallelized and made way more efficient
        for j in 0..size {
            let f_x = interpolate_linear_poly([
                (diag[j], current_oracle[j]),
                (diag_neg[j], current_oracle[j + size]),
            ]);
            new_oracle.push(eval_linear_poly(f_x, &alpha));
        }

        current_oracle = new_oracle;
        oracles.push(current_oracle.clone());
        size >>= 1;
    }

    (oracles, challenges)
}

// Query phase of basefold. A verifier checks for consistencies in the given oracles and
// challenges, and outputs accept if the final oracle is a codeword in the base generator matrix
// (which is implied if all the consistency checks pass).
pub fn query<F: SmallField>(
    matrices: &GeneratorMatrix<F>,
    oracles: Vec<Vec<F>>,
    challenges: Vec<F>,
) -> bool {
    assert_eq!(challenges.len() + 1, oracles.len());
    assert!(challenges.len() <= matrices.diagonal_matrices.len() - 1);

    let mut rng = rand::thread_rng();
    let mut index = rng.gen_range(0..oracles[1].len());
    // TODO(jules): believe this can also be parallelized but it's already quite fast so maybe the
    // gain is negligible here
    for (i, challenge) in challenges.iter().enumerate() {
        let diag = &matrices.diagonal_matrices[challenges.len() - 1 - i];
        let diag_neg = &matrices.negated_diagonal_matrices[challenges.len() - 1 - i];

        let p_x = interpolate_linear_poly([
            (diag[index], oracles[i][index]),
            (diag_neg[index], oracles[i][index + oracles[i + 1].len()]),
        ]);

        let eval = eval_linear_poly(p_x, challenge);
        if eval != oracles[i + 1][index] {
            return false;
        }

        if i != challenges.len() - 1 && index >= oracles[i + 2].len() {
            index -= oracles[i + 2].len();
        }
    }

    true
}

// Degree-1 Lagrange interpolation.
//
// For points (x_0, f(x_0)), (x_1, f(x_1)), computes p(x) such that
// p(x_0) = f(x_0) and p(x_1) = f(x_1).
fn interpolate_linear_poly<F: SmallField>(x_y: [(F, F); 2]) -> [F; 2] {
    // L_0(X) = X - x_1 / x_0 - x_1.
    // This becomes -x_1 * (x_0 - x_1)^-1 + X * (x_0 - x_1)^-1.
    let l0_coeffs = {
        let mut first = x_y[1].0;
        first.negate();
        let mut second = x_y[0].0;
        second.sub_assign(&x_y[1].0);
        second = second.inverse().unwrap();
        first.mul_assign(&second);
        [first, second]
    };
    // L_1(X) = X - x_0 / x_1 - x_0.
    // This becomes -x_0 * (x_1 - x_0)^-1 + X * (x_1 - x_0)^-1.
    let l1_coeffs = {
        let mut first = x_y[0].0;
        first.negate();
        let mut second = x_y[1].0;
        second.sub_assign(&x_y[0].0);
        second = second.inverse().unwrap();
        first.mul_assign(&second);
        [first, second]
    };

    // L_0(X)f(x_0)
    let l0 = l0_coeffs.into_iter().map(|el| {
        let mut el = el;
        el.mul_assign(&x_y[0].1);
        el
    });
    // L_1(X)f(x_1)
    let l1 = l1_coeffs.into_iter().map(|el| {
        let mut el = el;
        el.mul_assign(&x_y[1].1);
        el
    });

    // L_0(X)f(x_0) + L_1(X)f(x_1)
    l0.zip(l1)
        .map(|(a, b)| {
            let mut r = a;
            r.add_assign(&b);
            r
        })
        .collect::<Vec<F>>()
        .try_into()
        .expect("should always be able to make 2 element array from 2 element vector")
}

fn eval_linear_poly<F: SmallField>(poly: [F; 2], point: &F) -> F {
    let mut eval = poly[0];
    let mut alpha = point.clone();
    alpha.mul_assign(&poly[1]);
    eval.add_assign(&alpha);
    eval
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cs::implementations::transcript::GoldilocksPoisedon2Transcript;
    use crate::field::goldilocks::GoldilocksField;
    use crate::field::rand_from_rng;
    use crate::field::traits::field::Field;

    #[test]
    fn test_commit_query() {
        let mut rng = rand::thread_rng();
        let degree = 25;
        let rate = 8;
        let now = std::time::Instant::now();
        let matrices = GeneratorMatrix::<GoldilocksField>::new(degree, rate);
        println!("GENERATING MATRICES {:?}", now.elapsed());
        let mut poly = vec![GoldilocksField::ZERO; 2i32.pow(degree as u32) as usize];
        poly.iter_mut().for_each(|el| *el = rand_from_rng(&mut rng));
        let now = std::time::Instant::now();
        let result = matrices.encode(poly, degree);
        println!("ENCODING POLY {:?}", now.elapsed());
        let mut transcript = GoldilocksPoisedon2Transcript::new(());
        let now = std::time::Instant::now();
        let (oracles, challenges) = do_basefold(&mut transcript, &matrices, result, degree);
        println!("PROVING {:?}", now.elapsed());
        let now = std::time::Instant::now();
        assert!(query(&matrices, oracles, challenges));
        println!("VERIFYING {:?}", now.elapsed());
    }

    #[test]
    fn test_commit_query_wrong_matrices() {
        let mut rng = rand::thread_rng();
        let degree = 16;
        let rate = 8;
        let matrices = GeneratorMatrix::<GoldilocksField>::new(degree, rate);
        let mut poly = vec![GoldilocksField::ZERO; 2i32.pow(degree as u32) as usize];
        poly.iter_mut().for_each(|el| *el = rand_from_rng(&mut rng));
        let result = matrices.encode(poly, degree);
        let mut transcript = GoldilocksPoisedon2Transcript::new(());
        let (oracles, challenges) = do_basefold(&mut transcript, &matrices, result, degree);
        let false_matrices = GeneratorMatrix::<GoldilocksField>::new(degree, rate);
        assert!(!query(&false_matrices, oracles, challenges));
    }
}
