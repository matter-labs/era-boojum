use super::polynomial::foldable::GeneratorMatrix;
use crate::cs::implementations::transcript::Transcript;
use crate::field::SmallField;
use rand::Rng;

// Commit phase for basefold. From an input oracle, we proceed to fold down to an oracle of a
// single element.
pub fn do_basefold<F: SmallField, T: Transcript<F>>(
    transcript: &mut T,
    matrices: &GeneratorMatrix<F>,
    encoding: Vec<F>,
    degree: usize,
) -> (Vec<Vec<F>>, Vec<F>) {
    let mut oracles = vec![];
    let mut challenges = vec![];
    let mut current_oracle = encoding;
    oracles.push(current_oracle.clone());
    let mut size = current_oracle.len() / 2;
    for i in 0..degree {
        let mut new_oracle = vec![];
        let alpha = transcript.get_challenge();
        challenges.push(alpha);
        for j in 0..size {
            let diag = &matrices.diagonal_matrices[degree - 1 - i];
            let mut diag_j_negated = diag[j].clone();
            diag_j_negated.negate();

            let f_x = interpolate_linear_poly([
                (diag[j], current_oracle[j]),
                (diag_j_negated, current_oracle[j + size]),
            ]);
            new_oracle.push(eval_linear_poly(f_x, &alpha));
        }

        current_oracle = new_oracle;
        oracles.push(current_oracle.clone());
        size /= 2;
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
    let mut rng = rand::thread_rng();
    let mut index = rng.gen_range(0..oracles[1].len());
    for (i, challenge) in challenges.iter().enumerate() {
        let diag = &matrices.diagonal_matrices[challenges.len() - 1 - i];
        let mut diag_index_negated = diag[index].clone();
        diag_index_negated.negate();

        let p_x = interpolate_linear_poly([
            (diag[index], oracles[i][index]),
            (diag_index_negated, oracles[i][index + oracles[i + 1].len()]),
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
        let mut first = x_y[1].0.clone();
        first.negate();
        let mut second = x_y[0].0.clone();
        second.sub_assign(&x_y[1].0);
        second = second.inverse().unwrap();
        first.mul_assign(&second);
        vec![first, second]
    };
    // L_1(X) = X - x_0 / x_1 - x_0.
    // This becomes -x_0 * (x_1 - x_0)^-1 + X * (x_1 - x_0)^-1.
    let l1_coeffs = {
        let mut first = x_y[0].0.clone();
        first.negate();
        let mut second = x_y[1].0.clone();
        second.sub_assign(&x_y[0].0);
        second = second.inverse().unwrap();
        first.mul_assign(&second);
        vec![first, second]
    };

    // L_0(X)f(x_0)
    let l0 = l0_coeffs
        .iter()
        .map(|el| {
            let mut el = el.clone();
            el.mul_assign(&x_y[0].1);
            el
        })
        .collect::<Vec<F>>();
    // L_1(X)f(x_1)
    let l1 = l1_coeffs
        .iter()
        .map(|el| {
            let mut el = el.clone();
            el.mul_assign(&x_y[1].1);
            el
        })
        .collect::<Vec<F>>();

    // L_0(X)f(x_0) + L_1(X)f(x_1)
    l0.iter()
        .zip(l1.iter())
        .map(|(a, b)| {
            let mut r = a.clone();
            r.add_assign(b);
            r
        })
        .collect::<Vec<F>>()
        .try_into()
        .expect("should always be able to make 2 element array from 2 element vector")
}

fn eval_linear_poly<F: SmallField>(poly: [F; 2], point: &F) -> F {
    let mut eval = poly[0].clone();
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
        println!("{:?}", now.elapsed());
        let mut poly = vec![GoldilocksField::ZERO; 2i32.pow(degree as u32) as usize];
        poly.iter_mut().for_each(|el| *el = rand_from_rng(&mut rng));
        let result = matrices.encode(poly, degree);
        let mut transcript = GoldilocksPoisedon2Transcript::new(());
        let now = std::time::Instant::now();
        let (oracles, challenges) = do_basefold(&mut transcript, &matrices, result, degree);
        println!("{:?}", now.elapsed());
        assert!(query(&matrices, oracles, challenges));
    }

    //#[test]
    //fn test_commit_query_wrong_matrices() {
    //    let mut rng = rand::thread_rng();
    //    let degree = 16;
    //    let rate = 8;
    //    let matrices = GeneratorMatrix::<GoldilocksField>::new(degree, rate);
    //    let mut poly = vec![GoldilocksField::ZERO; 2i32.pow(degree as u32) as usize];
    //    poly.iter_mut().for_each(|el| *el = rand_from_rng(&mut rng));
    //    let result = matrices.encode(poly, degree);
    //    let mut transcript = GoldilocksPoisedon2Transcript::new(());
    //    let (oracles, challenges) = do_basefold(&mut transcript, &matrices, result, degree);
    //    let false_matrices = GeneratorMatrix::<GoldilocksField>::new(degree, rate);
    //    assert!(!query(&false_matrices, oracles, challenges));
    //}

    //#[test]
    //fn test_commit_query_wrong_matrices_2() {
    //    let mut rng = rand::thread_rng();
    //    let degree = 16;
    //    let rate = 8;
    //    let matrices = GeneratorMatrix::<GoldilocksField>::new(degree, rate);
    //    let mut poly = vec![GoldilocksField::ZERO; 2i32.pow(degree as u32) as usize];
    //    poly.iter_mut().for_each(|el| *el = rand_from_rng(&mut rng));
    //    let result = matrices.encode(poly.clone(), degree);
    //    let mut transcript = GoldilocksPoisedon2Transcript::new(());
    //    let false_matrices = GeneratorMatrix::<GoldilocksField>::new(degree, rate);
    //    let new_result = false_matrices.encode(poly, degree);
    //    assert_ne!(result, new_result);
    //    let (oracles, challenges) = do_basefold(&mut transcript, &false_matrices, result, degree);
    //    assert!(!query(&false_matrices, oracles, challenges));
    //}
}
