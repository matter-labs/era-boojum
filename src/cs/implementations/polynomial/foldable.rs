use crate::field::{rand_from_rng, SmallField};

#[derive(Clone, Debug)]
pub struct GeneratorMatrix<F: SmallField> {
    pub base_matrix: Vec<Vec<F>>,
    pub diagonal_matrices: Vec<Vec<F>>,
    pub negated_diagonal_matrices: Vec<Vec<F>>,
}

impl<F: SmallField> GeneratorMatrix<F> {
    pub fn new(degree: usize, rate: usize) -> GeneratorMatrix<F> {
        assert!(F::TWO_ADICITY >= degree);

        let mut diagonal_matrices = Vec::with_capacity(degree);
        let mut negated_diagonal_matrices = Vec::with_capacity(degree);
        let mut rng = rand::thread_rng();

        let mut base_matrix = vec![vec![F::ZERO; 1]; rate];
        for column in base_matrix.iter_mut() {
            for entry in column.iter_mut() {
                *entry = rand_from_rng(&mut rng);
            }
        }

        let mut size = rate;
        for _ in 0..degree {
            let (diag, diag_neg) = {
                let mut diag = vec![F::ZERO; size];
                diag.iter_mut().for_each(|el| *el = rand_from_rng(&mut rng));
                let mut diag_neg = diag.clone();
                diag_neg.iter_mut().for_each(|el| *el = *el.negate());
                (diag, diag_neg)
            };
            diagonal_matrices.push(diag);
            negated_diagonal_matrices.push(diag_neg);
            size *= 2;
        }

        GeneratorMatrix {
            base_matrix,
            diagonal_matrices,
            negated_diagonal_matrices,
        }
    }

    pub fn encode(&self, mut poly: Vec<F>, degree: usize) -> Vec<F> {
        assert!(poly.len().is_power_of_two());
        assert_eq!(poly.len(), 2i32.pow(degree.try_into().unwrap()) as usize);

        if degree != 0 {
            let right_poly = poly.split_off(poly.len() / 2);
            let diag = &self.diagonal_matrices[degree - 1];
            let l = self.encode(poly, degree - 1);
            let r = self.encode(right_poly, degree - 1);
            let t_hadamard_r = diag
                .iter()
                .zip(r.iter())
                .map(|(d, r)| {
                    let mut d = d.clone();
                    d.mul_assign(r);
                    d
                })
                .collect::<Vec<F>>();
            let mut left = l
                .iter()
                .zip(t_hadamard_r.iter())
                .map(|(l, r)| {
                    let mut l = l.clone();
                    l.add_assign(r);
                    l
                })
                .collect::<Vec<F>>();
            let right = l
                .iter()
                .zip(t_hadamard_r.iter())
                .map(|(l, r)| {
                    let mut l = l.clone();
                    l.sub_assign(r);
                    l
                })
                .collect::<Vec<F>>();
            left.extend(right);
            left
        } else {
            // degree is 0 so poly length is 1, and so our multiplication is just elementwise over
            // the first row
            self.base_matrix
                .iter()
                .map(|el| {
                    let mut el = el[0].clone();
                    el.mul_assign(&poly[0]);
                    el
                })
                .collect::<Vec<F>>()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::goldilocks::GoldilocksField;
    use crate::field::traits::field::Field;

    #[test]
    fn generate_matrix() {
        let _ = GeneratorMatrix::<GoldilocksField>::new(10, 8);
    }

    #[test]
    fn encode_poly() {
        let mut rng = rand::thread_rng();
        let matrices = GeneratorMatrix::<GoldilocksField>::new(6, 8);
        let mut poly = vec![GoldilocksField::ZERO; 32];
        poly.iter_mut().for_each(|el| *el = rand_from_rng(&mut rng));
        let result = matrices.encode(poly, 5);
        assert_eq!(result.len(), 32 * 8);
    }
}
