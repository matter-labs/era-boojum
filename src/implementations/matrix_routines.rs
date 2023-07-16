//! Useful functions for dealing with matrices.
use crate::field::SmallField;

pub const fn array_const_equal<T: PartialEq, const N: usize>(a: &[T; N], b: &[T; N]) -> bool {
    let mut idx = 0;
    while idx < N {
        if a[idx] != b[idx] {
            return false;
        }
        idx += 1;
    }

    true
}

pub const fn matrix_const_equal<T: PartialEq, const N: usize, const M: usize>(
    a: &[[T; N]; M],
    b: &[[T; N]; M],
) -> bool {
    let mut row = 0;
    while row < M {
        let mut column = 0;
        while column < N {
            if a[row][column] != b[row][column] {
                return false;
            }
            column += 1;
        }
        row += 1;
    }

    true
}

pub const fn square_matrix_transpose<F: SmallField, const N: usize>(
    a: &[[F; N]; N],
) -> [[F; N]; N] {
    let mut result = [[F::ZERO; N]; N];
    // we want to assign columns to rows
    let mut column = 0;
    while column < N {
        let mut idx = 0;
        while idx < N {
            result[column][idx] = a[idx][column];
            idx += 1;
        }
        column += 1;
    }

    result
}

pub const fn identity_matrix<F: SmallField, const N: usize>() -> [[F; N]; N] {
    let mut result = [[F::ZERO; N]; N];
    let mut idx = 0;
    while idx < N {
        result[idx][idx] = F::ONE;
        idx += 1;
    }

    result
}

pub const fn square_matrix_negate<F: SmallField, const N: usize>(a: &mut [[F; N]; N]) {
    let mut row = 0;
    while row < N {
        let mut column = 0;
        while column < N {
            a[row][column].negate();
            column += 1;
        }

        row += 1;
    }

    square_matrix_by_matrix_make_canonical(a);
}

// constant time matrix addition for precomputations
// assumes inputs in row-major order, so inner array is a row
pub const fn square_matrix_add<F: SmallField, const N: usize>(
    a: &[[F; N]; N],
    b: &[[F; N]; N],
) -> [[F; N]; N] {
    let mut result = *a;
    let mut row = 0;
    while row < N {
        let mut column = 0;
        while column < N {
            result[row][column].add_assign(&b[row][column]);
            column += 1;
        }

        row += 1;
    }

    square_matrix_by_matrix_make_canonical(&mut result);

    result
}

// constant time matrix subtraction for precomputations
// assumes inputs in row-major order, so inner array is a row
pub const fn square_matrix_sub<F: SmallField, const N: usize>(
    a: &[[F; N]; N],
    b: &[[F; N]; N],
) -> [[F; N]; N] {
    let mut result = *a;
    let mut row = 0;
    while row < N {
        let mut column = 0;
        while column < N {
            result[row][column].sub_assign(&b[row][column]);
            column += 1;
        }

        row += 1;
    }

    square_matrix_by_matrix_make_canonical(&mut result);

    result
}

pub const fn square_matrix_by_vector_multiply<F: SmallField, const N: usize>(
    a: &[[F; N]; N],
    b: &[F; N],
) -> [F; N] {
    let mut result = [F::ZERO; N];
    let mut row = 0;
    while row < N {
        let mut column = 0;
        let a_row = &a[row];
        while column < N {
            let mut tmp = a_row[column];
            tmp.mul_assign(&b[column]);
            result[row].add_assign(&tmp);
            column += 1;
        }

        row += 1;
    }

    row_make_canonical(&mut result);

    result
}

// constant time matrix multiplication for precomputations
// assumes inputs in row-major order, so inner array is a row
pub const fn square_matrix_by_matrix_multiply<F: SmallField, const N: usize>(
    a: &[[F; N]; N],
    b: &[[F; N]; N],
) -> [[F; N]; N] {
    let b = square_matrix_transpose(b);
    let mut result = [[F::ZERO; N]; N];
    let mut row = 0;
    while row < N {
        let mut column = 0;
        while column < N {
            let a_row = &a[row];
            let b_row = &b[column];
            let mut idx = 0;
            while idx < N {
                let mut tmp = a_row[idx];
                tmp.mul_assign(&b_row[idx]);
                result[row][column].add_assign(&tmp);

                idx += 1;
            }

            column += 1;
        }

        row += 1;
    }

    square_matrix_by_matrix_make_canonical(&mut result);

    result
}

pub const fn mul_row_by_element<F: SmallField, const N: usize>(row: &mut [F; N], by: &F) {
    let mut idx = 0;
    while idx < N {
        row[idx].mul_assign(by);
        idx += 1;
    }
}

pub const fn row_add_assign<F: SmallField, const N: usize>(a: &mut [F; N], b: &[F; N]) {
    let mut idx = 0;
    while idx < N {
        a[idx].add_assign(&b[idx]);
        idx += 1;
    }

    row_make_canonical(a);
}

pub const fn row_sub_assign<F: SmallField, const N: usize>(a: &mut [F; N], b: &[F; N]) {
    let mut idx = 0;
    while idx < N {
        a[idx].sub_assign(&b[idx]);
        idx += 1;
    }

    row_make_canonical(a);
}

pub const fn row_make_canonical<F: SmallField, const N: usize>(a: &mut [F; N]) {
    let mut idx = 0;
    while idx < N {
        a[idx] = F::from_u64_with_reduction(a[idx].as_u64_reduced());
        idx += 1;
    }
}

pub const fn square_matrix_by_matrix_make_canonical<F: SmallField, const N: usize>(
    a: &mut [[F; N]; N],
) {
    let mut row = 0;
    while row < N {
        let mut column = 0;
        while column < N {
            a[row][column] = F::from_u64_with_reduction(a[row][column].as_u64_reduced());
            column += 1;
        }

        row += 1;
    }
}

// constant time matrix inversion for precomputations
pub const fn matrix_inverse<F: SmallField, const N: usize>(input: &[[F; N]; N]) -> [[F; N]; N] {
    if N == 1 {
        let inv = input[0][0].inverse().expect("must exist");
        let output = [[inv]];
        let output: [[F; N]; N] = unsafe { *(&output as *const _ as *const _) };

        return output;
    } else if N == 2 {
        // this is safe, but just std::mem::transmute will not work due to size
        // not known before monomorphization
        let tmp: [[F; 2]; 2] = unsafe { *(&input as *const _ as *const _) };
        let output = matrix_inverse_2x2(&tmp);
        let output: [[F; N]; N] = unsafe { *(&output as *const _ as *const _) };

        return output;
    } else if N == 3 {
        let tmp: [[F; 3]; 3] = unsafe { *(&input as *const _ as *const _) };
        let output = matrix_inverse_3x3(&tmp);
        let output: [[F; N]; N] = unsafe { *(&output as *const _ as *const _) };

        return output;
    } else {
        // Gaussian elimination

        let mut lhs = *input;
        let mut rhs = identity_matrix::<F, N>();

        let mut diag_idx = 0;
        while diag_idx < N {
            // normalize a row
            let coeff = lhs[diag_idx][diag_idx].inverse().expect("must exist");
            mul_row_by_element(&mut lhs[diag_idx], &coeff);
            mul_row_by_element(&mut rhs[diag_idx], &coeff);

            debug_assert!(lhs[diag_idx][diag_idx] == F::ONE);

            // perform elimination
            let mut another_row = 0;
            while another_row < N {
                if another_row == diag_idx {
                    another_row += 1;
                    continue;
                }

                let coeff = lhs[another_row][diag_idx];
                let mut tmp = lhs[diag_idx];
                mul_row_by_element(&mut tmp, &coeff);
                row_sub_assign(&mut lhs[another_row], &tmp);

                let mut tmp = rhs[diag_idx];
                mul_row_by_element(&mut tmp, &coeff);
                row_sub_assign(&mut rhs[another_row], &tmp);

                debug_assert!(lhs[another_row][diag_idx] == F::ZERO);

                another_row += 1
            }

            diag_idx += 1;
        }

        return rhs;
    }
}

// // constant time matrix inversion for precomputations
// pub const fn matrix_inverse<F:  SmallField, const N: usize>(
//     input: &[[F; N]; N]
// ) -> [[F; N]; N] where [(); N/2]:, [(); N*2]: {
//     if N == 1 {
//         let inv = input[0][0].inverse().expect("must exist");
//         let output = [[inv]];
//         let output: [[F; N]; N] = unsafe { *(&output as *const _ as *const _) };

//         return output;
//     } else if N == 2 {
//         // this is safe, but just std::mem::transmute will not work due to size
//         // not known before monomorphization
//         let tmp: [[F; 2]; 2] = unsafe { *(&input as *const _ as *const _) };
//         let output = matrix_inverse_2x2(&tmp);
//         let output: [[F; N]; N] = unsafe { *(&output as *const _ as *const _) };

//         return output;
//     } else if N == 3 {
//         let tmp: [[F; 3]; 3] = unsafe { *(&input as *const _ as *const _) };
//         let output = matrix_inverse_3x3(&tmp);
//         let output: [[F; N]; N] = unsafe { *(&output as *const _ as *const _) };

//         return output;
//     } else {
//         // recursive block matrix algo
//         let [[aa, bb], [cc, dd]] = block_matrix_decompose::<F, N>(&input);
//         let aa: [[F; N/2]; N/2] = aa;
//         let aa_inv = matrix_inverse::<F, {N/2}>(&aa);
//         // we do not need any other inverses

//         let mut cc_aainv_bb = square_matrix_by_matrix_multiply(&cc, &aa_inv);
//         cc_aainv_bb = square_matrix_by_matrix_multiply(&cc_aainv_bb, &bb);

//         let dd_minus_cc_aainv_bb = square_matrix_sub(&dd, &cc_aainv_bb);

//         let mut tmp = square_matrix_by_matrix_multiply(&aa_inv, &bb);
//         tmp = square_matrix_by_matrix_multiply(&tmp, &dd_minus_cc_aainv_bb);
//         tmp = square_matrix_by_matrix_multiply(&tmp, &cc);
//         tmp = square_matrix_by_matrix_multiply(&tmp, &aa_inv);

//         let aaa = square_matrix_add(&aa, &tmp);

//         let mut bbb = square_matrix_by_matrix_multiply(&aa_inv, &bb);
//         bbb = square_matrix_by_matrix_multiply(&bbb, &dd_minus_cc_aainv_bb);
//         square_matrix_negate(&mut bbb);

//         let mut ccc = square_matrix_by_matrix_multiply(&dd_minus_cc_aainv_bb, &cc);
//         ccc = square_matrix_by_matrix_multiply(&ccc, &aa_inv);
//         square_matrix_negate(&mut ccc);

//         let ddd = dd_minus_cc_aainv_bb;

//         let block_result = [
//             [aaa, bbb],
//             [ccc, ddd]
//         ];

//         let tmp = block_matrix_recompose(&block_result);

//         return unsafe { *(&tmp as *const _ as *const _) };
//     }
// }

pub const fn matrix_inverse_2x2<F: SmallField>(input: &[[F; 2]; 2]) -> [[F; 2]; 2] {
    let mut ad = input[0][0];
    ad.mul_assign(&input[1][1]);

    let mut bc = input[1][0];
    bc.mul_assign(&input[0][1]);

    let mut det = ad;
    det.sub_assign(&bc);

    let mut result = [[input[1][1], input[0][1]], [input[1][0], input[0][0]]];

    result[0][1].negate();
    result[1][0].negate();

    let det_inv = det.inverse().expect("must exist");
    result[0][0].mul_assign(&det_inv);
    result[0][1].mul_assign(&det_inv);
    result[1][0].mul_assign(&det_inv);
    result[1][1].mul_assign(&det_inv);

    result
}

// pub const fn block_matrix_decompose<F:  SmallField, const N: usize>(
//     a: &[[F; N]; N],
// ) -> [[[[F; N/2]; N/2]; 2]; 2] where [(); N/2]: {
//     let mut result = [[[[F::ZERO; N/2]; N/2]; 2]; 2];

//     let mut block_row = 0;
//     while block_row < 2 {
//         let mut block_column = 0;
//         while block_column < 2 {
//             // copy
//             let row_offset = N/2 * block_row;
//             let column_offset = N/2 * block_column;

//             let mut row = 0;
//             while row < N/2 {
//                 let mut column = 0;
//                 while column < N/2 {
//                     result[block_row][block_column][row][column] =
//                         a[row + row_offset][column + column_offset];

//                     column += 1;
//                 }
//                 row += 1;
//             }

//             block_column += 1;
//         }

//         block_row += 1;
//     }

//     result
// }

// pub const fn block_matrix_recompose<F:  SmallField, const N: usize>(
//     a: &[[[[F; N]; N]; 2]; 2],
// ) -> [[F; N*2]; N*2] where [(); N*2]: {
//     let mut result = [[F::ZERO; N*2]; N*2];

//     let mut block_row = 0;
//     while block_row < 2 {
//         let mut block_column = 0;
//         while block_column < 2 {
//             // copy
//             let row_offset = N/2 * block_row;
//             let column_offset = N/2 * block_column;

//             let mut row = 0;
//             while row < N/2 {
//                 let mut column = 0;
//                 while column < N/2 {
//                     result[row + row_offset][column + column_offset] =
//                         a[block_row][block_column][row][column];

//                     column += 1;
//                 }
//                 row += 1;
//             }

//             block_column += 1;
//         }

//         block_row += 1;
//     }

//     result
// }

pub const fn matrix_inverse_3x3<F: SmallField>(input: &[[F; 3]; 3]) -> [[F; 3]; 3] {
    let [[a, b, c], [d, e, f], [g, h, i]] = *input;

    let mut ei = e;
    ei.mul_assign(&i);

    let mut fh = f;
    fh.mul_assign(&h);

    let mut aa = ei;
    aa.sub_assign(&fh);

    let mut di = d;
    di.mul_assign(&i);

    let mut fg = f;
    fg.mul_assign(&g);

    let mut bb = fg;
    bb.sub_assign(&di);

    let mut dh = d;
    dh.mul_assign(&h);

    let mut eg = e;
    eg.mul_assign(&g);

    let mut cc = dh;
    cc.sub_assign(&eg);

    let mut tmp = a;
    tmp.mul_assign(&aa);

    let mut det = tmp;

    let mut tmp = b;
    tmp.mul_assign(&bb);
    det.add_assign(&tmp);

    let mut tmp = c;
    tmp.mul_assign(&cc);
    det.add_assign(&tmp);

    // drop(ei);
    // drop(fh);
    // drop(di);
    // drop(fg);
    // drop(dh);
    // drop(eg);

    // now the other two columns

    let mut bi = b;
    bi.mul_assign(&i);

    let mut ch = c;
    ch.mul_assign(&h);

    let mut dd = ch;
    dd.sub_assign(&bi);

    let mut ai = a;
    ai.mul_assign(&i);

    let mut cg = c;
    cg.mul_assign(&g);

    let mut ee = ai;
    ee.sub_assign(&cg);

    let mut ah = a;
    ah.mul_assign(&h);

    let mut bg = b;
    bg.mul_assign(&g);

    let mut ff = bg;
    ff.sub_assign(&ah);

    // drop(bi);
    // drop(ch);
    // drop(ai);
    // drop(cg);
    // drop(ah);
    // drop(eg);

    // and the last one

    let mut bf = b;
    bf.mul_assign(&f);

    let mut ce = c;
    ce.mul_assign(&f);

    let mut gg = bf;
    gg.sub_assign(&ce);

    let mut af = a;
    af.mul_assign(&f);

    let mut cd = c;
    cd.mul_assign(&d);

    let mut hh = cd;
    hh.sub_assign(&af);

    let mut ae = a;
    ae.mul_assign(&e);

    let mut bd = b;
    bd.mul_assign(&d);

    let mut ii = ae;
    ii.sub_assign(&bd);

    // drop(bf);
    // drop(ce);
    // drop(af);
    // drop(cd);
    // drop(ae);
    // drop(bd);

    let mut result = [[aa, dd, gg], [bb, ee, hh], [cc, ff, ii]];

    let det_inv = det.inverse().expect("must exist");
    result[0][0].mul_assign(&det_inv);
    result[0][1].mul_assign(&det_inv);
    result[0][2].mul_assign(&det_inv);
    result[1][0].mul_assign(&det_inv);
    result[1][1].mul_assign(&det_inv);
    result[1][2].mul_assign(&det_inv);
    result[2][0].mul_assign(&det_inv);
    result[2][1].mul_assign(&det_inv);
    result[2][2].mul_assign(&det_inv);

    result
}

#[cfg(test)]
mod test {
    use crate::field::{goldilocks::GoldilocksField, Field};

    use super::*;

    type F = GoldilocksField;

    #[test]
    fn test_trivial_transpose() {
        const INPUT: [[F; 3]; 3] = [
            [
                F::ONE,
                F::RADIX_2_SUBGROUP_GENERATOR,
                F::MULTIPLICATIVE_GROUP_GENERATOR,
            ],
            [F::ZERO, F::MINUS_ONE, F::MINUS_ONE],
            [F::MULTIPLICATIVE_GROUP_GENERATOR, F::ONE, F::ONE],
        ];

        dbg!(&INPUT);

        const TRANSPOSED: [[F; 3]; 3] = square_matrix_transpose(&INPUT);

        dbg!(&TRANSPOSED);
    }

    #[test]
    fn test_inverse_2x2() {
        const INPUT: [[F; 2]; 2] = [
            [F::ONE, F::RADIX_2_SUBGROUP_GENERATOR],
            [F::MINUS_ONE, F::MINUS_ONE],
        ];

        const INVERSED: [[F; 2]; 2] = matrix_inverse_2x2(&INPUT);

        const EXPECTED_IDENTITY: [[F; 2]; 2] = square_matrix_by_matrix_multiply(&INPUT, &INVERSED);

        dbg!(&EXPECTED_IDENTITY);

        assert_eq!(EXPECTED_IDENTITY, identity_matrix::<F, 2>());
    }

    #[test]
    fn test_inverse_3x3() {
        const INPUT: [[F; 3]; 3] = [
            [
                F::ONE,
                F::RADIX_2_SUBGROUP_GENERATOR,
                F::MULTIPLICATIVE_GROUP_GENERATOR,
            ],
            [F::ZERO, F::MINUS_ONE, F::MINUS_ONE],
            [F::MULTIPLICATIVE_GROUP_GENERATOR, F::ONE, F::ONE],
        ];

        const INVERSED: [[F; 3]; 3] = matrix_inverse_3x3(&INPUT);

        const EXPECTED_IDENTITY: [[F; 3]; 3] = square_matrix_by_matrix_multiply(&INPUT, &INVERSED);

        dbg!(&EXPECTED_IDENTITY);

        assert_eq!(EXPECTED_IDENTITY, identity_matrix::<F, 3>());
    }

    #[test]
    fn test_inverse_gaussian() {
        const INPUT: [[F; 4]; 4] = [
            [
                F::ONE,
                F::RADIX_2_SUBGROUP_GENERATOR,
                F::MULTIPLICATIVE_GROUP_GENERATOR,
                F::ONE,
            ],
            [
                F::ZERO,
                F::MINUS_ONE,
                F::MINUS_ONE,
                F::RADIX_2_SUBGROUP_GENERATOR,
            ],
            [
                F::MULTIPLICATIVE_GROUP_GENERATOR,
                F::ONE,
                F::ONE,
                F::RADIX_2_SUBGROUP_GENERATOR,
            ],
            [F::MINUS_ONE, F::ONE, F::ONE, F::MINUS_ONE],
        ];

        const INVERSED: [[F; 4]; 4] = matrix_inverse(&INPUT);

        const EXPECTED_IDENTITY: [[F; 4]; 4] = square_matrix_by_matrix_multiply(&INPUT, &INVERSED);

        dbg!(&EXPECTED_IDENTITY);

        assert_eq!(EXPECTED_IDENTITY, identity_matrix::<F, 4>());
    }
}
