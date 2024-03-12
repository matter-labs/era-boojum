use crate::cs::implementations::lookup_table::LookupTable;
use crate::field::SmallField;
use derivative::*;

const TABLE_NAME: &'static str = "WNAFDECOMP table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WnafDecompTable;

const GLV_WINDOW_SIZE: usize = 2;
const TABLE_SIZE: i8 = 1 << (GLV_WINDOW_SIZE + 1);
const HALF_TABLE_SIZE: i8 = 1 << GLV_WINDOW_SIZE;
const MASK_FOR_MOD_TABLE_SIZE: u8 = (TABLE_SIZE as u8) - 1;

// Lookups for wNAF decomposition of scalars.
pub fn create_wnaf_decomp_table<F>() -> LookupTable<F, 3>
where
    F: SmallField,
{
    let mut all_keys = Vec::with_capacity(1 << 8);
    for a in 0..=u8::MAX {
        let key = smallvec::smallvec![F::from_u64_unchecked(a as u64)];
        all_keys.push(key);
    }
    LookupTable::new_from_keys_and_generation_function(
        &all_keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let mut a = keys[0].as_u64_reduced() as u8;
            let mut v = Vec::with_capacity(4);
            let mut carry_bit = false;
            for _ in 0..2 {
                if a % 2 == 1 {
                    let mut naf = (a & MASK_FOR_MOD_TABLE_SIZE) as i8;
                    if naf >= HALF_TABLE_SIZE {
                        naf -= TABLE_SIZE
                    };

                    let naf_abs = naf.abs() as u8;
                    if naf < 0 {
                        if carry_bit {
                            a += naf_abs;
                        } else {
                            (a, carry_bit) = a.overflowing_add(naf_abs);
                        }
                    } else {
                        a -= naf_abs;
                    }
                    v.push(naf);
                } else {
                    v.push(0i8);
                }

                a >>= 1;
            }

            let concat = {
                let mut res = 0u32;
                res |= (v[0] as u8) as u32;
                let shifted_v1 = ((v[1] as u8) as u32) << 8;
                res |= shifted_v1;
                // Add carry bit if we overflowed
                if carry_bit {
                    res |= 1 << 16;
                }
                res
            };
            smallvec::smallvec![
                F::from_u64_unchecked(concat as u64),
                F::from_u64_unchecked(a as u64)
            ]
        },
    )
}
