use super::*;

const TABLE_NAME: &str = "Monolith SBox table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MonolithSBox;

pub fn create_monolith_sbox_table<F: SmallField, const LOOKUP_BITS: usize>() -> LookupTable<F, 2> {
    let table_size = 1 << LOOKUP_BITS;
    let mut all_keys = Vec::with_capacity(table_size);
    for a in 0..table_size {
        let key = smallvec::smallvec![
            F::from_u64_unchecked(a as u64),
        ];
        all_keys.push(key);
    }
    LookupTable::new_from_keys_and_generation_function(
        &all_keys,
        TABLE_NAME.to_string(),
        1,
        |keys| {
            let limb = keys[0].as_u64_reduced() as u32;
            let value = match LOOKUP_BITS {
                8 => {
                    let limbl1 = ((!limb & 0x80) >> 7) | ((!limb & 0x7F) << 1); // Left rotation by 1
                    let limbl2 = ((limb & 0xC0) >> 6) | ((limb & 0x3F) << 2); // Left rotation by 2
                    let limbl3 = ((limb & 0xE0) >> 5) | ((limb & 0x1F) << 3); // Left rotation by 3
    
                    // y_i = x_i + (1 + x_{i+1}) * x_{i+2} * x_{i+3}
                    let tmp = limb ^ limbl1 & limbl2 & limbl3;
                    ((tmp & 0x80) >> 7) | ((tmp & 0x7F) << 1)
                }
                16 => {
                    let limbl1 = ((!limb & 0x8000) >> 15) | ((!limb & 0x7FFF) << 1); // Left rotation by 1
                    let limbl2 = ((limb & 0xC000) >> 14) | ((limb & 0x3FFF) << 2); // Left rotation by 2
                    let limbl3 = ((limb & 0xE000) >> 13) | ((limb & 0x1FFF) << 3); // Left rotation by 3
    
                    // y_i = x_i + (1 + x_{i+1}) * x_{i+2} * x_{i+3}
                    let tmp = limb ^ limbl1 & limbl2 & limbl3;
                    ((tmp & 0x8000) >> 15) | ((tmp & 0x7FFF) << 1)
                    // Final rotation
                }
                _ => {
                    panic!("Unsupported lookup size");
                }
            };

            smallvec::smallvec![
                F::from_u64_unchecked(value as u64),
            ]
        },
    )
}


const TABLE_NAME_2: &str = "Monolith SBox Upper Limb table";

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MonolithSBoxUpperLimb;

pub fn create_monolith_sbox_upper_limb_table<F: SmallField, const LOOKUP_BITS: usize>() -> LookupTable<F, 2> {
    let table_size = 1 << (LOOKUP_BITS-1);
    let mut all_keys = Vec::with_capacity(table_size);
    for a in 0..table_size {
        let key = smallvec::smallvec![
            F::from_u64_unchecked(a as u64),
        ];
        all_keys.push(key);
    }
    LookupTable::new_from_keys_and_generation_function(
        &all_keys,
        TABLE_NAME_2.to_string(),
        1,
        |keys| {
            let limb = keys[0].as_u64_reduced() as u32;
            let value = match LOOKUP_BITS {
                8 => {
                    let limbl1 = ((!limb & 0x40) >> 6) | ((!limb & 0x3F) << 1); // Left rotation by 1
                    let limbl2 = ((limb & 0x60) >> 5) | ((limb & 0x1F) << 2); // Left rotation by 2
                    
                    // y_i = x_i + (1 + x_{i+1}) * x_{i+2} * x_{i+3}
                    let tmp = limb ^ limbl1 & limbl2;
                    ((tmp & 0x40) >> 6) | ((tmp & 0x3F) << 1)
                }
                16 => {
                    let limbl1 = ((!limb & 0x4000) >> 14) | ((!limb & 0x3FFF) << 1); // Left rotation by 1
                    let limbl2 = ((limb & 0x6000) >> 13) | ((limb & 0x1FFF) << 2); // Left rotation by 2
                    
                    // y_i = x_i + (1 + x_{i+1}) * x_{i+2} * x_{i+3}
                    let tmp = limb ^ limbl1 & limbl2;
                    ((tmp & 0x4000) >> 14) | ((tmp & 0x3FFF) << 1)
                    // Final rotation
                }
                _ => {
                    panic!("Unsupported lookup size");
                }
            };

            smallvec::smallvec![
                F::from_u64_unchecked(value as u64),
            ]
        },
    )
}
