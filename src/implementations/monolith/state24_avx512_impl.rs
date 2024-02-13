use std::arch::x86_64;

use crate::field::traits::field_like::PrimeFieldLike;
use crate::field::mersenne::MersenneFieldVec;
use crate::field::mersenne::MersenneField;
use unroll::unroll_for_loops;
use monolithvec_mds_24::mds_multiply_freq;
use crate::implementations::monolith::State;
use crate::field::traits::field::Field;
use crate::implementations::monolith::{Monolith, N_ROUNDS};
use crate::field::{
    PrimeField, SmallField, SmallFieldRepresentable, U64RawRepresentable, U64Representable,
};

// ternary logic is taken from Table 5-1 5-2 
// https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2c-manual.pdf
// andA!B -> 0x30
// andABC -> 0x80
// andBA -> 0xc0
// orABC -. 0xfe
// orBA -> 0xfc
// xorBA -> 0x3c 
pub const AND_A_NOT_B: i32 = 0x30;
pub const AND_A_B_C: i32 = 0x80;
pub const AND_B_A: i32 = 0xc0;
pub const OR_A_B_C: i32 = 0xfe;
pub const OR_B_A: i32 = 0xfc;
pub const XOR_B_A: i32 = 0x3c;


/// `Monolith` trait provides all the functions necessary to perform a Monolith permutation
pub trait MonolithVec<const T: usize>: Sized + State<T> {
    // Static data
    /// Number of round constants employed in a full Monolith permutation
    const N_ROUND_CONSTANTS: usize = Self::SPONGE_WIDTH * (N_ROUNDS + 1);
    /// All the round constants employed in a full Monolith permutation
    const ROUND_CONSTANTS: [Self; N_ROUNDS + 1];
    /// This constant contains the first row of a circulant `SPONGE_WIDTH x SPONGE_WIDTH` MDS matrix
    /// M. All of the remaining rows of M are rotations of this constant vector. A multiplication
    /// by M is used in the affine layer of Monolith.
    // const M: usize = 24;
    type MatrixType: Default;

    const MDS: Self::MatrixType;
    const M_POWERS: Self::MatrixType;

    const S_BOX_SHR_1: x86_64::__m512i;
    const S_BOX_SHR_1_UPPER_LIMB: x86_64::__m512i;
    const S_BOX_SHL_1: x86_64::__m512i;
    const S_BOX_SHR_2: x86_64::__m512i;
    const S_BOX_SHR_2_UPPER_LIMB: x86_64::__m512i;
    const S_BOX_SHL_2: x86_64::__m512i; 
    const S_BOX_SHR_3: x86_64::__m512i;
    const S_BOX_SHL_3: x86_64::__m512i;

    fn new_from_field_state<F: Field + U64Representable>(state: &[F; T]) -> Self {
        let state_u64 = state.map(|el| el.as_u64());
        Self::new_from_u64_array(state_u64)
    }

    fn as_field_state<F: Field + U64Representable>(&self) -> [F; T] {
        let state_u64 = Self::as_u64_array(self);
        state_u64.map(|el| F::from_u64(el).unwrap_or_default())
    }

    fn bars(&'_ mut self) -> &'_ mut Self;
    fn bricks(&'_ mut self) -> &'_ mut Self;
    fn concrete(&'_ mut self, rc: &Self) -> &'_ mut Self;
    fn concrete_in_frequency_domain(&'_ mut self, rc: &Self) -> &'_ mut Self;
    fn monolith(&'_ mut self) -> Self;
    fn monolith_in_frequency_domain(&'_ mut self) -> Self;

    fn monolith_ext(self) -> Self {
        let mut res = self;
        res.monolith_in_frequency_domain();
        res
    }
}

#[derive(Hash, Clone, Copy, Default)]
#[repr(C, align(64))]
pub struct StateVec24(pub [MersenneFieldVec; 3]);

impl StateVec24 {
    pub const fn new() -> Self{
        Self([
            MersenneFieldVec::new([0u64; 8]),
            MersenneFieldVec::new([0u64; 8]),
            MersenneFieldVec::new([0u64; 8])
        ])
    }
    pub const fn new_from_u64_array(values: [u64; 24]) -> Self{
        let mut part0 = [0u64; 8];
        let mut part1 = [0u64; 8];
        let mut part2 = [0u64; 8];
        let mut i = 0;
        while i < 8 {
            part0[i] = values[i];
            part1[i] = values[8 + i];
            part2[i] = values[16 + i];
            i += 1;
        }
        Self([
            MersenneFieldVec::new(part0),
            MersenneFieldVec::new(part1),
            MersenneFieldVec::new(part2)
        ])
    }
    pub const fn new_from_u32_array(values: [u32; 24]) -> Self{
        let mut part0 = [0u64; 8];
        let mut part1 = [0u64; 8];
        let mut part2 = [0u64; 8];
        let mut i = 0;
        while i < 8 {
            part0[i] = values[i] as u64;
            part1[i] = values[8 + i] as u64;
            part2[i] = values[16 + i] as u64;
            i += 1;
        }
        Self([
            MersenneFieldVec::new(part0),
            MersenneFieldVec::new(part1),
            MersenneFieldVec::new(part2)
        ])
    }
    pub const fn as_u64_array(values: &Self) -> [u64; 24]{
        let part0 = values.0[0].0;
        let part1 = values.0[1].0;
        let part2 = values.0[2].0;
        let mut result = [0u64; 24];
        let mut i = 0;
        while i < 8 {
            result[i] = part0[i];
            result[8 + i] = part1[i];
            result[16 + i] = part2[i];
            i += 1;
        }
        result
    }
}

impl State<24> for StateVec24 {
    // const SPONGE_WIDTH: usize = 24;
    fn new() -> Self{
        Self::new()
    }
    fn new_from_u64_array(values: [u64; Self::SPONGE_WIDTH]) -> Self{
        Self::new_from_u64_array(values)
    }
    fn new_from_u32_array(values: [u32; Self::SPONGE_WIDTH]) -> Self{
        Self::new_from_u32_array(values)
    }
    fn as_u64_array(values: &Self) -> [u64; Self::SPONGE_WIDTH]{
        Self::as_u64_array(values)
    }
}

impl MonolithVec<24> for StateVec24 {
    const ROUND_CONSTANTS: [Self; N_ROUNDS + 1] = const {
        let mut constants_array =
            [Self::new(); N_ROUNDS + 1];
        let mut i = 0;
        while i < N_ROUNDS + 1 {
            constants_array[i] = Self::new_from_u32_array(MersenneField::ROUND_CONSTANTS[i]);
            i += 1;
        }
        constants_array
    };

    type MatrixType = [Self; Self::SPONGE_WIDTH];

    const MDS: Self::MatrixType = const {
        let mut constants_array =
            [Self::new(); Self::SPONGE_WIDTH];
        let mut i = 0;
        while i < Self::SPONGE_WIDTH {
            constants_array[i] = Self::new_from_u32_array(MersenneField::MDS[i]);
            i += 1;
        }
        constants_array
    };

    const M_POWERS: Self::MatrixType = const {
        let mut constants_array =
            [Self::new(); Self::SPONGE_WIDTH];
        let mut i = 0;
        while i < Self::SPONGE_WIDTH {
            constants_array[i] = Self::new_from_u32_array(MersenneField::M_POWERS[i]);
            i += 1;
        }
        constants_array
    };

    const S_BOX_SHR_1: x86_64::__m512i = MersenneFieldVec([0x808080; 8]).to_v();
    const S_BOX_SHR_1_UPPER_LIMB: x86_64::__m512i = MersenneFieldVec([0x40000000; 8]).to_v();
    const S_BOX_SHL_1: x86_64::__m512i = MersenneFieldVec([0x3F7F7F7F; 8]).to_v();
    const S_BOX_SHR_2: x86_64::__m512i = MersenneFieldVec([0xC0C0C0; 8]).to_v();
    const S_BOX_SHR_2_UPPER_LIMB: x86_64::__m512i = MersenneFieldVec([0x60000000; 8]).to_v();
    const S_BOX_SHL_2: x86_64::__m512i = MersenneFieldVec([0x1F3F3F3F; 8]).to_v();
    const S_BOX_SHR_3: x86_64::__m512i = MersenneFieldVec([0xE0E0E0; 8]).to_v();
    const S_BOX_SHL_3: x86_64::__m512i = MersenneFieldVec([0x1F1F1F; 8]).to_v();

    #[inline(always)]
    fn bars(&'_ mut self) -> &'_ mut Self {
        unsafe {
            let limb = self.0[0].to_v();
            let empty_vec = x86_64::_mm512_setzero_si512();
            let upper_bits_mask = x86_64::_mm512_set1_epi64(0xFF000000);

            // Shift rotation left by 1
            // (!limb & 0x808080) >> 7
            let limbl1_0 = x86_64::_mm512_srli_epi64::<7>(x86_64::_mm512_ternarylogic_epi64::<AND_A_NOT_B>(Self::S_BOX_SHR_1, limb, empty_vec)); 
            // (!limb & 0x40000000) >> 6
            let limbl1_1 = x86_64::_mm512_srli_epi64::<6>(x86_64::_mm512_ternarylogic_epi64::<AND_A_NOT_B>(Self::S_BOX_SHR_1_UPPER_LIMB, limb, empty_vec));
            // (!limb & 0x3F7F7F7F) << 1
            let limbl1_2 = x86_64::_mm512_slli_epi64::<1>(x86_64::_mm512_ternarylogic_epi64::<AND_A_NOT_B>(Self::S_BOX_SHL_1, limb, empty_vec)); 
            let limbl1 = x86_64::_mm512_ternarylogic_epi64::<OR_A_B_C>(limbl1_0, limbl1_1, limbl1_2);

            // Shift rotation left by 2
            // (limb & 0xC0C0C0) >> 6
            let limbl2_0 = x86_64::_mm512_srli_epi64::<6>(x86_64::_mm512_ternarylogic_epi64::<AND_B_A>(Self::S_BOX_SHR_2, limb, empty_vec)); 
            // (limb & 0x60000000) >> 5
            let limbl2_1 = x86_64::_mm512_srli_epi64::<5>(x86_64::_mm512_ternarylogic_epi64::<AND_B_A>(Self::S_BOX_SHR_2_UPPER_LIMB, limb, empty_vec)); 
            // (limb & 0x1F3F3F3F) << 2
            let limbl2_2 = x86_64::_mm512_slli_epi64::<2>(x86_64::_mm512_ternarylogic_epi64::<AND_B_A>(Self::S_BOX_SHL_2, limb, empty_vec)); 
            let limbl2 = x86_64::_mm512_ternarylogic_epi64::<OR_A_B_C>(limbl2_0, limbl2_1, limbl2_2);

            // Shift rotation left by 3
            // (limb & 0xE0E0E0) >> 5
            let limbl3_0 = x86_64::_mm512_srli_epi64::<5>(x86_64::_mm512_ternarylogic_epi64::<AND_B_A>(Self::S_BOX_SHR_3, limb, empty_vec)); 
            // (limb & 0x1F1F1F) << 3
            let limbl3_1 = x86_64::_mm512_slli_epi64::<3>(x86_64::_mm512_ternarylogic_epi64::<AND_B_A>(Self::S_BOX_SHL_3, limb, empty_vec)); 
            let limbl3 = x86_64::_mm512_ternarylogic_epi64::<OR_A_B_C>(limbl3_0, limbl3_1, upper_bits_mask);

            let tmp = x86_64::_mm512_ternarylogic_epi64::<AND_A_B_C>(limbl1, limbl2, limbl3);
            let tmp = x86_64::_mm512_ternarylogic_epi64::<XOR_B_A>(tmp, limb, empty_vec);
            
            // Final shift rotation left by 1
            // (tmp & 0x808080) >> 7
            let res_0 = x86_64::_mm512_srli_epi64::<7>(x86_64::_mm512_ternarylogic_epi64::<AND_B_A>(Self::S_BOX_SHR_1, tmp, empty_vec)); 
            // (tmp & 0x40000000) >> 6
            let res_1 = x86_64::_mm512_srli_epi64::<6>(x86_64::_mm512_ternarylogic_epi64::<AND_B_A>(Self::S_BOX_SHR_1_UPPER_LIMB, tmp, empty_vec));
            // (tmp & 0x3F7F7F7F) << 1
            let res_2 = x86_64::_mm512_slli_epi64::<1>(x86_64::_mm512_ternarylogic_epi64::<AND_B_A>(Self::S_BOX_SHL_1, tmp, empty_vec)); 
            let res = x86_64::_mm512_ternarylogic_epi64::<OR_A_B_C>(res_0, res_1, res_2);
            self.0[0] = MersenneFieldVec::from_v(res);
        }
        
        self
    }

    #[inline(always)]
    fn bricks(&'_ mut self) -> &'_ mut Self {
        let mut input = self.clone();
        input.0[0].square(&mut ());
        input.0[1].square(&mut ());
        input.0[2].square(&mut ());
        let (square_shifted_0, square_shifted_1, square_shifted_2) = unsafe {
            let square_shifted_0 = x86_64::_mm512_maskz_alignr_epi64(0xfe, input.0[0].to_v(), input.0[1].to_v(), 7);
            let square_shifted_1 = x86_64::_mm512_alignr_epi64(input.0[1].to_v(), input.0[0].to_v(), 7);
            let square_shifted_2 = x86_64::_mm512_alignr_epi64(input.0[2].to_v(), input.0[1].to_v(), 7);
            (MersenneFieldVec::from_v(square_shifted_0), MersenneFieldVec::from_v(square_shifted_1), MersenneFieldVec::from_v(square_shifted_2))
        };
        self.0[0].add_assign(&square_shifted_0, &mut ());
        self.0[1].add_assign(&square_shifted_1, &mut ());
        self.0[2].add_assign(&square_shifted_2, &mut ());
        
        self
    }

    #[inline(always)]
    #[unroll_for_loops]
    fn concrete(&'_ mut self, rc: &Self) -> &'_ mut Self {
        let mut res = Self::new();
        unsafe {
            for row in 0..Self::SPONGE_WIDTH {
                let product_0 = x86_64::_mm512_mul_epu32(self.0[0].to_v(), Self::MDS[row].0[0].to_v());
                let product_1 = x86_64::_mm512_mul_epu32(self.0[1].to_v(), Self::MDS[row].0[1].to_v());
                let product_2 = x86_64::_mm512_mul_epu32(self.0[2].to_v(), Self::MDS[row].0[2].to_v());
                let product = x86_64::_mm512_add_epi64(product_0, product_1);
                let product = x86_64::_mm512_add_epi64(product, product_2);

                let vec_idx = (row >> 3) & 3;
                let el_idx = row & 7;
                res.0[vec_idx].0[el_idx] = x86_64::_mm512_reduce_add_epi64(product) as u64;
            }
            res.0[0].add_assign(&rc.0[0], &mut ());
            res.0[1].add_assign(&rc.0[1], &mut ());
            res.0[2].add_assign(&rc.0[2], &mut ());
            res.0[0] = MersenneFieldVec::from_v(MersenneFieldVec::reduce64(res.0[0].to_v()));
            res.0[1] = MersenneFieldVec::from_v(MersenneFieldVec::reduce64(res.0[1].to_v()));
            res.0[2] = MersenneFieldVec::from_v(MersenneFieldVec::reduce64(res.0[2].to_v()));
        }
        
        *self = res;
        self
    }

    #[inline(always)]
    fn concrete_in_frequency_domain(&'_ mut self, rc: &Self) -> &'_ mut Self {
        unsafe {
            mds_multiply_freq(self);

            self.0[0] = MersenneFieldVec::from_v(x86_64::_mm512_add_epi64(self.0[0].to_v(), rc.0[0].to_v()));
            self.0[1] = MersenneFieldVec::from_v(x86_64::_mm512_add_epi64(self.0[1].to_v(), rc.0[1].to_v()));
            self.0[2] = MersenneFieldVec::from_v(x86_64::_mm512_add_epi64(self.0[2].to_v(), rc.0[2].to_v()));

            self.0[0] = MersenneFieldVec::from_v(MersenneFieldVec::reduce_negative64(self.0[0].to_v()));
            self.0[1] = MersenneFieldVec::from_v(MersenneFieldVec::reduce_negative64(self.0[1].to_v()));
            self.0[2] = MersenneFieldVec::from_v(MersenneFieldVec::reduce_negative64(self.0[2].to_v()));
        }
        
        self
    }

    #[inline(always)]
    fn monolith(&'_ mut self) -> Self {

        self.concrete(&Self::ROUND_CONSTANTS[0]);
        for rc in Self::ROUND_CONSTANTS.iter().skip(1) {
            self.bars();
            self.bricks();
            self.concrete(rc);
        }
        *self
    }

    #[inline(always)]
    fn monolith_in_frequency_domain(&'_ mut self) -> Self {

        self.concrete_in_frequency_domain(&Self::ROUND_CONSTANTS[0]);
        for rc in Self::ROUND_CONSTANTS.iter().skip(1) {
            self.bars();
            self.bricks();
            self.concrete_in_frequency_domain(rc);
        }
        *self
    }

}

#[inline(always)]
pub fn monolith_permutation(state: &mut [MersenneField; MersenneField::SPONGE_WIDTH]) {
    let mut state_vec = StateVec24::new_from_field_state(state);
    state_vec.monolith_in_frequency_domain();
    *state = StateVec24::as_field_state(&state_vec);
}

mod monolithvec_mds_24 {
    use std::arch::x86_64;
    use crate::field::mersenne::MersenneFieldVec;
    use crate::implementations::monolith::StateVec24;

    const BLOCK2_RE_Y0_MOD: i64 = 62;
    const BLOCK2_RE_Y1_MOD: i64 = 131038;
    const BLOCK2_RE_Y2_MOD: i64 = 16376;
    const BLOCK2_RE_Y3_MOD: i64 = 16;
    const BLOCK2_RE_Y4_MOD: i64 = 8162;
    const BLOCK2_RE_Y5_MOD: i64 = 254;
    const BLOCK2_IM_Y0_MOD: i64 = 2038;
    const BLOCK2_IM_Y1_MOD: i64 = 32762;
    const BLOCK2_IM_Y2_MOD: i64 = 6;
    const BLOCK2_IM_Y3_MOD: i64 = 22;
    const BLOCK2_IM_Y4_MOD: i64 = 16;
    const BLOCK2_IM_Y5_MOD: i64 = 10;
    const BLOCK2_Y0S_MOD: i64 = 2100;
    const BLOCK2_Y1S_MOD: i64 = 163800;
    const BLOCK2_Y2S_MOD: i64 = 16370;
    const BLOCK2_Y3S_MOD: i64 = 6;
    const BLOCK2_Y4S_MOD: i64 = 8178;
    const BLOCK2_Y5S_MOD: i64 = 244;
    const BLOCK1_Y0_MOD: i64 = 1062;
    const BLOCK1_Y1_MOD: i64 = 81940;
    const BLOCK1_Y2_MOD: i64 = 8201;
    const BLOCK1_Y3_MOD: i64 = 37;
    const BLOCK1_Y4_MOD: i64 = 4121;
    const BLOCK1_Y5_MOD: i64 = 138;
    const BLOCK3_Y0_MOD: i64 = 996;
    const BLOCK3_Y1_MOD: i64 = 49166;
    const BLOCK3_Y2_MOD: i64 = 8191;
    const BLOCK3_Y3_MOD: i64 = 11;
    const BLOCK3_Y4_MOD: i64 = 4101;
    const BLOCK3_Y5_MOD: i64 = 120;
    
    const BLOCK2_RE_Y0_SIGN: u8 = 1;
    const BLOCK2_RE_Y1_SIGN: u8 = 1;
    const BLOCK2_RE_Y2_SIGN: u8 = 1;
    const BLOCK2_RE_Y3_SIGN: u8 = 0;
    const BLOCK2_RE_Y4_SIGN: u8 = 1;
    const BLOCK2_RE_Y5_SIGN: u8 = 0;
    const BLOCK2_IM_Y0_SIGN: u8 = 1;
    const BLOCK2_IM_Y1_SIGN: u8 = 1;
    const BLOCK2_IM_Y2_SIGN: u8 = 0;
    const BLOCK2_IM_Y3_SIGN: u8 = 1;
    const BLOCK2_IM_Y4_SIGN: u8 = 1;
    const BLOCK2_IM_Y5_SIGN: u8 = 1;
    const BLOCK2_Y0S_SIGN: u8 = 1;
    const BLOCK2_Y1S_SIGN: u8 = 1;
    const BLOCK2_Y2S_SIGN: u8 = 1;
    const BLOCK2_Y3S_SIGN: u8 = 1;
    const BLOCK2_Y4S_SIGN: u8 = 1;
    const BLOCK2_Y5S_SIGN: u8 = 0;
    const BLOCK1_Y0_SIGN: u8 = 0;
    const BLOCK1_Y1_SIGN: u8 = 0;
    const BLOCK1_Y2_SIGN: u8 = 0;
    const BLOCK1_Y3_SIGN: u8 = 0;
    const BLOCK1_Y4_SIGN: u8 = 0;
    const BLOCK1_Y5_SIGN: u8 = 0;
    const BLOCK3_Y0_SIGN: u8 = 1;
    const BLOCK3_Y1_SIGN: u8 = 0;
    const BLOCK3_Y2_SIGN: u8 = 0;
    const BLOCK3_Y3_SIGN: u8 = 0;
    const BLOCK3_Y4_SIGN: u8 = 0;
    const BLOCK3_Y5_SIGN: u8 = 0;

    const MDS_FREQ_BLOCK_ONE_X0_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK1_Y0_MOD, BLOCK1_Y0_MOD, BLOCK1_Y0_MOD, BLOCK1_Y0_MOD, BLOCK1_Y0_MOD, BLOCK1_Y0_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_ONE_X1_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK1_Y5_MOD, BLOCK1_Y5_MOD, BLOCK1_Y5_MOD, BLOCK1_Y5_MOD, BLOCK1_Y5_MOD, BLOCK1_Y5_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_ONE_X2_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK1_Y4_MOD, BLOCK1_Y4_MOD, BLOCK1_Y4_MOD, BLOCK1_Y4_MOD, BLOCK1_Y4_MOD, BLOCK1_Y4_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_ONE_X3_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK1_Y3_MOD, BLOCK1_Y3_MOD, BLOCK1_Y3_MOD, BLOCK1_Y3_MOD, BLOCK1_Y3_MOD, BLOCK1_Y3_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_ONE_X4_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK1_Y2_MOD, BLOCK1_Y2_MOD, BLOCK1_Y2_MOD, BLOCK1_Y2_MOD, BLOCK1_Y2_MOD, BLOCK1_Y2_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_ONE_X5_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK1_Y1_MOD, BLOCK1_Y1_MOD, BLOCK1_Y1_MOD, BLOCK1_Y1_MOD, BLOCK1_Y1_MOD, BLOCK1_Y1_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_THREE_X0_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK3_Y0_MOD, BLOCK3_Y0_MOD, BLOCK3_Y0_MOD, BLOCK3_Y0_MOD, BLOCK3_Y0_MOD, BLOCK3_Y0_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_THREE_X1_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK3_Y5_MOD, BLOCK3_Y5_MOD, BLOCK3_Y5_MOD, BLOCK3_Y5_MOD, BLOCK3_Y5_MOD, BLOCK3_Y5_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_THREE_X2_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK3_Y4_MOD, BLOCK3_Y4_MOD, BLOCK3_Y4_MOD, BLOCK3_Y4_MOD, BLOCK3_Y4_MOD, BLOCK3_Y4_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_THREE_X3_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK3_Y3_MOD, BLOCK3_Y3_MOD, BLOCK3_Y3_MOD, BLOCK3_Y3_MOD, BLOCK3_Y3_MOD, BLOCK3_Y3_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_THREE_X4_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK3_Y2_MOD, BLOCK3_Y2_MOD, BLOCK3_Y2_MOD, BLOCK3_Y2_MOD, BLOCK3_Y2_MOD, BLOCK3_Y2_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_THREE_X5_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK3_Y1_MOD, BLOCK3_Y1_MOD, BLOCK3_Y1_MOD, BLOCK3_Y1_MOD, BLOCK3_Y1_MOD, BLOCK3_Y1_MOD, 0, 0]).to_v();

    const MDS_FREQ_BLOCK_TWO_M0R_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_RE_Y0_MOD, BLOCK2_RE_Y0_MOD, BLOCK2_RE_Y0_MOD, BLOCK2_RE_Y0_MOD, BLOCK2_RE_Y0_MOD, BLOCK2_RE_Y0_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_M1R_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_RE_Y5_MOD, BLOCK2_RE_Y5_MOD, BLOCK2_RE_Y5_MOD, BLOCK2_RE_Y5_MOD, BLOCK2_RE_Y5_MOD, BLOCK2_RE_Y5_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_M2R_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_RE_Y4_MOD, BLOCK2_RE_Y4_MOD, BLOCK2_RE_Y4_MOD, BLOCK2_RE_Y4_MOD, BLOCK2_RE_Y4_MOD, BLOCK2_RE_Y4_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_M3R_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_RE_Y3_MOD, BLOCK2_RE_Y3_MOD, BLOCK2_RE_Y3_MOD, BLOCK2_RE_Y3_MOD, BLOCK2_RE_Y3_MOD, BLOCK2_RE_Y3_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_M4R_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_RE_Y2_MOD, BLOCK2_RE_Y2_MOD, BLOCK2_RE_Y2_MOD, BLOCK2_RE_Y2_MOD, BLOCK2_RE_Y2_MOD, BLOCK2_RE_Y2_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_M5R_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_RE_Y1_MOD, BLOCK2_RE_Y1_MOD, BLOCK2_RE_Y1_MOD, BLOCK2_RE_Y1_MOD, BLOCK2_RE_Y1_MOD, BLOCK2_RE_Y1_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_M0I_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_IM_Y0_MOD, BLOCK2_IM_Y0_MOD, BLOCK2_IM_Y0_MOD, BLOCK2_IM_Y0_MOD, BLOCK2_IM_Y0_MOD, BLOCK2_IM_Y0_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_M1I_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_IM_Y5_MOD, BLOCK2_IM_Y5_MOD, BLOCK2_IM_Y5_MOD, BLOCK2_IM_Y5_MOD, BLOCK2_IM_Y5_MOD, BLOCK2_IM_Y5_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_M2I_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_IM_Y4_MOD, BLOCK2_IM_Y4_MOD, BLOCK2_IM_Y4_MOD, BLOCK2_IM_Y4_MOD, BLOCK2_IM_Y4_MOD, BLOCK2_IM_Y4_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_M3I_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_IM_Y3_MOD, BLOCK2_IM_Y3_MOD, BLOCK2_IM_Y3_MOD, BLOCK2_IM_Y3_MOD, BLOCK2_IM_Y3_MOD, BLOCK2_IM_Y3_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_M4I_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_IM_Y2_MOD, BLOCK2_IM_Y2_MOD, BLOCK2_IM_Y2_MOD, BLOCK2_IM_Y2_MOD, BLOCK2_IM_Y2_MOD, BLOCK2_IM_Y2_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_M5I_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_IM_Y1_MOD, BLOCK2_IM_Y1_MOD, BLOCK2_IM_Y1_MOD, BLOCK2_IM_Y1_MOD, BLOCK2_IM_Y1_MOD, BLOCK2_IM_Y1_MOD, 0, 0]).to_v();

    const MDS_FREQ_BLOCK_TWO_Y0_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_Y0S_MOD, BLOCK2_Y0S_MOD, BLOCK2_Y0S_MOD, BLOCK2_Y0S_MOD, BLOCK2_Y0S_MOD, BLOCK2_Y0S_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_Y1_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_Y1S_MOD, BLOCK2_Y1S_MOD, BLOCK2_Y1S_MOD, BLOCK2_Y1S_MOD, BLOCK2_Y1S_MOD, BLOCK2_Y1S_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_Y2_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_Y2S_MOD, BLOCK2_Y2S_MOD, BLOCK2_Y2S_MOD, BLOCK2_Y2S_MOD, BLOCK2_Y2S_MOD, BLOCK2_Y2S_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_Y3_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_Y3S_MOD, BLOCK2_Y3S_MOD, BLOCK2_Y3S_MOD, BLOCK2_Y3S_MOD, BLOCK2_Y3S_MOD, BLOCK2_Y3S_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_Y4_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_Y4S_MOD, BLOCK2_Y4S_MOD, BLOCK2_Y4S_MOD, BLOCK2_Y4S_MOD, BLOCK2_Y4S_MOD, BLOCK2_Y4S_MOD, 0, 0]).to_v();
    const MDS_FREQ_BLOCK_TWO_Y5_MOD: x86_64::__m512i = MersenneFieldVec::new_from_i64([BLOCK2_Y5S_MOD, BLOCK2_Y5S_MOD, BLOCK2_Y5S_MOD, BLOCK2_Y5S_MOD, BLOCK2_Y5S_MOD, BLOCK2_Y5S_MOD, 0, 0]).to_v();

    const MDS_FREQ_BLOCK_TWO_M0R_SIGN: u8 = BLOCK2_RE_Y0_SIGN | (BLOCK2_RE_Y0_SIGN << 1) | (BLOCK2_RE_Y0_SIGN << 2) | (BLOCK2_RE_Y0_SIGN << 3) | (BLOCK2_RE_Y0_SIGN << 4) | (BLOCK2_RE_Y0_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_M1R_SIGN: u8 = BLOCK2_RE_Y5_SIGN | (BLOCK2_RE_Y5_SIGN << 1) | (BLOCK2_RE_Y5_SIGN << 2) | (BLOCK2_RE_Y5_SIGN << 3) | (BLOCK2_RE_Y5_SIGN << 4) | (BLOCK2_RE_Y5_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_M2R_SIGN: u8 = BLOCK2_RE_Y4_SIGN | (BLOCK2_RE_Y4_SIGN << 1) | (BLOCK2_RE_Y4_SIGN << 2) | (BLOCK2_RE_Y4_SIGN << 3) | (BLOCK2_RE_Y4_SIGN << 4) | (BLOCK2_RE_Y4_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_M3R_SIGN: u8 = BLOCK2_RE_Y3_SIGN | (BLOCK2_RE_Y3_SIGN << 1) | (BLOCK2_RE_Y3_SIGN << 2) | (BLOCK2_RE_Y3_SIGN << 3) | (BLOCK2_RE_Y3_SIGN << 4) | (BLOCK2_RE_Y3_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_M4R_SIGN: u8 = BLOCK2_RE_Y2_SIGN | (BLOCK2_RE_Y2_SIGN << 1) | (BLOCK2_RE_Y2_SIGN << 2) | (BLOCK2_RE_Y2_SIGN << 3) | (BLOCK2_RE_Y2_SIGN << 4) | (BLOCK2_RE_Y2_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_M5R_SIGN: u8 = BLOCK2_RE_Y1_SIGN | (BLOCK2_RE_Y1_SIGN << 1) | (BLOCK2_RE_Y1_SIGN << 2) | (BLOCK2_RE_Y1_SIGN << 3) | (BLOCK2_RE_Y1_SIGN << 4) | (BLOCK2_RE_Y1_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_M0I_SIGN: u8 = BLOCK2_IM_Y0_SIGN | (BLOCK2_IM_Y0_SIGN << 1) | (BLOCK2_IM_Y0_SIGN << 2) | (BLOCK2_IM_Y0_SIGN << 3) | (BLOCK2_IM_Y0_SIGN << 4) | (BLOCK2_IM_Y0_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_M1I_SIGN: u8 = BLOCK2_IM_Y5_SIGN | (BLOCK2_IM_Y5_SIGN << 1) | (BLOCK2_IM_Y5_SIGN << 2) | (BLOCK2_IM_Y5_SIGN << 3) | (BLOCK2_IM_Y5_SIGN << 4) | (BLOCK2_IM_Y5_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_M2I_SIGN: u8 = BLOCK2_IM_Y4_SIGN | (BLOCK2_IM_Y4_SIGN << 1) | (BLOCK2_IM_Y4_SIGN << 2) | (BLOCK2_IM_Y4_SIGN << 3) | (BLOCK2_IM_Y4_SIGN << 4) | (BLOCK2_IM_Y4_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_M3I_SIGN: u8 = BLOCK2_IM_Y3_SIGN | (BLOCK2_IM_Y3_SIGN << 1) | (BLOCK2_IM_Y3_SIGN << 2) | (BLOCK2_IM_Y3_SIGN << 3) | (BLOCK2_IM_Y3_SIGN << 4) | (BLOCK2_IM_Y3_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_M4I_SIGN: u8 = BLOCK2_IM_Y2_SIGN | (BLOCK2_IM_Y2_SIGN << 1) | (BLOCK2_IM_Y2_SIGN << 2) | (BLOCK2_IM_Y2_SIGN << 3) | (BLOCK2_IM_Y2_SIGN << 4) | (BLOCK2_IM_Y2_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_M5I_SIGN: u8 = BLOCK2_IM_Y1_SIGN | (BLOCK2_IM_Y1_SIGN << 1) | (BLOCK2_IM_Y1_SIGN << 2) | (BLOCK2_IM_Y1_SIGN << 3) | (BLOCK2_IM_Y1_SIGN << 4) | (BLOCK2_IM_Y1_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_Y0_SIGN: u8 = BLOCK2_Y0S_SIGN | (BLOCK2_Y0S_SIGN << 1) | (BLOCK2_Y0S_SIGN << 2) | (BLOCK2_Y0S_SIGN << 3) | (BLOCK2_Y0S_SIGN << 4) | (BLOCK2_Y0S_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_Y1_SIGN: u8 = BLOCK2_Y1S_SIGN | (BLOCK2_Y1S_SIGN << 1) | (BLOCK2_Y1S_SIGN << 2) | (BLOCK2_Y1S_SIGN << 3) | (BLOCK2_Y1S_SIGN << 4) | (BLOCK2_Y1S_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_Y2_SIGN: u8 = BLOCK2_Y2S_SIGN | (BLOCK2_Y2S_SIGN << 1) | (BLOCK2_Y2S_SIGN << 2) | (BLOCK2_Y2S_SIGN << 3) | (BLOCK2_Y2S_SIGN << 4) | (BLOCK2_Y2S_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_Y3_SIGN: u8 = BLOCK2_Y3S_SIGN | (BLOCK2_Y3S_SIGN << 1) | (BLOCK2_Y3S_SIGN << 2) | (BLOCK2_Y3S_SIGN << 3) | (BLOCK2_Y3S_SIGN << 4) | (BLOCK2_Y3S_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_Y4_SIGN: u8 = BLOCK2_Y4S_SIGN | (BLOCK2_Y4S_SIGN << 1) | (BLOCK2_Y4S_SIGN << 2) | (BLOCK2_Y4S_SIGN << 3) | (BLOCK2_Y4S_SIGN << 4) | (BLOCK2_Y4S_SIGN << 5);
    const MDS_FREQ_BLOCK_TWO_Y5_SIGN: u8 = BLOCK2_Y5S_SIGN | (BLOCK2_Y5S_SIGN << 1) | (BLOCK2_Y5S_SIGN << 2) | (BLOCK2_Y5S_SIGN << 3) | (BLOCK2_Y5S_SIGN << 4) | (BLOCK2_Y5S_SIGN << 5);
    const MDS_FREQ_BLOCK_ONE_X0_SIGN: u8 = BLOCK1_Y0_SIGN | (BLOCK1_Y0_SIGN << 1) | (BLOCK1_Y0_SIGN << 2) | (BLOCK1_Y0_SIGN << 3) | (BLOCK1_Y0_SIGN << 4) | (BLOCK1_Y0_SIGN << 5);
    const MDS_FREQ_BLOCK_ONE_X1_SIGN: u8 = BLOCK1_Y5_SIGN | (BLOCK1_Y5_SIGN << 1) | (BLOCK1_Y5_SIGN << 2) | (BLOCK1_Y5_SIGN << 3) | (BLOCK1_Y5_SIGN << 4) | (BLOCK1_Y5_SIGN << 5);
    const MDS_FREQ_BLOCK_ONE_X2_SIGN: u8 = BLOCK1_Y4_SIGN | (BLOCK1_Y4_SIGN << 1) | (BLOCK1_Y4_SIGN << 2) | (BLOCK1_Y4_SIGN << 3) | (BLOCK1_Y4_SIGN << 4) | (BLOCK1_Y4_SIGN << 5);
    const MDS_FREQ_BLOCK_ONE_X3_SIGN: u8 = BLOCK1_Y3_SIGN | (BLOCK1_Y3_SIGN << 1) | (BLOCK1_Y3_SIGN << 2) | (BLOCK1_Y3_SIGN << 3) | (BLOCK1_Y3_SIGN << 4) | (BLOCK1_Y3_SIGN << 5);
    const MDS_FREQ_BLOCK_ONE_X4_SIGN: u8 = BLOCK1_Y2_SIGN | (BLOCK1_Y2_SIGN << 1) | (BLOCK1_Y2_SIGN << 2) | (BLOCK1_Y2_SIGN << 3) | (BLOCK1_Y2_SIGN << 4) | (BLOCK1_Y2_SIGN << 5);
    const MDS_FREQ_BLOCK_ONE_X5_SIGN: u8 = BLOCK1_Y1_SIGN | (BLOCK1_Y1_SIGN << 1) | (BLOCK1_Y1_SIGN << 2) | (BLOCK1_Y1_SIGN << 3) | (BLOCK1_Y1_SIGN << 4) | (BLOCK1_Y1_SIGN << 5);
    const MDS_FREQ_BLOCK_THREE_X0_SIGN: u8 = BLOCK3_Y0_SIGN | (BLOCK3_Y0_SIGN << 1) | (BLOCK3_Y0_SIGN << 2) | (BLOCK3_Y0_SIGN << 3) | (BLOCK3_Y0_SIGN << 4) | (BLOCK3_Y0_SIGN << 5);
    const MDS_FREQ_BLOCK_THREE_X1_SIGN: u8 = BLOCK3_Y5_SIGN | ((BLOCK3_Y5_SIGN ^ 1) << 1) | ((BLOCK3_Y5_SIGN ^ 1) << 2) | ((BLOCK3_Y5_SIGN ^ 1) << 3) | ((BLOCK3_Y5_SIGN ^ 1) << 4) | ((BLOCK3_Y5_SIGN ^ 1) << 5);
    const MDS_FREQ_BLOCK_THREE_X2_SIGN: u8 = BLOCK3_Y4_SIGN | (BLOCK3_Y4_SIGN << 1) | ((BLOCK3_Y4_SIGN ^ 1) << 2) | ((BLOCK3_Y4_SIGN ^ 1) << 3) | ((BLOCK3_Y4_SIGN ^ 1) << 4) | ((BLOCK3_Y4_SIGN ^ 1) << 5);
    const MDS_FREQ_BLOCK_THREE_X3_SIGN: u8 = BLOCK3_Y3_SIGN | (BLOCK3_Y3_SIGN << 1) | (BLOCK3_Y3_SIGN << 2) | ((BLOCK3_Y3_SIGN ^ 1) << 3) | ((BLOCK3_Y3_SIGN ^ 1) << 4) | ((BLOCK3_Y3_SIGN ^ 1) << 5);
    const MDS_FREQ_BLOCK_THREE_X4_SIGN: u8 = BLOCK3_Y2_SIGN | (BLOCK3_Y2_SIGN << 1) | (BLOCK3_Y2_SIGN << 2) | (BLOCK3_Y2_SIGN << 3) | ((BLOCK3_Y2_SIGN ^ 1) << 4) | ((BLOCK3_Y2_SIGN ^ 1) << 5);
    const MDS_FREQ_BLOCK_THREE_X5_SIGN: u8 = BLOCK3_Y1_SIGN | (BLOCK3_Y1_SIGN << 1) | (BLOCK3_Y1_SIGN << 2) | (BLOCK3_Y1_SIGN << 3) | (BLOCK3_Y1_SIGN << 4) | ((BLOCK3_Y1_SIGN ^ 1) << 5);
    
    const ALL_SIGNS: [u8;30] = [
        MDS_FREQ_BLOCK_TWO_M0R_SIGN,
        MDS_FREQ_BLOCK_TWO_M1R_SIGN,
        MDS_FREQ_BLOCK_TWO_M2R_SIGN,
        MDS_FREQ_BLOCK_TWO_M3R_SIGN,
        MDS_FREQ_BLOCK_TWO_M4R_SIGN,
        MDS_FREQ_BLOCK_TWO_M5R_SIGN,
        MDS_FREQ_BLOCK_TWO_M0I_SIGN,
        MDS_FREQ_BLOCK_TWO_M1I_SIGN,
        MDS_FREQ_BLOCK_TWO_M2I_SIGN,
        MDS_FREQ_BLOCK_TWO_M3I_SIGN,
        MDS_FREQ_BLOCK_TWO_M4I_SIGN,
        MDS_FREQ_BLOCK_TWO_M5I_SIGN,
        MDS_FREQ_BLOCK_TWO_Y0_SIGN,
        MDS_FREQ_BLOCK_TWO_Y1_SIGN,
        MDS_FREQ_BLOCK_TWO_Y2_SIGN,
        MDS_FREQ_BLOCK_TWO_Y3_SIGN,
        MDS_FREQ_BLOCK_TWO_Y4_SIGN,
        MDS_FREQ_BLOCK_TWO_Y5_SIGN,  
        MDS_FREQ_BLOCK_THREE_X0_SIGN,
        MDS_FREQ_BLOCK_THREE_X1_SIGN,
        MDS_FREQ_BLOCK_THREE_X2_SIGN,
        MDS_FREQ_BLOCK_THREE_X3_SIGN,
        MDS_FREQ_BLOCK_THREE_X4_SIGN,
        MDS_FREQ_BLOCK_THREE_X5_SIGN,
        MDS_FREQ_BLOCK_ONE_X0_SIGN,
        MDS_FREQ_BLOCK_ONE_X1_SIGN,
        MDS_FREQ_BLOCK_ONE_X2_SIGN,
        MDS_FREQ_BLOCK_ONE_X3_SIGN,
        MDS_FREQ_BLOCK_ONE_X4_SIGN,
        MDS_FREQ_BLOCK_ONE_X5_SIGN,
    ];

    #[inline(always)]
    pub(crate) fn mds_multiply_freq(state: &'_ mut StateVec24) -> &'_ mut StateVec24 {
        unsafe {
            let zeros = x86_64::_mm512_setzero_si512();

            let state_0 = state.0[0].to_v();
            let state_1 = x86_64::_mm512_permutex2var_epi64(state.0[0].to_v(), x86_64::_mm512_set_epi64(0,0,11,10,9,8,7,6), state.0[1].to_v());
            let state_2 = x86_64::_mm512_permutex2var_epi64(state.0[1].to_v(), x86_64::_mm512_set_epi64(0,0,9,8,7,6,5,4), state.0[2].to_v());
            let state_3 = x86_64::_mm512_permutexvar_epi64(x86_64::_mm512_set_epi64(0,0,7,6,5,4,3,2), state.0[2].to_v());

            // first we make 4 complex ffts over 4 elements
            let fft2_add_0 = x86_64::_mm512_add_epi64(state_0, state_2);
            let fft2_add_1 = x86_64::_mm512_add_epi64(state_1, state_3);
            let fft2_sub_0 = x86_64::_mm512_sub_epi64(state_0, state_2);
            let fft2_sub_1 = x86_64::_mm512_sub_epi64(state_3, state_1);
            let fft2_add_shifted_0 = fft2_add_1;
            let fft2_add_shifted_1 = fft2_add_0;

            let u0_4_8_12_16_20 = x86_64::_mm512_add_epi64(fft2_add_0, fft2_add_shifted_0);
            let u2_6_10_14_18_22 = x86_64::_mm512_sub_epi64(fft2_add_shifted_1, fft2_add_1);

            let u1r_5r_9r_13r_17r_21r = fft2_sub_0;
            let u1i_5i_9i_13i_17i_21i = fft2_sub_1;

            let x0_1_2_3_4_5_s = x86_64::_mm512_add_epi64(u1r_5r_9r_13r_17r_21r, u1i_5i_9i_13i_17i_21i);
            let u0_4_8_12_16_20 = MersenneFieldVec::canonicalize(u0_4_8_12_16_20);
            let u0_4_8_12_16_20 = MersenneFieldVec::canonicalize(u0_4_8_12_16_20);
            let u0_4_8_12_16_20_mod = u0_4_8_12_16_20;

            let u2_6_10_14_18_22_sign = x86_64::_mm512_castps_si512(x86_64::_mm512_movehdup_ps(x86_64::_mm512_castsi512_ps(u2_6_10_14_18_22)));
            let u2_6_10_14_18_22_mod = x86_64::_mm512_xor_epi64(u2_6_10_14_18_22_sign, u2_6_10_14_18_22);
            let u2_6_10_14_18_22_mod = x86_64::_mm512_sub_epi64(u2_6_10_14_18_22_mod, u2_6_10_14_18_22_sign);

            let x0_1_2_3_4_5_s_sign = x86_64::_mm512_castps_si512(x86_64::_mm512_movehdup_ps(x86_64::_mm512_castsi512_ps(x0_1_2_3_4_5_s)));
            let x0_1_2_3_4_5_s_mod = x86_64::_mm512_xor_epi64(x0_1_2_3_4_5_s_sign, x0_1_2_3_4_5_s);
            let x0_1_2_3_4_5_s_mod = x86_64::_mm512_sub_epi64(x0_1_2_3_4_5_s_mod, x0_1_2_3_4_5_s_sign);

            let u1r_5r_9r_13r_17r_21r_sign = x86_64::_mm512_castps_si512(x86_64::_mm512_movehdup_ps(x86_64::_mm512_castsi512_ps(u1r_5r_9r_13r_17r_21r)));
            let u1r_5r_9r_13r_17r_21r_mod = x86_64::_mm512_xor_epi64(u1r_5r_9r_13r_17r_21r_sign, u1r_5r_9r_13r_17r_21r);
            let u1r_5r_9r_13r_17r_21r_mod = x86_64::_mm512_sub_epi64(u1r_5r_9r_13r_17r_21r_mod, u1r_5r_9r_13r_17r_21r_sign);

            let u1i_5i_9i_13i_17i_21i_sign = x86_64::_mm512_castps_si512(x86_64::_mm512_movehdup_ps(x86_64::_mm512_castsi512_ps(u1i_5i_9i_13i_17i_21i)));
            let u1i_5i_9i_13i_17i_21i_mod = x86_64::_mm512_xor_epi64(u1i_5i_9i_13i_17i_21i_sign, u1i_5i_9i_13i_17i_21i);
            let u1i_5i_9i_13i_17i_21i_mod = x86_64::_mm512_sub_epi64(u1i_5i_9i_13i_17i_21i_mod, u1i_5i_9i_13i_17i_21i_sign);

            let m0r_mod = x86_64::_mm512_mul_epu32(u1r_5r_9r_13r_17r_21r_mod, MDS_FREQ_BLOCK_TWO_M0R_MOD);
            let m1r_mod = x86_64::_mm512_mul_epu32(u1r_5r_9r_13r_17r_21r_mod, MDS_FREQ_BLOCK_TWO_M1R_MOD);
            let m2r_mod = x86_64::_mm512_mul_epu32(u1r_5r_9r_13r_17r_21r_mod, MDS_FREQ_BLOCK_TWO_M2R_MOD);
            let m3r_mod = x86_64::_mm512_mul_epu32(u1r_5r_9r_13r_17r_21r_mod, MDS_FREQ_BLOCK_TWO_M3R_MOD);
            let m4r_mod = x86_64::_mm512_mul_epu32(u1r_5r_9r_13r_17r_21r_mod, MDS_FREQ_BLOCK_TWO_M4R_MOD);
            let m5r_mod = x86_64::_mm512_mul_epu32(u1r_5r_9r_13r_17r_21r_mod, MDS_FREQ_BLOCK_TWO_M5R_MOD);
            let m0i_mod = x86_64::_mm512_mul_epu32(u1i_5i_9i_13i_17i_21i_mod, MDS_FREQ_BLOCK_TWO_M0I_MOD);
            let m1i_mod = x86_64::_mm512_mul_epu32(u1i_5i_9i_13i_17i_21i_mod, MDS_FREQ_BLOCK_TWO_M1I_MOD);
            let m2i_mod = x86_64::_mm512_mul_epu32(u1i_5i_9i_13i_17i_21i_mod, MDS_FREQ_BLOCK_TWO_M2I_MOD);
            let m3i_mod = x86_64::_mm512_mul_epu32(u1i_5i_9i_13i_17i_21i_mod, MDS_FREQ_BLOCK_TWO_M3I_MOD);
            let m4i_mod = x86_64::_mm512_mul_epu32(u1i_5i_9i_13i_17i_21i_mod, MDS_FREQ_BLOCK_TWO_M4I_MOD);
            let m5i_mod = x86_64::_mm512_mul_epu32(u1i_5i_9i_13i_17i_21i_mod, MDS_FREQ_BLOCK_TWO_M5I_MOD);

            let xys0_mod = x86_64::_mm512_mul_epu32(x0_1_2_3_4_5_s_mod, MDS_FREQ_BLOCK_TWO_Y0_MOD);
            let xys1_mod = x86_64::_mm512_mul_epu32(x0_1_2_3_4_5_s_mod, MDS_FREQ_BLOCK_TWO_Y1_MOD);
            let xys2_mod = x86_64::_mm512_mul_epu32(x0_1_2_3_4_5_s_mod, MDS_FREQ_BLOCK_TWO_Y2_MOD);
            let xys3_mod = x86_64::_mm512_mul_epu32(x0_1_2_3_4_5_s_mod, MDS_FREQ_BLOCK_TWO_Y3_MOD);
            let xys4_mod = x86_64::_mm512_mul_epu32(x0_1_2_3_4_5_s_mod, MDS_FREQ_BLOCK_TWO_Y4_MOD);
            let xys5_mod = x86_64::_mm512_mul_epu32(x0_1_2_3_4_5_s_mod, MDS_FREQ_BLOCK_TWO_Y5_MOD);
            
            let x0_block1_mul_mod = x86_64::_mm512_mul_epu32(u0_4_8_12_16_20_mod, MDS_FREQ_BLOCK_ONE_X0_MOD);
            let x1_block1_mul_mod = x86_64::_mm512_mul_epu32(u0_4_8_12_16_20_mod, MDS_FREQ_BLOCK_ONE_X1_MOD);
            let x2_block1_mul_mod = x86_64::_mm512_mul_epu32(u0_4_8_12_16_20_mod, MDS_FREQ_BLOCK_ONE_X2_MOD);
            let x3_block1_mul_mod = x86_64::_mm512_mul_epu32(u0_4_8_12_16_20_mod, MDS_FREQ_BLOCK_ONE_X3_MOD);
            let x4_block1_mul_mod = x86_64::_mm512_mul_epu32(u0_4_8_12_16_20_mod, MDS_FREQ_BLOCK_ONE_X4_MOD);
            let x5_block1_mul_mod = x86_64::_mm512_mul_epu32(u0_4_8_12_16_20_mod, MDS_FREQ_BLOCK_ONE_X5_MOD);
            let x0_block3_mul_mod = x86_64::_mm512_mul_epu32(u2_6_10_14_18_22_mod, MDS_FREQ_BLOCK_THREE_X0_MOD);
            let x1_block3_mul_mod = x86_64::_mm512_mul_epu32(u2_6_10_14_18_22_mod, MDS_FREQ_BLOCK_THREE_X1_MOD);
            let x2_block3_mul_mod = x86_64::_mm512_mul_epu32(u2_6_10_14_18_22_mod, MDS_FREQ_BLOCK_THREE_X2_MOD);
            let x3_block3_mul_mod = x86_64::_mm512_mul_epu32(u2_6_10_14_18_22_mod, MDS_FREQ_BLOCK_THREE_X3_MOD);
            let x4_block3_mul_mod = x86_64::_mm512_mul_epu32(u2_6_10_14_18_22_mod, MDS_FREQ_BLOCK_THREE_X4_MOD);
            let x5_block3_mul_mod = x86_64::_mm512_mul_epu32(u2_6_10_14_18_22_mod, MDS_FREQ_BLOCK_THREE_X5_MOD);
 
            let u2_6_10_14_18_22_sign = x86_64::_mm512_cmpneq_epi64_mask(u2_6_10_14_18_22_sign, zeros);
            let x0_1_2_3_4_5_s_sign = x86_64::_mm512_cmpneq_epi64_mask(x0_1_2_3_4_5_s_sign, zeros);
            let u1r_5r_9r_13r_17r_21r_sign = x86_64::_mm512_cmpneq_epi64_mask(u1r_5r_9r_13r_17r_21r_sign, zeros);
            let u1i_5i_9i_13i_17i_21i_sign = x86_64::_mm512_cmpneq_epi64_mask(u1i_5i_9i_13i_17i_21i_sign, zeros);
            
            let mut sign_flags = [
                u1r_5r_9r_13r_17r_21r_sign,
                u1r_5r_9r_13r_17r_21r_sign,
                u1r_5r_9r_13r_17r_21r_sign,
                u1r_5r_9r_13r_17r_21r_sign,
                u1r_5r_9r_13r_17r_21r_sign,
                u1r_5r_9r_13r_17r_21r_sign,
                u1i_5i_9i_13i_17i_21i_sign,
                u1i_5i_9i_13i_17i_21i_sign,
                u1i_5i_9i_13i_17i_21i_sign,
                u1i_5i_9i_13i_17i_21i_sign,
                u1i_5i_9i_13i_17i_21i_sign,
                u1i_5i_9i_13i_17i_21i_sign,
                x0_1_2_3_4_5_s_sign,
                x0_1_2_3_4_5_s_sign,
                x0_1_2_3_4_5_s_sign,
                x0_1_2_3_4_5_s_sign,
                x0_1_2_3_4_5_s_sign,
                x0_1_2_3_4_5_s_sign,
                u2_6_10_14_18_22_sign,
                u2_6_10_14_18_22_sign,
                u2_6_10_14_18_22_sign,
                u2_6_10_14_18_22_sign,
                u2_6_10_14_18_22_sign,
                u2_6_10_14_18_22_sign,
            ];

            for i in 0..24 {
                sign_flags[i] = sign_flags[i] ^ ALL_SIGNS[i];
            }

            let m0r = x86_64::_mm512_mask_sub_epi64(m0r_mod, sign_flags[0], zeros, m0r_mod);
            let m1r = x86_64::_mm512_mask_sub_epi64(m1r_mod, sign_flags[1], zeros, m1r_mod);
            let m2r = x86_64::_mm512_mask_sub_epi64(m2r_mod, sign_flags[2], zeros, m2r_mod);
            let m3r = x86_64::_mm512_mask_sub_epi64(m3r_mod, sign_flags[3], zeros, m3r_mod);
            let m4r = x86_64::_mm512_mask_sub_epi64(m4r_mod, sign_flags[4], zeros, m4r_mod);
            let m5r = x86_64::_mm512_mask_sub_epi64(m5r_mod, sign_flags[5], zeros, m5r_mod);
            let m0i = x86_64::_mm512_mask_sub_epi64(m0i_mod, sign_flags[6], zeros, m0i_mod);
            let m1i = x86_64::_mm512_mask_sub_epi64(m1i_mod, sign_flags[7], zeros, m1i_mod);
            let m2i = x86_64::_mm512_mask_sub_epi64(m2i_mod, sign_flags[8], zeros, m2i_mod);
            let m3i = x86_64::_mm512_mask_sub_epi64(m3i_mod, sign_flags[9], zeros, m3i_mod);
            let m4i = x86_64::_mm512_mask_sub_epi64(m4i_mod, sign_flags[10], zeros, m4i_mod);
            let m5i = x86_64::_mm512_mask_sub_epi64(m5i_mod, sign_flags[11], zeros, m5i_mod);
            let xys0 = x86_64::_mm512_mask_sub_epi64(xys0_mod, sign_flags[12], zeros, xys0_mod);
            let xys1 = x86_64::_mm512_mask_sub_epi64(xys1_mod, sign_flags[13], zeros, xys1_mod);
            let xys2 = x86_64::_mm512_mask_sub_epi64(xys2_mod, sign_flags[14], zeros, xys2_mod);
            let xys3 = x86_64::_mm512_mask_sub_epi64(xys3_mod, sign_flags[15], zeros, xys3_mod);
            let xys4 = x86_64::_mm512_mask_sub_epi64(xys4_mod, sign_flags[16], zeros, xys4_mod);
            let xys5 = x86_64::_mm512_mask_sub_epi64(xys5_mod, sign_flags[17], zeros, xys5_mod);
            let x0_block3_mul = x86_64::_mm512_mask_sub_epi64(x0_block3_mul_mod, sign_flags[18], zeros, x0_block3_mul_mod);
            let x1_block3_mul = x86_64::_mm512_mask_sub_epi64(x1_block3_mul_mod, sign_flags[19], zeros, x1_block3_mul_mod);
            let x2_block3_mul = x86_64::_mm512_mask_sub_epi64(x2_block3_mul_mod, sign_flags[20], zeros, x2_block3_mul_mod);
            let x3_block3_mul = x86_64::_mm512_mask_sub_epi64(x3_block3_mul_mod, sign_flags[21], zeros, x3_block3_mul_mod);
            let x4_block3_mul = x86_64::_mm512_mask_sub_epi64(x4_block3_mul_mod, sign_flags[22], zeros, x4_block3_mul_mod);
            let x5_block3_mul = x86_64::_mm512_mask_sub_epi64(x5_block3_mul_mod, sign_flags[23], zeros, x5_block3_mul_mod);
            let x0_block1_mul = x86_64::_mm512_mask_sub_epi64(x0_block1_mul_mod, ALL_SIGNS[24], zeros, x0_block1_mul_mod);
            let x1_block1_mul = x86_64::_mm512_mask_sub_epi64(x1_block1_mul_mod, ALL_SIGNS[25], zeros, x1_block1_mul_mod);
            let x2_block1_mul = x86_64::_mm512_mask_sub_epi64(x2_block1_mul_mod, ALL_SIGNS[26], zeros, x2_block1_mul_mod);
            let x3_block1_mul = x86_64::_mm512_mask_sub_epi64(x3_block1_mul_mod, ALL_SIGNS[27], zeros, x3_block1_mul_mod);
            let x4_block1_mul = x86_64::_mm512_mask_sub_epi64(x4_block1_mul_mod, ALL_SIGNS[28], zeros, x4_block1_mul_mod);
            let x5_block1_mul = x86_64::_mm512_mask_sub_epi64(x5_block1_mul_mod, ALL_SIGNS[29], zeros, x5_block1_mul_mod);

            let m1r_shifted = x86_64::_mm512_alignr_epi64(m1r, m1r, 6);
            let m1r = x86_64::_mm512_alignr_epi64(m1r, m1r_shifted, 3);
            let m2r_shifted = x86_64::_mm512_alignr_epi64(m2r, m2r, 6);
            let m2r = x86_64::_mm512_alignr_epi64(m2r, m2r_shifted, 4);
            let m3r_shifted = x86_64::_mm512_alignr_epi64(m3r, m3r, 6);
            let m3r = x86_64::_mm512_alignr_epi64(m3r, m3r_shifted, 5);
            let m4r_shifted = x86_64::_mm512_alignr_epi64(m4r, m4r, 6);
            let m4r = x86_64::_mm512_alignr_epi64(m4r, m4r_shifted, 6);
            let m5r_shifted = x86_64::_mm512_alignr_epi64(m5r, m5r, 6);
            let m5r = x86_64::_mm512_alignr_epi64(m5r, m5r_shifted, 7);
            let m1i_shifted = x86_64::_mm512_alignr_epi64(m1i, m1i, 6);
            let m1i = x86_64::_mm512_alignr_epi64(m1i, m1i_shifted, 3);
            let m2i_shifted = x86_64::_mm512_alignr_epi64(m2i, m2i, 6);
            let m2i = x86_64::_mm512_alignr_epi64(m2i, m2i_shifted, 4);
            let m3i_shifted = x86_64::_mm512_alignr_epi64(m3i, m3i, 6);
            let m3i = x86_64::_mm512_alignr_epi64(m3i, m3i_shifted, 5);
            let m4i_shifted = x86_64::_mm512_alignr_epi64(m4i, m4i, 6);
            let m4i = x86_64::_mm512_alignr_epi64(m4i, m4i_shifted, 6);
            let m5i_shifted = x86_64::_mm512_alignr_epi64(m5i, m5i, 6);
            let m5i = x86_64::_mm512_alignr_epi64(m5i, m5i_shifted, 7);
            let x1_block1_mul_shifted = x86_64::_mm512_alignr_epi64(x1_block1_mul, x1_block1_mul, 6);
            let x1_block1_mul = x86_64::_mm512_alignr_epi64(x1_block1_mul, x1_block1_mul_shifted, 3);
            let x2_block1_mul_shifted = x86_64::_mm512_alignr_epi64(x2_block1_mul, x2_block1_mul, 6);
            let x2_block1_mul = x86_64::_mm512_alignr_epi64(x2_block1_mul, x2_block1_mul_shifted, 4);
            let x3_block1_mul_shifted = x86_64::_mm512_alignr_epi64(x3_block1_mul, x3_block1_mul, 6);
            let x3_block1_mul = x86_64::_mm512_alignr_epi64(x3_block1_mul, x3_block1_mul_shifted, 5);
            let x4_block1_mul_shifted = x86_64::_mm512_alignr_epi64(x4_block1_mul, x4_block1_mul, 6);
            let x4_block1_mul = x86_64::_mm512_alignr_epi64(x4_block1_mul, x4_block1_mul_shifted, 6);
            let x5_block1_mul_shifted = x86_64::_mm512_alignr_epi64(x5_block1_mul, x5_block1_mul, 6);
            let x5_block1_mul = x86_64::_mm512_alignr_epi64(x5_block1_mul, x5_block1_mul_shifted, 7);
            let x1_block3_mul_shifted = x86_64::_mm512_alignr_epi64(x1_block3_mul, x1_block3_mul, 6);
            let x1_block3_mul = x86_64::_mm512_alignr_epi64(x1_block3_mul, x1_block3_mul_shifted, 3);
            let x2_block3_mul_shifted = x86_64::_mm512_alignr_epi64(x2_block3_mul, x2_block3_mul, 6);
            let x2_block3_mul = x86_64::_mm512_alignr_epi64(x2_block3_mul, x2_block3_mul_shifted, 4);
            let x3_block3_mul_shifted = x86_64::_mm512_alignr_epi64(x3_block3_mul, x3_block3_mul, 6);
            let x3_block3_mul = x86_64::_mm512_alignr_epi64(x3_block3_mul, x3_block3_mul_shifted, 5);
            let x4_block3_mul_shifted = x86_64::_mm512_alignr_epi64(x4_block3_mul, x4_block3_mul, 6);
            let x4_block3_mul = x86_64::_mm512_alignr_epi64(x4_block3_mul, x4_block3_mul_shifted, 6);
            let x5_block3_mul_shifted = x86_64::_mm512_alignr_epi64(x5_block3_mul, x5_block3_mul, 6);
            let x5_block3_mul = x86_64::_mm512_alignr_epi64(x5_block3_mul, x5_block3_mul_shifted, 7);

            let tmp = x86_64::_mm512_add_epi64(x0_block1_mul, x1_block1_mul);
            let tmp = x86_64::_mm512_add_epi64(tmp, x2_block1_mul);
            let tmp = x86_64::_mm512_add_epi64(tmp, x3_block1_mul);
            let tmp = x86_64::_mm512_add_epi64(tmp, x4_block1_mul);
            let v0_4_8_12_16_20 = x86_64::_mm512_add_epi64(tmp, x5_block1_mul);

            let tmp = x86_64::_mm512_add_epi64(x0_block3_mul, x1_block3_mul);
            let tmp = x86_64::_mm512_add_epi64(tmp, x2_block3_mul);
            let tmp = x86_64::_mm512_add_epi64(tmp, x3_block3_mul);
            let tmp = x86_64::_mm512_add_epi64(tmp, x4_block3_mul);
            let v2_6_10_14_18_22 = x86_64::_mm512_add_epi64(tmp, x5_block3_mul);
            
            let m1r_signed = x86_64::_mm512_mask_sub_epi64(m1r, 0b00100000, zeros, m1r);
            let m2r_signed = x86_64::_mm512_mask_sub_epi64(m2r, 0b00110000, zeros, m2r);
            let m3r_signed = x86_64::_mm512_mask_sub_epi64(m3r, 0b00111000, zeros, m3r);
            let m4r_signed = x86_64::_mm512_mask_sub_epi64(m4r, 0b00111100, zeros, m4r);
            let m5r_signed = x86_64::_mm512_mask_sub_epi64(m5r, 0b00111110, zeros, m5r);

            let m1i_signed = x86_64::_mm512_mask_sub_epi64(m1i, 0b00011111, zeros, m1i);
            let m2i_signed = x86_64::_mm512_mask_sub_epi64(m2i, 0b00001111, zeros, m2i);
            let m3i_signed = x86_64::_mm512_mask_sub_epi64(m3i, 0b00000111, zeros, m3i);
            let m4i_signed = x86_64::_mm512_mask_sub_epi64(m4i, 0b00000011, zeros, m4i);
            let m5i_signed = x86_64::_mm512_mask_sub_epi64(m5i, 0b00000001, zeros, m5i);

            let xys_v0r = x86_64::_mm512_maskz_permutexvar_epi64(0b00011111, x86_64::_mm512_set_epi64(0,0,0,5,4,3,2,1), xys5);
            let xys_v1r = x86_64::_mm512_maskz_permutexvar_epi64(0b00001111, x86_64::_mm512_set_epi64(0,0,0,0,5,4,3,2), xys4);
            let xys_v2r = x86_64::_mm512_maskz_permutexvar_epi64(0b00000111, x86_64::_mm512_set_epi64(0,0,0,0,0,5,4,3), xys3);
            let xys_v3r = x86_64::_mm512_maskz_permutexvar_epi64(0b00000011, x86_64::_mm512_set_epi64(0,0,0,0,0,0,5,4), xys2);
            let xys_v4r = x86_64::_mm512_maskz_permutexvar_epi64(0b00000001, x86_64::_mm512_set_epi64(0,0,0,0,0,0,0,5), xys1);

            let xys_v0i = xys0;
            let xys_v1i = x86_64::_mm512_maskz_permutexvar_epi64(0b00111110, x86_64::_mm512_set_epi64(0,0,4,3,2,1,0,0), xys1);
            let xys_v2i = x86_64::_mm512_maskz_permutexvar_epi64(0b00111100, x86_64::_mm512_set_epi64(0,0,3,2,1,0,0,0), xys2);
            let xys_v3i = x86_64::_mm512_maskz_permutexvar_epi64(0b00111000, x86_64::_mm512_set_epi64(0,0,2,1,0,0,0,0), xys3);
            let xys_v4i = x86_64::_mm512_maskz_permutexvar_epi64(0b00110000, x86_64::_mm512_set_epi64(0,0,1,0,0,0,0,0), xys4);
            let xys_v5i = x86_64::_mm512_maskz_permutexvar_epi64(0b00100000, zeros, xys5);

            let tmp = x86_64::_mm512_add_epi64(xys_v0r, xys_v1r);
            let tmp = x86_64::_mm512_add_epi64(tmp, xys_v2r);
            let tmp = x86_64::_mm512_add_epi64(tmp, xys_v3r);
            let tmp = x86_64::_mm512_add_epi64(tmp, xys_v4r);
            let tmp = x86_64::_mm512_add_epi64(tmp, m0r);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m0i);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m1r_signed);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m1i);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m2r_signed);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m2i);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m3r_signed);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m3i);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m4r_signed);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m4i);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m5r_signed);
            let v1_5_9_13_17_21_re = x86_64::_mm512_sub_epi64(tmp, m5i);

            let tmp = x86_64::_mm512_add_epi64(xys_v0i, xys_v1i);
            let tmp = x86_64::_mm512_add_epi64(tmp, xys_v2i);
            let tmp = x86_64::_mm512_add_epi64(tmp, xys_v3i);
            let tmp = x86_64::_mm512_add_epi64(tmp, xys_v4i);
            let tmp = x86_64::_mm512_add_epi64(tmp, xys_v5i);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m0i);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m0r);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m1i_signed);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m1r);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m2i_signed);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m2r);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m3i_signed);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m3r);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m4i_signed);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m4r);
            let tmp = x86_64::_mm512_sub_epi64(tmp, m5i_signed);
            let v1_5_9_13_17_21_im = x86_64::_mm512_sub_epi64(tmp, m5r);

            // now perform complex ifft
            let z0 = x86_64::_mm512_add_epi64(v0_4_8_12_16_20, v2_6_10_14_18_22);
            let z1 = x86_64::_mm512_sub_epi64(v0_4_8_12_16_20, v2_6_10_14_18_22);

            let z2 = v1_5_9_13_17_21_re;
            let z3 = x86_64::_mm512_sub_epi64(zeros, v1_5_9_13_17_21_im);
            let s0_1_2_3_4_5 = x86_64::_mm512_add_epi64(z0, z2);
            let s6_7_8_9_10_11 = x86_64::_mm512_add_epi64(z1, z3);
            let s12_13_14_15_16_17 = x86_64::_mm512_sub_epi64(z0, z2);
            let s18_19_20_21_22_23 = x86_64::_mm512_sub_epi64(z1, z3);

            let new_state_0 = x86_64::_mm512_permutex2var_epi64(s0_1_2_3_4_5, x86_64::_mm512_set_epi64(9,8,5,4,3,2,1,0), s6_7_8_9_10_11);
            let new_state_1 = x86_64::_mm512_permutex2var_epi64(s6_7_8_9_10_11, x86_64::_mm512_set_epi64(11,10,9,8,5,4,3,2), s12_13_14_15_16_17);
            let new_state_2 = x86_64::_mm512_permutex2var_epi64(s12_13_14_15_16_17, x86_64::_mm512_set_epi64(13,12,11,10,9,8,5,4), s18_19_20_21_22_23);

            (*state).0[0] = MersenneFieldVec::from_v(new_state_0);
            (*state).0[1] = MersenneFieldVec::from_v(new_state_1);
            (*state).0[2] = MersenneFieldVec::from_v(new_state_2);
        }

        state
    }

}