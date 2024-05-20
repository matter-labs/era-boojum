//! A set of generic constants for poseidon2, and an implementation of its sponge state.
use super::poseidon_goldilocks_params;
use super::suggested_mds;
use crate::field::goldilocks::GoldilocksField;
use crate::field::traits::representation::U64Representable;
use crate::field::Field;
use std::usize;
use unroll::unroll_for_loops;

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub struct State(pub [GoldilocksField; 12]);

impl std::fmt::Debug for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl std::fmt::Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl State {
    pub const ORDER_BITS: usize = GoldilocksField::ORDER_BITS;
    pub const ORDER: u64 = GoldilocksField::ORDER;
    pub const TWO_ADICITY: usize = GoldilocksField::TWO_ADICITY;
    pub const T: u64 = (Self::ORDER - 1) >> Self::TWO_ADICITY;
    pub const BARRETT: u128 = 18446744078004518912; // 0x10000000100000000
    pub const EPSILON: u64 = (1 << 32) - 1;
    #[cfg(feature = "include_packed_simd")]
    pub const EPSILON_VECTOR: packed_simd::u64x4 = packed_simd::u64x4::splat(Self::EPSILON);
    #[cfg(feature = "include_packed_simd")]
    pub const EPSILON_VECTOR_D: packed_simd::u64x8 = packed_simd::u64x8::splat(Self::EPSILON);

    pub const RATE: usize = poseidon_goldilocks_params::RATE;
    pub const CAPACITY: usize = poseidon_goldilocks_params::CAPACITY;
    pub const STATE_WIDTH: usize = poseidon_goldilocks_params::STATE_WIDTH;
    pub const HALF_NUM_FULL_ROUNDS: usize = poseidon_goldilocks_params::HALF_NUM_FULL_ROUNDS;
    pub const NUM_FULL_ROUNDS_TOTAL: usize = poseidon_goldilocks_params::NUM_FULL_ROUNDS_TOTAL;
    pub const NUM_PARTIAL_ROUNDS: usize = poseidon_goldilocks_params::NUM_PARTIAL_ROUNDS;
    pub const TOTAL_NUM_ROUNDS: usize = poseidon_goldilocks_params::TOTAL_NUM_ROUNDS;

    pub const ALL_ROUND_CONSTANTS: [Self; Self::TOTAL_NUM_ROUNDS] = const {
        let mut constants_array =
            [Self([GoldilocksField::ZERO; Self::STATE_WIDTH]); Self::TOTAL_NUM_ROUNDS];
        let mut i = 0;
        while i < Self::TOTAL_NUM_ROUNDS {
            constants_array[i] = Self(
                poseidon_goldilocks_params::ROUND_CONSTANTS_ALIGNED_PER_ROUND_AS_FIELD_ELEMENTS[i],
            );
            i += 1;
        }
        constants_array
    };
    pub const ALL_INNER_ROUND_CONSTANTS: [u64; Self::TOTAL_NUM_ROUNDS] = const {
        let mut constants_array = [0u64; Self::TOTAL_NUM_ROUNDS];
        let mut i = 0;
        while i < Self::TOTAL_NUM_ROUNDS {
            constants_array[i] =
                poseidon_goldilocks_params::ALL_ROUND_CONSTANTS[i * Self::STATE_WIDTH];
            i += 1;
        }
        constants_array
    };
    pub const ALL_INNER_ROUND_CONSTANTS_AS_FIELD_ELEMENTS: [GoldilocksField;
        Self::TOTAL_NUM_ROUNDS] = const {
        // those are reduced, so we can just cast
        unsafe { std::mem::transmute(Self::ALL_INNER_ROUND_CONSTANTS) }
    };

    pub const M_I_DIAGONAL_ELEMENTS_MINUS_ONE: Self = Self([
        GoldilocksField(1 << 4),
        GoldilocksField(1 << 14),
        GoldilocksField(1 << 11),
        GoldilocksField(1 << 8),
        GoldilocksField(1 << 0),
        GoldilocksField(1 << 5),
        GoldilocksField(1 << 2),
        GoldilocksField(1 << 9),
        GoldilocksField(1 << 13),
        GoldilocksField(1 << 6),
        GoldilocksField(1 << 3),
        GoldilocksField(1 << 12),
    ]);

    #[inline(always)]
    pub fn new() -> Self {
        Self([GoldilocksField::ZERO; 12])
    }

    #[inline(always)]
    pub fn from_constant(value: GoldilocksField) -> Self {
        Self([value; 12])
    }

    #[inline(always)]
    #[unroll_for_loops]
    pub fn to_reduced(&mut self) -> &mut Self {
        for i in 0..12 {
            let r = self.0[i].to_reduced_u64();
            self.0[i] = GoldilocksField(r);
        }

        self
    }

    #[inline(always)]
    #[unroll_for_loops]
    fn mul_assign_impl(&mut self, other: &Self) -> &mut Self {
        for i in 0..12 {
            self.0[i].mul_assign(&other.0[i]);
        }

        self
    }

    #[inline(always)]
    pub fn from_field_array(input: [GoldilocksField; 12]) -> Self {
        Self(input)
    }

    #[inline(always)]
    pub fn as_field_array(self) -> [GoldilocksField; 12] {
        self.0
    }

    //vectorized mds_mul
    #[inline(always)]
    #[unroll_for_loops]
    pub fn suggested_mds_mul(&mut self) {
        suggested_mds::suggested_mds_mul(&mut self.0);
    }

    #[inline(always)]
    #[unroll_for_loops]
    pub fn apply_round_constants(&mut self, round: usize) {
        for i in 0..12 {
            self.0[i].add_assign(&GoldilocksField::from_u64_unchecked(
                poseidon_goldilocks_params::ALL_ROUND_CONSTANTS[round * Self::STATE_WIDTH + i],
            ));
        }
    }

    #[inline(always)]
    pub fn apply_non_linearity(&mut self) {
        let mut t = *self;
        self.square_impl();
        t.mul_assign_impl(&*self);
        self.square_impl();
        self.mul_assign_impl(&t);
    }

    #[inline(always)]
    fn square_impl(&mut self) {
        let t = *self;
        self.mul_assign_impl(&t);
    }

    #[inline(always)]
    pub fn full_round(&mut self, round_counter: &mut usize) {
        // add constants
        self.apply_round_constants(*round_counter);
        // apply non-linearity
        self.apply_non_linearity();
        // multiply by MDS
        self.suggested_mds_mul();

        *round_counter += 1;
    }

    #[unroll_for_loops]
    #[inline(always)]
    pub fn m_i_mul(state: &mut [GoldilocksField; 12]) {
        let mut t0 = state[0];
        t0.add_assign(&state[1]);
        let mut t1 = state[2];
        t1.add_assign(&state[3]);
        let mut t2 = state[4];
        t2.add_assign(&state[5]);
        let mut t3 = state[6];
        t3.add_assign(&state[7]);
        let mut t4 = state[8];
        t4.add_assign(&state[9]);
        let mut t5 = state[10];
        t5.add_assign(&state[11]);

        t0.add_assign(&t1);
        t2.add_assign(&t3);
        t4.add_assign(&t5);

        let mut rowwise_sum = t0;
        rowwise_sum.add_assign(&t2).add_assign(&t4);

        for i in 0..12 {
            state[i].mul_assign(&Self::M_I_DIAGONAL_ELEMENTS_MINUS_ONE.0[i]);
        }

        // and this is also well vectorizable later on
        for i in 0..12 {
            state[i].add_assign(&rowwise_sum);
        }
    }

    #[inline(always)]
    pub fn partial_round_poseidon2(&mut self, round_counter: &mut usize) {
        // add constant
        self.0[0].add_assign(&Self::ALL_INNER_ROUND_CONSTANTS_AS_FIELD_ELEMENTS[*round_counter]);
        // apply non-linearity to the single element
        let mut t = self.0[0];
        self.0[0].square();
        t.mul_assign(&self.0[0]);
        self.0[0].square();
        self.0[0].mul_assign(&t);

        // multiply by MDS
        Self::m_i_mul(&mut self.0);

        *round_counter += 1;
    }

    #[inline(always)]
    #[unroll_for_loops]
    pub fn poseidon2_permutation(&mut self) {
        self.suggested_mds_mul();
        let mut round_counter = 0;
        for _i in 0..4 {
            self.full_round(&mut round_counter);
        }
        for _i in 0..22 {
            self.partial_round_poseidon2(&mut round_counter);
        }
        for _i in 0..4 {
            self.full_round(&mut round_counter);
        }
    }
}

impl Default for State {
    fn default() -> Self {
        Self([GoldilocksField::ZERO; 12])
    }
}

#[inline(always)]
pub fn poseidon2_permutation(state: &mut [GoldilocksField; State::STATE_WIDTH]) {
    let mut state_vec = State::from_field_array(*state);
    state_vec.poseidon2_permutation();
    *state = state_vec.as_field_array();
}

#[inline(never)]
pub fn poseidon2_inner_mul_ext(state: &mut [GoldilocksField; 12]) {
    State::m_i_mul(state);
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::field::rand_from_rng;
    use crate::field::{goldilocks::GoldilocksField, Field};
    use crate::implementations::poseidon_goldilocks_naive;
    use crate::implementations::suggested_mds;

    //test for apply_round_constants
    #[test]
    fn test_apply_round_constants() {
        let mut rng = rand::thread_rng();
        let mut state = [GoldilocksField::ONE; 12];

        for i in 0..state.len() {
            state[i] = rand_from_rng(&mut rng);
        }
        dbg!(state);

        let mut state_ref = state;
        poseidon_goldilocks_naive::apply_round_constants(&mut state_ref, 0);

        let mut state_vec = State(state);
        state_vec.apply_round_constants(0);

        // dbg!(&state_vec);

        assert_eq!(state_ref, state_vec.0);
    }

    //test for apply_non_linearity
    #[test]
    fn test_apply_non_linearity() {
        let mut rng = rand::thread_rng();
        let mut state = [GoldilocksField::ONE; 12];

        for i in 0..state.len() {
            state[i] = rand_from_rng(&mut rng);
        }
        dbg!(state);

        let mut state_ref = state;
        for i in 0..12 {
            poseidon_goldilocks_naive::apply_non_linearity(&mut state_ref[i]);
        }

        let mut state_vec = State(state);
        state_vec.apply_non_linearity();

        // dbg!(&state_vec);

        assert_eq!(state_ref, state_vec.0);
    }

    //test for suggested_mds_mul
    #[test]
    fn test_suggested_mds_mul() {
        let mut rng = rand::thread_rng();
        let mut state = [GoldilocksField::ONE; 12];

        for i in 0..state.len() {
            state[i] = rand_from_rng(&mut rng);
        }
        dbg!(state);

        let mut state_ref = state;
        suggested_mds::suggested_mds_mul(&mut state_ref);

        let mut state_vec = State(state);
        state_vec.suggested_mds_mul();

        // dbg!(&state_vec);

        assert_eq!(state_ref, state_vec.0);
    }

    //test for poseidon2_permutation
    #[test]
    fn test_poseidon2_permutation_generic_impl() {
        let mut rng = rand::thread_rng();
        let mut state = [GoldilocksField::ONE; 12];

        for i in 0..state.len() {
            state[i] = rand_from_rng(&mut rng);
        }
        dbg!(state);

        let mut state_ref = State::from_field_array(state);
        state_ref.poseidon2_permutation();
        // let mut state_ref_convert = State::default();
        // for i in 0..12 {
        //     state_ref_convert.0[i] = GoldilocksField::from_u128_with_reduction(state_ref.0[i]);
        // }

        let mut state_vec = State(state);
        state_vec.poseidon2_permutation();

        // dbg!(&state_vec);

        assert_eq!(state_ref.0, state_vec.0);
    }
}
