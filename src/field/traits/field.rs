// use core::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Neg};

// Small note on function signatures: we assume that field will be eventually "small" in practice,
// so we may want to pass is "by value" to avoid copies. Unfortunately Rust's semantics will
// make extra stack-to-stack copy for functions like f(mut a: Value), so to prevent disoptimizations
// and also assuming that 99.999% of calls below will be inlined, we only keep
// "standard" methods line "mul_assign", and do not add "by value" counterparts

pub trait Field:
    'static
    + Clone
    + Copy
    + std::fmt::Display
    + std::fmt::Debug
    + std::hash::Hash
    + std::cmp::PartialEq
    + std::cmp::Eq
    + std::marker::Send
    + std::marker::Sync
    + std::default::Default
{
    // identities
    const ZERO: Self;
    const ONE: Self;
    const TWO: Self;
    const MINUS_ONE: Self;
    // zero check
    fn is_zero(&self) -> bool;
    // add
    fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self;
    // sub
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self;
    // mul
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self;
    // square
    fn square(&'_ mut self) -> &'_ mut Self;
    // negate
    fn negate(&'_ mut self) -> &'_ mut Self;
    // double
    fn double(&'_ mut self) -> &'_ mut Self;
    // exponentiate for short exponent
    fn pow_u64(&self, power: u64) -> Self {
        let mut current = *self;
        let mut product = Self::ONE;

        let mut j = 0;
        let num_bits = crate::utils::num_bits_u64(power);
        while j < num_bits {
            if (power >> j & 1) != 0 {
                product.mul_assign(&current);
            }
            current.square();
            j += 1;
        }

        product
    }

    // exponentiate for large exponent, that is in LE form (least significant word first)
    fn pow(&self, exp: &[u64]) -> Self {
        let mut current = *self;
        let mut product = Self::ONE;

        let mut word_idx = 0;
        while word_idx < exp.len() {
            let power = exp[word_idx];
            let num_bits = if word_idx == exp.len() - 1 {
                crate::utils::num_bits_u64(power)
            } else {
                64
            };

            let mut j = 0;
            while j < num_bits {
                if (power >> j & 1) != 0 {
                    product.mul_assign(&current);
                }
                current.square();
                j += 1;
            }

            word_idx += 1;
        }

        product
    }

    #[inline(always)]
    fn small_pow(&mut self, pow: usize) {
        match pow {
            3 => {
                let mut tmp = *self;
                tmp.square().mul_assign(&*self);

                *self = tmp;
            }
            5 => {
                let mut tmp = *self;
                tmp.square().square().mul_assign(&*self);

                *self = tmp;
            }
            7 => {
                let mut tmp = *self;
                tmp.square();
                let pow2 = tmp;
                tmp.square().mul_assign(&pow2).mul_assign(&*self);

                *self = tmp;
            }
            _ => {
                unimplemented!()
            }
        }
    }

    #[inline(always)]
    fn mul_and_accumulate_into(acc: &mut Self, a: &Self, b: &Self) {
        let mut tmp = *a;
        tmp.mul_assign(b);
        acc.add_assign(&tmp);
    }

    fn from_u64_with_reduction(value: u64) -> Self;
}

use derivative::Derivative;

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug, Hash)]
#[repr(isize)]
pub enum LegendreSymbol {
    Zero = 0,
    QuadraticResidue = 1,
    QuadraticNonResidue = -1,
}

impl PartialEq<LegendreSymbol> for LegendreSymbol {
    fn eq(&self, other: &LegendreSymbol) -> bool {
        *self as isize == *other as isize
    }
}

impl Eq for LegendreSymbol {}

pub trait SqrtField: Field {
    fn sqrt(&self) -> Option<Self>;
}

// we also create a macro to add default implementations for overrides of arithmetic ops from std

// Produces impl blocks for feature enabled and disabled
#[macro_export]
macro_rules! impl_std_ops_for_field {
    { $type_name:tt } => {
        impl std::ops::Add<$type_name> for $type_name {
            type Output = Self;

            // note that we do not put "mut self" here or anywhere!
            #[inline(always)]
            fn add(self, rhs: $type_name) -> Self::Output {
                let mut this = self;
                <Self as Field>::add_assign(&mut this, &rhs);

                this
            }
        }

        impl std::ops::Add<&'_ $type_name> for $type_name {
            type Output = Self;

            #[inline(always)]
            fn add(self, rhs: & $type_name) -> Self::Output {
                let mut this = self;
                <Self as Field>::add_assign(&mut this, rhs);

                this
            }
        }

        impl std::ops::AddAssign<$type_name> for $type_name {
            #[inline(always)]
            fn add_assign(&mut self, rhs: $type_name) {
                <Self as Field>::add_assign(self, &rhs);
            }
        }

        impl std::ops::AddAssign<&'_ $type_name> for $type_name {
            #[inline(always)]
            fn add_assign(&mut self, rhs: & $type_name) {
                <Self as Field>::add_assign(self, rhs);
            }
        }

        impl std::ops::Sub<$type_name> for $type_name {
            type Output = Self;

            #[inline(always)]
            fn sub(self, rhs: $type_name) -> Self::Output {
                let mut this = self;
                <Self as Field>::sub_assign(&mut this, &rhs);

                this
            }
        }

        impl std::ops::Sub<&'_ $type_name> for $type_name {
            type Output = Self;

            #[inline(always)]
            fn sub(self, rhs: & $type_name) -> Self::Output {
                let mut this = self;
                <Self as Field>::sub_assign(&mut this, rhs);

                this
            }
        }

        impl std::ops::SubAssign<$type_name> for $type_name {
            #[inline(always)]
            fn sub_assign(&mut self, rhs: $type_name) {
                <Self as Field>::sub_assign(self, &rhs);
            }
        }

        impl std::ops::SubAssign<&'_ $type_name> for $type_name {
            #[inline(always)]
            fn sub_assign(&mut self, rhs: & $type_name) {
                <Self as Field>::sub_assign(self, rhs);
            }
        }

        impl std::ops::Mul<$type_name> for $type_name {
            type Output = Self;

            #[inline(always)]
            fn mul(self, rhs: $type_name) -> Self::Output {
                let mut this = self;
                <Self as Field>::mul_assign(&mut this, &rhs);

                this
            }
        }

        impl std::ops::Mul<&'_ $type_name> for $type_name {
            type Output = Self;

            #[inline(always)]
            fn mul(self, rhs: & $type_name) -> Self::Output {
                let mut this = self;
                <Self as Field>::mul_assign(&mut this, rhs);

                this
            }
        }

        impl std::ops::MulAssign<$type_name> for $type_name {
            #[inline(always)]
            fn mul_assign(&mut self, rhs: $type_name) {
                <Self as Field>::mul_assign(self, &rhs);
            }
        }

        impl std::ops::MulAssign<&'_ $type_name> for $type_name {
            #[inline(always)]
            fn mul_assign(&mut self, rhs: & $type_name) {
                <Self as Field>::mul_assign(self, rhs);
            }
        }

        impl std::ops::Neg for $type_name {
            type Output = Self;

            #[inline(always)]
            fn neg(self) -> Self::Output {
                let mut this = self;
                <Self as Field>::negate(&mut this);

                this
            }
        }
    }
}

pub trait PrimeField: Field {
    const CAPACITY_BITS: usize;
    const CHAR_BITS: usize;
    const TWO_ADICITY: usize;
    const SHIFTS: &'static [Self];
    // generator
    fn multiplicative_generator() -> Self;
    // generator of the largest subgroup of size 2^n
    fn radix_2_subgroup_generator() -> Self;
    fn inverse(&self) -> Option<Self>;
    fn frobenius(&self, power: usize) -> Self;
    // even though we do not give a way to compute square root, we still can compute
    // legendre symbol
    fn legendre(&self) -> LegendreSymbol;
}

pub trait FieldExtension<const DEGREE: usize>:
    'static
    + Clone
    + Copy
    + std::fmt::Display
    + std::fmt::Debug
    + std::hash::Hash
    + std::marker::Send
    + std::marker::Sync
{
    const TWO_ADICITY: usize;

    type BaseField: Field;
    // non-residue explicitly
    fn non_residue() -> Self::BaseField;
    // generator's parametrization should also happen here
    fn multiplicative_generator_coeffs() -> [Self::BaseField; DEGREE];
    // norm
    fn compute_norm(el: &[Self::BaseField; DEGREE]) -> Self::BaseField;
    // there is no &self paramter here as we do not expect runtime parametrization
    fn mul_by_non_residue(el: &mut Self::BaseField);
}

#[repr(C)]
#[derive(Clone, Copy, Hash, serde::Serialize, serde::Deserialize)]
pub struct ExtensionField<F: Field, const DEGREE: usize, E: FieldExtension<DEGREE, BaseField = F>> {
    #[serde(bound(serialize = "[F; DEGREE]: serde::Serialize"))]
    #[serde(bound(deserialize = "[F; DEGREE]: serde::de::DeserializeOwned"))]
    pub coeffs: [F; DEGREE],
    pub _marker: std::marker::PhantomData<E>,
}

impl<F: Field, E: FieldExtension<2, BaseField = F>> std::cmp::PartialEq
    for ExtensionField<F, 2, E>
{
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.coeffs[0].eq(&other.coeffs[0]) && self.coeffs[1].eq(&other.coeffs[1])
    }
}

impl<F: Field, E: FieldExtension<2, BaseField = F>> std::cmp::Eq for ExtensionField<F, 2, E> {}

impl<F: Field, E: FieldExtension<2, BaseField = F>> std::default::Default
    for ExtensionField<F, 2, E>
{
    #[inline(always)]
    fn default() -> Self {
        Self::ZERO
    }
}

impl<F: Field, E: FieldExtension<2, BaseField = F>> std::fmt::Debug for ExtensionField<F, 2, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "F2{{")?;
        writeln!(f, "\t{},", self.coeffs[0])?;
        writeln!(f, "\t{},", self.coeffs[1])?;
        write!(f, "}}")
    }
}

impl<F: Field, E: FieldExtension<2, BaseField = F>> std::fmt::Display for ExtensionField<F, 2, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "F2{{")?;
        writeln!(f, "{},", self.coeffs[0])?;
        writeln!(f, "{}", self.coeffs[1])?;
        writeln!(f, "}}")
    }
}

impl<F: Field, E: FieldExtension<2, BaseField = F>> Field for ExtensionField<F, 2, E> {
    const ZERO: Self = ExtensionField {
        coeffs: [F::ZERO; 2],
        _marker: std::marker::PhantomData,
    };
    const ONE: Self = ExtensionField {
        coeffs: [F::ONE, F::ZERO],
        _marker: std::marker::PhantomData,
    };
    const TWO: Self = ExtensionField {
        coeffs: [F::TWO, F::ZERO],
        _marker: std::marker::PhantomData,
    };
    const MINUS_ONE: Self = ExtensionField {
        coeffs: [F::MINUS_ONE, F::ZERO],
        _marker: std::marker::PhantomData,
    };
    #[inline]
    fn is_zero(&self) -> bool {
        self.coeffs[0].is_zero() && self.coeffs[1].is_zero()
    }
    #[inline]
    fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.coeffs[0].add_assign(&other.coeffs[0]);
        self.coeffs[1].add_assign(&other.coeffs[1]);

        self
    }
    #[inline]
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        self.coeffs[0].sub_assign(&other.coeffs[0]);
        self.coeffs[1].sub_assign(&other.coeffs[1]);

        self
    }
    #[inline]
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
        let mut v0 = self.coeffs[0];
        v0.mul_assign(&other.coeffs[0]);
        let mut v1 = self.coeffs[1];
        v1.mul_assign(&other.coeffs[1]);

        let t = self.coeffs[0];
        self.coeffs[1].add_assign(&t);

        let mut t0 = other.coeffs[0];
        t0.add_assign(&other.coeffs[1]);
        self.coeffs[1].mul_assign(&t0);
        self.coeffs[1].sub_assign(&v0);
        self.coeffs[1].sub_assign(&v1);
        self.coeffs[0] = v0;
        E::mul_by_non_residue(&mut v1);
        self.coeffs[0].add_assign(&v1);

        self
    }
    #[inline]
    fn square(&mut self) -> &mut Self {
        let mut v0 = self.coeffs[0];
        v0.sub_assign(&self.coeffs[1]);
        let mut v3 = self.coeffs[0];
        let mut t0 = self.coeffs[1];
        E::mul_by_non_residue(&mut t0);
        v3.sub_assign(&t0);
        let mut v2 = self.coeffs[0];
        v2.mul_assign(&self.coeffs[1]);
        v0.mul_assign(&v3);
        v0.add_assign(&v2);

        self.coeffs[1] = v2;
        self.coeffs[1].double();
        self.coeffs[0] = v0;
        E::mul_by_non_residue(&mut v2);
        self.coeffs[0].add_assign(&v2);

        self
    }
    #[inline]
    fn negate(&mut self) -> &mut Self {
        self.coeffs[0].negate();
        self.coeffs[1].negate();

        self
    }
    #[inline]
    fn double(&mut self) -> &mut Self {
        self.coeffs[0].double();
        self.coeffs[1].double();

        self
    }
    #[inline]
    fn from_u64_with_reduction(value: u64) -> Self {
        ExtensionField {
            coeffs: [F::from_u64_with_reduction(value), F::ZERO],
            _marker: std::marker::PhantomData,
        }
    }
}

impl<F: PrimeField, E: FieldExtension<2, BaseField = F>> PrimeField for ExtensionField<F, 2, E> {
    const CAPACITY_BITS: usize = 1;
    const CHAR_BITS: usize = F::CHAR_BITS;
    const TWO_ADICITY: usize = 0;
    const SHIFTS: &'static [Self] = &[];

    #[inline]
    fn multiplicative_generator() -> Self {
        Self::from_coeff_in_base(E::multiplicative_generator_coeffs())
    }
    fn radix_2_subgroup_generator() -> Self {
        unreachable!()
    }
    fn inverse(&self) -> Option<Self> {
        let mut v0 = self.coeffs[0];
        v0.square();
        let mut v1 = self.coeffs[1];
        v1.square();
        // v0 = v0 - beta * v1
        let mut v1_by_nonresidue = v1;
        E::mul_by_non_residue(&mut v1_by_nonresidue);
        v0.sub_assign(&v1_by_nonresidue);
        match v0.inverse() {
            Some(inversed) => {
                let mut c0 = self.coeffs[0];
                c0.mul_assign(&inversed);
                let mut c1 = self.coeffs[1];
                c1.mul_assign(&inversed);
                c1.negate();

                let new = Self {
                    coeffs: [c0, c1],
                    _marker: std::marker::PhantomData,
                };

                Some(new)
            }
            None => None,
        }
    }
    fn frobenius(&self, _power: usize) -> Self {
        unimplemented!()
    }
    fn legendre(&self) -> LegendreSymbol {
        unimplemented!()
    }
}

impl<F: Field, E: FieldExtension<2, BaseField = F>> ExtensionField<F, 2, E> {
    #[inline(always)]
    pub fn mul_assign_by_base(&mut self, base: &F)
    where
        F: Field,
        E: FieldExtension<2, BaseField = F>,
    {
        self.coeffs[0].mul_assign(base);
        self.coeffs[1].mul_assign(base);
    }
    #[inline(always)]
    pub const fn as_coeffs_in_base(&self) -> &[F; 2] {
        &self.coeffs
    }
    #[inline(always)]
    pub const fn into_coeffs_in_base(self) -> [F; 2] {
        self.coeffs
    }
    #[inline(always)]
    pub const fn from_coeff_in_base(coeffs: [F; 2]) -> Self {
        Self {
            coeffs,
            _marker: std::marker::PhantomData,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::field::goldilocks::{GoldilocksExt2, GoldilocksField};

    use super::*;

    type Base = GoldilocksField;
    type Ext = GoldilocksExt2;
    type F = ExtensionField<Base, 2, Ext>;

    #[test]
    fn test_basic_properties() {
        let a = F::from_coeff_in_base([Base::ONE, Base::TWO]);

        let b = F::from_coeff_in_base([
            Base::from_u64_with_reduction(123),
            Base::from_u64_with_reduction(456),
        ]);

        // ab = ba
        let mut ab = a;
        ab.mul_assign(&b);

        let mut ba = b;
        ba.mul_assign(&a);

        assert_eq!(ab, ba);

        // 1 * a = a

        let mut mul_by_identity = a;
        mul_by_identity.mul_assign(&F::ONE);

        assert_eq!(mul_by_identity, a);

        // 2 * a = a + a

        let mut double_by_mul = a;
        double_by_mul.mul_assign(&F::TWO);

        let mut double_by_add = a;
        double_by_add.add_assign(&a);

        assert_eq!(double_by_add, double_by_mul);

        // a^2 = a * a

        let mut square_by_mul = a;
        square_by_mul.mul_assign(&a);

        let mut square_by_square = a;
        square_by_square.square();

        assert_eq!(square_by_square, square_by_mul);

        // try inverse
        let b_inversed = b.inverse().unwrap();
        let mut product = b_inversed;
        product.mul_assign(&b);

        assert_eq!(product, F::ONE);
    }
}
