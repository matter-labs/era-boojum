use std::sync::Arc;

use pairing::{ff::PrimeField, BitIterator};

use crate::{
    cs::traits::cs::ConstraintSystem,
    field::SmallField,
    gadgets::{boolean::Boolean, non_native_field::traits::NonNativeField},
};

use super::{fq12::Fq12, fq6::Fq6, params::Extension12Params};

/// [`TorusWrapper`] is an algebraic compression of the `Fq12` element via underlying encoding of `Fq6`.
/// In compressed form operations over Fq12 are less expensive.
///
/// The implementation is based on the following paper:
/// https://eprint.iacr.org/2022/1162.pdf.
#[derive(Clone, Debug, Copy)]
pub struct TorusWrapper<F, T, NN, P>
where
    F: SmallField,
    T: PrimeField,
    NN: NonNativeField<F, T>,
    P: Extension12Params<T>,
{
    pub encoding: Fq6<F, T, NN, P::Ex6>,
}

// TODO: Probably, this could be implemented generally for any two Fqk and Fq(k/2) elements.
impl<F: SmallField, T: PrimeField, NN: NonNativeField<F, T>, P: Extension12Params<T>>
    TorusWrapper<F, T, NN, P>
{
    /// Creates a new instance of the [`TorusWrapper`] with the given encoding.
    pub fn new(encoding: Fq6<F, T, NN, P::Ex6>) -> Self {
        Self { encoding }
    }

    /// Returns the underlying parameters of the encoded `Fq6` element.
    pub fn get_params(&self) -> &Arc<NN::Params> {
        self.encoding.get_params()
    }

    /// Normalizes the encoding of the `Fq6` element.
    pub fn normalize<CS>(&mut self, cs: &mut CS)
    where
        CS: ConstraintSystem<F>,
    {
        self.encoding.normalize(cs);
    }

    /// Returns an instance if `flag` is `true`, otherwise returns a zero element.
    pub fn mask<CS>(&mut self, cs: &mut CS, flag: Boolean<F>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let zero = Fq6::zero(cs, self.get_params());
        let new_encoding = Fq6::conditionally_select(cs, flag, &self.encoding, &zero);

        Self::new(new_encoding)
    }

    /// Compresses the `Fq12` element `c0 + c1*w` to the Torus (`T2`) element.
    ///
    /// Uses the formula `m <- (1 + c0) / c1` to compress the `Fq12` element with the additional
    /// check for the exceptional case when `c1` is zero.
    ///
    /// If `SAFE=false`, then the function will not check for the exceptional case when `c1` is zero.
    pub fn compress<CS, const SAFE: bool>(cs: &mut CS, f: &mut Fq12<F, T, NN, P>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let params = f.get_params();
        let mut c0 = f.c0.clone();
        let mut c1 = f.c1.clone();

        let encoding = if SAFE {
            // Preparing flags for exception cases
            let is_exceptional = Fq6::is_zero(&mut c1, cs);
            let mut c0_is_one = Fq6::one(cs, params);
            let c0_is_one = c0_is_one.equals(cs, &mut c0);
            let mut is_exceptional = Fq6::from_boolean(cs, is_exceptional, params);
            let mut c0_is_one = Fq6::from_boolean(cs, c0_is_one, params);
            
            // m <- (1 + c0) / c1 if c1 is non-zero. However, to account for the case where
            // c1 is zero, we set numerator to 1 + c0 - 2*c0_is_one and denominator to c1 + is_exceptional.
            let mut numerator = Fq6::one(cs, params);
            let mut numerator = numerator.add(cs, &mut c0);
            let mut c0_is_one_doubled = c0_is_one.double(cs);
            let mut numerator = numerator.sub(cs, &mut c0_is_one_doubled);
            let mut denominator = f.c1.add(cs, &mut is_exceptional);
            
            let encoding = numerator.div(cs, &mut denominator);
            encoding
        } else {
            // Verifying that c1 is non-zero
            let boolean_false = Boolean::allocated_constant(cs, false);
            let c1_is_zero = c1.is_zero(cs);
            Boolean::enforce_equal(cs, &c1_is_zero, &boolean_false);

            // m <- (1 + c0) / c1
            let mut encoding = Fq6::one(cs, params);
            let mut encoding = encoding.add(cs, &mut f.c0);
            let encoding = encoding.div(cs, &mut f.c1);

            encoding
        };

        Self::new(encoding)
    }

    /// Decompresses the Torus (`T2`) element `g` back to the `Fq12` element by using the formula
    ///
    /// `zeta^{-1} = (g + w)/(g - w)`
    pub fn decompress<CS>(&self, cs: &mut CS) -> Fq12<F, T, NN, P>
    where
        CS: ConstraintSystem<F>,
    {
        let params = self.get_params();
        let mut one = Fq6::one(cs, params);
        let negative_one = one.negated(cs);

        // Since `g` is a pure `Fq6` element, `g+w` is just an `Fq12` element with `c0 = g` and `c1 = 1`.
        let mut numerator = Fq12::new(self.encoding.clone(), one);
        // Since `g` is a pure `Fq6` element, `g-w` is just an `Fq12` element with `c0 = g` and `c1 = -1`.
        let mut denominator = Fq12::new(self.encoding.clone(), negative_one);

        // zeta^{-1} = (g + w)/(g - w)
        let decompressed = numerator.div(cs, &mut denominator);
        decompressed
    }

    /// Computes the inverse of the Torus element using the formula g -> -g.
    pub fn inverse<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let encoding = self.encoding.inverse(cs);
        Self::new(encoding)
    }

    /// Computes the conjugate of the Torus element using the formula g -> -g.
    /// Note that the conjugate of the Torus element is the same as its inverse.
    pub fn conjugate<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.inverse(cs)
    }

    /// Computes the Frobenius map of the Torus element with the given power using the formula
    ///
    /// frob_map(g, i) = g^(p^i) / \gamma^{(p^i-1)/2}
    pub fn frobenius_map<CS>(&mut self, cs: &mut CS, power: usize) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let params = self.get_params();
        // Numerator is simply frob_map(g, i)
        let mut g = self.encoding.clone();
        let mut numerator = g.frobenius_map(cs, power);

        // Since w^2 = \gamma, that means \gamma^{1/2} = w and therefore
        // \gamma^{(p^i-1)/2} = w^{p^i-1} = frob_map(w, i)*w^{-1}. Thus,
        // denominator is frob_map(w, i)*w^{-1}
        let mut w: Fq12<F, T, NN, P> = Fq12::one_imaginary(cs, params);
        // TODO: w_inverse can be known in compile-time so there is no need to allocate it in run-time.
        let mut w_inverse = w.inverse(cs);
        let mut denominator = w.frobenius_map(cs, power);
        let denominator = denominator.mul(cs, &mut w_inverse);

        // Asserting that c1 is zero since denominator must be a pure Fq6 element.
        let boolean_true = Boolean::allocated_constant(cs, true);
        let c1_is_zero = g.c1.is_zero(cs);
        Boolean::enforce_equal(cs, &c1_is_zero, &boolean_true);
        let mut denominator = denominator.c0.clone();

        // frob_map(g, i) / \gamma^{(p^i-1)/2}
        let encoding = numerator.div(cs, &mut denominator);
        Self::new(encoding)
    }

    /// Computes the product of two Torus elements using the formula
    ///
    /// `(g, g') -> (g * g' + \gamma) / (g + g')`
    ///
    /// The formula handles the exceptional case when `g + g'` is zero.
    pub fn mul<CS, const SAFE: bool>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let params = self.get_params();
        let mut gamma = Fq6::gamma(cs, params);

        // g1 <- g, g2 <- g'
        let mut g1 = self.encoding.clone();
        let mut g2 = other.encoding.clone();

        // x <- g * g' + \gamma
        let mut x = g1.mul(cs, &mut g2);
        let mut x = x.add(cs, &mut gamma);

        // y <- g + g'
        let mut y = g1.add(cs, &mut g2);

        let encoding = if SAFE {
            // Exception occurs when g = -g'. To account for such case,
            // the following formula is used (flag = (y == 0)? 1 : 0 --- exception case):
            // result <- (x - flag * x) / (g + g' + flag)

            let mut zero = Fq6::zero(cs, params);
            let exception = y.equals(cs, &mut zero);
            let mut flag = Fq6::from_boolean(cs, exception, params);

            let mut numerator = flag.mul(cs, &mut x);
            let mut numerator = x.sub(cs, &mut numerator);
            let mut denominator = y.add(cs, &mut flag);
            numerator.div(cs, &mut denominator)
        } else {
            // Here we do not check whether g = -g' since the function is unsafe
            x.div(cs, &mut y)
        };

        Self::new(encoding)
    }

    pub fn pow_u32<CS, S: AsRef<[u64]>, const SAFE: bool>(
        &mut self,
        cs: &mut CS,
        exponent: S,
    ) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let mut one = Fq12::one(cs, self.get_params());
        let mut result = Self::compress::<CS, false>(cs, &mut one);
        let mut found_one = false;

        for i in BitIterator::new(exponent) {
            if found_one {
                result = result.square::<CS, SAFE>(cs);
            } else {
                found_one = i;
            }

            if i {
                result = result.mul::<CS, SAFE>(cs, self);
            }

            // Normalize the result to stay in field
            result.normalize(cs);
        }

        result
    }

    /// Squares the Torus element using the formula
    ///
    /// `g -> (1/2)(g + \gamma/g)`
    ///
    /// The formula handles the exceptional case when `g` is zero.
    pub fn square<CS, const SAFE: bool>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let params = self.get_params();
        let mut one = Fq6::one(cs, params);
        let mut gamma = Fq6::gamma(cs, params);
        let mut g = self.encoding.clone();

        // Calculating \gamma/g safely
        let mut exception_term = if SAFE {
            // Exception occurs when g = 0. To account for such case,
            // the following formula is used (flag = (g == 0)? 1 : 0 --- exception case):
            // result <- (1/2)(g + (\gamma*(1-flag)) / (g + flag))

            let mut zero = Fq6::zero(cs, params);
            let exception = g.equals(cs, &mut zero);
            let mut flag = Fq6::from_boolean(cs, exception, params);

            let mut flag_negated = one.sub(cs, &mut flag);
            let mut numerator = gamma.mul(cs, &mut flag_negated);
            let mut denominator = g.add(cs, &mut flag);

            numerator.div(cs, &mut denominator)
        } else {
            // Here we do not check whether g = 0 since the function is unsafe
            gamma.div(cs, &mut g)
        };

        // Calculating (1/2)(g + \gamma/g)
        let mut encoding = g.add(cs, &mut exception_term);
        // TODO: 2^{-1} might be known in compile-time so there is no need to allocate it in run-time.
        let mut two = one.double(cs);
        let mut two_inverse = two.inverse(cs);
        encoding = encoding.mul(cs, &mut two_inverse);

        Self::new(encoding)
    }
}
