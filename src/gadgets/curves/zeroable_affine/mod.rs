use self::traits::selectable::Selectable;

use super::*;
use crate::{
    cs::traits::cs::ConstraintSystem,
    gadgets::{boolean::Boolean, non_native_field::traits::NonNativeField},
    pairing::{
        self,
        ff::{Field, PrimeField},
        GenericCurveAffine,
    },
};
use std::{marker::PhantomData, sync::Arc};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ZeroableAffinePoint<F, GC, NF>
where
    F: SmallField,
    GC: GenericCurveAffine,
    NF: NonNativeField<F, GC::Base>,
    GC::Base: pairing::ff::PrimeField,
{
    x: NF,
    y: NF,
    pub is_infinity: Boolean<F>,
    pub _marker: PhantomData<GC>,
}

impl<F, GC, NF> ZeroableAffinePoint<F, GC, NF>
where
    F: SmallField,
    GC: GenericCurveAffine,
    NF: NonNativeField<F, GC::Base>,
    GC::Base: PrimeField,
{
    /// Initializes a new non-infinite affine point with the specified coordinates
    fn new<CS>(cs: &mut CS, x: NF, y: NF) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        Self {
            x,
            y,
            is_infinity: Boolean::allocated_constant(cs, false),
            _marker: PhantomData,
        }
    }

    /// Returns the x-coordinate of the point
    fn x(&self) -> &NF {
        &self.x
    }

    /// Returns the y-coordinate of the point
    fn y(&self) -> &NF {
        &self.y
    }

    /// Initializes the point at infinity. x and y are set to zero, and is_infinity is set to true.
    fn zero_point<CS>(cs: &mut CS, params: &Arc<NF::Params>) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let zero_nf = NF::allocated_constant(cs, GC::Base::zero(), params);

        Self {
            x: zero_nf.clone(),
            y: zero_nf,
            is_infinity: Boolean::allocated_constant(cs, true),
            _marker: PhantomData,
        }
    }

    /// Multiplies the affine point by a scalar using a basic brute log2(scalar) method.
    fn mul<CS>(&mut self, cs: &mut CS, scalar: &GC::Base) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        let params = self.x.get_params().clone();
        let mut result = Self::zero_point(cs, &params);
        let mut temp = self.clone();
        let zero = Self::zero_point(cs, &params);

        // Convert the scalar to bits
        let scalar_bits = scalar
            .into_repr()
            .as_ref()
            .iter()
            .rev()
            .flat_map(|byte| (0..8).rev().map(move |i| (byte >> i) & 1 == 1))
            .collect::<Vec<_>>();

        for bit in scalar_bits {
            let bit_is_one = Boolean::allocated_constant(cs, bit);
            let mut point_to_add = Self::conditionally_select(cs, bit_is_one, &temp, &zero);

            result = result.add_unequal_x(cs, &mut point_to_add);
            temp.double(cs);
        }

        result
    }

    /// Doubling the point X (that is, finding 2X = X + X)
    fn double<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // Validatoring that y1 is not zero
        let is_zero = self.y.is_zero(cs);
        let boolean_false = Boolean::allocated_constant(cs, false);
        Boolean::enforce_equal(cs, &is_zero, &boolean_false);

        // Algorithm for doubling a point (x1, y1):
        // First, finding slope = (3 * x1^2 + a) / (2 * y1)
        // Then, finding x3 = slope^2 - 2 * x1 and y3 = slope * (x1 - x3) - y1

        // Getting parameter a
        let params = self.x.get_params().clone();
        let a = GC::a_coeff();
        let mut a_nf = NF::allocated_constant(cs, a, &params);

        // Calculating nominator
        let mut nominator = self.x.clone().square(cs);
        // Multiplying by 3
        let mut initial_nominator = nominator.clone();
        nominator = nominator.double(cs);
        nominator = nominator.add(cs, &mut initial_nominator);
        // Adding a
        nominator = nominator.add(cs, &mut a_nf);

        // Calculating denominator
        let mut denominator = self.y.clone();
        // Multiplying by 2
        denominator = denominator.double(cs);

        // Calculating slope
        let mut slope = nominator.div_unchecked(cs, &mut denominator);

        // Finding x3
        let mut x = slope.clone().square(cs);
        x = x.sub(cs, &mut self.x);
        x = x.sub(cs, &mut self.x);

        // Finding y3
        let mut y = self.x.sub(cs, &mut x);
        y = slope.mul(cs, &mut y);
        y = y.sub(cs, &mut self.y);

        self.x = x;
        self.y = y;
        Self {
            x: self.x.clone(),
            y: self.y.clone(),
            is_infinity: self.is_infinity,
            _marker: PhantomData,
        }
    }

    /// Negates the point by negating the y coordinate
    fn negate<CS>(&mut self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.y = self.y.negated(cs);

        Self {
            x: self.x.clone(),
            y: self.y.clone(),
            is_infinity: self.is_infinity,
            _marker: PhantomData,
        }
    }
}

impl<F, GC, NF> ZeroableAffinePoint<F, GC, NF>
where
    F: SmallField,
    GC: GenericCurveAffine,
    NF: NonNativeField<F, GC::Base>,
    GC::Base: PrimeField,
{
    /// Returns a boolean that is true if the x coordinates of the two points are equal.
    pub fn same_x<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Boolean<F>
    where
        CS: ConstraintSystem<F>,
    {
        self.x.equals(cs, &mut other.x)
    }

    /// Returns a boolean that is true if the y coordinates of the two points are equal.
    pub fn same_y<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Boolean<F>
    where
        CS: ConstraintSystem<F>,
    {
        self.y.equals(cs, &mut other.y)
    }

    /// Adds two affine points elementwise.
    pub fn elementwise_add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        self.x = self.x.add(cs, &mut other.x);
        self.y = self.y.add(cs, &mut other.y);
        Self {
            x: self.x.clone(),
            y: self.y.clone(),
            is_infinity: self.is_infinity,
            _marker: PhantomData,
        }
    }

    /// Adds two points with unequal x coordinates. If the x coordinates are equal, the result is undefined
    /// and therefore the panic is raised.
    pub fn add_unequal_x<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Self
    where
        CS: ConstraintSystem<F>,
    {
        // Verify that the x coordinates are not equal
        let same_x = self.same_x(cs, other);
        let boolean_false = Boolean::allocated_constant(cs, false);
        Boolean::enforce_equal(cs, &same_x, &boolean_false);

        // Algorithm for having two points (x1, y1) and (x2, y2) and adding them together:
        // First, finding slope = (y2 - y1) / (x2 - x1)
        // Then, finding x3 = slope^2 - x1 - x2 and y3 = slope * (x1 - x3) - y1
        let mut dx = self.x.sub(cs, &mut other.x);
        let mut dy = self.y.sub(cs, &mut other.y);
        // slope = dy / dx and we do not care whether dx is zero or not since we have already checked that
        let mut slope = dy.div_unchecked(cs, &mut dx);

        // x3 = slope^2 - x1 - x2
        let mut x = slope.clone().square(cs);
        x = x.sub(cs, &mut self.x);
        x = x.sub(cs, &mut other.x);

        // y3 = slope * (x1 - x3) - y1
        let mut y = self.x.sub(cs, &mut x);
        y = slope.mul(cs, &mut y);
        y = y.sub(cs, &mut self.y);

        self.x = x;
        self.y = y;
        Self {
            x: self.x.clone(),
            y: self.y.clone(),
            is_infinity: self.is_infinity,
            _marker: PhantomData,
        }
    }
}

impl<F: SmallField, C: GenericCurveAffine, NN: NonNativeField<F, C::Base>> Selectable<F>
    for ZeroableAffinePoint<F, C, NN>
where
    C::Base: pairing::ff::PrimeField,
{
    const SUPPORTS_PARALLEL_SELECT: bool = false;

    fn conditionally_select<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        flag: Boolean<F>,
        a: &Self,
        b: &Self,
    ) -> Self {
        let x = NN::conditionally_select(cs, flag, &a.x, &b.x);
        let y = NN::conditionally_select(cs, flag, &a.y, &b.y);
        let is_infinity = Boolean::conditionally_select(cs, flag, &a.is_infinity, &b.is_infinity);

        Self {
            x,
            y,
            is_infinity,
            _marker: std::marker::PhantomData,
        }
    }
}
