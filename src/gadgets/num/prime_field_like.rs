use super::*;
use crate::cs::gates::FmaGateInExtensionWithoutConstant;
use crate::field::Field;
use crate::field::{traits::field_like::PrimeFieldLike, ExtensionField, FieldExtension};

#[derive(Derivative)]
#[derivative(Clone, Copy, Debug(bound = ""), Hash(bound = ""))]
pub struct NumAsFieldWrapper<F: SmallField, CS: ConstraintSystem<F>> {
    inner: Num<F>,
    #[derivative(Debug = "ignore", Hash = "ignore")]
    _marker: std::marker::PhantomData<fn() -> CS>,
}

impl<F: SmallField, CS: ConstraintSystem<F>> std::fmt::Display for NumAsFieldWrapper<F, CS> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Num as PrimeFieldLike{{")?;
        writeln!(f, "variable: {:?},", self.inner.variable)?;
        writeln!(f, "}}")
    }
}

impl<F: SmallField, CS: ConstraintSystem<F>> From<Num<F>> for NumAsFieldWrapper<F, CS> {
    fn from(value: Num<F>) -> Self {
        Self {
            inner: value,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<F: SmallField, CSO: ConstraintSystem<F>> CSAllocatable<F> for NumAsFieldWrapper<F, CSO> {
    type Witness = F;

    #[must_use]
    fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let inner = Num::allocate(cs, witness);
        inner.into()
    }

    #[must_use]
    fn allocate_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let inner = Num::allocate_without_value(cs);
        inner.into()
    }

    fn placeholder_witness() -> Self::Witness {
        F::ZERO
    }
}

impl<F: SmallField, CSO: ConstraintSystem<F>> WitnessHookable<F> for NumAsFieldWrapper<F, CSO> {
    fn witness_hook<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
    ) -> Box<dyn FnOnce() -> Option<Self::Witness> + 'static> {
        self.inner.witness_hook(cs)
    }
}

impl<F: SmallField, CS: ConstraintSystem<F>> NumAsFieldWrapper<F, CS> {
    #[must_use]
    pub const fn into_num(&self) -> Num<F> {
        self.inner
    }

    #[must_use]
    pub fn conditionally_select(cs: &mut CS, flag: Boolean<F>, a: &Self, b: &Self) -> Self {
        let inner = Num::conditionally_select(cs, flag, &a.inner, &b.inner);

        Self {
            inner,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<F: SmallField, CS: ConstraintSystem<F>> PrimeFieldLike for NumAsFieldWrapper<F, CS>
where
    CS: 'static,
{
    type Base = F;

    type Context = CS;
    // identities
    #[must_use]
    fn zero(ctx: &mut Self::Context) -> Self {
        let inner = Num::allocated_constant(ctx, F::ZERO);
        inner.into()
    }
    #[must_use]
    fn one(ctx: &mut Self::Context) -> Self {
        let inner = Num::allocated_constant(ctx, F::ONE);
        inner.into()
    }
    #[must_use]
    fn minus_one(ctx: &mut Self::Context) -> Self {
        let inner = Num::allocated_constant(ctx, F::MINUS_ONE);
        inner.into()
    }
    fn add_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        let new = self.into_num().add(ctx, &other.into_num());
        *self = new.into();

        self
    }
    fn sub_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        let new = self.into_num().sub(ctx, &other.into_num());
        *self = new.into();

        self
    }
    #[must_use]
    fn mul_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        let new = self.into_num().mul(ctx, &other.into_num());
        *self = new.into();

        self
    }
    fn square(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        let this = self.into_num();
        let new = self.into_num().mul(ctx, &this);
        *self = new.into();

        self
    }
    fn negate(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        let mut result = Self::zero(ctx);
        result.sub_assign(&*self, ctx);
        *self = result;

        self
    }
    fn double(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        let this = self.into_num();
        let new = self.into_num().add(ctx, &this);
        *self = new.into();

        self
    }
    // infallible inverse
    #[must_use]
    fn inverse(&self, ctx: &mut Self::Context) -> Self {
        let new = self.into_num().inverse_unchecked(ctx);

        new.into()
    }
    // constant creation
    #[must_use]
    fn constant(value: Self::Base, ctx: &mut Self::Context) -> Self {
        let new = Num::allocated_constant(ctx, value);

        new.into()
    }
}

#[derive(Derivative)]
#[derivative(Debug(bound = ""), Hash(bound = ""))]
pub struct NumExtAsFieldWrapper<
    F: SmallField,
    EXT: FieldExtension<2, BaseField = F>,
    CS: ConstraintSystem<F>,
> {
    c0: NumAsFieldWrapper<F, CS>,
    c1: NumAsFieldWrapper<F, CS>,
    #[derivative(Debug = "ignore", Hash = "ignore")]
    _marker: std::marker::PhantomData<EXT>,
}

impl<F: SmallField, EXT: FieldExtension<2, BaseField = F>, CS: ConstraintSystem<F>>
    std::fmt::Display for NumExtAsFieldWrapper<F, EXT, CS>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "NumExt as PrimeFieldLike{{")?;
        writeln!(f, "c0: {:?},", self.c0.inner.variable)?;
        writeln!(f, "c1: {:?},", self.c1.inner.variable)?;
        writeln!(f, "}}")
    }
}

impl<F: SmallField, EXT: FieldExtension<2, BaseField = F>, CS: ConstraintSystem<F>> Clone
    for NumExtAsFieldWrapper<F, EXT, CS>
{
    #[must_use]
    fn clone(&self) -> Self {
        Self {
            c0: self.c0,
            c1: self.c1,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<F: SmallField, EXT: FieldExtension<2, BaseField = F>, CS: ConstraintSystem<F>> Copy
    for NumExtAsFieldWrapper<F, EXT, CS>
{
}

impl<F: SmallField, EXT: FieldExtension<2, BaseField = F>, CSO: ConstraintSystem<F> + 'static>
    CSAllocatable<F> for NumExtAsFieldWrapper<F, EXT, CSO>
{
    type Witness = ExtensionField<F, 2, EXT>;

    #[must_use]
    fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
        let [c0, c1] = witness.into_coeffs_in_base();
        let c0 = Num::allocate(cs, c0).into();
        let c1 = Num::allocate(cs, c1).into();

        Self::from_coeffs_in_base([c0, c1])
    }

    #[must_use]
    fn allocate_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
        let c0 = Num::allocate_without_value(cs).into();
        let c1 = Num::allocate_without_value(cs).into();

        Self::from_coeffs_in_base([c0, c1])
    }

    fn placeholder_witness() -> Self::Witness {
        <ExtensionField<F, 2, EXT> as crate::field::traits::field::Field>::ZERO
    }
}
impl<F: SmallField, EXT: FieldExtension<2, BaseField = F>, CSO: ConstraintSystem<F> + 'static>
    WitnessHookable<F> for NumExtAsFieldWrapper<F, EXT, CSO>
{
    fn witness_hook<CS: ConstraintSystem<F>>(
        &self,
        cs: &CS,
    ) -> Box<dyn FnOnce() -> Option<Self::Witness> + 'static> {
        let c0_hook = self.c0.witness_hook(cs);
        let c1_hook = self.c1.witness_hook(cs);
        Box::new(|| {
            let c0 = c0_hook()?;
            let c1 = c1_hook()?;

            Some(ExtensionField::<F, 2, EXT>::from_coeff_in_base([c0, c1]))
        })
    }
}

impl<F: SmallField, EXT: FieldExtension<2, BaseField = F>, CS: ConstraintSystem<F> + 'static>
    NumExtAsFieldWrapper<F, EXT, CS>
{
    #[must_use]
    pub const fn from_coeffs_in_base(coeffs: [NumAsFieldWrapper<F, CS>; 2]) -> Self {
        let [c0, c1] = coeffs;

        Self {
            c0,
            c1,
            _marker: std::marker::PhantomData,
        }
    }

    #[must_use]
    pub fn from_num_coeffs_in_base(coeffs: [Num<F>; 2]) -> Self {
        let [c0, c1] = coeffs;

        Self {
            c0: c0.into(),
            c1: c1.into(),
            _marker: std::marker::PhantomData,
        }
    }

    #[must_use]
    pub const fn into_coeffs_in_base(self) -> [NumAsFieldWrapper<F, CS>; 2] {
        [self.c0, self.c1]
    }

    #[must_use]
    pub const fn into_num_coeffs_in_base(self) -> [Num<F>; 2] {
        [self.c0.into_num(), self.c1.into_num()]
    }

    pub fn mul_assign_by_base(&mut self, base: &NumAsFieldWrapper<F, CS>, cs: &mut CS) {
        // // There is no win here
        // if cs.gate_is_allowed::<FmaGateInExtensionWithoutConstant<F, EXT>>() {
        //     // we can use FMA
        //     let a0 = self.c0.inner.get_variable();
        //     let a1 = self.c1.inner.get_variable();

        //     let zero_var = cs.allocate_constant(F::ZERO);

        //     let [c0, c1] = FmaGateInExtensionWithoutConstant::<F, EXT>::compute_fma_in_extension(
        //         cs,
        //         ExtensionField::<F, 2, EXT>::ONE,
        //         ([a0, a1], [base.inner.get_variable(), zero_var]),
        //         ExtensionField::<F, 2, EXT>::ZERO,
        //         [a0, a1],
        //     );

        //     let c0 = Num::from_variable(c0);
        //     let c1 = Num::from_variable(c1);

        //     let result = Self::from_num_coeffs_in_base([c0, c1]);

        //     *self = result;

        //     return;
        // }

        self.c0.mul_assign(base, cs);
        self.c1.mul_assign(base, cs);
    }

    #[must_use]
    pub fn conditionally_select(cs: &mut CS, flag: Boolean<F>, a: &Self, b: &Self) -> Self {
        let c0 = NumAsFieldWrapper::conditionally_select(cs, flag, &a.c0, &b.c0);
        let c1 = NumAsFieldWrapper::conditionally_select(cs, flag, &a.c1, &b.c1);

        Self {
            c0,
            c1,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn mul_by_base_and_accumulate_into(
        dst: &mut Self,
        base: &NumAsFieldWrapper<F, CS>,
        other: &Self,
        cs: &mut CS,
    ) {
        if cs.gate_is_allowed::<FmaGateInExtensionWithoutConstant<F, EXT>>() {
            // we can use FMA gate
            let a0 = other.c0.inner.get_variable();
            let a1 = other.c1.inner.get_variable();

            let c0 = dst.c0.inner.get_variable();
            let c1 = dst.c1.inner.get_variable();

            let zero_var = cs.allocate_constant(F::ZERO);

            let [c0, c1] = FmaGateInExtensionWithoutConstant::<F, EXT>::compute_fma_in_extension(
                cs,
                ExtensionField::<F, 2, EXT>::ONE,
                ([a0, a1], [base.inner.get_variable(), zero_var]),
                ExtensionField::<F, 2, EXT>::ONE,
                [c0, c1],
            );

            let c0 = Num::from_variable(c0);
            let c1 = Num::from_variable(c1);

            let result = Self::from_num_coeffs_in_base([c0, c1]);

            *dst = result;
        } else {
            // baseline
            let mut tmp = *other;
            tmp.mul_assign_by_base(base, cs);

            dst.add_assign(&tmp, cs);
        }
    }
}

impl<F: SmallField, EXT: FieldExtension<2, BaseField = F>, CS: ConstraintSystem<F>> PrimeFieldLike
    for NumExtAsFieldWrapper<F, EXT, CS>
where
    CS: 'static,
{
    type Base = F;

    type Context = CS;
    // identities
    #[must_use]
    fn zero(ctx: &mut Self::Context) -> Self {
        let zero = Num::allocated_constant(ctx, F::ZERO).into();
        Self {
            c0: zero,
            c1: zero,
            _marker: std::marker::PhantomData,
        }
    }
    #[must_use]
    fn one(ctx: &mut Self::Context) -> Self {
        let zero = Num::allocated_constant(ctx, F::ZERO).into();
        let one = Num::allocated_constant(ctx, F::ONE).into();
        Self {
            c0: one,
            c1: zero,
            _marker: std::marker::PhantomData,
        }
    }
    #[must_use]
    fn minus_one(ctx: &mut Self::Context) -> Self {
        let zero = Num::allocated_constant(ctx, F::ZERO).into();
        let minus_one = Num::allocated_constant(ctx, F::MINUS_ONE).into();
        Self {
            c0: minus_one,
            c1: zero,
            _marker: std::marker::PhantomData,
        }
    }
    fn add_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        self.c0.add_assign(&other.c0, ctx);
        self.c1.add_assign(&other.c1, ctx);

        self
    }
    fn sub_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        self.c0.sub_assign(&other.c0, ctx);
        self.c1.sub_assign(&other.c1, ctx);

        self
    }
    fn mul_assign(&'_ mut self, other: &Self, ctx: &mut Self::Context) -> &'_ mut Self {
        if ctx.gate_is_allowed::<FmaGateInExtensionWithoutConstant<F, EXT>>() {
            // we can use FMA
            let a0 = self.c0.inner.get_variable();
            let a1 = self.c1.inner.get_variable();

            let b0 = other.c0.inner.get_variable();
            let b1 = other.c1.inner.get_variable();

            let [c0, c1] = FmaGateInExtensionWithoutConstant::<F, EXT>::compute_fma_in_extension(
                ctx,
                ExtensionField::<F, 2, EXT>::ONE,
                ([a0, a1], [b0, b1]),
                ExtensionField::<F, 2, EXT>::ZERO,
                [a0, a1],
            );

            let c0 = Num::from_variable(c0);
            let c1 = Num::from_variable(c1);

            let result = Self::from_num_coeffs_in_base([c0, c1]);

            *self = result;

            return self;
        }

        let mut v0 = self.c0;
        v0.mul_assign(&other.c0, ctx);
        let mut v1 = self.c1;
        v1.mul_assign(&other.c1, ctx);

        let t = self.c0;
        self.c1.add_assign(&t, ctx);

        let mut t0 = other.c0;
        t0.add_assign(&other.c1, ctx);
        self.c1.mul_assign(&t0, ctx);
        self.c1.sub_assign(&v0, ctx);
        self.c1.sub_assign(&v1, ctx);
        self.c0 = v0;
        let non_residue = NumAsFieldWrapper::constant(EXT::non_residue(), ctx);
        v1.mul_assign(&non_residue, ctx);
        self.c0.add_assign(&v1, ctx);

        self
    }
    fn square(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        if ctx.gate_is_allowed::<FmaGateInExtensionWithoutConstant<F, EXT>>() {
            // we can use FMA
            let c0 = self.c0.inner.get_variable();
            let c1 = self.c1.inner.get_variable();

            let [c0, c1] = FmaGateInExtensionWithoutConstant::<F, EXT>::compute_fma_in_extension(
                ctx,
                ExtensionField::<F, 2, EXT>::ONE,
                ([c0, c1], [c0, c1]),
                ExtensionField::<F, 2, EXT>::ZERO,
                [c0, c1],
            );

            let c0 = Num::from_variable(c0);
            let c1 = Num::from_variable(c1);

            let result = Self::from_num_coeffs_in_base([c0, c1]);

            *self = result;

            return self;
        }

        let mut v0 = self.c0;
        v0.sub_assign(&self.c1, ctx);
        let mut v3 = self.c0;
        let mut t0 = self.c1;
        let non_residue = NumAsFieldWrapper::constant(EXT::non_residue(), ctx);
        t0.mul_assign(&non_residue, ctx);
        v3.sub_assign(&t0, ctx);
        let mut v2 = self.c0;
        v2.mul_assign(&self.c1, ctx);
        v0.mul_assign(&v3, ctx);
        v0.add_assign(&v2, ctx);

        self.c1 = v2;
        self.c1.double(ctx);
        self.c0 = v0;

        v2.mul_assign(&non_residue, ctx);
        self.c0.add_assign(&v2, ctx);

        self
    }
    fn negate(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        self.c0.negate(ctx);
        self.c1.negate(ctx);

        self
    }
    fn double(&'_ mut self, ctx: &mut Self::Context) -> &'_ mut Self {
        self.c0.double(ctx);
        self.c1.double(ctx);

        self
    }
    // infallible inverse
    #[must_use]
    fn inverse(&self, ctx: &mut Self::Context) -> Self {
        if ctx.gate_is_allowed::<FmaGateInExtensionWithoutConstant<F, EXT>>() {
            // we can use FMA
            let c0 = self.c0.inner.get_variable();
            let c1 = self.c1.inner.get_variable();
            let zero_var = ctx.allocate_constant(F::ZERO);
            let one_var = ctx.allocate_constant(F::ONE);

            let [c0, c1] = FmaGateInExtensionWithoutConstant::<F, EXT>::create_inversion_constraint(
                ctx,
                [c0, c1],
                zero_var,
                one_var,
            );

            let c0 = Num::from_variable(c0);
            let c1 = Num::from_variable(c1);

            let result = Self::from_num_coeffs_in_base([c0, c1]);

            return result;
        }

        let mut v0 = self.c0;
        v0.square(ctx);
        let mut v1 = self.c1;
        v1.square(ctx);
        // v0 = v0 - beta * v1
        let mut v1_by_nonresidue = v1;
        let non_residue = NumAsFieldWrapper::constant(EXT::non_residue(), ctx);
        v1_by_nonresidue.mul_assign(&non_residue, ctx);
        v0.sub_assign(&v1_by_nonresidue, ctx);
        let inversed = v0.inverse(ctx);
        let mut c0 = self.c0;
        c0.mul_assign(&inversed, ctx);
        let mut c1 = self.c1;
        c1.mul_assign(&inversed, ctx);
        c1.negate(ctx);

        let new = Self {
            c0,
            c1,
            _marker: std::marker::PhantomData,
        };

        new
    }
    // constant creation
    #[must_use]
    fn constant(value: Self::Base, ctx: &mut Self::Context) -> Self {
        let zero = Num::allocated_constant(ctx, F::ZERO).into();
        let constant = Num::allocated_constant(ctx, value).into();
        Self {
            c0: constant,
            c1: zero,
            _marker: std::marker::PhantomData,
        }
    }
    #[must_use]
    fn mul_and_accumulate_into(acc: &mut Self, a: &Self, b: &Self, ctx: &mut Self::Context) {
        if ctx.gate_is_allowed::<FmaGateInExtensionWithoutConstant<F, EXT>>() {
            // we can use FMA
            let a_c0 = a.c0.inner.get_variable();
            let a_c1 = a.c1.inner.get_variable();
            let b_c0 = b.c0.inner.get_variable();
            let b_c1 = b.c1.inner.get_variable();
            let acc_c0 = acc.c0.inner.get_variable();
            let acc_c1 = acc.c1.inner.get_variable();

            let [c0, c1] = FmaGateInExtensionWithoutConstant::<F, EXT>::compute_fma_in_extension(
                ctx,
                ExtensionField::<F, 2, EXT>::ONE,
                ([a_c0, a_c1], [b_c0, b_c1]),
                ExtensionField::<F, 2, EXT>::ONE,
                [acc_c0, acc_c1],
            );

            let c0 = Num::from_variable(c0);
            let c1 = Num::from_variable(c1);

            let result = Self::from_num_coeffs_in_base([c0, c1]);

            *acc = result;
        } else {
            // degrade to default implementation
            let mut tmp = *a;
            tmp.mul_assign(b, ctx);
            acc.add_assign(&tmp, ctx);
        }
    }
}
