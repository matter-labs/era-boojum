use pairing::ff::{Field, PrimeField};

use std::fmt::Debug;

pub mod bn256;

// We don't have generic unconstrained tower extensions element, so we resolve it using following.
// Besides, one may include here field-specific characteristics, such as non-residue for example,
// and branch out implementations with the help of it.

pub trait Extension2Params<P: PrimeField>: 'static + Clone + Copy + Send + Sync + Debug {
    /// Witness here represents field element not under CS.
    type Witness: Field;

    fn convert_to_structured_witness(c0: P, c1: P) -> Self::Witness;
    fn convert_from_structured_witness(val: Self::Witness) -> (P, P);
}

pub trait Extension6Params<P: PrimeField>: 'static + Clone + Copy + Send + Sync + Debug {
    type Ex2: Extension2Params<P>;
    /// Witness here represents field element not under CS.
    type Witness: Field;

    const FROBENIUS_COEFFS_C1: [<Self::Ex2 as Extension2Params<P>>::Witness; 6];
    const FROBENIUS_COEFFS_C2: [<Self::Ex2 as Extension2Params<P>>::Witness; 6];

    fn convert_to_structured_witness(
        c0: <Self::Ex2 as Extension2Params<P>>::Witness,
        c1: <Self::Ex2 as Extension2Params<P>>::Witness,
        c2: <Self::Ex2 as Extension2Params<P>>::Witness,
    ) -> Self::Witness;
    fn convert_from_structured_witness(
        wit: Self::Witness,
    ) -> [<Self::Ex2 as Extension2Params<P>>::Witness; 3];
}

pub trait Extension12Params<P: PrimeField>: 'static + Clone + Copy + Send + Sync + Debug {
    type Ex6: Extension6Params<P>;
    /// Witness here represents field element not under CS.
    type Witness: Field;

    const FROBENIUS_COEFFS_C1: [<<Self::Ex6 as Extension6Params<P>>::Ex2 as Extension2Params<
        P,
    >>::Witness; 12];

    fn convert_to_structured_witness(
        c0: <Self::Ex6 as Extension6Params<P>>::Witness,
        c1: <Self::Ex6 as Extension6Params<P>>::Witness,
    ) -> Self::Witness;
    fn convert_from_structured_witness(
        wit: Self::Witness,
    ) -> (
        <Self::Ex6 as Extension6Params<P>>::Witness,
        <Self::Ex6 as Extension6Params<P>>::Witness,
    );
}

pub trait TorusExtension12Params<T>:
    'static + Clone + Copy + Send + Sync + Debug + Extension12Params<T>
where
    T: PrimeField,
{
    // NOTE: Here, we use selectors instead of constants as BN256Fq2 does not allow to allocate constant without accessing a private field.
    // TODO: Not sure whether w^{-1} is just c6*v^2*w in a general Fq12 extension, but this is the case for BN256.
    fn get_w_inverse_coeffs_c6() -> <<Self::Ex6 as Extension6Params<T>>::Ex2 as Extension2Params<T>>::Witness;
    fn get_two_inverse_coeffs_c0() -> T;
}
