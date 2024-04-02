use pairing::ff::{Field, PrimeField};

pub mod bn256;

// We don't have generic unconstrained tower extensions element, so we resolve it using following.
// Besides, one may include here field-specific characteristics, such as non-residue for example,
// and branch out implementations with the help of it.

pub trait Extension2Params<P: PrimeField>: Clone + Copy {
    /// Witness here represents field element not under CS.
    type Witness: Field;

    fn convert_to_structured_witness(c0: P, c1: P) -> Self::Witness;
    fn convert_from_structured_witness(val: Self::Witness) -> (P, P);
}

pub trait Extension6Params<P: PrimeField>: Clone + Copy {
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

pub trait Extension12Params<P: PrimeField>: Clone + Copy {
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
