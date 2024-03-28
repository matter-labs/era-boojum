use pairing::ff::{Field, PrimeField};

pub mod bn256;

// We don't have generic unconstrained tower extensions element, so we resolve it using following.
// Besides, one may include here field-specific characteristics, such as non-residue for example,
// and branch out implementations with the help of it.

pub trait Extension2Params<P: PrimeField>: Clone {
    /// Witness here represents field element not under CS.
    type Witness: Field;
}

pub trait Extension6Params<P: PrimeField>: Clone {
    type Ex2: Extension2Params<P>;
    /// Witness here represents field element not under CS.
    type Witness: Field;

    const FROBENIUS_COEFFS_C1: [<Self::Ex2 as Extension2Params<P>>::Witness; 6];
    const FROBENIUS_COEFFS_C2: [<Self::Ex2 as Extension2Params<P>>::Witness; 6];
}

pub trait Extension12Params<P: PrimeField>: Clone {
    type Ex6: Extension6Params<P>;
    /// Witness here represents field element not under CS.
    type Witness: Field;

    const FROBENIUS_COEFFS_C1: [<<Self::Ex6 as Extension6Params<P>>::Ex2 as Extension2Params<
        P,
    >>::Witness; 12];
}
