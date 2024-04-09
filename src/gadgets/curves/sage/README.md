# :part_alternation_mark: SageMath Code for Elliptic Curve Gadgets

This folder contains SageMath code for validation and parameters generation for the Elliptic Curve Gadgets library for _Boojum_ constraint system.

## :file_folder: Structure

Below, we describe the structure of the folder:

| File/Folder | Description |
|-------------|-------------|
| [`endomorphism.sage`](endomorphism.sage) | SageMath code for getting $\lambda$ and $\beta$ parameters for BN254 curve used in useful endomorphism. |
| [`balanced_representation.sage`](balanced_representation.sage) | SageMath code for getting short vectors $(a_1,b_1)$ and $(a_2,b_2)$ used for further balanced representation of a scalar in wnaf. |
| [`scalar_decomposition.sage`](scalar_decomposition.sage) | SageMath code for testing decomposing a vector $k$ into $k_1,k_2$ such that $k = k_1 + \lambda k_2$. |
| [`params.sage`](pairing.sage) | SageMath code for pairing-related parameters. |

The majority of material (including wnaf multiplication implementation) is based on the "Guide to Elliptic Curve Cryptography" [1].

## :arrow_forward: References

[1] Darrel Hankerson, Alfred Menezes, Scott Vanstone. "Guide to Elliptic Curve Cryptography". Springer, 2004.
