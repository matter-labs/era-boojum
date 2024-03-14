# :part_alternation_mark: Elliptic Curve Gadgets

This folder contains the source code for the Elliptic Curve Gadgets library for _Boojum_ constraint system.

## :white_check_mark: Current progress

- [x] Point multiplication by a scalar in $\mathbb{Z}_p$ using wnaf.
- [ ] Pairing implementation using Miller loop.
  - [ ] $\mathbb{F}_{p^2}$ extension support.
  - [ ] $\mathbb{F}_{p^{12}}$ extension support.
  - [ ] Line equation support.
  - [ ] Miller loop implementation.

## :heavy_plus_sign: Additional features

We also include the experiment files in [`sage`](sage) folder. These files are used to derive certain constants used in optimized algorithms.
