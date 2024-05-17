# Stable traits & implementations for boojum.

Boojum depends on Goldilocks and Poseidon - and internally it has optimized implementations.

Unfortunately these optimizations mean, that it has to depend on unstable rust features and nighly compiler.

This crate contains the NOT-optimized versions of Goldilocks & Poseidon, which can be used for non-performance critical tasks
(for example computing the commitments, some local verifications etc).

This way, this crate can be compiled with Stable rust.
