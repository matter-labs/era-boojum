#!/bin/sh
RUSTFLAGS='-C target-cpu=native' cargo +nightly test --release -- --nocapture run_sha256_prover_recursive_mode_poseidon2