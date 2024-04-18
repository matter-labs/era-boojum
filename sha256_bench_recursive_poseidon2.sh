#!/bin/sh
RUSTFLAGS='-C target-cpu=native' cargo test --release -- --ignored --nocapture run_sha256_prover_recursive_mode_poseidon2
