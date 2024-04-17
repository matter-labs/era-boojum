#!/bin/sh
RUSTFLAGS='-C target-cpu=native -C target-feature=+avx2' cargo +nightly test --release -- --ignored --nocapture run_sha256_prover_non_recursive