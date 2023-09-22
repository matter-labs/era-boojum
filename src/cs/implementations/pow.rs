use blake2::Blake2s256;
use blake2::Digest;
use sha3::Keccak256;

use super::*;

pub trait PoWRunner: 'static + Send + Sync {
    fn run_from_field_elements<F: SmallField>(seed: Vec<F>, pow_bits: u32, worker: &Worker) -> u64 {
        let mut buffer = vec![];
        for el in seed.into_iter() {
            let el = el.as_u64_reduced().to_le_bytes();
            buffer.extend(el);
        }

        Self::run_from_bytes(buffer, pow_bits, worker)
    }
    fn run_from_bytes(seed: Vec<u8>, pow_bits: u32, worker: &Worker) -> u64;
    fn verify_from_field_elements<F: SmallField>(
        seed: Vec<F>,
        pow_bits: u32,
        challenge: u64,
    ) -> bool {
        let mut buffer = vec![];
        for el in seed.into_iter() {
            let el = el.as_u64_reduced().to_le_bytes();
            buffer.extend(el);
        }

        Self::verify_from_bytes(buffer, pow_bits, challenge)
    }
    fn verify_from_bytes(seed: Vec<u8>, pow_bits: u32, challenge: u64) -> bool;
}

pub struct NoPow;

impl PoWRunner for NoPow {
    fn run_from_bytes(_seed: Vec<u8>, pow_bits: u32, _worker: &Worker) -> u64 {
        assert_eq!(pow_bits, 0);
        unreachable!()
    }

    fn verify_from_bytes(_seed: Vec<u8>, pow_bits: u32, _challenge: u64) -> bool {
        assert_eq!(pow_bits, 0);
        unreachable!()
    }
}

const BLAKE2S_NO_RESULT: u64 = u64::MAX;
const BLAKE2S_ROUNDS_PER_INVOCAITON: usize = 1 << 16u32;

impl PoWRunner for Blake2s256 {
    fn run_from_bytes(seed: Vec<u8>, pow_bits: u32, worker: &Worker) -> u64 {
        assert!(pow_bits <= 32);

        let mut base_transcript = Blake2s256::new();
        base_transcript.update(&seed);

        if pow_bits <= BLAKE2S_ROUNDS_PER_INVOCAITON.trailing_zeros() {
            // serial case
            log!("Do serial PoW");
            for challenge in 0u64..(BLAKE2S_NO_RESULT - 1) {
                // we expect somewhat "good" hash distribution
                let mut new_transcript = base_transcript.clone();
                new_transcript.update(challenge.to_le_bytes());
                let mut le_bytes = [0u8; 8];
                le_bytes.copy_from_slice(&new_transcript.finalize().as_slice()[..8]);
                if u64::from_le_bytes(le_bytes).trailing_zeros() >= pow_bits {
                    return challenge;
                }
            }
        }

        use std::sync::atomic::AtomicU64;
        use std::sync::atomic::Ordering;

        let result = std::sync::Arc::new(AtomicU64::new(BLAKE2S_NO_RESULT));

        log!("Do parallel PoW");

        let pow_rounds_per_invocation = BLAKE2S_ROUNDS_PER_INVOCAITON as u64;
        // it's good to parallelize
        let num_workers = worker.num_cores as u64;
        worker.scope(0, |scope, _| {
            for worker_idx in 0..num_workers {
                let base_transcript = base_transcript.clone();
                let result = std::sync::Arc::clone(&result);
                scope.spawn(move |_| {
                    for i in 0..((BLAKE2S_NO_RESULT - 1) / num_workers / pow_rounds_per_invocation)
                    {
                        let base = (worker_idx + i * num_workers) * pow_rounds_per_invocation;
                        let current_flag = result.load(Ordering::Relaxed);
                        if current_flag == BLAKE2S_NO_RESULT {
                            for j in 0..pow_rounds_per_invocation {
                                let challenge_u64 = base + j;
                                let mut new_transcript = base_transcript.clone();
                                new_transcript.update(challenge_u64.to_le_bytes());
                                let mut le_bytes = [0u8; 8];
                                le_bytes
                                    .copy_from_slice(&new_transcript.finalize().as_slice()[..8]);
                                if u64::from_le_bytes(le_bytes).trailing_zeros() >= pow_bits {
                                    let _ = result.compare_exchange(
                                        BLAKE2S_NO_RESULT,
                                        challenge_u64,
                                        Ordering::Acquire,
                                        Ordering::Relaxed,
                                    );

                                    break;
                                }
                            }
                        } else {
                            break;
                        }
                    }
                })
            }
        });

        let challenge_u64 = result.load(Ordering::SeqCst);

        assert!(Self::verify_from_bytes(seed, pow_bits, challenge_u64));

        challenge_u64
    }

    fn verify_from_bytes(seed: Vec<u8>, pow_bits: u32, challenge: u64) -> bool {
        let mut new_transcript = Blake2s256::new();
        new_transcript.update(&seed);
        new_transcript.update(challenge.to_le_bytes());
        let mut le_bytes = [0u8; 8];
        le_bytes.copy_from_slice(&new_transcript.finalize().as_slice()[..8]);

        u64::from_le_bytes(le_bytes).trailing_zeros() >= pow_bits
    }
}

const KECCAK256_NO_RESULT: u64 = u64::MAX;
const KECCAK256_ROUNDS_PER_INVOCAITON: usize = 1 << 16u32;

impl PoWRunner for Keccak256 {
    fn run_from_bytes(seed: Vec<u8>, pow_bits: u32, worker: &Worker) -> u64 {
        assert!(pow_bits <= 32);

        let mut base_transcript = Keccak256::new();
        base_transcript.update(&seed);

        if pow_bits <= BLAKE2S_ROUNDS_PER_INVOCAITON.trailing_zeros() {
            // serial case
            log!("Do serial PoW");
            for challenge in 0u64..(KECCAK256_NO_RESULT - 1) {
                // we expect somewhat "good" hash distribution
                let mut new_transcript = base_transcript.clone();
                new_transcript.update(challenge.to_le_bytes());
                let mut le_bytes = [0u8; 8];
                le_bytes.copy_from_slice(&new_transcript.finalize().as_slice()[..8]);
                if u64::from_le_bytes(le_bytes).trailing_zeros() >= pow_bits {
                    return challenge;
                }
            }
        }

        use std::sync::atomic::AtomicU64;
        use std::sync::atomic::Ordering;

        let result = std::sync::Arc::new(AtomicU64::new(KECCAK256_NO_RESULT));

        log!("Do parallel PoW");

        let pow_rounds_per_invocation = KECCAK256_ROUNDS_PER_INVOCAITON as u64;
        // it's good to parallelize
        let num_workers = worker.num_cores as u64;
        worker.scope(0, |scope, _| {
            for worker_idx in 0..num_workers {
                let base_transcript = base_transcript.clone();
                let result = std::sync::Arc::clone(&result);
                scope.spawn(move |_| {
                    for i in
                        0..((KECCAK256_NO_RESULT - 1) / num_workers / pow_rounds_per_invocation)
                    {
                        let base = (worker_idx + i * num_workers) * pow_rounds_per_invocation;
                        let current_flag = result.load(Ordering::Relaxed);
                        if current_flag == KECCAK256_NO_RESULT {
                            for j in 0..pow_rounds_per_invocation {
                                let challenge_u64 = base + j;
                                let mut new_transcript = base_transcript.clone();
                                new_transcript.update(challenge_u64.to_le_bytes());
                                let mut le_bytes = [0u8; 8];
                                le_bytes
                                    .copy_from_slice(&new_transcript.finalize().as_slice()[..8]);
                                if u64::from_le_bytes(le_bytes).trailing_zeros() >= pow_bits {
                                    let _ = result.compare_exchange(
                                        KECCAK256_NO_RESULT,
                                        challenge_u64,
                                        Ordering::Acquire,
                                        Ordering::Relaxed,
                                    );

                                    break;
                                }
                            }
                        } else {
                            break;
                        }
                    }
                })
            }
        });

        let challenge_u64 = result.load(Ordering::SeqCst);

        assert!(Self::verify_from_bytes(seed, pow_bits, challenge_u64));

        challenge_u64
    }

    fn verify_from_bytes(seed: Vec<u8>, pow_bits: u32, challenge: u64) -> bool {
        let mut new_transcript = Keccak256::new();
        new_transcript.update(&seed);
        new_transcript.update(challenge.to_le_bytes());
        let mut le_bytes = [0u8; 8];
        le_bytes.copy_from_slice(&new_transcript.finalize().as_slice()[..8]);

        u64::from_le_bytes(le_bytes).trailing_zeros() >= pow_bits
    }
}
