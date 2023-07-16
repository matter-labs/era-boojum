//! Machinery for multi-threaded proving.
use rayon::{ThreadPool, ThreadPoolBuilder};

// We allocate a pool of (ideally) high-performance cores only!
pub struct Worker {
    pool: ThreadPool,
    pub num_cores: usize,
}

// For some reason stack size is different in debug/release, and in rust-analyzer and without it, so we enforce it
pub const REQUIRED_STACK_SIZE: usize = 8 * 1024 * 1024;

impl Worker {
    pub fn new() -> Self {
        let num_cores = num_cpus::get_physical();
        let pool = ThreadPoolBuilder::new()
            .num_threads(num_cores)
            .stack_size(REQUIRED_STACK_SIZE)
            .build()
            .expect("failed to build thread pool");

        Self { pool, num_cores }
    }

    pub fn new_with_num_threads(num_threads: usize) -> Self {
        let pool = ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .stack_size(REQUIRED_STACK_SIZE)
            .build()
            .expect("failed to build thread pool");

        Self {
            pool,
            num_cores: num_threads,
        }
    }

    pub const fn compute_chunk_size(work_size: usize, num_chunks: usize) -> usize {
        if work_size <= num_chunks {
            1
        } else {
            let mut chunk_size = work_size / num_chunks;
            if work_size % num_chunks != 0 {
                chunk_size += 1;
            }

            chunk_size
        }
    }

    pub const fn compute_num_chunks(work_size: usize, chunk_size: usize) -> usize {
        if work_size <= chunk_size {
            1
        } else {
            let mut num_chunks = work_size / chunk_size;
            if work_size % chunk_size != 0 {
                num_chunks += 1;
            }

            num_chunks
        }
    }

    pub const fn get_chunk_size(&self, work_size: usize) -> usize {
        Self::compute_chunk_size(work_size, self.num_cores)
    }

    pub fn scope<'a, F, R>(&self, work_size: usize, f: F) -> R
    where
        F: FnOnce(&rayon::Scope<'a>, usize) -> R,
    {
        let chunk_size = self.get_chunk_size(work_size);

        self.pool.in_place_scope(|scope| f(scope, chunk_size))
    }

    pub fn scope_with_num_chunks<'a, F, R>(&self, work_size: usize, f: F) -> R
    where
        F: FnOnce(&rayon::Scope<'a>, usize, usize) -> R,
    {
        let chunk_size = self.get_chunk_size(work_size);
        let num_chunks = Self::compute_num_chunks(work_size, chunk_size);

        self.pool
            .in_place_scope(|scope| f(scope, chunk_size, num_chunks))
    }
}
