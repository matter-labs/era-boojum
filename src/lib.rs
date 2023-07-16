#![allow(clippy::drop_ref)]
#![allow(dead_code)]
#![allow(dropping_references)]
#![allow(incomplete_features)]
#![feature(allocator_api)]
#![feature(const_mut_refs)]
#![feature(const_refs_to_cell)]
#![feature(const_for)]
#![feature(const_swap)]
#![feature(inline_const)]
#![feature(const_intoiterator_identity)]
#![feature(slice_swap_unchecked)]
#![feature(const_option)]
#![feature(const_slice_index)]
#![feature(core_intrinsics)]
#![feature(const_eval_select)]
#![feature(get_mut_unchecked)]
#![feature(array_chunks)]
#![feature(stmt_expr_attributes)]
#![feature(vec_into_raw_parts)]
#![feature(iter_collect_into)]
#![feature(strict_provenance)]
#![feature(ready_into_inner)]
#![feature(unboxed_closures)]
#![feature(portable_simd)]
#![feature(ptr_metadata)]
#![feature(fn_traits)]
#![feature(generic_const_exprs)]
#![feature(const_type_id)]
#![feature(const_type_name)]
#![feature(iter_array_chunks)]
#![feature(iter_next_chunk)]
// #![recursion_limit = "1024"]
#![feature(bigint_helper_methods)]
#![feature(const_bigint_helper_methods)]
#![feature(stdsimd)]
#![feature(avx512_target_feature)]
#![feature(associated_type_defaults)]
#![feature(trait_alias)]
#![feature(is_sorted)]
#![feature(vec_push_within_capacity)]
#![feature(cell_update)]
#![feature(return_position_impl_trait_in_trait)]
#![feature(type_changing_struct_update)]
#![feature(slice_flatten)]

pub mod algebraic_props;
pub mod config;
pub mod cs;
pub mod dag;
pub mod fft;
pub mod field;
pub mod gadgets;
pub mod gpu_synthesizer;
pub mod implementations;
pub mod serde_utils;
pub mod utils;
pub mod worker;

pub use blake2;
pub use crypto_bigint;
pub use pairing;
pub use sha2;
pub use sha3;

// #[cfg(target_arch = "aarch64")]
pub mod experiments;
pub mod log_utils;

pub(crate) use firestorm::{profile_fn, profile_section};
