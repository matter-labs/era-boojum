// Allowed lints
// Whenever add an item here, please write a short yet meaningful comment on why so.
#![allow(
    clippy::incorrect_clone_impl_on_copy_type, // False positives in derivative: https://github.com/mcarton/rust-derivative/issues/112
    clippy::bool_comparison, // Explicitness is good in critical contexts.
    clippy::mut_from_ref, // Triggers on unsafe functions (e.g. ones using `UnsafeCell`).
    clippy::type_complexity, // Many types in this create are inherently complex.
    clippy::needless_range_loop, // Suggested code is often less readable than original.
    clippy::identity_op, // Suggested code is often less readable than original.
    clippy::too_many_arguments, // No easy way around this.
    clippy::len_zero, // Breaks consistency for bound checks.
    clippy::new_without_default, // Suggests writing more code than required
    clippy::let_unit_value, // False positives.
    clippy::let_and_return, // Suggests less expressive code.
    clippy::assertions_on_constants, // Doesn't play well with existing dev approach.
    clippy::drop_non_drop, // Reduces explicitness when marking mutable references as dropped.
    clippy::needless_pass_by_ref_mut, // Mutable references are often used indirectly (e.g. via unsafe code).
    clippy::int_plus_one, // Suggests less expressive code.
    clippy::bool_assert_comparison, // This crate prefers explicitness.
)]
#![allow(dead_code)]
#![allow(dropping_references)] // Required to explicitly show that mutable references are dropped.
#![allow(incomplete_features)]
#![allow(internal_features)] // Required for core_intrinsics
#![allow(stable_features)]
#![allow(unused_unsafe)]
// Enabled features
#![feature(allocator_api)]
#![feature(const_mut_refs)]
#![feature(const_swap)]
#![feature(inline_const)]
#![feature(slice_swap_unchecked)]
#![feature(const_slice_index)]
#![feature(core_intrinsics)]
#![feature(const_eval_select)]
#![feature(get_mut_unchecked)]
#![feature(array_chunks)]
#![feature(stmt_expr_attributes)]
#![feature(vec_into_raw_parts)]
#![feature(iter_collect_into)]
#![feature(strict_provenance)]
#![feature(unboxed_closures)]
#![feature(portable_simd)]
#![feature(ptr_metadata)]
#![feature(fn_traits)]
#![feature(generic_const_exprs)]
#![feature(iter_array_chunks)]
// #![recursion_limit = "1024"]
#![feature(avx512_target_feature)]
#![feature(associated_type_defaults)]
#![feature(trait_alias)]
#![feature(vec_push_within_capacity)]
#![feature(return_position_impl_trait_in_trait)]
#![feature(type_changing_struct_update)]
#![feature(slice_flatten)]
#![cfg_attr(feature = "include_packed_simd", feature(stdsimd))]

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
pub use ethereum_types;
pub use pairing;
pub use sha2;
pub use sha3;

// #[cfg(target_arch = "aarch64")]
// pub mod experiments;

pub mod log_utils;

pub(crate) use firestorm::{profile_fn, profile_section};
