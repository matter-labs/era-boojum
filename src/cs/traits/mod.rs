use std::alloc::Allocator;

use super::*;

pub mod circuit;
pub mod composite_type;
pub mod cs;
pub mod destination_view;
pub mod evaluator;
pub mod gate;
pub mod trace_source;

pub trait GoodAllocator: Allocator + Clone + Default + Send + Sync + std::fmt::Debug {}

impl GoodAllocator for std::alloc::Global {}
