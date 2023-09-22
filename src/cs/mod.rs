use self::implementations::lookup_table::{LookupTable, LookupTableWrapper, Wrappable};

use self::traits::trace_source::TraceSource;
use arrayvec::ArrayVec;

use super::*;
use crate::config::CSConfig;
use crate::field::traits::field_like::TrivialContext;
use crate::field::SmallField;
use crate::worker::Worker;
use derivative::Derivative;
use smallvec::SmallVec;
use std::collections::{HashMap, VecDeque};
use std::fmt::Debug;

pub mod cs_builder;
pub mod cs_builder_reference;
pub mod cs_builder_verifier;
pub mod gates;
pub mod implementations;
pub mod oracle;
pub mod toolboxes;
pub mod traits;

pub use crate::cs::toolboxes::gate_config::*;
pub use crate::cs::toolboxes::static_toolbox::*;

// one of the most important set of traits is how do we want to approach a proof system
// that is simultaneously easy to write for, and can utilize high complexity parallelism
// underneath

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Place(pub(crate) u64);

pub enum VariableType {
    CopyableVariable = 0,
    Witness = 1,
}

// when we will evaluate copy-chains we need to know whether it's and index of variable,
// or a copy of another variable in some column and row
const PLACEHOLDER_BIT_MASK: u64 = 1u64 << 63;
const WITNESS_BIT_MASK: u64 = 1u64 << 62;

const LOW_U48_MASK: u64 = (1u64 << 48) - 1;

impl Place {
    #[inline(always)]
    pub const fn placeholder() -> Self {
        Self(PLACEHOLDER_BIT_MASK)
    }

    pub fn get_type(&self) -> VariableType {
        //std::mem::transmute::<bool, VariableType>((self.0 & Self::WITNESS_BIT_MASK) != 0)
        if self.is_copiable_variable() {
            VariableType::CopyableVariable
        } else {
            VariableType::Witness
        }
    }

    pub fn raw_ix(&self) -> usize {
        (self.0 & LOW_U48_MASK) as usize
    }

    #[inline(always)]
    pub const fn is_copiable_variable(&self) -> bool {
        self.0 & WITNESS_BIT_MASK == 0
    }

    #[inline(always)]
    pub const fn is_witness(&self) -> bool {
        self.0 & WITNESS_BIT_MASK != 0
    }

    #[inline(always)]
    pub const fn as_variable(&self) -> Variable {
        debug_assert!(self.is_copiable_variable());
        debug_assert!(!self.is_placeholder());

        Variable(self.0)
    }

    #[inline(always)]
    pub const fn as_any_index(&self) -> u64 {
        debug_assert!(!self.is_placeholder());
        self.0 & LOW_U48_MASK
    }

    #[inline(always)]
    pub const fn is_placeholder(&self) -> bool {
        self.0 & PLACEHOLDER_BIT_MASK != 0
    }

    #[inline(always)]
    pub const fn as_witness(&self) -> Witness {
        debug_assert!(self.is_witness());
        debug_assert!(!self.is_placeholder());

        let idx = self.0 & LOW_U48_MASK;

        Witness::from_witness_index(idx)
    }

    #[inline(always)]
    pub const fn from_variable(variable: Variable) -> Self {
        debug_assert!(variable.is_placeholder() == false);
        Self(variable.0)
    }

    #[inline(always)]
    pub const fn from_witness(witness: Witness) -> Self {
        Self(witness.0 | WITNESS_BIT_MASK)
    }

    #[inline(always)]
    pub fn from_variables<const N: usize>(variables: [Variable; N]) -> [Self; N] {
        variables.map(Self::from_variable)
    }

    #[inline(always)]
    pub fn from_witnesses<const N: usize>(witnesses: [Witness; N]) -> [Self; N] {
        witnesses.map(Self::from_witness)
    }
}

impl PartialOrd for Place {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.is_placeholder() || other.is_placeholder() {
            None
        } else {
            Some(self.as_any_index().cmp(&other.as_any_index()))
        }
    }
}

impl Debug for Place {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let t = match self.get_type() {
            VariableType::CopyableVariable => "cv_",
            VariableType::Witness => "w_",
        };

        f.write_fmt(format_args!("{}{}", t, self.0))
    }
}

// Variable is quite diverse, and to have "good" alignment and size we
// manually do encoding management to be able to represent it as both
// copiable variable or witness
#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Variable(pub(crate) u64);

impl Variable {
    #[inline(always)]
    pub const fn placeholder() -> Self {
        Self(PLACEHOLDER_BIT_MASK)
    }

    #[inline(always)]
    pub const fn as_variable_index(&self) -> u32 {
        debug_assert!(!self.is_placeholder());

        let var_idx = self.0 & LOW_U48_MASK;

        var_idx as u32
    }

    #[inline(always)]
    pub const fn is_placeholder(&self) -> bool {
        self.0 & PLACEHOLDER_BIT_MASK != 0
    }

    #[inline(always)]
    pub const fn from_variable_index(variable_index: u64) -> Self {
        Self(variable_index)
    }
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Witness(pub(crate) u64);

impl Witness {
    // when we will evaluate copy-chains we need to know whether it's and index of variable,
    // or a copy of another variable in some column and row

    #[inline(always)]
    pub const fn placeholder() -> Self {
        Self(PLACEHOLDER_BIT_MASK)
    }

    #[inline(always)]
    pub const fn as_witness_index(&self) -> u64 {
        debug_assert!(!self.is_placeholder());

        let idx = self.0 & LOW_U48_MASK;

        idx
    }

    #[inline(always)]
    pub const fn is_placeholder(&self) -> bool {
        self.0 & PLACEHOLDER_BIT_MASK != 0
    }

    #[inline(always)]
    pub const fn from_witness_index(witness_index: u64) -> Self {
        Self(witness_index)
    }
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CSGeometry {
    pub num_columns_under_copy_permutation: usize,
    pub num_witness_columns: usize,
    pub num_constant_columns: usize,
    pub max_allowed_constraint_degree: usize,
}

#[derive(Derivative, serde::Serialize, serde::Deserialize)]
#[derivative(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LookupParameters {
    NoLookup,
    TableIdAsVariable {
        width: u32,
        share_table_id: bool,
    },
    TableIdAsConstant {
        width: u32,
        share_table_id: bool,
    },
    UseSpecializedColumnsWithTableIdAsVariable {
        width: u32,
        num_repetitions: usize,
        share_table_id: bool,
    },
    UseSpecializedColumnsWithTableIdAsConstant {
        width: u32,
        num_repetitions: usize,
        share_table_id: bool,
    },
}

impl LookupParameters {
    pub const fn lookup_is_allowed(&self) -> bool {
        !matches!(self, LookupParameters::NoLookup)
    }

    pub const fn is_specialized_lookup(&self) -> bool {
        match self {
            LookupParameters::NoLookup => unreachable!(),
            LookupParameters::UseSpecializedColumnsWithTableIdAsVariable { .. } => true,
            LookupParameters::UseSpecializedColumnsWithTableIdAsConstant { .. } => true,
            _ => false,
        }
    }

    pub const fn lookup_width(&self) -> usize {
        match self {
            LookupParameters::NoLookup => 0,
            LookupParameters::TableIdAsVariable { width, .. } => *width as usize,
            LookupParameters::TableIdAsConstant { width, .. } => *width as usize,
            LookupParameters::UseSpecializedColumnsWithTableIdAsVariable { width, .. } => {
                *width as usize
            }
            LookupParameters::UseSpecializedColumnsWithTableIdAsConstant { width, .. } => {
                *width as usize
            }
        }
    }

    pub const fn share_table_id(&self) -> bool {
        match self {
            LookupParameters::NoLookup => {
                unreachable!()
            }
            LookupParameters::TableIdAsVariable { share_table_id, .. } => *share_table_id,
            LookupParameters::TableIdAsConstant { share_table_id, .. } => *share_table_id,
            LookupParameters::UseSpecializedColumnsWithTableIdAsVariable {
                share_table_id, ..
            } => *share_table_id,
            LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                share_table_id, ..
            } => *share_table_id,
        }
    }

    pub const fn columns_per_subargument(&self) -> u32 {
        match self {
            LookupParameters::TableIdAsConstant { width, .. } => *width,
            LookupParameters::TableIdAsVariable { width, .. } => *width + 1,
            _ => unreachable!(),
        }
    }

    pub const fn specialized_columns_per_subargument(&self) -> u32 {
        match self {
            LookupParameters::UseSpecializedColumnsWithTableIdAsConstant { width, .. } => *width,
            LookupParameters::UseSpecializedColumnsWithTableIdAsVariable { width, .. } => {
                *width + 1
            }
            _ => unreachable!(),
        }
    }

    pub(crate) const fn num_specialized_repetitions(&self) -> usize {
        match self {
            LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                num_repetitions,
                ..
            } => *num_repetitions,
            LookupParameters::UseSpecializedColumnsWithTableIdAsVariable {
                num_repetitions,
                ..
            } => *num_repetitions,
            _ => unreachable!(),
        }
    }

    #[inline]
    pub fn num_sublookup_arguments_for_geometry(&self, geometry: &CSGeometry) -> usize {
        match self {
            LookupParameters::NoLookup => 0,
            LookupParameters::TableIdAsVariable { width, .. } => {
                let principal_width = (*width as usize) + 1;
                geometry.num_columns_under_copy_permutation / principal_width
            }
            LookupParameters::TableIdAsConstant { width, .. } => {
                let principal_width = *width as usize;
                geometry.num_columns_under_copy_permutation / principal_width
            }
            LookupParameters::UseSpecializedColumnsWithTableIdAsVariable {
                num_repetitions,
                ..
            } => *num_repetitions,
            LookupParameters::UseSpecializedColumnsWithTableIdAsConstant {
                num_repetitions,
                ..
            } => *num_repetitions,
        }
    }

    #[inline]
    pub fn num_multipicities_polys(&self, total_tables_len: usize, trace_len: usize) -> usize {
        match self {
            LookupParameters::NoLookup => 0,
            _ => {
                if total_tables_len > trace_len {
                    unimplemented!("not yet supported")
                } else {
                    1
                }
            }
        }
    }
}

pub trait GateTool: 'static + std::any::Any + Send + Sync {
    fn create() -> Self
    where
        Self: Sized;
}

impl GateTool for () {
    fn create() -> Self {}
}

impl<K: 'static + Send + Sync, V: 'static + Send + Sync> GateTool
    for std::collections::HashMap<K, V>
{
    fn create() -> Self {
        Self::new()
    }
}

impl<T: 'static + Send + Sync> GateTool for Option<T> {
    fn create() -> Self {
        None
    }
}

impl<V: 'static + Send + Sync> GateTool for std::collections::HashSet<V> {
    fn create() -> Self {
        Self::new()
    }
}

impl<T: 'static + Send + Sync> GateTool for Vec<T> {
    fn create() -> Self {
        Self::new()
    }
}

impl<T: 'static + Send + Sync> GateTool for VecDeque<T> {
    fn create() -> Self {
        Self::new()
    }
}

impl From<Variable> for Place {
    #[inline(always)]
    fn from(variable: Variable) -> Place {
        Place::from_variable(variable)
    }
}

impl From<Witness> for Place {
    #[inline(always)]
    fn from(witness: Witness) -> Place {
        Place::from_witness(witness)
    }
}
