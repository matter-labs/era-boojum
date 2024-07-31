#![allow(dead_code)]

use proc_macro::TokenStream;

mod allocatable;
mod selectable;
pub(crate) mod utils;
mod var_length_encodable;
mod witness_hook;
mod witness_var_length_encodable;

#[proc_macro_derive(CSSelectable, attributes(CSSelectableBound))]
#[proc_macro_error::proc_macro_error]
pub fn derive_selectable(input: TokenStream) -> TokenStream {
    self::selectable::derive_select(input)
}

#[proc_macro_derive(CSAllocatable, attributes(DerivePrettyComparison))]
#[proc_macro_error::proc_macro_error]
pub fn derive_allocatable(input: TokenStream) -> TokenStream {
    self::allocatable::derive_allocatable(input)
}

#[proc_macro_derive(WitnessHookable, attributes(WitnessHookBound))]
#[proc_macro_error::proc_macro_error]
pub fn derive_witness_hook(input: TokenStream) -> TokenStream {
    self::witness_hook::derive_witness_hook(input)
}

#[proc_macro_derive(CSVarLengthEncodable, attributes(CSVarLengthEncodableBound))]
#[proc_macro_error::proc_macro_error]
pub fn derive_var_length_encodable(input: TokenStream) -> TokenStream {
    self::var_length_encodable::derive_var_length_encodable(input)
}

#[proc_macro_derive(WitVarLengthEncodable, attributes(WitnessVarLengthEncodableBound))]
#[proc_macro_error::proc_macro_error]
pub fn derive_witness_length_encodable(input: TokenStream) -> TokenStream {
    self::witness_var_length_encodable::derive_witness_var_length_encodable(input)
}
