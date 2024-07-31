use proc_macro2::{Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::quote;
use syn::{parse_macro_input, token::Comma, DeriveInput, GenericParam, Type, WhereClause};

use crate::utils::*;

const BOUND_ATTR_NAME: &'static str = "WitnessVarLengthEncodableBound";

pub(crate) fn derive_witness_var_length_encodable(
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);
    let DeriveInput {
        ident,
        generics,
        data,
        attrs,
        ..
    } = derived_input.clone();

    let mut witness_to_buffer_impls = TokenStream::new();
    let mut witness_length_impls = TokenStream::new();

    let extra_bound = if let Some(bound) = fetch_attr_from_list(BOUND_ATTR_NAME, &attrs) {
        let bound = syn::parse_str::<WhereClause>(&bound).expect("must parse bound as WhereClause");

        Some(bound)
    } else {
        None
    };

    let bound = merge_where_clauses(generics.where_clause.clone(), extra_bound);

    match data {
        syn::Data::Struct(ref struct_data) => match struct_data.fields {
            syn::Fields::Named(ref named_fields) => {
                for field in named_fields.named.iter() {
                    let field_ident = field.ident.clone().expect("should have a field elem ident");
                    match field.ty {
                        Type::Array(ref array_ty) => {
                            let wit_to_buf_impl = quote! {
                                <#array_ty as WitnessVarLengthEncodable<F>>::encode_witness_to_buffer(&witness.#field_ident, dst);
                            };
                            witness_to_buffer_impls.extend(wit_to_buf_impl);
                            let wit_length_impl = quote! {
                                total_len += <#array_ty as WitnessVarLengthEncodable<F>>::witness_encoding_length(&witness.#field_ident);
                            };
                            witness_length_impls.extend(wit_length_impl);
                        }
                        Type::Path(ref path_ty) => {
                            let wit_to_buf_impl = quote! {
                                <#path_ty as WitnessVarLengthEncodable<F>>::encode_witness_to_buffer(&witness.#field_ident, dst);
                            };
                            witness_to_buffer_impls.extend(wit_to_buf_impl);
                            let wit_length_impl = quote! {
                                total_len += <#path_ty as WitnessVarLengthEncodable<F>>::witness_encoding_length(&witness.#field_ident);
                            };
                            witness_length_impls.extend(wit_length_impl);
                        }
                        _ => abort_call_site!("only array and path types are allowed"),
                    };
                }
            }
            _ => abort_call_site!("only named fields are allowed!"),
        },
        _ => abort_call_site!("only struct types are allowed!"),
    }

    let comma = Comma(Span::call_site());

    let field_generic_param = syn::parse_str::<GenericParam>(&"F: SmallField").unwrap();
    let has_engine_param = has_proper_small_field_parameter(&generics.params, &field_generic_param);
    if has_engine_param == false {
        panic!("Expected to have `F: SmallField` somewhere in bounds");
    }

    let type_params_of_allocated_struct = get_type_params_from_generics(&generics, &comma);

    let expanded = quote! {
        impl #generics WitnessVarLengthEncodable<F> for #ident<#type_params_of_allocated_struct> #bound {
            fn witness_encoding_length(witness: &Self::Witness) -> usize {
                let mut total_len = 0;
                #witness_length_impls

                total_len
            }
            fn encode_witness_to_buffer(witness: &Self::Witness, dst: &mut Vec<F>) {
                #witness_to_buffer_impls
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}
