use proc_macro2::{Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::quote;
use syn::{
    parse_macro_input, punctuated::Punctuated, token::Comma, DeriveInput, GenericParam, Type,
    WhereClause,
};

use crate::utils::*;

const BOUND_ATTR_NAME: &'static str = "CSVarLengthEncodableBound";

pub(crate) fn derive_var_length_encodable(
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

    let mut length_impls = TokenStream::new();
    let mut field_impls = TokenStream::new();

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
                        Type::Array(ref _array_ty) => {
                            let field_impl = quote! {
                                total_len += CircuitVarLengthEncodable::<F>::encoding_length(&self.#field_ident);
                            };
                            length_impls.extend(field_impl);

                            let field_impl = quote! {
                                CircuitVarLengthEncodable::<F>::encode_to_buffer(&self.#field_ident, cs, dst);
                            };
                            field_impls.extend(field_impl);
                        }
                        Type::Path(_) => {
                            let field_impl = quote! {
                                total_len += CircuitVarLengthEncodable::<F>::encoding_length(&self.#field_ident);
                            };
                            length_impls.extend(field_impl);
                            let field_impl = quote! {
                                CircuitVarLengthEncodable::<F>::encode_to_buffer(&self.#field_ident, cs, dst);
                            };
                            field_impls.extend(field_impl);
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

    // add CS to func generic params
    let mut function_generic_params = Punctuated::new();
    let cs_generic_param = syn::parse_str::<GenericParam>(&"CS: ConstraintSystem<F>").unwrap();
    function_generic_params.push(cs_generic_param.clone());
    function_generic_params.push_punct(comma.clone());

    let type_params_of_allocated_struct = get_type_params_from_generics(&generics, &comma);

    // let function_generics = Generics {
    //     lt_token: Some(syn::token::Lt(Span::call_site())),
    //     params: function_generic_params,
    //     gt_token: Some(syn::token::Gt(Span::call_site())),
    //     where_clause: None,
    // };

    let expanded = quote! {
        impl #generics CircuitVarLengthEncodable<F> for #ident<#type_params_of_allocated_struct> #bound {
            #[inline(always)]
            fn encoding_length(&self) -> usize {
                let mut total_len = 0;
                #length_impls;

                total_len
            }
            fn encode_to_buffer<CS: ConstraintSystem<F>>(&self, cs: &mut CS, dst: &mut Vec<Variable>) {
                #field_impls
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}
