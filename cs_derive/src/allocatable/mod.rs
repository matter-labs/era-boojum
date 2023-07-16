use proc_macro2::{Ident, Literal, Span, TokenStream};
use proc_macro_error::abort_call_site;
use quote::quote;
use syn::{
    parse_macro_input, token::Comma, Attribute, Data, DeriveInput, Fields, GenericParam, Generics,
    Type, TypeArray, TypePath,
};

use crate::utils::*;

const SERDE_REMOVE_BOUNDS: &'static str = "SerdeRemoveBounds";
const PRETTY_COMPARISON_ATTR: &'static str = "DerivePrettyComparison";

pub(crate) fn derive_allocatable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let derived_input = parse_macro_input!(input as DeriveInput);

    let DeriveInput {
        ident,
        data,
        generics,
        attrs,
        ..
    } = derived_input.clone();

    let serde_remove_bounds =
        if let Some(serde_remove_bounds) = fetch_attr_nopanic(SERDE_REMOVE_BOUNDS, &attrs) {
            let serde_remove_bounds =
                syn::parse_str::<syn::Expr>(&serde_remove_bounds).expect("has attr as Expr");

            serde_remove_bounds == syn::parse_str::<syn::Expr>("true").unwrap()
        } else {
            false
        };

    let derive_pretty_comparison = if let Some(derive_pretty_comparison) =
        fetch_attr_from_list(PRETTY_COMPARISON_ATTR, &attrs)
    {
        let derive_pretty_comparison =
            syn::parse_str::<syn::Expr>(&derive_pretty_comparison).expect("has attr as Expr");

        derive_pretty_comparison == syn::parse_str::<syn::Expr>("true").unwrap()
    } else {
        false
    };

    let mut allocations = TokenStream::new();
    let mut allocations_without_value = TokenStream::new();
    let mut allocations_as_constant = TokenStream::new();
    let mut initializations = TokenStream::new();
    let mut placeholder_initializations = TokenStream::new();

    let mut pretty_comparison_lines = TokenStream::new();

    match data {
        syn::Data::Struct(ref struct_data) => match struct_data.fields {
            syn::Fields::Named(ref named_fields) => {
                for field in named_fields.named.iter() {
                    let field_ident = field.ident.clone().expect("a field ident");

                    let allocation_line = match field.ty {
                        Type::Path(ref _path_ty) => {
                            derive_allocate_by_type_path(&field_ident, _path_ty)
                        }
                        Type::Array(ref _arr_ty) => {
                            derive_allocate_by_array_type(&field_ident, _arr_ty)
                        }
                        _ => abort_call_site!("only array and path types are allowed"),
                    };
                    allocations.extend(allocation_line);

                    let allocation_without_value_line = match field.ty {
                        Type::Path(ref _path_ty) => {
                            derive_allocate_without_value_by_type_path(&field_ident, _path_ty)
                        }
                        Type::Array(ref _arr_ty) => {
                            derive_allocate_without_value_by_array_type(&field_ident, _arr_ty)
                        }
                        _ => abort_call_site!("only array and path types are allowed"),
                    };
                    allocations_without_value.extend(allocation_without_value_line);

                    let allocations_as_constant_line = match field.ty {
                        Type::Path(ref _path_ty) => {
                            derive_allocate_as_constant_by_type_path(&field_ident, _path_ty)
                        }
                        Type::Array(ref _arr_ty) => {
                            derive_allocate_as_constant_by_array_type(&field_ident, _arr_ty)
                        }
                        _ => abort_call_site!("only array and path types are allowed"),
                    };
                    allocations_as_constant.extend(allocations_as_constant_line);

                    let placeholder_init_line = match field.ty {
                        Type::Path(ref _path_ty) => {
                            derive_placeholder_witness_by_type(&field_ident, _path_ty)
                        }
                        Type::Array(ref _arr_ty) => {
                            derive_placeholder_witness_by_array_type(&field_ident, _arr_ty)
                        }
                        _ => abort_call_site!("only array and path types are allowed"),
                    };

                    placeholder_initializations.extend(placeholder_init_line);

                    if derive_pretty_comparison {
                        match field.ty {
                            Type::Array(ref _array_ty) => {
                                let lit = Literal::string(&format!("{}", field_ident));
                                let field_impl = quote! {
                                    if &a.#field_ident != &b.#field_ident {
                                        comparison_lines.push(
                                            format!(
                                                "`{}`:\nLeft value: `{:?}`\nRight value: `{:?}`",
                                                #lit,
                                                &a.#field_ident,
                                                &b.#field_ident
                                            )
                                        );
                                    }
                                };
                                pretty_comparison_lines.extend(field_impl);
                            }
                            Type::Path(_) => {
                                let lit = Literal::string(&format!("{}", field_ident));
                                let field_impl = quote! {
                                    if &a.#field_ident != &b.#field_ident {
                                        comparison_lines.push(
                                            format!(
                                                "`{}`:\nLeft value: `{:?}`\nRight value: `{:?}`",
                                                #lit,
                                                &a.#field_ident,
                                                &b.#field_ident
                                            )
                                        );
                                    }
                                };
                                pretty_comparison_lines.extend(field_impl);
                            }
                            _ => abort_call_site!("only array and path types are allowed"),
                        };
                    }

                    initializations.extend(quote! {
                        #field_ident,
                    });
                }
            }
            _ => abort_call_site!("only named fields are allowed"),
        },
        _ => abort_call_site!("only data structs are allowed"),
    }

    let comma = Comma(Span::call_site());

    let type_params_of_allocated_struct = get_type_params_from_generics(&generics, &comma);

    let where_clause = if let Some(clause) = generics.where_clause.as_ref() {
        quote! {
            #clause
        }
    } else {
        quote! {}
    };

    let field_generic_param = syn::parse_str::<GenericParam>(&"F: SmallField").unwrap();
    let has_engine_param = has_proper_small_field_parameter(&generics.params, &field_generic_param);
    if has_engine_param == false {
        panic!("Expected to have `F: SmallField` somewhere in bounds");
    }

    let witness_ident = get_witness_ident(&ident);
    let witness_struct = derive_witness_struct_recursive(derived_input.clone());

    let derive_line = if serde_remove_bounds {
        quote! {
            #[derive(Derivative, ::serde::Serialize, ::serde::Deserialize)]
            #[derivative(Clone, Debug, Hash(bound = ""), PartialEq(bound = ""), Eq(bound = ""))]
        }
    } else {
        quote! {
            #[derive(Derivative, ::serde::Serialize, ::serde::Deserialize)]
            #[serde(bound = "")]
            #[derivative(Clone, Debug, Hash(bound = ""), PartialEq(bound = ""), Eq(bound = ""))]
        }
    };

    let mut expanded = quote! {
        #derive_line
        #witness_struct

        impl #generics CSAllocatable<F> for #ident<#type_params_of_allocated_struct> #where_clause {

            type Witness = #witness_ident <#type_params_of_allocated_struct>;

            fn placeholder_witness() -> Self::Witness {
                #witness_ident :: <#type_params_of_allocated_struct> {
                    #placeholder_initializations
                }
            }

            fn allocate<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
                #allocations

                Self {
                    #initializations
                }
            }

            fn allocate_without_value<CS: ConstraintSystem<F>>(cs: &mut CS) -> Self {
                #allocations_without_value

                Self {
                    #initializations
                }
            }

            fn allocate_constant<CS: ConstraintSystem<F>>(cs: &mut CS, witness: Self::Witness) -> Self {
                #allocations_as_constant

                Self {
                    #initializations
                }
            }
        }
    };

    if derive_pretty_comparison {
        expanded.extend(quote!{
            impl #generics PrettyComparison<F> for #ident<#type_params_of_allocated_struct> #where_clause {
                fn find_diffs(a: &Self::Witness, b: &Self::Witness) -> Vec<String> {
                    let mut comparison_lines = vec![];
                    #pretty_comparison_lines

                    comparison_lines
                }
            }
        });
    }

    proc_macro::TokenStream::from(expanded)
}

fn derive_allocate_by_type_path(ident: &Ident, ty: &TypePath) -> TokenStream {
    // create a witness element
    quote! {
        let wit = witness.#ident.clone();
        let #ident = <#ty as CSAllocatable<F>>::allocate(cs, wit);
    }
}

fn derive_allocate_by_array_type(ident: &Ident, ty: &TypeArray) -> TokenStream {
    quote! {
        let wit = witness.#ident.clone();
        let #ident = <#ty as CSAllocatable<F>>::allocate(cs, wit);
    }
}

fn derive_allocate_without_value_by_type_path(ident: &Ident, ty: &TypePath) -> TokenStream {
    quote! {
        let #ident = <#ty as CSAllocatable<F>>::allocate_without_value(cs);
    }
}

fn derive_allocate_without_value_by_array_type(ident: &Ident, ty: &TypeArray) -> TokenStream {
    quote! {
        let #ident = <#ty as CSAllocatable<F>>::allocate_without_value(cs);
    }
}

fn derive_allocate_as_constant_by_type_path(ident: &Ident, ty: &TypePath) -> TokenStream {
    quote! {
        let wit = witness.#ident.clone();
        let #ident = <#ty as CSAllocatable<F>>::allocate_constant(cs, wit);
    }
}

fn derive_allocate_as_constant_by_array_type(ident: &Ident, ty: &TypeArray) -> TokenStream {
    quote! {
        let wit = witness.#ident.clone();
        let #ident = <#ty as CSAllocatable<F>>::allocate_constant(cs, wit);
    }
}

fn derive_placeholder_witness_by_type(ident: &Ident, ty: &TypePath) -> TokenStream {
    quote! {
        #ident: <#ty as CSAllocatable<F>>::placeholder_witness(),
    }
}

fn derive_placeholder_witness_by_array_type(ident: &Ident, ty: &TypeArray) -> TokenStream {
    quote! {
        #ident: <#ty as CSAllocatable<F>>::placeholder_witness(),
    }
}

pub(crate) fn derive_witness_struct_recursive(derived_input: DeriveInput) -> DeriveInput {
    let DeriveInput {
        attrs: _attrs,
        vis,
        ident,
        generics,
        mut data,
        ..
    } = derived_input;

    let comma = Comma(Span::call_site());

    match data {
        Data::Struct(ref mut struct_data) => {
            match struct_data.fields {
                // we only use named fields for now
                Fields::Named(ref mut fields) => {
                    for field in fields.named.iter_mut() {
                        let (new_ty, derive_hint) = get_equivalent_type_recursive(&field.ty);
                        field.ty = new_ty;
                        match derive_hint {
                            SerdeDeriveToUse::Default => {
                                // let att: Attribute = syn::parse_quote! {
                                //     #[serde(bound = "")]
                                // };
                                // field.attrs.push(att);
                            }
                            SerdeDeriveToUse::BigArray => {
                                let att: Attribute = syn::parse_quote! {
                                    #[serde(with = "BigArraySerde")]
                                };
                                field.attrs.push(att);
                            }
                        }
                    }
                }
                _ => abort_call_site!("only named fields are allowed"),
            }
        }
        _ => abort_call_site!("only structs are allowed"),
    };

    let punc_generic_params = get_type_params_from_generics_output_params(&generics, &comma);

    let new_generics = Generics {
        lt_token: generics.lt_token,
        params: punc_generic_params,
        gt_token: generics.gt_token,
        where_clause: generics.where_clause,
    };

    let witness_ident = get_witness_ident(&ident);

    DeriveInput {
        attrs: vec![],
        vis: vis,
        ident: witness_ident,
        generics: new_generics,
        data: data,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SerdeDeriveToUse {
    Default,
    BigArray,
}

// we assume that every type implements a trait
pub(crate) fn get_equivalent_type_recursive(original_ty: &Type) -> (Type, SerdeDeriveToUse) {
    match original_ty {
        Type::Array(ty) => {
            let ts = quote! {
                <#ty as CSAllocatable<F>>::Witness
            };
            let ts = proc_macro::TokenStream::from(ts);
            (
                Type::Path(syn::parse::<TypePath>(ts).unwrap()),
                SerdeDeriveToUse::BigArray,
            )
        }
        Type::Path(ty) => {
            let ts = quote! {
                <#ty as CSAllocatable<F>>::Witness
            };
            let ts = proc_macro::TokenStream::from(ts);
            (
                Type::Path(syn::parse::<TypePath>(ts).unwrap()),
                SerdeDeriveToUse::Default,
            )
        }
        _ => abort_call_site!("only array and path types are allowed"),
    }
}
