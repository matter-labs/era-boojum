use proc_macro2::TokenStream;
use quote::quote;
use syn::punctuated::Punctuated;
use syn::{GenericParam, Generics, Ident, WhereClause};

/// Fetch an attribute string from the derived struct.
pub(crate) fn fetch_attr(name: &str, attrs: &[syn::Attribute]) -> Option<String> {
    for attr in attrs {
        if let Ok(meta) = attr.parse_meta() {
            match meta {
                syn::Meta::NameValue(nv) => {
                    if nv.path.is_ident(name) {
                        match nv.lit {
                            syn::Lit::Str(ref s) => return Some(s.value()),
                            _ => panic!("attribute {} not found", name),
                        }
                    }
                }
                _ => panic!("attribute {} not found", name),
            }
        }
    }

    None
}

pub(crate) fn merge_where_clauses(a: Option<WhereClause>, b: Option<WhereClause>) -> TokenStream {
    match (a, b) {
        (None, None) => {
            quote! {}
        }
        (Some(a), None) | (None, Some(a)) => {
            quote! { #a }
        }
        (Some(a), Some(b)) => {
            let mut result = a;
            result.predicates.extend(b.predicates);

            quote! { #result }
        }
    }
}

pub(crate) fn fetch_attr_from_list(name: &str, attrs: &[syn::Attribute]) -> Option<String> {
    for attr in attrs {
        if attr.path.is_ident(name) {
            if let Ok(meta) = attr.parse_meta() {
                match meta {
                    syn::Meta::List(ml) => {
                        if let Some(nv) = ml.nested.first() {
                            match nv {
                                syn::NestedMeta::Lit(nl) => match nl {
                                    syn::Lit::Str(ref s) => return Some(s.value()),
                                    _ => {}
                                },
                                _ => {}
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    None
}

pub(crate) fn fetch_attr_nopanic(name: &str, attrs: &[syn::Attribute]) -> Option<String> {
    for attr in attrs {
        if let Ok(meta) = attr.parse_meta() {
            match meta {
                syn::Meta::NameValue(nv) => {
                    if nv.path.is_ident(name) {
                        match nv.lit {
                            syn::Lit::Str(ref s) => return Some(s.value()),
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
    }

    None
}

pub(crate) fn has_proper_small_field_parameter<P>(
    generic_params: &Punctuated<GenericParam, P>,
    expected: &GenericParam,
) -> bool {
    for p in generic_params.iter() {
        if p == expected {
            return true;
        }
    }
    return false;
}

pub(crate) fn get_type_params_from_generics<P: Clone + Default>(
    generics: &Generics,
    punc: &P,
) -> Punctuated<Ident, P> {
    let type_params = generics.type_params();
    let const_params = generics.const_params();

    let mut idents = Punctuated::new();

    for param in type_params.into_iter() {
        let ident = param.ident.clone();
        idents.push(ident);
        idents.push_punct(punc.clone());
    }

    for param in const_params.into_iter() {
        let ident = param.ident.clone();
        idents.push(ident.clone());
        idents.push_punct(punc.clone());
    }

    idents
}

pub(crate) fn get_witness_ident(original_ident: &Ident) -> Ident {
    let mut witness_ident_str = original_ident.to_string();
    witness_ident_str.push_str(&"Witness");
    syn::parse_str(&witness_ident_str).unwrap()
}

pub(crate) fn get_type_params_from_generics_output_params<P: Clone + Default>(
    generics: &Generics,
    punc: &P,
) -> Punctuated<GenericParam, P> {
    let type_params = generics.type_params();
    let const_params = generics.const_params();

    let mut idents = Punctuated::new();

    for param in type_params.into_iter() {
        idents.push(GenericParam::Type(param.clone()));
        idents.push_punct(punc.clone());
    }

    for param in const_params.into_iter() {
        idents.push(GenericParam::Const(param.clone()));
        idents.push_punct(punc.clone());
    }

    idents
}

// pub(crate) fn has_small_field_parameter<P>(
//     generic_params: &Punctuated<GenericParam, P>,
// ) -> bool {
//     for p in generic_params.iter() {
//         match p {
//             GenericParam::Type(ty) => {
//                 for bound in ty.bounds.iter() {
//                     match bound {
//                         TypeParamBound::Trait(t) => {

//                         },
//                         _ => {}
//                     }
//                 }
//             }
//             _ => {}
//         }
//     }
//     return false;
// }
