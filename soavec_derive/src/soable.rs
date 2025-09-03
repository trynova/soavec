// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Data, DeriveInput, Fields, spanned::Spanned};

pub fn expand_derive_soable(input: DeriveInput) -> syn::Result<TokenStream> {
    let struct_name = &input.ident;
    let generics = &input.generics;

    let fields = match &input.data {
        Data::Struct(data_struct) => match &data_struct.fields {
            Fields::Named(fields_named) => Ok(&fields_named.named),
            _ => Err(syn::Error::new(
                data_struct.fields.span(),
                "Soable can only be derived for structs with named fields",
            )),
        },
        _ => Err(syn::Error::new(
            input.span(),
            "Soable can only be derived for structs with named fields",
        )),
    }?;

    if fields.len() == 1 {
        return Err(syn::Error::new(
            fields.span(),
            "Soable cannot be derived for single-field structs; use a normal Vec instead",
        ));
    }

    let field_names: Vec<_> = fields.iter().map(|f| f.ident.as_ref().unwrap()).collect();
    let field_types: Vec<_> = fields.iter().map(|f| &f.ty).collect();

    // Note: use 'soa lifetime name as both more descriptive and less likely to
    // shadow the struct's lifetime.
    let impl_block = quote! {
        unsafe impl #generics soavec::SoAble for #struct_name #generics {
            type TupleRepr = (#(#field_types),*);
            type Ref<'soa> = (#(&'soa #field_types),*) where Self: 'soa;
            type Mut<'soa> = (#(&'soa mut #field_types),*) where Self: 'soa;
            type Slice<'soa> = (#(&'soa [#field_types]),*) where Self: 'soa;
            type SliceMut<'soa> = (#(&'soa mut [#field_types]),*) where Self: 'soa;

            fn into_tuple(value: Self) -> Self::TupleRepr {
                let Self { #(#field_names),* } = value;
                (#(#field_names),*)
            }

            fn from_tuple(value: Self::TupleRepr) -> Self {
                let (#(#field_names),*) = value;
                Self { #(#field_names),* }
            }

            fn as_ref<'soa>(
                _: std::marker::PhantomData<&'soa Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
            ) -> Self::Ref<'soa> {
                let (#(#field_names),*) = value;
                unsafe {
                    (#(#field_names.as_ref()),*)
                }
            }

            fn as_mut<'soa>(
                _: std::marker::PhantomData<&'soa mut Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
            ) -> Self::Mut<'soa> {
                let (#(mut #field_names),*) = value;
                unsafe {
                    (#(#field_names.as_mut()),*)
                }
            }

            fn as_slice<'soa>(
                _: std::marker::PhantomData<&'soa Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
                len: u32,
            ) -> Self::Slice<'soa> {
                let len = len as usize;
                let (#(#field_names),*) = value;
                unsafe {
                    (
                        #(core::slice::from_raw_parts(#field_names.as_ptr(), len)),*
                    )
                }
            }

            fn as_mut_slice<'soa>(
                _: std::marker::PhantomData<&'soa mut Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
                len: u32,
            ) -> Self::SliceMut<'soa> {
                let len = len as usize;
                let (#(#field_names),*) = value;
                unsafe {
                    (
                        #(core::slice::from_raw_parts_mut(#field_names.as_ptr(), len)),*
                    )
                }
            }
        }
    };

    Ok(impl_block)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expand_derive_soable() {
        let input: DeriveInput = syn::parse_quote! {
            struct TestStruct {
                a: u32,
                b: u64,
            }
        };

        let result = expand_derive_soable(input).unwrap();

        assert!(
            result
                .to_string()
                .contains("impl soavec :: SoAble for TestStruct")
        );
        assert!(result.to_string().contains("type TupleRepr = (u32 , u64)"));
        assert!(result.to_string().contains("fn into_tuple"));
    }

    #[test]
    fn test_expand_derive_soable_lifetime() {
        let input: DeriveInput = syn::parse_quote! {
            struct TestStruct<'a> {
                a: &'a u32,
                b: &'a u64,
            }
        };

        let result = expand_derive_soable(input).unwrap();

        assert!(
            result
                .to_string()
                .contains("impl < 'a > soavec :: SoAble for TestStruct < 'a >"),
        );
        assert!(
            result
                .to_string()
                .contains("type TupleRepr = (& 'a u32 , & 'a u64)")
        );
        assert!(result.to_string().contains("fn into_tuple"));
    }

    #[test]
    fn test_single_field_error() {
        let input: DeriveInput = syn::parse_quote! {
            struct SingleField {
                a: u32,
            }
        };

        let result = expand_derive_soable(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_zero_field_error() {
        let input: DeriveInput = syn::parse_quote! {
            struct ZeroField;
        };

        let result = expand_derive_soable(input);
        assert!(result.is_err());
    }
}
