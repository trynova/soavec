// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Data, DeriveInput, Fields, spanned::Spanned};

pub fn expand_data_struct(input: DeriveInput) -> syn::Result<TokenStream> {
    let struct_name = &input.ident;
    let generics = &input.generics;

    let (fields, is_tuple_struct) = match &input.data {
        Data::Struct(data_struct) => match &data_struct.fields {
            Fields::Named(fields_named) => Ok((&fields_named.named, false)),
            Fields::Unnamed(fields_unnamed) => Ok((&fields_unnamed.unnamed, true)),
            Fields::Unit => Err(syn::Error::new(
                input.span(),
                "Soable cannot be derived for unit structs",
            )),
        },
        _ => Err(syn::Error::new(
            input.span(),
            "Soable can only be derived for structs",
        )),
    }?;

    if fields.len() == 1 {
        return Err(syn::Error::new(
            fields.span(),
            "Soable cannot be derived for single-field structs; use a normal Vec instead",
        ));
    }

    // Generate the field names from the original struct.
    // - For a named struct it uses the original field names.
    // - For a tuple struct it generates names like _0, _1, _2, etc.
    let field_names: Vec<proc_macro2::Ident> = if is_tuple_struct {
        (0..fields.len())
            .map(|i| quote::format_ident!("_{}", i))
            .collect()
    } else {
        fields
            .iter()
            .map(|f| f.ident.as_ref().unwrap().clone())
            .collect()
    };

    let field_types: Vec<_> = fields.iter().map(|f| &f.ty).collect();
    let field_vis: Vec<_> = fields.iter().map(|f| &f.vis).collect();

    let ref_struct_name = quote::format_ident!("{}Ref", struct_name);
    let mut_struct_name = quote::format_ident!("{}Mut", struct_name);
    let slice_struct_name = quote::format_ident!("{}Slice", struct_name);
    let slice_mut_struct_name = quote::format_ident!("{}SliceMut", struct_name);

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let type_params = generics.type_params().collect::<Vec<_>>();
    let lifetime_params = generics.lifetimes().collect::<Vec<_>>();

    let has_type_generics = !type_params.is_empty();
    let has_lifetime_generics = !lifetime_params.is_empty();

    let helper_generics = if has_lifetime_generics || has_type_generics {
        quote! { <'soa, #(#lifetime_params,)* #(#type_params,)*> }
    } else {
        quote! { <'soa> }
    };

    let helper_ty_generics = if has_lifetime_generics || has_type_generics {
        let lifetime_idents = lifetime_params.iter().map(|lp| &lp.lifetime);
        let type_idents = type_params.iter().map(|tp| &tp.ident);
        quote! { <'soa, #(#lifetime_idents,)* #(#type_idents,)*> }
    } else {
        quote! { <'soa> }
    };

    let lifetime_bounds = if has_lifetime_generics {
        let bounds = lifetime_params.iter().map(|lp| {
            let lifetime = &lp.lifetime;
            quote! { #lifetime: 'soa }
        });
        quote! { #(#bounds),* }
    } else {
        quote! {}
    };

    let combined_where_clause = match (where_clause, has_lifetime_generics) {
        (Some(wc), true) => quote! { #wc, #lifetime_bounds },
        (Some(wc), false) => quote! { #wc },
        (None, true) => quote! { where #lifetime_bounds },
        (None, false) => quote! {},
    };

    let struct_vis = &input.vis;

    // Generate different patterns for destructuring and constructing depending
    // on whether it is a tuple struct or a named struct.
    let struct_pattern = if is_tuple_struct {
        quote! { Self(#(#field_names),*) }
    } else {
        quote! { Self { #(#field_names),* } }
    };

    // Note: use 'soa lifetime name as both more descriptive and less likely to
    // shadow the struct's lifetime.
    let expanded = quote! {
        #[allow(dead_code)]
        #struct_vis struct #ref_struct_name #helper_generics #combined_where_clause {
            #(#field_vis #field_names: &'soa #field_types),*
        }

        impl #helper_generics Copy for #ref_struct_name #helper_ty_generics #combined_where_clause {}
        impl #helper_generics Clone for #ref_struct_name #helper_ty_generics #combined_where_clause {
            fn clone(&self) -> Self {
                *self
            }
        }

        #[allow(dead_code)]
        #struct_vis struct #mut_struct_name #helper_generics #combined_where_clause {
            #(#field_vis #field_names: &'soa mut #field_types),*
        }

        #[allow(dead_code)]
        #struct_vis struct #slice_struct_name #helper_generics #combined_where_clause {
            #(#field_vis #field_names: &'soa [#field_types]),*
        }

        impl #helper_generics Copy for #slice_struct_name #helper_ty_generics #combined_where_clause {}
        impl #helper_generics Clone for #slice_struct_name #helper_ty_generics #combined_where_clause {
            fn clone(&self) -> Self {
                *self
            }
        }

        #[allow(dead_code)]
        #struct_vis struct #slice_mut_struct_name #helper_generics #combined_where_clause {
            #(#field_vis #field_names: &'soa mut [#field_types]),*
        }

        unsafe impl #impl_generics soavec::SoAble for #struct_name #ty_generics #where_clause {
            type TupleRepr = (#(#field_types),*);
            type Ref<'soa> = #ref_struct_name #helper_ty_generics where Self: 'soa;
            type Mut<'soa> = #mut_struct_name #helper_ty_generics where Self: 'soa;
            type Slice<'soa> = #slice_struct_name #helper_ty_generics where Self: 'soa;
            type SliceMut<'soa> = #slice_mut_struct_name #helper_ty_generics where Self: 'soa;

            fn into_tuple(value: Self) -> Self::TupleRepr {
                let #struct_pattern = value;
                (#(#field_names),*)
            }

            fn from_tuple(value: Self::TupleRepr) -> Self {
                let (#(#field_names),*) = value;
                #struct_pattern
            }

            fn as_ref<'soa>(
                _: std::marker::PhantomData<&'soa Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
            ) -> Self::Ref<'soa> {
                let (#(#field_names),*) = value;
                unsafe {
                    #ref_struct_name {
                        #(#field_names: #field_names.as_ref()),*
                    }
                }
            }

            fn as_mut<'soa>(
                _: std::marker::PhantomData<&'soa mut Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
            ) -> Self::Mut<'soa> {
                let (#(mut #field_names),*) = value;
                unsafe {
                    #mut_struct_name {
                        #(#field_names: #field_names.as_mut()),*
                    }
                }
            }

            fn as_slice<'soa>(
                _: std::marker::PhantomData<&'soa Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
                len: u32,
            ) -> Self::Slice<'soa> {
                let __soa_len = len as usize;
                let (#(#field_names),*) = value;
                unsafe {
                    #slice_struct_name {
                        #(#field_names: core::slice::from_raw_parts(#field_names.as_ptr(), __soa_len)),*
                    }
                }
            }

            fn as_mut_slice<'soa>(
                _: std::marker::PhantomData<&'soa mut Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
                len: u32,
            ) -> Self::SliceMut<'soa> {
                let __soa_len = len as usize;
                let (#(#field_names),*) = value;
                unsafe {
                    #slice_mut_struct_name {
                        #(#field_names: core::slice::from_raw_parts_mut(#field_names.as_ptr(), __soa_len)),*
                    }
                }
            }
        }
    };

    Ok(expanded)
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

        let result = expand_data_struct(input).unwrap().to_string();

        assert!(result.contains("impl soavec :: SoAble for TestStruct"));
        assert!(result.contains("type TupleRepr = (u32 , u64)"));
        assert!(result.contains("fn into_tuple"));
        assert!(result.contains("struct TestStructRef"));
        assert!(result.contains("struct TestStructMut"));
        assert!(result.contains("struct TestStructSlice"));
        assert!(result.contains("struct TestStructSliceMut"));
    }

    #[test]
    fn test_derives_visibility() {
        let input: DeriveInput = syn::parse_quote! {
            pub struct TestStruct {
                a: u32,
                b: u64,
            }
        };

        let result = expand_data_struct(input).unwrap().to_string();

        assert!(result.contains("pub struct TestStructMut"));
        assert!(result.contains("pub struct TestStructRef"));
        assert!(result.contains("pub struct TestStructSlice"));
        assert!(result.contains("pub struct TestStructSliceMut"));
    }

    #[test]
    fn test_expand_derive_soable_lifetime() {
        let input: DeriveInput = syn::parse_quote! {
            struct TestStruct<'a> {
                a: &'a u32,
                b: &'a u64,
            }
        };

        let result = expand_data_struct(input).unwrap().to_string();

        assert!(result.contains("impl < 'a > soavec :: SoAble for TestStruct < 'a >"),);
        assert!(result.contains("type TupleRepr = (& 'a u32 , & 'a u64)"));
        assert!(result.contains("fn into_tuple"));
        assert!(result.contains("TestStructRef < 'soa , 'a , >"));
        assert!(result.contains("'a : 'soa"));
        assert!(result.contains("& 'soa & 'a u32"));
    }

    #[test]
    fn test_simple_lifetime() {
        let input: DeriveInput = syn::parse_quote! {
            struct WithLifetime<'a> {
                data: &'a str,
                count: u32,
            }
        };

        let result = expand_data_struct(input).unwrap().to_string();

        assert!(result.contains("'a : 'soa"));

        assert!(result.contains("& 'soa & 'a str"));
        assert!(result.contains("& 'soa u32"));
    }

    #[test]
    fn test_complex_generics() {
        let input: DeriveInput = syn::parse_quote! {
            struct ComplexStruct<'a, 'b, T, U>
            where
                T: Clone,
                U: Default
            {
                first: &'a T,
                second: &'b str,
                owned: U,
            }
        };

        let result = expand_data_struct(input).unwrap();
        let result_str = result.to_string();

        assert!(result_str.contains("< 'soa , 'a , 'b , T , U ,"));

        assert!(result_str.contains("'a : 'soa"));
        assert!(result_str.contains("'b : 'soa"));

        assert!(result_str.contains("T : Clone"));
        assert!(result_str.contains("U : Default"));
    }

    #[test]
    fn test_tuple_struct() {
        let input: DeriveInput = syn::parse_quote! {
            struct TupleStruct(u32, f64, String);
        };

        let result = expand_data_struct(input).unwrap().to_string();

        assert!(result.contains("struct TupleStructRef"));
        assert!(result.contains("struct TupleStructMut"));
        assert!(result.contains("struct TupleStructSlice"));
        assert!(result.contains("struct TupleStructSliceMut"));

        assert!(result.contains("_0 : & 'soa u32"));
        assert!(result.contains("_1 : & 'soa f64"));
        assert!(result.contains("_2 : & 'soa String"));
    }

    #[test]
    fn test_field_visibility_preservation() {
        let input: DeriveInput = syn::parse_quote! {
            pub struct MixedVisStruct {
                pub public_field: u32,
                private_field: u64,
            }
        };

        let result = expand_data_struct(input).unwrap().to_string();

        assert!(result.contains("pub public_field : & 'soa u32"));
        assert!(result.contains("private_field : & 'soa u64"));
        assert!(!result.contains("pub private_field : & 'soa u64"));
    }

    #[test]
    fn test_single_field_error() {
        let input: DeriveInput = syn::parse_quote! {
            struct SingleField {
                a: u32,
            }
        };

        let result = expand_data_struct(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_zero_field_error() {
        let input: DeriveInput = syn::parse_quote! {
            struct ZeroField;
        };

        let result = expand_data_struct(input);
        assert!(result.is_err());
    }
}
