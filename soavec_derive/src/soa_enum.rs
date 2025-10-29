// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Data, DeriveInput, Fields, Expr, Lit, spanned::Spanned};

pub fn expand_data_enum(input: DeriveInput) -> syn::Result<TokenStream> {
    let enum_name = &input.ident;
    let generics = &input.generics;

    let variants = match &input.data {
        Data::Enum(data_enum) => &data_enum.variants,
        _ => unreachable!(),
    };

    if variants.len() == 1 {
        return Err(syn::Error::new(
            variants.span(),
            "Soable cannot be derived for single-variant enums; use a normal Vec instead",
        ));
    }

    let max_fields = variants
        .iter()
        .map(|v| match &v.fields {
            Fields::Named(f) => f.named.len(),
            Fields::Unnamed(f) => f.unnamed.len(),
            Fields::Unit => 0,
        })
        .max()
        .unwrap_or(0);

    // Information about the variants
    let mut variant_data = Vec::new();
    let mut current_discriminant: Expr = syn::parse_quote!(0); 
    for variant in variants.iter() {
        let variant_name = &variant.ident;

        let discriminant_value = variant.discriminant
            .as_ref()
            .map(|(_, expr)| expr.clone())
            .unwrap_or_else(|| current_discriminant.clone());

        // Update current_discriminant for next variant
        current_discriminant = syn::parse_quote!(#discriminant_value + 1);

        // Get field names and types
        let (field_names, field_types): (Vec<_>, Vec<_>) = match &variant.fields {
            Fields::Named(fields_named) => fields_named
                .named
                .iter()
                .map(|f| (f.ident.as_ref().unwrap().clone(), &f.ty))
                .unzip(),
            Fields::Unnamed(fields_unnamed) => {
                let count = fields_unnamed.unnamed.len();
                let names: Vec<_> = (0..count)
                    .map(|i| quote::format_ident!("__field{}", i))
                    .collect();
                let types: Vec<_> = fields_unnamed.unnamed.iter().map(|f| &f.ty).collect();
                (names, types)
            }
            Fields::Unit => (vec![], vec![]),
        };

        variant_data.push((variant_name, discriminant_value, field_names, field_types));
    }

    // Build union fields for each field position
    let mut field_unions = Vec::new();
    for field_idx in 0..max_fields {
        let mut union_fields = Vec::new();

        for variant in variants.iter() {
            let variant_name = &variant.ident;
            let variant_name_lower = variant_name.to_string().to_lowercase();
            let union_field_name = quote::format_ident!("{}", variant_name_lower);

            let field_type = match &variant.fields {
                Fields::Named(fields_named) => {
                    if let Some(field) = fields_named.named.iter().nth(field_idx) {
                        let ty = &field.ty;
                        quote! { #ty }
                    } else {
                        quote! { () }
                    }
                }
                Fields::Unnamed(fields_unnamed) => {
                    if let Some(field) = fields_unnamed.unnamed.iter().nth(field_idx) {
                        let ty = &field.ty;
                        quote! { #ty }
                    } else {
                        quote! { () }
                    }
                }
                Fields::Unit => quote! { () },
            };

            union_fields.push((union_field_name, field_type));
        }

        field_unions.push(union_fields);
    }

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let type_params = generics.type_params().collect::<Vec<_>>();
    let lifetime_params = generics.lifetimes().collect::<Vec<_>>();

    let has_type_generics = !type_params.is_empty();
    let has_lifetime_generics = !lifetime_params.is_empty();

    let union_generics = if has_lifetime_generics || has_type_generics {
        let lifetime_idents = lifetime_params.iter().map(|lp| &lp.lifetime);
        let type_idents = type_params.iter().map(|tp| &tp.ident);
        quote! { <#(#lifetime_idents),* #(, #type_idents)*> }
    } else {
        quote! {}
    };

    let union_ty_generics = union_generics.clone();

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

    let enum_vis = &input.vis;

    // Generate union types for each field position
    let union_types: Vec<_> = field_unions
        .iter()
        .enumerate()
        .map(|(idx, union_fields)| {
            let union_name = quote::format_ident!("{}Field{}", enum_name, idx);
            let field_defs = union_fields.iter().map(|(name, ty)| {
                quote! { #name: #ty }
            });

            quote! {
                #[allow(dead_code)]
                #[derive(Copy, Clone)]
                #enum_vis union #union_name #union_generics {
                    #(#field_defs),*
                }
            }
        })
        .collect();

    // Generate Ref struct with discriminant + union references
    let ref_struct_name = quote::format_ident!("{}Ref", enum_name);
    let mut_struct_name = quote::format_ident!("{}Mut", enum_name);
    let slice_struct_name = quote::format_ident!("{}Slice", enum_name);
    let slice_mut_struct_name = quote::format_ident!("{}SliceMut", enum_name);

    let ref_fields: Vec<_> = (0..max_fields)
        .map(|idx| {
            let field_name = quote::format_ident!("_{}", idx);
            let union_name = quote::format_ident!("{}Field{}", enum_name, idx);
            quote! { #field_name: &'soa #union_name #union_ty_generics }
        })
        .collect();

    let mut_fields: Vec<_> = (0..max_fields)
        .map(|idx| {
            let field_name = quote::format_ident!("_{}", idx);
            let union_name = quote::format_ident!("{}Field{}", enum_name, idx);
            quote! { #field_name: &'soa mut #union_name #union_ty_generics }
        })
        .collect();

    let slice_fields: Vec<_> = (0..max_fields)
        .map(|idx| {
            let field_name = quote::format_ident!("_{}", idx);
            let union_name = quote::format_ident!("{}Field{}", enum_name, idx);
            quote! { #field_name: &'soa [#union_name #union_ty_generics] }
        })
        .collect();

    let slice_mut_fields: Vec<_> = (0..max_fields)
        .map(|idx| {
            let field_name = quote::format_ident!("_{}", idx);
            let union_name = quote::format_ident!("{}Field{}", enum_name, idx);
            quote! { #field_name: &'soa mut [#union_name #union_ty_generics] }
        })
        .collect();

    let union_names: Vec<_> = (0..max_fields)
        .map(|idx| {
            let union_name = quote::format_ident!("{}Field{}", enum_name, idx);
            quote! { #union_name #union_ty_generics }
        })
        .collect();

    let tuple_repr = if union_names.is_empty() {
        quote! { (u8,) }
    } else {
        quote! { (u8, #(#union_names),*) }
    };

    // Generate into_tuple match arms
    let into_tuple_arms: Vec<_> = variant_data.iter().map(|(variant_name, disc_value, field_names, _field_types)| {
        let variant_name_lower = variant_name.to_string().to_lowercase();

        if field_names.is_empty() {
            // Unit variant
            let union_constructions: Vec<_> = (0..max_fields).map(|idx| {
                let union_name = quote::format_ident!("{}Field{}", enum_name, idx);
                let union_field = quote::format_ident!("{}", variant_name_lower);
                quote! { #union_name #union_ty_generics { #union_field: () } }
            }).collect();

            if union_constructions.is_empty() {
                quote! {
                    Self::#variant_name => (#disc_value,)
                }
            } else {
                quote! {
                    Self::#variant_name => (#disc_value, #(#union_constructions),*)
                }
            }
        }
        else {
        // Variant with fields
            let union_constructions: Vec<_> = (0..max_fields).map(|idx| {
                let union_name = quote::format_ident!("{}Field{}", enum_name, idx);
                let union_field = quote::format_ident!("{}", variant_name_lower);

                if let Some(field_name) = field_names.get(idx) {
                    quote! { #union_name #union_ty_generics { #union_field: #field_name } }
                } else {
                    quote! { #union_name #union_ty_generics { #union_field: () } }
                }
            }).collect();

            quote! {
                Self::#variant_name(#(#field_names),*) => (#disc_value, #(#union_constructions),*)
            }
        }
    }).collect();

    // Generate from_tuple match arms
    let from_tuple_arms: Vec<_> = variant_data
        .iter()
        .map(|(variant_name, disc_value, field_names, _field_types)| {
            let variant_name_lower = variant_name.to_string().to_lowercase();

            if field_names.is_empty() {
                // Unit variant
                quote! {
                    #disc_value => Self::#variant_name
                }
            } else {
                // Variant with fields - extract from unions
                let field_extractions: Vec<_> = (0..field_names.len())
                    .map(|idx| {
                        let union_field_name = quote::format_ident!("__union{}", idx);
                        let union_field = quote::format_ident!("{}", variant_name_lower);
                        let field_name = &field_names[idx];
                        quote! {
                            let #field_name = unsafe { #union_field_name.#union_field };
                        }
                    })
                    .collect();

                quote! {
                    #disc_value => {
                        #(#field_extractions)*
                        Self::#variant_name(#(#field_names),*)
                    }
                }
            }
        })
        .collect();

    let union_field_names: Vec<_> = (0..max_fields)
        .map(|idx| quote::format_ident!("__union{}", idx))
        .collect();

    // Generate field names for Ref/Mut structs (_0, _1, _2, ...)
    let ref_union_field_names: Vec<_> = (0..max_fields)
        .map(|idx| quote::format_ident!("_{}", idx))
        .collect();

    let expanded = quote! {
        #(#union_types)*

        #[allow(dead_code)]
        #enum_vis struct #ref_struct_name #helper_generics #combined_where_clause {
            discriminant: &'soa core::mem::Discriminant<#enum_name #ty_generics>,
            #(#ref_fields),*
        }

        impl #helper_generics Copy for #ref_struct_name #helper_ty_generics #combined_where_clause {}
        impl #helper_generics Clone for #ref_struct_name #helper_ty_generics #combined_where_clause {
            fn clone(&self) -> Self {
                *self
            }
        }

        #[allow(dead_code)]
        #enum_vis struct #mut_struct_name #helper_generics #combined_where_clause {
            discriminant: &'soa core::mem::Discriminant<#enum_name #ty_generics>,
            #(#mut_fields),*
        }

        #[allow(dead_code)]
        #enum_vis struct #slice_struct_name #helper_generics #combined_where_clause {
            discriminant: &'soa [core::mem::Discriminant<#enum_name #ty_generics>],
            #(#slice_fields),*
        }

        impl #helper_generics Copy for #slice_struct_name #helper_ty_generics #combined_where_clause {}
        impl #helper_generics Clone for #slice_struct_name #helper_ty_generics #combined_where_clause {
            fn clone(&self) -> Self {
                *self
            }
        }

        #[allow(dead_code)]
        #enum_vis struct #slice_mut_struct_name #helper_generics #combined_where_clause {
            discriminant: &'soa mut [core::mem::Discriminant<#enum_name #ty_generics>],
            #(#slice_mut_fields),*
        }

        unsafe impl #impl_generics soavec::SoAble for #enum_name #ty_generics #where_clause {
            type TupleRepr = #tuple_repr;
            type Ref<'soa> = #ref_struct_name #helper_ty_generics where Self: 'soa;
            type Mut<'soa> = #mut_struct_name #helper_ty_generics where Self: 'soa;
            type Slice<'soa> = #slice_struct_name #helper_ty_generics where Self: 'soa;
            type SliceMut<'soa> = #slice_mut_struct_name #helper_ty_generics where Self: 'soa;

            fn into_tuple(value: Self) -> Self::TupleRepr {
                match value {
                    #(#into_tuple_arms),*
                }
            }

            fn from_tuple(value: Self::TupleRepr) -> Self {
                let (__disc, #(#union_field_names),*) = value;
                match __disc {
                    #(#from_tuple_arms),*,
                    _ => panic!("invalid discriminant: {}", __disc),
                }
            }

            fn as_ref<'soa>(
                _: std::marker::PhantomData<&'soa Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
            ) -> Self::Ref<'soa> {
                let (__disc_ptr, #(#union_field_names),*) = value;
                unsafe {
                    #ref_struct_name {
                        discriminant: core::mem::transmute(__disc_ptr.as_ptr()),
                        #(#ref_union_field_names: #union_field_names.as_ref()),*
                    }
                }
            }

            fn as_mut<'soa>(
                _: std::marker::PhantomData<&'soa mut Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
            ) -> Self::Mut<'soa> {
                let (__disc_ptr, #(mut #union_field_names),*) = value;
                unsafe {
                    #mut_struct_name {
                        discriminant: core::mem::transmute(__disc_ptr.as_ptr()),
                        #(#ref_union_field_names: #union_field_names.as_mut()),*
                    }
                }
            }

            fn as_slice<'soa>(
                _: std::marker::PhantomData<&'soa Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
                len: u32,
            ) -> Self::Slice<'soa> {
                let __soa_len = len as usize;
                let (__disc_ptr, #(#union_field_names),*) = value;
                unsafe {
                    #slice_struct_name {
                        discriminant: core::slice::from_raw_parts(core::mem::transmute(__disc_ptr.as_ptr()), __soa_len),
                        #(#ref_union_field_names: core::slice::from_raw_parts(#union_field_names.as_ptr(), __soa_len)),*
                    }
                }
            }

            fn as_mut_slice<'soa>(
                _: std::marker::PhantomData<&'soa mut Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
                len: u32,
            ) -> Self::SliceMut<'soa> {
                let __soa_len = len as usize;
                let (__disc_ptr, #(#union_field_names),*) = value;
                unsafe {
                    #slice_mut_struct_name {
                        discriminant: core::slice::from_raw_parts_mut(core::mem::transmute(__disc_ptr.as_ptr()), __soa_len),
                        #(#ref_union_field_names: core::slice::from_raw_parts_mut(#union_field_names.as_ptr(), __soa_len)),*
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
    fn test_expand_derive_enum() {
        let input: DeriveInput = syn::parse_quote! {
            enum TestEnum {
                Undefined,
                Null,
                Boolean(bool),
                Number(u32),
            }
        };

        let result = expand_data_enum(input).unwrap().to_string();

        // std::fs::write("test_expand_derive_enum_output.rs", &result).unwrap();

        assert!(result.contains("union TestEnumField0"));
        assert!(result.contains("undefined : ()"));
        assert!(result.contains("null : ()"));
        assert!(result.contains("boolean : bool"));
        assert!(result.contains("number : u32"));

        assert!(result.contains("struct TestEnumRef"));
        assert!(result.contains("discriminant : & 'soa core :: mem :: Discriminant < TestEnum >"));
        assert!(result.contains("_0 : & 'soa TestEnumField0"));

        assert!(result.contains("struct TestEnumMut"));
        assert!(result.contains("struct TestEnumSlice"));
        assert!(result.contains("struct TestEnumSliceMut"));

        assert!(result.contains("type TupleRepr = (u8 , TestEnumField0)"));
    }

    #[test]
    fn test_expand_derive_enum_explicit_discriminant() {
        let input: DeriveInput = syn::parse_quote!(
            enum Value {
                Undefined = 1,
                String(&'static str) = 2,
                Number(u32) = 3,
            }
        );

        let result = expand_data_enum(input).unwrap().to_string();

        // std::fs::write("test_expand_derive_enum_explicit_discriminant.rs", &result).unwrap();

        assert!(result.contains("union ValueField0"));
        assert!(result.contains("undefined : ()"));
        assert!(result.contains("string : & 'static str"));
        assert!(result.contains("number : u32"));

        assert!(result.contains("struct ValueRef"));
        assert!(result.contains("discriminant : & 'soa core :: mem :: Discriminant < Value >"));
        assert!(result.contains("_0 : & 'soa ValueField0"));

        assert!(result.contains("struct ValueMut"));
        assert!(result.contains("struct ValueSlice"));
        assert!(result.contains("struct ValueSliceMut"));
    }

    #[test]
    fn test_expand_derive_enum_with_lifetimes() {
        let input: DeriveInput = syn::parse_quote! {
            enum Value<'a> {
                Undefined,
                String(&'a str),
                Number(u32),
            }
        };

        let result = expand_data_enum(input).unwrap().to_string();

        assert!(result.contains("union ValueField0") && result.contains("'a"));
        assert!(result.contains("string : & 'a str"));

        assert!(
            result.contains("struct ValueRef") && result.contains("'soa") && result.contains("'a")
        );
        assert!(result.contains("'a : 'soa"));
    }

    #[test]
    fn test_single_variant_enum_error() {
        let input: DeriveInput = syn::parse_quote! {
            enum SingleVariant {
                OnlyOne(u32),
            }
        };

        let result = expand_data_enum(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_multiple_field_variants() {
        let input: DeriveInput = syn::parse_quote! {
            enum MultiField {
                VariantA(u32, f64),
                VariantB(bool, String, i32),
                VariantC,
            }
        };

        let result = expand_data_enum(input).unwrap().to_string();

        // std::fs::write("test_multiple_field_variants_output.rs", &result).unwrap();

        assert!(result.contains("union MultiFieldField0"));
        assert!(result.contains("union MultiFieldField1"));
        assert!(result.contains("union MultiFieldField2"));

        assert!(result.contains("u32"));
        assert!(result.contains("f64"));
        assert!(result.contains("bool"));
        assert!(result.contains("String"));
        assert!(result.contains("i32"));
    }
}
