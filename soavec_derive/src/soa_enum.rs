// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Data, DeriveInput, Fields, spanned::Spanned};

fn union_name(enum_name: &syn::Ident, idx: usize) -> syn::Ident {
    quote::format_ident!("{}Field{}", enum_name, idx)
}

fn union_field_name(variant_name: &syn::Ident) -> syn::Ident {
    let variant_name_lower = variant_name.to_string().to_lowercase();
    quote::format_ident!("{}", variant_name_lower)
}

/// Extract field names and types from a variant
fn extract_fields(fields: &Fields) -> (Vec<syn::Ident>, Vec<&syn::Type>) {
    match fields {
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
    }
}

/// Get the type for a field at a specific index, or () if it doesn't exist
fn field_type_at_index(fields: &Fields, field_idx: usize) -> TokenStream {
    match fields {
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
    }
}

/// Get the max number of fields across all variants
fn get_max_fields(
    variants: &syn::punctuated::Punctuated<syn::Variant, syn::token::Comma>,
) -> usize {
    variants
        .iter()
        .map(|v| match &v.fields {
            Fields::Named(f) => f.named.len(),
            Fields::Unnamed(f) => f.unnamed.len(),
            Fields::Unit => 0,
        })
        .max()
        .unwrap_or(0)
}

pub fn expand_data_enum(input: DeriveInput) -> syn::Result<TokenStream> {
    let enum_name = &input.ident;
    let generics = &input.generics;

    let variants = match &input.data {
        Data::Enum(data_enum) => &data_enum.variants,
        _ => unreachable!(),
    };

    if variants.is_empty() {
        return Err(syn::Error::new(
            variants.span(),
            "Soable cannot be derived for enums with no variants",
        ));
    }

    let is_mixed_fields = {
        let mut has_named = false;
        let mut has_unnamed = false;

        for variant in variants.iter() {
            match &variant.fields {
                Fields::Named(_) => has_named = true,
                Fields::Unnamed(_) => has_unnamed = true,
                Fields::Unit => {}
            }
        }

        has_named && has_unnamed
    };

    if is_mixed_fields {
        return Err(syn::Error::new(
            variants.span(),
            "Soable does not know how to pair up fields that are named and unnamed; use either all named or all unnamed fields",
        ));
    }

    let max_fields = get_max_fields(variants);
    let discriminant_enum_name = quote::format_ident!("{}Discriminant", enum_name);

    // Extract repr attributes to apply to discriminant enum
    let repr_attrs: Vec<_> = input
        .attrs
        .iter()
        .filter(|attr| attr.path().is_ident("repr"))
        .collect();

    // Generate discriminant-only enum variants (without fields)
    let discriminant_variants: Vec<_> = variants
        .iter()
        .map(|v| {
            let variant_name = &v.ident;
            let discriminant = v
                .discriminant
                .as_ref()
                .map(|(eq, expr)| quote! { #eq #expr });

            quote! {
                #variant_name #discriminant
            }
        })
        .collect();

    // Extract variant information: variant name, field names, and whether fields are named
    let variant_data: Vec<_> = variants
        .iter()
        .map(|variant| {
            let variant_name = &variant.ident;
            let (field_names, _) = extract_fields(&variant.fields);
            let is_named = matches!(&variant.fields, Fields::Named(_));
            (variant_name, field_names, is_named)
        })
        .collect();

    // Build union fields for each field position
    let field_unions: Vec<Vec<_>> = (0..max_fields)
        .map(|field_idx| {
            variants
                .iter()
                .map(|variant| {
                    let field_name = union_field_name(&variant.ident);
                    let field_type = field_type_at_index(&variant.fields, field_idx);
                    (field_name, field_type)
                })
                .collect()
        })
        .collect();

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let type_params = generics.type_params().collect::<Vec<_>>();
    let lifetime_params = generics.lifetimes().collect::<Vec<_>>();

    let has_type_generics = !type_params.is_empty();
    let has_lifetime_generics = !lifetime_params.is_empty();

    // Build generic parameter lists for unions and helper structs
    let (union_generics, helper_generics, helper_ty_generics) =
        if has_lifetime_generics || has_type_generics {
            let union_gen = {
                let lifetime_idents = lifetime_params.iter().map(|lp| &lp.lifetime);
                let type_idents = type_params.iter().map(|tp| &tp.ident);
                quote! { <#(#lifetime_idents),* #(, #type_idents)*> }
            };
            let helper_gen = quote! { <'soa, #(#lifetime_params,)* #(#type_params,)*> };
            let helper_ty_gen = {
                let lifetime_idents = lifetime_params.iter().map(|lp| &lp.lifetime);
                let type_idents = type_params.iter().map(|tp| &tp.ident);
                quote! { <'soa, #(#lifetime_idents,)* #(#type_idents,)*> }
            };

            (union_gen, helper_gen, helper_ty_gen)
        } else {
            (quote! {}, quote! { <'soa> }, quote! { <'soa> })
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
            let u_name = union_name(enum_name, idx);
            let field_defs = union_fields.iter().map(|(name, ty)| {
                quote! { #name: #ty }
            });

            quote! {
                #[allow(dead_code)]
                #[derive(Copy, Clone)]
                #enum_vis union #u_name #union_generics {
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
            let u_name = union_name(enum_name, idx);
            quote! { #field_name: &'soa #u_name #union_generics }
        })
        .collect();

    let mut_fields: Vec<_> = (0..max_fields)
        .map(|idx| {
            let field_name = quote::format_ident!("_{}", idx);
            let u_name = union_name(enum_name, idx);
            quote! { #field_name: &'soa mut #u_name #union_generics }
        })
        .collect();

    let slice_fields: Vec<_> = (0..max_fields)
        .map(|idx| {
            let field_name = quote::format_ident!("_{}", idx);
            let u_name = union_name(enum_name, idx);
            quote! { #field_name: &'soa [#u_name #union_generics] }
        })
        .collect();

    let slice_mut_fields: Vec<_> = (0..max_fields)
        .map(|idx| {
            let field_name = quote::format_ident!("_{}", idx);
            let u_name = union_name(enum_name, idx);
            quote! { #field_name: &'soa mut [#u_name #union_generics] }
        })
        .collect();

    let union_names: Vec<_> = (0..max_fields)
        .map(|idx| {
            let u_name = union_name(enum_name, idx);
            quote! { #u_name #union_generics }
        })
        .collect();

    // Generate into_tuple match arms
    let into_tuple_arms: Vec<_> = variant_data.iter().map(|(variant_name, field_names, is_named)| {
        let u_field = union_field_name(variant_name);

        if field_names.is_empty() {
            // Unit variant
            let union_constructions: Vec<_> = (0..max_fields).map(|idx| {
                let u_name = union_name(enum_name, idx);
                quote! { #u_name #union_generics { #u_field: () } }
            }).collect();

            if union_constructions.is_empty() {
                quote! {
                    Self::#variant_name => (#discriminant_enum_name::#variant_name,)
                }
            } else {
                quote! {
                    Self::#variant_name => (#discriminant_enum_name::#variant_name, #(#union_constructions),*)
                }
            }
        } else {
            // Variant with fields
            let union_constructions: Vec<_> = (0..max_fields).map(|idx| {
                let u_name = union_name(enum_name, idx);

                if let Some(field_name) = field_names.get(idx) {
                    quote! { #u_name #union_generics { #u_field: #field_name } }
                } else {
                    quote! { #u_name #union_generics { #u_field: () } }
                }
            }).collect();

            // Use {} for named fields, () for unnamed/tuple fields
            let pattern = if *is_named {
                quote! { Self::#variant_name { #(#field_names),* } }
            } else {
                quote! { Self::#variant_name(#(#field_names),*) }
            };

            quote! {
                #pattern => (#discriminant_enum_name::#variant_name, #(#union_constructions),*)
            }
        }
    }).collect();

    // Generate from_tuple match arms
    let from_tuple_arms: Vec<_> = variant_data
        .iter()
        .map(|(variant_name, field_names, is_named)| {
            let u_field = union_field_name(variant_name);

            if field_names.is_empty() {
                // Unit variant
                quote! {
                    #discriminant_enum_name::#variant_name => Self::#variant_name
                }
            } else {
                // Variant with fields - extract from unions
                let field_extractions: Vec<_> = (0..field_names.len())
                    .map(|idx| {
                        let union_field_name = quote::format_ident!("__union{}", idx);
                        let field_name = &field_names[idx];
                        quote! {
                            let #field_name = unsafe { #union_field_name.#u_field };
                        }
                    })
                    .collect();

                // Use {} for named fields, () for unnamed/tuple fields
                let construction = if *is_named {
                    quote! { Self::#variant_name { #(#field_names),* } }
                } else {
                    quote! { Self::#variant_name(#(#field_names),*) }
                };

                quote! {
                    #discriminant_enum_name::#variant_name => {
                        #(#field_extractions)*
                        #construction
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

    // Build the tuple repr type
    let tuple_repr = if max_fields == 0 {
        quote! { (#discriminant_enum_name,) }
    } else {
        quote! { (#discriminant_enum_name, #(#union_names),*) }
    };

    let expanded = quote! {
        // Generate the discriminant-only enum
        #(#repr_attrs)*
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        #enum_vis enum #discriminant_enum_name {
            #(#discriminant_variants),*
        }

        #(#union_types)*

        #[allow(dead_code)]
        #enum_vis struct #ref_struct_name #helper_generics #combined_where_clause {
            discriminant: &'soa #discriminant_enum_name,
            #(#ref_fields),*
        }

        impl #helper_generics Copy for #ref_struct_name #helper_ty_generics #combined_where_clause {}
        impl #helper_generics Clone for #ref_struct_name #helper_ty_generics #combined_where_clause {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl #helper_generics #ref_struct_name #helper_ty_generics #combined_where_clause {
            /// Returns a reference to the discriminant.
            #[inline]
            pub fn get_discriminant(&self) -> &#discriminant_enum_name {
                self.discriminant
            }
        }

        #[allow(dead_code)]
        #enum_vis struct #mut_struct_name #helper_generics #combined_where_clause {
            discriminant: &'soa mut #discriminant_enum_name,
            #(#mut_fields),*
        }

        impl #helper_generics #mut_struct_name #helper_ty_generics #combined_where_clause {
            /// Returns a reference to the discriminant.
            #[inline]
            pub fn get_discriminant(&self) -> &#discriminant_enum_name {
                self.discriminant
            }

            /// Returns a mutable reference to the discriminant.
            ///
            /// # Safety
            ///
            /// Caller must ensure the discriminant value matches the union field data.
            /// Changing the discriminant without updating the union fields is undefined behavior.
            #[inline]
            pub unsafe fn get_discriminant_mut(&mut self) -> &mut #discriminant_enum_name {
                self.discriminant
            }
        }

        #[allow(dead_code)]
        #enum_vis struct #slice_struct_name #helper_generics #combined_where_clause {
            discriminant: &'soa [#discriminant_enum_name],
            #(#slice_fields),*
        }

        impl #helper_generics Copy for #slice_struct_name #helper_ty_generics #combined_where_clause {}
        impl #helper_generics Clone for #slice_struct_name #helper_ty_generics #combined_where_clause {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl #helper_generics #slice_struct_name #helper_ty_generics #combined_where_clause {
            /// Returns a reference to the discriminant slice.
            #[inline]
            pub fn get_discriminant(&self) -> &[#discriminant_enum_name] {
                self.discriminant
            }
        }

        #[allow(dead_code)]
        #enum_vis struct #slice_mut_struct_name #helper_generics #combined_where_clause {
            discriminant: &'soa mut [#discriminant_enum_name],
            #(#slice_mut_fields),*
        }

        impl #helper_generics #slice_mut_struct_name #helper_ty_generics #combined_where_clause {
            /// Returns a reference to the discriminant slice.
            #[inline]
            pub fn get_discriminant(&self) -> &[#discriminant_enum_name] {
                self.discriminant
            }

            /// Returns a mutable reference to the discriminant slice.
            ///
            /// # Safety
            ///
            /// For each index, the discriminant must match the union field data at that index.
            /// Changing discriminants without updating union fields is undefined behavior.
            #[inline]
            pub unsafe fn get_discriminant_mut(&mut self) -> &mut [#discriminant_enum_name] {
                self.discriminant
            }
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
                    #(#from_tuple_arms),*
                }
            }

            fn as_ref<'soa>(
                _: std::marker::PhantomData<&'soa Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
            ) -> Self::Ref<'soa> {
                let (__disc_ptr, #(#union_field_names),*) = value;
                unsafe {
                    #ref_struct_name {
                        discriminant: &*(__disc_ptr.as_ptr() as *const _),
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
                        discriminant: &mut *(__disc_ptr.as_ptr() as *mut _),
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
                        discriminant: core::slice::from_raw_parts(__disc_ptr.as_ptr() as *const _, __soa_len),
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
                        discriminant: core::slice::from_raw_parts_mut(__disc_ptr.as_ptr() as *mut _, __soa_len),
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
            #[repr(u8)]
            enum TestEnum {
                Undefined,
                Null,
                Boolean(bool),
                Number(u32),
            }
        };

        let result = expand_data_enum(input).unwrap().to_string();

        assert!(result.contains("enum TestEnumDiscriminant"));
        assert!(result.contains("Undefined"));
        assert!(result.contains("Null"));
        assert!(result.contains("Boolean"));
        assert!(result.contains("Number"));

        assert!(result.contains("union TestEnumField0"));
        assert!(result.contains("undefined : ()"));
        assert!(result.contains("null : ()"));
        assert!(result.contains("boolean : bool"));
        assert!(result.contains("number : u32"));

        assert!(result.contains("struct TestEnumRef"));
        assert!(result.contains("discriminant : & 'soa TestEnumDiscriminant"));
        assert!(result.contains("_0 : & 'soa TestEnumField0"));

        assert!(result.contains("struct TestEnumMut"));
        assert!(result.contains("struct TestEnumSlice"));
        assert!(result.contains("struct TestEnumSliceMut"));

        assert!(result.contains("type TupleRepr = (TestEnumDiscriminant , TestEnumField0)"));
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

        // Check for discriminant enum with explicit values
        assert!(result.contains("enum ValueDiscriminant"));
        assert!(result.contains("Undefined = 1"));
        assert!(result.contains("String = 2"));
        assert!(result.contains("Number = 3"));

        assert!(result.contains("union ValueField0"));
        assert!(result.contains("undefined : ()"));
        assert!(result.contains("string : & 'static str"));
        assert!(result.contains("number : u32"));

        assert!(result.contains("struct ValueRef"));
        assert!(result.contains("discriminant : & 'soa ValueDiscriminant"));
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
    fn test_empty_variant_enum_error() {
        let input: DeriveInput = syn::parse_quote! {
            enum EmptyEnum {}
        };

        let result = expand_data_enum(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_mixed_enum_error() {
        let input: DeriveInput = syn::parse_quote! {
            enum MixedEnum {
                A { x: u32 },
                B(u32),
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

        assert!(result.contains("union MultiFieldField0"));
        assert!(result.contains("union MultiFieldField1"));
        assert!(result.contains("union MultiFieldField2"));

        assert!(result.contains("u32"));
        assert!(result.contains("f64"));
        assert!(result.contains("bool"));
        assert!(result.contains("String"));
        assert!(result.contains("i32"));
    }

    #[test]
    fn test_creates_discriminant_enum() {
        let input: DeriveInput = syn::parse_quote! {
            #[repr(C, u8)]
            enum CustomDiscriminants {
                A = 10,
                B(String, u32) = 20,
                C,
                D = some_function(),
            }
        };

        let result = expand_data_enum(input).unwrap().to_string();

        assert!(result.contains("# [repr (C , u8)]"));
        assert!(result.contains("enum CustomDiscriminantsDiscriminant"));
        assert!(result.contains("A = 10"));
        assert!(result.contains("B = 20"));
        assert!(result.contains("C ,"));
        assert!(result.contains("D = some_function ()"));
    }
}
