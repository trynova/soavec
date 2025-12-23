// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{Data, DeriveInput, Fields, spanned::Spanned};
use std::collections::BTreeMap;

fn union_name(enum_name: &syn::Ident, field_name: &str) -> syn::Ident {
    quote::format_ident!("{}Field{}", enum_name, field_name)
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

/// NEW: Collect all unique field names across all variants (for named fields)
fn collect_all_field_names(
    variants: &syn::punctuated::Punctuated<syn::Variant, syn::token::Comma>,
) -> Vec<String> {
    let mut field_names = BTreeMap::new();
    
    for variant in variants.iter() {
        if let Fields::Named(fields_named) = &variant.fields {
            for field in fields_named.named.iter() {
                let name = field.ident.as_ref().unwrap().to_string();
                field_names.insert(name, ());
            }
        }
    }
    
    field_names.into_keys().collect()
}

/// NEW: Get the type for a specific named field in a variant, or () if it doesn't exist
fn field_type_by_name<'a>(fields: &'a Fields, field_name: &str) -> Option<&'a syn::Type> {
    match fields {
        Fields::Named(fields_named) => {
            fields_named.named.iter()
                .find(|f| f.ident.as_ref().unwrap() == field_name)
                .map(|f| &f.ty)
        }
        _ => None,
    }
}

/// Get the type for a field at a specific index, or () if it doesn't exist (for unnamed fields)
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

    // CHANGE: Determine if we have named fields
    let has_named_fields = variants.iter().any(|v| matches!(&v.fields, Fields::Named(_)));
    
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
            let (field_names, field_types) = extract_fields(&variant.fields);
            let is_named = matches!(&variant.fields, Fields::Named(_));
            (variant_name, field_names, field_types, is_named)
        })
        .collect();

    // CHANGE: Build union fields differently for named vs unnamed
    let (field_unions, all_field_identifiers): (Vec<Vec<_>>, Vec<String>) = if has_named_fields {
        // For NAMED fields: organize by field name
        let all_field_names = collect_all_field_names(variants);
        
        let unions: Vec<Vec<_>> = all_field_names.iter().map(|field_name| {
            variants.iter().map(|variant| {
                let variant_field_name = union_field_name(&variant.ident);
                
                if let Some(field_type) = field_type_by_name(&variant.fields, field_name) {
                    (variant_field_name, quote! { #field_type })
                } else {
                    (variant_field_name, quote! { () })
                }
            }).collect()
        }).collect();
        
        (unions, all_field_names)
    } else {
        // For UNNAMED fields: organize by position (original behavior)
        let identifiers: Vec<_> = (0..max_fields)
            .map(|idx| format!("field{}", idx))
            .collect();
        
        let unions: Vec<Vec<_>> = (0..max_fields).map(|field_idx| {
            variants.iter().map(|variant| {
                let field_name = union_field_name(&variant.ident);
                let field_type = field_type_at_index(&variant.fields, field_idx);
                (field_name, field_type)
            }).collect()
        }).collect();
        
        (unions, identifiers)
    };

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

    // CHANGE: Generate union types with proper names
    let union_types: Vec<_> = field_unions
        .iter()
        .zip(all_field_identifiers.iter())
        .map(|(union_fields, field_str)| {
            let u_name = union_name(enum_name, field_str);
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

    // CHANGE: Use actual field names instead of _0, _1, _2
    let ref_fields: Vec<_> = all_field_identifiers.iter().map(|field_str| {
        let field_ident = quote::format_ident!("{}", field_str);
        let u_name = union_name(enum_name, field_str);
        quote! { #field_ident: &'soa #u_name #union_generics }
    }).collect();

    let mut_fields: Vec<_> = all_field_identifiers.iter().map(|field_str| {
        let field_ident = quote::format_ident!("{}", field_str);
        let u_name = union_name(enum_name, field_str);
        quote! { #field_ident: &'soa mut #u_name #union_generics }
    }).collect();

    let slice_fields: Vec<_> = all_field_identifiers.iter().map(|field_str| {
        let field_ident = quote::format_ident!("{}", field_str);
        let u_name = union_name(enum_name, field_str);
        quote! { #field_ident: &'soa [#u_name #union_generics] }
    }).collect();

    let slice_mut_fields: Vec<_> = all_field_identifiers.iter().map(|field_str| {
        let field_ident = quote::format_ident!("{}", field_str);
        let u_name = union_name(enum_name, field_str);
        quote! { #field_ident: &'soa mut [#u_name #union_generics] }
    }).collect();

    let union_names: Vec<_> = all_field_identifiers.iter().map(|field_str| {
        let u_name = union_name(enum_name, field_str);
        quote! { #u_name #union_generics }
    }).collect();

    // CHANGE: Update into_tuple to use field names for named enums
    let into_tuple_arms: Vec<_> = variant_data.iter().map(|(variant_name, field_names, _field_types, is_named)| {
        let u_field = union_field_name(variant_name);

        if field_names.is_empty() {
            // Unit variant
            let union_constructions: Vec<_> = all_field_identifiers.iter().map(|field_str| {
                let u_name = union_name(enum_name, field_str);
                quote! { #u_name #union_generics { #u_field: () } }
            }).collect();

            if all_field_identifiers.is_empty() {
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
            let union_constructions: Vec<_> = if has_named_fields {
                // For named fields: match by field name
                all_field_identifiers.iter().map(|field_str| {
                    let u_name = union_name(enum_name, field_str);
                    let field_ident = quote::format_ident!("{}", field_str);
                    
                    if field_names.iter().any(|f| f.to_string() == *field_str) {
                        quote! { #u_name #union_generics { #u_field: #field_ident } }
                    } else {
                        quote! { #u_name #union_generics { #u_field: () } }
                    }
                }).collect()
            } else {
                // For unnamed fields: match by position
                all_field_identifiers.iter().enumerate().map(|(idx, field_str)| {
                    let u_name = union_name(enum_name, field_str);
                    
                    if let Some(field_name) = field_names.get(idx) {
                        quote! { #u_name #union_generics { #u_field: #field_name } }
                    } else {
                        quote! { #u_name #union_generics { #u_field: () } }
                    }
                }).collect()
            };

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

    // CHANGE: Update from_tuple to use field names for named enums
    let from_tuple_arms: Vec<_> = variant_data
        .iter()
        .map(|(variant_name, field_names, _field_types, is_named)| {
            let u_field = union_field_name(variant_name);

            if field_names.is_empty() {
                // Unit variant
                quote! {
                    #discriminant_enum_name::#variant_name => Self::#variant_name
                }
            } else {
                // Variant with fields - extract from unions
                let field_extractions: Vec<_> = if has_named_fields {
                    // For named fields: extract by field name
                    field_names.iter().map(|field_name| {
                        let union_var_name = quote::format_ident!("__union_{}", field_name);
                        quote! {
                            let #field_name = unsafe { #union_var_name.#u_field };
                        }
                    }).collect()
                } else {
                    // For unnamed fields: extract by position
                    field_names.iter().enumerate().map(|(idx, field_name)| {
                        let union_var_name = quote::format_ident!("__union_field{}", idx);
                        quote! {
                            let #field_name = unsafe { #union_var_name.#u_field };
                        }
                    }).collect()
                };

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

    let union_field_names: Vec<_> = all_field_identifiers.iter()
        .map(|field_str| quote::format_ident!("__union_{}", field_str))
        .collect();
    
    let all_field_idents: Vec<_> = all_field_identifiers.iter()
        .map(|field_str| quote::format_ident!("{}", field_str))
        .collect();

    // Build the tuple repr type
    let tuple_repr = if all_field_identifiers.is_empty() {
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
                        #(#all_field_idents: #union_field_names.as_ref()),*
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
                        #(#all_field_idents: #union_field_names.as_mut()),*
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
                        #(#all_field_idents: core::slice::from_raw_parts(#union_field_names.as_ptr(), __soa_len)),*
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
                        #(#all_field_idents: core::slice::from_raw_parts_mut(#union_field_names.as_ptr(), __soa_len)),*
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
    fn test_named_fields() {
        let input: DeriveInput = syn::parse_quote! {
            enum Foo {
                A { x: u32, y: u32 },
                B { y: u32, z: u32 },
            }
        };

        let result = expand_data_enum(input).unwrap().to_string();

        // Should have unions named after fields, not positions
        assert!(result.contains("union FooFieldx"));
        assert!(result.contains("union FooFieldy"));
        assert!(result.contains("union FooFieldz"));

        // Should NOT have Field0, Field1
        assert!(!result.contains("FooFieldfield"));

        // Ref struct should have named fields
        assert!(result.contains("x : & 'soa FooFieldx"));
        assert!(result.contains("y : & 'soa FooFieldy"));
        assert!(result.contains("z : & 'soa FooFieldz"));
    }

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

        // For unnamed enums, unions should be named Fieldfield0, Fieldfield1, etc.
        assert!(result.contains("union TestEnumFieldfield0"));
        assert!(result.contains("undefined : ()"));
        assert!(result.contains("null : ()"));
        assert!(result.contains("boolean : bool"));
        assert!(result.contains("number : u32"));

        assert!(result.contains("struct TestEnumRef"));
        assert!(result.contains("discriminant : & 'soa TestEnumDiscriminant"));

        assert!(result.contains("struct TestEnumMut"));
        assert!(result.contains("struct TestEnumSlice"));
        assert!(result.contains("struct TestEnumSliceMut"));
    }
}