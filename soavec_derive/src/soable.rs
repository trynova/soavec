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

    let impl_block = quote! {
        unsafe impl #generics soavec::SoAble for #struct_name #generics {
            type TupleRepr = (#(#field_types),*);
            type Ref<'a> = (#(&'a #field_types),*) where Self: 'a;
            type Mut<'a> = (#(&'a mut #field_types),*) where Self: 'a;
            type Slice<'a> = (#(&'a [#field_types]),*) where Self: 'a;
            type SliceMut<'a> = (#(&'a mut [#field_types]),*) where Self: 'a;

            fn into_tuple(value: Self) -> Self::TupleRepr {
                let Self { #(#field_names),* } = value;
                (#(#field_names),*)
            }

            fn from_tuple(value: Self::TupleRepr) -> Self {
                let (#(#field_names),*) = value;
                Self { #(#field_names),* }
            }

            fn as_ref<'a>(
                _: std::marker::PhantomData<&'a Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
            ) -> Self::Ref<'a> {
                let (#(#field_names),*) = value;
                unsafe {
                    (#(#field_names.as_ref()),*)
                }
            }

            fn as_mut<'a>(
                _: std::marker::PhantomData<&'a mut Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
            ) -> Self::Mut<'a> {
                let (#(mut #field_names),*) = value;
                unsafe {
                    (#(#field_names.as_mut()),*)
                }
            }

            fn as_slice<'a>(
                _: std::marker::PhantomData<&'a Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
                len: u32,
            ) -> Self::Slice<'a> {
                let len = len as usize;
                let (#(#field_names),*) = value;
                unsafe {
                    (
                        #(core::slice::from_raw_parts(#field_names.as_ptr(), len)),*
                    )
                }
            }

            fn as_mut_slice<'a>(
                _: std::marker::PhantomData<&'a mut Self>,
                value: <Self::TupleRepr as soavec::SoATuple>::Pointers,
                len: u32,
            ) -> Self::SliceMut<'a> {
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
