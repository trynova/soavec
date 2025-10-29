// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use proc_macro2::TokenStream;
use syn::{Data, DeriveInput, spanned::Spanned};

use crate::{soa_enum::expand_data_enum, soa_struct::expand_data_struct};

pub fn expand_derive_soable(input: DeriveInput) -> syn::Result<TokenStream> {
    match &input.data {
        Data::Struct(_) => expand_data_struct(input),
        Data::Enum(_) => expand_data_enum(input),
        _ => Err(syn::Error::new(
            input.span(),
            "Soable can only be derived for structs",
        )),
    }
}
