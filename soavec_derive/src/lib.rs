// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

mod soable;

use proc_macro::TokenStream;
use syn::{DeriveInput, parse_macro_input};

#[proc_macro_derive(SoAble)]
pub fn derive_soable(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    soable::expand_derive_soable(input)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}
