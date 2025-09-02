mod soable;

use proc_macro::TokenStream;
use syn::{DeriveInput, parse_macro_input};

#[proc_macro_derive(SoAble)]
pub fn derive_soable(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    soable::expand_derive_soable(input).into()
}
