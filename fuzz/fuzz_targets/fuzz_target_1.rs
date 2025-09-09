#![no_main]
use libfuzzer_sys::fuzz_target;
use arbitrary::Arbitrary;
use quote::{quote, ToTokens};
use syn::{self, DeriveInput};
use std::process::Command;
use std::fs;
use std::io::Write;

#[derive(Arbitrary, Debug)]
struct FuzzStruct {
    name: String,
    lifetimes: Vec<String>,
    type_params: Vec<String>, 
    fields: Vec<FuzzField>,
    visibility: FuzzVisibility,
}

#[derive(Arbitrary, Debug)]
struct FuzzField {
    name: String,
    field_type: FuzzType,
}

#[derive(Arbitrary, Debug)]
enum FuzzType {
    U32,
    U64,
    I32,
    String,
    Reference { lifetime: usize, inner: Box<FuzzType> },
    Generic { param: usize },
}

#[derive(Arbitrary, Debug)]
enum FuzzVisibility {
    Private,
    Public,
}

impl FuzzStruct {
    fn to_derive_input(&self) -> Option<DeriveInput> {
        // Ensure we have at least 2 fields (SoAble requirement)
        if self.fields.len() < 2 {
            return None;
        }
        
        // Build struct name
        let struct_name = format!("Fuzz{}", self.name.chars().take(10).collect::<String>())
            .replace(|c: char| !c.is_alphanumeric(), "");
        if struct_name.is_empty() {
            return None;
        }

        let mut struct_def = "#[derive(soavec_derive::SoAble)]\n".to_string();

        // Create the struct as a string and parse it
        let vis = match self.visibility {
            FuzzVisibility::Public => "pub struct ".to_string(),
            FuzzVisibility::Private => "struct ".to_string(),
        };

        struct_def.push_str(&vis);
        
        struct_def.push_str(&struct_name);
        
        // Add generics
        if !self.lifetimes.is_empty() || !self.type_params.is_empty() {
            struct_def.push('<');
            
            // Add lifetimes
            for (i, _lt) in self.lifetimes.iter().enumerate() {
                if i > 0 { struct_def.push_str(", "); }
                struct_def.push('\'');
                struct_def.push_str(&format!("lt{}", i));
            }
            
            // Add type params
            for (i, _tp) in self.type_params.iter().enumerate() {
                if !self.lifetimes.is_empty() || i > 0 { struct_def.push_str(", "); }
                struct_def.push_str(&format!("T{}", i));
            }
            
            struct_def.push('>');
        }
        
        struct_def.push_str(" {\n");
        
        // Add fields
        for field in &self.fields {
            let field_name = format!("field_{}", field.name.chars().take(10).collect::<String>())
                .replace(|c: char| !c.is_alphanumeric(), "");
            if field_name.is_empty() { continue; }
            
            let field_type = field.field_type.to_type_string(&self.lifetimes, &self.type_params);
            struct_def.push_str(&format!("    pub {}: {},\n", field_name, field_type));
        }
        
        struct_def.push('}');
        
        // Try to parse the generated struct
        syn::parse_str(&struct_def).ok()
    }
}

impl FuzzType {
    fn to_type_string(&self, lifetimes: &[String], type_params: &[String]) -> String {
        match self {
            FuzzType::U32 => "u32".to_string(),
            FuzzType::U64 => "u64".to_string(),
            FuzzType::I32 => "i32".to_string(),
            FuzzType::String => "String".to_string(),
            FuzzType::Reference { lifetime, inner } => {
                let lt = if lifetimes.is_empty() {
                    "'static".to_string()
                } else {
                    format!("'lt{}", lifetime % lifetimes.len())
                };
                format!("&{} {}", lt, inner.to_type_string(lifetimes, type_params))
            },
            FuzzType::Generic { param } => {
                if type_params.is_empty() {
                    "u32".to_string() // fallback
                } else {
                    format!("T{}", param % type_params.len())
                }
            }
        }
    }
}

fuzz_target!(|input: FuzzStruct| {
    if let Some(derive_input) = input.to_derive_input() {
        // Just test that we can generate a valid struct and parse it
        // This catches parsing errors and malformed struct definitions
        
        // Test that the generated struct has the expected structure
        if let syn::Data::Struct(data_struct) = &derive_input.data {
            if let syn::Fields::Named(fields) = &data_struct.fields {
                // Basic validation - SoAble requires at least 2 fields
                assert!(fields.named.len() >= 2, "Generated struct should have at least 2 fields");
                
                // Just validate the struct is good
                // (removed debug counter due to static mut warnings)
                
                // Verify field names are valid identifiers
                for field in &fields.named {
                    if let Some(ident) = &field.ident {
                        assert!(!ident.to_string().is_empty(), "Field name should not be empty");
                    }
                }
                
                // Test struct can be converted back to string and parsed
                let struct_str = quote! { #derive_input }.to_string();
                match syn::parse_str::<DeriveInput>(&struct_str) {
                    Err(e) => panic!("Generated struct is not valid Rust: {}\nError: {}", struct_str, e),
                    Ok(s) => println!("{}", s.into_token_stream().to_string())
                }
            }
        }
    }
});
