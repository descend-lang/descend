use std::collections::HashSet;

use proc_macro::TokenStream;
use quote::quote;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    Fields, FieldsNamed, Ident, ItemStruct, Token, Type, TypeReference,
};

// Copy paste from syn example
struct Args {
    vars: HashSet<Ident>,
}

impl Parse for Args {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        let vars = Punctuated::<Ident, Token![,]>::parse_terminated(input)?;
        Ok(Args {
            vars: vars.into_iter().collect(),
        })
    }
}

const IGNORE_ATTR_NAME: &str = "span_derive_ignore";

#[proc_macro_attribute]
pub fn span_derive(attr: TokenStream, input: TokenStream) -> TokenStream {
    // Parse input
    let input = parse_macro_input!(input as ItemStruct);
    let args = parse_macro_input!(attr as Args);
    if args.vars.is_empty() {
        panic!("Need at least one attribute in span_derive!");
    }
    // Get original data
    let original_name = &input.ident;
    let original_fields = match &input.fields {
        syn::Fields::Named(fields) => fields,
        _ => unreachable!(),
    };
    // Create new fields with helper attributes stripped
    let mut new_fields = original_fields.clone();
    for field in new_fields.named.iter_mut() {
        let mut tmp = vec![];
        std::mem::swap(&mut tmp, &mut field.attrs);
        tmp = tmp
            .into_iter()
            .filter(|attr| !attr.path.is_ident(IGNORE_ATTR_NAME))
            .collect::<Vec<_>>();
        std::mem::swap(&mut tmp, &mut field.attrs);
    }
    let mut original = input.clone();
    original.fields = Fields::Named(new_fields);
    // Create the helper
    let mut helper = input.clone();
    // Helper holds references => add generic lifetime parameter
    helper.generics = syn::parse_str("<'helper>").unwrap();
    // Only insert non-ignored fields into helper
    let mut helper_fields = FieldsNamed {
        brace_token: original_fields.brace_token.clone(),
        named: Punctuated::new(),
    };
    for mut field in original_fields.named.clone().into_iter() {
        let mut ignored = false;
        for attr in field.attrs.iter() {
            if attr.path.is_ident(IGNORE_ATTR_NAME) {
                ignored = true;
                break;
            }
        }
        if !ignored {
            // Create reference type with placeholder type
            let mut typ: TypeReference = syn::parse_str("&'helper i64").unwrap();
            typ.elem = Box::new(field.ty); // Put real type behind reference
            field.ty = Type::Reference(typ);
            helper_fields.named.push(field);
        }
    }
    helper.fields = Fields::Named(helper_fields);
    // Set helper name
    let helper_name = Ident::new(
        &format!("__{}SpanHelper", original_name.to_string()),
        input.ident.span(),
    );
    helper.ident = helper_name.clone();
    // Disable all macros for helper
    helper.attrs.clear();

    // List of field to use in return of into function
    let into_fields = helper
        .fields
        .iter()
        .map(|field| field.ident.as_ref().unwrap().clone())
        .collect::<Vec<_>>();

    // Guaranteed output
    let derive_args = args.vars.iter();
    let mut output = quote!(
        #original

        #[derive(#(#derive_args),*)]
        #helper

        impl<'a> From<&'a #original_name> for #helper_name<'a> {
            fn from(orig: &'a #original_name) -> Self {
                #helper_name {
                    #(#into_fields: &orig.#into_fields),*
                }
            }
        }
    );
    // Derive specific output
    for derive_arg in args.vars.iter() {
        match &derive_arg.to_string() as &str {
            "PartialEq" => {
                let impl_code = quote!(
                    impl ::core::cmp::PartialEq for #original_name {
                        fn eq(&self, other: &Self) -> bool {
                            let helper: #helper_name = self.into();
                            let helper_other: #helper_name = other.into();
                            helper == helper_other
                        }
                    }
                );
                output.extend(impl_code);
            }
            "Eq" => {
                let impl_code = quote!(
                    impl ::core::cmp::Eq for #original_name {}
                );
                output.extend(impl_code);
            }
            "Hash" => {
                let impl_code = quote!(
                    impl ::core::hash::Hash for #original_name {
                        fn hash<H: ::core::hash::Hasher>(&self, state: &mut H) {
                            let helper: #helper_name = self.into();
                            helper.hash(state);
                        }
                    }
                );
                output.extend(impl_code);
            }
            _ => panic!("span_derive not implemented for {}", derive_arg),
        }
    }

    TokenStream::from(output)
}
