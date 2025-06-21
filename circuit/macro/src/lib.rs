use proc_macro::TokenStream;
use proc_macro_error2::{ResultExt as _, abort, proc_macro_error};
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{parse::Parse, punctuated::Punctuated};

#[proc_macro_error]
#[proc_macro]
pub fn circuit(input: TokenStream) -> TokenStream {
    let input = syn::parse::<Circuit>(input).expect_or_abort("failed to parse circuit");

    let var_definitions: Vec<_> = input
        .vars
        .iter()
        .map(|var| {
            let name = &var.name;
            quote! {
                let #name = ::std::borrow::Cow::Borrowed(stringify!(#name));
            }
        })
        .collect();

    let constraints: Vec<_> = input
        .constraints
        .into_iter()
        .map(transform_constraint)
        .collect();

    let mut prev_vis_private = false;
    let vars = input.vars.into_iter().map(|var| {
        let name = var.name;

        // Here we reconstruct variables from string values and not cloning their definitions,
        // so that caller-code get warnings when there are unused variables.
        match var.vis {
            syn::Visibility::Public(public) => {
                if prev_vis_private {
                    abort!(public, "public variable cannot follow private variable");
                }
                quote! {
                    ::circuit::ScopedVar::Public(::std::borrow::Cow::Borrowed(stringify!(#name)))
                }
            }
            syn::Visibility::Inherited => {
                prev_vis_private = true;
                quote! {
                    ::circuit::ScopedVar::Private(::std::borrow::Cow::Borrowed(stringify!(#name)))
                }
            }
            syn::Visibility::Restricted(restricted) => {
                abort!(
                    restricted,
                    "restricted visibility is not supported in circuits"
                );
            }
        }
    });

    quote! {{
        let mut __circuit = ::circuit::Circuit::default();

        #(#var_definitions)*

        __circuit.vars.extend([#(#vars),*]);

        #(
            __circuit.constraints.push(
                #constraints
            );
        )*

        __circuit
    }}
    .into()
}

#[derive(Debug)]
struct Circuit {
    _or1_token: syn::Token![|],
    vars: Punctuated<VarDefinition, syn::Token![,]>,
    _or2_token: syn::Token![|],
    _brace_token: syn::token::Brace,
    /// Parsing [`syn::Expr`] is the easiest way to parse everything
    /// we need for the circuit.
    /// This will include operations we don't support, but that will be
    /// processed later in the macro implementation.
    constraints: Punctuated<syn::Expr, syn::Token![;]>,
}

impl Parse for Circuit {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let content;
        Ok(Self {
            _or1_token: input.parse()?,
            vars: Punctuated::parse_separated_nonempty(input)?,
            _or2_token: input.parse()?,
            _brace_token: syn::braced!(content in input),
            constraints: content.parse_terminated(syn::Expr::parse, syn::Token![;])?,
        })
    }
}

#[derive(Debug)]
struct VarDefinition {
    vis: syn::Visibility,
    name: syn::Ident,
}

impl Parse for VarDefinition {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(Self {
            vis: input.parse()?,
            name: input.parse()?,
        })
    }
}

fn transform_constraint(constraint: syn::Expr) -> TokenStream2 {
    let syn::Expr::Binary(syn::ExprBinary {
        op: syn::BinOp::Eq(_),
        left,
        right,
        ..
    }) = constraint
    else {
        abort!(constraint, "expected `==`")
    };

    let left = recursively_transform_expression(left);
    let right = recursively_transform_expression(right);

    quote! {
        ::circuit::Constraint {
            left: #left,
            right: #right,
        }
    }
}

fn recursively_transform_expression(expr: Box<syn::Expr>) -> TokenStream2 {
    match *expr {
        syn::Expr::Binary(syn::ExprBinary {
            op, left, right, ..
        }) => {
            let left = recursively_transform_expression(left);
            let right = recursively_transform_expression(right);

            match op {
                syn::BinOp::Add(_) => quote! {
                    ::circuit::Expr::Add {
                        left: ::std::boxed::Box::new(#left),
                        right: ::std::boxed::Box::new(#right),
                    }
                },
                syn::BinOp::Sub(_) => quote! {
                    ::circuit::Expr::Sub {
                        left: ::std::boxed::Box::new(#left),
                        right: ::std::boxed::Box::new(#right),
                    }
                },
                syn::BinOp::Mul(_) => quote! {
                    ::circuit::Expr::Mul {
                        left: ::std::boxed::Box::new(#left),
                        right: ::std::boxed::Box::new(#right),
                    }
                },
                _ => abort!(op, "unsupported operator"),
            }
        }
        syn::Expr::Unary(syn::ExprUnary {
            op: syn::UnOp::Neg(_),
            expr,
            ..
        }) => {
            let expr = recursively_transform_expression(expr);
            quote! {
                ::circuit::Expr::UnaryMinus(
                    ::std::boxed::Box::new(#expr),
                )
            }
        }
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => {
            quote! {
                ::circuit::Expr::Const(#lit.into())
            }
        }
        syn::Expr::Path(syn::ExprPath { path, .. }) => {
            quote! {
                ::circuit::Expr::Var(#path.clone())
            }
        }
        syn::Expr::Paren(syn::ExprParen { expr, .. }) => recursively_transform_expression(expr),
        _ => {
            println!("expr: {expr:?}");
            abort!(
                expr,
                "unsupported expression. Allowed literals, parentheses and operations: +, -, *, /."
            )
        }
    }
}
