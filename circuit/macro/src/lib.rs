use proc_macro::TokenStream;
use proc_macro_error2::{ResultExt as _, abort, proc_macro_error};
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{parse::Parse, punctuated::Punctuated};

#[proc_macro_error]
#[proc_macro]
pub fn circuit(input: TokenStream) -> TokenStream {
    let input = syn::parse::<Circuit>(input).expect_or_abort("failed to parse circuit");

    let constraints: Vec<_> = input
        .constraints
        .into_iter()
        .map(transform_constraint)
        .collect();

    quote! {{
        let mut __circuit = ::circuit::Circuit::new();
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
    /// Parsing [`syn::Expr`] is the easiest way to parse everything
    /// we need for the circuit.
    /// This will include operations we don't support, but that will be
    /// processed later in the macro implementation.
    constraints: Punctuated<syn::Expr, syn::Token![;]>,
}

impl Parse for Circuit {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let constraints = Punctuated::parse_terminated(input)?;
        Ok(Self { constraints })
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
                    ::circuit::Expression::Add {
                        left: ::std::boxed::Box::new(#left),
                        right: ::std::boxed::Box::new(#right),
                    }
                },
                syn::BinOp::Sub(_) => quote! {
                    ::circuit::Expression::Sub {
                        left: ::std::boxed::Box::new(#left),
                        right: ::std::boxed::Box::new(#right),
                    }
                },
                syn::BinOp::Mul(_) => quote! {
                    ::circuit::Expression::Mul {
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
                ::circuit::Expression::UnaryMinus(
                    ::std::boxed::Box::new(#expr),
                )
            }
        }
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(lit),
            ..
        }) => {
            // Won't compile on caller-site, but the error message looks good
            quote! {
                ::circuit::Expression::Const(#lit)
            }
        }
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Float(lit),
            ..
        }) => quote! {
            ::circuit::Expression::Const(#lit)
        },
        syn::Expr::Path(syn::ExprPath { path, .. }) => quote! {
            ::circuit::Expression::Var(stringify!(#path))
        },
        syn::Expr::Paren(syn::ExprParen { expr, .. }) => recursively_transform_expression(expr),
        _ => abort!(
            expr,
            "unsupported expression. Allowed literals, parentheses and operations: +, -, *, /."
        ),
    }
}
