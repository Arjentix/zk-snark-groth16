//! Arithmetic circuit utilities.

use std::{borrow::Cow, collections::HashSet};

pub use circuit_macro::circuit;
use derive_more::Display;
use ff::PrimeField;
use itertools::Itertools as _;

pub type VarName = Cow<'static, str>;

/// Arithmetic circuit.
#[derive(Default, Debug)]
pub struct Circuit<F: PrimeField> {
    pub vars: HashSet<VarName>,
    pub constraints: Vec<Constraint<F>>,
}

impl<F: PrimeField> Circuit<F> {
    /// Create a new circuit.
    pub fn new() -> Self {
        Self {
            vars: HashSet::new(),
            constraints: Vec::new(),
        }
    }
}

impl<F: PrimeField + std::fmt::Display> std::fmt::Display for Circuit<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.constraints
            .iter()
            .format_with("\n", |c, f| f(&format_args!("{c}")))
            .fmt(f)?;
        Ok(())
    }
}

#[derive(Debug, Display)]
#[display("{left} == {right}")]
pub struct Constraint<F: PrimeField> {
    pub left: Expr<F>,
    pub right: Expr<F>,
}

/// Expression in the circuit.
/// Note that division is not supported.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr<F: PrimeField> {
    Add {
        left: Box<Expr<F>>,
        right: Box<Expr<F>>,
    },
    Sub {
        left: Box<Expr<F>>,
        right: Box<Expr<F>>,
    },
    Mul {
        left: Box<Expr<F>>,
        right: Box<Expr<F>>,
    },
    UnaryMinus(Box<Expr<F>>),
    Const(F),
    Var(VarName),
}

impl<F: PrimeField + std::fmt::Display> std::fmt::Display for Expr<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Add { left, right } => write!(f, "({left} + {right})"),
            Expr::Sub { left, right } => write!(f, "({left} - {right})"),
            Expr::Mul { left, right } => write!(f, "({left} * {right})"),
            Expr::UnaryMinus(expr) => write!(f, "-{expr}"),
            Expr::Const(value) => write!(f, "{value}"),
            Expr::Var(name) => write!(f, "{name}"),
        }
    }
}
