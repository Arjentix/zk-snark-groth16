//! Arithmetic circuit utilities.

use std::{borrow::Cow, collections::HashSet};

pub use circuit_macro::circuit;
use derive_more::Display;
use itertools::Itertools as _;

pub type VarName = Cow<'static, str>;

/// Arithmetic circuit.
#[derive(Default, Debug)]
pub struct Circuit {
    pub vars: HashSet<VarName>,
    pub constraints: Vec<Constraint>,
}

impl Circuit {
    /// Create a new circuit.
    pub fn new() -> Self {
        Self {
            vars: HashSet::new(),
            constraints: Vec::new(),
        }
    }
}

impl std::fmt::Display for Circuit {
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
pub struct Constraint {
    pub left: Expr,
    pub right: Expr,
}

/// Expression in the circuit.
/// Note that division is not supported.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Add { left: Box<Expr>, right: Box<Expr> },
    Sub { left: Box<Expr>, right: Box<Expr> },
    Mul { left: Box<Expr>, right: Box<Expr> },
    UnaryMinus(Box<Expr>),
    Const(f64),
    Var(VarName),
}

impl std::fmt::Display for Expr {
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
