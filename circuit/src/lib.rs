//! Arithmetic circuit utilities.

use std::borrow::Cow;

pub use circuit_macro::circuit;
use derive_more::Display;
use ff::PrimeField;
use indexmap::IndexSet;
use itertools::Itertools as _;

pub type VarName = Cow<'static, str>;

/// Arithmetic circuit.
#[derive(Default, Debug)]
pub struct Circuit<F: PrimeField> {
    /// Variables where all public variables go first.
    pub vars: IndexSet<ScopedVar>,
    pub constraints: Vec<Constraint<F>>,
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

/// Public or private variable in the circuit.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum ScopedVar {
    /// Public variable which won't be hidden in the proof.
    Public(VarName),
    /// Private variable which will be hidden in the proof.
    Private(VarName),
}

impl ScopedVar {
    /// Returns the name of the variable.
    pub fn name(&self) -> &VarName {
        match self {
            ScopedVar::Public(name) | ScopedVar::Private(name) => name,
        }
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
            Self::Add { left, right } => write!(f, "({left} + {right})"),
            Self::Sub { left, right } => write!(f, "({left} - {right})"),
            Self::Mul { left, right } => write!(f, "({left} * {right})"),
            Self::UnaryMinus(expr) => write!(f, "-{expr}"),
            Self::Const(value) => write!(f, "{value}"),
            Self::Var(name) => write!(f, "{name}"),
        }
    }
}
