//! Arithmetic circuit utilities.

pub use circuit_macro::circuit;

/// Arithmetic circuit.
#[derive(Debug, Default)]
pub struct Circuit {
    pub constraints: Vec<Constraint>,
}

impl Circuit {
    /// Create a new circuit.
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
        }
    }
}

#[derive(Debug)]
pub struct Constraint {
    pub left: Expression,
    pub right: Expression,
}

#[derive(Debug)]
pub enum Expression {
    Add {
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Sub {
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Mul {
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Div {
        left: Box<Expression>,
        right: Box<Expression>,
    },
    UnaryMinus(Box<Expression>),
    Const(f64),
    Var(&'static str),
}
