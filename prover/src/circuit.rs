//! Arithmetic circuit utilities.

/// Arithmetic circuit.
#[derive(Debug, Default)]
pub struct Circuit {
    constraints: Vec<Constraint>,
}

impl Circuit {
    /// Create a new circuit.
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
        }
    }

    /// Add a constraint to the circuit.
    pub fn add_constraint(mut self, left: Expression, right: Expression) -> Self {
        self.constraints.push(Constraint { left, right });
        self
    }
}

#[derive(Debug)]
struct Constraint {
    left: Expression,
    right: Expression,
}

#[derive(Debug)]
pub enum Expression {
    Plus {
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Minus {
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Multiply {
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Divide {
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Constant(f64),
    Variable(&'static str),
    UnaryMinusVariable(&'static str),
}
