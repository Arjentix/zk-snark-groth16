//! Circuit normalization for R1CS form.

use std::ops::{Add, Neg, Sub};

use brackets_reveal::RevealedMul;
use circuit::{Circuit, Expr, ScopedVar, VarName};
use derive_more::Display;
use ff::PrimeField;
use indexmap::IndexSet;
use itertools::Itertools as _;
pub use left_right::{LeftExpr, RightExpr};

mod brackets_reveal;
mod left_right;
mod packing;
mod term;

/// Normalized circuit.
pub struct NormalizedCircuit<F: PrimeField> {
    pub vars: IndexSet<ScopedVar>,
    pub constraints: Vec<NormalizedConstraint<F>>,
}

impl<F: PrimeField + std::fmt::Display> std::fmt::Display for NormalizedCircuit<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.constraints
            .iter()
            .format_with("\n", |c, f| f(&format_args!("{c}")))
            .fmt(f)?;
        Ok(())
    }
}

impl<F: PrimeField> NormalizedCircuit<F> {
    /// Create a new normalized circuit from the given circuit.
    pub fn normalize(circuit: Circuit<F>) -> Self {
        let mut intermediate_constraints = Vec::new();

        let mut vars = circuit.vars;
        let mut new_var_names = IndexSet::new();

        let mut normalized_constraints = circuit
            .constraints
            .into_iter()
            .map(|mut constraint| {
                left_right::move_right_to_left(&mut constraint.left, &mut constraint.right);
                let left = brackets_reveal::reveal(constraint.left);
                let mut left = packing::pack_var_multiplications(
                    &vars,
                    left,
                    &mut intermediate_constraints,
                    &mut new_var_names,
                    &mut false,
                );
                term::sum_terms(&mut left);

                let mut right = RightExpr::zero();
                let left =
                    left_right::move_non_var_multiplications_to_right(left, &mut right, true);

                NormalizedConstraint { left, right }
            })
            .collect();

        vars.extend(new_var_names.into_iter().map(ScopedVar::Private));

        let constraints = {
            intermediate_constraints.append(&mut normalized_constraints);
            intermediate_constraints
        };

        Self { vars, constraints }
    }
}

/// Normalized constraint where left is a multiplication of variables and right is a normalized
/// expression.
#[derive(Debug, Display)]
#[display("{left} == {right}")]
pub struct NormalizedConstraint<F: PrimeField> {
    pub left: LeftExpr<F>,
    pub right: RightExpr<F>,
}

/// Like `()`, but implements [`std::fmt::Display`]
#[derive(Debug, Display, PartialEq, Eq)]
#[display("")]
pub struct Nothing;

/// Like `Option<VarName>`, but implements [`std::fmt::Display`]
#[derive(Debug, Display, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum MaybeVarName {
    #[display("")]
    None,
    VarName(VarName),
}

impl From<Option<VarName>> for MaybeVarName {
    fn from(value: Option<VarName>) -> Self {
        match value {
            Some(var_name) => MaybeVarName::VarName(var_name),
            None => MaybeVarName::None,
        }
    }
}

impl From<MaybeVarName> for Option<VarName> {
    fn from(value: MaybeVarName) -> Self {
        match value {
            MaybeVarName::None => None,
            MaybeVarName::VarName(var_name) => Some(var_name),
        }
    }
}

pub type TwoVarMul<F> = VarMul<F, VarName>;
type MaybeTwoVarMul<F> = VarMul<F, MaybeVarName>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct VarMul<F: PrimeField, R> {
    scalar: F,
    left: VarName,
    right: R,
}

impl<F: PrimeField> VarMul<F, MaybeVarName> {
    fn sorted(scalar: F, left: VarName, right: MaybeVarName) -> Self {
        let term = term::Term::sorted(left, right);
        let (left, right) = term.into_raw_parts();
        Self {
            scalar,
            left,
            right,
        }
    }
}

impl<F: PrimeField> VarMul<F, VarName> {
    fn sorted(scalar: F, left: VarName, right: VarName) -> Self {
        if left > right {
            return Self {
                scalar,
                left: right,
                right: left,
            };
        }

        Self {
            scalar,
            left,
            right,
        }
    }
}

impl<F: PrimeField, R> Neg for VarMul<F, R> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            scalar: -self.scalar,
            left: self.left,
            right: self.right,
        }
    }
}

impl<F, R> VarMul<F, R>
where
    F: PrimeField,
    R: Into<Option<VarName>> + From<Option<VarName>>,
{
    fn simplified(self) -> MulGenericExpr<F, Self> {
        let right = self.right.into();

        match (self.left, right, self.scalar) {
            (_, _, zero) if zero == F::ZERO => MulGenericExpr::zero(),
            (left, None, one) if one == F::ONE => MulGenericExpr::Var(left),
            (left, None, minus_one) if minus_one == -F::ONE => MulGenericExpr::UnaryMinus(left),
            (left, right, scalar) => MulGenericExpr::Mul(Self {
                scalar,
                left,
                right: right.into(),
            }),
        }
    }
}

impl<F: PrimeField + std::fmt::Display, R: std::fmt::Display> std::fmt::Display for VarMul<F, R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let right = self.right.to_string();
        if right.is_empty() {
            write!(f, "{} * {}", self.scalar, self.left)
        } else {
            write!(f, "{} * {} * {}", self.scalar, self.left, self.right)
        }
    }
}

/// Multiplication agnostic expression where unary minus is a leaf.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum MulGenericExpr<F: PrimeField, M> {
    Add {
        left: Box<MulGenericExpr<F, M>>,
        right: Box<MulGenericExpr<F, M>>,
    },
    Sub {
        left: Box<MulGenericExpr<F, M>>,
        right: Box<MulGenericExpr<F, M>>,
    },
    Mul(M),
    UnaryMinus(VarName),
    Const(F),
    Var(VarName),
}

impl<F: PrimeField, M> MulGenericExpr<F, M> {
    /// Construct expression consisting of one zero constant.
    fn zero() -> Self {
        Self::Const(F::ZERO)
    }

    /// Check if the expression is a zero constant.
    fn is_zero(&self) -> bool {
        matches!(self, Self::Const(c) if *c == F::ZERO)
    }

    /// Take the expression, replacing it with a zero constant.
    fn take(&mut self) -> Self {
        std::mem::replace(self, Self::zero())
    }
}

impl<F: PrimeField, M: Neg<Output = M>> Neg for MulGenericExpr<F, M> {
    type Output = Self;

    /// Multiply expression by `-1` but without packing it into Mul or UnaryMinus operation if
    /// possible.
    fn neg(self) -> Self::Output {
        match self {
            Self::Add { left, right } => Self::Sub {
                left: Box::new(left.neg()),
                right,
            },
            Self::Sub { left, right } => Self::Add {
                left: Box::new(left.neg()),
                right,
            },
            Self::Mul(mul) => Self::Mul(mul.neg()),
            Self::UnaryMinus(var) => Self::Var(var),
            Self::Const(c) => Self::Const(-c),
            Self::Var(var) => Self::UnaryMinus(var),
        }
    }
}

impl<F: PrimeField, M> Add for MulGenericExpr<F, M> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if self.is_zero() {
            return rhs;
        }
        if rhs.is_zero() {
            return self;
        }

        Self::Add {
            left: Box::new(self),
            right: Box::new(rhs),
        }
    }
}

impl<F: PrimeField, M: Neg<Output = M>> Sub for MulGenericExpr<F, M> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        if self.is_zero() {
            return -rhs;
        }
        if rhs.is_zero() {
            return self;
        }

        Self::Sub {
            left: Box::new(self),
            right: Box::new(rhs),
        }
    }
}

impl<F: PrimeField + std::fmt::Display, M: std::fmt::Display> std::fmt::Display
    for MulGenericExpr<F, M>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add { left, right } => write!(f, "({left} + {right})"),
            Self::Sub { left, right } => write!(f, "({left} - {right})"),
            Self::Mul(mul) => {
                write!(f, "{mul}")
            }
            Self::UnaryMinus(expr) => write!(f, "-{expr}"),
            Self::Const(c) => write!(f, "{c}"),
            Self::Var(name) => write!(f, "{name}"),
        }
    }
}

impl<F: PrimeField> From<MulGenericExpr<F, RevealedMul<F>>> for Expr<F> {
    fn from(value: MulGenericExpr<F, RevealedMul<F>>) -> Self {
        match value {
            MulGenericExpr::Add { left, right } => Expr::Add {
                left: Box::new((*left).into()),
                right: Box::new((*right).into()),
            },
            MulGenericExpr::Sub { left, right } => Expr::Sub {
                left: Box::new((*left).into()),
                right: Box::new((*right).into()),
            },
            MulGenericExpr::Mul(RevealedMul { left, right }) => Expr::Mul {
                left: Box::new((*left).into()),
                right: Box::new((*right).into()),
            },
            MulGenericExpr::UnaryMinus(var_name) => Expr::UnaryMinus(Box::new(Expr::Var(var_name))),
            MulGenericExpr::Const(c) => Expr::Const(c),
            MulGenericExpr::Var(var_name) => Expr::Var(var_name),
        }
    }
}
