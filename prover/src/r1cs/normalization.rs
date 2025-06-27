//! Circuit normalization for R1CS form.

use std::{
    collections::BTreeMap,
    hash::{BuildHasher as _, Hash as _, Hasher as _},
};

use circuit::{Circuit, Expr, ScopedVar, VarName};
use derive_more::Display;
use ff::PrimeField;
use indexmap::IndexSet;
use itertools::Itertools as _;
use sorted_vec::SortedVec;

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

/// Normalized constraint where each constraint contains at leas one vars multiplication.
#[derive(Debug, Display)]
#[display("{left} == {right}")]
pub struct NormalizedConstraint<F: PrimeField> {
    pub left: NormalizedExpr<F>,
    pub right: NormalizedExpr<F>,
}

/// Normalized expression where multiplication and unary minus are leafs.
#[derive(Debug, PartialEq, Eq)]
pub enum NormalizedExpr<F: PrimeField> {
    Add {
        left: Box<NormalizedExpr<F>>,
        right: Box<NormalizedExpr<F>>,
    },
    Sub {
        left: Box<NormalizedExpr<F>>,
        right: Box<NormalizedExpr<F>>,
    },
    Mul {
        scalar: F,
        term: SortedTerm,
    },
    UnaryMinus(VarName),
    Const(F),
    Var(VarName),
}

impl<F: PrimeField> NormalizedExpr<F> {
    /// Construct expression consisting of one zero constant.
    fn zero() -> Self {
        Self::Const(F::ZERO)
    }

    /// Check if the expression is a zero constant.
    fn is_zero(&self) -> bool {
        matches!(self, NormalizedExpr::Const(c) if *c == F::ZERO)
    }

    /// Take the expression, replacing it with a zero constant.
    fn take(&mut self) -> Self {
        std::mem::replace(self, Self::zero())
    }

    /// Multiply expression by `-1` but without packing it into Mul or UnaryMinus operation.
    fn negate(self) -> Self {
        match self {
            Self::Add { left, right } => Self::Sub {
                left: Box::new(left.negate()),
                right,
            },
            Self::Sub { left, right } => Self::Add {
                left: Box::new(left.negate()),
                right,
            },
            Self::Mul { scalar, term } => Self::Mul {
                scalar: -scalar,
                term,
            },
            Self::UnaryMinus(var) => Self::Var(var),
            Self::Const(c) => Self::Const(-c),
            Self::Var(var) => Self::UnaryMinus(var),
        }
    }
}

impl<F: PrimeField + std::fmt::Display> std::fmt::Display for NormalizedExpr<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add { left, right } => write!(f, "({left} + {right})"),
            Self::Sub { left, right } => write!(f, "({left} - {right})"),
            Self::Mul { scalar, term } => {
                let scalar_str = if *scalar == F::ONE {
                    String::new()
                } else {
                    format!("{scalar} * ")
                };

                write!(f, "{scalar_str}{term}")
            }
            Self::UnaryMinus(expr) => write!(f, "-{expr}"),
            Self::Const(value) => write!(f, "{value}"),
            Self::Var(name) => write!(f, "{name}"),
        }
    }
}

impl std::fmt::Display for SortedTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(right) = &self.right {
            write!(f, "{} * {}", self.left, right)
        } else {
            write!(f, "{}", self.left)
        }
    }
}

impl<F: PrimeField> From<Circuit<F>> for NormalizedCircuit<F> {
    fn from(circuit: Circuit<F>) -> Self {
        let mut intermediate_constraints = Vec::new();

        let mut vars = circuit.vars;
        let mut new_var_names = IndexSet::new();

        let mut normalized_constraints = circuit
            .constraints
            .into_iter()
            .map(|mut constraint| {
                move_right_to_left(&mut constraint.left, &mut constraint.right);
                reveal_brackets(&mut constraint.left);
                let mut left = pack_var_multiplications(
                    &vars,
                    constraint.left,
                    &mut intermediate_constraints,
                    &mut new_var_names,
                    &mut false,
                );
                sum_terms(&mut left);

                let mut right = NormalizedExpr::zero();
                move_non_var_multiplications_to_right(&mut left, &mut right, true);

                NormalizedConstraint { left, right }
            })
            .collect();

        vars.extend(new_var_names.into_iter().map(ScopedVar::Private));

        let constraints = {
            intermediate_constraints.append(&mut normalized_constraints);
            intermediate_constraints
        };

        NormalizedCircuit { vars, constraints }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SortedTerm {
    left: VarName,
    right: Option<VarName>,
}

impl SortedTerm {
    fn new(first: VarName, mut second: Option<VarName>) -> Self {
        if let Some(second) = second.take_if(|s| first > *s) {
            return Self {
                left: second.clone(),
                right: Some(first),
            };
        }

        Self {
            left: first,
            right: second,
        }
    }
}

fn move_right_to_left<F: PrimeField>(left: &mut Expr<F>, right: &mut Expr<F>) {
    let l = std::mem::replace(left, Expr::Const(F::ZERO));
    let r = std::mem::replace(right, Expr::Const(F::ZERO));
    *left = Expr::Sub {
        left: Box::new(l),
        right: Box::new(r),
    };
}

fn reveal_brackets<F: PrimeField>(expr: &mut Expr<F>) {
    match expr {
        Expr::Add { left, right } => {
            reveal_brackets(left);
            reveal_brackets(right);
        }
        Expr::Sub { left, right } => {
            reveal_brackets(left);
            reveal_brackets(right);

            if let Expr::UnaryMinus(sub_expr) = &**right {
                // Replace `x - (-y)` with `x + y`
                *expr = Expr::Add {
                    left: left.clone(),
                    right: sub_expr.clone(),
                };
            }
        }
        Expr::Mul { left, right } => {
            reveal_brackets(left);
            reveal_brackets(right);

            match (&**left, &**right) {
                (
                    Expr::Add {
                        left: add_left,
                        right: add_right,
                    },
                    _,
                ) => {
                    // Replace `(x + y) * z` with `x * z + y * z`
                    *expr = Expr::Add {
                        left: Box::new(Expr::Mul {
                            left: add_left.clone(),
                            right: right.clone(),
                        }),
                        right: Box::new(Expr::Mul {
                            left: add_right.clone(),
                            right: right.clone(),
                        }),
                    };
                    reveal_brackets(expr);
                }
                (
                    Expr::Sub {
                        left: sub_left,
                        right: sub_right,
                    },
                    _,
                ) => {
                    // Replace `(x - y) * z` with `x * z - y * z`
                    *expr = Expr::Sub {
                        left: Box::new(Expr::Mul {
                            left: sub_left.clone(),
                            right: right.clone(),
                        }),
                        right: Box::new(Expr::Mul {
                            left: sub_right.clone(),
                            right: right.clone(),
                        }),
                    };
                    reveal_brackets(expr);
                }
                (
                    _,
                    Expr::Add {
                        left: add_left,
                        right: add_right,
                    },
                ) => {
                    // Replace `x * (y + z)` with `x * y + x * z`
                    *expr = Expr::Add {
                        left: Box::new(Expr::Mul {
                            left: left.clone(),
                            right: add_left.clone(),
                        }),
                        right: Box::new(Expr::Mul {
                            left: left.clone(),
                            right: add_right.clone(),
                        }),
                    };
                    reveal_brackets(expr);
                }
                (
                    _,
                    Expr::Sub {
                        left: sub_left,
                        right: sub_right,
                    },
                ) => {
                    // Replace `x * (y - z)` with `x * y - x * z`
                    *expr = Expr::Sub {
                        left: Box::new(Expr::Mul {
                            left: left.clone(),
                            right: sub_left.clone(),
                        }),
                        right: Box::new(Expr::Mul {
                            left: left.clone(),
                            right: sub_right.clone(),
                        }),
                    };
                    reveal_brackets(expr);
                }
                (Expr::UnaryMinus(left), Expr::UnaryMinus(right)) => {
                    // Replace `(-x) * (-y)` with `x * y`
                    *expr = Expr::Mul {
                        left: left.clone(),
                        right: right.clone(),
                    };
                }
                _ => {}
            }
        }
        Expr::UnaryMinus(sub_expr) => {
            reveal_brackets(sub_expr);

            match &**sub_expr {
                Expr::Add { left, right } => {
                    // Replace `-(x + y)` with `(-x) - y`
                    *expr = Expr::Sub {
                        left: Box::new(Expr::UnaryMinus(left.clone())),
                        right: right.clone(),
                    };
                }
                Expr::Sub { left, right } => {
                    // Replace `-(x - y)` with `-x + y`
                    *expr = Expr::Add {
                        left: Box::new(Expr::UnaryMinus(left.clone())),
                        right: right.clone(),
                    };
                }
                Expr::Mul { left, right } => {
                    // Replace `-(x * y)` with `-x * y`
                    *expr = Expr::Mul {
                        left: Box::new(Expr::UnaryMinus(left.clone())),
                        right: right.clone(),
                    };
                }
                Expr::UnaryMinus(sub_sub_expr) => {
                    // Replace `-(-x)` with `x`
                    *expr = *sub_sub_expr.clone();
                }
                Expr::Const(c) => {
                    // Replace `-(c)` with `-c`
                    *expr = Expr::Const(-(*c));
                }
                Expr::Var(_) => {}
            }
        }
        Expr::Const(_) | Expr::Var(_) => {}
    }
}

/// Packs each variable multiplication into a new variable and places it as constraint.
///
/// # Example
///
/// ```text
///              [ v = a*b
/// a*b*c = 0 => |
///              [ v*c = 0
/// ```
fn pack_var_multiplications<F: PrimeField>(
    var_names: &IndexSet<ScopedVar>,
    expr: Expr<F>,
    new_constraints: &mut Vec<NormalizedConstraint<F>>,
    new_var_names: &mut IndexSet<VarName>,
    var_multiplication_set: &mut bool,
) -> NormalizedExpr<F> {
    match expr {
        Expr::Add { left, right } => {
            let left_normalized = pack_var_multiplications(
                var_names,
                *left,
                new_constraints,
                new_var_names,
                var_multiplication_set,
            );
            let right_normalized = pack_var_multiplications(
                var_names,
                *right,
                new_constraints,
                new_var_names,
                var_multiplication_set,
            );

            NormalizedExpr::Add {
                left: Box::new(left_normalized),
                right: Box::new(right_normalized),
            }
        }
        Expr::Sub { left, right } => {
            let left_normalized = pack_var_multiplications(
                var_names,
                *left,
                new_constraints,
                new_var_names,
                var_multiplication_set,
            );
            let right_normalized = pack_var_multiplications(
                var_names,
                *right,
                new_constraints,
                new_var_names,
                var_multiplication_set,
            );

            NormalizedExpr::Sub {
                left: Box::new(left_normalized),
                right: Box::new(right_normalized),
            }
        }
        Expr::Mul { left, right } => {
            let mut found_vars = SortedVec::new();
            let mut const_factor = F::ONE;
            find_factors(&left, &mut found_vars, &mut const_factor);
            find_factors(&right, &mut found_vars, &mut const_factor);

            let vars = loop {
                match found_vars.len() {
                    0 => {
                        break None;
                    }
                    1 => {
                        break Some(SortedTerm::new(
                            found_vars
                                .pop()
                                .unwrap_or_else(|| unreachable!("checked length = 1")),
                            None,
                        ));
                    }
                    2 if !*var_multiplication_set => {
                        *var_multiplication_set = true;
                        break Some(SortedTerm::new(
                            found_vars
                                .pop()
                                .unwrap_or_else(|| unreachable!("checked length = 2")),
                            Some(
                                found_vars
                                    .pop()
                                    .unwrap_or_else(|| unreachable!("checked length = 2")),
                            ),
                        ));
                    }
                    _ => {
                        // Pop two variables, create a new variable and push it back

                        let var1 = found_vars
                            .pop()
                            .unwrap_or_else(|| unreachable!("checked length >= 2"));
                        let var2 = found_vars
                            .pop()
                            .unwrap_or_else(|| unreachable!("checked length >= 2"));

                        let new_var = gen_var_name(var_names, &var1, &var2);

                        if new_var_names.insert(new_var.clone()) {
                            // Created new variable, so we need to create a new constraint for
                            // it

                            let new_constraint = NormalizedConstraint {
                                left: NormalizedExpr::Mul {
                                    scalar: F::ONE,
                                    term: SortedTerm::new(var1, Some(var2)),
                                },
                                right: NormalizedExpr::Var(new_var.clone()),
                            };
                            new_constraints.push(new_constraint);
                        } else {
                            // We have already created this variable and constraint for it, so
                            // no need to do it again
                        }

                        found_vars.push(new_var);
                    }
                }
            };

            simplify_multiplication(vars, const_factor)
        }
        Expr::UnaryMinus(sub_expr) => match *sub_expr {
            Expr::Var(var_name) => NormalizedExpr::UnaryMinus(var_name),
            _ => panic!("unary minus should contain only variable after brackets reveal"),
        },
        Expr::Const(c) => NormalizedExpr::Const(c),
        Expr::Var(v) => NormalizedExpr::Var(v),
    }
}

/// Sums terms in the expression, e.g. `2 * a + 3 * a - a` becomes `4 * a`.
fn sum_terms<F: PrimeField>(expr: &mut NormalizedExpr<F>) {
    let mut terms = BTreeMap::new();
    sum_terms_recursively(expr, &mut terms, true);

    let mut new_expr = None;
    for (vars, const_factor) in terms {
        if const_factor == F::ZERO {
            continue;
        }

        let term_expr = simplify_multiplication(vars, const_factor);

        if let Some(existing_expr) = new_expr {
            new_expr = Some(NormalizedExpr::Add {
                left: Box::new(existing_expr),
                right: Box::new(term_expr),
            });
        } else {
            new_expr = Some(term_expr);
        }
    }

    *expr = new_expr.unwrap_or(NormalizedExpr::zero());
}

fn sum_terms_recursively<F: PrimeField>(
    expr: &NormalizedExpr<F>,
    terms: &mut BTreeMap<Option<SortedTerm>, F>,
    is_positive: bool,
) {
    match expr {
        NormalizedExpr::Add { left, right } => {
            sum_terms_recursively(left, terms, is_positive);
            sum_terms_recursively(right, terms, is_positive);
        }
        NormalizedExpr::Sub { left, right } => {
            sum_terms_recursively(left, terms, is_positive);
            sum_terms_recursively(right, terms, !is_positive);
        }
        NormalizedExpr::Mul { scalar, term } => {
            let sign = if is_positive { F::ONE } else { -F::ONE };
            *terms.entry(Some(term.clone())).or_default() += (*scalar) * sign;
        }
        NormalizedExpr::UnaryMinus(var) => {
            let sign = if is_positive { -F::ONE } else { F::ONE };
            *terms
                .entry(Some(SortedTerm::new(var.clone(), None)))
                .or_default() += sign;
        }
        NormalizedExpr::Var(var) => {
            let sign = if is_positive { F::ONE } else { -F::ONE };
            *terms
                .entry(Some(SortedTerm::new(var.clone(), None)))
                .or_default() += sign;
        }
        NormalizedExpr::Const(c) => {
            let sign = if is_positive { F::ONE } else { -F::ONE };
            *terms.entry(None).or_default() += sign * (*c);
        }
    }
}

fn simplify_multiplication<F: PrimeField>(
    vars: Option<SortedTerm>,
    const_factor: F,
) -> NormalizedExpr<F> {
    match (vars, const_factor) {
        (_, zero) if zero == F::ZERO => NormalizedExpr::zero(),
        (None, c) => NormalizedExpr::Const(c),
        (Some(SortedTerm { left, right: None }), minus_one) if minus_one == -F::ONE => {
            NormalizedExpr::UnaryMinus(left)
        }
        (Some(term), c) => NormalizedExpr::Mul { scalar: c, term },
    }
}

#[track_caller]
fn find_factors<F: PrimeField>(
    expr: &Expr<F>,
    found_vars: &mut SortedVec<VarName>,
    const_factor: &mut F,
) {
    match expr {
        Expr::Mul { left, right } => {
            find_factors(left, found_vars, const_factor);
            find_factors(right, found_vars, const_factor);
        }
        Expr::UnaryMinus(sub_expr) => match &**sub_expr {
            Expr::Var(var_name) => {
                found_vars.push(var_name.clone());
                *const_factor = -(*const_factor);
            }
            _ => {
                panic!("unary minus should contain only variable after brackets reveal");
            }
        },
        Expr::Var(var_name) => {
            found_vars.push(var_name.clone());
        }
        Expr::Const(c) => {
            *const_factor *= c;
        }
        Expr::Add { .. } | Expr::Sub { .. } => {
            panic!(
                "multiplication should not contain addition or subtraction after brackets reveal"
            );
        }
    }
}

fn gen_var_name(vars: &IndexSet<ScopedVar>, var1: &VarName, var2: &VarName) -> VarName {
    // Using hash of all user-provided variables to avoid theoretical collisions
    let mut hasher = ahash::RandomState::with_seed(5555).build_hasher();
    for var in vars.iter() {
        var.hash(&mut hasher);
    }
    let hash = hasher.finish();

    let name: VarName = format!("__{var1}_{var2}_{hash}").into();
    if vars.contains(&ScopedVar::Private(name.clone()))
        || vars.contains(&ScopedVar::Public(name.clone()))
    {
        panic!("converting to R1CS generated a duplicated variable name, this should never happen");
    }

    name
}

fn move_non_var_multiplications_to_right<F: PrimeField>(
    mut left: &mut NormalizedExpr<F>,
    right: &mut NormalizedExpr<F>,
    is_positive: bool,
) {
    match &mut left {
        NormalizedExpr::Add { left: l, right: r } => {
            move_non_var_multiplications_to_right(l, right, is_positive);
            move_non_var_multiplications_to_right(r, right, is_positive);
            match (&mut **l, &mut **r) {
                (NormalizedExpr::Const(l_zero), NormalizedExpr::Const(r_zero))
                    if *l_zero == F::ZERO && *r_zero == F::ZERO =>
                {
                    *left = NormalizedExpr::zero();
                }
                (NormalizedExpr::Const(zero), _) if *zero == F::ZERO => {
                    *left = r.take();
                }
                (_, NormalizedExpr::Const(zero)) if *zero == F::ZERO => {
                    *left = l.take();
                }
                _ => {}
            }
        }
        NormalizedExpr::Sub { left: l, right: r } => {
            move_non_var_multiplications_to_right(l, right, is_positive);
            move_non_var_multiplications_to_right(r, right, !is_positive);
            match (&mut **l, &mut **r) {
                (l_zero, r_zero) if l_zero.is_zero() && r_zero.is_zero() => {
                    *left = NormalizedExpr::zero();
                }
                (zero, _) if zero.is_zero() => {
                    *left = r.take().negate();
                }
                (_, zero) if zero.is_zero() => {
                    *left = l.take();
                }
                _ => {}
            }
        }
        NormalizedExpr::Mul { scalar, term } => {
            if term.right.is_some() {
                // Main case, leaving as is
            } else {
                let sign = if is_positive { F::ONE } else { -F::ONE };
                let scalar = (*scalar) * sign;
                *right = NormalizedExpr::Sub {
                    left: Box::new(right.take()),
                    right: Box::new(NormalizedExpr::Mul {
                        scalar,
                        term: term.clone(),
                    }),
                };
                *left = NormalizedExpr::zero();
            }
        }
        NormalizedExpr::UnaryMinus(var) => {
            let mut var_expr = NormalizedExpr::Var(var.clone());
            move_non_var_multiplications_to_right(&mut var_expr, right, !is_positive);
            *left = NormalizedExpr::zero();
        }
        NormalizedExpr::Const(_) => {
            match (&*right, is_positive) {
                (zero, true) if zero.is_zero() => {
                    *right = left.take().negate();
                }
                (zero, false) if zero.is_zero() => {
                    *right = left.take();
                }
                (_, true) => {
                    *right = NormalizedExpr::Sub {
                        left: Box::new(right.take()),
                        right: Box::new(left.take()),
                    };
                }
                (_, false) => {
                    *right = NormalizedExpr::Add {
                        left: Box::new(right.take()),
                        right: Box::new(left.take()),
                    };
                }
            }

            *left = NormalizedExpr::zero();
        }
        NormalizedExpr::Var(var) => {
            match (&*right, is_positive) {
                (zero, true) if zero.is_zero() => {
                    *right = NormalizedExpr::UnaryMinus(var.clone());
                }
                (zero, false) if zero.is_zero() => {
                    *right = left.take();
                }
                (_, true) => {
                    *right = NormalizedExpr::Sub {
                        left: Box::new(right.take()),
                        right: Box::new(left.take()),
                    };
                }
                (_, false) => {
                    *right = NormalizedExpr::Add {
                        left: Box::new(right.take()),
                        right: Box::new(left.take()),
                    };
                }
            }

            *left = NormalizedExpr::zero();
        }
    }
}

#[cfg(test)]
mod tests {
    use bls12_381::Scalar;
    use ff::Field as _;
    use regex::Regex;

    use super::*;

    #[test]
    fn test_normalized_expr_negate_smoke() {
        let expr = NormalizedExpr::<Scalar>::Add {
            left: Box::new(NormalizedExpr::Const(5.into())),
            right: Box::new(NormalizedExpr::Var("a".into())),
        };

        assert_eq!(
            expr.negate(),
            NormalizedExpr::Sub {
                left: Box::new(NormalizedExpr::Const(-Scalar::from(5))),
                right: Box::new(NormalizedExpr::Var("a".into())),
            }
        );
    }

    #[test]
    fn test_reveal_brackets_smoke() {
        // (-a + b * c) * (d - (e + f)) - g
        let mut expr = Expr::<Scalar>::Sub {
            left: Box::new(Expr::Mul {
                left: Box::new(Expr::Add {
                    left: Box::new(Expr::UnaryMinus(Box::new(Expr::Var("a".into())))),
                    right: Box::new(Expr::Mul {
                        left: Box::new(Expr::Var("b".into())),
                        right: Box::new(Expr::Var("c".into())),
                    }),
                }),
                right: Box::new(Expr::Sub {
                    left: Box::new(Expr::Var("d".into())),
                    right: Box::new(Expr::Add {
                        left: Box::new(Expr::Var("e".into())),
                        right: Box::new(Expr::Var("f".into())),
                    }),
                }),
            }),
            right: Box::new(Expr::Var("g".into())),
        };

        // ((((-a * d) - ((-a * e) + (-a * f))) + (((b * c) * d) - (((b * c) * e) + ((b * c) * f))))
        // - g)
        let expected = Expr::Sub {
            left: Box::new(Expr::Add {
                left: Box::new(Expr::Sub {
                    left: Box::new(Expr::Mul {
                        left: Box::new(Expr::UnaryMinus(Box::new(Expr::Var("a".into())))),
                        right: Box::new(Expr::Var("d".into())),
                    }),
                    right: Box::new(Expr::Add {
                        left: Box::new(Expr::Mul {
                            left: Box::new(Expr::UnaryMinus(Box::new(Expr::Var("a".into())))),
                            right: Box::new(Expr::Var("e".into())),
                        }),
                        right: Box::new(Expr::Mul {
                            left: Box::new(Expr::UnaryMinus(Box::new(Expr::Var("a".into())))),
                            right: Box::new(Expr::Var("f".into())),
                        }),
                    }),
                }),
                right: Box::new(Expr::Sub {
                    left: Box::new(Expr::Mul {
                        left: Box::new(Expr::Mul {
                            left: Box::new(Expr::Var("b".into())),
                            right: Box::new(Expr::Var("c".into())),
                        }),
                        right: Box::new(Expr::Var("d".into())),
                    }),
                    right: Box::new(Expr::Add {
                        left: Box::new(Expr::Mul {
                            left: Box::new(Expr::Mul {
                                left: Box::new(Expr::Var("b".into())),
                                right: Box::new(Expr::Var("c".into())),
                            }),
                            right: Box::new(Expr::Var("e".into())),
                        }),
                        right: Box::new(Expr::Mul {
                            left: Box::new(Expr::Mul {
                                left: Box::new(Expr::Var("b".into())),
                                right: Box::new(Expr::Var("c".into())),
                            }),
                            right: Box::new(Expr::Var("f".into())),
                        }),
                    }),
                }),
            }),
            right: Box::new(Expr::Var("g".into())),
        };

        reveal_brackets(&mut expr);
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_pack_var_multiplications_smoke() {
        let var_names = IndexSet::from_iter([
            ScopedVar::Public("a".into()),
            ScopedVar::Private("b".into()),
            ScopedVar::Private("c".into()),
            ScopedVar::Private("d".into()),
        ]);
        // (((-2 * (a * (b * c))) + (a * (b * d))) - ((-b * d) - (3 * d)))
        let expr = Expr::<Scalar>::Sub {
            left: Box::new(Expr::Add {
                left: Box::new(Expr::Mul {
                    left: Box::new(Expr::Const(-Scalar::from(2))),
                    right: Box::new(Expr::Mul {
                        left: Box::new(Expr::Var("a".into())),
                        right: Box::new(Expr::Mul {
                            left: Box::new(Expr::Var("b".into())),
                            right: Box::new(Expr::Var("c".into())),
                        }),
                    }),
                }),
                right: Box::new(Expr::Mul {
                    left: Box::new(Expr::Var("a".into())),
                    right: Box::new(Expr::Mul {
                        left: Box::new(Expr::Var("b".into())),
                        right: Box::new(Expr::Var("d".into())),
                    }),
                }),
            }),
            right: Box::new(Expr::Sub {
                left: Box::new(Expr::Mul {
                    left: Box::new(Expr::UnaryMinus(Box::new(Expr::Var("b".into())))),
                    right: Box::new(Expr::Var("d".into())),
                }),
                right: Box::new(Expr::Mul {
                    left: Box::new(Expr::Const(Scalar::from(3))),
                    right: Box::new(Expr::Var("d".into())),
                }),
            }),
        };
        let mut new_constraints = Vec::new();
        let mut new_var_names = IndexSet::new();

        let normalized = pack_var_multiplications(
            &var_names,
            expr,
            &mut new_constraints,
            &mut new_var_names,
            &mut false,
        );

        // ((-2 * cb * a + adb) - (-db - (3 * d)))
        let regex = Regex::new(&format!(
            r"\(\({} \* __c_b_\d+\ \* a \+ __a___d_b_\d+_\d+\) - \(-__d_b_\d+ - {} \* d\)\)",
            -Scalar::from(2),
            Scalar::from(3),
        ))
        .unwrap();
        let normalized = normalized.to_string();
        assert!(
            regex.is_match(&normalized),
            "{normalized} does not match {regex}"
        );
        assert_eq!(new_constraints.len(), 3);
    }

    #[test]
    fn test_sum_terms_smoke() {
        // 2 * a * b + 3 * b * a - a
        let mut expr = NormalizedExpr::<Scalar>::Add {
            left: Box::new(NormalizedExpr::Mul {
                scalar: 2.into(),
                term: SortedTerm::new("a".into(), Some("b".into())),
            }),
            right: Box::new(NormalizedExpr::Sub {
                left: Box::new(NormalizedExpr::Mul {
                    scalar: 3.into(),
                    term: SortedTerm::new("b".into(), Some("a".into())),
                }),
                right: Box::new(NormalizedExpr::Mul {
                    scalar: 1.into(),
                    term: SortedTerm::new("a".into(), None),
                }),
            }),
        };

        // - a + 5 * a * b
        let expected = NormalizedExpr::Add {
            left: Box::new(NormalizedExpr::UnaryMinus("a".into())),
            right: Box::new(NormalizedExpr::Mul {
                scalar: 5.into(),
                term: SortedTerm::new("a".into(), Some("b".into())),
            }),
        };

        sum_terms(&mut expr);
        assert_eq!(expr, expected, "expected: {expected}, got: {expr}");
    }

    #[test]
    fn test_move_non_var_multiplications_to_right_smoke() {
        // -2 * a * b + d - 3 * f + 4
        let mut left = NormalizedExpr::<Scalar>::Add {
            left: Box::new(NormalizedExpr::Add {
                left: Box::new(NormalizedExpr::Mul {
                    scalar: -Scalar::from(2),
                    term: SortedTerm::new("a".into(), Some("b".into())),
                }),
                right: Box::new(NormalizedExpr::Sub {
                    left: Box::new(NormalizedExpr::Var("d".into())),
                    right: Box::new(NormalizedExpr::Mul {
                        scalar: 3.into(),
                        term: SortedTerm::new("f".into(), None),
                    }),
                }),
            }),
            right: Box::new(NormalizedExpr::Const(Scalar::from(4))),
        };
        let mut right = NormalizedExpr::Const(Scalar::ZERO);

        // -2 * a * b
        let expected_left = NormalizedExpr::Mul {
            scalar: -Scalar::from(2),
            term: SortedTerm::new("a".into(), Some("b".into())),
        };

        // (-d) + 3 * f - 4
        let expected_right = NormalizedExpr::Sub {
            left: Box::new(NormalizedExpr::Sub {
                left: Box::new(NormalizedExpr::UnaryMinus("d".into())),
                right: Box::new(NormalizedExpr::Mul {
                    scalar: -Scalar::from(3),
                    term: SortedTerm::new("f".into(), None),
                }),
            }),
            right: Box::new(NormalizedExpr::Const(Scalar::from(4))),
        };

        move_non_var_multiplications_to_right(&mut left, &mut right, true);

        assert_eq!(
            left, expected_left,
            "expected: {expected_left}, got: {left}"
        );
        assert_eq!(
            right, expected_right,
            "expected: {expected_right}, got: {right}"
        );
    }
}
