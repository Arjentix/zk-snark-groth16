//! Rank One Constraint System (R1CS) utilities.

use std::{
    collections::BTreeMap,
    hash::{BuildHasher as _, Hash as _, Hasher as _},
};

use circuit::{Circuit, Constraint, Expr, ScopedVar, VarName};
use ff::PrimeField;
use indexmap::IndexSet;
use logger::info;
use sorted_vec::SortedVec;

type Matrix<F> = ndarray::Array2<F>;

/// Rank One Constraint System.
///
/// Contains L, R, and O (`La * Ra = Oa`, where `a` -- witness vector) matrices which have meaning
/// only with the corresponding [`WitnessSchema`].
pub struct R1cs<F: PrimeField> {
    left: Matrix<F>,
    right: Matrix<F>,
    output: Matrix<F>,
}

pub struct WitnessSchema {
    pub schema: Vec<VarName>,
}

/// Derives a R1CS and witness schema from a given circuit.
pub fn derive<F: PrimeField + std::fmt::Display>(
    mut circuit: Circuit<F>,
) -> (R1cs<F>, WitnessSchema) {
    normalize(&mut circuit);
    info!(circuit = %circuit, "normalized circuit");

    todo!()
}

fn normalize<F: PrimeField>(circuit: &mut Circuit<F>) {
    let mut constraints = std::mem::take(&mut circuit.constraints);
    let mut new_constraints = Vec::new();
    let mut new_var_names = IndexSet::new();

    for constraint in &mut constraints {
        move_right_to_left(&mut constraint.left, &mut constraint.right);
        reveal_brackets(&mut constraint.left);
        pack_var_multiplications(
            &circuit.vars,
            &mut constraint.left,
            &mut new_constraints,
            &mut new_var_names,
            &mut false,
        );
        sum_terms(&mut constraint.left);
        move_non_var_multiplications_to_right(&mut constraint.left, &mut constraint.right, true);
    }

    new_constraints.append(&mut constraints);
    circuit.constraints = new_constraints;
    circuit
        .vars
        .extend(new_var_names.into_iter().map(ScopedVar::Private));
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
                Expr::Const(_) | Expr::Var(_) => {}
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
    expr: &mut Expr<F>,
    new_constraints: &mut Vec<Constraint<F>>,
    new_var_names: &mut IndexSet<VarName>,
    var_multiplication_set: &mut bool,
) {
    match expr {
        Expr::Add { left, right } => {
            pack_var_multiplications(
                var_names,
                left,
                new_constraints,
                new_var_names,
                var_multiplication_set,
            );
            pack_var_multiplications(
                var_names,
                right,
                new_constraints,
                new_var_names,
                var_multiplication_set,
            );
        }
        Expr::Sub { left, right } => {
            pack_var_multiplications(
                var_names,
                left,
                new_constraints,
                new_var_names,
                var_multiplication_set,
            );
            pack_var_multiplications(
                var_names,
                right,
                new_constraints,
                new_var_names,
                var_multiplication_set,
            );
        }
        Expr::Mul { left, right } => {
            let mut found_vars = SortedVec::new();
            let mut const_factor = F::ONE;
            find_factors(left, &mut found_vars, &mut const_factor);
            find_factors(right, &mut found_vars, &mut const_factor);

            let var_expr = loop {
                match found_vars.len() {
                    0 => {
                        break None;
                    }
                    1 => {
                        break Some(Expr::Var(found_vars.pop().expect("checked length = 1")));
                    }
                    2 if !*var_multiplication_set => {
                        *var_multiplication_set = true;
                        break Some(Expr::Mul {
                            left: Box::new(Expr::Var(
                                found_vars.pop().expect("checked length = 2"),
                            )),
                            right: Box::new(Expr::Var(
                                found_vars.pop().expect("checked length = 2"),
                            )),
                        });
                    }
                    _ => {
                        // Pop two variables, create a new variable and push it back

                        let var1 = found_vars.pop().expect("checked length >= 2");
                        let var2 = found_vars.pop().expect("checked length >= 2");

                        let new_var = gen_var_name(var_names, &var1, &var2);

                        if new_var_names.insert(new_var.clone()) {
                            // Created new variable, so we need to create a new constraint for
                            // it

                            let new_constraint = Constraint {
                                left: Expr::Mul {
                                    left: Box::new(Expr::Var(var1)),
                                    right: Box::new(Expr::Var(var2)),
                                },
                                right: Expr::Var(new_var.clone()),
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

            *expr = mul_var_expr_and_const_factor(var_expr, const_factor);
        }
        Expr::UnaryMinus(sub_expr) => {
            pack_var_multiplications(
                var_names,
                sub_expr,
                new_constraints,
                new_var_names,
                var_multiplication_set,
            );
        }
        Expr::Const(_) | Expr::Var(_) => {}
    }
}

/// Sums terms in the expression, e.g. `2 * a + 3 * a - a` becomes `4 * a`.
fn sum_terms<F: PrimeField>(expr: &mut Expr<F>) {
    let mut terms = BTreeMap::new();
    sum_terms_recursively(expr, &mut terms, true);

    let mut new_expr = None;
    for (vars, const_factor) in terms {
        if const_factor == F::ZERO {
            continue;
        }

        let var_expr = mul_vars(&vars);
        let term_expr = mul_var_expr_and_const_factor(var_expr, const_factor);

        if let Some(existing_expr) = new_expr {
            new_expr = Some(Expr::Add {
                left: Box::new(existing_expr),
                right: Box::new(term_expr),
            });
        } else {
            new_expr = Some(term_expr);
        }
    }

    *expr = new_expr.unwrap_or(Expr::Const(F::ZERO));
}

fn sum_terms_recursively<F: PrimeField>(
    expr: &Expr<F>,
    terms: &mut BTreeMap<SortedVec<VarName>, F>,
    is_positive: bool,
) {
    match expr {
        Expr::Add { left, right } => {
            sum_terms_recursively(left, terms, is_positive);
            sum_terms_recursively(right, terms, is_positive);
        }
        Expr::Sub { left, right } => {
            sum_terms_recursively(left, terms, is_positive);
            sum_terms_recursively(right, terms, !is_positive);
        }
        Expr::Mul { left, right } => {
            let mut found_vars = SortedVec::new();
            let mut const_factor = if is_positive { F::ONE } else { -F::ONE };
            find_factors(left, &mut found_vars, &mut const_factor);
            find_factors(right, &mut found_vars, &mut const_factor);

            *terms.entry(found_vars).or_default() += const_factor;
        }
        Expr::UnaryMinus(sub_expr) => {
            sum_terms_recursively(sub_expr, terms, !is_positive);
        }
        Expr::Var(var) => {
            let sign = if is_positive { F::ONE } else { -F::ONE };
            *terms.entry(SortedVec::from(vec![var.clone()])).or_default() += sign;
        }
        Expr::Const(c) => {
            let sign = if is_positive { F::ONE } else { -F::ONE };
            *terms.entry(SortedVec::default()).or_default() += sign * (*c);
        }
    }
}

fn mul_vars<F: PrimeField>(vars: &[VarName]) -> Option<Expr<F>> {
    match vars.len() {
        0 => None,
        1 => Some(Expr::Var(vars[0].clone())),
        _ => Some(Expr::Mul {
            left: Box::new(Expr::Var(vars[0].clone())),
            right: Box::new(mul_vars(&vars[1..]).unwrap_or_else(|| unreachable!("never empty"))),
        }),
    }
}

fn mul_var_expr_and_const_factor<F: PrimeField>(
    var_expr: Option<Expr<F>>,
    const_factor: F,
) -> Expr<F> {
    match (var_expr, const_factor) {
        (_, zero) if zero == F::ZERO => {
            // If the const is 0, we can just ignore this multiplication
            Expr::Const(F::ZERO)
        }
        (None, c) => {
            // If there are no variables, we can just replace the multiplication with a
            // constant
            Expr::Const(c)
        }
        (Some(var_expr), one) if one == F::ONE => {
            // If the const is 1, we can just replace the multiplication with the variable
            var_expr
        }
        (Some(var_expr), minus_one) if minus_one == -F::ONE => {
            // If the const is -1, we can just replace the multiplication with the unary
            // minus of the variable
            Expr::UnaryMinus(Box::new(var_expr))
        }
        (Some(var_expr), c) => {
            // Otherwise, we can replace the multiplication with a new variable
            Expr::Mul {
                left: Box::new(Expr::Const(c)),
                right: Box::new(var_expr),
            }
        }
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
            Expr::Const(c) => {
                *const_factor *= -(*c);
            }
            _ => {
                panic!(
                    "unary minus should contain only variable or constant after brackets reveal"
                );
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
    mut left: &mut Expr<F>,
    right: &mut Expr<F>,
    is_positive: bool,
) {
    match &mut left {
        Expr::Add { left: l, right: r } => {
            move_non_var_multiplications_to_right(l, right, is_positive);
            move_non_var_multiplications_to_right(r, right, is_positive);
            match (&**l, &**r) {
                (Expr::Const(l_zero), Expr::Const(r_zero))
                    if *l_zero == F::ZERO && *r_zero == F::ZERO =>
                {
                    *left = Expr::Const(F::ZERO);
                }
                (Expr::Const(zero), _) if *zero == F::ZERO => {
                    *left = (**r).clone();
                }
                (_, Expr::Const(zero)) if *zero == F::ZERO => {
                    *left = (**l).clone();
                }
                _ => {}
            }
        }
        Expr::Sub { left: l, right: r } => {
            move_non_var_multiplications_to_right(l, right, is_positive);
            move_non_var_multiplications_to_right(r, right, !is_positive);
            match (&**l, &**r) {
                (Expr::Const(l_zero), Expr::Const(r_zero))
                    if *l_zero == F::ZERO && *r_zero == F::ZERO =>
                {
                    *left = Expr::Const(F::ZERO);
                }
                (Expr::Const(zero), _) if *zero == F::ZERO => {
                    *left = Expr::UnaryMinus((*r).clone());
                }
                (_, Expr::Const(zero)) if *zero == F::ZERO => {
                    *left = (**l).clone();
                }
                _ => {}
            }
        }
        Expr::Mul { left: l, right: r } => {
            let mut found_vars = SortedVec::new();
            let mut const_factor = if is_positive { F::ONE } else { -F::ONE };
            find_factors(l, &mut found_vars, &mut const_factor);
            find_factors(r, &mut found_vars, &mut const_factor);

            match found_vars.len() {
                0 | 1 => {
                    *right = Expr::Sub {
                        left: Box::new(right.clone()),
                        right: Box::new(left.clone()),
                    };
                    *left = Expr::Const(F::ZERO);
                }
                2 => {
                    // Main case, leaving as is
                }
                _ => unreachable!(
                    "should not have more than 2 variables in multiplication after packing"
                ),
            }
        }
        Expr::UnaryMinus(sub_expr) => {
            move_non_var_multiplications_to_right(sub_expr, right, !is_positive);
            if **sub_expr == Expr::Const(F::ZERO) {
                *left = Expr::Const(F::ZERO);
            }
        }
        Expr::Const(_) | Expr::Var(_) => {
            match (&*right, is_positive) {
                (Expr::Const(zero), true) if *zero == F::ZERO => {
                    *right = Expr::UnaryMinus(Box::new(left.clone()));
                }
                (Expr::Const(zero), false) if *zero == F::ZERO => {
                    *right = left.clone();
                }
                (_, true) => {
                    *right = Expr::Sub {
                        left: Box::new(right.clone()),
                        right: Box::new(left.clone()),
                    };
                }
                (_, false) => {
                    *right = Expr::Add {
                        left: Box::new(right.clone()),
                        right: Box::new(left.clone()),
                    };
                }
            }

            *left = Expr::Const(F::ZERO);
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
        let mut expr = Expr::<Scalar>::Sub {
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

        pack_var_multiplications(
            &var_names,
            &mut expr,
            &mut new_constraints,
            &mut new_var_names,
            &mut false,
        );

        // (((-2 * (a * cb)) + adb) - (-db - (3 * d)))
        let regex = Regex::new(
            &format!(
                r"\(\(\({} \* \(a \* __c_b_\d+\)\) \+ __a___d_b_\d+_\d+\) - \(-__d_b_\d+ - \({} \* d\)\)\)",
                -Scalar::from(2),
                Scalar::from(3),
            ),
        )
        .unwrap();
        let expr = expr.to_string();
        assert!(regex.is_match(&expr), "{expr} does not match {regex}");
        assert_eq!(new_constraints.len(), 3);
    }

    #[test]
    fn test_sum_terms_smoke() {
        // 2 * a * b * c + a * 3 * b * c - a * a * b * c
        let mut expr = Expr::<Scalar>::Add {
            left: Box::new(Expr::Mul {
                left: Box::new(Expr::Const(Scalar::from(2))),
                right: Box::new(Expr::Mul {
                    left: Box::new(Expr::Var("a".into())),
                    right: Box::new(Expr::Mul {
                        left: Box::new(Expr::Var("b".into())),
                        right: Box::new(Expr::Var("c".into())),
                    }),
                }),
            }),
            right: Box::new(Expr::Sub {
                left: Box::new(Expr::Mul {
                    left: Box::new(Expr::Var("a".into())),
                    right: Box::new(Expr::Mul {
                        left: Box::new(Expr::Const(Scalar::from(3))),
                        right: Box::new(Expr::Mul {
                            left: Box::new(Expr::Var("b".into())),
                            right: Box::new(Expr::Var("c".into())),
                        }),
                    }),
                }),
                right: Box::new(Expr::Mul {
                    left: Box::new(Expr::Var("a".into())),
                    right: Box::new(Expr::Mul {
                        left: Box::new(Expr::Var("a".into())),
                        right: Box::new(Expr::Mul {
                            left: Box::new(Expr::Var("b".into())),
                            right: Box::new(Expr::Var("c".into())),
                        }),
                    }),
                }),
            }),
        };

        // - a * a * b * c + 5 * a * b * c
        let expected = Expr::<Scalar>::Add {
            left: Box::new(Expr::UnaryMinus(Box::new(Expr::Mul {
                left: Box::new(Expr::Var("a".into())),
                right: Box::new(Expr::Mul {
                    left: Box::new(Expr::Var("a".into())),
                    right: Box::new(Expr::Mul {
                        left: Box::new(Expr::Var("b".into())),
                        right: Box::new(Expr::Var("c".into())),
                    }),
                }),
            }))),
            right: Box::new(Expr::Mul {
                left: Box::new(Expr::Const(Scalar::from(5))),
                right: Box::new(Expr::Mul {
                    left: Box::new(Expr::Var("a".into())),
                    right: Box::new(Expr::Mul {
                        left: Box::new(Expr::Var("b".into())),
                        right: Box::new(Expr::Var("c".into())),
                    }),
                }),
            }),
        };

        sum_terms(&mut expr);
        assert_eq!(expr, expected, "expected: {expected}, got: {expr}");
    }

    #[test]
    fn test_move_non_var_multiplications_to_right_smoke() {
        // a * (-b) * 2 + d - 3 * f + 4
        let mut left = Expr::<Scalar>::Add {
            left: Box::new(Expr::Add {
                left: Box::new(Expr::Mul {
                    left: Box::new(Expr::Var("a".into())),
                    right: Box::new(Expr::Mul {
                        left: Box::new(Expr::UnaryMinus(Box::new(Expr::Var("b".into())))),
                        right: Box::new(Expr::Const(Scalar::from(2))),
                    }),
                }),
                right: Box::new(Expr::Sub {
                    left: Box::new(Expr::Var("d".into())),
                    right: Box::new(Expr::Mul {
                        left: Box::new(Expr::Const(Scalar::from(3))),
                        right: Box::new(Expr::Var("f".into())),
                    }),
                }),
            }),
            right: Box::new(Expr::Const(Scalar::from(4))),
        };
        let mut right = Expr::Const(Scalar::ZERO);

        // a * (-b) * 2
        let expected_left = Expr::<Scalar>::Mul {
            left: Box::new(Expr::Var("a".into())),
            right: Box::new(Expr::Mul {
                left: Box::new(Expr::UnaryMinus(Box::new(Expr::Var("b".into())))),
                right: Box::new(Expr::Const(Scalar::from(2))),
            }),
        };

        // (-d) + 3 * f - 4
        let expected_right = Expr::<Scalar>::Sub {
            left: Box::new(Expr::Add {
                left: Box::new(Expr::UnaryMinus(Box::new(Expr::Var("d".into())))),
                right: Box::new(Expr::Mul {
                    left: Box::new(Expr::Const(Scalar::from(3))),
                    right: Box::new(Expr::Var("f".into())),
                }),
            }),
            right: Box::new(Expr::Const(Scalar::from(4))),
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
