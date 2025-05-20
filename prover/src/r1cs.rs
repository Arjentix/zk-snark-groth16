//! Rank One Constraint System (R1CS) utilities.

use circuit::{Circuit, Expression};

type Matrix = ndarray::Array2<f64>;

/// Rank One Constraint System.
///
/// Contains L, R, and O (`La * Ra = Oa`, where `a` -- witness vector) matrices which have meaning
/// only with the corresponding [`WitnessSchema`].
pub struct R1cs {
    left: Matrix,
    right: Matrix,
    output: Matrix,
}

pub struct WitnessSchema {
    pub schema: Vec<String>,
}

/// Derives a R1CS and witness schema from a given circuit.
pub fn derive(mut circuit: Circuit) -> (R1cs, WitnessSchema) {
    normalize(&mut circuit);

    todo!()
}

fn normalize(circuit: &mut Circuit) {
    let mut new_constraints = Vec::<circuit::Constraint>::new();

    let mut i = 0;
    while i < circuit.constraints.len() {
        let constraint = &mut circuit.constraints[i];
        reveal_brackets(&mut constraint.left);
        reveal_brackets(&mut constraint.right);
        todo!()
    }

    todo!()
}

fn reveal_brackets(expr: &mut Expression) {
    match expr {
        Expression::Add { left, right } => {
            reveal_brackets(left);
            reveal_brackets(right);
        }
        Expression::Sub { left, right } => {
            reveal_brackets(left);
            reveal_brackets(right);

            if let Expression::UnaryMinus(sub_expr) = &**right {
                // Replace `x - (-y)` with `x + y`
                *expr = Expression::Add {
                    left: left.clone(),
                    right: sub_expr.clone(),
                };
            }
        }
        Expression::Mul { left, right } => {
            reveal_brackets(left);
            reveal_brackets(right);

            match (&**left, &**right) {
                (
                    Expression::Add {
                        left: add_left,
                        right: add_right,
                    },
                    _,
                ) => {
                    // Replace `(x + y) * z` with `x * z + y * z`
                    *expr = Expression::Add {
                        left: Box::new(Expression::Mul {
                            left: add_left.clone(),
                            right: right.clone(),
                        }),
                        right: Box::new(Expression::Mul {
                            left: add_right.clone(),
                            right: right.clone(),
                        }),
                    };
                    reveal_brackets(expr);
                }
                (
                    Expression::Sub {
                        left: sub_left,
                        right: sub_right,
                    },
                    _,
                ) => {
                    // Replace `(x - y) * z` with `x * z - y * z`
                    *expr = Expression::Sub {
                        left: Box::new(Expression::Mul {
                            left: sub_left.clone(),
                            right: right.clone(),
                        }),
                        right: Box::new(Expression::Mul {
                            left: sub_right.clone(),
                            right: right.clone(),
                        }),
                    };
                    reveal_brackets(expr);
                }
                (
                    _,
                    Expression::Add {
                        left: add_left,
                        right: add_right,
                    },
                ) => {
                    // Replace `x * (y + z)` with `x * y + x * z`
                    *expr = Expression::Add {
                        left: Box::new(Expression::Mul {
                            left: left.clone(),
                            right: add_left.clone(),
                        }),
                        right: Box::new(Expression::Mul {
                            left: left.clone(),
                            right: add_right.clone(),
                        }),
                    };
                    reveal_brackets(expr);
                }
                (
                    _,
                    Expression::Sub {
                        left: sub_left,
                        right: sub_right,
                    },
                ) => {
                    // Replace `x * (y - z)` with `x * y - x * z`
                    *expr = Expression::Sub {
                        left: Box::new(Expression::Mul {
                            left: left.clone(),
                            right: sub_left.clone(),
                        }),
                        right: Box::new(Expression::Mul {
                            left: left.clone(),
                            right: sub_right.clone(),
                        }),
                    };
                    reveal_brackets(expr);
                }
                (Expression::UnaryMinus(left), Expression::UnaryMinus(right)) => {
                    // Replace `(-x) * (-y)` with `x * y`
                    *expr = Expression::Mul {
                        left: left.clone(),
                        right: right.clone(),
                    };
                }
                _ => {}
            }
        }
        Expression::UnaryMinus(sub_expr) => {
            reveal_brackets(sub_expr);

            match &**sub_expr {
                Expression::Add { left, right } => {
                    // Replace `-(x + y)` with `-x - y`
                    *expr = Expression::Sub {
                        left: Box::new(Expression::UnaryMinus(left.clone())),
                        right: Box::new(Expression::UnaryMinus(right.clone())),
                    };
                }
                Expression::Sub { left, right } => {
                    // Replace `-(x - y)` with `-x + y`
                    *expr = Expression::Add {
                        left: Box::new(Expression::UnaryMinus(left.clone())),
                        right: right.clone(),
                    };
                }
                Expression::Mul { left, right } => {
                    // Replace `-(x * y)` with `-x * y`
                    *expr = Expression::Mul {
                        left: Box::new(Expression::UnaryMinus(left.clone())),
                        right: right.clone(),
                    };
                }
                Expression::UnaryMinus(sub_sub_expr) => {
                    // Replace `-(-x)` with `x`
                    *expr = *sub_sub_expr.clone();
                }
                Expression::Const(_) | Expression::Var(_) => {}
            }
        }
        Expression::Const(_) | Expression::Var(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reveal_brackets_smoke() {
        // (-a + b*c) * (d - (e + f)) - g
        let mut expr = Expression::Sub {
            left: Box::new(Expression::Mul {
                left: Box::new(Expression::Add {
                    left: Box::new(Expression::UnaryMinus(Box::new(Expression::Var("a")))),
                    right: Box::new(Expression::Mul {
                        left: Box::new(Expression::Var("b")),
                        right: Box::new(Expression::Var("c")),
                    }),
                }),
                right: Box::new(Expression::Sub {
                    left: Box::new(Expression::Var("d")),
                    right: Box::new(Expression::Add {
                        left: Box::new(Expression::Var("e")),
                        right: Box::new(Expression::Var("f")),
                    }),
                }),
            }),
            right: Box::new(Expression::Var("g")),
        };

        // ((((-a * d) - ((-a * e) + (-a * f))) + (((b * c) * d) - (((b * c) * e) + ((b * c) * f))))
        // - g)
        let expected = Expression::Sub {
            left: Box::new(Expression::Add {
                left: Box::new(Expression::Sub {
                    left: Box::new(Expression::Mul {
                        left: Box::new(Expression::UnaryMinus(Box::new(Expression::Var("a")))),
                        right: Box::new(Expression::Var("d")),
                    }),
                    right: Box::new(Expression::Add {
                        left: Box::new(Expression::Mul {
                            left: Box::new(Expression::UnaryMinus(Box::new(Expression::Var("a")))),
                            right: Box::new(Expression::Var("e")),
                        }),
                        right: Box::new(Expression::Mul {
                            left: Box::new(Expression::UnaryMinus(Box::new(Expression::Var("a")))),
                            right: Box::new(Expression::Var("f")),
                        }),
                    }),
                }),
                right: Box::new(Expression::Sub {
                    left: Box::new(Expression::Mul {
                        left: Box::new(Expression::Mul {
                            left: Box::new(Expression::Var("b")),
                            right: Box::new(Expression::Var("c")),
                        }),
                        right: Box::new(Expression::Var("d")),
                    }),
                    right: Box::new(Expression::Add {
                        left: Box::new(Expression::Mul {
                            left: Box::new(Expression::Mul {
                                left: Box::new(Expression::Var("b")),
                                right: Box::new(Expression::Var("c")),
                            }),
                            right: Box::new(Expression::Var("e")),
                        }),
                        right: Box::new(Expression::Mul {
                            left: Box::new(Expression::Mul {
                                left: Box::new(Expression::Var("b")),
                                right: Box::new(Expression::Var("c")),
                            }),
                            right: Box::new(Expression::Var("f")),
                        }),
                    }),
                }),
            }),
            right: Box::new(Expression::Var("g")),
        };

        reveal_brackets(&mut expr);
        assert_eq!(expr, expected);
    }
}
