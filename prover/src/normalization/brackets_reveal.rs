use std::ops::Deref as _;

use circuit::{Expr, VarName};
use ff::PrimeField;

use super::MulGenericExpr;

/// Multiplication after brackets reveal
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct RevealedMul<F: PrimeField> {
    pub left: Box<RevealedMulOperandExpr<F>>,
    pub right: Box<RevealedMulOperandExpr<F>>,
}

/// Expression that can be contained by multiplication operation after brackets reveal.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum RevealedMulOperandExpr<F: PrimeField> {
    Mul(RevealedMul<F>),
    UnaryMinus(VarName),
    Const(F),
    Var(VarName),
}

impl<F: PrimeField> From<RevealedMulOperandExpr<F>> for Expr<F> {
    fn from(value: RevealedMulOperandExpr<F>) -> Self {
        match value {
            RevealedMulOperandExpr::Mul(RevealedMul { left, right }) => Self::Mul {
                left: Box::new(left.deref().clone().into()),
                right: Box::new(right.deref().clone().into()),
            },
            RevealedMulOperandExpr::UnaryMinus(var_name) => {
                Self::UnaryMinus(Box::new(Self::Var(var_name)))
            }
            RevealedMulOperandExpr::Const(c) => Self::Const(c),
            RevealedMulOperandExpr::Var(v) => Self::Var(v),
        }
    }
}

/// Intermediate expression after brackets reveal,
pub type RevealedExpr<F> = MulGenericExpr<F, RevealedMul<F>>;

/// Reveal brackets from the expression.
///
/// # Example
///
/// ```text
/// (a + b) * c => a * c + b * c
/// ```
pub fn reveal<F: PrimeField>(expr: Expr<F>) -> RevealedExpr<F> {
    match expr {
        Expr::Add { left, right } => reveal_add(*left, *right),
        Expr::Sub { left, right } => reveal_sub(*left, *right),
        Expr::Mul { left, right } => reveal_mul(*left, *right),
        Expr::UnaryMinus(sub_expr) => reveal_unary_minus(*sub_expr),
        Expr::Const(c) => reveal_const(c),
        Expr::Var(var) => reveal_var(var),
    }
}

fn reveal_add<F: PrimeField>(left: Expr<F>, right: Expr<F>) -> RevealedExpr<F> {
    RevealedExpr::Add {
        left: Box::new(reveal(left)),
        right: Box::new(reveal(right)),
    }
}

fn reveal_sub<F: PrimeField>(left: Expr<F>, right: Expr<F>) -> RevealedExpr<F> {
    let left = reveal(left);
    let right = reveal(right);

    if let RevealedExpr::UnaryMinus(var) = right {
        // Replace `x - (-y)` with `x + y`
        RevealedExpr::Add {
            left: Box::new(left),
            right: Box::new(RevealedExpr::Var(var)),
        }
    } else {
        RevealedExpr::Sub {
            left: Box::new(left),
            right: Box::new(right),
        }
    }
}

fn reveal_mul<F: PrimeField>(left: Expr<F>, right: Expr<F>) -> RevealedExpr<F> {
    let left = reveal(left);
    let right = reveal(right);

    match (left, right) {
        (
            RevealedExpr::Add {
                left: add_left,
                right: add_right,
            },
            right,
        ) => {
            // Replace `(x + y) * z` with `x * z + y * z`
            let expr = Expr::Add {
                left: Box::new(Expr::Mul {
                    left: Box::new(add_left.deref().clone().into()),
                    right: Box::new(right.clone().into()),
                }),
                right: Box::new(Expr::Mul {
                    left: Box::new(add_right.deref().clone().into()),
                    right: Box::new(right.into()),
                }),
            };
            reveal(expr)
        }
        (
            RevealedExpr::Sub {
                left: sub_left,
                right: sub_right,
            },
            right,
        ) => {
            // Replace `(x - y) * z` with `x * z - y * z`
            let expr = Expr::Sub {
                left: Box::new(Expr::Mul {
                    left: Box::new(sub_left.deref().clone().into()),
                    right: Box::new(right.clone().into()),
                }),
                right: Box::new(Expr::Mul {
                    left: Box::new(sub_right.deref().clone().into()),
                    right: Box::new(right.into()),
                }),
            };
            reveal(expr)
        }
        (
            left,
            RevealedExpr::Add {
                left: add_left,
                right: add_right,
            },
        ) => {
            // Replace `x * (y + z)` with `x * y + x * z`
            let expr = Expr::Add {
                left: Box::new(Expr::Mul {
                    left: Box::new(left.clone().into()),
                    right: Box::new(add_left.deref().clone().into()),
                }),
                right: Box::new(Expr::Mul {
                    left: Box::new(left.into()),
                    right: Box::new(add_right.deref().clone().into()),
                }),
            };
            reveal(expr)
        }
        (
            left,
            RevealedExpr::Sub {
                left: sub_left,
                right: sub_right,
            },
        ) => {
            // Replace `x * (y - z)` with `x * y - x * z`
            let expr = Expr::Sub {
                left: Box::new(Expr::Mul {
                    left: Box::new(left.clone().into()),
                    right: Box::new(sub_left.deref().clone().into()),
                }),
                right: Box::new(Expr::Mul {
                    left: Box::new(left.into()),
                    right: Box::new(sub_right.deref().clone().into()),
                }),
            };
            reveal(expr)
        }
        (RevealedExpr::UnaryMinus(left), RevealedExpr::UnaryMinus(right)) => {
            // Replace `(-x) * (-y)` with `x * y`
            RevealedExpr::Mul(RevealedMul {
                left: Box::new(RevealedMulOperandExpr::Var(left)),
                right: Box::new(RevealedMulOperandExpr::Var(right)),
            })
        }

        // Below goes simple conversions from `ReveledExpr` to `ReveledMulOperandExpr`
        (RevealedExpr::Mul(left), RevealedExpr::Mul(right)) => RevealedExpr::Mul(RevealedMul {
            left: Box::new(RevealedMulOperandExpr::Mul(left)),
            right: Box::new(RevealedMulOperandExpr::Mul(right)),
        }),
        (RevealedExpr::Const(c), RevealedExpr::Mul(right)) => RevealedExpr::Mul(RevealedMul {
            left: Box::new(RevealedMulOperandExpr::Const(c)),
            right: Box::new(RevealedMulOperandExpr::Mul(right)),
        }),
        (RevealedExpr::Mul(left), RevealedExpr::Const(c)) => RevealedExpr::Mul(RevealedMul {
            left: Box::new(RevealedMulOperandExpr::Mul(left)),
            right: Box::new(RevealedMulOperandExpr::Const(c)),
        }),
        (RevealedExpr::Var(var), RevealedExpr::Mul(right)) => RevealedExpr::Mul(RevealedMul {
            left: Box::new(RevealedMulOperandExpr::Var(var)),
            right: Box::new(RevealedMulOperandExpr::Mul(right)),
        }),
        (RevealedExpr::Mul(left), RevealedExpr::Var(var)) => RevealedExpr::Mul(RevealedMul {
            left: Box::new(RevealedMulOperandExpr::Mul(left)),
            right: Box::new(RevealedMulOperandExpr::Var(var)),
        }),
        (RevealedExpr::Mul(left), RevealedExpr::UnaryMinus(var)) => {
            RevealedExpr::Mul(RevealedMul {
                left: Box::new(RevealedMulOperandExpr::Mul(left)),
                right: Box::new(RevealedMulOperandExpr::UnaryMinus(var)),
            })
        }
        (RevealedExpr::UnaryMinus(var), RevealedExpr::Mul(right)) => {
            RevealedExpr::Mul(RevealedMul {
                left: Box::new(RevealedMulOperandExpr::UnaryMinus(var)),
                right: Box::new(RevealedMulOperandExpr::Mul(right)),
            })
        }
        (RevealedExpr::UnaryMinus(left), RevealedExpr::Var(right)) => {
            RevealedExpr::Mul(RevealedMul {
                left: Box::new(RevealedMulOperandExpr::UnaryMinus(left)),
                right: Box::new(RevealedMulOperandExpr::Var(right)),
            })
        }
        (RevealedExpr::Var(left), RevealedExpr::UnaryMinus(right)) => {
            RevealedExpr::Mul(RevealedMul {
                left: Box::new(RevealedMulOperandExpr::Var(left)),
                right: Box::new(RevealedMulOperandExpr::UnaryMinus(right)),
            })
        }
        (RevealedExpr::UnaryMinus(var), RevealedExpr::Const(c)) => RevealedExpr::Mul(RevealedMul {
            left: Box::new(RevealedMulOperandExpr::UnaryMinus(var)),
            right: Box::new(RevealedMulOperandExpr::Const(c)),
        }),
        (RevealedExpr::Const(c), RevealedExpr::UnaryMinus(var)) => RevealedExpr::Mul(RevealedMul {
            left: Box::new(RevealedMulOperandExpr::Const(c)),
            right: Box::new(RevealedMulOperandExpr::UnaryMinus(var)),
        }),
        (RevealedExpr::Const(left), RevealedExpr::Const(right)) => RevealedExpr::Mul(RevealedMul {
            left: Box::new(RevealedMulOperandExpr::Const(left)),
            right: Box::new(RevealedMulOperandExpr::Const(right)),
        }),
        (RevealedExpr::Const(left), RevealedExpr::Var(right)) => RevealedExpr::Mul(RevealedMul {
            left: Box::new(RevealedMulOperandExpr::Const(left)),
            right: Box::new(RevealedMulOperandExpr::Var(right)),
        }),
        (RevealedExpr::Var(left), RevealedExpr::Const(right)) => RevealedExpr::Mul(RevealedMul {
            left: Box::new(RevealedMulOperandExpr::Var(left)),
            right: Box::new(RevealedMulOperandExpr::Const(right)),
        }),
        (RevealedExpr::Var(left), RevealedExpr::Var(right)) => RevealedExpr::Mul(RevealedMul {
            left: Box::new(RevealedMulOperandExpr::Var(left)),
            right: Box::new(RevealedMulOperandExpr::Var(right)),
        }),
    }
}

fn apply_unary_minus_recursively<F: PrimeField>(
    expr: RevealedMulOperandExpr<F>,
) -> RevealedMulOperandExpr<F> {
    match expr {
        RevealedMulOperandExpr::Mul(RevealedMul { left, right }) => {
            let left = Box::new(apply_unary_minus_recursively(*left));
            RevealedMulOperandExpr::Mul(RevealedMul { left, right })
        }
        RevealedMulOperandExpr::UnaryMinus(var_name) => RevealedMulOperandExpr::Var(var_name),
        RevealedMulOperandExpr::Const(c) => RevealedMulOperandExpr::Const(-c),
        RevealedMulOperandExpr::Var(var_name) => RevealedMulOperandExpr::UnaryMinus(var_name),
    }
}

fn reveal_unary_minus<F: PrimeField>(sub_expr: Expr<F>) -> RevealedExpr<F> {
    let sub_expr = reveal(sub_expr);

    match sub_expr {
        RevealedExpr::Add { left, right } => {
            // Replace `-(x + y)` with `(-x) - y`
            let left = Expr::UnaryMinus(Box::new(left.deref().clone().into()));
            let left = reveal(left);
            RevealedExpr::Sub {
                left: Box::new(left),
                right,
            }
        }
        RevealedExpr::Sub { left, right } => {
            // Replace `-(x - y)` with `-x + y`
            let left = Expr::UnaryMinus(Box::new(left.deref().clone().into()));
            let left = reveal(left);
            RevealedExpr::Add {
                left: Box::new(left),
                right,
            }
        }
        RevealedExpr::Mul(RevealedMul { left, right }) => {
            // Replace `-(x * y)` with `-x * y`
            let left = Box::new(apply_unary_minus_recursively(*left));
            RevealedExpr::Mul(RevealedMul { left, right })
        }
        RevealedExpr::UnaryMinus(var_name) => {
            // Replace `-(-x)` with `x`
            RevealedExpr::Var(var_name)
        }
        RevealedExpr::Var(var_name) => RevealedExpr::UnaryMinus(var_name),
        RevealedExpr::Const(c) => {
            // Replace `-(c)` with `-c`
            RevealedExpr::Const(-c)
        }
    }
}

fn reveal_const<F: PrimeField>(c: F) -> RevealedExpr<F> {
    RevealedExpr::Const(c)
}

fn reveal_var<F: PrimeField>(var: VarName) -> RevealedExpr<F> {
    RevealedExpr::Var(var)
}

#[cfg(test)]
mod tests {
    use bls12_381::Scalar;

    use super::*;

    #[test]
    fn test_reveal_smoke() {
        // (-a + b * c) * (d - (e + f)) - g
        let expr = Expr::<Scalar>::Sub {
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
        let expected = RevealedExpr::Sub {
            left: Box::new(RevealedExpr::Add {
                left: Box::new(RevealedExpr::Sub {
                    left: Box::new(RevealedExpr::Mul(RevealedMul {
                        left: Box::new(RevealedMulOperandExpr::UnaryMinus("a".into())),
                        right: Box::new(RevealedMulOperandExpr::Var("d".into())),
                    })),
                    right: Box::new(RevealedExpr::Add {
                        left: Box::new(RevealedExpr::Mul(RevealedMul {
                            left: Box::new(RevealedMulOperandExpr::UnaryMinus("a".into())),
                            right: Box::new(RevealedMulOperandExpr::Var("e".into())),
                        })),
                        right: Box::new(RevealedExpr::Mul(RevealedMul {
                            left: Box::new(RevealedMulOperandExpr::UnaryMinus("a".into())),
                            right: Box::new(RevealedMulOperandExpr::Var("f".into())),
                        })),
                    }),
                }),
                right: Box::new(RevealedExpr::Sub {
                    left: Box::new(RevealedExpr::Mul(RevealedMul {
                        left: Box::new(RevealedMulOperandExpr::Mul(RevealedMul {
                            left: Box::new(RevealedMulOperandExpr::Var("b".into())),
                            right: Box::new(RevealedMulOperandExpr::Var("c".into())),
                        })),
                        right: Box::new(RevealedMulOperandExpr::Var("d".into())),
                    })),
                    right: Box::new(RevealedExpr::Add {
                        left: Box::new(RevealedExpr::Mul(RevealedMul {
                            left: Box::new(RevealedMulOperandExpr::Mul(RevealedMul {
                                left: Box::new(RevealedMulOperandExpr::Var("b".into())),
                                right: Box::new(RevealedMulOperandExpr::Var("c".into())),
                            })),
                            right: Box::new(RevealedMulOperandExpr::Var("e".into())),
                        })),
                        right: Box::new(RevealedExpr::Mul(RevealedMul {
                            left: Box::new(RevealedMulOperandExpr::Mul(RevealedMul {
                                left: Box::new(RevealedMulOperandExpr::Var("b".into())),
                                right: Box::new(RevealedMulOperandExpr::Var("c".into())),
                            })),
                            right: Box::new(RevealedMulOperandExpr::Var("f".into())),
                        })),
                    }),
                }),
            }),
            right: Box::new(RevealedExpr::Var("g".into())),
        };

        let expr = reveal(expr);
        assert_eq!(expr, expected);
    }
}
