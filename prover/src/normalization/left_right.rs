use std::ops::Neg;

use ark_ff::PrimeField;
use circuit::Expr;
use derive_more::Display;

use super::{
    MaybeTwoVarMul, MaybeVarName, MulGenericExpr, Nothing, TwoVarMul, packing::PackedExpr,
};
use crate::normalization::OneVarMul;

/// Normalized left constraint expression with zero or two variable multiplication.
#[derive(Debug, Display, PartialEq, Eq, Clone)]
pub enum LeftExpr<F: PrimeField> {
    #[display("0")]
    Zero,
    Mul(TwoVarMul<F>),
}

impl<F: PrimeField> Neg for LeftExpr<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            LeftExpr::Zero => LeftExpr::Zero,
            LeftExpr::Mul(mul) => LeftExpr::Mul(mul.neg()),
        }
    }
}

impl<F: PrimeField> From<LeftExpr<F>> for Expr<F> {
    fn from(left: LeftExpr<F>) -> Self {
        match left {
            LeftExpr::Zero => Expr::Const(F::ZERO),
            LeftExpr::Mul(TwoVarMul {
                scalar,
                left,
                right,
            }) => Expr::Mul {
                left: Box::new(Expr::Mul {
                    left: Box::new(Expr::Const(scalar)),
                    right: Box::new(Expr::Var(left)),
                }),
                right: Box::new(Expr::Var(right)),
            },
        }
    }
}

/// Normalized right constraint expression where multiplication consist of one variable.
pub type RightExpr<F> = MulGenericExpr<F, OneVarMul<F>>;

impl<F: PrimeField> From<RightExpr<F>> for Expr<F> {
    fn from(right: RightExpr<F>) -> Self {
        match right {
            RightExpr::Add { left, right } => Expr::Add {
                left: Box::new(Expr::from(*left)),
                right: Box::new(Expr::from(*right)),
            },
            RightExpr::Sub { left, right } => Expr::Sub {
                left: Box::new(Expr::from(*left)),
                right: Box::new(Expr::from(*right)),
            },
            RightExpr::Const(c) => Expr::Const(c),
            RightExpr::Var(var_name) => Expr::Var(var_name),
            RightExpr::UnaryMinus(var_name) => Expr::UnaryMinus(Box::new(Expr::Var(var_name))),
            RightExpr::Mul(OneVarMul {
                scalar,
                left,
                right: Nothing,
            }) => Expr::Mul {
                left: Box::new(Expr::Const(scalar)),
                right: Box::new(Expr::Var(left)),
            },
        }
    }
}

pub fn move_right_to_left<F: PrimeField>(left: &mut Expr<F>, right: &mut Expr<F>) {
    let l = std::mem::replace(left, Expr::Const(F::ZERO));
    let r = std::mem::replace(right, Expr::Const(F::ZERO));
    *left = Expr::Sub {
        left: Box::new(l),
        right: Box::new(r),
    };
}

pub fn move_non_var_multiplications_to_right<F: PrimeField>(
    left: PackedExpr<F>,
    right: &mut RightExpr<F>,
    is_positive: bool,
) -> LeftExpr<F> {
    match left {
        PackedExpr::Add { left: l, right: r } => {
            let l = move_non_var_multiplications_to_right(*l, right, is_positive);
            let r = move_non_var_multiplications_to_right(*r, right, is_positive);
            match (l, r) {
                (LeftExpr::Zero, r) => r,
                (l, LeftExpr::Zero) => l,
                (LeftExpr::Mul(_), LeftExpr::Mul(_)) => {
                    panic!(
                        "there should be no two variable multiplications after variable multiplication packing"
                    );
                }
            }
        }
        PackedExpr::Sub { left: l, right: r } => {
            let l = move_non_var_multiplications_to_right(*l, right, is_positive);
            let r = move_non_var_multiplications_to_right(*r, right, !is_positive);
            match (l, r) {
                (LeftExpr::Zero, r) => -r,
                (l, LeftExpr::Zero) => l,
                (LeftExpr::Mul(_), LeftExpr::Mul(_)) => {
                    panic!(
                        "there should be no two variable multiplications after variable multiplication packing"
                    );
                }
            }
        }
        PackedExpr::Mul(MaybeTwoVarMul {
            scalar,
            left: l,
            right: r,
        }) => {
            let sign = if is_positive { F::ONE } else { -F::ONE };
            let scalar = scalar * sign;

            if let MaybeVarName::VarName(r) = r {
                // Main case, leaving as is
                LeftExpr::Mul(TwoVarMul {
                    scalar,
                    left: l,
                    right: r,
                })
            } else {
                *right = right.take()
                    - RightExpr::Mul(OneVarMul {
                        scalar,
                        left: l,
                        right: Nothing,
                    });

                LeftExpr::Zero
            }
        }
        PackedExpr::UnaryMinus(var) => {
            let var_expr = PackedExpr::Var(var);
            move_non_var_multiplications_to_right(var_expr, right, !is_positive)
        }
        PackedExpr::Const(c) => {
            if is_positive {
                *right = right.take() - RightExpr::Const(c);
            } else {
                *right = right.take() + RightExpr::Const(c);
            }

            LeftExpr::Zero
        }
        PackedExpr::Var(var_name) => {
            if is_positive {
                *right = right.take() - RightExpr::Var(var_name);
            } else {
                *right = right.take() + RightExpr::Var(var_name);
            }

            LeftExpr::Zero
        }
    }
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::Fq;
    use ark_ff::AdditiveGroup as _;

    use super::*;

    #[test]
    fn test_move_non_var_multiplications_to_right_smoke() {
        // -2 * a * b + d - 3 * f + 4
        let left = PackedExpr::<Fq>::Add {
            left: Box::new(PackedExpr::Add {
                left: Box::new(PackedExpr::Mul(MaybeTwoVarMul {
                    scalar: Fq::from(-2),
                    left: "a".into(),
                    right: MaybeVarName::VarName("b".into()),
                })),
                right: Box::new(PackedExpr::Sub {
                    left: Box::new(PackedExpr::Var("d".into())),
                    right: Box::new(PackedExpr::Mul(MaybeTwoVarMul {
                        scalar: 3.into(),
                        left: "f".into(),
                        right: MaybeVarName::None,
                    })),
                }),
            }),
            right: Box::new(PackedExpr::Const(Fq::from(4))),
        };
        let mut right = RightExpr::Const(Fq::ZERO);

        // -2 * a * b
        let expected_left = LeftExpr::Mul(TwoVarMul {
            scalar: Fq::from(-2),
            left: "a".into(),
            right: "b".into(),
        });

        // (-d) + 3 * f - 4
        let expected_right = RightExpr::Sub {
            left: Box::new(RightExpr::Sub {
                left: Box::new(RightExpr::UnaryMinus("d".into())),
                right: Box::new(RightExpr::Mul(OneVarMul {
                    scalar: Fq::from(-3),
                    left: "f".into(),
                    right: Nothing,
                })),
            }),
            right: Box::new(RightExpr::Const(Fq::from(4))),
        };

        let left = move_non_var_multiplications_to_right(left, &mut right, true);

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
