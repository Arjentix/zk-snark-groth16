use std::collections::BTreeMap;

use circuit::VarName;
use ff::PrimeField;

use super::{MaybeTwoVarMul, MaybeVarName, packing::PackedExpr};

/// Sums terms in the expression.
///
/// # Example
///
/// ```text
/// 2 * a + 3 * a - a => 4 * a
/// ```
pub fn sum_terms<F: PrimeField>(expr: &mut PackedExpr<F>) {
    let mut terms = BTreeMap::new();
    sum_terms_recursively(expr, &mut terms, true);

    let mut new_expr = None;
    for (term, const_factor) in terms {
        if const_factor == F::ZERO {
            continue;
        }

        let term_expr = if let Some(term) = term {
            let mul = MaybeTwoVarMul::sorted(const_factor, term.left, term.right);
            mul.simplified()
        } else {
            PackedExpr::Const(const_factor)
        };

        if let Some(existing_expr) = new_expr {
            new_expr = Some(PackedExpr::Add {
                left: Box::new(existing_expr),
                right: Box::new(term_expr),
            });
        } else {
            new_expr = Some(term_expr);
        }
    }

    *expr = new_expr.unwrap_or(PackedExpr::zero());
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Term {
    left: VarName,
    right: MaybeVarName,
}

impl Term {
    pub fn sorted(left: VarName, right: MaybeVarName) -> Self {
        if let MaybeVarName::VarName(var_name) = &right {
            if left > *var_name {
                return Self {
                    left: var_name.clone(),
                    right: MaybeVarName::VarName(left),
                };
            }
        }

        Self { left, right }
    }

    pub fn into_raw_parts(self) -> (VarName, MaybeVarName) {
        (self.left, self.right)
    }
}

fn sum_terms_recursively<F: PrimeField>(
    expr: &PackedExpr<F>,
    terms: &mut BTreeMap<Option<Term>, F>,
    is_positive: bool,
) {
    match expr {
        PackedExpr::Add { left, right } => {
            sum_terms_recursively(left, terms, is_positive);
            sum_terms_recursively(right, terms, is_positive);
        }
        PackedExpr::Sub { left, right } => {
            sum_terms_recursively(left, terms, is_positive);
            sum_terms_recursively(right, terms, !is_positive);
        }
        PackedExpr::Mul(mul) => {
            let sign = if is_positive { F::ONE } else { -F::ONE };
            *terms
                .entry(Some(Term::sorted(mul.left.clone(), mul.right.clone())))
                .or_default() += mul.scalar * sign;
        }
        PackedExpr::UnaryMinus(var) => {
            let sign = if is_positive { -F::ONE } else { F::ONE };
            *terms
                .entry(Some(Term::sorted(var.clone(), MaybeVarName::None)))
                .or_default() += sign;
        }
        PackedExpr::Var(var) => {
            let sign = if is_positive { F::ONE } else { -F::ONE };
            *terms
                .entry(Some(Term::sorted(var.clone(), MaybeVarName::None)))
                .or_default() += sign;
        }
        PackedExpr::Const(c) => {
            let sign = if is_positive { F::ONE } else { -F::ONE };
            *terms.entry(None).or_default() += sign * (*c);
        }
    }
}

#[cfg(test)]
mod tests {
    use bls12_381::Scalar;

    use super::*;

    #[test]
    fn test_sum_terms_smoke() {
        // 2 * a * b + 3 * b * a - a
        let mut expr = PackedExpr::<Scalar>::Add {
            left: Box::new(PackedExpr::Mul(MaybeTwoVarMul {
                scalar: 2.into(),
                left: "a".into(),
                right: MaybeVarName::VarName("b".into()),
            })),
            right: Box::new(PackedExpr::Sub {
                left: Box::new(PackedExpr::Mul(MaybeTwoVarMul {
                    scalar: 3.into(),
                    left: "b".into(),
                    right: MaybeVarName::VarName("a".into()),
                })),
                right: Box::new(PackedExpr::Mul(MaybeTwoVarMul {
                    scalar: 1.into(),
                    left: "a".into(),
                    right: MaybeVarName::None,
                })),
            }),
        };

        // - a + 5 * a * b
        let expected = PackedExpr::Add {
            left: Box::new(PackedExpr::UnaryMinus("a".into())),
            right: Box::new(PackedExpr::Mul(MaybeTwoVarMul {
                scalar: 5.into(),
                left: "a".into(),
                right: MaybeVarName::VarName("b".into()),
            })),
        };

        sum_terms(&mut expr);
        assert_eq!(expr, expected, "expected: {expected}, got: {expr}");
    }
}
