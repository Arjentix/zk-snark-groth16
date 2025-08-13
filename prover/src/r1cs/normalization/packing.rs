use std::hash::{BuildHasher as _, Hash as _, Hasher as _};

use circuit::{ScopedVar, VarName};
use ff::PrimeField;
use indexmap::IndexSet;
use sorted_vec::SortedVec;

use super::{
    MaybeTwoVarMul, MaybeVarName, MulGenericExpr, NormalizedConstraint, TwoVarMul,
    brackets_reveal::{RevealedExpr, RevealedMul, RevealedMulOperandExpr},
    left_right::{LeftExpr, RightExpr},
};

/// Intermediate expression where multiplication contains one or two variables.
pub type PackedExpr<F> = MulGenericExpr<F, MaybeTwoVarMul<F>>;

/// Packs each variable multiplication into a new variable and places it as constraint.
///
/// # Example
///
/// ```text
///              [ v = a*b
/// a*b*c = 0 => |
///              [ v*c = 0
/// ```
pub fn pack_var_multiplications<F: PrimeField>(
    var_names: &IndexSet<ScopedVar>,
    expr: RevealedExpr<F>,
    new_constraints: &mut Vec<NormalizedConstraint<F>>,
    new_var_names: &mut IndexSet<VarName>,
    var_multiplication_set: &mut bool,
) -> PackedExpr<F> {
    match expr {
        RevealedExpr::Add { left, right } => {
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

            PackedExpr::Add {
                left: Box::new(left_normalized),
                right: Box::new(right_normalized),
            }
        }
        RevealedExpr::Sub { left, right } => {
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

            PackedExpr::Sub {
                left: Box::new(left_normalized),
                right: Box::new(right_normalized),
            }
        }
        RevealedExpr::Mul(RevealedMul { left, right }) => {
            let mut found_vars = SortedVec::new();
            let mut const_factor = F::ONE;
            find_factors(&left, &mut found_vars, &mut const_factor);
            find_factors(&right, &mut found_vars, &mut const_factor);

            let mul = loop {
                match found_vars.len() {
                    0 => {
                        break None;
                    }
                    1 => {
                        break Some(MaybeTwoVarMul::sorted(
                            const_factor,
                            found_vars
                                .pop()
                                .unwrap_or_else(|| unreachable!("checked length = 1")),
                            MaybeVarName::None,
                        ));
                    }
                    2 if !*var_multiplication_set => {
                        *var_multiplication_set = true;
                        break Some(MaybeTwoVarMul::sorted(
                            const_factor,
                            found_vars
                                .pop()
                                .unwrap_or_else(|| unreachable!("checked length = 2")),
                            MaybeVarName::VarName(
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
                                left: LeftExpr::Mul(TwoVarMul::sorted(F::ONE, var1, var2)),
                                right: RightExpr::Var(new_var.clone()),
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

            if let Some(mul) = mul {
                mul.simplified()
            } else {
                PackedExpr::Const(const_factor)
            }
        }
        RevealedExpr::UnaryMinus(var_name) => PackedExpr::UnaryMinus(var_name),
        RevealedExpr::Const(c) => PackedExpr::Const(c),
        RevealedExpr::Var(v) => PackedExpr::Var(v),
    }
}

fn find_factors<F: PrimeField>(
    mul: &RevealedMulOperandExpr<F>,
    found_vars: &mut SortedVec<VarName>,
    const_factor: &mut F,
) {
    match mul {
        RevealedMulOperandExpr::Mul(RevealedMul { left, right }) => {
            find_factors(left, found_vars, const_factor);
            find_factors(right, found_vars, const_factor);
        }
        RevealedMulOperandExpr::UnaryMinus(var_name) => {
            found_vars.push(var_name.clone());
            *const_factor = -(*const_factor);
        }
        RevealedMulOperandExpr::Var(var_name) => {
            found_vars.push(var_name.clone());
        }
        RevealedMulOperandExpr::Const(c) => {
            *const_factor *= c;
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

#[cfg(test)]
mod tests {
    use bls12_381::Scalar;
    use regex::Regex;

    use super::*;

    #[test]
    fn test_pack_var_multiplications_smoke() {
        let var_names = IndexSet::from_iter([
            ScopedVar::Public("a".into()),
            ScopedVar::Private("b".into()),
            ScopedVar::Private("c".into()),
            ScopedVar::Private("d".into()),
        ]);
        // (((-2 * (a * (b * c))) + (a * (b * d))) - ((-b * d) - (3 * d)))
        let expr = RevealedExpr::<Scalar>::Sub {
            left: Box::new(RevealedExpr::Add {
                left: Box::new(RevealedExpr::Mul(RevealedMul {
                    left: Box::new(RevealedMulOperandExpr::Const(-Scalar::from(2))),
                    right: Box::new(RevealedMulOperandExpr::Mul(RevealedMul {
                        left: Box::new(RevealedMulOperandExpr::Var("a".into())),
                        right: Box::new(RevealedMulOperandExpr::Mul(RevealedMul {
                            left: Box::new(RevealedMulOperandExpr::Var("b".into())),
                            right: Box::new(RevealedMulOperandExpr::Var("c".into())),
                        })),
                    })),
                })),
                right: Box::new(RevealedExpr::Mul(RevealedMul {
                    left: Box::new(RevealedMulOperandExpr::Var("a".into())),
                    right: Box::new(RevealedMulOperandExpr::Mul(RevealedMul {
                        left: Box::new(RevealedMulOperandExpr::Var("b".into())),
                        right: Box::new(RevealedMulOperandExpr::Var("d".into())),
                    })),
                })),
            }),
            right: Box::new(RevealedExpr::Sub {
                left: Box::new(RevealedExpr::Mul(RevealedMul {
                    left: Box::new(RevealedMulOperandExpr::UnaryMinus("b".into())),
                    right: Box::new(RevealedMulOperandExpr::Var("d".into())),
                })),
                right: Box::new(RevealedExpr::Mul(RevealedMul {
                    left: Box::new(RevealedMulOperandExpr::Const(Scalar::from(3))),
                    right: Box::new(RevealedMulOperandExpr::Var("d".into())),
                })),
            }),
        };
        let mut new_constraints = Vec::new();
        let mut new_var_names = IndexSet::new();

        let packed = pack_var_multiplications(
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
        let normalized = packed.to_string();
        assert!(
            regex.is_match(&normalized),
            "{normalized} does not match {regex}"
        );
        assert_eq!(new_constraints.len(), 3);
    }
}
