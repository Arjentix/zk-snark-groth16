//! Rank One Constraint System (R1CS) utilities.

use std::collections::HashMap;

use ark_ff::PrimeField;
use circuit::{ScopedVar, VarName};
use derive_more::Display;
use eyre::{ContextCompat as _, Result};
use indexmap::IndexSet;
use itertools::Itertools as _;

use crate::normalization::{
    LeftExpr, MulGenericExpr, NormalizedCircuit, Nothing, OneVarMul, RightExpr,
};

type Matrix<F> = ndarray::Array2<F>;
type Row<F> = ndarray::Array1<F>;

/// Rank One Constraint System.
///
/// Contains L, R, and O matrices (`La * Ra = Oa`, where `a` -- witness vector) which have meaning
/// only with the corresponding [`WitnessSchema`].
#[derive(Debug, Display)]
#[display("L: {left},\nR: {right},\nO: {output}")]
pub struct R1cs<F: PrimeField> {
    left: Matrix<F>,
    right: Matrix<F>,
    output: Matrix<F>,
}

impl<F: PrimeField> R1cs<F> {
    /// Derives the [`R1CS`](R1cs) from circuit and witness schema.
    pub fn from_normalized(circuit: &NormalizedCircuit<F>, schema: &WitnessSchema<F>) -> R1cs<F> {
        let schema_len = schema.len();
        let shape = (0, schema_len);

        let empty = R1cs {
            left: Matrix::default(shape),
            right: Matrix::default(shape),
            output: Matrix::default(shape),
        };

        circuit
            .constraints
            .iter()
            .fold(empty, |mut r1cs, constraint| {
                let (left_row, right_row) = produce_l_r_rows(&constraint.left, schema);
                r1cs.left.push_row(left_row.view()).expect(
                    "L matrix row length doesn't match L matrix expectation, this is a bug",
                );
                r1cs.right.push_row(right_row.view()).expect(
                    "R matrix row length doesn't match R matrix expectation, this is a bug",
                );

                let o_row = produce_o_row(&constraint.right, schema);
                r1cs.output.push_row(o_row.view()).expect(
                    "O matrix row length doesn't match O matrix expectation, this is a bug",
                );

                r1cs
            })
    }

    pub fn is_satisfied(&self, witness: &[F]) -> bool {
        let witness = ndarray::arr1(witness);

        let left_product = self.left.dot(&witness);
        let right_product = self.right.dot(&witness);
        let output_product = self.output.dot(&witness);

        left_product * right_product == output_product
    }
}

pub struct WitnessSchema<F: PrimeField> {
    /// Scalar multiplier always equal to 1.
    one: F,
    /// Schema variables where all public variables go first.
    vars: IndexSet<ScopedVar>,
}

impl<F: PrimeField> WitnessSchema<F> {
    pub fn from_circuit_vars(vars: IndexSet<ScopedVar>) -> Self {
        #[cfg(debug_assertions)]
        {
            let mut prev_was_private = false;
            for var in &vars {
                match var {
                    ScopedVar::Public(_) => {
                        if prev_was_private {
                            panic!("public variable cannot follow private variable");
                        }
                    }
                    ScopedVar::Private(_) => {
                        prev_was_private = true;
                    }
                }
            }
        }

        Self { one: F::ONE, vars }
    }

    /// Returns the number of variables in the schema.
    #[expect(
        clippy::len_without_is_empty,
        reason = "is_empty doesn't make sense for witness schema"
    )]
    pub fn len(&self) -> usize {
        self.vars.len() + 1 // +1 for the scalar multiplier
    }

    /// Returns the index of the variable in the schema.
    pub fn index_of(&self, elem: ScalarOrVarName<'_>) -> Option<usize> {
        // Technically could be faster with a hashmap, but this is simpler and
        // the number of variables is usually very small.

        let var = match elem {
            ScalarOrVarName::Scalar => return Some(0),
            ScalarOrVarName::VarName(var) => var,
        };

        self.vars
            .iter()
            .position(|v| v.name() == var)
            .map(|i| i + 1) // +1 for the scalar multiplier
    }

    pub fn construct_witness(&self, vars: HashMap<VarName, F>) -> Result<Vec<F>> {
        std::iter::once(Ok(self.one))
            .chain(self.vars.iter().map(|var| {
                vars.get(var.name())
                    .copied()
                    .wrap_err_with(|| format!("missing value for variable `{}`", var.name()))
            }))
            .collect()
    }
}

impl<F: PrimeField + std::fmt::Display> std::fmt::Display for WitnessSchema<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;

        std::iter::once(self.one.to_string())
            .chain(self.vars.iter().map(|var| var.name().to_string()))
            .format_with(",", |s, f| f(&format_args!("{s}")))
            .fmt(f)?;

        write!(f, "]")?;

        Ok(())
    }
}

pub enum ScalarOrVarName<'name> {
    Scalar,
    VarName(&'name VarName),
}

fn produce_l_r_rows<F: PrimeField>(
    expr: &LeftExpr<F>,
    schema: &WitnessSchema<F>,
) -> (Row<F>, Row<F>) {
    let shape = schema.len();

    let mut left = Row::from_elem(shape, F::ZERO);
    let mut right = Row::from_elem(shape, F::ZERO);

    let var_mul = match expr {
        LeftExpr::Mul(var_mul) => var_mul,
        LeftExpr::Zero => return (left, right),
    };

    let index_of_left_var = schema
        .index_of(ScalarOrVarName::VarName(&var_mul.left))
        .unwrap_or_else(|| {
            panic!(
                "failed to get witness schema index of `{}` variable, this is a bug",
                var_mul.left
            )
        });
    left[index_of_left_var] = var_mul.scalar;

    let index_of_right_var = schema
        .index_of(ScalarOrVarName::VarName(&var_mul.right))
        .unwrap_or_else(|| {
            panic!(
                "failed to get witness schema index of `{}` variable, this is a bug",
                var_mul.right
            )
        });
    right[index_of_right_var] = F::ONE;

    (left, right)
}

fn produce_o_row<F: PrimeField>(expr: &RightExpr<F>, schema: &WitnessSchema<F>) -> Row<F> {
    let shape = schema.len();

    let mut row = Row::from_elem(shape, F::ZERO);

    fn produce_o_row_recursively<F: PrimeField>(
        expr: &RightExpr<F>,
        schema: &WitnessSchema<F>,
        is_positive: bool,
        row: &mut Row<F>,
    ) {
        let sign = if is_positive { F::ONE } else { -F::ONE };

        match expr {
            MulGenericExpr::Add { left, right } => {
                produce_o_row_recursively(left, schema, is_positive, row);
                produce_o_row_recursively(right, schema, is_positive, row);
            }
            MulGenericExpr::Sub { left, right } => {
                produce_o_row_recursively(left, schema, is_positive, row);
                produce_o_row_recursively(right, schema, !is_positive, row);
            }
            MulGenericExpr::Mul(mul) => {
                let OneVarMul {
                    scalar,
                    left,
                    right: Nothing,
                } = mul;
                let index_of_var = schema
                .index_of(ScalarOrVarName::VarName(left))
                .unwrap_or_else(|| {
                    panic!(
                        "failed to get witness schema index of `{left}` variable, this is a bug",
                    )
                });
                row[index_of_var] = *scalar * sign;
            }
            MulGenericExpr::UnaryMinus(var) => {
                let index_of_var = schema
                    .index_of(ScalarOrVarName::VarName(var))
                    .unwrap_or_else(|| {
                        panic!(
                            "failed to get witness schema index of `{var}` variable, this is a bug",
                        )
                    });
                assert_eq!(
                    row[index_of_var],
                    F::ZERO,
                    "malformed normalized expression, variable `{var}` is not normalized, this is a bug"
                );
                row[index_of_var] = -F::ONE * sign;
            }
            MulGenericExpr::Const(scalar) => {
                let index_of_scalar = schema
                    .index_of(ScalarOrVarName::Scalar)
                    .expect("index of scalar should always persist");
                assert_eq!(
                    row[index_of_scalar],
                    F::ZERO,
                    "malformed normalized expression, scalar is not normalized, this is a bug"
                );
                row[index_of_scalar] = *scalar * sign;
            }
            MulGenericExpr::Var(var) => {
                let index_of_var = schema
                    .index_of(ScalarOrVarName::VarName(var))
                    .unwrap_or_else(|| {
                        panic!(
                            "failed to get witness schema index of `{var}` variable, this is a bug",
                        )
                    });
                assert_eq!(
                    row[index_of_var],
                    F::ZERO,
                    "malformed normalized expression, variable `{var}` is not normalized, this is a bug"
                );
                row[index_of_var] = sign;
            }
        }
    }

    produce_o_row_recursively(expr, schema, true, &mut row);

    row
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::Fq;
    use ark_ff::{AdditiveGroup as _, Field as _};

    use super::*;
    use crate::normalization::{OneVarMul, VarMul};

    #[test]
    fn test_produce_l_r_rows_smoke() {
        let expr = LeftExpr::Mul(VarMul {
            scalar: Fq::from(5),
            left: "a".into(),
            right: "b".into(),
        });
        let schema = WitnessSchema::from_circuit_vars(
            [
                ScopedVar::Private("a".into()),
                ScopedVar::Private("b".into()),
            ]
            .into(),
        );

        let expected_left = Row::from_iter([Fq::ZERO, Fq::from(5), Fq::ZERO]);
        let expected_right = Row::from_iter([Fq::ZERO, Fq::ZERO, Fq::ONE]);

        let (left_row, right_row) = produce_l_r_rows(&expr, &schema);
        assert_eq!(
            left_row, expected_left,
            "expected: {expected_left}, got: {left_row}"
        );
        assert_eq!(
            right_row, expected_right,
            "expected: {expected_right}, got: {right_row}"
        );
    }

    #[test]
    fn test_produce_o_row_smoke() {
        // -3 * a + 8
        let expr = RightExpr::Add {
            left: Box::new(RightExpr::Mul(OneVarMul {
                scalar: Fq::from(-3),
                left: "a".into(),
                right: Nothing,
            })),
            right: Box::new(RightExpr::Const(Fq::from(8))),
        };
        let schema = WitnessSchema::from_circuit_vars([ScopedVar::Private("a".into())].into());

        let expected_row = Row::from_iter([Fq::from(8), Fq::from(-3)]);

        let row = produce_o_row(&expr, &schema);
        assert_eq!(row, expected_row, "expected: {expected_row}, got: {row}")
    }
}
