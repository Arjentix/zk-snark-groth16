//! Rank One Constraint System (R1CS) utilities.

use circuit::{Circuit, ScopedVar, VarName};
use derive_more::Display;
use ff::PrimeField;
use indexmap::IndexSet;
use itertools::Itertools as _;
use logger::info;
use normalization::{LeftExpr, NormalizedCircuit, NormalizedConstraint};

use crate::r1cs::normalization::RightExpr;

mod normalization;

type Matrix<F> = ndarray::Array2<F>;

/// Rank One Constraint System.
///
/// Contains L, R, and O (`La * Ra = Oa`, where `a` -- witness vector) matrices which have meaning
/// only with the corresponding [`WitnessSchema`].
#[derive(Debug, Display)]
#[display("L: {left},\nR: {right},\nO: {output}")]
pub struct R1cs<F: PrimeField> {
    left: Matrix<F>,
    right: Matrix<F>,
    output: Matrix<F>,
}

pub struct WitnessSchema<F: PrimeField> {
    /// Scalar multiplier always equal to 1.
    pub one: F,
    /// Schema variables where all public variables go first.
    pub vars: IndexSet<ScopedVar>,
}

/// Derives a R1CS and witness schema from a given circuit.
pub fn derive<F: PrimeField + std::fmt::Display>(
    circuit: Circuit<F>,
) -> (R1cs<F>, WitnessSchema<F>) {
    let circuit = NormalizedCircuit::normalize(circuit);
    info!(circuit = %circuit, "normalized circuit");

    let schema = WitnessSchema::from_circuit_vars(circuit.vars);
    info!(schema = %schema, "witness schema");

    let r1cs = derive_from_normalized(&circuit.constraints, &schema);
    info!(r1cs = %r1cs, "R1CS");
    (r1cs, schema)
}

impl<F: PrimeField> WitnessSchema<F> {
    fn from_circuit_vars(vars: IndexSet<ScopedVar>) -> Self {
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
    fn len(&self) -> usize {
        self.vars.len() + 1 // +1 for the scalar multiplier
    }

    /// Returns the index of the variable in the schema.
    fn index_of(&self, var: Option<&VarName>) -> Option<usize> {
        // Technically could be faster with a hashmap, but this is simpler and
        // the number of variables is usually very small.

        let Some(var) = var else {
            return Some(0); // 0 is the index of the scalar multiplier
        };

        self.vars
            .iter()
            .position(|v| v.name() == var)
            .map(|i| i + 1) // +1 for the scalar multiplier
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

fn derive_from_normalized<F: PrimeField>(
    constraints: &[NormalizedConstraint<F>],
    schema: &WitnessSchema<F>,
) -> R1cs<F> {
    let schema_len = schema.len();
    let constraints_count = constraints.len();

    let zeroed = R1cs {
        left: Matrix::from_elem((constraints_count, schema_len), F::ZERO),
        right: Matrix::from_elem((constraints_count, schema_len), F::ZERO),
        output: Matrix::from_elem((constraints_count, schema_len), F::ZERO),
    };

    constraints.iter().fold(zeroed, |mut r1cs, constraint| {
        fill_l_r_matrices(&constraint.left, schema, &mut r1cs.left, &mut r1cs.right);
        fill_o_matrix_recursively(&constraint.right, schema, true, &mut r1cs.output);
        r1cs
    })
}

fn fill_l_r_matrices<F: PrimeField>(
    expr: &LeftExpr<F>,
    schema: &WitnessSchema<F>,
    left: &mut Matrix<F>,
    right: &mut Matrix<F>,
) {
    todo!()
}

fn fill_o_matrix_recursively<F: PrimeField>(
    expr: &RightExpr<F>,
    schema: &WitnessSchema<F>,
    is_positive: bool,
    output: &mut Matrix<F>,
) {
    todo!()
}
