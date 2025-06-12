//! Quadratic Arithmetic Program (QAP) utilities.

use ff::PrimeField;

use crate::r1cs::R1cs;

/// Quadratic Arithmetic Program.
pub struct Qap {}

impl<F: PrimeField> From<R1cs<F>> for Qap {
    fn from(_r1cs: R1cs<F>) -> Self {
        todo!()
    }
}
