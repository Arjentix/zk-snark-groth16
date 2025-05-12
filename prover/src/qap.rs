//! Quadratic Arithmetic Program (QAP) utilities.

use crate::r1cs::R1cs;

/// Quadratic Arithmetic Program.
pub struct Qap {}

impl From<R1cs> for Qap {
    fn from(_r1cs: R1cs) -> Self {
        todo!()
    }
}
