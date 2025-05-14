//! Rank One Constraint System (R1CS) utilities.

use circuit::Circuit;

/// Rank One Constraint System.
pub struct R1cs {}

impl From<Circuit> for R1cs {
    fn from(_circuit: Circuit) -> Self {
        todo!()
    }
}
