//! Protocol types.

use serde::{Deserialize, Serialize};

/// Circuit, published by *prover* and that *prover* claims to have solution for.
#[derive(Debug, Deserialize, Serialize)]
pub struct PublishCircuit {}

/// Output from *trusted setup* generated for a circuit.
#[derive(Debug, Deserialize, Serialize)]
pub struct TrustedSetupOutput {}

/// A Zero Knowledge Proof of having a solution for a circuit.
#[derive(Debug, Deserialize, Serialize)]
pub struct Proof {}
