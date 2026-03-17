use std::{collections::HashMap, net::SocketAddr};

use bls12_381::Scalar;
use circuit::{Circuit, circuit};
use eyre::{Context as _, Result};
use logger::info;
use network::Network;
use prover::{
    normalization::NormalizedCircuit,
    qap::Qap,
    r1cs::{R1cs, WitnessSchema},
};

#[tokio::main]
async fn main() -> Result<()> {
    // Setup

    logger::init_logger().wrap_err("failed to initialize logger")?;

    let mut network = Network::establish(
        SocketAddr::from(([127, 0, 0, 1], 1031)),
        [
            SocketAddr::from(([127, 0, 0, 1], 1032)),
            SocketAddr::from(([127, 0, 0, 1], 1033)),
        ]
        .as_slice(),
    )
    .await
    .wrap_err("failed to establish network")?;

    // Circuit

    let circuit: Circuit<Scalar> = circuit!(|pub a, pub b, x, y| {
        -3*x*x*y + 5*x*y - (x - 2)*y + 3 == a;
        2*x + y == b - 5;
    });
    info!(circuit = %circuit, "input circuit");

    let normalized_circuit = NormalizedCircuit::normalize(circuit);
    info!(circuit = %normalized_circuit, "normalized circuit");

    let schema = WitnessSchema::from_circuit_vars(normalized_circuit.vars.clone());
    info!(schema = %schema, "witness schema");

    // Witness

    let x = 3.into();
    let y = 5.into();
    let computed_vars = normalized_circuit
        .clone()
        .compute(HashMap::from([("x".into(), x), ("y".into(), y)]));
    let a = -Scalar::from(3) * x * x * y + 5.into() * x * y - (x - 2.into()) * y + 3.into();
    let b = Scalar::from(2) * x + y + 5.into();
    assert_eq!(computed_vars.get("a"), Some(&a));
    assert_eq!(computed_vars.get("b"), Some(&b));
    let witness = schema.construct_witness(computed_vars)?;

    // R1CS

    let r1cs = R1cs::from_normalized(&normalized_circuit, &schema);
    info!(r1cs = %r1cs, "R1CS");
    assert!(
        r1cs.is_satisfied(&witness),
        "witness does not satisfy the R1CS constraints"
    );

    // QAP

    let _qap = Qap::from(r1cs);

    network
        .broadcast(protocol::PublishCircuit {})
        .await
        .wrap_err("failed to broadcast `PublishCircuit` message")?;

    let _trusted_setup_output: protocol::TrustedSetupOutput = network
        .recv()
        .await
        .wrap_err("failed to receive `TrustedSetupOutput` message")?;

    network
        .broadcast(protocol::Proof {})
        .await
        .wrap_err("failed to broadcast `Proof` message")?;

    Ok(())
}
