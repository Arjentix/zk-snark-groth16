use std::net::SocketAddr;

use circuit::{Circuit, circuit};
use eyre::{Context as _, Result};
use logger::info;
use network::Network;
use prover::{qap::Qap, r1cs};

#[tokio::main]
async fn main() -> Result<()> {
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

    let circuit: Circuit<bls12_381::Scalar> = circuit!(|pub a, pub b, x, y| {
        -3*x*x*y + 5*x*y - (x - 2)*y + 3 == a;
        2*x + y == b - 5;
    });
    info!(circuit = %circuit, "input circuit");
    let (r1cs, _witness_schema) = r1cs::derive(circuit);
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
