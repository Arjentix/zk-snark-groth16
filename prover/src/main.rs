use std::net::SocketAddr;

use circuit::circuit;
use eyre::{Context as _, Result};
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

    let circuit = circuit! {
        -3.0*x*x*y + 5.0*x*y - (x - 2.0)*y + 3.0 == a;
        2.0*x + y == b - 5.0;
    };
    let r1cs = R1cs::from(circuit);
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
