use std::net::SocketAddr;

use eyre::{Context as _, Result};

use network::Network;

#[tokio::main]
async fn main() -> Result<()> {
    logger::init_logger().wrap_err("failed to initialize logger")?;

    let mut network = Network::establish(
        SocketAddr::from(([127, 0, 0, 1], 1033)),
        [
            SocketAddr::from(([127, 0, 0, 1], 1031)),
            SocketAddr::from(([127, 0, 0, 1], 1032)),
        ]
        .as_slice(),
    )
    .await
    .wrap_err("failed to establish network")?;

    let _publish_circuit: protocol::PublishCircuit = network
        .recv()
        .await
        .wrap_err("failed to receive `PublishCircuit` message")?;

    let _trusted_setup_output: protocol::TrustedSetupOutput = network
        .recv()
        .await
        .wrap_err("failed to receive `TrustedSetupOutput` message")?;

    let _proof: protocol::Proof = network
        .recv()
        .await
        .wrap_err("failed to receive `Proof` message")?;

    Ok(())
}
