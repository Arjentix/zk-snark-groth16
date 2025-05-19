use std::net::SocketAddr;

use eyre::{Context as _, Result};
use network::Network;

#[tokio::main]
async fn main() -> Result<()> {
    logger::init_logger().wrap_err("failed to initialize logger")?;

    let mut network = Network::establish(
        SocketAddr::from(([127, 0, 0, 1], 1032)),
        [
            SocketAddr::from(([127, 0, 0, 1], 1031)),
            SocketAddr::from(([127, 0, 0, 1], 1033)),
        ]
        .as_slice(),
    )
    .await
    .wrap_err("failed to establish network")?;

    let _publish_circuit: protocol::PublishCircuit = network
        .recv()
        .await
        .wrap_err("failed to receive `PublishCircuit` message")?;

    network
        .broadcast(protocol::TrustedSetupOutput {})
        .await
        .wrap_err("failed to broadcast `TrustedSetupOutput` message")?;

    Ok(())
}
