use std::net::SocketAddr;

use circuit_macro::circuit;
use eyre::{Context as _, Result};

use network::Network;

use prover::{qap::Qap, r1cs::R1cs};

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

    // Circuit::new()
    //     .add_constraint(
    //         Expression::Plus {
    //             left: Box::new(Expression::Minus {
    //                 left: Box::new(Expression::Minus {
    //                     left: Box::new(Expression::Plus {
    //                         left: Box::new(Expression::Multiply {
    //                             left: Box::new(Expression::Multiply {
    //                                 left: Box::new(Expression::Multiply {
    //                                     left: Box::new(Expression::Constant(3.0)),
    //                                     right: Box::new(Expression::Variable("x")),
    //                                 }),
    //                                 right: Box::new(Expression::Variable("x")),
    //                             }),
    //                             right: Box::new(Expression::Variable("y")),
    //                         }),
    //                         right: Box::new(Expression::Multiply {
    //                             left: Box::new(Expression::Multiply {
    //                                 left: Box::new(Expression::Constant(5.0)),
    //                                 right: Box::new(Expression::Variable("x")),
    //                             }),
    //                             right: Box::new(Expression::Variable("y")),
    //                         }),
    //                     }),
    //                     right: Box::new(Expression::Variable("x")),
    //                 }),
    //                 right: Box::new(Expression::Multiply {
    //                     left: Box::new(Expression::Constant(2.0)),
    //                     right: Box::new(Expression::Variable("y")),
    //                 }),
    //             }),
    //             right: Box::new(Expression::Constant(3.0)),
    //         },
    //         Expression::Variable("a"),
    //     )
    //     .add_constraint(
    //         Expression::Plus {
    //             left: Box::new(Expression::Multiply {
    //                 left: Box::new(Expression::Constant(2.0)),
    //                 right: Box::new(Expression::Variable("x")),
    //             }),
    //             right: Box::new(Expression::Variable("y")),
    //         },
    //         Expression::Minus {
    //             left: Box::new(Expression::Variable("b")),
    //             right: Box::new(Expression::Constant(5.0)),
    //         },
    //     );

    let circuit = circuit! {
        3*x*x*y + 5*x*y - x - 2*y + 3 == a;
        2*x + y == b - 5;
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
