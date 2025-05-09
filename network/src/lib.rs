//! Network module for handling peer-to-peer communication.

use std::{
    collections::HashSet,
    net::{SocketAddr, ToSocketAddrs},
    time::Duration,
};

use eyre::{Context as _, OptionExt as _, Result};
use futures::{SinkExt, StreamExt as _};
use serde::{Serialize, de::DeserializeOwned};
use tokio::net::{TcpListener, TcpStream};
use tokio_util::codec::{Framed, LengthDelimitedCodec};

use logger::{debug, info};

const BINCODE_CONFIG: bincode::config::Configuration = bincode::config::standard();
const CONNECT_RETRY_COUNT: usize = 3;
const CONNECT_RETRY_TIMEOUT: Duration = Duration::from_secs(3);

/// Network to communicate with peers.
pub struct Network {
    peers: Box<[Peer]>,
}

struct Peer {
    addr: SocketAddr,
    stream: Framed<TcpStream, LengthDelimitedCodec>,
}

impl Network {
    /// Establish a network connection with this node and the given peers.
    ///
    /// Connections are coordinated such that the lower address connects to the higher address.
    pub async fn establish(listen_addr: SocketAddr, peers: impl ToSocketAddrs) -> Result<Self> {
        let addrs = peers
            .to_socket_addrs()
            .wrap_err("failed to resolve peer addresses")?;

        let (accept_count, addrs_to_connect) = addrs.fold(
            (0, HashSet::new()),
            |(mut listen_count, mut addrs_to_connect), addr| {
                if addr > listen_addr {
                    addrs_to_connect.insert(addr);
                } else {
                    listen_count += 1;
                }

                (listen_count, addrs_to_connect)
            },
        );

        let (listen_streams, mut connect_streams) = tokio::try_join!(
            Self::listen(listen_addr, accept_count),
            Self::connect(addrs_to_connect)
        )?;
        let mut streams = listen_streams;
        streams.append(&mut connect_streams);

        Ok(Self {
            peers: streams.into(),
        })
    }

    /// Broadcast a message to all peers.
    pub async fn broadcast<M: Serialize>(&mut self, msg: M) -> Result<()> {
        let bytes = bincode::serde::encode_to_vec(msg, BINCODE_CONFIG)
            .wrap_err("failed to encode message")?;
        let bytes = tokio_util::bytes::Bytes::from(bytes);

        for peer in &mut self.peers {
            peer.stream
                .send(bytes.clone())
                .await
                .wrap_err_with(|| format!("failed to send message to {} peer", peer.addr))?
        }

        Ok(())
    }

    /// Receive a message from any peer.
    pub async fn recv<M: DeserializeOwned + std::fmt::Debug>(&mut self) -> Result<M> {
        let futures = self.peers.iter_mut().map(|peer| peer.stream.next());
        let (msg, peer_idx, _remaining) = futures::future::select_all(futures).await;
        let peer = &self.peers[peer_idx];

        let msg = || -> eyre::Result<M> {
            let bytes = msg
                .map(|res| res.map_err(eyre::Report::from))
                .ok_or_eyre("stream is closed")??;
            let (msg, _size) = bincode::serde::decode_from_slice::<M, _>(&bytes, BINCODE_CONFIG)
                .wrap_err("failed to decode message")?;

            Ok(msg)
        }()
        .wrap_err_with(|| format!("failed to received message from {} peer", peer.addr))?;

        debug!(addr = %peer.addr, msg = ?msg, "received message");

        Ok(msg)
    }

    async fn listen(listen_addr: SocketAddr, accept_count: usize) -> Result<Vec<Peer>> {
        let listener = TcpListener::bind(listen_addr)
            .await
            .wrap_err("failed to bind to listen address")?;

        let mut streams = Vec::with_capacity(accept_count);
        info!(addr = %listen_addr, waiting_connections_count = accept_count, "listening for incoming connections");
        for i in 0..accept_count {
            let (stream, addr) = listener
                .accept()
                .await
                .wrap_err("failed to accept incoming connection")?;
            info!(addr = %addr, left_connections_count = accept_count - i - 1,"accepted connection");

            let stream = Framed::new(stream, LengthDelimitedCodec::new());
            streams.push(Peer { addr, stream });
        }

        Ok(streams)
    }

    async fn connect(addrs_to_connect: HashSet<SocketAddr>) -> Result<Vec<Peer>> {
        futures::future::try_join_all(
            addrs_to_connect.into_iter().map(|addr| async move {
                let mut try_count = 0;
                loop {
                    match TcpStream::connect(addr).await {
                        Ok(stream) => {
                            info!(addr = %addr, "connected to peer");
                            let stream = Framed::new(stream, LengthDelimitedCodec::new());
                            return Ok(Peer { addr, stream });
                        }
                        Err(err) if try_count < CONNECT_RETRY_COUNT => {
                            try_count += 1;
                            debug!(addr = %addr, r#try = try_count, error = %err, "failed to connect to peer, retrying...");
                            tokio::time::sleep(CONNECT_RETRY_TIMEOUT).await;
                        }
                        Err(err) => {
                            return Err(err)
                                .wrap_err_with(|| format!("failed to connect to {addr} peer"));
                        }
                    }
                }
            })
        ).await
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU16, Ordering};

    use eyre::Result;
    use logger::{Instrument as _, debug_span};
    use test_log::test;

    use super::*;

    static LAST_PORT: AtomicU16 = AtomicU16::new(10010);

    fn next_port() -> u16 {
        let port = LAST_PORT.fetch_add(1, Ordering::Relaxed);
        if port == 0 {
            panic!("port overflow");
        }
        port
    }

    fn addr_generator() -> impl Iterator<Item = SocketAddr> {
        std::iter::from_fn(|| Some(([127, 0, 0, 1], next_port()).into()))
    }

    #[test(tokio::test)]
    async fn smoke() -> Result<()> {
        let addrs: Vec<_> = addr_generator().take(3).collect();

        let peers1 = &addrs[1..];
        let peers2 = [addrs[0], addrs[2]];
        let peers3 = &addrs[..2];

        let (mut net1, mut net2, mut net3) = tokio::try_join!(
            Network::establish(addrs[0], peers1).instrument(debug_span!("net1")),
            Network::establish(addrs[1], peers2.as_slice()).instrument(debug_span!("net2")),
            Network::establish(addrs[2], peers3).instrument(debug_span!("net3")),
        )
        .wrap_err("failed to establish networks")?;

        net1.broadcast("hello").await?;

        let msg2 = net2.recv::<String>().await?;
        assert_eq!(msg2, "hello");

        let msg3 = net3.recv::<String>().await?;
        assert_eq!(msg3, "hello");

        Ok(())
    }
}
