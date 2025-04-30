use std::{net::SocketAddr, time::Duration};

use eyre::{Context as _, OptionExt as _, Result};
use futures::{SinkExt, StreamExt as _, TryFutureExt as _};
use serde::{Serialize, de::DeserializeOwned};
use tokio::{net::TcpStream, time::timeout};
use tokio_util::codec::{Framed, LengthDelimitedCodec};

const BINCODE_CONFIG: bincode::config::Configuration = bincode::config::standard();

pub struct Network {
    peers: Vec<Peer>,
}

pub struct Peer {
    addr: SocketAddr,
    stream: Framed<TcpStream, LengthDelimitedCodec>,
}

impl Network {
    pub async fn connect_all_peers(peers: &[SocketAddr]) -> Result<Self> {
        let addrs = peers;
        let mut streams = Vec::with_capacity(addrs.len());

        for addr in addrs {
            let stream = timeout(
                Duration::from_secs(60),
                TcpStream::connect(addr).map_err(eyre::Report::from),
            )
            .map_err(eyre::Report::from)
            .await
            .and_then(std::convert::identity) // .flatten() is unstable
            .wrap_err_with(|| format!("failed to connect to {addr} peer"))?;
            let stream = Framed::new(stream, LengthDelimitedCodec::new());

            streams.push(Peer {
                addr: *addr,
                stream,
            });
        }

        Ok(Self { peers: streams })
    }

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

    pub async fn recv<M: DeserializeOwned>(&mut self) -> Result<M> {
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

        Ok(msg)
    }
}
