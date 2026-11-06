//! This module implements tagged channels between the operators over TCP.
//!
//! - A frame is a tag and a length in words, and then the words.
//! - A read thread for each peer routes each frame to the channel of its tag, and a write thread
//!   for each peer sends the frames.
//! - A dropped channel sends an abort frame to its members, in place of the disconnection of the
//!   leanSPHINCS prototype.
//! - A receive on the channel then fails after the frames that arrived before the abort frame.
//! - The reader ignores an abort frame for a channel that it does not know yet.

use std::collections::HashMap;
use std::io::{BufReader, BufWriter, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

use futures::future::try_join_all;
use primitives::{cast_slice, cast_slice_mut};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use tokio::sync::mpsc::{UnboundedReceiver, UnboundedSender, unbounded_channel};
use tracing::info;

/// The sender that the read thread uses, and the receiver until a channel takes it.
type Route = (
    UnboundedSender<Vec<u64>>,
    Option<UnboundedReceiver<Vec<u64>>>,
);
type Frame = (u64, Vec<u64>);
type Routes = Arc<Mutex<Option<HashMap<u64, Route>>>>;

const ABORT: u64 = 1 << 63;

pub struct Network {
    pub id: usize,
    pub n: usize,
    writers: Vec<Option<UnboundedSender<Frame>>>,
    routes: Vec<Routes>,
    session: u64,
    next: AtomicU64,
    pub sent: Arc<AtomicU64>,
}

/// Connects to all operators. Each operator dials the operators with lower numbers and accepts the
/// others.
pub fn connect(id: usize, listener: TcpListener, addresses: Vec<String>) -> Arc<Network> {
    let n = addresses.len();
    let mut streams: Vec<Option<TcpStream>> = (0..n).map(|_| None).collect();
    let connected = |count: usize| info!("connected to {count} of {} operators", n - 1);
    connected(0);
    for j in 0..id {
        let mut stream = loop {
            match TcpStream::connect(&addresses[j]) {
                Ok(stream) => break stream,
                Err(_) => thread::sleep(Duration::from_millis(100)),
            }
        };
        stream.write_all(&[id as u8]).unwrap();
        streams[j] = Some(stream);
        connected(j + 1);
    }
    for count in id + 1..n {
        let (mut stream, _) = listener.accept().unwrap();
        let mut peer = [0];
        stream.read_exact(&mut peer).unwrap();
        streams[peer[0] as usize] = Some(stream);
        connected(count);
    }
    let routes: Vec<Routes> = (0..n)
        .map(|_| Arc::new(Mutex::new(Some(HashMap::new()))))
        .collect();
    let writers = streams
        .into_iter()
        .zip(&routes)
        .enumerate()
        .map(|(j, (stream, routes))| {
            let stream = stream?;
            stream.set_nodelay(true).unwrap();
            let (reader, routes) = (stream.try_clone().unwrap(), routes.clone());
            let (frames, queue) = unbounded_channel();
            let spawn = |name: &str| thread::Builder::new().name(format!("{name} {j}"));
            spawn("read").spawn(move || read(reader, routes)).unwrap();
            spawn("write").spawn(move || write(stream, queue)).unwrap();
            Some(frames)
        })
        .collect();
    Arc::new(Network {
        id,
        n,
        writers,
        routes,
        session: 0,
        // Tag 0 carries the session announcements, so the channels of session 0 start at 1.
        next: AtomicU64::new(1),
        sent: Arc::default(),
    })
}

fn read(stream: TcpStream, routes: Routes) {
    let mut reader = BufReader::with_capacity(1 << 16, stream);
    let mut header = [0; 2];
    while reader.read_exact(cast_slice_mut(&mut header)).is_ok() {
        let mut words = vec![0; header[1] as usize];
        if reader.read_exact(cast_slice_mut(&mut words)).is_err() {
            break;
        }
        let mut routes = routes.lock().unwrap();
        let (routes, tag) = (routes.as_mut().unwrap(), header[0] & !ABORT);
        if header[0] & ABORT == 0 {
            route(routes, tag).0.send(words).ok();
        } else if let Some(route) = routes.get_mut(&tag) {
            // The new sender drops the old one, so the receiver ends after the frames that it
            // already has. The reader drops later frames of the channel.
            route.0 = unbounded_channel().0;
        }
    }
    routes.lock().unwrap().take();
}

fn write(stream: TcpStream, mut queue: UnboundedReceiver<Frame>) {
    let mut writer = BufWriter::with_capacity(1 << 16, stream);
    while let Some(mut frame) = queue.blocking_recv() {
        loop {
            let header = [frame.0, frame.1.len() as u64];
            if writer.write_all(cast_slice(&header)).is_err()
                || writer.write_all(cast_slice(&frame.1)).is_err()
            {
                return;
            }
            match queue.try_recv() {
                Ok(next) => frame = next,
                Err(_) => break,
            }
        }
        if writer.flush().is_err() {
            return;
        }
    }
}

fn route(routes: &mut HashMap<u64, Route>, tag: u64) -> &mut Route {
    routes.entry(tag).or_insert_with(|| {
        let (sender, receiver) = unbounded_channel();
        (sender, Some(receiver))
    })
}

impl Network {
    pub fn channel(self: &Arc<Self>) -> Channel {
        self.channel_among(&(0..self.n).collect::<Vec<_>>())
    }

    pub fn channel_among(self: &Arc<Self>, members: &[usize]) -> Channel {
        let tag = self.session << 32 | self.next.fetch_add(1, Ordering::Relaxed);
        Channel::new(self, tag, members)
    }

    pub fn session(&self, session: u32) -> Arc<Network> {
        Arc::new(Network {
            id: self.id,
            n: self.n,
            writers: self.writers.clone(),
            routes: self.routes.clone(),
            session: session as u64,
            next: AtomicU64::new(0),
            sent: self.sent.clone(),
        })
    }

    pub fn receiver(&self, peer: usize, tag: u64) -> UnboundedReceiver<Vec<u64>> {
        let mut routes = self.routes[peer].lock().unwrap();
        let routes = routes
            .as_mut()
            .unwrap_or_else(|| panic!("operator {peer} disconnected"));
        route(routes, tag).1.take().unwrap()
    }

    pub fn send(&self, peer: usize, tag: u64, words: Vec<u64>) {
        self.sent
            .fetch_add(8 * words.len() as u64, Ordering::Relaxed);
        self.writers[peer]
            .as_ref()
            .unwrap()
            .send((tag, words))
            .unwrap();
    }
}

pub struct Channel {
    network: Arc<Network>,
    pub tag: u64,
    receivers: Vec<Option<UnboundedReceiver<Vec<u64>>>>,
    pub rounds: u64,
}

impl Channel {
    fn new(network: &Arc<Network>, tag: u64, members: &[usize]) -> Channel {
        Channel {
            receivers: (0..network.n)
                .map(|j| {
                    (j != network.id && members.contains(&j)).then(|| network.receiver(j, tag))
                })
                .collect(),
            network: network.clone(),
            tag,
            rounds: 0,
        }
    }

    /// One round, which sends one message to each member and receives one message from each member.
    pub async fn exchange(&mut self, outgoing: Vec<Vec<u64>>) -> Result<Vec<Vec<u64>>, String> {
        for (j, words) in outgoing.into_iter().enumerate() {
            if self.receivers[j].is_some() {
                self.network.send(j, self.tag, words);
            }
        }
        let receives = self
            .receivers
            .iter_mut()
            .enumerate()
            .map(|(j, receiver)| async move {
                match receiver {
                    Some(receiver) => receiver
                        .recv()
                        .await
                        .ok_or_else(|| format!("operator {j} aborts")),
                    None => Ok(vec![]),
                }
            });
        let received = try_join_all(receives).await?;
        self.rounds += 1;
        Ok(received)
    }

    pub async fn exchange_bytes(&mut self, outgoing: Vec<Vec<u8>>) -> Result<Vec<Vec<u8>>, String> {
        let outgoing = outgoing.iter().map(|bytes| pack(bytes)).collect();
        let received = self.exchange(outgoing).await?;
        Ok(received.iter().map(|words| unpack(words)).collect())
    }
}

impl Drop for Channel {
    fn drop(&mut self) {
        for (j, receiver) in self.receivers.iter().enumerate() {
            if let (Some(_), Some(writer)) = (receiver, &self.network.writers[j]) {
                writer.send((self.tag | ABORT, vec![])).ok();
            }
        }
        for routes in &self.network.routes {
            if let Some(routes) = routes.lock().unwrap().as_mut() {
                routes.remove(&self.tag);
            }
        }
    }
}

pub fn pack(bytes: &[u8]) -> Vec<u64> {
    let mut words = vec![0; 1 + bytes.len().div_ceil(8)];
    words[0] = bytes.len() as u64;
    cast_slice_mut(&mut words[1..])[..bytes.len()].copy_from_slice(bytes);
    words
}

pub fn unpack(words: &[u64]) -> Vec<u8> {
    words.first().map_or(vec![], |&length| {
        cast_slice(&words[1..])[..length as usize].to_vec()
    })
}

pub async fn write_frame(stream: &mut (impl AsyncWrite + Unpin), bytes: &[u8]) {
    stream.write_u64_le(bytes.len() as u64).await.unwrap();
    stream.write_all(bytes).await.unwrap();
}

pub async fn read_frame(stream: &mut (impl AsyncRead + Unpin)) -> Vec<u8> {
    let mut bytes = vec![0; stream.read_u64_le().await.unwrap() as usize];
    stream.read_exact(&mut bytes).await.unwrap();
    bytes
}

const _: () = assert!(cfg!(target_endian = "little"));
