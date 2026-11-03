//! This module runs an operator. An admin command starts a session, and the operator announces the session to the other operators of the session.

use crate::dkg::{self, BottomTree};
use crate::mpc::Reshare;
use crate::net::{self, Network};
use crate::prawns::{self, Operator};
use crate::xmss::{self, KEYS};
use std::fs;
use std::future;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};
use tokio::net::TcpListener;
use tokio::task;
use tracing::{Instrument, info, info_span};

pub type Outcome = Result<Vec<u8>, String>;

pub enum Session {
    NewTopTree,
    NewBottomTree {
        bottom: u32,
    },
    Sign {
        leaf: u32,
        quorum: Vec<usize>,
        message: Vec<u8>,
    },
}

impl Session {
    fn participants(&self, n: usize) -> Vec<usize> {
        match self {
            Session::Sign { quorum, .. } => quorum.clone(),
            _ => (0..n).collect(),
        }
    }

    pub fn bytes(&self) -> Vec<u8> {
        let (kind, number, message) = match self {
            Session::NewTopTree => (0, 0, vec![]),
            Session::NewBottomTree { bottom } => (1, *bottom, vec![]),
            Session::Sign {
                leaf,
                quorum,
                message,
            } => (2, *leaf, [members(quorum), message.clone()].concat()),
        };
        [&[kind][..], &number.to_le_bytes(), &message].concat()
    }

    pub fn parse(bytes: &[u8]) -> Session {
        let number = u32::from_le_bytes(bytes[1..5].try_into().unwrap());
        match bytes[0] {
            0 => Session::NewTopTree,
            1 => Session::NewBottomTree { bottom: number },
            _ => {
                let (quorum, message) = parse_members(&bytes[5..]);
                Session::Sign {
                    leaf: number,
                    quorum,
                    message: message.to_vec(),
                }
            }
        }
    }
}

fn members(ids: &[usize]) -> Vec<u8> {
    [
        vec![ids.len() as u8],
        ids.iter().map(|&j| j as u8).collect(),
    ]
    .concat()
}

fn parse_members(bytes: &[u8]) -> (Vec<usize>, &[u8]) {
    let count = bytes[0] as usize;
    let ids = bytes[1..1 + count].iter().map(|&j| j as usize).collect();
    (ids, &bytes[1 + count..])
}

struct Server {
    dir: PathBuf,
    id: usize,
    network: Arc<Network>,
    reshare: Reshare,
    batch_size: usize,
    concurrency: usize,
    sessions: AtomicU32,
}

impl Server {
    async fn start(&self, request: &Session) -> Outcome {
        let session = self.session(request)?;
        // The top byte holds the operator number plus one. So for fewer than `2^24` sessions on each operator, the session numbers of different operators differ and none is 0.
        let session_id = (self.id as u32 + 1) << 24 | self.sessions.fetch_add(1, Ordering::Relaxed);
        let announcement = net::pack(&[&session_id.to_le_bytes()[..], &session.bytes()].concat());
        for j in session.participants(self.network.n) {
            if j != self.id {
                self.network.send(j, 0, announcement.clone());
            }
        }
        self.run(session_id, &session).await
    }

    fn session(&self, request: &Session) -> Result<Session, String> {
        let key = self.dir.join("pk").exists();
        match *request {
            Session::NewTopTree if key => Err("the key exists".into()),
            Session::NewTopTree => Ok(Session::NewTopTree),
            _ if !key => Err("no key, run dkg --top first".into()),
            Session::NewBottomTree { bottom } if bottom as usize >= KEYS => {
                Err(format!("the bottom tree index must be less than {KEYS}"))
            }
            Session::NewBottomTree { bottom } if dkg::tree_file(&self.dir, bottom).exists() => {
                Err(format!("bottom tree {bottom} exists"))
            }
            Session::NewBottomTree { bottom } => Ok(Session::NewBottomTree { bottom }),
            Session::Sign { ref message, .. } if message.len() != 32 => {
                Err("the message must be 32 bytes".into())
            }
            Session::Sign { leaf, .. }
                if !dkg::tree_file(&self.dir, xmss::layer_index(leaf, 1)).exists() =>
            {
                Err(format!(
                    "no bottom tree {}, run dkg --bottom {} first",
                    xmss::layer_index(leaf, 1),
                    xmss::layer_index(leaf, 1)
                ))
            }
            Session::Sign {
                leaf,
                ref quorum,
                ref message,
            } => {
                let (n, t) = (self.network.n, self.network.n.div_ceil(2));
                let mut quorum = if quorum.is_empty() {
                    (0..t).collect()
                } else {
                    quorum.clone()
                };
                quorum.sort();
                quorum.dedup();
                if quorum.len() != t || quorum.iter().any(|&j| j >= n) {
                    return Err(format!(
                        "the quorum must be {t} distinct operators below {n}"
                    ));
                }
                if !quorum.contains(&self.id) {
                    return Err(format!(
                        "operator {} receives the request, so it must be in the quorum",
                        self.id
                    ));
                }
                Ok(Session::Sign {
                    leaf,
                    quorum,
                    message: message.clone(),
                })
            }
        }
    }

    async fn run(&self, session_id: u32, session: &Session) -> Outcome {
        let network = self.network.session(session_id);
        match session {
            Session::NewTopTree if self.dir.join("pk").exists() => Err("the key exists".into()),
            Session::NewTopTree => {
                dkg::new_top_tree(
                    &self.dir,
                    &network,
                    self.reshare,
                    self.batch_size,
                    self.concurrency,
                )
                .await
            }
            Session::NewBottomTree { bottom } => {
                dkg::new_bottom_tree(
                    &self.dir,
                    &network,
                    *bottom,
                    self.reshare,
                    self.batch_size,
                    self.concurrency,
                )
                .await?;
                Ok(fs::read(self.dir.join("pk")).unwrap())
            }
            Session::Sign {
                leaf,
                quorum,
                message,
            } => {
                sign(&self.dir, &network, *leaf, quorum, message)
                    .instrument(info_span!("sign", leaf))
                    .await
            }
        }
    }
}

pub async fn serve(
    address: &str,
    admin: Option<&str>,
    peers: Vec<String>,
    dir: PathBuf,
    reshare: Reshare,
    batch_size: usize,
    concurrency: usize,
) {
    let mut addresses = [peers, vec![address.to_string()]].concat();
    // Each operator takes the rank of its address among all addresses, in string order, as its number.
    addresses.sort();
    let (id, n) = (
        addresses.iter().position(|a| a == address).unwrap(),
        addresses.len(),
    );
    if dir.join("operator").exists() {
        assert_eq!(
            Operator::load(&dir).1.id,
            id,
            "the key belongs to another operator"
        );
    }
    let listener = std::net::TcpListener::bind(address).unwrap();
    let network = task::spawn_blocking(move || net::connect(id, listener, addresses))
        .await
        .unwrap();
    let server = Arc::new(Server {
        dir,
        id,
        network,
        reshare,
        batch_size,
        concurrency,
        sessions: AtomicU32::new(0),
    });
    for j in (0..n).filter(|&j| j != id) {
        let mut announcements = server.network.receiver(j, 0);
        let server = server.clone();
        tokio::spawn(async move {
            while let Some(words) = announcements.recv().await {
                let announcement = net::unpack(&words);
                let session_id = u32::from_le_bytes(announcement[..4].try_into().unwrap());
                let server = server.clone();
                tokio::spawn(async move {
                    if let Err(error) = server
                        .run(session_id, &Session::parse(&announcement[4..]))
                        .await
                    {
                        info!("{error}");
                    }
                });
            }
        });
    }
    info!("operator {id} of {n} is ready");
    let Some(admin) = admin else {
        return future::pending().await;
    };
    let commands = TcpListener::bind(admin).await.unwrap();
    info!("admin commands on {admin}");
    loop {
        let (mut stream, _) = commands.accept().await.unwrap();
        let server = server.clone();
        tokio::spawn(async move {
            let request = Session::parse(&net::read_frame(&mut stream).await);
            let reply = match server.start(&request).await {
                Ok(bytes) => [vec![0], bytes].concat(),
                Err(error) => [vec![1], error.into_bytes()].concat(),
            };
            net::write_frame(&mut stream, &reply).await;
        });
    }
}

async fn sign(
    dir: &Path,
    network: &Arc<Network>,
    leaf: u32,
    quorum: &[usize],
    message: &[u8],
) -> Outcome {
    let load = info_span!("load").entered();
    let (group, operator) = Operator::load(dir);
    let pk = fs::read(dir.join("pk")).unwrap();
    let tree = BottomTree::open(dir, xmss::layer_index(leaf, 1));
    let tree_leaf = xmss::tree_leaf(leaf) as usize;
    let (cpk, commitment, path, top) = (
        tree.cpk(tree_leaf),
        tree.commitment(tree_leaf),
        tree.path(tree_leaf),
        tree.top_signature(),
    );
    load.exit();
    let bottom = prawns::sign(
        network,
        &group,
        &operator,
        quorum,
        leaf,
        message,
        (&cpk, &commitment),
    )
    .await?;
    let signature = [&leaf.to_le_bytes()[..], &bottom, &path, &top].concat();
    match info_span!("verify").in_scope(|| xmss::verify(&pk, message, &signature)) {
        true => Ok(signature),
        false => Err("the signature does not verify".into()),
    }
}
