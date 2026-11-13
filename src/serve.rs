//! This module runs an operator. An admin command starts a session, and the operator announces the
//! session to the other operators of the session.
//!
//! - An admin sign request first runs the agreement on `(leaf, message)` with all operators, and
//!   then the 2 signing rounds with the quorum. The note assumes this agreement by consensus.
//! - The PoC does the agreement with one exchange of acknowledgements. A signer signs only a
//!   message that `Q = ⌊(n + f)/2⌋ + 1` operators acknowledged, and each operator acknowledges one
//!   message for each leaf.
//! - Without the agreement, two quorums that share only corrupt operators can sign two messages at
//!   one key.
//! - The count follows the condition `t > (n + f)/2` of PRAWNS (ePrint 2026/2142), applied to the
//!   acknowledgements. The exchange is not in PRAWNS or in the leanSPHINCS prototype.
//! - An operator runs the acknowledgement session of a peer to its end before it takes the next
//!   announcement of that peer, so the signing session that follows finds the certificate.

use std::fs::{File, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};
use std::{fs, future};

use tokio::net::TcpListener;
use tokio::sync::Mutex;
use tokio::task;
use tracing::{Instrument, info, info_span};

use crate::dkg::{self, BottomTree};
use crate::mpc::Reshare;
use crate::net::{self, Network};
use crate::prawns::{self, Operator};
use crate::xmss::{self, KEYS};

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
    Acknowledge {
        leaf: u32,
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
            Session::Acknowledge { leaf, message } => (3, *leaf, message.clone()),
        };
        [&[kind][..], &number.to_le_bytes(), &message].concat()
    }

    pub fn parse(bytes: &[u8]) -> Session {
        let number = u32::from_le_bytes(bytes[1..5].try_into().unwrap());
        match bytes[0] {
            0 => Session::NewTopTree,
            1 => Session::NewBottomTree { bottom: number },
            2 => {
                let (quorum, message) = parse_members(&bytes[5..]);
                Session::Sign {
                    leaf: number,
                    quorum,
                    message: message.to_vec(),
                }
            }
            _ => Session::Acknowledge {
                leaf: number,
                message: bytes[5..].to_vec(),
            },
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
    announcing: Mutex<()>,
}

impl Server {
    async fn start(&self, request: &Session) -> Outcome {
        let session = self.session(request)?;
        if let Session::Sign { leaf, message, .. } = &session {
            let acknowledge = Session::Acknowledge {
                leaf: *leaf,
                message: message.clone(),
            };
            self.announce(&acknowledge).await?;
        }
        self.announce(&session).await
    }

    async fn announce(&self, session: &Session) -> Outcome {
        // The top byte holds the operator number plus one. So for fewer than `2^24` sessions on
        // each operator, the session numbers of different operators differ and none is 0.
        let session_id = (self.id as u32 + 1) << 24 | self.sessions.fetch_add(1, Ordering::Relaxed);
        let announcement = net::pack(&[&session_id.to_le_bytes()[..], &session.bytes()].concat());
        // The lock gives all peers the announcements of this operator in one order. Else two
        // acknowledgement sessions can wait for each other.
        let sending = self.announcing.lock().await;
        for j in session.participants(self.network.n) {
            if j != self.id {
                self.network.send(j, 0, announcement.clone());
            }
        }
        drop(sending);
        self.run(session_id, session).await
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
            Session::Acknowledge { .. } => {
                Err("an admin request is a dkg or a sign request".into())
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
            Session::Acknowledge { leaf, message } => {
                acknowledge(&self.dir, &network, *leaf, message)
                    .instrument(info_span!("acknowledge", leaf))
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
    // Each operator takes the rank of its address among all addresses, in string order, as its
    // number.
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
        announcing: Mutex::new(()),
    });
    for j in (0..n).filter(|&j| j != id) {
        let mut announcements = server.network.receiver(j, 0);
        let server = server.clone();
        tokio::spawn(async move {
            while let Some(words) = announcements.recv().await {
                let announcement = net::unpack(&words);
                let session_id = u32::from_le_bytes(announcement[..4].try_into().unwrap());
                let session = Session::parse(&announcement[4..]);
                let acknowledgement = matches!(session, Session::Acknowledge { .. });
                let server = server.clone();
                let run = async move {
                    if let Err(error) = server.run(session_id, &session).await {
                        info!("{error}");
                    }
                };
                if acknowledgement {
                    run.await
                } else {
                    tokio::spawn(run);
                }
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
    certified(dir, leaf, message)?;
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

/// The exchange of acknowledgements. It certifies `(leaf, message)` when `Q` operators acknowledge
/// exactly this pair.
pub async fn acknowledge(dir: &Path, network: &Arc<Network>, leaf: u32, message: &[u8]) -> Outcome {
    let (n, f) = (network.n, network.n / 2);
    let q = (n + f) / 2 + 1;
    let own = match message.len() {
        32 => record(dir, &format!("acknowledgement{leaf}"), message),
        _ => Err("the message must be 32 bytes".into()),
    };
    // An operator that refuses still takes part with an empty acknowledgement, so the others can
    // count the rest.
    let pair = [&leaf.to_le_bytes()[..], message].concat();
    let acknowledgement = match own {
        Ok(()) => pair.clone(),
        Err(_) => vec![],
    };
    let received = network
        .channel()
        .exchange_bytes(vec![acknowledgement; n])
        .await?;
    own?;
    let count = (0..n)
        .filter(|&j| j == network.id || received[j] == pair)
        .count();
    if count < q {
        return Err(format!("{count} of the {q} needed operators acknowledge"));
    }
    record(dir, &format!("certificate{leaf}"), message)?;
    Ok(vec![])
}

/// Writes `message` to the new file `name` and syncs it to disk. If the file exists, it must hold
/// the same message.
fn record(dir: &Path, name: &str, message: &[u8]) -> Result<(), String> {
    let path = dir.join(name);
    match OpenOptions::new().write(true).create_new(true).open(&path) {
        Ok(mut file) => {
            file.write_all(message).unwrap();
            file.sync_all().unwrap();
            File::open(dir).unwrap().sync_all().unwrap();
            Ok(())
        }
        // Another task can read the file before the task that wrote it syncs it, so this task syncs
        // it too.
        Err(_) if fs::read(&path).unwrap() == message => {
            File::open(&path).unwrap().sync_all().unwrap();
            File::open(dir).unwrap().sync_all().unwrap();
            Ok(())
        }
        Err(_) => Err(format!(
            "{name} holds another message or an incomplete record"
        )),
    }
}

/// The operator signs `(leaf, message)` only when its acknowledgement and its certificate both hold
/// `message`. The acknowledgement is durable before it goes out, so a certificate that a crash
/// damaged cannot name another message.
pub fn certified(dir: &Path, leaf: u32, message: &[u8]) -> Result<(), String> {
    let holds = |name: &str| {
        fs::read(dir.join(format!("{name}{leaf}"))).is_ok_and(|bytes| bytes == message)
    };
    match holds("acknowledgement") && holds("certificate") {
        true => Ok(()),
        false => Err(format!("leaf {leaf} has no certificate for this message")),
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Barrier;
    use std::{env, thread};

    use crate::mpc::tests::local_networks;
    use crate::serve::*;

    fn temporary_dir(run: u64, id: usize) -> PathBuf {
        let dir = env::temp_dir().join(format!("threshold-lean-xmss-{run}-{id}"));
        fs::create_dir(&dir).unwrap();
        dir
    }

    #[test]
    fn a_second_message_at_a_leaf_gets_no_acknowledgement_and_no_certificate() {
        let run = rand::random::<u64>();
        let outcomes = local_networks(2, async |network, _| {
            let dir = temporary_dir(run, network.id);
            let first = acknowledge(&dir, &network, 7, &[1; 32]).await;
            let second = acknowledge(&dir, &network, 7, &[2; 32]).await;
            let outcome = (first, second, certified(&dir, 7, &[2; 32]));
            fs::remove_dir_all(&dir).unwrap();
            outcome
        });
        let refused = Err("acknowledgement7 holds another message or an incomplete record".into());
        let uncertified = Err("leaf 7 has no certificate for this message".into());
        assert_eq!(outcomes, vec![(Ok(vec![]), refused, uncertified); 3]);
    }

    #[test]
    fn a_certificate_counts_only_with_an_acknowledgement_of_the_same_message() {
        let dir = temporary_dir(rand::random(), 0);
        record(&dir, "certificate7", &[2; 32]).unwrap();
        let alone = certified(&dir, 7, &[2; 32]);
        record(&dir, "acknowledgement7", &[1; 32]).unwrap();
        let outcomes = (
            alone,
            certified(&dir, 7, &[1; 32]),
            certified(&dir, 7, &[2; 32]),
        );
        fs::remove_dir_all(&dir).unwrap();
        let uncertified: Result<(), String> =
            Err("leaf 7 has no certificate for this message".into());
        assert_eq!(
            outcomes,
            (uncertified.clone(), uncertified.clone(), uncertified)
        );
    }

    #[test]
    fn at_3_of_5_four_acknowledgements_certify_and_a_message_of_another_length_gets_none() {
        let run = rand::random::<u64>();
        let outcomes = local_networks(3, async |network, _| {
            let dir = temporary_dir(run, network.id);
            if network.id == 4 {
                record(&dir, "acknowledgement7", &[2; 32]).unwrap();
            }
            let outcome = (
                acknowledge(&dir, &network, 7, &[1; 32]).await,
                certified(&dir, 7, &[1; 32]),
                acknowledge(&dir, &network, 8, &[]).await,
                certified(&dir, 8, &[]),
            );
            fs::remove_dir_all(&dir).unwrap();
            outcome
        });
        let short = Err("the message must be 32 bytes".to_string());
        let uncertified = |leaf| Err(format!("leaf {leaf} has no certificate for this message"));
        let certified = (Ok(vec![]), Ok(()), short.clone(), uncertified(8));
        let refused = Err("acknowledgement7 holds another message or an incomplete record".into());
        let expected = [
            vec![certified; 4],
            vec![(refused, uncertified(7), short, uncertified(8))],
        ];
        assert_eq!(outcomes, expected.concat());
    }

    #[test]
    fn at_3_of_5_three_acknowledgements_do_not_certify() {
        let run = rand::random::<u64>();
        let outcomes = local_networks(3, async |network, _| {
            let dir = temporary_dir(run, network.id);
            if network.id >= 3 {
                record(&dir, "acknowledgement7", &[2; 32]).unwrap();
            }
            let outcome = (
                acknowledge(&dir, &network, 7, &[1; 32]).await,
                certified(&dir, 7, &[1; 32]),
            );
            fs::remove_dir_all(&dir).unwrap();
            outcome
        });
        let short = Err("3 of the 4 needed operators acknowledge".into());
        let refused = Err("acknowledgement7 holds another message or an incomplete record".into());
        let uncertified = Err("leaf 7 has no certificate for this message".to_string());
        let expected = [
            vec![(short, uncertified.clone()); 3],
            vec![(refused, uncertified); 2],
        ];
        assert_eq!(outcomes, expected.concat());
    }

    #[test]
    fn one_message_at_two_leaves_gets_no_certificate() {
        let run = rand::random::<u64>();
        let outcomes = local_networks(2, async |network, _| {
            let dir = temporary_dir(run, network.id);
            let leaf = if network.id == 0 { 8 } else { 7 };
            let outcome = (
                acknowledge(&dir, &network, leaf, &[1; 32]).await,
                certified(&dir, leaf, &[1; 32]),
            );
            fs::remove_dir_all(&dir).unwrap();
            outcome
        });
        let short = |count| Err(format!("{count} of the 3 needed operators acknowledge"));
        let uncertified = |leaf| Err(format!("leaf {leaf} has no certificate for this message"));
        let expected = [
            vec![(short(1), uncertified(8))],
            vec![(short(2), uncertified(7)); 2],
        ];
        assert_eq!(outcomes, expected.concat());
    }

    #[test]
    fn a_second_record_of_the_same_message_succeeds() {
        let dir = temporary_dir(rand::random(), 0);
        record(&dir, "acknowledgement7", &[1; 32]).unwrap();
        let second = record(&dir, "acknowledgement7", &[1; 32]);
        fs::remove_dir_all(&dir).unwrap();
        assert_eq!(second, Ok(()));
    }

    #[test]
    fn a_signer_refuses_a_message_with_no_certificate() {
        let run = rand::random::<u64>();
        let outcomes = local_networks(2, async |network, _| {
            let dir = temporary_dir(run, network.id);
            let outcome = sign(&dir, &network, 7, &[0, 1], &[1; 32]).await;
            fs::remove_dir_all(&dir).unwrap();
            outcome
        });
        let refused = Err("leaf 7 has no certificate for this message".to_string());
        assert_eq!(outcomes, vec![refused; 3]);
    }

    #[test]
    fn of_two_concurrent_messages_at_a_leaf_at_most_one_is_acknowledged() {
        let dir = temporary_dir(rand::random(), 0);
        for leaf in 0..64 {
            let name = format!("acknowledgement{leaf}");
            let barrier = Barrier::new(2);
            let outcomes: Vec<_> = thread::scope(|s| {
                let handles: Vec<_> = [[1; 32], [2; 32]]
                    .map(|message| {
                        let (dir, name, barrier) = (&dir, &name, &barrier);
                        s.spawn(move || {
                            barrier.wait();
                            record(dir, name, &message).ok().map(|()| message)
                        })
                    })
                    .into_iter()
                    .collect();
                handles.into_iter().map(|h| h.join().unwrap()).collect()
            });
            let acknowledged: Vec<[u8; 32]> = outcomes.into_iter().flatten().collect();
            assert!(acknowledged.len() <= 1);
            for message in acknowledged {
                assert_eq!(fs::read(dir.join(&name)).unwrap(), message);
            }
        }
        fs::remove_dir_all(&dir).unwrap();
    }
}
