mod check;
mod circuit;
mod dkg;
mod lean_xmss;
mod mpc;
mod net;
mod prawns;
mod serve;
mod wots;

use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::process::exit;
use std::str::FromStr;
use std::time::Duration;
use std::{io, thread};

use clap::{ArgGroup, Parser};
use dkg::{BATCH_SIZE, Settings};
use mpc::{LANES, Reshare};
use serve::Session;
use tikv_jemallocator::Jemalloc;
use tokio::net::TcpStream;
use tracing_forest::ForestLayer;
use tracing_forest::printer::{MakeStderr, PrettyPrinter};
use tracing_forest::tag::NoTag;
use tracing_subscriber::filter::filter_fn;
use tracing_subscriber::fmt::format::FmtSpan;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Layer, Registry, fmt};

#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

#[derive(Parser)]
#[command(about = "A t-of-(2t - 1) threshold leanXMSS key (EIP-8450)")]
enum Command {
    #[command(about = "Runs one operator, which connects to all others and then accepts commands")]
    Serve {
        #[arg(long, help = "The host:port of this operator for the other operators")]
        addr: String,
        #[arg(long, help = "The host:port of this operator for admin commands, none if not given")]
        admin: Option<String>,
        #[arg(
            long,
            required = true,
            help = "The party host:port of another operator, once for each other operator"
        )]
        peers: Vec<String>,
        #[arg(long, help = "The directory of the key share of this operator")]
        sk: PathBuf,
        #[arg(
            long,
            value_enum,
            default_value_t = Reshare::Collector,
            help = "peer: 1 round per AND layer; for n = 3 this is Araki et al. CCS'16 (Rep3)."
        )]
        reshare: Reshare,
        #[arg(
            long,
            default_value_t = BATCH_SIZE,
            value_parser = parse_batch_size,
            help = "The chains of a chain batch and the keys of a commitment batch, a multiple of 4 that all operators share"
        )]
        batch_size: usize,
        #[arg(
            long,
            default_value_t = NonZeroUsize::new(2 * thread::available_parallelism().unwrap().get()).unwrap(),
            help = "The batches that this operator runs at the same time"
        )]
        concurrency: NonZeroUsize,
        #[arg(
            long,
            default_value_t = 86_400,
            help = "The seconds that a key ceremony can take before this operator votes for its abort"
        )]
        time_limit: u64,
    },
    #[command(about = "Generates the key and its top tree, or one bottom tree, and prints the public key")]
    #[command(group = ArgGroup::new("tree").required(true).args(["top", "bottom"]))]
    Dkg {
        #[arg(long, help = "The admin host:port of an operator")]
        admin: String,
        #[arg(long, help = "Generates the key and its top tree")]
        top: bool,
        #[arg(long, help = "Generates the bottom tree with this index")]
        bottom: Option<u32>,
        #[arg(
            long,
            default_value_t = wots::KEYS as u32,
            help = "The count of the first keys of the tree that the ceremony generates, a power of two"
        )]
        leaves: u32,
    },
    #[command(about = "Signs a 32-byte message at a leaf and prints the signature")]
    Sign {
        #[arg(long, help = "The admin host:port of an operator")]
        admin: String,
        #[arg(
            long,
            help = "The leaf index, bottom tree index times 65536 plus the leaf in that tree"
        )]
        leaf: u32,
        #[arg(
            long,
            help = "An operator of the quorum, once for each of the t operators, the first t operators if not given"
        )]
        quorum: Vec<usize>,
        #[arg(long, help = "The 32-byte message in hex")]
        msg: Hex,
    },
    #[command(about = "Verifies a signature with the plain leanXMSS verifier")]
    Verify {
        #[arg(long, help = "The public key in hex")]
        pk: Hex,
        #[arg(long, help = "The message in hex")]
        msg: Hex,
        #[arg(long, help = "The signature in hex")]
        sig: Hex,
    },
}

async fn request(address: &str, request: Session) -> Vec<u8> {
    let mut stream = TcpStream::connect(address).await.unwrap();
    net::write_frame(&mut stream, &request.bytes()).await;
    let reply = net::read_frame(&mut stream).await;
    if reply[0] != 0 {
        eprintln!("{}", String::from_utf8_lossy(&reply[1..]));
        exit(1);
    }
    reply[1..].to_vec()
}

#[tokio::main]
async fn main() {
    Registry::default()
        .with(
            EnvFilter::builder()
                .with_default_directive(tracing::Level::INFO.into())
                .from_env_lossy(),
        )
        .with(ForestLayer::new(PrettyPrinter::new().writer(MakeStderr), NoTag))
        // The forest printer gives a span only the time in which it runs. This layer prints the
        // busy time and the idle time of each span when it closes, and their sum is the elapsed
        // time.
        .with(
            fmt::layer()
                .with_span_events(FmtSpan::CLOSE)
                .with_writer(io::stderr)
                .with_filter(filter_fn(|metadata| metadata.is_span())),
        )
        .init();
    match Command::parse() {
        Command::Serve {
            addr,
            admin,
            peers,
            sk,
            reshare,
            batch_size,
            concurrency,
            time_limit,
        } => {
            let settings = Settings {
                reshare,
                batch_size,
                concurrency: concurrency.get(),
                time_limit: Duration::from_secs(time_limit),
            };
            serve::serve(&addr, admin.as_deref(), peers, sk, settings).await
        }
        Command::Dkg {
            admin, bottom, leaves, ..
        } => {
            let session = match bottom {
                None => Session::NewTopTree { leaves },
                Some(bottom) => Session::NewBottomTree { bottom, leaves },
            };
            println!("{}", hex::encode(request(&admin, session).await))
        }
        Command::Sign {
            admin,
            leaf,
            quorum,
            msg,
        } => {
            println!(
                "{}",
                hex::encode(
                    request(
                        &admin,
                        Session::Sign {
                            leaf,
                            quorum,
                            message: msg.0,
                        }
                    )
                    .await
                )
            )
        }
        Command::Verify { pk, msg, sig } => {
            let valid = wots::verify(&pk.0, &msg.0, &sig.0);
            println!("{valid}");
            exit(!valid as i32);
        }
    }
}

#[derive(Clone)]
struct Hex(Vec<u8>);

impl FromStr for Hex {
    type Err = hex::FromHexError;

    fn from_str(text: &str) -> Result<Hex, hex::FromHexError> {
        hex::decode(text.strip_prefix("0x").unwrap_or(text)).map(Hex)
    }
}

fn parse_batch_size(text: &str) -> Result<usize, String> {
    match text.parse::<usize>() {
        Ok(batch_size) if batch_size > 0 && batch_size.is_multiple_of(LANES) => Ok(batch_size),
        _ => Err(format!("must be a positive multiple of {LANES}")),
    }
}
