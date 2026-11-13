//! This module runs the key ceremonies of the leanXMSS note in MPC and stores the trees.
//!
//! - `e` is the index of a one-time key in its layer.
//! - `x_0` holds the PRF inputs `X_0` of the chain starts.
//! - `cpk` holds the published rows of the chains, as in PRAWNS, and `pk` is the public key.
//! - A ceremony splits the chains into chain batches of the batch size, and each batch runs on its
//!   own channel.
//! - A batch takes its inputs from the threshold PRF and hashes its chain steps in MPC.
//! - Then `rerand` reshares its outputs, `mult_verification` checks its AND tuples and the reshare,
//!   and `open` opens the reshared outputs.
//! - Each ceremony starts with its own `Party`, which derives fresh PRSS keys and drops them at the
//!   end.
//! - A retry of the top ceremony reuses the `operator` file. The operators delete that file
//!   together only when the key generation itself failed at an operator.
//! - Each operator starts the batches in batch order and runs at most `concurrency` of them at the
//!   same time.
//!   - So operators with different concurrencies do not deadlock.
//! - The top tree opens the chain ends. A bottom tree also opens the masked middle values, so that
//!   a quorum signs with no MPC.
//! - The top key of a bottom tree signs its root in MPC, because the top tree stores no masked
//!   values.
//! - A bottom tree also opens the commitment `c_e` of each key `e`, in commitment batches of the
//!   batch size.
//!   - The commitment hashes `F(A_rnd(e))` once, at `A_rnd(e)` with step 1.
//!   - The last commitment batch also opens the randomizer value `F(A_rnd)` of the top key, but not
//!     its hash output.
//!   - The input of this value does not depend on the root, so it needs no batch of its own.
//!   - The commitment is an addition to the note. A top key needs none, because the last commitment
//!     batch opens its `F(A_rnd(e))` after the check.

use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::Write;
use std::os::unix::fs::{DirBuilderExt, FileExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::time::Instant;

use futures::stream::{self, StreamExt, TryStreamExt};
use primitives::field::F192;
use tracing::info;

use crate::check;
use crate::circuit::{self, HashPublic};
use crate::mpc::{Group, LANES, Party, Replicated, Reshare, Tuples, Word};
use crate::net::{Channel, Network};
use crate::prawns::{self, ChainRow, Operator, digest_lanes};
use crate::xmss::{
    self, Digest, KEYS, LAYER_HEIGHT, LAYER_SIG_SIZE, Layer, TWEAK_CHAIN, TWEAK_RANDOMIZER, V,
    layer_address, prf_address,
};

/// The default chains or keys of a batch, in 32 words of `LANES` instances.
pub const BATCH_SIZE: usize = 32 * LANES;

fn hash_public(
    public_parameter: &Digest,
    layer: Layer,
    e: u32,
    chain: usize,
    step: usize,
) -> HashPublic {
    let [p0, p1] = digest_lanes(public_parameter);
    let [a0, a1] = digest_lanes(&layer_address(TWEAK_CHAIN, layer, 0, e, step));
    ([p0, p1, a0, a1], [chain as u64, 0])
}

/// Hashes each chain from `F(X_0)` in MPC, for the PRF input `X_0` of each chain in `x_0`, and
/// opens the value at its position.
async fn open_chains(
    party: &Party,
    channel: &mut Channel,
    x_0: &[Digest],
    public: impl Fn(usize, usize) -> Option<HashPublic>,
    position: impl Fn(usize) -> usize,
) -> Result<(Vec<Digest>, u64), String> {
    let words = x_0.len().div_ceil(LANES);
    let last = (0..x_0.len()).map(&position).max().unwrap();
    let mut tuples = Tuples::new(party, padded_words(x_0.len(), last, 2));
    let mut state = Replicated::new(party, words);
    prawns::prf_inputs(party, x_0, &mut state, [0, 1]);
    let mut selected = Replicated::<2>::new(party, words);
    let mut ands = 0;
    for step in 0..=last {
        for (word, (selected, lanes)) in selected.blocks_mut().zip(state.blocks()).enumerate() {
            let slots = (0..LANES).filter(|&slot| x_0.get(LANES * word + slot).is_some());
            for slot in slots.filter(|&slot| position(LANES * word + slot) == step) {
                for (selected, lanes) in selected.iter_mut().zip(lanes) {
                    (selected[0].0[slot], selected[1].0[slot]) =
                        (lanes[0].0[slot], lanes[1].0[slot]);
                }
            }
        }
        if step < last {
            ands += circuit::hash(
                party,
                channel,
                &mut state,
                |instance| public(step, instance),
                &mut tuples,
            )
            .await?;
        }
    }
    let values = checked_open(party, channel, &selected, tuples)
        .await?
        .iter()
        .flat_map(|opened| {
            (0..LANES).map(move |slot| prawns::lanes_digest(opened[0].0[slot], opened[1].0[slot]))
        })
        .take(x_0.len())
        .collect();
    Ok((values, ands))
}

/// Reshares the outputs with `rerand`, checks the AND tuples of the batch and opens the reshared
/// outputs.
async fn checked_open<const W: usize>(
    party: &Party,
    channel: &mut Channel,
    outputs: &Replicated<W>,
    mut tuples: Tuples,
) -> Result<Vec<[Word; W]>, String> {
    let reshared = party.rerand(channel, outputs, &mut tuples).await?;
    check::mult_verification(party, channel, tuples).await?;
    party.open(channel, &reshared).await
}

/// Hashes three chain steps in MPC and opens the row of each chain. The six lanes of `published`
/// hold the three positions, two lanes each.
async fn masked_batch(
    party: &Party,
    channel: &mut Channel,
    addresses: impl Fn(usize) -> Vec<Digest>,
    public: impl Fn(usize, usize) -> Option<HashPublic>,
) -> Result<(Vec<ChainRow>, u64), String> {
    let x_0 = addresses(0);
    let mut tuples = Tuples::new(party, padded_words(x_0.len(), 3, 6));
    let words = x_0.len().div_ceil(LANES);
    let mut state = Replicated::new(party, words);
    prawns::prf_inputs(party, &x_0, &mut state, [0, 1]);
    let mut published = Replicated::<6>::new(party, words);
    let mut ands = 0;
    for step in 0..3 {
        ands += circuit::hash(
            party,
            channel,
            &mut state,
            |instance| public(step, instance),
            &mut tuples,
        )
        .await?;
        for (published, lanes) in published.blocks_mut().zip(state.blocks()) {
            for (published, lanes) in published.iter_mut().zip(lanes) {
                published[2 * step..2 * step + 2].copy_from_slice(&lanes[..2]);
            }
        }
        if step < 2 {
            prawns::prf_inputs(
                party,
                &addresses(step + 1),
                &mut published,
                [2 * step, 2 * step + 1],
            );
        }
    }
    let cpk = checked_open(party, channel, &published, tuples)
        .await?
        .iter()
        .flat_map(|opened| {
            (0..LANES).map(move |slot| {
                [0, 1, 2]
                    .map(|p| prawns::lanes_digest(opened[2 * p].0[slot], opened[2 * p + 1].0[slot]))
            })
        })
        .take(x_0.len())
        .collect();
    Ok((cpk, ands))
}

/// Hashes `F(A_rnd(e))` of each bottom key `e` once in MPC and opens its commitment `c_e`. With
/// `top_key`, it also opens `F(A_rnd)` of that top key as the last value.
async fn commitment_batch(
    party: &Party,
    channel: &mut Channel,
    public_parameter: &Digest,
    keys: &[u32],
    top_key: Option<u32>,
) -> Result<(Vec<Digest>, u64), String> {
    let address = |e, step| layer_address(TWEAK_RANDOMIZER, Layer::Bottom, 0, e, step);
    let top = top_key.map(|e| layer_address(TWEAK_RANDOMIZER, Layer::Top, 0, e, 0));
    let x_0: Vec<Digest> = keys.iter().map(|&e| address(e, 0)).chain(top).collect();
    let [p0, p1] = digest_lanes(public_parameter);
    let public = |_, instance: usize| {
        let [a0, a1] = digest_lanes(&address(*keys.get(instance)?, 1));
        Some(([p0, p1, a0, a1], [0, 0]))
    };
    let position = |instance| usize::from(instance < keys.len());
    open_chains(party, channel, &x_0, public, position).await
}

/// Signs the root of a bottom tree with its top key, in MPC, from the opened randomizer value
/// `secret` of the key.
async fn top_signature(
    party: &Party,
    public_parameter: Digest,
    bottom: u32,
    root: Digest,
    secret: Digest,
) -> Result<Vec<u8>, String> {
    let mut channel = party.network.channel();
    let reveal = async |digits: &[usize; V]| {
        let x_0: Vec<Digest> = (0..V)
            .map(|chain| prf_address(Layer::Top, bottom, chain, 0))
            .collect();
        let public = |step, chain| {
            (chain < V).then(|| hash_public(&public_parameter, Layer::Top, bottom, chain, step))
        };
        let opened = open_chains(party, &mut channel, &x_0, public, |chain| digits[chain]);
        Ok(opened.await?.0)
    };
    xmss::wots_sign(
        &public_parameter,
        Layer::Top,
        bottom,
        &root,
        &secret,
        reveal,
    )
    .await
}

/// The tuple words of each held term in a batch of `instances` instances that hash `hashes` times
/// and reshare `outputs` lanes in `rerand`.
fn tuple_words(instances: usize, hashes: usize, outputs: usize) -> usize {
    instances * (hashes * circuit::gates() + outputs)
}

/// The tuple words of `tuple_words` for full words of `LANES` instances, with the padding of the
/// check.
fn padded_words(instances: usize, hashes: usize, outputs: usize) -> usize {
    let words = tuple_words(instances.next_multiple_of(LANES), hashes, outputs);
    check::SLICES * check::slice_length(words)
}

/// The estimated bytes of a full chain batch and the padding of its check. A chain hashes 3 times
/// and reshares 6 output lanes, and the tuples of all held terms coexist with the check vectors `x`
/// and `y` in `Slices::materialize`.
fn chain_batch_estimate(party: &Party) -> (usize, f64) {
    let words = tuple_words(party.batch_size, 3, 6);
    let padded = padded_words(party.batch_size, 3, 6);
    // `lift` gives `x` and `y` one element for each bit of a slice word.
    let vector = 64 * (padded / check::SLICES);
    let bytes = padded * 3 * party.held.len() * size_of::<u64>() + 2 * vector * size_of::<F192>();
    (bytes, padded as f64 / words as f64)
}

/// The peak resident set size of this process, `VmHWM`, in bytes.
fn peak_rss() -> u64 {
    let status = fs::read_to_string("/proc/self/status").unwrap();
    let line = status.lines().find_map(|line| line.strip_prefix("VmHWM:"));
    let kilobytes = line.unwrap().trim().strip_suffix(" kB").unwrap();
    1024 * kilobytes.parse::<u64>().unwrap()
}

/// Runs the MPC for all chains of `keys`, with at most `concurrency` batches in flight.
///
/// - A bottom tree also opens the commitments of its keys and then the randomizer value of its top
///   key.
/// - The rounds are the most rounds of a chain batch and of a commitment batch.
async fn ceremony(
    party: &Arc<Party>,
    public_parameter: Digest,
    layer: Layer,
    keys: &[u32],
    concurrency: usize,
) -> Result<
    (
        Vec<Digest>,
        Vec<ChainRow>,
        Vec<Digest>,
        Option<Digest>,
        u64,
        [u64; 2],
    ),
    String,
> {
    let bottom = keys[0] >> LAYER_HEIGHT;
    let tree = match layer {
        Layer::Top => "top".to_string(),
        Layer::Bottom => format!("bottom {bottom}"),
    };
    let chains: Arc<Vec<(u32, usize)>> = Arc::new(
        keys.iter()
            .flat_map(|&e| (0..V).map(move |chain| (e, chain)))
            .collect(),
    );
    let committed: Arc<Vec<u32>> = Arc::new(match layer {
        Layer::Top => vec![],
        Layer::Bottom => keys.to_vec(),
    });
    let (sent, start) = (party.network.sent.load(Ordering::Relaxed), Instant::now());
    let batch_size = party.batch_size;
    let chain_batches = chains.len().div_ceil(batch_size);
    // The channels open in batch order before any batch runs, so all operators give each batch the
    // same tag. The commitment batches follow the chain batches.
    let channels: Vec<Channel> = (0..chain_batches + committed.len().div_ceil(batch_size))
        .map(|_| party.network.channel())
        .collect();
    let (bytes, padding) = chain_batch_estimate(party);
    info!(
        "{tree}: {chain_batches} batches of {batch_size} chains and {} batches of {batch_size} keys, {concurrency} in flight, about {bytes} bytes of tuples and check vectors for each chain batch and {} bytes in flight, check padding {padding:.3}",
        channels.len() - chain_batches,
        concurrency * bytes
    );
    let mut batches: Vec<_> = stream::iter(channels.into_iter().enumerate())
        .map(|(b, mut channel)| {
            let (party, chains, committed) = (party.clone(), chains.clone(), committed.clone());
            tokio::spawn(async move {
                if let Some(k) = b.checked_sub(chain_batches) {
                    let keys =
                        &committed[k * batch_size..committed.len().min((k + 1) * batch_size)];
                    let top_key = ((k + 1) * batch_size >= committed.len()).then_some(bottom);
                    let (commitments, ands) =
                        commitment_batch(&party, &mut channel, &public_parameter, keys, top_key)
                            .await?;
                    return Ok((b, commitments, vec![], ands, channel.rounds));
                }
                let chains = &chains[b * batch_size..chains.len().min((b + 1) * batch_size)];
                let addresses = |position| -> Vec<Digest> {
                    chains
                        .iter()
                        .map(|&(e, chain)| prf_address(layer, e, chain, position))
                        .collect()
                };
                let public = |step, instance: usize| {
                    let &(e, chain) = chains.get(instance)?;
                    Some(hash_public(&public_parameter, layer, e, chain, step))
                };
                let (ends, cpk, ands) = if layer == Layer::Top {
                    let (ends, ands) =
                        open_chains(&party, &mut channel, &addresses(0), public, |_| 3).await?;
                    (ends, vec![], ands)
                } else {
                    let (cpk, ands) = masked_batch(&party, &mut channel, addresses, public).await?;
                    (cpk.iter().map(|row: &ChainRow| row[2]).collect(), cpk, ands)
                };
                Ok::<_, String>((b, ends, cpk, ands, channel.rounds))
            })
        })
        .buffer_unordered(concurrency)
        .map(Result::unwrap)
        .try_collect()
        .await?;
    batches.sort_by_key(|batch| batch.0);
    let ands = batches.iter().map(|batch| batch.3).sum();
    let commitment_batches = batches.split_off(chain_batches);
    let rounds = [&batches, &commitment_batches]
        .map(|batches| batches.iter().map(|batch| batch.4).max().unwrap_or(0));
    let elapsed = start.elapsed();
    info!(
        "{tree}: {} keys in {elapsed:.1?} at {:.1} batches per second, {} batches of {batch_size} chains in {} rounds, {} batches of {batch_size} keys in {} rounds, {ands} ANDs, {} bytes sent, {} bytes of peak RSS",
        keys.len(),
        (batches.len() + commitment_batches.len()) as f64 / elapsed.as_secs_f64(),
        batches.len(),
        rounds[0],
        commitment_batches.len(),
        rounds[1],
        party.network.sent.load(Ordering::Relaxed) - sent,
        peak_rss()
    );
    let ends: Vec<Digest> = batches
        .iter()
        .flat_map(|batch| batch.1.iter().copied())
        .collect();
    let cpk: Vec<ChainRow> = batches.into_iter().flat_map(|batch| batch.2).collect();
    let mut commitments: Vec<Digest> = commitment_batches
        .into_iter()
        .flat_map(|batch| batch.1)
        .collect();
    let randomizer = (layer == Layer::Bottom).then(|| commitments.pop().unwrap());
    let leaves = ends
        .chunks(V)
        .zip(keys)
        .map(|(ends, &e)| {
            xmss::wots_leaf_hash(
                &public_parameter,
                layer as usize,
                e,
                ends.try_into().unwrap(),
            )
        })
        .collect();
    Ok((leaves, cpk, commitments, randomizer, ands, rounds))
}

async fn party(
    group: Group,
    operator: &Operator,
    network: &Arc<Network>,
    reshare: Reshare,
    batch_size: usize,
) -> Result<Arc<Party>, String> {
    let party = Party::new(
        group,
        operator.sk.clone(),
        network.clone(),
        reshare,
        batch_size,
    );
    Ok(Arc::new(party.await?))
}

pub async fn new_top_tree(
    dir: &Path,
    network: &Arc<Network>,
    reshare: Reshare,
    batch_size: usize,
    concurrency: usize,
) -> Result<Vec<u8>, String> {
    let (group, operator) = match dir.join("operator").exists() {
        true => Operator::load(dir),
        false => {
            let group = Group::new(network.n.div_ceil(2));
            let operator = prawns::keygen(&group, network).await?;
            DirBuilder::new()
                .recursive(true)
                .mode(0o700)
                .create(dir)
                .unwrap();
            OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(true)
                .mode(0o600)
                .open(dir.join("operator"))
                .and_then(|mut file| file.write_all(&operator.bytes(group.t)))
                .unwrap();
            (group, operator)
        }
    };
    let party = party(group, &operator, network, reshare, batch_size).await?;
    let keys: Vec<u32> = (0..KEYS as u32).collect();
    let (leaves, ..) = ceremony(
        &party,
        operator.public_parameter,
        Layer::Top,
        &keys,
        concurrency,
    )
    .await?;
    let pk = [
        xmss::levels(&operator.public_parameter, Layer::Top, 0, leaves.clone())[LAYER_HEIGHT][0],
        operator.public_parameter,
    ]
    .concat();
    fs::write(dir.join("top"), leaves.concat()).unwrap();
    fs::write(dir.join("pk"), &pk).unwrap();
    Ok(pk)
}

pub async fn new_bottom_tree(
    dir: &Path,
    network: &Arc<Network>,
    bottom: u32,
    reshare: Reshare,
    batch_size: usize,
    concurrency: usize,
) -> Result<(), String> {
    let (group, operator) = Operator::load(dir);
    let party = party(group, &operator, network, reshare, batch_size).await?;
    let public_parameter = operator.public_parameter;
    let keys: Vec<u32> = (0..KEYS as u32)
        .map(|k| bottom << LAYER_HEIGHT | k)
        .collect();
    let (leaves, cpk, commitments, randomizer, ..) =
        ceremony(&party, public_parameter, Layer::Bottom, &keys, concurrency).await?;
    let levels = xmss::levels(&public_parameter, Layer::Bottom, bottom, leaves);
    let root = levels[LAYER_HEIGHT][0];
    let top = xmss::levels(
        &public_parameter,
        Layer::Top,
        0,
        digests(&fs::read(dir.join("top")).unwrap()),
    );
    let top_signature =
        top_signature(&party, public_parameter, bottom, root, randomizer.unwrap()).await?;
    let top_signature = [top_signature, xmss::path(&top, bottom as usize)].concat();
    if xmss::layer_root(&public_parameter, Layer::Top, bottom, &root, &top_signature)
        != Some(top[LAYER_HEIGHT][0])
    {
        return Err("the top signature does not lead to the top root".into());
    }
    BottomTree::write(dir, bottom, &levels, &cpk, &top_signature, &commitments);
    Ok(())
}

pub fn tree_file(dir: &Path, bottom: u32) -> PathBuf {
    dir.join(format!("tree{bottom}"))
}

/// The file of a bottom tree holds its Merkle levels from the leaves to the root. The rows of its
/// chains, its top signature and the commitments of its keys follow.
pub struct BottomTree(File);

const NODES: usize = 2 * KEYS - 1;

impl BottomTree {
    fn write(
        dir: &Path,
        bottom: u32,
        levels: &[Vec<Digest>],
        cpk: &[ChainRow],
        top_signature: &[u8],
        commitments: &[Digest],
    ) {
        let nodes = levels.iter().flatten().flatten();
        let cpk = cpk.iter().flatten().flatten();
        let commitments = commitments.iter().flatten();
        let bytes: Vec<u8> = nodes
            .chain(cpk)
            .chain(top_signature)
            .chain(commitments)
            .copied()
            .collect();
        fs::write(tree_file(dir, bottom), bytes).unwrap();
    }

    pub fn open(dir: &Path, bottom: u32) -> BottomTree {
        BottomTree(File::open(tree_file(dir, bottom)).unwrap())
    }

    fn read(&self, offset: usize, length: usize) -> Vec<u8> {
        let mut bytes = vec![0; length];
        self.0.read_exact_at(&mut bytes, offset as u64).unwrap();
        bytes
    }

    pub fn path(&self, leaf: usize) -> Vec<u8> {
        (0..LAYER_HEIGHT)
            .flat_map(|level| {
                let nodes_before_level = 2 * (KEYS - (KEYS >> level));
                self.read(16 * (nodes_before_level + ((leaf >> level) ^ 1)), 16)
            })
            .collect()
    }

    pub fn cpk(&self, leaf: usize) -> Vec<ChainRow> {
        self.read(16 * NODES + 48 * V * leaf, 48 * V)
            .chunks(48)
            .map(|row| digests(row).try_into().unwrap())
            .collect()
    }

    pub fn top_signature(&self) -> Vec<u8> {
        self.read(16 * NODES + 48 * V * KEYS, LAYER_SIG_SIZE)
    }

    pub fn commitment(&self, leaf: usize) -> Digest {
        let offset = 16 * NODES + 48 * V * KEYS + LAYER_SIG_SIZE + 16 * leaf;
        self.read(offset, 16).try_into().unwrap()
    }
}

fn digests(bytes: &[u8]) -> Vec<Digest> {
    bytes.chunks(16).map(|d| d.try_into().unwrap()).collect()
}

#[cfg(test)]
mod tests {
    use std::array::from_fn;
    use std::env;

    use signatures::lean_xmss::{codeword, message_digest};

    use crate::dkg::*;
    use crate::mpc::Key;
    use crate::mpc::tests::{local_networks, local_operators, local_parties, random_keys};
    use crate::net::pack;
    use crate::serve;
    use crate::xmss::{truncated_hash, xor};

    /// The threshold PRF `F(x)` from the seeds of all terms.
    fn prf(all_seeds: &[Key], x: Digest) -> Digest {
        all_seeds
            .iter()
            .map(|seed| truncated_hash(&[seed, &x]))
            .fold([0; 16], xor)
    }

    /// The leaves, the rows, the opened commitments and the randomizer value of a ceremony. Only a
    /// bottom tree has a randomizer value, the one of its top key.
    fn trusted_dealer(
        all_seeds: &[Key],
        public_parameter: Digest,
        layer: Layer,
        keys: &[u32],
    ) -> (Vec<Digest>, Vec<ChainRow>, Vec<Digest>, Option<Digest>) {
        let f = |x: Digest| prf(all_seeds, x);
        let cpk: Vec<ChainRow> = keys
            .iter()
            .flat_map(|&e| (0..V).map(move |chain| (e, chain)))
            .map(|(e, chain)| {
                let address = |position| prf_address(layer, e, chain, position);
                let value = |steps| {
                    xmss::chain(
                        &public_parameter,
                        layer as usize,
                        e,
                        chain,
                        0,
                        steps,
                        f(address(0)),
                    )
                };
                [
                    xor(value(1), f(address(1))),
                    xor(value(2), f(address(2))),
                    value(3),
                ]
            })
            .collect();
        let leaves = cpk
            .chunks(V)
            .zip(keys)
            .map(|(cpk, &e)| {
                let ends = from_fn(|chain| cpk[chain][2]);
                xmss::wots_leaf_hash(&public_parameter, layer as usize, e, &ends)
            })
            .collect();
        let commitments = match layer {
            Layer::Top => vec![],
            Layer::Bottom => keys
                .iter()
                .map(|&e| {
                    let value = f(layer_address(TWEAK_RANDOMIZER, layer, 0, e, 0));
                    xmss::commitment(&public_parameter, e, value)
                })
                .collect(),
        };
        let randomizer = (layer == Layer::Bottom).then(|| {
            let top_key = keys[0] >> LAYER_HEIGHT;
            f(layer_address(TWEAK_RANDOMIZER, Layer::Top, 0, top_key, 0))
        });
        (leaves, cpk, commitments, randomizer)
    }

    /// Runs a ceremony of the keys 5 and 9000 with `P = [9; 16]` at the reshare mode, batch size
    /// and concurrency of each operator.
    ///
    /// It asserts that every operator opens the values of the trusted dealer, and it returns the
    /// ANDs and rounds of each operator.
    fn local_ceremony(layer: Layer, operators: &[(Reshare, usize, usize)]) -> Vec<(u64, [u64; 2])> {
        let (public_parameter, keys) = ([9; 16], [5, 9_000]);
        let parameters: Vec<(Reshare, usize)> = operators
            .iter()
            .map(|&(reshare, batch_size, _)| (reshare, batch_size))
            .collect();
        let t = operators.len().div_ceil(2);
        let outcomes = local_operators(t, &parameters, async |party, all_seeds| {
            let party = Arc::new(party.unwrap());
            let concurrency = operators[party.id].2;
            let outcome = ceremony(&party, public_parameter, layer, &keys, concurrency).await;
            (outcome.unwrap(), all_seeds)
        });
        outcomes
            .into_iter()
            .map(
                |((leaves, cpk, commitments, randomizer, ands, rounds), all_seeds)| {
                    let dealt = trusted_dealer(&all_seeds, public_parameter, layer, &keys);
                    assert_eq!(leaves, dealt.0);
                    assert!(layer == Layer::Top || cpk == dealt.1);
                    assert_eq!((commitments, randomizer), (dealt.2, dealt.3));
                    (ands, rounds)
                },
            )
            .collect()
    }

    #[test]
    fn a_ceremony_matches_the_trusted_dealer_at_each_batch_size_with_36288_ands_per_hash() {
        // The rounds of a chain batch and of a commitment batch. The commitment batch holds one
        // word of keys, and a full commitment batch of 128 keys takes 100 or 76 rounds.
        let expected_rounds = |reshare, batch_size| match (reshare, batch_size) {
            (Reshare::Collector, 128) => Some([198, 90]),
            (Reshare::Peer, 128) => Some([126, 66]),
            (Reshare::Collector, 4) => Some([188, 90]),
            (Reshare::Peer, 4) => Some([116, 66]),
            _ => None,
        };
        let modes = [Reshare::Collector, Reshare::Peer];
        let trees = [(2, Layer::Bottom), (3, Layer::Bottom), (2, Layer::Top)];
        for batch_size in [4, 64, 128, 256] {
            for ((t, layer), reshare) in trees
                .into_iter()
                .flat_map(|tree| modes.map(|mode| (tree, mode)))
            {
                let expected_rounds =
                    expected_rounds(reshare, batch_size).map(|[chain, commitment]| match layer {
                        Layer::Top => [chain, 0],
                        Layer::Bottom => [chain, commitment],
                    });
                // Each of the two keys hashes its chains 3 times. A word holds `LANES` instances,
                // so the commitments of the two keys take the hashes of one word.
                let hashes = 2 * V * 3 + if layer == Layer::Bottom { LANES } else { 0 };
                // The operators run different concurrencies, which must not deadlock.
                let operators: Vec<_> = (0..2 * t - 1)
                    .map(|id| (reshare, batch_size, 2 << id))
                    .collect();
                for (ands, rounds) in local_ceremony(layer, &operators) {
                    assert_eq!(ands, hashes as u64 * 36_288);
                    if let Some(expected_rounds) = expected_rounds {
                        assert_eq!(rounds, expected_rounds, "{reshare:?} at {batch_size}");
                    }
                }
            }
        }
    }

    #[test]
    fn the_rerand_the_check_and_the_opening_of_a_bottom_chain_batch_send_the_same_bytes_in_both_modes()
     {
        // The bytes that each operator sends in the rerand of the six lanes of 128 chains, in the
        // check and in the opening.
        for (t, expected) in [(2, (6_144, 2_720, 6_176)), (3, (12_288, 5_952, 24_832))] {
            for reshare in [Reshare::Collector, Reshare::Peer] {
                let sent = local_parties(t, reshare, async |party, _| {
                    let (words, mut channel) = (BATCH_SIZE / LANES, party.network.channel());
                    let mut state = Replicated::new(&party, words);
                    let mut tuples = Tuples::new(&party, padded_words(BATCH_SIZE, 3, 6));
                    for _ in 0..3 {
                        let hash =
                            circuit::hash(&party, &mut channel, &mut state, |_| None, &mut tuples);
                        hash.await.unwrap();
                    }
                    let sent = || party.network.sent.load(Ordering::Relaxed);
                    let start = sent();
                    let rows = Replicated::<6>::new(&party, words);
                    let reshared = party
                        .rerand(&mut channel, &rows, &mut tuples)
                        .await
                        .unwrap();
                    let rerandomized = sent();
                    check::mult_verification(&party, &mut channel, tuples)
                        .await
                        .unwrap();
                    let checked = sent();
                    party.open(&mut channel, &reshared).await.unwrap();
                    (
                        rerandomized - start,
                        checked - rerandomized,
                        sent() - checked,
                    )
                });
                assert_eq!(sent, vec![expected; 2 * t - 1], "t = {t}, {reshare:?}");
            }
        }
    }

    #[test]
    fn a_tampered_contribution_to_an_and_gate_or_to_the_rerand_in_batch_3_fails_the_check_at_every_operator()
     {
        // `establish` in `Party::new` takes channel 1, so batch `b` has the tag `2 + b`. Round 0 is
        // the first AND layer, and round 144 is the rerand after the 72 AND layers of 2 rounds.
        // Operator 0 flips every message of the round and the copy that it keeps, so the holders
        // of each term agree and only the multiplication check catches it.
        for round in [0, 144] {
            let outcomes = local_operators(2, &[(Reshare::Collector, 4); 3], async |party, _| {
                let mut party = party.unwrap();
                if party.id == 0 {
                    party.tamper = match round {
                        0 => flip_in_batch_3::<0>,
                        _ => flip_in_batch_3::<144>,
                    };
                }
                let party = Arc::new(party);
                let outcome = ceremony(&party, [9; 16], Layer::Bottom, &[5, 9_000], 1).await;
                outcome.err()
            });
            let failed = Some("the AND tuples fail the check".to_string());
            assert_eq!(outcomes, vec![failed; 3], "round {round}");
        }
    }

    #[test]
    fn a_retry_of_a_failed_top_ceremony_keeps_the_operator_files() {
        // Operator 2 uses another batch size, so each top ceremony fails after the keygen.
        let run = rand::random::<u64>();
        let dirs: Vec<PathBuf> = (0..3)
            .map(|id| env::temp_dir().join(format!("threshold-lean-xmss-{run}-{id}")))
            .collect();
        let top_tree = || {
            local_networks(2, async |network, _| {
                let (dir, batch_size) = (&dirs[network.id], [128, 128, 64][network.id]);
                let outcome = new_top_tree(dir, &network, Reshare::Peer, batch_size, 1).await;
                (outcome.err(), fs::read(dir.join("operator")).unwrap())
            })
        };
        let first = top_tree();
        let failed = Some("the operators use the batch sizes [128, 128, 64]".to_string());
        assert!(first.iter().all(|(error, _)| *error == failed));
        assert_eq!(top_tree(), first);
        dirs.iter().for_each(|dir| fs::remove_dir_all(dir).unwrap());
    }

    fn flip_in_batch_3<const ROUND: u64>(
        channel: &Channel,
        mut outgoing: Vec<Vec<u64>>,
    ) -> Vec<Vec<u64>> {
        if channel.tag == 2 + 3 && channel.rounds == ROUND {
            let messages = outgoing.iter_mut().filter(|words| !words.is_empty());
            messages.for_each(|words| words[0] ^= 1);
        }
        outgoing
    }

    #[test]
    fn a_quorum_and_the_mpc_sign_layers_that_lead_to_the_roots_of_their_paths_and_a_tampered_row_or_commitment_aborts_the_quorum()
     {
        let (public_parameter, message) = ([9; 16], [3; 32]);
        let path: Vec<u8> = (0..LAYER_HEIGHT * 16).map(|byte| byte as u8).collect();
        let leads_to_root = |layer, message: &[u8], signature: Vec<u8>, leaf| {
            let signature = [signature, path.clone()].concat();
            let root = xmss::layer_root(&public_parameter, layer, 9, message, &signature);
            assert_eq!(
                root,
                Some(xmss::tests::fold(&public_parameter, layer, 9, leaf, &path))
            );
        };
        let (_, all_pairs) = random_keys(&Group::new(2));
        local_parties(2, Reshare::Collector, async |party, all_seeds| {
            let (leaves, cpk, commitments, _) =
                trusted_dealer(&all_seeds, public_parameter, Layer::Bottom, &[9]);
            let (top_leaves, ..) = trusted_dealer(&all_seeds, public_parameter, Layer::Top, &[9]);
            let secret = prf(
                &all_seeds,
                layer_address(TWEAK_RANDOMIZER, Layer::Top, 0, 9, 0),
            );
            let signature = top_signature(&party, public_parameter, 9, leaves[0], secret).await;
            leads_to_root(Layer::Top, &leaves[0], signature.unwrap(), top_leaves[0]);
            let quorum = [1, 2];
            if !quorum.contains(&party.id) {
                return;
            }
            let operator = Operator {
                id: party.id,
                public_parameter,
                sk: party.seeds.clone(),
                k_ij: all_pairs[party.id].clone(),
            };
            let sign = async |cpk: &[ChainRow], c_e: &Digest| {
                let sent = party.network.sent.load(Ordering::Relaxed);
                let outcome = prawns::sign(
                    &party.network,
                    &party.group,
                    &operator,
                    &quorum,
                    9,
                    &message,
                    (cpk, c_e),
                );
                (
                    outcome.await,
                    party.network.sent.load(Ordering::Relaxed) - sent,
                )
            };
            let signature = sign(&cpk, &commitments[0]).await.0.unwrap();
            let randomizer = signature[..16].try_into().unwrap();
            let digits = codeword(&message_digest(
                &public_parameter,
                0,
                9,
                &randomizer,
                &message,
            ));
            leads_to_root(Layer::Bottom, &message, signature, leaves[0]);
            // The signing grinds to the same digits again. Only the row of the last chain below
            // position 3 changes, so every chain must be checked.
            let chain = digits
                .unwrap()
                .iter()
                .rposition(|&digit| digit < 3)
                .unwrap();
            let mut tampered_rows = cpk.clone();
            tampered_rows[chain] = tampered_rows[chain].map(|digest| xor(digest, [1; 16]));
            let outcome = sign(&tampered_rows, &commitments[0]).await.0;
            assert_eq!(
                outcome,
                Err(format!("chain {chain} does not lead to its end"))
            );
            // Each signer sends only its part of `F(A_rnd(e))` to its co-signer, so `reveal` never
            // runs.
            let tampered_commitment = xor(commitments[0], [1; 16]);
            assert_eq!(
                sign(&cpk, &tampered_commitment).await,
                (
                    Err("the randomizer value does not match its commitment".to_string()),
                    8 * pack(&[0; 16]).len() as u64,
                )
            );
        });
    }

    #[test]
    fn a_quorum_signs_a_certified_message_and_signs_it_again_on_a_second_request() {
        let (public_parameter, message, quorum) = ([9; 16], [3; 32], [1, 2]);
        let path: Vec<u8> = (0..LAYER_HEIGHT * 16).map(|byte| byte as u8).collect();
        let group = Group::new(2);
        let (_, all_pairs) = random_keys(&group);
        let run = rand::random::<u64>();
        let outcomes = local_networks(2, async |network, all_seeds| {
            let dir = env::temp_dir().join(format!("threshold-lean-xmss-{run}-{}", network.id));
            fs::create_dir(&dir).unwrap();
            let (leaves, cpk, commitments, _) =
                trusted_dealer(&all_seeds, public_parameter, Layer::Bottom, &[9]);
            let operator = Operator {
                id: network.id,
                public_parameter,
                sk: group
                    .held(network.id)
                    .iter()
                    .map(|&k| all_seeds[k])
                    .collect(),
                k_ij: all_pairs[network.id].clone(),
            };
            // Each request runs its two sessions on their own networks, as an operator does.
            let request = async |session: u32| {
                serve::acknowledge(&dir, &network.session(session), 9, &message).await?;
                if !quorum.contains(&network.id) {
                    return Ok(None);
                }
                serve::certified(&dir, 9, &message)?;
                let cpk = (&cpk[..], &commitments[0]);
                let network = network.session(session + 1);
                let signature =
                    prawns::sign(&network, &group, &operator, &quorum, 9, &message, cpk).await?;
                let root = xmss::layer_root(
                    &public_parameter,
                    Layer::Bottom,
                    9,
                    &message,
                    &[signature.clone(), path.clone()].concat(),
                );
                let leads_to_root = root
                    == Some(xmss::tests::fold(
                        &public_parameter,
                        Layer::Bottom,
                        9,
                        leaves[0],
                        &path,
                    ));
                Ok::<_, String>(Some((signature, leads_to_root)))
            };
            let outcome = (request(1).await, request(3).await);
            fs::remove_dir_all(&dir).unwrap();
            outcome
        });
        assert_eq!(outcomes[0], (Ok(None), Ok(None)));
        for (first, second) in &outcomes[1..] {
            assert!(first.as_ref().unwrap().as_ref().unwrap().1);
            assert_eq!(first, second);
        }
    }
}
