//! This module implements the setup and the quorum signing of the leanXMSS note, with the threshold PRF of [PRAWNS](https://eprint.iacr.org/2026/2142).
//!
//! - `F(x)` is the XOR of `H16(k_T || x)` over all terms `T`, so the holders of the terms share
//!   `F(x)` with no messages.
//! - `keygen` derives `P` from a contribution of each operator.
//!   - It derives each term seed from the parts of all its holders.
//!   - It derives each pair key from the parts of both operators.
//! - One commit-reveal carries all contributions and parts, as Section 2.1 of the note asks.
//!   - A commitment hashes the tag `thlxmss-commit`, the sender, the receiver and the reveal.
//!   - Naming both operators is an addition to the note, so a corrupt operator cannot copy a
//!     commitment.
//!   - An echo then carries the hash of all contributions and a hash of the shared seeds.
//!   - An operator aborts on a mismatch.
//!   - The keygen of the prototype sends the parts in one round with no commitments.
//! - `seed_T` keys only the PRF, and `k_ij` keys only the signing masks. The ceremonies use fresh
//!   PRSS keys of their own.
//! - A quorum of `t` operators holds every term, because a term contains only `t - 1` operators.
//!   Each term goes to its first holder in the quorum.
//! - A signer masks its part with `H16(k_ij || x || m || J)` for each co-signer `j`.
//!   - The masks cancel only among parts with the same `x`, `m` and `J`.
//!   - So parts of signings that differ in one of them do not combine.
//! - Before it grinds, a signer checks the opened `F(A_rnd(e))` against the commitment `c_e` that
//!   the bottom tree stores.
//!   - So a corrupt signer cannot change the value and steer the codeword.
//!   - The commitment is an addition to the note.
//!   - In PRAWNS terms, `F(A_rnd(e))` starts one more chain of length one, as for FORS, and `c_e`
//!     is its end in `cpk`.
//! - As the note asks, each pair of operators has one key `k_ij`, and a signer adds one mask for
//!   each co-signer.
//!   - PRAWNS uses the keys `k_{i,j}`, `k_{j,i}` and the masks `mask_{i,1}`, `mask_{i,2}`.

use std::fs;
use std::path::Path;
use std::sync::Arc;

use primitives::load_at;
use tracing::{Instrument, info_span};

use crate::mpc::{self, Group, Key, LANES, Party, Replicated};
use crate::net::{Channel, Network};
use crate::xmss::{
    self, CHAIN_LEN, Digest, Layer, TWEAK_RANDOMIZER, V, layer_address, prf_address,
    truncated_hash, xor,
};

/// One row of `cpk`, the published values of one chain, `y_1 XOR F(X_1)`, `y_2 XOR F(X_2)` and the
/// chain end `y_3`.
pub type ChainRow = [Digest; 3];

pub struct Operator {
    pub id: usize,
    pub public_parameter: Digest,
    /// `sk_i` of PRAWNS, the seeds `k_T` of the terms that this operator holds, in term number
    /// order.
    pub sk: Vec<Key>,
    /// The pair key `k_ij` with each operator `j`, which is zero at `j = i`.
    pub k_ij: Vec<Key>,
}

impl Operator {
    /// The file of an operator holds `t`, the operator number, `P`, the seeds and the pair keys.
    pub fn bytes(&self, t: usize) -> Vec<u8> {
        [
            &[t as u8, self.id as u8][..],
            &self.public_parameter,
            &self.sk.concat(),
            &self.k_ij.concat(),
        ]
        .concat()
    }

    pub fn load(dir: &Path) -> (Group, Operator) {
        let bytes = fs::read(dir.join("operator")).unwrap();
        let group = Group::new(bytes[0] as usize);
        let held = group.held(bytes[1] as usize).len();
        assert_eq!(bytes.len(), 18 + 32 * (held + group.n));
        let keys: Vec<Key> = bytes[18..]
            .chunks(32)
            .map(|k| k.try_into().unwrap())
            .collect();
        let operator = Operator {
            id: bytes[1] as usize,
            public_parameter: bytes[2..18].try_into().unwrap(),
            sk: keys[..held].to_vec(),
            k_ij: keys[held..].to_vec(),
        };
        (group, operator)
    }
}

/// The tag of the commitments of `keygen`.
pub const KEYGEN_COMMIT: &[u8] = b"thlxmss-commit";

/// The tag of the hash of all contributions, which gives `P`.
pub const PARAMETER: &[u8] = b"thlxmss-keygen-parameter";

/// `keygen` in three rounds. Each operator commits to and reveals `[contribution to P || seed parts
/// of the terms shared with j || pair part for j]` for each `j`. Then it echoes `[H(all P
/// contributions) || hash of the seeds shared with j]`, and it aborts on a mismatch.
pub async fn keygen(group: &Group, network: &Arc<Network>) -> Result<Operator, String> {
    let id = network.id;
    let contribution: Key = rand::random();
    let parts = mpc::Parts::random(group);
    let outgoing = (0..group.n)
        .map(|j| [&contribution[..], &parts.reveal(group, id, j)].concat())
        .collect();
    let mut channel = network.channel();
    let received = mpc::commit_reveal(&mut channel, id, KEYGEN_COMMIT, outgoing).await?;
    let contributions: Vec<u8> = (0..group.n)
        .flat_map(|j| match j == id {
            true => contribution.to_vec(),
            false => received[j][..32].to_vec(),
        })
        .collect();
    let contributions_hash = mpc::tagged_hash(PARAMETER, &[&contributions]);
    let revealed: Vec<&[u8]> = received
        .iter()
        .map(|bytes| &bytes[32.min(bytes.len())..])
        .collect();
    let tags: [&[u8]; 2] = [b"thlxmss-keygen-term", b"thlxmss-keygen-pair"];
    let (sk, k_ij) = parts.keys(group, id, &revealed, tags);
    let seed_digest = |j: usize| mpc::shared_keys_hash(group, b"thlxmss-keygen-echo", id, j, &sk);
    let echo = |j: usize| [&contributions_hash[..], &seed_digest(j)].concat();
    let echoes = channel
        .exchange_bytes((0..group.n).map(echo).collect())
        .await?;
    let others = || (0..group.n).filter(|&j| j != id);
    if let Some(j) = others().find(|&j| !echoes[j].starts_with(&contributions_hash)) {
        return Err(format!("operator {j} received other contributions"));
    }
    if let Some(j) = others().find(|&j| echoes[j][32..] != seed_digest(j)) {
        return Err(format!("operator {j} holds other seeds"));
    }
    Ok(Operator {
        id,
        public_parameter: contributions_hash[..16].try_into().unwrap(),
        sk,
        k_ij,
    })
}

pub fn digest_lanes(digest: &Digest) -> [u64; 2] {
    load_at(digest, 0)
}

pub fn lanes_digest(low: u64, high: u64) -> Digest {
    load_at(&[low, high], 0)
}

/// Adds the shares of `F(x)` for each instance into the lanes `lanes` of the held terms. The public
/// part does not change.
pub fn prf_inputs<const W: usize>(
    party: &Party,
    xs: &[Digest],
    blocks: &mut Replicated<W>,
    lanes: [usize; 2],
) {
    for (block, xs) in blocks.blocks_mut().zip(xs.chunks(LANES)) {
        for (slot, x) in xs.iter().enumerate() {
            for (seed, words) in party.seeds.iter().zip(&mut block[1..]) {
                let [low, high] = digest_lanes(&truncated_hash(&[seed, x]));
                words[lanes[0]].0[slot] ^= low;
                words[lanes[1]].0[slot] ^= high;
            }
        }
    }
}

/// `Eval` of PRAWNS. It gives the part of this operator for `F(x)` in the quorum `J`, with the
/// masks of the evaluation context `ec`. The context is the signed message.
pub fn eval(group: &Group, operator: &Operator, quorum: &[usize], x: &Digest, ec: &[u8]) -> Digest {
    let quorum_bits = quorum.iter().map(|&j| 1u32 << j).sum::<u32>().to_le_bytes();
    let terms = group
        .held(operator.id)
        .into_iter()
        .zip(&operator.sk)
        .filter(|&(k, _)| quorum.iter().find(|&&j| group.holds(j, k)) == Some(&operator.id))
        .map(|(_, seed)| truncated_hash(&[seed, x]));
    let masks = quorum
        .iter()
        .filter(|&&j| j != operator.id)
        .map(|&j| truncated_hash(&[&operator.k_ij[j], x, ec, &quorum_bits]));
    terms.chain(masks).fold([0; 16], xor)
}

/// Opens `F` at each `x` among the quorum in one round. Each signer sends its `eval` part to the
/// others and runs `Combine` itself, because the note has no separate combiner.
pub async fn combine(
    channel: &mut Channel,
    group: &Group,
    operator: &Operator,
    quorum: &[usize],
    xs: &[Digest],
    ec: &[u8],
) -> Result<Vec<Digest>, String> {
    let own: Vec<Digest> = xs
        .iter()
        .map(|x| eval(group, operator, quorum, x, ec))
        .collect();
    let received = channel.exchange_bytes(vec![own.concat(); group.n]).await?;
    Ok((0..xs.len())
        .map(|k| {
            quorum.iter().fold([0; 16], |value, &j| {
                let part = if j == operator.id {
                    own[k]
                } else {
                    received[j][16 * k..16 * k + 16].try_into().unwrap()
                };
                xor(value, part)
            })
        })
        .collect())
}

/// Signs the message `m` at the bottom key `e` with a quorum, in two rounds and with no MPC.
///
/// - It runs PRAWNS `Sign` and `Combine` at each signer and returns the full signature, not a
///   share.
/// - `cpk` holds the published rows of the chains of key `e`, and `c_e` is the commitment of
///   `F(A_rnd(e))`.
pub async fn sign(
    network: &Arc<Network>,
    group: &Group,
    operator: &Operator,
    quorum: &[usize],
    e: u32,
    m: &[u8],
    (cpk, c_e): (&[ChainRow], &Digest),
) -> Result<Vec<u8>, String> {
    let layer = Layer::Bottom;
    let mut channel = network.channel_among(quorum);
    let secret = combine(
        &mut channel,
        group,
        operator,
        quorum,
        &[layer_address(TWEAK_RANDOMIZER, layer, 0, e, 0)],
        m,
    )
    .instrument(info_span!("randomizer"))
    .await?[0];
    if xmss::commitment(&operator.public_parameter, e, secret) != *c_e {
        return Err("the randomizer value does not match its commitment".into());
    }
    let reveal = async |digits: &[usize; V]| {
        let xs: Vec<Digest> = (0..V)
            .filter(|&chain| digits[chain] < 3)
            .map(|chain| prf_address(layer, e, chain, digits[chain]))
            .collect();
        let mut opened = combine(&mut channel, group, operator, quorum, &xs, m)
            .instrument(info_span!("reveal", values = xs.len()))
            .await?
            .into_iter();
        // `sigma` holds the WOTS signature, one chain value for each chain. Position 3 is the
        // public chain end, position 0 is `F(X_0)` itself, and positions 1 and 2 unmask the
        // published row.
        let sigma: Vec<Digest> = (0..V)
            .map(|chain| match digits[chain] {
                3 => cpk[chain][2],
                0 => opened.next().unwrap(),
                position => xor(cpk[chain][position - 1], opened.next().unwrap()),
            })
            .collect();
        let public_parameter = &operator.public_parameter;
        match (0..V).find(|&chain| {
            let steps = CHAIN_LEN - 1 - digits[chain];
            xmss::chain(
                public_parameter,
                layer as usize,
                e,
                chain,
                digits[chain],
                steps,
                sigma[chain],
            ) != cpk[chain][2]
        }) {
            Some(chain) => Err(format!("chain {chain} does not lead to its end")),
            None => Ok(sigma),
        }
    };
    xmss::wots_sign(&operator.public_parameter, layer, e, m, &secret, reveal).await
}

#[cfg(test)]
mod tests {
    use std::env;

    use crate::dkg::BATCH_SIZE;
    use crate::mpc::tests::{local_networks, random_keys};
    use crate::mpc::{PRSS_COMMIT, Reshare, commitment};
    use crate::prawns::*;
    use crate::xmss::{address, tweak};

    #[derive(Clone, Copy, Debug)]
    enum Setup {
        Keygen,
        Prss,
    }

    /// The commitment and the reveal of operator 2 to operator `j`, from the tag, `j` and the
    /// reveal of an honest operator.
    type Commit = fn(&[u8], usize, Vec<u8>) -> (Key, Vec<u8>);

    /// The echo of operator 2, from the hash of all `P` contributions in `keygen`.
    type Echo = fn(Key) -> Vec<u8>;

    /// Operator 2 runs the rounds of a setup by hand. All its parts are 7.
    async fn corrupt_setup(
        network: &Arc<Network>,
        t: usize,
        setup: Setup,
        commit: Commit,
        echo: Echo,
    ) {
        let group = Group::new(t);
        let n = group.n;
        let (tag, prefix) = match setup {
            Setup::Keygen => (KEYGEN_COMMIT, 32),
            Setup::Prss => (PRSS_COMMIT, 0),
        };
        let shared = |j: usize| {
            let terms = 0..group.terms.len();
            terms
                .filter(|&k| group.holds(2, k) && group.holds(j, k))
                .count()
        };
        let (commitments, reveals): (Vec<Key>, Vec<Vec<u8>>) = (0..n)
            .map(|j| commit(tag, j, vec![7; prefix + 32 * (shared(j) + 1)]))
            .unzip();
        let mut channel = network.channel();
        match setup {
            Setup::Keygen => {
                let commitments = commitments.iter().map(|c| c.to_vec()).collect();
                channel.exchange_bytes(commitments).await.unwrap();
            }
            Setup::Prss => {
                let parameters = [0, 0, Reshare::Peer as u64, BATCH_SIZE as u64];
                let message = |c: &Key| [parameters, load_at(c, 0)].concat();
                channel
                    .exchange(commitments.iter().map(message).collect())
                    .await
                    .unwrap();
            }
        }
        let revealed = channel.exchange_bytes(reveals).await.unwrap();
        let contributions: Vec<u8> = (0..n)
            .flat_map(|j| match j {
                2 => vec![7; 32],
                _ => revealed[j][..32].to_vec(),
            })
            .collect();
        let echo = echo(mpc::tagged_hash(PARAMETER, &[&contributions]));
        channel.exchange_bytes(vec![echo; n]).await.ok();
    }

    #[test]
    fn keygen_gives_each_key_to_its_holders_in_a_file_that_loads_back() {
        let group = Group::new(2);
        let operators = local_networks(2, async |network, _| {
            keygen(&Group::new(2), &network).await.unwrap()
        });
        let seed = |i: usize, term: usize| {
            let local = group.held(i).iter().position(|&k| k == term).unwrap();
            operators[i].sk[local]
        };
        for term in 0..group.terms.len() {
            let holders: Vec<usize> = (0..group.n).filter(|&i| group.holds(i, term)).collect();
            assert!(
                holders
                    .iter()
                    .all(|&i| seed(i, term) == seed(holders[0], term))
            );
        }
        for (i, j) in [(0, 1), (0, 2), (1, 2)] {
            assert_eq!(operators[i].k_ij[j], operators[j].k_ij[i]);
        }
        let public_parameter = operators[0].public_parameter;
        assert!(
            operators
                .iter()
                .all(|o| o.public_parameter == public_parameter)
        );
        let dir = env::temp_dir().join(format!("threshold-lean-xmss-{}", rand::random::<u64>()));
        fs::create_dir(&dir).unwrap();
        for operator in &operators {
            fs::write(dir.join("operator"), operator.bytes(2)).unwrap();
            let (loaded_group, loaded) = Operator::load(&dir);
            let fields = |o: &Operator| (o.id, o.public_parameter, o.sk.clone(), o.k_ij.clone());
            assert_eq!((loaded_group.t, fields(&loaded)), (2, fields(operator)));
        }
        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn a_wrong_reveal_a_copied_commitment_or_a_wrong_echo_aborts_keygen_and_the_prss_setup() {
        let honest: Commit = |tag, j, message| (commitment(tag, 2, j, &message), message);
        let no_echo: Echo = |_| vec![];
        // The third fault commits to a short message, so only the length check stops it. The fourth
        // fault copies a commitment, which names the receiver as its sender.
        let reveal_faults: [Commit; 4] = [
            |tag, j, message| {
                let mut reveal = message.clone();
                reveal[0] ^= 1;
                (commitment(tag, 2, j, &message), reveal)
            },
            |tag, j, message| (commitment(tag, 2, j, &message), message[..32].to_vec()),
            |tag, j, message| (commitment(tag, 2, j, &message[..8]), message[..8].to_vec()),
            |tag, j, message| (commitment(tag, j, 2, &message), message),
        ];
        let aborts = |error: &str| vec![Some(error.to_string()), Some(error.to_string()), None];
        let wrong_reveal = aborts("operator 2 reveals a value that differs from its commitment");
        let echo_faults: [(Setup, Echo, &str); 3] = [
            (
                Setup::Keygen,
                |_| vec![0; 64],
                "operator 2 received other contributions",
            ),
            (
                Setup::Keygen,
                |p| [&p[..], &[0; 32]].concat(),
                "operator 2 holds other seeds",
            ),
            (
                Setup::Prss,
                |_| vec![0; 32],
                "operator 2 holds other PRSS keys",
            ),
        ];
        // At t = 3, operator 2 gives each receiver other term parts with a matching commitment.
        // So the holders of a term with operator 2 derive different keys, and only the echo
        // between two honest operators stops them.
        let split: Commit = |tag, j, message| {
            let reveal = vec![j as u8; message.len()];
            (commitment(tag, 2, j, &reveal), reveal)
        };
        let other_keys = |j: usize| Some(format!("operator {j} holds other PRSS keys"));
        let split_outcomes = vec![
            other_keys(1),
            other_keys(0),
            None,
            other_keys(0),
            other_keys(0),
        ];
        let faults = [Setup::Keygen, Setup::Prss]
            .into_iter()
            .flat_map(|setup| {
                let wrong_reveal = wrong_reveal.clone();
                reveal_faults.map(|commit| (2, setup, commit, no_echo, wrong_reveal.clone()))
            })
            .chain(echo_faults.map(|(setup, echo, error)| (2, setup, honest, echo, aborts(error))))
            .chain([(3, Setup::Prss, split, no_echo, split_outcomes)]);
        for (t, setup, commit, echo, expected) in faults {
            let outcomes = local_networks(t, async |network, _| match (network.id, setup) {
                (2, _) => {
                    corrupt_setup(&network, t, setup, commit, echo).await;
                    None
                }
                (_, Setup::Keygen) => keygen(&Group::new(t), &network).await.err(),
                (_, Setup::Prss) => {
                    let party = Party::new(
                        Group::new(t),
                        vec![],
                        network,
                        rand::random(),
                        Reshare::Peer,
                        BATCH_SIZE,
                    );
                    party.await.err()
                }
            });
            assert_eq!(outcomes, expected, "{setup:?} at t = {t}");
        }
    }

    #[test]
    fn quorum_parts_combine_into_the_prf() {
        for t in [2, 3, 4] {
            let group = Group::new(t);
            let (all_seeds, all_pairs) = random_keys(&group);
            let operators: Vec<Operator> = (0..group.n)
                .map(|id| Operator {
                    id,
                    public_parameter: rand::random(),
                    sk: group.held(id).iter().map(|&k| all_seeds[k]).collect(),
                    k_ij: all_pairs[id].clone(),
                })
                .collect();
            let x = address(&tweak(0, 2, 3).step(1));
            let expected = all_seeds
                .iter()
                .map(|seed| truncated_hash(&[seed, &x]))
                .fold([0; 16], xor);
            for set in (0..1u32 << group.n).filter(|s| s.count_ones() as usize == t) {
                let quorum: Vec<usize> = (0..group.n).filter(|id| set >> id & 1 == 1).collect();
                let combined = quorum
                    .iter()
                    .map(|&id| eval(&group, &operators[id], &quorum, &x, b"m"))
                    .fold([0; 16], xor);
                assert_eq!(combined, expected);
            }
        }
    }
}
