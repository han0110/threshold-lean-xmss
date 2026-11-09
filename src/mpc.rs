//! This module implements the replicated secret sharing of [Cramer, Damgard and Ishai](https://doi.org/10.1007/978-3-540-30576-7_19) among `n = 2t - 1` operators, and the gadgets of `doc/dkg.md` on it. It follows [`structure.rs`](https://github.com/TomWambsgans/sphincs.art/blob/df77d5671f70ba4959264183296777bdddec778d/crates/rss/src/structure.rs), [`engine.rs`](https://github.com/TomWambsgans/sphincs.art/blob/df77d5671f70ba4959264183296777bdddec778d/crates/rss/src/engine.rs) and [`setup.rs`](https://github.com/TomWambsgans/sphincs.art/blob/df77d5671f70ba4959264183296777bdddec778d/crates/rss/src/setup.rs) of the leanSPHINCS prototype.
//!
//! - The terms are the sets of `t - 1` operators, and an operator holds each term that does not
//!   contain it.
//! - A block of shares holds the public part first and then one part for each held term, in the
//!   order of `held`.
//! - `rand`, `mul` and `conv` send nothing.
//!   - `rand` gives each holder of a term `T` its pseudorandom value `r_T`.
//!   - `conv` gives the Shamir share of a replicated value.
//! - At an AND gate, `mul` gives operator `i` the XOR `v_i` of `a_A & b_B` over its pairs of terms
//!   `(A, B)`.
//! - Then `reshare` adds the share `zeta_i` of a pairwise zero sharing.
//! - In collector mode, a rotation gives each gate a term `T*` and a collector `kappa` in
//!   `Hold(T*)`. Every other term is `z_T = r_T`.
//!   - Each `i != kappa` sends `u_i = v_i ^ zeta_i ^ XOR_{T != T*, owner(T) = i} r_T` to `kappa`.
//!     Then `kappa` sends `z_T* = XOR_i u_i` to `Hold(T*) \ {kappa}`.
//! - In peer mode, operator `i` fills the term `T_i` of the operators `i + 1` to `i + t - 1` modulo
//!   `n`.
//!   - These terms form `C`, and every other term is `z_T = r_T`.
//!   - Each `i` sends `u_i = v_i ^ zeta_i ^ XOR_{T not in C, owner(T) = i} r_T` to `Hold(T_i) \
//!     {i}`. Then `z_T_i = u_i`, and the gate takes one round in place of two.
//!   - For `n = 3`, `C` contains all three terms, and peer mode is the multiplication of [Araki et al. CCS'16](https://eprint.iacr.org/2016/768).
//! - The generalization of peer mode to `n > 3` comes from this code. A coalition `D` of `t - 1`
//!   operators lacks only the term `D`.
//!   - If `D` is not in `C`, then `z_D = r_D`, and the honest `u_i` that `D` sees have masks of
//!     full rank.
//!   - If `D = T_i`, then `u_i` goes only to honest holders, and the other honest values are
//!     independent.
//! - Each holder of a filled term adds its new values to the running hash `h_T` of the term.
//! - `establish` derives fresh PRSS keys `prss_T` and `prss_ij` in each ceremony, with the
//!   commit-reveal-echo of the keygen of the note.
//!   - All streams of `rand` and of the zero sharing use only these keys, as the pseudorandom
//!     sharings of Cramer, Damgard and Ishai.
//!   - So no stream depends on the seeds `seed_T` or the pair keys `K_ij` that the ceremony outputs
//!     to signing.
//! - At the end of each ceremony, a production implementation erases its private ceremony state, as
//!   `doc/dkg.md`, Section 3.3, states.
//! - `rerand` reshares each output before it opens, and the check verifies the reshare.
//!   - So `open` reveals only a fresh sharing of the output value.
//! - A coin is a pseudorandom sharing that opens robustly in the round after the messages that it
//!   checks.
//!   - As in the paper and the prototype, this assumes synchronous rounds.
//!
//! The module differs from the prototype in these points.
//!
//! - The Shamir shares use the leanVM field `F192` in place of GF(2^128).
//! - A gate covers one 64-bit lane of a circuit layer for all instances of the batch. A `Word`
//!   holds this lane for four instances.
//! - The pseudorandom streams use AES-128 in place of Keccak-256 with labeled tags.
//!   - The AES key hashes the label `rss-prss`, a PRSS key and the session value.
//!   - A stream depends on the channel, its round and an index, and a coin key hashes the channel
//!     tag, the round and the opened value.
//! - The prototype derives its PRSS keys once, in its keygen. Here each ceremony derives fresh PRSS
//!   keys in its first three rounds.
//! - The prototype gives each pair to the least loaded holder in one pass and each term to its
//!   first holder.
//!   - Here `balance` adds a local search, so the loads of the operators differ by at most one in
//!     both tables.
//! - The prototype has only collector mode.
//!   - The first message of `establish` also carries the mode and the batch size, so operators with
//!     different values abort before the first gate.
//! - The prototype sends the digest of a term only to the other holders of the term.
//!   - Here every operator receives the salted digest of every term, so a split copy stops every
//!     honest operator.
//! - The prototype opens an output through a king, a coin with digests, a random linear combination
//!   and a vote, in 5 rounds.
//!   - Here `rerand` takes 1 round before the check, and `open` takes 1 round after it.
//! - The prototype ends each opening with a vote. Here each operator decides alone, as in Goyal and
//!   Song.
//! - The caller checks the tuples before it opens outputs, and it stops at the first error.
//!   - The prototype enforces both with the provenance of the shares and a failed state.
//! - `reshare` and `open` pad a short message with zeros and truncate a long message.
//!   - This gives an additive error or different hashes, where the prototype aborts.

use std::array::from_fn;
use std::fmt::Debug;
use std::ops::{BitAnd, BitXor, BitXorAssign, Range};
use std::slice::{Chunks, ChunksMut};
use std::sync::Arc;
use std::{iter, mem};

use aes::cipher::{Array, BlockCipherEncrypt, KeyInit};
use aes::{Aes128, Block};
use clap::ValueEnum;
use primitives::field::F192;
use primitives::hash::{self, Hasher};
use primitives::{cast_slice, load_at};

use crate::net::{Channel, Network};

pub type Key = [u8; 32];
pub const LANES: usize = 4;

pub trait Lane: Copy + BitXor<Output = Self> {
    fn rotate_left(self, n: u32) -> Self;
    fn splat(word: u64) -> Self;
}

/// The same 64-bit lane of `LANES` instances.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Word(pub [u64; LANES]);

impl Word {
    pub const ZERO: Word = Word([0; LANES]);

    pub fn load(words: &[u64]) -> Word {
        Word(words[..LANES].try_into().unwrap())
    }
}

impl BitXor for Word {
    type Output = Word;

    fn bitxor(self, other: Word) -> Word {
        Word(from_fn(|s| self.0[s] ^ other.0[s]))
    }
}

impl BitAnd for Word {
    type Output = Word;

    fn bitand(self, other: Word) -> Word {
        Word(from_fn(|s| self.0[s] & other.0[s]))
    }
}

impl BitXorAssign for Word {
    fn bitxor_assign(&mut self, other: Word) {
        *self = *self ^ other;
    }
}

impl Lane for Word {
    fn rotate_left(self, n: u32) -> Word {
        Word(self.0.map(|word| word.rotate_left(n)))
    }

    fn splat(word: u64) -> Word {
        Word([word; LANES])
    }
}

pub struct Group {
    pub n: usize,
    pub t: usize,
    /// The operators of each term, as a bit set.
    pub terms: Vec<u32>,
    /// The pairs of terms whose products each operator adds. `balance` gives each pair to one
    /// holder of both terms.
    pub product_pairs: Vec<Vec<(usize, usize)>>,
    /// The holder that adds the pseudorandom value of each term into its gate contributions, and
    /// that sends its copy in `open`. `balance` gives each term to one of its holders.
    pub owner: Vec<usize>,
    /// The collected term and the collector of each gate, in rotation.
    pub collectors: Vec<(usize, usize)>,
    /// The term `T_i` that each operator `i` fills in peer mode. It contains the operators `i + 1`
    /// to `i + t - 1` modulo `n`.
    pub peer_terms: Vec<usize>,
    /// `phi[i][k]` weights held term `k` of operator `i` in its Shamir share. It is the value at
    /// `alpha(i)` of the polynomial of degree `t - 1` that is one at zero and zero at the
    /// operators of the term.
    pub phi: Vec<Vec<F192>>,
    /// `lambda[i]` weights the share of operator `i`. The weighted shares of a polynomial of
    /// degree at most `2t - 2` add up to its value at zero.
    pub lambda: Vec<F192>,
    /// The rows that give the shares of operators `t` to `n - 1`, and last the secret, from the
    /// shares of operators 0 to `t - 1`.
    interpolation: Vec<Vec<F192>>,
}

fn alpha(i: usize) -> F192 {
    F192::new(i as u64 + 1, 0, 0)
}

fn lagrange(node: F192, others: impl Iterator<Item = F192>, at: F192) -> F192 {
    others.fold(F192::ONE, |product, other| {
        product * (at + other) * (node + other).inv()
    })
}

/// Gives each item to one of its eligible operators, and returns the operator of each item.
fn balance(n: usize, eligible: &[Vec<usize>]) -> Vec<usize> {
    let least_loaded = |load: &[usize], operators: &[usize]| {
        *operators.iter().min_by_key(|&&i| (load[i], i)).unwrap()
    };
    let mut load = vec![0; n];
    // The first pass gives each item to its least loaded eligible operator, and the lowest index on
    // a tie.
    let mut owner: Vec<usize> = eligible
        .iter()
        .map(|operators| {
            let i = least_loaded(&load, operators);
            load[i] += 1;
            i
        })
        .collect();
    // Then each scan moves an item to its least loaded eligible operator if this lowers the larger
    // of the two loads. A move lowers the sum of the squared loads, so the scans end.
    let mut moved = true;
    while moved {
        moved = false;
        for (item, operators) in eligible.iter().enumerate() {
            let (i, j) = (owner[item], least_loaded(&load, operators));
            if load[j] + 1 < load[i] {
                load[i] -= 1;
                load[j] += 1;
                owner[item] = j;
                moved = true;
            }
        }
    }
    owner
}

impl Group {
    pub fn new(t: usize) -> Group {
        assert!((1..=16).contains(&t), "the threshold t must be in 1..=16");
        let n = 2 * t - 1;
        let terms: Vec<u32> = (0..1u32 << n)
            .filter(|set| set.count_ones() as usize + 1 == t)
            .collect();
        let holds = |i: usize, k: usize| terms[k] >> i & 1 == 0;
        let holders = |k: usize| (0..n).filter(move |&i| holds(i, k));
        let pairs: Vec<(usize, usize)> = (0..terms.len())
            .flat_map(|a| (0..terms.len()).map(move |b| (a, b)))
            .collect();
        // Two terms contain at most `2t - 2` of the `2t - 1` operators, so some operator holds
        // both.
        let pair_holders: Vec<Vec<usize>> = pairs
            .iter()
            .map(|&(a, b)| holders(a).filter(|&i| holds(i, b)).collect())
            .collect();
        let multipliers = balance(n, &pair_holders);
        let product_pairs = (0..n)
            .map(|i| {
                let assigned = pairs.iter().zip(&multipliers).filter(|&(_, &j)| j == i);
                assigned.map(|(&pair, _)| pair).collect()
            })
            .collect();
        let term_holders: Vec<Vec<usize>> =
            (0..terms.len()).map(|k| holders(k).collect()).collect();
        let owner = balance(n, &term_holders);
        let collectors = (0..t)
            .flat_map(|round| {
                (0..terms.len()).map(move |k| (k, holders(k).nth((round + k) % t).unwrap()))
            })
            .collect();
        let peer_terms = (0..n)
            .map(|i| {
                let term = (1..t).fold(0, |term, d| term | 1 << ((i + d) % n));
                terms.iter().position(|&k| k == term).unwrap()
            })
            .collect();
        let others = |count: usize, node: usize| (0..count).filter(move |&j| j != node).map(alpha);
        let phi = (0..n)
            .map(|i| {
                let members = |k: usize| (0..n).filter(move |&j| !holds(j, k)).map(alpha);
                let held = (0..terms.len()).filter(|&k| holds(i, k));
                held.map(|k| lagrange(F192::ZERO, members(k), alpha(i)))
                    .collect()
            })
            .collect();
        let lambda = (0..n)
            .map(|i| lagrange(alpha(i), others(n, i), F192::ZERO))
            .collect();
        let basis = |at: F192| -> Vec<F192> {
            (0..t)
                .map(|k| lagrange(alpha(k), others(t, k), at))
                .collect()
        };
        Group {
            n,
            t,
            terms,
            product_pairs,
            owner,
            collectors,
            peer_terms,
            phi,
            lambda,
            interpolation: (t..n).map(alpha).chain([F192::ZERO]).map(basis).collect(),
        }
    }

    pub fn holds(&self, i: usize, k: usize) -> bool {
        self.terms[k] >> i & 1 == 0
    }

    pub fn held(&self, i: usize) -> Vec<usize> {
        (0..self.terms.len())
            .filter(|&k| self.holds(i, k))
            .collect()
    }

    /// The secret of the shares, if all shares lie on the polynomial of the first `t` shares.
    fn reconstruct(&self, shares: &[F192]) -> Option<F192> {
        let at = |basis: &[F192]| {
            basis
                .iter()
                .zip(shares)
                .fold(F192::ZERO, |sum, (&b, &s)| sum + b * s)
        };
        let (secret, others) = self.interpolation.split_last().unwrap();
        let consistent = others
            .iter()
            .zip(&shares[self.t..])
            .all(|(basis, &share)| at(basis) == share);
        consistent.then(|| at(secret))
    }
}

/// A replicated sharing `[[v]]` of `W` lanes in each word of `LANES` instances.
pub struct Replicated<const W: usize> {
    /// The parts of all words. The block of a word holds the public part first and then one part
    /// for each held term, in the order of `held`.
    pub parts: Vec<[Word; W]>,
    held: usize,
}

impl<const W: usize> Replicated<W> {
    /// The sharing of zero in `words` words.
    pub fn new(party: &Party, words: usize) -> Replicated<W> {
        let held = party.held.len();
        let parts = vec![[Word::ZERO; W]; words * (held + 1)];
        Replicated { parts, held }
    }

    /// The block of each word.
    pub fn blocks(&self) -> Chunks<'_, [Word; W]> {
        self.parts.chunks(self.held + 1)
    }

    pub fn blocks_mut(&mut self) -> ChunksMut<'_, [Word; W]> {
        self.parts.chunks_mut(self.held + 1)
    }
}

/// The held terms of a replicated sharing with no public part, in the order of `held`. Each held
/// term has one column of `length` words for each gate, and a term that no column needs is empty.
#[derive(Default)]
pub struct Terms {
    words: Vec<Vec<u64>>,
    length: usize,
}

impl Terms {
    /// Column `c` of held term `k`.
    pub fn column(&self, k: usize, c: usize) -> &[u64] {
        &self.words[k][c * self.length..][..self.length]
    }

    fn column_mut(&mut self, k: usize, c: usize) -> &mut [u64] {
        &mut self.words[k][c * self.length..][..self.length]
    }

    /// The element `v` of `F192` in each held term.
    pub fn value(&self, v: usize) -> impl Iterator<Item = F192> + '_ {
        self.words.iter().map(move |term| load_at(term, 3 * v))
    }
}

/// The additive share `{v}` of this operator, in one column of `length` words for each gate.
pub struct Additive {
    words: Vec<u64>,
    length: usize,
}

impl Additive {
    /// Zero shares in `gates` columns of `length` words.
    pub fn new(gates: usize, length: usize) -> Additive {
        let words = vec![0; gates * length];
        Additive { words, length }
    }

    fn column(&self, c: usize) -> &[u64] {
        &self.words[c * self.length..][..self.length]
    }

    /// Column `c`, the shares of gate `c`.
    pub fn column_mut(&mut self, c: usize) -> &mut [u64] {
        &mut self.words[c * self.length..][..self.length]
    }

    /// The additive shares of elements of `F192`, in one column.
    pub fn values(values: impl ExactSizeIterator<Item = F192>) -> Additive {
        let length = 3 * values.len();
        let words = values.flat_map(|value| load_at::<F192, [u64; 3]>(&[value], 0));
        Additive {
            words: words.collect(),
            length,
        }
    }
}

/// A Shamir share `<v>` of this operator.
pub type Shamir = F192;

/// The AND tuples of a batch with one copy for each held term, and the running hash `h_T` of each
/// held term.
pub struct Tuples {
    pub x: Vec<Vec<u64>>,
    pub y: Vec<Vec<u64>>,
    pub z: Vec<Vec<u64>>,
    pub hashes: Vec<Hasher>,
}

impl Tuples {
    /// Empty tuples with room for `words` tuple words in each copy.
    pub fn new(party: &Party, words: usize) -> Tuples {
        let copies = || -> Vec<Vec<u64>> {
            (0..party.held.len())
                .map(|_| Vec::with_capacity(words))
                .collect()
        };
        Tuples {
            x: copies(),
            y: copies(),
            z: copies(),
            hashes: vec![Hasher::new().update(b"thlxmss-history").clone(); party.held.len()],
        }
    }
}

/// `mul` of replicated sharings, the additive share of this operator. It XORs `x_A & y_B` over the
/// pairs `(A, B)` of `pairs`.
pub fn mul(pairs: &[(usize, usize)], x: impl Fn(usize) -> Word, y: impl Fn(usize) -> Word) -> Word {
    pairs
        .iter()
        .fold(Word::ZERO, |sum, &(a, b)| sum ^ (x(a) & y(b)))
}

/// The commitment `H(tag || u8(i) || u8(j) || reveal)` of operator `i` to its reveal to operator
/// `j`. It names the sender and the receiver, so an operator cannot copy the commitment of another,
/// as in [CF01](https://eprint.iacr.org/2001/055).
pub fn commitment(tag: &[u8], i: usize, j: usize, reveal: &[u8]) -> Key {
    tagged_hash(tag, &[&[i as u8, j as u8], reveal])
}

/// Commits to `outgoing[j]` for each operator `j` in one round and reveals in the next round.
pub async fn commit_reveal(
    channel: &mut Channel,
    id: usize,
    tag: &[u8],
    outgoing: Vec<Vec<u8>>,
) -> Result<Vec<Vec<u8>>, String> {
    let commitments: Vec<Vec<u8>> = (0..outgoing.len())
        .map(|j| match j == id {
            true => vec![],
            false => commitment(tag, id, j, &outgoing[j]).to_vec(),
        })
        .collect();
    let commitments = channel.exchange_bytes(commitments).await?;
    reveal(channel, id, tag, &commitments, outgoing).await
}

/// Reveals `outgoing[j]` to each operator `j` in one round. It accepts the reveal `r` of `j` only
/// if `r` has the length of `outgoing[j]` and `commitment(tag, j, id, r)` is the commitment of `j`.
async fn reveal(
    channel: &mut Channel,
    id: usize,
    tag: &[u8],
    commitments: &[Vec<u8>],
    outgoing: Vec<Vec<u8>>,
) -> Result<Vec<Vec<u8>>, String> {
    let revealed = channel.exchange_bytes(outgoing.clone()).await?;
    let honest = |j: usize| {
        revealed[j].len() == outgoing[j].len()
            && commitment(tag, j, id, &revealed[j])[..] == commitments[j]
    };
    match (0..outgoing.len()).find(|&j| j != id && !honest(j)) {
        Some(j) => Err(format!(
            "operator {j} reveals a value that differs from its commitment"
        )),
        None => Ok(revealed),
    }
}

/// The fresh parts that one operator deals in a setup, one for each term and one for each other
/// operator.
pub struct Parts {
    terms: Vec<Key>,
    pairs: Vec<Key>,
}

impl Parts {
    pub fn random(group: &Group) -> Parts {
        Parts {
            terms: (0..group.terms.len()).map(|_| rand::random()).collect(),
            pairs: (0..group.n).map(|_| rand::random()).collect(),
        }
    }

    /// The reveal of operator `i` to operator `j`, the parts of the terms that both hold in term
    /// order and then the pair part for `j`.
    pub fn reveal(&self, group: &Group, i: usize, j: usize) -> Vec<u8> {
        let shared = shared(group, i, j).into_iter().map(|k| &self.terms[k][..]);
        shared
            .chain([&self.pairs[j][..]])
            .collect::<Vec<_>>()
            .concat()
    }

    /// The term keys and the pair keys of operator `id` from its own parts and the reveal of each
    /// other operator.
    ///
    /// - The key of a held term hashes `term_tag` and the parts of all its holders in operator
    ///   order.
    /// - The pair key with `j` hashes `pair_tag`, the part of the lower operator and then the part
    ///   of the higher operator. It is zero at `j = id`.
    pub fn keys(
        &self,
        group: &Group,
        id: usize,
        revealed: &[&[u8]],
        [term_tag, pair_tag]: [&[u8]; 2],
    ) -> (Vec<Key>, Vec<Key>) {
        let term_part = |j: usize, k: usize| -> &[u8] {
            match j == id {
                true => &self.terms[k],
                false => {
                    let position = shared(group, id, j).iter().position(|&s| s == k).unwrap();
                    &revealed[j][32 * position..][..32]
                }
            }
        };
        let terms = group
            .held(id)
            .into_iter()
            .map(|k| {
                let holders = (0..group.n).filter(|&j| group.holds(j, k));
                tagged_hash(
                    term_tag,
                    &holders.map(|j| term_part(j, k)).collect::<Vec<_>>(),
                )
            })
            .collect();
        let pairs = (0..group.n)
            .map(|j| match j == id {
                true => [0; 32],
                false => {
                    let theirs = &revealed[j][revealed[j].len() - 32..];
                    let (low, high) = match id < j {
                        true => (&self.pairs[j][..], theirs),
                        false => (theirs, &self.pairs[j][..]),
                    };
                    tagged_hash(pair_tag, &[low, high])
                }
            })
            .collect();
        (terms, pairs)
    }
}

/// The terms that operators `i` and `j` both hold, in term order.
fn shared(group: &Group, i: usize, j: usize) -> Vec<usize> {
    let held = group.held(i).into_iter();
    held.filter(|&k| group.holds(j, k)).collect()
}

/// The echo of operator `id` to operator `j`, the hash of `tag` and the keys of the terms that both
/// hold. `keys` holds the keys of the held terms of `id`, in the order of `held`.
pub fn shared_keys_hash(group: &Group, tag: &[u8], id: usize, j: usize, keys: &[Key]) -> Key {
    let held = group.held(id).into_iter().zip(keys);
    let shared: Vec<&[u8]> = held
        .filter(|&(k, _)| group.holds(j, k))
        .map(|(_, key)| &key[..])
        .collect();
    tagged_hash(tag, &shared)
}

/// The tag of the commitments of the PRSS setup.
pub const PRSS_COMMIT: &[u8] = b"thlxmss-prss-commit";

/// `establish` in three rounds, with the PRSS setup of the ceremony. It returns the session value,
/// the PRSS keys of the held terms and the PRSS pair keys.
///
/// 1. Each operator sends `[nonce || mode || batch_size]` and its PRSS commitment to `j` to each
///    operator `j`. The session value hashes the first part of the messages of all operators, in
///    operator order.
/// 2. Each operator reveals its fresh PRSS parts.
/// 3. Each operator echoes the hash of the PRSS term keys that it shares with the receiver.
///
/// An operator aborts unless every mode and batch size equals its own, every reveal matches its
/// commitment and every echo equals its own.
async fn establish(
    network: &Arc<Network>,
    group: &Group,
    nonce: [u8; 16],
    mode: Reshare,
    batch_size: usize,
) -> Result<(Key, Vec<Key>, Vec<Key>), String> {
    let (id, n) = (network.id, network.n);
    let [low, high]: [u64; 2] = load_at(&nonce, 0);
    let parameters = [low, high, mode as u64, batch_size as u64];
    let parts = Parts::random(group);
    let reveals: Vec<Vec<u8>> = (0..n)
        .map(|j| match j == id {
            true => vec![],
            false => parts.reveal(group, id, j),
        })
        .collect();
    let message = |j: usize| -> Vec<u64> {
        let committed: [u64; 4] = load_at(&commitment(PRSS_COMMIT, id, j, &reveals[j]), 0);
        [parameters, committed].concat()
    };
    let mut channel = network.channel();
    let outgoing = (0..n).map(|j| match j == id {
        true => vec![],
        false => message(j),
    });
    let mut received = channel.exchange(outgoing.collect()).await?;
    // No commitment goes to the operator itself, so zeros fill its place.
    received[id] = [parameters, [0; 4]].concat();
    let parse = |words: &[u64]| -> Option<(Reshare, usize)> {
        let [_, _, mode, size, ..]: [u64; 8] = words.try_into().ok()?;
        let variants = Reshare::value_variants().iter();
        let mode = variants.copied().find(|&variant| variant as u64 == mode)?;
        Some((mode, size as usize))
    };
    let (modes, batch_sizes): (Vec<Reshare>, Vec<usize>) = (0..n)
        .map(|j| {
            parse(&received[j]).ok_or_else(|| format!("operator {j} sends malformed parameters"))
        })
        .collect::<Result<_, _>>()?;
    same("reshare modes", &modes)?;
    same("batch sizes", &batch_sizes)?;
    let session_words: Vec<u64> = received
        .iter()
        .flat_map(|words| words[..4].to_vec())
        .collect();
    let commitments: Vec<Vec<u8>> = received
        .iter()
        .map(|words| cast_slice(&words[4..]).to_vec())
        .collect();
    let revealed = reveal(&mut channel, id, PRSS_COMMIT, &commitments, reveals).await?;
    let revealed: Vec<&[u8]> = revealed.iter().map(Vec::as_slice).collect();
    let tags: [&[u8]; 2] = [b"thlxmss-prss-term", b"thlxmss-prss-pair"];
    let (terms, pairs) = parts.keys(group, id, &revealed, tags);
    let echo = |j: usize| shared_keys_hash(group, b"thlxmss-prss-echo", id, j, &terms).to_vec();
    let echoes = channel.exchange_bytes((0..n).map(echo).collect()).await?;
    match (0..n).find(|&j| j != id && echoes[j] != echo(j)) {
        Some(j) => Err(format!("operator {j} holds other PRSS keys")),
        None => {
            let session = tagged_hash(b"thlxmss-session", &[cast_slice(&session_words)]);
            Ok((session, terms, pairs))
        }
    }
}

/// Fails unless all operators use the same value of the parameter `name`.
fn same<T: Debug + PartialEq>(name: &str, values: &[T]) -> Result<(), String> {
    match values.iter().all(|value| *value == values[0]) {
        true => Ok(()),
        false => Err(format!("the operators use the {name} {values:?}")),
    }
}

/// The resharing of the AND gates.
#[derive(Clone, Copy, Debug, PartialEq, ValueEnum)]
pub enum Reshare {
    Collector,
    Peer,
}

#[cfg(test)]
pub type Tamper = fn(&Channel, Vec<Vec<u64>>) -> Vec<Vec<u64>>;

pub struct Party {
    pub group: Group,
    pub id: usize,
    pub held: Vec<usize>,
    /// The PRF seeds `seed_T` of the held terms, which only `prawns::prf_inputs` uses.
    pub seeds: Vec<Key>,
    pub network: Arc<Network>,
    /// The reshare mode of the AND gates.
    pub mode: Reshare,
    /// The batch size that all operators of the ceremony use.
    pub batch_size: usize,
    /// A test changes the messages of a reshare with this function, as a corrupt operator can. The
    /// function gets the channel and the messages, and in peer mode index `id` holds the copy that
    /// the operator keeps.
    #[cfg(test)]
    pub tamper: Tamper,
    /// A test makes a corrupt operator accept all digests with this flag.
    #[cfg(test)]
    pub ignores_digests: bool,
    /// The session value of `establish`, which keys all streams of the session.
    session: Key,
    /// The PRSS keys `prss_T` of the held terms, which key the streams of `rand`.
    prss_terms: Vec<Key>,
    /// The PRSS key `prss_ij` with each operator `j`, which keys the streams of the pairwise zero
    /// sharing.
    prss_pairs: Vec<Key>,
}

impl Party {
    pub async fn new(
        group: Group,
        seeds: Vec<Key>,
        network: Arc<Network>,
        nonce: [u8; 16],
        mode: Reshare,
        batch_size: usize,
    ) -> Result<Party, String> {
        let (session, prss_terms, prss_pairs) =
            establish(&network, &group, nonce, mode, batch_size).await?;
        Ok(Party {
            held: group.held(network.id),
            group,
            id: network.id,
            seeds,
            network,
            mode,
            batch_size,
            #[cfg(test)]
            tamper: |_, outgoing| outgoing,
            #[cfg(test)]
            ignores_digests: false,
            session,
            prss_terms,
            prss_pairs,
        })
    }

    pub fn local(&self, term: usize) -> Option<usize> {
        self.held.iter().position(|&k| k == term)
    }

    pub fn product_pairs(&self) -> Vec<(usize, usize)> {
        let local = |term| self.local(term).unwrap();
        self.group.product_pairs[self.id]
            .iter()
            .map(|&(a, b)| (local(a), local(b)))
            .collect()
    }

    fn stream(&self, key: &Key, channel: &Channel, index: u64, length: usize) -> Vec<u64> {
        assert!(channel.rounds < 1 << 24);
        let mut words = vec![0; length];
        // The stream number holds the channel number, the round and an 8-bit index. The session
        // value keys every stream, so the number leaves out the session part of the tag.
        let stream = (channel.tag as u32 as u64) << 32 | channel.rounds << 8 | index;
        prg(key, &self.session, stream, &mut words);
        words
    }

    /// `rand(index)` in this round, the term `r_T` of each held term in `length` words.
    pub fn rand(&self, channel: &Channel, index: u64, length: usize) -> Terms {
        let keys = self.prss_terms.iter();
        let words = keys.map(|key| self.stream(key, channel, index, length));
        Terms {
            words: words.collect(),
            length,
        }
    }

    /// Adds the share `zeta_i` of a pairwise zero sharing to `words`. Each pair of operators adds
    /// the stream of its PRSS pair key, so the shares of all operators add up to zero.
    fn zero_sharing(&self, channel: &Channel, words: &mut [u64]) {
        let others = (0..self.group.n).filter(|&j| j != self.id);
        let length = words.len();
        let stream = |j: usize| self.stream(&self.prss_pairs[j], channel, 0, length);
        others.for_each(|j| xor_into(words, &stream(j)));
    }

    /// `conv`, the Shamir share of a value from the held terms of its replicated sharing.
    pub fn conv(&self, terms: impl IntoIterator<Item = F192>) -> Shamir {
        let phi = &self.group.phi[self.id];
        let terms = terms.into_iter().zip(phi);
        terms.fold(F192::ZERO, |share, (term, &phi)| share + phi * term)
    }

    /// `mul` of Shamir shares, `lambda_i` times each local product `x_i y_i`. On vectors a local
    /// product is the inner product.
    pub fn mul_shamir(&self, products: &[F192]) -> Additive {
        let lambda = self.group.lambda[self.id];
        Additive::values(products.iter().map(|&product| lambda * product))
    }

    pub fn expand(&self, key: &Key, index: u64, count: usize) -> Vec<F192> {
        let mut words = vec![0; 3 * count];
        prg(key, &self.session, index, &mut words);
        cast_slice(&words).to_vec()
    }

    /// The masks `rand(0)` of a reshare of `additive` that fills the held terms of `filled` at each
    /// gate. A held term that the reshare fills at every gate, as each held term of `C` in peer
    /// mode, draws no stream.
    pub fn reshare_masks(
        &self,
        channel: &Channel,
        filled: &[Vec<usize>],
        additive: &Additive,
    ) -> Terms {
        let drawn = |k: usize| !filled.iter().all(|terms| terms.contains(&k));
        let keys = self.prss_terms.iter().enumerate();
        let words = keys.map(|(k, key)| match drawn(k) {
            true => self.stream(key, channel, 0, additive.words.len()),
            false => vec![],
        });
        Terms {
            words: words.collect(),
            length: additive.length,
        }
    }

    /// `reshare` of the additive columns of `gates` in `mode`, with the masks of `reshare_masks`.
    ///
    /// It returns the new held terms and the masks with the filled columns in place. Each holder of
    /// a filled term hashes its new columns.
    pub async fn reshare(
        &self,
        channel: &mut Channel,
        mode: Reshare,
        gates: Range<usize>,
        mut additive: Additive,
        masks: Terms,
        hashes: &mut [Hasher],
    ) -> Result<Terms, String> {
        let (group, collectors, mut terms) = (&self.group, &self.group.collectors, masks);
        let filled = self.exchanged(mode, gates.clone());
        self.zero_sharing(channel, &mut additive.words);
        for (c, filled) in filled.iter().enumerate() {
            let owned = |&k: &usize| !filled.contains(&k) && group.owner[self.held[k]] == self.id;
            for k in (0..self.held.len()).filter(owned) {
                xor_into(additive.column_mut(c), terms.column(k, c));
            }
        }
        match mode {
            Reshare::Collector => {
                let stars: Vec<(usize, usize)> = gates
                    .map(|gate| collectors[gate % collectors.len()])
                    .collect();
                self.collect(channel, &stars, additive, &mut terms).await?
            }
            Reshare::Peer => {
                self.send_to_co_holders(channel, additive.words, &mut terms)
                    .await?
            }
        }
        for (c, filled) in filled.iter().enumerate() {
            for &k in filled {
                hashes[k].update(cast_slice(terms.column(k, c)));
            }
        }
        Ok(terms)
    }

    /// The held terms, by local index, that a reshare in `mode` fills at each gate. These are `T*`
    /// in collector mode and the held terms of `C` in peer mode.
    pub fn exchanged(&self, mode: Reshare, gates: Range<usize>) -> Vec<Vec<usize>> {
        let local = |terms: &[usize]| terms.iter().filter_map(|&term| self.local(term)).collect();
        let collectors = &self.group.collectors;
        match mode {
            Reshare::Collector => gates
                .map(|gate| local(&[collectors[gate % collectors.len()].0]))
                .collect(),
            Reshare::Peer => vec![local(&self.group.peer_terms); gates.len()],
        }
    }

    /// Round 1 sends the contribution `u_i` of each gate to the other holders of `T_i`. Each held
    /// term of `C` takes the own or the received contribution.
    async fn send_to_co_holders(
        &self,
        channel: &mut Channel,
        message: Vec<u64>,
        terms: &mut Terms,
    ) -> Result<(), String> {
        let (group, id, n) = (&self.group, self.id, self.group.n);
        let length = message.len();
        let mut outgoing: Vec<Vec<u64>> = (0..n)
            .map(|j| match j != id && group.holds(j, group.peer_terms[id]) {
                true => message.clone(),
                false => vec![],
            })
            .collect();
        outgoing[id] = message;
        #[cfg(test)]
        let mut outgoing = (self.tamper)(channel, outgoing);
        let kept = mem::take(&mut outgoing[id]);
        let mut received = channel.exchange(outgoing).await?;
        received[id] = kept;
        for (j, mut words) in received.into_iter().enumerate() {
            if let Some(k) = self.local(group.peer_terms[j]) {
                words.resize(length, 0);
                terms.words[k] = words;
            }
        }
        Ok(())
    }

    /// Round 1 sends each contribution to the collector of its gate. Round 2 forwards each
    /// collected term to its other holders, which write it into the term of the gate.
    async fn collect(
        &self,
        channel: &mut Channel,
        stars: &[(usize, usize)],
        mut additive: Additive,
        terms: &mut Terms,
    ) -> Result<(), String> {
        let (group, id, n, length) = (&self.group, self.id, self.group.n, additive.length);
        let collected_by = |collector: usize| -> Vec<usize> {
            (0..stars.len())
                .filter(|&c| stars[c].1 == collector)
                .collect()
        };
        let held_by = |j: usize, gates: &[usize]| -> Vec<usize> {
            let gates = gates.iter().copied();
            gates.filter(|&c| group.holds(j, stars[c].0)).collect()
        };
        let message = |additive: &Additive, gates: Vec<usize>| -> Vec<u64> {
            let columns = gates.iter().flat_map(|&c| additive.column(c));
            columns.copied().collect()
        };
        let own = collected_by(id);
        let outgoing: Vec<Vec<u64>> = (0..n)
            .map(|j| match j == id {
                true => vec![],
                false => message(&additive, collected_by(j)),
            })
            .collect();
        #[cfg(test)]
        let outgoing = (self.tamper)(channel, outgoing);
        let received = channel.exchange(outgoing).await?;
        for (_, mut sent) in received.into_iter().enumerate().filter(|&(j, _)| j != id) {
            sent.resize(own.len() * length, 0);
            for (position, &c) in own.iter().enumerate() {
                xor_into(additive.column_mut(c), &sent[position * length..]);
            }
        }
        let outgoing: Vec<Vec<u64>> = (0..n)
            .map(|j| match j == id {
                true => vec![],
                false => message(&additive, held_by(j, &own)),
            })
            .collect();
        #[cfg(test)]
        let outgoing = (self.tamper)(channel, outgoing);
        let received = channel.exchange(outgoing).await?;
        let mut place = |c: usize, column: &[u64]| {
            let k = self.local(stars[c].0).unwrap();
            terms.words[k].resize(stars.len() * length, 0);
            terms.column_mut(k, c).copy_from_slice(&column[..length]);
        };
        for (j, mut forwarded) in received.into_iter().enumerate().filter(|&(j, _)| j != id) {
            let gates = held_by(id, &collected_by(j));
            forwarded.resize(gates.len() * length, 0);
            for (position, c) in gates.into_iter().enumerate() {
                place(c, &forwarded[position * length..]);
            }
        }
        for c in own {
            place(c, additive.column(c));
        }
        Ok(())
    }

    /// `Rerand` of the outputs `[[out]]`, one peer `reshare` of their additive form, as in
    /// [BBY23](https://eprint.iacr.org/2020/1577) (Section 4.3).
    ///
    /// - Each operator reshares the sum of the held terms that it owns. The public part moves into
    ///   term 0, so the owner of term 0 also adds it.
    /// - The tuple `([[out]], [[1]], [[out']])` joins `tuples`, so the check verifies the reshare
    ///   as a multiplication by the public constant 1, as in Protocol 19 of Goyal and Song.
    /// - It returns `[[out']]`, which has no public part.
    pub async fn rerand<const W: usize>(
        &self,
        channel: &mut Channel,
        outputs: &Replicated<W>,
        tuples: &mut Tuples,
    ) -> Result<Replicated<W>, String> {
        let length = outputs.blocks().len() * W * LANES;
        let public = words(outputs.blocks().flat_map(|block| block[0]));
        let x: Vec<Vec<u64>> = (1..=self.held.len())
            .map(|part| {
                let mut copy = words(outputs.blocks().flat_map(|block| block[part]));
                if self.held[part - 1] == 0 {
                    xor_into(&mut copy, &public);
                }
                copy
            })
            .collect();
        let mut additive = Additive::new(1, length);
        let owned = x.iter().zip(&self.held);
        let owned = owned.filter(|&(_, &term)| self.group.owner[term] == self.id);
        owned.for_each(|(copy, _)| xor_into(additive.column_mut(0), copy));
        let filled = self.exchanged(Reshare::Peer, 0..1);
        let masks = self.reshare_masks(channel, &filled, &additive);
        let hashes = &mut tuples.hashes;
        let terms = self.reshare(channel, Reshare::Peer, 0..1, additive, masks, hashes);
        let terms = terms.await?;
        let mut reshared = Replicated::new(self, outputs.blocks().len());
        for (k, copy) in x.into_iter().enumerate() {
            let column = terms.column(k, 0);
            for (block, words) in reshared.blocks_mut().zip(column.chunks(W * LANES)) {
                for (l, lane) in block[k + 1].iter_mut().enumerate() {
                    *lane = Word::load(&words[l * LANES..]);
                }
            }
            let one = if self.held[k] == 0 { !0 } else { 0 };
            tuples.x[k].extend_from_slice(&copy);
            tuples.y[k].extend(iter::repeat_n(one, length));
            tuples.z[k].extend_from_slice(column);
        }
        Ok(reshared)
    }

    /// `open` of a replicated sharing in one round, as in [MPClan](https://eprint.iacr.org/2022/675) (App. B).
    ///
    /// 1. For each term `T` and each operator `j` in `T`, `owner(T)` sends `v_T` to `j` and each
    ///    other holder sends `H(v_T)`.
    /// 2. The receiver aborts unless the hash of each copy equals every received hash.
    /// 3. The value is the public part plus all terms.
    pub async fn open<const W: usize>(
        &self,
        channel: &mut Channel,
        shares: &Replicated<W>,
    ) -> Result<Vec<[Word; W]>, String> {
        let (group, id, n) = (&self.group, self.id, self.group.n);
        let length = shares.blocks().len() * W * LANES;
        let copies: Vec<Vec<u64>> = (1..=self.held.len())
            .map(|part| words(shares.blocks().flat_map(|block| block[part])))
            .collect();
        // The message from `i` to `j` has a segment for each term that `i` holds and `j` lacks, in
        // term order. The segment is the copy if `i` owns the term and its hash otherwise.
        let segments = |i: usize, j: usize| -> Vec<(usize, Range<usize>)> {
            let sent = group
                .held(i)
                .into_iter()
                .filter(|&term| !group.holds(j, term));
            let next = |end: &mut usize, term: usize| {
                let start = *end;
                *end += if group.owner[term] == i {
                    length
                } else {
                    HASH_WORDS
                };
                Some((term, start..*end))
            };
            sent.scan(0, next).collect()
        };
        let copy_hash = |copy: &[u64]| digest(b"thlxmss-copy", &[cast_slice(copy)]);
        let hash = |(copy, &term): (&Vec<u64>, &usize)| match group.owner[term] == id {
            true => [0; HASH_WORDS],
            false => copy_hash(copy),
        };
        let hashes: Vec<[u64; HASH_WORDS]> = copies.iter().zip(&self.held).map(hash).collect();
        let encode = |j: usize| -> Vec<u64> {
            let segments = segments(id, j).into_iter();
            let segment = segments.flat_map(|(term, _)| {
                let k = self.local(term).unwrap();
                match group.owner[term] == id {
                    true => &copies[k][..],
                    false => &hashes[k][..],
                }
            });
            segment.copied().collect()
        };
        let outgoing = (0..n).map(|j| match j == id {
            true => vec![],
            false => encode(j),
        });
        let mut received = channel.exchange(outgoing.collect()).await?;
        let incoming: Vec<Vec<(usize, Range<usize>)>> = (0..n).map(|i| segments(i, id)).collect();
        for (words, segments) in received.iter_mut().zip(&incoming) {
            words.resize(segments.last().map_or(0, |(_, range)| range.end), 0);
        }
        let segment = |i: usize, term: usize| {
            let (_, range) = incoming[i].iter().find(|&&(k, _)| k == term).unwrap();
            &received[i][range.clone()]
        };
        let lacked: Vec<usize> = (0..group.terms.len())
            .filter(|&term| !group.holds(id, term))
            .collect();
        let consistent = |term: usize| {
            let copy = copy_hash(segment(group.owner[term], term));
            let mut others = (0..n).filter(|&i| i != group.owner[term] && group.holds(i, term));
            others.all(|i| segment(i, term) == &copy[..])
        };
        if let Some(term) = lacked.iter().copied().find(|&term| !consistent(term)) {
            return Err(format!("the holders of term {term} send different copies"));
        }
        let mut values: Vec<[Word; W]> = shares
            .blocks()
            .map(|block| {
                let add = |sum: [Word; W], part: &[Word; W]| from_fn(|l| sum[l] ^ part[l]);
                block.iter().fold([Word::ZERO; W], add)
            })
            .collect();
        for &term in &lacked {
            let copy = segment(group.owner[term], term);
            for (value, words) in values.iter_mut().zip(copy.chunks(W * LANES)) {
                for (l, lane) in value.iter_mut().enumerate() {
                    *lane ^= Word::load(&words[l * LANES..]);
                }
            }
        }
        Ok(values)
    }

    /// Opens Shamir shares robustly. Each operator sends its shares and `payload` to all, and the
    /// opening also returns the payload of each operator.
    pub async fn open_shamir(
        &self,
        channel: &mut Channel,
        shares: &[Shamir],
        payload: &[u64],
    ) -> Result<(Vec<F192>, Vec<Vec<u64>>), String> {
        let (n, id, length) = (self.group.n, self.id, 3 * shares.len());
        let own: &[u64] = cast_slice(shares);
        let received = channel.exchange(vec![[own, payload].concat(); n]).await?;
        if let Some(j) = (0..n).find(|&j| j != id && received[j].len() < length) {
            return Err(format!("operator {j} sends a short share"));
        }
        let column = |v: usize| -> Vec<F192> {
            let share = |j: usize| {
                if j == id {
                    shares[v]
                } else {
                    load_at(&received[j], 3 * v)
                }
            };
            (0..n).map(share).collect()
        };
        let opened = (0..shares.len())
            .map(|v| self.group.reconstruct(&column(v)))
            .collect::<Option<Vec<F192>>>()
            .ok_or("an opened value has shares off one polynomial")?;
        let payloads = received
            .iter()
            .map(|words| words[length.min(words.len())..].to_vec());
        Ok((opened, payloads.collect()))
    }

    /// `coin(payload)`, the hash of the channel tag, the round and `open_shamir(conv(rand(1)),
    /// payload)`. It also returns the payload of each operator.
    pub async fn coin(
        &self,
        channel: &mut Channel,
        payload: &[u64],
    ) -> Result<(Key, Vec<Vec<u64>>), String> {
        let position = [channel.tag, channel.rounds];
        let share = self.conv(self.rand(channel, 1, 3).value(0));
        let (opened, payloads) = self.open_shamir(channel, &[share], payload).await?;
        let key = tagged_hash(
            b"thlxmss-coin",
            &[cast_slice(&position), cast_slice(&opened)],
        );
        Ok((key, payloads))
    }

    /// The digest `d_T = H(s_T || h_T)` of each held term, with the salt `s_T` of `rand(2)` in this round and the running hash `h_T`. The salt hides `h_T` from the operators that lack `T`, as in [GRW18](https://eprint.iacr.org/2018/216) (Section 5).
    pub fn digests(&self, channel: &Channel, hashes: &[Hasher]) -> Vec<u64> {
        let salts = self.rand(channel, 2, HASH_WORDS);
        let salted = |(salt, running): (&Vec<u64>, &Hasher)| {
            digest(b"thlxmss-digest", &[cast_slice(salt), &running.finalize()])
        };
        salts.words.iter().zip(hashes).flat_map(salted).collect()
    }

    /// Fails unless all holders of each term send the same digest, as in [CGH+18](https://eprint.iacr.org/2018/570) (Prot. 3.3) and MPClan. `own` holds the digests of this operator and `received` the digests of each other operator.
    pub fn compare_digests(&self, own: &[u64], received: &[Vec<u64>]) -> Result<(), String> {
        #[cfg(test)]
        if self.ignores_digests {
            return Ok(());
        }
        let (group, id) = (&self.group, self.id);
        let held: Vec<Vec<usize>> = (0..group.n).map(|j| group.held(j)).collect();
        let digest = |j: usize, term: usize| {
            let words = if j == id { own } else { &received[j][..] };
            let position = held[j].iter().position(|&k| k == term).unwrap();
            words.as_chunks::<HASH_WORDS>().0.get(position)
        };
        let consistent = |term: usize| {
            let mut digests = (0..group.n)
                .filter(|&j| group.holds(j, term))
                .map(|j| digest(j, term));
            let first = digests.next().unwrap();
            first.is_some() && digests.all(|other| other == first)
        };
        match (0..group.terms.len()).find(|&term| !consistent(term)) {
            Some(term) => Err(format!("the holders of term {term} send different digests")),
            None => Ok(()),
        }
    }
}

fn prg(seed: &Key, session: &Key, stream: u64, target: &mut [u64]) {
    let key = tagged_hash(b"rss-prss", &[seed, session]);
    let cipher = Aes128::new(&Array(key[..16].try_into().unwrap()));
    for (counter, words) in target.chunks_mut(16).enumerate() {
        let mut blocks: [Block; 8] = from_fn(|block| {
            Array(((stream as u128) << 64 | (8 * counter + block) as u128).to_le_bytes())
        });
        cipher.encrypt_blocks(&mut blocks);
        for (w, word) in words.iter_mut().enumerate() {
            *word = u64::from_le_bytes(blocks[w / 2][8 * (w % 2)..][..8].try_into().unwrap());
        }
    }
}

/// The words of a hash.
const HASH_WORDS: usize = hash::OUT_LEN / size_of::<u64>();

fn digest(tag: &[u8], parts: &[&[u8]]) -> [u64; HASH_WORDS] {
    load_at(&tagged_hash(tag, parts), 0)
}

/// `H(tag || parts)`. Each use of `H` in the protocol has its own tag, so no two uses share an
/// input.
pub fn tagged_hash(tag: &[u8], parts: &[&[u8]]) -> Key {
    hash::hash(&[&[tag], parts].concat().concat())
}

fn words(values: impl IntoIterator<Item = Word>) -> Vec<u64> {
    values.into_iter().flat_map(|value| value.0).collect()
}

pub fn xor_into(target: &mut [u64], source: &[u64]) {
    target.iter_mut().zip(source).for_each(|(t, s)| *t ^= s);
}

#[cfg(test)]
pub mod tests {
    use std::net::TcpListener;
    use std::thread;

    use tokio::runtime::Runtime;

    use crate::check;
    use crate::circuit::{Keccak, evaluate};
    use crate::dkg::BATCH_SIZE;
    use crate::mpc::*;

    pub fn local_parties<T: Send>(
        t: usize,
        reshare: Reshare,
        run: impl AsyncFn(Party, Vec<Key>) -> T + Sync,
    ) -> Vec<T> {
        let parameters = vec![(reshare, BATCH_SIZE); 2 * t - 1];
        local_operators(t, &parameters, async |party, all_seeds| {
            run(party.unwrap(), all_seeds).await
        })
    }

    /// Random seeds of all terms and the pair keys of each operator, with `pairs[i][j] =
    /// pairs[j][i]` and a zero key at `i = j` as `keygen` gives.
    pub fn random_keys(group: &Group) -> (Vec<Key>, Vec<Vec<Key>>) {
        let all_seeds = (0..group.terms.len()).map(|_| rand::random()).collect();
        let upper: Vec<Vec<Key>> = (0..group.n)
            .map(|_| (0..group.n).map(|_| rand::random()).collect())
            .collect();
        let pairs = (0..group.n)
            .map(|i| {
                (0..group.n)
                    .map(|j| match i == j {
                        true => [0; 32],
                        false => upper[i.min(j)][i.max(j)],
                    })
                    .collect()
            })
            .collect();
        (all_seeds, pairs)
    }

    /// Each operator runs `run` with the outcome of `Party::new` at its reshare mode and batch size
    /// of `parameters`.
    pub fn local_operators<T: Send>(
        t: usize,
        parameters: &[(Reshare, usize)],
        run: impl AsyncFn(Result<Party, String>, Vec<Key>) -> T + Sync,
    ) -> Vec<T> {
        local_networks(t, async |network, all_seeds| {
            let group = Group::new(t);
            let seeds = group
                .held(network.id)
                .iter()
                .map(|&k| all_seeds[k])
                .collect();
            let (reshare, batch_size) = parameters[network.id];
            let party = Party::new(group, seeds, network, rand::random(), reshare, batch_size);
            run(party.await, all_seeds).await
        })
    }

    /// Each operator runs `run` with its network and random seeds of all terms.
    pub fn local_networks<T: Send>(
        t: usize,
        run: impl AsyncFn(Arc<Network>, Vec<Key>) -> T + Sync,
    ) -> Vec<T> {
        let group = Group::new(t);
        let (all_seeds, _) = random_keys(&group);
        let listeners: Vec<TcpListener> = (0..group.n)
            .map(|_| TcpListener::bind("127.0.0.1:0").unwrap())
            .collect();
        let addresses: Vec<String> = listeners
            .iter()
            .map(|l| l.local_addr().unwrap().to_string())
            .collect();
        thread::scope(|s| {
            let handles: Vec<_> = listeners
                .into_iter()
                .enumerate()
                .map(|(id, listener)| {
                    let (addresses, all_seeds, run) = (&addresses, &all_seeds, &run);
                    s.spawn(move || {
                        Runtime::new().unwrap().block_on(async {
                            let network = crate::net::connect(id, listener, addresses.clone());
                            run(network, all_seeds.clone()).await
                        })
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        })
    }

    #[test]
    fn prg_streams_extend_and_depend_on_seed_session_and_stream() {
        let words = |seed: u8, halves: [u8; 2], stream: u64, length: usize| {
            let session: Key = from_fn(|byte| halves[byte / 16]);
            let mut words = vec![0; length];
            prg(&[seed; 32], &session, stream, &mut words);
            words
        };
        let whole = words(1, [2, 3], 4, 40);
        assert_eq!(words(1, [2, 3], 4, 17), whole[..17]);
        for other in [
            words(9, [2, 3], 4, 40),
            words(1, [5, 3], 4, 40),
            words(1, [2, 5], 4, 40),
            words(1, [2, 3], 5, 40),
        ] {
            assert!(other.iter().zip(&whole).all(|(a, b)| a != b));
        }
    }

    #[test]
    fn each_pair_and_each_term_goes_to_a_holder_and_the_loads_differ_by_at_most_one() {
        for t in 1..=6 {
            let group = Group::new(t);
            let terms = group.terms.len();
            let mut assigned = group.product_pairs.concat();
            assigned.sort();
            let all_pairs = (0..terms).flat_map(|a| (0..terms).map(move |b| (a, b)));
            assert_eq!(assigned, all_pairs.collect::<Vec<_>>());
            for (i, pairs) in group.product_pairs.iter().enumerate() {
                let held = |&(a, b): &(usize, usize)| group.holds(i, a) && group.holds(i, b);
                assert!(pairs.iter().all(held));
            }
            assert!((0..terms).all(|k| group.holds(group.owner[k], k)));
            let pair_loads: Vec<usize> = group.product_pairs.iter().map(Vec::len).collect();
            let owner_loads = (0..group.n)
                .map(|i| group.owner.iter().filter(|&&owner| owner == i).count())
                .collect();
            for loads in [pair_loads, owner_loads] {
                let spread = loads.iter().max().unwrap() - loads.iter().min().unwrap();
                assert!(spread <= 1, "the loads {loads:?} at t = {t}");
            }
        }
    }

    #[test]
    fn at_2_of_3_each_operator_multiplies_one_diagonal_pair_and_two_other_pairs() {
        for pairs in Group::new(2).product_pairs {
            let diagonal = pairs.iter().filter(|&&(a, b)| a == b).count();
            assert_eq!((diagonal, pairs.len() - diagonal), (1, 2));
        }
    }

    #[test]
    fn operators_with_different_reshare_modes_or_batch_sizes_abort_before_the_first_and_gate() {
        let (collector, peer) = (Reshare::Collector, Reshare::Peer);
        for (parameters, error) in [
            (
                [(collector, 128), (collector, 128), (peer, 128)],
                "the operators use the reshare modes [Collector, Collector, Peer]",
            ),
            (
                [(peer, 128), (peer, 64), (peer, 128)],
                "the operators use the batch sizes [128, 64, 128]",
            ),
        ] {
            let errors = local_operators(2, &parameters, async |party, _| party.err());
            assert_eq!(errors, vec![Some(error.to_string()); 3]);
        }
    }

    #[test]
    fn an_operator_with_another_session_value_or_a_short_share_aborts_the_others_at_the_first_coin()
    {
        // With another session value, the coin shares of operator 1 come from other streams.
        // So the shares of the first coin after the 24 layers lie off one polynomial.
        // A short share has 2 of the 3 words of an element.
        for (short, error) in [
            (false, "an opened value has shares off one polynomial"),
            (true, "operator 1 sends a short share"),
        ] {
            for t in [2, 3] {
                let outcomes = local_parties(t, Reshare::Peer, async |mut party, _| {
                    let corrupt = party.id == 1;
                    if corrupt && !short {
                        party.session[0] ^= 1;
                    }
                    let mut channel = party.network.channel();
                    let (mut blocks, mut tuples) =
                        (Replicated::new(&party, 1), Tuples::new(&party, 0));
                    let circuit = Keccak { outputs: 25 };
                    let evaluation = evaluate(
                        &party,
                        &circuit,
                        &mut channel,
                        &mut blocks,
                        [true; 25],
                        &mut tuples,
                    );
                    evaluation.await.unwrap();
                    let outcome = match corrupt && short {
                        true => channel
                            .exchange(vec![vec![0; 2]; party.group.n])
                            .await
                            .map(|_| ()),
                        false => check::mult_verification(&party, &mut channel, tuples).await,
                    };
                    (outcome, channel.rounds)
                });
                for (id, outcome) in outcomes
                    .into_iter()
                    .enumerate()
                    .filter(|&(id, _)| !short || id != 1)
                {
                    assert_eq!(
                        outcome,
                        (Err(error.to_string()), 25),
                        "operator {id} at t = {t}"
                    );
                }
            }
        }
    }

    #[test]
    fn the_salted_digests_agree_in_one_session_and_differ_at_an_operator_with_another_session_value()
     {
        for t in [2, 3] {
            // Operator 1 and another holder of its first held term draw different salts for it.
            let other = Err(format!(
                "the holders of term {} send different digests",
                Group::new(t).held(1)[0]
            ));
            for flipped in [false, true] {
                let outcomes = local_parties(t, Reshare::Peer, async |mut party, _| {
                    if flipped && party.id == 1 {
                        party.session[0] ^= 1;
                    }
                    let mut channel = party.network.channel();
                    let own = party.digests(&channel, &vec![Hasher::new(); party.held.len()]);
                    let received = channel.exchange(vec![own.clone(); party.group.n]).await;
                    party.compare_digests(&own, &received.unwrap())
                });
                let expected = if flipped { other.clone() } else { Ok(()) };
                assert_eq!(outcomes, vec![expected; 2 * t - 1], "t = {t}");
            }
        }
    }

    #[test]
    fn an_opening_gives_the_public_part_plus_all_terms_and_a_wrong_copy_or_hash_aborts_its_receivers()
     {
        // The public part is part 0, and term `k` is part `k + 1`.
        let part = |part: usize, word: usize| -> [Word; 2] {
            from_fn(|l| Word(from_fn(|s| (part * 1000 + word * 100 + l * 10 + s) as u64)))
        };
        for t in [2, 3] {
            let group = Group::new(t);
            let (terms, owner) = (group.terms.len(), group.owner[0]);
            let holder = (0..group.n).find(|&i| i != owner && group.holds(i, 0));
            let expected: Vec<[Word; 2]> = (0..3)
                .map(|word| {
                    let add = |sum: [Word; 2], part: [Word; 2]| from_fn(|l| sum[l] ^ part[l]);
                    (0..=terms)
                        .map(|p| part(p, word))
                        .fold([Word::ZERO; 2], add)
                })
                .collect();
            // Operator `flipped` changes its copy of term 0, so the owner sends a wrong copy and
            // another holder a wrong hash.
            for flipped in [None, Some(owner), holder] {
                let outcomes = local_parties(t, Reshare::Peer, async |party, _| {
                    let mut shares = Replicated::<2>::new(&party, 3);
                    for (word, block) in shares.blocks_mut().enumerate() {
                        block[0] = part(0, word);
                        for (k, &term) in party.held.iter().enumerate() {
                            block[k + 1] = part(term + 1, word);
                        }
                    }
                    if flipped == Some(party.id) {
                        shares.parts[1 + party.local(0).unwrap()][1].0[2] ^= 1;
                    }
                    let mut channel = party.network.channel();
                    party.open(&mut channel, &shares).await
                });
                for (id, outcome) in outcomes.into_iter().enumerate() {
                    let expected = match (flipped, group.holds(id, 0)) {
                        (Some(j), _) if j == id => continue,
                        (Some(_), false) => {
                            Err("the holders of term 0 send different copies".into())
                        }
                        _ => Ok(expected.clone()),
                    };
                    assert_eq!(
                        outcome, expected,
                        "operator {id} at t = {t}, flipped {flipped:?}"
                    );
                }
            }
        }
    }
}
