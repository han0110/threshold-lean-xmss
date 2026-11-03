//! This module evaluates circuits on replicated sharings and gives Keccak-f as a circuit of 24 layers, with chi as the AND gates. It also hashes one chain step of each instance in MPC.
//!
//! - `plans` finds the AND gates with two secret inputs. Only these gates send messages, and an AND gate with a public input is local.

use crate::mpc::{Additive, LANES, Lane, Party, Replicated, Terms, Tuples, Word, mul, xor_into};
use crate::net::Channel;
use primitives::hash;
use std::array::from_fn;
use std::iter;
use std::ops::BitXor;

/// The public lanes of a chain step, `P` and the chain address, and then the chain number.
pub type HashPublic = ([u64; 4], [u64; 2]);

/// A lane that records only whether its value can depend on a secret input. `plans` runs the circuit on these lanes to find the AND gates that need messages.
#[derive(Clone, Copy)]
struct Secret(bool);

impl BitXor for Secret {
    type Output = Secret;

    fn bitxor(self, other: Secret) -> Secret {
        Secret(self.0 || other.0)
    }
}

impl Lane for Secret {
    fn rotate_left(self, _: u32) -> Secret {
        self
    }

    fn splat(_: u64) -> Secret {
        Secret(false)
    }
}

/// A layer applies `linear` and then `combine`. The AND gates of `ands` take their inputs after `linear`, and gate `a` adds its product into lane `a` after `combine`. `constant` acts on the public part only.
pub trait Circuit<const W: usize>: Sync {
    const LAYERS: usize;
    fn linear<T: Lane>(&self, layer: usize, state: &mut [T; W]);
    fn ands(&self, layer: usize) -> Vec<(usize, usize)>;
    fn combine<T: Lane>(&self, layer: usize, state: &mut [T; W]);
    fn constant<T: Lane>(&self, layer: usize, public: &mut [T; W]);
}

/// The AND gates of one layer. `shared` lists the gates with two secret inputs, which need messages, and `secret` marks the secret lanes after `linear`.
struct Plan<const W: usize> {
    ands: Vec<(usize, usize)>,
    shared: Vec<usize>,
    secret: [bool; W],
}

fn plans<const W: usize, C: Circuit<W>>(circuit: &C, secret: [bool; W]) -> Vec<Plan<W>> {
    let mut secret = secret.map(Secret);
    (0..C::LAYERS)
        .map(|layer| {
            circuit.linear(layer, &mut secret);
            let after_linear = secret.map(|lane| lane.0);
            let ands = circuit.ands(layer);
            let shared = (0..ands.len())
                .filter(|&a| after_linear[ands[a].0] && after_linear[ands[a].1])
                .collect();
            let product_secret: Vec<Secret> =
                ands.iter().map(|&(x, y)| secret[x] ^ secret[y]).collect();
            circuit.combine(layer, &mut secret);
            for (a, product) in product_secret.into_iter().enumerate() {
                secret[a] = secret[a] ^ product;
            }
            Plan {
                ands,
                shared,
                secret: after_linear,
            }
        })
        .collect()
}

/// Evaluates a circuit on all instances of the batch and records the AND tuples. Each layer takes `mul` at its gates and then `reshare`, in one pass over the blocks. The pass first adds the filled columns of the layer before, and then it adds the masks `r_T` of its own gates.
pub async fn evaluate<const W: usize, C: Circuit<W>>(
    party: &Party,
    circuit: &C,
    channel: &mut Channel,
    blocks: &mut Replicated<W>,
    secret: [bool; W],
    tuples: &mut Tuples,
) -> Result<u64, String> {
    let (words, pairs, term_zero) = (blocks.blocks().len(), party.product_pairs(), party.local(0));
    let plans = plans(circuit, secret);
    let shared: usize = plans.iter().map(|plan| plan.shared.len()).sum();
    for copy in tuples
        .x
        .iter_mut()
        .chain(&mut tuples.y)
        .chain(&mut tuples.z)
    {
        copy.reserve(words * shared * LANES);
    }
    let mut product = vec![[Word::ZERO; W]; party.held.len() + 1];
    // The gate number continues from the earlier evaluations of the batch, so the collectors rotate over all gates of the batch.
    let (mut ands, mut gates) = (0, tuples.z[0].len() / (words * LANES).max(1));
    let (column, mut terms) = (words * LANES, Terms::default());
    let (mut filled, mut finished_start): (Vec<Vec<usize>>, _) = (vec![], 0);
    for step in 0..=C::LAYERS {
        let (finishing, starting) = (step.checked_sub(1).map(|l| &plans[l]), plans.get(step));
        let width = starting.map_or(0, |plan| plan.shared.len());
        let layer = gates..gates + width;
        let filling = party.exchanged(party.mode, layer.clone());
        let mut additive = Additive::new(width, column);
        let masks = party.reshare_masks(channel, &filling, &additive);
        let start = tuples.z[0].len();
        for (i, block) in blocks.blocks_mut().enumerate() {
            let (public, held) = block.split_first_mut().unwrap();
            if let Some(plan) = finishing {
                for (c, &a) in plan.shared.iter().enumerate() {
                    let at_tuple = finished_start + (i * plan.shared.len() + c) * LANES;
                    for &k in &filled[c] {
                        let value = Word::load(&terms.column(k, c)[i * LANES..]);
                        held[k][a] ^= value;
                        xor_into(&mut tuples.z[k][at_tuple..][..LANES], &value.0);
                    }
                }
            }
            let Some(plan) = starting else {
                continue;
            };
            circuit.linear(step, public);
            held.iter_mut()
                .for_each(|lanes| circuit.linear(step, lanes));
            // The holders of term 0 move the public part of each secret lane into term 0, so the terms alone hold the gate inputs.
            for l in (0..W).filter(|&l| plan.secret[l]) {
                if let Some(k) = term_zero {
                    held[k][l] ^= public[l];
                }
                public[l] = Word::ZERO;
            }
            let (public_product, held_product) = product.split_first_mut().unwrap();
            for (a, &(x, y)) in plan.ands.iter().enumerate() {
                let both = plan.secret[x] && plan.secret[y];
                public_product[a] = public[x] & public[y];
                for (product, term) in held_product.iter_mut().zip(held.iter()) {
                    product[a] = if both {
                        Word::ZERO
                    } else {
                        (public[x] & term[y]) ^ (public[y] & term[x])
                    };
                }
            }
            for (c, &a) in plan.shared.iter().enumerate() {
                let (x, y) = plan.ands[a];
                let v = mul(&pairs, |p| held[p][x], |q| held[q][y]);
                additive.column_mut(c)[i * LANES..][..LANES].copy_from_slice(&v.0);
                for (k, term) in held.iter().enumerate() {
                    let mask = match filling[c].contains(&k) {
                        true => Word::ZERO,
                        false => Word::load(&masks.column(k, c)[i * LANES..]),
                    };
                    held_product[k][a] = mask;
                    tuples.x[k].extend(term[x].0);
                    tuples.y[k].extend(term[y].0);
                    tuples.z[k].extend(mask.0);
                }
            }
            let parts = iter::once(&mut *public).chain(held.iter_mut());
            for (lanes, product) in parts.zip(&product) {
                circuit.combine(step, lanes);
                for a in 0..plan.ands.len() {
                    lanes[a] ^= product[a];
                }
            }
            circuit.constant(step, public);
        }
        if starting.is_none() {
            break;
        }
        let hashes = &mut tuples.hashes;
        terms = party
            .reshare(channel, party.mode, layer, additive, masks, hashes)
            .await?;
        (filled, finished_start) = (filling, start);
        gates += width;
        ands += 64 * (width * column) as u64;
    }
    Ok(ands)
}

pub struct Keccak {
    pub outputs: usize,
}

/// The lane `offset` places to the right in the same row.
fn neighbor(lane: usize, offset: usize) -> usize {
    lane / 5 * 5 + (lane + offset) % 5
}

impl Keccak {
    fn lanes(&self, layer: usize) -> usize {
        if layer + 1 == hash::ROUNDS {
            self.outputs
        } else {
            25
        }
    }
}

impl Circuit<25> for Keccak {
    const LAYERS: usize = hash::ROUNDS;

    /// Theta, rho and pi.
    fn linear<T: Lane>(&self, _: usize, a: &mut [T; 25]) {
        let c: [T; 5] = from_fn(|x| a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]);
        for x in 0..5 {
            let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            (0..5).for_each(|y| a[x + 5 * y] = a[x + 5 * y] ^ d);
        }
        let b = *a;
        for lane in 0..25 {
            a[hash::PI[lane]] = b[lane].rotate_left(hash::RHO[lane]);
        }
    }

    /// Chi is `a[x] ^ !a[x + 1] & a[x + 2]`, which equals `a[x] ^ a[x + 2] ^ a[x + 1] & a[x + 2]`. So gate `x` takes lanes `x + 1` and `x + 2` of its row, and `combine` adds lane `x + 2`.
    fn ands(&self, layer: usize) -> Vec<(usize, usize)> {
        (0..self.lanes(layer))
            .map(|l| (neighbor(l, 1), neighbor(l, 2)))
            .collect()
    }

    fn combine<T: Lane>(&self, layer: usize, a: &mut [T; 25]) {
        let b = *a;
        for l in 0..self.lanes(layer) {
            a[l] = b[l] ^ b[neighbor(l, 2)];
        }
    }

    /// Iota.
    fn constant<T: Lane>(&self, layer: usize, public: &mut [T; 25]) {
        public[0] = public[0] ^ T::splat(hash::RC[layer]);
    }
}

/// The circuit of one chain step and its secret lanes.
fn chain_step() -> (Keccak, [bool; 25]) {
    (Keccak { outputs: 2 }, from_fn(|l| l == 4 || l == 5))
}

/// The AND gates of one chain step that need messages.
pub fn gates() -> usize {
    let (circuit, secret) = chain_step();
    plans(&circuit, secret)
        .iter()
        .map(|plan| plan.shared.len())
        .sum()
}

/// Hashes one chain step for each instance. The state holds `P || A || y || l` and the Keccak padding, and only `y` in lanes 4 and 5 is secret.
pub async fn hash(
    party: &Party,
    channel: &mut Channel,
    blocks: &mut Replicated<25>,
    public: impl Fn(usize) -> Option<HashPublic>,
    tuples: &mut Tuples,
) -> Result<u64, String> {
    for (word, block) in blocks.blocks_mut().enumerate() {
        for lanes in block.iter_mut() {
            let secret = [lanes[0], lanes[1]];
            *lanes = [Word::ZERO; 25];
            lanes[4..6].copy_from_slice(&secret);
        }
        for slot in 0..LANES {
            let ([p0, p1, p2, p3], [s0, s1]) = public(LANES * word + slot).unwrap_or_default();
            for (l, value) in [p0, p1, p2, p3, 0, 0, s0, s1, hash::PAD_FIRST as u64]
                .into_iter()
                .enumerate()
            {
                block[0][l].0[slot] ^= value;
            }
            block[0][hash::RATE / 8 - 1].0[slot] = hash::END_BIT;
        }
    }
    let (circuit, secret_lanes) = chain_step();
    evaluate(party, &circuit, channel, blocks, secret_lanes, tuples).await
}

#[cfg(test)]
mod tests {
    use crate::check;
    use crate::circuit::*;
    use crate::mpc::Reshare;
    use crate::mpc::tests::local_parties;
    use std::iter;

    #[test]
    fn shared_keccak_f_matches_keccak_f() {
        let modes = [(Reshare::Collector, 89), (Reshare::Peer, 65)];
        for (t, (reshare, expected_rounds)) in [2, 3, 4]
            .into_iter()
            .flat_map(|t| modes.map(|mode| (t, mode)))
        {
            let word = |k: usize, l: usize, b: usize| {
                u64::from_le_bytes(
                    hash::hash(&[k as u8, l as u8, b as u8])[..8]
                        .try_into()
                        .unwrap(),
                )
            };
            let outcomes = local_parties(t, reshare, async |party, all_seeds| {
                let terms = all_seeds.len();
                let public = from_fn(|l| Word(from_fn(|b| word(terms, l, b))));
                let shares = party
                    .held
                    .iter()
                    .map(|&k| from_fn(|l| Word(from_fn(|b| word(k, l, b)))));
                let mut blocks = Replicated::new(&party, 1);
                blocks.parts = iter::once(public).chain(shares).collect();
                let mut channel = party.network.channel();
                let mut tuples = Tuples::new(&party, 0);
                let ands = evaluate(
                    &party,
                    &Keccak { outputs: 25 },
                    &mut channel,
                    &mut blocks,
                    [true; 25],
                    &mut tuples,
                )
                .await
                .unwrap();
                let copies = tuples.x.iter().chain(&tuples.y).chain(&tuples.z);
                assert!(copies.map(Vec::len).all(|words| words as u64 == ands / 64));
                check::mult_verification(&party, &mut channel, tuples)
                    .await
                    .unwrap();
                let opened = party.open(&mut channel, &blocks).await.unwrap();
                (opened, ands, channel.rounds, terms)
            });
            for (opened, ands, rounds, terms) in outcomes {
                for b in 0..LANES {
                    let mut expected: [u64; 25] =
                        from_fn(|l| (0..=terms).fold(0, |a, k| a ^ word(k, l, b)));
                    hash::keccak_f(&mut expected);
                    assert_eq!(opened[0].map(|lane| lane.0[b]), expected);
                }
                assert_eq!((ands, rounds), (LANES as u64 * 24 * 1600, expected_rounds));
            }
        }
    }
}
