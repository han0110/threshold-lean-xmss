//! This module implements `mult_verification`, the check of the AND tuples of one batch, after [`verify.rs`](https://github.com/TomWambsgans/sphincs.art/blob/df77d5671f70ba4959264183296777bdddec778d/crates/rss/src/verify.rs) of the leanSPHINCS prototype. That check is the sublinear check of [Goyal and Song](https://eprint.iacr.org/2020/134) with the compression factor 2.
//!
//! - The semi-honest gate is secure up to an additive attack. The check rejects a wrong tuple, except with a negligible probability, before any output opens.
//! - A coin is a random sharing from the seeds. Each operator converts it to a Shamir share, and the shares open robustly.
//! - `de_linearization` is Protocol 13 of the paper. A coin gives the coins `tau`, and their tensor `beta` weights the tuples.
//! - The claim is the inner-product tuple `(x, y, z)` with `x = beta x^(i)`, `y = y^(i)` and `z = sum beta z^(i)` for the tuples `(x^(i), y^(i), z^(i))`.
//! - Each operator converts its replicated terms to a Shamir share, as Cramer, Damgard and Ishai do. Its local inner product times `lambda` is an additive share of the inner product.
//! - `dimension_reduction` is Protocol 14 for each of the `R` halving steps. A step splits `x` into `a^(1)`, `a^(2)` and `y` into `b^(1)`, `b^(2)`, and it reshares `c^(1) = <a^(1), b^(1)>` and `p_2 = <a^(1) + a^(2), b^(1) + b^(2)>` in peer mode.
//! - A coin then gives a challenge `r` outside `{0, 1}`. The operators fold `x` and `y` at `r`, and the claim becomes `c^(1) + (z + p_2) r + p_2 r^2`.
//! - `randomization` is Protocol 15. It reshares `c^(0) = a^(0) b^(0)` and `q_2 = (a^(0) + a^(1)) (b^(0) + b^(1))` for random `a^(0)` and `b^(0)` and the last elements `a^(1)` and `b^(1)` of `x` and `y`.
//! - Its coin carries the salted digests of all held terms to every operator. An operator aborts unless all holders of each term send the same digest.
//! - Then `a = a^(0) + r (a^(0) + a^(1))`, `b = b^(0) + r (b^(0) + b^(1))` and `c = c^(0) + (z + c^(0) + q_2) r + q_2 r^2` open robustly, and each operator accepts if `a b = c`.
//! - A wrong tuple passes with a probability of at most `(d + 2 (R + 1)) / (2^192 - 2)` for `d` coins and `R` halving steps. A batch of 128 chains has `d = 18` and `R = 24`, so the bound is below `2^-185`, plus the advantages against AES-128 and Keccak-256.
//! - The code writes `a^(0)`, `a^(1)`, `b^(0)`, `b^(1)`, `c^(0)` and `c^(1)` of the paper as `a_0`, `a_1`, `b_0`, `b_1`, `c_0` and `c_1`.
//! - `F64` and `F192` are binary fields, so `+` also subtracts.
//!
//! The module differs from the prototype in these points.
//!
//! - The field is the leanVM field `F192` in place of GF(2^128).
//! - Bit `q` of a tuple word has the weight `x^q` in place of a coin. The lift of a word to `F64` is injective, so a wrong tuple still gives a nonzero multilinear polynomial in the coins.
//! - The first six halving steps fold the 64 slices of the tuple words with the small-value optimization of [Bagad, Dao, Domb and Thaler](https://eprint.iacr.org/2025/1117). Each operator adds the products of its pairs of terms into a table `T` at the 729 points of `{0, 1, INF}^6`. As [Gruen](https://eprint.iacr.org/2024/108) does, step `j` keeps the slice coin `c_j` out of `x`, so `x` and `y` fold with the same weights. The step reshares `t_j(0)` and `t_j(INF)`, and the claim `t_j(0) + c_j t_j(1)` gives `t_j(1)`.
//! - A slice has a multiple of 8 words. A halving step pads a vector of more than 16 elements to a multiple of 16, and a shorter vector to an even length. The prototype pads to powers of two.
//! - The callers derive the input terms from seeds whose holders compare hashes at the setup, so the check does not hash the input terms.
//! - The reshare pads a short message with zeros and truncates a long message, which gives an additive error. The prototype aborts.
//! - The prototype reshares each value of the check to the holders of the term number `j mod K`. Here every reshare of the check is the peer reshare of the AND gates, in both modes.
//! - The prototype compares the digests of a term only among its holders. Here every operator compares them, so a split copy stops every honest operator before `a`, `b` and `c` open.
//! - The prototype ends the check with a vote. Here each operator decides alone, as in step 8 of Protocol 15.

use crate::mpc::{Additive, Key, Party, Reshare, Shamir, Tuples, xor_into};
use crate::net::Channel;
use primitives::bit_fold::BitFold;
use primitives::bits::bit_transpose_64bytes;
use primitives::cast_slice;
use primitives::field::{
    Acc8, F192, F192Unreduced, Weights8, dot_base, fold_pairs8_ext, msg_terms8_ext, mul_by_g_e,
    mul4,
};
use primitives::hash::Hasher;
use primitives::multilinear::eq_table;
use std::array::from_fn;
use std::mem;

pub const SLICES: usize = 64;
/// The words of a block in `accumulate`. Its table of 729 points and its rows of the slices stay in the L2 cache.
const ACCUMULATE_BLOCK: usize = 32;

/// The words of a slice for `words` tuple words of a term.
pub fn slice_length(words: usize) -> usize {
    words.div_ceil(SLICES).next_multiple_of(8)
}

/// The tensor product of the factors. Bit `k` of an index selects `high` of factor `k`.
fn tensor(factors: impl IntoIterator<Item = [F192; 2]>) -> Vec<F192> {
    factors
        .into_iter()
        .fold(vec![F192::ONE], |table, [low, high]| {
            let scaled = |factor: F192| table.iter().map(move |&entry| entry * factor);
            scaled(low).chain(scaled(high)).collect()
        })
}

/// The value at `r` of the quadratic polynomial with the given values at zero and one and the given leading coefficient.
fn interpolate(at_zero: F192, at_one: F192, leading: F192, r: F192) -> F192 {
    at_zero + (at_one + at_zero + leading) * r + leading * r * r
}

/// `conv(reshare({v}))` of two additive values in peer mode, which gives their Shamir shares.
async fn conv_reshare(
    party: &Party,
    channel: &mut Channel,
    additive: Additive,
    hashes: &mut [Hasher],
) -> Result<[Shamir; 2], String> {
    let filled = party.exchanged(Reshare::Peer, 0..1);
    let masks = party.reshare_masks(channel, &filled, &additive);
    let terms = party.reshare(channel, Reshare::Peer, 0..1, additive, masks, hashes);
    let terms = terms.await?;
    Ok([0, 1].map(|v| party.conv(terms.value(v))))
}

fn challenge(party: &Party, key: &Key) -> F192 {
    let mut candidates = (0..).map(|index| party.expand(key, index, 1)[0]);
    candidates
        .find(|&r| r != F192::ZERO && r != F192::ONE)
        .unwrap()
}

/// XORs `x_z AND y_z` into row `z` of `products` at each point `z` of `{0, 1, INF}^m`, for `2^m` rows of `x` and of `y`. `x_z` is the XOR of the rows that match `z` at each coordinate other than INF. A point is a base-3 number with the digit 2 for INF, and its top digit is the top bit of a row number. `scratch` holds `2^(m + 1)` rows.
fn add_products(x: &[u64], y: &[u64], products: &mut [u64], scratch: &mut [u64]) {
    if x.len() == products.len() {
        let terms = products.iter_mut().zip(x.iter().zip(y));
        terms.for_each(|(product, (x, y))| *product ^= x & y);
        return;
    }
    let half = x.len() / 2;
    let ((x_low, x_high), (y_low, y_high)) = (x.split_at(half), y.split_at(half));
    let (at_zero, rest) = products.split_at_mut(products.len() / 3);
    let (at_one, at_infinity) = rest.split_at_mut(at_zero.len());
    add_products(x_low, y_low, at_zero, scratch);
    add_products(x_high, y_high, at_one, scratch);
    // The extension is linear, so the rows at INF are the sums of the rows at 0 and 1.
    let (sums, scratch) = scratch.split_at_mut(x.len());
    let (x_sum, y_sum) = sums.split_at_mut(half);
    let add = |sum: &mut [u64], low: &[u64], high: &[u64]| {
        let pairs = sum.iter_mut().zip(low.iter().zip(high));
        pairs.for_each(|(sum, (low, high))| *sum = low ^ high);
    };
    add(x_sum, x_low, x_high);
    add(y_sum, y_low, y_high);
    add_products(x_sum, y_sum, at_infinity, scratch);
}

/// The additive shares of `t_j(0)` and `t_j(INF)` of slice step `j`, from the additive shares of `T`. The challenges are those of the steps before `j`.
fn slice_round(table: &[F192], challenges: &[F192], slice_coins: &[F192]) -> [F192; 2] {
    // Each sum removes the last coordinate of the points, with the weights of the nodes 0, 1 and INF.
    let sum_out = |table: Vec<F192>, weights: [F192; 3]| -> Vec<F192> {
        let point = |values: &[F192]| {
            let terms = values.iter().zip(weights);
            terms.fold(F192::ZERO, |sum, (&value, weight)| sum + weight * value)
        };
        table.chunks(3).map(point).collect()
    };
    // The positions after `j` take the weights 1 and `c_k` of `beta`. Position `k` is bit `m - 1 - k` of a slice number, so the last position takes the first coin.
    let later = &slice_coins[..slice_coins.len() - 1 - challenges.len()];
    let at_bits = later.iter().fold(table.to_vec(), |table, &coin| {
        sum_out(table, [F192::ONE, coin, F192::ZERO])
    });
    // The positions before `j` take the Lagrange weights `L_0(r) = 1 + r`, `L_1(r) = r` and `L_INF(r) = r (1 + r)` of their challenges.
    let lagrange = |r: F192| [F192::ONE + r, r, r * (F192::ONE + r)];
    [0, 2].map(|node| {
        let at_node = at_bits.iter().skip(node).step_by(3).copied().collect();
        let earlier = challenges.iter().rev();
        earlier.fold(at_node, |table, &r| sum_out(table, lagrange(r)))[0]
    })
}

fn eights(vector: &[F192]) -> &[[F192; 8]] {
    vector.as_chunks().0
}

/// Pads `x` and `y`, and returns in one pass the two local inner products of a halving step, of `c^(1) = <a^(1), b^(1)>` and `p_2 = <a^(1) + a^(2), b^(1) + b^(2)>`.
fn sums(x: &mut Vec<Shamir>, y: &mut Vec<Shamir>) -> [F192; 2] {
    let length = x.len().next_multiple_of(if x.len() > 16 { 16 } else { 2 });
    x.resize(length, F192::ZERO);
    y.resize(length, F192::ZERO);
    let ((a_1, a_2), (b_1, b_2)) = (x.split_at(length / 2), y.split_at(length / 2));
    if a_1.len().is_multiple_of(8) {
        let (mut low, mut sum) = (Acc8::ZERO, Acc8::ZERO);
        let chunks = eights(a_1)
            .iter()
            .zip(eights(a_2))
            .zip(eights(b_1))
            .zip(eights(b_2));
        for (((a_1, a_2), b_1), b_2) in chunks {
            let (product, both) = msg_terms8_ext(a_1, a_2, b_1, b_2);
            low ^= product;
            sum ^= both;
        }
        [low.reduce(), sum.reduce()]
    } else {
        (0..a_1.len()).fold([F192::ZERO; 2], |[low, sum], i| {
            let both = (a_1[i] + a_2[i]) * (b_1[i] + b_2[i]);
            [low + a_1[i] * b_1[i], sum + both]
        })
    }
}

fn fold(vector: &mut Vec<Shamir>, r: F192) {
    let half = vector.len() / 2;
    let (low, high) = vector.split_at_mut(half);
    if half.is_multiple_of(8) {
        let pairs = low.as_chunks_mut::<8>().0.iter_mut().zip(eights(high));
        pairs.for_each(|(low, high)| *low = fold_pairs8_ext(low, high, r));
    } else {
        let pairs = low.iter_mut().zip(high.iter());
        pairs.for_each(|(low, &high)| *low += r * (*low + high));
    }
    vector.truncate(half);
}

/// The tuple words of each term as 64 slices of `length` words. Word `w` of slice `s` is at `s * length + w`.
struct Slices {
    length: usize,
    slice_coins: Vec<F192>,
    beta_slice: Vec<F192>,
    beta_word: Vec<F192>,
    weights: Vec<Weights8>,
}

impl Slices {
    fn new(tuples: &mut Tuples, length: usize, coins: &[F192]) -> Slices {
        let copies = tuples
            .x
            .iter_mut()
            .chain(&mut tuples.y)
            .chain(&mut tuples.z);
        copies.for_each(|copy| copy.resize(SLICES * length, 0));
        let (slice_coins, word_coins) = coins.split_at(SLICES.trailing_zeros() as usize);
        let beta = |coins: &[F192]| tensor(coins.iter().map(|&coin| [F192::ONE, coin]));
        let beta_word = beta(word_coins)[..length].to_vec();
        Slices {
            length,
            slice_coins: slice_coins.to_vec(),
            beta_slice: beta(slice_coins),
            weights: beta_word
                .chunks(8)
                .map(|w| Weights8::new(w.try_into().unwrap()))
                .collect(),
            beta_word,
        }
    }

    fn weighted(&self, words: &[u64]) -> F192 {
        dot_base(&self.weights, cast_slice(words)).reduce()
    }

    /// The Shamir share of the claim `z`.
    fn claim(&self, party: &Party, tuples: &Tuples) -> Shamir {
        let length = self.length;
        party.conv(tuples.z.iter().map(|z| {
            (0..SLICES).fold(F192::ZERO, |sum, s| {
                sum + self.beta_slice[s] * self.weighted(&z[s * length..(s + 1) * length])
            })
        }))
    }

    /// The additive share of this operator in `T`, from its pairs of terms as in the AND gate. Entry `z` is `sum_w beta_word[w] (x_z[w] AND y_z[w])` at the point `z` of `add_products`, and `m` is the number of slice coins.
    fn accumulate(&self, pairs: &[(usize, usize)], tuples: &Tuples) -> Vec<F192> {
        let (length, m) = (self.length, self.slice_coins.len());
        let (slices, points) = (1 << m, 3usize.pow(m as u32));
        let mut sums = vec![F192Unreduced::ZERO; points];
        let [mut x_rows, mut partner] = [(); 2].map(|_| vec![0; slices * ACCUMULATE_BLOCK]);
        let mut scratch = vec![0; 2 * slices * ACCUMULATE_BLOCK];
        let mut products = vec![0; points * ACCUMULATE_BLOCK];
        for start in (0..length).step_by(ACCUMULATE_BLOCK) {
            let block = ACCUMULATE_BLOCK.min(length - start);
            let (x_rows, partner) = (
                &mut x_rows[..slices * block],
                &mut partner[..slices * block],
            );
            let products = &mut products[..points * block];
            products.fill(0);
            for (a, x) in tuples.x.iter().enumerate() {
                // The local term first adds the `y` copies of its partner terms, so one AND covers all its pairs.
                partner.fill(0);
                for &(_, b) in pairs.iter().filter(|&&(first, _)| first == a) {
                    for (s, row) in partner.chunks_mut(block).enumerate() {
                        xor_into(row, &tuples.y[b][s * length + start..]);
                    }
                }
                for (s, row) in x_rows.chunks_mut(block).enumerate() {
                    row.copy_from_slice(&x[s * length + start..][..block]);
                }
                add_products(x_rows, partner, products, &mut scratch);
            }
            let weights = &self.weights[start / 8..(start + block) / 8];
            for (sum, product) in sums.iter_mut().zip(products.chunks(block)) {
                *sum ^= dot_base(weights, cast_slice(product));
            }
        }
        sums.iter().map(|sum| sum.reduce()).collect()
    }

    /// The vectors `x` and `y` after the six slice steps, lifted from the tuples. The first challenge folds the top bit of the slice number, so the weights take the challenges in reverse order.
    fn materialize(
        &self,
        party: &Party,
        tuples: &Tuples,
        challenges: &[F192],
    ) -> (Vec<Shamir>, Vec<Shamir>) {
        let fold_weights = eq_table(&challenges.iter().rev().copied().collect::<Vec<_>>());
        (
            self.lift(party, &tuples.x, &fold_weights, true),
            self.lift(party, &tuples.y, &fold_weights, false),
        )
    }

    /// Lifts the tuple words to a Shamir vector and folds the 64 slices with `slice_weights`. Element `64 w + q` is bit `q` of word `w`, and `weighted` multiplies it by `beta_word[w] x^q`.
    fn lift(
        &self,
        party: &Party,
        copies: &[Vec<u64>],
        slice_weights: &[F192],
        weighted: bool,
    ) -> Vec<Shamir> {
        let folds: Vec<BitFold> = party.group.phi[party.id]
            .iter()
            .map(|&phi| BitFold::new(&slice_weights.iter().map(|&w| w * phi).collect::<Vec<_>>()))
            .collect();
        let mut lifted = [F192::ZERO; 64];
        let mut vector = Vec::with_capacity(64 * self.length);
        for w in 0..self.length {
            let mut sum = [F192::ZERO; 64];
            for (copy, fold) in copies.iter().zip(&folds) {
                // The transposes give row `q` the bit `q` of word `w` from each of the 64 slices.
                let columns: [[u8; 64]; 8] = from_fn(|byte| {
                    let mut rows = [0; 64];
                    for (slice, row) in rows.as_chunks_mut::<8>().0.iter_mut().enumerate() {
                        *row = copy[(8 * byte + slice) * self.length + w].to_le_bytes();
                    }
                    let mut columns = [0; 64];
                    bit_transpose_64bytes(&rows, &mut columns);
                    columns
                });
                fold.fold_columns(&columns, &mut lifted);
                sum.iter_mut()
                    .zip(&lifted)
                    .for_each(|(sum, &value)| *sum += value);
            }
            if weighted {
                let mut weight = self.beta_word[w];
                for group in sum.as_chunks_mut::<4>().0 {
                    let weights = from_fn(|_| {
                        let current = weight;
                        weight = mul_by_g_e(weight);
                        current
                    });
                    *group = mul4(*group, weights);
                }
            }
            vector.extend_from_slice(&sum);
        }
        vector
    }
}

/// `MultVerification` (Protocol 17) of the AND tuples of the batch. Every operator aborts if a tuple is wrong, except with a negligible probability.
pub async fn mult_verification(
    party: &Party,
    channel: &mut Channel,
    mut tuples: Tuples,
) -> Result<(), String> {
    if tuples.x[0].is_empty() {
        return Ok(());
    }
    let (slices, z) = de_linearization(party, channel, &mut tuples).await?;
    let (z, a_1, b_1, hashes) = dimension_reduction(party, channel, tuples, &slices, z).await?;
    randomization(party, channel, z, a_1, b_1, hashes).await
}

/// `De-Linearization` (Protocol 13). A coin gives the coins `tau` of the tensor `beta`, and the claim is `<z> = conv(sum beta [[z^(i)]])`.
async fn de_linearization(
    party: &Party,
    channel: &mut Channel,
    tuples: &mut Tuples,
) -> Result<(Slices, Shamir), String> {
    let (key, _) = party.coin(channel, &[]).await?;
    let length = slice_length(tuples.x[0].len());
    let coins = (SLICES * length).next_power_of_two().trailing_zeros() as usize;
    let slices = Slices::new(tuples, length, &party.expand(&key, 0, coins));
    if slices.slice_coins.contains(&F192::ZERO) {
        return Err("a slice coin is zero".into());
    }
    let z = slices.claim(party, tuples);
    Ok((slices, z))
}

/// `Dimension-Reduction` (Protocol 14) with the compression factor 2, for each of the `R` halving steps. The slice steps fold the slices of the tuples with the table `T`, and the vector steps halve `x` and `y`. Each step reshares two values in peer mode, and a coin then gives its challenge.
async fn dimension_reduction(
    party: &Party,
    channel: &mut Channel,
    mut tuples: Tuples,
    slices: &Slices,
    z: Shamir,
) -> Result<(Shamir, Shamir, Shamir, Vec<Hasher>), String> {
    // `t` is the additive share of this operator in the table `T`, and `d` is the claim `D` of the slice steps, which starts at `z`.
    let t = slices.accumulate(&party.product_pairs(), &tuples);
    let (mut d, mut challenges) = (z, vec![]);
    for &coin in slices.slice_coins.iter().rev() {
        let t_j = Additive::values(slice_round(&t, &challenges, &slices.slice_coins).into_iter());
        let [t_j0, t_jinf] = conv_reshare(party, channel, t_j, &mut tuples.hashes).await?;
        let r = challenge(party, &party.coin(channel, &[]).await?.0);
        // The claim is `t_j(0) + c_j t_j(1)`, so it gives `t_j(1)`.
        d = interpolate(t_j0, (d + t_j0) * coin.inv(), t_jinf, r);
        challenges.push(r);
    }
    let (mut x, mut y) = slices.materialize(party, &tuples, &challenges);
    let mut hashes = mem::take(&mut tuples.hashes);
    drop(tuples);
    let mut z = d;
    while x.len() > 1 {
        let p = party.mul_shamir(&sums(&mut x, &mut y));
        let [c_1, p_2] = conv_reshare(party, channel, p, &mut hashes).await?;
        let r = challenge(party, &party.coin(channel, &[]).await?.0);
        z = interpolate(c_1, z + c_1, p_2, r);
        fold(&mut x, r);
        fold(&mut y, r);
    }
    Ok((z, x[0], y[0], hashes))
}

/// `Randomization` (Protocol 15). Random `a^(0)` and `b^(0)` mask the last elements `a^(1)` and `b^(1)` of `x` and `y`. The coin of `r` carries the digests, so a split term stops every operator before `a`, `b` and `c` open.
async fn randomization(
    party: &Party,
    channel: &mut Channel,
    z: Shamir,
    a_1: Shamir,
    b_1: Shamir,
    mut hashes: Vec<Hasher>,
) -> Result<(), String> {
    let random = party.rand(channel, 1, 6);
    let (a_0, b_0) = (party.conv(random.value(0)), party.conv(random.value(1)));
    let q = party.mul_shamir(&[a_0 * b_0, (a_0 + a_1) * (b_0 + b_1)]);
    let [c_0, q_2] = conv_reshare(party, channel, q, &mut hashes).await?;
    let digests = party.digests(channel, &hashes);
    let (key, received) = party.coin(channel, &digests).await?;
    party.compare_digests(&digests, &received)?;
    let r = challenge(party, &key);
    let shares = [
        a_0 + r * (a_0 + a_1),
        b_0 + r * (b_0 + b_1),
        interpolate(c_0, z, q_2, r),
    ];
    let opened = party.open_shamir(channel, &shares, &[]).await?.0;
    let [a, b, c]: [F192; 3] = opened.try_into().unwrap();
    match a * b == c {
        true => Ok(()),
        false => Err("the AND tuples fail the check".into()),
    }
}

#[cfg(test)]
mod tests {
    use crate::check::*;
    use crate::circuit::{Keccak, evaluate};
    use crate::mpc::tests::local_parties;
    use crate::mpc::{Group, Replicated, Reshare, Tamper, Word};
    use primitives::field::F64;
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};
    use std::sync::atomic::Ordering;

    async fn evaluated(party: &Party, channel: &mut Channel) -> (Tuples, Replicated<25>) {
        let mut blocks = Replicated::new(party, 1);
        blocks.parts.fill([Word([7, 8, 9, 10]); 25]);
        let (circuit, mut tuples) = (Keccak { outputs: 25 }, Tuples::new(party, 0));
        let evaluation = evaluate(
            party,
            &circuit,
            channel,
            &mut blocks,
            [true; 25],
            &mut tuples,
        );
        evaluation.await.unwrap();
        (tuples, blocks)
    }

    fn honest(_: &Channel, outgoing: Vec<Vec<u64>>) -> Vec<Vec<u64>> {
        outgoing
    }

    /// Operator 0 keeps `u_0` and sends it with one flipped bit to the last co-holder of `T_0` in the first peer round.
    fn flip_to_one_co_holder(channel: &Channel, mut outgoing: Vec<Vec<u64>>) -> Vec<Vec<u64>> {
        if channel.rounds == 0 {
            outgoing.last_mut().unwrap()[0] ^= 1;
        }
        outgoing
    }

    /// Operator 0 sends the messages that carry its contributions `u_0` through `send`, and every operator applies `tamper` before the check.
    fn tampered(
        t: usize,
        reshare: Reshare,
        send: Tamper,
        tamper: impl Fn(&Party, &mut Tuples, &mut Replicated<25>) + Sync,
    ) -> Vec<Result<(), String>> {
        local_parties(t, reshare, async |mut party, _| {
            if party.id == 0 {
                party.tamper = send;
            }
            let mut channel = party.network.channel();
            let (mut tuples, mut blocks) = evaluated(&party, &mut channel).await;
            tamper(&party, &mut tuples, &mut blocks);
            mult_verification(&party, &mut channel, tuples).await?;
            party.open(&mut channel, &blocks).await.map(|_| ())
        })
    }

    #[test]
    fn an_additive_error_or_an_inconsistent_copy_aborts_every_honest_operator() {
        let modes = [Reshare::Collector, Reshare::Peer];
        for (t, reshare) in [2, 3].into_iter().flat_map(|t| modes.map(|mode| (t, mode))) {
            // A batch with no tuples passes the check.
            for clear in [false, true] {
                let clear_tuples = |_: &Party, tuples: &mut Tuples, _: &mut Replicated<25>| {
                    if clear {
                        let copies = tuples
                            .x
                            .iter_mut()
                            .chain(&mut tuples.y)
                            .chain(&mut tuples.z);
                        copies.for_each(Vec::clear);
                    }
                };
                let outcomes = tampered(t, reshare, honest, clear_tuples);
                assert!(outcomes.iter().all(Result::is_ok));
            }
            // A slice has 40 words, so the last flip hits the last word of slice 63, which only pads the tuples.
            for flips in [
                &[(77, 1 << 13)][..],
                &[(77, 1 << 3 | 1 << 40)],
                &[(5, 1 << 9), (900, 1 << 9)],
                &[(0, 1)],
                &[(SLICES * 40 - 1, 1 << 63)],
            ] {
                let flip_held_term_zero =
                    |party: &Party, tuples: &mut Tuples, _: &mut Replicated<25>| {
                        if let Some(k) = party.held.iter().position(|&term| term == 0) {
                            tuples.z[k].resize(SLICES * slice_length(tuples.x[0].len()), 0);
                            flips
                                .iter()
                                .for_each(|&(word, bits)| tuples.z[k][word] ^= bits);
                        }
                    };
                assert!(
                    tampered(t, reshare, honest, flip_held_term_zero)
                        .iter()
                        .all(Result::is_err)
                );
            }
            let flip_one_tuple_copy =
                |party: &Party, tuples: &mut Tuples, _: &mut Replicated<25>| {
                    if party.id == 1 {
                        tuples.z[0][77] ^= 1 << 13;
                    }
                };
            assert!(
                tampered(t, reshare, honest, flip_one_tuple_copy)
                    .iter()
                    .all(Result::is_err)
            );
            // Operator 1 hashes one more value for its first held term, so every operator sees the digests of that term differ.
            let group = Group::new(t);
            let term = group.held(1)[0];
            let collect_another_value =
                |party: &Party, tuples: &mut Tuples, _: &mut Replicated<25>| {
                    if party.id == 1 {
                        tuples.hashes[0].update(&[1]);
                    }
                };
            let differ = Err(format!("the holders of term {term} send different digests"));
            let outcomes = tampered(t, reshare, honest, collect_another_value);
            assert_eq!(outcomes, vec![differ; group.n]);
            // Only the operators that lack the term receive its copy or a hash of it, so only they abort.
            let flip_one_copy = |party: &Party, _: &mut Tuples, blocks: &mut Replicated<25>| {
                if party.id == 1 {
                    blocks.parts[1][3].0[2] ^= 1;
                }
            };
            let outcomes = tampered(t, reshare, honest, flip_one_copy);
            for (id, outcome) in outcomes.into_iter().enumerate().filter(|&(id, _)| id != 1) {
                let expected = match group.holds(id, term) {
                    true => Ok(()),
                    false => Err(format!("the holders of term {term} send different copies")),
                };
                assert_eq!(outcome, expected, "operator {id} at t = {t}");
            }
        }
        // Operator 0 keeps `u_0` and sends it with one flipped bit in the first peer round. At `t = 2` the term `T_0` has only one co-holder.
        let flip_to_every_co_holder = |channel: &Channel, mut outgoing: Vec<Vec<u64>>| {
            if channel.rounds == 0 {
                let co_holders = outgoing
                    .iter_mut()
                    .skip(1)
                    .filter(|words| !words.is_empty());
                co_holders.for_each(|words| words[0] ^= 1);
            }
            outgoing
        };
        // Operator 0 also flips the copy that it keeps, so all holders of `T_0` agree and only the multiplication check fails.
        let flip_every_copy = |channel: &Channel, mut outgoing: Vec<Vec<u64>>| {
            if channel.rounds == 0 {
                let copies = outgoing.iter_mut().filter(|words| !words.is_empty());
                copies.for_each(|words| words[0] ^= 1);
            }
            outgoing
        };
        // The holders of `T_0` hold different copies, so every operator sees their digests differ at the coin of `r`.
        let differ = |t: usize| {
            let term = Group::new(t).peer_terms[0];
            vec![Err(format!("the holders of term {term} send different digests")); 2 * t - 1]
        };
        for t in [2, 3] {
            let outcomes = tampered(t, Reshare::Peer, flip_to_every_co_holder, |_, _, _| ());
            assert_eq!(outcomes, differ(t));
            let outcomes = tampered(t, Reshare::Peer, flip_every_copy, |_, _, _| ());
            let failed = Err("the AND tuples fail the check".to_string());
            assert_eq!(outcomes, vec![failed; 2 * t - 1]);
        }
        let outcomes = tampered(3, Reshare::Peer, flip_to_one_co_holder, |_, _, _| ());
        assert_eq!(outcomes, differ(3));
    }

    /// Operator 0 forwards a collected term with one flipped bit to the last operator in round 2 of the first layer.
    fn flip_forwarded(channel: &Channel, mut outgoing: Vec<Vec<u64>>) -> Vec<Vec<u64>> {
        if channel.rounds == 1 {
            outgoing.last_mut().unwrap()[0] ^= 1;
        }
        outgoing
    }

    #[test]
    fn a_coalition_that_splits_a_gate_copy_stops_every_honest_operator_before_its_final_shares() {
        let modes = [Reshare::Collector, Reshare::Peer];
        for (t, mode) in [3, 4].into_iter().flat_map(|t| modes.map(|mode| (t, mode))) {
            // Operators 0 to `t - 2` ignore the digests. In peer mode the honest operator `t - 1` is a member of `T_0`, so it holds no copy.
            let (group, stars) = (Group::new(t), &Group::new(t).collectors);
            let (send, term): (Tamper, usize) = match mode {
                Reshare::Peer => (flip_to_one_co_holder, group.peer_terms[0]),
                Reshare::Collector => {
                    let forwarded = (0..25).map(|gate| stars[gate % stars.len()]);
                    let mut to_last =
                        forwarded.filter(|&(k, kappa)| kappa == 0 && group.holds(group.n - 1, k));
                    (flip_forwarded, to_last.next().unwrap().0)
                }
            };
            let outcomes = local_parties(t, mode, async |mut party, _| {
                if party.id == 0 {
                    party.tamper = send;
                }
                party.ignores_digests = party.id + 1 < t;
                let mut channel = party.network.channel();
                let (tuples, _) = evaluated(&party, &mut channel).await;
                let sent = || party.network.sent.load(Ordering::Relaxed);
                let start = sent();
                let outcome = mult_verification(&party, &mut channel, tuples).await;
                (outcome, sent() - start)
            });
            let differ = Err(format!("the holders of term {term} send different digests"));
            // Every operator sends the same bytes until the coin of `r`. The final shares are 9 words for each other operator.
            let (honest, final_shares) = (outcomes[t - 1].1, 72 * (2 * t as u64 - 2));
            for (id, (outcome, sent)) in outcomes.into_iter().enumerate() {
                match id + 1 < t {
                    true => assert_eq!(
                        sent,
                        honest + final_shares,
                        "operator {id}, t = {t}, {mode:?}"
                    ),
                    false => assert_eq!(
                        (outcome, sent),
                        (differ.clone(), honest),
                        "t = {t}, {mode:?}"
                    ),
                }
            }
        }
    }

    fn elements(rng: &mut StdRng, count: usize) -> Vec<F192> {
        let element = |_| F192::new(rng.random(), rng.random(), rng.random());
        (0..count).map(element).collect()
    }

    /// Random tuples of one copy in `2^m` slices of 8 words, and their slices with random coins.
    fn plaintext(rng: &mut StdRng, m: usize) -> (Tuples, Slices) {
        let length = 8;
        let mut words = || -> Vec<u64> { (0..length << m).map(|_| rng.random()).collect() };
        let (x, y) = (words(), words());
        let z = x.iter().zip(&y).map(|(x, y)| x & y).collect();
        let beta = |coins: &[F192]| tensor(coins.iter().map(|&coin| [F192::ONE, coin]));
        let (slice_coins, beta_word) = (elements(rng, m), beta(&elements(rng, 3)));
        let slices = Slices {
            length,
            beta_slice: beta(&slice_coins),
            slice_coins,
            weights: vec![Weights8::new(beta_word[..].try_into().unwrap())],
            beta_word,
        };
        let tuples = Tuples {
            x: vec![x],
            y: vec![y],
            z: vec![z],
            hashes: vec![],
        };
        (tuples, slices)
    }

    /// `sum_w beta_word[w] sum_q x^q X(w, q) Y(w, q)`, where `X(w, q)` adds the weights of the slices with bit `q` set in word `w`. Slice `s` has the weight `prod_k weights[k][s_k]` for its bit `s_k` at position `k`.
    fn naive(x: &[u64], y: &[u64], beta_word: &[F192], weights: &[[F192; 2]]) -> F192 {
        let (m, length) = (weights.len(), beta_word.len());
        let slice_weight = |s: usize| {
            let bit = |k: usize| s >> (m - 1 - k) & 1;
            (0..m).fold(F192::ONE, |product, k| product * weights[k][bit(k)])
        };
        let slice_weights: Vec<F192> = (0..1 << m).map(slice_weight).collect();
        let folded = |copy: &[u64], w: usize, q: usize| {
            let set = slice_weights
                .iter()
                .enumerate()
                .filter(|&(s, _)| copy[s * length + w] >> q & 1 == 1);
            set.fold(F192::ZERO, |sum, (_, &weight)| sum + weight)
        };
        let bits = (0..length).flat_map(|w| (0..64).map(move |q| (w, q)));
        bits.fold(F192::ZERO, |sum, (w, q)| {
            sum + beta_word[w].mul_base(F64(1 << q)) * folded(x, w, q) * folded(y, w, q)
        })
    }

    /// `t_j(0)` and `t_j(INF)` of slice step `j` from the folded words, without `T`. The challenges are those of the steps before `j`.
    fn naive_round(x: &[u64], y: &[u64], slices: &Slices, challenges: &[F192]) -> [F192; 2] {
        let (m, j) = (slices.slice_coins.len(), challenges.len());
        let earlier = challenges.iter().map(|&r| [F192::ONE + r, r]);
        let selected = |bit: usize| match bit {
            0 => [F192::ONE, F192::ZERO],
            _ => [F192::ZERO, F192::ONE],
        };
        [[F192::ONE, F192::ZERO], [F192::ONE; 2]].map(|at_node| {
            (0..1 << (m - 1 - j)).fold(F192::ZERO, |sum, later: usize| {
                let bits: Vec<(usize, usize)> =
                    (j + 1..m).map(|k| (k, later >> (m - 1 - k) & 1)).collect();
                let coins = bits.iter().filter(|&&(_, bit)| bit == 1);
                let coin = coins.fold(F192::ONE, |product, &(k, _)| {
                    product * slices.slice_coins[m - 1 - k]
                });
                let weights: Vec<[F192; 2]> = earlier
                    .clone()
                    .chain([at_node])
                    .chain(bits.iter().map(|&(_, bit)| selected(bit)))
                    .collect();
                sum + coin * naive(x, y, &slices.beta_word, &weights)
            })
        })
    }

    #[test]
    fn the_slice_steps_end_at_the_product_of_the_folded_words_unless_a_tuple_is_wrong() {
        let mut rng = StdRng::seed_from_u64(7);
        for (m, wrong) in (1..=6).flat_map(|m| [(m, false), (m, true)]) {
            let (mut tuples, slices) = plaintext(&mut rng, m);
            let length = slices.length;
            if wrong {
                let word = rng.random_range(0..length << m);
                tuples.z[0][word] ^= 1 << rng.random_range(0..64);
            }
            let claim = (0..1 << m).fold(F192::ZERO, |sum, s: usize| {
                let coins = (0..m).filter(|&k| s >> k & 1 == 1);
                let beta_slice =
                    coins.fold(F192::ONE, |product, k| product * slices.slice_coins[k]);
                let words = tuples.z[0][s * length..(s + 1) * length].iter();
                let weighted = words
                    .zip(&slices.beta_word)
                    .fold(F192::ZERO, |sum, (&word, &beta)| {
                        sum + beta.mul_base(F64(word))
                    });
                sum + beta_slice * weighted
            });
            let table = slices.accumulate(&[(0, 0)], &tuples);
            let challenges = elements(&mut rng, m);
            let coins = slices.slice_coins.iter().rev().enumerate();
            let claim = coins.fold(claim, |claim, (j, &coin)| {
                let [at_zero, at_infinity] =
                    slice_round(&table, &challenges[..j], &slices.slice_coins);
                let at_one = (claim + at_zero) * coin.inv();
                interpolate(at_zero, at_one, at_infinity, challenges[j])
            });
            let eq: Vec<[F192; 2]> = challenges.iter().map(|&r| [F192::ONE + r, r]).collect();
            let direct = naive(&tuples.x[0], &tuples.y[0], &slices.beta_word, &eq);
            assert_eq!(claim == direct, !wrong, "m = {m}");
        }
    }

    #[test]
    fn each_slice_step_gives_the_values_of_the_folded_words() {
        let mut rng = StdRng::seed_from_u64(8);
        for m in 1..=6 {
            let (tuples, slices) = plaintext(&mut rng, m);
            let table = slices.accumulate(&[(0, 0)], &tuples);
            let challenges = elements(&mut rng, m);
            for j in 0..m {
                let naive = naive_round(&tuples.x[0], &tuples.y[0], &slices, &challenges[..j]);
                let values = slice_round(&table, &challenges[..j], &slices.slice_coins);
                assert_eq!(values, naive, "m = {m}, j = {j}");
            }
        }
    }

    #[test]
    fn the_shares_of_each_slice_step_add_up_to_its_values_on_the_plaintext_words() {
        let challenges = elements(
            &mut StdRng::seed_from_u64(9),
            SLICES.trailing_zeros() as usize,
        );
        for t in [2, 3] {
            let outcomes = local_parties(t, Reshare::Collector, async |party, _| {
                let mut channel = party.network.channel();
                let (mut tuples, _) = evaluated(&party, &mut channel).await;
                let length = slice_length(tuples.x[0].len());
                let count = (SLICES * length).next_power_of_two().trailing_zeros() as usize;
                let coins = elements(&mut StdRng::seed_from_u64(10), count);
                let slices = Slices::new(&mut tuples, length, &coins);
                let table = slices.accumulate(&party.product_pairs(), &tuples);
                let shares: Vec<[F192; 2]> = (0..challenges.len())
                    .map(|j| slice_round(&table, &challenges[..j], &slices.slice_coins))
                    .collect();
                // Each term has one owner, so the owned copies of all operators add up to the plaintext words.
                let owned = |copies: &[Vec<u64>]| {
                    let held = party.held.iter().zip(copies);
                    let owned = held.filter(|&(&term, _)| party.group.owner[term] == party.id);
                    owned.fold(vec![0; SLICES * length], |mut sum, (_, copy)| {
                        xor_into(&mut sum, copy);
                        sum
                    })
                };
                (shares, owned(&tuples.x), owned(&tuples.y), slices)
            });
            let combine = |copies: Vec<&Vec<u64>>| {
                copies
                    .iter()
                    .fold(vec![0; copies[0].len()], |mut sum, copy| {
                        xor_into(&mut sum, copy);
                        sum
                    })
            };
            let x = combine(outcomes.iter().map(|outcome| &outcome.1).collect());
            let y = combine(outcomes.iter().map(|outcome| &outcome.2).collect());
            for j in 0..challenges.len() {
                let add = |[a, b]: [F192; 2], outcome: &(Vec<[F192; 2]>, _, _, _)| {
                    [a + outcome.0[j][0], b + outcome.0[j][1]]
                };
                let summed = outcomes.iter().fold([F192::ZERO; 2], add);
                let naive = naive_round(&x, &y, &outcomes[0].3, &challenges[..j]);
                assert_eq!(summed, naive, "t = {t}, j = {j}");
            }
        }
    }
}
