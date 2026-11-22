//! This module holds verbatim copies of the leanXMSS items of leanVM that the code needs and that are not public at the
//! pinned revision. Each item keeps its upstream name. A comment names its source file, which is [`hash.rs`],
//! [`lib.rs`], [`tree.rs`] or [`wots.rs`].
//!
//! These copies are a deviation from the rule to never duplicate leanVM code. They hold only the items that no public
//! leanVM item replaces.
//!
//! [`hash.rs`]: https://github.com/leanEthereum/leanVM/blob/f95bc21a4875e10a733f4b2e56f1d4adb81536eb/crates/lean_xmss/src/hash.rs
//! [`lib.rs`]: https://github.com/leanEthereum/leanVM/blob/f95bc21a4875e10a733f4b2e56f1d4adb81536eb/crates/lean_xmss/src/lib.rs
//! [`tree.rs`]: https://github.com/leanEthereum/leanVM/blob/f95bc21a4875e10a733f4b2e56f1d4adb81536eb/crates/lean_xmss/src/tree.rs
//! [`wots.rs`]: https://github.com/leanEthereum/leanVM/blob/f95bc21a4875e10a733f4b2e56f1d4adb81536eb/crates/lean_xmss/src/wots.rs

use keccak256::RATE;
use lean_xmss::internals::*;
use tracing::instrument;

// Copied from `hash.rs`.
pub(crate) const TWEAK_PRF: u8 = 0;
pub(crate) const TWEAK_RANDOMIZER: u8 = 7;

// Copied from `hash.rs`.
/// `Th` over a concatenation of digests: a Merkle node or a leaf.
pub(crate) fn th_digests(pp: &PublicParam, tw: &Tweak, values: &[Digest]) -> Digest {
    th(pp, tw, values.as_flattened())
}

// Copied from `lib.rs`.
/// Randomizers tried per layer signature.
pub(crate) const MAX_RANDOMIZER_TRIALS: u64 = 1 << 32;

// Copied from `wots.rs`.
/// The Merkle leaf of a one-time key: `Th` over its `v` chain ends.
#[rustfmt::skip]
pub(crate) fn wots_leaf_hash(pp: &PublicParam, layer: usize, e: u32, ends: &[Digest; V]) -> Digest {
    th_digests(pp, &tweak(TWEAK_LEAF, layer_hi(layer, 0), e), ends)
}

// Copied from `wots.rs`.
/// Whether the digest `d`, little endian, is a codeword: its digits past the `v`th are
/// zero, and a two-bit digit being its low bit plus twice its high bit, the others sum
/// to `T`.
fn is_codeword(d: u128) -> bool {
    const _: () = assert!(W == 2);
    const LOW: u128 = u128::MAX / 3;
    d >> (W * V) == 0 && (d & LOW).count_ones() + 2 * (d & !LOW).count_ones() == TARGET_SUM as u32
}

// Copied from `wots.rs`.
/// Trials hashed at once.
const GRIND_BATCH: usize = 64;

// Copied from `wots.rs`.
/// The least `c` below `MAX_RANDOMIZER_TRIALS` whose randomizer `base + c`, as the last
/// 16 bytes of `input`, makes its digest a codeword: the least, which keeps one key to one
/// codeword. Those bytes are zero in `input` and lie in its last block, so the blocks before
/// are absorbed once and a trial costs one permutation.
#[rustfmt::skip]
#[instrument(name = "grind", skip_all)]
pub(crate) fn least_trial(input: &[u8], base: u128) -> Option<u64> {
    let at = input.len() - RANDOMIZER_LEN;
    assert!(at.is_multiple_of(8) && at / RATE == input.len() / RATE);
    let template = keccak256::final_state(input);
    let (mut values, mut digests) = ([0; GRIND_BATCH], [0; GRIND_BATCH]);
    (0..MAX_RANDOMIZER_TRIALS).step_by(GRIND_BATCH).find_map(|first| {
        let n = (MAX_RANDOMIZER_TRIALS - first).min(GRIND_BATCH as u64) as usize;
        for (c, value) in (first..).zip(&mut values[..n]) {
            *value = base.wrapping_add(u128::from(c));
        }
        keccak256::digest_halves_from(&template, at % RATE / 8, &values[..n], &mut digests[..n]);
        digests[..n]
            .iter()
            .position(|&d| is_codeword(d))
            .map(|hit| first + hit as u64)
    })
}

// Copied from `tree.rs`.
/// The Merkle parent at `level` and index `j` of `layer`.
#[rustfmt::skip]
pub fn node(pp: &PublicParam, layer: usize, level: usize, j: u32, children: &[Digest; 2]) -> Digest {
    th_digests(pp, &tweak(TWEAK_NODE, layer_hi(layer, level as u32), j), children)
}
