//! This module holds verbatim copies of the leanXMSS items of leanVM that the code needs and that are not public at the pinned revision. Each item keeps its upstream name and links its source.
//!
//! These copies are a deviation from the rule to never duplicate leanVM code. They hold only the items that no public leanVM item replaces.

use signatures::lean_xmss::*;

// Copied from https://github.com/leanEthereum/leanVM/blob/f5f3672f2b72d3f89dbbaeff18a53a73c975d620/crates/signatures/src/lean_xmss/hash.rs
pub(crate) const TWEAK_PRF: u8 = 0;
pub(crate) const TWEAK_RANDOMIZER: u8 = 7;

// Copied from https://github.com/leanEthereum/leanVM/blob/f5f3672f2b72d3f89dbbaeff18a53a73c975d620/crates/signatures/src/lean_xmss/hash.rs
/// `Th` over a concatenation of digests: a Merkle node or a leaf.
pub(crate) fn th_digests(pp: &PublicParam, tw: &Tweak, values: &[Digest]) -> Digest {
    th(pp, tw, values.as_flattened())
}

// Copied from https://github.com/leanEthereum/leanVM/blob/f5f3672f2b72d3f89dbbaeff18a53a73c975d620/crates/signatures/src/lean_xmss/mod.rs
/// Randomizers tried per layer signature.
pub(crate) const MAX_RANDOMIZER_TRIALS: u64 = 1 << 32;

// Copied from https://github.com/leanEthereum/leanVM/blob/f5f3672f2b72d3f89dbbaeff18a53a73c975d620/crates/signatures/src/lean_xmss/wots.rs
/// The Merkle leaf of a one-time key: `Th` over its `v` chain ends.
#[rustfmt::skip]
pub(crate) fn wots_leaf_hash(pp: &PublicParam, layer: usize, e: u32, ends: &[Digest; V]) -> Digest {
    th_digests(pp, &tweak(TWEAK_LEAF, layer_hi(layer, 0), e), ends)
}

// Copied from https://github.com/leanEthereum/leanVM/blob/f5f3672f2b72d3f89dbbaeff18a53a73c975d620/crates/signatures/src/lean_xmss/tree.rs
/// The Merkle parent at `level` and index `j` of `layer`.
#[rustfmt::skip]
pub fn node(pp: &PublicParam, layer: usize, level: usize, j: u32, children: &[Digest; 2]) -> Digest {
    th_digests(pp, &tweak(TWEAK_NODE, layer_hi(layer, level as u32), j), children)
}
