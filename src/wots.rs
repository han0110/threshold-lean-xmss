//! This module implements the leanXMSS signature of [EIP-8450], from leanVM [`lean_xmss`].
//!
//! - `pp` is the public parameter `P`, and `e` is the index of a one-time key in its layer.
//! - `Layer::Bottom` signs messages and `Layer::Top` signs the roots of the bottom trees. Their discriminants are the
//!   leanVM layer indices.
//! - The randomizer search of `wots_sign` takes an opened value of the threshold PRF in place of the seed.
//!   - A quorum opens it for the bottom layer, and the MPC opens it for the top layer.
//!
//! [EIP-8450]: https://eips.ethereum.org/EIPS/eip-8450
//! [`lean_xmss`]: https://github.com/leanEthereum/leanVM/tree/f95bc21a4875e10a733f4b2e56f1d4adb81536eb/crates/lean_xmss

use std::array::from_fn;

pub use lean_xmss::internals::{
    CHAIN_LEN, Digest, LAYER_HEIGHT, TWEAK_CHAIN, V, address, chain, layer_hi, layer_index, tweak,
};
use lean_xmss::internals::{RANDOMIZER_LEN, TWEAK_MSG, codeword, hasher, message_digest, sig_bottom};
use lean_xmss::{LeafIndex, LeanXmssPublicKey, LeanXmssSignature, SIG_SIZE};
use tracing::instrument;

pub(crate) use crate::lean_xmss::{TWEAK_PRF, TWEAK_RANDOMIZER, wots_leaf_hash};
use crate::lean_xmss::{least_trial, node, th_digests};
use crate::mpc::{Tag, tagged_hash};

pub const KEYS: usize = 1 << LAYER_HEIGHT;
/// One layer signature, the half of a leanXMSS signature after the leaf index.
pub const LAYER_SIG_SIZE: usize = (SIG_SIZE - size_of::<LeafIndex>()) / 2;

pub fn truncated_hash(tag: &Tag, parts: &[&[u8]]) -> Digest {
    tagged_hash(tag, parts)[..16].try_into().unwrap()
}

pub fn xor(a: Digest, b: Digest) -> Digest {
    from_fn(|i| a[i] ^ b[i])
}

#[derive(Clone, Copy, PartialEq)]
pub enum Layer {
    Bottom,
    Top,
}

pub fn layer_address(kind: u8, layer: Layer, hi: u32, e: u32, step: usize) -> Digest {
    address(&tweak(kind, layer_hi(layer as usize, hi), e).step(step))
}

pub fn prf_address(layer: Layer, e: u32, chain: usize, position: usize) -> Digest {
    layer_address(TWEAK_PRF, layer, chain as u32, e, position)
}

/// The commitment `c_e` of bottom key `e` to the randomizer value `F(A_rnd(e))`. It hashes the
/// value at `A_rnd(e)` with step 1, which no leanXMSS hash uses.
pub fn commitment(pp: &Digest, e: u32, value: Digest) -> Digest {
    let address = tweak(TWEAK_RANDOMIZER, layer_hi(Layer::Bottom as usize, 0), e).step(1);
    th_digests(pp, &address, &[value, 0u128.to_le_bytes()])
}

pub fn layer_root(pp: &Digest, layer: Layer, e: u32, message: &[u8], signature: &[u8]) -> Option<Digest> {
    // leanVM builds a `LayerSignature` only from the bytes of a full signature, so the layer
    // signature takes the place of the bottom layer in a zero signature.
    let mut bytes = [0; SIG_SIZE];
    bytes[size_of::<LeafIndex>()..][..LAYER_SIG_SIZE].copy_from_slice(signature);
    let signature = LeanXmssSignature::from_bytes(&bytes);
    lean_xmss::internals::layer_root(pp, layer as usize, e, message, sig_bottom(&signature), |_| {})
        .map(|(_, root)| root)
}

#[instrument(skip_all)]
pub fn verify(public_key: &[u8], message: &[u8], signature: &[u8]) -> bool {
    let (Ok(public_key), Ok(message), Ok(signature)) =
        (public_key.try_into(), message.try_into(), signature.try_into())
    else {
        return false;
    };
    let (public_key, signature) = (
        LeanXmssPublicKey::from_bytes(public_key),
        LeanXmssSignature::from_bytes(signature),
    );
    lean_xmss::verify(&public_key, message, &signature)
}

/// The tweak kind of a surrogate node. It is `TWEAK_SURROGATE` of the pruned keys of leanSPHINCS in [`hash.rs`], and
/// no leanXMSS hash uses it.
///
/// [`hash.rs`]: https://github.com/leanEthereum/leanVM/blob/1acdff19dffcaaf1642e88a9e9b522b415425168/crates/signatures/src/lean_sphincs/hash.rs
pub const TWEAK_SURROGATE: u8 = 13;

/// The surrogate of node `j` at `level`, which takes the place of a subtree with no keys.
///
/// It follows the surrogate nodes of `key_gen_from_seed` of leanSPHINCS in [`scheme.rs`], with these differences.
///
/// - leanSPHINCS hashes the master secret, which no operator holds. This function hashes no input.
/// - leanSPHINCS uses the address `(TWEAK_SURROGATE, level, 0)`. This address also has the layer and the node `j`.
/// - leanSPHINCS selects the kept subtree by the bits of the public parameter. `levels` keeps the first keys.
///
/// [`scheme.rs`]: https://github.com/leanEthereum/leanVM/blob/1acdff19dffcaaf1642e88a9e9b522b415425168/crates/signatures/src/lean_sphincs/scheme.rs
pub fn surrogate(pp: &Digest, layer: Layer, level: usize, j: u32) -> Digest {
    th_digests(
        pp,
        &tweak(TWEAK_SURROGATE, layer_hi(layer as usize, level as u32), j),
        &[],
    )
}

/// This function follows `LayerTree::build` of [`tree.rs`] for the first keys of a tree, a power of two.
///
/// A level above the keys holds its node and then the surrogate beside it, so `path` reads each level in one way.
///
/// [`tree.rs`]: https://github.com/leanEthereum/leanVM/blob/f95bc21a4875e10a733f4b2e56f1d4adb81536eb/crates/lean_xmss/src/tree.rs
pub fn levels(pp: &Digest, layer: Layer, index: u32, leaves: Vec<Digest>) -> Vec<Vec<Digest>> {
    assert!(leaves.len().is_power_of_two() && leaves.len() <= KEYS);
    let first = index << LAYER_HEIGHT;
    let mut levels: Vec<Vec<Digest>> = vec![leaves];
    for level in 1..=LAYER_HEIGHT {
        let below = &mut levels[level - 1];
        if below.len() == 1 {
            below.push(surrogate(pp, layer, level - 1, first >> (level - 1) | 1));
        }
        let up = below.as_chunks().0.iter().zip(first >> level..);
        let up = up
            .map(|(children, j)| node(pp, layer as usize, level, j, children))
            .collect();
        levels.push(up);
    }
    levels
}

/// This function follows `LayerTree::path` of [`tree.rs`].
///
/// [`tree.rs`]: https://github.com/leanEthereum/leanVM/blob/f95bc21a4875e10a733f4b2e56f1d4adb81536eb/crates/lean_xmss/src/tree.rs
pub fn path(levels: &[Vec<Digest>], k: usize) -> Vec<u8> {
    (0..LAYER_HEIGHT)
        .flat_map(|level| levels[level][(k >> level) ^ 1])
        .collect()
}

/// This function follows `wots_sign` of [`wots.rs`].
///
/// [`wots.rs`]: https://github.com/leanEthereum/leanVM/blob/f95bc21a4875e10a733f4b2e56f1d4adb81536eb/crates/lean_xmss/src/wots.rs
pub async fn wots_sign(
    pp: &Digest,
    secret: &[u8],
    layer: Layer,
    e: u32,
    message: &[u8],
    reveal: impl AsyncFnOnce(&[usize; V]) -> Result<Vec<Digest>, String>,
) -> Result<Vec<u8>, String> {
    let layer = layer as usize;
    let base = {
        let mut hasher = hasher(pp, &tweak(TWEAK_RANDOMIZER, layer_hi(layer, 0), e));
        hasher.update(secret).update(message);
        u128::from_le_bytes(hasher.finalize()[..RANDOMIZER_LEN].try_into().unwrap())
    };
    let address = address(&tweak(TWEAK_MSG, layer_hi(layer, 0), e));
    let input = [pp.as_slice(), &address, message, &[0; RANDOMIZER_LEN]].concat();
    let randomizer = base
        .wrapping_add(u128::from(least_trial(&input, base).ok_or_else(no_codeword)?))
        .to_le_bytes();
    let x = codeword(&message_digest(pp, layer, e, &randomizer, message)).ok_or_else(no_codeword)?;
    let values = reveal(&x.map(usize::from)).await?;
    Ok([randomizer.to_vec(), values.concat()].concat())
}

fn no_codeword() -> String {
    "no admissible codeword".to_string()
}

#[cfg(test)]
pub mod tests {
    use keccak256::path_fold;
    use lean_xmss::internals::{TWEAK_LEAF, TWEAK_NODE};

    use crate::wots::*;

    pub fn fold(pp: &Digest, layer: Layer, e: u32, leaf: Digest, path: &[u8]) -> Digest {
        let node = |level, j, children: &_| node(pp, layer as usize, level, j as u32, children);
        path_fold(leaf, e as usize, path.as_chunks().0, |_| {}, node)
    }

    /// The tag blocks of `mpc::tag` rely on this layout of leanVM.
    #[test]
    fn the_last_8_bytes_of_an_address_are_zero_for_each_tweak_kind() {
        let kinds = [
            TWEAK_PRF,
            TWEAK_CHAIN,
            TWEAK_LEAF,
            TWEAK_NODE,
            TWEAK_RANDOMIZER,
            TWEAK_MSG,
        ];
        for (kind, layer, step) in kinds
            .into_iter()
            .flat_map(|kind| [Layer::Bottom, Layer::Top].map(|layer| (kind, layer)))
            .flat_map(|(kind, layer)| (0..8).map(move |step| (kind, layer, step)))
        {
            let address = layer_address(kind, layer, (1 << 23) - 1, u32::MAX, step);
            assert_eq!(address[8..], [0; 8]);
        }
    }

    #[test]
    fn the_paths_of_a_tree_of_the_first_keys_fold_to_its_root_through_the_surrogates() {
        let pp = [5; 16];
        for (layer, index) in [(Layer::Bottom, 3), (Layer::Top, 0)] {
            let first = index << LAYER_HEIGHT;
            for height in [0, 1, 4, LAYER_HEIGHT] {
                let leaves: Vec<Digest> = (0..1u32 << height).map(|k| [k as u8; 16]).collect();
                let levels = levels(&pp, layer, index, leaves.clone());
                for (level, nodes) in levels[..LAYER_HEIGHT].iter().enumerate() {
                    assert_eq!(nodes.len(), (leaves.len() >> level).max(2));
                    if level >= height {
                        assert_eq!(nodes[1], surrogate(&pp, layer, level, first >> level | 1));
                    }
                }
                // Each leaf of a small tree, and 16 leaves of the full tree.
                for k in (0..leaves.len()).step_by((leaves.len() / 16).max(1)) {
                    let root = fold(&pp, layer, first | k as u32, leaves[k], &path(&levels, k));
                    assert_eq!(vec![root], levels[LAYER_HEIGHT]);
                }
            }
        }
    }

    #[tokio::test]
    async fn signed_layer_leads_to_the_root_of_its_path() {
        let pp = [5; 16];
        let reveal = |i: usize, p: usize| chain(&pp, 0, 9, i, 0, p, [i as u8; 16]);
        let ends: [Digest; V] = from_fn(|i| reveal(i, CHAIN_LEN - 1));
        let path: Vec<u8> = (0..LAYER_HEIGHT * 16).map(|b| b as u8).collect();
        let reveal_all = async |digits: &[usize; V]| Ok((0..V).map(|i| reveal(i, digits[i])).collect());
        let signature = wots_sign(&pp, &[7; 16], Layer::Bottom, 9, &[3; 32], reveal_all)
            .await
            .unwrap();
        let leaf = wots_leaf_hash(&pp, 0, 9, &ends);
        let signature = [signature, path.clone()].concat();
        assert_eq!(
            layer_root(&pp, Layer::Bottom, 9, &[3; 32], &signature),
            Some(fold(&pp, Layer::Bottom, 9, leaf, &path))
        );
    }
}
