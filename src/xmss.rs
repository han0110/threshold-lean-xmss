//! This module implements the leanXMSS signature of [EIP-8450](https://eips.ethereum.org/EIPS/eip-8450), from leanVM [`signatures::lean_xmss`](https://github.com/leanEthereum/leanVM/tree/f5f3672f2b72d3f89dbbaeff18a53a73c975d620/crates/signatures/src/lean_xmss).
//!
//! - `pp` is the public parameter `P`, and `e` is the index of a one-time key in its layer.
//! - `Layer::Bottom` signs messages and `Layer::Top` signs the roots of the bottom trees. Their
//!   discriminants are the leanVM layer indices.
//! - The randomizer search of `wots_sign` takes an opened value of the threshold PRF in place of
//!   the seed.
//!   - A quorum opens it for the bottom layer, and the MPC opens it for the top layer.

use std::array::from_fn;

pub use signatures::lean_xmss::{
    CHAIN_LEN, Digest, LAYER_HEIGHT, TWEAK_CHAIN, V, address, chain, layer_hi, layer_index, tweak,
};
use signatures::lean_xmss::{
    LeafIndex, LeanXmssPublicKey, LeanXmssSignature, SIG_SIZE, TWEAK_MSG, codeword, hasher,
    message_digest, th,
};
use tracing::info_span;

use crate::lean_xmss::{MAX_RANDOMIZER_TRIALS, node, th_digests};
pub(crate) use crate::lean_xmss::{TWEAK_PRF, TWEAK_RANDOMIZER, wots_leaf_hash};
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

pub fn layer_root(
    pp: &Digest,
    layer: Layer,
    e: u32,
    message: &[u8],
    signature: &[u8],
) -> Option<Digest> {
    // leanVM builds a `LayerSignature` only from the bytes of a full signature, so the layer
    // signature takes the place of the bottom layer in a zero signature.
    let mut bytes = [0; SIG_SIZE];
    bytes[size_of::<LeafIndex>()..][..LAYER_SIG_SIZE].copy_from_slice(signature);
    let signature = LeanXmssSignature::from_bytes(&bytes);
    signatures::lean_xmss::layer_root(pp, layer as usize, e, message, signature.__bottom(), |_| {})
        .map(|(_, root)| root)
}

pub fn verify(public_key: &[u8], message: &[u8], signature: &[u8]) -> bool {
    let (Ok(public_key), Ok(message), Ok(signature)) = (
        public_key.try_into(),
        message.try_into(),
        signature.try_into(),
    ) else {
        return false;
    };
    let (public_key, signature) = (
        LeanXmssPublicKey::from_bytes(public_key),
        LeanXmssSignature::from_bytes(signature),
    );
    signatures::lean_xmss::verify(&public_key, message, &signature).is_ok()
}

pub fn levels(pp: &Digest, layer: Layer, tree: u32, leaves: Vec<Digest>) -> Vec<Vec<Digest>> {
    let mut levels = vec![leaves];
    for level in 1..=LAYER_HEIGHT {
        let below = &levels[level - 1];
        let above = (0..below.len() / 2)
            .map(|k| {
                // A node address holds its index in the whole layer, so the index includes the tree
                // number.
                let j = (tree << (LAYER_HEIGHT - level)) + k as u32;
                node(
                    pp,
                    layer as usize,
                    level,
                    j,
                    &[below[2 * k], below[2 * k + 1]],
                )
            })
            .collect();
        levels.push(above);
    }
    levels
}

pub fn path(levels: &[Vec<Digest>], e: usize) -> Vec<u8> {
    (0..LAYER_HEIGHT)
        .flat_map(|level| levels[level][(e >> level) ^ 1])
        .collect()
}

// Adapted from `wots_sign` in https://github.com/leanEthereum/leanVM/blob/1acdff19dffcaaf1642e88a9e9b522b415425168/crates/signatures/src/lean_xmss/wots.rs
/// Randomizer trials searched per parallel dispatch: the first hit is expected
/// after about `2^20`, and a batch has to be small for the search to stop near it.
const GRIND_BATCH: u64 = 1 << 14;

fn grind(pp: &Digest, layer: usize, e: u32, message: &[u8], base: u128) -> (Digest, [u8; V]) {
    let trial = |c: u64| base.wrapping_add(u128::from(c)).to_le_bytes();
    let mut prefix = hasher(pp, &tweak(TWEAK_MSG, layer_hi(layer, 0), e));
    prefix.update(message);
    let admits = |c: u64| {
        let digest = prefix.clone().update(&trial(c)).finalize();
        codeword(&digest[..16].try_into().unwrap()).is_some()
    };
    let c = (0..MAX_RANDOMIZER_TRIALS)
        .step_by(GRIND_BATCH as usize)
        .find_map(|start| {
            parallel::find_first(GRIND_BATCH as usize, |i| admits(start + i as u64))
                .map(|i| start + i as u64)
        })
        .expect("no randomizer trial gives a codeword");
    let randomizer = trial(c);
    (
        randomizer,
        codeword(&message_digest(pp, layer, e, &randomizer, message)).unwrap(),
    )
}

pub async fn wots_sign(
    pp: &Digest,
    layer: Layer,
    e: u32,
    message: &[u8],
    secret: &[u8],
    reveal: impl AsyncFnOnce(&[usize; V]) -> Result<Vec<Digest>, String>,
) -> Result<Vec<u8>, String> {
    let randomizer = tweak(TWEAK_RANDOMIZER, layer_hi(layer as usize, 0), e);
    let base = u128::from_le_bytes(th(pp, &randomizer, &[secret, message].concat()));
    let (randomizer, digits) =
        info_span!("grind").in_scope(|| grind(pp, layer as usize, e, message, base));
    Ok([
        randomizer.to_vec(),
        reveal(&digits.map(usize::from)).await?.concat(),
    ]
    .concat())
}

#[cfg(test)]
pub mod tests {
    use signatures::lean_xmss::{TWEAK_LEAF, TWEAK_NODE};

    use crate::xmss::*;

    pub fn fold(pp: &Digest, layer: Layer, e: u32, leaf: Digest, path: &[u8]) -> Digest {
        (0..LAYER_HEIGHT).fold(leaf, |current, level| {
            let sibling: Digest = path[16 * level..16 * level + 16].try_into().unwrap();
            let children = if e >> level & 1 == 0 {
                [current, sibling]
            } else {
                [sibling, current]
            };
            node(pp, layer as usize, level + 1, e >> (level + 1), &children)
        })
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

    #[tokio::test]
    async fn signed_layer_leads_to_the_root_of_its_path() {
        let pp = [5; 16];
        let reveal = |i: usize, p: usize| chain(&pp, 0, 9, i, 0, p, [i as u8; 16]);
        let ends: [Digest; V] = from_fn(|i| reveal(i, CHAIN_LEN - 1));
        let path: Vec<u8> = (0..LAYER_HEIGHT * 16).map(|b| b as u8).collect();
        let reveal_all =
            async |digits: &[usize; V]| Ok((0..V).map(|i| reveal(i, digits[i])).collect());
        let signature = wots_sign(&pp, Layer::Bottom, 9, &[3; 32], &[7; 16], reveal_all)
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
