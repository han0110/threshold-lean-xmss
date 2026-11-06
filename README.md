# Threshold leanXMSS

> [!WARNING]
> This is an experimental proof of concept. It has no security audit and no complete security proof. Please do not use it.

This repository implements threshold t-of-(2t-1) leanXMSS (EIP-8450) base on the [leanXMSS note](https://github.com/TomWambsgans/sphincs.art/blob/9a528527d2d0ea41d2b3b322d2548c0828569a6d/leanXMSS.tex).

- Key generation is an honest-majority MPC over the replicated secret sharing of [Cramer, Damgard and Ishai](https://doi.org/10.1007/978-3-540-30576-7_19).
- The batch check of [Goyal and Song](https://eprint.iacr.org/2020/134) makes the MPC secure against malicious operators, with abort.
- Signing uses the threshold PRF of [PRAWNS](https://eprint.iacr.org/2026/2142) and needs no MPC.

## Usage

Build the binary.

```sh
cargo build --release
```

Start each operator in its own terminal. An operator with `--admin` accepts admin commands after it connects to all peers.

```sh
target/release/threshold-lean-xmss serve --addr 127.0.0.1:47360 --peers 127.0.0.1:47361 --peers 127.0.0.1:47362 --sk keys/p0 --admin 127.0.0.1:48360
target/release/threshold-lean-xmss serve --addr 127.0.0.1:47361 --peers 127.0.0.1:47360 --peers 127.0.0.1:47362 --sk keys/p1
target/release/threshold-lean-xmss serve --addr 127.0.0.1:47362 --peers 127.0.0.1:47360 --peers 127.0.0.1:47361 --sk keys/p2
```

With `--reshare peer` on every `serve` command, each AND layer takes 1 round in place of 2. The check is the same in both modes, and operators with different values abort.

With the same `--batch-size` on every `serve` command, each batch of a tree holds at most that number of chains or keys. Operators with different values abort. `--concurrency` sets the batches that one operator runs at the same time.

Generate the key and its top tree, which prints the public key.

```sh
target/release/threshold-lean-xmss dkg --admin 127.0.0.1:48360 --top
```

Generate bottom tree 0, which holds the first 65536 signing leaves.

```sh
target/release/threshold-lean-xmss dkg --admin 127.0.0.1:48360 --bottom 0
```

Sign a 32-byte message at a leaf, which prints the signature. Use each leaf for only one sign command, also after a failure. The operators do not record the used leaves.

```sh
target/release/threshold-lean-xmss sign --admin 127.0.0.1:48360 --leaf 0 --msg 030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dc
```

Verify the signature.

```sh
target/release/threshold-lean-xmss verify --pk <pk> --msg 030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dc --sig <sig>
```

Generate another bottom tree when the leaves of the existing trees are used.

```sh
target/release/threshold-lean-xmss dkg --admin 127.0.0.1:48360 --bottom 1
```
