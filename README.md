# Threshold leanXMSS

> [!WARNING]
> This is an experimental proof of concept. It has no security audit and no complete security proof. Please do not use it.

This repository implements threshold t-of-(2t-1) leanXMSS (EIP-8450) base on the [leanXMSS note](https://github.com/TomWambsgans/sphincs.art/blob/9a528527d2d0ea41d2b3b322d2548c0828569a6d/leanXMSS.tex).

- Key generation is an honest-majority MPC over the replicated secret sharing of [Cramer, Damgard and Ishai](https://doi.org/10.1007/978-3-540-30576-7_19).
- The batch check of [Goyal and Song](https://eprint.iacr.org/2020/134) makes the MPC secure against malicious operators, with abort.
- Signing uses the threshold PRF of [PRAWNS](https://eprint.iacr.org/2026/2142) and needs no MPC.

See [`doc/dkg.md`](doc/dkg.md) for the DKG and [`doc/sign.md`](doc/sign.md) for signing.

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

## Benchmark

A key has a top tree of $2^{16}$ leaves, and each bottom tree has $2^{16}$ more. A leaf is a WOTS key of $58$ chains of length $4$.

### DKG

A ceremony generates one tree in batches of $128$ chains, and many batches run at the same time.

| Group  | Mode      | Concurrency | Wall time for each tree | CPU for each operator and tree | Peak RAM for each operator | Sent by each operator for each tree |
| ------ | --------- | ----------- | ----------------------- | ------------------------------ | -------------------------- | ----------------------------------- |
| 2-of-3 | collector | $64$        | $3.0$ min               | $28$ min                       | $2.9$ GB                   | $52.3$ GB                           |
| 2-of-3 | peer      | $64$        | $2.8$ min               | $27$ min                       | $2.9$ GB                   | $52.3$ GB                           |
| 3-of-5 | collector | $64$        | $11.6$ min              | $71$ min                       | $8.4$ GB                   | $63.3$ GB                           |
| 4-of-7 | collector | $16$        | $90.2$ min              | $400$ min                      | $9.0$ GB                   | $70.0$ GB                           |

The measurement has this setup.

- All operators run on one i9-13900K host with $32$ threads and $62$ GB, over localhost with no added latency.
- Each row runs $4{,}096$ keys, which is $1/16$ of a bottom tree, and scales the result by $16$.
- 4-of-7 runs at concurrency $16$, because $7$ operators at concurrency $64$ need more than the RAM of the host.
- All operators share the host. So with one host for each operator, the CPU column is the better guide.
- A full 2-of-3 bottom tree took $181$ s, sent $52.3$ GB and peaked at $4.0$ GB of RAM.
  - So the time and the bytes scale by $16$.
  - But a full tree needs about $1$ GB more RAM.

The sent bytes are a little above the bandwidth of the AND layers in [`doc/dkg.md`](doc/dkg.md). They also include the check, the opening, the commitments and the message framing.

A batch has a fixed number of rounds, the same for every group.

| Batch            | Mode      | AND layers   | Check | Opening | Total |
| ---------------- | --------- | ------------ | ----- | ------- | ----- |
| Chain batch      | collector | $72 \cdot 2$ | $52$  | $1$     | $197$ |
| Chain batch      | peer      | $72$         | $52$  | $1$     | $125$ |
| Commitment batch | collector | $24 \cdot 2$ | $50$  | $1$     | $99$  |
| Commitment batch | peer      | $24$         | $50$  | $1$     | $75$  |

The key setup before the top tree takes $3$ rounds, and each ceremony starts with $1$ more round.

### Sign

A quorum of $t$ operators signs in $2$ rounds with no MPC, as [`doc/sign.md`](doc/sign.md) specifies.

1. Each signer sends its part of $F(A_{\mathrm{rnd}}(e))$ to the other signers. Then each signer grinds the randomizer and finds the codeword.
2. Each signer sends its part of $F(x_p)$ for each chain with a codeword digit below $3$. Then each signer unmasks the chain values.

A part has $16$ B. Let $k$ be the number of chains with a digit below $3$. Then $23 \le k \le 58$, and $k \approx 37$ on average.

| Round | Bytes from one signer to each other signer | At $k = 37$ | At $k = 58$ |
| ----- | ------------------------------------------ | ----------- | ----------- |
| 1     | $16$                                       | $16$ B      | $16$ B      |
| 2     | $16 k$                                     | $592$ B     | $928$ B     |
| Total | $16 (k + 1)$                               | $608$ B     | $944$ B     |

The signature has $2{,}404$ B.
