# Threshold leanXMSS

> [!WARNING]
> This is an experimental proof of concept. It has no security audit and no complete security proof. Please do not use it.

This repository implements threshold t-of-(2t-1) leanXMSS (EIP-8450) base on the [leanXMSS note](https://github.com/TomWambsgans/sphincs.art/blob/9a528527d2d0ea41d2b3b322d2548c0828569a6d/leanXMSS.tex).

- Key generation is an honest-majority MPC over the replicated secret sharing of [Cramer, Damgard and Ishai](https://doi.org/10.1007/978-3-540-30576-7_19).
- The batch check of [Goyal and Song](https://eprint.iacr.org/2020/134) is the defense of the MPC against malicious operators, with abort.
- Signing uses the threshold PRF of [PRAWNS](https://eprint.iacr.org/2026/2142) and needs no MPC.

See [`doc/dkg.md`](doc/dkg.md) for the DKG and [`doc/sign.md`](doc/sign.md) for signing.

## Cluster

The table compares threshold BLS with threshold leanXMSS for some $t$-of-$n$ clusters. Each cell is the number of faulty operators that the cluster tolerates.

Both schemes run QBFT before each signature, and an honest operator signs only the message that QBFT decides. QBFT tolerates $f = \lfloor (n-1)/3 \rfloor$ Byzantine operators with the quorum $q = \lfloor (n+f)/2 \rfloor + 1$. Each cluster of the table has $t \le q$.

- Unforgeability is against a static coalition of corrupt operators.
- Safety is against Byzantine operators. No two messages get a signature for one slot.
- Liveness is against offline operators. The other operators continue to sign.

| Cluster | Unforgeability <br> (BLS) | Unforgeability <br> (leanXMSS + dealer) | Unforgeability <br> (leanXMSS + DKG) | Safety | Liveness |
| ------- | ------------------------- | --------------------------------------- | ------------------------------------ | ------ | -------- |
| 2-of-3  | $1$                       | $1$                                     | $1$                                  | $0$    | $1$      |
| 3-of-4  | $2$                       | $2$                                     | $\textcolor{red}{1}$                 | $1$    | $1$      |
| 3-of-5  | $2$                       | $2$                                     | $2$                                  | $1$    | $1$      |
| 4-of-7  | $3$                       | $3$                                     | $3$                                  | $2$    | $2$      |
| 5-of-7  | $4$                       | $4$                                     | $\textcolor{red}{3}$                 | $2$    | $2$      |
| 5-of-9  | $4$                       | $4$                                     | $4$                                  | $2$    | $3$      |

The DKG of leanXMSS is an MPC with only symmetric primitives. Such an MPC keeps its secrets against fewer than $n/2$ corrupt operators. It computes the one-time keys of each tree, so its limit is also the limit of the unforgeability. The rows for 3-of-4 and 5-of-7 assume a DKG with an MPC at that limit.

A trusted dealer computes the trees in the clear, so the limit of the MPC does not apply.

| Property                           | Faulty operators that the cluster tolerates |
| ---------------------------------- | ------------------------------------------- |
| Unforgeability (BLS)               | $t - 1$                                     |
| Unforgeability (leanXMSS + dealer) | $t - 1$                                     |
| Unforgeability (leanXMSS + DKG)    | $\min(t - 1, \lfloor (n-1)/2 \rfloor)$      |
| Safety                             | $f$                                         |
| Liveness                           | $n - q$                                     |

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

Each key ceremony ends with a vote, and an operator keeps the result only if all operators vote for it. The vote assumes a broadcast channel, as [`doc/dkg.md`](doc/dkg.md) 3.3 describes. The Lean model has the same vote.

`--time-limit` sets the seconds after which an operator that is still in a ceremony votes for its abort. The default is 24 hours. The delay of the network adds about $\lceil N / c \rceil$ times the rounds per batch times the one-way delay to a tree, for $N = \lceil 2^{16} \cdot 58 / B \rceil$ chain batches of the batch size $B$ and the concurrency $c$. Add the time of the computation, which the benchmark gives. Set a larger limit if the sum comes near the limit.

Generate the key and its top tree, which prints the public key.

```sh
target/release/threshold-lean-xmss dkg --admin 127.0.0.1:48360 --top
```

Generate bottom tree 0, which holds the first 65536 signing leaves.

```sh
target/release/threshold-lean-xmss dkg --admin 127.0.0.1:48360 --bottom 0
```

Sign a 32-byte message at a leaf, which prints the signature. Each operator records the one message that it acknowledges at a leaf, so a sign command with another message at a used leaf fails.

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

`--leaves` on a `dkg` command generates only the first keys of the tree. The count is a power of two. A public surrogate node takes the place of each part of the tree with no keys. With a count below 65536, the ceremony runs fewer chains.

As another start with new key folders, the next commands generate a key with $2^{12}$ top keys and then bottom tree 0 with one key, for a first signature at leaf 0.

```sh
target/release/threshold-lean-xmss dkg --admin 127.0.0.1:48360 --top --leaves 4096
target/release/threshold-lean-xmss dkg --admin 127.0.0.1:48360 --bottom 0 --leaves 1
```

Once an operator records the count of a bottom tree, it refuses another count for that tree. An operator refuses a sign command at a leaf with no key. A tree with fewer keys is outside the formal claims, as [`doc/dkg.md`](doc/dkg.md) 3.3 describes.

The admin command and all operators must run the same version of the binary, because the announcement of a key ceremony holds the count. A version before this option refuses the seeds of this version, because it keeps no count.

## Benchmark

A key has a top tree of $2^{16}$ leaves, and each bottom tree has $2^{16}$ more. A leaf is a WOTS key of $58$ chains of length $4$.

### DKG

The following table gives the traffic that each operator sends for one bottom tree. The average rate is over the $2^{16}$ epochs of $384$ s.

| Group  | Mode      | Rounds per batch | Sent per operator | Average rate |
| ------ | --------- | ---------------- | ----------------- | ------------ |
| 2-of-3 | peer      | $126$            | $52.5$ GB         | $2.09$ KB/s  |
| 3-of-5 | collector | $198$            | $63.7$ GB         | $2.53$ KB/s  |
| 4-of-7 | collector | $198$            | $70.7$ GB         | $2.81$ KB/s  |
| 5-of-9 | collector | $198$            | $81.4$ GB         | $3.24$ KB/s  |

The following table gives the wall time of one bottom tree and its bottleneck (C for computation, L for latency, B for bandwidth). Each operator runs on one c4-highmem-8 machine with $8$ vCPUs and $32$ GiB.

| Profile  |      RTT |     Upload |        2-of-3 |        3-of-5 |        4-of-7 | 5-of-9 (estimate) |
| -------- | -------: | ---------: | ------------: | ------------: | ------------: | ----------------: |
| P1       |   $1$ ms |   no limit | $2.5$ min / C | $6.0$ min / C |  $22$ min / C |     $129$ min / C |
| P140     | $140$ ms |   $1$ Gbps | $8.9$ min / B |  $13$ min / B |  $31$ min / L |     $226$ min / C |
| P235     | $235$ ms |   $1$ Gbps |  $10$ min / B |  $15$ min / L |  $45$ min / L |     $284$ min / L |
| P140-100 | $140$ ms | $100$ Mbps |  $75$ min / B |  $92$ min / B | $104$ min / B |     $242$ min / C |

- The RTT of $140$ ms is the average latency of a cluster in the [report of Lido and Obol](https://obol.org/lido_obol_2.pdf).
- The RTT of $235$ ms is the recommended latency inside a cluster in the [Simple DVT test of Lido](https://blog.obol.org/lido-simple-dvt-wave-1-testing-complete).
- More RAM with more batches in flight hides the latency.
- More cores make the compute faster.
- The bandwidth stays the floor. With the bandwidth as the bottleneck, the DKG time is about the traffic divided by the upload rate.
- The column for 5-of-9 is an estimate from the measured groups, with no run. It is the worst case, the compute time plus the max of bandwidth and latency time.

### Sign

A quorum of $t$ operators signs in $2$ rounds with no MPC, as [`doc/sign.md`](doc/sign.md) specifies. Before the two rounds, all operators agree on the leaf and the message. The note assumes this agreement by consensus. The proof of concept does it with one exchange of acknowledgements, which is step 0.

0. Each operator acknowledges the leaf and the message and sends its acknowledgement to all $n$ operators. A signer continues only when $Q = \lfloor (n + t - 1)/2 \rfloor + 1$ operators acknowledge the same leaf and message. A refusing operator sends an empty acknowledgement, so the round tolerates $n - Q$ refusals. One silent operator stops it.
1. Each signer sends its part of $F(A_{\mathrm{rnd}}(e))$ to the other signers. Then each signer grinds the randomizer and finds the codeword.
2. Each signer sends its part of $F(x_p)$ for each chain with a codeword digit below $3$. Then each signer unmasks the chain values.

A part has $16$ B. Let $k$ be the number of chains with a digit below $3$. Then $23 \le k \le 58$, and $k \approx 37$ on average.

| Round          | Bytes from one signer to each other signer     | At $k = 37$ | At $k = 58$ |
| -------------- | ---------------------------------------------- | ----------- | ----------- |
| Agreement      | $36$, also to the operators outside the quorum | $36$ B      | $36$ B      |
| 1              | $16$                                           | $16$ B      | $16$ B      |
| 2              | $16 k$                                         | $592$ B     | $928$ B     |
| Rounds 1 and 2 | $16 (k + 1)$                                   | $608$ B     | $944$ B     |

The signature has $2{,}404$ B.
