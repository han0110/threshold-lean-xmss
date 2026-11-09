# Signing

> [!WARNING]
> This is an experimental proof of concept. It has no security audit and no complete security proof. Please do not use it.

This note gives the signing protocol. It needs no MPC. It uses the threshold PRF of [BBDLN26](https://eprint.iacr.org/2026/2142) and the outputs of the key generation in [`dkg.md`](dkg.md).

## 1. Legend

### 1.1 Symbols

| symbol                                                                   | meaning                                                                      |
| ------------------------------------------------------------------------ | ---------------------------------------------------------------------------- |
| $J$                                                                      | the quorum, a set of $t$ operators that sign together                        |
| $m$                                                                      | the message, 32 bytes                                                        |
| $e$                                                                      | the index of the one-time key that signs, used for one message only          |
| $P$                                                                      | the public parameter                                                         |
| $\mathrm{Th}(P, A, M)$                                                   | the tweakable hash of [Wam26](#references) at address $A$ on input $M$       |
| $x_{l,p} = A_{\mathrm{prf}}(e, l, p)$                                    | the PRF input of position $p$ on chain $l$, for $l < 58$ and $p < 4$         |
| $A_{\mathrm{rnd}}(e, s)$, $A_{\mathrm{msg}}(e)$                          | the addresses of the randomizer, at step $s$, and of the message digest      |
| $A_{\mathrm{rnd}}(e) = A_{\mathrm{rnd}}(e, 0)$                           | the input of the randomizer value                                            |
| $`F(x) = \bigoplus_T H(\mathrm{seed}_T \,\Vert\, x)`$                    | the threshold PRF                                                            |
| $`\mathrm{cpk}_e`$, $c_e$                                                | the public outputs of the key generation for key $e$, see [`dkg.md`](dkg.md) |
| $`f_{l,p}(y) = \mathrm{Th}(P, A_{\mathrm{chain}}(e, p), y \,\Vert\, l)`$ | the chain step from position $p$ to $p + 1$ on chain $l$                     |

### 1.2 Inputs

Every signer knows the public inputs.

- These are $P$, $`\mathrm{cpk}_e`$ and $c_e$.
- They also include the stored top layer signature and the Merkle path of key $e$.

Signer $P_i$ holds two kinds of secret keys, as in the key generation.

- It holds $`\mathrm{seed}_T`$ for each term $T$ with $i \notin T$.
- It holds $K_{ij} = K_{ji}$ for each other operator $j$.

## 2. Gadgets

### 2.1 Eval

#### Syntax

$`\mathsf{Eval}_i(x, m, J) \to y_i`$. Local. It is $\mathsf{Eval}'$ of [BBDLN26](https://eprint.iacr.org/2026/2142), Section 5.1.

#### Protocol

Each term goes to its first holder in $J$.
```math
L_i = \{\, T \in \mathcal T : \min (J \setminus T) = i \,\}
```

The part of $P_i$ adds its terms and one mask for each co-signer.
```math
y_i = \bigoplus_{T \in L_i} H(\mathrm{seed}_T \,\Vert\, x) \ \oplus \bigoplus_{j \in J \setminus \{i\}} H(K_{ij} \,\Vert\, x \,\Vert\, m \,\Vert\, J)
```

#### Correctness

- The sets $L_i$ for $i \in J$ partition $\mathcal T$, because $\lvert J \rvert = t > t - 1 = \lvert T \rvert$.
- $P_i$ holds every term of $L_i$, because $i \in J \setminus T$.

#### Security

With the masks, $\mathsf{Eval}$ and $\mathsf{Combine}$ form a context-aware threshold PRF with the evaluation context $m$ [BBDLN26, Sec. 5.1](https://eprint.iacr.org/2026/2142). It is adaptively secure in the random-oracle model [BBDLN26, Def. 2.2, Thm. 5.1](https://eprint.iacr.org/2026/2142).

So shares of $F(x)$ for two different messages do not combine to $F(x)$.

<details>
<summary>Example 2-of-3</summary>

For $`J = \{0, 1\}`$, the terms are $`\{0\}`$, $`\{1\}`$ and $`\{2\}`$. Let $`M = H(K_{01} \,\Vert\, x \,\Vert\, m \,\Vert\, J)`$.

| signer | $L_i$                | $y_i$                                                                     |
| ------ | -------------------- | ------------------------------------------------------------------------- |
| $P_0$  | $`\{1\}`$, $`\{2\}`$ | $`H(\mathrm{seed}_1 \Vert x) \oplus H(\mathrm{seed}_2 \Vert x) \oplus M`$ |
| $P_1$  | $`\{0\}`$            | $`H(\mathrm{seed}_0 \Vert x) \oplus M`$                                   |

</details>

<details>
<summary>Example 3-of-5</summary>

For $`J = \{0, 1, 2\}`$, the 10 terms split as follows.

| signer | $L_i$                                                    | count |
| ------ | -------------------------------------------------------- | ----- |
| $P_0$  | $`\{1,2\}, \{1,3\}, \{1,4\}, \{2,3\}, \{2,4\}, \{3,4\}`$ | 6     |
| $P_1$  | $`\{0,2\}, \{0,3\}, \{0,4\}`$                            | 3     |
| $P_2$  | $`\{0,1\}`$                                              | 1     |

Each $y_i$ also carries two masks, one for each co-signer.

</details>

### 2.2 Combine

#### Syntax

$`\mathsf{Combine}(\{y_i\}_{i \in J}) \to F(x)`$. Local. It is $\mathsf{Combine}'$ of [BBDLN26](https://eprint.iacr.org/2026/2142), Section 5.1.

#### Protocol

```math
F(x) = \bigoplus_{i \in J} y_i
```

#### Correctness

- Each term appears in exactly one $L_i$, so the terms give $F(x)$.
- Each mask appears twice, in $y_i$ and in $y_j$, because $K_{ij} = K_{ji}$. So the masks cancel.

<details>
<summary>Example 2-of-3</summary>

With the parts above, $`y_0 \oplus y_1 = H(\mathrm{seed}_0 \Vert x) \oplus H(\mathrm{seed}_1 \Vert x) \oplus H(\mathrm{seed}_2 \Vert x) = F(x)`$, because $M \oplus M = 0$.

</details>

## 3. Protocol

The quorum $J$ signs $m$ at key $e$ in 2 rounds. Each signer runs the same steps, and each signer aborts alone.

### 3.1 Round 1, the randomizer value

1. $P_i$ computes $`y_i = \mathsf{Eval}_i(A_{\mathrm{rnd}}(e), m, J)`$ and sends it to each other signer.
2. $P_i$ computes $`\rho_e = \mathsf{Combine}(\{y_j\}_{j \in J})`$, which is $F(A_{\mathrm{rnd}}(e))$.
3. $P_i$ aborts unless $\rho_e$ matches the commitment.
```math
\mathrm{Th}\big( P,\ A_{\mathrm{rnd}}(e, 1),\ \rho_e \,\Vert\, 0 \big) = c_e
```

### 3.2 Grinding, with no message

4. $P_i$ computes the start of the search.
```math
R_0 = \mathrm{Th}\big( P,\ A_{\mathrm{rnd}}(e),\ \rho_e \,\Vert\, m \big)
```
5. $P_i$ takes the first $R$ of $R_0, R_0 + 1, R_0 + 2, \dots$ (mod $2^{128}$) whose digest is a codeword.
```math
d = \mathrm{Th}\big( P,\ A_{\mathrm{msg}}(e),\ m \,\Vert\, R \big)
```
6. The codeword gives the position $p_l < 4$ of each chain $l < 58$. The positions sum to 106.

All signers find the same $R$, because the search is a function of $\rho_e$ and $m$.

### 3.3 Round 2, the chain values

7. For each chain $l$ with $p_l < 3$, $P_i$ computes $`y_{i,l} = \mathsf{Eval}_i(x_{l,p_l}, m, J)`$. It sends all $y_{i,l}$ to each other signer.
8. $P_i$ computes $`F(x_{l,p_l}) = \mathsf{Combine}(\{y_{j,l}\}_{j \in J})`$ and the chain value $\sigma_l$.
```math
\sigma_l = \begin{cases} F(x_{l,0}) & \text{if } p_l = 0, \\ \mathrm{cpk}_e[l, p_l] \oplus F(x_{l,p_l}) & \text{if } p_l \in \{1, 2\}, \\ \mathrm{cpk}_e[l, 3] & \text{if } p_l = 3. \end{cases}
```
9. $P_i$ aborts unless each chain value leads to the chain end.
```math
f_{l,2} \circ \dots \circ f_{l,p_l}(\sigma_l) = \mathrm{cpk}_e[l, 3] \quad \text{for each } l
```

### 3.4 Output

10. The bottom layer signature is $(R, \sigma_0, \dots, \sigma_{57})$ with the Merkle path of key $e$.
11. The signature is $e$, the bottom layer signature and the stored top layer signature. It is a plain leanXMSS signature of 2,404 bytes.

### 3.5 Cost

Let $k$ be the number of chains with $p_l < 3$. Then $23 \le k \le 58$, and $k \approx 37$ on average.

| round | each signer sends to each other signer | bits    |
| ----- | -------------------------------------- | ------- |
| 1     | $y_i$ at $A_{\mathrm{rnd}}(e)$         | $128$   |
| 2     | $y_{i,l}$ for $k$ chains               | $128 k$ |

## 4. Security

The signing targets the unforgeability of a threshold one-time signature, the game of [BBDLN26, Def. 3.2, Fig. 3](https://eprint.iacr.org/2026/2142). No complete proof exists.

The formal claim models $\mathrm{Th}$ as a random oracle and states the bound $q / 2^{127}$ plus the terms of a call on a hidden key or seed. The budget $q$ counts every hash call of every party. The key generation claims keep $\mathrm{Th}$ as one fixed function.

The formal claim replaces the threshold PRF property below by the terms of a call on a hidden key. The reduction of [BBDLN26, Thm. 3.1](https://eprint.iacr.org/2026/2142) uses two properties.

- The threshold PRF is secure [BBDLN26, Def. 2.2](https://eprint.iacr.org/2026/2142). Its replicated construction with masks is secure in the random-oracle model [BBDLN26, Thm. 5.1](https://eprint.iacr.org/2026/2142).
- The one-time signature is secure. Here it is leanXMSS [Wam26](#references), in place of the Winternitz scheme of [BBDLN26, Sec. 3.1](https://eprint.iacr.org/2026/2142).

The game differs from [BBDLN26, Fig. 3](https://eprint.iacr.org/2026/2142) in three points, and each point needs its own argument.

- $\mathsf{Eval}$ and the signing oracle take the quorum $J$, as [BBDLN26, Sec. 4](https://eprint.iacr.org/2026/2142) allows.
- Line 8 of the game requires $t > (n + \lvert D \rvert)/2$, which fails for $n = 2t - 1$, $\lvert D \rvert = t - 1$ and $t \ge 2$.
  - So the game drops line 8.
  - In its place, honest operators sign at most one message for each key, over all quorums and also after an abort, as [Wam26](#references) assumes.
- [BBDLN26, Sec. 3.4](https://eprint.iacr.org/2026/2142) samples the randomizer key by a commit-reveal in the quorum. Here $c_e$ from the key generation fixes the randomizer value $F(A_{\mathrm{rnd}}(e))$.

So signing the same $m$ again at key $e$ gives the same signature, and signing another message at $e$ breaks the one-time rule.

A production implementation must enforce this one-message rule.

The signing claim covers adaptive corruptions [BBDLN26, Def. 3.2](https://eprint.iacr.org/2026/2142) of at most $t - 1$ operators over the lifetime of the key. It is separate from the key generation claims of [`dkg.md`, Section 3.3](dkg.md#33-security). The adversary gets every public output of the key generation.

## References

| key                                                                                                             | reference                                                                                                                                                                                    |
| --------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [BBDLN26](https://eprint.iacr.org/2026/2142)                                                                    | D. Boneh, B. Bünz, J. D., Y. Litchev, K. Nazirkhanova. PRAWNS: Threshold Hash-Based Signatures from Threshold PRFs. [ePrint 2026/2142](https://eprint.iacr.org/2026/2142)                    |
| [Wam26](https://github.com/TomWambsgans/sphincs.art/blob/9a528527d2d0ea41d2b3b322d2548c0828569a6d/leanXMSS.tex) | T. Wambsgans. leanXMSS candidate. [github.com/TomWambsgans/sphincs.art/leanXMSS.tex](https://github.com/TomWambsgans/sphincs.art/blob/9a528527d2d0ea41d2b3b322d2548c0828569a6d/leanXMSS.tex) |
