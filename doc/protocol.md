# Protocol

> [!WARNING]
> This is an experimental proof of concept. It has no security audit and no complete security proof. Please do not use it.

In this note we give the MPC gadgets we used in the protocol, and give a toy example for understanding.

## 1. Gadgets

### 1.1 Legend

#### 1.1.1 Parties and field

| symbol                                                        | meaning                                                                                                    |
| ------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------- |
| $n = 2t - 1$                                                  | operators $P_0, \dots, P_{n-1}$                                                                            |
| $t - 1$                                                       | corrupt operators at most, malicious, security with abort                                                  |
| $\mathbb F_2$                                                 | the field of the circuit                                                                                   |
| $\mathbb F_{192}$                                             | the field of the check                                                                                     |
| $\mathbb F$                                                   | either of the two, in a gadget that works over both. Both have characteristic 2, so $+$ is XOR and $- = +$ |
| $\mathrm{GF}(2^8) = \mathbb F_2[x]/(x^8 + x^4 + x^3 + x + 1)$ | the field of the examples, elements written as integers ($x = 2$, $2^{-1} = 141$, $3^{-1} = 246$)          |
| $\alpha_i = i + 1$                                            | the evaluation point of $P_i$                                                                              |
| $H$                                                           | a collision-resistant hash                                                                                 |

Examples use $t = 2$, $n = 3$.

#### 1.1.2 Terms and sharings

| symbol                                                                     | definition                                                                                              |
| -------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------- |
| $\mathcal T = \{T \subseteq \{0, \dots, n-1\} : \lvert T \rvert = t - 1\}$ | the terms                                                                                               |
| $\mathrm{holders}(T) = \{i : i \notin T\}$                                 | the $t$ operators holding $T$                                                                           |
| $[\![ v ]\!]$                                                              | replicated: $v = c + \sum_{T \in \mathcal T} v_T$, public part $c$, $v_T$ held by $\mathrm{holders}(T)$ |
| $\langle v \rangle$                                                        | Shamir: $P_i$ holds $v_i = V(\alpha_i)$, $\deg V \le t - 1$, $V(0) = v$                                 |
| $\{v\}$                                                                    | additive: $P_i$ holds $v_i$, $v = \sum_i v_i$                                                           |
| $[\![ A ]\!]$                                                              | a vector, shared elementwise                                                                            |

- A coalition of $t - 1$ operators lacks exactly one term, the term equal to itself.
- $[\![ \cdot ]\!]$ is the sharing of every wire. $\langle \cdot \rangle$ needs $n$ distinct points, so it exists over $\mathbb F_{192}$ only and is used in the check only. $\{\cdot\}$ is the output of a multiplication and is reshared in the next round.
- For 2-of-3, a term is one operator, written $k$ for $\{k\}$, held by the two operators other than $P_k$.

#### 1.1.3 Public constants of a group $(n, t)$

| constant                                                           | definition                                                                                                                                                                |
| ------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| $\mathrm{pairs}_i \subseteq \mathcal T \times \mathcal T$          | a balanced partition of all pairs of terms, pair $(A, B)$ given to an operator holding both ($\lvert A \cup B \rvert \le 2t - 2 < n$)                                     |
| $T_i$                                                              | the term lacking $i + 1, \dots, i + t - 1 \pmod n$, filled by $P_i$ in a reshare                                                                                          |
| $\mathcal C = \{T_0, \dots, T_{n-1}\}$                             | the filled terms                                                                                                                                                          |
| $\mathrm{owner}(T) \in \mathrm{holders}(T)$                        | a balanced choice of one holder per term                                                                                                                                  |
| $\psi_T(X) = \prod_{j \in T} \frac{X + \alpha_j}{\alpha_j}$        | the polynomial of term $T$ ($f_A$ in [CDI05](https://doi.org/10.1007/978-3-540-30576-7_19)): $\deg \psi_T = t - 1$, $\psi_T(0) = 1$, $\psi_T(\alpha_j) = 0$ for $j \in T$ |
| $\lambda_i = \prod_{j \ne i} \frac{\alpha_j}{\alpha_j + \alpha_i}$ | the Lagrange weight of $\alpha_i$ at $0$ among all $n$ points                                                                                                             |

For 2-of-3: $\alpha = (1, 2, 3)$, $\lambda = (1, 1, 1)$, $(T_0, T_1, T_2) = (1, 2, 0)$, $\mathrm{owner}(0, 1, 2) = (P_1, P_2, P_0)$.

| term $k$ | holders    | $\psi_k(X)$ | $\psi_k(\alpha_0)$ | $\psi_k(\alpha_1)$ | $\psi_k(\alpha_2)$ | $\mathrm{pairs}_k$        |
| -------- | ---------- | ----------- | ------------------ | ------------------ | ------------------ | ------------------------- |
| 0        | $P_1, P_2$ | $1 + X$     | not held           | 3                  | 2                  | $\{(1,2), (2,1), (2,2)\}$ |
| 1        | $P_0, P_2$ | $1 + 141X$  | 140                | not held           | 141                | $\{(0,0), (0,2), (2,0)\}$ |
| 2        | $P_0, P_1$ | $1 + 246X$  | 247                | 246                | not held           | $\{(0,1), (1,0), (1,1)\}$ |

#### 1.1.4 Keys and pseudorandom streams

| symbol                                           | definition                                                                                                                       |
| ------------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------------- |
| $\mathrm{seed}_T$                                | a key known to $\mathrm{holders}(T)$                                                                                             |
| $K_{ij} = K_{ji}$                                | a key known to $P_i$ and $P_j$                                                                                                   |
| $\mathsf{PRG}(\mathrm{key}, \rho, \mathrm{idx})$ | a pseudorandom stream for round $\rho$, used once. $\mathrm{idx} = 0$ reshare masks, $1$ coins and final masks, $2$ digest salts |

#### 1.1.5 Gadget table

| gadget                    | input $\to$ output                                            | rounds                  | messages                                                       | section |
| ------------------------- | ------------------------------------------------------------- | ----------------------- | -------------------------------------------------------------- | ------- |
| $\mathsf{Rand}$           | $\to [\![ r ]\!]$                                             | 0                       | none                                                           | 1.2     |
| $\mathsf{MulRep}$         | $[\![ x ]\!], [\![ y ]\!] \to \{xy\}$                         | 0                       | none                                                           | 1.3     |
| $\mathsf{MulSh}$          | $\langle x \rangle, \langle y \rangle \to \{xy\}$             | 0                       | none                                                           | 1.4     |
| $\mathsf{Conv}$           | $[\![ v ]\!] \to \langle v \rangle$                           | 0                       | none                                                           | 1.5     |
| $\mathsf{Reshare}$        | $\{v\} \to [\![ v ]\!]$                                       | 1 (2 in collector mode) | $n(t-1)$                                                       | 1.6     |
| $\mathsf{OpenRep}$        | $[\![ v ]\!] \to v$                                           | 1                       | $n\binom{n-1}{t-2}$ copies and $n(t-1)\binom{n-1}{t-2}$ hashes | 1.7     |
| $\mathsf{OpenSh}$         | $\langle v \rangle \to v$                                     | 1                       | $n(n-1)$                                                       | 1.8     |
| $\mathsf{Coin}$ (derived) | $\to r$ public                                                | 1                       | as $\mathsf{OpenSh}$                                           | 1.9     |

Composition rule: a product is $\{\cdot\}$, and $\{\cdot\}$ is reshared to $[\![ \cdot ]\!]$ in the next round.

#### 1.1.6 Notation against the literature

[GS20](https://eprint.iacr.org/2020/134) counts $t$ corrupt among $n = 2t + 1$. Here $t$ is the quorum size, so a sharing $[x]_t$ of [GS20](https://eprint.iacr.org/2020/134) has degree $t - 1$ here.

| here                                                                              | literature                                                                                                                                                        |
| --------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| $\langle x \rangle$, degree $t - 1$                                               | $[x]_t$ in [GS20](https://eprint.iacr.org/2020/134)                                                                                                               |
| $[\![ x ]\!]$                                                                     | replicated sharing of [CDI05](https://doi.org/10.1007/978-3-540-30576-7_19), [AFL+16](https://eprint.iacr.org/2016/768), [MR18](https://eprint.iacr.org/2018/403) |
| $\psi_T$                                                                          | $f_A$ in [CDI05](https://doi.org/10.1007/978-3-540-30576-7_19), $A = T$ a maximal unqualified set                                                                 |
| $\lambda_i$                                                                       | Lagrange coefficients at $0$ from all $n$ shares                                                                                                                  |
| $(\langle A \rangle, \langle B \rangle, \langle C \rangle)$, $C = \sum_e A_e B_e$ | the inner-product tuple $([\boldsymbol x]_t, [\boldsymbol y]_t, [z]_t)$ of [GS20, §4](https://eprint.iacr.org/2020/134)                                           |
| halving, $r$                                                                      | compression of [GS20](https://eprint.iacr.org/2020/134) with $k = 2$, challenge $r$                                                                               |
| $\mathsf{Coin}$                                                                   | $\mathcal F_{\mathrm{coin}}$ of [GS20](https://eprint.iacr.org/2020/134)                                                                                          |

### 1.2 Rand

#### Syntax

$\mathsf{Rand}(\rho, \mathrm{idx}) \to [\![ r ]\!]$. Local.

#### Protocol

Each holder of $T$ sets
$$r_T = \mathsf{PRG}(\mathrm{seed}_T, \rho, \mathrm{idx}).$$

#### Correctness

The holders of $T$ share $\mathrm{seed}_T$.

#### Privacy

A coalition lacks one seed, so one term of $r$ is pseudorandom to it.

<details>
<summary>Example</summary>

| term | computed by | $r_T$ |
| ---- | ----------- | ----- |
| 0    | $P_1, P_2$  | 4     |
| 1    | $P_0, P_2$  | 5     |
| 2    | $P_0, P_1$  | 6     |

$r = 4 + 5 + 6 = 7$, known to nobody.

</details>

### 1.3 MulRep

#### Syntax

$\mathsf{MulRep}([\![ x ]\!], [\![ y ]\!]) \to \{xy\}$. Local. On vectors, the additive share of $\sum_e x_e y_e$.

#### Protocol

$$(xy)_i = \sum_{(A,B) \in \mathrm{pairs}_i} x_A\, y_B .$$

#### Correctness

$xy = \sum_{A, B} x_A y_B$ and the pairs partition all $(A, B)$.

#### Privacy

No message.

#### Use

Over $\mathbb F_2$: the AND gate and the slice table of the check.

<details>
<summary>Example</summary>

$[\![ a ]\!] = (1, 1, 1)$, $[\![ b ]\!] = (0, 1, 0)$, $a = b = 1$.

| operator | $\sum_{\mathrm{pairs}_i} a_A b_B$         | share |
| -------- | ----------------------------------------- | ----- |
| $P_0$    | $a_1 b_2 + a_2 b_1 + a_2 b_2 = 0 + 1 + 0$ | 1     |
| $P_1$    | $a_0 b_0 + a_0 b_2 + a_2 b_0 = 0 + 0 + 0$ | 0     |
| $P_2$    | $a_0 b_1 + a_1 b_0 + a_1 b_1 = 1 + 0 + 1$ | 0     |

$\{ab\} = (1, 0, 0)$, sum $1 = ab$.

</details>

### 1.4 MulSh

#### Syntax

$\mathsf{MulSh}(\langle x \rangle, \langle y \rangle) \to \{xy\}$. Local. On vectors, the additive share of $\sum_e x_e y_e$.

#### Protocol

$$(xy)_i = \lambda_i\, x_i\, y_i .$$

#### Correctness

$x_i y_i = (XY)(\alpha_i)$ with $\deg XY \le 2t - 2 = n - 1$, so $\sum_i \lambda_i x_i y_i = (XY)(0) = xy$.

#### Privacy

No message.

#### Use

The vector phase of the check, one multiplication per element.

<details>
<summary>Example</summary>

$\langle x \rangle = (142, 14, 135)$ with $x = 7$, $\langle y \rangle = (240, 247, 3)$ with $y = 4$, $\lambda = (1, 1, 1)$.

| operator | $\lambda_i x_i y_i$ | share |
| -------- | ------------------- | ----- |
| $P_0$    | $142 \cdot 240$     | 115   |
| $P_1$    | $14 \cdot 247$      | 253   |
| $P_2$    | $135 \cdot 3$       | 146   |

$\{xy\} = (115, 253, 146)$, sum $28 = 7 \cdot 4$.

</details>

### 1.5 Conv

#### Syntax

$\mathsf{Conv}([\![ v ]\!]) \to \langle v \rangle$. Local.

#### Protocol

$$v_i = \sum_{T \not\ni i} \psi_T(\alpha_i)\, v_T .$$

#### Correctness

$V(X) = \sum_T v_T\, \psi_T(X)$ has $\deg V \le t - 1$, $V(0) = v$, and $V(\alpha_i) = v_i$ since $\psi_T(\alpha_i) = 0$ for $T \ni i$.

#### Privacy

No message.

<details>
<summary>Example</summary>

$[\![ v ]\!] = (4, 5, 6)$, $v = 7$, $V(X) = 4(1 + X) + 5(1 + 141X) + 6(1 + 246X) = 7 + 137X$.

| operator | $\sum_{T \not\ni i} \psi_T(\alpha_i)\, v_T$ | $V(\alpha_i)$ |
| -------- | ------------------------------------------- | ------------- |
| $P_0$    | $140 \cdot 5 + 247 \cdot 6 = 138 + 4$       | 142           |
| $P_1$    | $3 \cdot 4 + 246 \cdot 6 = 12 + 2$          | 14            |
| $P_2$    | $2 \cdot 4 + 141 \cdot 5 = 8 + 143$         | 135           |

</details>

### 1.6 Reshare

#### Syntax

$\mathsf{Reshare}(\{v\}) \to [\![ v ]\!]$. One round, $n(t-1)$ messages.

#### Protocol, round $\rho$

1. $[\![ r ]\!] = \mathsf{Rand}(\rho, 0)$, $\zeta_i = \sum_{j \ne i} \mathsf{PRG}(K_{ij}, \rho, 0)$.
2. $P_i$ sends $u_i = v_i + \zeta_i + \sum_{T \notin \mathcal C,\ \mathrm{owner}(T) = i} r_T$ to $\mathrm{holders}(T_i) \setminus \{i\}$.
3. $v_{T_i} = u_i$, and $v_T = r_T$ for $T \notin \mathcal C$. Each holder of $T \in \mathcal C$ appends $v_T$ to its digest $h_T$ (see 1.9).

#### Correctness

$\sum_i \zeta_i = 0$ (each pair stream is added twice), and each $r_T$, $T \notin \mathcal C$, is added twice:
$$\sum_T v_T = \sum_i u_i + \sum_{T \notin \mathcal C} r_T = \sum_i v_i = v .$$

#### Privacy

A coalition $D$ lacks only term $D$.
- $D \notin \mathcal C$: $r_D$ is unknown to $D$ and masks $\sum_{i \text{ honest}} u_i$. Each honest $u_i$ is masked by a stream with another honest operator.
- $D = T_i$: $u_i$ reaches honest operators only, and every other honest $u_j$ carries $\mathsf{PRG}(K_{ji}, \rho, 0)$, unknown to $D$.

#### Modes

- $n = 3$: $\mathcal C = \mathcal T$, no $r_T$, one bit per AND per operator [AFL+16](https://eprint.iacr.org/2016/768).
- Collector, the default of the AND gates (`--reshare collector`): $u_i$ goes to one collector of a rotating $T^\star$, which forwards $v_{T^\star} = \sum_i u_i$. Two rounds, less bandwidth for $t \ge 3$.
- `--reshare peer`: the one-round form above for the AND gates. The check always uses it.

<details>
<summary>Example</summary>

$\{v\} = (2, 7, 4)$, $v = 1$. Pair streams $Z_{01} = 5$, $Z_{02} = 1$, $Z_{12} = 2$.

| operator | $\zeta_i$   | $u_i = v_i + \zeta_i$ | sends to | fills     |
| -------- | ----------- | --------------------- | -------- | --------- |
| $P_0$    | $5 + 1 = 4$ | $2 + 4 = 6$           | $P_2$    | $v_1 = 6$ |
| $P_1$    | $5 + 2 = 7$ | $7 + 7 = 0$           | $P_0$    | $v_2 = 0$ |
| $P_2$    | $1 + 2 = 3$ | $4 + 3 = 7$           | $P_1$    | $v_0 = 7$ |

$[\![ v ]\!] = (7, 6, 0)$, sum $1 = v$.

</details>

### 1.7 OpenRep

#### Syntax

$\mathsf{OpenRep}([\![ v ]\!]) \to v$ or abort. One round, $n\binom{n-1}{t-2}$ copies and $n(t-1)\binom{n-1}{t-2}$ hashes. Robust: no honest operator accepts a wrong value.

#### Protocol

For every term $T$ and every $P_j$, $j \in T$:

1. $\mathrm{owner}(T)$ sends $v_T$ to $P_j$. Every other holder of $T$ sends $H(v_T)$ to $P_j$.
2. $P_j$ aborts unless the hash of the copy equals every received hash.
3. $P_j$ outputs $v = c + \sum_T v_T$.

#### Correctness and robustness

At most $t - 1$ of the $t$ holders are corrupt, so an honest copy or an honest hash reaches $P_j$, and a wrong one aborts. This is the opening of [KPPS23, App. B](https://eprint.iacr.org/2022/675). Honest holders agree on their copies by 1.9.

#### Privacy

Only the output is revealed.

#### Use

Bit vectors: the outputs of a batch and PRF values. Bits have no Shamir sharing.

<details>
<summary>Example</summary>

$[\![ v ]\!] = (4, 5, 6)$, $v = 7$. At $P_0$, which lacks term 0:

| case          | copy from $\mathrm{owner}(0) = P_1$ | hash from $P_2$ | check           | output          |
| ------------- | ----------------------------------- | --------------- | --------------- | --------------- |
| honest        | 4                                   | $H(4)$          | $H(4) = H(4)$   | $4 + 5 + 6 = 7$ |
| $P_1$ corrupt | 2                                   | $H(4)$          | $H(2) \ne H(4)$ | abort           |

</details>

### 1.8 OpenSh

#### Syntax

$\mathsf{OpenSh}(\langle v \rangle, \mathrm{payload}) \to v$ or abort. One round, $n(n-1)$ messages. Robust.

#### Protocol

1. $P_i$ sends $v_i$ and a payload to all.
2. $P_j$ takes $V$ through $v_0, \dots, v_{t-1}$ and aborts unless $v_t, \dots, v_{n-1}$ lie on $V$.
3. $P_j$ outputs $V(0)$ and the payloads.

#### Correctness and robustness

The $t$ honest points fix $V$, so a false point is off it.

#### Privacy

Only the output is revealed.

#### Use

Coins and the final values of the check, which are Shamir shares already.

<details>
<summary>Example</summary>

Received $(v_0, v_1, v_2) = (142, 14, 135)$.

| step                                            | computation                     | result        |
| ----------------------------------------------- | ------------------------------- | ------------- |
| $V$ through $v_0, v_1$, evaluated at $\alpha_2$ | $246 v_0 + 247 v_1 = 122 + 253$ | $135 = v_2$ ✓ |
| $V(0)$                                          | $247 v_0 + 246 v_1 = 244 + 243$ | $v = 7$       |

A corrupt $P_2$ sending any other $v_2$ aborts.

</details>

### 1.9 Coin and digests (derived)

#### Syntax

$\mathsf{Coin}(\rho) \to r$ public. One round.

#### Protocol

$$r = \mathrm{expand}\Big( H\big( \mathsf{OpenSh}( \mathsf{Conv}( \mathsf{Rand}(\rho, 1) ) ) \big) \Big).$$
A challenge is the first expanded value outside $\{0, 1\}$.

#### Soundness

$\mathsf{Rand}$ is unknown to any coalition and $\mathsf{OpenSh}$ is robust, so $r$ is unbiased. A coin that checks reshared values opens in the round after the reshare, since a rushing operator sees the honest shares first. No Fiat-Shamir transform.

#### Digests

The coin of the last check step carries, from every operator to every operator,
$$d_T = H(s_T \,\|\, h_T) \quad \text{for each held } T, \qquad s_T = \text{term } T \text{ of } \mathsf{Rand}(\rho, 2).$$
An operator aborts unless all holders of each $T$ sent the same $d_T$, equal to its own when it holds $T$. A copy split between two honest holders is thus seen by every honest operator before any secret-dependent value opens [CGH+18, Prot. 3.3](https://eprint.iacr.org/2018/570), [KPPS23, $\Pi_{\mathrm{agree}}$](https://eprint.iacr.org/2022/675). The salt hides $h_T$ from operators lacking $T$ [GRW18, §5](https://eprint.iacr.org/2018/216).

## 2. Toy example - AND of 8 secret-shared bits

Inputs $[\![ b_0 ]\!], \dots, [\![ b_7 ]\!]$, bits. Output $b_0 \wedge \dots \wedge b_7$, public. Seven AND gates in $L = 3$ layers, then the check of the seven gates, then the opening. Every multiplication is a gadget, every gadget is one of 1.2 to 1.9, and every message is sent by $\mathsf{Reshare}$, $\mathsf{OpenRep}$ or $\mathsf{OpenSh}$.

### 2.1 AND layers

$[\![ z^{(0)}_e ]\!] = [\![ b_e ]\!]$ for $e < 8$. For $\ell = 1, 2, 3$ and $g < 2^{3 - \ell}$:
$$[\![ z^{(\ell)}_g ]\!] = \mathsf{Reshare}\Big( \mathsf{MulRep}\big( [\![ z^{(\ell-1)}_{2g} ]\!],\ [\![ z^{(\ell-1)}_{2g+1} ]\!] \big) \Big).$$
One round per layer. Each gate records its tuple
$$\big( [\![ x_e ]\!], [\![ y_e ]\!], [\![ z_e ]\!] \big) = \big( [\![ z^{(\ell-1)}_{2g} ]\!], [\![ z^{(\ell-1)}_{2g+1} ]\!], [\![ z^{(\ell)}_g ]\!] \big), \qquad e = 0, \dots, 6 .$$
$\mathsf{Reshare}$ admits an additive error, so $z_e = x_e y_e$ is not yet guaranteed.

### 2.2 Check

Pad with $([\![ 0 ]\!], [\![ 0 ]\!], [\![ 0 ]\!])$ to $N = 2^m = 8$ tuples, $m = 3$.

#### Setup

$$(c_0, \dots, c_{m-1}) = \mathsf{Coin}, \qquad \beta_e = \prod_{k : e_k = 1} c_k \quad \text{for } e = \textstyle\sum_k e_k 2^k,$$
$$\langle C \rangle = \mathsf{Conv}\Big( \sum_{e < N} \beta_e [\![ z_e ]\!] \Big), \qquad \langle A \rangle = \big( \mathsf{Conv}( \beta_e [\![ x_e ]\!] ) \big)_{e < N}, \qquad \langle B \rangle = \big( \mathsf{Conv}( [\![ y_e ]\!] ) \big)_{e < N} .$$
Claim: $C = \sum_e A_e B_e$, true iff every $z_e = x_e y_e$, up to the probability that $\beta$ hides a difference.

#### Halving, $m$ times

With $h = \lvert A \rvert / 2$, $A_{\mathrm{lo}} = A[0{:}h]$, $A_{\mathrm{hi}} = A[h{:}2h]$, the same for $B$:
$$\langle p_0 \rangle, \langle p_2 \rangle = \mathsf{Conv}\Big( \mathsf{Reshare}\big( \mathsf{MulSh}(\langle A_{\mathrm{lo}} \rangle, \langle B_{\mathrm{lo}} \rangle),\ \mathsf{MulSh}(\langle A_{\mathrm{lo}} + A_{\mathrm{hi}} \rangle, \langle B_{\mathrm{lo}} + B_{\mathrm{hi}} \rangle) \big) \Big),$$
$$r = \mathsf{Coin},$$
$$\langle C \rangle \leftarrow \langle p_0 \rangle + (\langle C \rangle + \langle p_2 \rangle)\, r + \langle p_2 \rangle\, r^2, \qquad \langle A \rangle \leftarrow \langle A_{\mathrm{lo}} \rangle + r (\langle A_{\mathrm{lo}} \rangle + \langle A_{\mathrm{hi}} \rangle), \qquad \langle B \rangle \leftarrow \langle B_{\mathrm{lo}} \rangle + r (\langle B_{\mathrm{lo}} \rangle + \langle B_{\mathrm{hi}} \rangle).$$
Two rounds each. $P(X) = \sum_{e < h} (A_{\mathrm{lo}} + X(A_{\mathrm{lo}} + A_{\mathrm{hi}}))_e (B_{\mathrm{lo}} + X(B_{\mathrm{lo}} + B_{\mathrm{hi}}))_e$ has $P(0) = p_0$, $P(1) = C + p_0$ and leading coefficient $p_2$, so the new claim is $P(r) = \sum_e A_e B_e$ of the folded vectors. A wrong claim survives a round with probability $\le 2/(\lvert \mathbb F \rvert - 2)$.

#### Final step

After $m$ halvings $\langle a \rangle = \langle A_0 \rangle$, $\langle b \rangle = \langle B_0 \rangle$ and the claim is $C = ab$:
$$\langle w_a \rangle = \mathsf{Conv}(\mathsf{Rand}), \qquad \langle w_b \rangle = \mathsf{Conv}(\mathsf{Rand}),$$
$$\langle q_0 \rangle, \langle q_2 \rangle = \mathsf{Conv}\Big( \mathsf{Reshare}\big( \mathsf{MulSh}(\langle w_a \rangle, \langle w_b \rangle),\ \mathsf{MulSh}(\langle w_a \rangle + \langle a \rangle, \langle w_b \rangle + \langle b \rangle) \big) \Big),$$
$$r = \mathsf{Coin} \ \text{with the digests of 1.9},$$
$$(u, v, w) = \mathsf{OpenSh}\Big( \langle w_a \rangle + r(\langle w_a \rangle + \langle a \rangle),\ \langle w_b \rangle + r(\langle w_b \rangle + \langle b \rangle),\ \langle q_0 \rangle + (\langle C \rangle + \langle q_0 \rangle + \langle q_2 \rangle)\, r + \langle q_2 \rangle\, r^2 \Big),$$
$$\text{accept iff } uv = w .$$
$Q(X) = (w_a + X(w_a + a))(w_b + X(w_b + b))$ has $Q(0) = q_0$, $Q(1) = ab$ and leading coefficient $q_2$. $w$ interpolates $Q$ with $Q(1)$ replaced by $C$, so $uv = w$ iff $C = ab$, up to $2/(\lvert \mathbb F \rvert - 2)$. $u = (1 + r) w_a + ra$ is uniform as $r \ne 1$, so $a, b$ stay hidden.

### 2.3 Open

$$b_0 \wedge \dots \wedge b_7 = \mathsf{OpenRep}\big( [\![ z^{(3)}_0 ]\!] \big).$$

### 2.4 Rounds

| phase       | gadgets                                            | rounds            |
| ----------- | -------------------------------------------------- | ----------------- |
| AND layers  | $L \times \mathsf{Reshare}$                        | $L = 3$           |
| check setup | $\mathsf{Coin}$                                    | 1                 |
| halving     | $m \times (\mathsf{Reshare}, \mathsf{Coin})$       | $2m = 6$          |
| final step  | $\mathsf{Reshare}, \mathsf{Coin}, \mathsf{OpenSh}$ | 3                 |
| open        | $\mathsf{OpenRep}$                                 | 1                 |
| total       |                                                    | $L + 2m + 5 = 14$ |

## 3. Threshold leanXMSS

### 3.1 From the toy to the key generation

| toy              | Threshold leanXMSS                                                                                                                                                                                                                                                            |
| ---------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 8 random bits    | the chain start $F(x) = \bigoplus_T H(\mathrm{seed}_T \,\|\, x)$, the threshold PRF of [BBDLN26](https://eprint.iacr.org/2026/2142), a $\mathsf{Rand}$ with chosen input, no message                                                                                          |
| 3 AND layers     | 3 Keccak-f[1600] per chain (the WOTS chain of length 4 of [Wam26](https://github.com/TomWambsgans/sphincs.art/blob/9a528527d2d0ea41d2b3b322d2548c0828569a6d/leanXMSS.tex)), 24 layers each, $\chi$ as AND gates on 25 lanes × 64 bits, gates with a public operand are linear |
| 1 gate per layer | 128 chains per batch in `u64` words, one $\mathsf{Reshare}$ round per layer                                                                                                                                                                                                   |
| the AND          | the chain end $y_3$, for bottom trees also $y_1 \oplus F(x_1)$, $y_2 \oplus F(x_2)$ and a commitment to $F(A_{\mathrm{rnd}}(e))$, so a quorum of $t$ signers unmasks $y_p$ with no MPC                                                                                        |

A tree is a session of batches, each batch the AND layers, the check and the OpenRep of 2. Keys and the public parameter $P$ are dealt once at keygen by commit-reveal. Signing a bottom root with its top key is one more run of the same shape.

### 3.2 Rounds and bandwidth

Per batch of 128 chains: $L = 72$ AND layers, $N = 128 \cdot 3 \cdot 36{,}288 \approx 1.4 \cdot 10^7$ tuple bits, $m = 24$ halvings.

| phase      | gadgets                                                                                                               | rounds                        |
| ---------- | --------------------------------------------------------------------------------------------------------------------- | ----------------------------- |
| AND layers | $L \times \mathsf{Reshare}$                                                                                           | 72 (peer) or 144 (collector)  |
| check      | $\mathsf{Coin}$, $m \times (\mathsf{Reshare}, \mathsf{Coin})$, $\mathsf{Reshare}$, $\mathsf{Coin}$, $\mathsf{OpenSh}$ | 52                            |
| open       | $\mathsf{OpenRep}$                                                                                                    | 1                             |
| total      |                                                                                                                       | 125 (peer) or 197 (collector) |

Bandwidth sent by one operator per bottom tree, in the better mode of each group. The AND layers dominate: $(t-1) N$ bits per batch in peer mode, $\frac{3t-3}{n} N$ bits in collector mode, so peer wins on rounds at 2-of-3 and ties on bandwidth, and collector wins on bandwidth from 3-of-5 on.

| group, mode       | bandwidth per tree |
| ----------------- | ------------------ |
| 2-of-3, peer      | 51.7 GB            |
| 3-of-5, collector | 62.1 GB            |
| 4-of-7, collector | 66.5 GB            |

A bottom tree is $2^{16} \cdot 58$ chains, 29,696 chain batches. Signing: 2 rounds among $t$ signers, no MPC.

### 3.3 Security

| property | argument                                                                                                                                                                                                                                                            |
| -------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| gates    | secure up to an additive error                                                                                                                                                                                                                                      |
| check    | before any output opens, misses a wrong tuple with probability $\le (d + 2(m+1)) / (2^{192} - 2) < 2^{-185}$, $d = 18$ coins, $m = 24$                                                                                                                              |
| coins    | robust openings, unbiased challenges                                                                                                                                                                                                                                |
| digests  | a split copy stops every honest operator before the final opening, so honest holders agree at every OpenRep                                                                                                                                                         |
| abort    | each operator decides alone [GS20](https://eprint.iacr.org/2020/134). A failing operator drops its channel, which ends the others' receives. A completing honest operator holds the correct values. A failed session is rerun, a tree being a function of the seeds |

## References

| key                                                                                                             | reference                                                                                                                                                                                                         |
| --------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [AFL+16](https://eprint.iacr.org/2016/768)                                                                      | T. Araki, J. Furukawa, Y. Lindell, A. Nof, K. Ohara. High-Throughput Semi-Honest Secure Three-Party Computation with an Honest Majority. CCS 2016. [ePrint 2016/768](https://eprint.iacr.org/2016/768)            |
| [BBDLN26](https://eprint.iacr.org/2026/2142)                                                                    | D. Boneh, B. Bünz, J. D., Y. Litchev, K. Nazirkhanova. PRAWNS: Threshold Hash-Based Signatures from Threshold PRFs. [ePrint 2026/2142](https://eprint.iacr.org/2026/2142)                                         |
| [CDI05](https://doi.org/10.1007/978-3-540-30576-7_19)                                                           | R. Cramer, I. Damgård, Y. Ishai. Share Conversion, Pseudorandom Secret-Sharing and Applications to Secure Computation. TCC 2005. [doi:10.1007/978-3-540-30576-7_19](https://doi.org/10.1007/978-3-540-30576-7_19) |
| [CGH+18](https://eprint.iacr.org/2018/570)                                                                      | K. Chida, D. Genkin, K. Hamada, D. Ikarashi, R. Kikuchi, Y. Lindell, A. Nof. Fast Large-Scale Honest-Majority MPC for Malicious Adversaries. CRYPTO 2018. [ePrint 2018/570](https://eprint.iacr.org/2018/570)     |
| [GRW18](https://eprint.iacr.org/2018/216)                                                                       | S. D. Gordon, S. Ranellucci, X. Wang. Secure Computation with Low Communication from Cross-Checking. ASIACRYPT 2018. [ePrint 2018/216](https://eprint.iacr.org/2018/216)                                          |
| [GS20](https://eprint.iacr.org/2020/134)                                                                        | V. Goyal, Y. Song. Malicious Security Comes Free in Honest-Majority MPC. [ePrint 2020/134](https://eprint.iacr.org/2020/134)                                                                                      |
| [KPPS23](https://eprint.iacr.org/2022/675)                                                                      | N. Koti, S. Patil, A. Patra, A. Suresh. MPClan: Protocol Suite for Privacy-Conscious Computations. Journal of Cryptology 2023. [ePrint 2022/675](https://eprint.iacr.org/2022/675)                                |
| [MR18](https://eprint.iacr.org/2018/403)                                                                        | P. Mohassel, P. Rindal. ABY3: A Mixed Protocol Framework for Machine Learning. CCS 2018. [ePrint 2018/403](https://eprint.iacr.org/2018/403)                                                                      |
| [Wam26](https://github.com/TomWambsgans/sphincs.art/blob/9a528527d2d0ea41d2b3b322d2548c0828569a6d/leanXMSS.tex) | T. Wambsgans. leanXMSS candidate. [github.com/TomWambsgans/sphincs.art/leanXMSS.tex](https://github.com/TomWambsgans/sphincs.art/blob/9a528527d2d0ea41d2b3b322d2548c0828569a6d/leanXMSS.tex)                      |