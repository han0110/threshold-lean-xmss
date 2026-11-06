# Protocol

> [!WARNING]
> This is an experimental proof of concept. It has no security audit and no complete security proof. Please do not use it.

This note gives the MPC gadgets that the protocol uses, and a toy example for understanding.

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

#### 1.1.2 Terms and sharings

| symbol                                                                       | definition                                                                                                                 |
| ---------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------- |
| $`\mathcal T = \{T \subseteq \{0, \dots, n-1\} : \lvert T \rvert = t - 1\}`$ | the terms                                                                                                                  |
| $`\mathrm{holders}(T) = \{i : i \notin T\}`$                                 | the $t$ operators holding $T$                                                                                              |
| $[\negthinspace[ v ]\negthinspace]$                                          | the replicated sharing $v = c + \sum_{T \in \mathcal T} v_T$, with public part $c$ and $v_T$ held by $\mathrm{holders}(T)$ |
| $\langle v \rangle$                                                          | the Shamir sharing, in which $P_i$ holds $v_i = V(\alpha_i)$, with $\deg V \le t - 1$ and $V(0) = v$                       |
| $`\{v\}`$                                                                    | the additive sharing, in which $P_i$ holds $v_i$ and $v = \sum_i v_i$                                                      |
| $[\negthinspace[ A ]\negthinspace]$                                          | a vector, shared elementwise                                                                                               |

- A coalition of $t - 1$ operators lacks exactly one term, the term equal to itself.
- The three sharings have these uses.
  - $[\negthinspace[ \cdot ]\negthinspace]$ is the sharing of every wire.
  - $\langle \cdot \rangle$ needs $n$ distinct points, so it exists over $\mathbb F_{192}$ only and is used in the check only.
  - $`\{\cdot\}`$ is the output of a multiplication and is reshared in the next round.
- For 2-of-3, a term is one operator, written $k$ for $`\{k\}`$, held by the two operators other than $P_k$.

#### 1.1.3 Public constants of a group $(n, t)$

| constant                                                           | definition                                                                                                                                                                        |
| ------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| $\mathrm{pairs}_i \subseteq \mathcal T \times \mathcal T$          | a balanced partition of all pairs of terms, pair $(A, B)$ given to an operator holding both ($\lvert A \cup B \rvert \le 2t - 2 < n$)                                             |
| $T_i$                                                              | the term lacking $i + 1, \dots, i + t - 1 \pmod n$, filled by $P_i$ in a reshare                                                                                                  |
| $`\mathcal C = \{T_0, \dots, T_{n-1}\}`$                           | the filled terms                                                                                                                                                                  |
| $\mathrm{owner}(T) \in \mathrm{holders}(T)$                        | a balanced choice of one holder per term                                                                                                                                          |
| $\psi_T(X) = \prod_{j \in T} \frac{X + \alpha_j}{\alpha_j}$        | the polynomial of term $T$ ($f_A$ in [CDI05](https://doi.org/10.1007/978-3-540-30576-7_19)), with $\deg \psi_T = t - 1$, $\psi_T(0) = 1$ and $\psi_T(\alpha_j) = 0$ for $j \in T$ |
| $\lambda_i = \prod_{j \ne i} \frac{\alpha_j}{\alpha_j + \alpha_i}$ | the Lagrange weight of $\alpha_i$ at $0$ among all $n$ points                                                                                                                     |

<details>
<summary>Example 2-of-3</summary>

For 2-of-3, the constants are $\alpha = (1, 2, 3)$, $\lambda = (1, 1, 1)$, $(T_0, T_1, T_2) = (1, 2, 0)$ and $\mathrm{owner}(0, 1, 2) = (P_1, P_2, P_0)$.

The constants of each term $k$ follow.

| term $k$ | holders    | $\mathrm{owner}(k)$ | $\psi_k(X)$ | $\psi_k(\alpha_0)$ | $\psi_k(\alpha_1)$ | $\psi_k(\alpha_2)$ |
| -------- | ---------- | ------------------- | ----------- | ------------------ | ------------------ | ------------------ |
| 0        | $P_1, P_2$ | $P_1$               | $1 + X$     | not held           | 3                  | 2                  |
| 1        | $P_0, P_2$ | $P_2$               | $1 + 141X$  | 140                | not held           | 141                |
| 2        | $P_0, P_1$ | $P_0$               | $1 + 246X$  | 247                | 246                | not held           |

The constants of each operator $P_i$ follow.

| operator | held terms | $T_i$ | $\mathrm{pairs}_i$          |
| -------- | ---------- | ----- | --------------------------- |
| $P_0$    | 1, 2       | 1     | $`\{(1,2), (2,1), (2,2)\}`$ |
| $P_1$    | 0, 2       | 2     | $`\{(0,0), (0,2), (2,0)\}`$ |
| $P_2$    | 0, 1       | 0     | $`\{(0,1), (1,0), (1,1)\}`$ |

</details>

<details>
<summary>Example 3-of-5</summary>

A term of 3-of-5 is a set of two operators, for example {0,1}. A subscript writes it as 01, for example $v_{01}$. The tables and the tuples list the 10 terms in the order of the first table.

For 3-of-5, the constants are $\alpha = (1, 2, 3, 4, 5)$ and $\lambda = (1, 208, 208, 209, 209)$. The filled terms $T_0, \dots, T_4$ are {1,2}, {2,3}, {3,4}, {0,4} and {0,1}.

The constants of each term $T$ follow.

| term $T$ | holders         | $\mathrm{owner}(T)$ | $\psi_T(X)$         | $\psi_T(\alpha_0)$ | $\psi_T(\alpha_1)$ | $\psi_T(\alpha_2)$ | $\psi_T(\alpha_3)$ | $\psi_T(\alpha_4)$ |
| -------- | --------------- | ------------------- | ------------------- | ------------------ | ------------------ | ------------------ | ------------------ | ------------------ |
| {0,1}    | $P_2, P_3, P_4$ | $P_2$               | $1 + 140X + 141X^2$ | not held           | not held           | 1                  | 15                 | 14                 |
| {0,2}    | $P_1, P_3, P_4$ | $P_1$               | $1 + 247X + 246X^2$ | not held           | 1                  | not held           | 9                  | 8                  |
| {1,2}    | $P_0, P_3, P_4$ | $P_4$               | $1 + 123X + 123X^2$ | 1                  | not held           | not held           | 7                  | 7                  |
| {0,3}    | $P_1, P_2, P_4$ | $P_4$               | $1 + 202X + 203X^2$ | not held           | 143                | 142                | not held           | 1                  |
| {1,3}    | $P_0, P_2, P_4$ | $P_0$               | $1 + 70X + 232X^2$  | 175                | not held           | 174                | not held           | 174                |
| {2,3}    | $P_0, P_1, P_4$ | $P_1$               | $1 + 61X + 176X^2$  | 140                | 141                | not held           | not held           | 141                |
| {0,4}    | $P_1, P_2, P_3$ | $P_3$               | $1 + 83X + 82X^2$   | not held           | 244                | 245                | 1                  | not held           |
| {1,4}    | $P_0, P_2, P_3$ | $P_2$               | $1 + 223X + 41X^2$  | 247                | not held           | 246                | 246                | not held           |
| {2,4}    | $P_0, P_1, P_3$ | $P_3$               | $1 + 164X + 199X^2$ | 98                 | 99                 | not held           | 99                 | not held           |
| {3,4}    | $P_0, P_1, P_2$ | $P_0$               | $1 + 153X + 153X^2$ | 1                  | 122                | 122                | not held           | not held           |

The constants of each operator $P_i$ follow.

| operator | held terms                               | $T_i$ | $\mathrm{pairs}_i$ |
| -------- | ---------------------------------------- | ----- | ------------------ |
| $P_0$    | {1,2}, {1,3}, {2,3}, {1,4}, {2,4}, {3,4} | {1,2} | 20 pairs           |
| $P_1$    | {0,2}, {0,3}, {2,3}, {0,4}, {2,4}, {3,4} | {2,3} | 20 pairs           |
| $P_2$    | {0,1}, {0,3}, {1,3}, {0,4}, {1,4}, {3,4} | {3,4} | 20 pairs           |
| $P_3$    | {0,1}, {0,2}, {1,2}, {0,4}, {1,4}, {2,4} | {0,4} | 20 pairs           |
| $P_4$    | {0,1}, {0,2}, {1,2}, {0,3}, {1,3}, {2,3} | {0,1} | 20 pairs           |

Each cell gives the operator $i$ with $(A, B) \in \mathrm{pairs}_i$, for row $A$ and column $B$.

| $(A, B)$ | {0,1} | {0,2} | {1,2} | {0,3} | {1,3} | {2,3} | {0,4} | {1,4} | {2,4} | {3,4} |
| -------- | ----- | ----- | ----- | ----- | ----- | ----- | ----- | ----- | ----- | ----- |
| {0,1}    | 4     | 4     | 4     | 4     | 4     | 4     | 3     | 2     | 3     | 2     |
| {0,2}    | 4     | 4     | 4     | 4     | 4     | 4     | 3     | 3     | 1     | 1     |
| {1,2}    | 3     | 4     | 3     | 4     | 4     | 0     | 3     | 0     | 0     | 0     |
| {0,3}    | 2     | 1     | 4     | 2     | 2     | 1     | 2     | 2     | 1     | 1     |
| {1,3}    | 4     | 4     | 0     | 2     | 0     | 0     | 2     | 0     | 0     | 0     |
| {2,3}    | 4     | 1     | 4     | 1     | 0     | 1     | 1     | 0     | 1     | 1     |
| {0,4}    | 3     | 3     | 3     | 2     | 2     | 1     | 3     | 3     | 3     | 2     |
| {1,4}    | 3     | 3     | 0     | 2     | 2     | 0     | 3     | 2     | 3     | 0     |
| {2,4}    | 3     | 1     | 0     | 1     | 0     | 1     | 3     | 3     | 1     | 0     |
| {3,4}    | 2     | 1     | 0     | 2     | 2     | 1     | 2     | 2     | 0     | 1     |

</details>

#### 1.1.4 Keys and pseudorandom streams

| symbol                                           | definition                                        |
| ------------------------------------------------ | ------------------------------------------------- |
| $\mathrm{seed}_T$                                | a key known to $\mathrm{holders}(T)$              |
| $K_{ij} = K_{ji}$                                | a key known to $P_i$ and $P_j$                    |
| $\mathsf{PRG}(\mathrm{key}, \rho, \mathrm{idx})$ | a pseudorandom stream for round $\rho$, used once |

The index $\mathrm{idx}$ is $0$ for reshare masks, $1$ for coins and final masks, and $2$ for digest salts.

#### 1.1.5 Gadget table

| gadget                    | input $\to$ output                                                                  | rounds                  | messages                                                       | section |
| ------------------------- | ----------------------------------------------------------------------------------- | ----------------------- | -------------------------------------------------------------- | ------- |
| $\mathsf{Rand}$           | $\to [\negthinspace[ r ]\negthinspace]$                                             | 0                       | none                                                           | 1.2     |
| $\mathsf{MulRep}$         | $`[\negthinspace[ x ]\negthinspace], [\negthinspace[ y ]\negthinspace] \to \{xy\}`$ | 0                       | none                                                           | 1.3     |
| $\mathsf{MulSh}$          | $`\langle x \rangle, \langle y \rangle \to \{xy\}`$                                 | 0                       | none                                                           | 1.4     |
| $\mathsf{Conv}$           | $[\negthinspace[ v ]\negthinspace] \to \langle v \rangle$                           | 0                       | none                                                           | 1.5     |
| $\mathsf{Reshare}$        | $`\{v\} \to [\negthinspace[ v ]\negthinspace]`$                                     | 1 (2 in collector mode) | $n(t-1)$                                                       | 1.6     |
| $\mathsf{OpenRep}$        | $[\negthinspace[ v ]\negthinspace] \to v$                                           | 1                       | $n\binom{n-1}{t-2}$ copies and $n(t-1)\binom{n-1}{t-2}$ hashes | 1.7     |
| $\mathsf{OpenSh}$         | $\langle v \rangle \to v$                                                           | 1                       | $n(n-1)$                                                       | 1.8     |
| $\mathsf{Coin}$ (derived) | $\to r$ public                                                                      | 1                       | as $\mathsf{OpenSh}$                                           | 1.9     |

The gadgets compose by one rule. A product is $`\{\cdot\}`$, and $`\{\cdot\}`$ is reshared to $[\negthinspace[ \cdot ]\negthinspace]$ in the next round.

#### 1.1.6 Notation against the literature

[GS20](https://eprint.iacr.org/2020/134) counts $t$ corrupt among $n = 2t + 1$. Here $t$ is the quorum size, so a sharing $[x]_t$ of [GS20](https://eprint.iacr.org/2020/134) has degree $t - 1$ here.

| here                                                                              | literature                                                                                                                                                        |
| --------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| $\langle x \rangle$, degree $t - 1$                                               | $[x]_t$ in [GS20](https://eprint.iacr.org/2020/134)                                                                                                               |
| $[\negthinspace[ x ]\negthinspace]$                                               | replicated sharing of [CDI05](https://doi.org/10.1007/978-3-540-30576-7_19), [AFL+16](https://eprint.iacr.org/2016/768), [MR18](https://eprint.iacr.org/2018/403) |
| $\psi_T$                                                                          | $f_A$ in [CDI05](https://doi.org/10.1007/978-3-540-30576-7_19), $A = T$ a maximal unqualified set                                                                 |
| $\lambda_i$                                                                       | Lagrange coefficients at $0$ from all $n$ shares                                                                                                                  |
| $(\langle A \rangle, \langle B \rangle, \langle C \rangle)$, $C = \sum_e A_e B_e$ | the inner-product tuple $([\boldsymbol x]_t, [\boldsymbol y]_t, [z]_t)$ of [GS20, §4](https://eprint.iacr.org/2020/134)                                           |
| halving, $r$                                                                      | compression of [GS20](https://eprint.iacr.org/2020/134) with $k = 2$, challenge $r$                                                                               |
| $\mathsf{Coin}$                                                                   | $\mathcal F_{\mathrm{coin}}$ of [GS20](https://eprint.iacr.org/2020/134)                                                                                          |

### 1.2 Rand

#### Syntax

$\mathsf{Rand}(\rho, \mathrm{idx}) \to [\negthinspace[ r ]\negthinspace]$. Local.

#### Protocol

Each holder of $T$ sets
```math
r_T = \mathsf{PRG}(\mathrm{seed}_T, \rho, \mathrm{idx}).
```

#### Correctness

The holders of $T$ share $\mathrm{seed}_T$.

#### Privacy

A coalition lacks one seed, so one term of $r$ is pseudorandom to it.

<details>
<summary>Example 2-of-3</summary>

| term | computed by | $r_T$ |
| ---- | ----------- | ----- |
| 0    | $P_1, P_2$  | 4     |
| 1    | $P_0, P_2$  | 5     |
| 2    | $P_0, P_1$  | 6     |

$r = 4 + 5 + 6 = 7$, known to nobody.

</details>

<details>
<summary>Example 3-of-5</summary>

| term  | computed by     | $r_T$ |
| ----- | --------------- | ----- |
| {0,1} | $P_2, P_3, P_4$ | 1     |
| {0,2} | $P_1, P_3, P_4$ | 2     |
| {1,2} | $P_0, P_3, P_4$ | 3     |
| {0,3} | $P_1, P_2, P_4$ | 4     |
| {1,3} | $P_0, P_2, P_4$ | 5     |
| {2,3} | $P_0, P_1, P_4$ | 6     |
| {0,4} | $P_1, P_2, P_3$ | 7     |
| {1,4} | $P_0, P_2, P_3$ | 8     |
| {2,4} | $P_0, P_1, P_3$ | 9     |
| {3,4} | $P_0, P_1, P_2$ | 10    |

$r = 1 + 2 + \dots + 10 = 11$, known to nobody.

</details>

### 1.3 MulRep

#### Syntax

$`\mathsf{MulRep}([\negthinspace[ x ]\negthinspace], [\negthinspace[ y ]\negthinspace]) \to \{xy\}`$. Local. On vectors, the additive share of $\sum_e x_e y_e$.

#### Protocol

```math
(xy)_i = \sum_{(A,B) \in \mathrm{pairs}_i} x_A\, y_B .
```

#### Correctness

$xy = \sum_{A, B} x_A y_B$ and the pairs partition all $(A, B)$.

#### Privacy

No message.

#### Use

The AND gate and the slice table of the check, over $\mathbb F_2$.

<details>
<summary>Example 2-of-3</summary>

$[\negthinspace[ a ]\negthinspace] = (1, 1, 1)$, $[\negthinspace[ b ]\negthinspace] = (0, 1, 0)$, $a = b = 1$.

| operator | $\sum_{\mathrm{pairs}_i} a_A b_B$         | share |
| -------- | ----------------------------------------- | ----- |
| $P_0$    | $a_1 b_2 + a_2 b_1 + a_2 b_2 = 0 + 1 + 0$ | 1     |
| $P_1$    | $a_0 b_0 + a_0 b_2 + a_2 b_0 = 0 + 0 + 0$ | 0     |
| $P_2$    | $a_0 b_1 + a_1 b_0 + a_1 b_1 = 1 + 0 + 1$ | 0     |

$`\{ab\} = (1, 0, 0)`$, sum $1 = ab$.

</details>

<details>
<summary>Example 3-of-5</summary>

$[\negthinspace[ a ]\negthinspace] = (1, 0, 0, 0, 0, 1, 0, 0, 1, 0)$, $[\negthinspace[ b ]\negthinspace] = (0, 0, 0, 0, 0, 0, 0, 0, 0, 1)$, $a = b = 1$. Only $a_{01}$, $a_{23}$, $a_{24}$ and $b_{34}$ are 1, so the table gives only the nonzero products.

| operator | nonzero $a_A b_B$ in $\mathrm{pairs}_i$ | share |
| -------- | --------------------------------------- | ----- |
| $P_0$    | $a_{24} b_{34}$                         | 1     |
| $P_1$    | $a_{23} b_{34}$                         | 1     |
| $P_2$    | $a_{01} b_{34}$                         | 1     |
| $P_3$    | none                                    | 0     |
| $P_4$    | none                                    | 0     |

$`\{ab\} = (1, 1, 1, 0, 0)`$, sum $1 = ab$.

</details>

### 1.4 MulSh

#### Syntax

$`\mathsf{MulSh}(\langle x \rangle, \langle y \rangle) \to \{xy\}`$. Local. On vectors, the additive share of $\sum_e x_e y_e$.

#### Protocol

```math
(xy)_i = \lambda_i\, x_i\, y_i .
```

#### Correctness

$x_i y_i = (XY)(\alpha_i)$ with $\deg XY \le 2t - 2 = n - 1$, so $\sum_i \lambda_i x_i y_i = (XY)(0) = xy$.

#### Privacy

No message.

#### Use

The vector phase of the check, one multiplication per element.

<details>
<summary>Example 2-of-3</summary>

$\langle x \rangle = (142, 14, 135)$ with $x = 7$, $\langle y \rangle = (240, 247, 3)$ with $y = 4$, $\lambda = (1, 1, 1)$.

| operator | $\lambda_i x_i y_i$ | share |
| -------- | ------------------- | ----- |
| $P_0$    | $142 \cdot 240$     | 115   |
| $P_1$    | $14 \cdot 247$      | 253   |
| $P_2$    | $135 \cdot 3$       | 146   |

$`\{xy\} = (115, 253, 146)`$, sum $28 = 7 \cdot 4$.

</details>

<details>
<summary>Example 3-of-5</summary>

$\langle x \rangle = (143, 174, 42, 180, 48)$ with $x = 11$, $\langle y \rangle = (14, 38, 44, 152, 146)$ with $y = 4$, $\lambda = (1, 208, 208, 209, 209)$.

| operator | $\lambda_i x_i y_i$       | share |
| -------- | ------------------------- | ----- |
| $P_0$    | $1 \cdot 143 \cdot 14$    | 27    |
| $P_1$    | $208 \cdot 174 \cdot 38$  | 151   |
| $P_2$    | $208 \cdot 42 \cdot 44$   | 71    |
| $P_3$    | $209 \cdot 180 \cdot 152$ | 63    |
| $P_4$    | $209 \cdot 48 \cdot 146$  | 216   |

$`\{xy\} = (27, 151, 71, 63, 216)`$, sum $44 = 11 \cdot 4$.

</details>

### 1.5 Conv

#### Syntax

$\mathsf{Conv}([\negthinspace[ v ]\negthinspace]) \to \langle v \rangle$. Local.

#### Protocol

```math
v_i = \sum_{T : i \notin T} \psi_T(\alpha_i)\, v_T .
```

#### Correctness

$`V(X) = \sum_T v_T\, \psi_T(X)`$ has $\deg V \le t - 1$, $V(0) = v$, and $V(\alpha_i) = v_i$ since $\psi_T(\alpha_i) = 0$ for $i \in T$.

#### Privacy

No message.

<details>
<summary>Example 2-of-3</summary>

$[\negthinspace[ v ]\negthinspace] = (4, 5, 6)$, $v = 7$, $V(X) = 4(1 + X) + 5(1 + 141X) + 6(1 + 246X) = 7 + 137X$.

| operator | $`\sum_{T : i \notin T} \psi_T(\alpha_i)\, v_T`$ | $V(\alpha_i)$ |
| -------- | ------------------------------------------------ | ------------- |
| $P_0$    | $140 \cdot 5 + 247 \cdot 6 = 138 + 4$            | 142           |
| $P_1$    | $3 \cdot 4 + 246 \cdot 6 = 12 + 2$               | 14            |
| $P_2$    | $2 \cdot 4 + 141 \cdot 5 = 8 + 143$              | 135           |

</details>

<details>
<summary>Example 3-of-5</summary>

$[\negthinspace[ v ]\negthinspace] = (1, 2, \dots, 10)$, $v = 11$, $`V(X) = \sum_T v_T\, \psi_T(X) = 11 + 68X + 192X^2`$.

| operator | $`\sum_{T : i \notin T} \psi_T(\alpha_i)\, v_T`$ | $V(\alpha_i)$ |
| -------- | ------------------------------------------------ | ------------- |
| $P_0$    | $3 + 37 + 5 + 249 + 95 + 10$                     | 143           |
| $P_1$    | $2 + 10 + 3 + 250 + 86 + 9$                      | 174           |
| $P_2$    | $1 + 14 + 32 + 253 + 241 + 9$                    | 42            |
| $P_3$    | $15 + 18 + 9 + 7 + 241 + 86$                     | 180           |
| $P_4$    | $14 + 16 + 9 + 4 + 32 + 3$                       | 48            |

</details>

### 1.6 Reshare

#### Syntax

$`\mathsf{Reshare}(\{v\}) \to [\negthinspace[ v ]\negthinspace]`$. One round, $n(t-1)$ messages.

#### Protocol, round $\rho$

1. $[\negthinspace[ r ]\negthinspace] = \mathsf{Rand}(\rho, 0)$, $\zeta_i = \sum_{j \ne i} \mathsf{PRG}(K_{ij}, \rho, 0)$.
2. $P_i$ sends $`u_i = v_i + \zeta_i + \sum_{T \notin \mathcal C,\ \mathrm{owner}(T) = i} r_T`$ to $`\mathrm{holders}(T_i) \setminus \{i\}`$.
3. $v_{T_i} = u_i$, and $v_T = r_T$ for $T \notin \mathcal C$. Each holder of $T \in \mathcal C$ appends $v_T$ to its digest $h_T$ (see 1.9).

#### Correctness

$\sum_i \zeta_i = 0$ (each pair stream is added twice), and each $r_T$, $T \notin \mathcal C$, is added twice. So the terms sum to
```math
\sum_T v_T = \sum_i u_i + \sum_{T \notin \mathcal C} r_T = \sum_i v_i = v .
```

#### Privacy

A coalition $D$ lacks only term $D$. The argument has two cases.

- If $D \notin \mathcal C$, then $r_D$ is unknown to $D$ and masks $\sum_{i \text{ honest}} u_i$. A stream with another honest operator masks each honest $u_i$.
- If $D = T_i$, then $u_i$ reaches honest operators only. Every other honest $u_j$ carries $\mathsf{PRG}(K_{ji}, \rho, 0)$, which is unknown to $D$.

#### Modes

- For $n = 3$, $\mathcal C = \mathcal T$ and there is no $r_T$. Each operator sends one bit per AND [AFL+16](https://eprint.iacr.org/2016/768).
- Collector mode is the default of the AND gates.
  - $u_i$ goes to one collector of a rotating $T^\star$, which forwards $v_{T^\star} = \sum_i u_i$.
  - It takes two rounds and uses less bandwidth for $t \ge 3$.
- Peer mode is the one-round form above for the AND gates. The check always uses it.

<details>
<summary>Example 2-of-3</summary>

$`\{v\} = (2, 7, 4)`$, $v = 1$. Pair streams $Z_{01} = 5$, $Z_{02} = 1$, $Z_{12} = 2$.

| operator | $\zeta_i$   | $u_i = v_i + \zeta_i$ | sends to | fills     |
| -------- | ----------- | --------------------- | -------- | --------- |
| $P_0$    | $5 + 1 = 4$ | $2 + 4 = 6$           | $P_2$    | $v_1 = 6$ |
| $P_1$    | $5 + 2 = 7$ | $7 + 7 = 0$           | $P_0$    | $v_2 = 0$ |
| $P_2$    | $1 + 2 = 3$ | $4 + 3 = 7$           | $P_1$    | $v_0 = 7$ |

$[\negthinspace[ v ]\negthinspace] = (7, 6, 0)$, sum $1 = v$.

</details>

<details>
<summary>Example 3-of-5</summary>

$`\{v\} = (2, 7, 4, 9, 5)`$, $v = 13$. The filled terms are {1,2}, {2,3}, {3,4}, {0,4} and {0,1}. Each other term has $v_T = r_T$, and its owner adds $r_T$ to $u_i$.

The pair streams $Z_{ij}$ and their sums $\zeta_i$ follow.

| $Z_{ij}$ | $j = 0$ | $j = 1$ | $j = 2$ | $j = 3$ | $j = 4$ | $\zeta_i$ |
| -------- | ------- | ------- | ------- | ------- | ------- | --------- |
| $i = 0$  |         | 5       | 1       | 6       | 3       | 1         |
| $i = 1$  | 5       |         | 2       | 8       | 4       | 11        |
| $i = 2$  | 1       | 2       |         | 7       | 9       | 13        |
| $i = 3$  | 6       | 8       | 7       |         | 6       | 15        |
| $i = 4$  | 3       | 4       | 9       | 6       |         | 8         |

The messages follow.

| operator | owned $r_T$  | $u_i = v_i + \zeta_i + r_T$ | sends to   | fills         |
| -------- | ------------ | --------------------------- | ---------- | ------------- |
| $P_0$    | $r_{13} = 8$ | $2 + 1 + 8 = 11$            | $P_3, P_4$ | $v_{12} = 11$ |
| $P_1$    | $r_{02} = 3$ | $7 + 11 + 3 = 15$           | $P_0, P_4$ | $v_{23} = 15$ |
| $P_2$    | $r_{14} = 9$ | $4 + 13 + 9 = 0$            | $P_0, P_1$ | $v_{34} = 0$  |
| $P_3$    | $r_{24} = 6$ | $9 + 15 + 6 = 0$            | $P_1, P_2$ | $v_{04} = 0$  |
| $P_4$    | $r_{03} = 1$ | $5 + 8 + 1 = 12$            | $P_2, P_3$ | $v_{01} = 12$ |

$[\negthinspace[ v ]\negthinspace] = (12, 3, 11, 1, 8, 15, 0, 9, 6, 0)$, sum $13 = v$.

</details>

### 1.7 OpenRep

#### Syntax

$\mathsf{OpenRep}([\negthinspace[ v ]\negthinspace]) \to v$ or abort. One round, $n\binom{n-1}{t-2}$ copies and $n(t-1)\binom{n-1}{t-2}$ hashes. It is robust, so no honest operator accepts a wrong value.

#### Protocol

The steps run for every term $T$ and every $P_j$, $j \in T$.

1. $\mathrm{owner}(T)$ sends $v_T$ to $P_j$. Every other holder of $T$ sends $H(v_T)$ to $P_j$.
2. $P_j$ aborts unless the hash of the copy equals every received hash.
3. $P_j$ outputs $v = c + \sum_T v_T$.

#### Correctness and robustness

At most $t - 1$ of the $t$ holders are corrupt, so an honest copy or an honest hash reaches $P_j$, and a wrong one aborts. This is the opening of [KPPS23, App. B](https://eprint.iacr.org/2022/675). Honest holders agree on their copies by 1.9.

#### Privacy

Only the output is revealed.

#### Use

The outputs of a batch and PRF values, which are bit vectors. Bits have no Shamir sharing.

<details>
<summary>Example 2-of-3</summary>

$[\negthinspace[ v ]\negthinspace] = (4, 5, 6)$, $v = 7$. The table gives the two cases at $P_0$, which lacks term 0.

| case          | copy from $\mathrm{owner}(0) = P_1$ | hash from $P_2$ | check           | output          |
| ------------- | ----------------------------------- | --------------- | --------------- | --------------- |
| honest        | 4                                   | $H(4)$          | $H(4) = H(4)$   | $4 + 5 + 6 = 7$ |
| $P_1$ corrupt | 2                                   | $H(4)$          | $H(2) \ne H(4)$ | abort           |

</details>

<details>
<summary>Example 3-of-5</summary>

$[\negthinspace[ v ]\negthinspace] = (1, 2, \dots, 10)$, $v = 11$. The table gives the two cases at $P_0$, which lacks the four terms that contain 0.

| case          | term $T$ | $\mathrm{owner}(T)$ | copy | hashes from | check           |
| ------------- | -------- | ------------------- | ---- | ----------- | --------------- |
| honest        | {0,1}    | $P_2$               | 1    | $P_3, P_4$  | $H(1) = H(1)$   |
| honest        | {0,2}    | $P_1$               | 2    | $P_3, P_4$  | $H(2) = H(2)$   |
| honest        | {0,3}    | $P_4$               | 4    | $P_1, P_2$  | $H(4) = H(4)$   |
| honest        | {0,4}    | $P_3$               | 7    | $P_1, P_2$  | $H(7) = H(7)$   |
| $P_2$ corrupt | {0,1}    | $P_2$               | 2    | $P_3, P_4$  | $H(2) \ne H(1)$ |

In the honest case, $P_0$ outputs $1 + 2 + \dots + 10 = 11$. If $P_2$ is corrupt, $P_0$ aborts.

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
<summary>Example 2-of-3</summary>

Received $(v_0, v_1, v_2) = (142, 14, 135)$.

| step                                            | computation                     | result        |
| ----------------------------------------------- | ------------------------------- | ------------- |
| $V$ through $v_0, v_1$, evaluated at $\alpha_2$ | $246 v_0 + 247 v_1 = 122 + 253$ | $135 = v_2$ ✓ |
| $V(0)$                                          | $247 v_0 + 246 v_1 = 244 + 243$ | $v = 7$       |

A corrupt $P_2$ sending any other $v_2$ aborts.

</details>

<details>
<summary>Example 3-of-5</summary>

Received $(v_0, \dots, v_4) = (143, 174, 42, 180, 48)$.

| step                                                 | computation                                | result        |
| ---------------------------------------------------- | ------------------------------------------ | ------------- |
| $V$ through $v_0, v_1, v_2$, evaluated at $\alpha_3$ | $7 v_0 + 9 v_1 + 15 v_2 = 128 + 169 + 157$ | $180 = v_3$ ✓ |
| $V$ through $v_0, v_1, v_2$, evaluated at $\alpha_4$ | $7 v_0 + 8 v_1 + 14 v_2 = 128 + 7 + 183$   | $48 = v_4$ ✓  |
| $V(0)$                                               | $v_0 + v_1 + v_2 = 143 + 174 + 42$         | $v = 11$      |

A corrupt $P_3$ or $P_4$ sending any other $v_3$ or $v_4$ aborts.

</details>

### 1.9 Coin and digests (derived)

#### Syntax

$\mathsf{Coin}(\rho) \to r$ public. One round.

#### Protocol

```math
r = \mathrm{expand}\Big( H\big( \mathsf{OpenSh}( \mathsf{Conv}( \mathsf{Rand}(\rho, 1) ) ) \big) \Big).
```
A challenge is the first expanded value outside $`\{0, 1\}`$.

#### Soundness

$\mathsf{Rand}$ is unknown to any coalition and $\mathsf{OpenSh}$ is robust, so $r$ is unbiased. A coin that checks reshared values opens in the round after the reshare, since a rushing operator sees the honest shares first. No Fiat-Shamir transform.

#### Digests

The coin of the last check step carries, from every operator to every operator,
```math
d_T = H(s_T \,\|\, h_T) \quad \text{for each held } T, \qquad s_T = \text{term } T \text{ of } \mathsf{Rand}(\rho, 2).
```

- An operator aborts unless all holders of each $T$ sent the same $d_T$, equal to its own when it holds $T$.
- Thus every honest operator sees a copy split between two honest holders before any secret-dependent value opens [CGH+18, Prot. 3.3](https://eprint.iacr.org/2018/570), [KPPS23](https://eprint.iacr.org/2022/675) $\Pi_{\mathrm{agree}}$.
- The salt hides $h_T$ from operators lacking $T$ [GRW18, §5](https://eprint.iacr.org/2018/216).

## 2. Toy example - AND of 8 secret-shared bits

The inputs are $[\negthinspace[ b_0 ]\negthinspace], \dots, [\negthinspace[ b_7 ]\negthinspace]$, which are bits. The output is $b_0 \wedge \dots \wedge b_7$, which is public. The protocol runs three phases in order.

1. Seven AND gates run in $L = 3$ layers.
2. The check covers the seven gates.
3. The output opens.

Every multiplication is a gadget, and every gadget is one of 1.2 to 1.9. Every message is sent by $\mathsf{Reshare}$, $\mathsf{OpenRep}$ or $\mathsf{OpenSh}$.

### 2.1 AND layers

$[\negthinspace[ z^{(0)}_e ]\negthinspace] = [\negthinspace[ b_e ]\negthinspace]$ for $e < 8$. For $\ell = 1, 2, 3$ and $g < 2^{3 - \ell}$, gate $g$ of layer $\ell$ computes
```math
[\negthinspace[ z^{(\ell)}_g ]\negthinspace] = \mathsf{Reshare}\Big( \mathsf{MulRep}\big( [\negthinspace[ z^{(\ell-1)}_{2g} ]\negthinspace],\ [\negthinspace[ z^{(\ell-1)}_{2g+1} ]\negthinspace] \big) \Big).
```
One round per layer. Each gate records its tuple
```math
\big( [\negthinspace[ x_e ]\negthinspace], [\negthinspace[ y_e ]\negthinspace], [\negthinspace[ z_e ]\negthinspace] \big) = \big( [\negthinspace[ z^{(\ell-1)}_{2g} ]\negthinspace], [\negthinspace[ z^{(\ell-1)}_{2g+1} ]\negthinspace], [\negthinspace[ z^{(\ell)}_g ]\negthinspace] \big), \qquad e = 0, \dots, 6 .
```
$\mathsf{Reshare}$ admits an additive error, so $z_e = x_e y_e$ is not yet guaranteed.

### 2.2 Check

Pad with $([\negthinspace[ 0 ]\negthinspace], [\negthinspace[ 0 ]\negthinspace], [\negthinspace[ 0 ]\negthinspace])$ to $N = 2^m = 8$ tuples, $m = 3$.

#### Setup

```math
(c_0, \dots, c_{m-1}) = \mathsf{Coin}, \qquad \beta_e = \prod_{k : e_k = 1} c_k \quad \text{for } e = \textstyle\sum_k e_k 2^k,
```
```math
\langle C \rangle = \mathsf{Conv}\Big( \sum_{e < N} \beta_e [\negthinspace[ z_e ]\negthinspace] \Big), \qquad \langle A \rangle = \big( \mathsf{Conv}( \beta_e [\negthinspace[ x_e ]\negthinspace] ) \big)_{e < N}, \qquad \langle B \rangle = \big( \mathsf{Conv}( [\negthinspace[ y_e ]\negthinspace] ) \big)_{e < N} .
```
The claim is $C = \sum_e A_e B_e$. It is true iff every $z_e = x_e y_e$, up to the probability that $\beta$ hides a difference.

#### Halving, $m$ times

With $h = \lvert A \rvert / 2$, $A_{\mathrm{lo}} = A[0{:}h]$, $A_{\mathrm{hi}} = A[h{:}2h]$, and the same for $B$, a halving computes
```math
\langle p_0 \rangle, \langle p_2 \rangle = \mathsf{Conv}\Big( \mathsf{Reshare}\big( \mathsf{MulSh}(\langle A_{\mathrm{lo}} \rangle, \langle B_{\mathrm{lo}} \rangle),\ \mathsf{MulSh}(\langle A_{\mathrm{lo}} + A_{\mathrm{hi}} \rangle, \langle B_{\mathrm{lo}} + B_{\mathrm{hi}} \rangle) \big) \Big),
```
```math
r = \mathsf{Coin},
```
```math
\langle C \rangle \leftarrow \langle p_0 \rangle + (\langle C \rangle + \langle p_2 \rangle)\, r + \langle p_2 \rangle\, r^2, \qquad \langle A \rangle \leftarrow \langle A_{\mathrm{lo}} \rangle + r (\langle A_{\mathrm{lo}} \rangle + \langle A_{\mathrm{hi}} \rangle), \qquad \langle B \rangle \leftarrow \langle B_{\mathrm{lo}} \rangle + r (\langle B_{\mathrm{lo}} \rangle + \langle B_{\mathrm{hi}} \rangle).
```
Two rounds each. $P(X) = \sum_{e < h} (A_{\mathrm{lo}} + X(A_{\mathrm{lo}} + A_{\mathrm{hi}}))_e (B_{\mathrm{lo}} + X(B_{\mathrm{lo}} + B_{\mathrm{hi}}))_e$ has $P(0) = p_0$, $P(1) = C + p_0$ and leading coefficient $p_2$, so the new claim is $P(r) = \sum_e A_e B_e$ of the folded vectors. A wrong claim survives a round with probability $\le 2/(\lvert \mathbb F \rvert - 2)$.

#### Final step

After $m$ halvings $\langle a \rangle = \langle A_0 \rangle$, $\langle b \rangle = \langle B_0 \rangle$ and the claim is $C = ab$. The final step computes
```math
\langle w_a \rangle = \mathsf{Conv}(\mathsf{Rand}), \qquad \langle w_b \rangle = \mathsf{Conv}(\mathsf{Rand}),
```
```math
\langle q_0 \rangle, \langle q_2 \rangle = \mathsf{Conv}\Big( \mathsf{Reshare}\big( \mathsf{MulSh}(\langle w_a \rangle, \langle w_b \rangle),\ \mathsf{MulSh}(\langle w_a \rangle + \langle a \rangle, \langle w_b \rangle + \langle b \rangle) \big) \Big),
```
```math
r = \mathsf{Coin} \ \text{with the digests of 1.9},
```
```math
(u, v, w) = \mathsf{OpenSh}\Big( \langle w_a \rangle + r(\langle w_a \rangle + \langle a \rangle),\ \langle w_b \rangle + r(\langle w_b \rangle + \langle b \rangle),\ \langle q_0 \rangle + (\langle C \rangle + \langle q_0 \rangle + \langle q_2 \rangle)\, r + \langle q_2 \rangle\, r^2 \Big),
```
```math
\text{accept iff } uv = w .
```
$Q(X) = (w_a + X(w_a + a))(w_b + X(w_b + b))$ has $Q(0) = q_0$, $Q(1) = ab$ and leading coefficient $q_2$. $w$ interpolates $Q$ with $Q(1)$ replaced by $C$, so $uv = w$ iff $C = ab$, up to $2/(\lvert \mathbb F \rvert - 2)$. $u = (1 + r) w_a + ra$ is uniform as $r \ne 1$, so $a, b$ stay hidden.

### 2.3 Open

```math
b_0 \wedge \dots \wedge b_7 = \mathsf{OpenRep}\big( [\negthinspace[ z^{(3)}_0 ]\negthinspace] \big).
```

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

| toy              | Threshold leanXMSS                                                                                                                                                                        |
| ---------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 8 random bits    | the chain start $`F(x) = \bigoplus_T H(\mathrm{seed}_T \,\Vert\, x)`$, the threshold PRF of [BBDLN26](https://eprint.iacr.org/2026/2142), a $\mathsf{Rand}$ with chosen input, no message |
| 3 AND layers     | 3 Keccak-f[1600] per chain, 24 layers each, with $\chi$ as AND gates on 25 lanes × 64 bits                                                                                                |
| 1 gate per layer | 128 chains per batch in `u64` words, one $\mathsf{Reshare}$ round per layer                                                                                                               |
| the AND          | the chain end $y_3$, for bottom trees also $y_1 \oplus F(x_1)$, $y_2 \oplus F(x_2)$ and a commitment to $F(A_{\mathrm{rnd}}(e))$                                                          |

These facts complete the table.

- The 3 Keccak-f[1600] of a chain form the WOTS chain of length 4 of [Wam26](https://github.com/TomWambsgans/sphincs.art/blob/9a528527d2d0ea41d2b3b322d2548c0828569a6d/leanXMSS.tex).
- Gates with a public operand are linear.
- With the extra outputs of a bottom tree, a quorum of $t$ signers unmasks $y_p$ with no MPC.

A tree is a session of batches, each batch the AND layers, the check and the OpenRep of 2. Signing a bottom root with its top key is one more run of the same shape.

Keys and the public parameter $P$ are dealt once at keygen by commit-reveal.

### 3.2 Rounds and bandwidth

A batch of 128 chains has $L = 72$ AND layers, $N = 128 \cdot 3 \cdot 36{,}288 \approx 1.4 \cdot 10^7$ tuple bits and $m = 24$ halvings.

| phase      | gadgets                                                                                                               | rounds                        |
| ---------- | --------------------------------------------------------------------------------------------------------------------- | ----------------------------- |
| AND layers | $L \times \mathsf{Reshare}$                                                                                           | 72 (peer) or 144 (collector)  |
| check      | $\mathsf{Coin}$, $m \times (\mathsf{Reshare}, \mathsf{Coin})$, $\mathsf{Reshare}$, $\mathsf{Coin}$, $\mathsf{OpenSh}$ | 52                            |
| open       | $\mathsf{OpenRep}$                                                                                                    | 1                             |
| total      |                                                                                                                       | 125 (peer) or 197 (collector) |

The AND layers dominate the bandwidth.

- Peer mode sends $(t-1) N$ bits per batch.
- Collector mode sends $\frac{3t-3}{n} N$ bits per batch.

So peer wins on rounds at 2-of-3 and ties on bandwidth, and collector wins on bandwidth from 3-of-5 on.

The table gives the bandwidth sent by one operator per bottom tree, in the better mode of each group.

| group, mode       | bandwidth per tree |
| ----------------- | ------------------ |
| 2-of-3, peer      | 51.7 GB            |
| 3-of-5, collector | 62.1 GB            |
| 4-of-7, collector | 66.5 GB            |

A bottom tree is $2^{16} \cdot 58$ chains, 29,696 chain batches. Signing takes 2 rounds among $t$ signers and needs no MPC.

### 3.3 Security

| property | argument                                                                                                                               |
| -------- | -------------------------------------------------------------------------------------------------------------------------------------- |
| gates    | secure up to an additive error                                                                                                         |
| check    | before any output opens, misses a wrong tuple with probability $\le (d + 2(m+1)) / (2^{192} - 2) < 2^{-185}$, $d = 18$ coins, $m = 24$ |
| coins    | robust openings, unbiased challenges                                                                                                   |
| digests  | a split copy stops every honest operator before the final opening, so honest holders agree at every OpenRep                            |
| abort    | each operator decides alone [GS20](https://eprint.iacr.org/2020/134)                                                                   |

The abort has these consequences.

- A failing operator drops its channel, which ends the others' receives.
- A completing honest operator holds the correct values.
- A failed session is rerun, because a tree is a function of the seeds.

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