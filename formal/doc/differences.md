# Differences to the sources

This file lists each difference of the model to GS20 [GS20], PRAWNS [BBD+26], the note [Wam26] and leanXMSS [lea26], with the row ids. [statement.tex](../statement.tex) is the guide, and its Appendix B keeps only the rows that change the meaning of a claim.

Table B.1 lists the basic differences in the model and in the assumptions, and Table B.2 lists the adaptations of the protocol. Each claim in the last column of Table B.2 is a proved field of the bundle for the adapted protocol. The module documentation also lists the deviations. The rules 1 and 2 are the rules of the deployment contract in Section 4 of `statement.tex`. The two points below are not differences.

- GS20 has $t$ corrupt parties among $n=2t+1$, and this model has $t-1$ among $n=2t-1$.
- The adversary is rushing. GS20 has malicious parties and synchronous channels (its Section 3.1), but it does not name a rushing adversary.

## Table B.1

| B.1 | Source | This model | Effect on the claim |
| --- | --- | --- | --- |
| A1 | GS20 aborts locally in Protocol 15, step 8. Its Functionalities 5, 16 and 18 have a common abort. | Each operator aborts alone [GL05], because the network has no broadcast. | Each simulation claim has selective abort. Rule 2 of the contract is a deployment requirement with no proof. |
| A2 | GS20 is information-theoretic, with a statistical error of the check. | $H$ is a random oracle for digests, coin keys and challenges. AES-128 is the PRG. | The bounds of `multVerifySecurity` and `mainSecurity` depend on the call count. The PRF advantage is in `prssRandSecurity`, in `prssRealRandSecurity` and in the open claim. |
| A3 | Honest Shamir shares fix each sharing (GS20, Section 3.2). Functionalities 7, 9, 16 leak corrupt shares. | Honest copies can differ. $`\mathcal F_{\mathrm{mult}}`$, $`\mathcal F_{\mathrm{multVerify}}`$, $`\mathcal F_{\mathrm{main}}`$ also leak honest copies of terms that corrupt operators hold. | Building-block claims hold on valid inputs only. On `MainInputs` the copy leak of $`\mathcal F_{\mathrm{main}}`$ gives no new value. |
| A4 | GS20, Theorem 2, covers the full protocol, $`\{\mathcal F_{\mathrm{mult}},\mathcal F_{\mathrm{multVerify}}\}`$-hybrid. | `mainSecurity` is Theorem 2 for one batch, `ceremonyHybridSecurity` for all batches of a ceremony, and `treeHybridSecurity` for all ceremonies of a tree, in the same hybrid model. On the real network, a ceremony also has a PRSS setup. | `CeremonySecurityStatement`, for one ceremony on the real network, is stated and not proved. `treeCompleteness` (proved) covers the honest run only. |
| A5 | PRAWNS, Figure 3, line 8, requires $`t>(n+\lvert D\rvert)/2`$ for signers that do not coordinate. Its Section 1 explains that coordination removes it. | Line 8 fails for $n=2t-1$ with one corrupt operator. The first accepted round-1 request fixes the message of its key for all honest operators. | `stronglyUnforgeable` (proved) holds under rule 1 in place of line 8, also in a stopped run. The note assumes this agreement too. |
| A6 | The note signs for both setups and every $t$. Its trusted dealer has $n=3f+1$ and $t=2f+1$. | Each claim is for $n=2t-1$. | No claim covers the committee of the trusted dealer. |
| A7 | leanXMSS ends in the random-permutation model, with a random-oracle step for $q$ own calls of the adversary. | `stronglyUnforgeable` is in the random-oracle model. | The claim (proved) is at the level of the leanXMSS step `leanXmss_rom_adversary_bound`, whose bound is $(q+2^{10}-1)/2^{127}$. |
| A8 | leanXMSS has one model of Keccak for all claims. | Setup claims fix $\mathrm{Th}$, which the MPC computes by a circuit. Signing has $\mathrm{Th}$ in the random oracle. | No theorem connects them. The step is the random-oracle heuristic for Keccak. `dealerTreeCorrectness` (proved) links the trees for the fixed $\mathrm{Th}$, under `CircuitsCompute`. |

## Table B.2

### The adaptations of GS20

| B.2 | Source | Here | Reason | Proved claim |
| --- | --- | --- | --- | --- |
| B1 | Shamir sharing. | Replicated sharing [CDI05]. The check also compares hash digests of the copies. | Note's choice | `multVerifySecurity`, `mainSecurity`, with birthday terms |
| B2 | Protocol 8 uses $`\mathcal F_{\mathrm{doubleRand}}`$ (Lemmas 4, 5). Lemma 11 has $`\mathcal F_{\mathrm{coin}}`$, $`\mathcal F_{\mathrm{mult}}`$, $`\mathcal F_{\mathrm{extendMult}}`$. Protocol 15 also calls $`\mathcal F_{\mathrm{rand}}`$. | A local product and a reshare on $`\mathcal F_{\mathrm{rand}}`$ outputs (`mulRep`, `reshare`). In the last step of the check, length-one $`\mathcal F_{\mathrm{extendMult}}`$ replaces $`\mathcal F_{\mathrm{mult}}`$. The PRSS streams from dealt keys give the $`\mathcal F_{\mathrm{rand}}`$ outputs. | Replicated sharing | `multSecurity`, `extendMultSecurity`, `multVerifySecurity`, in their hybrid models ([mpc-layer.md](./mpc-layer.md)). `prssRandSecurity`. `prssRealRandSecurity` joins it to the PRSS setup with a direct proof and no composition theorem ([mpc-layer.md](./mpc-layer.md)). |
| B3 | Powers of one coin (Protocol 13). Halving by Protocol 14. | Products of $d$ coins and public bit weights $x^j$. The first seven halving steps differ, still of degree 2. | Performance | `multVerifySecurity`, for weights independent over $`\mathbb F_2`$ and any basis |
| B4 | Each challenge is a $`\mathcal F_{\mathrm{coin}}`$ value. Protocol 12 aborts on a challenge in $[m]$. | $H$ expands a hash of two $`\mathcal F_{\mathrm{coin}}`$ values (`coinKey`, `expand`). A halving challenge is the first expanded value outside $`\{0,1\}`$ among at most $2^{64}$ (`challenge`). | Fewer openings | `multVerifySecurity` with $2^{128}-2$, `multVerifyCompleteness` with `abortErrorOf` |
| B5 | Arithmetic circuits over $\mathbb F$ with $`\lvert\mathbb F\rvert\ge n+1`$ and random gates, and an extension field for the check. | Layered Boolean circuits of products and sums of wires and a constant. No random gate. The check field has the role of the extension field. | Keccak on bits | `mainSecurity`, for every circuit list |
| B6 | Clients give inputs and get outputs. The adversary gets corrupt-client outputs (Protocol 19, Functionality 18). | No client, pre-shared inputs. A batch (`runJobs`) reshares the outputs, checks every tuple and opens them to all, the adversary too. | Public outputs | `mainSecurity`, `mainCompleteness`, for one batch in their hybrid model. `ceremonyHybridSecurity`, for all batches of a ceremony |

### The adaptations of the note, PRAWNS and leanXMSS

| B.2 | Source | Here | Reason | Proved claim |
| --- | --- | --- | --- | --- |
| B7 | The note has a commit and a reveal. | One more round, the echo, compares a hash of $P$ and a hash of the shared seeds. | Seed agreement | `seedGenSecurity`, `seedGenCompleteness` |
| B8 | The note has no commitment to the randomizer value and no round-1 check. | The ceremony of a bottom tree opens a commitment $c_e$ to each randomizer value. Round 2 checks the sum of the round-1 parts against it. | Fixed randomizer value | `stronglyUnforgeable`, `signingCorrectness`, with $c_e$ from the dealer |
| B9 | $\mathsf{OSign}$ (PRAWNS, Figure 3) has one round and one request for each party. | Two rounds (`TsigQuery`) as in the note, Section 2.3, with quorum input as PRAWNS, Section 4, allows. Same-message repeats help the forger. | Randomizer round | `stronglyUnforgeable` |
| B10 | $\mathsf{OCorrupt}$ of PRAWNS has no limit. Line 7 rejects a forgery when $`\lvert D\cup Q[m]\rvert\ge t`$. | $\mathsf{OCorrupt}$ stops at $t-1$ operators, as in the note. A forgery also wins when it differs from the signature of the dealer, which is strong unforgeability. | Note's limit | `stronglyUnforgeable` |
| B11 | PRAWNS gives the forger the public key and the key of the combiner. | Public key, top tree, and on request a bottom tree with the opened randomizer value of its top key. | leanXMSS trees | `stronglyUnforgeable` |
| B12 | leanXMSS has one signer with no state, separate limits for calls and signing requests, and the slack $2^{10}$. | Adaptive corruption, state, one budget for own calls and round-2 requests, two more terms, and the slack $2^{15}+384$. | Threshold game | `stronglyUnforgeable` |
| B13 | The note has one ceremony for each bottom tree, which also opens the signature of its root. | The signature is a second ceremony with its own PRSS setup, after the local search. | One protocol | `treeCompleteness`, for the honest run. `treeHybridSecurity`, in the hybrid model |
| B14 | The note defines the PRF and the masks with no tag. | Each use of $H$ except $\mathrm{Th}$ hashes its own tag of 32 bytes first. | Separate domains | `tprfSecurity`, `stronglyUnforgeable`, with one domain of $H$ for each use |

## Sources

- [CDI05] Ronald Cramer, Ivan Damgard, and Yuval Ishai. Share conversion, pseudorandom secret-sharing and applications to secure computation. In Theory of Cryptography (TCC 2005), pages 342-362. Springer, 2005. [doi:10.1007/978-3-540-30576-7_19](https://doi.org/10.1007/978-3-540-30576-7_19).
- [GL05] Shafi Goldwasser and Yehuda Lindell. Secure multi-party computation without agreement. Journal of Cryptology, 18(3):247-287, 2005. [doi:10.1007/s00145-005-0319-z](https://doi.org/10.1007/s00145-005-0319-z).
- [GS20] Vipul Goyal and Yifan Song. Malicious security comes free in honest-majority MPC. Cryptology ePrint Archive, Paper 2020/134, 2020. <https://eprint.iacr.org/2020/134>.
- [BBD+26] Dan Boneh, Benedikt Bunz, Justin D., Yavor Litchev, and Kamilla Nazirkhanova. PRAWNS: Threshold hash-based signatures from threshold PRFs. Cryptology ePrint Archive, Paper 2026/2142, 2026. <https://eprint.iacr.org/2026/2142>.
- [lea26] leanEthereum. leanVM. Software repository, 2026. The Lean proof of leanXMSS, with its SUF-CMA and leanXMSS statements, at the revision of the dependency manifest. <https://github.com/leanEthereum/leanVM>.
- [Wam26] Tom Wambsgans. leanXMSS candidate (WIP). Note, 2026. A copy is in the repository at `doc/leanXMSS.pdf`. <https://github.com/TomWambsgans/sphincs.art/blob/9a528527d2d0ea41d2b3b322d2548c0828569a6d/leanXMSS.tex>.
