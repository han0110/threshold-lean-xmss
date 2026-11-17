# The MPC layer

This file holds the ceremony claims, the building blocks of GS20 [GS20], the PRSS setup and the PRSS streams [CDI05], which the security of a ceremony rests on. [statement.tex](../statement.tex) is the guide, and its Appendix C gives these claims in one table.

Section 2 of `statement.tex` defines `DealtInputs`. A ceremony evaluates one of the public job lists `topJobs`, `bottomJobs` or `signJobs`. A signature ceremony continues the two counters of the MPC state, the round label and the batch tag, from the ceremony before it. For a check of GS20 with $d$ random coins and $R$ halving steps, which shorten the checked vector of products, define

```math
e(d,R,q)=\frac{d+2(R+1)}{2^{128}-2}+\frac{(R+2)q}{2^{256}},\quad h(R,q)=\frac{(q+2n\binom n{t-1}+R+2)^2}{2^{256}}.
```

These are `checkErrorOf` and `checkHashError`. The second term of $e$ is the cost of a hash call that hits the key input of a coin before the coin opens. The key input holds two field elements that are secret until then. The error $\mathsf{ceremonyCheckError}$ of a ceremony adds one $e$ for each batch. Each $e$ uses the maximum coin count and halving count over all batches of all ceremonies. An honest check can also abort. The next formulas give the failure probability of its coins and its abort error.

```math
\mathsf{coinFailure}(R)=\mathsf{sliceBits}/2^{128}+(R+1)(2/2^{128})^{2^{64}},\quad \mathsf{abortErrorOf}(R)=\mathsf{coinFailure}(R)+(R+2)^2/2^{257}.
```

## One ceremony

The ceremony security in the hybrid model (`CeremonyHybridSecurityStatement`) is this claim. Assume $\mathsf{batchSize}>0$, `DealtInputs` and a static coalition. Take every circuit family, every start of the labels and tags, and each of the three job lists. Then in the $`\{\mathcal F_{\mathrm{mult}},\mathcal F_{\mathrm{multVerify}}\}`$ hybrid, one ceremony securely computes $`\mathcal F_{\mathrm{ceremony}}`$ with selective abort. The error is $`(q+B\cdot 2n\binom n{t-1})^2/2^{256}`$, where $B$ counts the batches of the job list. A simulator exists, with at most $q+\mathsf{hybridOverhead}$ counted calls. This is the claim of `mainSecurity` for all batches of a ceremony (GS20, Theorem 2). The multiplication, the rerandomization and the check are ideal, and the ceremony has no PRSS setup. It is no claim for the real network, for the PRSS or for the meaning of the circuits. $`\mathcal F_{\mathrm{ceremony}}`$ leaks $P$ and the outputs of all jobs, also of batches that the real run does not reach. After a partial abort before the last batch, the next functionality call does not run, and no honest operator gets an output. A partial abort at the last opening can leave some honest operators with outputs.

The ceremony security on the real network (`CeremonySecurityStatement`) is stated and not proved. Assume $\mathsf{batchSize}>0$ and `DealtInputs`. Take every circuit family, every start of the labels and tags, and each of the three job lists. Then one ceremony would securely compute $`\mathcal F_{\mathrm{ceremony}}`$ with selective abort against its own static coalition. The job list and the encoding of a signature ceremony are fixed public inputs. The functionality $`\mathcal F_{\mathrm{ceremony}}`$ computes the jobs in the clear on the seeds and leaks $P$ and every output. The simulator is the fixed ceremony simulator, and the error is

```math
\mathsf{ceremonyCheckError}+ (q+s_{\mathrm{ceremony}})^2/2^{256}+k^2/2^{129}+\operatorname{Adv}^{\rm prf}_{\mathsf{hiddenStreams}}(\mathsf{prgReduction}).
```

In the last term, the reduction takes the real execution of the ceremony and its distinguisher, exactly as the Lean declaration states. The number $`s_{\mathrm{ceremony}}=\mathsf{ceremonySecrets}`$ counts the secret hash inputs of the honest operators. A counted call that hits one of them is a part of the error. The number $`k=\binom n{t-1}+\binom n2`$ counts the PRSS keys that are hashed to AES keys. The terms count the batches of this one job list. This claim is no field of the bundle.

## The building blocks of GS20

The building-block claims adapt the lemmas of GS20 to one batch of the model. These claims do not give the security of a ceremony on the real network, which is stated and not proved. The ideal functionality $`\mathcal F_{\mathrm{rand}}`$ gives random sharings, and the PRSS replaces it in a ceremony. "Up to an additive attack" means that the adversary can add offsets of its choice to the shares of a product. A tuple holds shared vectors of two factors and of their claimed products. In the building-block claims, $d$ and $R$ are the coin and halving counts for the number of input tuples. GS20 gives no completeness lemma. A source marked "honest run" in Appendix A of `statement.tex` gives only a protocol. Each claim of GS20 holds on its valid inputs in this table.

| Valid inputs | Requirement |
| --- | --- |
| `SameCount` | The honest operators agree on the count. |
| `ShamirInputs` | Honest operators agree on entry kinds and lengths. The honest shares of each Shamir entry lie on polynomials of degree at most $t-1$. |
| `TupleInputs` | The honest operators have equal counts and modes. The honest holders of a term agree on all its copies whenever they agree on the values that corrupt operators fill. |
| `CorrectTuples` | Every tuple is a product, with each term from its first holder. |
| `MainInputs` | The honest operators hold one sharing for each job. All terms of a job have one length at their honest holders and are empty at the other honest operators. All holders of a term hold the same value, corrupt holders included. |

The coin claim (`CoinSecurityStatement`) is this. In the $`\mathcal F_{\mathrm{rand}}`$ hybrid and on `SameCount`, the coin protocol securely computes $`\mathcal F_{\mathrm{coin}}`$ with selective abort and error $0$ (GS20, Lemma 3).

The multiplication claim (`MultSecurityStatement`) is this. In the $`\mathcal F_{\mathrm{rand}}`$ hybrid, on `SameCount`, in every reshare mode, multiplication securely computes $`\mathcal F_{\mathrm{mult}}`$ up to an additive attack, with selective abort and error $0$ (GS20, Lemma 4).

The inner-product claim (`ExtendMultSecurityStatement`) is this. In the $`\mathcal F_{\mathrm{rand}}`$ hybrid and on `ShamirInputs`, the inner-product protocol securely computes $`\mathcal F_{\mathrm{extendMult}}`$ up to an additive attack, with selective abort and error $0$ (GS20, Lemma 5).

The claim on checking products (`MultVerifySecurityStatement`) is this. In the $`\{\mathcal F_{\mathrm{coin}},\mathcal F_{\mathrm{extendMult}},\mathcal F_{\mathrm{rand}}\}`$ hybrid, for each count list, on `TupleInputs`, the check with salted digests securely computes $`\mathcal F_{\mathrm{multVerify}}`$ with selective abort and error $e(d,R,q)+h(R,q)$ (GS20, Lemmas 8 to 11).

The claim on one batch (`MainSecurityStatement`) is this. In the $`\{\mathcal F_{\mathrm{mult}},\mathcal F_{\mathrm{multVerify}}\}`$ hybrid, for every mode and circuit list, on `MainInputs`, a batch securely computes $`\mathcal F_{\mathrm{main}}`$ with selective abort and error $`(q+2n\binom n{t-1})^2/2^{256}`$ (GS20, Theorem 2). The functionality $`\mathcal F_{\mathrm{main}}`$ evaluates the circuits of the batch and opens the outputs.

The honest coin claim (`CoinCompletenessStatement`) is this. In the $`\mathcal F_{\mathrm{rand}}`$ hybrid and on `SameCount`, an honest coin gives the output of $`\mathcal F_{\mathrm{coin}}`$ with error $0$ (GS20, Protocol 6).

The honest check claim (`MultVerifyCompletenessStatement`) is this. In the $`\{\mathcal F_{\mathrm{coin}},\mathcal F_{\mathrm{extendMult}},\mathcal F_{\mathrm{rand}}\}`$ hybrid, for each count list, on `TupleInputs` and `CorrectTuples`, an honest check accepts with error at most $\mathsf{abortErrorOf}(R)$ (GS20, Protocol 17).

The honest batch claim (`MainCompletenessStatement`) is this. In the $`\{\mathcal F_{\mathrm{mult}},\mathcal F_{\mathrm{multVerify}}\}`$ hybrid, for every mode and circuit list, on `MainInputs`, an honest batch gives the outputs of $`\mathcal F_{\mathrm{main}}`$ with error $0$ (GS20, Protocol 19).

## The PRSS setup

The PRSS setup claim (`PrssSetupSecurityStatement`) is this. Take a static coalition. Then on the real network, the PRSS setup of a ceremony securely computes the dealer $`\mathcal F_{\mathrm{prssKeys}}`$ of the PRSS keys with selective abort. The simulator is the fixed `prssSetupSimulator`. The ideal run makes at most $q+\mathsf{prssSetupOverhead}$ counted calls, and the error is $`(q+\mathsf{prssSetupSecrets})^2/2^{256}`$.

```math
\mathsf{prssSetupOverhead}=\binom n{t-1}+n^2,\quad \mathsf{prssSetupSecrets}=n\left(\binom n{t-1}+n\right)+\binom n{t-1}+\binom n2+n^2.
```

The overhead counts the programming queries of the simulator. It has at most one query for each term and one for each pair of a corrupt and an honest operator. The secrets count the honest points of $H$ that a counted call must not hit. They are the parts of each operator, the derived keys and the inputs of the hashes of the shared keys.

The protocol is the seed generation protocol with the phase of the PRSS setup. This phase samples a part of $P$, but it does not reveal it, derives no $P$ from it and does not hash it in the echo. The claim is for one setup from an empty hash cache. A bottom tree runs two setups, and the second starts from a cache with cells of the first. The claim does not cover the second setup. It does not join the setup to the building-block claims or to the PRSS streams claim.

No cited paper proves this setup. The setup argument and its bound are an adaptation of this project. Selective abort is security with abort and no fairness [GL05, Definition 5]. The simulator observes and programs $H$ as a local random oracle [CDG+18, Section 3]. It extracts the corrupt reveals from the observed calls, as in the proof of [CDG+18, Theorem 6]. CDI05, Section 4, takes the PRSS keys as a predistributed input and has no protocol that makes them.

## Random sharings from the PRSS

The claim on random sharings from the PRSS (`PrssRandSecurityStatement`) is this. Take a static coalition and PRSS keys from a trusted dealer $`\mathcal F_{\mathrm{prssKeys}}`$, who can leave an honest operator with no keys. Then for every start label and fixed public list of calls, the PRSS streams securely compute these $`\mathcal F_{\mathrm{rand}}`$ calls with selective abort. A simulator exists that does not program $H$, with at most $q+\mathsf{prssRandOverhead}$ counted calls. The error is $`k(q+k)/2^{256}+\operatorname{Adv}^{\rm prf}_{\mathsf{hiddenStreams}}(\mathsf{prgReduction})`$ for the $`k=\binom n{t-1}+\binom n2`$ PRSS keys. The source is CDI05, Sections 2 and 4, with predistributed keys. It differs in the pair keys, the hash to an AES key, and the use as replicated terms with no Shamir conversion. It covers neither the PRSS setup nor a join of the building blocks to the PRSS. It is not GS20, Lemma 1.

## One PRSS setup with its random sharings

The claim on one PRSS setup with its random sharings (`PrssRealRandSecurityStatement`) is this. Take a static coalition. Then on the real network, one PRSS setup and the `Rand` calls from its keys securely compute a fixed public list of $`\mathcal F_{\mathrm{rand}}`$ calls with selective abort, for every start label. The simulator is the fixed `prssRealRandSimulator`. It runs the setup code of the honest operators against the adversary and names the operators that end with keys. For each call it gives the streams under the keys that the coalition knows. It makes no programming query. The ideal run makes at most $q$ counted calls, because the simulator runs the honest code on the free copy of the oracle. With $`q'=q+n(\binom n{t-1}+n)`$ and the $k$ of the section before, the error is

```math
\frac{(q+\mathsf{prssSetupSecrets})^2}{2^{256}}+\frac{(q'+\mathsf{prssSetupSecrets})^2}{2^{257}}+\frac{k(q'+k)}{2^{256}}+\operatorname{Adv}^{\rm prf}_{\mathsf{hiddenStreams}}(\mathsf{prgReduction}).
```

The first term is for two honest operators that hold two keys for one term or one pair. The other two hash terms are for a counted call that hits a hidden key.

The claim is for one setup from an empty hash cache and one public list of calls. It joins the two claims before it and replaces neither of them. `prssRandSecurity` counts each call of its simulator, and this claim does not count the honest code that its simulator runs. It does not join the PRSS to the building blocks.

The papers get such a claim from the composition theorem [Can00, Theorem 5]. The Lean proof is direct. It bounds the event that two honest operators hold two keys with `prssSetupSecurity`. Outside that event, the streams are those of dealt keys.

## Sources

- [Can00] Ran Canetti. Security and composition of multiparty cryptographic protocols. Journal of Cryptology, 13(1):143-202, 2000. [doi:10.1007/s001459910006](https://doi.org/10.1007/s001459910006).
- [CDG+18] Jan Camenisch, Manu Drijvers, Tommaso Gagliardoni, Anja Lehmann, and Gregory Neven. The wonderful world of global random oracles. In Advances in Cryptology - EUROCRYPT 2018, pages 280-312. Springer, 2018. [doi:10.1007/978-3-319-78381-9_11](https://doi.org/10.1007/978-3-319-78381-9_11).
- [CDI05] Ronald Cramer, Ivan Damgard, and Yuval Ishai. Share conversion, pseudorandom secret-sharing and applications to secure computation. In Theory of Cryptography (TCC 2005), pages 342-362. Springer, 2005. [doi:10.1007/978-3-540-30576-7_19](https://doi.org/10.1007/978-3-540-30576-7_19).
- [GL05] Shafi Goldwasser and Yehuda Lindell. Secure multi-party computation without agreement. Journal of Cryptology, 18(3):247-287, 2005. [doi:10.1007/s00145-005-0319-z](https://doi.org/10.1007/s00145-005-0319-z).
- [GS20] Vipul Goyal and Yifan Song. Malicious security comes free in honest-majority MPC. Cryptology ePrint Archive, Paper 2020/134, 2020. <https://eprint.iacr.org/2020/134>.
