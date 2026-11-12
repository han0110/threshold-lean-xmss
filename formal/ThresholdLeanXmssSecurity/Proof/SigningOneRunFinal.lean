import ThresholdLeanXmssSecurity.Proof.SigningOneRun
import ThresholdLeanXmssSecurity.Proof.SigningTopRows

/-!
# The signing assembly on one run with the cached-base trigger

This module tests the cached-base trigger proposed as the first trigger choice of
`SigningR1Fixed` and `SigningOneRun`. The support counterexample refutes that proposed
trigger, not the actual `cachedExtra` trigger of `SigningOneRun`. The module holds no
Lean statement. The arguments are on the support, not Lean proofs, as in `SigningR1Fixed` and
`SigningOneRun`.

## The trigger

The grind of key `e` runs once, at the first world call after which three things are cached.

* All PRF entries `.prf (seeds T) (.randomizer bottomLayer e)` (`RandomizerCached`).
* The bound message `m` of `e` (`bound e`).
* The base answer, the answer of `H` at `randomizerInput P bottomLayer e ρ m` with
  `ρ = cachedRandomizer seeds cache e`.

The three conditions only grow, so the trigger fires at most once for each key. One call can make
the conditions true for many keys (a `.tree b` call caches the PRF entries of all keys of `b`), so
the trigger runs one grind for each of them.

## The two known counterexamples

* `SigningR1Fixed`. The forger asks the base input with a guess `ρ'` and the trials, then
  `.tree (treeOf e)`, then round 1 on `m`. After round 1 all three conditions hold, because the
  guess is the true `ρ`. The grind runs and meets the cached selection, so the flag of `e` in
  `CachedSelectionAt` rises. The counterexample fails.
* `SigningOneRun`. The forger asks a partial round 1 on `m`, then the base input with a guess
  `ρ'` and the trials, then `.tree (treeOf e)`. After the `.tree` call all three conditions hold.
  The grind meets the cached selection, and the flag of `e` rises. The counterexample fails.

## A third counterexample

`FinalState.selected` replays `signCodeword` on the final cache with `answers = getD 0`. If the
base input is not cached at the end, the replay reads the base as `truncateHash 0`, a public
constant. The trials `messageDigest P bottomLayer e m (truncateHash 0 + k)` then need no hidden
value, and the forger can ask them itself.

1. Take any committee and no corruption. The forger asks `.tree (treeOf e)`. The ceremony caches
   all PRF entries at `e`, all chain starts at `e`, and `commitmentInput P e ρ` with the true `ρ`.
   It asks `randomizerInput` only at `topLayer`, so the bottom base input of `e` stays uncached.
2. The forger asks round 1 at `e` on `m`. This sets `bound e`. The forger asks no round 2, and it
   never asks `H` at `randomizerInput P bottomLayer e ρ m`. Only `signCodeword` asks that input,
   and only round 2 and `honestSignature` run it. So the base answer is never cached, and the
   trigger never fires at `e`.
3. The forger asks the encoding inputs of `e` and `m` at the randomness `truncateHash 0 + k` for
   `k = 0, 1, ...` up to the first codeword `k*`. It then asks a partner `(m', r')` with the same
   digest. Take a support point where these answers hold.
4. The forger outputs a forgery at `e` on `(m', r')` with guessed chain values that verify, as in
   step 4 of the `SigningR1Fixed` counterexample. It asks no PRF or mask entry, so the flag stays
   false. No operator released chain parts at `e`, so `tsigFinish` does not run
   `honestSignature`, and the base input stays uncached through the end.
5. The rows on the split run are as follows.
   * `BottomPartnerCase` holds. The replay opens `c_e` with the cached `ρ`, reads the base as
     `truncateHash 0`, and selects `(m, truncateHash 0 + k*)`, which differs from `(m', r')` and
     has the same digest.
   * `R1HitRow` and `CachedSelectionAt` are false. Only an extra call installs a target or raises
     the flag, and no grind ran at `e`.
   * `AlternativeCommitment` is false. The cache holds only the canonical commitment input of `e`.
   * `TrueOpeningHit` is false. The forger asks only encoding inputs (tag `12`), and
     `hiddenCandidate` matches none of them, so the candidate log is empty.
   * `ForgedStartAbsent` is false. Step 1 caches the bottom chain starts, and the setup caches the
     top chain starts.

So `R1Link` of `SigningOneRun`, with the true-opening disjunct, is false on the run with this
trigger. The guess of the partner costs `2^-128` for each call, so this refutes only the support
form of `R1Link`. It does not refute `PartnerCrossing` or the numerical bound.

## Trigger choices

* The trigger asks the base itself. At the first world call after which the PRF entries and the
  bound message of `e` are cached, the extra call asks `H` at the base input and then grinds.
  `hashLaw_eagerWorld` and `potStep_monitoredGame` hold for each extra call, so the eager law and
  the R1 bound stay free. On the eager cache the replay then reads the true base, and a partner of
  the eager selection is an R1 hit (a pending digest at the install, or a later query) or a cached
  selection. The risk is in `PartnerTransfer`. The lazy row of step 5 selects from the default
  base, so it has no image on the eager cache, and the transfer must pay it.
* A separate row for a selection from a default base, as `AbsentRow` is for an absent chain start.
  It keeps that proposed cached-base trigger, but the row needs a payer in the
  uncharged lane.
-/
