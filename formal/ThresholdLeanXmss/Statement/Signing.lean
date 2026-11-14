import ThresholdLeanXmss.Statement.Dkg

/-!
# The threshold PRF and the signing

The claims about the signing of `doc/sign.md`, at the level at which PRAWNS states them.
`Theorems.lean` holds the model.

The signing claim is strong unforgeability for the game of PRAWNS, Figure 3, in the form of leanXMSS.
That form is `StronglyUnforgeable` of leanVM, in `formal/Statement/SufCma.lean` at the pinned
revision `f5f3672f`. The game is not the generic game of leanXMSS, which has one signer with no state. It has adaptive corruption,
tree requests, two signing rounds of a quorum, and `breaksOneMessagePerKey`. The model and the bound
differ from leanXMSS in three points.

* `H` is a random oracle. leanXMSS has the random permutation of Keccak.
* One cost counts the own calls of `H` and `PRG` and the round-2 requests (`adversaryCost`). leanXMSS
  has a budget for the permutation calls and a limit for the signing requests.
* The bound has two more terms, for the hidden keys of the operators.

## Deviations from PRAWNS

* The `Eval'` of PRAWNS, Section 5.1, adds two masks under `k_ij` and `k_ji`. The note adds one mask
  under the common key `K_ij`, and the masks still cancel in pairs.
* The signing game takes the quorum, and `c_e` fixes the randomizer value (`doc/sign.md`, Section
  4). `OSign` has two rounds.
* The signing game drops line 8 of PRAWNS, Figure 3, and takes `breaksOneMessagePerKey` in its place
  (`doc/sign.md`, Section 4).
* The win test `forgeryWins` gives strong unforgeability, which goes beyond PRAWNS.
* PRAWNS lets the adversary choose `n` and `t`. Here the committee is a parameter of each claim.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-! ## The threshold PRF -/

/-- The game `G^tprf` of PRAWNS, Figure 1, with `KeyGen'` of PRAWNS, Section 5.1. -/
def tprfGame (A : TprfAdversary C) (b : Bool) : OracleComp (WorldSpec C) Bool := do
  let (_, seeds, keys) ← free (liftComp (prawnsKeyGen (C := C)) _)
  let forward : QueryImpl (LocalSpec C) (StateT (TprfState C) (OracleComp (WorldSpec C))) :=
    fun t => StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))
  (simulateQ (forward + tprfOracles keys seeds b) A : StateT (TprfState C) (OracleComp (WorldSpec C)) Bool).run'
    ⟨∅, fun _ _ => ∅, ∅, fun _ => none⟩

/-- `Adv^tprf`, PRAWNS, Definition 2.2. -/
def tprfAdvantage (A : TprfAdversary C) : ℝ :=
  |accepts prims (tprfGame A false) - accepts prims (tprfGame A true)|

/-- The error of Theorem 5.1 with `F(k, x) = H16(k ‖ x)` in the random-oracle model, for `q`
counted calls. PRAWNS bounds it by `2 C(n, t - 1) ε_F`, which gives `2 C(n, t - 1) q / 2^256`. The
masks add `n² q / 2^256` for the guess of a hidden pair key. Honest calls are free, so two of the
`C(n, t - 1) + n²` keys may also collide. -/
def tprfError (C : Committee) (q : ℕ) : ℝ :=
  ((2 * C.n.choose (C.t - 1) + C.n ^ 2) * q + (C.n.choose (C.t - 1) + C.n ^ 2) ^ 2 : ℕ) / 2 ^ 256

/-- `Combine'` of the parts of every quorum gives `F(msk, x)` (PRAWNS, Definition 2.1). -/
def TprfCorrectnessStatement (C : Committee) : Prop :=
  ∀ (J : C.Quorum) (x : Point) (ec : Message), ∀ r ∈ support (runWorld prims (tprfCorrectnessRun J x ec)), r.1 = true

/-- The threshold PRF is adaptively secure (PRAWNS, Definition 2.2 and Theorem 5.1). -/
def TprfSecurityStatement (C : Committee) : Prop :=
  ∀ (A : TprfAdversary C) (q : ℕ),
    IsQueryBoundP A (fun t => Sum.elim Counted (fun _ => False) t) q →
    tprfAdvantage prims A ≤ tprfError C q

/-! ## The signing game -/

/-- The game `G^tsig` of PRAWNS, Figure 3. -/
def tsigGame (A : TsigAdversary C) : OracleComp (WorldSpec C) Bool := do
  let some dealt ← dealerKeyGen | pure false
  (·.1) <$> tsigGameWith worldRoles dealt A

/-- `Adv^tsig`, PRAWNS, Definition 3.2, in the signing world. -/
def tsigAdvantage (A : TsigAdversary C) : ℝ := signingAccepts prims (tsigGame A)

/-- The own cost of the adversary of the signing game, the forger. A call of `H` or of `PRG` costs
one, and a round-2 request costs one. Private sampling, a corruption, a tree request and a round-1
request cost nothing. -/
def adversaryCost : (LocalSpec C + TsigSpec C).Domain → ℕ
  | .inl (.inr _) => 1
  | .inr (.round2 ..) => 1
  | _ => 0

/-! ## The claims of the signing -/

/-- An honest quorum fails with probability at most `2 (1 - p)^L`, for the search of the top
signature in `KeyGen` and the search of the signature. Every signature that it outputs verifies
(PRAWNS, Section 3.1, honest run). -/
def SigningCorrectnessStatement (C : Committee) : Prop :=
  ∀ (J : C.Quorum) (e : KeyIndex) (m : Message),
    (∀ r ∈ support (runWorld prims (honestSigning J e m)), r.1 ≠ some false) ∧
      (Pr{let r ← runWorld prims (honestSigning J e m)}[r.1 = none]).toReal ≤ 2 * searchFailure

/-- The probability that one of `q` calls hits the input of a hidden key, namely a term seed or a
pair key, of the `C(n, t - 1) + n²` keys. Each call names one key, which is uniform on 256 bits. -/
def seedHitError (C : Committee) (q : ℕ) : ℝ :=
  ((C.n.choose (C.t - 1) + C.n ^ 2) * q : ℕ) / 2 ^ 256

/-- The probability that two of the `C(n, t - 1) + n²` keys are equal. Equal term seeds cancel in
`F`, and a hidden key equal to a corrupt key is known. -/
def seedCollisionError (C : Committee) : ℝ :=
  ((C.n.choose (C.t - 1) + C.n ^ 2) ^ 2 : ℕ) / 2 ^ 256

/-- `securityBits` bits of strong unforgeability with adaptive corruption (PRAWNS, Definition 3.2),
in the random-oracle model. A forger with own cost at most `q` on every path, whatever the oracles
answer (`QueryCostAtMost`), wins `tsigGame` with probability at most
`(q + slack) / 2 ^ securityBits` plus the two terms of the hidden keys.

* `q` counts the own calls of the forger to `H` and to `PRG` and its round-2 requests (`adversaryCost`).
  A rejected round-2 request counts too. The calls of the dealer, of the honest operators and of the
  verification are calls of the game, and `q` does not count them.
* `slack` is a fixed part of the bound. It pays the security loss from the calls that `q` does not
  count. It does not bound the number of those calls.
* At most `t - 1` corrupt operators leave the seed of at least one term and the pair keys of the
  honest pairs hidden. `seedHitError` pays a call on such a key, and `seedCollisionError` two equal
  keys. Otherwise each unopened `F(x)` is a fresh uniform value, which covers `ρ_e` before round 1
  and the chain starts. Each mask under a hidden pair key is fresh too.
* The game has one coordination assumption, `breaksOneMessagePerKey`. Honest operators sign at most
  one message for each key over all quorums. The game enforces it. The PoC has the exchange
  of acknowledgements of `doc/sign.md` 4.1 for it, and a deployment must enforce it too. -/
def StronglyUnforgeable (C : Committee) (slack securityBits : ℕ) : Prop :=
  ∀ q, ∀ A : TsigAdversary C, (∀ pk top, QueryCostAtMost (A pk top) adversaryCost q) →
    tsigAdvantage prims A ≤ (q + slack) / 2 ^ securityBits + seedHitError C q + seedCollisionError C

/-- The fixed slack of `ThresholdLeanXmssStronglyUnforgeable`, in calls. A call costs two units of
`2^-128`, so the slack is `2 ^ 16 + 2 * 384` units.

* `2 ^ 16` units pay the first read of each of the `2 ^ 16` top keys.
* `384` units for each of the two units of a call pay the verification of the forgery. One
  verification makes at most `2 (1 + 58 * 3 + 1 + 16) = 384` calls of `H`. -/
def securitySlack : ℕ := 2 ^ 15 + 384

/-- Threshold leanXMSS in the random-oracle model. A forger that itself makes at most `q` calls of
`H` and `PRG` and round-2 requests forges with probability at most
`(q + 2^15 + 384) / 2^127 + N q / 2^256 + N² / 2^256`, where `N = C(n, t - 1) + n²` bounds the
number of hidden keys (`StronglyUnforgeable` at 127 bits).

A call costs two units of `2^-128`. One unit pays a call whose output hits an honest output at its
tweak. The other pays a call that meets a hidden honest input, namely a chain value below an opened
position or `ρ_e` before round 1, or the output of a digest that a later search selects. -/
abbrev ThresholdLeanXmssStronglyUnforgeable (C : Committee) : Prop :=
  StronglyUnforgeable prims C securitySlack 127

end ThresholdLeanXmss
