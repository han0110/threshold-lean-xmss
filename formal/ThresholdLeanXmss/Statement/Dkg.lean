import ThresholdLeanXmss.Statement.DkgGame
import ThresholdLeanXmss.Statement.DkgErrors

/-!
# The claims of the setup

The three claims of the setup by DKG, on the games of `DkgGame.lean`, with the error terms of
`DkgErrors.lean`. A claim holds for each `prims` with circuits that compute `prims.Th`.

* `DkgSecurity` is the security preservation of Gurkan and others, Definition 8. A forger against
  the signing game with the real setup gives a forger against `tsigGame`, which has the trusted
  dealer.
* `DkgCorrectness` bounds inconsistent seeds and wrong outputs of a tree against the adversary.
* `DkgCompleteness` bounds the abort of an honest run and its distance to `dealerKeyGen`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The precondition on the circuits -/

/-- The circuits compute the jobs of leanXMSS, namely chain steps and the commitment, with the fixed
function `Th`, on every job with the number of points that its kind takes. -/
def CircuitsCompute (Th : HashInput → HashOutput) : Prop :=
  ∀ (parameter : PublicParameter) (job : Job) (F : Point → Digest), job.points.length = job.kind.arity →
    (circuits parameter job.kind).eval ((job.points.map F).flatMap bitsOfDigest) =
      referenceJob (m := Id) (fun oa => evalTh Th oa) F parameter job

/-! ## The claims -/

/-- Security preservation of the real setup (Gurkan and others, ePrint 2021/005, Definition 8). For
each static coalition `D` and each adversary `A` of budget `q`, the forger `reduction prims.aes D A`
of `tsigGame` has cost at most `q + dkgOverhead C` on every path. `A` wins `dkgTsigGame` at most
`dkgError C q` plus the PRF advantage of the streams more often than the forger wins `tsigGame`.
The claim holds for each `prims` with circuits that compute `prims.Th`. `A` keeps its state from the
setup into the signing phase, as the text after Definition 8 asks.

The reduction is fixed before `prims` and reads only `prims.aes` from it. It can depend on the
circuits, so it can evaluate the fixed `Th` through the circuits with no oracle cost. Its only limit
is its query cost. It has no bound on its computation.

The claim adapts Definition 8 in these points.

* The forger is explicit, as in the proofs of Lemmas 3 to 5 of the paper (Appendix C). Definition 8
  has the same adversary on both sides.
* The bound is a fixed function of `q`, the forger has a cost bound, and the bound has the PRF
  advantage of the streams. Definition 8 has a negligible term and no cost. No source.
* The game is a threshold game. The honest operators sign with their own key shares, and the bottom
  trees are made during the signing phase. The paper has only games with one key. No source.
* The coalition of the setup is static, as the paper assumes. `tsigGame` has adaptive corruption.
  No game of the paper has a corruption oracle, so this mix has no source.
* The abort is selective, and each honest operator acts on what it holds. Definition 8 has no
  abort. No source.
* `Th` is a fixed function, and the circuits compute it. The paper uses a programmable random
  oracle. No source.
* Each tree has at most `runLimit` runs, and each run is atomic. No source.
* Each operator keeps the first output of its runs of a tree. The top tree runs again while an
  honest operator has no top tree, and the first signing request on a bottom tree ends its runs.
  No source.
* The public key and the trees of the win test are those of the first honest operator that holds
  them (`topHolder`, `canonicalDealt`). No source.
* The adversary and the forger are bounded only by their queries, with no bound on their
  computation. The paper takes PPT adversaries. No source.
* The network has private authenticated links and no broadcast channel, as in GS20, Section 3.1.
  Gurkan and others assume a broadcast channel. -/
def DkgSecurity (reduction : Aes → C.Coalition → DkgTsigAdversary C E → TsigAdversary C) : Prop :=
  0 < settings.batchSize → ∀ prims : Primitives, CircuitsCompute circuits prims.Th →
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
      (∀ pk top, QueryCostAtMost (reduction prims.aes D A pk top) adversaryCost (q + dkgOverhead runLimit C)) ∧
        accepts prims (dkgTsigGame K circuits settings runLimit D A) ≤
          accepts prims (tsigGame (reduction prims.aes D A)) + dkgError (E := E) circuits settings runLimit C q +
            streamAdvantage prims D (dkgTsigGame K circuits settings runLimit D A)

/-- Correctness with selective abort of the real setup. For each static coalition `D` and each
adversary `A` of budget `q`, two honest operators hold inconsistent seeds, or an honest operator ends
a run of a tree with an output that is not `referenceTree` on the seeds of the game, with a
probability that `dkgCorrectnessError C q` plus the PRF advantage of the streams bounds. An abort is
no win. The claim holds for each `prims` with circuits that compute `prims.Th`.

Its nearest model is the first clause of robustness (Gurkan and others, Definition 6), by which all
honest parties agree on the public key. The claim adapts that clause in these points.

* Consistent seeds take the place of one public key, and each output of a tree must be the reference
  output. The paper has no game for a protocol that runs after the key generation. No source.
* An abort is no win, so the claim allows a selective abort. Definition 6 has no abort. No source.
* The bound is a fixed function of `q` with the PRF advantage of the streams. The paper states no
  error. No source.
* The claim omits the second clause of Definition 6, by which `t + 1` honest shares reconstruct the
  secret key of the public key. No source.
* The coalition is static, as the paper assumes.
* `Th` is a fixed function. No source.
* Each tree has at most `runLimit` runs, and each run is atomic. No source.
* Each operator keeps the first output of its runs of a tree, and the runs of a tree stop as in
  `DkgSecurity`. No source.
* The seeds of the game are those of the first honest holder of each term (`gameSeeds`), and the
  reference output uses them. No source.
* The adversary is bounded only by its queries, with no bound on its computation. The paper takes
  PPT adversaries. No source.
* The network has private authenticated links and no broadcast channel, as in GS20, Section 3.1.
  Gurkan and others assume a broadcast channel. -/
def DkgCorrectness : Prop :=
  0 < settings.batchSize → 0 < runLimit → ∀ prims : Primitives, CircuitsCompute circuits prims.Th →
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
      accepts prims (dkgTreeGame K circuits settings runLimit D A) ≤
        dkgCorrectnessError (E := E) circuits settings runLimit C q +
          streamAdvantage prims D (dkgTreeGame K circuits settings runLimit D A)

/-- Completeness of the real setup. The claim is about an honest run with no corrupt operator, and
about one bottom tree `b` at a time. The run makes the seeds, at most `runLimit` runs of the top tree
and at most `runLimit` runs of bottom tree `b`. It stops the runs of a tree when each operator holds
an output of it. The probability that some operator lacks its keys, the top tree
or bottom tree `b` is at most `dkgAbortError C b`. The claim compares the outputs of all operators
with the outputs of `dealerKeyGen`, and their distance is at most `dkgCompletenessError C b`. The
claim holds for each `prims` with circuits that compute `prims.Th`.

No definition of GS20 or of Gurkan and others is its model. GS20 states no completeness lemma, and
security with abort alone allows a protocol that always aborts. The bound on the abort has the form
of Lemmas 1 and 2 of Gurkan and others, a bound on the probability that an honest party ends with no
output. The distance to `dealerKeyGen` has no source.

The claim is about an honest run only. It is not robustness under faults. A corrupt operator can
make each honest operator abort, and no claim excludes that. Each operator keeps the first output of
its runs of a tree, as in `DkgSecurity`. No source. -/
def DkgCompleteness : Prop :=
  0 < settings.batchSize → 0 < runLimit → ∀ prims : Primitives, CircuitsCompute circuits prims.Th →
    ∀ b : Fin (2 ^ layerHeight),
      (Pr{let r ← runWorld prims (honestDkg K circuits settings runLimit b)}[∃ i,
          (r.1 i).1 = none ∨ (r.1 i).2.1 = none ∨ (r.1 i).2.2 = none]).toReal ≤
          dkgAbortError (E := E) circuits settings C b ∧
        letI : MeasurableSpace (SetupOutputs C) := ⊤
        measureTVDist (Prod.fst <$> runWorld prims (honestDkg K circuits settings runLimit b))
            (Prod.fst <$> runWorld prims (dealerDkg b)) ≤
          dkgCompletenessError (E := E) circuits settings C b

end ThresholdLeanXmss
