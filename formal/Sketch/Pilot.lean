import Sketch.Count
import ThresholdLeanXmssSecurity.Proof.CheckSplit
import ThresholdLeanXmssSecurity.Proof.Tree

/-!
# The pilot. The soundness of the check of one batch as a bad event

The pilot is the bad event "an honest operator accepts the check of a batch with a wrong tuple" in
the world `streamWorld`, where each stream under a hidden key is a random function. The check is the
real check `check` with `realCheckBuildingBlocks` on the PRSS keys of the ceremony, and its challenge
searches are the code of the game. The adversary plays the coalition through the rounds of the check.
The start is a pair of a hash cache and a cache of the hidden streams that earlier calls can leave.

* `pilotRun` is the check of one batch on the network, with each honest operator at the label `L` and
  the tag `tg` of the batch.
* `PilotCache` holds the premises on the hash cache. They are the challenge ledger `SoundCache`, the
  cover `DigestSaltsCovered` of the digest salts, and a bound and no collision of the history and
  digest cells. `pilotCache_empty` shows them for the empty cache.
* `StreamsFresh` says that the hidden streams of the honest keys have no cell at a label from `L`.
  `PrssKeysAgree` says that the honest holders of a key hold the same key.
* `PilotSound` is the case where the honest copies of the tuples agree, and `PilotSplit` is the case
  where they disagree. `PilotCheck` is the pilot. `pilotCheck_of_cases` gives it from the two cases.
* `pilotSoundError_sum` writes the errors of the coins of the library soundness, with `keys` earlier
  expansion keys, as the terms of `pilotSoundError`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity ENNReal

noncomputable section

namespace ThresholdLeanXmss.Sketch

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The game -/

/-- The context of operator `i` in a ceremony with the keys `keys i` and the PRSS keys `prss i`. -/
def pilotContext (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (i : C.Party) : Context C :=
  ⟨i, keys i, prss i⟩

/-- The real check of the tuples `x` of one batch on the network, with the adversary `net` from the
state `st`. Each honest operator starts the check at the label `L` and the tag `tg`, with the values
of its tuples as its running values. -/
def pilotRun (K : Constants C E) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (counts : List ℕ)
    (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State) :
    OracleComp (WorldSpec C) (net.State × (C.Party → Option Unit)) :=
  executePhase worldRoles D net noFunctionality (checkRounds counts.sum) st fun i =>
    (check K (pilotContext keys prss i) (realCheckBuildingBlocks K (pilotContext keys prss i)) (x i)).run'
      ⟨filledHistory K i (x i), L, tg⟩

/-- A wrong tuple. On the honest views of the tuples, a tuple has a position where `z` is not
`x * y`. -/
def WrongTuple (D : C.Coalition) (x : C.Party → List (Tuple C)) : Prop :=
  ∃ m < (firstInput (fun i => if i ∈ D.1 then none else some (x i))).length,
    ∃ g < (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).count,
      shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).z g -
        shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).x g *
          shareValue (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).y g ≠ 0

/-! ## The premises -/

/-- The premises on the hash cache at the start of the check.

* `SoundCache L cache seen keys`. Each cached input of `.coinKey` at a label from `L` is in `seen`,
  and each cached `.expand key idx` has `key ∈ keys` or is in `seen`.
* `DigestSaltsCovered cache salts`. The salt of each cached digest is in `salts`.
* The history and digest cells of the cache are at most `split`, with no two equal outputs. -/
def PilotCache (L : ℕ) (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput)
    (salts : Finset (List Bit)) (split : ℕ) : Prop :=
  SoundCache L cache seen keys ∧ DigestSaltsCovered cache salts ∧
    SplitCacheBound (splitRegionCache SplitHashDomain cache) split ∧
    ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache)

/-- The hidden streams of the honest keys are fresh from label `L`. For each honest operator and
each hidden term that it holds or hidden pair that it is in, the cache of the hidden streams has no
cell of its key at a label from `L`. -/
def StreamsFresh (D : C.Coalition) (L : ℕ) (prss : C.Party → PrssKeys C) (hidden : HiddenCache C) : Prop :=
  ∀ i, i ∉ D.1 → ∀ ρ, L ≤ ρ → ∀ idx position : ℕ,
    (∀ T, i ∈ C.holders T → Hidden D (.term T) →
      hidden ((.term T, (prss i).term T), ρ, idx, position) = none) ∧
    ∀ j (h : j ≠ i), Hidden D (.pair (C.pairOf i j (Ne.symm h))) →
      hidden ((.pair (C.pairOf i j (Ne.symm h)), (prss i).pair j), ρ, idx, position) = none

/-- The honest operators agree on the PRSS keys. Two honest holders of a term hold one key of it,
and the two ends of an honest pair hold one key of it. -/
def PrssKeysAgree (D : C.Coalition) (prss : C.Party → PrssKeys C) : Prop :=
  (∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T → (prss i).term T = (prss j).term T) ∧
    ∀ i j, i ∉ D.1 → j ∉ D.1 → i ≠ j → (prss i).pair j = (prss j).pair i

/-- The premises hold for the empty caches. -/
theorem pilotCache_empty (D : C.Coalition) (L : ℕ) (prss : C.Party → PrssKeys C) :
    PilotCache (C := C) L ∅ ∅ ∅ ∅ 0 ∧ StreamsFresh D L prss ∅ := by
  refine ⟨⟨SoundCache.of_covered L ∅ ∅ (fun _ h => (h rfl).elim), fun _ _ h => (h rfl).elim,
    ⟨∅, le_rfl, fun q h => ?_⟩, ?_⟩, fun _ _ _ _ _ _ => ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩
  · simp [splitRegionCache] at h
  · rintro ⟨a, b, v, w, _, ha, _, _⟩
    simp [splitRegionCache] at ha

/-! ## The errors -/

/-- The error of `digest_after_call_hide` in the step from the real check on drawn values to the
check in the hybrid model, with `salts` cached digest salts and no call after the check. -/
def pilotDigestError (C : Committee) (step salts count : ℕ) : ℝ :=
  ((C.terms.length * (salts + 4 * checkRounds count * step + (C.n + 1) * C.terms.length) : ℕ) : ℝ) / 2 ^ 256

/-- The error of the case with agreeing copies. `seen` counts the cached inputs that the check
charges one by one, `keys` the earlier expansion keys, and `step` the calls of each round of the
adversary. The first two terms are the soundness of GS20, Lemmas 8 to 10, with the coin-key
collisions, at the budget `seen + checkRounds count * step`. -/
def pilotSoundError (C : Committee) (count step seen keys salts : ℕ) : ℝ :=
  checkErrorOf (E := E) (coins count) (halvings count) (seen + checkRounds count * step) +
    soundHashError count (seen + checkRounds count * step + keys) +
    pilotDigestError C step salts count

/-- The error of the case with split copies, a collision of the history and digest cells. The
cache has at most `split` such cells, and the check adds at most `checkRounds count * step` calls
of the adversary and `termHashes C` honest cells. -/
def pilotSplitError (C : Committee) (count step split : ℕ) : ℝ :=
  splitRisk split (checkRounds count * step + termHashes C)

/-- The error of the pilot. -/
def pilotError (C : Committee) (count step seen keys salts split : ℕ) : ℝ :=
  pilotSoundError (E := E) C count step seen keys salts + pilotSplitError C count step split

omit [DecidableEq E] in
/-- The errors of the `halvings count + 2` coins of the soundness of the library, `soundError` of
`Proof/CheckSound.lean` with `keys` earlier expansion keys and the `halvings count + 2` keys of the
check, are the first two terms of `pilotSoundError`. It is `sound_error_sum` with the earlier keys. -/
theorem pilotSoundError_sum [SampleableType E] (K : Constants C E) (count q keys : ℕ) :
    soundError E q (keys + (halvings count + 2)) (coins count) +
      (halvings count + 1 : ℕ) * soundError E q (keys + (halvings count + 2)) 2 =
    ENNReal.ofReal (checkErrorOf (E := E) (coins count) (halvings count) q + soundHashError count (q + keys)) := by
  have hnonneg := add_nonneg (checkErrorOf_nonneg K (coins count) (halvings count) q)
    (soundHashError_nonneg count (q + keys))
  apply (ENNReal.toReal_eq_toReal_iff' (by
    exact ENNReal.add_ne_top.mpr ⟨soundError_ne_top K _ _ _, ENNReal.mul_ne_top (by simp) (soundError_ne_top K _ _ _)⟩)
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_add (soundError_ne_top K _ _ _) (ENNReal.mul_ne_top (by simp) (soundError_ne_top K _ _ _)),
    ENNReal.toReal_mul, soundError_toReal K, soundError_toReal K, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hnonneg]
  unfold checkErrorOf soundHashError
  push_cast
  ring

/-! ## The claims -/

variable (prims : Primitives)

/-- The outputs of `pilotRun` in `streamWorld`, from the hash cache `cache` and the cache `hidden`
of the hidden streams. -/
def pilotOutputs (K : Constants C E) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (counts : List ℕ)
    (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State) (cache : HashCache C)
    (hidden : HiddenCache C) : ProbComp (net.State × (C.Party → Option Unit)) :=
  StateT.run' (simulateQ (streamWorld prims D) (pilotRun K D net keys prss counts x L tg st)) (cache, hidden)

variable (K : Constants C E)

/-- The pilot in the case where the honest copies of the tuples agree. -/
def PilotSound : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ),
    (∀ st sent, IsQueryBoundP (net.round st sent) Counted step) →
    ∀ (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (counts : List ℕ)
      (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State) (cache : HashCache C)
      (hidden : HiddenCache C) (seen : Finset (Query C)) (expansionKeys : Finset HashOutput)
      (salts : Finset (List Bit)) (split : ℕ),
      TupleInputs K counts D x → WrongTuple D x →
      MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) →
      PrssKeysAgree D prss → StreamsFresh D L prss hidden →
      PilotCache L cache seen expansionKeys salts split →
      (Pr{let out ← pilotOutputs prims K D net keys prss counts x L tg st cache hidden}[∃ i, i ∉ D.1 ∧
          out.2 i = some ()]).toReal ≤
        pilotSoundError (E := E) C counts.sum step seen.card expansionKeys.card salts.card

/-- The pilot in the case where the honest copies of the tuples disagree. -/
def PilotSplit : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ),
    (∀ st sent, IsQueryBoundP (net.round st sent) Counted step) →
    ∀ (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (counts : List ℕ)
      (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State) (cache : HashCache C)
      (hidden : HiddenCache C) (seen : Finset (Query C)) (expansionKeys : Finset HashOutput)
      (salts : Finset (List Bit)) (split : ℕ),
      TupleInputs K counts D x →
      ¬ MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) →
      PrssKeysAgree D prss → StreamsFresh D L prss hidden →
      PilotCache L cache seen expansionKeys salts split →
      (Pr{let out ← pilotOutputs prims K D net keys prss counts x L tg st cache hidden}[∃ i, i ∉ D.1 ∧
          out.2 i = some ()]).toReal ≤
        pilotSplitError C counts.sum step split

/-- The pilot. In `streamWorld`, from a start that earlier calls can leave, an honest operator
accepts the real check of tuples with a wrong tuple with probability at most `pilotError`. -/
def PilotCheck : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ),
    (∀ st sent, IsQueryBoundP (net.round st sent) Counted step) →
    ∀ (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (counts : List ℕ)
      (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State) (cache : HashCache C)
      (hidden : HiddenCache C) (seen : Finset (Query C)) (expansionKeys : Finset HashOutput)
      (salts : Finset (List Bit)) (split : ℕ),
      TupleInputs K counts D x → WrongTuple D x →
      PrssKeysAgree D prss → StreamsFresh D L prss hidden →
      PilotCache L cache seen expansionKeys salts split →
      (Pr{let out ← pilotOutputs prims K D net keys prss counts x L tg st cache hidden}[∃ i, i ∉ D.1 ∧
          out.2 i = some ()]).toReal ≤
        pilotError (E := E) C counts.sum step seen.card expansionKeys.card salts.card split

omit [DecidableEq E] in
/-- The pilot follows from its two cases. -/
theorem pilotCheck_of_cases [SampleableType E] (sound : PilotSound prims K) (split : PilotSplit prims K) :
    PilotCheck prims K := by
  intro D net step hstep keys prss counts x L tg st cache hidden seen expansionKeys salts splitCells
    hx hwrong hagree hfresh hcache
  have hsound : 0 ≤ pilotSoundError (E := E) C counts.sum step seen.card expansionKeys.card salts.card :=
    add_nonneg (add_nonneg (checkErrorOf_nonneg K _ _ _) (soundHashError_nonneg _ _))
      (by unfold pilotDigestError; positivity)
  have hsplit : 0 ≤ pilotSplitError C counts.sum step splitCells := splitRisk_nonneg _ _
  unfold pilotError
  by_cases hcopies : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i))
  · exact (sound D net step hstep keys prss counts x L tg st cache hidden seen expansionKeys salts
      splitCells hx hwrong hcopies hagree hfresh hcache).trans (le_add_of_nonneg_right hsplit)
  · exact (split D net step hstep keys prss counts x L tg st cache hidden seen expansionKeys salts
      splitCells hx hcopies hagree hfresh hcache).trans (le_add_of_nonneg_left hsound)

end ThresholdLeanXmss.Sketch
