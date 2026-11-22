import ThresholdLeanXmss.Statement.DkgGame
import ThresholdLeanXmssSecurity.Proof.CheckSound
import ThresholdLeanXmssSecurity.Proof.CheckSplit
import ThresholdLeanXmssSecurity.Proof.StreamWorld

/-!
# The pilot

The pilot is the bad event that an honest operator accepts the check of a batch with a wrong tuple,
in the world `streamWorld`, where each stream under a hidden key is a lazy uniform table. `PilotSound`
and `PilotCheck` state its bound. The file also holds the count of the calls of `H` by class and the
sound induction of the check from a start cache with earlier keys (`checkSoundFrom`).
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

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

/-- The error of the hiding of the salted digests in the step from the real check on drawn values to the
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

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

/-! ## The classes -/

/-- A class of the domains of `H` and `PRG`. -/
inductive HashClass
  /-- The commitments, the derived keys and the echo hashes of the seed generation. -/
  | seedGen
  /-- The commitments, the derived keys and the echo hashes of a PRSS setup. -/
  | prssSetup
  /-- The stream keys and the calls of `PRG`. -/
  | stream
  /-- The running hashes and the salted digests of the check. -/
  | digest
  /-- The coin keys and the expanded values of the challenges of the check. -/
  | challenge
  /-- The copy hashes of `OpenRep`. -/
  | copy
  /-- The domains that the signing also uses, namely `Th` off the inputs of the MPC, the PRF and the
  masks. -/
  | signing
  deriving DecidableEq

/-- The class of the domains of a setup in `phase`. -/
def phaseClass : Phase → HashClass
  | .seedGen => .seedGen
  | .prss => .prssSetup

/-- The class of an input of `H`. -/
def queryClass {C : Committee} : Query C → HashClass
  | .hash _ => .signing
  | .prf .. => .signing
  | .mask .. => .signing
  | .commit phase .. => phaseClass phase
  | .derive phase .. => phaseClass phase
  | .sharedKeys phase _ => phaseClass phase
  | .copy _ => .copy
  | .history _ => .digest
  | .digest .. => .digest
  | .streamKey _ => .stream
  | .coinKey .. => .challenge
  | .expand .. => .challenge

variable {C : Committee}

/-- A call of a local computation in class `c`. Private sampling and `Th` on an input of the MPC
are in no class. -/
def InClass (c : HashClass) : (LocalSpec C).Domain → Prop
  | .inl _ => False
  | .inr (.inl (.hash input)) => ¬ MpcInput input ∧ c = .signing
  | .inr (.inl q) => queryClass q = c
  | .inr (.inr _) => c = .stream

/-- A counted call is in a class. -/
theorem exists_inClass {t : (LocalSpec C).Domain} (h : Counted t) : ∃ c, InClass c t := by
  rcases t with _ | q | _
  · exact h.elim
  · cases q <;> simp_all [InClass, Counted]
  · exact ⟨.stream, rfl⟩

/-- A call in a class costs one in `ownCost`. -/
theorem one_le_ownCost {c : HashClass} {t : (LocalSpec C).Domain} (h : InClass c t) :
    1 ≤ ownCost (C := C) t := by
  rcases t with _ | _
  · exact h.elim
  · exact le_rfl

/-- A call of `forge` in class `c`, namely a local call in class `c`. -/
def ForgeInClass {σ : Type} (c : HashClass) : (LocalSpec C + (TsigSpec C + StateSpec σ)).Domain → Prop
  | .inl t => InClass c t
  | .inr _ => False

/-- A call of `forge` in a class costs one in `forgeCost`. -/
theorem one_le_forgeCost {σ : Type} {c : HashClass} {t : (LocalSpec C + (TsigSpec C + StateSpec σ)).Domain}
    (h : ForgeInClass c t) : 1 ≤ forgeCost (C := C) t := by
  rcases t with (_ | _) | _
  · exact h.elim
  · exact le_rfl
  · exact h.elim

/-! ## A cost bound gives a count -/

/-- A cost bound gives a count of the calls of `p` when each call of `p` costs at least one. -/
theorem isQueryBoundP_of_queryCostAtMost {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {oa : OracleComp spec α} {cost : ι → ℕ} {p : ι → Prop} [DecidablePred p] {n : ℕ}
    (h : QueryCostAtMost oa cost n) (hp : ∀ t, p t → 1 ≤ cost t) : IsQueryBoundP oa p n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [QueryCostAtMost, isQueryBound_query_bind_iff] at h
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨?_, fun u => (ih u (h.2 u)).mono ?_⟩
    · by_cases ht : p t
      · have := hp t ht
        exact Or.inr (by omega)
      · exact Or.inl ht
    · by_cases ht : p t
      · have := hp t ht
        simp only [ht, ite_true]
        omega
      · simp only [ht, ite_false]
        omega

/-! ## The calls of a run of the world -/

/-- An honest call in class `c`, namely a call on the free copy. -/
def HonestIn (c : HashClass) : (WorldSpec C).Domain → Prop
  | .inr t => InClass c t
  | _ => False

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The budget of an adversary in each class, in the form of `DkgTsigBounded`. In class `c`, its
start makes at most `start` calls, each round at most `step`, and `forge` at most `forge` on every
path. For the most rounds of a game, the sum is at most `own c`. -/
def DkgTsigClassBounded (A : DkgTsigAdversary C E) (own : HashClass → ℕ) : Prop :=
  ∀ c, ∃ start step forge : ℕ, start + dkgTsigRounds circuits settings runLimit * step + forge ≤ own c ∧
    (∀ x z, IsQueryBoundP (A.net.start x z) (InClass c) start) ∧
    (∀ state sent, IsQueryBoundP (A.net.round state sent) (InClass c) step) ∧
    (∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass c) forge)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- An adversary of budget `q` makes at most `q` calls in each class. -/
theorem dkgTsigBounded_classBounded {A : DkgTsigAdversary C E} {q : ℕ}
    (h : DkgTsigBounded circuits settings runLimit A q) :
    DkgTsigClassBounded circuits settings runLimit A fun _ => q := fun _ => by
  obtain ⟨start, step, forge, hsum, hs, hr, hf⟩ := h
  exact ⟨start, step, forge, hsum,
    fun x z => isQueryBoundP_of_queryCostAtMost (hs x z) fun _ => one_le_ownCost,
    fun state sent => isQueryBoundP_of_queryCostAtMost (hr state sent) fun _ => one_le_ownCost,
    fun pk top => isQueryBoundP_of_queryCostAtMost (hf pk top) fun _ => one_le_forgeCost⟩

/-! ## The count of the real game by class -/

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity Finset
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable inhabitedField

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra Bit E] [SampleableType E]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- A wrong tuple has a position, so the batch has at least one position. -/
theorem wrongTuple_sum_ne_zero (K : Constants C E) {counts : List ℕ} {D : C.Coalition}
    {x : C.Party → List (Tuple C)} (hx : TupleInputs K counts D x) (hwrong : WrongTuple D x) :
    counts.sum ≠ 0 := by
  obtain ⟨m, hm, g, hg, _⟩ := hwrong
  rw [firstInput_length K hx] at hm
  rw [tupleAt_count K hx m, List.getD_eq_getElem _ _ hm] at hg
  have hle := List.le_sum_of_mem (List.getElem_mem hm)
  omega

/-- The sound induction of the check from the label `L`, the tag `tg` and a start cache with the
earlier coin key inputs `seen` and the earlier expansion keys `keys`. -/
def CheckSoundFrom (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (counts : List ℕ) (D : C.Coalition) (A : CheckAdversary C E (List (Tuple C)))
    (x : C.Party → List (Tuple C)) (step q L tg : ℕ) (st : A.State)
    (cache : HashCache C) (seen : Finset (Query C)) (keys : Finset HashOutput),
    TupleInputs K counts D x →
    (∀ state sent, IsQueryBoundP (A.round state sent) Counted step) →
    (∀ state l, IsQueryBoundP (A.answer state l) Counted step) →
    SoundCache L cache seen keys → seen.card + checkRounds counts.sum * step ≤ q →
    MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) →
    WrongTuple D x →
    Pr{let out ←
      (simulateQ (localAnswer prims)
        (executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st
          (fun i => (startProg K counts.sum (liftedPart (x i) (·.x)) (liftedPart (x i) (·.y))
            (liftedPart (x i) (·.z)) i).run' ⟨filledHistory K i (x i), L, tg⟩))).run' cache}[∃ i,
        i ∉ D.1 ∧ out.2 i = some ()] ≤
      ENNReal.ofReal (checkErrorOf (E := E) (coins counts.sum) (halvings counts.sum) q +
        soundHashError counts.sum (q + keys.card))

/-- The sound induction of the check holds from each label, tag and start cache with earlier keys.
The proof is the proof of `checkSoundRoundInduction` in
`ThresholdLeanXmssSecurity/Proof/CheckSound.lean`, with the label `L`, the tag `tg`, the keys
`keys` in place of `0`, `0`, `∅`, and the key budget `keys.card + (halvings + 2)`. The wrong tuple
gives the positive count. -/
theorem checkSoundFrom (prims : Primitives) (K : Constants C E) : CheckSoundFrom prims K := by
  intro counts D A x step q L tg st cache seen keys hx hr ha hc hb hagree hwrong
  have hpos := wrongTuple_sum_ne_zero K hx hwrong
  let H := keys.card + (halvings counts.sum + 2)
  let F := 1 + 2 * (sliceBits + halvingSteps (sliceWidth counts.sum)) + 6
  let hs : C.Party → RunState C := fun i => ⟨filledHistory K i (x i), L, tg⟩
  let g : C.Party → List E → RunM C E (CheckSpec C E) Unit := fun i τ => do
    StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
    sliceProg K τ counts.sum sliceBits 0 (fun T k => wordWeightOf K τ counts.sum k * liftedPart (x i) (·.x) T k)
      (liftedPart (x i) (·.y)) (conv K (localContext i) (claimOf K τ counts.sum (liftedPart (x i) (·.z))) 0) i
  let bad := soundInitialBad K D counts.sum (fun i => liftedPart (x i) (·.x))
    (fun i => liftedPart (x i) (·.y)) (fun i => liftedPart (x i) (·.z))
  have hF : checkRounds counts.sum = F + 1 := by unfold F checkRounds halvings; omega
  rw [hF]
  change Pr{let out ← (simulateQ (localAnswer prims)
    (executePhase localRoles D A (checkFunctionalities K) (F + 1) st
      (fun i => ((coinKey K (hybridCheckBuildingBlocks K i) >>= fun key => expand K key (coins counts.sum)) >>= g i).run'
        (hs i)))).run' cache}[∃ i, i ∉ D.1 ∧ out.2 i = some ()] ≤ _
  apply le_trans (sound_start_phase prims K D A F step (coins counts.sum) ha st hs tg L
    (fun i hi => ⟨rfl, rfl⟩) g cache seen keys hc bad
    ((coins counts.sum : ℝ≥0∞) / (Fintype.card E - 2 : ℕ))
    (sound_initial_weights K counts D x hx hpos hagree hwrong)
    ((halvings counts.sum + 1 : ℕ) * soundError E q H 2) ?_) ?_
  · intro p τ key cache' seen' hc' hn' hgood
    unfold soundStartNext
    simp only [g, require_bind_run']
    by_cases hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0
    · simp only [ite_eq_left hτ]
      apply sound_sliceRest_all prims K D A τ step q H counts.sum hr ha (sliceWidth_pos hpos) hτ
        sliceBits 0 1 (by omega) p.1 (fun i => i ∈ p.2)
        (fun i => ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩) tg (L + 1)
        (fun i hi => ⟨rfl, rfl⟩)
      · exact hgood
      · exact hc'
      · simp only [checkRounds, halvings, Nat.add_mul, Nat.mul_add] at hb ⊢
        omega
      · have hk := Finset.card_insert_le key keys
        simp only [H, halvings]
        omega
    · simp only [ite_eq_right hτ, ite_self, executePhase_failure]
      simp
  · have hmono := soundError_mono (E := E) q H (coins counts.sum) seen keys (by omega) (by omega)
    calc
      _ ≤ soundError E q H (coins counts.sum) +
          (halvings counts.sum + 1 : ℕ) * soundError E q H 2 := by
        simpa only [add_assoc] using add_le_add hmono
          (le_refl ((halvings counts.sum + 1 : ℕ) * soundError E q H 2))
      _ = _ := pilotSoundError_sum K counts.sum q keys.card

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.checkSoundFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.checkSoundFrom
