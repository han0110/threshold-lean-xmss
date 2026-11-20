import Sketch.DkgGame

/-!
# The count of the calls of `H` by class

A hash term of the library has the form `(q + k)² / 2^256`, and `q` counts calls. The hops of the
game with the real setup count the own calls of the adversary and the honest calls of each class of
domains apart.

* `HashClass` is a class of the domains of `H` and `PRG`. `InClass` is a call of a local computation
  in a class. Each counted call is in exactly one class.
* `OwnIn` and `HonestIn` are the calls of a run of the world in a class, on the counted copy and on
  the free copy.
* `DkgTsigClassBounded` is the budget of an adversary in each class. `DkgTsigBounded` gives it with
  `q` in each class.
* `DkgTsigClassCount` is the count of the calls of the real game by class, for a table `honest` of
  the honest calls and a quiet monitor. `noMonitor` is quiet. It has no honest bound of `challenge`,
  because an honest search makes up to `challengeTries` calls of `.expand`.
* `ChallengeLedger` charges class `challenge` by key. It counts the own calls of the adversary, the
  earlier inputs of `.coinKey` and the distinct keys of the honest expansions.
  `DkgTsigChallengeCount` bounds the honest calls of `.coinKey` of the real game.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmss.Sketch

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

/-- A call in a class is a counted call. -/
theorem inClass_counted {c : HashClass} {t : (LocalSpec C).Domain} (h : InClass c t) : Counted t := by
  rcases t with _ | q | _
  · exact h.elim
  · cases q <;> simp_all [InClass, Counted]
  · trivial

/-- A counted call is in a class. -/
theorem exists_inClass {t : (LocalSpec C).Domain} (h : Counted t) : ∃ c, InClass c t := by
  rcases t with _ | q | _
  · exact h.elim
  · cases q <;> simp_all [InClass, Counted]
  · exact ⟨.stream, rfl⟩

/-- A call is in at most one class. -/
theorem inClass_unique {c c' : HashClass} {t : (LocalSpec C).Domain} (h : InClass c t)
    (h' : InClass c' t) : c = c' := by
  rcases t with _ | q | _
  · exact h.elim
  · cases q <;> simp_all [InClass]
  · exact h.trans h'.symm

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

/-- An own call of the adversary in class `c`, namely a local call on the counted copy. -/
def OwnIn (c : HashClass) : (WorldSpec C).Domain → Prop
  | .inl (.inl t) => InClass c t
  | _ => False

/-- An honest call in class `c`, namely a call on the free copy. -/
def HonestIn (c : HashClass) : (WorldSpec C).Domain → Prop
  | .inr t => InClass c t
  | _ => False

/-- An own call in a class is a call that `world` charges. -/
theorem ownIn_counted {c : HashClass} {t : (WorldSpec C).Domain} (h : OwnIn c t) :
    ∃ t', t = .inl (.inl t') ∧ Counted t' := by
  rcases t with (t | _) | _
  · exact ⟨t, rfl, inClass_counted h⟩
  · exact h.elim
  · exact h.elim

/-! ## The budget of the adversary by class -/

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
/-- A class budget holds for a larger budget. -/
theorem DkgTsigClassBounded.mono {A : DkgTsigAdversary C E} {own own' : HashClass → ℕ}
    (h : DkgTsigClassBounded circuits settings runLimit A own) (hle : ∀ c, own c ≤ own' c) :
    DkgTsigClassBounded circuits settings runLimit A own' := fun c => by
  obtain ⟨start, step, forge, hsum, hs, hr, hf⟩ := h c
  exact ⟨start, step, forge, hsum.trans (hle c), hs, hr, hf⟩

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

/-- A monitor that makes no own call in a class, and no honest call in a class other than
`signing`. -/
def QuietMonitor (monitor : TreeMonitor C) : Prop :=
  ∀ keys tree outputs c, IsQueryBoundP (monitor keys tree outputs) (OwnIn c) 0 ∧
    (c ≠ .signing → IsQueryBoundP (monitor keys tree outputs) (HonestIn c) 0)

/-- The monitor of `dkgTsigGame` is quiet. -/
theorem noMonitor_quiet : QuietMonitor (noMonitor (C := C)) :=
  fun _ _ _ _ => ⟨by simp [noMonitor], fun _ => by simp [noMonitor]⟩

/-- The count of the calls of the real game by class, for the table `honest` of the honest calls. For
each quiet monitor, coalition and adversary with the class budget `own`, a run makes at most `own c`
own calls in class `c`. It makes at most `honest c` honest calls in each class `c` other than
`signing` and `challenge`. The count has no bound of the honest calls of `signing`. The honest calls
of `challenge` go to `ChallengeLedger`. -/
def DkgTsigClassCount (honest : HashClass → ℕ) : Prop :=
  ∀ (monitor : TreeMonitor C), QuietMonitor monitor →
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (own : HashClass → ℕ),
      DkgTsigClassBounded circuits settings runLimit A own → ∀ c,
        IsQueryBoundP (dkgTsigRun K circuits settings runLimit monitor D A) (OwnIn c) (own c) ∧
          (c ≠ .signing → c ≠ .challenge →
            IsQueryBoundP (dkgTsigRun K circuits settings runLimit monitor D A) (HonestIn c) (honest c))

omit [Fintype E] [DecidableEq E] in
/-- The count holds for a larger table of the honest calls. -/
theorem DkgTsigClassCount.mono {honest honest' : HashClass → ℕ}
    (h : DkgTsigClassCount K circuits settings runLimit honest) (hle : ∀ c, honest c ≤ honest' c) :
    DkgTsigClassCount K circuits settings runLimit honest' := fun monitor hm D A own hA c =>
  ⟨(h monitor hm D A own hA c).1, fun hc hc' => ((h monitor hm D A own hA c).2 hc hc').mono (hle c)⟩

omit [Fintype E] [DecidableEq E] in
/-- With the count, an adversary of budget `q` makes at most `q` own calls in each class of a run
with a quiet monitor. -/
theorem DkgTsigClassCount.own_le {honest : HashClass → ℕ}
    (h : DkgTsigClassCount K circuits settings runLimit honest) {monitor : TreeMonitor C}
    (hm : QuietMonitor monitor) (D : C.Coalition) {A : DkgTsigAdversary C E} {q : ℕ}
    (hA : DkgTsigBounded circuits settings runLimit A q) (c : HashClass) :
    IsQueryBoundP (dkgTsigRun K circuits settings runLimit monitor D A) (OwnIn c) q :=
  (h monitor hm D A _ (dkgTsigBounded_classBounded circuits settings runLimit hA) c).1

/-! ## The ledger of the challenges -/

/-- An honest call of `.coinKey`, namely a call of the free copy. -/
def HonestCoinKey : (WorldSpec C).Domain → Prop
  | .inr (.inr (.inl (.coinKey ..))) => True
  | _ => False

/-- An honest call of `.coinKey` is an honest call in class `challenge`. -/
theorem honestCoinKey_honestIn {t : (WorldSpec C).Domain} (h : HonestCoinKey t) :
    HonestIn .challenge t := by
  rcases t with _ | _ | (q | _)
  · exact h.elim
  · exact h.elim
  · cases q <;> first | exact h.elim | rfl
  · exact h.elim

/-- The ledger of class `challenge` at the start of a check. `own` counts the own calls of the
adversary in the class. `coinInputs` counts the inputs of `.coinKey` of the earlier honest checks.
`expansionKeys` counts the distinct keys of the earlier honest expansions. A search is charged by its
key, and not by its calls of `.expand`. -/
structure ChallengeLedger where
  own : ℕ
  coinInputs : ℕ
  expansionKeys : ℕ

/-- The bound of the cached inputs of `.coinKey` and `.expand` that a check charges one by one, namely
the own calls and the earlier inputs of `.coinKey`. -/
def ChallengeLedger.seen (ledger : ChallengeLedger) : ℕ := ledger.own + ledger.coinInputs

/-- The ledger of a run with `own` own calls in class `challenge` and `coinKeys` honest calls of
`.coinKey`. The key of each honest expansion is the output of an honest call of `.coinKey` (`expand`
and `challenge` of `Scheme.lean`), so `coinKeys` also bounds the distinct expansion keys. -/
def challengeLedger (own coinKeys : ℕ) : ChallengeLedger := ⟨own, coinKeys, coinKeys⟩

/-- The count of the honest calls of `.coinKey` of the real game. For each quiet monitor, coalition
and adversary with a class budget, a run makes at most `coinKeys` honest calls of `.coinKey`. -/
def DkgTsigChallengeCount (coinKeys : ℕ) : Prop :=
  ∀ (monitor : TreeMonitor C), QuietMonitor monitor →
    ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (own : HashClass → ℕ),
      DkgTsigClassBounded circuits settings runLimit A own →
        IsQueryBoundP (dkgTsigRun K circuits settings runLimit monitor D A) HonestCoinKey coinKeys

end ThresholdLeanXmss.Sketch
