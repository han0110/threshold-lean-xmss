import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Basics
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.HonestBudgets
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Readiness

/-!
# The budget parts of the readiness at the test `RunReady`

`firstRun_unreadyFails` states that each start that `firstRunWith` at the test `RunReady` records as
not ready fails a budget part. `SplitAtUnready`, `SoundAtUnready`, `SaltsAtUnready` and
`HiddenAtUnready` bound the four budget parts at such a start, and `SplitAtEnd`, `SoundAtEnd` and
`SaltsAtEnd` bound them at the end of the game. `splitAtEnd_of_premises` and
`saltsAtEnd_of_premises` prove the bounds of the split region and of the salts from the count of the
class `digest`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace DigestBudgets

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map
  noCall_mapM noCall_mono noCall_sequenceFin noCall_query)

attribute [local instance] Classical.propDecidable

/-! ## The premises of the count of the classes `digest` and `copy` -/

section Premises

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings)

theorem signQuiet_digest : FirstCounts.SignQuiet (C := C) .digest := signQuiet (by decide)

omit [Field E] [Algebra Bit E] in
theorem seedHonest_digest : FirstCounts.SeedHonest (C := C) (E := E) .digest 0 := seedHonest (by decide)

theorem treeHonest_digest :
    FirstCounts.TreeHonest K circuits settings .digest fun tree => treeBatches settings tree * termHashes C :=
  treeHonest K circuits settings (Or.inl rfl)
end Premises

end DigestBudgets

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

namespace Ready

/-! ## The invariant of readiness -/

section Game

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (budget : StartBudget)

attribute [local irreducible] streamTreeRun wrongOutput

theorem firstTreeRun_keeps (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    Keeps (Inv prims budget D) (firstTreeRunWith prims K circuits settings D net (RunReady prims budget D) tree) := by
  intro s world hs z hz
  unfold firstTreeRunWith at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, mem_support_bind_iff, StateT.run_set,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
  obtain ⟨hlive, hunready⟩ := hs
  have hgrow : world ≤ x.2 := streamTreeRun_le prims K circuits settings D net tree s.real world x hx
  have hkeys : (fun j => ((s.real.operators j).keep (x.1.1.2 j) tree).keys) = fun j => (s.real.operators j).keys :=
    funext fun j => keep_keys _ _ _
  refine ⟨fun hn => ?_, fun tree' index w hw => ?_⟩
  · obtain ⟨hn₁, hn₂⟩ := orElse_eq_none hn
    obtain ⟨hfirst, -⟩ := orElse_eq_none hn₁
    have hbad : x.1.2 = false := by
      by_contra hb
      simp [hb] at hn₂
    obtain ⟨hseeds, htop⟩ := hlive hfirst
    refine ⟨?_, fun i hi topTree htop' => ?_⟩
    · change seedsDiffer D (fun j => ((s.real.operators j).keep (x.1.1.2 j) tree).keys) = false
      rw [hkeys]
      exact hseeds
    · change ((s.real.operators i).keep (x.1.1.2 i) tree).top = some topTree at htop'
      change ∃ w z, z ∈ support (freeRun prims D
        (refTop D fun j => ((s.real.operators j).keep (x.1.1.2 j) tree).keys) w) ∧ z.1 = some (.top topTree) ∧
          z.2 ≤ x.2
      rw [hkeys]
      have old : (s.real.operators i).top = some topTree →
          ∃ w z, z ∈ support (freeRun prims D (refTop D fun j => (s.real.operators j).keys) w) ∧
            z.1 = some (.top topTree) ∧ z.2 ≤ x.2 := fun h => by
        obtain ⟨w₀, z₀, hz₀, hz₀1, hz₀2⟩ := htop i hi topTree h
        refine ⟨w₀, z₀, hz₀, hz₀1, ?_⟩
        exact le_trans hz₀2 hgrow
      cases tree with
      | bottom b => exact old htop'
      | top =>
        cases hold : (s.real.operators i).top with
        | some t =>
          simp only [OperatorState.keep, hold, some_orElse] at htop'
          exact old (hold.trans htop')
        | none =>
          simp only [OperatorState.keep, hold, none_orElse] at htop'
          have hout : x.1.1.2 i = some (.top topTree) := topTree_eq_some htop'
          obtain ⟨w₀, z₀, hz₀, hz₀2, hz₀3⟩ := streamTreeRun_top prims K circuits settings D net s.real world x hx
          refine ⟨w₀, z₀, hz₀, ?_, le_of_eq hz₀2⟩
          rw [← hz₀3 hbad i hi (by rw [hout]; rfl), hout]
  · cases hfirst : s.first with
    | some v =>
      simp only [hfirst, some_orElse] at hw
      obtain ⟨hfail, hw'⟩ := hunready tree' index w (hfirst.trans hw)
      exact ⟨hfail, le_trans hw' hgrow⟩
    | none =>
      simp only [hfirst, none_orElse] at hw
      by_cases hready : RunReady prims budget D s.real world
      · simp only [hready, ite_true, none_orElse] at hw
        split_ifs at hw
        simp at hw
      · simp only [hready, ite_false, some_orElse] at hw
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
        exact ⟨fun hbudget => hready (runReady_of_live prims budget D s.real world (hlive hfirst) hbudget), hgrow⟩

theorem firstTreeRuns_keeps (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    ∀ count, Keeps (Inv prims budget D) (firstTreeRunsWith prims K circuits settings runLimit D net
        (RunReady prims budget D) tree count)
  | 0 => keeps_pure _
  | count + 1 => by
    unfold firstTreeRunsWith
    refine keeps_get_bind fun s => ?_
    split_ifs
    · exact keeps_bind (firstTreeRun_keeps prims K circuits settings budget D net tree) fun _ =>
        firstTreeRuns_keeps D net tree count
    · exact keeps_pure _

theorem firstTreeRequest_keeps (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) :
    Keeps (Inv prims budget D) (firstTreeRequestWith prims K circuits settings runLimit D net
        (RunReady prims budget D) b) := by
  unfold firstTreeRequestWith
  refine keeps_bind (firstTreeRuns_keeps prims K circuits settings runLimit budget D net _ 1) fun _ =>
    keeps_get_bind fun s => ?_
  split
  · exact keeps_bind (inStream_keeps prims budget D _) fun _ => keeps_pure _
  · exact keeps_pure _

theorem firstOracles_keeps (D : C.Coalition) (A : DkgTsigAdversary C E) (q : TsigQuery C) :
    KeepsT (Inv prims budget D) (firstOraclesWith prims K circuits settings runLimit D A
        (RunReady prims budget D) q) := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact fun t => keeps_pure _
  · exact keepsT_lift (firstTreeRequest_keeps prims K circuits settings runLimit budget D A.net b)
  · exact firstSignRequest_keeps prims budget D i e _
  · exact firstSignRequest_keeps prims budget D i e _

theorem firstSigning_keeps (D : C.Coalition) (A : DkgTsigAdversary C E) :
    Keeps (Inv prims budget D) (firstSigningWith prims K circuits settings runLimit D A (RunReady prims budget D)) := by
  unfold firstSigningWith
  refine keeps_get_bind fun s => ?_
  split
  · refine keeps_bind (keepsT_simulateQ _ (fun q => ?_) _ _) fun _ => keeps_pure _
    rcases q with t | q | q
    · exact keepsT_lift (inStream_keeps prims budget D _)
    · exact firstOracles_keeps prims K circuits settings runLimit budget D A q
    · rcases q with _ | state
      · exact keepsT_lift (keeps_bind keeps_get fun _ => keeps_pure _)
      · exact keepsT_lift (keeps_modify _ fun s w hs => hs)
  · exact keeps_pure _

/-- Each start that `firstRunWith` records as not ready fails a budget part, and its world is below the
final world. -/
theorem firstRun_unreadyFails (D : C.Coalition) (A : DkgTsigAdversary C E) :
    ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A
        (RunReady prims budget D)), UnreadyFails budget r.1.first r.2 := by
  intro r hr
  unfold firstRunWith at hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨y, -, hr⟩ := hr
  rcases y with ⟨⟨state, keys⟩, world⟩
  simp only [StateT.run_get, support_pure, Set.mem_singleton_iff, exists_eq_left, StateT.run_pure] at hr
  obtain ⟨x, ⟨z, hz, hx⟩, rfl⟩ := hr
  have hstart : Inv prims budget D (⟨startState D state keys,
      if (startState D state keys).flag then some (.seeds, world) else none⟩ : FirstState C A.net.State) world := by
    refine ⟨fun hn => ⟨?_, fun i _ topTree htop => ?_⟩, fun tree index w hw => ?_⟩
    · by_contra hflag
      simp only [startState, Bool.not_eq_false] at hflag hn
      simp [hflag] at hn
    · cases htop
    · split_ifs at hw
      simp at hw
  exact (keeps_bind (firstTreeRuns_keeps prims K circuits settings runLimit budget D A.net .top runLimit)
    (fun _ => firstSigning_keeps prims K circuits settings runLimit budget D A) _ world hstart x
    (by rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff]; exact ⟨z, hz, hx⟩)).2

end Game

/-! ## The budget parts -/

section Hop

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The split region at a start that `firstRunWith` records as not ready, with no global event, has at
most `splitBudget` cells. -/
def SplitAtUnready : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A
        (RunReady prims (startBudget circuits settings runLimit C q) D)),
      ∀ tree index w, r.1.first = some (.unready tree index, w) → ¬ GlobalEvent w →
        SplitCacheBound (splitRegionCache SplitHashDomain w.1) (startBudget circuits settings runLimit C q).split

/-- The coin keys and the expansions at a start that `firstRunWith` records as not ready, with no global
event, have the ledger `SoundCache` with at most `q + gameCoinKeys` charged inputs and `gameCoinKeys`
expansion keys. -/
def SoundAtUnready : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A
        (RunReady prims (startBudget circuits settings runLimit C q) D)),
      ∀ tree index w, r.1.first = some (.unready tree index, w) → ¬ GlobalEvent w →
        ∃ (seen : Finset (Query C)) (keys : Finset HashOutput), SoundCache 0 w.1 seen keys ∧
          seen.card ≤ (startBudget circuits settings runLimit C q).coins ∧
          keys.card ≤ (startBudget circuits settings runLimit C q).keys

/-- The digests at a start that `firstRunWith` records as not ready, with no global event, have at most
`splitBudget` salts. -/
def SaltsAtUnready : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A
        (RunReady prims (startBudget circuits settings runLimit C q) D)),
      ∀ tree index w, r.1.first = some (.unready tree index, w) → ¬ GlobalEvent w →
        ∃ salts : Finset (List Bit), DigestSaltsCovered w.1 salts ∧
          salts.card ≤ (startBudget circuits settings runLimit C q).salts

/-- The hidden streams at a start that `firstRunWith` records as not ready, with no global event, have at
most `gameSetups` keys under each name. -/
def HiddenAtUnready : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A
        (RunReady prims (startBudget circuits settings runLimit C q) D)),
      ∀ tree index w, r.1.first = some (.unready tree index, w) → ¬ GlobalEvent w →
        HiddenKeyBound w.2 (startBudget circuits settings runLimit C q).hiddenKeys

omit [Field E] [Algebra Bit E] in
theorem cell_ne_none_of_le {α β : Type} {c c' : (α →ₒ β).QueryCache} (hle : c ≤ c') {x : α} (h : c x ≠ none) :
    c' x ≠ none := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h
  rw [hle hv]
  simp

/-- The split region at the end of `firstRunWith` has at most `splitBudget` cells. -/
def SplitAtEnd : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A
        (RunReady prims (startBudget circuits settings runLimit C q) D)),
      SplitCacheBound (splitRegionCache SplitHashDomain r.2.1) (startBudget circuits settings runLimit C q).split

/-- The coin keys and the expansions at the end of `firstRunWith` have the ledger `SoundCache` with at
most `q + gameCoinKeys` charged inputs and `gameCoinKeys` expansion keys. -/
def SoundAtEnd : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A
        (RunReady prims (startBudget circuits settings runLimit C q) D)),
      ∃ (seen : Finset (Query C)) (keys : Finset HashOutput), SoundCache 0 r.2.1 seen keys ∧
        seen.card ≤ (startBudget circuits settings runLimit C q).coins ∧
        keys.card ≤ (startBudget circuits settings runLimit C q).keys

/-- The digests at the end of `firstRunWith` have at most `splitBudget` salts. -/
def SaltsAtEnd : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A
        (RunReady prims (startBudget circuits settings runLimit C q) D)),
      ∃ salts : Finset (List Bit), DigestSaltsCovered r.2.1 salts ∧
        salts.card ≤ (startBudget circuits settings runLimit C q).salts

theorem splitAtUnready_of_end (h : SplitAtEnd prims K circuits settings runLimit) :
    SplitAtUnready prims K circuits settings runLimit := by
  intro D A q bounded r hr tree index w hw _
  have hle := (firstRun_unreadyFails prims K circuits settings runLimit _ D A r hr tree index w hw).2
  obtain ⟨S, hS, hcover⟩ := h D A q bounded r hr
  refine ⟨S, hS, fun x hx => hcover x ?_⟩
  simp only [splitRegionCache, QueryCache.ofFn_apply] at hx ⊢
  split_ifs at hx ⊢
  · exact cell_ne_none_of_le hle.1 hx
  · exact hx

theorem soundAtUnready_of_end (h : SoundAtEnd prims K circuits settings runLimit) :
    SoundAtUnready prims K circuits settings runLimit := by
  intro D A q bounded r hr tree index w hw _
  have hle := (firstRun_unreadyFails prims K circuits settings runLimit _ D A r hr tree index w hw).2
  obtain ⟨seen, keys, ⟨hcoin, hexpand⟩, hseen, hkeys⟩ := h D A q bounded r hr
  exact ⟨seen, keys, ⟨fun tag label bits hL hx => hcoin tag label bits hL (cell_ne_none_of_le hle.1 hx),
    fun key idx hx => hexpand key idx (cell_ne_none_of_le hle.1 hx)⟩, hseen, hkeys⟩

theorem saltsAtUnready_of_end (h : SaltsAtEnd prims K circuits settings runLimit) :
    SaltsAtUnready prims K circuits settings runLimit := by
  intro D A q bounded r hr tree index w hw _
  have hle := (firstRun_unreadyFails prims K circuits settings runLimit _ D A r hr tree index w hw).2
  obtain ⟨salts, hcover, hcard⟩ := h D A q bounded r hr
  exact ⟨salts, fun salt x hx => hcover salt x (cell_ne_none_of_le hle.1 hx), hcard⟩

end Hop

end Ready

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace FirstCounts

open GameCount (CellIn)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_sequenceFin)

attribute [local instance] Classical.propDecidable

/-! ## The cells of a class -/

section Cells

variable {C : Committee}

/-- A cell of class `digest` is a cell of a running hash or of a salted digest. -/
theorem cellIn_digest_iff (x : Query C) : CellIn .digest x ↔ SplitHashDomain x := by
  have hp : ∀ phase : Phase, phaseClass phase ≠ .digest := by intro phase; cases phase <;> simp [phaseClass]
  cases x <;> simp [CellIn, queryClass, SplitHashDomain, hp]

end Cells

/-! ## The count and its consumers -/

section Count

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The salt of a salted digest, and the empty salt for each other input. -/
def saltOf : Query C → List Bit
  | .digest salt _ => salt
  | _ => []

/-- The split region at the end of `firstRunWith` has at most `splitBudget` cells. -/
theorem splitAtEnd_of_count
    (h : FirstCount prims K circuits settings runLimit .digest (gameBatches settings runLimit * termHashes C)) :
    Ready.SplitAtEnd prims K circuits settings runLimit := by
  intro D A q bounded r hr
  obtain ⟨cells, hcard, hcover⟩ :=
    h D A _ _ (dkgTsigBounded_classBounded circuits settings runLimit bounded) r hr
  refine ⟨cells, hcard, fun x hx => ?_⟩
  simp only [splitRegionCache, QueryCache.ofFn_apply] at hx
  split_ifs at hx with hd
  · exact hcover x ((cellIn_digest_iff x).2 hd) hx
  · exact absurd rfl hx

/-- The digests at the end of `firstRunWith` have at most `splitBudget` salts. -/
theorem saltsAtEnd_of_count
    (h : FirstCount prims K circuits settings runLimit .digest (gameBatches settings runLimit * termHashes C)) :
    Ready.SaltsAtEnd prims K circuits settings runLimit := by
  intro D A q bounded r hr
  obtain ⟨cells, hcard, hcover⟩ :=
    h D A _ _ (dkgTsigBounded_classBounded circuits settings runLimit bounded) r hr
  refine ⟨cells.image saltOf, fun salt x hx => ?_, Finset.card_image_le.trans hcard⟩
  exact Finset.mem_image.2 ⟨.digest salt x, hcover _ (by simp [CellIn, queryClass]) hx, rfl⟩

/-- The count of class `digest` with the honest bound `gameBatches * termHashes C`. -/
theorem firstCount_digest (hseed : SeedHonest (C := C) (E := E) .digest 0)
    (htree : TreeHonest K circuits settings .digest fun tree => treeBatches settings tree * termHashes C)
    (hsign : SignQuiet (C := C) .digest) :
    FirstCount prims K circuits settings runLimit .digest (gameBatches settings runLimit * termHashes C) := by
  have h := firstCount_of prims K circuits settings runLimit .digest (by decide) 0 _ hseed htree hsign
  have e : 0 + runLimit * (treeBatches settings .top * termHashes C +
      ∑ b : Fin (2 ^ layerHeight), treeBatches settings (.bottom b) * termHashes C) =
        gameBatches settings runLimit * termHashes C := by
    simp only [gameBatches, ← Finset.sum_mul]
    ring
  rwa [e] at h

/-- `Ready.SplitAtEnd` from the honest calls of class `digest`. -/
theorem splitAtEnd_of_premises (hseed : SeedHonest (C := C) (E := E) .digest 0)
    (htree : TreeHonest K circuits settings .digest fun tree => treeBatches settings tree * termHashes C)
    (hsign : SignQuiet (C := C) .digest) : Ready.SplitAtEnd prims K circuits settings runLimit :=
  splitAtEnd_of_count prims K circuits settings runLimit
    (firstCount_digest prims K circuits settings runLimit hseed htree hsign)

/-- `Ready.SaltsAtEnd` from the honest calls of class `digest`. -/
theorem saltsAtEnd_of_premises (hseed : SeedHonest (C := C) (E := E) .digest 0)
    (htree : TreeHonest K circuits settings .digest fun tree => treeBatches settings tree * termHashes C)
    (hsign : SignQuiet (C := C) .digest) : Ready.SaltsAtEnd prims K circuits settings runLimit :=
  saltsAtEnd_of_count prims K circuits settings runLimit
    (firstCount_digest prims K circuits settings runLimit hseed htree hsign)

end Count

end FirstCounts

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestBudgets.signQuiet_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestBudgets.signQuiet_digest

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestBudgets.seedHonest_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestBudgets.seedHonest_digest

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestBudgets.treeHonest_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestBudgets.treeHonest_digest

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.FirstCounts.firstCount_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.FirstCounts.firstCount_digest

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.FirstCounts.splitAtEnd_of_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.FirstCounts.splitAtEnd_of_premises

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.FirstCounts.saltsAtEnd_of_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.FirstCounts.saltsAtEnd_of_premises

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.Ready.soundAtUnready_of_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.Ready.soundAtUnready_of_end
