import ThresholdLeanXmssSecurity.Proof.BatchCheck.Rand

/-!
# The steps of `C1bStatement` and the tails of the head

`c1MidTail` is the middle of the step with the tail of the wrapper in place of the real digest round
after a partial output of the head. The dead blocks after a partial output (`planDead`, `coinDead`),
the known columns of the digest round (`knownColumns`), the hidden histories through
`F_extendMult` (`extendHidden`) and the rest of the check after a partial head (`restAbort`) follow.
`headTails` proves `HeadTailsStatement` from the four blocks of the tails.
-/

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1r

open RealNetworkV3 RealNetworkC1s

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-! ## The invariants of the outputs -/

/-- The memory holds the history of each known term of each honest operator with an output. -/
def KnownInv (D : C.Coalition) (mem : C1Memory C E) {α : Type} (out : C.Party → Option (α × RunState C)) : Prop :=
  ∀ i, i ∉ D.1 → ∀ z, out i = some z → ∀ T, KnownTo D.1 T → mem.hist i T = z.2.history T

/-- Two honest holders of a hidden term with an output have the same history of it. -/
def HiddenInv (D : C.Coalition) {α : Type} (out : C.Party → Option (α × RunState C)) : Prop :=
  ∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
    ∀ zi zj, out i = some zi → out j = some zj → zi.2.history T = zj.2.history T

/-- The live holders of a hidden term have one common history. The real digest round reads it. -/
theorem hiddenInv_common (D : C.Coalition) {α : Type} (out : C.Party → Option (α × RunState C))
    (h : HiddenInv D out) : ∃ hist : C.Term → List Bit, ∀ T, ¬ KnownTo D.1 T → ∀ i, i ∉ D.1 →
      i ∈ C.holders T → ∀ z, out i = some z → z.2.history T = hist T := by
  refine ⟨fun T => if hT : ∃ i z, i ∉ D.1 ∧ i ∈ C.holders T ∧ out i = some z then
    hT.choose_spec.choose.2.history T else [], fun T hk i hi hiT z hz => ?_⟩
  have hT : ∃ i z, i ∉ D.1 ∧ i ∈ C.holders T ∧ out i = some z := ⟨i, z, hi, hiT, hz⟩
  dsimp only
  rw [dite_eq_left_of_eq_true (eq_true hT)]
  obtain ⟨hj, hjT, hjz⟩ := hT.choose_spec.choose_spec
  exact h T hk i _ hi hj hiT hjT z _ hz hjz

section Steps

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-! ## The runs -/

section Runs

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
  (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
  (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
  (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (count L tg : ℕ)
  (hist : C.Party → C.Term → List Bit)

/-- The part of `c1MidTail` after the head. After a partial output the wrapper plays the digest tail on
the live operators, with the known columns from its memory. After each other output it is `midRest`. -/
def midTailRest (r : (c1WrapperWith K D W knownE knownB count hist names
      (c1HeadTails K D W knownE knownB count L tg)).State × (C.Party → Option (HeadOut C E × RunState C))) :
    OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
  if PartialOut D r.2 then
    (fun st' => (st', fun _ => none)) <$> RealNetworkRC.digestTail D W (liveSet D r.2)
      (knownColumns (liveSet D r.2) knownB.1 r.1.1.2.hist) r.1.1.1
  else
    (fun r' => (r'.1.1.1, r'.2)) <$> executePhase localRoles D
      (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
      (checkFunctionalities K) 5 r.1 (fun i => (r.2 i).elim failure (restAt K i))

/-- The head of the check under the wrapper with the tails of the head. -/
def headPhase (counts : List ℕ) (x : C.Party → List (Tuple C)) (st : W.State) :
    OracleComp (LocalSpec C) ((c1WrapperWith K D W knownE knownB counts.sum (knownHist K D x) names
      (c1HeadTails K D W knownE knownB counts.sum L tg)).State × (C.Party → Option (HeadOut C E × RunState C))) :=
  executePhase localRoles D
    (c1WrapperWith K D W knownE knownB counts.sum (knownHist K D x) names
      (c1HeadTails K D W knownE knownB counts.sum L tg))
    (checkFunctionalities K) (2 * halvings counts.sum + 3) ((st, ⟨knownHist K D x, []⟩), 0) (headAt K L tg x)

/-- `c1Mid` with the digest tail of the wrapper after a partial output of the head. -/
def c1MidTail (counts : List ℕ) (x : C.Party → List (Tuple C)) (st : W.State) :
    OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
  headPhase K D W knownE knownB names L tg counts x st >>=
    midTailRest K D W knownE knownB names counts.sum L tg (knownHist K D x)

/-- The program of the head in the hybrid model from the first coin, for the plans `next`. -/
def hybridStart (count : ℕ) (i : C.Party) (next : List E → Plan C E) : RunM C E (CheckSpec C E) (HeadOut C E) := do
  let τ ← expand K (← coinKey K (hybridCheckBuildingBlocks K i)) (coins count)
  StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
  runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (next τ)

/-- The program of the hybrid model from the coin of a challenge, for the plans `next`. -/
def hybridCoin (i : C.Party) (next : E → Plan C E) : RunM C E (CheckSpec C E) (HeadOut C E) :=
  challenge K (hybridCheckBuildingBlocks K i) >>= fun r => runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (next r)

/-- The tail of the digest round after the head, when its output is partial. -/
def digestAfter (r : (c1WrapperWith K D W knownE knownB count hist names
      (c1HeadTails K D W knownE knownB count L tg)).State × (C.Party → Option (HeadOut C E × RunState C))) :
    OracleComp (LocalSpec C) ((c1WrapperWith K D W knownE knownB count hist names
      (c1HeadTails K D W knownE knownB count L tg)).State × (C.Party → Option (HeadOut C E × RunState C))) :=
  if PartialOut D r.2 then
    (fun s' => ((s', r.1.2), r.2)) <$> c1Tails K D W knownE knownB count L tg (2 * halvings count + 2) (liveSet D r.2) r.1.1
  else pure r

/-- The claim of `HeadTailsStatement` from position `n` with `f` steps of fuel. The run under `c1Tails`
is the run under `c1HeadTails` and then the digest tail after a partial output. -/
def TailsSuffix (n f : ℕ) {β : Type} (Rel : (C.Party → β) → Prop)
    (kH : C.Party → β → RunM C E (CheckSpec C E) (HeadOut C E)) : Prop :=
  ∀ (st : W.State) (mem : C1Memory C E) (b : C.Party → β) (hs : C.Party → RunState C), Rel b →
    SameRun prims
      (executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
        (checkFunctionalities K) f ((st, mem), n) (fun i => (kH i (b i)).run (hs i)))
      (executePhase localRoles D
          (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
          (checkFunctionalities K) f ((st, mem), n) (fun i => (kH i (b i)).run (hs i)) >>=
        digestAfter K D W knownE knownB names count L tg hist)

/-- The claim of `HeadTailsStatement` before the `extendMult` of step `j`, with `d` steps to run. -/
def PlanTailsSuffix (j d : ℕ) : Prop :=
  TailsSuffix prims K D W knownE knownB names count L tg hist (2 * j + 1) (2 * d + 2)
    (fun p : C.Party → Plan C E => ∀ i, i ∉ D.1 → PlanOK (p i) d)
    (fun i p => runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p)

/-- The claim of `HeadTailsStatement` before the coin of step `j`, with `d` steps after it. -/
def CoinTailsSuffix (j d : ℕ) : Prop :=
  TailsSuffix prims K D W knownE knownB names count L tg hist (2 * j + 2) (2 * d + 3)
    (fun next : C.Party → E → Plan C E => ∀ i, i ∉ D.1 → ∀ r, PlanOK (next i r) d) (hybridCoin K)

/-- The claim of `HeadTailsStatement` before the first coin. -/
def StartTailsSuffix : Prop :=
  TailsSuffix prims K D W knownE knownB names count L tg hist 0 (2 * halvings count + 3)
    (fun next : C.Party → List E → Plan C E => ∀ i, i ∉ D.1 → ∀ τ, PlanOK (next i τ) (halvings count))
    (hybridStart K count)

/-- The claim of `HeadHistStatement` from position `n` with `f` steps of fuel. When the invariants hold
at the start, they hold for each output in the support of the run under `c1HeadTails`. -/
def HistSuffix (n f : ℕ) {β : Type} (Rel : (C.Party → β) → Prop)
    (kH : C.Party → β → RunM C E (CheckSpec C E) (HeadOut C E)) : Prop :=
  ∀ (st : W.State) (mem : C1Memory C E) (b : C.Party → β) (hs : C.Party → RunState C), Rel b →
    KnownInv D mem (fun i => some (b i, hs i)) → HiddenInv D (fun i => some (b i, hs i)) →
    ∀ (cache : HashCache C), ∀ z ∈ support ((simulateQ (localAnswer prims) (executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
        (checkFunctionalities K) f ((st, mem), n) (fun i => (kH i (b i)).run (hs i)))).run cache),
      KnownInv D z.1.1.1.2 z.1.2 ∧ HiddenInv D z.1.2

/-- The claim of `HeadHistStatement` before the `extendMult` of step `j`, with `d` steps to run. -/
def PlanHistSuffix (j d : ℕ) : Prop :=
  HistSuffix prims K D W knownE knownB names count L tg hist (2 * j + 1) (2 * d + 2)
    (fun p : C.Party → Plan C E => ∀ i, i ∉ D.1 → PlanOK (p i) d)
    (fun i p => runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p)

/-- The claim of `HeadHistStatement` before the coin of step `j`, with `d` steps after it. -/
def CoinHistSuffix (j d : ℕ) : Prop :=
  HistSuffix prims K D W knownE knownB names count L tg hist (2 * j + 2) (2 * d + 3)
    (fun next : C.Party → E → Plan C E => ∀ i, i ∉ D.1 → ∀ r, PlanOK (next i r) d) (hybridCoin K)

/-- The claim of `HeadHistStatement` before the first coin. -/
def StartHistSuffix : Prop :=
  HistSuffix prims K D W knownE knownB names count L tg hist 0 (2 * halvings count + 3)
    (fun next : C.Party → List E → Plan C E => ∀ i, i ∉ D.1 → ∀ τ, PlanOK (next i τ) (halvings count))
    (hybridStart K count)

end Runs

/-! ## The parts of `C1bStatement` -/

/-- With the premises of `C1bStatement`, `c1Mid` and `c1MidTail` are close. The bound is `c1Error`. -/
def DigestJoinStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (step : ℕ), (∀ st sent, IsQueryBoundP (W.round st sent) Counted step) →
    ∀ (counts : List ℕ) (L tg : ℕ) (x : C.Party → List (Tuple C)) (st : W.State), counts.sum ≠ 0 →
      (∀ i, i ∉ D.1 → (x i).map (·.count) = counts) →
      (∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
        filledHistory K i (x i) T = filledHistory K j (x j) T) →
      ∀ (cache : HashCache C) (seen : Finset (List Bit)), DigestSaltsCovered cache seen →
      ∀ (Z : W.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) Bool) (q : ℕ),
        (∀ out, IsQueryBoundP (Z out) DigestQuery q) →
        measureTVDist
          ((simulateQ (localAnswer prims) (c1Mid K D W knownE knownB names counts L tg x st >>= Z)).run' cache)
          ((simulateQ (localAnswer prims) (c1MidTail K D W knownE knownB names L tg counts x st >>= Z)).run' cache) ≤
          c1Error C step q seen.card counts.sum

/-- `c1MidTail` is the check in the hybrid model under the wrapper. -/
def HybridTailStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (counts : List ℕ) (L tg : ℕ) (x : C.Party → List (Tuple C)) (st : W.State), counts.sum ≠ 0 →
      (∀ i, i ∉ D.1 → (x i).map (·.count) = counts) →
      SameRun prims (c1Hybrid K D W knownE knownB names counts L tg x st)
        (c1MidTail K D W knownE knownB names L tg counts x st)

/-- After a partial output of the head the rest of the check makes no step. The first call of each
live operator is `F_rand` for the salts, and it does not run. -/
def RestAbortStatement (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (A : CheckAdversary C E Ia) (s : A.State) (o : C.Party → Option (HeadOut C E × RunState C)),
    PartialOut D o →
    executePhase localRoles D A (checkFunctionalities K) 5 s (fun i => (o i).elim failure (restAt K i)) =
      pure (s, fun _ => none)

omit [Fintype E] in
/-- The two parts above give `C1bStatement`. -/
theorem c1b_of_steps (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (hjoin : DigestJoinStatement prims K D) (htail : HybridTailStatement prims K D) : C1bStatement prims K D := by
  intro Ia W knownE knownB names hn step hW counts L tg x st hpos hx hh cache seen hc Z q hZ
  have h1 := (htail W knownE knownB names hn counts L tg x st hpos hx).bind fun r => SameRun.refl prims (Z r)
  unfold c1Hybrid at h1
  rw [bind_map_left] at h1
  have he := (h1 cache).map Prod.fst
  simp only [← StateT.run'_eq] at he
  have hb := hjoin W knownE knownB names hn step hW counts L tg x st hpos hx hh cache seen hc Z q hZ
  rw [measureTVDist] at hb ⊢
  rw [he.evalDist_eq]
  exact hb

/-! ## The digest tail of the head -/

/-- The head under `c1Tails` is the head under `c1HeadTails` and then the digest tail after a partial
output. -/
def HeadTailsStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (counts : List ℕ) (L tg : ℕ) (x : C.Party → List (Tuple C)) (st : W.State), counts.sum ≠ 0 →
      (∀ i, i ∉ D.1 → (x i).map (·.count) = counts) →
      SameRun prims
        (executePhase localRoles D
          (c1WrapperWith K D W knownE knownB counts.sum (knownHist K D x) names
            (c1Tails K D W knownE knownB counts.sum L tg))
          (checkFunctionalities K) (2 * halvings counts.sum + 3) ((st, ⟨knownHist K D x, []⟩), 0) (headAt K L tg x))
        (headPhase K D W knownE knownB names L tg counts x st >>=
          digestAfter K D W knownE knownB names counts.sum L tg (knownHist K D x))

/-- `HeadTailsStatement` for the masked multiplication at `2 * R + 1`. The reply to `F_extendMult` at `2
* R + 2` is the only reply whose tail differs. -/
def TailsMaskBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit),
      PlanTailsSuffix prims K D W knownE knownB names count L tg hist (halvings count) 0

/-- `HeadTailsStatement` for the `extendMult` of step `j` at `2 * j + 1`. Both tails are `coinTail`
there. -/
def TailsExtendBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit) (j d : ℕ), j + d + 1 = halvings count →
      CoinTailsSuffix prims K D W knownE knownB names count L tg hist j d →
      PlanTailsSuffix prims K D W knownE knownB names count L tg hist j (d + 1)

/-- `HeadTailsStatement` for the coin of step `j` at `2 * j + 2`. Both tails are the search and
`reshareTail` there. -/
def TailsCoinBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit) (j d : ℕ), j + 1 + d = halvings count →
      PlanTailsSuffix prims K D W knownE knownB names count L tg hist (j + 1) d →
      CoinTailsSuffix prims K D W knownE knownB names count L tg hist j d

/-- `HeadTailsStatement` for the first coin at position 0. -/
def TailsFirstBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit),
      PlanTailsSuffix prims K D W knownE knownB names count L tg hist 0 (halvings count) →
      StartTailsSuffix prims K D W knownE knownB names count L tg hist

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The head at operator `i` is `hybridStart` on the plan of the head. -/
theorem headAt_eq (K : Constants C E) (D : C.Coalition) (counts : List ℕ) (L tg : ℕ) (x : C.Party → List (Tuple C))
    (hx : ∀ i, i ∉ D.1 → (x i).map (·.count) = counts) (i : C.Party) (hi : i ∉ D.1) :
    headAt K L tg x i = (hybridStart K counts.sum i fun τ => headPlan K (localContext i) τ (x i)).run
      ⟨filledHistory K i (x i), L, tg⟩ := by
  unfold headAt hybridStart
  rw [checkHead_eq, headPlan_eq, hx i hi]

omit [Fintype E] in
/-- The four block statements give `HeadTailsStatement`. -/
theorem headTails_of_steps (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (hmask : TailsMaskBlockStatement prims K D) (hextend : TailsExtendBlockStatement prims K D)
    (hcoin : TailsCoinBlockStatement prims K D) (hfirst : TailsFirstBlockStatement prims K D) :
    HeadTailsStatement prims K D := by
  intro Ia W knownE knownB names hn counts L tg x st hpos hx
  have hall : ∀ d j, j + d = halvings counts.sum →
      PlanTailsSuffix prims K D W knownE knownB names counts.sum L tg (knownHist K D x) j d := by
    intro d
    induction d with
    | zero =>
      intro j h
      rw [show j = halvings counts.sum by omega]
      exact hmask W knownE knownB names hn _ L tg _
    | succ d ih =>
      intro j h
      exact hextend W knownE knownB names hn _ L tg _ j d (by omega)
        (hcoin W knownE knownB names hn _ L tg _ j d (by omega) (ih (j + 1) (by omega)))
  have h := hfirst W knownE knownB names hn _ L tg _ (hall _ 0 (by omega)) st ⟨knownHist K D x, []⟩
    (fun i τ => headPlan K (localContext i) τ (x i)) (fun i => ⟨filledHistory K i (x i), L, tg⟩)
    (fun i hi τ => by
      have h := planOK_headPlan K (localContext i) τ (x i)
      rwa [hx i hi] at h)
  unfold headPhase
  rw [executePhase_congr D _ (checkFunctionalities K) _ _ (headAt K L tg x) _ (headAt_eq K D counts L tg x hx),
    executePhase_congr D _ (checkFunctionalities K) _ _ (headAt K L tg x) _ (headAt_eq K D counts L tg x hx)]
  exact h

/-! ## The invariants of the outputs of the head -/

/-- Each output of the head under `c1HeadTails` has the invariants. -/
def HeadHistStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (counts : List ℕ) (L tg : ℕ) (x : C.Party → List (Tuple C)) (st : W.State), counts.sum ≠ 0 →
      (∀ i, i ∉ D.1 → (x i).map (·.count) = counts) →
      (∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
        filledHistory K i (x i) T = filledHistory K j (x j) T) →
      ∀ (cache : HashCache C),
        ∀ z ∈ support ((simulateQ (localAnswer prims) (headPhase K D W knownE knownB names L tg counts x st)).run cache),
          KnownInv D z.1.1.1.2 z.1.2 ∧ HiddenInv D z.1.2

/-- `HeadHistStatement` for the masked multiplication. -/
def HistMaskBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit),
      PlanHistSuffix prims K D W knownE knownB names count L tg hist (halvings count) 0

/-- `HeadHistStatement` for the `extendMult` of step `j`. -/
def HistExtendBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit) (j d : ℕ), j + d + 1 = halvings count →
      CoinHistSuffix prims K D W knownE knownB names count L tg hist j d →
      PlanHistSuffix prims K D W knownE knownB names count L tg hist j (d + 1)

/-- `HeadHistStatement` for the coin of step `j`. -/
def HistCoinBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit) (j d : ℕ), j + 1 + d = halvings count →
      PlanHistSuffix prims K D W knownE knownB names count L tg hist (j + 1) d →
      CoinHistSuffix prims K D W knownE knownB names count L tg hist j d

/-- `HeadHistStatement` for the first coin. -/
def HistFirstBlockStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (count L tg : ℕ) (hist : C.Party → C.Term → List Bit),
      PlanHistSuffix prims K D W knownE knownB names count L tg hist 0 (halvings count) →
      StartHistSuffix prims K D W knownE knownB names count L tg hist

omit [Fintype E] in
/-- The four block statements give `HeadHistStatement`. -/
theorem headHist_of_steps (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (hmask : HistMaskBlockStatement prims K D) (hextend : HistExtendBlockStatement prims K D)
    (hcoin : HistCoinBlockStatement prims K D) (hfirst : HistFirstBlockStatement prims K D) :
    HeadHistStatement prims K D := by
  intro Ia W knownE knownB names hn counts L tg x st hpos hx hh cache
  have hall : ∀ d j, j + d = halvings counts.sum →
      PlanHistSuffix prims K D W knownE knownB names counts.sum L tg (knownHist K D x) j d := by
    intro d
    induction d with
    | zero =>
      intro j h
      rw [show j = halvings counts.sum by omega]
      exact hmask W knownE knownB names hn _ L tg _
    | succ d ih =>
      intro j h
      exact hextend W knownE knownB names hn _ L tg _ j d (by omega)
        (hcoin W knownE knownB names hn _ L tg _ j d (by omega) (ih (j + 1) (by omega)))
  have h := hfirst W knownE knownB names hn _ L tg _ (hall _ 0 (by omega)) st ⟨knownHist K D x, []⟩
    (fun i τ => headPlan K (localContext i) τ (x i)) (fun i => ⟨filledHistory K i (x i), L, tg⟩)
    (fun i hi τ => by
      have h := planOK_headPlan K (localContext i) τ (x i)
      rwa [hx i hi] at h)
    (fun i hi z hz T hT => by
      cases hz
      simp only [knownHist, hi, not_false_eq_true, hT, and_self, ite_true])
    (fun T hT i j hi hj hiT hjT zi zj hzi hzj => by
      cases hzi
      cases hzj
      exact hh T hT i j hi hj hiT hjT) cache
  unfold headPhase
  rw [executePhase_congr D _ (checkFunctionalities K) _ _ (headAt K L tg x) _ (headAt_eq K D counts L tg x hx)]
  exact h

/-! ## The tail of the check in the hybrid model -/

/-- `HeadTailsStatement` and `RestAbortStatement` with `hybridCut` give `HybridTailStatement`. -/
theorem hybridTail_of_steps (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (htails : HeadTailsStatement prims K D) (habort : RestAbortStatement K D) : HybridTailStatement prims K D := by
  intro Ia W knownE knownB names hn counts L tg x st hpos hx
  have hcut := RealNetworkC1p.hybridCut prims K D (c1WrapperWith K D W knownE knownB counts.sum (knownHist K D x) names
    (c1Tails K D W knownE knownB counts.sum L tg)) counts L tg x ((st, ⟨knownHist K D x, []⟩), 0) hpos hx
  have h3 := (htails W knownE knownB names hn counts L tg x st hpos hx).bind fun r =>
    SameRun.refl prims (executePhase localRoles D (c1WrapperWith K D W knownE knownB counts.sum (knownHist K D x)
      names (c1Tails K D W knownE knownB counts.sum L tg)) (checkFunctionalities K) 5 r.1
      (fun i => (r.2 i).elim failure (restAt K i)))
  unfold c1Hybrid c1MidTail
  refine (hcut.map _).trans ((h3.map _).trans (SameRun.of_eq ?_))
  rw [bind_assoc, map_bind]
  refine bind_congr fun r => ?_
  unfold digestAfter midTailRest
  split_ifs with hp
  · have hT : c1Tails K D W knownE knownB counts.sum L tg (2 * halvings counts.sum + 2) (liveSet D r.2) r.1.1 =
        (fun st' => (st', r.1.1.2)) <$> RealNetworkRC.digestTail D W (liveSet D r.2)
          (knownColumns (liveSet D r.2) knownB.1 r.1.1.2.hist) r.1.1.1 := by
      unfold c1Tails
      rw [ite_eq_right (by omega)]
      simp only [↓reduceIte]
    rw [hT, map_bind]
    erw [bind_map_left, bind_map_left]
    refine (bind_congr fun st' => ?_).trans (map_eq_bind_pure_comp _ _ _).symm
    simp only [Function.comp_apply]
    rw [habort _ _ r.2 hp, map_pure]
  · rw [pure_bind]

/-! ## The memory and the digests under the tails of the head

The memory and the counter under `c1HeadTails` are `coinMemoryHead` and `extendMemoryHead`. -/

/-- After a call of `F_extendMult` under the tails of the head, two honest receivers that hold a hidden
term have the same history of it, when they had the same history before. -/
def ExtendHiddenStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg : ℕ)
    (hist : C.Party → C.Term → List Bit) (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (fuel k : ℕ) (s : W.State × C1Memory C E) (products : C.Party → List (Product C E))
    (hs : C.Party → RunState C) (cache : HashCache C), (∀ i, i ∉ D.1 → (products i).length = 2) →
    (∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (hs i).history T = (hs j).history T) →
    ∀ z ∈ support ((simulateQ (localAnswer prims) (RealNetworkGP.callPhase D
        (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
        (checkFunctionalities K) (fuel + 1) (s, k) (fun i => Sum.inl (Sum.inr (products i)))
        (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z)))).run cache),
      HiddenInv D z.1.2

/-- A plan block after a partial output. The first step of each live operator is a call, which does not
run. So the adversary gets no step and no honest operator has an output. -/
def PlanDeadStatement (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State) (o : C.Party → Option (Plan C E × RunState C)),
    (∃ i, i ∉ D.1 ∧ o i = none) →
    executePhase localRoles D A (checkFunctionalities K) fuel st
      (fun i => (o i).elim failure fun p => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p.1).run p.2) =
      pure (st, fun _ => none)

/-- A coin block after a partial output. The first step of each live operator is the call of `F_coin`,
which does not run. -/
def CoinDeadStatement (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (A : CheckAdversary C E Ia) (fuel : ℕ) (st : A.State)
    (o : C.Party → Option ((E → Plan C E) × RunState C)), (∃ i, i ∉ D.1 ∧ o i = none) →
    executePhase localRoles D A (checkFunctionalities K) fuel st
      (fun i => (o i).elim failure fun p => (hybridCoin K i p.1).run p.2) = pure (st, fun _ => none)

/-- On an output with `KnownInv`, the real digests of a known term on drawn salts are the known
columns of the wrapper. The left side is the premise `hknown` of `realDigestPhase_partial_hide`. -/
def KnownColumnsStatement (D : C.Coalition) : Prop :=
  ∀ (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (mem : C1Memory C E)
    (out : C.Party → Option (HeadOut C E × RunState C)), KnownInv D mem out →
    ∀ (table : C.Term → Fin 256 → Bit) (T : C.Term), KnownTo D.1 T →
      OverPermutation.sequenceFin (fun i => RealNetworkRC.liveCol
        (· ∈ RealNetworkRC.liveSet D (fun i => (out i).map Prod.snd)) (digestSalts D knownB table)
        (RealNetworkRC.histOf fun i => (out i).map Prod.snd) T i) =
      knownColumns (liveSet D out) knownB.1 mem.hist T

/-- A known column makes at most `C.n` digest calls. It is the premise `hbound` of
`realDigestPhase_partial_hide` with `p = C.n`, as `c1Error` charges it. -/
def KnownColumnsBoundStatement (C : Committee) : Prop :=
  ∀ (live : Finset C.Party) (known : Shares C Bit) (hist : C.Party → C.Term → List Bit) (T : C.Term),
    IsQueryBoundP (knownColumns live known hist T) DigestQuery C.n

/-- The cover of the digest salts after the head. The head makes at most `2 * (2 * R + 3) * step`
digest calls (`head_digestBound_proved`). -/
theorem headCover (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (step : ℕ)
    (hW : ∀ st m, IsQueryBoundP (W.round st m) Counted step) (counts : List ℕ) (L tg : ℕ)
    (x : C.Party → List (Tuple C)) (st : W.State) (cache : HashCache C) (seen : Finset (List Bit))
    (hc : DigestSaltsCovered cache seen) :
    ∀ z ∈ support ((simulateQ (localAnswer prims) (headPhase K D W knownE knownB names L tg counts x st)).run cache),
      ∃ seen', DigestSaltsCovered z.2 seen' ∧ seen'.card ≤ seen.card + 2 * (2 * halvings counts.sum + 3) * step :=
  fun z hz => localProgram_digest_covered prims _ DigestQuery (fun _ ht => ht) _
    (RealNetworkC1p.head_digestBound_proved K D W knownE knownB names step hW counts L tg x st) cache seen hc z hz

/-! ## Corner cases -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- The invariants hold on an output with no honest receiver. -/
theorem inv_none (D : C.Coalition) (mem : C1Memory C E) {α : Type} :
    KnownInv D mem (fun _ : C.Party => (none : Option (α × RunState C))) ∧
      HiddenInv D (fun _ : C.Party => (none : Option (α × RunState C))) :=
  ⟨fun _ _ _ h => (by cases h), fun _ _ _ _ _ _ _ _ _ _ h => (by cases h)⟩

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The salts of an honest holder of a known term are the known salts. This is the part of
`KnownColumnsStatement` that does not need `KnownInv`. -/
theorem digestSalts_known (D : C.Coalition) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (table : C.Term → Fin 256 → Bit) (i : C.Party) (T : C.Term) (hiT : i ∈ C.holders T) (hT : KnownTo D.1 T) :
    digestSalts D knownB table i T = knownB.1 T := by
  simp only [digestSalts, frandShare, hiT, hT, ite_true]

omit [Fintype E] in
/-- After an output with no honest receiver the head plays no digest tail. -/
theorem digestAfter_none {Ia : Type} (K : Constants C E) (D : C.Coalition) (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (count L tg : ℕ)
    (hist : C.Party → C.Term → List Bit)
    (s : (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg)).State) :
    digestAfter K D W knownE knownB names count L tg hist (s, fun _ => none) = pure (s, fun _ => none) := by
  have hp : ¬ PartialOut D (fun _ : C.Party => (none : Option (HeadOut C E × RunState C))) :=
    fun h => by obtain ⟨-, i, -, hi⟩ := h; cases hi
  unfold digestAfter
  rw [ite_eq_right hp]

omit [DecidableEq E] [SampleableType E] in
/-- The fact behind `ExtendHiddenStatement`. Two honest receivers of `F_extendMult` that hold a hidden term
get the same values on it. A corrupt filler of a term holds it, so a hidden term has no offset. -/
theorem multFinish_hidden (K : Constants C E) (D : C.Coalition) (width : ℕ) (result : ℕ → E) (known : Shares C E)
    (offset : C.Party → Shares C E) (receivers : Finset C.Party) (fresh : C.Term → Fin width → E) (T : C.Term)
    (hT : ¬ KnownTo D.1 T) (i j : C.Party) (hi : i ∉ D.1) (hj : j ∉ D.1) (hir : i ∈ receivers)
    (hjr : j ∈ receivers) (hiT : i ∈ C.holders T) (hjT : j ∈ C.holders T) :
    (multFinish D width (filler K .peer) result known offset receivers fresh i).map (fun z => z T) =
      (multFinish D width (filler K .peer) result known offset receivers fresh j).map (fun z => z T) := by
  have hno : ∀ g, ¬ ∃ c ∈ D.1, filler K .peer T g = some c := fun g ⟨c, hc, hf⟩ =>
    hT ⟨c, hc, filler_held K .peer T g c hf⟩
  simp only [multFinish, hi, hj, hir, hjr, not_true_eq_false, or_false, ite_false, Option.map_some, hiT, hjT,
    true_and, hno, ite_false, add_zero]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- `KnownColumnsBoundStatement` holds. Each live holder makes one digest call. -/
theorem knownColumnsBound : KnownColumnsBoundStatement C := by
  intro live known hist T
  unfold knownColumns
  simpa only [Nat.mul_one] using RealNetworkC1p.isQueryBoundP_sequenceFin_le _ fun i =>
    RealNetworkC1p.liveCol_digest (· ∈ live) (fun _ => known) hist T i

end Steps

end ThresholdLeanXmssSecurity.RealNetworkC1r

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1v

open RealNetworkV3 RealNetworkC1s RealNetworkC1r

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-- A phase where each honest program fails or starts with a call, and one honest program fails, makes no
step. -/
theorem executePhase_dead {I O Ia L R α : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (fuel : ℕ) (st : A.State) (prog : C.Party → PartyM C E (CallSpec I O) α)
    (hcall : ∀ i, i ∉ D.1 → prog i = failure ∨
      ∃ v g, g none = failure ∧ prog i = call v >>= g)
    (hmissing : ∃ i, i ∉ D.1 ∧ prog i = failure) :
    executePhase localRoles D A F fuel st prog = pure (st, fun _ => none) := by
  let P : C.Party → Prop := fun i => prog i ≠ failure ∧ ∃ v g, g none = failure ∧ prog i = call v >>= g
  let input : C.Party → Option I := fun i => if h : P i then some h.2.choose else none
  let f : C.Party → Option O → PartyM C E (CallSpec I O) α := fun i =>
    if h : P i then h.2.choose_spec.choose else fun _ => failure
  have hf : ∀ i, i ∉ D.1 → f i none = failure := by
    intro i _
    by_cases h : P i
    · simp only [f, dite_eq_left_of_eq_true (eq_true h)]
      exact h.2.choose_spec.choose_spec.1
    · simp only [f, dite_eq_right_of_eq_false (eq_false h)]
  have hprog : ∀ i, i ∉ D.1 → prog i = optionalCall (input i) (f i) := by
    intro i hi
    by_cases h : P i
    · simp only [input, f, dite_eq_left_of_eq_true (eq_true h), optionalCall]
      exact h.2.choose_spec.choose_spec.2
    · simp only [input, dite_eq_right_of_eq_false (eq_false h), optionalCall]
      rcases hcall i hi with h' | h'
      · exact h'
      · by_contra hne
        exact h ⟨hne, h'⟩
  obtain ⟨a, ha, hfa⟩ := hmissing
  have hna : input a = none := by
    have h : ¬ P a := fun h => h.1 hfa
    simp only [input, dite_eq_right_of_eq_false (eq_false h)]
  rw [executePhase_congr_honest D A F fuel st prog _ hprog]
  cases fuel with
  | zero =>
    unfold executePhase
    rw [startSteps_optionalCall, pure_bind]
    simp only [executeRounds]
    congr 1
    refine Prod.ext rfl (funext fun i => ?_)
    simp only [optionalCallSteps]
    split_ifs
    · rfl
    · split <;> rfl
  | succ fuel => exact executePhase_partialCall_abort D A F fuel st input f hf ⟨a, ha, hna⟩

/-- `x.run s` is `.run'` of the program that returns the result of `x` with the state after it. -/
theorem run_eq_run' {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} (x : StateT σ m α)
    (s : σ) : x.run s = (x >>= fun a => (fun s' => (a, s')) <$> get).run' s := by
  simp [StateT.run'_eq, StateT.run_bind, StateT.run_get]

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] in
/-- A plan block after a partial output makes no step. -/
theorem planDead (K : Constants C E) (D : C.Coalition) : PlanDeadStatement K D := by
  intro Ia A fuel st o ho
  refine executePhase_dead D A _ fuel st _ (fun i _ => ?_) (ho.imp fun i h => ⟨h.1, by rw [h.2]; rfl⟩)
  rcases o i with _ | ⟨p, hs⟩
  · exact Or.inl rfl
  · right
    rw [Option.elim, run_eq_run']
    cases p with
    | mask A B V =>
      simp only [runPlan, maskHeadOf, bind_assoc]
      rw [randElements_run']
      exact ⟨_, _, rfl, rfl⟩
    | step products next =>
      simp only [runPlan, bind_assoc]
      rw [extendMult_run']
      exact ⟨_, _, rfl, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- A coin block after a partial output makes no step. -/
theorem coinDead (K : Constants C E) (D : C.Coalition) : CoinDeadStatement K D := by
  intro Ia A fuel st o ho
  refine executePhase_dead D A _ fuel st _ (fun i _ => ?_) (ho.imp fun i h => ⟨h.1, by rw [h.2]; rfl⟩)
  rcases o i with _ | ⟨next, hs⟩
  · exact Or.inl rfl
  · right
    rw [Option.elim, run_eq_run']
    simp only [hybridCoin, bind_assoc]
    rw [challenge_run']
    exact ⟨_, _, rfl, rfl⟩

end ThresholdLeanXmssSecurity.RealNetworkC1v

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1v

open RealNetworkV3 RealNetworkC1s RealNetworkC1r

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- The real digests of a known term on drawn salts are the known columns of the wrapper. -/
theorem knownColumns (D : C.Coalition) : KnownColumnsStatement (E := E) D := by
  intro knownB mem out hinv table T hT
  unfold RealNetworkC1s.knownColumns
  refine congrArg _ (funext fun i => ?_)
  unfold RealNetworkRC.liveCol
  have hlive : (i ∈ RealNetworkRC.liveSet D fun i => (out i).map Prod.snd) ↔ i ∈ liveSet D out := by
    simp [RealNetworkRC.liveSet, liveSet]
  by_cases h : i ∈ liveSet D out ∧ i ∈ C.holders T
  · rw [ite_eq_left ⟨hlive.2 h.1, h.2⟩, ite_eq_left h]
    obtain ⟨hi, hz⟩ := (Finset.mem_filter.1 h.1).2
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hz
    rw [digestSalts_known D knownB table i T h.2 hT, hinv i hi z hz T hT]
    simp [RealNetworkRC.histOf, hz]
  · rw [ite_eq_right fun h' => h ⟨hlive.1 h'.1, h'.2⟩, ite_eq_right h]

/-- The salts of an honest holder of a hidden term are the row of the table. This is the premise `hsalt`
of `realDigestPhase_partial_hide` for the salts `digestSalts D knownB`. -/
theorem digestSalts_hidden (D : C.Coalition) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) :
    ∀ (table : C.Term → Fin 256 → Bit) (T : C.Term), ¬ KnownTo D.1 T → ∀ i ∉ D.1, i ∈ C.holders T →
      vector 256 (digestSalts D knownB table i T) = List.ofFn (table T) := by
  intro table T hT i _ hiT
  simp only [digestSalts, frandShare, hiT, hT, ite_true, ite_false, vector]
  apply List.ext_getElem (by simp only [List.length_map, List.length_range, List.length_ofFn])
  intro n h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, dite_eq_left_of_eq_true (eq_true h1)]

end ThresholdLeanXmssSecurity.RealNetworkC1v

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1v

open RealNetworkV3 RealNetworkC1s RealNetworkC1q RealNetworkC1r

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [DecidableEq E] [SampleableType E] in
/-- Two honest outputs of `multFinish` agree on a hidden term that both operators hold. -/
theorem multFinish_hidden_of_some (K : Constants C E) (D : C.Coalition) (width : ℕ) (result : ℕ → E)
    (known : Shares C E) (offset : C.Party → Shares C E) (receivers : Finset C.Party)
    (fresh : C.Term → Fin width → E) (T : C.Term) (hT : ¬ KnownTo D.1 T) (i j : C.Party) (hi : i ∉ D.1)
    (hj : j ∉ D.1) (hiT : i ∈ C.holders T) (hjT : j ∈ C.holders T) (mi mj : Shares C E)
    (hmi : multFinish D width (filler K .peer) result known offset receivers fresh i = some mi)
    (hmj : multFinish D width (filler K .peer) result known offset receivers fresh j = some mj) :
    mi T = mj T := by
  have hir : i ∈ receivers := by
    by_contra h
    simp [multFinish, h] at hmi
  have hjr : j ∈ receivers := by
    by_contra h
    simp [multFinish, h] at hmj
  have h := multFinish_hidden K D width result known offset receivers fresh T hT i j hi hj hir hjr hiT hjT
  rw [hmi, hmj] at h
  simpa using h

/-- The hidden histories of two honest receivers stay equal through a call of `F_extendMult`. -/
theorem extendHidden (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    ExtendHiddenStatement prims K D := by
  intro Ia W knownE knownB count L tg hist names fuel k s products hs cache hlen hh z hz
  have h1 := fst_mem_support_run prims _ cache z hz
  rw [RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun i => Sum.inl (Sum.inr (products i)))
    (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z))
    (pure () : OracleComp (LocalSpec C) Unit)
    (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
    (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
    (fun _ r fresh => extendOutputs K D products r fresh) _ (fun st => extendRun_form K D _ st products)] at h1
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h1
  obtain ⟨-, -, a, ha, fresh, -, hz1⟩ := h1
  rw [hz1]
  intro T hT i j hi hj hiT hjT zi zj hzi hzj
  simp only [hi, hj, ite_false, extendOutputs, Option.bind_map, Function.comp_def, extendOutput,
    Option.map_some, Option.bind_eq_some_iff, Option.some.injEq] at hzi hzj
  obtain ⟨mi, hmi, rfl⟩ := hzi
  obtain ⟨mj, hmj, rfl⟩ := hzj
  have h := multFinish_hidden_of_some K D _ _ _ _ _ fresh T hT i j hi hj hiT hjT mi mj hmi hmj
  simp only [extendState, recordHistory, hiT, hjT, ite_true, h, hh T hT i j hi hj hiT hjT]

end ThresholdLeanXmssSecurity.RealNetworkC1v

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1v

open RealNetworkV3 RealNetworkC1s RealNetworkC1r

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] in
/-- After a partial output of the head the rest of the check makes no step. -/
theorem restAbort (K : Constants C E) (D : C.Coalition) : RestAbortStatement K D := by
  intro Ia A s o ho
  obtain ⟨⟨a, ha, hoa⟩, -⟩ := ho
  let next : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) →
      PartyM C E (CheckSpec C E) Unit := fun i r => match r with
    | some (.inr (.inr w)) => (o i).elim failure fun p =>
        (compareDigests (localContext i) w.1 >>= fun _ => finalAfterDigests K i
          (conv K (localContext i) p.1.2.2.2.1 0) (conv K (localContext i) p.1.2.2.2.1 1) p.1.1 p.1.2.1
          p.1.2.2.1 (conv K (localContext i) p.1.2.2.2.2 0) (conv K (localContext i) p.1.2.2.2.2 1)).run'
          ⟨p.2.history, p.2.label + 1, p.2.tag⟩
    | _ => failure
  have hp : (fun i => (o i).elim failure (restAt K i)) =
      fun i => optionalCall ((o i).map fun _ => .inr (.inr 256)) (next i) := by
    funext i
    rcases hi : o i with _ | p
    · rfl
    · simp only [Option.elim, Option.map, optionalCall, restAt, checkRest, finalRest]
      rw [randBits_run']
      refine bind_congr fun r => ?_
      rcases r with _ | ((u | u) | (u | u)) <;> simp [next, hi]
  rw [hp]
  exact executePhase_partialCall_abort D A (checkFunctionalities K) 4 s _ next (fun _ _ => rfl)
    ⟨a, ha, by rw [hoa]; rfl⟩

end ThresholdLeanXmssSecurity.RealNetworkC1v

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1x

open RealNetworkV3 RealNetworkC1s RealNetworkC1r RealNetworkC1v

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

section Claim

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
  (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
  (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
  (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (count L tg : ℕ)
  (hist : C.Party → C.Term → List Bit)

/-- The claim of `HeadTailsStatement` for the programs `prog` from position `n` with `f` steps of fuel.
-/
def TailsAt (f n : ℕ) (prog : C.Party → PartyM C E (CheckSpec C E) (HeadOut C E × RunState C)) : Prop :=
  ∀ s : W.State × C1Memory C E, SameRun prims
    (executePhase localRoles D
      (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
      (checkFunctionalities K) f (s, n) prog)
    (executePhase localRoles D
        (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
        (checkFunctionalities K) f (s, n) prog >>=
      digestAfter K D W knownE knownB names count L tg hist)

omit [Fintype E] in
theorem tailsSuffix_of (n f : ℕ) {β : Type} (Rel : (C.Party → β) → Prop)
    (kH : C.Party → β → RunM C E (CheckSpec C E) (HeadOut C E))
    (h : ∀ (b : C.Party → β) (hs : C.Party → RunState C), Rel b →
      TailsAt prims K D W knownE knownB names count L tg hist f n (fun i => (kH i (b i)).run (hs i))) :
    TailsSuffix prims K D W knownE knownB names count L tg hist n f Rel kH :=
  fun st mem b hs hb => h b hs hb (st, mem)

omit [Fintype E] in
theorem tailsAt_of_suffix (n f : ℕ) {β : Type} (Rel : (C.Party → β) → Prop)
    (kH : C.Party → β → RunM C E (CheckSpec C E) (HeadOut C E))
    (h : TailsSuffix prims K D W knownE knownB names count L tg hist n f Rel kH)
    (b : C.Party → β) (hs : C.Party → RunState C) (hb : Rel b) :
    TailsAt prims K D W knownE knownB names count L tg hist f n (fun i => (kH i (b i)).run (hs i)) :=
  fun s => h s.1 s.2 b hs hb

omit [Fintype E] in
/-- Programs that make no step on each adversary. -/
theorem tailsAt_dead (f n : ℕ) (prog : C.Party → PartyM C E (CheckSpec C E) (HeadOut C E × RunState C))
    (h : ∀ (A : CheckAdversary C E Ia) (st : A.State),
      executePhase localRoles D A (checkFunctionalities K) f st prog = pure (st, fun _ => none)) :
    TailsAt prims K D W knownE knownB names count L tg hist f n prog := by
  intro s
  rw [h, h, pure_bind, digestAfter_none]
  exact SameRun.refl prims _

omit [Fintype E] in
theorem tailsAt_congr (f n : ℕ) (p p' : C.Party → PartyM C E (CheckSpec C E) (HeadOut C E × RunState C))
    (hp : ∀ i, i ∉ D.1 → p i = p' i) (h : TailsAt prims K D W knownE knownB names count L tg hist f n p') :
    TailsAt prims K D W knownE knownB names count L tg hist f n p := by
  intro s
  rw [executePhase_congr_honest D _ _ f _ p p' hp, executePhase_congr_honest D _ _ f _ p p' hp]
  exact h s

omit [Fintype E] in
/-- The split of an output. -/
theorem tailsAt_elim (f n : ℕ) {β : Type} (o : C.Party → Option β)
    (k : C.Party → β → PartyM C E (CheckSpec C E) (HeadOut C E × RunState C))
    (hdead : (∃ i, i ∉ D.1 ∧ o i = none) → ∀ (A : CheckAdversary C E Ia) (st : A.State),
      executePhase localRoles D A (checkFunctionalities K) f st (fun i => (o i).elim failure (k i)) =
        pure (st, fun _ => none))
    (hfull : ∀ b : C.Party → β, (∀ i, i ∉ D.1 → o i = some (b i)) →
      TailsAt prims K D W knownE knownB names count L tg hist f n (fun i => k i (b i))) :
    TailsAt prims K D W knownE knownB names count L tg hist f n (fun i => (o i).elim failure (k i)) := by
  by_cases hn : ∃ i, i ∉ D.1 ∧ o i = none
  · exact tailsAt_dead prims K D W knownE knownB names count L tg hist f n _ (hdead hn)
  push Not at hn
  obtain ⟨i₀, hi₀⟩ := exists_honest D
  obtain ⟨b₀, -⟩ := Option.ne_none_iff_exists'.1 (hn i₀ hi₀)
  let b : C.Party → β := fun i => (o i).getD b₀
  have hb : ∀ i, i ∉ D.1 → o i = some (b i) := fun i hi => by
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (hn i hi)
    simp only [b, hx, Option.getD_some]
  refine tailsAt_congr prims K D W knownE knownB names count L tg hist f n _ _ (fun i hi => ?_) (hfull b hb)
  rw [hb i hi, Option.elim_some]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- The form of the answer of the wrapper. The state types unify only up to the unfolding of the
state of the wrapper, so the counter lemma closes with `exact` on this form. -/
theorem bind_ite_counter {S R : Type} (x : OracleComp (LocalSpec C) (S × R)) (P : S × R → Prop)
    (t : S × R → OracleComp (LocalSpec C) S) (c : ℕ) :
    (x >>= fun a => if P a then (fun st' => ((st', c), a.2)) <$> t a else pure ((a.1, c), a.2)) =
      (fun a => ((a.1.1, c), a.2)) <$>
        (x >>= fun a => if P a then (fun st' => ((st', c), a.2)) <$> t a else pure ((a.1, c), a.2)) := by
  rw [map_bind]
  refine bind_congr fun a => ?_
  split_ifs <;> simp

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- After an answer of the wrapper the counter is `c`. -/
theorem sameRun_bind_counter {S R Z : Type} (x : OracleComp (LocalSpec C) (S × R)) (P : S × R → Prop)
    (t : S × R → OracleComp (LocalSpec C) S) (c : ℕ) (G₁ G₂ : (S × ℕ) × R → OracleComp (LocalSpec C) Z)
    (h : ∀ st r, SameRun prims (G₁ ((st, c), r)) (G₂ ((st, c), r))) :
    SameRun prims
      ((x >>= fun a => if P a then (fun st' => ((st', c), a.2)) <$> t a else pure ((a.1, c), a.2)) >>= G₁)
      ((x >>= fun a => if P a then (fun st' => ((st', c), a.2)) <$> t a else pure ((a.1, c), a.2)) >>= G₂) := by
  rw [bind_ite_counter x P t c, bind_map_left, bind_map_left]
  exact SameRun.bind_right _ fun a => h a.1.1 a.2

omit [Fintype E] in
/-- A call at a position other than the digest round. -/
theorem tailsAt_call (k fuel : ℕ) (hk : k ≠ 2 * halvings count + 2) {P X : Type}
    (input : C.Party → (ℕ ⊕ List (Product C E)) ⊕ (ℕ ⊕ ℕ))
    (f : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) →
      PartyM C E (CheckSpec C E) (HeadOut C E × RunState C))
    (pre : OracleComp (LocalSpec C) P) (lk : P → CheckLeak C E)
    (samp : P → CheckAnswer C E → OracleComp (LocalSpec C) X)
    (outF : P → CheckAnswer C E → X → C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)))
    (hF : ∀ (A : CheckAdversary C E Ia) (st : A.State),
      runFunctionality localRoles D A (checkFunctionalities K) st (fun i => if i ∈ D.1 then none else some (input i)) =
        pre >>= fun p => A.answer st (lk p) >>= fun a => samp p a.2 >>= fun x => pure (a.1, outF p a.2 x))
    (hrest : ∀ out : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)),
      TailsAt prims K D W knownE knownB names count L tg hist fuel (k + 1) (fun i => f i (out i))) :
    TailsAt prims K D W knownE knownB names count L tg hist (fuel + 1) k (fun i => call (input i) >>= f i) := by
  intro s
  rw [executePhase_call, executePhase_call, hF, hF]
  simp only [bind_assoc, pure_bind]
  refine SameRun.bind_right _ fun p => ?_
  simp only [c1HeadTails, hk, ↓reduceIte]
  refine sameRun_bind_counter prims _ _ _ _ _ _ fun st r => SameRun.bind_right _ fun x => ?_
  exact hrest (outF p r x) st

/-- A call of `F_rand` for two elements. Its answer runs no tail. -/
theorem tailsAt_rand (hn : NamesReceivers D names) (k fuel : ℕ)
    (f : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) →
      PartyM C E (CheckSpec C E) (HeadOut C E × RunState C))
    (hrest : ∀ out : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)),
      TailsAt prims K D W knownE knownB names count L tg hist fuel (k + 1) (fun i => f i (out i))) :
    TailsAt prims K D W knownE knownB names count L tg hist (fuel + 1) k
      (fun i => call (Sum.inr (Sum.inl 2)) >>= f i) := by
  intro s
  rw [executePhase_call, executePhase_call, runCheck_randElements K D _ _ (fun _ => 2),
    runCheck_randElements K D _ _ (fun _ => 2), bind_map_left, bind_map_left,
    runFunctionality_rand_local D _ _ _ (by intro i hi; simp [hi]),
    runFunctionality_rand_local D _ _ _ (by intro i hi; simp [hi]),
    RealNetworkC1u.frandElements_answer K D W knownE knownB count hist names hn _ s k,
    RealNetworkC1u.frandElements_answer K D W knownE knownB count hist names hn _ s k, pure_bind]
  simp only [bind_assoc, pure_bind]
  exact SameRun.bind_right _ fun a => SameRun.bind_right _ fun b => hrest _ s

omit [Fintype E] in
/-- The values of `H` of the honest operators move to the front. -/
theorem tailsAt_oracle (f n : ℕ) {γ : Type} (d : γ) (q : C.Party → OracleComp (RoSpec C) γ)
    (g : C.Party → γ → PartyM C E (CheckSpec C E) (HeadOut C E × RunState C))
    (h : ∀ w : C.Party → γ, TailsAt prims K D W knownE knownB names count L tg hist f n (fun i => g i (w i))) :
    TailsAt prims K D W knownE knownB names count L tg hist f n (fun i => oracleStep (q i) >>= g i) := by
  intro s
  have h₁ := executePhase_oracleStep_bind prims D
    (c1WrapperWith K D W knownE knownB count hist names (c1Tails K D W knownE knownB count L tg))
    (checkFunctionalities K) d f (s, n) q g
  have h₂ := executePhase_oracleStep_bind prims D
    (c1WrapperWith K D W knownE knownB count hist names (c1HeadTails K D W knownE knownB count L tg))
    (checkFunctionalities K) d f (s, n) q g
  have h₃ := h₂.bind fun r => SameRun.refl prims (digestAfter K D W knownE knownB names count L tg hist r)
  rw [bind_assoc] at h₃
  exact h₁.trans ((SameRun.bind_right _ fun w => h w s).trans h₃.symm)

end Claim

end ThresholdLeanXmssSecurity.RealNetworkC1x

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1x

open RealNetworkV3 RealNetworkC1s RealNetworkC1r RealNetworkC1v

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The search of the challenge after the output `o` of `F_coin`. -/
def coinSearch (K : Constants C E) (hs : RunState C)
    (o : Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit))) : OracleComp (RoSpec C) (Option E) :=
  match o.bind coinOutput with
  | some v => challengeQuery K hs.tag hs.label v
  | none => pure none

/-- The plan and the state after the output `o` of `F_coin` and the challenge `w`. -/
def coinNext (hs : RunState C) (next : E → Plan C E)
    (o : Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit))) (w : Option E) :
    Option (Plan C E × RunState C) :=
  (o.bind coinOutput).bind fun _ => w.map fun r => (next r, ⟨hs.history, hs.label + 1, hs.tag⟩)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- `hybridCoin` is the call of `F_coin`, the search of the challenge and the plan. -/
theorem coin_run (K : Constants C E) (i : C.Party) (hs : RunState C) (next : E → Plan C E) :
    (hybridCoin K i next).run hs =
      call (Sum.inl (Sum.inl 2)) >>= fun o => oracleStep (coinSearch K hs o) >>= fun w =>
        (coinNext hs next o w).elim failure fun p =>
          (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p.1).run p.2 := by
  rw [run_eq_run']
  simp only [hybridCoin, bind_assoc]
  rw [challenge_run']
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | w) <;>
    simp only [coinSearch, coinNext, coinOutput, Option.bind_none, Option.bind_some, oracleStep_pure, pure_bind,
      Option.elim_none]
  refine bind_congr fun r => ?_
  rcases r with _ | r
  · rfl
  · simp only [Option.map_some, Option.elim_some]
    rw [run_eq_run']

theorem tailsCoinBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    TailsCoinBlockStatement prims K D := by
  intro Ia W knownE knownB names hn count L tg hist j d hjd hIH
  refine tailsSuffix_of prims K D W knownE knownB names count L tg hist _ _ _ _ fun next hs hRel => ?_
  refine tailsAt_congr prims K D W knownE knownB names count L tg hist _ _ _
    (fun i => call (Sum.inl (Sum.inl 2)) >>= fun o => oracleStep (coinSearch K (hs i) o) >>= fun w =>
      (coinNext (hs i) (next i) o w).elim failure fun p =>
        (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p.1).run p.2)
    (fun i _ => coin_run K i (hs i) (next i)) ?_
  refine tailsAt_call prims K D W knownE knownB names count L tg hist (2 * j + 2) (2 * d + 2) (by omega)
    (fun _ => Sum.inl (Sum.inl 2)) _ (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C))
    (fun v => Sum.inl (Sum.inl (List.ofFn v))) (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit))
    (fun v r _ => coinOutputs D v r) (fun A st => coinRun_form K D A st) fun out => ?_
  refine tailsAt_oracle prims K D W knownE knownB names count L tg hist _ _ none
    (fun i => coinSearch K (hs i) (out i)) _ fun w => ?_
  refine tailsAt_elim prims K D W knownE knownB names count L tg hist _ _
    (fun i => coinNext (hs i) (next i) (out i) (w i))
    (fun i p => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p.1).run p.2)
    (fun hdead A st => planDead K D A _ st _ hdead) (fun b hb => ?_)
  rw [show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by omega]
  refine tailsAt_of_suffix prims K D W knownE knownB names count L tg hist _ _ _ _ hIH (fun i => (b i).1)
    (fun i => (b i).2) fun i hi => ?_
  have h := hb i hi
  simp only [coinNext, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨-, -, r, -, hr⟩ := h
  rw [← hr]
  exact hRel i hi r

end ThresholdLeanXmssSecurity.RealNetworkC1x

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1x

open RealNetworkV3 RealNetworkC1s RealNetworkC1r RealNetworkC1v

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- A step of a plan in the hybrid model is the call of `F_extendMult` and then `hybridCoin`. -/
theorem step_run (K : Constants C E) (i : C.Party) (hs : RunState C) (products : List (Product C E))
    (next : Shares C E → E → Plan C E) :
    (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (.step products next)).run hs =
      call (Sum.inl (Sum.inr products)) >>= fun o => (o.bind extendOutput).elim failure fun z =>
        (hybridCoin K i (next z)).run ⟨recordHistory K i hs.history z products.length, hs.label + 1, hs.tag⟩ := by
  rw [run_eq_run']
  simp only [runPlan, bind_assoc]
  rw [extendMult_run']
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | w) <;> try rfl
  simp only [Option.bind_some, extendOutput, Option.elim_some]
  rw [run_eq_run' (hybridCoin K i (next z))]
  simp only [hybridCoin, bind_assoc]

theorem tailsExtendBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    TailsExtendBlockStatement prims K D := by
  intro Ia W knownE knownB names hn count L tg hist j d hjd hIH
  refine tailsSuffix_of prims K D W knownE knownB names count L tg hist _ _ _ _ fun p hs hRel => ?_
  let products : C.Party → List (Product C E) := fun i => match p i with
    | .step ps _ => ps
    | .mask _ _ _ => []
  let next : C.Party → Shares C E → E → Plan C E := fun i => match p i with
    | .step _ nx => nx
    | .mask _ _ _ => fun _ _ => p i
  have hp : ∀ i, i ∉ D.1 → p i = .step (products i) (next i) ∧ (products i).length = 2 ∧
      ∀ z r, PlanOK (next i z r) d := by
    intro i hi
    have h := hRel i hi
    simp only [products, next]
    cases hpi : p i with
    | mask A B V =>
      rw [hpi] at h
      simp only [PlanOK] at h
      omega
    | step ps nx =>
      rw [hpi] at h
      obtain ⟨hl, d', hd, hnx⟩ := h
      obtain rfl : d' = d := by omega
      exact ⟨rfl, hl, hnx⟩
  let st' : C.Party → Shares C E → RunState C := fun i z =>
    ⟨recordHistory K i (hs i).history z (products i).length, (hs i).label + 1, (hs i).tag⟩
  rw [show 2 * (d + 1) + 2 = 2 * d + 3 + 1 by omega]
  refine tailsAt_congr prims K D W knownE knownB names count L tg hist _ _ _
    (fun i => call (Sum.inl (Sum.inr (products i))) >>= fun o => (o.bind extendOutput).elim failure fun z =>
      (hybridCoin K i (next i z)).run (st' i z)) (fun i hi => by rw [(hp i hi).1, step_run]) ?_
  refine tailsAt_call prims K D W knownE knownB names count L tg hist (2 * j + 1) (2 * d + 3) (by omega)
    (fun i => Sum.inl (Sum.inr (products i))) _ (pure () : OracleComp (LocalSpec C) Unit)
    (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
    (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
    (fun _ r fresh => extendOutputs K D products r fresh) (fun A st => extendRun_form K D A st products) fun out => ?_
  refine tailsAt_elim prims K D W knownE knownB names count L tg hist _ _ (fun i => (out i).bind extendOutput)
    (fun i z => (hybridCoin K i (next i z)).run (st' i z)) (fun hdead A st => ?_) (fun b hb => ?_)
  · have h := coinDead K D A (2 * d + 3) st (fun i => ((out i).bind extendOutput).map fun z => (next i z, st' i z))
      (hdead.imp fun i h => ⟨h.1, by rw [h.2]; rfl⟩)
    rw [← h]
    congr 1
    funext i
    cases (out i).bind extendOutput <;> rfl
  · rw [show 2 * j + 1 + 1 = 2 * j + 2 by omega]
    exact tailsAt_of_suffix prims K D W knownE knownB names count L tg hist _ _ _ _ hIH (fun i => next i (b i))
      (fun i => st' i (b i)) fun i hi r => (hp i hi).2.2 (b i) r

end ThresholdLeanXmssSecurity.RealNetworkC1x

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1x

open RealNetworkV3 RealNetworkC1s RealNetworkC1r RealNetworkC1v

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The coins `τ` after the output `o` of the first `F_coin`. -/
def startSearch (K : Constants C E) (count : ℕ) (hs : RunState C)
    (o : Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit))) : OracleComp (RoSpec C) (List E) :=
  match o.bind coinOutput with
  | some v => hashQuery (.coinKey hs.tag hs.label (v.flatMap fun x => List.ofFn (K.encode x))) >>= fun key =>
      (List.range (coins count)).mapM fun k => elementOfHash K <$> hashQuery (.expand key k)
  | none => pure []

/-- The plan and the state after the output `o` of the first `F_coin` and the coins `τ`. -/
def startNext (hs : RunState C) (next : List E → Plan C E)
    (o : Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit))) (τ : List E) :
    Option (Plan C E × RunState C) :=
  (o.bind coinOutput).bind fun _ =>
    if ∀ b < sliceBits, τ.getD b 0 ≠ 0 then some (next τ, ⟨hs.history, hs.label + 1, hs.tag⟩) else none

omit [Fintype E] [SampleableType E] in
/-- `hybridStart` is the call of `F_coin`, the values of `H`, the test of the slice coins and the plan. -/
theorem start_run (K : Constants C E) (count : ℕ) (i : C.Party) (hs : RunState C) (next : List E → Plan C E) :
    (hybridStart K count i next).run hs =
      call (Sum.inl (Sum.inl 2)) >>= fun o => oracleStep (startSearch K count hs o) >>= fun τ =>
        (startNext hs next o τ).elim failure fun p =>
          (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p.1).run p.2 := by
  simp only [hybridStart, coinKey, expand, bind_assoc, hybridCheckBuildingBlocks, freshLabel, StateT.run_bind,
    StateT.run_get, StateT.run_modifyGet, StateT.run_lift, pure_bind]
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | w) <;>
    simp only [startSearch, startNext, coinOutput, Option.bind_none, Option.bind_some, oracleStep_pure, pure_bind,
      Option.elim_none, StateT.run_lift, StateT.run_pure, bind_assoc]
  · exact failure_bind _
  · rw [oracleStep_bind]
    simp only [bind_assoc]
    refine bind_congr fun key => bind_congr fun τ => ?_
    by_cases h : ∀ b < sliceBits, τ.getD b 0 ≠ 0
    · simp only [require]
      rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h), pure_bind, Option.elim_some]
    · simp only [require, h, ↓reduceIte, failure_bind, Option.elim_none]
  · exact failure_bind _
  · exact failure_bind _

theorem tailsFirstBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    TailsFirstBlockStatement prims K D := by
  intro Ia W knownE knownB names hn count L tg hist hIH
  refine tailsSuffix_of prims K D W knownE knownB names count L tg hist _ _ _ _ fun next hs hRel => ?_
  refine tailsAt_congr prims K D W knownE knownB names count L tg hist _ _ _
    (fun i => call (Sum.inl (Sum.inl 2)) >>= fun o => oracleStep (startSearch K count (hs i) o) >>= fun τ =>
      (startNext (hs i) (next i) o τ).elim failure fun p =>
        (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p.1).run p.2)
    (fun i _ => start_run K count i (hs i) (next i)) ?_
  refine tailsAt_call prims K D W knownE knownB names count L tg hist 0 (2 * halvings count + 2) (by omega)
    (fun _ => Sum.inl (Sum.inl 2)) _ (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C))
    (fun v => Sum.inl (Sum.inl (List.ofFn v))) (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit))
    (fun v r _ => coinOutputs D v r) (fun A st => coinRun_form K D A st) fun out => ?_
  refine tailsAt_oracle prims K D W knownE knownB names count L tg hist _ _ []
    (fun i => startSearch K count (hs i) (out i)) _ fun τ => ?_
  refine tailsAt_elim prims K D W knownE knownB names count L tg hist _ _
    (fun i => startNext (hs i) (next i) (out i) (τ i))
    (fun i p => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p.1).run p.2)
    (fun hdead A st => planDead K D A _ st _ hdead) (fun b hb => ?_)
  rw [show 0 + 1 = 2 * 0 + 1 by omega]
  refine tailsAt_of_suffix prims K D W knownE knownB names count L tg hist _ _ _ _ hIH (fun i => (b i).1)
    (fun i => (b i).2) fun i hi => ?_
  have h := hb i hi
  simp only [startNext, Option.bind_eq_some_iff] at h
  obtain ⟨-, -, h⟩ := h
  split_ifs at h
  rw [← Option.some_inj.1 h]
  exact hRel i hi (τ i)

end ThresholdLeanXmssSecurity.RealNetworkC1x

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1x

open RealNetworkV3 RealNetworkC1s RealNetworkC1r RealNetworkC1v

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The output of `F_rand` for elements. -/
def randOutput : (List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit) → Option (PrssOutput C E)
  | .inr (.inl w) => some w
  | _ => none

/-- The two products of the masked multiplication on the mask `w`. -/
def maskProducts (K : Constants C E) (i : C.Party) (A B : ℕ → E) (w : PrssOutput C E) : List (Product C E) :=
  [.shamir (fun _ => conv K (localContext i) w.1 0) (fun _ => conv K (localContext i) w.1 1) 1,
    .shamir (fun _ => conv K (localContext i) w.1 0 + A 0) (fun _ => conv K (localContext i) w.1 1 + B 0) 1]

/-- The output of the masked multiplication. -/
def maskOut (K : Constants C E) (i : C.Party) (hs : RunState C) (A B : ℕ → E) (V : E) (w : PrssOutput C E)
    (z : Shares C E) : HeadOut C E × RunState C :=
  ((A 0, B 0, V, w.1, z), ⟨recordHistory K i hs.history z 2, hs.label + 1 + 1, hs.tag⟩)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The masked multiplication is the call of `F_rand`, the call of `F_extendMult` and the output. -/
theorem mask_run (K : Constants C E) (i : C.Party) (hs : RunState C) (A B : ℕ → E) (V : E) :
    (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (.mask A B V)).run hs =
      call (Sum.inr (Sum.inl 2)) >>= fun o => (o.bind randOutput).elim failure fun w =>
        call (Sum.inl (Sum.inr (maskProducts K i A B w))) >>= fun o' =>
          (o'.bind extendOutput).elim failure fun z => pure (maskOut K i hs A B V w z) := by
  rw [run_eq_run']
  simp only [runPlan, maskHeadOf, bind_assoc]
  rw [randElements_run']
  refine bind_congr fun o => ?_
  rcases o with _ | ((v | z) | (w | w)) <;> try rfl
  simp only [Option.bind_some, randOutput, Option.elim_some]
  rw [extendMult_run']
  refine bind_congr fun o' => ?_
  rcases o' with _ | ((v | z) | w) <;> try rfl

/-- The call of `F_extendMult` at the digest round, with the output at once. -/
theorem maskLast (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (hn : NamesReceivers D names) (count L tg : ℕ)
    (hist : C.Party → C.Term → List Bit) (products : C.Party → List (Product C E))
    (out : C.Party → Shares C E → HeadOut C E × RunState C) :
    TailsAt prims K D W knownE knownB names count L tg hist 1 (2 * halvings count + 2)
      (fun i => call (Sum.inl (Sum.inr (products i))) >>= fun o =>
        (o.bind extendOutput).elim failure fun z => pure (out i z)) := by
  intro s
  have hp : (fun i => call (Sum.inl (Sum.inr (products i))) >>= fun o =>
      (o.bind extendOutput).elim failure fun z => (pure (out i z) : PartyM C E (CheckSpec C E) _)) =
      fun i => RealNetworkGP.callProg (Sum.inl (Sum.inr (products i))) (fun o => (extendOutput o).map (out i)) := by
    funext i
    unfold RealNetworkGP.callProg
    refine bind_congr fun r => ?_
    rcases r with _ | o
    · rfl
    · simp only [Option.bind_some]
      cases extendOutput o <;> rfl
  have hnames : ∀ (u : Unit) (r : CheckAnswer C E)
      (fresh : C.Term → Fin (firstInput (fullInputs D products)).length → E), ∀ j ∉ D.1,
      ((extendOutputs K D products r fresh j).bind fun o => (extendOutput o).map (out j)).isSome ↔
        names (Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products)))) r j := by
    intro _ r fresh j hj
    rw [hn _ _ j hj]
    unfold extendOutputs multFinish
    by_cases h : j ∈ (extendReply r).2.2.2 <;> simp [hj, h, c1Names, extendOutput]
  have htail : ∀ tails, SameRun prims
      (RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names tails)
        (checkFunctionalities K) (0 + 1) (s, 2 * halvings count + 2) (fun i => Sum.inl (Sum.inr (products i)))
        (fun i o => (extendOutput o).map (out i)))
      (RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails)
          (checkFunctionalities K) (0 + 1) (s, 2 * halvings count + 2) (fun i => Sum.inl (Sum.inr (products i)))
          (fun i o => (extendOutput o).map (out i)) >>=
        fun r => if PartialOut D r.2 then
          (fun s' => ((s', r.1.2), r.2)) <$> tails (2 * halvings count + 2) (liveSet D r.2) r.1.1
        else pure r) := by
    intro tails
    have h := RealNetworkGP.callPhase_tail D (checkFunctionalities K)
      (fun i => Sum.inl (Sum.inr (products i))) (fun i o => (extendOutput o).map (out i))
      (pure () : OracleComp (LocalSpec C) Unit)
      (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
      (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
      (fun _ r fresh => extendOutputs K D products r fresh) prims
      (relabel (withMemory W (C1Memory C E) ⟨hist, []⟩) (checkReply (C := C) (E := E)))
      (c1Sims K D W knownE knownB) names tails
      (fun A st => extendRun_form K D A st products) hnames 0 s (2 * halvings count + 2)
    rw [RealNetworkGP.callPhase_eq D (checkFunctionalities K)
        (fun i => Sum.inl (Sum.inr (products i))) (fun i o => (extendOutput o).map (out i))
        (pure () : OracleComp (LocalSpec C) Unit)
        (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
        (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
        (fun _ r fresh => extendOutputs K D products r fresh) _ (fun st => extendRun_form K D _ st products),
      RealNetworkGP.callPhase_eq D (checkFunctionalities K)
        (fun i => Sum.inl (Sum.inr (products i))) (fun i o => (extendOutput o).map (out i))
        (pure () : OracleComp (LocalSpec C) Unit)
        (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
        (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
        (fun _ r fresh => extendOutputs K D products r fresh) _ (fun st => extendRun_form K D _ st products)] at h
    rw [RealNetworkGP.callPhase_eq D (checkFunctionalities K)
        (fun i => Sum.inl (Sum.inr (products i))) (fun i o => (extendOutput o).map (out i))
        (pure () : OracleComp (LocalSpec C) Unit)
        (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
        (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
        (fun _ r fresh => extendOutputs K D products r fresh) _ (fun st => extendRun_form K D _ st products),
      RealNetworkGP.callPhase_eq D (checkFunctionalities K)
        (fun i => Sum.inl (Sum.inr (products i))) (fun i o => (extendOutput o).map (out i))
        (pure () : OracleComp (LocalSpec C) Unit)
        (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
        (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
        (fun _ r fresh => extendOutputs K D products r fresh) _ (fun st => extendRun_form K D _ st products)]
    exact h
  rw [hp]
  refine (htail (c1Tails K D W knownE knownB count L tg)).trans ?_
  refine SameRun.trans ?_ ((htail (c1HeadTails K D W knownE knownB count L tg)).bind fun r =>
    SameRun.refl prims (digestAfter K D W knownE knownB names count L tg hist r)).symm
  rw [bind_assoc]
  refine SameRun.bind_right _ fun r => SameRun.of_eq ?_
  unfold digestAfter
  by_cases h : PartialOut D r.2
  · simp only [h, ↓reduceIte, c1HeadTails]
    erw [map_pure, pure_bind]
    simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, pure_bind]

theorem tailsMaskBlock (prims : Primitives) (K : Constants C E) (D : C.Coalition) :
    TailsMaskBlockStatement prims K D := by
  intro Ia W knownE knownB names hn count L tg hist
  refine tailsSuffix_of prims K D W knownE knownB names count L tg hist _ _ _ _ fun p hs hRel => ?_
  let maskA : C.Party → ℕ → E := fun i => match p i with
    | .mask A _ _ => A
    | .step _ _ => fun _ => 0
  let maskB : C.Party → ℕ → E := fun i => match p i with
    | .mask _ B _ => B
    | .step _ _ => fun _ => 0
  let maskV : C.Party → E := fun i => match p i with
    | .mask _ _ V => V
    | .step _ _ => 0
  have hp : ∀ i, i ∉ D.1 → p i = .mask (maskA i) (maskB i) (maskV i) := by
    intro i hi
    have h := hRel i hi
    simp only [maskA, maskB, maskV]
    cases hpi : p i with
    | mask A B V => rfl
    | step ps nx =>
      rw [hpi] at h
      obtain ⟨-, d', hd, -⟩ := h
      omega
  rw [show 2 * 0 + 2 = 1 + 1 by rfl]
  refine tailsAt_congr prims K D W knownE knownB names count L tg hist _ _ _
    (fun i => call (Sum.inr (Sum.inl 2)) >>= fun o => (o.bind randOutput).elim failure fun w =>
      call (Sum.inl (Sum.inr (maskProducts K i (maskA i) (maskB i) w))) >>= fun o' =>
        (o'.bind extendOutput).elim failure fun z => pure (maskOut K i (hs i) (maskA i) (maskB i) (maskV i) w z))
    (fun i hi => by rw [hp i hi, mask_run]) ?_
  refine tailsAt_rand prims K D W knownE knownB names count L tg hist hn (2 * halvings count + 1) 1 _ fun out => ?_
  refine tailsAt_elim prims K D W knownE knownB names count L tg hist _ _ (fun i => (out i).bind randOutput)
    (fun i w => call (Sum.inl (Sum.inr (maskProducts K i (maskA i) (maskB i) w))) >>= fun o' =>
      (o'.bind extendOutput).elim failure fun z => pure (maskOut K i (hs i) (maskA i) (maskB i) (maskV i) w z))
    (fun hdead A st => ?_) (fun b _ => ?_)
  · refine executePhase_dead D A _ 1 st _ (fun i _ => ?_) (hdead.imp fun i h => ⟨h.1, by rw [h.2]; rfl⟩)
    cases (out i).bind randOutput with
    | none => exact Or.inl rfl
    | some w => exact Or.inr ⟨_, _, rfl, rfl⟩
  · rw [show 2 * halvings count + 1 + 1 = 2 * halvings count + 2 by omega]
    exact maskLast prims K D W knownE knownB names hn count L tg hist
      (fun i => maskProducts K i (maskA i) (maskB i) (b i))
      (fun i z => maskOut K i (hs i) (maskA i) (maskB i) (maskV i) (b i) z)

end ThresholdLeanXmssSecurity.RealNetworkC1x

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1x

open RealNetworkC1r

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

theorem headTails (prims : Primitives) (K : Constants C E) (D : C.Coalition) : HeadTailsStatement prims K D :=
  headTails_of_steps prims K D (tailsMaskBlock prims K D) (tailsExtendBlock prims K D) (tailsCoinBlock prims K D)
    (tailsFirstBlock prims K D)

end ThresholdLeanXmssSecurity.RealNetworkC1x

end

end

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.hiddenInv_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.hiddenInv_common

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.c1b_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.c1b_of_steps

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.headTails_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.headTails_of_steps

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.headHist_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.headHist_of_steps

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.hybridTail_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.hybridTail_of_steps

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.headCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.headCover

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.digestSalts_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.digestSalts_known

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.multFinish_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.multFinish_hidden

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1r.knownColumnsBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1r.knownColumnsBound

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1v.executePhase_dead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1v.executePhase_dead

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1v.planDead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1v.planDead

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1v.coinDead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1v.coinDead

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1v.knownColumns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1v.knownColumns

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1v.digestSalts_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1v.digestSalts_hidden

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1v.multFinish_hidden_of_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1v.multFinish_hidden_of_some

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1v.extendHidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1v.extendHidden

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1v.restAbort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1v.restAbort

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1x.tailsAt_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1x.tailsAt_call

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1x.tailsAt_rand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1x.tailsAt_rand

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1x.tailsAt_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1x.tailsAt_oracle

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1x.tailsAt_elim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1x.tailsAt_elim

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1x.tailsCoinBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1x.tailsCoinBlock

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1x.tailsExtendBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1x.tailsExtendBlock

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1x.tailsFirstBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1x.tailsFirstBlock

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1x.tailsMaskBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1x.tailsMaskBlock

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1x.headTails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1x.headTails
