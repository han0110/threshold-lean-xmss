import ThresholdLeanXmss.Ideal
import ThresholdLeanXmss.Scheme
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Hops
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Walk

/-!
# The parts of the readiness of a start

`freeRun` runs a free computation on the caches, and `streamWorld_replay` states that a run on cached
cells does not change the world. `Live` and `BudgetPart` are the parts of `RunReady`, and
`runReady_of_live` joins them. `inStream_keeps`, `operatorAnswer_keeps` and `firstSignRequest_keeps`
state that the steps of the signing phase keep the invariant `Inv`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

namespace Ready

/-! ## The world grows -/

section Grow

variable {C : Committee} (prims : Primitives)

/-- A call of a lazy random oracle on a cached point gives the cached answer and keeps the cache. -/
theorem randomOracle_run_cached {α β : Type} [DecidableEq α] [SampleableType β] (q : α)
    (s : (α →ₒ β).QueryCache) (u : β) (hs : s q = some u) :
    ((α →ₒ β).randomOracle q).run s = pure (u, s) := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs]

/-- A computation on `H` and `PRG` on the free copy, answered by `streamWorld`. -/
def freeRun (D : C.Coalition) {α : Type} (oa : OracleComp (RoSpec C) α) (w : StreamState C) :
    ProbComp (α × StreamState C) :=
  (simulateQ (streamWorld prims D) (free (liftComp oa (LocalSpec C)))).run w

theorem freeRun_bind (D : C.Coalition) {α β : Type} (oa : OracleComp (RoSpec C) α)
    (f : α → OracleComp (RoSpec C) β) (w : StreamState C) :
    freeRun prims D (oa >>= f) w = freeRun prims D oa w >>= fun x => freeRun prims D (f x.1) x.2 := by
  simp only [freeRun, liftComp_bind, free, simulateQ_bind, StateT.run_bind]

theorem freeRun_query (D : C.Coalition) (t : (RoSpec C).Domain) (w : StreamState C) :
    freeRun prims D (query (spec := RoSpec C) t : OracleComp (RoSpec C) _) w =
      (streamWorld prims D (.inr (.inr t))).run w := by
  have e : free (liftComp (query (spec := RoSpec C) t : OracleComp (RoSpec C) _) (LocalSpec C)) =
      (query (spec := WorldSpec C) (.inr (.inr t)) : OracleComp (WorldSpec C) _) := by
    rcases t with q | x <;> rfl
  have e' : simulateQ (streamWorld prims D) (query (spec := WorldSpec C) (.inr (.inr t))) =
      streamWorld prims D (.inr (.inr t)) := (simulateQ_query _ _).trans (id_map _)
  rw [freeRun, e, e']

/-- A call of `H` that ends in the cache `s₁` gives its answer again from each cache above `s₁`. -/
theorem hashAnswer_replay (q : Query C) (s : HashCache C) (p : HashOutput × HashCache C)
    (hp : p ∈ support ((hashAnswer prims q).run s)) (s' : HashCache C) (hle : p.2 ≤ s') :
    (hashAnswer prims q).run s' = pure (p.1, s') := by
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    rw [hashAnswer_of_isFixed prims hm] at hp ⊢
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rfl
  · rw [hashAnswer_of_not_isFixed prims hq] at hp ⊢
    exact randomOracle_run_cached q s' p.1 (hle (randomOracle_support' q s p hp).2)

theorem prgAnswer_replay (x : PrgInput C) (s : HashCache C) (p : Bit × HashCache C)
    (hp : p ∈ support ((prgAnswer prims x).run s)) (s' : HashCache C) (hle : p.2 ≤ s') :
    (prgAnswer prims x).run s' = pure (p.1, s') := by
  unfold prgAnswer at hp ⊢
  rw [StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨p', hp', hp⟩ := hp
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  rw [StateT.run_bind, hashAnswer_replay prims _ s p' hp' s' hle, pure_bind, StateT.run_pure]

theorem onHash_replay {α : Type} {m : StateT (HashCache C) ProbComp α}
    (hm : ∀ s, ∀ r ∈ support (m.run s), ∀ s', r.2 ≤ s' → m.run s' = pure (r.1, s')) :
    ∀ w, ∀ z ∈ support ((onHash m).run w), ∀ w' : StreamState C, z.2 ≤ w' → (onHash m).run w' = pure (z.1, w') := by
  intro w z hz w' hle
  simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hz ⊢
  obtain ⟨r, hr, rfl⟩ := hz
  rw [hm w.1 r hr w'.1 hle.1]
  simp

/-- A call of `H` or `PRG` on the free copy that ends in the world `w₁` gives its answer again from
each world above `w₁`. -/
theorem streamWorld_replay (D : C.Coalition) (t : (RoSpec C).Domain) :
    ∀ w, ∀ z ∈ support ((streamWorld prims D (.inr (.inr t))).run w), ∀ w', z.2 ≤ w' →
      (streamWorld prims D (.inr (.inr t))).run w' = pure (z.1, w') := by
  rcases t with q | x
  · exact onHash_replay (hashAnswer_replay prims q)
  · show ∀ w, ∀ z ∈ support ((if Hidden D x.1 then _ else _ : StateT (StreamState C) ProbComp _).run w), ∀ w',
      z.2 ≤ w' → (if Hidden D x.1 then _ else _ : StateT (StreamState C) ProbComp _).run w' = pure (z.1, w')
    split_ifs
    · intro w z hz w' hle
      simp only [StateT.run_mk, support_map, Set.mem_image] at hz ⊢
      obtain ⟨r, hr, rfl⟩ := hz
      rw [randomOracle_run_cached _ w'.2 r.1 (hle.2 (randomOracle_support' _ _ r hr).2)]
      simp
    · exact onHash_replay (prgAnswer_replay prims x)

theorem freeRun_replay (D : C.Coalition) {α : Type} (oa : OracleComp (RoSpec C) α) :
    ∀ w, ∀ z ∈ support (freeRun prims D oa w), ∀ w', z.2 ≤ w' → ∀ z' ∈ support (freeRun prims D oa w'),
      z' = (z.1, w') := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro w z hz w' _ z' hz'
    simp [freeRun] at hz hz'
    subst hz hz'
    rfl
  | query_bind t k ih =>
    intro w z hz w' hle z' hz'
    rw [freeRun_bind, mem_support_bind_iff] at hz hz'
    obtain ⟨x, hx, hz⟩ := hz
    obtain ⟨x', hx', hz'⟩ := hz'
    erw [freeRun_query] at hx hx'
    have hxz : x.2 ≤ z.2 := simulateQ_le prims D _ x.2 z hz
    rw [streamWorld_replay prims D t w x hx w' (hxz.trans hle), support_pure, Set.mem_singleton_iff] at hx'
    subst hx'
    exact ih x.1 x.2 z hz w' hle z' hz'

end Grow

/-! ## The invariant of readiness -/

section Game

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (budget : StartBudget)

/-- The reference top tree on the seeds and the parameter of the game. -/
@[irreducible] def refTop (D : C.Coalition) (keys : C.Party → Option (Keys C)) : OracleComp (RoSpec C) (Option TreeOutput) :=
  referenceTree (fun oa => tweakable oa) (prfValue (gameSeeds D keys)) (gameParameter D keys) emptyTop .top

/-- Each honest top tree is the result of a run of the reference top tree that ends below `world`. -/
def TopCached (D : C.Coalition) {σ : Type} (real : RealState C σ) (world : StreamState C) : Prop :=
  ∀ i, i ∉ D.1 → ∀ top, (real.operators i).top = some top →
    ∃ w z, z ∈ support (freeRun prims D (refTop D fun j => (real.operators j).keys) w) ∧
      z.1 = some (.top top) ∧ z.2 ≤ world

/-- The honest seeds agree, and each honest top tree is a cached reference top tree. -/
def Live (D : C.Coalition) {σ : Type} (real : RealState C σ) (world : StreamState C) : Prop :=
  seedsDiffer D (fun i => (real.operators i).keys) = false ∧ TopCached prims D real world

/-- The budget parts of `RunReady`, namely its last four conjuncts. -/
def BudgetPart (world : StreamState C) : Prop :=
  SplitCacheBound (splitRegionCache SplitHashDomain world.1) budget.split ∧
    (∃ (seen : Finset (Query C)) (keys : Finset HashOutput), SoundCache 0 world.1 seen keys ∧
      seen.card ≤ budget.coins ∧ keys.card ≤ budget.keys) ∧
    (∃ salts : Finset (List Bit), DigestSaltsCovered world.1 salts ∧ salts.card ≤ budget.salts) ∧
    HiddenKeyBound world.2 budget.hiddenKeys

/-- Each recorded start that is not ready fails a budget part, and its world is below `world`. -/
def UnreadyFails (first : Option (Stage × StreamState C)) (world : StreamState C) : Prop :=
  ∀ tree index w, first = some (.unready tree index, w) → ¬ BudgetPart budget w ∧ w ≤ world

/-- The invariant of readiness. While no bad event is recorded the state is `Live`, and each recorded
start that is not ready fails a budget part. -/
def Inv (D : C.Coalition) {σ : Type} (s : FirstState C σ) (world : StreamState C) : Prop :=
  (s.first = none → Live prims D s.real world) ∧ UnreadyFails budget s.first world

theorem freeRun_refTop (D : C.Coalition) (keys : C.Party → Option (Keys C)) (w : StreamState C) :
    (simulateQ (streamWorld prims D) (free (liftComp (referenceTree (fun oa => tweakable oa)
      (prfValue (gameSeeds D keys)) (gameParameter D keys) emptyTop .top) _))).run w =
      freeRun prims D (refTop D keys) w := by
  unfold refTop freeRun
  rfl

omit [Field E] [Algebra Bit E] in
theorem inv_grow (D : C.Coalition) {σ : Type} (s : FirstState C σ) (w w' : StreamState C)
    (h : Inv prims budget D s w) (hle : w ≤ w') : Inv prims budget D s w' := by
  refine ⟨fun hn => ?_, fun tree index w₁ hw => ?_⟩
  · obtain ⟨hseeds, htop⟩ := h.1 hn
    refine ⟨hseeds, fun i hi top htop' => ?_⟩
    obtain ⟨w₀, z, hz, hz1, hz2⟩ := htop i hi top htop'
    exact ⟨w₀, z, hz, hz1, le_trans hz2 hle⟩
  · obtain ⟨hfail, hw₁⟩ := h.2 tree index w₁ hw
    exact ⟨hfail, le_trans hw₁ hle⟩

omit [Field E] [Algebra Bit E] in
/-- A live state with the budget parts is ready. -/
theorem runReady_of_live (D : C.Coalition) {σ : Type} (real : RealState C σ) (world : StreamState C)
    (hlive : Live prims D real world) (hbudget : BudgetPart budget world) : RunReady prims budget D real world := by
  have key : ∀ i, i ∉ D.1 → ∀ topTree, (real.operators i).top = some topTree →
      ∀ z ∈ support (freeRun prims D (refTop D fun j => (real.operators j).keys) world),
        z.1 = some (.top topTree) := by
    intro i hi topTree htop z hz
    obtain ⟨w₀, z₀, hz₀, hz₀1, hz₀2⟩ := hlive.2 i hi topTree htop
    rw [freeRun_replay prims D _ w₀ z₀ hz₀ world hz₀2 z hz]
    exact hz₀1
  refine ⟨hlive.1, ?_, hbudget⟩
  simp only [freeRun_refTop]
  exact key

attribute [local irreducible] streamTreeRun wrongOutput

/-- `wrongOutput` on the top tree compares each honest output with the reference top tree. -/
theorem wrongOutput_top (D : C.Coalition) (keys : C.Party → Option (Keys C)) (outputs : C.Party → Option TreeOutput) :
    wrongOutput D keys .top outputs = free (liftComp (refTop D keys) (LocalSpec C)) >>= fun reference =>
      pure (decide (∃ i, i ∉ D.1 ∧ (outputs i).isSome ∧ outputs i ≠ reference)) := by
  unfold wrongOutput refTop
  simp only [bind_pure]

/-- A run of the top tree ends with the final world of a run of the reference top tree, and with no
flag each honest output is that reference. -/
theorem streamTreeRun_top (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (s : RealState C net.State)
    (world : StreamState C) :
    ∀ x ∈ support ((streamTreeRun prims K circuits settings D net .top s).run world),
      ∃ w z, z ∈ support (freeRun prims D (refTop D fun j => (s.operators j).keys) w) ∧ z.2 = x.2 ∧
        (x.1.2 = false → ∀ i, i ∉ D.1 → (x.1.1.2 i).isSome → x.1.1.2 i = z.1) := by
  intro x hx
  unfold streamTreeRun at hx
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx
  obtain ⟨r, -, hx⟩ := hx
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hx
  obtain ⟨b, hb, hx⟩ := hx
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
  subst hx
  rw [wrongOutput_top, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hb
  obtain ⟨ref, href, hb⟩ := hb
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hb
  subst hb
  refine ⟨r.2, ref, href, rfl, fun hbad i hi hsome => ?_⟩
  by_contra hne
  simp only [decide_eq_false_iff_not] at hbad
  exact hbad ⟨i, hi, hsome, hne⟩

omit [Field E] [Algebra Bit E] in
theorem keep_keys (operator : OperatorState C) (output : Option TreeOutput) (tree : Tree) :
    (operator.keep output tree).keys = operator.keys := by
  cases tree <;> rfl

theorem orElse_eq_none {α : Type} {a b : Option α} (h : (a <|> b) = none) : a = none ∧ b = none := by
  cases a with
  | none => exact ⟨rfl, h⟩
  | some _ => cases h

theorem topTree_eq_some {output : Option TreeOutput} {topTree : TopTree}
    (h : TreeOutput.topTree output = some topTree) : output = some (.top topTree) := by
  rcases output with _ | (t | t)
  · cases h
  · cases h
    rfl
  · cases h

omit [Field E] [Algebra Bit E] in
theorem inStream_keeps (D : C.Coalition) {σ β : Type} (oa : OracleComp (WorldSpec C) β) :
    Keeps (Inv prims budget D) (inStream (σ := σ) prims D oa) :=
  keeps_lift (inv_grow prims budget D) (simulateQ_le prims D oa)

omit [Field E] [Algebra Bit E] in
/-- The answer of an honest operator keeps `Inv`. It is `tsigOracles` on the free copy under the monad
maps `simulateQ'` of `streamWorld` and `streamLift`, as in `operatorAnswer_keepsClean`. -/
theorem operatorAnswer_keeps {σ : Type} (D : C.Coalition) (operators : C.Party → OperatorState C)
    (operator : OperatorState C) (e : KeyIndex) (q : TsigQuery C) :
    KeepsT (Inv prims budget D)
      (operatorAnswer (m := FirstM C σ) (firstLift prims D) (firstValue prims D operators) operator e q) := by
  intro t
  unfold operatorAnswer
  split
  · rename_i keys top _ _ _ _
    rw [ownAnswer_run]
    let ψ := simulateQ' (streamWorld prims D)
    let freeLift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β :=
      fun oa => free (liftComp oa _)
    let value : Point → OracleComp (WorldSpec C) Digest :=
      fun x => freeLift (prfValue (gameSeeds D fun i => (operators i).keys) x)
    let dealt := dealtWith freeLift keys.parameter (fun _ => keys) top value
    have hdealt : SeedHitProof.Dealt.hmap (streamLift C σ) (SeedHitProof.Dealt.hmap ψ dealt) =
        dealtWith (m := FirstM C σ) (fun oa => firstLift prims D oa) keys.parameter (fun _ => keys) top
          (firstValue prims D operators) := by
      simp only [SeedHitProof.Dealt.hmap, dealt, dealtWith, SeedHitProof.hom_map, SeedHitProof.hom_referenceTree]
      rfl
    rw [← hdealt]
    let t' : TsigState C := { t with trees := fun b => some (operator.bottom b) }
    have hom₁ := SeedHitProof.hom_tsigOracles (streamLift C σ) (fun oa => ψ (freeLift oa))
      (SeedHitProof.Dealt.hmap ψ dealt) q t'
    have hom₂ := SeedHitProof.hom_tsigOracles ψ freeLift dealt q t'
    change Keeps (Inv prims budget D) ((tsigOracles (fun oa => streamLift C σ (ψ (freeLift oa)))
      (SeedHitProof.Dealt.hmap (streamLift C σ) (SeedHitProof.Dealt.hmap ψ dealt)) q).run t')
    rw [← hom₁, ← hom₂]
    exact keeps_lift (inv_grow prims budget D) (simulateQ_le prims D _)
  · exact keeps_pure _

omit [Field E] [Algebra Bit E] in
theorem firstSignRequest_keeps (D : C.Coalition) {σ : Type} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    KeepsT (Inv prims budget D) (firstSignRequest (σ := σ) prims D i e q) := by
  unfold firstSignRequest
  refine keepsT_bind (keepsT_lift (keeps_modify _ fun s w hs => hs)) fun _ =>
    keepsT_bind (keepsT_lift keeps_get) fun s => ?_
  exact operatorAnswer_keeps prims budget D _ _ e q

end Game

end Ready

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.Ready.runReady_of_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.Ready.runReady_of_live
