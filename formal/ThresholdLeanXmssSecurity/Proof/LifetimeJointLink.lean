import ThresholdLeanXmssSecurity.Proof.Lifetime
import ThresholdLeanXmssSecurity.Proof.LifetimeBridge

/-!
# Local keygen programming and lifetime ceremony slots

The local compiler answers keygen derivations and their programming from one
private lazy table. Its output is an ordinary `LocalSpec` computation, and its
execution law retains both that table and the public cache. Merging the two
recovers the original world execution.

Ceremony errors are indexed by the tree and its attempt number. Each slot has
its own prefix distribution, so their sum does not condition on a common
global-run schedule.

The pinned leanVM and current leanVM proof directories were searched for the
local-programming compiler and slot accounting. Their signing-specific
programmed-cache couplings do not implement these threshold interfaces.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

set_option maxRecDepth 100000

namespace ThresholdLeanXmssSecurity.LifetimeJointLink

attribute [local instance] Classical.propDecidable

variable {C : Committee}

local instance : DecidableEq (LifetimeBridge.JointInput C × HashCache C) := Classical.decEq _
local instance : DecidableEq Tree := Classical.decEq _

/-- Lift an operation on the private derivation table using local randomness only. -/
def tableStep {α : Type} (m : StateT (HashCache C) ProbComp α) :
    StateT (HashCache C) (OracleComp (LocalSpec C)) α :=
  StateT.mk fun s => liftComp (m.run s) (LocalSpec C)

/-- The keygen derivation domain is private; all other local requests are forwarded. -/
def compileLocal : QueryImpl (LocalSpec C) (StateT (HashCache C) (OracleComp (LocalSpec C)))
  | .inr (.inl q) => if KeygenPoint q then
      tableStep ((Query C →ₒ HashOutput).randomOracle q)
    else StateT.lift (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q))))
  | t => StateT.lift (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t))

/-- Programming is local to the derivation table. -/
def compileWorld : QueryImpl (WorldSpec C) (StateT (HashCache C) (OracleComp (LocalSpec C))) :=
  compileLocal (C := C) + (fun x => tableStep (programAnswer (C := C) x)) + compileLocal (C := C)

/-- A forbidden programming request targets a domain other than keygen derivation. -/
def OtherProgram : (WorldSpec C).Domain → Prop
  | .inl (.inr x) => ¬ KeygenPoint x.1
  | _ => False

/-- Interpret a compiled stateful program, retaining the table and public cache. -/
def runLocal (prims : Primitives) {α : Type}
    (m : StateT (HashCache C) (OracleComp (LocalSpec C)) α) :
    StateT (HashCache C × HashCache C) ProbComp α :=
  StateT.mk fun s => (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (localAnswer prims) (m.run s.1)).run s.2

theorem runLocal_pure (prims : Primitives) {α : Type} (a : α) :
    runLocal (C := C) prims (pure a) = pure a := by
  ext s
  simp [runLocal]

theorem runLocal_bind (prims : Primitives) {α β : Type}
    (m : StateT (HashCache C) (OracleComp (LocalSpec C)) α)
    (f : α → StateT (HashCache C) (OracleComp (LocalSpec C)) β) :
    runLocal prims (m >>= f) = runLocal prims m >>= fun a => runLocal prims (f a) := by
  ext s
  simp [runLocal, StateT.run_bind, map_bind, bind_map_left]

theorem simulate_local_prob (prims : Primitives) {α : Type} (p : ProbComp α) :
    simulateQ (localAnswer (C := C) prims) (liftComp p (LocalSpec C)) = StateT.lift p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    simp only [liftComp_bind, simulateQ_bind, ih]
    ext s
    simp [StateT.run_bind, StateT.run_lift]
    rfl

theorem runLocal_tableStep (prims : Primitives) {α : Type}
    (m : StateT (HashCache C) ProbComp α) :
    runLocal prims (tableStep m) = onKeygenTable m := by
  ext s
  change (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (localAnswer prims) (liftComp (m.run s.1) (LocalSpec C))).run s.2 = _
  rw [simulate_local_prob]
  simp [StateT.run_lift, onKeygenTable]

theorem runLocal_lift (prims : Primitives) (q : (LocalSpec C).Domain) :
    runLocal prims (StateT.lift (OracleComp.lift (OracleSpec.query q))) =
      onGameCache (localAnswer (C := C) prims q) := by
  ext s
  simp [runLocal, StateT.run_lift, onGameCache]

theorem runLocal_compileLocal (prims : Primitives) (q : (LocalSpec C).Domain) :
    runLocal prims (compileLocal q) = localTableLocal prims (hashAnswer prims) q := by
  rcases q with u | q | x
  · exact runLocal_lift prims (.inl u)
  · change runLocal prims (if KeygenPoint q then _ else _) =
      if KeygenPoint q then _ else _
    split
    · exact runLocal_tableStep prims _
    · exact runLocal_lift prims (.inr (.inl q))
  · exact runLocal_lift prims (.inr (.inr x))

theorem runLocal_compileWorld (prims : Primitives) (q : (WorldSpec C).Domain)
    (hq : ¬ OtherProgram q) :
    runLocal prims (compileWorld q) = localTableWorld prims (hashAnswer prims) q := by
  rcases q with (q | x) | q
  · exact runLocal_compileLocal prims q
  · have hx : KeygenPoint x.1 := by simpa [OtherProgram] using hq
    change runLocal prims (tableStep (programAnswer x)) = if KeygenPoint x.1 then _ else _
    rw [if_pos hx]
    exact runLocal_tableStep prims _
  · exact runLocal_compileLocal prims q

/-- The compiler uses exactly the split-table world on every allowed source branch. -/
theorem compile_run (prims : Primitives) {α : Type} (p : OracleComp (WorldSpec C) α)
    (safe : IsQueryBoundP p OtherProgram 0) :
    runLocal prims (simulateQ compileWorld p) =
      simulateQ (localTableWorld prims (hashAnswer prims)) p := by
  induction p using OracleComp.inductionOn with
  | pure a => exact runLocal_pure prims a
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at safe
    have hq : ¬ OtherProgram q := by simpa using safe.1
    simp only [simulateQ_bind, simulateQ_spec_query, runLocal_bind,
      runLocal_compileWorld prims q hq]
    congr 1
    funext a
    exact ih a (by simpa using safe.2 a)

/-- The same full source law, with the private table and public cache merged at the end. -/
theorem compile_merged_run (prims : Primitives) {α : Type} (p : OracleComp (WorldSpec C) α)
    (safe : IsQueryBoundP p OtherProgram 0) (s : HashCache C × HashCache C) :
    Prod.map id mergedCache <$> (runLocal prims (simulateQ compileWorld p)).run s =
      (simulateQ (worldAnswer prims) p).run (mergedCache s) := by
  rw [compile_run prims p safe]
  exact localTableWorld_run prims (hashAnswer prims) (localTable_hashAnswer prims).1
    (localTable_hashAnswer prims).2 p s

theorem tableStep_bound {α : Type} (m : StateT (HashCache C) ProbComp α) (s : HashCache C) :
    IsQueryBoundP ((tableStep m).run s) Counted 0 :=
  isQueryBoundP_liftComp_counted (m.run s)

theorem lifted_query_bound (t : (LocalSpec C).Domain) (s : HashCache C) (n : ℕ)
    (h : Counted t → 0 < n) :
    IsQueryBoundP ((StateT.lift (OracleComp.lift (OracleSpec.query t)) :
      StateT (HashCache C) (OracleComp (LocalSpec C)) _).run s) Counted n := by
  change IsQueryBoundP ((fun a => (a, s)) <$>
    (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t))) Counted n
  rw [isQueryBoundP_map_iff]
  exact (isQueryBoundP_query_iff Counted t n).2 h

theorem compileLocal_bound (q : (LocalSpec C).Domain) (s : HashCache C) :
    IsQueryBoundP ((compileLocal q).run s) Counted
      (if LifetimeCounted (.inr q) then 1 else 0) := by
  rcases q with u | q | x
  · simpa only [compileLocal, LifetimeCounted, if_false] using
      lifted_query_bound (.inl u) s 0 (by simp [Counted])
  · simp only [compileLocal, LifetimeCounted, if_true]
    split
    · exact (tableStep_bound _ s).mono (by omega)
    · exact lifted_query_bound (.inr (.inl q)) s 1 (fun _ => by omega)
  · simpa only [compileLocal, LifetimeCounted, if_true] using
      lifted_query_bound (.inr (.inr x)) s 1 (fun _ => by omega)

theorem compileWorld_bound (q : (WorldSpec C).Domain) (s : HashCache C) :
    IsQueryBoundP ((compileWorld q).run s) Counted
      (if LifetimeCounted q then 1 else 0) := by
  rcases q with (q | x) | q
  · have hcount : LifetimeCounted (.inl (.inl q)) = LifetimeCounted (.inr q) := by
      rcases q with u | q | x <;> rfl
    change IsQueryBoundP ((compileLocal q).run s) Counted _
    rw [hcount]
    exact compileLocal_bound q s
  · exact (tableStep_bound _ s).mono (by simp [LifetimeCounted])
  · exact compileLocal_bound q s

/-- Compilation preserves the all-answer lifetime budget on every initial private table. -/
theorem compile_bound {α : Type} (p : OracleComp (WorldSpec C) α) (q : ℕ)
    (hq : IsQueryBoundP p LifetimeCounted q) (s : HashCache C) :
    IsQueryBoundP ((simulateQ compileWorld p).run s) Counted q := by
  induction p using OracleComp.inductionOn generalizing q s with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply (isQueryBoundP_bind (compileWorld_bound t s)
      (fun r _ => ih r.1 _ (hq.2 r.1) r.2)).mono
    by_cases ht : LifetimeCounted t
    · have hp := hq.1.resolve_left (not_not.mpr ht)
      simp only [ht, if_true]
      omega
    · simp [ht]

theorem keygen_program_safe (q : Query C) (v : HashOutput) (hq : KeygenPoint q) :
    IsQueryBoundP (program q v) OtherProgram 0 := by
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inl (.inr (q, v))))) _ 0
  rw [isQueryBoundP_query_iff]
  simp [OtherProgram, hq]

theorem safe_mapM {α β : Type} (xs : List α) (f : α → OracleComp (WorldSpec C) β)
    (hf : ∀ a ∈ xs, IsQueryBoundP (f a) OtherProgram 0) :
    IsQueryBoundP (xs.mapM f) OtherProgram 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.mapM_cons]
    exact isQueryBoundP_bind (hf a (by simp)) fun _ _ =>
      isQueryBoundP_bind (ih fun b hb => hf b (by simp [hb])) fun _ _ =>
        isQueryBoundP_pure _ _ 0

/-- The simulator's entire programming block, including rejected writes, is accepted by the compiler. -/
theorem keygenProgramBlock_safe {E : Type} (D : C.Coalition) (parts : C.Party → Parts C)
    (log : CallLog C) (sent : C.Party → Mail C E) (parameter : PublicParameter)
    (corrupt : C.Party → Option (Keys C)) (high : HashOutput) :
    IsQueryBoundP (keygenProgramBlock D parts log sent parameter corrupt high) OtherProgram 0 := by
  dsimp only [keygenProgramBlock]
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · exact keygen_program_safe _ _ trivial
  intro _ _
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · apply safe_mapM
    intro T _
    split
    · exact keygen_program_safe _ _ trivial
    · exact isQueryBoundP_pure _ _ 0
  intro _ _
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · apply safe_mapM
    intro j _
    apply safe_mapM
    intro i _
    split
    · exact keygen_program_safe _ _ trivial
    · exact isQueryBoundP_pure _ _ 0
  intro _ _
  exact isQueryBoundP_pure _ _ 0

/-- Local execution of the actual keygen programming block keeps its original joint cache law. -/
theorem keygenProgramBlock_local {E : Type} (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E)
    (parameter : PublicParameter) (corrupt : C.Party → Option (Keys C)) (high : HashOutput)
    (s : HashCache C × HashCache C) :
    Prod.map id mergedCache <$>
      (runLocal prims (simulateQ compileWorld
        (keygenProgramBlock D parts log sent parameter corrupt high))).run s =
      (simulateQ (worldAnswer prims)
        (keygenProgramBlock D parts log sent parameter corrupt high)).run (mergedCache s) :=
  compile_merged_run prims _ (keygenProgramBlock_safe D parts log sent parameter corrupt high) s

/-- The VCVio enforcement construction with one shared budget for `Counted`,
instead of the per-index budget of `OracleSpec.enforceOracle`. -/
def capOracle : QueryImpl (LocalSpec C) (StateT ℕ (OracleComp (LocalSpec C))) := fun t =>
  StateT.mk fun q =>
    if Counted t then
      if 0 < q then (fun a => (a, q - 1)) <$> OracleComp.lift (OracleSpec.query t)
      else pure (default, q)
    else (fun a => (a, q)) <$> OracleComp.lift (OracleSpec.query t)

def cap {α : Type} (q : ℕ) (p : OracleComp (LocalSpec C) α) : OracleComp (LocalSpec C) α :=
  (simulateQ capOracle p).run' q

/-- Enforcement gives a syntactic bound even on unreachable inputs and states. -/
theorem cap_run_bound {α : Type} (p : OracleComp (LocalSpec C) α) (q : ℕ) :
    IsQueryBoundP ((simulateQ capOracle p).run q) Counted q := by
  induction p using OracleComp.inductionOn generalizing q with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, capOracle, StateT.run_mk]
    by_cases ht : Counted t
    · rw [if_pos ht]
      by_cases hq : 0 < q
      · rw [if_pos hq, bind_map_left]
        apply (isQueryBoundP_query_bind_iff Counted t _ q).2
        exact ⟨.inr hq, fun a => by simpa [ht] using ih a (q - 1)⟩
      · rw [if_neg hq, pure_bind]
        exact ih default q
    · rw [if_neg ht, bind_map_left]
      apply (isQueryBoundP_query_bind_iff Counted t _ q).2
      exact ⟨.inl ht, fun a => by simpa [ht] using ih a q⟩

theorem cap_bound {α : Type} (p : OracleComp (LocalSpec C) α) (q : ℕ) :
    IsQueryBoundP (cap q p) Counted q := by
  unfold cap
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  exact cap_run_bound p q

/-- A segment within its budget is unchanged as an oracle program, not just in probability. -/
theorem cap_eq {α : Type} (p : OracleComp (LocalSpec C) α) (q : ℕ)
    (hq : IsQueryBoundP p Counted q) : cap q p = p := by
  unfold cap
  rw [StateT.run'_eq]
  induction p using OracleComp.inductionOn generalizing q with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, capOracle, StateT.run_mk]
    by_cases ht : Counted t
    · have hp := hq.1.resolve_left (not_not.mpr ht)
      rw [if_pos ht, if_pos hp, bind_map_left, map_bind]
      apply bind_congr
      intro a
      exact ih a (q - 1) (by simpa [ht] using hq.2 a)
    · rw [if_neg ht, bind_map_left, map_bind]
      apply bind_congr
      intro a
      exact ih a q (by simpa [ht] using hq.2 a)

/-- Cap each segment of a ceremony adversary independently, including its start. -/
def capAdversary {E I L R : Type} (Q : ℕ) (A : Adversary C E I L R) : Adversary C E I L R where
  State := A.State
  start x z := cap Q (A.start x z)
  round state sent := cap Q (A.round state sent)
  answer state leak := cap Q (A.answer state leak)

/-- The exact D11/D18 allowance for capped start, round and final segments. -/
theorem capAdversary_queryBound {E I L R O : Type} (Q fuel : ℕ)
    (A : Adversary C E I L R) (Z : Distinguisher C A.State O) :
    IsQueryBounded (capAdversary Q A) (fun r => cap Q (Z r)) fuel ((fuel + 2) * Q) := by
  refine ⟨Q, Q, Q, ?_, fun _ _ => cap_bound _ Q, fun _ _ => cap_bound _ Q,
    fun _ _ => cap_bound _ Q, fun _ => cap_bound _ Q⟩
  rw [Nat.add_mul]
  omega

/-- A tree together with one of its allotted attempts. -/
abbrev Slot (attempts : ℕ) := Fin attempts ⊕ (Fin (2 ^ layerHeight) × Fin attempts)

def slotTree {attempts : ℕ} : Slot attempts → Tree
  | .inl _ => .top
  | .inr (b, _) => .bottom b

def slotAttempt {attempts : ℕ} : Slot attempts → Fin attempts
  | .inl k => k
  | .inr (_, k) => k

theorem slot_card (attempts : ℕ) : Fintype.card (Slot attempts) = lifetimeRuns attempts := by
  simp [Slot, lifetimeRuns]
  ring

/-- A finite enumeration for telescoping; each position denotes a fixed tree and attempt. -/
def slotEquiv (attempts : ℕ) : Slot attempts ≃ Fin (lifetimeRuns attempts) :=
  (Fintype.equivFin _).trans (finCongr (slot_card attempts))

theorem sum_slot_error (attempts : ℕ) (e : Tree → ℝ) :
    ∑ slot : Slot attempts, e (slotTree slot) =
      (attempts : ℝ) * e .top + ∑ b : Fin (2 ^ layerHeight), (attempts : ℝ) * e (.bottom b) := by
  rw [Fintype.sum_sum_type]
  simp [slotTree, Fintype.sum_prod_type]

/-- The slot sum telescopes even when every neighboring game has a different prefix law. -/
theorem slot_hybrid_bound (attempts : ℕ) (p : ℕ → ℝ) (e : Tree → ℝ)
    (hop : ∀ k : Fin (lifetimeRuns attempts),
      |p k - p (k + 1)| ≤ e (slotTree ((slotEquiv attempts).symm k))) :
    |p 0 - p (lifetimeRuns attempts)| ≤
      (attempts : ℝ) * e .top + ∑ b : Fin (2 ^ layerHeight), (attempts : ℝ) * e (.bottom b) := by
  let err : ℕ → ℝ := fun k => if h : k < lifetimeRuns attempts then
    e (slotTree ((slotEquiv attempts).symm ⟨k, h⟩)) else 0
  have hs := abs_sub_le_sum_of_hybrid p (lifetimeRuns attempts) err (fun k hk => by
    simpa [err, hk] using hop ⟨k, hk⟩)
  have hfin : ∑ k ∈ Finset.range (lifetimeRuns attempts), err k =
      ∑ k : Fin (lifetimeRuns attempts), e (slotTree ((slotEquiv attempts).symm k)) := by
    rw [Finset.sum_fin_eq_sum_range]
  rw [hfin] at hs
  have hslots := Fintype.sum_equiv (slotEquiv attempts)
    (fun slot => e (slotTree slot))
    (fun k => e (slotTree ((slotEquiv attempts).symm k))) (fun slot => by simp)
  rw [← hslots, sum_slot_error] at hs
  exact hs

/-- An admitted start has one fixed slot, given by its actual pre-start tree counter. -/
def nextSlot {E : Type} (attempts : ℕ) (D : C.Coalition) (st : LifetimeState C E)
    (tree : Tree) (h : LifetimeProof.canStart attempts D st tree) : Slot attempts :=
  match tree with
  | .top => .inl ⟨st.topRuns, h.2.1⟩
  | .bottom b => .inr (b, ⟨st.bottomRuns b, h.2.1⟩)

theorem nextSlot_tree {E : Type} (attempts : ℕ) (D : C.Coalition) (st : LifetimeState C E)
    (tree : Tree) (h : LifetimeProof.canStart attempts D st tree) :
    slotTree (nextSlot attempts D st tree h) = tree := by
  cases tree <;> rfl

theorem nextSlot_attempt {E : Type} (attempts : ℕ) (D : C.Coalition) (st : LifetimeState C E)
    (tree : Tree) (h : LifetimeProof.canStart attempts D st tree) :
    (slotAttempt (nextSlot attempts D st tree h)).val = LifetimeProof.runsAt st tree := by
  cases tree <;> rfl

/-- The actual accepted start increments the counter of its slot and preserves every other counter. -/
theorem accepted_start_slot {E : Type} [Field E] [Algebra Bit E]
    {ι : Type} {spec : OracleSpec ι}
    (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
    (Ro : ℕ → Roles C (OracleComp spec)) (base : Roles C (OracleComp spec))
    (D : C.Coalition) (keys : C.Party → Keys C) (value : Point → OracleComp spec Digest)
    (honest : C.Party) (tree : Tree) (st : LifetimeState C E)
    (hc : LifetimeProof.canStart attempts D st tree)
    (r : (LifetimeSpec C E).Range (.start tree) × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value
      honest (.start tree)).run st)) (accepted : r.1 ≠ none) :
    LifetimeProof.runsAt r.2 tree =
        (slotAttempt (nextSlot attempts D st tree hc)).val + 1 ∧
      ∀ other, other ≠ tree → LifetimeProof.runsAt r.2 other = LifetimeProof.runsAt st other := by
  have hcounts := LifetimeProof.lifetimeOracles_runs K circuits settings attempts Ro base D keys
    value honest (.start tree) st r hr
  cases ha : r.1 with
  | none => exact (accepted ha).elim
  | some messages =>
    simp only [LifetimeProof.newRun, ha, Option.map_some, Option.some.injEq] at hcounts
    constructor
    · rw [hcounts, nextSlot_attempt]
      simp
    · intro other hne
      rw [hcounts]
      simp [Ne.symm hne]

theorem weighted_constant {α : Type} [DecidableEq α] (draw : ProbComp α) (w : α → ℝ) (c : ℝ)
    (hw : ∀ a ∈ support draw, w a = c) :
    ∑ a ∈ finSupport draw, (Pr[= a | draw]).toReal * w a = c := by
  have he : ∀ a ∈ finSupport draw, w a = c := fun a ha =>
    hw a ((mem_finSupport_iff_mem_support draw a).mp ha)
  rw [Finset.sum_congr rfl (fun a ha => congrArg ((Pr[= a | draw]).toReal * ·) (he a ha))]
  rw [← Finset.sum_mul, ← ENNReal.toReal_sum (fun _ _ => probOutput_ne_top),
    sum_finSupport_probOutput_eq_one (by simp), ENNReal.toReal_one, one_mul]

/-- A fixed-tree selector's complete joint prefix has exactly that tree's error. -/
theorem jointError_fixed_tree (prims : Primitives) (pre : LifetimeBridge.Selector C)
    (tree : Tree) (e : Tree → ℝ)
    (htree : ∀ p ∈ support (LifetimeBridge.jointPrefixRun prims pre), p.1.2.2.1 = tree) :
    LifetimeBridge.jointError prims pre e = e tree := by
  apply weighted_constant
  intro p hp
  exact congrArg e (htree p hp)

/-- Fixed-tree errors sum correctly for independently chosen slot-prefix programs. -/
theorem jointError_slots (attempts : ℕ) (prims : Primitives)
    (pre : Slot attempts → LifetimeBridge.Selector C) (e : Tree → ℝ)
    (htree : ∀ slot p, p ∈ support (LifetimeBridge.jointPrefixRun prims (pre slot)) →
      p.1.2.2.1 = slotTree slot) :
    ∑ slot, LifetimeBridge.jointError prims (pre slot) e =
      (attempts : ℝ) * e .top + ∑ b : Fin (2 ^ layerHeight), (attempts : ℝ) * e (.bottom b) := by
  simp_rw [jointError_fixed_tree prims _ _ e (htree _)]
  exact sum_slot_error attempts e

set_option backward.isDefEq.respectTransparency true in
/-- The slot arithmetic specializes to the exact fixed per-tree expression in the lifetime statement. -/
theorem sum_lifetime_slot_error {E : Type} [Field E] [Fintype E] [Algebra Bit E]
    (attempts : ℕ) (circuits : Circuits) (settings : Settings) (q₀ q : ℕ) :
    (∑ slot : Slot attempts,
      (treeCheckError (E := E) circuits settings (slotTree slot) (q₀ + q) +
        treeHashError circuits settings C (slotTree slot) (q₀ + q) + streamKeyError C +
          seedHitError C (q₀ + q))) =
      (let runError := fun tree => (attempts : ℝ) *
        (treeCheckError (E := E) circuits settings tree (q₀ + q) +
          treeHashError circuits settings C tree (q₀ + q) + streamKeyError C + seedHitError C (q₀ + q))
       runError .top + ∑ b : Fin (2 ^ layerHeight), runError (.bottom b)) :=
  sum_slot_error attempts (fun tree => treeCheckError (E := E) circuits settings tree (q₀ + q) +
    treeHashError circuits settings C tree (q₀ + q) + streamKeyError C + seedHitError C (q₀ + q))

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointLink.compile_merged_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compile_merged_run

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointLink.compile_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compile_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointLink.keygenProgramBlock_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keygenProgramBlock_local

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointLink.cap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cap_eq

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointLink.capAdversary_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms capAdversary_queryBound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointLink.slot_hybrid_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slot_hybrid_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointLink.accepted_start_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted_start_slot

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointLink.jointError_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jointError_slots

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointLink.sum_lifetime_slot_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_lifetime_slot_error

end ThresholdLeanXmssSecurity.LifetimeJointLink
