import ThresholdLeanXmssSecurity.Proof.TreeHashBudgetFinal
import ThresholdLeanXmssSecurity.Proof.TreeLockstepLateBottom
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkSync

/-!
# Honest hash inputs of a retained ceremony

The cover counts distinct budget-domain inputs across the actual synchronous
run. A reshare gives zero copies outside held terms. Coin-key inputs share the
check's tag and label, and accepting Coin receivers use the same value. Digest
and opening covers retain the log even when the next exchange rejects.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

/-- The peer reshare returns zero at every nonholder, independently of the
adversarial inbox and of consistency between held shares. -/
theorem treeHashBudget_reshare_nonholder (ctx : Context C) (rnd : PrssOutput C Bit)
    (v : ℕ → Bit) (count : ℕ) (st : RunState C) (z : Shares C Bit) (final : RunState C)
    (run : some (z, final) ∈ support
      ((reshare (G := RealSpec) K ctx bitCodec rnd v count).run st).run) :
    ∀ T, ctx.self ∉ C.holders T → ∀ g, z T g = 0 := by
  rw [show rnd = (rnd.1, rnd.2) from rfl, reshare_run] at run
  obtain ⟨inbox, _, he⟩ := treeSimCheck_some_bind _ _ _ run
  simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl⟩
  intro T held g
  simp [reshareZ, held]

/-- The output rerandomization retains the nonholder zero restriction. -/
theorem treeHashBudget_rerand_nonholder (ctx : Context C) (mode : ReshareMode)
    (v : Shares C Bit) (count : ℕ) (st : RunState C) (z : Shares C Bit) (final : RunState C)
    (run : some (z, final) ∈ support
      (((realRunGadgets (G := RealSpec) K ctx mode).rerand v count).run st).run) :
    ∀ T, ctx.self ∉ C.holders T → ∀ g, z T g = 0 := by
  change some (z, final) ∈ support
    (((prssRandomness ctx bitCodec 0 count >>= fun rnd =>
      reshare K ctx bitCodec rnd (ownerSum K ctx v) count).run st).run) at run
  rw [prssRandomness_run] at run
  obtain ⟨rnd, _, hr⟩ := treeSimCheck_some_bind _ _ _ run
  exact treeHashBudget_reshare_nonholder K ctx rnd _ count (nextLabel st) z final hr

/-- Saved copies at the pre-check boundary inherit the actual rerandomization
restriction; circuit correctness is unnecessary. -/
theorem treeHashBudget_beforeVerify_nonholder (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) (st : RunState C)
    (out : Shares C Bit × List (Tuple C)) (final : RunState C)
    (run : some (out, final) ∈ support
      ((treeSimCheckBeforeVerify K ctx mode jobs inputs).run st).run) :
    ∀ T, ctx.self ∉ C.holders T → ∀ g, out.1 T g = 0 := by
  simp only [treeSimCheckBeforeVerify, StateT.run_bind, StateT.run_pure] at run
  obtain ⟨⟨p, next⟩, _, run⟩ := treeSimCheck_some_bind _ _ _ run
  obtain ⟨⟨z, last⟩, hz, he⟩ := treeSimCheck_some_bind _ _ _ run
  simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl, rfl⟩
  exact treeHashBudget_rerand_nonholder K ctx mode _ _ next z final hz

/-- The actual audited checkpoint fixes the copy restriction and the common
initial check counters. It also fixes every tuple count before checking. -/
theorem treeHashBudget_batchPrefix_fields (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (data : List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C)
    (run : some data ∈ support (treeSimCheckBatchPrefix K circuits settings ctx jobs initial).run) :
    (∀ T, ctx.self ∉ C.holders T → ∀ g, data.2.1.1 T g = 0) ∧
    data.2.2.label = initial.1 + depth (jobs.map (circuits ctx.keys.parameter ·.kind)) + 1 ∧
    data.2.2.tag = initial.2 ∧
    (data.2.1.2.map (·.count)).sum = tupleCount (jobs.map (circuits ctx.keys.parameter ·.kind)) := by
  have shape := treeSimCheckBatchPrefix_state K circuits settings ctx jobs initial data run
  refine ⟨?_, shape.2.1, shape.2.2.1, ?_⟩
  · unfold treeSimCheckBatchPrefix at run
    obtain ⟨inputs, _, rest⟩ := treeSimCheck_some_bind _ _ _ run
    obtain ⟨saved, hs, he⟩ := treeSimCheck_some_bind _ _ _ rest
    have eq : data = (inputs, saved) := by
      simpa only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq] using he
    subst data
    exact treeHashBudget_beforeVerify_nonholder K ctx settings.mode _ inputs _ saved.1 saved.2 hs
  · rw [shape.2.2.2.1]
    simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
    exact (tupleCount_eq _).symm

section NoRegion
open TreeSimHashCount

/-- PRSS and the recorded circuit gadgets make no query in the budget region. -/
theorem treeHashBudget_beforeVerify_zero (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    RunBudget Region (treeSimCheckBeforeVerify K ctx mode jobs inputs) 0 := by
  have hm : ∀ x y count, RunBudget Region
      ((realRunGadgets (G := RealSpec) K ctx mode).mult x y count) 0 := by
    intro x y count
    change RunBudget Region (prssRandomness ctx bitCodec 0 count >>= _) 0
    exact (prss_zero ctx bitCodec prg_zero 0 count).bind (m := 0)
      (fun r => reshareWith_zero K ctx mode r _ count)
  have hr : ∀ v count, RunBudget Region
      ((realRunGadgets (G := RealSpec) K ctx mode).rerand v count) 0 := by
    intro v count
    change RunBudget Region (prssRandomness ctx bitCodec 0 count >>= _) 0
    exact (prss_zero ctx bitCodec prg_zero 0 count).bind (m := 0)
      (fun r => reshare_zero K ctx _ r _ count)
  unfold treeSimCheckBeforeVerify
  refine RunBudget.bind_zero ?_ (fun p => (hr _ _).bind_zero (fun _ => .pure _ 0))
  have hb := RunBudget.foldlM (layerBody K (realRunGadgets (G := RealSpec) K ctx mode) jobs) 0
    (fun p l => by
      unfold layerBody
      exact (hm _ _ _).bind_zero (fun _ => .pure _ 0)) (List.range (depth jobs)) (inputs, [])
  simpa only [Nat.mul_zero] using hb

/-- Input PRF calls and circuit evaluation up to the check have zero region cost. -/
theorem treeHashBudget_batchPrefix_zero (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    PartyBudget Region (treeSimCheckBatchPrefix K circuits settings ctx jobs initial) 0 := by
  unfold treeSimCheckBatchPrefix
  have hi : PartyBudget Region (jobs.mapM (inputShares ctx) : PartyM C E RealSpec _) 0 := by
    simpa only [Nat.mul_zero] using party_mapM (inputShares ctx) 0 (inputShares_zero ctx) jobs
  exact hi.bind (m := 0) (fun inputs =>
    (treeHashBudget_beforeVerify_zero K ctx settings.mode _ inputs _).bind (m := 0) (fun _ => .pure _))

end NoRegion

section FixedCover
open TreeSimHashCount
variable (prims : Primitives) (D : C.Coalition)

/-- A fixed finite cover survives a complete real round when each continuation
avoids other budget-domain inputs. The scheduler order and log are retained. -/
theorem treeHashBudget_round_cover {α : Type} (S : Finset (Query C))
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (bounds : ∀ i, StepBudget (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) (steps i) 0)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (stepRound worldRoles D A noFunctionality state steps)).run s)) :
    TreeHashBudgetRegionCover S s.2 r.2.2 ∧
      ∀ i, StepBudget (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) (r.1.2.1 i) 0 := by
  -- The scheduler induction is the general finite-cover form of
  -- TreeCheckGuess.round_noNewFree; advance_zero/advance_stepBudget are reused.
  rw [stepRound_real] at run
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨adv, hadv, next, hnext, rfl⟩ := run
  have localBounds : ∀ i, IsQueryBoundP (roundLocal D steps adv.1.2 i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0 := by
    intro i
    unfold roundLocal
    cases h : steps i with
    | done out => trivial
    | wait out resume =>
      have hb := bounds i
      rw [h] at hb
      dsimp only
      split_ifs
      · trivial
      · exact advance_zero _ _ (hb _)
    | call input _ => exact input.elim
  refine ⟨(treeHashBudget_adversary_cover prims D S _ s adv hadv).region.trans
    (treeHashBudget_free_region_cover prims D S _
      (isQueryBoundP_sequenceFin _ localBounds) adv.2 next hnext), ?_⟩
  letI : Preorder (TreeSimState C) := {
    le := fun _ _ => True
    le_refl := fun _ => trivial
    le_trans := fun _ _ _ _ _ => trivial }
  rw [free_sequenceFin, simulateQ_sequenceFin] at hnext
  refine (sequenceFin_state_post _ (fun _ out _ =>
      StepBudget (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) out 0)
    (fun i st r hr => ⟨trivial, ?_⟩) (fun _ _ _ _ _ h => h) adv.2 next hnext).2
  have hs := free_support prims D _ st r hr
  revert hs
  unfold roundLocal
  cases h : steps i with
  | done out =>
    intro hs
    rw [mem_support_pure_iff] at hs
    rw [hs]
    trivial
  | wait out resume =>
    have hb := bounds i
    rw [h] at hb
    dsimp only
    split_ifs
    · intro hs
      rw [mem_support_pure_iff] at hs
      rw [hs]
      trivial
    · exact advance_stepBudget _ _ (hb _) r.1
  | call input _ => exact input.elim

/-- A fixed cover applies to every retained suffix, including the last local
queries before a rejection and a suffix whose operators have all stopped. -/
theorem treeHashBudget_steps_cover {α : Type} (S : Finset (Query C))
    (A : Adversary C E (Keys C) PEmpty PEmpty) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α)
      (s : TreeSimState C) (r : (A.State × (C.Party → Step C E RealSpec α)) × TreeSimState C),
      (∀ i, StepBudget (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) (steps i) 0) →
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executeSteps worldRoles D A noFunctionality fuel state steps)).run s) →
      TreeHashBudgetRegionCover S s.2 r.2.2
  | 0, state, steps, s, r, _, run => by
    simp only [executeSteps, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst r
    exact .refl _ _
  | fuel+1, state, steps, s, r, bounds, run => by
    rw [executeSteps] at run
    split_ifs at run
    · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
      subst r
      exact .refl _ _
    · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
      obtain ⟨mid, hm, tail⟩ := run
      obtain ⟨cover, bounds⟩ := treeHashBudget_round_cover prims D S A state steps bounds s mid hm
      exact cover.trans (treeHashBudget_steps_cover S A fuel mid.1.1 mid.1.2.1 mid.2 r bounds tail)

/-- A complete phase inherits a common fixed cover of the honest programs;
its adversary remains unrestricted. -/
theorem treeHashBudget_phase_cover {α : Type} (S : Finset (Query C))
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α)
    (bounds : ∀ i, i ∉ D.1 → PartyBudget
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) (program i) 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state program)).run s)) :
    TreeHashBudgetRegionCover S s.2 r.2.2 := by
  simp only [executePhase, executeRounds_eq_executeSteps] at run
  simp only [simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map,
    mem_support_bind_iff, support_map] at run
  obtain ⟨start, hstart, last, hlast, eq⟩ := run
  have localBounds (i : C.Party) : IsQueryBoundP
      (if i ∈ D.1 then pure (.done none) else advance (program i).run)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0 := by
    split_ifs with hi
    · exact isQueryBoundP_pure _ _ _
    · exact advance_zero _ _ (bounds i hi)
  have startEq : startSteps worldRoles D program = free (Concrete.sequenceFin fun i =>
      if i ∈ D.1 then pure (.done none) else advance (program i).run) := by
    rw [startSteps, free_sequenceFin]
    congr 1
    funext i
    split_ifs <;> rfl
  rw [startEq] at hstart
  have first := treeHashBudget_free_region_cover prims D S _
    (isQueryBoundP_sequenceFin _ localBounds) s start hstart
  have raw := free_support prims D _ s start hstart
  have remaining : ∀ i, StepBudget
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) (start.1 i) 0 := by
    intro i
    have hi := mem_support_sequenceFin_oc _ _ raw i
    split_ifs at hi with hc
    · rw [mem_support_pure_iff] at hi
      rw [hi]
      trivial
    · exact advance_stepBudget _ _ (bounds i hc) _ hi
  have cover := first.trans (treeHashBudget_steps_cover prims D S A fuel state start.1 start.2 last remaining hlast)
  have logs : last.2.2 = r.2.2 := congrArg (fun v => v.2.2) eq
  exact logs ▸ cover

end FixedCover

/-- A budget-domain free hash is one of the syntactically counted region inputs. -/
theorem treeHashBudget_free_region (t : (LocalSpec C).Domain)
    (h : FreeHashIn TreeSimHashBudgetDomain t) : TreeSimHashCount.Region t := by
  obtain ⟨q, domain, rfl⟩ := h
  exact ⟨q, by simp [splitLocalHashInput, treeSimHashBudgetDomain_not_fixed q domain], domain⟩

/-- An input already in the cover cannot charge the outside-cover predicate. -/
theorem treeHashBudget_hash_covered (S : Finset (Query C)) (q : Query C) (hq : q ∈ S) :
    IsQueryBoundP (liftComp (hashQuery q) (LocalSpec C))
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0 := by
  change IsQueryBoundP (OracleComp.lift ((LocalSpec C).query (.inr (.inl q)))) _ 0
  rw [isQueryBoundP_query_iff]
  rintro ⟨q', ⟨_, outside⟩, eq⟩
  simp only [Sum.inr.injEq, Sum.inl.injEq] at eq
  exact (outside (eq ▸ hq)).elim

/-- The actual pre-check phase adds no budget-domain hash input, even when
some operators abort and no checkpoint survives. -/
theorem treeHashBudget_batchPrefix_cover (prims : Primitives) (circuits : Circuits)
    (settings : Settings) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) (ctx : C.Party → Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial))).run s)) :
    TreeHashBudgetRegionCover ∅ s.2 r.2.2 := by
  apply treeHashBudget_phase_cover prims D ∅ A fuel state _ _ s r run
  intro i _
  apply IsQueryBoundP.of_imp _ (treeHashBudget_batchPrefix_zero K circuits settings (ctx i) jobs initial)
  rintro ((t | _) | _) ht
  · obtain ⟨q, hq, eq⟩ := ht
    exact treeHashBudget_free_region t ⟨q, hq.1, eq⟩
  · exact ht.elim
  · exact ht.elim

/-- One common Coin round costs at most one honest region point before the
next exchanges. Its continuation heads may draw PRSS or public hash inputs
outside the budget domain, in the original per-operator order. -/
theorem treeHashBudget_coin_round (prims : Primitives) (D : C.Coalition) {α : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (count tag label : ℕ)
    (rnd : C.Party → PrssOutput C E) (st : C.Party → RunState C)
    (body : C.Party → List E × RunState C → HashOutput → PartyM C E RealSpec α)
    (heads : ∀ i, i ∉ D.1 → ∀ vals key, IsQueryBoundP
      (advance (body i (vals, nextLabel (st i)) key).run) TreeSimHashCount.Region 0)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (stepRound worldRoles D A noFunctionality state
        (treeSimCoinWaiting K D count rnd st (fun i vals =>
          oracleStep (hashQuery (.coinKey tag label (vals.1.flatMap fun v => List.ofFn (K.encode v)))) >>=
            body i vals)))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ 1 ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  rw [treeSim_coin_round_factor] at run
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨adv, hadv, next, hnext, rfl⟩ := run
  obtain ⟨S, size, points⟩ := treeSimHash_coin_points K D count tag label rnd adv.1.2
  refine ⟨S, size, (treeHashBudget_adversary_cover prims D S _ s adv hadv).region.trans ?_⟩
  apply treeHashBudget_free_region_cover prims D S _ _ adv.2 next hnext
  apply isQueryBoundP_sequenceFin
  intro i
  cases accepted : treeSimCoinOutput K D count rnd adv.1.2 i with
  | none => simp only [accepted, Option.map_none, treeSimResume]; exact isQueryBoundP_pure _ _ _
  | some vals =>
    have honest : i ∉ D.1 := by
      intro hi
      simp only [treeSimCoinOutput, if_pos hi, reduceCtorEq] at accepted
    simp only [accepted, Option.map_some, treeSimResume, advance_oracleStep_bind]
    refine isQueryBoundP_bind (n := 0) (m := 0)
      (treeHashBudget_hash_covered S _ (points i vals accepted)) (fun key _ => ?_)
    apply IsQueryBoundP.of_imp _ (heads i honest vals key)
    rintro t ⟨q, hq, eq⟩
    exact treeHashBudget_free_region t ⟨q, hq.1, eq⟩

/-- A Coin with an already aborted honest sender adds no honest hash point;
the same actual round leaves all continuations stopped. -/
theorem treeHashBudget_coin_partial_round (prims : Primitives) (D : C.Coalition) {α : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (live : C.Party → Bool)
    (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true) (count : ℕ)
    (rnd : C.Party → PrssOutput C E) (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (stepRound worldRoles D A noFunctionality state (treeSimCoinPartial K D live count rnd st k))).run s)) :
    r.1.2.1 = (fun _ => .done none) ∧ TreeHashBudgetRegionCover ∅ s.2 r.2.2 := by
  rw [treeSim_coin_partial_factor K D A state live stopped] at run
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨adv, hadv, rfl⟩ := run
  exact ⟨rfl, (treeHashBudget_adversary_cover prims D ∅ _ s adv hadv).region⟩

/-- Every successful row of one actual gated prefix has the saved-copy
restriction, common checkpoint counters and deterministic tuple count. -/
theorem treeHashBudget_batchPrefix_actual (prims : Primitives) (circuits : Circuits)
    (settings : Settings) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) (ctx : C.Party → Context C)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (jobs : List Job) (initial : ℕ × ℕ) (prelude : C.Party → PartyM C E RealSpec Unit)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => prelude i >>= fun _ => treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial))).run s)) :
    ∀ i, i ∉ D.1 → ∀ data, r.1.2 i = some data →
      (∀ T, (ctx i).self ∉ C.holders T → ∀ g, data.2.1.1 T g = 0) ∧
      data.2.2.label = initial.1 + depth (jobs.map (circuits parameter ·.kind)) + 1 ∧
      data.2.2.tag = initial.2 ∧
      (data.2.1.2.map (·.count)).sum = tupleCount (jobs.map (circuits parameter ·.kind)) := by
  have replay := treeLockstep_logged_run_allowed prims D _ s r run
  intro i hi data hd
  have party := treeSimCheck_phase_replay D A noFunctionality _ fuel state _ r.1 replay i hi data hd
  obtain ⟨_, _, party⟩ := party.option_bind_inv _ _ _
  simpa only [parameters i] using treeHashBudget_batchPrefix_fields K circuits settings (ctx i)
    jobs initial data party.choose_spec.1.mem_support

section OpeningCover
variable (prims : Primitives) (D : C.Coalition)

/-- A local region-zero program fits every cover. -/
theorem treeHashBudget_local_zero_cover {α : Type} (S : Finset (Query C))
    (p : OracleComp (LocalSpec C) α) (bound : IsQueryBoundP p TreeSimHashCount.Region 0)
    (s : TreeSimState C) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run s)) :
    TreeHashBudgetRegionCover S s.2 r.2.2 := by
  apply treeHashBudget_free_region_cover prims D S p _ s r run
  apply IsQueryBoundP.of_imp _ bound
  rintro t ⟨q, hq, eq⟩
  exact treeHashBudget_free_region t ⟨q, hq.1, eq⟩

/-- Compose region covers in the scheduler's actual operator order. -/
theorem treeHashBudget_sequence_region_cover {α : Type} (S : Finset (Query C)) :
    ∀ {n : ℕ} (f : Fin n → OracleComp (WorldSpec C) α),
      (∀ i s r, r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (f i)).run s) →
        TreeHashBudgetRegionCover S s.2 r.2.2) →
      ∀ s r, r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (Concrete.sequenceFin f)).run s) → TreeHashBudgetRegionCover S s.2 r.2.2
  | 0, f, step, s, r, run => by
    simp only [Concrete.sequenceFin, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst r
    exact .refl _ _
  | n+1, f, step, s, r, run => by
    simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at run
    obtain ⟨head, hh, tail, ht, rfl⟩ := run
    exact (step 0 s head hh).trans
      (treeHashBudget_sequence_region_cover S (fun i : Fin n => f i.succ)
        (fun i => step i.succ) head.2 tail ht)

/-- The two actual copy passes and their continued local heads fit the same
finite set, including partial openings and rejection. -/
theorem treeHashBudget_open_boundary {α : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (zero : ∀ i T, i ∉ C.holders T → ∀ g, v i T g = 0)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α)
    (heads : ∀ i out, IsQueryBoundP (advance (k i out).run) TreeSimHashCount.Region 0)
    (s : TreeSimState C) (ds : (C.Party → List HashOutput) × TreeSimState C)
    (hashes : ds ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (treeLockstepOpenHashes D live count v))).run s))
    (r : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (stepRound worldRoles D A noFunctionality state
        (treeSimOpenPartial K D live count v ds.1 k))).run ds.2)) :
    ∃ S : Finset (Query C), S.card ≤ C.n * termCount C + 1 ∧
      TreeHashBudgetRegionCover S s.2 r.2.2 := by
  rw [stepRound_real] at run
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨adv, hadv, next, hnext, rfl⟩ := run
  obtain ⟨S, size, points⟩ := treeSimHash_open_points K count v
    (treeSimOpenInbox K D live count v ds.1 adv.1.2) zero
  have first : TreeHashCover S s.2 ds.2.2 := by
    apply treeHashBudget_free_cover prims D S _ _ s ds hashes
    unfold treeLockstepOpenHashes
    apply isQueryBoundP_sequenceFin
    intro i
    split_ifs
    · exact hashes_freeHashIn_zero _ _ _ (fun T _ outside => outside (points i T).1)
    · exact isQueryBoundP_pure _ _ _
  refine ⟨S, size, first.region.trans
    ((treeHashBudget_adversary_cover prims D S _ ds.2 adv hadv).region.trans ?_)⟩
  rw [free_sequenceFin] at hnext
  apply treeHashBudget_sequence_region_cover prims D S _ _ adv.2 next hnext
  intro i cache out ho
  rw [treeLockstep_open_local_factor] at ho
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at ho
  obtain ⟨head, hh, tail⟩ := ho
  have headCover : TreeHashCover S cache.2 head.2.2 := by
    apply treeHashBudget_free_cover prims D S _ _ cache head hh
    unfold treeSimOpenHead
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · dsimp only
      split_ifs
      · exact isQueryBoundP_pure _ _ _
      · simp only [liftComp_bind, liftComp_pure]
        exact isQueryBoundP_bind (n := 0) (m := 0)
          (hashes_freeHashIn_zero (fun q => q ∉ S) _ _
            (fun T _ outside => outside (points i T).2))
          (fun _ _ => isQueryBoundP_pure _ _ _)
    · exact isQueryBoundP_pure _ _ _
  apply headCover.region.trans
  cases h : head.1 with
  | none =>
    simp only [h, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at tail
    subst out
    exact .refl _ _
  | some opened =>
    simp only [h, treeSimResume] at tail
    exact treeHashBudget_local_zero_cover prims D S _ (heads i opened) head.2 out tail

end OpeningCover

section CoinPhase

/-- The first local pass of a partially active Coin exposes the actual PRSS
rows and the original common exchange. -/
theorem treeHashBudget_coin_start_shape (D : C.Coalition)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (live : C.Party → Bool) (count : ℕ) (st : C.Party → RunState C)
    (steps : C.Party → Step C E RealSpec (List E × RunState C))
    (run : steps ∈ support (startSteps worldRoles D (fun i => if live i then
      ((realCheckGadgets K (ctx i)).coin count).run (st i) else failure))) :
    ∃ rnd : C.Party → PrssOutput C E,
      steps = treeSimCoinPartial K D live count rnd st (fun _ => pure) := by
  have one : ∀ i, ∃ rnd : PrssOutput C E, steps i =
      if i ∈ D.1 then .done none else if live i then
        treeSimCoinStep K (localContext i) rnd count (st i) pure else .done none := by
    intro i
    have hi := mem_support_sequenceFin_oc _ _ run i
    by_cases corrupt : i ∈ D.1
    · simp only [if_pos corrupt, mem_support_pure_iff] at hi
      exact ⟨0, by simpa only [if_pos corrupt] using hi⟩
    · simp only [if_neg corrupt] at hi ⊢
      by_cases active : live i = true
      · simp only [if_pos active] at hi ⊢
        have entry := treeSim_coin_entry K (ctx i) count (st i)
          (pure : List E × RunState C → PartyM C E RealSpec (List E × RunState C))
        simp only [bind_pure] at entry
        rw [entry, support_map] at hi
        obtain ⟨rnd, _, eq⟩ := hi
        refine ⟨rnd, ?_⟩
        have hc : conv K (ctx i) rnd.1 = conv K (localContext i) rnd.1 := by
          funext g
          simp only [ThresholdLeanXmss.conv, self i, localContext]
        simpa only [treeSimCoinStep, hc, self i, localContext] using eq.symm
      · simp only [if_neg active, worldRoles, advance_run_failure, free_pure,
          mem_support_pure_iff] at hi ⊢
        exact ⟨0, hi⟩
  choose rnd shape using one
  refine ⟨rnd, funext fun i => ?_⟩
  by_cases active : live i = true
  · simpa only [treeSimCoinPartial, if_pos active, treeSimCoinWaiting] using shape i
  · by_cases corrupt : i ∈ D.1 <;>
      simpa only [treeSimCoinPartial, if_neg active, corrupt, if_true, if_false] using shape i

/-- A partially active Coin phase has at most one accepted coin-key input at
fixed tag/label. Earlier aborts cannot create a second accepted value. -/
theorem treeHashBudget_coin_phase_points (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (live : C.Party → Bool) (count tag label : ℕ) (st : C.Party → RunState C)
    (out : A.State × (C.Party → Option (List E × RunState C)))
    (run : out ∈ support (executePhase worldRoles D A noFunctionality 1 state
      (fun i => if live i then ((realCheckGadgets K (ctx i)).coin count).run (st i) else failure))) :
    ∃ S : Finset (Query C), S.card ≤ 1 ∧ ∀ i vals final, out.2 i = some (vals, final) →
      Query.coinKey tag label (vals.flatMap fun v => List.ofFn (K.encode v)) ∈ S := by
  unfold executePhase at run
  rw [mem_support_bind_iff] at run
  obtain ⟨steps, hs, tail⟩ := run
  obtain ⟨rnd, rfl⟩ := treeHashBudget_coin_start_shape K D ctx self live count st steps hs
  rw [executeRounds] at tail
  split_ifs at tail with stopped
  · rw [mem_support_pure_iff] at tail
    subst out
    refine ⟨∅, by simp, ?_⟩
    intro i vals final accepted
    simp only [treeSimCoinPartial, treeSimCoinWaiting, treeSimCoinStep] at accepted
    split_ifs at accepted <;> cases accepted
  · by_cases inactive : ∃ j, j ∉ D.1 ∧ live j ≠ true
    · rw [treeSim_coin_partial_factor K D A state live inactive] at tail
      simp only [bind_assoc, pure_bind, executeRounds, mem_support_bind_iff,
        mem_support_pure_iff] at tail
      obtain ⟨adv, _, rfl⟩ := tail
      exact ⟨∅, by simp, fun _ _ _ h => by cases h⟩
    · have allLive : ∀ i, i ∉ D.1 → live i = true := by
        intro i hi
        by_contra h
        exact inactive ⟨i, hi, h⟩
      have same : treeSimCoinPartial K D live count rnd st (fun _ => pure) =
          treeSimCoinWaiting K D count rnd st (fun _ => pure) := by
        funext i
        by_cases hi : i ∈ D.1
        · simp only [treeSimCoinPartial, treeSimCoinWaiting, if_pos hi]
          split_ifs <;> rfl
        · simp only [treeSimCoinPartial, if_pos (allLive i hi)]
      rw [same, treeSim_coin_round_factor] at tail
      simp only [bind_assoc, pure_bind, executeRounds, mem_support_bind_iff,
        mem_support_pure_iff] at tail
      obtain ⟨adv, _, next, hn, rfl⟩ := tail
      obtain ⟨S, size, points⟩ := treeSimHash_coin_points K D count tag label rnd adv.2
      refine ⟨S, size, ?_⟩
      intro i vals final accepted
      change (next i).output = some (vals, final) at accepted
      have localRun := mem_support_sequenceFin_oc _ _ (treeSimCheck_support_free _ hn) i
      cases coin : treeSimCoinOutput K D count rnd adv.2 i with
      | none =>
        simp only [coin, Option.map_none, treeSimResume, mem_support_pure_iff] at localRun
        rw [localRun] at accepted
        cases accepted
      | some values =>
        simp only [coin, Option.map_some, treeSimResume, advance_run_pure, mem_support_pure_iff] at localRun
        rw [localRun] at accepted
        have eq : values = vals := (Prod.mk.inj (Option.some.inj accepted)).1
        exact eq ▸ points i values coin

/-- A completed timed prefix is followed by the same remaining phase, with
absent output rows represented by failure gates. -/
theorem treeHashBudget_phase_cut (prims : Primitives) {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n fuel : ℕ) (state : A.State)
    (p : C.Party → PartyM C E RealSpec α) (k : C.Party → α → PartyM C E RealSpec β)
    (timed : ∀ i, TreeSimCheckTimed (n + 1) (p i).run)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option β)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (n + 1 + fuel) state
        (fun i => p i >>= k i))).run s)) :
    ∃ pref : (A.State × (C.Party → Option α)) × TreeSimState C,
      pref ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (n + 1) state p)).run s) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel pref.1.1
          (fun i => (pref.1.2 i).elim failure (k i)))).run pref.2) := by
  rw [treeSimCheckTimed_phase_split D A n fuel state p k timed] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨pref, first, next, hn, tail⟩ := run
  have corrupt := treeStages_phase_corrupt (treeSimLoggedWorld prims D) D A
    (n+1) state p s pref (by simpa only [simulateQ_executePhase] using first)
  have restart : free (Concrete.sequenceFin fun i => continueStep (k i) (.done (pref.1.2 i))) =
      startSteps worldRoles D (fun i => (pref.1.2 i).elim failure (k i)) := by
    unfold startSteps
    rw [free_sequenceFin]
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp [hi, corrupt i hi, continueStep, free_pure]
    · cases h : pref.1.2 i <;>
        simp [hi, h, continueStep, worldRoles, advance_pure, free_pure]
  refine ⟨pref, first, ?_⟩
  unfold executePhase
  rw [← restart]
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨next, hn, tail⟩

open TreeSimHashCount in
/-- A gated Coin followed by its key hash and region-free work has one
common honest hash input throughout the actual continuation. -/
theorem treeHashBudget_coin_phase_cover (prims : Primitives) {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (live : C.Party → Bool) (count tag label : ℕ) (st : C.Party → RunState C)
    (body : C.Party → List E × RunState C → HashOutput → PartyM C E RealSpec α)
    (zero : ∀ i, i ∉ D.1 → ∀ vals key, PartyBudget Region (body i vals key) 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (1 + fuel) state (fun i =>
        (if live i then ((realCheckGadgets K (ctx i)).coin count).run (st i) else failure) >>=
          fun vals => oracleStep (hashQuery (.coinKey tag label
            (vals.1.flatMap fun v => List.ofFn (K.encode v)))) >>= body i vals))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ 1 ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  let p : C.Party → PartyM C E RealSpec (List E × RunState C) :=
    fun i => if live i then ((realCheckGadgets K (ctx i)).coin count).run (st i) else failure
  let k := fun i (vals : List E × RunState C) =>
    oracleStep (hashQuery (.coinKey tag label (vals.1.flatMap fun v => List.ofFn (K.encode v)))) >>=
      body i vals
  have timed (i) : TreeSimCheckTimed (0+1) (p i).run := by
    dsimp only [p]
    split_ifs
    · exact treeLockstep_timed_coin K _ _ _
    · exact .abort _
  obtain ⟨pref, first, tail⟩ := treeHashBudget_phase_cut prims D A 0 fuel state p k timed s r run
  have raw := (treeLockstep_logged_run_allowed prims D _ s pref first).choose_spec.1.mem_support
  obtain ⟨S, size, points⟩ := treeHashBudget_coin_phase_points K D A state ctx self live
    count tag label st pref.1 raw
  have covered : TreeHashBudgetRegionCover S s.2 pref.2.2 := by
    apply treeHashBudget_phase_cover prims D S A 1 state p _ s pref first
    intro i hi
    dsimp only [p]
    split_ifs
    · apply IsQueryBoundP.of_imp _ ((gadgets_zero K (ctx i)).coin count (st i))
      rintro ((t | _) | _) ht
      · obtain ⟨q, domain, eq⟩ := ht
        exact treeHashBudget_free_region t ⟨q, domain.1, eq⟩
      · exact ht.elim
      · exact ht.elim
    · exact isQueryBoundP_pure _ _ _
  refine ⟨S, size, covered.trans ?_⟩
  apply treeHashBudget_phase_cover prims D S A fuel pref.1.1 _ _ pref.2 r tail
  intro i hi
  cases accepted : pref.1.2 i with
  | none => exact isQueryBoundP_pure _ _ _
  | some vals =>
    simp only [Option.elim_some]
    apply PartyBudget.bind (m := 0)
    · exact localStep_bound (treeHashBudget_hash_covered S _ (points i vals.1 vals.2 accepted))
    · intro key
      apply IsQueryBoundP.of_imp _ (zero i hi vals key)
      rintro ((t | _) | _) ht
      · obtain ⟨q, domain, eq⟩ := ht
        exact treeHashBudget_free_region t ⟨q, domain.1, eq⟩
      · exact ht.elim
      · exact ht.elim

/-- Corrupted programs do not affect a real phase. -/
theorem treeHashBudget_phase_congr {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (p q : C.Party → PartyM C E RealSpec α) (same : ∀ i, i ∉ D.1 → p i = q i) :
    executePhase worldRoles D A noFunctionality fuel state p =
      executePhase worldRoles D A noFunctionality fuel state q := by
  unfold executePhase
  congr 1
  unfold startSteps
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi]
  · simp only [if_neg hi, same i hi]

open TreeSimHashCount in
/-- The real stateful coin-key program has the same one-point cover when
its reached honest counters are common. -/
theorem treeHashBudget_coinKey_phase_cover (prims : Primitives) {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (live : C.Party → Bool) (tag label : ℕ) (st : C.Party → RunState C)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (body : C.Party → HashOutput → RunM C E RealSpec α)
    (zero : ∀ i, i ∉ D.1 → ∀ key, RunBudget Region (body i key) 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option (α × RunState C))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (1 + fuel) state (fun i =>
        if live i then ((coinKey K (realCheckGadgets K (ctx i)) >>= body i).run (st i))
        else failure))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ 1 ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  have eq := treeHashBudget_phase_congr D A (1+fuel) state
    (fun i => if live i then ((coinKey K (realCheckGadgets K (ctx i)) >>= body i).run (st i)) else failure)
    (fun i => (if live i then ((realCheckGadgets K (ctx i)).coin 1).run (st i) else failure) >>=
      fun vals => oracleStep (hashQuery (.coinKey tag label
        (vals.1.flatMap fun v => List.ofFn (K.encode v)))) >>= fun key => (body i key).run vals.2)
    (by
      intro i hi
      by_cases active : live i = true
      · simp only [if_pos active, coinKey, StateT.run_bind, StateT.run_get,
          StateT.run_lift, pure_bind, bind_assoc, (counters i hi).1, (counters i hi).2]
      · simp only [if_neg active]
        rfl)
  rw [eq] at run
  exact treeHashBudget_coin_phase_cover K prims D A fuel state ctx self live 1 tag label st
    (fun i vals key => (body i key).run vals.2) (fun i hi vals key => zero i hi key vals.2) s r run

open TreeSimHashCount in
/-- Challenge rejection and expansion do not add a budget-domain input
beyond the common coin key, including a rejected challenge. -/
theorem treeHashBudget_challenge_phase_cover (prims : Primitives) {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (live : C.Party → Bool) (tag label : ℕ) (st : C.Party → RunState C)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (body : C.Party → E → RunM C E RealSpec α)
    (zero : ∀ i, i ∉ D.1 → ∀ v, RunBudget Region (body i v) 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option (α × RunState C))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (1 + fuel) state (fun i =>
        if live i then ((challenge K (realCheckGadgets K (ctx i)) >>= body i).run (st i))
        else failure))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ 1 ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  simp only [challenge, bind_assoc] at run
  apply treeHashBudget_coinKey_phase_cover K prims D A fuel state ctx self live tag label st
    counters _ _ s r run
  intro i hi key
  refine (RunBudget.lift (oracle_bound (findChallenge_zero K key challengeTries 0))).bind_zero ?_
  intro value
  cases value with
  | none => intro initial; exact isQueryBoundP_pure _ _ _
  | some value => simpa only [pure_bind] using zero i hi value

/-- A successful real Coin retains history and tag and increments its label once. -/
theorem treeHashBudget_coin_state (ctx : Context C) (count : ℕ)
    (st : RunState C) (vals : List E) (final : RunState C)
    (run : some (vals, final) ∈ support
      (((realCheckGadgets (G := RealSpec) K ctx).coin count).run st).run) :
    final = nextLabel st := by
  rw [realCoin_run] at run
  obtain ⟨rnd, _, run⟩ := treeSimCheck_some_bind _ _ _ run
  obtain ⟨opened, _, run⟩ := treeSimCheck_some_bind _ _ _ run
  simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at run
  exact run.2

/-- Local hashing after a real Coin leaves the reached state unchanged. -/
theorem treeHashBudget_coinKey_state (ctx : Context C)
    (st : RunState C) (key : HashOutput) (final : RunState C)
    (run : some (key, final) ∈ support
      ((coinKey K (realCheckGadgets (G := RealSpec) K ctx)).run st).run) :
    final = nextLabel st := by
  simp only [coinKey, StateT.run_bind, StateT.run_get, pure_bind] at run
  obtain ⟨⟨vals, mid⟩, coin, run⟩ := treeSimCheck_some_bind _ _ _ run
  have state : final = mid := by
    simp only [StateT.run_lift] at run
    obtain ⟨_, _, run⟩ := treeSimCheck_some_bind _ _ _ run
    simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at run
    exact run.2
  exact state.trans (treeHashBudget_coin_state K ctx 1 st vals mid coin)

/-- A successful real challenge has exactly the Coin state transition. -/
theorem treeHashBudget_challenge_state (ctx : Context C)
    (st : RunState C) (value : E) (final : RunState C)
    (run : some (value, final) ∈ support
      ((challenge K (realCheckGadgets (G := RealSpec) K ctx)).run st).run) :
    final = nextLabel st := by
  rw [realChallenge_run] at run
  obtain ⟨rnd, _, run⟩ := treeSimCheck_some_bind _ _ _ run
  obtain ⟨opened, _, run⟩ := treeSimCheck_some_bind _ _ _ run
  obtain ⟨result, _, run⟩ := treeSimCheck_some_bind _ _ _ run
  cases result with
  | none => simp only [OptionT.run_failure, mem_support_pure_iff, reduceCtorEq] at run
  | some result =>
    simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at run
    exact run.2

/-- The real multiplication reshare increments the label and preserves the tag. -/
theorem treeHashBudget_extendMult_fields (ctx : Context C) (products : List (Product C E))
    (st : RunState C) (values : Shares C E) (final : RunState C)
    (run : some (values, final) ∈ support
      (((realCheckGadgets (G := RealSpec) K ctx).extendMult products).run st).run) :
    final.label = st.label + 1 ∧ final.tag = st.tag := by
  rw [realExtendMult_run] at run
  obtain ⟨rnd, _, run⟩ := treeSimCheck_some_bind _ _ _ run
  obtain ⟨inbox, _, run⟩ := treeSimCheck_some_bind _ _ _ run
  simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at run
  rw [run.2]
  exact ⟨rfl, rfl⟩

/-- Every present output of a gated actual phase inherits the local state
law of its own original program. -/
theorem treeHashBudget_phase_fields (prims : Primitives) {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (p : C.Party → RunM C E RealSpec α) (live : C.Party → Bool)
    (st : C.Party → RunState C) (tag label delta : ℕ)
    (initial : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (fields : ∀ i before value final, some (value, final) ∈ support ((p i).run before).run →
      final.label = before.label + delta ∧ final.tag = before.tag)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option (α × RunState C))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state (fun i =>
        if live i then (p i).run (st i) else failure))).run s)) :
    ∀ i, i ∉ D.1 → ∀ value final, r.1.2 i = some (value, final) →
      final.label = label + delta ∧ final.tag = tag := by
  have replay := treeLockstep_logged_run_allowed prims D _ s r run
  intro i hi value final accepted
  have party := treeSimCheck_phase_replay D A noFunctionality _ fuel state _ r.1 replay
    i hi (value, final) accepted
  have localRun := party.choose_spec.1.mem_support
  by_cases active : live i = true
  · simp only [if_pos active] at localRun
    simpa only [(initial i hi).1, (initial i hi).2] using fields i (st i) value final localRun
  · simp only [if_neg active, OptionT.run_failure, mem_support_pure_iff, reduceCtorEq] at localRun

open TreeSimHashCount in
/-- A challenge and its next one-round region-free gadget form an actual
cut with a one-point cover and common counters on every present output.
Absent outputs remain failure gates in the unchanged remaining execution. -/
theorem treeHashBudget_challenge_cut (prims : Primitives) {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (live : C.Party → Bool) (tag label delta : ℕ) (st : C.Party → RunState C)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (body : C.Party → E → RunM C E RealSpec α)
    (zero : ∀ i, i ∉ D.1 → ∀ v, RunBudget Region (body i v) 0)
    (timed : ∀ i v st, TreeSimCheckTimed 1 ((body i v).run st).run)
    (fields : ∀ i v before value final,
      some (value, final) ∈ support ((body i v).run before).run →
      final.label = before.label + delta ∧ final.tag = before.tag)
    (k : C.Party → α × RunState C → PartyM C E RealSpec β)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option β)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (2 + fuel) state (fun i =>
        (if live i then ((challenge K (realCheckGadgets K (ctx i)) >>= body i).run (st i))
        else failure) >>= k i))).run s)) :
    ∃ (pref : (A.State × (C.Party → Option (α × RunState C))) × TreeSimState C)
      (S : Finset (Query C)),
      pref ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality 2 state (fun i =>
          if live i then ((challenge K (realCheckGadgets K (ctx i)) >>= body i).run (st i))
          else failure))).run s) ∧
      S.card ≤ 1 ∧ TreeHashBudgetRegionCover S s.2 pref.2.2 ∧
      (∀ i, i ∉ D.1 → ∀ value final, pref.1.2 i = some (value, final) →
        final.label = label + (1 + delta) ∧ final.tag = tag) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel pref.1.1
          (fun i => (pref.1.2 i).elim failure (k i)))).run pref.2) := by
  let p := fun i => if live i then
    ((challenge K (realCheckGadgets K (ctx i)) >>= body i).run (st i)) else failure
  have ht (i) : TreeSimCheckTimed (1+1) (p i).run := by
    dsimp only [p]
    split_ifs
    · rw [StateT.run_bind]
      exact treeLockstep_timed_challenge K (ctx i) 0
        (fun out => (body i out.1).run out.2) (fun out => timed i out.1 out.2) (st i)
    · exact .abort _
  obtain ⟨pref, first, tail⟩ := treeHashBudget_phase_cut prims D A 1 fuel state p k ht s r run
  obtain ⟨S, size, cover⟩ := treeHashBudget_challenge_phase_cover K prims D A 1 state ctx self
    live tag label st counters body zero s pref first
  refine ⟨pref, S, first, size, cover, ?_, tail⟩
  apply treeHashBudget_phase_fields prims D A 2 state
    (fun i => challenge K (realCheckGadgets K (ctx i)) >>= body i) live st tag label (1+delta)
    counters _ s pref first
  intro i before value final raw
  rw [StateT.run_bind] at raw
  obtain ⟨⟨v, mid⟩, challengeRun, bodyRun⟩ := treeSimCheck_some_bind _ _ _ raw
  have hm := treeHashBudget_challenge_state K (ctx i) before v mid challengeRun
  have hf := fields i v mid value final bodyRun
  simp only [hm, nextLabel] at hf
  exact ⟨by omega, hf.2⟩

/-- The common state counters at a challenge/reshare cut follow from the
actual real gadget code, independently of the product values. -/
theorem treeHashBudget_challenge_mult_cut (prims : Primitives) {β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (live : C.Party → Bool) (tag label : ℕ) (st : C.Party → RunState C)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (products : C.Party → E → List (Product C E))
    (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec β)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option β)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (2 + fuel) state (fun i =>
        (if live i then ((challenge K (realCheckGadgets K (ctx i)) >>= fun v =>
          (realCheckGadgets K (ctx i)).extendMult (products i v)).run (st i))
        else failure) >>= k i))).run s)) :
    ∃ (pref : (A.State × (C.Party → Option (Shares C E × RunState C))) × TreeSimState C)
      (S : Finset (Query C)),
      pref ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality 2 state (fun i =>
          if live i then ((challenge K (realCheckGadgets K (ctx i)) >>= fun v =>
            (realCheckGadgets K (ctx i)).extendMult (products i v)).run (st i))
          else failure))).run s) ∧
      S.card ≤ 1 ∧ TreeHashBudgetRegionCover S s.2 pref.2.2 ∧
      (∀ i, i ∉ D.1 → ∀ value final, pref.1.2 i = some (value, final) →
        final.label = label + 2 ∧ final.tag = tag) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel pref.1.1
          (fun i => (pref.1.2 i).elim failure (k i)))).run pref.2) :=
  treeHashBudget_challenge_cut K prims D A fuel state ctx self live tag label 1 st counters
    (fun i v => (realCheckGadgets K (ctx i)).extendMult (products i v))
    (fun i _ _ => (TreeSimHashCount.gadgets_zero K (ctx i)).mult _)
    (fun i _ st => treeLockstep_timed_extendMult K (ctx i) _ st)
    (fun i _ before value final => treeHashBudget_extendMult_fields K (ctx i) _ before value final)
    k s r run

/-- Repeated challenge/gadget pairs, with the payload carrying the reduction state. -/
def treeHashBudgetChallengeChain {α : Type} (ctx : Context C)
    (body : α → E → RunM C E RealSpec α) : ℕ → α → RunM C E RealSpec α
  | 0, value => pure value
  | n+1, value => do
    let challenge ← challenge K (realCheckGadgets K ctx)
    let next ← body value challenge
    treeHashBudgetChallengeChain ctx body n next

open TreeSimHashCount in
/-- A chain of real challenge/gadget cuts costs at most one input per pair.
Its gates may become false at any reached cut; local zero-region tails retain
all queries made before rejection. -/
theorem treeHashBudget_challenge_chain_cover (prims : Primitives) {α β : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (body : C.Party → α → E → RunM C E RealSpec α)
    (zero : ∀ i, i ∉ D.1 → ∀ a v, RunBudget Region (body i a v) 0)
    (timed : ∀ i a v st, TreeSimCheckTimed 1 ((body i a v).run st).run)
    (fields : ∀ i a v before value final,
      some (value, final) ∈ support ((body i a v).run before).run →
      final.label = before.label + 1 ∧ final.tag = before.tag)
    (k : C.Party → α × RunState C → PartyM C E RealSpec β)
    (tailZero : ∀ i, i ∉ D.1 → ∀ out, PartyBudget Region (k i out) 0) :
    ∀ (n fuel : ℕ) (state : A.State) (live : C.Party → Bool)
      (tag label : ℕ) (st : C.Party → RunState C) (value : C.Party → α),
      (∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label) →
      ∀ (s : TreeSimState C) (r : (A.State × (C.Party → Option β)) × TreeSimState C),
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (2*n + fuel) state (fun i =>
          if live i then (treeHashBudgetChallengeChain K (ctx i) (body i) n (value i)).run (st i) >>= k i
          else failure))).run s) →
      ∃ S : Finset (Query C), S.card ≤ n ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  intro n
  induction n with
  | zero =>
    intro fuel state live tag label st value counters s r run
    refine ⟨∅, by simp, ?_⟩
    simp only [Nat.mul_zero, Nat.zero_add, treeHashBudgetChallengeChain, StateT.run_pure, pure_bind] at run
    apply treeHashBudget_phase_cover prims D ∅ A fuel state _ _ s r run
    intro i hi
    split_ifs
    · apply IsQueryBoundP.of_imp _ (tailZero i hi (value i, st i))
      rintro ((t | _) | _) ht
      · obtain ⟨q, domain, eq⟩ := ht
        exact treeHashBudget_free_region t ⟨q, domain.1, eq⟩
      · exact ht.elim
      · exact ht.elim
    · exact isQueryBoundP_pure _ _ _
  | succ n ih =>
    intro fuel state live tag label st value counters s r run
    let cont := fun i (out : α × RunState C) =>
      (treeHashBudgetChallengeChain K (ctx i) (body i) n out.1).run out.2 >>= k i
    have shape : (fun i => if live i then
        (treeHashBudgetChallengeChain K (ctx i) (body i) (n+1) (value i)).run (st i) >>= k i
        else failure) = fun i =>
      (if live i then ((challenge K (realCheckGadgets K (ctx i)) >>= body i (value i)).run (st i))
        else failure) >>= cont i := by
      funext i
      by_cases active : live i = true
      · simp only [if_pos active, treeHashBudgetChallengeChain, StateT.run_bind, bind_assoc, cont]
      · simp only [if_neg active]
        rfl
    rw [shape, show 2 * (n+1) + fuel = 2 + (2*n + fuel) by omega] at run
    obtain ⟨pref, S, first, size, cover, counter, tail⟩ := treeHashBudget_challenge_cut K prims D A
      (2*n + fuel) state ctx self live tag label 1 st counters (fun i => body i (value i))
      (fun i hi => zero i hi (value i)) (fun i => timed i (value i))
      (fun i => fields i (value i)) cont s r run
    let saved := fun i => (pref.1.2 i).getD (value i, ⟨fun _ => [], label+2, tag⟩)
    let active := fun i => (pref.1.2 i).isSome
    have nextCounters (i) (hi : i ∉ D.1) :
        (saved i).2.tag = tag ∧ (saved i).2.label = label + 2 := by
      cases accepted : pref.1.2 i with
      | none => simp only [saved, accepted, Option.getD_none]; trivial
      | some out =>
        have hc := counter i hi out.1 out.2 accepted
        simp only [saved, accepted, Option.getD_some]
        exact ⟨hc.2, hc.1⟩
    have restart : (fun i => (pref.1.2 i).elim failure (cont i)) = fun i =>
        if active i then
          (treeHashBudgetChallengeChain K (ctx i) (body i) n (saved i).1).run (saved i).2 >>= k i
        else failure := by
      funext i
      cases h : pref.1.2 i <;> simp only [active, saved, h, Option.isSome_none,
        Bool.false_eq_true, if_false, Option.elim_none, Option.isSome_some,
        if_true, Option.getD_some, Option.elim_some, cont]
    rw [restart] at tail
    obtain ⟨T, tailSize, tailCover⟩ := ih fuel pref.1.1 active tag (label+2)
      (fun i => (saved i).2) (fun i => (saved i).1) nextCounters pref.2 r tail
    refine ⟨S ∪ T, (Finset.card_union_le _ _).trans ?_, cover.union_trans tailCover⟩
    omega

/-- A reduction after its first multiplication, ending at the next
multiplication boundary supplied by `finish`. -/
def treeHashBudgetReductionTail {α β γ : Type} (ctx : Context C)
    (prepare : α → ℕ → RunM C E RealSpec β) (update : α → β → E → α)
    (finish : α → RunM C E RealSpec γ) : List ℕ → α → β → RunM C E RealSpec γ
  | [], a, b => challenge K (realCheckGadgets K ctx) >>= fun r => finish (update a b r)
  | j :: js, a, b => do
    let r ← challenge K (realCheckGadgets K ctx)
    let next := update a b r
    let value ← prepare next j
    treeHashBudgetReductionTail ctx prepare update finish js next value

/-- Shifting a fold's boundary across its multiplication is an exact program
identity; the local challenges and all failure branches are unchanged. -/
theorem treeHashBudget_reduction_tail_eq {α β γ : Type} (ctx : Context C)
    (prepare : α → ℕ → RunM C E RealSpec β) (update : α → β → E → α)
    (finish : α → RunM C E RealSpec γ) (js : List ℕ) (a : α) (b : β) :
    treeHashBudgetReductionTail K ctx prepare update finish js a b = (do
      let r ← challenge K (realCheckGadgets K ctx)
      let out ← js.foldlM (fun a j => do
        let b ← prepare a j
        let r ← challenge K (realCheckGadgets K ctx)
        pure (update a b r)) (update a b r)
      finish out) := by
  induction js generalizing a b with
  | nil => simp only [treeHashBudgetReductionTail, List.foldlM_nil, pure_bind]
  | cons j js ih =>
    simp only [treeHashBudgetReductionTail, List.foldlM_cons, bind_assoc, pure_bind]
    apply bind_congr
    intro r
    apply bind_congr
    intro value
    exact ih _ _

open TreeSimHashCount in
/-- The cost of a shifted reduction fold is one point per remaining
challenge, plus the cost of its actual final continuation. -/
theorem treeHashBudget_reduction_tail_cover (prims : Primitives) {α β γ δ : Type}
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (prepare : C.Party → α → ℕ → RunM C E RealSpec β)
    (update : C.Party → α → β → E → α) (finish : C.Party → α → RunM C E RealSpec γ)
    (zero : ∀ i, i ∉ D.1 → ∀ a j, RunBudget Region (prepare i a j) 0)
    (timed : ∀ i a j st, TreeSimCheckTimed 1 ((prepare i a j).run st).run)
    (fields : ∀ i a j before value final,
      some (value, final) ∈ support ((prepare i a j).run before).run →
      final.label = before.label + 1 ∧ final.tag = before.tag)
    (k : C.Party → γ × RunState C → PartyM C E RealSpec δ) (baseRounds baseCost : ℕ)
    (base : ∀ (fuel : ℕ) (state : A.State) (live : C.Party → Bool)
      (tag label : ℕ) (st : C.Party → RunState C) (a : C.Party → α) (b : C.Party → β),
      (∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label) →
      ∀ (s : TreeSimState C) (r : (A.State × (C.Party → Option δ)) × TreeSimState C),
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (baseRounds + fuel) state (fun i =>
          if live i then
            (treeHashBudgetReductionTail K (ctx i) (prepare i) (update i) (finish i) [] (a i) (b i)).run (st i) >>= k i
          else failure))).run s) →
      ∃ S : Finset (Query C), S.card ≤ baseCost ∧ TreeHashBudgetRegionCover S s.2 r.2.2) :
    ∀ (js : List ℕ) (fuel : ℕ) (state : A.State) (live : C.Party → Bool)
      (tag label : ℕ) (st : C.Party → RunState C) (a : C.Party → α) (b : C.Party → β),
      (∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label) →
      ∀ (s : TreeSimState C) (r : (A.State × (C.Party → Option δ)) × TreeSimState C),
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (2*js.length + baseRounds + fuel) state (fun i =>
          if live i then
            (treeHashBudgetReductionTail K (ctx i) (prepare i) (update i) (finish i) js (a i) (b i)).run (st i) >>= k i
          else failure))).run s) →
      ∃ S : Finset (Query C), S.card ≤ js.length + baseCost ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  intro js
  induction js with
  | nil => simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using base
  | cons j js ih =>
    intro fuel state live tag label st a b counters s r run
    let body := fun i v => do
      let next := update i (a i) (b i) v
      let value ← prepare i next j
      pure (next, value)
    let cont := fun i (out : (α × β) × RunState C) =>
      (treeHashBudgetReductionTail K (ctx i) (prepare i) (update i) (finish i) js out.1.1 out.1.2).run out.2 >>= k i
    have shape : (fun i => if live i then
        (treeHashBudgetReductionTail K (ctx i) (prepare i) (update i) (finish i) (j::js) (a i) (b i)).run (st i) >>= k i
        else failure) = fun i =>
      (if live i then ((challenge K (realCheckGadgets K (ctx i)) >>= body i).run (st i))
        else failure) >>= cont i := by
      funext i
      by_cases active : live i = true
      · simp only [if_pos active, treeHashBudgetReductionTail, StateT.run_bind,
          StateT.run_pure, pure_bind, bind_assoc, body, cont]
      · simp only [if_neg active]; rfl
    rw [shape, show 2*(j::js).length + baseRounds + fuel =
        2 + (2*js.length + baseRounds + fuel) by simp only [List.length_cons]; omega] at run
    have zb (i) (hi : i ∉ D.1) (v) : RunBudget Region (body i v) 0 :=
      (zero i hi _ _).bind_zero (fun _ => .pure _ 0)
    have tb (i) (v) (st) : TreeSimCheckTimed 1 ((body i v).run st).run := by
      dsimp only [body]
      simp only [StateT.run_bind, StateT.run_pure]
      exact (timed i (update i (a i) (b i) v) j st).bind (n := 0) (fun _ => .done _)
    have fb (i) (v) (before) (value : α × β) (final) (raw : some (value, final) ∈ support
        ((body i v).run before).run) : final.label = before.label + 1 ∧ final.tag = before.tag := by
      simp only [body, StateT.run_bind, StateT.run_pure] at raw
      obtain ⟨⟨val, mid⟩, hm, he⟩ := treeSimCheck_some_bind _ _ _ raw
      simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at he
      rw [he.2]
      exact fields i _ j before val mid hm
    obtain ⟨pref, S, first, size, cover, counter, tail⟩ := treeHashBudget_challenge_cut K prims D A
      (2*js.length + baseRounds + fuel) state ctx self live tag label 1 st counters body zb tb fb cont s r run
    let saved := fun i => (pref.1.2 i).getD ((a i, b i), ⟨fun _ => [], label+2, tag⟩)
    let active := fun i => (pref.1.2 i).isSome
    have nextCounters (i) (hi : i ∉ D.1) :
        (saved i).2.tag = tag ∧ (saved i).2.label = label + 2 := by
      cases accepted : pref.1.2 i with
      | none => simp only [saved, accepted, Option.getD_none]; trivial
      | some out =>
        have hc := counter i hi out.1 out.2 accepted
        simp only [saved, accepted, Option.getD_some]
        exact ⟨hc.2, hc.1⟩
    have restart : (fun i => (pref.1.2 i).elim failure (cont i)) = fun i =>
        if active i then
          (treeHashBudgetReductionTail K (ctx i) (prepare i) (update i) (finish i) js
            (saved i).1.1 (saved i).1.2).run (saved i).2 >>= k i
        else failure := by
      funext i
      cases h : pref.1.2 i <;> simp only [active, saved, h, Option.isSome_none,
        Bool.false_eq_true, if_false, Option.elim_none, Option.isSome_some,
        if_true, Option.getD_some, Option.elim_some, cont]
    rw [restart] at tail
    obtain ⟨T, tailSize, tailCover⟩ := ih fuel pref.1.1 active tag (label+2)
      (fun i => (saved i).2) (fun i => (saved i).1.1) (fun i => (saved i).1.2) nextCounters pref.2 r tail
    refine ⟨S ∪ T, (Finset.card_union_le _ _).trans ?_, cover.union_trans tailCover⟩
    simp only [List.length_cons]
    omega

/-- A phase whose honest programs have zero region cost fits every cover. -/
theorem treeHashBudget_zero_phase_cover (prims : Primitives) {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (p : C.Party → PartyM C E RealSpec α)
    (zero : ∀ i, i ∉ D.1 → TreeSimHashCount.PartyBudget TreeSimHashCount.Region (p i) 0)
    (S : Finset (Query C)) (s : TreeSimState C)
    (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state p)).run s)) :
    TreeHashBudgetRegionCover S s.2 r.2.2 := by
  apply treeHashBudget_phase_cover prims D S A fuel state p _ s r run
  intro i hi
  apply IsQueryBoundP.of_imp _ (zero i hi)
  rintro ((t | _) | _) ht
  · obtain ⟨q, domain, eq⟩ := ht
    exact treeHashBudget_free_region t ⟨q, domain.1, eq⟩
  · exact ht.elim
  · exact ht.elim

end CoinPhase

-- A75_CHECK_HELPERS_BEGIN

section FinalBeforeSalt
open TreeSimHashCount

/-- The final randomization and multiplication reshare make no budget-region query. -/
theorem treeHashBudget_finalBeforeSalt_zero (ctx : Context C)
    (p : (ℕ → E) × (ℕ → E) × E) :
    RunBudget Region (treeLockstepFinalBeforeSalt K ctx p) 0 := by
  unfold treeLockstepFinalBeforeSalt
  exact ((gadgets_zero K ctx).elements 2).bind_zero fun _ =>
    ((gadgets_zero K ctx).mult _).bind_zero fun _ => .pure _ 0

/-- A successful final pre-salt randomization increments the label twice and retains the tag. -/
theorem treeHashBudget_finalBeforeSalt_fields (ctx : Context C)
    (p : (ℕ → E) × (ℕ → E) × E) (st : RunState C)
    (polynomial : E → ℕ → E) (final : RunState C)
    (run : some (polynomial, final) ∈ support
      ((treeLockstepFinalBeforeSalt K ctx p).run st).run) :
    final.label = st.label + 2 ∧ final.tag = st.tag := by
  unfold treeLockstepFinalBeforeSalt at run
  change some (polynomial, final) ∈ support
    (((prssRandomness ctx (elementCodec K) 1 2 >>= _).run st).run) at run
  rw [prssRandomness_run] at run
  obtain ⟨w, _, run⟩ := treeSimCheck_some_bind _ _ _ run
  simp only [StateT.run_bind, StateT.run_pure] at run
  obtain ⟨⟨q, after⟩, mult, result⟩ := treeSimCheck_some_bind _ _ _ run
  simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq,
    Prod.mk.injEq] at result
  have fields := treeHashBudget_extendMult_fields K ctx _ (nextLabel st) q after mult
  rw [result.2]
  simpa only [nextLabel, Nat.add_assoc, Nat.reduceAdd] using fields

end FinalBeforeSalt

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_finalBeforeSalt_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_finalBeforeSalt_zero

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_finalBeforeSalt_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_finalBeforeSalt_fields

section SlicePreparation
open TreeSimHashCount

/-- The multiplication reshare preceding the challenge of one slice step. -/
def treeHashBudgetSlicePrepare (ctx : Context C) (τ : List E) (count : ℕ)
    (p : Shares C E × Shares C E × E) (j : ℕ) : RunM C E RealSpec (Shares C E) :=
  let half := sliceWidth count * 2 ^ (sliceBits - 1 - j)
  let rest := fun k => coinProduct τ 0 (sliceBits - 1 - j) (k / sliceWidth count)
  (realCheckGadgets K ctx).extendMult
    [.replicated (fun T k => rest k * p.1 T k) p.2.1 half,
      .replicated (fun T k => rest k * (p.1 T k + p.1 T (k + half)))
        (fun T k => p.2.1 T k + p.2.1 T (k + half)) half]

/-- The deterministic slice update from its reshare and challenge. -/
def treeHashBudgetSliceUpdate (ctx : Context C) (τ : List E) (count : ℕ)
    (p : Shares C E × Shares C E × E) (j : ℕ) (t : Shares C E) (r : E) :
    Shares C E × Shares C E × E :=
  let half := sliceWidth count * 2 ^ (sliceBits - 1 - j)
  let t₀ := conv K ctx t 0
  let tInf := conv K ctx t 1
  let t₁ := (p.2.2 + t₀) / τ.getD (sliceBits - 1 - j) 0
  let fold := fun (v : Shares C E) T k => v T k + r * (v T k + v T (k + half))
  (fold p.1, fold p.2.1, (1 + r) * t₀ + r * t₁ + r * (1 + r) * tInf)

/-- Factoring a slice step preserves its original local computation exactly. -/
theorem treeHashBudget_sliceStep_eq (ctx : Context C) (τ : List E) (count : ℕ)
    (p : Shares C E × Shares C E × E) (j : ℕ) :
    sliceStep K ctx (realCheckGadgets (G := RealSpec) K ctx) τ count p j =
      (do
        let t ← treeHashBudgetSlicePrepare K ctx τ count p j
        let r ← challenge K (realCheckGadgets K ctx)
        pure (treeHashBudgetSliceUpdate K ctx τ count p j t r)) := by
  rcases p with ⟨xs, ys, claim⟩
  rfl

/-- Slice preparation has no budget-region query. -/
theorem treeHashBudget_slicePrepare_zero (ctx : Context C) (τ : List E) (count : ℕ)
    (p : Shares C E × Shares C E × E) (j : ℕ) :
    RunBudget Region (treeHashBudgetSlicePrepare K ctx τ count p j) 0 :=
  (gadgets_zero K ctx).mult _

/-- Slice preparation contains exactly its one multiplication-resharing round. -/
theorem treeHashBudget_slicePrepare_timed (ctx : Context C) (τ : List E) (count : ℕ)
    (p : Shares C E × Shares C E × E) (j : ℕ) (st : RunState C) :
    TreeSimCheckTimed 1 ((treeHashBudgetSlicePrepare K ctx τ count p j).run st).run :=
  treeLockstep_timed_extendMult K ctx _ st

/-- A successful slice preparation increments the label once and retains the tag. -/
theorem treeHashBudget_slicePrepare_fields (ctx : Context C) (τ : List E) (count : ℕ)
    (p : Shares C E × Shares C E × E) (j : ℕ) (st : RunState C)
    (t : Shares C E) (final : RunState C)
    (run : some (t, final) ∈ support
      ((treeHashBudgetSlicePrepare K ctx τ count p j).run st).run) :
    final.label = st.label + 1 ∧ final.tag = st.tag :=
  treeHashBudget_extendMult_fields K ctx _ st t final run

end SlicePreparation

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_slicePrepare_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_slicePrepare_zero

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_slicePrepare_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_slicePrepare_timed

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_slicePrepare_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_slicePrepare_fields

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_sliceStep_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_sliceStep_eq

section HalvingPreparation
open TreeSimHashCount

/-- The multiplication reshare preceding the challenge of one halving step. -/
def treeHashBudgetHalvingPrepare (ctx : Context C) (width : ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (j : ℕ) : RunM C E RealSpec (Shares C E) :=
  let length := halvedLength^[j] width
  let half := halvedLength length
  let hi := fun (v : ℕ → E) k => if k + half < length then v (k + half) else 0
  let sum := fun (v : ℕ → E) k => v k + hi v k
  (realCheckGadgets K ctx).extendMult
    [.shamir p.1 p.2.1 half, .shamir (sum p.1) (sum p.2.1) half]

/-- The deterministic halving update from its reshare and challenge. -/
def treeHashBudgetHalvingUpdate (ctx : Context C) (width : ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (j : ℕ) (t : Shares C E) (r : E) :
    (ℕ → E) × (ℕ → E) × E :=
  let length := halvedLength^[j] width
  let half := halvedLength length
  let hi := fun (v : ℕ → E) k => if k + half < length then v (k + half) else 0
  let fold := fun (v : ℕ → E) k => v k + r * (v k + hi v k)
  (fold p.1, fold p.2.1,
    conv K ctx t 0 + (p.2.2 + conv K ctx t 1) * r + conv K ctx t 1 * r ^ 2)

/-- Factoring a halving step preserves its original local computation exactly. -/
theorem treeHashBudget_halvingStep_eq (ctx : Context C) (width : ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    halvingStep K ctx (realCheckGadgets (G := RealSpec) K ctx) width p j =
      (do
        let t ← treeHashBudgetHalvingPrepare K ctx width p j
        let r ← challenge K (realCheckGadgets K ctx)
        pure (treeHashBudgetHalvingUpdate K ctx width p j t r)) := by
  rcases p with ⟨a, b, claim⟩
  rfl

/-- Halving preparation has no budget-region query. -/
theorem treeHashBudget_halvingPrepare_zero (ctx : Context C) (width : ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    RunBudget Region (treeHashBudgetHalvingPrepare K ctx width p j) 0 :=
  (gadgets_zero K ctx).mult _

/-- Halving preparation contains one multiplication-resharing round. -/
theorem treeHashBudget_halvingPrepare_timed (ctx : Context C) (width : ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (j : ℕ) (st : RunState C) :
    TreeSimCheckTimed 1 ((treeHashBudgetHalvingPrepare K ctx width p j).run st).run :=
  treeLockstep_timed_extendMult K ctx _ st

/-- A successful halving preparation increments the label once and retains the tag. -/
theorem treeHashBudget_halvingPrepare_fields (ctx : Context C) (width : ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (j : ℕ) (st : RunState C)
    (t : Shares C E) (final : RunState C)
    (run : some (t, final) ∈ support
      ((treeHashBudgetHalvingPrepare K ctx width p j).run st).run) :
    final.label = st.label + 1 ∧ final.tag = st.tag :=
  treeHashBudget_extendMult_fields K ctx _ st t final run

end HalvingPreparation

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_halvingStep_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_halvingStep_eq

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_halvingPrepare_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_halvingPrepare_zero

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_halvingPrepare_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_halvingPrepare_timed

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_halvingPrepare_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_halvingPrepare_fields

section SliceInitial
open TreeSimHashCount

/-- The expansion, nonzero check and first multiplication after the initial Coin. -/
def treeHashBudgetSliceInitial (ctx : Context C) (tuples : List (Tuple C))
    (key : HashOutput) :
    RunM C E RealSpec (List E × (Shares C E × Shares C E × E) × Shares C E) := do
  let count := (tuples.map (·.count)).sum
  let τ ← expand K key (coins count)
  StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
  let p : Shares C E × Shares C E × E :=
    ((fun T k => wordWeightOf K τ count k * liftedPart tuples (·.x) T k),
      liftedPart tuples (·.y), conv K ctx (claimOf K τ count (liftedPart tuples (·.z))) 0)
  let t ← treeHashBudgetSlicePrepare K ctx τ count p 0
  pure (τ, p, t)

/-- The continuation of the initial Coin makes no budget-region query. -/
theorem treeHashBudget_sliceInitial_zero (ctx : Context C) (tuples : List (Tuple C))
    (key : HashOutput) :
    RunBudget Region (treeHashBudgetSliceInitial K ctx tuples key) 0 := by
  unfold treeHashBudgetSliceInitial
  apply (expand_zero K key _).bind_zero
  intro τ
  apply (RunBudget.lift (PartyBudget.of_all (PartyBound.require _))).bind_zero
  intro _
  exact (treeHashBudget_slicePrepare_zero K ctx τ _ _ 0).bind_zero fun _ => .pure _ 0

/-- The initial Coin continuation reaches its one reshare round or aborts. -/
theorem treeHashBudget_sliceInitial_timed (ctx : Context C) (tuples : List (Tuple C))
    (key : HashOutput) (st : RunState C) :
    TreeSimCheckTimed 1 ((treeHashBudgetSliceInitial K ctx tuples key).run st).run := by
  unfold treeHashBudgetSliceInitial expand
  simp only [StateT.run_bind, StateT.run_lift, pure_bind, bind_assoc, StateT.run_pure]
  apply TreeSimCheckTimed.oracle_bind
  intro τ
  apply TreeSimCheckTimed.require_bind
  change TreeSimCheckTimed (1 + 0) _
  apply (treeHashBudget_slicePrepare_timed K ctx τ _ _ 0 st).bind (n := 0)
  intro result
  exact .done _

/-- A successful initial Coin continuation increments the label once and retains the tag. -/
theorem treeHashBudget_sliceInitial_fields (ctx : Context C) (tuples : List (Tuple C))
    (key : HashOutput) (st : RunState C)
    (value : List E × (Shares C E × Shares C E × E) × Shares C E) (final : RunState C)
    (run : some (value, final) ∈ support
      ((treeHashBudgetSliceInitial K ctx tuples key).run st).run) :
    final.label = st.label + 1 ∧ final.tag = st.tag := by
  unfold treeHashBudgetSliceInitial expand at run
  simp only [StateT.run_bind, StateT.run_lift, pure_bind, bind_assoc, StateT.run_pure] at run
  obtain ⟨τ, _, run⟩ := treeSimCheck_some_bind _ _ _ run
  obtain ⟨u, _, run⟩ := treeSimCheck_some_bind _ _ _ run
  obtain ⟨⟨t, after⟩, preparation, result⟩ := treeSimCheck_some_bind _ _ _ run
  simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at result
  rw [result.2]
  exact treeHashBudget_slicePrepare_fields K ctx τ _ _ 0 st t after preparation

end SliceInitial

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_sliceInitial_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_sliceInitial_zero

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_sliceInitial_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_sliceInitial_timed

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_sliceInitial_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_sliceInitial_fields

-- A75_CHECK_HELPERS_END

-- A75_CHECK_COUNTERS_BEGIN
section CheckCounters

/-- Exact label increment and tag preservation on every successful raw run. -/
private def TreeHashBudgetFields {α : Type} (n : ℕ) (p : RunM C E RealSpec α) : Prop :=
  ∀ st value final, some (value, final) ∈ support (p.run st).run →
    final.label = st.label + n ∧ final.tag = st.tag

-- The support decomposition is LockstepLabels' bind/fold argument with
-- the unchanged tag retained alongside its label equation.
private theorem TreeHashBudgetFields.pure {α : Type} (a : α) :
    TreeHashBudgetFields (C := C) (E := E) 0 (pure a) := by
  intro st value final run
  simp only [StateT.run_pure, OptionT.run_pure, mem_support_pure_iff,
    Option.some.injEq, Prod.mk.injEq] at run
  rw [run.2]
  exact ⟨rfl, rfl⟩

private theorem TreeHashBudgetFields.bind {α β : Type} {m n : ℕ} {p : RunM C E RealSpec α}
    {k : α → RunM C E RealSpec β} (hp : TreeHashBudgetFields m p)
    (hk : ∀ a, TreeHashBudgetFields n (k a)) : TreeHashBudgetFields (m+n) (p >>= k) := by
  intro st value final run
  rw [StateT.run_bind] at run
  obtain ⟨⟨a, mid⟩, first, tail⟩ := treeSimCheck_some_bind _ _ _ run
  have h₁ := hp st a mid first
  have h₂ := hk a mid value final tail
  exact ⟨by omega, h₂.2.trans h₁.2⟩

private theorem TreeHashBudgetFields.lift {α : Type} (p : PartyM C E RealSpec α) :
    TreeHashBudgetFields 0 (StateT.lift p : RunM C E RealSpec α) := by
  intro st value final run
  rw [StateT.run_lift] at run
  obtain ⟨a, _, eq⟩ := treeSimCheck_some_bind _ _ _ run
  simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at eq
  rw [eq.2]
  exact ⟨rfl, rfl⟩

private theorem TreeHashBudgetFields.foldlM {α β : Type} (n : ℕ)
    (f : α → β → RunM C E RealSpec α) (hf : ∀ a b, TreeHashBudgetFields n (f a b))
    (xs : List β) (a : α) : TreeHashBudgetFields (xs.length*n) (xs.foldlM f a) := by
  induction xs generalizing a with
  | nil => simpa only [List.foldlM_nil, List.length_nil, Nat.zero_mul] using
      TreeHashBudgetFields.pure (C := C) (E := E) a
  | cons b xs ih =>
    simpa only [List.foldlM_cons, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
      using (hf a b).bind (fun next => ih next)

private theorem treeHashBudget_fields_challenge (ctx : Context C) :
    TreeHashBudgetFields 1 (challenge K (realCheckGadgets K ctx)) := by
  intro st value final run
  rw [treeHashBudget_challenge_state K ctx st value final run]
  exact ⟨rfl, rfl⟩

private theorem treeHashBudget_fields_slice (ctx : Context C) (τ : List E) (count : ℕ)
    (p : Shares C E × Shares C E × E) (j : ℕ) :
    TreeHashBudgetFields 2 (sliceStep K ctx (realCheckGadgets K ctx) τ count p j) := by
  rw [treeHashBudget_sliceStep_eq]
  have prepare : TreeHashBudgetFields 1 (treeHashBudgetSlicePrepare K ctx τ count p j) :=
    treeHashBudget_slicePrepare_fields K ctx τ count p j
  simpa using prepare.bind (fun t => (treeHashBudget_fields_challenge K ctx).bind
    (fun r => TreeHashBudgetFields.pure (treeHashBudgetSliceUpdate K ctx τ count p j t r)))

private theorem treeHashBudget_fields_halving (ctx : Context C) (width : ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    TreeHashBudgetFields 2 (halvingStep K ctx (realCheckGadgets K ctx) width p j) := by
  rw [treeHashBudget_halvingStep_eq]
  have prepare : TreeHashBudgetFields 1 (treeHashBudgetHalvingPrepare K ctx width p j) :=
    treeHashBudget_halvingPrepare_fields K ctx width p j
  simpa using prepare.bind (fun t => (treeHashBudget_fields_challenge K ctx).bind
    (fun r => TreeHashBudgetFields.pure (treeHashBudgetHalvingUpdate K ctx width p j t r)))

/-- The actual pre-salt check has common counters independently of its
intermediate values and of all adversarial answers on a successful row. -/
theorem treeHashBudget_checkBeforeSalt_fields (ctx : Context C) (tuples : List (Tuple C))
    (st : RunState C) (value : E → ℕ → E) (final : RunState C)
    (run : some (value, final) ∈ support ((treeLockstepCheckBeforeSalt K ctx tuples).run st).run) :
    final.label = st.label +
      (2*sliceBits + 2*(halvings (tuples.map (·.count)).sum - sliceBits) + 3) ∧
    final.tag = st.tag := by
  have coin : TreeHashBudgetFields 1 (coinKey K (realCheckGadgets K ctx)) := by
    intro before key after raw
    rw [treeHashBudget_coinKey_state K ctx before key after raw]
    exact ⟨rfl, rfl⟩
  have whole : TreeHashBudgetFields
      (1+(0+(0+(sliceBits*2+((halvings (tuples.map (·.count)).sum-sliceBits)*2+2)))))
      (treeLockstepCheckBeforeSalt K ctx tuples) := by
    unfold treeLockstepCheckBeforeSalt treeLockstepCheckPrefixWith
    refine coin.bind (fun key => (TreeHashBudgetFields.lift _).bind (fun τ =>
      (TreeHashBudgetFields.lift _).bind (fun _ => ?_)))
    have slice := TreeHashBudgetFields.foldlM 2 _ (treeHashBudget_fields_slice K ctx τ (tuples.map (·.count)).sum)
      (List.range sliceBits)
    simp only [List.length_range] at slice
    apply (slice _).bind
    intro p
    have halving := TreeHashBudgetFields.foldlM 2 _ (treeHashBudget_fields_halving K ctx (sliceWidth (tuples.map (·.count)).sum))
      (List.range (halvings (tuples.map (·.count)).sum-sliceBits))
      (conv K ctx p.1, conv K ctx p.2.1, p.2.2)
    simp only [List.length_range] at halving
    exact halving.bind (fun p => treeHashBudget_finalBeforeSalt_fields K ctx p)
  have fields := whole st value final run
  exact ⟨by omega, fields.2⟩

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_checkBeforeSalt_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_checkBeforeSalt_fields

end CheckCounters

-- A75_CHECK_COUNTERS_END

section ShiftedCheck

/-- A halving multiplication carries its actual reduction index as payload. -/
def treeHashBudgetHalvingIndexed (ctx : Context C) (width : ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (j : ℕ) : RunM C E RealSpec (Shares C E × ℕ) := do
  let values ← treeHashBudgetHalvingPrepare K ctx width p j
  pure (values, j)

/-- The actual halving fold after its first multiplication. -/
def treeHashBudgetHalvingTail (ctx : Context C) (width : ℕ) (js : List ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (t : Shares C E × ℕ) : RunM C E RealSpec (E → ℕ → E) :=
  treeHashBudgetReductionTail K ctx (treeHashBudgetHalvingIndexed K ctx width)
    (fun p t r => treeHashBudgetHalvingUpdate K ctx width p t.2 t.1 r)
    (treeLockstepFinalBeforeSalt K ctx) js p t

/-- The shifted halving program is the original halving fold followed by
the final randomization, with exactly the same continuation order. -/
theorem treeHashBudget_halvingTail_eq (ctx : Context C) (width : ℕ) (js : List ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (t : Shares C E × ℕ) :
    treeHashBudgetHalvingTail K ctx width js p t = (do
      let r ← challenge K (realCheckGadgets K ctx)
      let out ← js.foldlM (halvingStep K ctx (realCheckGadgets K ctx) width)
        (treeHashBudgetHalvingUpdate K ctx width p t.2 t.1 r)
      treeLockstepFinalBeforeSalt K ctx out) := by
  unfold treeHashBudgetHalvingTail
  rw [treeHashBudget_reduction_tail_eq]
  simp only [treeHashBudgetHalvingIndexed, bind_assoc, pure_bind,
    ← treeHashBudget_halvingStep_eq]

open TreeSimHashCount in
/-- A partially active halving tail has one honest coin-key input per
remaining challenge; the final randomization adds none. -/
theorem treeHashBudget_halvingTail_cover (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (width : ℕ) (js : List ℕ) (fuel : ℕ) (state : A.State)
    (live : C.Party → Bool) (tag label : ℕ) (st : C.Party → RunState C)
    (p : C.Party → (ℕ → E) × (ℕ → E) × E) (t : C.Party → Shares C E × ℕ)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Option ((E → ℕ → E) × RunState C))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (2*js.length + 2 + fuel) state (fun i =>
        if live i then (treeHashBudgetHalvingTail K (ctx i) width js (p i) (t i)).run (st i)
        else failure))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ js.length + 1 ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  apply treeHashBudget_reduction_tail_cover K prims D A ctx self
    (fun i => treeHashBudgetHalvingIndexed K (ctx i) width)
    (fun i p t r => treeHashBudgetHalvingUpdate K (ctx i) width p t.2 t.1 r)
    (fun i => treeLockstepFinalBeforeSalt K (ctx i))
    (fun i _ p j => (treeHashBudget_halvingPrepare_zero K (ctx i) width p j).bind_zero
      (fun _ => .pure _ 0))
    (fun i p j st => by
      simp only [treeHashBudgetHalvingIndexed, StateT.run_bind, StateT.run_pure]
      exact (treeHashBudget_halvingPrepare_timed K (ctx i) width p j st).bind (n := 0) (fun _ => .done _))
    (fun i p j before value final raw => by
      simp only [treeHashBudgetHalvingIndexed, StateT.run_bind, StateT.run_pure] at raw
      obtain ⟨⟨val, mid⟩, hm, he⟩ := treeSimCheck_some_bind _ _ _ raw
      simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at he
      rw [he.2]
      exact treeHashBudget_halvingPrepare_fields K (ctx i) width p j before val mid hm)
    (fun _ => pure) 2 1 _ js fuel state live tag label st p t counters s r
  · simpa only [treeHashBudgetHalvingTail, bind_pure] using run
  · intro fuel state live tag label st p t counters s r run
    simp only [treeHashBudgetReductionTail, bind_pure] at run
    have fuelEq : 2 + fuel = 1 + (1 + fuel) := by omega
    rw [fuelEq] at run
    exact treeHashBudget_challenge_phase_cover K prims D A (1+fuel) state ctx self live
      tag label st counters
      (fun i r => treeLockstepFinalBeforeSalt K (ctx i)
        (treeHashBudgetHalvingUpdate K (ctx i) width (p i) (t i).2 (t i).1 r))
      (fun i _ _ => treeHashBudget_finalBeforeSalt_zero K (ctx i) _) s r run
/-- The unshifted halving fold through its final randomization. -/
def treeHashBudgetHalvingFold (ctx : Context C) (width : ℕ) (js : List ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) : RunM C E RealSpec (E → ℕ → E) := do
  let out ← js.foldlM (halvingStep K ctx (realCheckGadgets K ctx) width) p
  treeLockstepFinalBeforeSalt K ctx out

theorem treeHashBudget_halvingFold_cons (ctx : Context C) (width : ℕ) (j : ℕ) (js : List ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) :
    treeHashBudgetHalvingFold K ctx width (j::js) p = (do
      let t ← treeHashBudgetHalvingIndexed K ctx width p j
      treeHashBudgetHalvingTail K ctx width js p t) := by
  simp only [treeHashBudgetHalvingFold, List.foldlM_cons, treeHashBudget_halvingStep_eq,
    treeHashBudgetHalvingIndexed, treeHashBudget_halvingTail_eq, bind_assoc, pure_bind]

open TreeSimHashCount in
/-- A real halving fold retains at most one distinct counted input per
challenge, including every query made before an aborted fold. -/
theorem treeHashBudget_halvingFold_cover (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (width : ℕ) (js : List ℕ) (fuel : ℕ) (state : A.State)
    (live : C.Party → Bool) (tag label : ℕ) (st : C.Party → RunState C)
    (p : C.Party → (ℕ → E) × (ℕ → E) × E)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Option ((E → ℕ → E) × RunState C))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (2*js.length + 1 + fuel) state (fun i =>
        if live i then (treeHashBudgetHalvingFold K (ctx i) width js (p i)).run (st i)
        else failure))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ js.length ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  cases js with
  | nil =>
    refine ⟨∅, by simp, ?_⟩
    simp only [treeHashBudgetHalvingFold, List.foldlM_nil, pure_bind, List.length_nil,
      Nat.mul_zero, Nat.zero_add] at run
    apply treeHashBudget_zero_phase_cover prims D A (1+fuel) state _ _ ∅ s r run
    intro i _
    split_ifs
    · exact treeHashBudget_finalBeforeSalt_zero K (ctx i) (p i) (st i)
    · exact isQueryBoundP_pure _ _ _
  | cons j js =>
    let prep := fun i => if live i then (treeHashBudgetHalvingIndexed K (ctx i) width (p i) j).run (st i) else failure
    let cont := fun i (out : (Shares C E × ℕ) × RunState C) =>
      (treeHashBudgetHalvingTail K (ctx i) width js (p i) out.1).run out.2
    have form : (fun i => if live i then
        (treeHashBudgetHalvingFold K (ctx i) width (j::js) (p i)).run (st i) else failure) =
        fun i => prep i >>= cont i := by
      funext i
      by_cases active : live i = true
      · simp only [prep, cont, if_pos active, treeHashBudget_halvingFold_cons, StateT.run_bind]
      · simp only [prep, if_neg active]; rfl
    rw [form, show 2*(j::js).length+1+fuel = 1+(2*js.length+2+fuel) by
      simp only [List.length_cons]; omega] at run
    have timed (i) : TreeSimCheckTimed (0+1) (prep i).run := by
      dsimp only [prep]
      split_ifs
      · simp only [treeHashBudgetHalvingIndexed, StateT.run_bind, StateT.run_pure]
        exact (treeHashBudget_halvingPrepare_timed K (ctx i) width (p i) j (st i)).bind (n := 0) (fun _ => .done _)
      · exact .abort _
    obtain ⟨pref, first, tail⟩ := treeHashBudget_phase_cut prims D A 0 (2*js.length+2+fuel)
      state prep cont timed s r run
    have fc := treeHashBudget_phase_fields prims D A 1 state
      (fun i => treeHashBudgetHalvingIndexed K (ctx i) width (p i) j) live st tag label 1 counters
      (fun i before value final raw => by
        simp only [treeHashBudgetHalvingIndexed, StateT.run_bind, StateT.run_pure] at raw
        obtain ⟨⟨v, mid⟩, hv, he⟩ := treeSimCheck_some_bind _ _ _ raw
        simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at he
        rw [he.2]
        exact treeHashBudget_halvingPrepare_fields K (ctx i) width (p i) j before v mid hv) s pref first
    let saved := fun i => (pref.1.2 i).getD ((0,j), ⟨fun _ => [], label+1, tag⟩)
    let active := fun i => (pref.1.2 i).isSome
    have nextCounters (i) (hi : i ∉ D.1) :
        (saved i).2.tag = tag ∧ (saved i).2.label = label+1 := by
      cases accepted : pref.1.2 i with
      | none => simp only [saved, accepted, Option.getD_none]; trivial
      | some out =>
        have hc := fc i hi out.1 out.2 accepted
        simp only [saved, accepted, Option.getD_some]
        exact ⟨hc.2, hc.1⟩
    have restart : (fun i => (pref.1.2 i).elim failure (cont i)) = fun i =>
        if active i then (treeHashBudgetHalvingTail K (ctx i) width js (p i) (saved i).1).run (saved i).2 else failure := by
      funext i
      cases h : pref.1.2 i <;> simp only [active, saved, h, Option.isSome_none,
        Bool.false_eq_true, if_false, Option.elim_none, Option.isSome_some,
        if_true, Option.getD_some, Option.elim_some, cont]
    rw [restart] at tail
    obtain ⟨S, size, cover⟩ := treeHashBudget_halvingTail_cover K prims D A ctx self width js fuel
      pref.1.1 active tag (label+1) (fun i => (saved i).2) p (fun i => (saved i).1) nextCounters pref.2 r tail
    refine ⟨S, by simpa only [List.length_cons] using size, ?_⟩
    have firstCover : TreeHashBudgetRegionCover S s.2 pref.2.2 := by
      apply treeHashBudget_zero_phase_cover prims D A 1 state prep _ S s pref first
      intro i _
      dsimp only [prep]
      split_ifs
      · exact ((treeHashBudget_halvingPrepare_zero K (ctx i) width (p i) j).bind_zero
          (fun _ => .pure _ 0)) (st i)
      · exact isQueryBoundP_pure _ _ _
    exact firstCover.trans cover

/-- The challenge preceding a halving fold adds one input to the fold's
bound, even when a receiver rejects before the first multiplication. -/
theorem treeHashBudget_challenge_halving_cover (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (width : ℕ) (js : List ℕ) (fuel : ℕ) (state : A.State)
    (live : C.Party → Bool) (tag label : ℕ) (st : C.Party → RunState C)
    (next : C.Party → E → (ℕ → E) × (ℕ → E) × E)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Option ((E → ℕ → E) × RunState C))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (2*js.length + 2 + fuel) state (fun i =>
        if live i then ((challenge K (realCheckGadgets K (ctx i)) >>= fun v =>
          treeHashBudgetHalvingFold K (ctx i) width js (next i v)).run (st i))
        else failure))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ js.length+1 ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  cases js with
  | nil =>
    simp only [treeHashBudgetHalvingFold, List.foldlM_nil, pure_bind, List.length_nil,
      Nat.mul_zero, Nat.zero_add] at run ⊢
    rw [show 2+fuel = 1+(1+fuel) by omega] at run
    exact treeHashBudget_challenge_phase_cover K prims D A (1+fuel) state ctx self live
      tag label st counters (fun i v => treeLockstepFinalBeforeSalt K (ctx i) (next i v))
      (fun i _ v => treeHashBudget_finalBeforeSalt_zero K (ctx i) (next i v)) s r run
  | cons j js =>
    let body := fun i v => do
      let t ← treeHashBudgetHalvingIndexed K (ctx i) width (next i v) j
      pure (next i v, t)
    let cont := fun i (out : (((ℕ → E) × (ℕ → E) × E) × (Shares C E × ℕ)) × RunState C) =>
      (treeHashBudgetHalvingTail K (ctx i) width js out.1.1 out.1.2).run out.2
    have form : (fun i => if live i then ((challenge K (realCheckGadgets K (ctx i)) >>= fun v =>
        treeHashBudgetHalvingFold K (ctx i) width (j::js) (next i v)).run (st i)) else failure) =
        fun i => (if live i then ((challenge K (realCheckGadgets K (ctx i)) >>= body i).run (st i))
          else failure) >>= cont i := by
      funext i
      by_cases active : live i = true
      · simp only [body, cont, if_pos active, treeHashBudget_halvingFold_cons,
          StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
      · simp only [if_neg active]; rfl
    rw [form, show 2*(j::js).length+2+fuel = 2+(2*js.length+2+fuel) by
      simp only [List.length_cons]; omega] at run
    have zero (i) (_ : i ∉ D.1) (v) : TreeSimHashCount.RunBudget TreeSimHashCount.Region (body i v) 0 := by
      unfold body treeHashBudgetHalvingIndexed
      exact ((treeHashBudget_halvingPrepare_zero K (ctx i) width (next i v) j).bind_zero
        (fun _ => .pure _ 0)).bind_zero (fun _ => .pure _ 0)
    have timed (i) (v) (st) : TreeSimCheckTimed 1 ((body i v).run st).run := by
      simp only [body, treeHashBudgetHalvingIndexed, StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
      exact (treeHashBudget_halvingPrepare_timed K (ctx i) width (next i v) j st).bind (n := 0) (fun _ => .done _)
    have fields (i) (v) (before) (value) (final) (raw : some (value,final) ∈ support
        ((body i v).run before).run) : final.label=before.label+1 ∧ final.tag=before.tag := by
      simp only [body, treeHashBudgetHalvingIndexed, StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc] at raw
      obtain ⟨⟨val, mid⟩, hm, he⟩ := treeSimCheck_some_bind _ _ _ raw
      simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at he
      rw [he.2]
      exact treeHashBudget_halvingPrepare_fields K (ctx i) width (next i v) j before val mid hm
    obtain ⟨pref, S, first, size, cover, counter, tail⟩ := treeHashBudget_challenge_cut K prims D A
      (2*js.length+2+fuel) state ctx self live tag label 1 st counters body zero timed fields cont s r run
    let saved := fun i => (pref.1.2 i).getD ((next i 0, (0,j)), ⟨fun _ => [], label+2, tag⟩)
    let active := fun i => (pref.1.2 i).isSome
    have nextCounters (i) (hi : i ∉ D.1) :
        (saved i).2.tag = tag ∧ (saved i).2.label = label+2 := by
      cases accepted : pref.1.2 i with
      | none => simp only [saved, accepted, Option.getD_none]; trivial
      | some out =>
        have hc := counter i hi out.1 out.2 accepted
        simp only [saved, accepted, Option.getD_some]
        exact ⟨hc.2, hc.1⟩
    have restart : (fun i => (pref.1.2 i).elim failure (cont i)) = fun i =>
        if active i then (treeHashBudgetHalvingTail K (ctx i) width js (saved i).1.1 (saved i).1.2).run (saved i).2 else failure := by
      funext i
      cases h : pref.1.2 i <;> simp only [active, saved, h, Option.isSome_none,
        Bool.false_eq_true, if_false, Option.elim_none, Option.isSome_some,
        if_true, Option.getD_some, Option.elim_some, cont]
    rw [restart] at tail
    obtain ⟨T, tailSize, tailCover⟩ := treeHashBudget_halvingTail_cover K prims D A ctx self width js fuel
      pref.1.1 active tag (label+2) (fun i => (saved i).2) (fun i => (saved i).1.1)
      (fun i => (saved i).1.2) nextCounters pref.2 r tail
    refine ⟨S ∪ T, (Finset.card_union_le _ _).trans ?_, cover.union_trans tailCover⟩
    simp only [List.length_cons]; omega

/-- A slice multiplication carries its reduction index to the following challenge. -/
def treeHashBudgetSliceIndexed (ctx : Context C) (τ : List E) (count : ℕ)
    (p : Shares C E × Shares C E × E) (j : ℕ) : RunM C E RealSpec (Shares C E × ℕ) := do
  let values ← treeHashBudgetSlicePrepare K ctx τ count p j
  pure (values, j)

/-- The slice fold after its first multiplication, including the complete
halving fold and final randomization. -/
def treeHashBudgetSliceTail (ctx : Context C) (τ : List E) (count : ℕ)
    (slices halves : List ℕ) (p : Shares C E × Shares C E × E) (t : Shares C E × ℕ) :
    RunM C E RealSpec (E → ℕ → E) :=
  treeHashBudgetReductionTail K ctx (treeHashBudgetSliceIndexed K ctx τ count)
    (fun p t r => treeHashBudgetSliceUpdate K ctx τ count p t.2 t.1 r)
    (fun p => treeHashBudgetHalvingFold K ctx (sliceWidth count) halves
      (conv K ctx p.1, conv K ctx p.2.1, p.2.2)) slices p t

/-- The shifted slice syntax retains the literal slice and halving folds. -/
theorem treeHashBudget_sliceTail_eq (ctx : Context C) (τ : List E) (count : ℕ)
    (slices halves : List ℕ) (p : Shares C E × Shares C E × E) (t : Shares C E × ℕ) :
    treeHashBudgetSliceTail K ctx τ count slices halves p t = (do
      let r ← challenge K (realCheckGadgets K ctx)
      let out ← slices.foldlM (sliceStep K ctx (realCheckGadgets K ctx) τ count)
        (treeHashBudgetSliceUpdate K ctx τ count p t.2 t.1 r)
      treeHashBudgetHalvingFold K ctx (sliceWidth count) halves
        (conv K ctx out.1, conv K ctx out.2.1, out.2.2)) := by
  unfold treeHashBudgetSliceTail
  rw [treeHashBudget_reduction_tail_eq]
  simp only [treeHashBudgetSliceIndexed, bind_assoc, pure_bind, ← treeHashBudget_sliceStep_eq]

open TreeSimHashCount in
/-- The complete shifted slice and halving reduction counts each actual
challenge once, with independent per-operator arithmetic payloads. -/
theorem treeHashBudget_sliceTail_cover (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (τ : C.Party → List E) (count : ℕ) (slices halves : List ℕ) (fuel : ℕ) (state : A.State)
    (live : C.Party → Bool) (tag label : ℕ) (st : C.Party → RunState C)
    (p : C.Party → Shares C E × Shares C E × E) (t : C.Party → Shares C E × ℕ)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Option ((E → ℕ → E) × RunState C))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (2*slices.length + (2*halves.length+2) + fuel) state (fun i =>
        if live i then (treeHashBudgetSliceTail K (ctx i) (τ i) count slices halves (p i) (t i)).run (st i)
        else failure))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ slices.length+(halves.length+1) ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  apply treeHashBudget_reduction_tail_cover K prims D A ctx self
    (fun i => treeHashBudgetSliceIndexed K (ctx i) (τ i) count)
    (fun i p t r => treeHashBudgetSliceUpdate K (ctx i) (τ i) count p t.2 t.1 r)
    (fun i p => treeHashBudgetHalvingFold K (ctx i) (sliceWidth count) halves
      (conv K (ctx i) p.1, conv K (ctx i) p.2.1, p.2.2))
    (fun i _ p j => (treeHashBudget_slicePrepare_zero K (ctx i) (τ i) count p j).bind_zero
      (fun _ => .pure _ 0))
    (fun i p j st => by
      simp only [treeHashBudgetSliceIndexed, StateT.run_bind, StateT.run_pure]
      exact (treeHashBudget_slicePrepare_timed K (ctx i) (τ i) count p j st).bind (n := 0) (fun _ => .done _))
    (fun i p j before value final raw => by
      simp only [treeHashBudgetSliceIndexed, StateT.run_bind, StateT.run_pure] at raw
      obtain ⟨⟨val, mid⟩, hm, he⟩ := treeSimCheck_some_bind _ _ _ raw
      simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at he
      rw [he.2]
      exact treeHashBudget_slicePrepare_fields K (ctx i) (τ i) count p j before val mid hm)
    (fun _ => pure) (2*halves.length+2) (halves.length+1) _ slices fuel state live tag label st p t counters s r
  · simpa only [treeHashBudgetSliceTail, bind_pure] using run
  · intro fuel state live tag label st p t counters s r run
    simp only [treeHashBudgetReductionTail, bind_pure] at run
    exact treeHashBudget_challenge_halving_cover K prims D A ctx self (sliceWidth count) halves fuel
      state live tag label st
      (fun i r => let out := treeHashBudgetSliceUpdate K (ctx i) (τ i) count (p i) (t i).2 (t i).1 r
        (conv K (ctx i) out.1, conv K (ctx i) out.2.1, out.2.2)) counters s r run

/-- The first Coin through the first slice multiplication. -/
def treeHashBudgetCheckInitial (ctx : Context C) (tuples : List (Tuple C)) :
    RunM C E RealSpec (List E × (Shares C E × Shares C E × E) × Shares C E) := do
  let key ← coinKey K (realCheckGadgets K ctx)
  treeHashBudgetSliceInitial K ctx tuples key

theorem treeHashBudget_checkInitial_timed (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C) :
    TreeSimCheckTimed 2 ((treeHashBudgetCheckInitial K ctx tuples).run st).run := by
  simp only [treeHashBudgetCheckInitial, coinKey, StateT.run_bind, StateT.run_get,
    StateT.run_lift, pure_bind, bind_assoc]
  apply (treeLockstep_timed_coin K ctx 1 st).bind (n := 1)
  intro out
  apply TreeSimCheckTimed.oracle_bind 0
  intro key
  exact treeHashBudget_sliceInitial_timed K ctx tuples key out.2

theorem treeHashBudget_checkInitial_fields (ctx : Context C) (tuples : List (Tuple C))
    (st : RunState C) (value) (final : RunState C)
    (run : some (value, final) ∈ support ((treeHashBudgetCheckInitial K ctx tuples).run st).run) :
    final.label = st.label+2 ∧ final.tag = st.tag := by
  simp only [treeHashBudgetCheckInitial, StateT.run_bind] at run
  obtain ⟨⟨key, mid⟩, hk, hs⟩ := treeSimCheck_some_bind _ _ _ run
  have hc := treeHashBudget_coinKey_state K ctx st key mid hk
  have hf := treeHashBudget_sliceInitial_fields K ctx tuples key mid value final hs
  simp only [hc, nextLabel] at hf
  exact ⟨by omega, hf.2⟩

/-- The literal pre-salt check factors at its first multiplication, before
the remaining slice and halving challenges. -/
theorem treeHashBudget_beforeSalt_factor (ctx : Context C) (tuples : List (Tuple C)) :
    treeLockstepCheckBeforeSalt K ctx tuples = (do
      let value ← treeHashBudgetCheckInitial K ctx tuples
      treeHashBudgetSliceTail K ctx value.1 (tuples.map (·.count)).sum
        (List.range sliceBits).tail (List.range (halvings (tuples.map (·.count)).sum - sliceBits))
        value.2.1 (value.2.2, 0)) := by
  have range : List.range sliceBits = 0 :: (List.range sliceBits).tail := by decide
  unfold treeLockstepCheckBeforeSalt treeLockstepCheckPrefixWith treeHashBudgetCheckInitial treeHashBudgetSliceInitial
  rw [range]
  simp only [List.foldlM_cons, treeHashBudget_sliceStep_eq, treeHashBudget_sliceTail_eq,
    treeHashBudgetHalvingFold, List.tail_cons, bind_assoc, pure_bind]

/-- The actual check before its salt draw has one common counted input per
Coin, including the initial expansion Coin and all rejected prefixes. -/
theorem treeHashBudget_beforeSalt_cover (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (tuples : C.Party → List (Tuple C)) (count : ℕ)
    (counts : ∀ i, i ∉ D.1 → ((tuples i).map (·.count)).sum = count)
    (fuel : ℕ) (state : A.State) (live : C.Party → Bool) (tag label : ℕ)
    (st : C.Party → RunState C)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Option ((E → ℕ → E) × RunState C))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (2*sliceBits + 2*(halvings count-sliceBits) + 2 + fuel) state (fun i =>
          if live i then (treeLockstepCheckBeforeSalt K (ctx i) (tuples i)).run (st i)
          else failure))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ halvings count+1 ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  let slices := (List.range sliceBits).tail
  let halves := List.range (halvings count-sliceBits)
  let restFuel := 2*slices.length+(2*halves.length+2)+fuel
  let prep := fun i => if live i then (treeHashBudgetCheckInitial K (ctx i) (tuples i)).run (st i) else failure
  let cont := fun i (out : (List E × (Shares C E × Shares C E × E) × Shares C E) × RunState C) =>
    (treeHashBudgetSliceTail K (ctx i) out.1.1 count slices halves out.1.2.1 (out.1.2.2,0)).run out.2
  have form := treeHashBudget_phase_congr D A
    (2*sliceBits+2*(halvings count-sliceBits)+2+fuel) state
    (fun i => if live i then (treeLockstepCheckBeforeSalt K (ctx i) (tuples i)).run (st i) else failure)
    (fun i => prep i >>= cont i) (by
      intro i hi
      by_cases active : live i = true
      · simp only [prep, cont, slices, halves, if_pos active, treeHashBudget_beforeSalt_factor,
          StateT.run_bind, counts i hi]
      · simp only [prep, if_neg active]; rfl)
  have ls : slices.length = sliceBits-1 := by simp [slices]
  have lh : halves.length = halvings count-sliceBits := by simp [halves]
  have positive : 0 < sliceBits := by decide
  have fuelEq : 2*sliceBits+2*(halvings count-sliceBits)+2+fuel = 2+restFuel := by
    dsimp only [restFuel]
    omega
  rw [form, fuelEq] at run
  have timed (i) : TreeSimCheckTimed (1+1) (prep i).run := by
    dsimp only [prep]
    split_ifs
    · exact treeHashBudget_checkInitial_timed K _ _ _
    · exact .abort _
  obtain ⟨pref, first, tail⟩ := treeHashBudget_phase_cut prims D A 1 restFuel state prep cont timed s r run
  obtain ⟨S, size, cover⟩ := treeHashBudget_coinKey_phase_cover K prims D A 1 state ctx self
    live tag label st counters (fun i => treeHashBudgetSliceInitial K (ctx i) (tuples i))
    (fun i _ key => treeHashBudget_sliceInitial_zero K (ctx i) (tuples i) key) s pref first
  have fc := treeHashBudget_phase_fields prims D A 2 state
    (fun i => treeHashBudgetCheckInitial K (ctx i) (tuples i)) live st tag label 2 counters
    (fun i => treeHashBudget_checkInitial_fields K (ctx i) (tuples i)) s pref first
  let saved := fun i => (pref.1.2 i).getD (([],(0,0,0),0),⟨fun _ => [],label+2,tag⟩)
  let active := fun i => (pref.1.2 i).isSome
  have nextCounters (i) (hi : i ∉ D.1) :
      (saved i).2.tag = tag ∧ (saved i).2.label = label+2 := by
    cases accepted : pref.1.2 i with
    | none => simp only [saved, accepted, Option.getD_none]; trivial
    | some out =>
      have hc := fc i hi out.1 out.2 accepted
      simp only [saved, accepted, Option.getD_some]
      exact ⟨hc.2, hc.1⟩
  have restart : (fun i => (pref.1.2 i).elim failure (cont i)) = fun i =>
      if active i then
        (treeHashBudgetSliceTail K (ctx i) (saved i).1.1 count slices halves
          (saved i).1.2.1 ((saved i).1.2.2,0)).run (saved i).2 else failure := by
    funext i
    cases h : pref.1.2 i <;> simp only [active, saved, h, Option.isSome_none,
      Bool.false_eq_true, if_false, Option.elim_none, Option.isSome_some,
      if_true, Option.getD_some, Option.elim_some, cont]
  rw [restart] at tail
  obtain ⟨T, tailSize, tailCover⟩ := treeHashBudget_sliceTail_cover K prims D A ctx self
    (fun i => (saved i).1.1) count slices halves fuel pref.1.1 active tag (label+2)
    (fun i => (saved i).2) (fun i => (saved i).1.2.1) (fun i => ((saved i).1.2.2,0))
    nextCounters pref.2 r tail
  refine ⟨S ∪ T, (Finset.card_union_le _ _).trans ?_, cover.union_trans tailCover⟩
  have lower : sliceBits ≤ halvings count := by unfold halvings; omega
  omega

/-- A positive timed region-free prefix shields the first local head from
an arbitrary later continuation. -/
theorem treeHashBudget_head_zero_bind {α β : Type} (p : PartyM C E RealSpec α)
    (k : α → PartyM C E RealSpec β) (n : ℕ)
    (timed : TreeSimCheckTimed (n+1) p.run)
    (zero : TreeSimHashCount.PartyBudget TreeSimHashCount.Region p 0) :
    IsQueryBoundP (advance (p >>= k).run) TreeSimHashCount.Region 0 := by
  rw [advance_bind, timed.suspend, isQueryBoundP_map_iff]
  exact advance_zero _ _ zero

/-- A zero-exchange snapshot has exactly the counted queries of the local
head it captures; the saved continuation is not evaluated. -/
theorem treeHashBudget_snapshot_zero {α : Type} (p : PartyM C E RealSpec α)
    (zero : IsQueryBoundP (advance p.run) TreeSimHashCount.Region 0) :
    TreeSimHashCount.PartyBudget TreeSimHashCount.Region (treeLateSnapshot 0 p) 0 := by
  unfold TreeSimHashCount.PartyBudget
  rw [treeLateSnapshot_zero_run, isQueryBoundP_map_iff]
  have h := TreeSimHashCount.localStep_bound (E := E) (G := RealSpec) zero
  change IsQueryBoundP (some <$> liftComp (advance p.run) (PartySpec C E RealSpec)) _ 0 at h
  exact (isQueryBoundP_map_iff _ _ _).mp h

/-- A snapshot at the start of an audited batch has no counted local head,
regardless of the later tuple check and ceremony continuation. -/
theorem treeHashBudget_batchPrefix_snapshot_zero {α : Type} (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (k : (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C) →
      PartyM C E RealSpec α) :
    TreeSimHashCount.PartyBudget TreeSimHashCount.Region
      (treeLateSnapshot 0 (treeSimCheckBatchPrefix K circuits settings ctx jobs initial >>= k)) 0 :=
  treeHashBudget_snapshot_zero _ (treeHashBudget_head_zero_bind _ _ _
    (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs initial)
    (treeHashBudget_batchPrefix_zero K circuits settings ctx jobs initial))

/-- A saved opening followed by a positive timed continuation admits an
exact cut after that continuation. Its post-exchange copy hashes remain
in their original local order. -/
theorem treeHashBudget_open_then_timed {α : Type} (ctx : Context C) (v : Shares C Bit)
    (count n : ℕ) (k : (ℕ → Bit) → PartyM C E RealSpec α)
    (timed : ∀ out, TreeSimCheckTimed (n+1) (k out).run) :
    TreeSimCheckTimed (n+2) (openRep K ctx v count >>= k).run := by
  unfold openRep
  simp only [bind_assoc]
  apply TreeSimCheckTimed.oracle_bind (n+1)
  intro digests
  apply TreeSimCheckTimed.exchange_bind (n+1)
  intro inbox
  apply TreeSimCheckTimed.oracle_bind n
  intro copyDigests
  simp only [require, pure_bind]
  split_ifs
  · exact timed _
  · exact .abort _

end ShiftedCheck

-- A75_FINISH_COVER_BEGIN
section FinishCover
open TreeSimHashCount

/-- Failure gates preserve the actual first copy-hash pass and its waiting rows. -/
theorem treeHashBudget_open_start_gated {α : Type} (D : C.Coalition)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α) :
    startSteps worldRoles D (fun i => if live i then openRep K (ctx i) (v i) count >>= k i
      else failure) = (do
      let ds ← free (treeLockstepOpenHashes D live count v)
      pure (treeSimOpenPartial K D live count v ds k)) := by
  unfold startSteps treeLockstepOpenHashes
  rw [free_sequenceFin]
  have one : ∀ i : C.Party,
      (if i ∈ D.1 then pure (Step.done none) else worldRoles.honest
        (advance ((if live i then openRep K (ctx i) (v i) count >>= k i else failure).run))) = (do
      let ds ← free (if i ∉ D.1 ∧ live i = true then
        liftComp (treeSimOpenCopyHashes count (v i)) (LocalSpec C) else pure [])
      pure (if i ∈ D.1 then .done none else if live i then
        treeSimOpenStep K i count (v i) ds (k i) else .done none)) := by
    intro i
    by_cases hi : i ∈ D.1
    · simp only [hi, if_true, not_true_eq_false, false_and, if_false, free_pure, pure_bind]
    · by_cases hl : live i = true
      · simp only [hi, hl, if_false, if_true, not_false_eq_true, true_and]
        simpa only [self i, map_eq_bind_pure_comp, Function.comp_def] using
          treeSim_open_entry K (ctx i) count (v i) (k i)
      · simp only [hi, hl, if_false, not_false_eq_true, true_and]
        rfl
  simp_rw [one]
  rw [sequenceFin_bind_pure]
  rfl

/-- After the opening exchange every remaining honest query belongs to its
original continuation, including when the copy comparison fails. -/
theorem treeHashBudget_open_round_budget {α : Type} (prims : Primitives) (D : C.Coalition)
    (P : (LocalSpec C).Domain → Prop)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α)
    (zero : ∀ i out, PartyBudget P (k i out) 0)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (stepRound worldRoles D A noFunctionality state
        (treeSimOpenPartial K D live count v ds k))).run s)) :
    ∀ i, StepBudget P (r.1.2.1 i) 0 := by
  rw [stepRound_real] at run
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨adv, _, next, hnext, rfl⟩ := run
  letI : Preorder (TreeSimState C) := {
    le := fun _ _ => True
    le_refl := fun _ => trivial
    le_trans := fun _ _ _ _ _ => trivial }
  rw [free_sequenceFin, simulateQ_sequenceFin] at hnext
  refine (sequenceFin_state_post _ (fun _ out _ => StepBudget P out 0)
    (fun i cache out localRun => ⟨trivial, ?_⟩)
    (fun _ _ _ _ _ h => h) adv.2 next hnext).2
  rw [treeLockstep_open_local_factor] at localRun
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at localRun
  obtain ⟨head, _, tail⟩ := localRun
  have raw := free_support prims D _ head.2 out tail
  cases h : head.1 with
  | none =>
    simp only [h, treeSimResume, mem_support_pure_iff] at raw
    rw [raw]
    trivial
  | some value =>
    simp only [h, treeSimResume] at raw
    exact advance_stepBudget _ _ (zero i value) _ raw

/-- A gated replicated opening and any region-free continuation have one
common cover for both copy passes and all later aborted prefixes. -/
theorem treeHashBudget_open_phase_gated {α : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (zero : ∀ i T, i ∉ C.holders T → ∀ g, v i T g = 0)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α)
    (tailZero : ∀ i out, PartyBudget Region (k i out) 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (fuel+1) state (fun i =>
        if live i then openRep K (ctx i) (v i) count >>= k i else failure))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ C.n * termCount C + 1 ∧
      TreeHashBudgetRegionCover S s.2 r.2.2 := by
  unfold executePhase at run
  rw [treeHashBudget_open_start_gated K D ctx self] at run
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨start, ⟨ds, hashes, rfl⟩, rest⟩ := run
  rw [executeRounds_eq_executeSteps] at rest
  simp only [simulateQ_map, StateT.run_map, support_map] at rest
  obtain ⟨last, hlast, eq⟩ := rest
  have logs : last.2.2 = r.2.2 := congrArg (fun z => z.2.2) eq
  rw [← logs]
  rw [executeSteps] at hlast
  split_ifs at hlast with stopped
  · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hlast
    subst last
    obtain ⟨S, size, points⟩ := treeSimHash_open_points K count v (fun _ _ => none) zero
    refine ⟨S, size, TreeHashCover.region ?_⟩
    apply treeHashBudget_free_cover prims D S _ _ s ds hashes
    unfold treeLockstepOpenHashes
    apply isQueryBoundP_sequenceFin
    intro i
    split_ifs
    · exact hashes_freeHashIn_zero _ _ _ (fun T _ outside => outside (points i T).1)
    · exact isQueryBoundP_pure _ _ _
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hlast
    obtain ⟨next, hnext, tail⟩ := hlast
    obtain ⟨S, size, cover⟩ := treeHashBudget_open_boundary K prims D A state live count v zero
      k (fun i out => advance_zero _ _ (tailZero i out)) s ds hashes next hnext
    refine ⟨S, size, cover.trans ?_⟩
    apply treeHashBudget_steps_cover prims D S A fuel next.1.1 next.1.2.1 next.2 last _ tail
    apply treeHashBudget_open_round_budget K prims D _ A state live count v ds.1 k _ ds.2 next hnext
    intro i out
    apply IsQueryBoundP.of_imp _ (tailZero i out)
    rintro ((t | _) | _) ht
    · obtain ⟨q, domain, eq⟩ := ht
      exact treeHashBudget_free_region t ⟨q, domain.1, eq⟩
    · exact ht.elim
    · exact ht.elim

private theorem treeHashBudget_timed_require {α : Type} (n : ℕ) (p : Prop)
    (k : Unit → PartyM C E RealSpec α) (hk : ∀ u, TreeSimCheckTimed n (k u).run) :
    TreeSimCheckTimed n (require p >>= k).run := by
  unfold require
  split_ifs
  · simpa only [pure_bind] using hk ()
  · exact .abort n

/-- The post-digest scalar test ends after the challenge and Shamir opening. -/
theorem treeHashBudget_checkSuffix_timed (ctx : Context C) (polynomial : E → ℕ → E)
    (st : RunState C) :
    TreeSimCheckTimed 2 ((treeLockstepCheckSuffix K ctx polynomial).run st).run := by
  unfold treeLockstepCheckSuffix
  simp only [StateT.run_bind, StateT.run_lift]
  apply treeLockstep_timed_challenge K ctx 0
  intro value
  unfold openSh
  simp only [bind_assoc]
  apply TreeSimCheckTimed.exchange_bind 0
  intro inbox
  apply treeHashBudget_timed_require 0
  intro _
  simp only [pure_bind]
  apply treeHashBudget_timed_require 0
  intro _
  exact .done _

/-- The whole post-digest challenge and scalar test use at most one common
coin-key input, including rejected challenges and scalar openings. -/
theorem treeHashBudget_checkSuffix_cover (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (live : C.Party → Bool) (tag label : ℕ) (st : C.Party → RunState C)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (polynomial : C.Party → E → ℕ → E)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option (Unit × RunState C))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (1+fuel) state (fun i =>
        if live i then (treeLockstepCheckSuffix K (ctx i) (polynomial i)).run (st i)
        else failure))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ 1 ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  unfold treeLockstepCheckSuffix at run
  apply treeHashBudget_challenge_phase_cover K prims D A fuel state ctx self live tag label st
    counters _ _ s r run
  intro i _ value
  exact (RunBudget.lift (PartyBudget.of_all (RunBound.openSh K (ctx i) _ 3))).bind
    (m := 0) (fun opened => RunBudget.lift (PartyBudget.of_all (PartyBound.require _)))

/-- The original scalar check, replicated opening and region-free continuation
share a cover of one coin key and at most n*T+1 copy inputs. -/
theorem treeHashBudget_check_open_cover {α : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (live : C.Party → Bool) (tag label : ℕ) (st : C.Party → RunState C)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (polynomial : C.Party → E → ℕ → E)
    (count : ℕ) (v : C.Party → Shares C Bit)
    (zero : ∀ i T, i ∉ C.holders T → ∀ g, v i T g = 0)
    (k : C.Party → Unit × RunState C → (ℕ → Bit) → PartyM C E RealSpec α)
    (tailZero : ∀ i saved out, PartyBudget Region (k i saved out) 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (2+(fuel+1)) state (fun i =>
        (if live i then (treeLockstepCheckSuffix K (ctx i) (polynomial i)).run (st i)
        else failure) >>= fun saved => openRep K (ctx i) (v i) count >>= k i saved))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ C.n * termCount C + 2 ∧
      TreeHashBudgetRegionCover S s.2 r.2.2 := by
  let p := fun i => if live i then
    (treeLockstepCheckSuffix K (ctx i) (polynomial i)).run (st i) else failure
  have timed (i) : TreeSimCheckTimed (1+1) (p i).run := by
    dsimp only [p]
    split_ifs
    · exact treeHashBudget_checkSuffix_timed K _ _ _
    · exact .abort _
  obtain ⟨pref, first, tail⟩ := treeHashBudget_phase_cut prims D A 1 (fuel+1) state p
    (fun i saved => openRep K (ctx i) (v i) count >>= k i saved) timed s r run
  obtain ⟨S, size, cover⟩ := treeHashBudget_checkSuffix_cover K prims D A 1 state ctx self
    live tag label st counters polynomial s pref first
  let active := fun i => (pref.1.2 i).isSome
  let saved := fun i => (pref.1.2 i).getD ((), st i)
  have rewrite : (fun i => (pref.1.2 i).elim failure
      (fun saved => openRep K (ctx i) (v i) count >>= k i saved)) =
      (fun i => if active i then openRep K (ctx i) (v i) count >>= k i (saved i) else failure) := by
    funext i
    cases h : pref.1.2 i <;> simp [h, active, saved]
  rw [rewrite] at tail
  obtain ⟨T, sizeT, coverT⟩ := treeHashBudget_open_phase_gated K prims D A fuel pref.1.1 ctx self
    active count v zero (fun i => k i (saved i)) (fun i => tailZero i (saved i)) pref.2 r tail
  refine ⟨S ∪ T, ?_, cover.union_trans coverT⟩
  have := Finset.card_union_le S T
  omega


/-- Salt generation increments the label once; digest comparison leaves
that state unchanged on every successful raw execution. -/
theorem treeHashBudget_saltedDigest_state (ctx : Context C) (before final : RunState C)
    (run : some ((), final) ∈ support ((treeStagesSaltedDigest K ctx).run before).run) :
    final = nextLabel before := by
  unfold treeStagesSaltedDigest at run
  change some ((), final) ∈ support
    ((prssRandomness ctx (bitCodec (E := E)) 2 256 >>= fun salts =>
      compareDigests ctx salts.1).run before).run at run
  rw [prssRandomness_run] at run
  obtain ⟨rnd, _, rest⟩ := treeSimCheck_some_bind _ _ _ run
  rw [compareDigests_run] at rest
  obtain ⟨ds, _, rest⟩ := treeSimCheck_some_bind _ _ _ rest
  obtain ⟨inbox, _, rest⟩ := treeSimCheck_some_bind _ _ _ rest
  obtain ⟨u, _, eq⟩ := treeSimCheck_some_bind _ _ _ rest
  simpa only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq,
    true_and] using eq

/-- The salt draws and digest hashes precede one exchange with only a pure
digest-equality test afterward. -/
theorem treeHashBudget_saltedDigest_timed (ctx : Context C) (st : RunState C) :
    TreeSimCheckTimed 1 ((treeStagesSaltedDigest K ctx).run st).run := by
  unfold treeStagesSaltedDigest
  change TreeSimCheckTimed 1
    ((prssRandomness ctx (bitCodec (E := E)) 2 256 >>= fun salts =>
      compareDigests ctx salts.1).run st).run
  rw [prssRandomness_run]
  exact TreeSimCheckTimed.oracle_bind 0 _ _
    (fun rnd => treeLockstep_timed_digest (E := E) ctx rnd.1 (nextLabel st))


/-- The actual salted-digest cut retains every failed row and advances the
common label once on each present output. -/
theorem treeHashBudget_saltedDigest_cut {α : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (live : C.Party → Bool)
    (tag label : ℕ) (st : C.Party → RunState C)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (1+fuel) state (fun i =>
        (if live i then (treeStagesSaltedDigest K (ctx i)).run (st i) else failure) >>= k i))).run s)) :
    ∃ pref : (A.State × (C.Party → Option (Unit × RunState C))) × TreeSimState C,
      pref ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality 1 state (fun i =>
          if live i then (treeStagesSaltedDigest K (ctx i)).run (st i) else failure))).run s) ∧
      (∀ i, i ∉ D.1 → ∀ value final, pref.1.2 i = some (value, final) →
        final.label = label+1 ∧ final.tag = tag) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel pref.1.1
          (fun i => (pref.1.2 i).elim failure (k i)))).run pref.2) := by
  let p := fun i => if live i then (treeStagesSaltedDigest K (ctx i)).run (st i) else failure
  have timed (i) : TreeSimCheckTimed (0+1) (p i).run := by
    dsimp only [p]
    split_ifs
    · exact treeHashBudget_saltedDigest_timed K _ _
    · exact .abort _
  obtain ⟨pref, first, tail⟩ := treeHashBudget_phase_cut prims D A 0 fuel state p k timed s r run
  refine ⟨pref, first, ?_, tail⟩
  apply treeHashBudget_phase_fields prims D A 1 state (fun i => treeStagesSaltedDigest K (ctx i))
    live st tag label 1 counters _ s pref first
  intro i before value final raw
  cases value
  rw [treeHashBudget_saltedDigest_state K (ctx i) before final raw]
  exact ⟨rfl, rfl⟩

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_open_start_gated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_open_start_gated

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_open_round_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_open_round_budget

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_open_phase_gated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_open_phase_gated

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_checkSuffix_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_checkSuffix_timed

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_checkSuffix_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_checkSuffix_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_check_open_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_check_open_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_saltedDigest_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_saltedDigest_state

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_saltedDigest_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_saltedDigest_timed

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_saltedDigest_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_saltedDigest_cut

end FinishCover

-- A75_FINISH_COVER_END

-- A75_SALTED_COVER_BEGIN
section SaltedCover
open TreeSimHashCount
variable (prims : Primitives) (D : C.Coalition)

/-- A traversal retains witnesses for its actual component executions and composes their covers. -/
theorem treeHashBudget_sequence_witness {α β : Type} (log : TreeSimLog C) :
    ∀ {n : ℕ} (f : Fin n → OracleComp (WorldSpec C) α)
      (P : Fin n → α → β → Prop) (Q : Fin n → β → Finset (Query C) → Prop),
      (∀ i s r, r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (f i)).run s) →
        r.2.2 ⊆ log → ∃ w, P i r.1 w ∧ ∀ S, Q i w S →
          TreeHashBudgetRegionCover S s.2 r.2.2) →
      ∀ s r, r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (Concrete.sequenceFin f)).run s) → r.2.2 ⊆ log →
      ∃ w : Fin n → β, (∀ i, P i (r.1 i) (w i)) ∧
        ∀ S, (∀ i, Q i (w i) S) → TreeHashBudgetRegionCover S s.2 r.2.2
  | 0, f, P, Q, step, s, r, run, final => by
    simp only [Concrete.sequenceFin, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at run
    subst r
    exact ⟨Fin.elim0, fun i => i.elim0, fun S _ => .refl S s.2⟩
  | n+1, f, P, Q, step, s, r, run, final => by
    simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at run
    obtain ⟨a, ha, tail, ht, rfl⟩ := run
    have grows := (treeSimLoggedWorld_prefix prims D _ a.2 tail ht).subset
    obtain ⟨first, property, cover⟩ := step 0 s a ha (grows.trans final)
    obtain ⟨rest, properties, covers⟩ := treeHashBudget_sequence_witness log
      (fun i : Fin n => f i.succ) (fun i => P i.succ) (fun i => Q i.succ)
      (fun i => step i.succ) a.2 tail ht final
    refine ⟨Fin.cases first rest, ?_, ?_⟩
    · intro i
      cases i using Fin.cases
      · exact property
      · exact properties _
    · intro S points
      exact (cover S (points 0)).trans (covers S (fun i => points i.succ))

/-- PRSS bit draws issue no query in the honest hash budget domain. -/
theorem treeHashBudget_prssDraw_zero (ctx : Context C) (label idx count : ℕ) :
    IsQueryBoundP (liftComp (prssDraw ctx (bitCodec (E := E)) label idx count) (LocalSpec C))
      Region 0 := by
  apply ro_bound
  unfold prssDraw
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => ?_)
  · unfold termDraws
    simpa only [Nat.mul_zero] using queryBound_mapM (fun t => Region (C := C) (.inr t))
      (fun T => if ctx.self ∈ C.holders T then
        (bitCodec (E := E)).draw (.term T) (ctx.prss.term T) label idx count else pure fun _ => 0)
      0 C.terms (fun T _ => by
        split_ifs
        · exact prg_zero _ _ _ _ _
        · exact isQueryBoundP_pure _ _ _)
  · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
    unfold pairDraws
    simpa only [Nat.mul_zero] using queryBound_mapM (fun t => Region (C := C) (.inr t))
      (fun j => if h : j = ctx.self then pure fun _ => 0 else
        (bitCodec (E := E)).draw (.pair (C.pairOf ctx.self j (Ne.symm h)))
          (ctx.prss.pair j) label idx count) 0 C.parties (fun j _ => by
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · exact prg_zero _ _ _ _ _)

/-- The actual interleaved salt draws and digest rows retain witnesses and a common cover law. -/
theorem treeHashBudget_saltedDigest_partial_cover {α : Type}
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (live : C.Party → Bool) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i) (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
      (fun i (_ : Unit) => (treeStagesSaltedDigest K (ctx i)).run (st i) >>= k i)
      (fun i => if i ∈ D.1 then none else if live i then some () else none))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ (salts : C.Party → Shares C Bit), ∃ ds,
      r.1 = treeSimCheckWaiting K D live (.digests ds)
        (fun i => k i ((), nextLabel (st i))) ∧
      (∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T → ∃ h d,
        TreeSimHashAnswer log (.history ((st i).history T)) h ∧
        TreeSimHashAnswer log (.digest (vector 256 (salts i T)) h) d ∧
        (ds i)[C.terms.idxOf T]? = some d) ∧
      ∀ S, (∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T →
        Query.history (C := C) ((st i).history T) ∈ S ∧
        Query.digest (vector 256 (salts i T))
          ((cache (.history ((st i).history T))).getD 0) ∈ S) →
        TreeHashBudgetRegionCover S s.2 r.2.2 := by
  let P := fun (i : C.Party) (v : Step C E RealSpec α) (w : Shares C Bit × List HashOutput) =>
    v = treeSimCheckWaiting K D live (.digests (fun _ => w.2))
      (fun j => k j ((), nextLabel (st j))) i ∧
    (i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T → ∃ h d,
      TreeSimHashAnswer log (.history ((st i).history T)) h ∧
      TreeSimHashAnswer log (.digest (vector 256 (w.1 T)) h) d ∧
      w.2[C.terms.idxOf T]? = some d)
  let Q := fun (i : C.Party) (w : Shares C Bit × List HashOutput) (S : Finset (Query C)) =>
    i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T →
      Query.history (C := C) ((st i).history T) ∈ S ∧
      Query.digest (vector 256 (w.1 T)) ((cache (.history ((st i).history T))).getD 0) ∈ S
  unfold treeSimResumeAll at run
  rw [free_sequenceFin] at run
  have step : ∀ i a b, b ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (treeSimResume
        (fun (_ : Unit) => (treeStagesSaltedDigest K (ctx i)).run (st i) >>= k i)
        (if i ∈ D.1 then none else if live i then some () else none)))).run a) →
      b.2.2 ⊆ log → ∃ w, P i b.1 w ∧ ∀ S, Q i w S →
        TreeHashBudgetRegionCover S a.2 b.2.2 := by
    intro i a b hb future
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff] at hb
      subst b
      exact ⟨(fun _ _ => 0, []), ⟨by simp [treeSimCheckWaiting, hi],
        fun hn => (hn hi).elim⟩, fun S _ => .refl S a.2⟩
    · simp only [if_neg hi] at hb
      by_cases hl : live i = true
      · simp only [if_pos hl, treeSimResume, treeLockstep_saltedDigest_factor,
          simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hb
        obtain ⟨rnd, hrnd, hb⟩ := hb
        change b ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (worldRoles.honest (advance (((compareDigests (ctx i) rnd.1.1).run
            (nextLabel (st i)) >>= k i).run)))).run rnd.2) at hb
        rw [treeSim_digest_entry (K := K), self i hi] at hb
        simp only [simulateQ_map, StateT.run_map, support_map] at hb
        obtain ⟨v, hv, rfl⟩ := hb
        refine ⟨(rnd.1.1, v.1), ⟨?_, ?_⟩, ?_⟩
        · simp [treeSimCheckWaiting, hi, hl]
        · intro _ _ T held
          obtain ⟨h, d, hh, hd, idx⟩ := treeStages_digestQuery_log prims D i rnd.1.1
            (nextLabel (st i)).history rnd.2 v hv T held
          exact ⟨h, d, hh.imp (fun h => future h) (fun h => future h),
            hd.imp (fun h => future h) (fun h => future h), idx⟩
        · intro S points
          have first := treeHashBudget_local_zero_cover prims D S _
            (treeHashBudget_prssDraw_zero (E := E) (ctx i) (st i).label 2 256) a rnd hrnd
          refine first.trans (TreeHashCover.region ?_)
          apply treeHashBudget_digestQueries_cover prims D S log i rnd.1.1 (st i).history
            (fun T => (cache (.history ((st i).history T))).getD 0) ?_
            (points hi hl) C.terms rnd.2 v hv future
          intro T h answer
          rw [coherent (.history ((st i).history T)) h trivial answer]
          rfl
      · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure,
          mem_support_pure_iff] at hb
        subst b
        exact ⟨(fun _ _ => 0, []), ⟨by simp [treeSimCheckWaiting, hi, hl],
          fun _ active => (hl active).elim⟩, fun S _ => .refl S a.2⟩
  obtain ⟨w, properties, cover⟩ := treeHashBudget_sequence_witness prims D log _ P Q step s r run final
  refine ⟨fun i => (w i).1, fun i => (w i).2, ?_, ?_, cover⟩
  · funext i
    have shape := (properties i).1
    simpa only [treeSimCheckWaiting, treeSimCheckStep, treeSimCheckOut, TreeSimCheckAccept] using shape
  · exact fun i => (properties i).2

/-- Pure continuations retain the accepted rows without issuing oracle queries. -/
theorem treeHashBudget_resume_pure {α β : Type}
    (f : C.Party → β → α) (out : C.Party → Option β) :
    treeSimResumeAll (fun i x => (pure (f i x) : PartyM C E RealSpec α)) out =
      pure (fun i => Step.done ((out i).map (f i))) := by
  have one (i) : treeSimResume (fun x => (pure (f i x) : PartyM C E RealSpec α)) (out i) =
      pure (Step.done ((out i).map (f i))) := by
    cases out i <;> simp [treeSimResume, OptionT.run_pure, advance_pure]
  simp only [treeSimResumeAll, one, sequenceFin_pure, free_pure]

/-- The sampled prefix has the terminal cover, and any accepting digest receiver gives the cheap cover. -/
theorem treeHashBudget_saltedDigest_covers {α : Type}
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (live : C.Party → Bool) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i) (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
      (fun i (_ : Unit) => (treeStagesSaltedDigest K (ctx i)).run (st i) >>= k i)
      (fun i => if i ∈ D.1 then none else if live i then some () else none))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ ds, r.1 = treeSimCheckWaiting K D live (.digests ds)
      (fun i => k i ((), nextLabel (st i))) ∧
      (∃ S : Finset (Query C), S.card ≤ (C.n + 1) * termCount C ∧
        TreeHashBudgetRegionCover S s.2 r.2.2) ∧
      ∀ sent receiver, treeSimCheckResult K D live (.digests ds) sent receiver = some () →
        ∃ S : Finset (Query C), S.card ≤ 2 * termCount C ∧
          TreeHashBudgetRegionCover S s.2 r.2.2 := by
  obtain ⟨salts, ds, waiting, recorded, covers⟩ := treeHashBudget_saltedDigest_partial_cover
    K prims D log cache coherent live ctx self st k s r run final
  refine ⟨ds, waiting, ?_, ?_⟩
  · obtain ⟨S, size, points⟩ := treeSimHash_digest_terminal_points
      (fun i T => vector 256 (salts i T)) (fun i => (st i).history)
      (fun i T => (cache (.history ((st i).history T))).getD 0)
    exact ⟨S, size, covers S (fun i _ _ => points i)⟩
  · intro sent receiver accepted
    have all : ∀ i, i ∉ D.1 → live i = true := by
      intro i hi
      by_contra hn
      rw [treeStages_check_inactive K D live (.digests ds) ⟨i, hi, hn⟩] at accepted
      cases accepted
    have inbox : treeSimCheckInbox D live (.digests ds) sent receiver =
        digestInbox D ds sent receiver := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimCheckInbox, digestInbox, hi]
      · simp [treeSimCheckInbox, digestInbox, hi, all i hi, treeSimCheckOut]
    have passed : digestLive D ds sent receiver := by
      unfold treeSimCheckResult at accepted
      split_ifs at accepted with hi hl ha hc
      exact ⟨by simpa only [inbox, anyAbort] using ha,
        by simpa only [TreeSimCheckAccept, inbox] using hc⟩
    let inner : C.Party → C.Term → HashOutput := fun i T =>
      (cache (.history ((st i).history T))).getD 0
    let outer : C.Party → C.Term → HashOutput := fun i T =>
      (cache (.digest (vector 256 (salts i T)) (inner i T))).getD 0
    have answers : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T →
        TreeSimHashAnswer log (.history ((st i).history T)) (inner i T) ∧
        TreeSimHashAnswer log (.digest (vector 256 (salts i T)) (inner i T)) (outer i T) ∧
        (ds i)[C.terms.idxOf T]? = some (outer i T) := by
      intro i hi T held
      obtain ⟨h, d, hh, hd, idx⟩ := recorded i hi (all i hi) T held
      have hin : inner i T = h := by
        dsimp only [inner]
        rw [coherent (.history ((st i).history T)) h trivial hh]
        rfl
      have hout : outer i T = d := by
        dsimp only [outer]
        rw [hin, coherent (.digest (vector 256 (salts i T)) h) d trivial hd]
        rfl
      rw [hout, hin]
      exact ⟨hh, hd, idx⟩
    have noCollision : ¬ TreeSimHashCollision log := by
      rintro ⟨q, t, h, hq, ht, ne, aq, ah⟩
      exact good ⟨q, t, h, treeSimHash_domain_budget q hq,
        treeSimHash_domain_budget t ht, ne, aq, ah⟩
    obtain ⟨S, size, points⟩ := treeSimHash_digest_points D log noCollision
      (fun i T => vector 256 (salts i T)) (fun i => (st i).history)
      inner outer ds answers sent receiver passed
    exact ⟨S, size, covers S (fun i hi _ => points i hi)⟩

/-- The actual sampled-salt phase has the surviving cover or stops with the terminal cover. -/
theorem treeHashBudget_saltedDigest_phase_cover
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (live : C.Party → Bool) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i) (st : C.Party → RunState C)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Option (Unit × RunState C))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality 1 state (fun i =>
        if live i then (treeStagesSaltedDigest K (ctx i)).run (st i) else failure))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ S : Finset (Query C), TreeHashBudgetRegionCover S s.2 r.2.2 ∧
      (S.card ≤ 2 * termCount C ∨
        ((∀ i, r.1.2 i = none) ∧ S.card ≤ (C.n + 1) * termCount C)) := by
  have start : startSteps worldRoles D (fun i =>
      if live i then (treeStagesSaltedDigest K (ctx i)).run (st i) else failure) =
      treeSimResumeAll
        (fun i (_ : Unit) => (treeStagesSaltedDigest K (ctx i)).run (st i) >>= pure)
        (fun i => if i ∈ D.1 then none else if live i then some () else none) := by
    unfold startSteps treeSimResumeAll
    rw [free_sequenceFin]
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp [hi, treeSimResume, free_pure]
    · by_cases hl : live i = true <;>
        simp [hi, hl, treeSimResume, bind_pure, advance_pure, worldRoles, free_pure]
  simp only [executePhase, start, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨before, hbefore, tail⟩ := run
  have future := (treeSimLoggedWorld_prefix prims D _ before.2 r tail).subset.trans final
  obtain ⟨ds, waiting, terminal, surviving⟩ := treeHashBudget_saltedDigest_covers K prims D
    log cache coherent good live ctx self st (fun _ => pure) s before hbefore future
  rw [waiting] at tail
  simp only [executeRounds] at tail
  split_ifs at tail with done
  · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at tail
    subst r
    obtain ⟨S, size, cover⟩ := terminal
    refine ⟨S, cover, Or.inr ⟨?_, size⟩⟩
    intro i
    simp only [treeSimCheckWaiting]
    split_ifs <;> rfl
  · rw [treeSim_check_round_factor] at tail
    simp only [treeHashBudget_resume_pure (E := E) (fun i (_ : Unit) => ((), nextLabel (st i)))] at tail
    simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at tail
    obtain ⟨adv, hadv, rfl⟩ := tail
    by_cases accepted : ∃ i, treeSimCheckResult K D live (.digests ds) adv.1.2 i = some ()
    · obtain ⟨i, hi⟩ := accepted
      obtain ⟨S, size, cover⟩ := surviving adv.1.2 i hi
      exact ⟨S, cover.trans (treeHashBudget_adversary_cover prims D S _ before.2 adv hadv).region,
        Or.inl size⟩
    · obtain ⟨S, size, cover⟩ := terminal
      refine ⟨S, cover.trans (treeHashBudget_adversary_cover prims D S _ before.2 adv hadv).region,
        Or.inr ⟨?_, size⟩⟩
      intro i
      have reject : treeSimCheckResult K D live (.digests ds) adv.1.2 i = none := by
        cases h : treeSimCheckResult K D live (.digests ds) adv.1.2 i with
        | none => rfl
        | some u => cases u; exact (accepted ⟨i, h⟩).elim
      simp only [Step.output, reject, Option.map_none]

end SaltedCover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_sequence_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_sequence_witness

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_prssDraw_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_prssDraw_zero

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_saltedDigest_partial_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_saltedDigest_partial_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_saltedDigest_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_saltedDigest_covers

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_saltedDigest_phase_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_saltedDigest_phase_cover

-- A75_SALTED_COVER_END

-- A75_SUFFIX_ASSEMBLY_BEGIN
section SuffixAssembly
open TreeSimHashCount

/-- The actual salted digest, scalar check and replicated opening retain a
single cover through any region-free continuation, including rejected prefixes. -/
theorem treeHashBudget_salted_check_open_cover {α : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (live : C.Party → Bool) (tag label : ℕ) (st : C.Party → RunState C)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (polynomial : C.Party → E → ℕ → E)
    (count : ℕ) (v : C.Party → Shares C Bit)
    (zero : ∀ i T, i ∉ C.holders T → ∀ g, v i T g = 0)
    (k : C.Party → Unit × RunState C → (ℕ → Bit) → PartyM C E RealSpec α)
    (tailZero : ∀ i saved out, PartyBudget Region (k i saved out) 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (1+(2+(fuel+1))) state (fun i =>
        (if live i then (treeStagesSaltedDigest K (ctx i)).run (st i) else failure) >>= fun digest =>
        (treeLockstepCheckSuffix K (ctx i) (polynomial i)).run digest.2 >>= fun saved =>
        openRep K (ctx i) (v i) count >>= k i saved))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ S : Finset (Query C), S.card ≤ (C.n+2)*termCount C+2 ∧
      TreeHashBudgetRegionCover S s.2 r.2.2 := by
  obtain ⟨pref, first, fields, tail⟩ := treeHashBudget_saltedDigest_cut K prims D A
    (2+(fuel+1)) state ctx live tag label st counters
    (fun i digest => (treeLockstepCheckSuffix K (ctx i) (polynomial i)).run digest.2 >>= fun saved =>
      openRep K (ctx i) (v i) count >>= k i saved) s r run
  have future := (treeSimLoggedWorld_prefix prims D _ pref.2 r tail).subset.trans final
  obtain ⟨S, cover, cases⟩ := treeHashBudget_saltedDigest_phase_cover K prims D A state
    log cache coherent good live ctx (fun i _ => self i) st s pref first future
  rcases cases with cheap | ⟨stopped, size⟩
  · let active := fun i => (pref.1.2 i).isSome
    let reached := fun i => ((pref.1.2 i).getD ((), nextLabel (st i))).2
    have nextCounters : ∀ i, i ∉ D.1 → (reached i).tag = tag ∧ (reached i).label = label+1 := by
      intro i hi
      cases h : pref.1.2 i with
      | none =>
        simpa only [reached, h, Option.getD_none, nextLabel] using
          And.intro (counters i hi).1 (congrArg (·+1) (counters i hi).2)
      | some p =>
        have hp := fields i hi p.1 p.2 h
        simpa only [reached, h, Option.getD_some] using And.intro hp.2 hp.1
    have rewrite : (fun i => (pref.1.2 i).elim failure
        (fun digest => (treeLockstepCheckSuffix K (ctx i) (polynomial i)).run digest.2 >>= fun saved =>
          openRep K (ctx i) (v i) count >>= k i saved)) =
        (fun i => (if active i then (treeLockstepCheckSuffix K (ctx i) (polynomial i)).run
          (reached i) else failure) >>= fun saved => openRep K (ctx i) (v i) count >>= k i saved) := by
      funext i
      cases h : pref.1.2 i <;> simp [h, active, reached]
    rw [rewrite] at tail
    obtain ⟨T, sizeT, coverT⟩ := treeHashBudget_check_open_cover K prims D A fuel pref.1.1
      ctx self active tag (label+1) reached nextCounters polynomial count v zero k tailZero pref.2 r tail
    refine ⟨S ∪ T, ?_, cover.union_trans coverT⟩
    have := Finset.card_union_le S T
    rw [Nat.add_mul] 
    omega
  · have stoppedCover : TreeHashBudgetRegionCover S pref.2.2 r.2.2 := by
      apply treeHashBudget_phase_cover prims D S A _ pref.1.1 _ _ pref.2 r tail
      intro i hi
      simp only [stopped i, Option.elim_none]
      exact isQueryBoundP_pure _ _ _
    refine ⟨S, ?_, cover.trans stoppedCover⟩
    rw [Nat.add_mul] at size ⊢
    omega

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_salted_check_open_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_salted_check_open_cover

end SuffixAssembly

-- A75_SUFFIX_ASSEMBLY_END

-- A75_CHECK_ASSEMBLY_BEGIN
section FullCheckCover
open TreeSimHashCount

/-- The literal check and replicated opening fit the per-batch allowance,
including empty checks, selective aborts and a region-free next-batch prefix. -/
theorem treeHashBudget_check_open_full_cover {α : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (tuples : C.Party → List (Tuple C)) (count : ℕ)
    (counts : ∀ i, i ∉ D.1 → ((tuples i).map (·.count)).sum = count)
    (live : C.Party → Bool) (tag label : ℕ) (st : C.Party → RunState C)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (outputCount : ℕ) (v : C.Party → Shares C Bit)
    (zero : ∀ i T, i ∉ C.holders T → ∀ g, v i T g = 0)
    (k : C.Party → Unit × RunState C → (ℕ → Bit) → PartyM C E RealSpec α)
    (tailZero : ∀ i saved out, PartyBudget Region (k i saved out) 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (checkLabels count+1+fuel) state (fun i =>
        (if live i then (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i)
        else failure) >>= fun saved => openRep K (ctx i) (v i) outputCount >>= k i saved))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ S : Finset (Query C), S.card ≤ (C.n+3)*termCount C+halvings count+2 ∧
      TreeHashBudgetRegionCover S s.2 r.2.2 := by
  by_cases empty : count = 0
  · have form := treeHashBudget_phase_congr D A (checkLabels count+1+fuel) state
      (fun i => (if live i then
        (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) else failure) >>=
        fun saved => openRep K (ctx i) (v i) outputCount >>= k i saved)
      (fun i => if live i then openRep K (ctx i) (v i) outputCount >>= k i ((), st i) else failure)
      (by
        intro i hi
        rw [check_zero_run K (ctx i) _ _ ((counts i hi).trans empty)]
        split_ifs
        · simp only [pure_bind]
        · rfl)
    rw [form] at run
    simp only [checkLabels, empty, if_true, Nat.zero_add, Nat.add_comm 1 fuel] at run
    obtain ⟨S, size, cover⟩ := treeHashBudget_open_phase_gated K prims D A fuel state ctx self
      live outputCount v zero (fun i => k i ((), st i)) (fun i => tailZero i ((), st i)) s r run
    refine ⟨S, ?_, cover⟩
    rw [Nat.add_mul]
    omega
  · let n := 2*sliceBits+2*(halvings count-sliceBits)+1
    let p := fun i => if i ∈ D.1 then failure else if live i then
      (treeLockstepCheckBeforeSalt K (ctx i) (tuples i)).run (st i) else failure
    let cont := fun i (out : (E → ℕ → E) × RunState C) =>
      (treeStagesSaltedDigest K (ctx i)).run out.2 >>= fun digest =>
      (treeLockstepCheckSuffix K (ctx i) out.1).run digest.2 >>= fun saved =>
      openRep K (ctx i) (v i) outputCount >>= k i saved
    have fuelEq : checkLabels count+1+fuel = n+1+(1+(2+(fuel+1))) := by
      have lower : sliceBits ≤ halvings count := by unfold halvings; omega
      simp only [checkLabels, if_neg empty]
      dsimp only [n]
      omega
    rw [fuelEq] at run
    have form := treeHashBudget_phase_congr D A (n+1+(1+(2+(fuel+1)))) state
      (fun i => (if live i then
        (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) else failure) >>=
        fun saved => openRep K (ctx i) (v i) outputCount >>= k i saved)
      (fun i => p i >>= cont i) (by
        intro i hi
        dsimp only [p, cont]
        rw [if_neg hi]
        by_cases active : live i = true
        · rw [if_pos active, if_pos active, treeLockstep_check_eq K _ _
            (fun h => empty ((counts i hi).symm.trans h)), treeLockstep_checkPrefix_eq]
          simp only [StateT.run_bind, bind_assoc, pure_bind]
        · simp only [if_neg active]
          rfl)
    rw [form] at run
    have timed (i) : TreeSimCheckTimed (n+1) (p i).run := by
      dsimp only [p]
      split_ifs with corrupt active
      · exact .abort _
      · simpa only [counts i corrupt, n, Nat.add_assoc] using
          treeLockstep_checkBeforeSalt_timed K (ctx i) (tuples i) (st i)
      · exact .abort _
    obtain ⟨pref, first, tail⟩ := treeHashBudget_phase_cut prims D A n
      (1+(2+(fuel+1))) state p cont timed s r run
    have firstForm := treeHashBudget_phase_congr D A (n+1) state p
      (fun i => if live i then (treeLockstepCheckBeforeSalt K (ctx i) (tuples i)).run (st i)
        else failure) (fun i hi => by simp only [p, if_neg hi])
    rw [firstForm] at first
    obtain ⟨S, size, cover⟩ := treeHashBudget_beforeSalt_cover K prims D A ctx self tuples count counts
      0 state live tag label st counters s pref (by simpa only [n, Nat.add_assoc, Nat.add_zero] using first)
    have fields : ∀ i, i ∉ D.1 → ∀ value last, pref.1.2 i = some (value,last) →
        last.label = label+(n+2) ∧ last.tag = tag := by
      have replay := treeLockstep_logged_run_allowed prims D _ s pref first
      intro i hi value last accepted
      have party := treeSimCheck_phase_replay D A noFunctionality _ (n+1) state _ pref.1 replay
        i hi (value,last) accepted
      have raw := party.choose_spec.1.mem_support
      by_cases active : live i = true
      · simp only [if_pos active] at raw
        have fields := treeHashBudget_checkBeforeSalt_fields K (ctx i) (tuples i) (st i) value last raw
        simpa only [counts i hi, (counters i hi).1, (counters i hi).2, n, Nat.add_assoc] using fields
      · simp only [if_neg active, OptionT.run_failure, mem_support_pure_iff, reduceCtorEq] at raw
    let active := fun i => (pref.1.2 i).isSome
    let fallback := fun i => ({ st i with label := label+(n+2), tag := tag } : RunState C)
    let value := fun i => (pref.1.2 i).getD ((fun _ _ => 0), fallback i)
    have nextCounters : ∀ i, i ∉ D.1 → (value i).2.tag = tag ∧ (value i).2.label = label+(n+2) := by
      intro i hi
      cases h : pref.1.2 i with
      | none => simp only [value, h, Option.getD_none, fallback, and_self]
      | some out =>
        have hp := fields i hi out.1 out.2 h
        simpa only [value, h, Option.getD_some] using And.intro hp.2 hp.1
    have tailForm : (fun i => (pref.1.2 i).elim failure (cont i)) =
        (fun i => (if active i then (treeStagesSaltedDigest K (ctx i)).run (value i).2 else failure) >>=
          fun digest => (treeLockstepCheckSuffix K (ctx i) (value i).1).run digest.2 >>= fun saved =>
          openRep K (ctx i) (v i) outputCount >>= k i saved) := by
      funext i
      cases h : pref.1.2 i <;> simp [cont, h, active, value]
    rw [tailForm] at tail
    obtain ⟨T, sizeT, coverT⟩ := treeHashBudget_salted_check_open_cover K prims D A fuel pref.1.1
      log cache coherent good ctx self active tag (label+(n+2)) (fun i => (value i).2)
      nextCounters (fun i => (value i).1) outputCount v zero k tailZero pref.2 r tail final
    refine ⟨S ∪ T, ?_, cover.union_trans coverT⟩
    have union := Finset.card_union_le S T
    have terms := treeSimHash_parties_le_terms (C := C)
    have positive := C.one_le_t
    unfold Committee.n at terms
    rw [Nat.add_mul] at sizeT ⊢
    omega

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_check_open_full_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_check_open_full_cover

end FullCheckCover

-- A75_CHECK_ASSEMBLY_END

-- A75_SURVIVING_CHECK_BEGIN
section SurvivingCheck
open TreeSimHashCount

/-- A surviving scalar check excludes the terminal digest branch, so the
actual digest and scalar-test log needs only two copies per term and one coin. -/
theorem treeHashBudget_salted_check_surviving_cover (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (live : C.Party → Bool) (tag label : ℕ) (st : C.Party → RunState C)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (polynomial : C.Party → E → ℕ → E)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option (Unit × RunState C))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (1+2) state (fun i =>
        (if live i then (treeStagesSaltedDigest K (ctx i)).run (st i) else failure) >>= fun digest =>
        (treeLockstepCheckSuffix K (ctx i) (polynomial i)).run digest.2))).run s))
    (final : r.2.2 ⊆ log) (accepted : ∃ i out, r.1.2 i = some out) :
    ∃ S : Finset (Query C), S.card ≤ 2*termCount C+1 ∧
      TreeHashBudgetRegionCover S s.2 r.2.2 := by
  obtain ⟨pref, first, fields, tail⟩ := treeHashBudget_saltedDigest_cut K prims D A
    2 state ctx live tag label st counters
    (fun i digest => (treeLockstepCheckSuffix K (ctx i) (polynomial i)).run digest.2) s r run
  have future := (treeSimLoggedWorld_prefix prims D _ pref.2 r tail).subset.trans final
  obtain ⟨S, cover, cases⟩ := treeHashBudget_saltedDigest_phase_cover K prims D A state
    log cache coherent good live ctx (fun i _ => self i) st s pref first future
  rcases cases with cheap | ⟨stopped, _⟩
  · let active := fun i => (pref.1.2 i).isSome
    let reached := fun i => ((pref.1.2 i).getD ((), nextLabel (st i))).2
    have nextCounters : ∀ i, i ∉ D.1 → (reached i).tag = tag ∧ (reached i).label = label+1 := by
      intro i hi
      cases h : pref.1.2 i with
      | none =>
        simpa only [reached, h, Option.getD_none, nextLabel] using
          And.intro (counters i hi).1 (congrArg (·+1) (counters i hi).2)
      | some p =>
        have hp := fields i hi p.1 p.2 h
        simpa only [reached, h, Option.getD_some] using And.intro hp.2 hp.1
    have form : (fun i => (pref.1.2 i).elim failure
        (fun digest => (treeLockstepCheckSuffix K (ctx i) (polynomial i)).run digest.2)) =
        (fun i => if active i then (treeLockstepCheckSuffix K (ctx i) (polynomial i)).run
          (reached i) else failure) := by
      funext i
      cases h : pref.1.2 i <;> simp [h, active, reached]
    rw [form] at tail
    obtain ⟨T, sizeT, coverT⟩ := treeHashBudget_checkSuffix_cover K prims D A 1 pref.1.1
      ctx self active tag (label+1) reached nextCounters polynomial pref.2 r tail
    refine ⟨S ∪ T, ?_, cover.union_trans coverT⟩
    have := Finset.card_union_le S T
    omega
  · simp only [stopped, Option.elim_none] at tail
    obtain ⟨i, out, accepted⟩ := accepted
    by_cases corrupt : i ∈ D.1
    · have absent := treeStages_phase_corrupt (treeSimLoggedWorld prims D) D A 2 pref.1.1
        (fun _ => failure) pref.2 r (by simpa only [simulateQ_executePhase] using tail) i corrupt
      simp only [absent, reduceCtorEq] at accepted
    · have allowed := treeLockstep_logged_run_allowed prims D _ pref.2 r tail
      have raw := (treeSimCheck_phase_replay D A noFunctionality _ 2 pref.1.1
        (fun _ => failure) r.1 allowed i corrupt out accepted).choose_spec.1.mem_support
      simp only [OptionT.run_failure, mem_support_pure_iff, reduceCtorEq] at raw

/-- A surviving actual check uses its common challenge counters and the
surviving digest allowance, before the replicated output opening begins. -/
theorem treeHashBudget_check_surviving_cover (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (tuples : C.Party → List (Tuple C)) (count : ℕ)
    (counts : ∀ i, i ∉ D.1 → ((tuples i).map (·.count)).sum = count)
    (live : C.Party → Bool) (tag label : ℕ) (st : C.Party → RunState C)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option (Unit × RunState C))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (checkLabels count) state (fun i =>
        (if live i then (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i)
        else failure)))).run s))
    (final : r.2.2 ⊆ log)
    (accepted : ∃ i out, r.1.2 i = some out) :
    ∃ S : Finset (Query C), S.card ≤ 2*termCount C+halvings count+2 ∧
      TreeHashBudgetRegionCover S s.2 r.2.2 := by
  by_cases empty : count = 0
  · refine ⟨∅, by simp, ?_⟩
    apply treeHashBudget_phase_cover prims D ∅ A _ state _ _ s r run
    intro i hi
    by_cases active : live i = true
    · simp only [if_pos active, check_zero_run K (ctx i) _ _ ((counts i hi).trans empty)]
      exact isQueryBoundP_pure _ _ _
    · simp only [if_neg active]
      exact isQueryBoundP_pure _ _ _
  · let n := 2*sliceBits+2*(halvings count-sliceBits)+1
    let p := fun i => if i ∈ D.1 then failure else if live i then
      (treeLockstepCheckBeforeSalt K (ctx i) (tuples i)).run (st i) else failure
    let cont := fun i (out : (E → ℕ → E) × RunState C) =>
      (treeStagesSaltedDigest K (ctx i)).run out.2 >>= fun digest =>
      (treeLockstepCheckSuffix K (ctx i) out.1).run digest.2
    have fuelEq : checkLabels count = n+1+(1+2) := by
      have lower : sliceBits ≤ halvings count := by unfold halvings; omega
      simp only [checkLabels, if_neg empty]
      dsimp only [n]
      omega
    rw [fuelEq] at run
    have form := treeHashBudget_phase_congr D A (n+1+(1+2)) state
      (fun i => (if live i then
        (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) else failure))
      (fun i => p i >>= cont i) (by
        intro i hi
        dsimp only [p, cont]
        rw [if_neg hi]
        by_cases active : live i = true
        · rw [if_pos active, if_pos active, treeLockstep_check_eq K _ _
            (fun h => empty ((counts i hi).symm.trans h)), treeLockstep_checkPrefix_eq]
          simp only [StateT.run_bind, bind_assoc, pure_bind]
        · simp only [if_neg active]
          rfl)
    rw [form] at run
    have timed (i) : TreeSimCheckTimed (n+1) (p i).run := by
      dsimp only [p]
      split_ifs with corrupt active
      · exact .abort _
      · simpa only [counts i corrupt, n, Nat.add_assoc] using
          treeLockstep_checkBeforeSalt_timed K (ctx i) (tuples i) (st i)
      · exact .abort _
    obtain ⟨pref, first, tail⟩ := treeHashBudget_phase_cut prims D A n
      (1+2) state p cont timed s r run
    have firstForm := treeHashBudget_phase_congr D A (n+1) state p
      (fun i => if live i then (treeLockstepCheckBeforeSalt K (ctx i) (tuples i)).run (st i)
        else failure) (fun i hi => by simp only [p, if_neg hi])
    rw [firstForm] at first
    obtain ⟨S, size, cover⟩ := treeHashBudget_beforeSalt_cover K prims D A ctx self tuples count counts
      0 state live tag label st counters s pref (by simpa only [n, Nat.add_assoc, Nat.add_zero] using first)
    have fields : ∀ i, i ∉ D.1 → ∀ value last, pref.1.2 i = some (value,last) →
        last.label = label+(n+2) ∧ last.tag = tag := by
      have replay := treeLockstep_logged_run_allowed prims D _ s pref first
      intro i hi value last accepted
      have party := treeSimCheck_phase_replay D A noFunctionality _ (n+1) state _ pref.1 replay
        i hi (value,last) accepted
      have raw := party.choose_spec.1.mem_support
      by_cases active : live i = true
      · simp only [if_pos active] at raw
        have fields := treeHashBudget_checkBeforeSalt_fields K (ctx i) (tuples i) (st i) value last raw
        simpa only [counts i hi, (counters i hi).1, (counters i hi).2, n, Nat.add_assoc] using fields
      · simp only [if_neg active, OptionT.run_failure, mem_support_pure_iff, reduceCtorEq] at raw
    let active := fun i => (pref.1.2 i).isSome
    let fallback := fun i => ({ st i with label := label+(n+2), tag := tag } : RunState C)
    let value := fun i => (pref.1.2 i).getD ((fun _ _ => 0), fallback i)
    have nextCounters : ∀ i, i ∉ D.1 → (value i).2.tag = tag ∧ (value i).2.label = label+(n+2) := by
      intro i hi
      cases h : pref.1.2 i with
      | none => simp only [value, h, Option.getD_none, fallback, and_self]
      | some out =>
        have hp := fields i hi out.1 out.2 h
        simpa only [value, h, Option.getD_some] using And.intro hp.2 hp.1
    have tailForm : (fun i => (pref.1.2 i).elim failure (cont i)) =
        (fun i => (if active i then (treeStagesSaltedDigest K (ctx i)).run (value i).2 else failure) >>=
          fun digest => (treeLockstepCheckSuffix K (ctx i) (value i).1).run digest.2) := by
      funext i
      cases h : pref.1.2 i <;> simp [cont, h, active, value]
    rw [tailForm] at tail
    obtain ⟨T, sizeT, coverT⟩ := treeHashBudget_salted_check_surviving_cover K prims D A pref.1.1
      log cache coherent good ctx self active tag (label+(n+2)) (fun i => (value i).2)
      nextCounters (fun i => (value i).1) pref.2 r tail final accepted
    refine ⟨S ∪ T, ?_, cover.union_trans coverT⟩
    have union := Finset.card_union_le S T
    omega

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_salted_check_surviving_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_salted_check_surviving_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_check_surviving_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_check_surviving_cover

end SurvivingCheck
-- A75_SURVIVING_CHECK_END


-- A75_BATCH_HEADS_BEGIN
section BatchHeads
open TreeSimHashCount

/-- An audited batch reaches a region-free exchange before any later continuation. -/
theorem treeHashBudget_audit_head_zero {α : Type} (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (k : ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α) :
    IsQueryBoundP (advance
      (((treeSimCheckBatchAudit K circuits settings ctx jobs).run.run initial) >>= k).run) Region 0 := by
  rw [treeSimCheckBatchAudit_run_prefix, bind_assoc]
  exact treeHashBudget_head_zero_bind _ _ _
    (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs initial)
    (treeHashBudget_batchPrefix_zero K circuits settings ctx jobs initial)

/-- A nonempty list of audited batches shields its local head from its arbitrary tail. -/
theorem treeHashBudget_batches_head_zero {α : Type} (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (batches : List (List Job)) (initial : ℕ × ℕ)
    (k : ((List (Option (List (List Bit))) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (empty : batches = [] → ∀ out, IsQueryBoundP (advance (k out).run) Region 0) :
    IsQueryBoundP (advance
      (((batches.mapM (treeSimCheckBatchAudit K circuits settings ctx)).run.run initial) >>= k).run)
      Region 0 := by
  cases batches with
  | nil =>
    simpa only [List.mapM_nil, WriterT.run_pure, StateT.run_pure, pure_bind] using
      empty rfl (([], ∅), initial)
  | cons jobs batches =>
    have factor : (((jobs :: batches).mapM
        (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx)).run.run initial) =
        (do
          let a ← (treeSimCheckBatchAudit K circuits settings ctx jobs).run.run initial
          let b ← ((batches.mapM (treeSimCheckBatchAudit K circuits settings ctx)).run.run a.2)
          pure ((a.1.1 :: b.1.1, a.1.2 ++ b.1.2), b.2)) := by
      simp [List.mapM_cons, WriterT.run_bind, StateT.run_bind]
    rw [factor, bind_assoc]
    exact treeHashBudget_audit_head_zero K circuits settings ctx jobs initial _

/-- Chunked execution has a region-free first head whenever its empty-case tail does. -/
theorem treeHashBudget_batched_head_zero {α : Type} (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (k : ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (empty : chunks settings.batchSize jobs = [] →
      ∀ out, IsQueryBoundP (advance (k out).run) Region 0) :
    IsQueryBoundP (advance
      (((batched settings.batchSize (treeSimCheckBatchAudit K circuits settings ctx) jobs).run.run initial)
        >>= k).run) Region 0 := by
  have factor : (batched settings.batchSize
      (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx) jobs).run.run initial =
      (do
        let a ← ((chunks settings.batchSize jobs).mapM
          (treeSimCheckBatchAudit K circuits settings ctx)).run.run initial
        pure ((a.1.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [], a.1.2), a.2)) := by
    simp [batched]
  rw [factor, bind_assoc]
  apply treeHashBudget_batches_head_zero K circuits settings ctx _ initial
  intro h out
  simpa only [pure_bind] using empty h _

/-- A zero-round snapshot of an audited batch retains no budget-region query. -/
theorem treeHashBudget_audit_snapshot_zero {α : Type} (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (k : ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α) :
    PartyBudget Region (treeLateSnapshot 0
      (((treeSimCheckBatchAudit K circuits settings ctx jobs).run.run initial) >>= k)) 0 :=
  treeHashBudget_snapshot_zero _ (treeHashBudget_audit_head_zero K circuits settings ctx jobs initial k)

/-- A zero-round snapshot preserves the empty-list condition on the pending tail. -/
theorem treeHashBudget_batches_snapshot_zero {α : Type} (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (batches : List (List Job)) (initial : ℕ × ℕ)
    (k : ((List (Option (List (List Bit))) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (empty : batches = [] → ∀ out, IsQueryBoundP (advance (k out).run) Region 0) :
    PartyBudget Region (treeLateSnapshot 0
      (((batches.mapM (treeSimCheckBatchAudit K circuits settings ctx)).run.run initial) >>= k)) 0 :=
  treeHashBudget_snapshot_zero _
    (treeHashBudget_batches_head_zero K circuits settings ctx batches initial k empty)

/-- A zero-round snapshot of chunked execution captures only its region-free local head. -/
theorem treeHashBudget_batched_snapshot_zero {α : Type} (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (k : ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (empty : chunks settings.batchSize jobs = [] →
      ∀ out, IsQueryBoundP (advance (k out).run) Region 0) :
    PartyBudget Region (treeLateSnapshot 0
      (((batched settings.batchSize (treeSimCheckBatchAudit K circuits settings ctx) jobs).run.run initial)
        >>= k)) 0 :=
  treeHashBudget_snapshot_zero _
    (treeHashBudget_batched_head_zero K circuits settings ctx jobs initial k empty)

end BatchHeads

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_audit_head_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_audit_head_zero

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batches_head_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batches_head_zero

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batched_head_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batched_head_zero

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_audit_snapshot_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_audit_snapshot_zero

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batches_snapshot_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batches_snapshot_zero

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batched_snapshot_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batched_snapshot_zero

-- A75_BATCH_HEADS_END

-- A75_OPEN_HEAD_COVER_BEGIN
/-- One finite set covers both copy-hash passes as local programs for the
same sent matrix. The bound survives arbitrary later prelude composition. -/
theorem treeHashBudget_open_head_cover (D : C.Coalition)
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (zero : ∀ i T, i ∉ C.holders T → ∀ g, v i T g = 0)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E) :
    ∃ S : Finset (Query C), S.card ≤ C.n * termCount C + 1 ∧
      IsQueryBoundP (treeLockstepOpenHashes D live count v)
        (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0 ∧
      ∀ i, IsQueryBoundP
        (liftComp (treeSimOpenHead K D live count v ds sent i) (LocalSpec C))
        (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0 := by
  obtain ⟨S, size, points⟩ := treeSimHash_open_points K count v
    (treeSimOpenInbox K D live count v ds sent) zero
  refine ⟨S, size, ?_, ?_⟩
  · unfold treeLockstepOpenHashes
    apply isQueryBoundP_sequenceFin
    intro i
    split_ifs
    · exact hashes_freeHashIn_zero _ _ _ (fun T _ outside => outside.2 (points i T).1)
    · exact isQueryBoundP_pure _ _ _
  · intro i
    unfold treeSimOpenHead
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · dsimp only
      split_ifs
      · exact isQueryBoundP_pure _ _ _
      · simp only [liftComp_bind, liftComp_pure]
        exact isQueryBoundP_bind (n := 0) (m := 0)
          (hashes_freeHashIn_zero (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S) _ _
            (fun T _ outside => outside.2 (points i T).2))
          (fun _ _ => isQueryBoundP_pure _ _ _)
    · exact isQueryBoundP_pure _ _ _

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_open_head_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_open_head_cover

-- A75_OPEN_HEAD_COVER_END

-- A75_OPEN_RESERVATION_BEGIN
/-- The actual opening cut reserves its pending local hashes in the same
finite set that covers the first copy pass and the adversarial reply. -/
theorem treeHashBudget_open_pending_reservation {α : Type} (prims : Primitives)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (count : ℕ) (v : C.Party → Shares C Bit)
    (zero : ∀ i T, i ∉ C.holders T → ∀ g, v i T g = 0)
    (k : C.Party → PartyM C E RealSpec α) (s : TreeSimState C)
    (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (fuel + 1) state
        (fun i => openRep K (ctx i) (v i) count >>= fun _ => k i))).run s)) :
    ∃ (S : Finset (Query C)) (state' : A.State) (cache : TreeSimState C)
      (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      S.card ≤ C.n * termCount C + 1 ∧
      TreeHashBudgetRegionCover S s.2 cache.2 ∧
      (∀ i, IsQueryBoundP (gate i)
        (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0) ∧
      (∃ ds sent, gate = treeLockstepOpenGate K D (fun _ => true) count v ds sent) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state'
          (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ => k i))).run cache) := by
  rw [treeLockstep_open_phase_preludes K D A fuel state ctx self] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨⟨ds, s₁⟩, hashes, ⟨b, s₂⟩, adv, tail⟩ := run
  obtain ⟨S, size, first, heads⟩ := treeHashBudget_open_head_cover K D
    (fun _ => true) count v zero ds b.2
  refine ⟨S, b.1, s₂, treeLockstepOpenGate K D (fun _ => true) count v ds b.2,
    size, ?_, ?_, ⟨ds, b.2, rfl⟩, tail⟩
  · exact (treeHashBudget_free_region_cover prims D S _ first s (ds, s₁) hashes).trans
      (treeHashBudget_adversary_cover prims D S _ s₁ (b, s₂) adv).region
  · intro i
    unfold treeLockstepOpenGate
    exact (isQueryBoundP_map_iff _ _ _).mpr (heads i)

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_open_pending_reservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_open_pending_reservation

-- A75_OPEN_RESERVATION_END

-- A75_CHECK_RESERVATION_BEGIN
/-- A surviving check and the following opening cut reserve the pending
copy hashes while retaining the actual check results and suffix execution. -/
theorem treeHashBudget_check_pending_reservation {α : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (log : TreeSimLog C) (hash : HashCache C) (coherent : TreeSimHashCoherent hash log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (tuples : C.Party → List (Tuple C)) (st : C.Party → RunState C) (count : ℕ)
    (counts : ∀ i, ((tuples i).map (·.count)).sum = count)
    (tag label : ℕ)
    (counters : ∀ i, i ∉ D.1 → (st i).tag = tag ∧ (st i).label = label)
    (width : ℕ) (v : C.Party → Shares C Bit)
    (zero : ∀ i T, i ∉ C.holders T → ∀ g, v i T g = 0)
    (k : C.Party → (Unit × RunState C) → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (checkLabels count + (fuel + 1)) state
        (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) >>= fun checked =>
          openRep K (ctx i) (v i) width >>= fun _ => k i checked))).run s))
    (final : r.2.2 ⊆ log) (accepted : ∃ i value, r.1.2 i = some value) :
    ∃ (checked : C.Party → Unit × RunState C) (state' : A.State) (cache : TreeSimState C)
      (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)) (S : Finset (Query C)),
      (∀ i, i ∉ D.1 → some (checked i) ∈ support
        ((check K (ctx i) (realCheckGadgets (G := RealSpec) K (ctx i)) (tuples i)).run (st i)).run) ∧
      S.card ≤ (C.n+2)*termCount C+halvings count+3 ∧
      TreeHashBudgetRegionCover S s.2 cache.2 ∧
      (∀ i, IsQueryBoundP (gate i)
        (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0) ∧
      (∃ ds sent, gate = treeLockstepOpenGate K D (fun _ => true) width v ds sent) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state'
          (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ => k i (checked i)))).run cache) := by
  by_cases empty : count = 0
  · have form (i) : (check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) =
        pure ((), st i) := by
      simp only [check, counts i, empty]
      rfl
    simp only [form, pure_bind, empty, checkLabels, if_true, Nat.zero_add] at run
    obtain ⟨S, state', cache, gate, size, cover, bound, shape, tail⟩ :=
      treeHashBudget_open_pending_reservation K prims D A fuel state ctx self width v zero
        (fun i => k i ((), st i)) s r run
    refine ⟨(fun i => ((), st i)), state', cache, gate, S, ?_, ?_, cover, bound, shape, tail⟩
    · intro i hi
      simp only [form, OptionT.run_pure, mem_support_pure_iff]
    · rw [Nat.add_mul]
      omega
  · have labels : checkLabels count = 2 * halvings count + 5 := by
      simp only [checkLabels, if_neg empty]
    let n := 2 * halvings count + 4
    let p := fun i => (check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i)
    let next := fun i out => openRep K (ctx i) (v i) width >>= fun _ => k i out
    have timed (i) : TreeSimCheckTimed (n + 1) (p i).run := by
      have h := treeLockstep_check_timed K (ctx i) (tuples i) (st i) (by rw [counts i]; exact empty)
      have hs : sliceBits ≤ halvings count := by unfold halvings; omega
      convert h using 1
      rw [counts i]
      dsimp only [n]
      omega
    have runcut : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (n + 1 + (fuel + 1)) state
          (fun i => p i >>= next i))).run s) := by
      simpa only [p, next, n, labels] using run
    obtain ⟨pref, checked, hpref, selected, hrest⟩ := treeLockstep_timed_boundary prims D A n
      (fuel + 1) state p next ((), ⟨fun _ => [], 0, 0⟩) timed
      (fun i out => (treeSimCheck_openRep_exchange K (ctx i) _ _).bind _) s r runcut accepted
    have firstAccepted : ∃ i out, pref.1.2 i = some out := by
      obtain ⟨i, out, hout⟩ := accepted
      have honest : i ∉ D.1 := by
        intro corrupt
        have absent := treeStages_phase_corrupt (treeSimLoggedWorld prims D) D A
          (checkLabels count+(fuel+1)) state _ s r
          (by simpa only [simulateQ_executePhase] using run) i corrupt
        simp only [absent, reduceCtorEq] at hout
      exact ⟨i, checked i, selected i honest⟩
    have future := (treeSimLoggedWorld_prefix prims D _ pref.2 r hrest).subset.trans final
    obtain ⟨S, sizeS, coverS⟩ := treeHashBudget_check_surviving_cover K prims D A state
      log hash coherent good ctx self tuples count (fun i _ => counts i) (fun _ => true)
      tag label st counters s pref (by simpa only [Bool.true_eq, if_true, n, labels, p] using hpref)
      future firstAccepted
    obtain ⟨T, state', cache, gate, sizeT, coverT, bound, shape, tail⟩ :=
      treeHashBudget_open_pending_reservation K prims D A fuel pref.1.1 ctx self width v zero
        (fun i => k i (checked i)) pref.2 r hrest
    refine ⟨checked, state', cache, gate, S ∪ T, ?_, ?_, coverS.union_trans coverT, ?_, shape, tail⟩
    · intro i hi
      have allowed := treeLockstep_logged_run_allowed prims D _ s pref hpref
      exact (treeSimCheck_phase_replay D A noFunctionality _ _ state _ pref.1 allowed i hi
        (checked i) (selected i hi)).choose_spec.1.mem_support
    · have union := Finset.card_union_le S T
      rw [Nat.add_mul]
      omega
    · intro i
      apply IsQueryBoundP.of_imp _ (bound i)
      rintro t ⟨q, ⟨domain, outside⟩, eq⟩
      exact ⟨q, ⟨domain, fun h => outside (Finset.mem_union_right S h)⟩, eq⟩

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_check_pending_reservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_check_pending_reservation

-- A75_CHECK_RESERVATION_END


-- A75_BATCH_GATE_SHAPE_BEGIN
section BatchGateShape
variable (prims : Primitives) (circuits : Circuits) (settings : Settings)

-- These operational cuts retain the opening-head witnesses discarded by
-- TreeLockstepOpenedFinal's open_pending_cut/check_pending_cut/batch_next.

/-- The actual pending opening prelude has the fixed copy-query program
for the same digest rows and adversarial sent matrix. -/
theorem treeHashBudget_open_pending_shape {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (count : ℕ) (v : C.Party → Shares C Bit)
    (k : C.Party → PartyM C E RealSpec α) (s : TreeSimState C)
    (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (fuel + 1) state
        (fun i => openRep K (ctx i) (v i) count >>= fun _ => k i))).run s)) :
    ∃ (state' : A.State) (cache : TreeSimState C)
      (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      (∃ ds sent, gate = treeLockstepOpenGate K D (fun _ => true) count v ds sent) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state'
          (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ => k i))).run cache) := by
  rw [treeLockstep_open_phase_preludes K D A fuel state ctx self] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨⟨ds, s₁⟩, _, ⟨b, s₂⟩, _, tail⟩ := run
  exact ⟨b.1, s₂, treeLockstepOpenGate K D (fun _ => true) count v ds b.2,
    ⟨ds, b.2, rfl⟩, tail⟩

/-- The post-check cut retains the exact pending opening program. -/
theorem treeHashBudget_check_pending_shape {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (tuples : C.Party → List (Tuple C)) (st : C.Party → RunState C) (count : ℕ)
    (counts : ∀ i, ((tuples i).map (·.count)).sum = count)
    (width : ℕ) (v : C.Party → Shares C Bit)
    (k : C.Party → (Unit × RunState C) → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (checkLabels count + (fuel + 1)) state
        (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) >>= fun checked =>
          openRep K (ctx i) (v i) width >>= fun _ => k i checked))).run s))
    (accepted : ∃ i value, r.1.2 i = some value) :
    ∃ (checked : C.Party → Unit × RunState C) (state' : A.State) (cache : TreeSimState C)
      (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      (∀ i, i ∉ D.1 → some (checked i) ∈ support
        ((check K (ctx i) (realCheckGadgets (G := RealSpec) K (ctx i)) (tuples i)).run (st i)).run) ∧
      (∃ ds sent, gate = treeLockstepOpenGate K D (fun _ => true) width v ds sent) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state'
          (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ => k i (checked i)))).run cache) := by
  by_cases zero : count = 0
  · have empty (i) : (check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) =
        pure ((), st i) := by
      simp only [check, counts i, zero]
      rfl
    simp only [empty, pure_bind, zero, checkLabels, if_true, Nat.zero_add] at run
    obtain ⟨state', cache, gate, shape, tail⟩ := treeHashBudget_open_pending_shape K prims D A fuel state ctx self
      width v (fun i => k i ((), st i)) s r run
    refine ⟨(fun i => ((), st i)), state', cache, gate, ?_, shape, tail⟩
    intro i hi
    simp only [empty, OptionT.run_pure, mem_support_pure_iff]
  · have labels : checkLabels count = 2 * halvings count + 5 := by
      simp only [checkLabels, if_neg zero]
    let n := 2 * halvings count + 4
    let p := fun i => (check (G := RealSpec) K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i)
    let next := fun i out => openRep K (ctx i) (v i) width >>= fun _ => k i out
    have timed (i) : TreeSimCheckTimed (n + 1) (p i).run := by
      have h := treeLockstep_check_timed K (ctx i) (tuples i) (st i) (by rw [counts i]; exact zero)
      have hs : sliceBits ≤ halvings count := by unfold halvings; omega
      convert h using 1
      rw [counts i]
      dsimp only [n]
      omega
    have runcut : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (n + 1 + (fuel + 1)) state
          (fun i => p i >>= next i))).run s) := by
      simpa only [p, next, n, labels] using run
    obtain ⟨pref, checked, hpref, selected, hrest⟩ := treeLockstep_timed_boundary prims D A n
      (fuel + 1) state p next ((), ⟨fun _ => [], 0, 0⟩) timed
      (fun i out => (treeSimCheck_openRep_exchange K (ctx i) _ _).bind _) s r runcut accepted
    obtain ⟨state', cache, gate, shape, tail⟩ := treeHashBudget_open_pending_shape K prims D A fuel pref.1.1 ctx self
      width v (fun i => k i (checked i)) pref.2 r hrest
    refine ⟨checked, state', cache, gate, ?_, shape, tail⟩
    intro i hi
    have allowed := treeLockstep_logged_run_allowed prims D _ s pref hpref
    exact (treeSimCheck_phase_replay D A noFunctionality _ _ state _ pref.1 allowed i hi
      (checked i) (selected i hi)).choose_spec.1.mem_support

/-- The next actual batch phase carries its preceding opening heads,
with the original query inputs and adversarial reply still identified. -/
theorem treeHashBudget_batch_next_shape {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (jobs : List Job) (initial : ℕ × ℕ)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (batchRounds circuits settings.mode parameter jobs + fuel)
        state (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) (accepted : ∃ i value, r.1.2 i = some value) :
    ∃ (value : List (List Bit)) (records : C.Party → TreeSimCheckBatchRecord C)
      (state' : A.State) (cache : TreeSimState C)
      (gate' : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      (∀ i, (records i).outputs = value ∧ (records i).jobs = jobs ∧ (records i).start = initial) ∧
      (∃ width v ds sent, gate' = treeLockstepOpenGate K D (fun _ => true) width v ds sent) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state'
          (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ =>
            k i ((some value, [records i]),
              (initial.1 + batchLabels circuits parameter jobs, initial.2 + 1))))).run cache) := by
  let js := jobs.map (circuits parameter ·.kind)
  let rest := checkLabels (tupleCount js) + (fuel + 1)
  have rounds : batchRounds circuits settings.mode parameter jobs + fuel =
      depth js * settings.mode.rounds + 1 + rest := by
    unfold batchRounds batchCount rest js
    omega
  rw [rounds] at run
  obtain ⟨value, canonical⟩ := treeLockstep_batch_canonical prims K circuits settings D A fuel state
    ctx self parameter parameters keys gate jobs initial k s r run good accepted
  let fixed := fun i out => k i (treeLockstepCanonicalBatchResult value out)
  let p := fun i => treeLockstepLocalPrelude (E := E) (gate i) >>= fun _ =>
    treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial
  let next := fun i data => treeSimCheckBatchFinish K circuits (ctx i) jobs initial data >>= fixed i
  have timed (i) : TreeSimCheckTimed (depth js * settings.mode.rounds + 1) (p i).run := by
    apply treeLockstep_localPrelude_timed
    simpa only [parameters i] using treeSimCheckBatchPrefix_timed K circuits settings (ctx i) jobs initial
  have cutrun : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (depth js * settings.mode.rounds + 1 + rest)
        state (fun i => p i >>= next i))).run s) := by
    simpa only [p, next, fixed, treeSimCheckBatchAudit_run_prefix, bind_assoc] using canonical
  obtain ⟨pref, raw, hpref, selectedRaw, suffixRaw⟩ := treeLockstep_timed_boundary prims D A
    (depth js * settings.mode.rounds) rest state p next
    ([], (0, []), ⟨fun _ => [], initial.1, initial.2⟩) timed
    (fun i data => by
      unfold next treeSimCheckBatchFinish
      rw [bind_assoc]
      exact (treeSimCheckAfterVerify_exchange K (ctx i) _ data.2).bind _) s r cutrun accepted
  let honest := fun i : C.Party => if i ∉ D.1 then i else refHolder D K.publicTerm
  have hh (i) : honest i ∉ D.1 := by
    by_cases hi : i ∉ D.1
    · simpa only [honest, if_pos hi] using hi
    · simpa only [honest, if_neg hi] using (refHolder_spec D K.publicTerm).2
  have keep (i) (hi : i ∉ D.1) : honest i = i := if_pos hi
  let data := fun i => raw (honest i)
  have suffix : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality rest pref.1.1
        (fun i => next i (data i)))).run pref.2) := by
    rw [treeHashBudget_phase_congr D A rest pref.1.1 _ (fun i => next i (raw i))
      (fun i hi => by rw [show data i = raw i from congrArg raw (keep i hi)])]
    exact suffixRaw
  have metadata (i) : (data i).2.2.label = initial.1 + depth js + 1 ∧
      (data i).2.1.2.map (·.count) =
        (List.range (depth js)).map (fun l => (gatesAt js l).length) ++ [(outputsOf js).length] := by
    have allowed := treeLockstep_logged_run_allowed prims D _ s pref hpref
    have party := treeSimCheck_phase_replay D A noFunctionality _ _ state _ pref.1 allowed
      (honest i) (hh i) (raw (honest i)) (selectedRaw _ (hh i))
    obtain ⟨_, _, party⟩ := party.option_bind_inv _ _ _
    have h := treeSimCheckBatchPrefix_state K circuits settings (ctx (honest i)) jobs initial
      (raw (honest i)) party.choose_spec.1.mem_support
    simpa only [parameters] using And.intro h.2.1 h.2.2.2.1
  have counts (i) : (((data i).2.1.2).map (·.count)).sum = tupleCount js := by
    rw [(metadata i).2, List.sum_append, List.sum_cons, List.sum_nil,
      Nat.add_zero, tupleCount_eq]
  have labels (i) : (data i).2.2.label = initial.1 + depth js + 1 := by
    exact (metadata i).1
  simp only [next, treeLockstep_batchFinish_check] at suffix
  unfold treeLockstepBatchCheckCont at suffix
  simp only [fixed, treeLockstepCanonicalBatchResult, List.map_cons, List.map_nil, parameters] at suffix
  let record := fun i (checked : Unit × RunState C) =>
    (⟨ctx i, jobs, initial, (data i).1, (data i).2.1.2, (data i).2.2, value, checked.2⟩ :
      TreeSimCheckBatchRecord C)
  let cont := fun i (checked : Unit × RunState C) =>
    k i ((some value, [record i checked]), (checked.2.label, initial.2 + 1))
  obtain ⟨checked, state', cache, gate', checkRuns, shape, tail⟩ := treeHashBudget_check_pending_shape K prims D A fuel
    pref.1.1 ctx self (fun i => (data i).2.1.2) (fun i => (data i).2.2) (tupleCount js) counts
    (outputsOf js).length (fun i => (data i).2.1.1) cont pref.2 r suffix accepted
  have finalLabel (i) (hi : i ∉ D.1) : (checked i).2.label = initial.1 + batchLabels circuits parameter jobs := by
    have h := lockstepLabels_check K (ctx i) (data i).2.1.2 (data i).2.2 (checked i).1 (checked i).2
      (checkRuns i hi)
    rw [counts i, labels i] at h
    unfold batchLabels batchCount
    dsimp only [js] at h
    omega
  refine ⟨value, (fun i => record i (checked i)), state', cache, gate', (fun i => ⟨rfl, rfl, rfl⟩), ?_, ?_⟩
  · obtain ⟨ds, sent, he⟩ := shape
    exact ⟨(outputsOf js).length, (fun i => (data i).2.1.1), ds, sent, he⟩
  · rw [treeHashBudget_phase_congr D A fuel state' _
      (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ => cont i (checked i)) ?_]
    · exact tail
    · intro i hi
      simp only [cont, finalLabel i hi]

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_open_pending_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_open_pending_shape

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_check_pending_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_check_pending_shape

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batch_next_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batch_next_shape

end BatchGateShape

-- A75_BATCH_GATE_SHAPE_END

-- A75_PUBLIC_HEADS_BEGIN
section PublicHeads
open TreeSimHashCount
attribute [local irreducible] merkleNode merklePath Concrete.layerRoot
  treeLockstepPublicChoiceCode signJobs

/-- The final top-tree computation uses only public tweakable hashes. -/
theorem treeHashBudget_topFinish_zero (parameter : PublicParameter)
    (outputs : List (List Bit)) (records : List (TreeSimCheckBatchRecord C)) :
    PartyBudget Region (treeLockstepTopFinish (E := E) parameter outputs records) 0 := by
  unfold treeLockstepTopFinish
  apply PartyBudget.bind (n := 0) (m := 0)
  · exact oracle_bound (tweakable_zero _)
  · intro root
    exact PartyBudget.pure _

/-- The final bottom-tree verification uses only public tweakable hashes,
including its abort branches. -/
theorem treeHashBudget_bottomFinish_zero (parameter : PublicParameter) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) (root : Digest)
    (randomness : Randomness) (values : Option (List (List Bit)))
    (records : List (TreeSimCheckBatchRecord C)) :
    PartyBudget Region
      (treeLockstepBottomFinish (E := E) parameter top b outputs root randomness values records) 0 := by
  cases values with
  | none => exact PartyBudget.of_all PartyBound.failure
  | some values =>
    unfold treeLockstepBottomFinish
    exact (oracle_bound (tweakable_zero _)).bind (m := 0) (fun _ =>
      (oracle_bound (tweakable_zero _)).bind (m := 0) (fun _ => by
        split_ifs
        · exact PartyBudget.of_all PartyBound.failure
        · exact PartyBudget.pure _))

/-- The first-run continuation has a region-free local head, up to the
next batched exchange or the terminal public verification. -/
theorem treeHashBudget_firstRest_head_zero (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (top : TopTree) (tree : Tree)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) :
    IsQueryBoundP (advance (treeLockstepFirstRest K circuits settings ctx top tree a).run)
      Region 0 := by
  obtain ⟨⟨values, records⟩, initial⟩ := a
  cases values with
  | none => exact advance_zero _ _ (PartyBudget.of_all PartyBound.failure)
  | some outputs =>
    cases tree with
    | top => exact advance_zero _ _ (treeHashBudget_topFinish_zero _ _ _)
    | bottom b =>
      unfold treeLockstepFirstRest
      rw [advance_oracleStep_bind]
      apply isQueryBoundP_bind (n := 0) (m := 0) (ro_bound (tweakable_zero _))
      intro chosen _
      cases chosen with
      | none => exact advance_zero _ _ (PartyBudget.of_all PartyBound.failure)
      | some chosen =>
        apply treeHashBudget_batched_head_zero K circuits settings ctx (signJobs b chosen.2.2) initial
        intro _ out
        exact advance_zero _ _ (treeHashBudget_bottomFinish_zero _ _ _ _ _ _ _ _)

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_topFinish_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_topFinish_zero

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_bottomFinish_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_bottomFinish_zero

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_firstRest_head_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_firstRest_head_zero

end PublicHeads
-- A75_PUBLIC_HEADS_END

-- A75_PUBLIC_RESERVATION_BEGIN
section PublicReservation
open TreeSimHashCount

/-- A pending local gate followed by public hashes keeps its budget-domain
reservation; all the public queries lie outside that domain. -/
theorem treeHashBudget_publicPrelude_zero {β : Type} (S : Finset (Query C))
    (gate : OracleComp (LocalSpec C) (Option Unit))
    (bound : IsQueryBoundP gate
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0)
    (p : OracleComp HashSpec β) :
    IsQueryBoundP (treeLockstepPublicPrelude gate p)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0 := by
  unfold treeLockstepPublicPrelude
  apply isQueryBoundP_bind (n := 0) (m := 0) bound
  intro out _
  cases out with
  | none => exact isQueryBoundP_pure _ _ _
  | some u =>
    rw [isQueryBoundP_map_iff]
    apply IsQueryBoundP.of_imp _ (ro_bound (tweakable_zero p))
    rintro t ⟨q, ⟨domain, _⟩, eq⟩
    exact treeHashBudget_free_region t ⟨q, domain, eq⟩

-- These equalities retain the explicit gate used by the private public-phase
-- factorization in TreeLockstepOpenedFinal.
private theorem treeHashBudget_publicPrelude_program {α β : Type}
    (gate : OracleComp (LocalSpec C) (Option Unit)) (p : OracleComp HashSpec β)
    (k : β → PartyM C E RealSpec α) :
    treeLockstepLocalOption (treeLockstepPublicPrelude gate p) >>= k =
      (treeLockstepLocalPrelude gate >>= fun _ => oracleStep (tweakable p) >>= k) := by
  apply OptionT.ext
  unfold treeLockstepLocalOption treeLockstepPublicPrelude treeLockstepLocalPrelude
  simp only [localStep, OptionT.run_bind, OptionT.lift, OptionT.run_mk, liftComp_bind,
    bind_assoc, pure_bind, Option.elimM]
  apply bind_congr
  intro out
  cases out with
  | none => simp [liftComp_pure]
  | some u => simp [oracleStep, localStep, liftComp_map, OptionT.lift, pure_bind]

private theorem treeHashBudget_localOption_ignore {α β : Type}
    (p : OracleComp (LocalSpec C) (Option β)) (k : PartyM C E RealSpec α) :
    (treeLockstepLocalOption p >>= fun _ => k) =
      (treeLockstepLocalPrelude (Option.map (fun _ => ()) <$> p) >>= fun _ => k) := by
  apply OptionT.ext
  unfold treeLockstepLocalOption treeLockstepLocalPrelude
  simp only [localStep, OptionT.run_bind, OptionT.lift, OptionT.run_mk,
    liftComp_map, bind_map_left, bind_assoc, pure_bind, Option.elimM]
  apply bind_congr
  intro out
  cases out <;> rfl

/-- Canonicalizing the public choice retains its exact query order and the
same finite reservation for the pending local gates. -/
theorem treeHashBudget_public_phase_gate {α β : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (hash : Query C → HashOutput) (S : Finset (Query C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (bound : ∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0)
    (p : OracleComp HashSpec β) (k : C.Party → β → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ => oracleStep (tweakable p) >>= k i))).run s))
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ r.2.2 →
      TreeSimCheckWorldHashes hash t u) :
    ∃ gate' : C.Party → OracleComp (LocalSpec C) (Option Unit),
      (∀ i, i ∉ D.1 → IsQueryBoundP (gate' i)
        (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state
          (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ =>
            k i (ThresholdLeanXmssSecurity.D prims hash (tweakable p))))).run s) := by
  have changed := treeLockstep_public_phase_canonical prims D A fuel state hash gate p k s r run rows
  simp_rw [← treeHashBudget_publicPrelude_program, treeHashBudget_localOption_ignore] at changed
  refine ⟨_, ?_, changed⟩
  intro i hi
  rw [isQueryBoundP_map_iff]
  exact treeHashBudget_publicPrelude_zero S (gate i) (bound i hi) p

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_publicPrelude_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_publicPrelude_zero

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_public_phase_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_public_phase_gate

end PublicReservation
-- A75_PUBLIC_RESERVATION_END


section BatchCover

/-- Missing checkpoint rows can be completed without changing any present
honest row or the common tuple count and counters. -/
theorem treeHashBudget_checkpoint_complete (D : C.Coalition) (count label tag : ℕ)
    (rows : C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))
    (fields : ∀ i, i ∉ D.1 → ∀ out, rows i = some out →
      (∀ T, i ∉ C.holders T → ∀ g, out.2.1.1 T g = 0) ∧
      out.2.2.label = label ∧ out.2.2.tag = tag ∧
      (out.2.1.2.map (·.count)).sum = count) :
    ∃ data : C.Party → List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C,
      (∀ i, i ∉ D.1 → ∀ out, rows i = some out → data i = out) ∧
      (∀ i, i ∉ D.1 → (data i).2.2.label = label ∧ (data i).2.2.tag = tag) ∧
      (∀ i, i ∉ D.1 → ((data i).2.1.2.map (·.count)).sum = count) ∧
      (∀ i T, i ∉ C.holders T → ∀ g, (data i).2.1.1 T g = 0) := by
  let fallback : List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C :=
    ([], (0, [⟨0,0,0,count,.peer⟩]), ⟨fun _ => [], label, tag⟩)
  let data := fun i => if i ∈ D.1 then fallback else (rows i).getD fallback
  refine ⟨data, ?_, ?_, ?_, ?_⟩
  · intro i hi out accepted
    simp only [data, if_neg hi, accepted, Option.getD_some]
  · intro i hi
    cases accepted : rows i with
    | none => simp only [data, if_neg hi, accepted, Option.getD_none, fallback]; trivial
    | some out =>
      simp only [data, if_neg hi, accepted, Option.getD_some]
      exact ⟨(fields i hi out accepted).2.1, (fields i hi out accepted).2.2.1⟩
  · intro i hi
    cases accepted : rows i with
    | none => simp [data, hi, accepted, fallback]
    | some out =>
      simp only [data, if_neg hi, accepted, Option.getD_some]
      exact (fields i hi out accepted).2.2.2
  · intro i T held g
    by_cases hi : i ∈ D.1
    · simp [data, hi, fallback]
    · cases accepted : rows i with
      | none => simp [data, hi, accepted, fallback]
      | some out =>
        simp only [data, if_neg hi, accepted, Option.getD_some]
        exact (fields i hi out accepted).1 T held g

/-- The actual batch prefix after any local prelude has common checkpoint
metadata on its present rows; aborting rows remain absent. -/
theorem treeHashBudget_checkpoint_prelude_data (prims : Primitives) (circuits : Circuits)
    (settings : Settings) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) (ctx : C.Party → Context C)
    (self : ∀ i, (ctx i).self = i) (parameter : PublicParameter)
    (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (jobs : List Job) (initial : ℕ × ℕ) (prelude : C.Party → PartyM C E RealSpec Unit)
    (s : TreeSimState C)
    (pref : (A.State × (C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (run : pref ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state (fun i => prelude i >>= fun _ =>
        treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial))).run s)) :
    ∃ data : C.Party → List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C,
      (∀ i, i ∉ D.1 → ∀ out, pref.1.2 i = some out → data i = out) ∧
      (∀ i, i ∉ D.1 → (data i).2.2.label =
        initial.1+depth (jobs.map (circuits parameter ·.kind))+1 ∧ (data i).2.2.tag = initial.2) ∧
      (∀ i, i ∉ D.1 → ((data i).2.1.2.map (·.count)).sum =
        tupleCount (jobs.map (circuits parameter ·.kind))) ∧
      (∀ i T, i ∉ C.holders T → ∀ g, (data i).2.1.1 T g = 0) := by
  apply treeHashBudget_checkpoint_complete
  intro i hi out accepted
  simpa only [self i] using treeHashBudget_batchPrefix_actual K prims circuits settings D A
    fuel state ctx parameter parameters jobs initial prelude s pref run i hi out accepted

/-- An actual partially active batch checkpoint admits total data arrays
with common counters and tuple counts. Missing rows use zero saved copies;
every present honest row remains its original checkpoint. -/
theorem treeHashBudget_checkpoint_data (prims : Primitives) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, i ∉ D.1 → (ctx i).keys.parameter = parameter)
    (jobs : List Job) (initial : ℕ × ℕ) (live : C.Party → Bool) (s : TreeSimState C)
    (pref : (A.State × (C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (run : pref ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state (fun i =>
        if live i then treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial else failure))).run s)) :
    ∃ data : C.Party → List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C,
      (∀ i, i ∉ D.1 → ∀ out, pref.1.2 i = some out → data i = out) ∧
      (∀ i, i ∉ D.1 → (data i).2.2.label =
        initial.1+depth (jobs.map (circuits parameter ·.kind))+1 ∧ (data i).2.2.tag = initial.2) ∧
      (∀ i, i ∉ D.1 → ((data i).2.1.2.map (·.count)).sum =
        tupleCount (jobs.map (circuits parameter ·.kind))) ∧
      (∀ i T, i ∉ C.holders T → ∀ g, (data i).2.1.1 T g = 0) := by
  let count := tupleCount (jobs.map (circuits parameter ·.kind))
  let fallback : List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C :=
    ([], (0, [⟨0,0,0,count,.peer⟩]),
      ⟨fun _ => [], initial.1+depth (jobs.map (circuits parameter ·.kind))+1, initial.2⟩)
  let data := fun i => if i ∈ D.1 then fallback else (pref.1.2 i).getD fallback
  have replay := treeLockstep_logged_run_allowed prims D _ s pref run
  have rows (i) (hi : i ∉ D.1) (out) (accepted : pref.1.2 i = some out) :
      (∀ T, i ∉ C.holders T → ∀ g, out.2.1.1 T g = 0) ∧
      out.2.2.label = initial.1+depth (jobs.map (circuits parameter ·.kind))+1 ∧
      out.2.2.tag = initial.2 ∧ (out.2.1.2.map (·.count)).sum = count := by
    have party := treeSimCheck_phase_replay D A noFunctionality _ fuel state _ pref.1 replay i hi out accepted
    have raw := party.choose_spec.1.mem_support
    by_cases active : live i = true
    · simp only [if_pos active] at raw
      simpa only [parameters i hi, self i, count] using
        treeHashBudget_batchPrefix_fields K circuits settings (ctx i) jobs initial out raw
    · simp only [if_neg active, OptionT.run_failure, mem_support_pure_iff, reduceCtorEq] at raw
  refine ⟨data, ?_, ?_, ?_, ?_⟩
  · intro i hi out accepted
    simp only [data, if_neg hi, accepted, Option.getD_some]
  · intro i hi
    cases accepted : pref.1.2 i with
    | none => simp only [data, if_neg hi, accepted, Option.getD_none, fallback]; trivial
    | some out =>
      simp only [data, if_neg hi, accepted, Option.getD_some]
      have h := rows i hi out accepted
      exact ⟨h.2.1,h.2.2.1⟩
  · intro i hi
    cases accepted : pref.1.2 i with
    | none => simp [data, hi, accepted, fallback, count]
    | some out =>
      simp only [data, if_neg hi, accepted, Option.getD_some]
      exact (rows i hi out accepted).2.2.2
  · intro i T held g
    by_cases hi : i ∈ D.1
    · simp [data, hi, fallback]
    · cases accepted : pref.1.2 i with
      | none => simp [data, hi, accepted, fallback]
      | some out =>
        simp only [data, if_neg hi, accepted, Option.getD_some]
        exact (rows i hi out accepted).1 T held g

/-- One actual audited batch, followed by region-free work, fits the paper's
per-batch hash allowance even when no checkpoint or final record survives. -/
theorem treeHashBudget_batchAudit_cover {α : Type} (prims : Primitives)
    (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (jobs : List Job) (initial : ℕ × ℕ) (live : C.Party → Bool)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (tailZero : ∀ i out, TreeSimHashCount.PartyBudget TreeSimHashCount.Region (k i out) 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (batchRounds circuits settings.mode parameter jobs+fuel)
        state (fun i => (if live i then
          (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial else failure) >>= k i))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ S : Finset (Query C), S.card ≤ (C.n+3)*termCount C+
        halvings (batchCount circuits parameter jobs)+2 ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  let js := jobs.map (circuits parameter ·.kind)
  let prefixFuel := depth js * settings.mode.rounds
  let restFuel := checkLabels (batchCount circuits parameter jobs)+1+fuel
  let prep := fun i => if live i then treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial else failure
  let cont := fun i data => treeSimCheckBatchFinish K circuits (ctx i) jobs initial data >>= k i
  have form : (fun i => (if live i then
      (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial else failure) >>= k i) =
      fun i => prep i >>= cont i := by
    funext i
    by_cases active : live i = true
    · simp only [prep, cont, if_pos active, treeSimCheckBatchAudit_run_prefix, bind_assoc]
    · simp only [prep, if_neg active]; rfl
  rw [form, show batchRounds circuits settings.mode parameter jobs+fuel = prefixFuel+1+restFuel by
    simp only [batchRounds, prefixFuel, restFuel, js]; omega] at run
  have timed (i) : TreeSimCheckTimed (prefixFuel+1) (prep i).run := by
    dsimp only [prep]
    split_ifs
    · simpa only [prefixFuel, js, parameters i] using
        treeSimCheckBatchPrefix_timed K circuits settings (ctx i) jobs initial
    · exact .abort _
  obtain ⟨pref, first, tail⟩ := treeHashBudget_phase_cut prims D A prefixFuel restFuel state prep cont timed s r run
  obtain ⟨data, keep, counters, counts, nonholder⟩ := treeHashBudget_checkpoint_data K prims circuits settings
    D A (prefixFuel+1) state ctx self parameter (fun i _ => parameters i) jobs initial live s pref first
  let active := fun i => (pref.1.2 i).isSome
  let next := fun i (saved : Unit × RunState C) (opened : ℕ → Bit) =>
    let value := assemble js opened
    k i ((some value, [⟨ctx i,jobs,initial,(data i).1,(data i).2.1.2,(data i).2.2,value,saved.2⟩]),
      (saved.2.label,initial.2+1))
  have rewrite := treeHashBudget_phase_congr D A restFuel pref.1.1
    (fun i => (pref.1.2 i).elim failure (cont i))
    (fun i => (if active i then
      (check K (ctx i) (realCheckGadgets K (ctx i)) (data i).2.1.2).run (data i).2.2 else failure) >>=
      fun saved => openRep K (ctx i) (data i).2.1.1 (outputsOf js).length >>= next i saved)
    (by
      intro i hi
      cases accepted : pref.1.2 i with
      | none => simp only [active, accepted, Option.isSome_none, Bool.false_eq_true, if_false, Option.elim_none]; rfl
      | some out =>
        rw [keep i hi out accepted]
        simp only [active, accepted, Option.isSome_some, if_true, Option.elim_some, cont,
          treeLockstep_batchFinish_check, next, js, keep i hi out accepted]
        apply bind_congr
        intro saved
        simp only [treeLockstepBatchCheckCont, parameters i])
  rw [rewrite] at tail
  obtain ⟨S, size, cover⟩ := treeHashBudget_check_open_full_cover K prims D A fuel pref.1.1
    log cache coherent good ctx self (fun i => (data i).2.1.2) (batchCount circuits parameter jobs)
    counts active initial.2 (initial.1+depth js+1) (fun i => (data i).2.2)
    (fun i hi => ⟨(counters i hi).2,(counters i hi).1⟩)
    (outputsOf js).length (fun i => (data i).2.1.1) nonholder next
    (fun i saved opened => tailZero i _) pref.2 r tail final
  refine ⟨S, size, ?_⟩
  have firstCover : TreeHashBudgetRegionCover S s.2 pref.2.2 := by
    apply treeHashBudget_zero_phase_cover prims D A (prefixFuel+1) state prep _ S s pref first
    intro i _
    dsimp only [prep]
    split_ifs
    · exact treeHashBudget_batchPrefix_zero K circuits settings (ctx i) jobs initial
    · exact isQueryBoundP_pure _ _ _
  exact firstCover.trans cover

/-- The same per-batch bound applies to an actual retained scheduler cut.
The next local head is captured, and its pending continuation is preserved. -/
theorem treeHashBudget_batch_cut_cover {α : Type} (prims : Primitives)
    (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (jobs : List Job) (initial : ℕ × ℕ) (live : C.Party → Bool)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (headZero : ∀ i out, IsQueryBoundP (advance (k i out).run) TreeSimHashCount.Region 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Step C E RealSpec α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (fun i => (if live i then
        (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial else failure) >>= k i) >>=
        fun steps => executeSteps worldRoles D A noFunctionality
          (batchRounds circuits settings.mode parameter jobs) state steps)).run s))
    (final : r.2.2 ⊆ log) :
    ∃ S : Finset (Query C), S.card ≤ (C.n+3)*termCount C+
        halvings (batchCount circuits parameter jobs)+2 ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  let n := batchRounds circuits settings.mode parameter jobs
  let p := fun i => (if live i then
    (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial else failure) >>= k i
  let captured := ((r.1.1, fun i => treeLateSnapshotOut (r.1.2 i)),r.2)
  have cap : captured ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality n state (fun i => treeLateSnapshot n (p i)))).run s) := by
    rw [treeLateSnapshot_phase, simulateQ_map, StateT.run_map, support_map]
    exact ⟨r,run,rfl⟩
  have programs : (fun i => treeLateSnapshot n (p i)) = fun i =>
      (if live i then (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial else failure) >>=
        fun out => treeLateSnapshot 0 (k i out) := by
    funext i
    by_cases active : live i = true
    · simp only [p, if_pos active]
      obtain ⟨within, exactRun⟩ := treeLateSnapshot_batch_timing K circuits settings (ctx i) jobs initial
      have h := treeLateSnapshot_bind within 0 (by simpa only [Nat.zero_add] using exactRun) 0 (k i)
      simpa only [n, parameters i, Nat.add_zero] using h
    · simp only [p, if_neg active]
      change treeLateSnapshot n (failure : PartyM C E RealSpec α) = failure
      apply OptionT.ext
      exact treeLateSnapshot_pure n none
  rw [programs] at cap
  have full := treeHashBudget_batchAudit_cover K prims circuits settings D A 0 state log cache coherent
    good ctx self parameter parameters jobs initial live (fun i out => treeLateSnapshot 0 (k i out))
    (fun i out => treeHashBudget_snapshot_zero _ (headZero i out)) s captured
    (by simpa only [Nat.add_zero] using cap) final
  exact full

/-- Local aborting preludes preserve every zero query bound. -/
theorem treeHashBudget_prelude_bound {P : (LocalSpec C).Domain → Prop}
    (gate : OracleComp (LocalSpec C) (Option Unit)) (bound : IsQueryBoundP gate P 0) :
    TreeSimHashCount.PartyBudget P (treeLockstepLocalPrelude (E := E) gate) 0 := by
  apply TreeSimHashCount.PartyBudget.bind (m := 0) (TreeSimHashCount.localStep_bound bound)
  intro out
  cases out <;> exact isQueryBoundP_pure _ _ _

/-- A region-free party program avoids the budget domain outside any cover. -/
theorem treeHashBudget_party_region_outside {α : Type} (S : Finset (Query C))
    (p : PartyM C E RealSpec α)
    (zero : TreeSimHashCount.PartyBudget TreeSimHashCount.Region p 0) :
    TreeSimHashCount.PartyBudget
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) p 0 := by
  apply IsQueryBoundP.of_imp _ zero
  rintro ((t | _) | _) ht
  · obtain ⟨q, domain, eq⟩ := ht
    exact treeHashBudget_free_region t ⟨q, domain.1, eq⟩
  · exact ht.elim
  · exact ht.elim

/-- A preceding reserved local head adds only inputs already in its cover.
The new allowance is the same for a complete or an aborted audited batch. -/
theorem treeHashBudget_batch_prelude_cover {α : Type} (prims : Primitives)
    (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (jobs : List Job) (initial : ℕ × ℕ) (S₀ : Finset (Query C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (gateBound : ∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S₀)) 0)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (tailZero : ∀ i out, TreeSimHashCount.PartyBudget TreeSimHashCount.Region (k i out) 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (batchRounds circuits settings.mode parameter jobs+fuel)
        state (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ S : Finset (Query C), S.card ≤ (C.n+3)*termCount C+
        halvings (batchCount circuits parameter jobs)+2 ∧ TreeHashBudgetRegionCover (S₀ ∪ S) s.2 r.2.2 := by
  let js := jobs.map (circuits parameter ·.kind)
  let prefixFuel := depth js * settings.mode.rounds
  let restFuel := checkLabels (batchCount circuits parameter jobs)+1+fuel
  let prep := fun i => treeLockstepLocalPrelude (E := E) (gate i) >>= fun _ =>
    treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial
  let cont := fun i data => treeSimCheckBatchFinish K circuits (ctx i) jobs initial data >>= k i
  have form : (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
      (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i) =
      fun i => prep i >>= cont i := by
    funext i
    simp only [prep, cont, treeSimCheckBatchAudit_run_prefix, bind_assoc]
  rw [form, show batchRounds circuits settings.mode parameter jobs+fuel = prefixFuel+1+restFuel by
    simp only [batchRounds, prefixFuel, restFuel, js]; omega] at run
  have timed (i) : TreeSimCheckTimed (prefixFuel+1) (prep i).run := by
    apply treeLockstep_localPrelude_timed
    simpa only [prefixFuel, js, parameters i] using
      treeSimCheckBatchPrefix_timed K circuits settings (ctx i) jobs initial
  obtain ⟨pref, first, tail⟩ := treeHashBudget_phase_cut prims D A prefixFuel restFuel state prep cont timed s r run
  obtain ⟨data, keep, counters, counts, nonholder⟩ := treeHashBudget_checkpoint_prelude_data K prims circuits settings
    D A (prefixFuel+1) state ctx self parameter parameters jobs initial
    (fun i => treeLockstepLocalPrelude (gate i)) s pref first
  let active := fun i => (pref.1.2 i).isSome
  let next := fun i (saved : Unit × RunState C) (opened : ℕ → Bit) =>
    let value := assemble js opened
    k i ((some value, [⟨ctx i,jobs,initial,(data i).1,(data i).2.1.2,(data i).2.2,value,saved.2⟩]),
      (saved.2.label,initial.2+1))
  have rewrite := treeHashBudget_phase_congr D A restFuel pref.1.1
    (fun i => (pref.1.2 i).elim failure (cont i))
    (fun i => (if active i then
      (check K (ctx i) (realCheckGadgets K (ctx i)) (data i).2.1.2).run (data i).2.2 else failure) >>=
      fun saved => openRep K (ctx i) (data i).2.1.1 (outputsOf js).length >>= next i saved)
    (by
      intro i hi
      cases accepted : pref.1.2 i with
      | none => simp only [active, accepted, Option.isSome_none, Bool.false_eq_true, if_false, Option.elim_none]; rfl
      | some out =>
        rw [keep i hi out accepted]
        simp only [active, accepted, Option.isSome_some, if_true, Option.elim_some, cont,
          treeLockstep_batchFinish_check, next, js, keep i hi out accepted]
        apply bind_congr
        intro saved
        simp only [treeLockstepBatchCheckCont, parameters i])
  rw [rewrite] at tail
  obtain ⟨S, size, cover⟩ := treeHashBudget_check_open_full_cover K prims D A fuel pref.1.1
    log cache coherent good ctx self (fun i => (data i).2.1.2) (batchCount circuits parameter jobs)
    counts active initial.2 (initial.1+depth js+1) (fun i => (data i).2.2)
    (fun i hi => ⟨(counters i hi).2,(counters i hi).1⟩)
    (outputsOf js).length (fun i => (data i).2.1.1) nonholder next
    (fun i saved opened => tailZero i _) pref.2 r tail final
  refine ⟨S, size, ?_⟩
  have firstCover : TreeHashBudgetRegionCover S₀ s.2 pref.2.2 := by
    apply treeHashBudget_phase_cover prims D S₀ A (prefixFuel+1) state prep _ s pref first
    intro i hi
    apply TreeSimHashCount.PartyBudget.bind (m := 0)
      (treeHashBudget_prelude_bound (gate i) (gateBound i hi))
    intro _
    exact treeHashBudget_party_region_outside S₀ _
      (treeHashBudget_batchPrefix_zero K circuits settings (ctx i) jobs initial)
  exact firstCover.union_trans cover

/-- An actual scheduler cut includes its reserved local prelude without
charging those inputs again in the per-batch allowance. -/
theorem treeHashBudget_batch_cut_prelude_cover {α : Type} (prims : Primitives)
    (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (jobs : List Job) (initial : ℕ × ℕ) (S₀ : Finset (Query C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (gateBound : ∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S₀)) 0)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (headZero : ∀ i out, IsQueryBoundP (advance (k i out).run) TreeSimHashCount.Region 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Step C E RealSpec α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
        (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i) >>=
        fun steps => executeSteps worldRoles D A noFunctionality
          (batchRounds circuits settings.mode parameter jobs) state steps)).run s))
    (final : r.2.2 ⊆ log) :
    ∃ S : Finset (Query C), S.card ≤ (C.n+3)*termCount C+
        halvings (batchCount circuits parameter jobs)+2 ∧ TreeHashBudgetRegionCover (S₀ ∪ S) s.2 r.2.2 := by
  let n := batchRounds circuits settings.mode parameter jobs
  let p := fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
    (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i
  let captured := ((r.1.1, fun i => treeLateSnapshotOut (r.1.2 i)),r.2)
  have cap : captured ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality n state (fun i => treeLateSnapshot n (p i)))).run s) := by
    rw [treeLateSnapshot_phase, simulateQ_map, StateT.run_map, support_map]
    exact ⟨r,run,rfl⟩
  have programs : (fun i => treeLateSnapshot n (p i)) = fun i =>
      treeLockstepLocalPrelude (gate i) >>= fun _ =>
        (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>=
          fun out => treeLateSnapshot 0 (k i out) := by
    funext i
    dsimp only [p]
    rw [treeLateSnapshot_gate]
    apply bind_congr
    intro _
    obtain ⟨within, exactRun⟩ := treeLateSnapshot_batch_timing K circuits settings (ctx i) jobs initial
    have h := treeLateSnapshot_bind within 0 (by simpa only [Nat.zero_add] using exactRun) 0 (k i)
    simpa only [n, parameters i, Nat.add_zero] using h
  rw [programs] at cap
  have full := treeHashBudget_batch_prelude_cover K prims circuits settings D A 0 state log cache coherent
    good ctx self parameter parameters jobs initial S₀ gate gateBound (fun i out => treeLateSnapshot 0 (k i out))
    (fun i out => treeHashBudget_snapshot_zero _ (headZero i out)) s captured
    (by simpa only [Nat.add_zero] using cap) final
  exact full


/-- Cutting a phase retains the exact pending steps, caches, adversary state
and log of that run, independently of whether any output eventually exists. -/
theorem treeHashBudget_phase_steps_cut {α : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n fuel : ℕ) (state : A.State)
    (p : C.Party → PartyM C E RealSpec α) (s : TreeSimState C)
    (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (n+fuel) state p)).run s)) :
    ∃ cut : (A.State × (C.Party → Step C E RealSpec α)) × TreeSimState C,
      cut ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (startSteps worldRoles D p >>= executeSteps worldRoles D A noFunctionality n state)).run s) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executeRounds worldRoles D A noFunctionality fuel cut.1.1 cut.1.2)).run cut.2) := by
  have form : executePhase worldRoles D A noFunctionality (n+fuel) state p =
      (startSteps worldRoles D p >>= executeSteps worldRoles D A noFunctionality n state) >>=
        fun cut => executeRounds worldRoles D A noFunctionality fuel cut.1 cut.2 := by
    simp only [executePhase, executeRounds_add, bind_assoc]
  rw [form, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  exact run

/-- The actual batch cut pays the new allowance once and leaves its exact
pending network to the rest of the ceremony. -/
theorem treeHashBudget_batch_split_cover {α : Type} (prims : Primitives)
    (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (jobs : List Job) (initial : ℕ × ℕ) (S₀ : Finset (Query C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (gateBound : ∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S₀)) 0)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (headZero : ∀ i out, IsQueryBoundP (advance (k i out).run) TreeSimHashCount.Region 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (batchRounds circuits settings.mode parameter jobs+fuel)
        state (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ (S : Finset (Query C)) (cut : (A.State × (C.Party → Step C E RealSpec α)) × TreeSimState C),
      S.card ≤ (C.n+3)*termCount C+halvings (batchCount circuits parameter jobs)+2 ∧
      TreeHashBudgetRegionCover (S₀ ∪ S) s.2 cut.2.2 ∧
      cut ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (startSteps worldRoles D (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i) >>=
          executeSteps worldRoles D A noFunctionality (batchRounds circuits settings.mode parameter jobs)
            state)).run s) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executeRounds worldRoles D A noFunctionality fuel cut.1.1 cut.1.2)).run cut.2) := by
  obtain ⟨cut, first, tail⟩ := treeHashBudget_phase_steps_cut prims D A
    (batchRounds circuits settings.mode parameter jobs) fuel state _ s r run
  have included : cut.2.2 ⊆ log :=
    (treeSimLoggedWorld_prefix prims D _ cut.2 r tail).subset.trans final
  obtain ⟨S, size, cover⟩ := treeHashBudget_batch_cut_prelude_cover K prims circuits settings D A state
    log cache coherent good ctx self parameter parameters jobs initial S₀ gate gateBound k headZero
    s cut first included
  exact ⟨S, cut, size, cover, first, tail⟩

/-- A zero-round snapshot can be reattached to the original retained suffix.
The saved continuations and both caches remain identical. -/
theorem treeHashBudget_snapshot_zero_attach {α : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (p : C.Party → PartyM C E RealSpec α) (s : TreeSimState C)
    (cut : (A.State × (C.Party → Step C E RealSpec α)) × TreeSimState C)
    (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (captured : ((cut.1.1, fun i => treeLateSnapshotOut (cut.1.2 i)), cut.2) ∈
      support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality 0 state
          (fun i => treeLateSnapshot 0 (p i)))).run s))
    (tail : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executeRounds worldRoles D A noFunctionality fuel cut.1.1 cut.1.2)).run cut.2)) :
    r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state p)).run s) := by
  have form := treeCheck_snapshot_logged prims D A 0 fuel state p s
  simp only [Nat.zero_add] at form
  rw [form, mem_support_bind_iff]
  refine ⟨((cut.1.1, fun i => treeLateSnapshotOut (cut.1.2 i)), cut.2), captured, ?_⟩
  simpa only [treeCheck_snapshot_restore] using tail

/-- An all-aborted retained network adds no honest query to any suffix. -/
theorem treeHashBudget_stopped_rounds_cover {α : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (stopped : ∀ i, steps i = .done none)
    (S : Finset (Query C)) (s : TreeSimState C)
    (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executeRounds worldRoles D A noFunctionality fuel state steps)).run s)) :
    TreeHashBudgetRegionCover S s.2 r.2.2 := by
  have doneAll : ∀ i, (steps i).isDone := by intro i; rw [stopped i]; trivial
  rw [executeRounds_all_done worldRoles D A noFunctionality fuel state steps (fun i _ => doneAll i)] at run
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
  subst r
  exact .refl _ _

/-- An accepted batch reserves all of its pending opening queries in its
single allowance. The original continuation and its complete log are retained. -/
theorem treeHashBudget_batch_next_reservation {α : Type} (prims : Primitives)
    (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (log : TreeSimLog C) (hash : HashCache C) (coherent : TreeSimHashCoherent hash log)
    (good : ¬ TreeSimHashBudgetCollision log) (S₀ : Finset (Query C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (gateBound : ∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S₀)) 0)
    (jobs : List Job) (initial : ℕ × ℕ)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (batchRounds circuits settings.mode parameter jobs + fuel)
        state (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i))).run s))
    (final : r.2.2 ⊆ log) (accepted : ∃ i value, r.1.2 i = some value) :
    ∃ (value : List (List Bit)) (records : C.Party → TreeSimCheckBatchRecord C)
      (state' : A.State) (cache : TreeSimState C)
      (gate' : C.Party → OracleComp (LocalSpec C) (Option Unit)) (S : Finset (Query C)),
      S.card ≤ (C.n+3)*termCount C+halvings (batchCount circuits parameter jobs)+2 ∧
      TreeHashBudgetRegionCover (S₀ ∪ S) s.2 cache.2 ∧
      (∀ i, IsQueryBoundP (gate' i)
        (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0) ∧
      (∀ i, (records i).outputs = value ∧ (records i).jobs = jobs ∧ (records i).start = initial) ∧
      (∃ width v ds sent, gate' = treeLockstepOpenGate K D (fun _ => true) width v ds sent) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state'
          (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ =>
            k i ((some value, [records i]),
              (initial.1 + batchLabels circuits parameter jobs, initial.2 + 1))))).run cache) := by
  let js := jobs.map (circuits parameter ·.kind)
  let rest := checkLabels (tupleCount js) + (fuel + 1)
  have rounds : batchRounds circuits settings.mode parameter jobs + fuel =
      depth js * settings.mode.rounds + 1 + rest := by
    unfold batchRounds batchCount rest js
    omega
  rw [rounds] at run
  have goodRun : ¬ TreeSimHashBudgetCollision r.2.2 := by
    rintro ⟨q, t, h, hq, ht, ne, a, b⟩
    exact good ⟨q, t, h, hq, ht, ne,
      a.imp (fun h => final h) (fun h => final h),
      b.imp (fun h => final h) (fun h => final h)⟩
  obtain ⟨value, canonical⟩ := treeLockstep_batch_canonical prims K circuits settings D A fuel state
    ctx self parameter parameters keys gate jobs initial k s r run goodRun accepted
  let fixed := fun i out => k i (treeLockstepCanonicalBatchResult value out)
  let p := fun i => treeLockstepLocalPrelude (E := E) (gate i) >>= fun _ =>
    treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial
  let next := fun i data => treeSimCheckBatchFinish K circuits (ctx i) jobs initial data >>= fixed i
  have timed (i) : TreeSimCheckTimed (depth js * settings.mode.rounds + 1) (p i).run := by
    apply treeLockstep_localPrelude_timed
    simpa only [parameters i] using treeSimCheckBatchPrefix_timed K circuits settings (ctx i) jobs initial
  have cutrun : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (depth js * settings.mode.rounds + 1 + rest)
        state (fun i => p i >>= next i))).run s) := by
    simpa only [p, next, fixed, treeSimCheckBatchAudit_run_prefix, bind_assoc] using canonical
  obtain ⟨pref, raw, hpref, selectedRaw, suffixRaw⟩ := treeLockstep_timed_boundary prims D A
    (depth js * settings.mode.rounds) rest state p next
    ([], (0, []), ⟨fun _ => [], initial.1, initial.2⟩) timed
    (fun i data => by
      unfold next treeSimCheckBatchFinish
      rw [bind_assoc]
      exact (treeSimCheckAfterVerify_exchange K (ctx i) _ data.2).bind _) s r cutrun accepted
  let honest := fun i : C.Party => if i ∉ D.1 then i else refHolder D K.publicTerm
  have hh (i) : honest i ∉ D.1 := by
    by_cases hi : i ∉ D.1
    · simpa only [honest, if_pos hi] using hi
    · simpa only [honest, if_neg hi] using (refHolder_spec D K.publicTerm).2
  have keep (i) (hi : i ∉ D.1) : honest i = i := if_pos hi
  let data := fun i => raw (honest i)
  have suffix : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality rest pref.1.1
        (fun i => next i (data i)))).run pref.2) := by
    rw [treeHashBudget_phase_congr D A rest pref.1.1 _ (fun i => next i (raw i))
      (fun i hi => by rw [show data i = raw i from congrArg raw (keep i hi)])]
    exact suffixRaw
  have localFields (i) :
      (∀ T, (ctx (honest i)).self ∉ C.holders T → ∀ g, (data i).2.1.1 T g = 0) ∧
      (data i).2.2.label = initial.1+depth js+1 ∧ (data i).2.2.tag = initial.2 ∧
      ((data i).2.1.2.map (·.count)).sum = tupleCount js := by
    have allowed := treeLockstep_logged_run_allowed prims D _ s pref hpref
    have party := treeSimCheck_phase_replay D A noFunctionality _ _ state _ pref.1 allowed
      (honest i) (hh i) (raw (honest i)) (selectedRaw _ (hh i))
    obtain ⟨_, _, party⟩ := party.option_bind_inv _ _ _
    simpa only [parameters, js] using treeHashBudget_batchPrefix_fields K circuits settings
      (ctx (honest i)) jobs initial (raw (honest i)) party.choose_spec.1.mem_support
  have counts (i) : (((data i).2.1.2).map (·.count)).sum = tupleCount js := (localFields i).2.2.2
  have labels (i) : (data i).2.2.label = initial.1 + depth js + 1 := (localFields i).2.1
  let v := fun i => if i ∈ D.1 then 0 else (data i).2.1.1
  have vEq (i) (hi : i ∉ D.1) : v i = (data i).2.1.1 := if_neg hi
  have zero (i T) (held : i ∉ C.holders T) (g) : v i T g = 0 := by
    by_cases hi : i ∈ D.1
    · simp only [v, if_pos hi, Pi.zero_apply]
    · rw [vEq i hi]
      exact (localFields i).1 T (by simpa only [keep i hi, self] using held) g
  simp only [next, treeLockstep_batchFinish_check] at suffix
  unfold treeLockstepBatchCheckCont at suffix
  simp only [fixed, treeLockstepCanonicalBatchResult, List.map_cons, List.map_nil, parameters] at suffix
  let record := fun i (checked : Unit × RunState C) =>
    (⟨ctx i, jobs, initial, (data i).1, (data i).2.1.2, (data i).2.2, value, checked.2⟩ :
      TreeSimCheckBatchRecord C)
  let cont := fun i (checked : Unit × RunState C) =>
    k i ((some value, [record i checked]), (checked.2.label, initial.2 + 1))
  have copyForm := treeHashBudget_phase_congr D A rest pref.1.1
    (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (data i).2.1.2).run (data i).2.2 >>=
      fun checked => openRep K (ctx i) (data i).2.1.1 (outputsOf js).length >>= fun _ => cont i checked)
    (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (data i).2.1.2).run (data i).2.2 >>=
      fun checked => openRep K (ctx i) (v i) (outputsOf js).length >>= fun _ => cont i checked)
    (by intro i hi; rw [vEq i hi])
  rw [copyForm] at suffix
  obtain ⟨checked, state', cache, gate', S, checkRuns, size, cover, gateZero, shape, tail⟩ :=
    treeHashBudget_check_pending_reservation K prims D A fuel pref.1.1 log hash coherent good ctx self
      (fun i => (data i).2.1.2) (fun i => (data i).2.2) (tupleCount js) counts initial.2
      (initial.1+depth js+1) (fun i _ => ⟨(localFields i).2.2.1, labels i⟩)
      (outputsOf js).length v zero cont pref.2 r suffix final accepted
  have finalLabel (i) (hi : i ∉ D.1) : (checked i).2.label = initial.1 + batchLabels circuits parameter jobs := by
    have h := lockstepLabels_check K (ctx i) (data i).2.1.2 (data i).2.2 (checked i).1 (checked i).2
      (checkRuns i hi)
    rw [counts i, labels i] at h
    unfold batchLabels batchCount
    dsimp only [js] at h
    omega
  refine ⟨value, (fun i => record i (checked i)), state', cache, gate', S, ?_, ?_, gateZero,
    (fun i => ⟨rfl, rfl, rfl⟩), ?_, ?_⟩
  · have terms := treeSimHash_parties_le_terms (C := C)
    have positive := C.one_le_t
    unfold Committee.n at terms
    dsimp only [js] at size
    change S.card ≤ (C.n+3)*termCount C+halvings (tupleCount (jobs.map (circuits parameter ·.kind)))+2
    rw [Nat.add_mul] at size ⊢
    omega
  · have firstCover : TreeHashBudgetRegionCover S₀ s.2 pref.2.2 := by
      apply treeHashBudget_phase_cover prims D S₀ A _ state p _ s pref hpref
      intro i hi
      apply TreeSimHashCount.PartyBudget.bind (m := 0)
        (treeHashBudget_prelude_bound (gate i) (gateBound i hi))
      intro _
      exact treeHashBudget_party_region_outside S₀ _
        (treeHashBudget_batchPrefix_zero K circuits settings (ctx i) jobs initial)
    exact firstCover.union_trans cover
  · obtain ⟨ds, sent, he⟩ := shape
    exact ⟨(outputsOf js).length, v, ds, sent, he⟩
  · rw [treeHashBudget_phase_congr D A fuel state' _
      (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ => cont i (checked i)) ?_]
    · exact tail
    · intro i hi
      simp only [cont, finalLabel i hi]


/-- A cutoff after a batch retains the pending local gate and captures
exactly the next continuation's local head. -/
theorem treeHashBudget_batch_snapshot {α : Type} (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (gate : OracleComp (LocalSpec C) (Option Unit))
    (k : ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α) :
    treeLateSnapshot (batchRounds circuits settings.mode ctx.keys.parameter jobs)
      (treeLockstepLocalPrelude gate >>= fun _ =>
        (treeSimCheckBatchAudit K circuits settings ctx jobs).run.run initial >>= k) =
      treeLockstepLocalPrelude gate >>= fun _ =>
        (treeSimCheckBatchAudit K circuits settings ctx jobs).run.run initial >>=
          fun out => treeLateSnapshot 0 (k out) := by
  rw [treeLateSnapshot_gate]
  apply bind_congr
  intro _
  obtain ⟨within, exactRun⟩ := treeLateSnapshot_batch_timing K circuits settings ctx jobs initial
  have h := treeLateSnapshot_bind within 0 (by simpa only [Nat.zero_add] using exactRun) 0 k
  simpa only [Nat.add_zero] using h

/-- A retained batch either ends the honest network within its allowance,
or reaches the next phase with common outputs and a reserved local gate.
The alternative is decided by the actual retained steps, not final records. -/
theorem treeHashBudget_batch_transition {α : Type} (prims : Primitives)
    (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (log : TreeSimLog C) (hash : HashCache C) (coherent : TreeSimHashCoherent hash log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (jobs : List Job) (initial : ℕ × ℕ) (S₀ : Finset (Query C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (gateBound : ∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S₀)) 0)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (headZero : ∀ i out, IsQueryBoundP (advance (k i out).run) TreeSimHashCount.Region 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (batchRounds circuits settings.mode parameter jobs+fuel)
        state (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i))).run s))
    (final : r.2.2 ⊆ log) :
    (∃ S : Finset (Query C), S.card ≤ (C.n+3)*termCount C+halvings (batchCount circuits parameter jobs)+2 ∧
      TreeHashBudgetRegionCover (S₀ ∪ S) s.2 r.2.2) ∨
    ∃ (value : List (List Bit)) (records : C.Party → TreeSimCheckBatchRecord C)
      (state' : A.State) (cache : TreeSimState C)
      (gate' : C.Party → OracleComp (LocalSpec C) (Option Unit)) (S : Finset (Query C)),
      S.card ≤ (C.n+3)*termCount C+halvings (batchCount circuits parameter jobs)+2 ∧
      TreeHashBudgetRegionCover (S₀ ∪ S) s.2 cache.2 ∧
      (∀ i, IsQueryBoundP (gate' i)
        (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0) ∧
      (∀ i, (records i).outputs = value ∧ (records i).jobs = jobs ∧ (records i).start = initial) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state'
          (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ =>
            k i ((some value, [records i]),
              (initial.1 + batchLabels circuits parameter jobs, initial.2 + 1))))).run cache) := by
  obtain ⟨S, cut, size, cover, first, tail⟩ := treeHashBudget_batch_split_cover K prims circuits settings
    D A fuel state log hash coherent good ctx self parameter parameters jobs initial S₀ gate gateBound
    k headZero s r run final
  by_cases stopped : ∀ i, cut.1.2 i = .done none
  · exact Or.inl ⟨S, size, cover.trans (treeHashBudget_stopped_rounds_cover prims D A fuel
      cut.1.1 cut.1.2 stopped _ cut.2 r tail)⟩
  · let n := batchRounds circuits settings.mode parameter jobs
    let p := fun i => treeLockstepLocalPrelude (E := E) (gate i) >>= fun _ =>
      (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= k i
    let captured := ((cut.1.1, fun i => treeLateSnapshotOut (cut.1.2 i)), cut.2)
    have cap : captured ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality n state (fun i => treeLateSnapshot n (p i)))).run s) := by
      rw [treeLateSnapshot_phase, simulateQ_map, StateT.run_map, support_map]
      exact ⟨cut, first, rfl⟩
    have programs : (fun i => treeLateSnapshot n (p i)) = fun i =>
        treeLockstepLocalPrelude (gate i) >>= fun _ =>
          (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>=
            fun out => treeLateSnapshot 0 (k i out) := by
      funext i
      simpa only [n, p, parameters i] using
        treeHashBudget_batch_snapshot K circuits settings (ctx i) jobs initial (gate i) (k i)
    rw [programs] at cap
    have accepted : ∃ i value, captured.1.2 i = some value := by
      push Not at stopped
      obtain ⟨i, hi⟩ := stopped
      exact ⟨i, cut.1.2 i, treeLateSnapshotOut_some _ hi⟩
    have included : captured.2.2 ⊆ log :=
      (treeSimLoggedWorld_prefix prims D _ cut.2 r tail).subset.trans final
    obtain ⟨value, records, state', cache, gate', T, sizeT, coverT, boundT, fields, _, next⟩ :=
      treeHashBudget_batch_next_reservation K prims circuits settings D A 0 state ctx self parameter
        parameters keys log hash coherent good S₀ gate gateBound jobs initial
        (fun i out => treeLateSnapshot 0 (k i out)) s captured
        (by simpa only [Nat.add_zero, n] using cap) included accepted
    refine Or.inr ⟨value, records, state', cache, gate', T, sizeT, coverT, boundT, fields, ?_⟩
    apply treeHashBudget_snapshot_zero_attach prims D A fuel state' _ cache cut r _ tail
    simpa only [treeLateSnapshot_gate] using next

/-- The writer/state decomposition of one audited batch followed by the
remaining list, with both record lists retained in order. -/
theorem treeHashBudget_batches_cons (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (jobs : List Job) (batches : List (List Job)) (initial : ℕ × ℕ) :
    (((jobs :: batches).mapM (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx)).run.run initial) =
      (do
        let a ← (treeSimCheckBatchAudit K circuits settings ctx jobs).run.run initial
        let b ← ((batches.mapM (treeSimCheckBatchAudit K circuits settings ctx)).run.run a.2)
        pure ((a.1.1 :: b.1.1, a.1.2 ++ b.1.2), b.2)) := by
  -- The raw writer/state law also used by treeLockstep_batches_cons.
  simp [List.mapM_cons, WriterT.run_bind, StateT.run_bind]

/-- A list of actual batches spends at most one allowance per reached batch.
The continuation receives common opened values if that boundary is reached;
an earlier all-aborted boundary needs no continuation hypothesis. -/
theorem treeHashBudget_batches_cover {α : Type} (prims : Primitives)
    (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ)
    (log : TreeSimLog C) (hash : HashCache C) (coherent : TreeSimHashCoherent hash log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (batches : List (List Job)) (B tailCost : ℕ)
    (cost : ∀ jobs ∈ batches, (C.n+3)*termCount C+halvings (batchCount circuits parameter jobs)+2 ≤ B)
    (state : A.State) (initial : ℕ × ℕ) (S₀ : Finset (Query C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (gateBound : ∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S₀)) 0)
    (k : C.Party → ((List (Option (List (List Bit))) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (headZero : ∀ i out, IsQueryBoundP (advance (k i out).run) TreeSimHashCount.Region 0)
    (finish : ∀ (outputs : List (List (List Bit))) (records : C.Party → List (TreeSimCheckBatchRecord C))
      (state : A.State) (S : Finset (Query C))
      (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      (∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
        (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0) →
      ∀ (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C),
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state
          (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
            k i ((outputs.map some, records i),
              (initial.1+(batches.map (batchLabels circuits parameter)).sum, initial.2+batches.length))))).run s) →
      r.2.2 ⊆ log → ∃ T : Finset (Query C), T.card ≤ tailCost ∧
        TreeHashBudgetRegionCover (S ∪ T) s.2 r.2.2)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        ((batches.map (batchRounds circuits settings.mode parameter)).sum+fuel)
        state (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          ((batches.mapM (treeSimCheckBatchAudit K circuits settings (ctx i))).run.run initial) >>= k i))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ T : Finset (Query C), T.card ≤ batches.length*B+tailCost ∧
      TreeHashBudgetRegionCover (S₀ ∪ T) s.2 r.2.2 := by
  induction batches generalizing state initial S₀ gate k s with
  | nil =>
    have first := finish [] (fun _ => []) state S₀ gate gateBound s r
    simp only [List.map_nil, List.length_nil, List.sum_nil, Nat.add_zero] at first
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]
    apply first
    · simpa [List.map_nil, List.sum_nil, Nat.zero_add, List.mapM_nil,
        WriterT.run_pure, StateT.run_pure, pure_bind] using run
    · exact final
  | cons jobs batches ih =>
    let cont := fun i (a : ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))) =>
      ((batches.mapM (treeSimCheckBatchAudit K circuits settings (ctx i))).run.run a.2) >>=
        fun b => k i ((a.1.1 :: b.1.1, a.1.2 ++ b.1.2), b.2)
    have contHead (i out) : IsQueryBoundP (advance (cont i out).run) TreeSimHashCount.Region 0 := by
      apply treeHashBudget_batches_head_zero K circuits settings (ctx i) batches out.2
      intro _ tail
      exact headZero i _
    have run' : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality
          (batchRounds circuits settings.mode parameter jobs+
            ((batches.map (batchRounds circuits settings.mode parameter)).sum+fuel))
          state (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
            (treeSimCheckBatchAudit K circuits settings (ctx i) jobs).run.run initial >>= cont i))).run s) := by
      simpa only [List.map_cons, List.sum_cons, Nat.add_assoc,
        treeHashBudget_batches_cons, bind_assoc, pure_bind, cont] using run
    rcases treeHashBudget_batch_transition K prims circuits settings D A
      ((batches.map (batchRounds circuits settings.mode parameter)).sum+fuel) state
      log hash coherent good ctx self parameter parameters keys jobs initial S₀ gate gateBound
      cont contHead s r run' final with terminal | next
    · obtain ⟨T, size, cover⟩ := terminal
      refine ⟨T, ?_, cover⟩
      have bound := size.trans (cost jobs (by simp))
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · obtain ⟨value, records, state', cache, gate', S, size, cover, gateZero, fields, next⟩ := next
      let nextK := fun i (out : ((List (Option (List (List Bit))) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ))) =>
        k i ((some value :: out.1.1, [records i] ++ out.1.2), out.2)
      have nextRun : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (executePhase worldRoles D A noFunctionality
            ((batches.map (batchRounds circuits settings.mode parameter)).sum+fuel) state'
            (fun i => treeLockstepLocalPrelude (gate' i) >>= fun _ =>
              ((batches.mapM (treeSimCheckBatchAudit K circuits settings (ctx i))).run.run
                (initial.1+batchLabels circuits parameter jobs,initial.2+1)) >>= nextK i))).run cache) := next
      have nextFinish : ∀ (outputs : List (List (List Bit)))
          (rec : C.Party → List (TreeSimCheckBatchRecord C)) (state : A.State)
          (S : Finset (Query C)) (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)),
          (∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
            (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0) →
          ∀ s r, r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
            (executePhase worldRoles D A noFunctionality fuel state
              (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
                nextK i ((outputs.map some, rec i),
                  ((initial.1+batchLabels circuits parameter jobs)+
                    (batches.map (batchLabels circuits parameter)).sum,
                    (initial.2+1)+batches.length))))).run s) →
          r.2.2 ⊆ log → ∃ T : Finset (Query C), T.card ≤ tailCost ∧
            TreeHashBudgetRegionCover (S ∪ T) s.2 r.2.2 := by
        intro outputs rec state S gate bound s r hr hl
        apply finish (value :: outputs) (fun i => [records i] ++ rec i) state S gate bound s r _ hl
        simpa only [List.map_cons, List.sum_cons, List.length_cons, nextK,
          Nat.add_assoc, Nat.add_comm 1 batches.length] using hr
      obtain ⟨T, sizeT, coverT⟩ := ih (fun js hj => cost js (List.mem_cons_of_mem jobs hj))
        state' (initial.1+batchLabels circuits parameter jobs,initial.2+1) S gate'
        (fun i _ => gateZero i) nextK (fun i out => headZero i _) nextFinish cache nextRun
      refine ⟨S ∪ T, (Finset.card_union_le S T).trans ?_, ?_⟩
      · have bound := size.trans (cost jobs (by simp))
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · simpa [Finset.union_assoc] using cover.union_trans coverT

/-- Chunked execution inherits the retained batch bound, passing one common
flattened output to the actual continuation. -/
theorem treeHashBudget_batched_cover {α : Type} (prims : Primitives)
    (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ)
    (log : TreeSimLog C) (hash : HashCache C) (coherent : TreeSimHashCoherent hash log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (jobs : List Job) (B tailCost : ℕ)
    (cost : ∀ batch ∈ chunks settings.batchSize jobs,
      (C.n+3)*termCount C+halvings (batchCount circuits parameter batch)+2 ≤ B)
    (state : A.State) (initial : ℕ × ℕ) (S₀ : Finset (Query C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (gateBound : ∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S₀)) 0)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (headZero : ∀ i out, IsQueryBoundP (advance (k i out).run) TreeSimHashCount.Region 0)
    (finish : ∀ (outputs : List (List Bit)) (records : C.Party → List (TreeSimCheckBatchRecord C))
      (state : A.State) (S : Finset (Query C))
      (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      (∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
        (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0) →
      ∀ (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C),
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state
          (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
            k i ((some outputs, records i),
              (initial.1+((chunks settings.batchSize jobs).map (batchLabels circuits parameter)).sum, initial.2+(chunks settings.batchSize jobs).length))))).run s) →
      r.2.2 ⊆ log → ∃ T : Finset (Query C), T.card ≤ tailCost ∧
        TreeHashBudgetRegionCover (S ∪ T) s.2 r.2.2)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (((chunks settings.batchSize jobs).map (batchRounds circuits settings.mode parameter)).sum+fuel)
        state (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          ((batched settings.batchSize (treeSimCheckBatchAudit K circuits settings (ctx i)) jobs).run.run initial) >>= k i))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ T : Finset (Query C), T.card ≤ (chunks settings.batchSize jobs).length*B+tailCost ∧
      TreeHashBudgetRegionCover (S₀ ∪ T) s.2 r.2.2 := by
  have raw (i) : (batched settings.batchSize (treeSimCheckBatchAudit (G := RealSpec) K circuits settings
      (ctx i)) jobs).run.run initial = (do
        let a ← ((chunks settings.batchSize jobs).mapM
          (treeSimCheckBatchAudit K circuits settings (ctx i))).run.run initial
        pure ((a.1.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [], a.1.2), a.2)) := by
    simp [batched]
  simp only [raw, bind_assoc, pure_bind] at run
  let next := fun i (a : (List (Option (List (List Bit))) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) =>
    k i ((a.1.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [], a.1.2), a.2)
  apply treeHashBudget_batches_cover K prims circuits settings D A fuel log hash coherent good ctx self
    parameter parameters keys (chunks settings.batchSize jobs) B tailCost cost state initial S₀ gate
    gateBound next (fun i out => headZero i _) _ s r run final
  intro outputs records state S gate bound s r hr hl
  apply finish outputs.flatten records state S gate bound s r _ hl
  simpa only [next, foldlM_some_append, List.nil_append] using hr

/-- Public local finishing code uses only the finite cover reserved by its
incoming gate, including a gate or continuation that aborts. -/
theorem treeHashBudget_gated_zero_phase_cover {α : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (S : Finset (Query C)) (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (bound : ∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0)
    (p : C.Party → PartyM C E RealSpec α)
    (zero : ∀ i, i ∉ D.1 → TreeSimHashCount.PartyBudget TreeSimHashCount.Region (p i) 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ => p i))).run s)) :
    TreeHashBudgetRegionCover S s.2 r.2.2 := by
  apply treeHashBudget_phase_cover prims D S A fuel state _ _ s r run
  intro i hi
  exact (treeHashBudget_prelude_bound (gate i) (bound i hi)).bind (m := 0)
    (fun _ => treeHashBudget_party_region_outside S (p i) (zero i hi))

end BatchCover

-- A75_SECOND_RUN_BEGIN
section SecondRunCover
open TreeSimHashCount
attribute [local irreducible] treeLockstepBottomFinish signJobs

/-- A region-free full continuation requires no additional allowance after
the actual chunked run, including any terminal aborted prefix. -/
theorem treeHashBudget_batched_zero_tail_cover {α : Type} (prims : Primitives)
    (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ)
    (log : TreeSimLog C) (hash : HashCache C) (coherent : TreeSimHashCoherent hash log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T)) (jobs : List Job) (B : ℕ)
    (cost : ∀ batch ∈ chunks settings.batchSize jobs,
      (C.n+3)*termCount C+halvings (batchCount circuits parameter batch)+2 ≤ B)
    (state : A.State) (initial : ℕ × ℕ) (S₀ : Finset (Query C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (gateBound : ∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S₀)) 0)
    (k : C.Party → ((Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) →
      PartyM C E RealSpec α)
    (zero : ∀ i out, PartyBudget Region (k i out) 0)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (((chunks settings.batchSize jobs).map (batchRounds circuits settings.mode parameter)).sum+fuel)
        state (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          (batched settings.batchSize (treeSimCheckBatchAudit K circuits settings (ctx i)) jobs).run.run initial
            >>= k i))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ T : Finset (Query C), T.card ≤ (chunks settings.batchSize jobs).length*B ∧
      TreeHashBudgetRegionCover (S₀ ∪ T) s.2 r.2.2 := by
  obtain ⟨T, size, cover⟩ := treeHashBudget_batched_cover K prims circuits settings D A fuel
    log hash coherent good ctx self parameter parameters keys jobs B 0 cost state initial S₀ gate
    gateBound k (fun i out => advance_zero _ _ (zero i out))
    (by
      intro outputs records state S gate bound s r hr hl
      refine ⟨∅, by simp, ?_⟩
      simpa only [Finset.union_empty] using treeHashBudget_gated_zero_phase_cover prims D A fuel
        state S gate bound _ (fun i _ => zero i _) s r hr)
    s r run final
  exact ⟨T, by simpa only [Nat.add_zero] using size, cover⟩

/-- The selected second run and its full bottom-tree verification use at
most one allowance per signing chunk, with the original earlier records. -/
theorem treeHashBudget_secondRun_cover (prims : Primitives) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ)
    (log : TreeSimLog C) (hash : HashCache C) (coherent : TreeSimHashCoherent hash log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit))
    (root : Digest) (randomness : Randomness) (enc : Encoding)
    (records : C.Party → List (TreeSimCheckBatchRecord C)) (B : ℕ)
    (cost : ∀ batch ∈ chunks settings.batchSize (signJobs b enc),
      (C.n+3)*termCount C+halvings (batchCount circuits parameter batch)+2 ≤ B)
    (state : A.State) (initial : ℕ × ℕ) (S₀ : Finset (Query C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (gateBound : ∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S₀)) 0)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (((chunks settings.batchSize (signJobs b enc)).map
          (batchRounds circuits settings.mode parameter)).sum+fuel) state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          (batched settings.batchSize (treeSimCheckBatchAudit K circuits settings (ctx i))
            (signJobs b enc)).run.run initial >>= fun a =>
              treeLockstepBottomFinish parameter top b outputs root randomness a.1.1
                (records i ++ a.1.2)))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ T : Finset (Query C), T.card ≤ (chunks settings.batchSize (signJobs b enc)).length*B ∧
      TreeHashBudgetRegionCover (S₀ ∪ T) s.2 r.2.2 := by
  exact treeHashBudget_batched_zero_tail_cover K prims circuits settings D A fuel
    log hash coherent good ctx self parameter parameters keys (signJobs b enc) B cost state initial
    S₀ gate gateBound
    (fun i a => treeLockstepBottomFinish parameter top b outputs root randomness a.1.1 (records i ++ a.1.2))
    (fun i a => treeHashBudget_bottomFinish_zero parameter top b outputs root randomness a.1.1 (records i ++ a.1.2))
    s r run final

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_secondRun_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_secondRun_cover

end SecondRunCover
-- A75_SECOND_RUN_END

-- A75_GLOBAL_CEREMONY_BEGIN
section GlobalCeremony
open TreeSimHashCount
attribute [local irreducible] topJobs bottomJobs signJobs maxBatch ceremonyBatches
  merkleNode merklePath Concrete.layerRoot treeLockstepPublicChoiceCode

set_option maxHeartbeats 200000 in
theorem treeHashBudget_top_ceremony_cover (prims : Primitives) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (S₀ : Finset (Query C)) (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (gateBound : ∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S₀)) 0)
    (top : TopTree) (log : TreeSimLog C) (hash : HashCache C)
    (coherent : TreeSimHashCoherent hash log) (good : ¬ TreeSimHashBudgetCollision log)
    (_rows : ∀ t u, (⟨t,u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log →
      TreeSimCheckWorldHashes (hashOf prims hash) t u)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode)) state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          treeSimCheckAfterSetupAudit K circuits settings (ctx i) top .top))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ T : Finset (Query C), T.card ≤ treeBatches settings .top * ((C.n+3)*termCount C+
      maxBatch circuits settings (fun jobs => halvings (tupleCount jobs))+2) ∧
      TreeHashBudgetRegionCover (S₀ ∪ T) s.2 r.2.2 := by
  simp only [treeLockstep_afterSetup_first, treeLockstepFirstJobs] at run
  let B := (C.n+3)*termCount C+maxBatch circuits settings (fun jobs => halvings (tupleCount jobs))+2
  let M := maxBatch circuits settings (runRounds settings.mode)
  let N := ceremonyBatches settings * M
  have cost (b : Fin (2 ^ layerHeight)) (enc : Encoding) (batch : List Job)
      (member : batch ∈ chunks settings.batchSize topJobs ∨
        batch ∈ chunks settings.batchSize (bottomJobs b) ∨
        batch ∈ chunks settings.batchSize (signJobs b enc)) :
      (C.n+3)*termCount C+halvings (batchCount circuits parameter batch)+2 ≤ B := by
    have h := measure_le_maxBatch circuits settings (fun js => halvings (tupleCount js)) parameter b enc batch member
    exact Nat.add_le_add_right (Nat.add_le_add_left h _) _
  let js := chunks settings.batchSize topJobs
  let X := (js.map (batchRounds circuits settings.mode parameter)).sum
  have hx : X ≤ N :=
    (chunks_rounds_le circuits settings parameter 0 (fun _ => digit 0) js
      (fun _ hj => Or.inl hj)).trans
      (Nat.mul_le_mul_right M (treeBatches_le_ceremonyBatches settings .top))
  have fuel : N = X + (N-X) := by omega
  change r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality N state _)).run s) at run
  rw [fuel] at run
  have zero (i) (out : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) :
      PartyBudget Region (treeLockstepFirstRest K circuits settings (ctx i) top .top out) 0 := by
    rcases out with ⟨⟨value, records⟩, initial⟩
    cases value with
    | none => exact PartyBudget.of_all PartyBound.failure
    | some values => exact treeHashBudget_topFinish_zero _ _ _
  obtain ⟨T, size, cover⟩ := treeHashBudget_batched_zero_tail_cover K prims circuits settings D A (N-X)
    log hash coherent good ctx self parameter parameters keys topJobs B
    (fun batch member => cost 0 (fun _ => digit 0) batch (Or.inl member))
    state (0,0) S₀ gate gateBound
    (fun i => treeLockstepFirstRest K circuits settings (ctx i) top .top) zero s r run final
  exact ⟨T, by simpa only [treeBatches, B] using size, cover⟩

set_option maxHeartbeats 300000 in
theorem treeHashBudget_bottom_ceremony_cover (prims : Primitives) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (S₀ : Finset (Query C)) (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (gateBound : ∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S₀)) 0)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (log : TreeSimLog C) (hash : HashCache C)
    (coherent : TreeSimHashCoherent hash log) (good : ¬ TreeSimHashBudgetCollision log)
    (rows : ∀ t u, (⟨t,u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log →
      TreeSimCheckWorldHashes (hashOf prims hash) t u)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode)) state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          treeSimCheckAfterSetupAudit K circuits settings (ctx i) top (.bottom b)))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ T : Finset (Query C), T.card ≤ treeBatches settings (.bottom b) * ((C.n+3)*termCount C+
      maxBatch circuits settings (fun jobs => halvings (tupleCount jobs))+2) ∧
      TreeHashBudgetRegionCover (S₀ ∪ T) s.2 r.2.2 := by
  simp only [treeLockstep_afterSetup_first, treeLockstepFirstJobs] at run
  let B := (C.n+3)*termCount C+maxBatch circuits settings (fun jobs => halvings (tupleCount jobs))+2
  let M := maxBatch circuits settings (runRounds settings.mode)
  let N := ceremonyBatches settings * M
  have cost (b : Fin (2 ^ layerHeight)) (enc : Encoding) (batch : List Job)
      (member : batch ∈ chunks settings.batchSize topJobs ∨
        batch ∈ chunks settings.batchSize (bottomJobs b) ∨
        batch ∈ chunks settings.batchSize (signJobs b enc)) :
      (C.n+3)*termCount C+halvings (batchCount circuits parameter batch)+2 ≤ B := by
    have h := measure_le_maxBatch circuits settings (fun js => halvings (tupleCount js)) parameter b enc batch member
    exact Nat.add_le_add_right (Nat.add_le_add_left h _) _
  let js := chunks settings.batchSize (bottomJobs b)
  let X := (js.map (batchRounds circuits settings.mode parameter)).sum
  let count₂ := (chunks settings.batchSize (signJobs b fun _ => digit 0)).length
  let Y := count₂ * M
  have hX : X ≤ js.length * M := chunks_rounds_le circuits settings parameter b
    (fun _ => digit 0) js (fun _ hj => Or.inr (Or.inl hj))
  have hY (enc : Encoding) : ((chunks settings.batchSize (signJobs b enc)).map
      (batchRounds circuits settings.mode parameter)).sum ≤ Y := by
    have h := chunks_rounds_le circuits settings parameter b enc
      (chunks settings.batchSize (signJobs b enc)) (fun _ hj => Or.inr (Or.inr hj))
    rw [length_chunks_signJobs settings b b enc (fun _ => digit 0)] at h
    exact h
  have hXY : X+Y ≤ N := by
    calc X+Y ≤ js.length*M+count₂*M := add_le_add hX le_rfl
      _ = treeBatches settings (.bottom b)*M := by
        change js.length*M+count₂*M = (js.length+count₂)*M
        ring
      _ ≤ N := Nat.mul_le_mul_right M (treeBatches_le_ceremonyBatches settings (.bottom b))
  have fuel : N = X+(N-X) := by omega
  change r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality N state _)).run s) at run
  rw [fuel] at run
  obtain ⟨T, size, cover⟩ := treeHashBudget_batched_cover K prims circuits settings D A (N-X)
    log hash coherent good ctx self parameter parameters keys (bottomJobs b) B (count₂*B)
    (fun batch member => cost b (fun _ => digit 0) batch (Or.inr (Or.inl member)))
    state (0,0) S₀ gate gateBound
    (fun i => treeLockstepFirstRest K circuits settings (ctx i) top (.bottom b))
    (fun i out => treeHashBudget_firstRest_head_zero K circuits settings (ctx i) top (.bottom b) out)
    (by
      intro outputs records state S gate bound s r hr final
      simp only [treeLockstepFirstRest, parameters] at hr
      obtain ⟨gate', bound', fixed⟩ := treeHashBudget_public_phase_gate prims D A (N-X) state
        (hashOf prims hash) S gate bound (treeLockstepPublicChoiceCode parameter b outputs) _ s r hr
        (fun t u mem => rows t u (final mem))
      cases choice : ThresholdLeanXmssSecurity.D prims (hashOf prims hash)
          (tweakable (treeLockstepPublicChoiceCode parameter b outputs)) with
      | none =>
        simp only [choice] at fixed
        refine ⟨∅, by simp, ?_⟩
        simpa only [Finset.union_empty] using treeHashBudget_gated_zero_phase_cover prims D A (N-X)
          state S gate' bound' (fun _ => failure)
          (fun _ _ => PartyBudget.of_all PartyBound.failure) s r fixed
      | some selected =>
        obtain ⟨root, randomness, enc⟩ := selected
        simp only [choice] at fixed
        let Z := ((chunks settings.batchSize (signJobs b enc)).map
          (batchRounds circuits settings.mode parameter)).sum
        have enough : Z ≤ N-X := by have h := hY enc; omega
        have fuel' : N-X = Z+(N-X-Z) := by omega
        rw [fuel'] at fixed
        obtain ⟨T, sizeT, coverT⟩ := treeHashBudget_secondRun_cover K prims circuits settings D A (N-X-Z)
          log hash coherent good ctx self parameter parameters keys top b outputs root randomness enc
          records B (fun batch member => cost b enc batch (Or.inr (Or.inr member)))
          state _ S gate' bound' s r fixed final
        refine ⟨T, ?_, coverT⟩
        simpa only [length_chunks_signJobs settings b b enc (fun _ => digit 0)] using sizeT)
    s r run final
  refine ⟨T, ?_, cover⟩
  calc T.card ≤ (chunks settings.batchSize (bottomJobs b)).length*B+count₂*B := size
    _ = treeBatches settings (.bottom b)*B := by
      change js.length*B+count₂*B = (js.length+count₂)*B
      ring

theorem treeHashBudget_afterSetup_cover (prims : Primitives) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (S₀ : Finset (Query C)) (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (gateBound : ∀ i, i ∉ D.1 → IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S₀)) 0)
    (top : TopTree) (tree : Tree) (log : TreeSimLog C) (hash : HashCache C)
    (coherent : TreeSimHashCoherent hash log) (good : ¬ TreeSimHashBudgetCollision log)
    (rows : ∀ t u, (⟨t,u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log →
      TreeSimCheckWorldHashes (hashOf prims hash) t u)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode)) state
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          treeSimCheckAfterSetupAudit K circuits settings (ctx i) top tree))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ T : Finset (Query C), T.card ≤ treeBatches settings tree * ((C.n+3)*termCount C+
      maxBatch circuits settings (fun jobs => halvings (tupleCount jobs))+2) ∧
      TreeHashBudgetRegionCover (S₀ ∪ T) s.2 r.2.2 := by
  cases tree with
  | top =>
    exact treeHashBudget_top_ceremony_cover K prims circuits settings D A state ctx self parameter
      parameters keys S₀ gate gateBound top log hash coherent good rows s r run final
  | bottom b =>
    exact treeHashBudget_bottom_ceremony_cover K prims circuits settings D A state ctx self parameter
      parameters keys S₀ gate gateBound top b log hash coherent good rows s r run final

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_top_ceremony_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_top_ceremony_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_bottom_ceremony_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_bottom_ceremony_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_afterSetup_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_afterSetup_cover

end GlobalCeremony

-- A75_GLOBAL_CEREMONY_END

-- A75_NORMALIZED_ASSEMBLY_BEGIN
section NormalizedAssembly
variable (prims : Primitives) (circuits : Circuits) (settings : Settings)

/-- Auditing and splitting the actual setup preserve the full terminal
state, including the hidden cache and retained query log. -/
theorem treeHashBudget_audit_setup_run (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    (simulateQ (treeSimLoggedWorld prims D)
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)).run ((∅,∅),[]) =
      (treeSaltSetup prims D A x z >>= fun p =>
        (simulateQ (treeSimLoggedWorld prims D)
          (auditAfterProgram K circuits settings top tree D A x Z p.1.1 p.1.2)).run p.2) := by
  obtain ⟨fuel, hf⟩ : ∃ fuel, ceremonyFuel circuits settings = fuel+3 :=
    ⟨ceremonyFuel circuits settings-3, by simp only [ceremonyFuel, setupRounds]; omega⟩
  have hc : (fun i => treeSimCheckCeremonyAudit K circuits settings i (x i) top tree) =
      (fun i => prssSetup i >>= fun prss =>
        treeSimCheckAfterSetupAudit K circuits settings ⟨i,x i,prss⟩ top tree) := rfl
  unfold treeSimCheckAuditedGame realExecution treeSaltSetup auditAfterProgram
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  apply bind_congr
  intro start
  rw [hf, hc, executePhase_prssSetup_bind]
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, simulateQ_executePhase,
    treeSimRealRoles, Nat.add_sub_cancel]
  rfl

/-- A normalized supported result has an audited setup and suffix with the
same Boolean, terminal caches and complete log. -/
theorem treeHashBudget_normalized_setup (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (r : ((Bool × TreeSimLog C) × HiddenCache C) × HashCache C)
    (run : r ∈ support ((simulateQ (localAnswer prims)
      (treeSimHashProgram K circuits settings top tree D A x z Z)).run ∅)) :
    ∃ p ∈ support (treeSaltSetup prims D A x z),
      ∃ after ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (auditAfterProgram K circuits settings top tree D A x Z p.1.1 p.1.2)).run p.2),
        after.1.1 = r.1.1.1 ∧ after.2 = ((r.2,r.1.2),r.1.1.2) := by
  have real : (r.1.1.1,(r.2,r.1.2),r.1.1.2) ∈ support
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeRealGame K circuits settings top tree D A x z Z)).run ((∅,∅),[])) := by
    rw [← treeSim_localReal_eq K circuits settings top tree D A x z Z,
      treeSimHash_state_normalize, support_map]
    exact ⟨r,run,rfl⟩
  rw [← treeSimCheck_audited_game_erase K circuits settings top tree D A x z Z,
    simulateQ_map, StateT.run_map, support_map] at real
  obtain ⟨after, ha, eq⟩ := real
  rw [treeHashBudget_audit_setup_run K prims circuits settings, mem_support_bind_iff] at ha
  obtain ⟨p,hp,tail⟩ := ha
  exact ⟨p,hp,after,tail,congrArg Prod.fst eq,congrArg Prod.snd eq⟩

/-- The actual setup, including the adversarial start, has the fixed setup
allowance and begins with an empty honest transcript. -/
theorem treeHashBudget_setup_logged_cover (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : p ∈ support (treeSaltSetup prims D A x z)) :
    ∃ S : Finset (Query C), S.card ≤ C.n*(termCount C+C.n)+C.n^2 ∧
      TreeHashBudgetRegionCover S [] p.2.2 := by
  unfold treeSaltSetup at run
  rw [mem_support_bind_iff] at run
  obtain ⟨start, first, setup⟩ := run
  obtain ⟨S,size,cover⟩ := treeHashBudget_setup_capacity prims D A start.1 start.2 p setup
  exact ⟨S,size,(treeHashBudget_adversary_cover prims D S _ ((∅,∅),[]) start first).region.trans cover⟩

/-- Setup and a cover of the actual audited post-setup execution imply the
original normalized honest-input budget with all its quantifiers unchanged. -/
theorem treeHashBudget_honest_of_postSetup
    (post : 0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput), DealtInputs D x →
      ∀ p ∈ support (treeSaltSetup prims D A x z),
        ∀ after ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (auditAfterProgram K circuits settings top tree D A x Z p.1.1 p.1.2)).run p.2),
          TreeSimHashCoherent after.2.1.1 after.2.2 → ¬ TreeSimHashBudgetCollision after.2.2 →
          ∃ T : Finset (Query C),
            T.card ≤ treeBatches settings tree * ((C.n+3)*termCount C +
              maxBatch circuits settings (fun jobs => halvings (tupleCount jobs))+2) ∧
            TreeHashBudgetRegionCover T p.2.2 after.2.2) :
    TreeSimHashHonestBudget prims K circuits settings := by
  intro positive top tree D A x z Z q dealt budget small r run good
  obtain ⟨p,hp,after,ha,_,state⟩ :=
    treeHashBudget_normalized_setup K prims circuits settings top tree D A x z Z r run
  have coherent : TreeSimHashCoherent r.2 r.1.1.2 :=
    treeSimHash_normalized_coherent prims D _ ∅ ∅ r run
  have collision := treeSimHashProgram_not_budgetCollision prims K circuits settings
    top tree D A x z Z r run good
  obtain ⟨S,size,cover⟩ := treeHashBudget_setup_logged_cover prims D A x z p hp
  obtain ⟨T,sizeT,coverT⟩ := post positive top tree D A x z Z dealt p hp after ha
    (by simpa only [state] using coherent) (by simpa only [state] using collision)
  refine ⟨S ∪ T, ?_, ?_⟩
  · calc
      (S ∪ T).card ≤ S.card+T.card := Finset.card_union_le _ _
      _ ≤ C.n*(termCount C+C.n)+C.n^2 + treeBatches settings tree *
          ((C.n+3)*termCount C+maxBatch circuits settings (fun jobs => halvings (tupleCount jobs))+2) :=
        Nat.add_le_add size sizeT
      _ = treeSecrets circuits settings C tree-2*prssKeyCount C := by
        rw [treeHashBudget_capacity]
        ring
  · have total := cover.union_trans coverT
    rw [state] at total
    intro t h ht hh
    exact (total t h ht hh).resolve_left (by simp)

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_normalized_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_normalized_setup

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_honest_of_postSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_honest_of_postSetup

end NormalizedAssembly

-- A75_NORMALIZED_ASSEMBLY_END

-- A75_SETUP_ASSEMBLY_BEGIN
section SetupAssembly
variable (prims : Primitives) (circuits : Circuits) (settings : Settings)

/-- Complete absent setup contexts with rejecting pure gates, preserving
all actual local starts and supplying common parameters and held keys. -/
theorem treeHashBudget_setup_contexts (D : C.Coalition) (x : C.Party → Keys C)
    (parameter : PublicParameter) (parameters : ∀ i, i ∉ D.1 → (x i).parameter = parameter)
    (setup : C.Party → Option (PrssKeys C)) (corrupt : ∀ i, i ∈ D.1 → setup i = none)
    (agreement : ∀ i j ki kj, setup i = some ki → setup j = some kj →
      ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.term T = kj.term T)
    (top : TopTree) (tree : Tree) :
    ∃ (ctx : C.Party → Context C)
      (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      (∀ i, IsQueryBoundP (gate i) TreeSimHashCount.Region 0) ∧
      (∀ i, (ctx i).self = i) ∧
      (∀ i, (ctx i).keys.parameter = parameter) ∧
      Consistent D (fun i T => (ctx i).prss.term T) ∧
      free (Concrete.sequenceFin fun i => continueStep
        (fun pi => treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, pi⟩ top tree)
        (.done (setup i))) =
      startSteps worldRoles D (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
        treeSimCheckAfterSetupAudit K circuits settings (ctx i) top tree) := by
  have shared : ∀ T : C.Term, ∃ key : HashOutput, ∀ i pi,
      i ∉ D.1 → setup i = some pi → i ∈ C.holders T → pi.term T = key := by
    intro T
    by_cases present : ∃ i pi, i ∉ D.1 ∧ setup i = some pi ∧ i ∈ C.holders T
    · obtain ⟨i, pi, hi, hpi, held⟩ := present
      exact ⟨pi.term T, fun j pj _ hpj hj => agreement j i pj pi hpj hpi T hj held⟩
    · exact ⟨0, fun i pi hi hpi held => (present ⟨i, pi, hi, hpi, held⟩).elim⟩
  choose commonTerm common using shared
  let fallback : PrssKeys C := ⟨commonTerm, fun _ => 0⟩
  let ctx : C.Party → Context C := fun i =>
    ⟨i, { x i with parameter := parameter }, (setup i).getD fallback⟩
  let gate : C.Party → OracleComp (LocalSpec C) (Option Unit) :=
    fun i => pure ((setup i).map fun _ => ())
  have held (i : C.Party) (hi : i ∉ D.1) (T : C.Term) (hT : i ∈ C.holders T) :
      (ctx i).prss.term T = commonTerm T := by
    cases hpi : setup i with
    | none => simp only [ctx, hpi, Option.getD_none, fallback]
    | some pi =>
      simpa only [ctx, hpi, Option.getD_some] using common T i pi hi hpi hT
  have actual (i : C.Party) (hi : i ∉ D.1) (pi : PrssKeys C) (hpi : setup i = some pi) :
      ctx i = ⟨i, x i, pi⟩ := by
    dsimp only [ctx]
    rw [hpi, Option.getD_some, ← parameters i hi]
  refine ⟨ctx, gate, (fun _ => isQueryBoundP_pure _ _ _), fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro T i hi j hj honestI honestJ
    exact (held i honestI T hi).trans (held j honestJ T hj).symm
  · unfold startSteps
    rw [free_sequenceFin]
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, corrupt i hi, continueStep, free_pure]
    · rw [if_neg hi]
      cases hpi : setup i with
      | none =>
        simp [gate, hpi, continueStep, treeLockstepLocalPrelude, localStep, advance_pure, free_pure]
      | some pi =>
        simp [gate, hpi, continueStep, treeLockstepLocalPrelude, localStep, worldRoles,
          actual i hi pi hpi]

/-- Every hash reply of a supported run from the empty log agrees with its
actual terminal hash interpretation, including the public tweakable hashes. -/
theorem treeHashBudget_logged_hashes {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (cache : HashCache C × HiddenCache C)
    (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run (cache, []))) :
    ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ r.2.2 →
      TreeSimCheckWorldHashes (hashOf prims r.2.1.1) t u := by
  rw [treeSimLoggedWorld_run, support_map] at run
  obtain ⟨⟨⟨a, log⟩, final⟩, raw, rfl⟩ := run
  simpa only [List.nil_append] using (treeSimCheck_logged_hashes prims D p cache a log final raw).2

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_setup_contexts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_setup_contexts

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_logged_hashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_logged_hashes

set_option maxRecDepth 3000 in
set_option linter.constructorNameAsVariable false in
/-- A cover for the actual gated ceremony phase gives the original honest
budget, including setup, the final distinguisher and normalized execution. -/
theorem treeHashBudget_honest_of_afterSetup
    (phase : 0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
      (ctx : C.Party → Context C), (∀ i, (ctx i).self = i) →
      ∀ parameter, (∀ i, (ctx i).keys.parameter = parameter) →
      Consistent D (fun i T => (ctx i).prss.term T) →
      ∀ (gate : C.Party → OracleComp (LocalSpec C) (Option Unit)),
      (∀ i, IsQueryBoundP (gate i) TreeSimHashCount.Region 0) →
      ∀ (log : TreeSimLog C) (hash : HashCache C), TreeSimHashCoherent hash log →
      ¬ TreeSimHashBudgetCollision log →
      (∀ t u, (⟨t,u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log →
        TreeSimCheckWorldHashes (hashOf prims hash) t u) →
      ∀ (s : TreeSimState C)
      (r : (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C)))) × TreeSimState C),
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality
          (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode)) state
          (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
            treeSimCheckAfterSetupAudit K circuits settings (ctx i) top tree))).run s) →
      r.2.2 ⊆ log →
      ∃ T : Finset (Query C), T.card ≤ treeBatches settings tree * ((C.n+3)*termCount C+
        maxBatch circuits settings (fun jobs => halvings (tupleCount jobs))+2) ∧
        TreeHashBudgetRegionCover T s.2 r.2.2) :
    TreeSimHashHonestBudget prims K circuits settings := by
  apply treeHashBudget_honest_of_postSetup K prims circuits settings
  intro positive top tree D A x z Z dealt setup hs after ha coherent good
  have full : after ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (treeSimCheckAuditedGame K circuits settings top tree D A x z Z)).run ((∅,∅),[])) := by
    rw [treeHashBudget_audit_setup_run K prims circuits settings]
    exact (mem_support_bind_iff _ _ _).mpr ⟨setup, hs, ha⟩
  have rows := treeHashBudget_logged_hashes prims D _ _ after full
  have goodSetup : ¬ TreeSimHashBudgetCollision setup.2.2 := by
    intro collision
    exact good (treeSimHashBudgetCollision_mono
      (treeSimLoggedWorld_prefix prims D _ setup.2 after ha) collision)
  have agree := treeAgreementSetupKeys (E := E) prims D A x z setup hs goodSetup
  have corrupt : ∀ i, i ∈ D.1 → setup.1.2 i = none := by
    have hs' := hs
    simp only [treeSaltSetup, mem_support_bind_iff] at hs'
    obtain ⟨start, _, hs'⟩ := hs'
    exact treeSetup_corrupt_none prims D A start.1 start.2 setup hs'
  obtain ⟨parameter, seeds, pairs, dealt⟩ := dealt
  have parameters : ∀ i, i ∉ D.1 → (x i).parameter = parameter := by
    intro i _
    rw [dealt i]
    rfl
  obtain ⟨ctx, gate, bound, self, uniform, keys, start⟩ :=
    treeHashBudget_setup_contexts K circuits settings D x parameter parameters setup.1.2 corrupt agree top tree
  unfold auditAfterProgram at ha
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at ha
  obtain ⟨next, hn, out, ho, answer, hz, rfl⟩ := ha
  have phaseRun : out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode)) setup.1.1
        (fun i => treeLockstepLocalPrelude (gate i) >>= fun _ =>
          treeSimCheckAfterSetupAudit K circuits settings (ctx i) top tree))).run setup.2) := by
    unfold executePhase
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    refine ⟨next, ?_, ?_⟩
    · rw [← start]
      exact hn
    · have fuelEq : ceremonyFuel circuits settings - 3 =
          ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode) := by
        unfold ceremonyFuel setupRounds
        omega
      rw [fuelEq] at ho
      with_reducible exact ho
  have final := (treeSimLoggedWorld_prefix prims D _ out.2 answer hz).subset
  obtain ⟨S, size, cover⟩ := phase positive top tree D A setup.1.1 ctx self parameter uniform keys
    gate bound answer.2.2 answer.2.1.1 coherent good rows setup.2 out phaseRun final
  exact ⟨S, size, cover.trans (treeHashBudget_adversary_cover prims D S _ out.2 answer hz).region⟩

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_honest_of_afterSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_honest_of_afterSetup

end SetupAssembly
-- A75_SETUP_ASSEMBLY_END


/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_beforeSalt_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_beforeSalt_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batchAudit_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batchAudit_cover

/-- Every supported normalized ceremony has the stated honest hash budget,
including retained queries from prefixes that abort. -/
theorem treeSimHashHonestBudget (prims : Primitives) (circuits : Circuits) (settings : Settings) :
    TreeSimHashHonestBudget prims K circuits settings := by
  apply treeHashBudget_honest_of_afterSetup K prims circuits settings
  intro _ top tree D A state ctx self parameter parameters keys gate bound log hash coherent good rows s r run final
  have outside (i) (_ : i ∉ D.1) : IsQueryBoundP (gate i)
      (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ (∅ : Finset (Query C)))) 0 := by
    apply IsQueryBoundP.of_imp _ (bound i)
    rintro t ⟨q, hq, eq⟩
    exact treeHashBudget_free_region t ⟨q, hq.1, eq⟩
  obtain ⟨T, size, cover⟩ := treeHashBudget_afterSetup_cover K prims circuits settings D A state
    ctx self parameter parameters keys ∅ gate outside top tree log hash coherent good rows s r run final
  exact ⟨T, size, by simpa only [Finset.empty_union] using cover⟩

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batchPrefix_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batchPrefix_fields

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batchPrefix_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batchPrefix_actual

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batchPrefix_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batchPrefix_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_round_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_round_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_steps_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_steps_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_phase_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_phase_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_coin_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_coin_round

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_coin_partial_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_coin_partial_round

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_open_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_open_boundary

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_coin_start_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_coin_start_shape

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_coin_phase_points' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_coin_phase_points

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_phase_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_phase_cut

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_coin_phase_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_coin_phase_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_coinKey_phase_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_coinKey_phase_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_challenge_phase_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_challenge_phase_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_phase_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_phase_fields

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_challenge_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_challenge_cut

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_challenge_mult_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_challenge_mult_cut

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_challenge_chain_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_challenge_chain_cover


/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_checkpoint_prelude_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_checkpoint_prelude_data

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batch_prelude_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batch_prelude_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batch_split_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batch_split_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_snapshot_zero_attach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_snapshot_zero_attach

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batch_next_reservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batch_next_reservation

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batch_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batch_transition

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batches_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batches_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_batched_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_batched_cover

/-- info: 'ThresholdLeanXmssSecurity.treeSimHashHonestBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHashHonestBudget

end ThresholdLeanXmssSecurity
