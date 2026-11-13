import ThresholdLeanXmssSecurity.Proof.LifetimeTailBridge
import ThresholdLeanXmssSecurity.Proof.LifetimeLegacy

/-!
# The exact path budget of the selected lifetime tail

The external setup and its driver follow the source's ordinary oracle answers.
Free honest setup calls preserve the remaining counted budget on every path.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeTailBudget

open LifetimeRunBoundary LifetimePrfTransportProof LifetimeSetupBridge LifetimeTailBridge
open LifetimeTailDriver LifetimeTailKernel LifetimeEmulatedBudget LifetimeHybridOrder

attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Re-embed the folded lifetime oracle in the counted world copy. -/
def foldMap : QueryImpl (WorldSpec C) (OracleComp (WorldSpec C)) :=
  fun t => worldRoles.adversary (foldWorld t)

/-- Folding and re-embedding commutes with every program continuation. -/
theorem foldMap_simulate {α : Type} (p : OracleComp (WorldSpec C) α) :
    simulateQ foldMap p = worldRoles.adversary (simulateQ foldWorld p) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih, foldMap]
    simp only [worldRoles, liftComp_bind, counted_bind]

/-- A folded query costs at most the original all-party lifetime charge. -/
theorem foldMap_step (t : (WorldSpec C).Domain) :
    IsQueryBoundP (foldMap t) WorldCounted (if LifetimeCounted t then 1 else 0) := by
  apply isQueryBoundP_adversary
  have hq : IsQueryBoundP (OracleComp.lift (OracleSpec.query t)) LifetimeCounted
      (if LifetimeCounted t then 1 else 0) := by
    rw [isQueryBoundP_query_iff]
    intro ht
    simp [ht]
  simpa only [simulateQ_spec_query] using foldWorld_bound _ _ hq

/-- Every counted world call is counted by the lifetime's all-party budget. -/
theorem worldCounted_imp (t : (WorldSpec C).Domain) : WorldCounted t → LifetimeCounted t := by
  rcases t with (t | t) | t
  · rcases t with t | t <;> simp [WorldCounted, LifetimeCounted, Counted]
  · simp [WorldCounted, LifetimeCounted]
  · simp [WorldCounted]

theorem world_bound {α : Type} {p : OracleComp (WorldSpec C) α} {Q : ℕ}
    (hQ : IsQueryBoundP p LifetimeCounted Q) : IsQueryBoundP p WorldCounted Q :=
  IsQueryBoundP.of_imp worldCounted_imp hQ

/-- Port of A161's `bound_replace_tail`: transport the shared prefix one call
at a time while retaining the exact residual source budget. -/
theorem transfer_prefix {α β γ : Type}
    (impl : QueryImpl (WorldSpec C) (OracleComp (WorldSpec C)))
    (hstep : ∀ t, IsQueryBoundP (impl t) WorldCounted (if LifetimeCounted t then 1 else 0))
    (p : OracleComp (WorldSpec C) α) (left : α → OracleComp (WorldSpec C) β)
    (right : α → OracleComp (WorldSpec C) γ)
    (hrest : ∀ a ∈ support p, ∀ q, IsQueryBoundP (left a) LifetimeCounted q →
      IsQueryBoundP (right a) WorldCounted q)
    (Q : ℕ) (hQ : IsQueryBoundP (p >>= left) LifetimeCounted Q) :
    IsQueryBoundP (simulateQ impl p >>= right) WorldCounted Q := by
  induction p using OracleComp.inductionOn generalizing Q with
  | pure a =>
    rw [simulateQ_pure, pure_bind]
    rw [pure_bind] at hQ
    exact hrest a (by simp) Q hQ
  | query_bind t k ih =>
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at hQ
    rw [simulateQ_bind, simulateQ_spec_query, bind_assoc]
    have hk : ∀ a, IsQueryBoundP (simulateQ impl (k a) >>= right) WorldCounted
        (if LifetimeCounted t then Q - 1 else Q) := by
      intro a
      exact ih a (fun b hb => hrest b ((mem_support_bind_iff _ _ _).mpr
        ⟨a, mem_support_query t a, hb⟩)) _ (hQ.2 a)
    refine (isQueryBoundP_bind (hstep t) (fun a _ => hk a)).mono ?_
    by_cases ht : LifetimeCounted t
    · have hpos : 0 < Q := hQ.1.resolve_left (not_not.mpr ht)
      simp only [if_pos ht]
      omega
    · simp only [if_neg ht]
      omega

/-- Interpret the four-copy source while retaining its stream table. -/
def erase4 (D : C.Coalition) {α : Type} (p : OracleComp (Spec4 C) α)
    (table : StreamCache C) : OracleComp (WorldSpec C) (α × StreamCache C) :=
  (treeSimErase (simulateQ (hybridImpl D) p)).run table

/-- The same prefix as observed by the external setup adversary. -/
def fold4 (D : C.Coalition) {α : Type} (p : OracleComp (Spec4 C) α)
    (table : StreamCache C) : OracleComp (WorldSpec C) (α × StreamCache C) :=
  worldRoles.adversary (localHybrid D p table)

theorem fold4_eq (D : C.Coalition) {α : Type} (p : OracleComp (Spec4 C) α) (table : StreamCache C) :
    fold4 D p table = simulateQ foldMap (erase4 D p table) :=
  (foldMap_simulate _).symm

@[simp] theorem erase4_pure (D : C.Coalition) {α : Type} (a : α) (table : StreamCache C) :
    erase4 D (pure a) table = pure (a, table) := by
  simp only [erase4, simulateQ_pure, treeSimErase_pure, StateT.run_pure]

theorem erase4_bind (D : C.Coalition) {α β : Type} (p : OracleComp (Spec4 C) α)
    (k : α → OracleComp (Spec4 C) β) (table : StreamCache C) :
    erase4 D (p >>= k) table = erase4 D p table >>= fun r => erase4 D (k r.1) r.2 := by
  simp only [erase4, simulateQ_bind, treeSimErase_bind, StateT.run_bind]

theorem erase4_map (D : C.Coalition) {α β : Type} (f : α → β)
    (p : OracleComp (Spec4 C) α) (table : StreamCache C) :
    erase4 D (f <$> p) table = (fun r => (f r.1, r.2)) <$> erase4 D p table := by
  simp only [map_eq_bind_pure_comp, erase4_bind, erase4_pure, Function.comp_def]

theorem erase4_target (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α)
    (table : StreamCache C) :
    erase4 D (targetCopy4 p) table = (fun a => (a, table)) <$> free p := by
  unfold erase4
  rw [impl4_targetCopy_free, LifetimeKeygenHopProof.erase_base_honest]
  rfl

theorem erase4_support (D : C.Coalition) {α : Type} (p : OracleComp (Spec4 C) α)
    (table : StreamCache C) (r : α × StreamCache C) (hr : r ∈ support (erase4 D p table)) :
    r.1 ∈ support p := by
  change r ∈ support (Prod.fst <$> ((simulateQ (hybridImpl D) p).run table).run) at hr
  rw [support_map, Set.mem_image] at hr
  obtain ⟨out, hout, he⟩ := hr
  exact he ▸ support_emulation (hybridImpl D) p table out hout

/-- The identity prefix also preserves the residual lifetime allowance. -/
theorem keep_prefix {α β γ : Type} (p : OracleComp (WorldSpec C) α)
    (left : α → OracleComp (WorldSpec C) β) (right : α → OracleComp (WorldSpec C) γ)
    (hrest : ∀ a ∈ support p, ∀ q, IsQueryBoundP (left a) LifetimeCounted q →
      IsQueryBoundP (right a) WorldCounted q)
    (Q : ℕ) (hQ : IsQueryBoundP (p >>= left) LifetimeCounted Q) :
    IsQueryBoundP (p >>= right) WorldCounted Q := by
  have hstep : ∀ t : (WorldSpec C).Domain,
      IsQueryBoundP (QueryImpl.id' (WorldSpec C) t) WorldCounted
        (if LifetimeCounted t then 1 else 0) := by
    intro t
    apply world_bound
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query t)) LifetimeCounted _
    rw [isQueryBoundP_query_iff]
    intro ht
    simp [ht]
  simpa only [simulateQ_id'] using transfer_prefix (QueryImpl.id' _) hstep p left right hrest Q hQ

/-- The counted external prefix uses the same source answers and residual budget. -/
theorem fold4_prefix (D : C.Coalition) {α β γ : Type} (p : OracleComp (Spec4 C) α)
    (table : StreamCache C) (left : α × StreamCache C → OracleComp (WorldSpec C) β)
    (right : α × StreamCache C → OracleComp (WorldSpec C) γ)
    (hrest : ∀ r ∈ support (erase4 D p table), ∀ q,
      IsQueryBoundP (left r) LifetimeCounted q → IsQueryBoundP (right r) WorldCounted q)
    (Q : ℕ) (hQ : IsQueryBoundP (erase4 D p table >>= left) LifetimeCounted Q) :
    IsQueryBoundP (fold4 D p table >>= right) WorldCounted Q := by
  rw [fold4_eq]
  exact transfer_prefix foldMap foldMap_step _ left right hrest Q hQ

@[simp] theorem fold4_pure (D : C.Coalition) {α : Type} (a : α) (table : StreamCache C) :
    fold4 D (pure a) table = pure (a, table) := by
  simp only [fold4_eq, erase4_pure, simulateQ_pure]

theorem fold4_bind (D : C.Coalition) {α β : Type} (p : OracleComp (Spec4 C) α)
    (k : α → OracleComp (Spec4 C) β) (table : StreamCache C) :
    fold4 D (p >>= k) table = fold4 D p table >>= fun r => fold4 D (k r.1) r.2 := by
  simp only [fold4_eq, erase4_bind, simulateQ_bind]

theorem fold4_map (D : C.Coalition) {α β : Type} (f : α → β)
    (p : OracleComp (Spec4 C) α) (table : StreamCache C) :
    fold4 D (f <$> p) table = (fun r => (f r.1, r.2)) <$> fold4 D p table := by
  simp only [map_eq_bind_pure_comp, fold4_bind, fold4_pure, Function.comp_def]

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (n : ℕ)

/-- The source tail in ordinary world roles. -/
def sourceTail (ob : Option (Boundary C E)) : OracleComp (WorldSpec C) Bool :=
  simulateQ tailMap (tail4 K circuits settings attempts D n ob)

/-- The driver tail ignores its private setup stream table. -/
def driverTail (held : Option (Held C E)) (rows : Option (RevealRows C)) : OracleComp (WorldSpec C) Bool :=
  (lifeDriver K circuits settings attempts D n seedOf).tail K circuits settings ((held, ∅), rows)

omit [Fintype E] [DecidableEq E] in
@[simp] theorem driverTail_none (rows : Option (RevealRows C)) :
    driverTail K circuits settings attempts D n none rows = pure false := by
  cases rows <;> rfl

omit [Fintype E] [DecidableEq E] in
@[simp] theorem driverTail_noRows (held : Option (Held C E)) :
    driverTail K circuits settings attempts D n held none = pure false := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The hybrid source and the log-erased setup plus mapped tail are exactly the
same world computation, before evaluating any ordinary oracle answer. -/
theorem source_full_eq (A : LifetimeAdversary C E) :
    (worldSetup K circuits settings attempts D n A >>= worldTail K circuits settings attempts D n) =
      (erase4 D (setup4 K circuits settings attempts D n A) ∅ >>= fun r =>
        sourceTail K circuits settings attempts D n r.1) := by
  change (worldSetup K circuits settings attempts D n A >>= _) =
    (Prod.fst <$> worldSetup K circuits settings attempts D n A >>= _)
  rw [bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro r hr
  exact worldTail_eq K circuits settings attempts D n A r.1.1
    (support_emulation (hybridImpl D) _ ∅ r hr) r.1.2 r.2

/-- The external reveal samples honest rows freely after its counted public segment. -/
def revealWorld (held : Held C E) (inbox : Sent C E) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (table : StreamCache C) :
    OracleComp (WorldSpec C) Bool := do
  let (out, _) ← fold4 D (resume4 K circuits settings attempts D n held inbox) table
  let rows ← free (prssRevealRows D active parts committed out.2)
  driverTail K circuits settings attempts D n out.1 (some rows)

/-- Both external setup rounds followed by the exact driver tail. -/
def finishWorld (state : Option (Held C E)) (data : C.Party → Parts C × List HashOutput)
    (table : StreamCache C) : OracleComp (WorldSpec C) Bool := do
  let (out, _) ← fold4 D (earlyRounds4 K circuits settings attempts D n state data) table
  match out.2.2 with
  | none => driverTail K circuits settings attempts D n out.1 none
  | some sent' => do
      let rows ← free (prssRevealRows D (prssCommitActive D out.2.1) (fun i => (data i).1)
        (prssCommitInbox D data out.2.1) sent')
      driverTail K circuits settings attempts D n out.1 (some rows)

/-- The external setup after the lifetime prefix has chosen a start or stopped. -/
def afterStartWorld (before : Option (BeforeStart C E)) (table : StreamCache C) :
    OracleComp (WorldSpec C) Bool := do
  let data ← free (prssInitialData D)
  finishWorld K circuits settings attempts D n (holdStart circuits settings attempts D n before) data table

set_option backward.isDefEq.respectTransparency false in
/-- Expanding the actual external setup gives the folded lifetime prefix, then
free honest setup passes and the same held continuation. -/
theorem driver_full_eq (A : LifetimeAdversary C E) (x : C.Party → Keys C) (z : Aux) :
    (setupPrefix D (boundaryAdv K circuits settings attempts D n A) x z >>=
      (lifeDriver K circuits settings attempts D n seedOf).tail K circuits settings) =
    (fold4 D (beforeStart4 K circuits settings attempts D n A) ∅ >>= fun r =>
      afterStartWorld K circuits settings attempts D n r.1 r.2) := by
  unfold setupPrefix
  simp only [bind_assoc]
  change (fold4 D (prefix4 K circuits settings attempts D n A) ∅ >>= _) = _
  erw [prefix4_eq, fold4_map, bind_map_left]
  unfold afterStartWorld
  apply bind_congr
  intro r
  apply bind_congr
  intro data
  rw [boundary_earlyRounds]
  unfold finishWorld
  simp only [fold4, worldRoles, liftComp_map, counted, simulateQ_map, bind_map_left]
  apply bind_congr
  intro out
  cases out.1.2.2 with
  | none =>
    simp only [pure_bind, driverTail]
    exact driver_tail_table K circuits settings attempts D n _ none _ ∅
  | some sent =>
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro rows
    exact driver_tail_table K circuits settings attempts D n _ (some rows) _ ∅

omit [Fintype E] [DecidableEq E] in
/-- With no held lifetime continuation, every externally scheduled setup call is free. -/
theorem finishWorld_none (data : C.Party → Parts C × List HashOutput) (table : StreamCache C) :
    IsQueryBoundP (finishWorld K circuits settings attempts D n none data table) WorldCounted 0 := by
  unfold finishWorld earlyRounds4
  simp only [round4, pure_bind]
  split
  · simp only [fold4_pure, pure_bind, driverTail_noRows]
    exact isQueryBoundP_pure _ _ _
  · simp only [pure_bind, fold4_pure, driverTail_none]
    exact (isQueryBoundP_bind (isQueryBoundP_free _ 0)
      (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)

omit [Fintype E] [DecidableEq E] in
/-- An unadmitted start spends no counted query after the actual lifetime prefix. -/
theorem afterStartWorld_dead (before : Option (BeforeStart C E))
    (hdead : holdStart circuits settings attempts D n before = none) (table : StreamCache C) :
    IsQueryBoundP (afterStartWorld K circuits settings attempts D n before table) WorldCounted 0 := by
  unfold afterStartWorld
  rw [hdead]
  exact (isQueryBoundP_bind (isQueryBoundP_free _ 0)
    (fun data _ => finishWorld_none K circuits settings attempts D n data table)).mono (by omega)

set_option backward.isDefEq.respectTransparency false in
/-- The reveal uses the source's exact residual allowance, including its full tail. -/
theorem reveal_bound (held : Held C E) (inbox : Sent C E)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (active : C.Party → Prop) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (hc : CountIs (n + 1) st) (hv : visibleState st = held.state)
    (hk : k = cont K circuits settings held.keys st tree)
    (hs : st.running = some (tree, ceremonyFuel circuits settings - 1,
      fun i => suspendStep (k i) (prssRevealStep D active parts committed i)))
    (table : StreamCache C) (Q : ℕ)
    (hQ : IsQueryBoundP
      (erase4 D (revealSegment K circuits settings attempts D n held.keys held.h k active parts committed
        (held.continuation (some inbox)) st) table >>= fun r =>
        sourceTail K circuits settings attempts D n (some ⟨held.keys, held.h, r.1.1.1, r.1.1.2, r.1.2⟩))
      LifetimeCounted Q) :
    IsQueryBoundP (revealWorld K circuits settings attempts D n held inbox active parts committed table)
      WorldCounted Q := by
  rw [revealSegment_running K circuits settings attempts D n held.keys held.h k active parts committed
    (held.continuation (some inbox)) st tree _ hc hs,
    runTo_reconstruct K circuits settings attempts D n held.keys held.h
      (held.continuation (some inbox)) st tree _ _ hs, hv] at hQ
  simp only [bind_map_left, erase4_bind, bind_assoc] at hQ
  unfold revealWorld
  rw [resume4_map, fold4_map, bind_map_left]
  refine fold4_prefix D _ table _ _ ?_ Q hQ
  intro r hr q hq
  have hr' := erase4_support D _ table r hr
  have hrun : (held.state.restore : LifetimeState C E).running =
      some (tree, ceremonyFuel circuits settings - 1, fun _ => .done none) := by
    rw [← hv]
    simp [VisibleState.restore, visibleState, hs]
  have hf := runTo_frame K circuits settings attempts D n held.keys held.h
    (held.continuation (some inbox)) held.state.restore (by rw [hrun]; simp) r.1 hr'
  have hcount : CountIs (n + 1) r.1.2 := by
    change r.1.2.runCount = n + 1
    rw [hf.1, ← hv]
    exact hc
  have hrunning := hf.2.trans hrun
  have htop := runTo_top K circuits settings attempts D n held.keys held.h
    (held.continuation (some inbox)) held.state.restore (by rw [hrun]; simp) r.1 hr'
  have hkt : k = cont K circuits settings held.keys r.1.2 tree := by
    rw [hk]
    funext i prss
    simp only [cont, htop, ← hv, VisibleState.restore, visibleState]
  cases hp : r.1.1 with
  | done f =>
    simp only [resumed, hp, Pause.atRound, driverTail_none]
    exact (isQueryBoundP_bind (isQueryBoundP_free _ 0)
      (fun _ _ => isQueryBoundP_pure _ _ q)).mono (by omega)
  | wait query next =>
    cases query <;> simp only [resumed, hp, Pause.atRound, driverTail_none]
    all_goals try { exact (isQueryBoundP_bind (isQueryBoundP_free _ 0)
      (fun _ _ => isQueryBoundP_pure _ _ q)).mono (by omega) }
    rename_i sent
    simp only [hp, Pause.atRound, erase4_bind, erase4_target, bind_map_left,
      erase4_pure, bind_assoc, pure_bind] at hq
    refine keep_prefix _ _ _ ?_ q hq
    intro rows _ tailQ htail
    apply world_bound
    simp only [driverTail, hrunning, Option.map_some, Nat.sub_sub]
    rw [driver_tail_reveal K circuits settings attempts D n held.keys held.h next
      r.1.2 tree hcount rows (∅ : StreamCache C)]
    simpa only [sourceTail, hkt, replaceSteps, cont, Nat.sub_sub] using htail

/-- A live held start, expanded into its two public segments and honest reveal. -/
def commitWorld (held : Held C E) (data : C.Party → Parts C × List HashOutput)
    (table : StreamCache C) : OracleComp (WorldSpec C) Bool := do
  let (out, table') ← fold4 D (resume4 K circuits settings attempts D n held (prssCommitVisible D data)) table
  if ∀ i, i ∉ D.1 → ¬ prssCommitActive D out.2 i then driverTail K circuits settings attempts D n out.1 none else do
  let (next, _) ← fold4 D (round4 K circuits settings attempts D n out.1
    (prssRevealVisible D (prssCommitActive D out.2) (fun i => (data i).1))) table'
  let rows ← free (prssRevealRows D (prssCommitActive D out.2) (fun i => (data i).1)
    (prssCommitInbox D data out.2) next.2)
  driverTail K circuits settings attempts D n next.1 (some rows)

omit [Fintype E] [DecidableEq E] in
set_option backward.isDefEq.respectTransparency false in
theorem finishWorld_some (held : Held C E) (data : C.Party → Parts C × List HashOutput)
    (table : StreamCache C) :
    finishWorld K circuits settings attempts D n (some held) data table =
      commitWorld K circuits settings attempts D n held data table := by
  unfold finishWorld earlyRounds4 commitWorld
  rw [round4, fold4_bind, bind_assoc]
  apply bind_congr
  rintro ⟨⟨state, sent⟩, table'⟩
  dsimp only
  by_cases hall : ∀ i, i ∉ D.1 → ¬ prssCommitActive D sent i
  · simp only [if_pos hall, fold4_pure, pure_bind]
  · simp only [if_neg hall, fold4_bind, bind_assoc]
    apply bind_congr
    rintro ⟨⟨state', sent'⟩, table''⟩
    rw [fold4_pure, pure_bind]

set_option backward.isDefEq.respectTransparency false in
/-- The commit and reveal consume their one shared residual lifetime allowance. -/
theorem commit_bound (held : Held C E) (data : C.Party → Parts C × List HashOutput)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (hc : CountIs (n + 1) st) (hv : visibleState st = held.state)
    (hk : k = cont K circuits settings held.keys st tree)
    (hs : st.running = some (tree, ceremonyFuel circuits settings,
      fun i => suspendStep (k i) (prssInitialSteps D data i)))
    (table : StreamCache C) (Q : ℕ)
    (hQ : IsQueryBoundP
      (erase4 D (commitSegment K circuits settings attempts D n held.keys held.h k data
        (held.continuation (some (prssCommitVisible D data))) st) table >>= fun r =>
        sourceTail K circuits settings attempts D n (some ⟨held.keys, held.h, r.1.1.1, r.1.1.2, r.1.2⟩))
      LifetimeCounted Q) :
    IsQueryBoundP (commitWorld K circuits settings attempts D n held data table) WorldCounted Q := by
  rw [commitSegment_running K circuits settings attempts D n held.keys held.h k data
    (held.continuation (some (prssCommitVisible D data))) st tree _ hc hs,
    runTo_reconstruct K circuits settings attempts D n held.keys held.h
      (held.continuation (some (prssCommitVisible D data))) st tree _ _ hs, hv] at hQ
  simp only [bind_map_left, erase4_bind, bind_assoc] at hQ
  unfold commitWorld resume4
  rw [fold4_bind, bind_assoc]
  refine fold4_prefix D _ table _ _ ?_ Q hQ
  intro r hr q hq
  have hr' := erase4_support D _ table r hr
  have hrun : (held.state.restore : LifetimeState C E).running =
      some (tree, ceremonyFuel circuits settings, fun _ => .done none) := by
    rw [← hv]
    simp [VisibleState.restore, visibleState, hs]
  have hf := runTo_frame K circuits settings attempts D n held.keys held.h
    (held.continuation (some (prssCommitVisible D data))) held.state.restore
    (by rw [hrun]; simp) r.1 hr'
  have hcount : CountIs (n + 1) r.1.2 := by
    change r.1.2.runCount = n + 1
    rw [hf.1, ← hv]
    exact hc
  have hrunning := hf.2.trans hrun
  have htop := runTo_top K circuits settings attempts D n held.keys held.h
    (held.continuation (some (prssCommitVisible D data))) held.state.restore
    (by rw [hrun]; simp) r.1 hr'
  have hkt : k = cont K circuits settings held.keys r.1.2 tree := by
    rw [hk]
    funext i prss
    simp only [cont, htop, ← hv, VisibleState.restore, visibleState]
  cases hp : r.1.1 with
  | done f =>
    simp only [hp, Pause.atRound, fold4_pure, pure_bind]
    split
    · simp only [driverTail_noRows]; exact isQueryBoundP_pure _ _ _
    · simp only [round4, fold4_pure, pure_bind, driverTail_none]
      exact (isQueryBoundP_bind (isQueryBoundP_free _ 0)
        (fun _ _ => isQueryBoundP_pure _ _ q)).mono (by omega)
  | wait query next =>
    cases query <;> simp only [hp, Pause.atRound, fold4_pure, pure_bind]
    all_goals try {
      split
      · simp only [driverTail_noRows]; exact isQueryBoundP_pure _ _ _
      · simp only [round4, fold4_pure, pure_bind, driverTail_none]
        exact (isQueryBoundP_bind (isQueryBoundP_free _ 0)
          (fun _ _ => isQueryBoundP_pure _ _ q)).mono (by omega) }
    rename_i sent
    simp only [hp, Pause.atRound] at hq
    have ha : (fun i => (C.parties.any fun j =>
        Msg.isAbort (prssCommitInbox D data sent i j)) = false) = prssCommitActive D sent :=
      funext (prssCommitInbox_active D data sent)
    rw [ha] at hq
    by_cases hall : ∀ i, i ∉ D.1 → ¬ prssCommitActive D sent i
    · rw [if_pos hall, driverTail_noRows]
      exact isQueryBoundP_pure _ _ _
    · rw [if_neg hall, round4]
      rw [settle_commit_active circuits settings D _ tree data sent k hall, reveal_visible D] at hq
      exact reveal_bound K circuits settings attempts D n
        ⟨held.keys, held.h, next,
          { visibleState r.1.2 with running := r.1.2.running.map fun r => (r.1, r.2.1 - 1) }⟩
        _ k (prssCommitActive D sent) (fun i => (data i).1) (prssCommitInbox D data sent)
        ({ replaceSteps (fun i => suspendStep (k i) (prssInitialSteps D data i)) r.1.2 with
          running := some (tree, ceremonyFuel circuits settings - 1,
            fun i => suspendStep (k i) (prssRevealStep D (prssCommitActive D sent)
              (fun j => (data j).1) (prssCommitInbox D data sent) i)) } : LifetimeState C E)
        tree hcount (visible_advance r.1.2 tree _ _ _ hrunning) hkt rfl r.2 q hq

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The selected setup and continuation share exactly the source allowance;
an unadmitted external setup has zero counted cost. -/
theorem afterStart_bound (before : Option (BeforeStart C E)) (table : StreamCache C) (Q : ℕ)
    (hQ : IsQueryBoundP
      (erase4 D (setupAfterStart4 K circuits settings attempts D n before) table >>= fun r =>
        sourceTail K circuits settings attempts D n r.1) LifetimeCounted Q) :
    IsQueryBoundP (afterStartWorld K circuits settings attempts D n before table) WorldCounted Q := by
  by_cases hdead : holdStart circuits settings attempts D n before = none
  · exact (afterStartWorld_dead K circuits settings attempts D n before hdead table).mono (by omega)
  · cases before with
    | none => exact False.elim (hdead rfl)
    | some before =>
      cases hp : before.pause with
      | done f => exact False.elim (hdead (by simp [holdStart, hp, Pause.atStart]))
      | wait query next =>
        cases query <;> simp only [holdStart, hp, Pause.atStart] at hdead
        all_goals try { exact False.elim (hdead trivial) }
        rename_i tree
        by_cases hstart : LifetimeProof.canStart attempts D before.state tree ∧ CountIs n before.state
        · unfold setupAfterStart4 at hQ
          simp only [hp, Pause.atStart, if_pos hstart, bind_assoc, erase4_bind,
            erase4_target, bind_map_left] at hQ
          unfold afterStartWorld
          simp only [holdStart, hp, Pause.atStart, if_pos hstart]
          refine keep_prefix _ _ _ ?_ Q hQ
          intro data _ q hq
          rw [finishWorld_some]
          rw [settle_initial circuits settings D, initial_visible D] at hq
          have hc : CountIs (n + 1)
              ({ LifetimeProof.increment before.state tree with
                running := some (tree, ceremonyFuel circuits settings,
                  fun i => suspendStep (cont K circuits settings before.keys before.state tree i)
                    (prssInitialSteps D data i)) } : LifetimeState C E) := by
            change (LifetimeProof.increment before.state tree).runCount = n + 1
            rw [LifetimeProof.increment_runCount]
            exact congrArg (fun x => x + 1) hstart.2
          have htop : (LifetimeProof.increment before.state tree).top = before.state.top := by
            cases tree <;> rfl
          have hk : cont K circuits settings before.keys before.state tree =
              cont K circuits settings before.keys
                ({ LifetimeProof.increment before.state tree with
                  running := some (tree, ceremonyFuel circuits settings,
                    fun i => suspendStep (cont K circuits settings before.keys before.state tree i)
                      (prssInitialSteps D data i)) } : LifetimeState C E) tree := by
            funext i prss
            simp only [cont, htop]
          apply commit_bound K circuits settings attempts D n
            ⟨before.keys, before.h, next, visibleState (E := E)
              { LifetimeProof.increment before.state tree with
                running := some (tree, ceremonyFuel circuits settings, fun _ => .done none) }⟩
            data (cont K circuits settings before.keys before.state tree)
            ({ LifetimeProof.increment before.state tree with
              running := some (tree, ceremonyFuel circuits settings,
                fun i => suspendStep (cont K circuits settings before.keys before.state tree i)
                  (prssInitialSteps D data i)) } : LifetimeState C E)
            tree hc rfl hk rfl table q
          simpa only [erase4_bind, erase4_pure, bind_assoc, pure_bind] using hq
        · exact False.elim (hdead (by simp [if_neg hstart]))

/-- Exact-Q transport from the all-answer hybrid budget to the full external
setup and the actual lifetime continuation. -/
theorem driver_bound_of_hybrid (A : LifetimeAdversary C E) (Q : ℕ)
    (hQ : IsQueryBoundP (emulationGame (lifetimeGameWith K circuits settings attempts
      (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A)) LifetimeCounted Q)
    (x : C.Party → Keys C) (z : Aux) :
    IsQueryBoundP
      (setupPrefix D (boundaryAdv K circuits settings attempts D n A) x z >>=
        (lifeDriver K circuits settings attempts D n seedOf).tail K circuits settings)
      WorldCounted Q := by
  rw [hybrid_split, source_full_eq, setup4_beforeStart, erase4_bind, bind_assoc] at hQ
  rw [driver_full_eq]
  refine fold4_prefix D _ ∅ _ _ ?_ Q hQ
  intro r _ q hq
  exact afterStart_bound K circuits settings attempts D n r.1 r.2 q hq

/-- The original real-lifetime query premise bounds every path of the selected
setup and lifetime driver at exactly Q, for every values, x and z. -/
theorem lifetime_tail_budget (circuitsOf : (HashInput → HashOutput) → Circuits)
    (A : LifetimeAdversary C E) (Q : ℕ)
    (hQ : HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q)
    (values : MpcDomain → HashOutput) (x : C.Party → Keys C) (z : Aux) :
    IsQueryBoundP
      (setupPrefix D (boundaryAdv K (circuitsOf (thOf values)) settings attempts D n A) x z >>=
        (lifeDriver K (circuitsOf (thOf values)) settings attempts D n seedOf).tail
          K (circuitsOf (thOf values)) settings)
      WorldCounted Q :=
  driver_bound_of_hybrid K (circuitsOf (thOf values)) settings attempts D n A Q
    (LifetimeRealBad.hybridBudget_of_real K (circuitsOf (thOf values)) settings attempts D A Q n
      (hQ values)) x z

end ThresholdLeanXmssSecurity.LifetimeTailBudget

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBudget.transfer_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBudget.transfer_prefix

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBudget.source_full_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBudget.source_full_eq

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBudget.driver_full_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBudget.driver_full_eq

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBudget.reveal_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBudget.reveal_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBudget.commit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBudget.commit_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBudget.afterStart_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBudget.afterStart_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBudget.driver_bound_of_hybrid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBudget.driver_bound_of_hybrid

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailBudget.lifetime_tail_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeTailBudget.lifetime_tail_budget
