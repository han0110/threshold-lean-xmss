import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Rename
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.TopCosts
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Hops

/-!
# The game with a permuted table of fresh keys

`keyParametric` proves `UsedHit.KeyParametric`. The game with the table `σ ∘ F` is the game with the
table `F` in which each honest call of `PRG` under a hidden name has the key `σ key`. The proof follows
the game from each state whose runs are at most `runLimit` (`RunsInv`). An allowed run of a tree then
takes its slots below `gameSetups` (`setupsBefore_add_le`), so each of its ceremonies has fresh keys of
the table, and `slotProgram_rename` applies. `Grows` states that the runs only grow and keep this bound.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

open UsedHit

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## The runs of the trees grow -/

section Grow

variable (runLimit : ℕ)

variable {S : Type}

/-- The runs of `s'` are at least the runs of `s`, and they are at most `runLimit` when the runs of
`s` are. -/
def RunsGrow (s s' : RealState C S) : Prop :=
  (∀ t, s.runs t ≤ s'.runs t) ∧ ((∀ t, s.runs t ≤ runLimit) → ∀ t, s'.runs t ≤ runLimit)

/-- Each end of `x` from `s` has runs that grow from `s`. -/
def Grows {α : Type} (x : RealM C S α) : Prop := ∀ s, ∀ r ∈ support (x.run s), RunsGrow runLimit s r.2

/-- Each end of `x` from `s` has at least the runs of `s`. -/
def Ups {α : Type} (x : RealM C S α) : Prop := ∀ s, ∀ r ∈ support (x.run s), ∀ t, s.runs t ≤ r.2.runs t

theorem Grows.ups {α : Type} {x : RealM C S α} (h : Grows runLimit x) : Ups x := fun s r hr => (h s r hr).1

theorem ups_bind {α β : Type} {x : RealM C S α} {f : α → RealM C S β} (hx : Ups x) (hf : ∀ a, Ups (f a)) :
    Ups (x >>= f) := by
  intro s r hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨y, hy, hr⟩ := hr
  exact fun t => (hx s y hy t).trans (hf y.1 y.2 r hr t)

theorem runsGrow_refl (s : RealState C S) : RunsGrow runLimit s s := ⟨fun _ => le_rfl, id⟩

theorem RunsGrow.trans {s s' s'' : RealState C S} (h : RunsGrow runLimit s s') (h' : RunsGrow runLimit s' s'') :
    RunsGrow runLimit s s'' := ⟨fun t => (h.1 t).trans (h'.1 t), fun hs => h'.2 (h.2 hs)⟩

theorem RunsGrow.of_runs {s s' : RealState C S} (h : s'.runs = s.runs) : RunsGrow runLimit s s' :=
  ⟨fun t => by rw [h], fun hs => by rw [h]; exact hs⟩

theorem grows_pure {α : Type} (a : α) : Grows runLimit (pure a : RealM C S α) := by
  intro s r hr
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact runsGrow_refl runLimit s

theorem grows_bind {α β : Type} {x : RealM C S α} {f : α → RealM C S β} (hx : Grows runLimit x)
    (hf : ∀ a, Grows runLimit (f a)) : Grows runLimit (x >>= f) := by
  intro s r hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨y, hy, hr⟩ := hr
  exact (hx s y hy).trans runLimit (hf y.1 y.2 r hr)

theorem grows_lift {α : Type} (x : OracleComp (WorldSpec C) α) :
    Grows runLimit (StateT.lift x : RealM C S α) := by
  intro s r hr
  simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨a, -, rfl⟩ := hr
  exact runsGrow_refl runLimit s

theorem grows_get : Grows runLimit (get : RealM C S (RealState C S)) := by
  intro s r hr
  simp only [StateT.run_get, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact runsGrow_refl runLimit s

theorem grows_get_bind {α : Type} {f : RealState C S → RealM C S α} (hf : ∀ s, Grows runLimit (f s)) :
    Grows runLimit (get >>= f) :=
  grows_bind runLimit (grows_get runLimit) hf

theorem grows_modify (g : RealState C S → RealState C S) (hg : ∀ s, (g s).runs = s.runs) :
    Grows runLimit (modify g : RealM C S Unit) := by
  intro s r hr
  simp only [StateT.run_modify, support_pure, Set.mem_singleton_iff] at hr
  subst hr
  exact RunsGrow.of_runs runLimit (hg s)

theorem setupsBefore_mono {runs runs' : Tree → ℕ} (h : ∀ t, runs t ≤ runs' t) :
    setupsBefore runs ≤ setupsBefore runs' := by
  unfold setupsBefore
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (h _))
    (Finset.sum_le_sum fun b _ => Nat.mul_le_mul_right _ (h _))

theorem setupsBefore_update (runs : Tree → ℕ) (tree : Tree) :
    setupsBefore (Function.update runs tree (runs tree + 1)) = setupsBefore runs + treeSetups tree := by
  unfold setupsBefore
  cases tree with
  | top =>
    simp only [Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne]
    ring
  | bottom b =>
    have hsum : ∑ b' : Fin (2 ^ layerHeight), Function.update runs (.bottom b) (runs (.bottom b) + 1) (.bottom b') *
        treeSetups (.bottom b') =
        ∑ b' : Fin (2 ^ layerHeight), runs (.bottom b') * treeSetups (.bottom b') + treeSetups (.bottom b) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), ← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
      rw [Finset.sum_congr rfl fun b' hb' => by
        rw [Function.update_of_ne (by simpa using (Finset.ne_of_mem_erase hb'))]]
      simp only [Function.update_self]
      ring
    rw [hsum, Function.update_of_ne (by simp)]
    ring

end Grow

/-! ## The run of a tree after its draw and the signing pieces -/

section Shared

variable [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (D : C.Coalition) {S : Type}

/-- The draw of the fresh keys of a slot. -/
abbrev Draw (C : Committee) := ℕ → ProbComp (Option (FreshKeys C))

/-- The lazy draw of the hybrid in which each slot below `gameSetups` has fresh keys. -/
abbrev lazyDraw : Draw C := sampleSlot (gameSetups runLimit)

/-- The draw of the table `F`. -/
abbrev tableDraw (F : Table C (gameSetups runLimit)) : Draw C := fun slot => pure (tableFresh F slot)

/-- The run of `tree` after the draw of its fresh keys. -/
def treeRest (monitor : TreeMonitor C) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) (fresh : List (Option (FreshKeys C))) : RealM C net.State Unit := do
  let (state, outputs) ← StateT.lift (executePhase worldRoles D net noFunctionality (treeFuel circuits settings)
    s.adversary fun i => slotProgram K circuits settings D (fun c => fresh.getD c none) i (s.operators i) tree)
  let bad ← StateT.lift (monitor (fun i => (s.operators i).keys) tree outputs)
  let operators := fun i => (s.operators i).keep (outputs i) tree
  let runs := Function.update s.runs tree (s.runs tree + 1)
  set (⟨state, operators, runs, s.closed, s.flag || bad⟩ : RealState C net.State)

theorem drawTreeRun_eq (draw : Draw C) (monitor : TreeMonitor C) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) : drawTreeRun K circuits settings draw monitor D net tree = (do
      let s ← get
      let fresh ← StateT.lift (free (liftComp ((List.range (treeSetups tree)).mapM fun c =>
        draw (setupsBefore s.runs + c)) _))
      treeRest K circuits settings D monitor net tree s fresh) := rfl

theorem treeRest_runs (monitor : TreeMonitor C) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) (fresh : List (Option (FreshKeys C))) (s' : RealState C net.State) :
    ∀ r ∈ support ((treeRest K circuits settings D monitor net tree s fresh).run s'),
      r.2.runs = Function.update s.runs tree (s.runs tree + 1) := by
  intro r hr
  simp only [treeRest, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff,
    StateT.run_set, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, _, _, rfl⟩ := hr
  rfl

theorem gameValue_grows {S : Type} (operators : C.Party → OperatorState C) (x : Point) :
    Grows runLimit (gameValue (σ := S) D operators x) :=
  grows_lift runLimit _

theorem grows_lift_lift {α : Type} (x : OracleComp (WorldSpec C) α) (t : TsigState C) :
    Grows runLimit ((StateT.lift (StateT.lift x : RealM C S α) : StateT (TsigState C) (RealM C S) α).run t) := by
  simp only [StateT.run_lift]
  exact grows_bind runLimit (grows_lift runLimit x) fun _ => grows_pure runLimit _

/-- The answer of an honest operator is a computation of the world. It keeps the runs. -/
theorem operatorAnswer_grows (operators : C.Party → OperatorState C) (operator : OperatorState C)
    (e : KeyIndex) (q : TsigQuery C) (t : TsigState C) :
    Grows runLimit ((operatorAnswer realLift (gameValue (σ := S) D operators) operator e q).run t) := by
  have h := hom_operatorAnswer (realHom S) (fun oa => free (liftComp oa (LocalSpec C)))
    (fun x => free (liftComp (prfValue (gameSeeds D fun i => (operators i).keys) x) (LocalSpec C))) operator e q t
  have he : (operatorAnswer (fun oa => realHom S (free (liftComp oa (LocalSpec C))))
      (fun x => realHom S (free (liftComp (prfValue (gameSeeds D fun i => (operators i).keys) x) (LocalSpec C))))
      operator e q).run t = (operatorAnswer realLift (gameValue (σ := S) D operators) operator e q).run t := rfl
  rw [← he, ← h]
  exact grows_lift runLimit _

theorem signRequest_grows (i : C.Party) (e : KeyIndex) (q : TsigQuery C) (t : TsigState C) :
    Grows runLimit ((signRequest (σ := S) D i e q).run t) := by
  unfold signRequest
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine grows_bind runLimit (grows_modify runLimit _ fun _ => rfl) fun _ =>
    grows_get_bind runLimit fun s => operatorAnswer_grows runLimit D _ _ _ _ _

theorem forgeryWins_grows (operators : C.Party → OperatorState C) (parameter : PublicParameter) (top : TopTree)
    (st : TsigState C) (forgery : Forgery) :
    Grows runLimit (forgeryWins (m := RealM C S) realLift (canonicalDealt D operators parameter top) st forgery) := by
  rw [forgeryWins_canonicalDealt]
  exact grows_lift runLimit _


end Shared

/-! ## The renaming through the game -/

section Support

theorem support_renameComp (D : C.Coalition) (σ : Equiv.Perm HashOutput) {α : Type} (oa : OracleComp (WorldSpec C) α)
    {a : α} (h : a ∈ support (renameComp D σ oa)) : a ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simpa [renameComp] using h
  | query_bind t k ih =>
    rw [renameComp_bind, mem_support_bind_iff] at h
    obtain ⟨u, -, hu⟩ := h
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ih u hu⟩

theorem bind_congr_support {α β : Type} (oa : OracleComp (WorldSpec C) α)
    {f g : α → OracleComp (WorldSpec C) β} (h : ∀ a ∈ support oa, f a = g a) : oa >>= f = oa >>= g := by
  induction oa using OracleComp.inductionOn with
  | pure x => simpa using h x (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]
    refine congrArg (_ >>= ·) (funext fun u => ih u fun a ha => h a ?_)
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ha⟩

end Support

section Param

variable (runLimit : ℕ) (D : C.Coalition) (σ : Equiv.Perm HashOutput) {S : Type}

/-- The runs of each tree are at most `runLimit`. -/
def RunsInv (s : RealState C S) : Prop := ∀ t, s.runs t ≤ runLimit

/-- `x'` from `s` is the renaming of `x` from `s`. -/
def RenAt {α : Type} (s : RealState C S) (x' x : RealM C S α) : Prop := x'.run s = renameComp D σ (x.run s)

/-- `x'` is the renaming of `x` from each state with runs at most `runLimit`. -/
def Ren {α : Type} (x' x : RealM C S α) : Prop := ∀ s, RunsInv runLimit s → RenAt D σ s x' x

variable {runLimit D σ}

theorem renAt_bind {α β : Type} {s : RealState C S} {x x' : RealM C S α} {f f' : α → RealM C S β}
    (hx : RenAt D σ s x' x) (hsupp : ∀ p ∈ support (x.run s), RunsInv runLimit p.2)
    (hf : ∀ a, Ren runLimit D σ (f' a) (f a)) : RenAt D σ s (x' >>= f') (x >>= f) := by
  unfold RenAt at hx ⊢
  rw [StateT.run_bind, StateT.run_bind, hx, renameComp_bind]
  exact bind_congr_support _ fun p hp => hf p.1 p.2 (hsupp p (support_renameComp D σ _ hp))

theorem ren_bind' {α β : Type} {x x' : RealM C S α} {f f' : α → RealM C S β}
    (hx : Ren runLimit D σ x' x) (hgrow : Grows runLimit x) (hf : ∀ a, Ren runLimit D σ (f' a) (f a)) :
    Ren runLimit D σ (x' >>= f') (x >>= f) :=
  fun s hs => renAt_bind (hx s hs) (fun p hp => (hgrow s p hp).2 hs) hf

theorem ren_self {α : Type} (x : RealM C S α) (hx : ∀ s, renameComp D σ (x.run s) = x.run s) :
    Ren runLimit D σ x x :=
  fun s _ => (hx s).symm

theorem ren_pure' {α : Type} (a : α) : Ren runLimit D σ (pure a : RealM C S α) (pure a) :=
  ren_self _ fun _ => renameComp_pure D σ _

theorem ren_liftW {α : Type} {y y' : OracleComp (WorldSpec C) α} (h : y' = renameComp D σ y) :
    Ren runLimit D σ (StateT.lift y' : RealM C S α) (StateT.lift y) := fun _ _ => by
  unfold RenAt
  rw [StateT.run_lift, StateT.run_lift, renameComp_bind, h]
  simp only [renameComp_pure]

theorem ren_get_bind {β : Type} {f f' : RealState C S → RealM C S β}
    (hf : ∀ s, RunsInv runLimit s → RenAt D σ s (f' s) (f s)) : Ren runLimit D σ (get >>= f') (get >>= f) :=
  fun s hs => by
    unfold RenAt at hf ⊢
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    exact hf s hs

/-- A computation of `H` on the free copy with no call of `PRG` is its renaming. -/
theorem renameComp_free_liftComp {α : Type} (oa : OracleComp (RoSpec C) α)
    (h : SigningSelectionProof.NoCall (DigestBudgets.RoIn .stream) oa) :
    renameComp D σ (free (liftComp oa (LocalSpec C))) = free (liftComp oa (LocalSpec C)) :=
  renameComp_eq_self D σ _ (DigestBudgets.free_liftComp_bound .stream _ (fun _ => Iff.rfl) _ 0
    ((SigningSelectionProof.noCall_iff _ _).1 h))

end Param

/-! ## The game with the renamed table -/

section KeyParam

variable [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (D : C.Coalition) (σ : Equiv.Perm HashOutput)

theorem tableFresh_rename {n : ℕ} (F : Table C n) (slot : ℕ) :
    tableFresh (fun x => σ (F x)) slot = (tableFresh F slot).map (renameFresh σ) := by
  unfold tableFresh
  split_ifs <;> rfl

/-- A run of a tree that the game allows takes its slots below `gameSetups`. -/
theorem setupsBefore_add_le (runs : Tree → ℕ) (hruns : ∀ t, runs t ≤ runLimit) (tree : Tree)
    (htree : runs tree < runLimit) : setupsBefore runs + treeSetups tree ≤ gameSetups runLimit := by
  rw [← setupsBefore_update]
  calc setupsBefore (Function.update runs tree (runs tree + 1)) ≤ setupsBefore (fun _ => runLimit) :=
        setupsBefore_mono fun t => by
          by_cases ht : t = tree
          · subst ht; simp; omega
          · simp [Function.update_of_ne ht, hruns t]
    _ = gameSetups runLimit := by
        simp [setupsBefore, gameSetups, treeSetups, Finset.sum_const, Finset.card_univ]
        ring

theorem monitorCall_not_stream (t : (WorldSpec C).Domain) (ht : GameCount.MonitorCall t) :
    ¬ HonestIn (C := C) .stream t := by
  rcases t with t | (u | q | x)
  · exact ht.elim
  · exact ht.elim
  · cases q <;> simp_all [GameCount.MonitorCall, GameCount.SignCall, HonestIn, InClass, queryClass]
  · exact (show False from ht).elim

attribute [local irreducible] wrongOutput in
/-- The monitor makes no call of `PRG`. -/
theorem renameComp_wrongOutput (keys : C.Party → Option (Keys C)) (tree : Tree) (outputs : C.Party → Option TreeOutput) :
    renameComp D σ (wrongOutput D keys tree outputs) = wrongOutput D keys tree outputs :=
  renameComp_eq_self D σ _ ((SigningSelectionProof.noCall_iff _ _).1
    (GameCount.wrongOutput_noCall D _ monitorCall_not_stream keys tree outputs))

variable {runLimit D σ}

theorem treeRest_rename (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) (s : RealState C net.State)
    (l l' : List (Option (FreshKeys C)))
    (hprog : ∀ i, slotProgram K circuits settings D (fun c => l'.getD c none) i (s.operators i) tree =
      renamePM D σ (slotProgram K circuits settings D (fun c => l.getD c none) i (s.operators i) tree))
    (s' : RealState C net.State) :
    RenAt D σ s' (treeRest K circuits settings D (wrongOutput D) net tree s l')
      (treeRest K circuits settings D (wrongOutput D) net tree s l) := by
  have hP : (fun i => slotProgram K circuits settings D (fun c => l'.getD c none) i (s.operators i) tree) =
      fun i => renamePM D σ (slotProgram K circuits settings D (fun c => l.getD c none) i (s.operators i) tree) :=
    funext hprog
  unfold RenAt treeRest
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  rw [hP, executePhase_rename, renameComp_bind]
  refine congrArg (_ >>= ·) (funext fun p => ?_)
  rcases p with ⟨state, outputs⟩
  simp only [renameComp_bind, renameComp_wrongOutput, StateT.run_set, renameComp_pure]

theorem drawTreeRun_runs (draw : Draw C) (monitor : TreeMonitor C) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) (s : RealState C net.State) :
    ∀ r ∈ support ((drawTreeRun K circuits settings draw monitor D net tree).run s),
      r.2.runs = Function.update s.runs tree (s.runs tree + 1) := by
  intro r hr
  rw [drawTreeRun_eq] at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc, mem_support_bind_iff] at hr
  obtain ⟨l, -, hr⟩ := hr
  exact treeRest_runs K circuits settings D monitor net tree s l s r hr

omit [Field E] [Algebra Bit E] in
theorem le_update_succ (runs : Tree → ℕ) (tree t : Tree) :
    runs t ≤ Function.update runs tree (runs tree + 1) t := by
  by_cases ht : t = tree
  · subst ht; simp
  · simp [Function.update_of_ne ht]

theorem runsGrow_update {S : Type} (s s' : RealState C S) (tree : Tree) (htree : s.runs tree < runLimit)
    (h : s'.runs = Function.update s.runs tree (s.runs tree + 1)) : RunsGrow runLimit s s' := by
  refine ⟨fun t => h ▸ le_update_succ s.runs tree t, fun hs t => ?_⟩
  · rw [h]
    by_cases ht : t = tree
    · subst ht; simp; omega
    · simp [Function.update_of_ne ht, hs t]

theorem grows_drawTreeRuns (draw : Draw C) (monitor : TreeMonitor C) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) : ∀ count, Grows runLimit (drawTreeRuns K circuits settings runLimit draw monitor D net tree count)
  | 0 => grows_pure runLimit ()
  | count + 1 => by
    intro s r hr
    simp only [drawTreeRuns, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split_ifs at hr with hm
    · simp only [StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨y, hy, hr⟩ := hr
      exact (runsGrow_update s y.2 tree (FirstCounts.mayRun_lt runLimit hm)
        (drawTreeRun_runs K circuits settings draw monitor net tree s y hy)).trans runLimit
        (grows_drawTreeRuns draw monitor net tree count y.2 r hr)
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact runsGrow_refl runLimit s

theorem getD_range_map {α : Type} (n c : ℕ) (f : ℕ → Option α) (h : c < n) :
    ((List.range n).map f).getD c none = f c := by
  simp [h]

theorem drawTreeRuns_rename (F : Table C (gameSetups runLimit)) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) : ∀ count, Ren runLimit D σ
      (drawTreeRuns K circuits settings runLimit (tableDraw runLimit fun x => σ (F x)) (wrongOutput D) D net tree count)
      (drawTreeRuns K circuits settings runLimit (tableDraw runLimit F) (wrongOutput D) D net tree count)
  | 0 => ren_pure' ()
  | count + 1 => by
    simp only [drawTreeRuns]
    refine ren_get_bind fun s hs => ?_
    split_ifs with hm
    · have hlt := FirstCounts.mayRun_lt runLimit hm
      have hle := setupsBefore_add_le runLimit s.runs hs tree hlt
      refine renAt_bind ?_ (fun p hp => (runsGrow_update s p.2 tree hlt
        (drawTreeRun_runs K circuits settings _ _ net tree s p hp)).2 hs) fun _ => drawTreeRuns_rename F net tree count
      unfold RenAt
      rw [drawTreeRun_eq, drawTreeRun_eq]
      simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, List.mapM_pure, liftComp_pure,
        free_pure]
      refine treeRest_rename K circuits settings net tree s _ _ (fun i => ?_) s
      refine slotProgram_rename D K circuits settings _ _ tree (fun c hc => ?_) (fun c hc => ?_) i (s.operators i)
      · rw [getD_range_map _ _ _ hc]
        have h : setupsBefore s.runs + c < gameSetups runLimit := by omega
        exact ⟨(fun T => F (⟨_, h⟩, .inl T), fun p => F (⟨_, h⟩, .inr p)), by simp [tableFresh, h]⟩
      · rw [getD_range_map _ _ _ hc, getD_range_map _ _ _ hc, tableFresh_rename]
    · exact ren_pure' () s hs

theorem ren_bind_pure {S α β : Type} {x x' : RealM C S α} (g : α → β) (hx : Ren runLimit D σ x' x) :
    Ren runLimit D σ (x' >>= fun a => pure (g a)) (x >>= fun a => pure (g a)) := fun s hs => by
  unfold RenAt
  rw [StateT.run_bind, StateT.run_bind, hx s hs, renameComp_bind]
  simp only [StateT.run_pure, renameComp_pure]

/-- A computation of `H` on the free copy that makes only calls on `.hash` and `.prf` is its renaming. -/
theorem renameComp_onlySign {α : Type} (oa : OracleComp (RoSpec C) α) (h : GameCount.OnlySign oa) :
    renameComp D σ (free (liftComp oa (LocalSpec C))) = free (liftComp oa (LocalSpec C)) :=
  renameComp_free_liftComp oa (DigestBudgets.noCall_of_onlySign (c := .stream) (by decide) h)

theorem grows_drawTreeRequest (draw : Draw C) (monitor : TreeMonitor C) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) :
    Grows runLimit (drawTreeRequest K circuits settings runLimit draw monitor D net b) := by
  unfold drawTreeRequest
  refine grows_bind runLimit (grows_drawTreeRuns K circuits settings _ _ _ _ 1) fun _ =>
    grows_get_bind runLimit fun s => ?_
  split
  · exact grows_bind runLimit (gameValue_grows runLimit D _ _) fun _ => grows_pure runLimit _
  · exact grows_pure runLimit _

theorem drawTreeRequest_rename (F : Table C (gameSetups runLimit)) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) : Ren runLimit D σ
      (drawTreeRequest K circuits settings runLimit (tableDraw runLimit fun x => σ (F x)) (wrongOutput D) D net b)
      (drawTreeRequest K circuits settings runLimit (tableDraw runLimit F) (wrongOutput D) D net b) := by
  unfold drawTreeRequest
  refine ren_bind' (drawTreeRuns_rename K circuits settings F net _ 1)
    (grows_drawTreeRuns K circuits settings _ _ _ _ 1) fun _ => ren_get_bind fun s hs => ?_
  split
  · refine (ren_bind_pure _ (ren_liftW ?_)) s hs
    exact (renameComp_onlySign _ (GameCount.onlySign_prfValue _ _)).symm
  · exact ren_pure' _ s hs

/-- The answer of an honest operator makes no call of `PRG`. -/
theorem renameComp_operatorAnswer (operators : C.Party → OperatorState C) (operator : OperatorState C)
    (e : KeyIndex) (q : TsigQuery C) (st : TsigState C) :
    renameComp D σ (free (liftComp ((operatorAnswer (fun oa => oa)
      (prfValue (gameSeeds D fun i => (operators i).keys)) operator e q).run st) (LocalSpec C))) =
      free (liftComp ((operatorAnswer (fun oa => oa)
        (prfValue (gameSeeds D fun i => (operators i).keys)) operator e q).run st) (LocalSpec C)) := by
  refine renameComp_free_liftComp _ ?_
  unfold operatorAnswer
  split
  · rw [ownAnswer_run]
    exact DigestBudgets.noCall_tsigOracles (by decide) _ _ _ q _
  · exact SigningSelectionProof.noCall_pure _ _

/-- The renaming on the state of the signing game. -/
def RenT {S α : Type} (y' y : StateT (TsigState C) (RealM C S) α) : Prop :=
  ∀ t, Ren runLimit D σ (y'.run t) (y.run t)

/-- The runs grow from each state of the signing game. -/
def GrowsT (runLimit : ℕ) {S α : Type} (y : StateT (TsigState C) (RealM C S) α) : Prop :=
  ∀ t, Grows runLimit (y.run t)

theorem renT_self {S α : Type} (y : StateT (TsigState C) (RealM C S) α)
    (h : ∀ t s, renameComp D σ ((y.run t).run s) = (y.run t).run s) : RenT (runLimit := runLimit) (D := D) (σ := σ) y y :=
  fun t => ren_self _ (h t)

theorem renT_bind {S α β : Type} {y y' : StateT (TsigState C) (RealM C S) α}
    {g g' : α → StateT (TsigState C) (RealM C S) β} (hy : RenT (runLimit := runLimit) (D := D) (σ := σ) y' y)
    (hgrow : GrowsT runLimit y) (hg : ∀ a, RenT (runLimit := runLimit) (D := D) (σ := σ) (g' a) (g a)) :
    RenT (runLimit := runLimit) (D := D) (σ := σ) (y' >>= g') (y >>= g) := fun t => by
  simp only [StateT.run_bind]
  exact ren_bind' (hy t) (hgrow t) fun p => hg p.1 p.2

theorem growsT_bind {S α β : Type} {y : StateT (TsigState C) (RealM C S) α}
    {g : α → StateT (TsigState C) (RealM C S) β} (hy : GrowsT runLimit y) (hg : ∀ a, GrowsT runLimit (g a)) :
    GrowsT runLimit (y >>= g) := fun t => by
  simp only [StateT.run_bind]
  exact grows_bind runLimit (hy t) fun p => hg p.1 p.2

theorem renT_lift {S α : Type} {x x' : RealM C S α} (hx : Ren runLimit D σ x' x) :
    RenT (runLimit := runLimit) (D := D) (σ := σ) (StateT.lift x' : StateT (TsigState C) (RealM C S) α)
      (StateT.lift x) := fun t => by
  simp only [StateT.run_lift]
  exact ren_bind_pure _ hx

theorem growsT_lift {S α : Type} {x : RealM C S α} (hx : Grows runLimit x) :
    GrowsT runLimit (StateT.lift x : StateT (TsigState C) (RealM C S) α) := fun t => by
  simp only [StateT.run_lift]
  exact grows_bind runLimit hx fun _ => grows_pure runLimit _

theorem growsT_simulateQ {S ι : Type} {spec : OracleSpec ι} {α : Type}
    (impl : QueryImpl spec (StateT (TsigState C) (RealM C S))) (himpl : ∀ q, GrowsT runLimit (impl q))
    (oa : OracleComp spec α) : GrowsT runLimit (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun t => grows_pure runLimit (a, t)
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    exact growsT_bind (himpl q) ih

theorem renT_simulateQ {S ι : Type} {spec : OracleSpec ι} {α : Type}
    (impl impl' : QueryImpl spec (StateT (TsigState C) (RealM C S)))
    (himpl : ∀ q, RenT (runLimit := runLimit) (D := D) (σ := σ) (impl' q) (impl q))
    (hgrow : ∀ q, GrowsT runLimit (impl q)) (oa : OracleComp spec α) :
    RenT (runLimit := runLimit) (D := D) (σ := σ) (simulateQ impl' oa) (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun t => ren_pure' (a, t)
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    exact renT_bind (himpl q) (hgrow q) ih

theorem renT_signRequest {S : Type} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    RenT (runLimit := runLimit) (D := D) (σ := σ) (signRequest (σ := S) D i e q) (signRequest D i e q) := by
  refine renT_self _ fun t s => ?_
  simp only [signRequest, StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_get, bind_assoc,
    pure_bind, operatorAnswer_eq_free, renameComp_bind, renameComp_pure, renameComp_operatorAnswer]

theorem growsT_drawOracles (draw : Draw C) (monitor : TreeMonitor C) (A : DkgTsigAdversary C E)
    (q : (TsigSpec C).Domain) :
    GrowsT runLimit (drawOracles K circuits settings runLimit draw monitor D A q) := by
  cases q with
  | corrupt i => exact fun t => grows_pure runLimit _
  | tree b => exact growsT_lift (grows_drawTreeRequest K circuits settings draw monitor A.net b)
  | round1 i J e message => exact fun t => signRequest_grows runLimit D i e _ t
  | round2 i J e message parts => exact fun t => signRequest_grows runLimit D i e _ t

theorem drawOracles_rename (F : Table C (gameSetups runLimit)) (A : DkgTsigAdversary C E)
    (q : (TsigSpec C).Domain) : RenT (runLimit := runLimit) (D := D) (σ := σ)
      (drawOracles K circuits settings runLimit (tableDraw runLimit fun x => σ (F x)) (wrongOutput D) D A q)
      (drawOracles K circuits settings runLimit (tableDraw runLimit F) (wrongOutput D) D A q) := by
  cases q with
  | corrupt i => exact fun t => ren_pure' _
  | tree b => exact renT_lift (drawTreeRequest_rename K circuits settings F A.net b)
  | round1 i J e message => exact renT_signRequest i e _
  | round2 i J e message parts => exact renT_signRequest i e _

theorem renT_liftSelf {S α : Type} (x : RealM C S α) (hx : ∀ s, renameComp D σ (x.run s) = x.run s) :
    RenT (runLimit := runLimit) (D := D) (σ := σ) (StateT.lift x : StateT (TsigState C) (RealM C S) α)
      (StateT.lift x) :=
  renT_lift (ren_self x hx)

theorem renameComp_liftAdversary {S α : Type} (y : OracleComp (LocalSpec C) α) (s : RealState C S) :
    renameComp D σ ((StateT.lift ((worldRoles (C := C)).adversary y) : RealM C S α).run s) =
      (StateT.lift ((worldRoles (C := C)).adversary y) : RealM C S α).run s := by
  rw [StateT.run_lift, renameComp_bind, renameComp_adversary]
  simp only [renameComp_pure]

omit [Field E] [Algebra Bit E] in
theorem grows_readAdversary {S : Type} : Grows runLimit ((·.adversary) <$> (get : RealM C S (RealState C S))) :=
  grows_bind runLimit (grows_get runLimit) fun _ => grows_pure runLimit _

omit [Field E] [Algebra Bit E] in
theorem grows_writeAdversary {S : Type} (state : S) :
    Grows runLimit (modify fun s : RealState C S => { s with adversary := state }) :=
  grows_modify runLimit _ fun _ => rfl

theorem renAt_signing {S ι α β : Type} {spec : OracleSpec ι}
    (impl impl' : QueryImpl spec (StateT (TsigState C) (RealM C S)))
    (himpl : ∀ q, RenT (runLimit := runLimit) (D := D) (σ := σ) (impl' q) (impl q))
    (hgrow : ∀ q, GrowsT runLimit (impl q)) (oa : OracleComp spec α) (t₀ : TsigState C)
    (k k' : α × TsigState C → RealM C S β) (hk : ∀ p, Ren runLimit D σ (k' p) (k p)) (s : RealState C S)
    (hs : RunsInv runLimit s) :
    RenAt D σ s ((simulateQ impl' oa).run t₀ >>= k') ((simulateQ impl oa).run t₀ >>= k) :=
  renAt_bind (renT_simulateQ impl impl' himpl hgrow oa t₀ s hs)
    (fun p hp => (growsT_simulateQ impl hgrow oa t₀ s p hp).2 hs) hk

theorem drawSigning_rename (F : Table C (gameSetups runLimit)) (A : DkgTsigAdversary C E) : Ren runLimit D σ
    (drawSigning K circuits settings runLimit (tableDraw runLimit fun x => σ (F x)) (wrongOutput D) D A)
    (drawSigning K circuits settings runLimit (tableDraw runLimit F) (wrongOutput D) D A) := by
  unfold drawSigning
  refine ren_get_bind fun s hs => ?_
  split
  · dsimp only
    refine renAt_signing _ _ (fun q => ?_) (fun q => ?_) _ _ _ _ (fun p => ?_) s hs
    · rcases q with q | q | q
      · exact renT_liftSelf _ fun s => renameComp_liftAdversary _ _
      · exact drawOracles_rename K circuits settings F A q
      · cases q with
        | read => exact renT_liftSelf _ fun s => rfl
        | write state => exact renT_liftSelf _ fun s => rfl
    · rcases q with q | q | q
      · exact fun t => grows_lift_lift runLimit _ t
      · exact growsT_drawOracles K circuits settings _ _ A q
      · cases q with
        | read => exact growsT_lift grows_readAdversary
        | write state => exact growsT_lift (grows_writeAdversary state)
    · rcases p with ⟨forgery, st⟩
      refine ren_get_bind fun s' hs' => ?_
      unfold RenAt
      rw [forgeryWins_eq_free, StateT.run_lift, renameComp_bind,
        renameComp_onlySign _ (onlySign_forgeryWins _ _ _ _ _ _ _)]
      simp only [renameComp_pure]
  · exact ren_pure' _ s hs

variable (runLimit) in
/-- The game with the permuted table is the game with the hidden keys of the honest calls renamed. -/
theorem keyParametric : KeyParametric K circuits settings runLimit := by
  intro D A F σ
  unfold tableGame drawGame drawRun
  rw [renameComp_map, renameComp_bind, renameComp_eq_self D σ _ ((GameCount.bound_iff _ _ _).1
    (DigestBudgets.seedHonest (c := .stream) (E := E) (by decide) D A.net))]
  refine congrArg (Prod.snd <$> ·) (congrArg (_ >>= ·) (funext fun x => ?_))
  rcases x with ⟨state, keys⟩
  dsimp only
  rw [renameComp_bind]
  have hb := ren_bind' (drawTreeRuns_rename (D := D) (σ := σ) K circuits settings F A.net .top runLimit)
    (grows_drawTreeRuns (D := D) K circuits settings (tableDraw runLimit F) (wrongOutput D) A.net .top runLimit)
    (fun _ => drawSigning_rename (D := D) (σ := σ) K circuits settings F A) (startState D state keys) (fun t => by
      simp [startState])
  unfold RenAt at hb
  erw [hb]
  simp only [renameComp_pure]

end KeyParam

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.keyParametric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.keyParametric
