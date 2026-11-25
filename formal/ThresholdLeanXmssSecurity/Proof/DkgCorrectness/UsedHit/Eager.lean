import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Param

/-!
# The eager draw of the fresh keys

`eagerDraw` proves `UsedHit.EagerDraw`. A run of a tree draws the rows of its slots from
`setupsBefore` of the runs on, and the runs only grow, so the game draws each row at most one time.
`Good X` holds for a piece `X` of the game when its runs grow, it reads only the rows of the table from
the runs of its start on (`LocalOK`), and, before each continuation that reads only later rows, the
lazy draw and the uniform table give one law (`EagerOK`). `good_bind` composes the three facts. The
base case is one run of a tree (`good_drawTreeRun`), and `eager_slot` moves one row of a uniform table
to the place of its lazy draw.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

open UsedHit

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
theorem hybridTreeRuns_eq_draw (j : ℕ) (monitor : TreeMonitor C) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    ∀ count, hybridTreeRuns K circuits settings runLimit j monitor D net tree count =
      drawTreeRuns K circuits settings runLimit (sampleSlot j) monitor D net tree count
  | 0 => rfl
  | count + 1 => by
    simp only [hybridTreeRuns, drawTreeRuns, hybridTreeRuns_eq_draw j monitor D net tree count]
    rfl

omit [Fintype E] [DecidableEq E] in
/-- `hybridGame j` is `drawGame` with the draw of hybrid `j`. -/
theorem hybridGame_eq_drawGame (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    hybridGame K circuits settings runLimit j D A = drawGame K circuits settings runLimit (sampleSlot j) D A := by
  have horacles : hybridOracles K circuits settings runLimit j (wrongOutput D) D A =
      drawOracles K circuits settings runLimit (sampleSlot j) (wrongOutput D) D A := by
    funext q
    cases q with
    | tree b =>
      simp only [hybridOracles, drawOracles, hybridTreeRequest, drawTreeRequest, hybridTreeRuns_eq_draw]
      rfl
    | _ => rfl
  have hsigning : hybridSigning K circuits settings runLimit j (wrongOutput D) D A =
      drawSigning K circuits settings runLimit (sampleSlot j) (wrongOutput D) D A := by
    simp only [hybridSigning, drawSigning, horacles]
    rfl
  simp only [hybridGame, drawGame, hybridRun, drawRun, hybridTreeRuns_eq_draw, hsigning]

variable (prims : Primitives)

omit [Fintype E] [DecidableEq E] in
/-- The test at run limit `0`. No slot has fresh keys and each table gives the hybrid game. -/
example : EagerDraw K circuits settings 0 prims := by
  intro D A
  have hgame : ∀ F : Table C (gameSetups 0),
      tableGame K circuits settings 0 F D A = hybridGame K circuits settings 0 (gameSetups 0) D A := by
    intro F
    rw [hybridGame_eq_drawGame, tableGame]
    congr 1
  simp only [hgame]
  exact (OracleComp.EvalDistEq.bind_const _ _).symm


/-! ## The runs of the game in the world -/

section Sem

variable (D : C.Coalition) {σ : Type}

/-- Two tables agree on each slot from `b` on. -/
def RowsAgree {n : ℕ} (b : ℕ) (F F' : Table C n) : Prop := ∀ x : Entry C n, b ≤ x.1.val → F x = F' x

theorem RowsAgree.mono {n b b' : ℕ} {F F' : Table C n} (h : RowsAgree b F F') (hb : b ≤ b') :
    RowsAgree b' F F' := fun x hx => h x (hb.trans hx)

/-- The run of `x` from the state `s` in `jointKeyWorld` from the state `w`. -/
def sem {α : Type} (x : RealM C σ α) (s : RealState C σ) (w : KeyJointState C) :
    ProbComp ((α × RealState C σ) × KeyJointState C) :=
  (simulateQ (jointKeyWorld prims D false) (x.run s)).run w

theorem sem_bind {α β : Type} (x : RealM C σ α) (f : α → RealM C σ β) (s : RealState C σ) (w : KeyJointState C) :
    sem prims D (x >>= f) s w = sem prims D x s w >>= fun r => sem prims D (f r.1.1) r.1.2 r.2 := by
  simp only [sem, StateT.run_bind, simulateQ_bind]

theorem mem_support_sem {α : Type} {x : RealM C σ α} {s : RealState C σ} {w : KeyJointState C}
    {r : (α × RealState C σ) × KeyJointState C} (hr : r ∈ support (sem prims D x s w)) :
    r.1 ∈ support (x.run s) := by
  apply support_simulateQ_run'_subset (jointKeyWorld prims D false) (x.run s) w
  simp only [StateT.run', support_map, Set.mem_image]
  exact ⟨r, hr, rfl⟩

/-- The eager draw for one piece `X` of the game. Before each continuation that reads only the slots
of the table from the runs at its start on, the lazy draw and the table give one law. -/
def EagerOK {α : Type} (X : Draw C → RealM C σ α) : Prop :=
  ∀ (s : RealState C σ) (w : KeyJointState C) {β : Type}
    (k : Table C (gameSetups runLimit) → (α × RealState C σ) × KeyJointState C → ProbComp β),
    (∀ F F' r, RowsAgree (setupsBefore r.1.2.runs) F F' → k F r =ᵈ k F' r) →
    (($ᵗ Table C (gameSetups runLimit)) >>= fun F => sem prims D (X (lazyDraw runLimit)) s w >>= k F) =ᵈ
      (($ᵗ Table C (gameSetups runLimit)) >>= fun F => sem prims D (X (tableDraw runLimit F)) s w >>= k F)

/-- The piece `X` from `s` reads only the slots of the table from the runs of `s` on. -/
def LocalOK {α : Type} (X : Draw C → RealM C σ α) : Prop :=
  ∀ (s : RealState C σ) (w : KeyJointState C) (F F' : Table C (gameSetups runLimit)),
    RowsAgree (setupsBefore s.runs) F F' →
      sem prims D (X (tableDraw runLimit F)) s w =ᵈ sem prims D (X (tableDraw runLimit F')) s w

/-- The three facts of a piece of the game for the eager draw. -/
structure Good {α : Type} (X : Draw C → RealM C σ α) : Prop where
  ups : ∀ d, Ups (X d)
  locally : LocalOK runLimit prims D X
  eager : EagerOK runLimit prims D X

theorem good_const {α : Type} (x : RealM C σ α) (hx : Grows runLimit x) :
    Good runLimit prims D (fun _ => x) :=
  ⟨fun _ => hx.ups, fun _ _ _ _ _ => EvalDistEq.rfl, fun _ _ _ _ _ => EvalDistEq.rfl⟩

theorem sem_agree {α : Type} {x : RealM C σ α} (hx : Ups x) {s : RealState C σ}
    {w : KeyJointState C} {r : (α × RealState C σ) × KeyJointState C} (hr : r ∈ support (sem prims D x s w))
    {F F' : Table C (gameSetups runLimit)} (h : RowsAgree (setupsBefore s.runs) F F') :
    RowsAgree (setupsBefore r.1.2.runs) F F' :=
  h.mono (setupsBefore_mono (hx s r.1 (mem_support_sem prims D hr)))

theorem good_bind {α β : Type} {X : Draw C → RealM C σ α} {f : Draw C → α → RealM C σ β}
    (hX : Good runLimit prims D X) (hf : ∀ a, Good runLimit prims D fun d => f d a) :
    Good runLimit prims D fun d => X d >>= f d := by
  refine ⟨fun d => ups_bind (hX.ups d) fun a => (hf a).ups d, ?_, ?_⟩
  · intro s w F F' h
    rw [sem_bind, sem_bind]
    refine (EvalDistEq.bind_left (hX.locally s w F F' h) _).trans
      (OracleComp.EvalDistEq.bind_congr_of_support _ fun r hr => ?_)
    exact (hf r.1.1).locally r.1.2 r.2 F F' (sem_agree runLimit prims D (hX.ups _) hr h)
  · intro s w β k hk
    simp only [sem_bind, bind_assoc]
    refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
    have h1 : (sem prims D (X (lazyDraw runLimit)) s w >>= fun b => ($ᵗ Table C (gameSetups runLimit)) >>= fun a =>
          sem prims D (f (lazyDraw runLimit) b.1.1) b.1.2 b.2 >>= k a) =ᵈ
        (sem prims D (X (lazyDraw runLimit)) s w >>= fun b => ($ᵗ Table C (gameSetups runLimit)) >>= fun a =>
          sem prims D (f (tableDraw runLimit a) b.1.1) b.1.2 b.2 >>= k a) :=
      _root_.EvalDistEq.bind_right _ fun r => (hf r.1.1).eager r.1.2 r.2 k hk
    refine h1.trans ((OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_)
    refine hX.eager s w (fun F r => sem prims D (f (tableDraw runLimit F) r.1.1) r.1.2 r.2 >>= k F) ?_
    intro F F' r h
    refine (EvalDistEq.bind_left ((hf r.1.1).locally r.1.2 r.2 F F' h) _).trans
      (OracleComp.EvalDistEq.bind_congr_of_support _ fun r' hr' => ?_)
    exact hk F F' r' (sem_agree runLimit prims D ((hf r.1.1).ups _) hr' h)

theorem good_pure {α : Type} (a : α) : Good runLimit prims D fun _ => (pure a : RealM C σ α) :=
  good_const runLimit prims D _ (grows_pure runLimit a)

theorem good_get_bind {β : Type} {f : Draw C → RealState C σ → RealM C σ β}
    (hf : ∀ s, Good runLimit prims D fun d => f d s) : Good runLimit prims D fun d => get >>= f d :=
  good_bind runLimit prims D (good_const runLimit prims D _ (grows_get runLimit)) hf

theorem good_ite {α : Type} (p : Prop) [Decidable p] {X Y : Draw C → RealM C σ α}
    (hX : p → Good runLimit prims D X) (hY : ¬ p → Good runLimit prims D Y) :
    Good runLimit prims D fun d => if p then X d else Y d := by
  by_cases h : p
  · simpa only [h, ↓reduceIte] using hX h
  · simpa only [h, ↓reduceIte] using hY h

end Sem

/-! ## One slot of a uniform table -/

section Slot

/-- The fresh keys of one row of a table. -/
def rowFresh (u : C.Term ⊕ C.Pair → HashOutput) : FreshKeys C := (fun T => u (.inl T), fun p => u (.inr p))

theorem rowFresh_uniform :
    rowFresh <$> ($ᵗ (C.Term ⊕ C.Pair → HashOutput)) =ᵈ (sampleFresh : ProbComp (FreshKeys C)) := by
  have hb : Function.Bijective (rowFresh (C := C)) := (Equiv.sumArrowEquivProdArrow C.Term C.Pair HashOutput).bijective
  refine (SampleableType.map_uniformSample_evalDistEq_of_bijective hb).trans ?_
  apply EvalDistEq.of_eq
  simp [sampleFresh, uniformSample, SampleableType.selectElem, seq_eq_bind_map]

/-- The table of the rows `G`. -/
def uncurryTable {n : ℕ} (G : Fin n → C.Term ⊕ C.Pair → HashOutput) : Table C n := fun x => G x.1 x.2

/-- A uniform table is a uniform function from the slots to the rows. -/
theorem uniform_table_bind {n : ℕ} {γ : Type} (g : Table C n → ProbComp γ) :
    (($ᵗ Table C n) >>= g) =ᵈ (($ᵗ (Fin n → C.Term ⊕ C.Pair → HashOutput)) >>= fun G => g (uncurryTable G)) := by
  have hb : Function.Bijective (uncurryTable (C := C) (n := n)) := (Equiv.curry _ _ _).symm.bijective
  refine (EvalDistEq.bind_left (SampleableType.map_uniformSample_evalDistEq_of_bijective hb).symm g).trans ?_
  rw [bind_map_left]

/-- The lazy draw of one slot before a continuation that reads only the later slots of the table is
the row of the slot in a uniform table. -/
theorem eager_slot (b : ℕ) {β : Type} (H : Table C (gameSetups runLimit) → Option (FreshKeys C) → ProbComp β)
    (hH : ∀ F F' x, RowsAgree (b + 1) F F' → H F x =ᵈ H F' x) :
    (($ᵗ Table C (gameSetups runLimit)) >>= fun F => lazyDraw runLimit b >>= H F) =ᵈ
      (($ᵗ Table C (gameSetups runLimit)) >>= fun F => H F (tableFresh F b)) := by
  by_cases hb : b < gameSetups runLimit
  · refine (uniform_table_bind _).trans (EvalDistEq.trans ?_ (uniform_table_bind _).symm)
    have hupd := evalDistEq_uniformSample_bind_update (D := Fin (gameSetups runLimit))
      (R := C.Term ⊕ C.Pair → HashOutput) ⟨b, hb⟩
      (fun G => H (uncurryTable G) (tableFresh (uncurryTable G) b))
    refine EvalDistEq.trans ?_ hupd
    have h2 : ∀ (u : C.Term ⊕ C.Pair → HashOutput) (G : Fin (gameSetups runLimit) → C.Term ⊕ C.Pair → HashOutput),
        H (uncurryTable (Function.update G ⟨b, hb⟩ u)) (tableFresh (uncurryTable (Function.update G ⟨b, hb⟩ u)) b) =ᵈ
          H (uncurryTable G) (some (rowFresh u)) := by
      intro u G
      have ht : tableFresh (uncurryTable (Function.update G ⟨b, hb⟩ u)) b = some (rowFresh u) := by
        simp [tableFresh, hb, uncurryTable, rowFresh]
      rw [ht]
      refine hH _ _ _ fun x hx => ?_
      have hne : x.1 ≠ ⟨b, hb⟩ := fun h => by rw [h] at hx; simp at hx
      simp [uncurryTable, Function.update_of_ne hne]
    refine EvalDistEq.trans ?_ (_root_.EvalDistEq.bind_right _ fun u =>
      _root_.EvalDistEq.bind_right _ fun G => (h2 u G).symm)
    refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
    refine _root_.EvalDistEq.bind_right _ fun G => ?_
    have hl : lazyDraw (C := C) runLimit b = some <$> sampleFresh := by simp [sampleSlot, hb]
    rw [hl]
    refine (_root_.EvalDistEq.bind_left (rowFresh_uniform.symm.map some) _).trans ?_
    simp only [Functor.map_map, bind_map_left]
    exact EvalDistEq.rfl
  · have hl : lazyDraw (C := C) runLimit b = pure none := by simp [sampleSlot, hb]
    have ht : ∀ F : Table C (gameSetups runLimit), tableFresh F b = none := by simp [tableFresh, hb]
    simp only [hl, ht, pure_bind]
    exact EvalDistEq.rfl

theorem tableFresh_congr {n slot : ℕ} {F F' : Table C n} (h : RowsAgree slot F F') :
    tableFresh F slot = tableFresh F' slot := by
  unfold tableFresh
  split_ifs with hs
  · congr 2
    · funext T; exact h _ le_rfl
    · funext p; exact h _ le_rfl
  · rfl

/-- The lazy draws of `n` consecutive slots from `b` on, before a continuation that reads only the
slots of the table from `b + n` on, are the rows of these slots in a uniform table. -/
theorem eager_draws (n : ℕ) : ∀ (b : ℕ) {β : Type}
    (H : Table C (gameSetups runLimit) → List (Option (FreshKeys C)) → ProbComp β),
    (∀ F F' l, RowsAgree (b + n) F F' → H F l =ᵈ H F' l) →
    (($ᵗ Table C (gameSetups runLimit)) >>= fun F =>
        ((List.range n).mapM fun c => lazyDraw runLimit (b + c)) >>= H F) =ᵈ
      (($ᵗ Table C (gameSetups runLimit)) >>= fun F => H F ((List.range n).map fun c => tableFresh F (b + c))) := by
  induction n with
  | zero =>
    intro b β H _
    simp only [List.range_zero, List.mapM_nil, pure_bind, List.map_nil]
    exact EvalDistEq.rfl
  | succ n ih =>
    intro b β H hH
    have hc : ∀ c, b + (c + 1) = (b + 1) + c := by omega
    rw [List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
    simp only [List.map_cons, List.map_map]
    simp only [Function.comp_def, Nat.succ_eq_add_one, Nat.add_zero, bind_assoc, pure_bind]
    have h1 : (fun x => lazyDraw (C := C) runLimit (b + (x + 1))) = fun x => lazyDraw runLimit (b + 1 + x) :=
      funext fun x => by rw [hc]
    have h2 : ∀ F : Table C (gameSetups runLimit), (fun x => tableFresh F (b + (x + 1))) = fun x => tableFresh F (b + 1 + x) :=
      fun F => funext fun x => by rw [hc]
    simp only [h1, h2]
    refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine (_root_.EvalDistEq.bind_right _ fun x => ih (b + 1) (fun F xs => H F (x :: xs)) fun F F' l h =>
      hH F F' _ (h.mono (by omega))).trans ?_
    refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
    refine eager_slot runLimit b (fun F x => H F (x :: (List.range n).map fun c => tableFresh F (b + 1 + c)))
      fun F F' x h => ?_
    have hl : ((List.range n).map fun c => tableFresh F (b + 1 + c)) =
        (List.range n).map fun c => tableFresh F' (b + 1 + c) :=
      List.map_congr_left fun c _ => tableFresh_congr (h.mono (by omega))
    rw [hl]
    exact hH F F' _ (h.mono (by omega))

end Slot

/-! ## One run of a tree -/

section TreeRun

variable (D : C.Coalition) {σ : Type}

/-- A private draw on the free copy keeps the state of `jointKeyWorld`. -/
theorem simulateQ_joint_free_liftComp {α : Type} (p : ProbComp α) :
    simulateQ (jointKeyWorld prims D false) (free (liftComp p (LocalSpec C))) = StateT.lift p := by
  induction p using OracleComp.inductionOn with
  | pure a => apply StateT.ext; intro w; simp
  | query_bind u k ih =>
    have e : free (liftComp (liftM (OracleSpec.query u) >>= k) (LocalSpec C)) =
        (liftM ((WorldSpec C).query (.inr (.inl u))) : OracleComp (WorldSpec C) _) >>= fun x =>
          free (liftComp (k x) (LocalSpec C)) := by
      rw [liftComp_bind, free_bind]
      rfl
    rw [e, simulateQ_bind]
    simp only [ih, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    apply StateT.ext
    intro w
    simp [jointKeyWorld, jointKeyWorldCore, jointLocal, onJointHash, keyJointRisk, unifFwdImpl, StateT.run_lift]

omit [Fintype E] [DecidableEq E] in
theorem sem_drawTreeRun (draw : Draw C) (monitor : TreeMonitor C) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) (s : RealState C net.State) (w : KeyJointState C) :
    sem prims D (drawTreeRun K circuits settings draw monitor D net tree) s w =
      ((List.range (treeSetups tree)).mapM fun c => draw (setupsBefore s.runs + c)) >>= fun l =>
        sem prims D (treeRest K circuits settings D monitor net tree s l) s w := by
  rw [drawTreeRun_eq]
  simp only [sem, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, simulateQ_bind,
    simulateQ_joint_free_liftComp, bind_assoc]

omit [Fintype E] [DecidableEq E] in
/-- One run of a tree is a good piece. -/
theorem good_drawTreeRun (monitor : TreeMonitor C) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    Good runLimit prims D fun d => drawTreeRun K circuits settings d monitor D net tree := by
  have hruns : ∀ (s : RealState C net.State) l w r,
      r ∈ support (sem prims D (treeRest K circuits settings D monitor net tree s l) s w) →
        r.1.2.runs = Function.update s.runs tree (s.runs tree + 1) :=
    fun s l w r hr => treeRest_runs K circuits settings D monitor net tree s l s r.1 (mem_support_sem prims D hr)
  refine ⟨fun d s r hr => ?_, fun s w F F' h => ?_, fun s w β k hk => ?_⟩
  · rw [drawTreeRun_runs K circuits settings d monitor net tree s r hr]
    exact le_update_succ s.runs tree
  · rw [sem_drawTreeRun, sem_drawTreeRun, List.mapM_pure, List.mapM_pure, pure_bind, pure_bind]
    have hl : ((List.range (treeSetups tree)).map fun c => tableFresh F (setupsBefore s.runs + c)) =
        (List.range (treeSetups tree)).map fun c => tableFresh F' (setupsBefore s.runs + c) :=
      List.map_congr_left fun c _ => tableFresh_congr (h.mono (by omega))
    rw [hl]
  · simp only [sem_drawTreeRun, List.mapM_pure, pure_bind, bind_assoc]
    refine eager_draws runLimit (treeSetups tree) (setupsBefore s.runs)
      (fun F l => sem prims D (treeRest K circuits settings D monitor net tree s l) s w >>= k F)
      fun F F' l h => OracleComp.EvalDistEq.bind_congr_of_support _ fun r hr => hk F F' r ?_
    rw [hruns s l w r hr, setupsBefore_update]
    exact h

end TreeRun

/-! ## The walk of the game -/

section Walk

variable (D : C.Coalition)

omit [Fintype E] [DecidableEq E] in
theorem good_drawTreeRuns (monitor : TreeMonitor C) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    ∀ count, Good runLimit prims D fun d => drawTreeRuns K circuits settings runLimit d monitor D net tree count
  | 0 => good_pure runLimit prims D ()
  | count + 1 => by
    simp only [drawTreeRuns]
    refine good_get_bind runLimit prims D fun s => good_ite runLimit prims D _ (fun _ => ?_) fun _ => good_pure _ _ _ _
    exact good_bind runLimit prims D (good_drawTreeRun K circuits settings runLimit prims D monitor net tree)
      fun _ => good_drawTreeRuns monitor net tree count

omit [Fintype E] [DecidableEq E] in
theorem good_drawTreeRequest (monitor : TreeMonitor C) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) :
    Good runLimit prims D fun d => drawTreeRequest K circuits settings runLimit d monitor D net b := by
  unfold drawTreeRequest
  refine good_bind runLimit prims D (good_drawTreeRuns K circuits settings runLimit prims D monitor net _ 1)
    fun _ => good_get_bind runLimit prims D fun s => good_const runLimit prims D _ ?_
  split
  · exact grows_bind runLimit (gameValue_grows runLimit D _ _) fun _ => grows_pure runLimit _
  · exact grows_pure runLimit _

variable {σ : Type}

/-- A good piece on the state of the signing game. -/
def GoodT {α : Type} (Y : Draw C → StateT (TsigState C) (RealM C σ) α) : Prop :=
  ∀ t, Good runLimit prims D fun d => (Y d).run t

theorem goodT_bind {α β : Type} {Y : Draw C → StateT (TsigState C) (RealM C σ) α}
    {g : Draw C → α → StateT (TsigState C) (RealM C σ) β} (hY : GoodT runLimit prims D Y)
    (hg : ∀ a, GoodT runLimit prims D fun d => g d a) : GoodT runLimit prims D fun d => Y d >>= g d := by
  intro t
  simp only [StateT.run_bind]
  exact good_bind runLimit prims D (hY t) fun p => hg p.1 p.2

theorem goodT_lift {α : Type} {X : Draw C → RealM C σ α} (hX : Good runLimit prims D X) :
    GoodT runLimit prims D fun d => (StateT.lift (X d) : StateT (TsigState C) (RealM C σ) α) := by
  intro t
  simp only [StateT.run_lift]
  exact good_bind runLimit prims D hX fun _ => good_pure runLimit prims D _

theorem goodT_const {α : Type} (y : StateT (TsigState C) (RealM C σ) α) (hy : ∀ t, Grows runLimit (y.run t)) :
    GoodT runLimit prims D fun _ => y :=
  fun t => good_const runLimit prims D _ (hy t)

theorem goodT_simulateQ {ι : Type} {spec : OracleSpec ι} {α : Type}
    (impl : Draw C → QueryImpl spec (StateT (TsigState C) (RealM C σ)))
    (himpl : ∀ q, GoodT runLimit prims D fun d => impl d q) (oa : OracleComp spec α) :
    GoodT runLimit prims D fun d => simulateQ (impl d) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact goodT_const runLimit prims D _ fun t => grows_pure runLimit (a, t)
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    exact goodT_bind runLimit prims D (himpl q) ih

omit [Fintype E] [DecidableEq E] in
theorem goodT_drawOracles (monitor : TreeMonitor C) (A : DkgTsigAdversary C E) (q : (TsigSpec C).Domain) :
    GoodT runLimit prims D fun d => drawOracles K circuits settings runLimit d monitor D A q := by
  cases q with
  | corrupt i => exact goodT_const runLimit prims D _ fun t => grows_pure runLimit _
  | tree b => exact goodT_lift runLimit prims D (good_drawTreeRequest K circuits settings runLimit prims D monitor A.net b)
  | round1 i J e message => exact goodT_const runLimit prims D _ fun t => signRequest_grows runLimit D i e _ t
  | round2 i J e message parts => exact goodT_const runLimit prims D _ fun t => signRequest_grows runLimit D i e _ t

omit [Fintype E] [DecidableEq E] in
theorem good_drawSigning (monitor : TreeMonitor C) (A : DkgTsigAdversary C E) :
    Good runLimit prims D fun d => drawSigning K circuits settings runLimit d monitor D A := by
  unfold drawSigning
  refine good_get_bind runLimit prims D fun s => ?_
  split
  · dsimp only
    refine good_bind runLimit prims D (goodT_simulateQ runLimit prims D _ (fun q => ?_) _ _) fun p => ?_
    swap
    · rcases p with ⟨forgery, st⟩
      exact good_get_bind runLimit prims D fun s' => good_const runLimit prims D _
        (forgeryWins_grows runLimit D _ _ _ _ _)
    rcases q with q | q | q
    · exact goodT_const runLimit prims D _ fun t => grows_lift_lift runLimit _ t
    · exact goodT_drawOracles K circuits settings runLimit prims D monitor A q
    · refine goodT_const runLimit prims D _ fun t => ?_
      cases q with
      | read => exact growsT_lift (grows_readAdversary (runLimit := runLimit)) t
      | write state => exact growsT_lift (grows_writeAdversary (runLimit := runLimit) state) t
  · exact good_pure runLimit prims D _

omit [Fintype E] [DecidableEq E] in
theorem jointRun_drawGame (draw : Draw C) (A : DkgTsigAdversary C E) :
    jointRun prims D (drawGame K circuits settings runLimit draw D A) =
      (simulateQ (jointKeyWorld prims D false) (realExecution D A.net noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [])).run keyJointInitial >>=
        fun p => (simulateQ (jointKeyWorld prims D false) (voteRound worldRoles D A.net p.1.1 fun i =>
          (p.1.2 i).map seedVote)).run p.2 >>=
        fun v => sem prims D (drawTreeRuns K circuits settings runLimit draw (wrongOutput D) D A.net .top runLimit >>=
          fun _ => drawSigning K circuits settings runLimit draw (wrongOutput D) D A) (seedState D v.1.1 p.1.2 v.1.2)
            v.2 >>=
          fun r => pure (r.1.2.flag, r.2) := by
  simp only [jointRun, drawGame, drawRun, sem, map_bind, simulateQ_bind, StateT.run_bind, bind_assoc, map_pure,
    simulateQ_pure, StateT.run_pure]

end Walk

variable (prims : Primitives)

omit [Fintype E] [DecidableEq E] in
/-- The eager draw. -/
theorem eagerDraw : EagerDraw K circuits settings runLimit prims := by
  intro D A
  rw [hybridGame_eq_drawGame]
  change jointRun prims D (drawGame K circuits settings runLimit (lazyDraw runLimit) D A) =ᵈ
    (($ᵗ Table C (gameSetups runLimit)) >>= fun F =>
      jointRun prims D (drawGame K circuits settings runLimit (tableDraw runLimit F) D A))
  simp only [jointRun_drawGame]
  have hgood := good_bind runLimit prims D
    (good_drawTreeRuns K circuits settings runLimit prims D (wrongOutput D) A.net .top runLimit)
    fun _ => good_drawSigning K circuits settings runLimit prims D (wrongOutput D) A
  refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap _ _ _).symm
  refine _root_.EvalDistEq.bind_right _ fun p => ?_
  refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap _ _ _).symm
  refine _root_.EvalDistEq.bind_right _ fun v => ?_
  refine (OracleComp.EvalDistEq.bind_const ($ᵗ Table C (gameSetups runLimit)) _).symm.trans ?_
  exact hgood.eager _ _ (fun _ r => pure (r.1.2.flag, r.2)) fun _ _ _ _ => EvalDistEq.rfl

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.eagerDraw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.eagerDraw
