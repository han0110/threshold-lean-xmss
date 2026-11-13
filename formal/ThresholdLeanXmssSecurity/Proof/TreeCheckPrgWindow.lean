import ThresholdLeanXmssSecurity.Proof.TreeCheckHonestLog

/-!
# PRG windows of real check programs

A window excludes PRG reads at and above its end on every answer path,
including aborts. Label increments are used only to place a bind's supported
continuations. The boundary frame assumes freshness after its first pass;
it does not assert freshness of the incoming walk state.

The syntax composition ports TreeCheckHonestDisc (A184); the retained-step
and boundary frames port TreeCheckHonestLog (A185). Query bounds use the
pinned VCVio laws, and hidden-address frames use treeSim_hiddenQuery_frame.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
set_option linter.unusedSectionVars false
set_option maxRecDepth 2000
noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckPrgWindow
open TreeSimHashCount TreeCheckWalkRecipe TreeCheckWalkState
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E α β : Type}

/-- Local PRG queries at or above the cutoff. -/
def PrgFrom (L : ℕ) : (LocalSpec C).Domain → Prop
  | .inr (.inr x) => L ≤ x.2.2.1
  | _ => False

/-- The all-answer query bound, including paths that abort. -/
def PrgWindow (n : ℕ) (p : RunM C E RealSpec α) : Prop :=
  ∀ st L, st.label + n ≤ L → IsQueryBoundP (p.run st).run (PartyQuery (G := RealSpec) (PrgFrom L)) 0

theorem PrgWindow.pure (a : α) : PrgWindow (C := C) (E := E) 0 (Pure.pure a) :=
  fun _ _ _ => isQueryBoundP_pure _ _ _

theorem PrgWindow.of_quiet {n : ℕ} {p : RunM C E RealSpec α}
    (h : ∀ L, RunBudget (PrgFrom L) p 0) : PrgWindow n p := fun st L _ => h L st

/-- Port of RunDisc.bind; aborted prefixes retain their own query bound. -/
theorem PrgWindow.bind {m n : ℕ} {p : RunM C E RealSpec α}
    {f : α → RunM C E RealSpec β} (h : PrgWindow m p)
    (labels : LockstepLabels m p) (rest : ∀ a, PrgWindow n (f a)) :
    PrgWindow (m + n) (p >>= f) := by
  intro st L le
  simp only [StateT.run_bind, OptionT.run_bind, Option.elimM]
  refine isQueryBoundP_bind (n := 0) (m := 0) (h st L (by omega)) ?_
  intro out ho
  cases out with
  | none => exact isQueryBoundP_pure _ _ _
  | some out =>
    apply rest out.1 out.2 L
    rw [labels st out.1 out.2 ho]
    omega

theorem PrgWindow.le_bind {m n N : ℕ} {p : RunM C E RealSpec α}
    {f : α → RunM C E RealSpec β} (h : PrgWindow m p)
    (labels : LockstepLabels m p) (rest : ∀ a, PrgWindow n (f a)) (eq : m + n = N) :
    PrgWindow N (p >>= f) := eq ▸ h.bind labels rest

theorem PrgWindow.foldlM {δ : Type} (n : ℕ) (f : α → δ → RunM C E RealSpec α)
    (hf : ∀ a b, PrgWindow n (f a b)) (hl : ∀ a b, LockstepLabels n (f a b))
    (xs : List δ) (a : α) : PrgWindow (xs.length * n) (xs.foldlM f a) := by
  induction xs generalizing a with
  | nil => simpa using PrgWindow.pure a
  | cons x xs ih =>
    rw [List.foldlM_cons, List.length_cons]
    exact (hf a x).le_bind (hl a x) ih (by ring)

section Gadgets
variable [Field E] [Algebra Bit E]
variable {ι : Type} {G : OracleSpec ι}

theorem prgFrom_counted (L : ℕ) (t : (LocalSpec C).Domain) (h : PrgFrom L t) : Counted t := by
  rcases t with noise | q
  · exact h.elim
  · rcases q with q | prg
    · exact h.elim
    · trivial

theorem party_quiet_of_zero (L : ℕ) {p : PartyM C E G α} (h : PartyBound p 0) :
    PartyBudget (PrgFrom L) p 0 := PartyBudget.of_counted (prgFrom_counted L) h

theorem run_quiet_of_zero (L : ℕ) {p : RunM C E G α} (h : RunBound p 0) :
    RunBudget (PrgFrom L) p 0 := RunBudget.of_counted (prgFrom_counted L) h

variable (K : Constants C E)

theorem prgBits_window (L : ℕ) (name : KeyName C) (key : HashOutput) (label idx count : ℕ)
    (below : label < L) :
    IsQueryBoundP (prgBits name key label idx count) (fun t => PrgFrom (C := C) L (.inr t)) 0 := by
  unfold prgBits
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
  have h := queryBound_mapM (fun t => PrgFrom (C := C) L (.inr t))
    (fun position => (query (spec := RoSpec C) (.inr (name, key, label, idx, position)) :
      OracleComp (RoSpec C) Bit)) 0 (List.range count) (fun position _ => ?_)
  · simpa using h
  · change IsQueryBoundP (OracleComp.lift (OracleSpec.query
      (spec := RoSpec C) (.inr (name, key, label, idx, position)))) _ 0
    rw [isQueryBoundP_query_iff]
    simp [PrgFrom, Nat.not_le.mpr below]

theorem prssRandomness_window {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R)
    (hd : ∀ L name key label idx count, label < L →
      IsQueryBoundP (codec.draw name key label idx count) (fun t => PrgFrom (C := C) L (.inr t)) 0)
    (idx count : ℕ) : PrgWindow 1 (prssRandomness ctx codec idx count) := by
  intro st L below
  have hr := prssRandomness_run (G := RealSpec) ctx codec idx count pure st
  rw [bind_pure] at hr
  rw [hr]
  apply PartyBudget.bind (m := 0)
  · apply oracle_bound
    unfold prssDraw termDraws pairDraws
    refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun r _ => ?_)
    · simpa using queryBound_mapM (fun t => PrgFrom (C := C) L (.inr t)) _ 0 C.terms (fun T _ => by
        split_ifs
        · exact hd _ _ _ _ _ _ (by omega)
        · exact isQueryBoundP_pure _ _ _)
    · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
      simpa using queryBound_mapM (fun t => PrgFrom (C := C) L (.inr t)) _ 0 C.parties (fun j _ => by
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · exact hd _ _ _ _ _ _ (by omega))
  · intro r
    exact PartyBudget.pure _

theorem reshare_zero (L : ℕ) {R : Type} [Field R] (ctx : Context C)
    (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R) (count : ℕ) :
    RunBudget (PrgFrom L) (reshare K ctx codec randomness v count : RunM C E G _) 0 := by
  apply run_quiet_of_zero L
  unfold reshare
  exact (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun inbox =>
    (RunBound.record K ctx codec .peer _ count).bind (m := 0) (fun _ => RunBound.pure _))

theorem hash_zero (L : ℕ) (q : Query C) :
    IsQueryBoundP (hashQuery q) (fun t => PrgFrom (C := C) L (.inr t)) 0 := by
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl q))) _ 0
  rw [isQueryBoundP_query_iff]
  simp [PrgFrom]

theorem compare_quiet (L : ℕ) (ctx : Context C) (salts : Shares C Bit) :
    RunBudget (PrgFrom L) (compareDigests ctx salts : RunM C E G _) 0 := by
  unfold compareDigests
  refine RunBudget.bind_zero (RunBudget.get) (fun s => ?_)
  refine RunBudget.bind_zero (RunBudget.lift (oracle_bound ?_)) (fun ds => ?_)
  · simpa using queryBound_mapM (fun t => PrgFrom (C := C) L (.inr t)) _ 0 C.terms
      (fun T _ => by
        split_ifs
        · exact isQueryBoundP_bind (n := 0) (m := 0)
            (hash_zero L _) (fun _ _ => hash_zero L _)
        · exact isQueryBoundP_pure _ _ _)
  · exact RunBudget.bind_zero (RunBudget.lift (party_quiet_of_zero L (PartyBound.exchange _))) (fun inbox =>
        RunBudget.lift (party_quiet_of_zero L (PartyBound.require _)))


theorem collector_zero (L : ℕ) (ctx : Context C) (r : PrssOutput C Bit)
    (v : ℕ → Bit) (count : ℕ) :
    RunBudget (PrgFrom L) (reshareCollector K ctx r v count : RunM C E G _) 0 := by
  apply run_quiet_of_zero L
  unfold reshareCollector
  exact (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun inbox =>
    (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun forward =>
      (RunBound.record K ctx bitCodec .collector _ count).bind (m := 0) (fun _ => RunBound.pure _)))

theorem reshareWith_zero (L : ℕ) (ctx : Context C) (mode : ReshareMode)
    (r : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    RunBudget (PrgFrom L) (reshareWith K ctx mode r v count : RunM C E G _) 0 := by
  cases mode with
  | peer => exact reshare_zero K L ctx _ r v count
  | collector => exact collector_zero K L ctx r v count

theorem inputShares_zero (L : ℕ) (ctx : Context C) (job : Job) :
    PartyBudget (PrgFrom L) (inputShares ctx job : PartyM C E G _) 0 := by
  have hp (seed : HashOutput) (xs : List Point) :
      IsQueryBoundP (xs.flatMapM fun x => bitsOfDigest <$> prf (C := C) seed x)
        (fun t => PrgFrom (C := C) L (.inr t)) 0 := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.flatMapM_cons]
      refine isQueryBoundP_bind (n := 0) (m := 0) ?_
        (fun ys _ => isQueryBoundP_bind ih (fun zs _ => isQueryBoundP_pure _ _ 0))
      simp only [prf, Functor.map_map, isQueryBoundP_map_iff]
      exact hash_zero L _
  unfold inputShares
  refine (oracle_bound (n := 0) ?_).bind (m := 0) (fun terms => PartyBudget.pure _)
  simpa using queryBound_mapM (fun t => PrgFrom (C := C) L (.inr t))
    (fun T => if ctx.self ∈ C.holders T then job.points.flatMapM fun x => bitsOfDigest <$> prf (ctx.keys.seed T) x
      else pure []) 0 C.terms (fun T _ => by
        split_ifs
        · exact hp _ _
        · exact isQueryBoundP_pure _ _ _)

theorem exchange_zero (L : ℕ) (out : Mail C E) :
    PartyBudget (PrgFrom L) (exchange out : PartyM C E G _) 0 :=
  party_quiet_of_zero L (PartyBound.exchange out)

theorem require_zero (L : ℕ) (condition : Prop) [Decidable condition] :
    PartyBudget (PrgFrom L) (require condition : PartyM C E G _) 0 :=
  party_quiet_of_zero L (PartyBound.require condition)

theorem record_zero {R : Type} (L : ℕ) (ctx : Context C) (codec : Codec C E R)
    (mode : ReshareMode) (v : Shares C R) (count : ℕ) :
    RunBudget (PrgFrom L) (record K ctx codec mode v count : RunM C E G _) 0 :=
  run_quiet_of_zero L (RunBound.record K ctx codec mode v count)

theorem openSh_zero (L : ℕ) (ctx : Context C) (v : ℕ → E) (count : ℕ) :
    PartyBudget (PrgFrom L) (openSh K ctx v count : PartyM C E G _) 0 :=
  party_quiet_of_zero L (RunBound.openSh K ctx v count)

theorem openRep_zero (L : ℕ) (ctx : Context C) (v : Shares C Bit) (count : ℕ) :
    PartyBudget (PrgFrom L) (openRep K ctx v count : PartyM C E G _) 0 := by
  have copies (xs : List C.Term) (f : C.Term → List Bit) :
      IsQueryBoundP (xs.mapM fun T => hashQuery (.copy (f T)))
        (fun t => PrgFrom (C := C) L (.inr t)) 0 := by
    simpa using queryBound_mapM (fun t => PrgFrom (C := C) L (.inr t))
      (fun T => hashQuery (.copy (f T))) 0 xs (fun _ _ => hash_zero L _)
  unfold openRep
  exact (oracle_bound (copies _ _)).bind (fun ds =>
    (exchange_zero L _).bind (fun inbox =>
      (oracle_bound (copies _ _)).bind (fun copies =>
        (require_zero L _).bind (fun _ => PartyBudget.pure _))))

theorem bit_window (ctx : Context C) (idx count : ℕ) :
    PrgWindow (E := E) 1 (prssRandomness ctx bitCodec idx count) :=
  prssRandomness_window ctx bitCodec prgBits_window idx count

theorem element_window (ctx : Context C) (idx count : ℕ) :
    PrgWindow 1 (prssRandomness ctx (elementCodec K) idx count) := by
  apply prssRandomness_window
  intro L name key label idx count below
  exact isQueryBoundP_bind (prgBits_window L name key label idx _ below)
    (fun _ _ => isQueryBoundP_pure _ _ 0)

variable [Fintype E] [DecidableEq E]

theorem mult_labels (ctx : Context C) (mode : ReshareMode) (x y : Shares C Bit) (count : ℕ) :
    LockstepLabels 1 ((realRunGadgets (G := RealSpec) K ctx mode).mult x y count) := by
  intro st z final h
  rw [treeSimCheck_mult_state K ctx mode x y count st z final h]

theorem rerand_labels (ctx : Context C) (mode : ReshareMode) (v : Shares C Bit) (count : ℕ) :
    LockstepLabels 1 ((realRunGadgets (G := RealSpec) K ctx mode).rerand v count) := by
  intro st z final h
  rw [treeSimCheck_rerand_state K ctx mode v count st z final h]

theorem mult_window (ctx : Context C) (mode : ReshareMode) (x y : Shares C Bit) (count : ℕ) :
    PrgWindow 1 ((realRunGadgets (G := RealSpec) K ctx mode).mult x y count) :=
  (bit_window (E := E) ctx 0 count).le_bind (lockstepLabels_prssRandomness ctx _ _ _)
    (n := 0) (fun r => PrgWindow.of_quiet (fun L => reshareWith_zero K L ctx mode r _ count)) rfl

theorem rerand_window (ctx : Context C) (mode : ReshareMode) (v : Shares C Bit) (count : ℕ) :
    PrgWindow 1 ((realRunGadgets (G := RealSpec) K ctx mode).rerand v count) :=
  (bit_window (E := E) ctx 0 count).le_bind (lockstepLabels_prssRandomness ctx _ _ _)
    (n := 0) (fun r => PrgWindow.of_quiet (fun L => reshare_zero K L ctx _ r _ count)) rfl

theorem extendMult_window (ctx : Context C) (products : List (Product C E)) :
    PrgWindow 1 ((realCheckGadgets (G := RealSpec) K ctx).extendMult products) :=
  (element_window K ctx 0 products.length).le_bind (lockstepLabels_prssRandomness ctx _ _ _)
    (n := 0) (fun r => PrgWindow.of_quiet (fun L => reshare_zero K L ctx _ r _ _)) rfl

theorem coin_window (ctx : Context C) (count : ℕ) :
    PrgWindow 1 ((realCheckGadgets (G := RealSpec) K ctx).coin count) := by
  apply (element_window K ctx 1 count).le_bind (lockstepLabels_prssRandomness ctx _ _ _)
    (n := 0) _ rfl
  intro r
  apply PrgWindow.of_quiet
  intro L
  unfold coinWith
  exact (RunBudget.lift (party_quiet_of_zero L (RunBound.openSh K ctx _ count))).bind
    (m := 0) (fun _ => .pure _ 0)

theorem coinKey_window (ctx : Context C) :
    PrgWindow 1 (coinKey K (realCheckGadgets (G := RealSpec) K ctx)) := by
  intro st L below
  simp only [coinKey, StateT.run_bind, StateT.run_get, pure_bind]
  refine PartyBudget.bind (m := 0) (coin_window K ctx 1 st L below) ?_
  intro r
  exact RunBudget.lift (oracle_bound (hash_zero L _)) r.2

theorem expand_zero (L : ℕ) (key : HashOutput) (count : ℕ) :
    RunBudget (PrgFrom L) (expand (G := RealSpec) K key count) 0 := by
  apply RunBudget.lift
  apply oracle_bound
  simpa using queryBound_mapM (fun t => PrgFrom (C := C) L (.inr t))
    (fun k => elementOfHash K <$> hashQuery (C := C) (.expand key k)) 0 (List.range count)
    (fun k _ => (isQueryBoundP_map_iff _ _ _).mpr (hash_zero L _))

theorem findChallenge_zero (L : ℕ) (key : HashOutput) (tries index : ℕ) :
    IsQueryBoundP (findChallenge K key tries index) (fun t => PrgFrom (C := C) L (.inr t)) 0 := by
  induction tries generalizing index with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ tries ih =>
    unfold findChallenge
    refine isQueryBoundP_bind (n := 0) (m := 0) (hash_zero L _) (fun h _ => ?_)
    dsimp only
    split
    · exact isQueryBoundP_pure _ _ _
    · exact ih _

theorem challenge_window (ctx : Context C) :
    PrgWindow 1 (challenge K (realCheckGadgets (G := RealSpec) K ctx)) := by
  unfold challenge
  refine (coinKey_window K ctx).le_bind (lockstepLabels_coinKey K ctx) (n := 0) (fun key => ?_) rfl
  apply PrgWindow.of_quiet
  intro L
  refine (RunBudget.lift (oracle_bound (findChallenge_zero K L key _ _))).bind_zero (fun r => ?_)
  cases r with
  | none => exact RunBudget.lift (party_quiet_of_zero L PartyBound.failure)
  | some _ => exact .pure _ _

theorem slice_window (ctx : Context C) (τ : List E) (count : ℕ)
    (v : Shares C E × Shares C E × E) (j : ℕ) :
    PrgWindow 2 (sliceStep K ctx (realCheckGadgets (G := RealSpec) K ctx) τ count v j) := by
  rcases v with ⟨xs, ys, d⟩
  unfold sliceStep
  exact (extendMult_window K ctx _).le_bind
    (lockstepLabels_extendMult K ctx _) (fun _ =>
      (challenge_window K ctx).le_bind (lockstepLabels_challenge K ctx)
        (fun _ => .pure _) rfl) rfl

theorem halving_window (ctx : Context C) (width : ℕ)
    (v : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    PrgWindow 2 (halvingStep K ctx (realCheckGadgets (G := RealSpec) K ctx) width v j) := by
  rcases v with ⟨xs, ys, d⟩
  unfold halvingStep
  exact (extendMult_window K ctx _).le_bind
    (lockstepLabels_extendMult K ctx _) (fun _ =>
      (challenge_window K ctx).le_bind (lockstepLabels_challenge K ctx)
        (fun _ => .pure _) rfl) rfl

theorem final_window (ctx : Context C) (v : (ℕ → E) × (ℕ → E) × E) :
    PrgWindow 4 (finalStep K ctx (realCheckGadgets (G := RealSpec) K ctx) v) := by
  rcases v with ⟨xs, ys, d⟩
  unfold finalStep
  refine (element_window K ctx 1 2).le_bind
    (lockstepLabels_prssRandomness ctx _ _ _) (n := 3) (fun w => ?_) rfl
  refine (extendMult_window K ctx _).le_bind
    (lockstepLabels_extendMult K ctx _) (n := 2) (fun q => ?_) rfl
  refine (bit_window (E := E) ctx 2 _).le_bind
    (lockstepLabels_prssRandomness ctx _ _ _) (n := 1) (fun salts => ?_) rfl
  refine (PrgWindow.of_quiet (fun L => compare_quiet L ctx salts.1)).le_bind
    (lockstepLabels_compareDigests ctx _) (n := 1) (fun _ => ?_) rfl
  refine (challenge_window K ctx).le_bind (lockstepLabels_challenge K ctx)
    (n := 0) (fun r => ?_) rfl
  exact PrgWindow.of_quiet (fun L => (RunBudget.lift (party_quiet_of_zero L (RunBound.openSh K ctx _ 3))).bind_zero
    (fun _ => RunBudget.lift (party_quiet_of_zero L (PartyBound.require _))))

theorem check_window (ctx : Context C) (tuples : List (Tuple C)) :
    PrgWindow (checkLabels (tuples.map (·.count)).sum)
      (check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples) := by
  by_cases hz : (tuples.map (·.count)).sum = 0
  · simp only [check, hz, ↓reduceIte, checkLabels]
    exact .pure _
  · rw [check_eq K ctx _ tuples hz]
    have hs : sliceBits ≤ halvings (tuples.map (·.count)).sum := by unfold halvings; omega
    have labels : LockstepLabels 1 (coinKey K (realCheckGadgets (G := RealSpec) K ctx) >>=
        fun key => expand K key (coins (tuples.map (·.count)).sum)) := (lockstepLabels_coinKey K ctx).le_bind
      (fun key => LockstepLabels.lift (oracleStep _)) (show 1 + 0 = 1 from rfl)
    rw [show checkLabels (tuples.map (·.count)).sum =
      1 + (sliceBits * 2 + ((halvings (tuples.map (·.count)).sum - sliceBits) * 2 + 4)) by
        simp only [checkLabels, if_neg hz]; omega]
    rw [← bind_assoc]
    refine ((coinKey_window K ctx).le_bind (lockstepLabels_coinKey K ctx) (n := 0) (fun key => PrgWindow.of_quiet (fun L => expand_zero K L key _)) rfl).bind labels (fun τ => ?_)
    refine (PrgWindow.of_quiet (fun L => RunBudget.lift (party_quiet_of_zero L (PartyBound.require _)))).le_bind
      (LockstepLabels.lift _)
      (n := sliceBits * 2 + ((halvings (tuples.map (·.count)).sum - sliceBits) * 2 + 4))
      (fun _ => ?_) (by omega)
    refine (PrgWindow.foldlM 2 _ (slice_window K ctx τ _) (TreeCheckHonestDisc.slice_labels K ctx τ _) _ _).le_bind
      (LockstepLabels.foldlM 2 _ (TreeCheckHonestDisc.slice_labels K ctx τ _) _ _)
      (n := (halvings (tuples.map (·.count)).sum - sliceBits) * 2 + 4) (fun v => ?_) (by simp)
    exact (PrgWindow.foldlM 2 _ (halving_window K ctx _) (TreeCheckHonestDisc.halving_labels K ctx _) _ _).le_bind
      (LockstepLabels.foldlM 2 _ (TreeCheckHonestDisc.halving_labels K ctx _) _ _) (final_window K ctx) (by simp)

theorem layer_labels (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit)
    (p : List (C.Term → List Bit) × List (Tuple C)) (layer : ℕ) :
    LockstepLabels 1 (layerBody K (realRunGadgets (G := RealSpec) K ctx mode) jobs p layer) :=
  (mult_labels K ctx mode _ _ _).le_bind (fun _ => .pure _) rfl

theorem beforeVerify_window (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    PrgWindow (depth jobs + 1) (treeSimCheckBeforeVerify K ctx mode jobs inputs) := by
  unfold treeSimCheckBeforeVerify
  refine (PrgWindow.foldlM 1 _ (fun p l => ?_) (layer_labels K ctx mode jobs) _ _).le_bind
    (LockstepLabels.foldlM 1 _ (layer_labels K ctx mode jobs) _ _) (n := 1) (fun p => ?_) (by simp)
  · exact (mult_window K ctx mode _ _ _).le_bind (mult_labels K ctx mode _ _ _) (fun _ => .pure _) rfl
  · exact (rerand_window K ctx mode _ _).le_bind (rerand_labels K ctx mode _ _) (fun _ => .pure _) rfl

theorem batchPrefix_window (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    PartyBudget (PrgFrom (initial.1 + depth (jobs.map (circuits ctx.keys.parameter ·.kind)) + 1))
      (treeSimCheckBatchPrefix K circuits settings ctx jobs initial) 0 := by
  unfold treeSimCheckBatchPrefix
  have inputs : PartyBudget (PrgFrom (initial.1 + depth (jobs.map (circuits ctx.keys.parameter ·.kind)) + 1))
      (jobs.mapM (inputShares ctx) : PartyM C E RealSpec _) 0 := by
    simpa using party_mapM (inputShares ctx) 0 (inputShares_zero _ ctx) jobs
  exact inputs.bind (fun inputs =>
    PartyBudget.bind (beforeVerify_window K ctx settings.mode _ inputs ⟨fun _ => [], initial.1, initial.2⟩ _ (by dsimp; omega)) (fun _ => .pure _))

end Gadgets
/-- Only free PRG reads can write the hidden cache. -/
def FreePrgFrom (L : ℕ) : (WorldSpec C).Domain → Prop
  | .inr q => PrgFrom L q
  | _ => False

/-- The precise exception to the one-query hidden-cache frame. -/
def HiddenPrgFrom (D : C.Coalition) (L : ℕ) : (WorldSpec C).Domain → Prop
  | .inr (.inr (.inr x)) => Hidden D x.1 ∧ L ≤ x.2.2.1
  | _ => False

variable (prims : Primitives) (D : C.Coalition)

theorem logged_query_futureEmpty (L : ℕ) (t : (WorldSpec C).Domain)
    (quiet : ¬ HiddenPrgFrom D L t) (s : TreeSimState C)
    (r : (WorldSpec C).Range t × TreeSimState C)
    (fresh : TreeSimFutureEmpty L s.1.2)
    (run : r ∈ support ((treeSimLoggedWorld prims D t).run s)) :
    TreeSimFutureEmpty L r.2.1.2 := by
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map] at run
  obtain ⟨p, hp, rfl⟩ := run
  rcases t with counted | (noise | (q | x))
  · simp only [streamWorld, onHash, StateT.run_mk, support_map] at hp
    obtain ⟨u, _, rfl⟩ := hp
    exact fresh
  · simp only [streamWorld, onHash, StateT.run_mk, support_map] at hp
    obtain ⟨u, _, rfl⟩ := hp
    exact fresh
  · simp only [streamWorld, onHash, StateT.run_mk, support_map] at hp
    obtain ⟨u, _, rfl⟩ := hp
    exact fresh
  · by_cases hidden : Hidden D x.1
    · have below : x.2.2.1 < L := Nat.lt_of_not_ge (fun ge => quiet ⟨hidden, ge⟩)
      intro y hy
      rw [treeSim_hiddenQuery_frame prims D ((x.1, x.2.1), x.2.2) y
        (by intro eq; have := congrArg (fun a : HiddenAddress C => a.2.1) eq; dsimp at this; omega)
        s.1 p (by unfold hiddenQuery; erw [simulateQ_spec_query]; exact hp)]
      exact fresh y hy
    · simp only [streamWorld, if_neg hidden, onHash, StateT.run_mk, support_map] at hp
      obtain ⟨u, _, rfl⟩ := hp
      exact fresh

theorem quiet_query (L : ℕ) (t : (WorldSpec C).Domain) (quiet : ¬ FreePrgFrom L t)
    (s : TreeSimState C) (r : (WorldSpec C).Range t × TreeSimState C)
    (fresh : TreeSimFutureEmpty L s.1.2)
    (run : r ∈ support ((treeSimLoggedWorld prims D t).run s)) :
    TreeSimFutureEmpty L r.2.1.2 := by
  apply logged_query_futureEmpty prims D L t _ s r fresh run
  rcases t with counted | (noise | (q | x))
  all_goals simp_all [HiddenPrgFrom, FreePrgFrom, PrgFrom]

theorem run_quiet (limit : ℕ) (p : OracleComp (WorldSpec C) α)
    (quiet : IsQueryBoundP p (FreePrgFrom limit) 0) (s : TreeSimState C)
    (honest : TreeSimFutureEmpty limit s.1.2) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) :
    TreeSimFutureEmpty limit r.2.1.2 := by
  induction p using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst r
    exact honest
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at quiet
    have ht : ¬ (FreePrgFrom limit) t := quiet.1.resolve_right (by omega)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at run
    obtain ⟨mid, hmid, hrun⟩ := run
    exact ih mid.1 (by simpa only [if_neg ht] using quiet.2 mid.1) mid.2
      (quiet_query prims D limit t ht s mid honest hmid) r hrun

theorem counted_zero (limit : ℕ) (p : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (worldRoles.adversary p) (FreePrgFrom limit) 0 := by
  change IsQueryBoundP (counted (liftComp p _)) (FreePrgFrom limit) 0
  apply ProgramQuiet.qb0_simulateQ
  intro t
  apply (isQueryBoundP_query_iff _ _ _).2
  simp [FreePrgFrom]

theorem free_zero (limit : ℕ) (p : OracleComp (LocalSpec C) α) (quiet : IsQueryBoundP p (PrgFrom limit) 0) :
    IsQueryBoundP (free p) (FreePrgFrom limit) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at quiet
    rw [free_bind]
    have ht : ¬ PrgFrom limit t := quiet.1.resolve_right (by omega)
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr t)) >>=
      fun r => free (k r)) (FreePrgFrom limit) 0
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl ht, fun r => ?_⟩
    simpa only [FreePrgFrom, if_neg ht] using ih r (by simpa only [if_neg ht] using quiet.2 r)

section Network
variable [Field E] [Algebra Bit E]
variable {A : Adversary C E (Keys C) PEmpty PEmpty}

theorem round_quiet (limit : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, StepBudget (PrgFrom limit) (steps i) 0) :
    IsQueryBoundP (stepRound worldRoles D A noFunctionality state steps) (FreePrgFrom limit) 0 := by
  rw [stepRound_real]
  refine ProgramQuiet.qb0_bind' (counted_zero limit _) fun reply => ?_
  refine ProgramQuiet.qb0_bind' (free_zero limit _ ?_) fun _ => isQueryBoundP_pure _ _ _
  apply isQueryBoundP_sequenceFin
  intro i
  unfold roundLocal
  cases h : steps i with
  | done out => exact isQueryBoundP_pure _ _ _
  | wait out resume =>
    have hb := hsteps i
    rw [h] at hb
    dsimp only
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact advance_zero (PrgFrom limit) _ (hb _)
  | call input _ => exact input.elim

theorem round_steps_quiet (limit : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, StepBudget (PrgFrom limit) (steps i) 0)
    (r : A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E))
    (run : r ∈ support (stepRound worldRoles D A noFunctionality state steps)) :
    ∀ i, StepBudget (PrgFrom limit) (r.2.1 i) 0 := by
  rw [stepRound_real] at run
  simp only [mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨reply, _, locals, hl, rfl⟩ := run
  have each := mem_support_sequenceFin_oc _ _ (treeSimCheck_support_free _ hl)
  intro i
  change StepBudget (PrgFrom limit) (locals i) 0
  have localRun := each i
  unfold roundLocal at localRun
  cases h : steps i with
  | done out =>
    simp only [h, mem_support_pure_iff] at localRun
    rw [localRun]
    trivial
  | wait out resume =>
    have hb := hsteps i
    rw [h] at hb
    simp only [h] at localRun
    split_ifs at localRun
    · simp only [mem_support_pure_iff] at localRun
      rw [localRun]
      trivial
    · exact advance_stepBudget (PrgFrom limit) _ (hb _) _ localRun
  | call input _ => exact input.elim

theorem rounds_futureEmpty (limit : ℕ) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, StepBudget (PrgFrom limit) (steps i) 0)
    (s : TreeSimState C) (honest : TreeSimFutureEmpty limit s.1.2)
    (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executeRounds worldRoles D A noFunctionality fuel state steps)).run s)) :
    TreeSimFutureEmpty limit r.2.1.2 := by
  induction fuel generalizing state steps s with
  | zero =>
    simp only [executeRounds, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst r
    exact honest
  | succ fuel ih =>
    rw [executeRounds] at run
    split_ifs at run
    · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
      subst r
      exact honest
    · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
      obtain ⟨mid, hmid, hrun⟩ := run
      exact ih mid.1.1 mid.1.2.1
        (round_steps_quiet D limit state steps hsteps mid.1 (treeCheck_logged_support prims D _ _ hmid))
        mid.2 (run_quiet prims D limit _ (round_quiet D limit state steps hsteps) s honest mid hmid) hrun

theorem prelude_advance_quiet (limit : ℕ) (gate : OracleComp (LocalSpec C) (Option Unit))
    (p : PartyM C E RealSpec α) (quiet : PartyBudget (PrgFrom limit) p 0)
    (step : Step C E RealSpec α)
    (run : step ∈ support (advance (treeLockstepLocalPrelude gate >>= fun _ => p).run)) :
    StepBudget (PrgFrom limit) step 0 := by
  unfold treeLockstepLocalPrelude at run
  rw [bind_assoc, advance_localStep_bind] at run
  rw [mem_support_bind_iff] at run
  obtain ⟨out, _, run⟩ := run
  cases out with
  | none =>
    simp only [failure_bind] at run
    subst step
    trivial
  | some u =>
    simp only [pure_bind] at run
    exact advance_stepBudget (PrgFrom limit) _ quiet step run

end Network

section Boundary
variable {A : Adversary C E (Keys C) PEmpty PEmpty}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- Transfer the literal first-pass world through the decoder's complete
start equality, then execute only quiet retained prefix continuations. -/
theorem boundary_pre_futureEmpty (b : TreeCheckTailBoundary A)
    (parameter : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter)
    (first : ∀ r, r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (b.program K circuits settings))).run b.batch.world) →
        TreeSimFutureEmpty (b.batch.initial.1 + depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) + 1) r.2.1.2)
    (o : TreeCheckTailCheckpoint A)
    (run : o ∈ support (b.pre prims K circuits settings D)) :
    TreeSimFutureEmpty (b.batch.initial.1 + depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) + 1) o.2.1.2 := by
  let p := fun i => treeLockstepLocalPrelude (b.tail i) >>= fun _ =>
    treeSimCheckBatchPrefix K circuits settings (b.batch.ctx i) b.batch.jobs b.batch.initial
  let k := fun i data => treeSimCheckBatchFinish K circuits (b.batch.ctx i) b.batch.jobs
    b.batch.initial data >>= b.batch.k i
  have timed := treeSimCheckTimed_start D
    (depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) * settings.mode.rounds)
    p k (fun i => treeLockstep_localPrelude_timed _ _ _ (by
      simpa only [parameter i] using treeSimCheckBatchPrefix_timed K circuits settings
        (b.batch.ctx i) b.batch.jobs b.batch.initial))
  have same : (b.program K circuits settings) = fun i => p i >>= k i := by
    funext i
    simp only [TreeCheckTailBoundary.program, treeSimCheckBatchAudit_run_prefix, bind_assoc, p, k]
  unfold TreeCheckTailBoundary.pre executePhase at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨started, hs, run⟩ := run
  have firstRun : ((fun i => suspendStep (k i) (started.1 i)), started.2) ∈
      support ((simulateQ (treeSimLoggedWorld prims D)
        (startSteps worldRoles D (b.program K circuits settings))).run b.batch.world) := by
    rw [same, timed, simulateQ_map, StateT.run_map, support_map]
    exact ⟨started, hs, rfl⟩
  have fresh := first _ firstRun
  apply rounds_futureEmpty prims D
    (b.batch.initial.1 + depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) + 1)
    _ _ started.1 _ started.2 fresh o run
  intro i
  have each := mem_support_sequenceFin_oc _ _ (treeCheck_logged_support prims D _ _ hs) i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, mem_support_pure_iff] at each
    rw [each]
    trivial
  · simp only [if_neg hi, worldRoles] at each
    apply prelude_advance_quiet
      (b.batch.initial.1 + depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) + 1)
      _ _ _ _ (treeSimCheck_support_free _ each)
    simpa only [parameter i] using
      batchPrefix_window K circuits settings (b.batch.ctx i) b.batch.jobs b.batch.initial

end Boundary

end TreeCheckPrgWindow
end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgWindow.PrgWindow.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgWindow.PrgWindow.bind

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgWindow.prssRandomness_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgWindow.prssRandomness_window

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgWindow.bit_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgWindow.bit_window

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgWindow.element_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgWindow.element_window

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgWindow.mult_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgWindow.mult_window

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgWindow.rerand_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgWindow.rerand_window

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgWindow.extendMult_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgWindow.extendMult_window

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgWindow.coin_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgWindow.coin_window

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgWindow.check_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgWindow.check_window

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgWindow.batchPrefix_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgWindow.batchPrefix_window

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgWindow.logged_query_futureEmpty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgWindow.logged_query_futureEmpty

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgWindow.boundary_pre_futureEmpty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgWindow.boundary_pre_futureEmpty

