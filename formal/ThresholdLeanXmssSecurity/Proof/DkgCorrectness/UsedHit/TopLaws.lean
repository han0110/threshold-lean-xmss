import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Partition

/-!
# The two laws of the reduction of a top slot

`topCutGameWith post` is hybrid `j` cut at top slot `j`, with the step `post` on the outputs of the
setup of a live slot. `topReductionViewWith` states that the reduction of top slot `j` with the
distinguisher after `post` accepts with the probability of `UsedHit` in that cut. `topGameCut_of`
gives hybrid `j` as its cut with `post = pure`, from `TopDeadRun` (`topDeadRun`), and
`topGameCutFresh` gives hybrid `j + 1` as its cut with the fresh hidden keys of `seedGenHiddenZ`.
`topLawReal` and `topLawFresh` prove `TopLawReal` and `TopLawFresh`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)

variable {C : Committee}


/-! ## The cut of hybrid `j` at top slot `j` and the parts of the real law -/

section Cut

variable {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (prims : Primitives)

/-- Hybrid `j` cut at top slot `j`. It runs the prefix. At a live place it runs the PRSS setup of the
slot as its own phase and then the rest of top run `j` and the game after it. At a dead or an absent
place it runs `topSkipRest`. -/
def topCutGame (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Bool := do
  match ← topPrefix K circuits settings runLimit j D A with
  | .live s => do
    let r ← executePhase worldRoles D A.net noFunctionality setupRounds s.adversary
      fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))
    topLiveRest K circuits settings runLimit j D A s r
  | .skip s runJ => topSkipRest K circuits settings runLimit j D A s runJ

/-- The game side of the real law. Hybrid `j` and its cut at top slot `j` have one probability of
`UsedHit`. -/
def TopGameCut : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E), ∀ j < runLimit,
    fixedProb K circuits settings runLimit prims D A j =
      usedHitProb prims D (topCutGame K circuits settings runLimit j D A)

/-- The reduction side of the real law. The reduction of top slot `j` with the real challenger accepts
with the probability of `UsedHit` in the cut of hybrid `j`. -/
def TopReductionView : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E), ∀ j < runLimit,
    accepts prims (distinguish (setupExec D (topReduction K circuits settings runLimit prims j D A) [])
        (topDistinguisher K circuits settings runLimit prims j D A)) =
      usedHitProb prims D (topCutGame K circuits settings runLimit j D A)

/-- The cut of hybrid `j` in which the outputs of the setup of a live slot pass through `post`. -/
def topCutGameWith (post : (C.Party → Option (Keys C)) → ProbComp (C.Party → Option (Keys C))) (j : ℕ)
    (D : C.Coalition) (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Bool := do
  match ← topPrefix K circuits settings runLimit j D A with
  | .live s => do
    let r ← executePhase worldRoles D A.net noFunctionality setupRounds s.adversary
      fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))
    let outputs ← free (liftComp (post r.2) (LocalSpec C))
    topLiveRest K circuits settings runLimit j D A s (r.1, outputs)
  | .skip s runJ => topSkipRest K circuits settings runLimit j D A s runJ

theorem topCutGameWith_pure (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    topCutGameWith K circuits settings runLimit pure j D A = topCutGame K circuits settings runLimit j D A := by
  unfold topCutGameWith topCutGame
  simp only [liftComp_pure, ThresholdLeanXmssSecurity.free_pure, pure_bind]

/-- The distinguisher `Z` after `post` on the outputs. -/
def postZ {σ : Type} (post : (C.Party → Option (Keys C)) → ProbComp (C.Party → Option (Keys C)))
    (Z : Distinguisher C σ (Keys C)) : Distinguisher C σ (Keys C) :=
  fun r => liftComp (post r.2) (LocalSpec C) >>= fun outputs => Z (r.1, outputs)

theorem postZ_pure {σ : Type} (Z : Distinguisher C σ (Keys C)) : postZ pure Z = Z := by
  funext r
  simp [postZ]

theorem liftComp_setup {α : Type} (p : ProbComp α) : AllQueriesSatisfy (liftComp p (LocalSpec C)) SetupLocal :=
  AllQueriesSatisfy.simulateQ (allQueriesSatisfy_of_forall (P := fun _ => True) (fun _ => trivial) p) fun t _ =>
    (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inl t) _).2 trivial

open ThresholdLeanXmssSecurity.SigningSelectionProof (noCall_bind noCall_pure noCall_map) in
theorem noProg_topRest (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (s : RealState C A.net.State) :
    NoCall WorldProgramQuery (topRest K circuits settings runLimit j D A s) := by
  unfold topRest
  exact noCall_map _ _ (((noProg_fixedTreeRuns K circuits settings runLimit (j + 1) D A.net _ _).bind fun _ =>
    noProg_fixedSigning K circuits settings runLimit (j + 1) D A) s)

open ThresholdLeanXmssSecurity.SigningSelectionProof (noCall_bind noCall_pure noCall_map) in
/-- The cut of hybrid `j` makes no programming call. -/
theorem topCutGameWith_noProgram (post : (C.Party → Option (Keys C)) → ProbComp (C.Party → Option (Keys C)))
    (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    NoCall WorldProgramQuery (topCutGameWith K circuits settings runLimit post j D A) := by
  unfold topCutGameWith
  refine noCall_bind _ ?_ fun place => ?_
  · unfold topPrefix
    refine noCall_bind _ (Collision.noProgram_realExecution D A.net _ _ _ _) fun p => ?_
    refine noCall_bind _ (noProg_topLoop K circuits settings runLimit j D A.net j _) fun q => ?_
    obtain ⟨ran, s⟩ := q
    dsimp only
    split_ifs <;> exact noCall_pure _ _
  · cases place with
    | live s =>
      refine noCall_bind _ (Collision.noProgram_executePhase D A.net _ _ _) fun r => ?_
      refine noCall_bind _ (Collision.noProgram_free _) fun outputs => ?_
      unfold topLiveRest
      refine noCall_bind _ (Collision.noProgram_executePhase D A.net _ _ _) fun r' => ?_
      obtain ⟨state, outputs⟩ := r'
      exact noCall_bind _ (noProgram_wrongOutput D _ _ _) fun _ => noProg_topRest K circuits settings runLimit j D A _
    | skip s runJ =>
      dsimp only
      unfold topSkipRest
      split
      · exact noCall_bind _ (noProg_fixedTreeRun K circuits settings runLimit (j + 1) D A.net .top s) fun p =>
          noProg_topRest K circuits settings runLimit j D A _
      · exact noCall_map _ _ (noProg_fixedSigning K circuits settings runLimit (j + 1) D A s)

/-- The reduction of top slot `j` with the real challenger and the distinguisher after `post`
accepts with the probability of `UsedHit` in the cut of hybrid `j` with `post`. -/
theorem topReductionViewWith (post : (C.Party → Option (Keys C)) → ProbComp (C.Party → Option (Keys C)))
    (D : C.Coalition) (A : DkgTsigAdversary C E) (j : ℕ) :
    accepts prims (distinguish (setupExec D (topReduction K circuits settings runLimit prims j D A) [])
        (postZ post (topDistinguisher K circuits settings runLimit prims j D A))) =
      usedHitProb prims D (topCutGameWith K circuits settings runLimit post j D A) := by
  have hpart := partition_run prims D (topCutGameWith K circuits settings runLimit post j D A)
    (allQueries_of_noCall (topCutGameWith_noProgram K circuits settings runLimit post j D A)) ∅ keyJointInitial
  rw [mergeSetup_empty] at hpart
  unfold usedHitProb
  rw [hpart, accepts_eq_probOutput]
  have key : (simulateQ (worldAnswer prims) (distinguish (setupExec D (topReduction K circuits settings runLimit prims j D A) [])
      (postZ post (topDistinguisher K circuits settings runLimit prims j D A)))).run' ∅ =ᵈ
      (fun z => decide (UsedHit D z.1.2)) <$> (simulateQ (localAnswer prims)
        ((simulateQ (slotHandler prims D) (topCutGameWith K circuits settings runLimit post j D A)).run
          keyJointInitial)).run ∅ := by
    have hstart : ∀ x z (h : HashCache C),
        (simulateQ (localAnswer prims) ((topReduction K circuits settings runLimit prims j D A).start x z)).run h =
          (fun p => (((p.1.2, p.1.1) : (topReduction K circuits settings runLimit prims j D A).State), p.2)) <$>
            (simulateQ (localAnswer prims) ((simulateQ (slotHandler prims D)
              (topPrefix K circuits settings runLimit j D A)).run keyJointInitial)).run h := by
      intro x z h
      change (simulateQ (localAnswer prims) ((fun r => (r.2, r.1)) <$> (simulateQ (slotHandler prims D)
        (topPrefix K circuits settings runLimit j D A)).run keyJointInitial)).run h = _
      rw [simulateQ_map, StateT.run_map]
    simp only [distinguish, setupExec, realExecution, bind_assoc, simulateQ_bind, StateT.run'_eq,
      StateT.run_bind, map_bind, simulateQ_world_adversary, topCutGameWith]
    refine bind_map_congr (hstart _ _ ∅) fun z => ?_
    obtain ⟨⟨place, priv⟩, h0⟩ := z
    cases place with
    | live s =>
      have hc := executePhase_coupling prims D A.net (topReduction K circuits settings runLimit prims j D A)
        (fun priv st => (priv, TopPlace.live { s with adversary := st })) (fun _ _ _ => rfl) setupRounds s.adversary
        (fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) (fun i => setupKeys_setup i) priv h0
      have e : ((priv, TopPlace.live s) : (topReduction K circuits settings runLimit prims j D A).State) =
          (priv, TopPlace.live { s with adversary := s.adversary }) := rfl
      simp only
      rw [e, ← hc, bind_map_left]
      simp only [simulateQ_bind, StateT.run_bind, map_bind]
      refine EvalDistEq.bind_congr EvalDistEq.rfl fun w => ?_
      rw [honest_run prims D _ (free_setup (liftComp_setup _)) _ _, simulateQ_world_sample]
      simp only [postZ, topDistinguisher, simulateQ_bind, simulateQ_local_sample_seedGensecurity, StateT.run_bind,
        StateT.run_lift, simulateQ_map, StateT.run_map, Functor.map_map, bind_assoc, pure_bind, map_bind,
        bind_map_left]
      exact EvalDistEq.rfl
    | skip s runJ =>
      let st : (topReduction K circuits settings runLimit prims j D A).State := (priv, TopPlace.skip s runJ)
      let phase := executePhase worldRoles D (topReduction K circuits settings runLimit prims j D A) noFunctionality
        setupRounds st fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))
      let Z0 : OracleComp (LocalSpec C) Bool := (fun x => decide (UsedHit D x.2)) <$>
        (simulateQ (slotHandler prims D) (topSkipRest K circuits settings runLimit j D A s runJ)).run priv
      have hidle := executePhase_idle D (topReduction K circuits settings runLimit prims j D A) st (fun _ => rfl)
        setupRounds fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))
      have hdrop : ((simulateQ (worldAnswer prims) phase).run h0 >>= fun a =>
          (fun x => x.1) <$> (simulateQ (localAnswer prims)
            (postZ post (topDistinguisher K circuits settings runLimit prims j D A) a.1)).run a.2) =ᵈ
          (simulateQ (worldAnswer prims) (phase >>= fun _ => worldRoles.adversary Z0)).run' h0 := by
        rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
        refine EvalDistEq.bind_congr_of_support (spec := unifSpec) ((simulateQ (worldAnswer prims) phase).run h0)
          fun a ha => ?_
        have ha' : a.1 ∈ support phase := support_simulateQ_run'_subset (worldAnswer prims) _ h0 (by
          rw [StateT.run'_eq, support_map]
          exact ⟨a, ha, rfl⟩)
        have hst : a.1.1 = st := hidle a.1 ha'
        obtain ⟨⟨st', out⟩, h1⟩ := a
        dsimp only at hst
        subst hst
        rw [simulateQ_world_adversary]
        simp only [postZ, simulateQ_bind, simulateQ_local_sample_seedGensecurity, StateT.run_bind,
          StateT.run_lift, bind_assoc, pure_bind, map_bind]
        exact EvalDistEq.bind_const (post out) ((fun x => x.1) <$> (simulateQ (localAnswer prims) Z0).run h1)
      simp only
      refine hdrop.trans ?_
      refine (discardAnswer prims phase (worldRoles.adversary Z0) h0
        (Collision.noProgram_executePhase D _ setupRounds st _) (Collision.noProgram_adversary Z0)).trans ?_
      rw [simulateQ_world_adversary, StateT.run'_eq]
      simp only [Z0, simulateQ_map, StateT.run_map, Functor.map_map]
      exact EvalDistEq.rfl
  rw [key.prEvent_eq, prEvent_map, prEvent_map]
  simp only [decide_eq_true_eq, usedHit_mergeSetup]

/-- The reduction side of the real law. -/
theorem topReductionView : TopReductionView K circuits settings runLimit prims := by
  intro D A j _
  have h := topReductionViewWith K circuits settings runLimit prims pure D A j
  rwa [postZ_pure, topCutGameWith_pure] at h

/-- The real law from its game side and its reduction side. -/
theorem topLawReal_of_parts (cut : TopGameCut K circuits settings runLimit prims)
    (view : TopReductionView K circuits settings runLimit prims) :
    TopLawReal K circuits settings runLimit prims :=
  fun D A j hj => (cut D A j hj).trans (view D A j hj).symm

/-- The fresh hidden keys of `seedGenHiddenZ` on the outputs of a setup. -/
def freshPost (D : C.Coalition) (outputs : C.Party → Option (Keys C)) : ProbComp (C.Party → Option (Keys C)) := do
  let seeds ← $ᵗ (C.Term → HashOutput)
  let pairs ← $ᵗ (C.Pair → HashOutput)
  pure fun i => (outputs i).map fun k => seedGenHiddenOverlay D i k (dealtKeys 0 seeds pairs i)

theorem seedGenHiddenZ_eq (D : C.Coalition) {σ : Type} (Z : Distinguisher C σ (Keys C)) :
    seedGenHiddenZ D Z = postZ (freshPost D) Z := by
  funext r
  simp [seedGenHiddenZ, postZ, freshPost, bind_assoc]

/-- The game side of the fresh law. Hybrid `j + 1` and the cut of hybrid `j` with the fresh hidden
keys after the setup have one probability of `UsedHit`. -/
def TopGameCutFresh : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E), ∀ j < runLimit,
    fixedProb K circuits settings runLimit prims D A (j + 1) =
      usedHitProb prims D (topCutGameWith K circuits settings runLimit (freshPost D) j D A)

/-- The fresh law from its game side. -/
theorem topLawFresh_of_cut (cut : TopGameCutFresh K circuits settings runLimit prims) :
    TopLawFresh K circuits settings runLimit prims := fun D A j hj => by
  rw [cut D A j hj, seedGenHiddenZ_eq, topReductionViewWith]

end Cut

/-! ## The game side of the real law -/

section GameCut

variable {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The program of an operator in a top run with its own PRSS keys is its PRSS setup and then the rest
of the run. -/
theorem newTree_top_eq (i : C.Party) (keys : Keys C) :
    (newTree K circuits settings i keys emptyTop .top : PartyM C E RealSpec TreeOutput) =
      setupKeys .prss i >>= fun k => topAfterSetup K circuits settings i keys (carrierPrssKeys k) := by
  have e : (newTree K circuits settings i keys emptyTop .top : PartyM C E RealSpec TreeOutput) =
      prssSetup i >>= fun prss => topAfterSetup K circuits settings i keys prss := by
    simp only [newTree, topAfterSetup, ceremonyOutput, ceremonyRun, bind_assoc, StateT.run'_eq,
      StateT.run_bind, StateT.run_lift, map_bind, pure_bind]
    rfl
  rw [e, prssSetup_eq_map, bind_map_left]

omit [Field E] [Algebra Bit E] in
theorem lift2_run {β γ : Type} (X : PartyM C E RealSpec β) (f : β → γ) (s : ℕ × ℕ) (n : ℕ) :
    (fun a => a.1.1) <$> (((StateT.lift (StateT.lift X) >>= fun r => pure (f r) :
      StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) γ).run s).run n) =
      (fun x => x.1) <$> ((StateT.lift X >>= fun r => pure (f r) : StateT (ℕ × ℕ) (PartyM C E RealSpec) γ).run s) := by
  simp [StateT.run_lift]

/-- The program of an operator in a top run of a hybrid is its PRSS setup and then the rest of the run
with the keys that the fresh keys of the first ceremony overlay. -/
theorem slotTree_top_eq (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (i : C.Party) (keys : Keys C) :
    slotTree K circuits settings D fresh i keys emptyTop .top =
      prssSetup i >>= fun prss =>
        topAfterSetup K circuits settings i keys (((fresh 0).map (prssOverlay D i prss)).getD prss) := by
  simp only [slotTree, topAfterSetup, ceremonyOutput, slotCeremony, bind_assoc, StateT.run'_eq,
    StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, map_bind, pure_bind, StateT.run_map,
    Functor.map_map]
  refine bind_congr fun prss => ?_
  refine erases_run_bind _ _ ?_ _ _ _ _ fun z => ?_
  · exact HybridStartProof.erases_batched _ (fun js => HybridStartProof.erases_bind HybridStartProof.erases_get
      fun p => HybridStartProof.erases_bind (HybridStartProof.erases_lift _) fun inputs =>
        HybridStartProof.erases_bind (HybridStartProof.erases_lift _) fun out =>
          HybridStartProof.erases_bind (HybridStartProof.erases_set _) fun _ => HybridStartProof.erases_pure _) _
  · obtain ⟨⟨o, c⟩, n⟩ := z
    rcases o with _ | outputs
    · rfl
    · dsimp only
      rw [lift2_run]
      rfl

theorem sampleSlot_eq (h h' x : ℕ) (hx : h ≤ x) (hx' : h' ≤ x) : sampleSlot (C := C) h x = sampleSlot h' x := by
  simp only [sampleSlot, ite_eq_right (Nat.not_lt.2 hx), ite_eq_right (Nat.not_lt.2 hx')]

theorem sampleSlot_eq_lt (h h' x : ℕ) (hx : x < h) (hx' : x < h') : sampleSlot (C := C) h x = sampleSlot h' x := by
  simp only [sampleSlot, ite_eq_left hx, ite_eq_left hx']

/-- Two hybrids run a tree alike when each slot of the run is at least both indices. -/
theorem fixedTreeRun_congr (h h' : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State)
    (hs : ∀ c < treeSetups tree,
      sampleSlot (C := C) h (fixedSlot runLimit s.runs tree + c) = sampleSlot h' (fixedSlot runLimit s.runs tree + c)) :
    (fixedTreeRun K circuits settings runLimit h (wrongOutput D) D net tree).run s =
      (fixedTreeRun K circuits settings runLimit h' (wrongOutput D) D net tree).run s := by
  have e : (List.range (treeSetups tree)).mapM (fun c => sampleSlot (C := C) h (fixedSlot runLimit s.runs tree + c)) =
      (List.range (treeSetups tree)).mapM (fun c => sampleSlot (C := C) h' (fixedSlot runLimit s.runs tree + c)) := by
    exact TprfSecurityProof.mapM_congr_mem fun c hc => hs c (List.mem_range.1 hc)
  simp only [fixedTreeRun, StateT.run_bind, StateT.run_get, pure_bind, e]

theorem fixedTreeRuns_top_congr (h h' : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    ∀ (m : ℕ) (s : RealState C net.State), h ≤ s.runs .top → h' ≤ s.runs .top →
      (fixedTreeRuns K circuits settings runLimit h (wrongOutput D) D net .top m).run s =
        (fixedTreeRuns K circuits settings runLimit h' (wrongOutput D) D net .top m).run s
  | 0, s, _, _ => rfl
  | m + 1, s, hs, hs' => by
    simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rw [StateT.run_bind, StateT.run_bind, fixedTreeRun_congr K circuits settings runLimit h h' D net .top s
        fun c _ => sampleSlot_eq h h' _ (by simp only [fixedSlot]; omega) (by simp only [fixedSlot]; omega)]
      refine bind_congr_of_forall_mem_support _ fun r hr => ?_
      have hr' := fixedTreeRun_runs K circuits settings runLimit h' D net .top s r hr
      exact fixedTreeRuns_top_congr h h' D net m r.2 (by rw [hr']; simp; omega) (by rw [hr']; simp; omega)
    · rfl

theorem fixedSlot_bottom_ge (runs : Tree → ℕ) (b : Fin (2 ^ layerHeight)) (c : ℕ) :
    runLimit ≤ fixedSlot runLimit runs (.bottom b) + c := by
  simp only [fixedSlot]
  omega

/-- The signing phase is one program in each hybrid up to `runLimit`, because each slot of a bottom run is
at least `runLimit`. -/
theorem fixedSigning_congr (h h' : ℕ) (hh : h ≤ runLimit) (hh' : h' ≤ runLimit) (D : C.Coalition)
    (A : DkgTsigAdversary C E) :
    fixedSigning K circuits settings runLimit h (wrongOutput D) D A =
      fixedSigning K circuits settings runLimit h' (wrongOutput D) D A := by
  have hrun : ∀ b, fixedTreeRun K circuits settings runLimit h (wrongOutput D) D A.net (.bottom b) =
      fixedTreeRun K circuits settings runLimit h' (wrongOutput D) D A.net (.bottom b) := fun b => by
    funext s
    exact fixedTreeRun_congr K circuits settings runLimit h h' D A.net _ s fun c _ =>
      sampleSlot_eq h h' _ (hh.trans (fixedSlot_bottom_ge runLimit _ b c)) (hh'.trans (fixedSlot_bottom_ge runLimit _ b c))
  have horacles : fixedOracles K circuits settings runLimit h (wrongOutput D) D A =
      fixedOracles K circuits settings runLimit h' (wrongOutput D) D A := by
    funext q
    cases q with
    | tree b => simp only [fixedOracles, fixedTreeRequest, fixedTreeRuns, hrun]
    | _ => rfl
  simp only [fixedSigning, horacles]

/-- The first `a + b` top runs are the first `a` runs and, when each of them ran, `b` more. -/
theorem fixedTreeRuns_split (h : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : ℕ) :
    ∀ (a : ℕ) (s : RealState C net.State),
      (fixedTreeRuns K circuits settings runLimit h (wrongOutput D) D net .top (a + b)).run s =
        (topLoop K circuits settings runLimit h D net a).run s >>= fun q =>
          if q.1 then (fixedTreeRuns K circuits settings runLimit h (wrongOutput D) D net .top b).run q.2
          else pure ((), q.2)
  | 0, s => by simp [topLoop]
  | a + 1, s => by
    rw [Nat.add_right_comm]
    simp only [fixedTreeRuns, topLoop, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rw [StateT.run_bind, StateT.run_bind, bind_assoc]
      exact bind_congr fun r => fixedTreeRuns_split h D net b a r.2
    · simp

/-- When the first `count` top runs ran, the runs of the top tree grew by `count`. -/
theorem topLoop_runs (h : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    ∀ (count : ℕ) (s : RealState C net.State),
      ∀ q ∈ support ((topLoop K circuits settings runLimit h D net count).run s), q.1 = true →
        q.2.runs .top = s.runs .top + count
  | 0, s, q, hq, _ => by
    simp only [topLoop, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
    rw [hq]
    rfl
  | count + 1, s, q, hq, hran => by
    simp only [topLoop, StateT.run_bind, StateT.run_get, pure_bind] at hq
    split_ifs at hq
    · rw [StateT.run_bind, mem_support_bind_iff] at hq
      obtain ⟨r, hr, hq⟩ := hq
      have h1 := topLoop_runs h D net count r.2 q hq hran
      have h2 := fixedTreeRun_runs K circuits settings runLimit h D net .top s r hr
      rw [h1, h2]
      simp only [Function.update_self]
      omega
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
      rw [hq] at hran
      simp at hran

/-- The first top runs below slot `j` are one program in hybrids `j` and `j + 1`. -/
theorem topLoop_congr (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    ∀ (count : ℕ) (s : RealState C net.State), s.runs .top + count ≤ j →
      (topLoop K circuits settings runLimit j D net count).run s =
        (topLoop K circuits settings runLimit (j + 1) D net count).run s
  | 0, s, _ => rfl
  | count + 1, s, hs => by
    simp only [topLoop, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rw [StateT.run_bind, StateT.run_bind, fixedTreeRun_congr K circuits settings runLimit j (j + 1) D net .top s
        fun c hc => by
          have hc0 : c = 0 := by simp only [treeSetups] at hc; omega
          subst hc0
          exact sampleSlot_eq_lt _ _ _ (by simp only [fixedSlot]; omega) (by simp only [fixedSlot]; omega)]
      refine bind_congr_of_forall_mem_support _ fun r hr => ?_
      have hr' := fixedTreeRun_runs K circuits settings runLimit (j + 1) D net .top s r hr
      exact topLoop_congr j D net count r.2 (by rw [hr']; simp; omega)
    · rfl

/-- The live cut. A top run at slot `j` in hybrid `j`, with keys at each honest operator, is the PRSS
setup of the slot as its own phase and then the rest of the run. -/
theorem fixedTreeRun_live (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (s : RealState C net.State)
    (hj : s.runs .top = j) (hkeys : ∀ i, i ∉ D.1 → (s.operators i).keys.isSome) :
    (fixedTreeRun K circuits settings runLimit j (wrongOutput D) D net .top).run s =
      executePhase worldRoles D net noFunctionality setupRounds s.adversary
          (fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) >>= fun r =>
        executePhase worldRoles D net noFunctionality (treeFuel circuits settings - setupRounds) r.1
          (fun i => match (s.operators i).keys, r.2 i with
            | some keys, some k => topAfterSetup K circuits settings i keys ⟨k.seed, k.pairKey⟩
            | _, _ => failure) >>= fun so =>
        wrongOutput D (fun i => (s.operators i).keys) .top so.2 >>= fun bad =>
        pure ((), (⟨so.1, fun i => (s.operators i).keep (so.2 i) .top,
          Function.update s.runs .top (s.runs .top + 1), s.closed, s.flag || bad⟩ : RealState C net.State)) := by
  have hfresh : (List.range (treeSetups .top)).mapM
      (fun c => sampleSlot (C := C) j (fixedSlot runLimit s.runs .top + c)) = pure [none] := by
    simp [treeSetups, fixedSlot, hj, sampleSlot]
  let k : C.Party → Keys C → PartyM C E RealSpec TreeOutput := fun i k' =>
    match (s.operators i).keys with
    | some keys => topAfterSetup K circuits settings i keys (carrierPrssKeys k')
    | none => failure
  have hprog : ∀ i, i ∉ D.1 → slotProgram K circuits settings D (fun c => [none].getD c none) i (s.operators i) .top =
      (setupKeys .prss i : PartyM C E RealSpec (Keys C)) >>= k i := by
    intro i hi
    rw [HybridStartProof.slotProgram_eq K circuits settings D _ (fun c => by cases c <;> rfl)]
    obtain ⟨keys, hk⟩ := Option.isSome_iff_exists.1 (hkeys i hi)
    simp only [treeProgram, hk, k]
    exact newTree_top_eq K circuits settings i keys
  have hfuel : treeFuel circuits settings = setupRounds + (treeFuel circuits settings - setupRounds) := by
    unfold treeFuel
    omega
  simp only [fixedTreeRun, StateT.run_bind, StateT.run_get, pure_bind, hfresh, liftComp_pure,
    ThresholdLeanXmssSecurity.free_pure, StateT.run_lift]
  rw [executePhase_congr_honest D net _ _ _ _ hprog, hfuel,
    executePhase_bind_eq (D := D) (A := net) (F := noFunctionality) setupRounds _ _ _ k
      fun i _ => timedQuiet_setupKeys .prss i]
  simp only [Nat.add_sub_cancel_left, bind_assoc, pure_bind, StateT.run_set]
  refine bind_congr fun r => ?_
  have hp : (fun i => (r.2 i).elim failure (k i)) = fun i => match (s.operators i).keys, r.2 i with
      | some keys, some k => topAfterSetup K circuits settings i keys ⟨k.seed, k.pairKey⟩
      | _, _ => failure := by
    funext i
    rcases h1 : (s.operators i).keys with _ | keys <;> rcases h2 : r.2 i with _ | k' <;>
      simp only [k, h1, Option.elim, carrierPrssKeys]
  rw [hp]

/-- The live cut in hybrid `j + 1`. A top run at slot `j` with keys at each honest operator draws the
fresh keys of the slot, runs the PRSS setup of the slot as its own phase and then the rest of the run
with the hidden coordinates of the setup outputs replaced by the fresh keys. -/
theorem fixedTreeRun_liveFresh (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (s : RealState C net.State) (hj : s.runs .top = j) (hkeys : ∀ i, i ∉ D.1 → (s.operators i).keys.isSome) :
    (fixedTreeRun K circuits settings runLimit (j + 1) (wrongOutput D) D net .top).run s =
      free (liftComp (sampleFresh (C := C)) (LocalSpec C)) >>= fun f =>
      executePhase worldRoles D net noFunctionality setupRounds s.adversary
          (fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) >>= fun r =>
        executePhase worldRoles D net noFunctionality (treeFuel circuits settings - setupRounds) r.1
          (fun i => match (s.operators i).keys, r.2 i with
            | some keys, some k => topAfterSetup K circuits settings i keys (prssOverlay D i (carrierPrssKeys k) f)
            | _, _ => failure) >>= fun so =>
        wrongOutput D (fun i => (s.operators i).keys) .top so.2 >>= fun bad =>
        pure ((), (⟨so.1, fun i => (s.operators i).keep (so.2 i) .top,
          Function.update s.runs .top (s.runs .top + 1), s.closed, s.flag || bad⟩ : RealState C net.State)) := by
  have hfresh : (List.range (treeSetups .top)).mapM
      (fun c => sampleSlot (C := C) (j + 1) (fixedSlot runLimit s.runs .top + c)) =
        (fun f => [some f]) <$> sampleFresh := by
    simp [treeSetups, fixedSlot, hj, sampleSlot, map_eq_bind_pure_comp]
  have hfuel : treeFuel circuits settings = setupRounds + (treeFuel circuits settings - setupRounds) := by
    unfold treeFuel
    omega
  simp only [fixedTreeRun, StateT.run_bind, StateT.run_get, pure_bind, hfresh, liftComp_map,
    StateT.run_lift, bind_assoc]
  rw [map_eq_bind_pure_comp, ThresholdLeanXmssSecurity.free_bind, bind_assoc]
  refine bind_congr fun f => ?_
  simp only [Function.comp_apply, ThresholdLeanXmssSecurity.free_pure, pure_bind]
  let k : C.Party → Keys C → PartyM C E RealSpec TreeOutput := fun i k' =>
    match (s.operators i).keys with
    | some keys => topAfterSetup K circuits settings i keys (prssOverlay D i (carrierPrssKeys k') f)
    | none => failure
  have hprog : ∀ i, i ∉ D.1 → slotProgram K circuits settings D (fun c => [some f].getD c none) i (s.operators i) .top =
      (setupKeys .prss i : PartyM C E RealSpec (Keys C)) >>= k i := by
    intro i hi
    obtain ⟨keys, hk⟩ := Option.isSome_iff_exists.1 (hkeys i hi)
    simp only [slotProgram, hk, k]
    rw [slotTree_top_eq, prssSetup_eq_map, bind_map_left]
    rfl
  rw [executePhase_congr_honest D net _ _ _ _ hprog, hfuel,
    executePhase_bind_eq (D := D) (A := net) (F := noFunctionality) setupRounds _ _ _ k
      fun i _ => timedQuiet_setupKeys .prss i]
  simp only [Nat.add_sub_cancel_left, bind_assoc, StateT.run_set]
  refine bind_congr fun r => ?_
  have hp : (fun i => (r.2 i).elim failure (k i)) = fun i => match (s.operators i).keys, r.2 i with
      | some keys, some k => topAfterSetup K circuits settings i keys (prssOverlay D i (carrierPrssKeys k) f)
      | _, _ => failure := by
    funext i
    rcases h1 : (s.operators i).keys with _ | keys <;> rcases h2 : r.2 i with _ | k' <;>
      simp only [k, h1, Option.elim]
  rw [hp]

variable (prims : Primitives)

/-- The dead run. When an honest operator has no keys, top run `j` in hybrid `j` and in hybrid `j + 1`
give one law of the result and of the state of `jointKeyWorld`. Each living operator aborts at the
first exchange of its PRSS setup, before it reads the fresh keys of hybrid `j + 1`. -/
def TopDeadRun : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (j : ℕ) (s : RealState C net.State),
    (∃ i, i ∉ D.1 ∧ (s.operators i).keys = none) → ∀ w : KeyJointState C,
      (simulateQ (jointKeyWorld prims D false)
          ((fixedTreeRun K circuits settings runLimit j (wrongOutput D) D net .top).run s)).run w =ᵈ
        (simulateQ (jointKeyWorld prims D false)
          ((fixedTreeRun K circuits settings runLimit (j + 1) (wrongOutput D) D net .top).run s)).run w

theorem freshPost_eq (D : C.Coalition) (outputs : C.Party → Option (Keys C)) :
    freshPost D outputs = (fun f => fun i => (outputs i).map fun k =>
      seedGenHiddenOverlay D i k (dealtKeys 0 f.1 f.2 i)) <$> sampleFresh (C := C) := by
  simp [freshPost, sampleFresh, map_eq_bind_pure_comp]

/-- Hybrid `h` with `j ≤ h ≤ j + 1` and the cut of hybrid `j` with `post` have one joint law, when the
first `j` top runs agree, and when top run `j` with the game after it has the law of the cut at a
live and at a dead place. -/
theorem fixedGame_cut (h : ℕ) (post : (C.Party → Option (Keys C)) → ProbComp (C.Party → Option (Keys C)))
    (D : C.Coalition) (A : DkgTsigAdversary C E) (j : ℕ) (hj : j < runLimit) (hh : j ≤ h) (hh' : h ≤ j + 1)
    (hloop : ∀ s : RealState C A.net.State, s.runs .top = 0 →
      (topLoop K circuits settings runLimit h D A.net j).run s = (topLoop K circuits settings runLimit j D A.net j).run s)
    (hlive : ∀ s : RealState C A.net.State, s.runs .top = j → (∀ i, i ∉ D.1 → (s.operators i).keys.isSome) →
      JEq prims D ((fixedTreeRun K circuits settings runLimit h (wrongOutput D) D A.net .top).run s >>= fun p =>
          topRest K circuits settings runLimit j D A p.2)
        (executePhase worldRoles D A.net noFunctionality setupRounds s.adversary
            (fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) >>= fun r =>
          free (liftComp (post r.2) (LocalSpec C)) >>= fun outputs =>
            topLiveRest K circuits settings runLimit j D A s (r.1, outputs)))
    (hdead : ∀ s : RealState C A.net.State, s.runs .top = j → (∃ i, i ∉ D.1 ∧ (s.operators i).keys = none) →
      JEq prims D ((fixedTreeRun K circuits settings runLimit h (wrongOutput D) D A.net .top).run s >>= fun p =>
          topRest K circuits settings runLimit j D A p.2)
        ((fixedTreeRun K circuits settings runLimit (j + 1) (wrongOutput D) D A.net .top).run s >>= fun p =>
          topRest K circuits settings runLimit j D A p.2)) :
    JEq prims D (fixedGame K circuits settings runLimit h D A) (topCutGameWith K circuits settings runLimit post j D A) := by
  unfold fixedGame fixedRun topCutGameWith topPrefix
  simp only [map_bind, bind_assoc]
  refine JEq.bind prims (JEq.of_eq prims rfl) fun p => ?_
  obtain ⟨state, keys⟩ := p
  obtain ⟨m, hm⟩ : ∃ m, runLimit = j + (m + 1) := ⟨runLimit - j - 1, by omega⟩
  have hcount : fixedTreeRuns K circuits settings runLimit h (wrongOutput D) D A.net .top runLimit =
      fixedTreeRuns K circuits settings runLimit h (wrongOutput D) D A.net .top (j + (m + 1)) := by
    rw [← hm]
  rw [hcount]
  simp only [StateT.run_bind]
  rw [fixedTreeRuns_split K circuits settings runLimit h D A.net (m + 1) j, hloop _ (by simp [startState])]
  simp only [bind_assoc]
  refine JEq.bind_support prims _ fun q hq => ?_
  have hq' : q.1 = true → q.2.runs .top = j := fun hr => by
    have := topLoop_runs K circuits settings runLimit j D A.net j _ q hq hr
    simpa [startState] using this
  obtain ⟨ran, s⟩ := q
  have hsign : ∀ s', (fixedSigning K circuits settings runLimit h (wrongOutput D) D A).run s' =
      (fixedSigning K circuits settings runLimit (j + 1) (wrongOutput D) D A).run s' := fun s' => by
    rw [fixedSigning_congr K circuits settings runLimit h (j + 1) (by omega) (by omega)]
  have hrest : ∀ s', s'.runs .top = j + 1 →
      ((fixedTreeRuns K circuits settings runLimit h (wrongOutput D) D A.net .top m).run s' >>= fun x =>
        (fixedSigning K circuits settings runLimit h (wrongOutput D) D A).run x.2 >>= fun a =>
          Prod.snd <$> pure (a.1, a.2.flag)) = topRest K circuits settings runLimit j D A s' := by
    intro s' hs'
    have hm' : runLimit - (j + 1) = m := by omega
    unfold topRest
    rw [hm', StateT.run_bind, fixedTreeRuns_top_congr K circuits settings runLimit h (j + 1) D A.net m s'
      (by omega) (by omega), map_bind]
    refine bind_congr fun x => ?_
    rw [hsign]
    simp only [map_pure]
    rw [map_eq_bind_pure_comp]
    rfl
  by_cases hrun : ran = true ∧ mayRun runLimit D s .top
  · obtain ⟨hran, hmay⟩ := hrun
    subst hran
    have hs : s.runs .top = j := hq' rfl
    simp only [ite_true, true_and, hmay, fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind]
    simp only [bind_assoc]
    have hcont : ((fixedTreeRun K circuits settings runLimit h (wrongOutput D) D A.net .top).run s >>= fun p =>
        (fixedTreeRuns K circuits settings runLimit h (wrongOutput D) D A.net .top m).run p.2 >>= fun x =>
          (fixedSigning K circuits settings runLimit h (wrongOutput D) D A).run x.2 >>= fun a =>
            Prod.snd <$> pure (a.1, a.2.flag)) =
        (fixedTreeRun K circuits settings runLimit h (wrongOutput D) D A.net .top).run s >>= fun p =>
          topRest K circuits settings runLimit j D A p.2 :=
      bind_congr_of_forall_mem_support _ fun p hp => by
        rw [← hrest p.2 (by rw [fixedTreeRun_runs K circuits settings runLimit h D A.net .top s p hp]; simp [hs])]
    rw [hcont]
    by_cases hk : ∀ i, i ∉ D.1 → (s.operators i).keys.isSome
    · rw [ite_eq_left hk, pure_bind]
      exact hlive s hs hk
    · rw [ite_eq_right hk, pure_bind]
      unfold topSkipRest
      simp only [↓reduceIte]
      have hd : ∃ i, i ∉ D.1 ∧ (s.operators i).keys = none := by
        push Not at hk
        obtain ⟨i, hi, hn⟩ := hk
        exact ⟨i, hi, by simpa using hn⟩
      exact (hdead s hs hd).trans prims (JEq.of_eq prims (bind_congr fun p => by obtain ⟨⟨⟩, s'⟩ := p; rfl))
  · apply JEq.of_eq
    dsimp only
    have hfirst : (if ran = true then
        (fixedTreeRuns K circuits settings runLimit h (wrongOutput D) D A.net .top (m + 1)).run s
        else pure ((), s)) = pure ((), s) := by
      split_ifs with hr
      · simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind]
        rw [ite_eq_right fun hm' => hrun ⟨hr, hm'⟩]
        rfl
      · rfl
    rw [hfirst, ite_eq_right hrun, pure_bind, pure_bind]
    unfold topSkipRest
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hsign]
    simp only [map_pure]
    rw [map_eq_bind_pure_comp]
    rfl

/-- The game side of the real law from the dead run. -/
theorem topGameCut_of (dead : TopDeadRun K circuits settings runLimit prims) :
    TopGameCut K circuits settings runLimit prims := by
  intro D A j hj
  have key := fixedGame_cut K circuits settings runLimit prims j pure D A j hj le_rfl (Nat.le_succ j)
    (fun _ _ => rfl)
    (fun s hs hk => JEq.of_eq prims (by
      rw [fixedTreeRun_live K circuits settings runLimit j D A.net s hs hk]
      simp only [bind_assoc, pure_bind, liftComp_pure, ThresholdLeanXmssSecurity.free_pure]
      refine bind_congr fun r => ?_
      unfold topLiveRest
      dsimp only
      rfl))
    (fun s _ hd => JEq.bind prims (dead D A.net j s hd) fun _ => JEq.of_eq prims rfl)
  rw [topCutGameWith_pure] at key
  unfold fixedProb usedHitProb
  rw [(key keyJointInitial).prEvent_eq]

/-- The game side of the fresh law. -/
theorem topGameCutFresh : TopGameCutFresh K circuits settings runLimit prims := by
  intro D A j hj
  have key := fixedGame_cut K circuits settings runLimit prims (j + 1) (freshPost D) D A j hj (Nat.le_succ j) le_rfl
    (fun s hs => (topLoop_congr K circuits settings runLimit j D A.net j s (by omega)).symm)
    (fun s hs hk => by
      rw [fixedTreeRun_liveFresh K circuits settings runLimit j D A.net s hs hk]
      simp only [bind_assoc]
      refine (freeDraw_commutes prims D _ _ _).trans prims (JEq.bind prims (JEq.of_eq prims rfl) fun r => ?_)
      apply JEq.of_eq
      rw [freshPost_eq, liftComp_map, map_eq_bind_pure_comp, ThresholdLeanXmssSecurity.free_bind, bind_assoc]
      refine bind_congr fun f => ?_
      simp only [Function.comp_apply, ThresholdLeanXmssSecurity.free_pure, pure_bind]
      unfold topLiveRest
      dsimp only
      have hp : (fun i => match (s.operators i).keys, r.2 i with
          | some keys, some k => topAfterSetup K circuits settings i keys (prssOverlay D i (carrierPrssKeys k) f)
          | _, _ => failure) = fun i => match (s.operators i).keys,
            Option.map (fun k => seedGenHiddenOverlay D i k (dealtKeys 0 f.1 f.2 i)) (r.2 i) with
          | some keys, some k => topAfterSetup K circuits settings i keys ⟨k.seed, k.pairKey⟩
          | _, _ => failure := by
        funext i
        rcases (s.operators i).keys with _ | keys <;> rcases r.2 i with _ | k' <;>
          simp only [Option.map_none, Option.map_some]
        rfl
      rw [hp]
      rfl)
    (fun _ _ _ => JEq.of_eq prims rfl)
  unfold fixedProb usedHitProb
  rw [(key keyJointInitial).prEvent_eq]

/-- `TopLawFresh`. The reduction of top slot `j` with the fresh hidden keys of `seedGenHiddenZ`
accepts with the probability of hybrid `j + 1`. -/
theorem topLawFresh : TopLawFresh K circuits settings runLimit prims :=
  topLawFresh_of_cut K circuits settings runLimit prims (topGameCutFresh K circuits settings runLimit prims)

/-- `TopLawReal` from the dead run. -/
theorem topLawReal_of_deadRun (dead : TopDeadRun K circuits settings runLimit prims) :
    TopLawReal K circuits settings runLimit prims :=
  topLawReal_of_parts K circuits settings runLimit prims (topGameCut_of K circuits settings runLimit prims dead)
    (topReductionView K circuits settings runLimit prims)

/-- The dead run. When an honest operator has no keys, the phase of a top run does not read the fresh
keys, and the private draw of the fresh keys keeps the state of `jointKeyWorld`. -/
theorem topDeadRun : TopDeadRun K circuits settings runLimit prims := by
  intro D net j s ⟨i₀, hi₀, hk₀⟩ w
  let X : C.Party → PartyM C E RealSpec (PrssKeys C) := fun i =>
    match (s.operators i).keys with
    | some _ => prssSetup i
    | none => failure
  let k : (ℕ → Option (FreshKeys C)) → C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput := fun fresh i prss =>
    match (s.operators i).keys with
    | some keys => topAfterSetup K circuits settings i keys (((fresh 0).map (prssOverlay D i prss)).getD prss)
    | none => failure
  have hprog : ∀ fresh : ℕ → Option (FreshKeys C), ∀ i, i ∉ D.1 →
      slotProgram K circuits settings D fresh i (s.operators i) .top = X i >>= k fresh i := by
    intro fresh i _
    rcases hk : (s.operators i).keys with _ | keys
    · simp only [slotProgram, X, k, hk]
      exact (failure_bind _).symm
    · simp only [slotProgram, X, k, hk]
      exact slotTree_top_eq K circuits settings D fresh i keys
  have hB : ∀ fresh : List (Option (FreshKeys C)),
      executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary
          (fun i => slotProgram K circuits settings D (fun c => fresh.getD c none) i (s.operators i) .top) =
        executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary
          (fun i => slotProgram K circuits settings D (fun c => ([] : List (Option (FreshKeys C))).getD c none) i
            (s.operators i) .top) := by
    intro fresh
    rw [executePhase_congr_honest D net _ _ _ _ (hprog _), executePhase_congr_honest D net _ _ _ _ (hprog _)]
    refine executePhase_dead_congr D net _ _ X _ _ i₀ hi₀ (by simp only [X, hk₀]) fun i hi => ?_
    rcases hk : (s.operators i).keys with _ | keys
    · simp only [X, hk]
      exact startsWithRound_failure
    · simp only [X, hk]
      exact startsWithRound_prssSetup i
  simp only [fixedTreeRun, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, hB, simulateQ_bind,
    jointKeyWorld_sample_run, bind_map_left]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, bind_assoc]
  exact (EvalDistEq.bind_const _ _).trans (EvalDistEq.bind_const _ _).symm

/-- `TopLawReal`. The reduction of top slot `j` with the real challenger accepts with the probability
of hybrid `j`. -/
theorem topLawReal : TopLawReal K circuits settings runLimit prims :=
  topLawReal_of_deadRun K circuits settings runLimit prims (topDeadRun K circuits settings runLimit prims)

end GameCut

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.topLawReal_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.topLawReal_of_parts

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.topReductionView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.topReductionView

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.topLawFresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.topLawFresh

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.topLawReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.topLawReal
