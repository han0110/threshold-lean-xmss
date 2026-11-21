import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.BottomLaws

/-!
# The game after a pause of a bottom slot

`pause_dead`, `pause_liveFirst` and `pause_liveSecond` give the law of the game after a pause of hybrid `j`
as the cut, and `pause_liveFirstFresh` and `pause_liveSecondFresh` give it for hybrid `j + 1`. The live
second setup uses `BottomHeadSplit` and one parameter of the honest operators, which comes from
`SeedParameterAgreeJoint`. `bottomLawReal_of_split` and `bottomLawFresh_of_split` prove the two laws.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_bind noCall_pure noCall_map)

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (prims : Primitives)
/-- A run whose phase does not read the fresh keys has one law in each hybrid. -/
theorem fixedTreeRun_draw_unread (h h' : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State)
    (hB : ∀ fresh : List (Option (FreshKeys C)),
      executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary
          (fun i => slotProgram K circuits settings D (fun c => fresh.getD c none) i (s.operators i) tree) =
        executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary
          (fun i => slotProgram K circuits settings D (fun c => ([] : List (Option (FreshKeys C))).getD c none) i
            (s.operators i) tree)) :
    JEq prims D ((fixedTreeRun K circuits settings runLimit h (wrongOutput D) D net tree).run s)
      ((fixedTreeRun K circuits settings runLimit h' (wrongOutput D) D net tree).run s) := by
  intro w
  simp only [fixedTreeRun, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, hB, simulateQ_bind,
    jointKeyWorld_sample_run, bind_map_left]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, bind_assoc]
  exact (EvalDistEq.bind_const _ _).trans (EvalDistEq.bind_const _ _).symm

/-- A dead run of a bottom tree. When an honest operator has no keys or no top tree, the phase does not
read the fresh keys, and the private draw of the fresh keys keeps the state of `jointKeyWorld`. -/
theorem bottomDeadRun (h h' : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) (hdead : ¬ AliveAtStart D s) :
    JEq prims D ((fixedTreeRun K circuits settings runLimit h (wrongOutput D) D net (.bottom b)).run s)
      ((fixedTreeRun K circuits settings runLimit h' (wrongOutput D) D net (.bottom b)).run s) := by
  intro w
  obtain ⟨i₀, hi₀, hd₀⟩ : ∃ i, i ∉ D.1 ∧ ¬ ((s.operators i).keys.isSome ∧ (s.operators i).top.isSome) := by
    unfold AliveAtStart at hdead
    push Not at hdead
    obtain ⟨i, hi, h⟩ := hdead
    exact ⟨i, hi, fun h' => absurd (h h'.1) (by simp [h'.2])⟩
  let X : C.Party → PartyM C E RealSpec (PrssKeys C) := fun i =>
    match (s.operators i).keys, (s.operators i).top with
    | some _, some _ => prssSetup i
    | _, _ => failure
  have hX₀ : X i₀ = failure := by
    simp only [X]
    rcases hk : (s.operators i₀).keys with _ | keys <;> rcases ht : (s.operators i₀).top with _ | top
    all_goals first | rfl | simp [hk, ht] at hd₀
  have hB : ∀ fresh : List (Option (FreshKeys C)),
      executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary
          (fun i => slotProgram K circuits settings D (fun c => fresh.getD c none) i (s.operators i) (.bottom b)) =
        executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary
          (fun i => slotProgram K circuits settings D (fun c => ([] : List (Option (FreshKeys C))).getD c none) i
            (s.operators i) (.bottom b)) := by
    intro fresh
    choose k₁ hk₁ using fun i => slotProgram_bottom_split K circuits settings D (fun c => fresh.getD c none) i
      (s.operators i) b
    choose k₂ hk₂ using fun i => slotProgram_bottom_split K circuits settings D
      (fun c => ([] : List (Option (FreshKeys C))).getD c none) i (s.operators i) b
    rw [executePhase_congr_honest D net _ _ _ _ fun i _ => hk₁ i, executePhase_congr_honest D net _ _ _ _ fun i _ => hk₂ i]
    refine executePhase_dead_congr D net _ _ X _ _ i₀ hi₀ hX₀ fun i _ => ?_
    simp only [X]
    split
    · exact startsWithRound_prssSetup i
    · exact startsWithRound_failure
  exact fixedTreeRun_draw_unread K circuits settings runLimit prims h h' D net _ s hB w

/-- A run whose program starts with the PRSS setup at each honest operator, for each draw of the fresh
keys, is the setup as its own phase and then the rest of the run. -/
theorem fixedTreeRun_setupSplit {α : Type} (h : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) (s : RealState C net.State) (g : ProbComp α) (φ : α → List (Option (FreshKeys C)))
    (hfresh : (List.range (treeSetups tree)).mapM (fun c => sampleSlot (C := C) h (fixedSlot runLimit s.runs tree + c)) =
      φ <$> g)
    (k : α → C.Party → Keys C → PartyM C E RealSpec TreeOutput)
    (hprog : ∀ a i, i ∉ D.1 → slotProgram K circuits settings D (fun c => (φ a).getD c none) i (s.operators i) tree =
      (setupKeys .prss i : PartyM C E RealSpec (Keys C)) >>= k a i) :
    (fixedTreeRun K circuits settings runLimit h (wrongOutput D) D net tree).run s =
      free (liftComp g (LocalSpec C)) >>= fun a =>
      executePhase worldRoles D net noFunctionality setupRounds s.adversary
          (fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) >>= fun r =>
        executePhase worldRoles D net noFunctionality (treeFuel circuits settings - setupRounds) r.1
          (fun i => (r.2 i).elim failure (k a i)) >>= fun so =>
        wrongOutput D (fun i => (s.operators i).keys) tree so.2 >>= fun bad =>
        pure ((), (⟨so.1, fun i => (s.operators i).keep (so.2 i) tree,
          Function.update s.runs tree (s.runs tree + 1), s.closed, s.flag || bad⟩ : RealState C net.State)) := by
  have hfuel : treeFuel circuits settings = setupRounds + (treeFuel circuits settings - setupRounds) := by
    unfold treeFuel
    omega
  simp only [fixedTreeRun, StateT.run_bind, StateT.run_get, pure_bind, hfresh, liftComp_map,
    StateT.run_lift, bind_assoc]
  rw [map_eq_bind_pure_comp, ThresholdLeanXmssSecurity.free_bind, bind_assoc]
  refine bind_congr fun a => ?_
  simp only [Function.comp_apply, ThresholdLeanXmssSecurity.free_pure, pure_bind]
  rw [executePhase_congr_honest D net _ _ _ _ (hprog a), hfuel,
    executePhase_bind_eq (D := D) (A := net) (F := noFunctionality) setupRounds _ _ _ (k a)
      fun i _ => timedQuiet_setupKeys .prss i]
  simp only [Nat.add_sub_cancel_left, bind_assoc, StateT.run_set]

/-- The tail with no fresh keys is the tail of the bottom tree. -/
theorem tailWith_none (D : C.Coalition) (i : C.Party) (operator : OperatorState C) (b : Fin (2 ^ layerHeight))
    (x : HeadOut) : tailWith K circuits settings D none i operator b x =
      CheckTiming.bottomTail K circuits settings i operator b x := by
  unfold tailWith CheckTiming.bottomTail
  rcases hk : operator.keys with _ | keys <;> rcases ht : operator.top with _ | top <;> simp only
  simp only [CheckTiming.secondPart, secondAfter, batchesWith, StateT.run_bind, CheckTiming.ceremonyRun_run_keys,
    bind_assoc, pure_bind, withFresh, Option.map_none, Option.getD_none]
  rfl

/-- The program of an operator in a bottom run is its first setup, the head on the keys of the setup
with `fresh 0`, and the tail with `fresh 1`. -/
theorem slotProgram_bottom_setup (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (i : C.Party)
    (operator : OperatorState C) (b : Fin (2 ^ layerHeight)) (keys : Keys C) (top : TopTree)
    (hk : operator.keys = some keys) (ht : operator.top = some top) :
    slotProgram K circuits settings D fresh i operator (.bottom b) =
      (setupKeys .prss i : PartyM C E RealSpec (Keys C)) >>= fun key =>
        (firstAfter K circuits settings i keys b (withFresh D i (fresh 0) (carrierPrssKeys key))).run (0, 0) >>= fun p =>
          p.1.elim failure fun x => tailWith K circuits settings D (fresh 1) i operator b (x, p.2) := by
  rw [slotProgram_bottom_cut K circuits settings D fresh i operator b]
  unfold headWith
  simp only [hk, ht]
  rw [prssSetup_eq_map, bind_map_left]
  simp only [bind_assoc]
  refine bind_congr fun key => bind_congr fun p => ?_
  rcases p with ⟨_ | x, st⟩
  · simp [Option.elim]
  · simp [Option.elim]

theorem mapM_two_sampleSlot_none (h x : ℕ) (hx : h ≤ x) :
    (List.range 2).mapM (fun c => sampleSlot (C := C) h (x + c)) = pure [none, none] := by
  have h0 : sampleSlot (C := C) h x = pure none := by simp only [sampleSlot]; rw [ite_eq_right (by omega)]
  have h1 : sampleSlot (C := C) h (x + 1) = pure none := by simp only [sampleSlot]; rw [ite_eq_right (by omega)]
  simp [List.range_succ, h0, h1]

/-- The program of an alive operator in a bottom run with no fresh keys in the second setup is its first
setup and then `afterFirstSetup`. -/
theorem slotProgram_bottom_afterFirst (D : C.Coalition) (i : C.Party) (operator : OperatorState C)
    (b : Fin (2 ^ layerHeight)) (hk : operator.keys.isSome) (ht : operator.top.isSome) :
    slotProgram K circuits settings D (fun c => [none, none].getD c none) i operator (.bottom b) =
      (setupKeys .prss i : PartyM C E RealSpec (Keys C)) >>= fun key =>
        afterFirstSetup K circuits settings i operator b (some key) := by
  obtain ⟨keys, hk⟩ := Option.isSome_iff_exists.1 hk
  obtain ⟨top, ht⟩ := Option.isSome_iff_exists.1 ht
  rw [slotProgram_bottom_setup K circuits settings D _ i operator b keys top hk ht]
  refine bind_congr fun key => ?_
  simp only [afterFirstSetup, hk, ht]
  refine bind_congr fun q => ?_
  rcases q with ⟨_ | x, st⟩
  · simp only [Option.elim]
  · simp only [Option.elim]
    exact tailWith_none K circuits settings D i operator b _

/-- The pause at a live first setup in hybrid `j`. The run is the setup and then the rest of the run, as
the cut. -/
theorem pause_liveFirst (j forge : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (p : BottomPause C A.net.State)
    (hp : PauseInRange runLimit forge j p) (halive : AliveAtStart D p.state) (hc : slotParity runLimit j = 0) :
    JEq prims D ((fixedTreeRun K circuits settings runLimit j (wrongOutput D) D A.net (.bottom p.b)).run p.state >>=
        fun x => resumeAfter K circuits settings runLimit j D A p x.2)
      (pauseAt K circuits settings runLimit j D A p >>= cutRest K circuits settings runLimit pure j D A) := by
  have hslot : fixedSlot runLimit p.state.runs (.bottom p.b) = j := by
    have h1 := hp.1
    generalize fixedSlot runLimit p.state.runs (.bottom p.b) = x at h1 ⊢
    generalize slotParity runLimit j = c at h1 hc
    omega
  have hsplit := fixedTreeRun_setupSplit K circuits settings runLimit j D A.net (.bottom p.b) p.state (pure ())
    (fun _ => [none, none]) (by
      rw [hslot, map_pure]
      exact mapM_two_sampleSlot_none j j le_rfl)
    (fun _ i key => afterFirstSetup K circuits settings i (p.state.operators i) p.b (some key))
    (fun _ i hi => slotProgram_bottom_afterFirst K circuits settings D i _ p.b (halive i hi).1 (halive i hi).2)
  apply JEq.of_eq
  have hout : ∀ r : A.net.State × (C.Party → Option (Keys C)),
      (fun i => (r.2 i).elim failure fun key => afterFirstSetup K circuits settings i (p.state.operators i) p.b
        (some key)) = fun i => afterFirstSetup K circuits settings i (p.state.operators i) p.b (r.2 i) := by
    intro r
    funext i
    rcases r.2 i with _ | key
    · simp only [Option.elim, afterFirstSetup]
      split <;> first | rfl | simp_all
    · rfl
  unfold pauseAt
  rw [ite_eq_right (not_not.2 halive), ite_eq_left hc, pure_bind, hsplit]
  simp only [cutRest, liftComp_pure, ThresholdLeanXmssSecurity.free_pure, pure_bind, bind_assoc, hout]
  simp only [bottomRest, hc, ite_true, bind_assoc, finishRun, pure_bind]

/-- The pause at a dead run. The run of hybrid `h` and the run of hybrid `j + 1` have one law. -/
theorem pause_dead (h j : ℕ) (post : (C.Party → Option (Keys C)) → ProbComp (C.Party → Option (Keys C)))
    (D : C.Coalition) (A : DkgTsigAdversary C E) (p : BottomPause C A.net.State) (hdead : ¬ AliveAtStart D p.state) :
    JEq prims D ((fixedTreeRun K circuits settings runLimit h (wrongOutput D) D A.net (.bottom p.b)).run p.state >>=
        fun x => resumeAfter K circuits settings runLimit j D A p x.2)
      (pauseAt K circuits settings runLimit j D A p >>= cutRest K circuits settings runLimit post j D A) := by
  unfold pauseAt
  rw [ite_eq_left hdead, pure_bind]
  simp only [cutRest, bottomRest]
  generalize j + 1 = J
  refine JEq.bind prims (bottomDeadRun K circuits settings runLimit prims h J D A.net p.b p.state hdead) fun x => ?_
  obtain ⟨⟨⟩, s⟩ := x
  exact JEq.of_eq prims rfl

/-- A run of a tree, with its draw, its phase and its end. -/
theorem fixedTreeRun_unfold (h : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) :
    (fixedTreeRun K circuits settings runLimit h (wrongOutput D) D net tree).run s =
      free (liftComp ((List.range (treeSetups tree)).mapM fun c =>
        sampleSlot (C := C) h (fixedSlot runLimit s.runs tree + c)) (LocalSpec C)) >>= fun fresh =>
      executePhase worldRoles D net noFunctionality (treeFuel circuits settings) s.adversary
          (fun i => slotProgram K circuits settings D (fun c => fresh.getD c none) i (s.operators i) tree) >>= fun so =>
        wrongOutput D (fun i => (s.operators i).keys) tree so.2 >>= fun bad =>
        pure ((), (⟨so.1, fun i => (s.operators i).keep (so.2 i) tree,
          Function.update s.runs tree (s.runs tree + 1), s.closed, s.flag || bad⟩ : RealState C net.State)) := by
  simp only [fixedTreeRun, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc, StateT.run_set]

/-- The tail of an alive operator is its second setup and then `afterSecondSetup`. -/
theorem bottomTail_setup (D : C.Coalition) (i : C.Party) (operator : OperatorState C) (b : Fin (2 ^ layerHeight)) (x : HeadOut)
    (hk : operator.keys.isSome) (ht : operator.top.isSome) :
    CheckTiming.bottomTail K circuits settings i operator b x =
      (setupKeys .prss i : PartyM C E RealSpec (Keys C)) >>= fun key =>
        afterSecondSetup K circuits settings i operator b (some x) (some key) := by
  obtain ⟨keys, hk⟩ := Option.isSome_iff_exists.1 hk
  obtain ⟨top, ht⟩ := Option.isSome_iff_exists.1 ht
  rw [← tailWith_none K circuits settings D i operator b x]
  simp only [tailWith, afterSecondSetup, hk, ht, withFresh, Option.map_none, Option.getD_none]
  rw [prssSetup_eq_map, bind_map_left]
  rfl

/-- The tail phase of a live second setup is the setup as its own phase and then `afterSecondSetup`. -/
theorem tailPhase_live (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (st : net.State)
    (operators : C.Party → OperatorState C) (b : Fin (2 ^ layerHeight)) (heads : C.Party → Option HeadOut)
    (halive : ∀ i, i ∉ D.1 → (operators i).keys.isSome ∧ (operators i).top.isSome)
    (hheads : ∀ i, i ∉ D.1 → (heads i).isSome) (n : ℕ) :
    executePhase worldRoles D net noFunctionality (setupRounds + n) st
        (fun i => (heads i).elim failure (CheckTiming.bottomTail K circuits settings i (operators i) b)) =
      executePhase worldRoles D net noFunctionality setupRounds st
          (fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) >>= fun r =>
        executePhase worldRoles D net noFunctionality n r.1
          (fun i => afterSecondSetup K circuits settings i (operators i) b (heads i) (r.2 i)) := by
  let k : C.Party → Keys C → PartyM C E RealSpec TreeOutput := fun i key =>
    afterSecondSetup K circuits settings i (operators i) b (heads i) (some key)
  have hprog : ∀ i, i ∉ D.1 → (heads i).elim failure (CheckTiming.bottomTail K circuits settings i (operators i) b) =
      (setupKeys .prss i : PartyM C E RealSpec (Keys C)) >>= k i := by
    intro i hi
    show (heads i).elim failure (CheckTiming.bottomTail K circuits settings i (operators i) b) =
      (setupKeys .prss i : PartyM C E RealSpec (Keys C)) >>= fun key =>
        afterSecondSetup K circuits settings i (operators i) b (heads i) (some key)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hheads i hi)
    rw [hx]
    exact bottomTail_setup K circuits settings D i _ b x (halive i hi).1 (halive i hi).2
  rw [executePhase_congr_honest D net _ _ _ _ hprog,
    executePhase_bind_eq (D := D) (A := net) (F := noFunctionality) setupRounds _ _ _ k
      fun i _ => timedQuiet_setupKeys .prss i]
  refine bind_congr fun r => ?_
  congr 1
  funext i
  rcases r.2 i with _ | key
  · simp only [Option.elim, afterSecondSetup]
    split <;> first | rfl | simp_all
  · rfl

theorem mapM_two_sampleSlot_firstFresh (h x : ℕ) (hx : x + 1 = h) :
    (List.range 2).mapM (fun c => sampleSlot (C := C) h (x + c)) = (fun f => [some f, none]) <$> sampleFresh := by
  have h0 : sampleSlot (C := C) h x = some <$> sampleFresh := by simp only [sampleSlot]; rw [ite_eq_left (by omega)]
  have h1 : sampleSlot (C := C) h (x + 1) = pure none := by simp only [sampleSlot]; rw [ite_eq_right (by omega)]
  simp [List.range_succ, h0, h1, map_eq_bind_pure_comp]

/-- The pause at a live second setup in hybrid `j`. The head split and the split at the second setup give
the cut. -/
theorem pause_liveSecond (j forge : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (p : BottomPause C A.net.State)
    (hp : PauseInRange runLimit forge j p) (halive : AliveAtStart D p.state) (hc : slotParity runLimit j ≠ 0)
    (hpar : ∀ i, i ∉ D.1 → ∀ keys, (p.state.operators i).keys = some keys → keys.parameter = stateParameter D p.state)
    (split : BottomHeadSplit K circuits settings prims) :
    JEq prims D ((fixedTreeRun K circuits settings runLimit j (wrongOutput D) D A.net (.bottom p.b)).run p.state >>=
        fun x => resumeAfter K circuits settings runLimit j D A p x.2)
      (pauseAt K circuits settings runLimit j D A p >>= cutRest K circuits settings runLimit pure j D A) := by
  have hslot : fixedSlot runLimit p.state.runs (.bottom p.b) + 1 = j := by
    have h1 := hp.1
    have h2 : slotParity runLimit j < 2 := Nat.mod_lt _ (by omega)
    generalize fixedSlot runLimit p.state.runs (.bottom p.b) = x at h1 ⊢
    generalize slotParity runLimit j = c at h1 hc h2
    omega
  have hfresh := mapM_two_sampleSlot_firstFresh (C := C) j _ hslot
  have hF := headRounds_add_le circuits settings (stateParameter D p.state) p.b
  rw [fixedTreeRun_unfold]
  unfold pauseAt
  rw [ite_eq_right (not_not.2 halive), ite_eq_right hc]
  change JEq prims D ((free (liftComp ((List.range 2).mapM fun c => sampleSlot (C := C) j
      (fixedSlot runLimit p.state.runs (.bottom p.b) + c)) (LocalSpec C)) >>= _) >>= _)
    ((free (liftComp ((List.range 2).mapM fun c => sampleSlot (C := C) j
      (fixedSlot runLimit p.state.runs (.bottom p.b) + c)) (LocalSpec C)) >>= _) >>= _)
  rw [hfresh, liftComp_map, map_eq_bind_pure_comp, ThresholdLeanXmssSecurity.free_bind]
  simp only [bind_assoc]
  refine JEq.bind prims (JEq.of_eq prims rfl) fun f => ?_
  simp only [Function.comp_apply, ThresholdLeanXmssSecurity.free_pure, pure_bind]
  have hJ := fun w => split D A.net p.state.adversary (fun c => [some f, none].getD c none) p.state.operators p.b w
    (stateParameter D p.state) hpar
  refine (JEq.bind prims (Y := executePhase worldRoles D A.net noFunctionality
      (CheckTiming.firstRounds circuits settings (stateParameter D p.state) (.bottom p.b)) p.state.adversary
      (fun i => headWith K circuits settings D ([some f, none].getD 0 none) i (p.state.operators i) p.b) >>= fun r =>
        executePhase worldRoles D A.net noFunctionality
          (treeFuel circuits settings - CheckTiming.firstRounds circuits settings (stateParameter D p.state) (.bottom p.b))
          r.1 fun i => (r.2 i).elim failure (tailWith K circuits settings D ([some f, none].getD 1 none) i
            (p.state.operators i) p.b)) hJ fun so => JEq.of_eq prims rfl).trans prims ?_
  simp only [bind_assoc]
  refine JEq.bind prims (JEq.of_eq prims rfl) fun r => ?_
  have htail : (fun i => (r.2 i).elim failure (tailWith K circuits settings D ([some f, none].getD 1 none) i
      (p.state.operators i) p.b)) =
      fun i => (r.2 i).elim failure (CheckTiming.bottomTail K circuits settings i (p.state.operators i) p.b) := by
    funext i
    have e : ([some f, none].getD 1 none : Option (FreshKeys C)) = none := rfl
    rw [e, show tailWith K circuits settings D none i (p.state.operators i) p.b =
      CheckTiming.bottomTail K circuits settings i (p.state.operators i) p.b from
      funext (tailWith_none K circuits settings D i _ p.b)]
  rw [htail]
  by_cases hall : ∀ i, i ∉ D.1 → (r.2 i).isSome
  · rw [ite_eq_left hall, pure_bind]
    apply JEq.of_eq
    have hfuel : treeFuel circuits settings - headRounds circuits settings D p =
        setupRounds + (treeFuel circuits settings - headRounds circuits settings D p - setupRounds) := by
      unfold headRounds
      omega
    change (executePhase worldRoles D A.net noFunctionality (treeFuel circuits settings - headRounds circuits settings D p)
      r.1 _ >>= _) = _
    rw [hfuel, tailPhase_live K circuits settings D A.net r.1 p.state.operators p.b r.2 halive hall]
    simp only [cutRest, bottomRest, hc, ite_false, liftComp_pure, ThresholdLeanXmssSecurity.free_pure, pure_bind,
      bind_assoc, finishRun]
  · rw [ite_eq_right hall, pure_bind]
    apply JEq.of_eq
    simp only [cutRest, bottomRest, bind_assoc, finishRun, pure_bind]
    rfl

/-- The seed generation on the network, answered by `jointKeyWorld` from each state of the adversary and
each world. Two honest operators with an output hold the same parameter. It is `SeedParameterAgree` of
`Setup.lean` with `jointKeyWorld` in place of `streamWorld`. -/
def SeedParameterAgreeJoint (D : C.Coalition) : Prop :=
  ∀ (net : Adversary C E Unit PEmpty PEmpty) (st : net.State) (w : KeyJointState C),
    ∀ y ∈ support ((simulateQ (jointKeyWorld prims D false) (executePhase worldRoles D net noFunctionality setupRounds st
        (fun i => (seedGen i : PartyM C E RealSpec (Keys C))))).run w),
    ∀ i j Ki Kj, i ∉ D.1 → j ∉ D.1 → y.1.2 i = some Ki → y.1.2 j = some Kj → Ki.parameter = Kj.parameter

omit [Field E] [Algebra Bit E] in
theorem oneParameter_start (D : C.Coalition) (agree : SeedParameterAgreeJoint (E := E) prims D) (A : DkgTsigAdversary C E)
    (w : KeyJointState C) (z : (A.net.State × (C.Party → Option (Keys C))) × KeyJointState C)
    (hz : z ∈ support ((simulateQ (jointKeyWorld prims D false) (realExecution D A.net noFunctionality
      setupRounds (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [])).run w)) :
    OneParameter D (startState D z.1.1 z.1.2) := by
  unfold realExecution at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨a, -, hz⟩ := hz
  have hagree := agree A.net a.1 a.2 _ hz
  by_cases h : ∃ j, j ∉ D.1 ∧ ∃ kj, z.1.2 j = some kj
  · obtain ⟨j, hj, kj, hkj⟩ := h
    exact ⟨kj.parameter, fun i hi ki hki => hagree i j ki kj hi hj hki hkj⟩
  · exact ⟨0, fun i hi ki hki => absurd ⟨i, hi, ki, hki⟩ h⟩

theorem usedHitProb_unit (D : C.Coalition) (g : OracleComp (WorldSpec C) Bool) :
    usedHitProb prims D g = usedHitProb prims D ((fun _ => true) <$> ((fun _ => ()) <$> g)) := by
  unfold usedHitProb
  simp only [simulateQ_map, StateT.run_map, Functor.map_map]

theorem JEq.map {D : C.Coalition} {α β : Type} {X Y : OracleComp (WorldSpec C) α} (f : α → β)
    (h : JEq prims D X Y) : JEq prims D (f <$> X) (f <$> Y) := fun w => by
  simp only [simulateQ_map, StateT.run_map]
  exact (h w).map _

/-- The game side of the real law, from the head split and the parameter of the seed generation. -/
theorem bottomGameCut (split : BottomHeadSplit K circuits settings prims)
    (agree : ∀ D : C.Coalition, SeedParameterAgreeJoint (E := E) prims D) :
    BottomGameCut K circuits settings runLimit prims := by
  intro D A forge hforge j hlo _
  have key := fixedGame_bottomCut K circuits settings runLimit prims j pure D A forge j hforge hlo le_rfl
    (fun w z hz => oneParameter_start prims D (agree D) A w z hz) fun p hp hm hone => by
      have hk := bottomRuns_of_pauseInRange runLimit forge j p hp
      rw [walkRest_pause K circuits settings runLimit j j D A p hm (fun oa st s hs =>
        signing_congr_above K circuits settings runLimit j hlo D A oa st s hs) hk]
      by_cases halive : AliveAtStart D p.state
      · by_cases hc : slotParity runLimit j = 0
        · exact pause_liveFirst K circuits settings runLimit prims j forge D A p hp halive hc
        · exact pause_liveSecond K circuits settings runLimit prims j forge D A p hp halive hc
            (oneParameter_stateParameter D p.state hone) split
      · exact pause_dead K circuits settings runLimit prims j j pure D A p halive
  unfold fixedProb
  rw [usedHitProb_unit]
  unfold usedHitProb
  rw [((JEq.map prims (fun _ => true) key) keyJointInitial).prEvent_eq]

/-- `BottomLawReal` from the head split and the parameter of the seed generation in `jointKeyWorld`. -/
theorem bottomLawReal_of_split (split : BottomHeadSplit K circuits settings prims)
    (agree : ∀ D : C.Coalition, SeedParameterAgreeJoint (E := E) prims D) :
    BottomLawReal K circuits settings runLimit prims :=
  bottomLawReal_of_cut K circuits settings runLimit prims (bottomGameCut K circuits settings runLimit prims split agree)

/-! ## The fresh law -/

/-- The program of an alive operator in a bottom run with fresh keys `f` in the first setup only is its
first setup and then `afterFirstSetup` on the overlaid keys. -/
theorem slotProgram_bottom_afterFirstFresh (D : C.Coalition) (f : FreshKeys C) (i : C.Party)
    (operator : OperatorState C) (b : Fin (2 ^ layerHeight)) (hk : operator.keys.isSome) (ht : operator.top.isSome) :
    slotProgram K circuits settings D (fun c => [some f, none].getD c none) i operator (.bottom b) =
      (setupKeys .prss i : PartyM C E RealSpec (Keys C)) >>= fun key =>
        afterFirstSetup K circuits settings i operator b (some (seedGenHiddenOverlay D i key (dealtKeys 0 f.1 f.2 i))) := by
  obtain ⟨keys, hk⟩ := Option.isSome_iff_exists.1 hk
  obtain ⟨top, ht⟩ := Option.isSome_iff_exists.1 ht
  rw [slotProgram_bottom_setup K circuits settings D _ i operator b keys top hk ht]
  refine bind_congr fun key => ?_
  simp only [afterFirstSetup, hk, ht]
  refine bind_congr fun q => ?_
  rcases q with ⟨_ | x, st⟩
  · simp only [Option.elim]
  · simp only [Option.elim]
    exact tailWith_none K circuits settings D i operator b _

/-- The pause at a live first setup in hybrid `j + 1`. The draw of the fresh keys of slot `j` moves after
the setup. -/
theorem pause_liveFirstFresh (j forge : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (p : BottomPause C A.net.State) (hp : PauseInRange runLimit forge j p) (halive : AliveAtStart D p.state)
    (hc : slotParity runLimit j = 0) (h : ℕ) (hh : h = j + 1) :
    JEq prims D ((fixedTreeRun K circuits settings runLimit h (wrongOutput D) D A.net (.bottom p.b)).run p.state >>=
        fun x => resumeAfter K circuits settings runLimit j D A p x.2)
      (pauseAt K circuits settings runLimit j D A p >>= cutRest K circuits settings runLimit (freshPost D) j D A) := by
  have hslot : fixedSlot runLimit p.state.runs (.bottom p.b) = j := by
    have h1 := hp.1
    generalize fixedSlot runLimit p.state.runs (.bottom p.b) = x at h1 ⊢
    generalize slotParity runLimit j = c at h1 hc
    omega
  have hsplit := fixedTreeRun_setupSplit K circuits settings runLimit h D A.net (.bottom p.b) p.state sampleFresh
    (fun f => [some f, none]) (by
      rw [hslot]
      exact mapM_two_sampleSlot_firstFresh h j (by omega))
    (fun f i key => afterFirstSetup K circuits settings i (p.state.operators i) p.b
      (some (seedGenHiddenOverlay D i key (dealtKeys 0 f.1 f.2 i))))
    (fun f i hi => slotProgram_bottom_afterFirstFresh K circuits settings D f i _ p.b (halive i hi).1 (halive i hi).2)
  unfold pauseAt
  rw [ite_eq_right (not_not.2 halive), ite_eq_left hc, pure_bind, hsplit]
  simp only [bind_assoc, cutRest]
  refine (freeDraw_commutes prims D _ _ _).trans prims (JEq.bind prims (JEq.of_eq prims rfl) fun r => ?_)
  apply JEq.of_eq
  rw [freshPost_eq, liftComp_map, map_eq_bind_pure_comp, ThresholdLeanXmssSecurity.free_bind, bind_assoc]
  refine bind_congr fun f => ?_
  simp only [Function.comp_apply, ThresholdLeanXmssSecurity.free_pure, pure_bind, bottomRest, hc, ite_true,
    bind_assoc, finishRun]
  have hout : (fun i => (r.2 i).elim failure fun key => afterFirstSetup K circuits settings i (p.state.operators i) p.b
      (some (seedGenHiddenOverlay D i key (dealtKeys 0 f.1 f.2 i)))) =
      fun i => afterFirstSetup K circuits settings i (p.state.operators i) p.b
        ((r.2 i).map fun k => seedGenHiddenOverlay D i k (dealtKeys 0 f.1 f.2 i)) := by
    funext i
    rcases r.2 i with _ | key
    · simp only [Option.elim, Option.map_none, afterFirstSetup]
      split <;> first | rfl | simp_all
    · rfl
  rw [hout]

theorem mapM_two_sampleSlot_bothFresh (h x : ℕ) (hx : x + 2 ≤ h) :
    (List.range 2).mapM (fun c => sampleSlot (C := C) h (x + c)) =
      sampleFresh >>= fun f₀ => sampleFresh >>= fun f₁ => pure [some f₀, some f₁] := by
  have h0 : sampleSlot (C := C) h x = some <$> sampleFresh := by simp only [sampleSlot]; rw [ite_eq_left (by omega)]
  have h1 : sampleSlot (C := C) h (x + 1) = some <$> sampleFresh := by
    simp only [sampleSlot]; rw [ite_eq_left (by omega)]
  simp [List.range_succ, h0, h1, map_eq_bind_pure_comp]

/-- The tail with fresh keys `f` of an alive operator is its second setup and then `afterSecondSetup` on
the overlaid keys. -/
theorem tailWith_some_setup (D : C.Coalition) (f : FreshKeys C) (i : C.Party) (operator : OperatorState C)
    (b : Fin (2 ^ layerHeight)) (x : HeadOut) (hk : operator.keys.isSome) (ht : operator.top.isSome) :
    tailWith K circuits settings D (some f) i operator b x =
      (setupKeys .prss i : PartyM C E RealSpec (Keys C)) >>= fun key =>
        afterSecondSetup K circuits settings i operator b (some x)
          (some (seedGenHiddenOverlay D i key (dealtKeys 0 f.1 f.2 i))) := by
  obtain ⟨keys, hk⟩ := Option.isSome_iff_exists.1 hk
  obtain ⟨top, ht⟩ := Option.isSome_iff_exists.1 ht
  simp only [tailWith, afterSecondSetup, hk, ht, withFresh, Option.map_some, Option.getD_some]
  rw [prssSetup_eq_map, bind_map_left]
  rfl

/-- The tail phase of a live second setup with fresh keys `f` is the setup as its own phase and then
`afterSecondSetup` on the overlaid keys. -/
theorem tailPhase_liveFresh (D : C.Coalition) (f : FreshKeys C) (net : Adversary C E Unit PEmpty PEmpty)
    (st : net.State) (operators : C.Party → OperatorState C) (b : Fin (2 ^ layerHeight))
    (heads : C.Party → Option HeadOut)
    (halive : ∀ i, i ∉ D.1 → (operators i).keys.isSome ∧ (operators i).top.isSome)
    (hheads : ∀ i, i ∉ D.1 → (heads i).isSome) (n : ℕ) :
    executePhase worldRoles D net noFunctionality (setupRounds + n) st
        (fun i => (heads i).elim failure (tailWith K circuits settings D (some f) i (operators i) b)) =
      executePhase worldRoles D net noFunctionality setupRounds st
          (fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) >>= fun r =>
        executePhase worldRoles D net noFunctionality n r.1
          (fun i => afterSecondSetup K circuits settings i (operators i) b (heads i)
            ((r.2 i).map fun k => seedGenHiddenOverlay D i k (dealtKeys 0 f.1 f.2 i))) := by
  let k : C.Party → Keys C → PartyM C E RealSpec TreeOutput := fun i key =>
    afterSecondSetup K circuits settings i (operators i) b (heads i)
      (some (seedGenHiddenOverlay D i key (dealtKeys 0 f.1 f.2 i)))
  have hprog : ∀ i, i ∉ D.1 → (heads i).elim failure (tailWith K circuits settings D (some f) i (operators i) b) =
      (setupKeys .prss i : PartyM C E RealSpec (Keys C)) >>= k i := by
    intro i hi
    show (heads i).elim failure (tailWith K circuits settings D (some f) i (operators i) b) =
      (setupKeys .prss i : PartyM C E RealSpec (Keys C)) >>= fun key =>
        afterSecondSetup K circuits settings i (operators i) b (heads i)
          (some (seedGenHiddenOverlay D i key (dealtKeys 0 f.1 f.2 i)))
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hheads i hi)
    rw [hx]
    exact tailWith_some_setup K circuits settings D f i _ b x (halive i hi).1 (halive i hi).2
  rw [executePhase_congr_honest D net _ _ _ _ hprog,
    executePhase_bind_eq (D := D) (A := net) (F := noFunctionality) setupRounds _ _ _ k
      fun i _ => timedQuiet_setupKeys .prss i]
  refine bind_congr fun r => ?_
  congr 1
  funext i
  rcases r.2 i with _ | key
  · simp only [Option.elim, Option.map_none, afterSecondSetup]
    split <;> first | rfl | simp_all
  · rfl

/-- A tail phase in which an honest operator has no head reads neither tail. -/
theorem tailPhase_skip_congr (D : C.Coalition) (f : Option (FreshKeys C)) (net : Adversary C E Unit PEmpty PEmpty)
    (st : net.State) (operators : C.Party → OperatorState C) (b : Fin (2 ^ layerHeight))
    (heads : C.Party → Option HeadOut)
    (halive : ∀ i, i ∉ D.1 → (operators i).keys.isSome ∧ (operators i).top.isSome)
    (hskip : ¬ ∀ i, i ∉ D.1 → (heads i).isSome) (n : ℕ) :
    executePhase worldRoles D net noFunctionality n st
        (fun i => (heads i).elim failure (tailWith K circuits settings D f i (operators i) b)) =
      executePhase worldRoles D net noFunctionality n st
        (fun i => (heads i).elim failure (CheckTiming.bottomTail K circuits settings i (operators i) b)) := by
  obtain ⟨i₀, hi₀, hn₀⟩ : ∃ i, i ∉ D.1 ∧ heads i = none := by
    push Not at hskip
    obtain ⟨i, hi, h⟩ := hskip
    exact ⟨i, hi, by simpa using h⟩
  let X : C.Party → PartyM C E RealSpec (PrssKeys C) := fun i => (heads i).elim failure fun _ => prssSetup i
  let k : Option (FreshKeys C) → C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput := fun g i prss =>
    match (operators i).keys, (operators i).top, heads i with
    | some keys, some top, some x =>
        (secondAfter K circuits settings i keys top b x.1 (withFresh D i g prss)).run x.2 >>= fun p => p.1.elim failure pure
    | _, _, _ => failure
  have hprog : ∀ g : Option (FreshKeys C), ∀ i, i ∉ D.1 →
      (heads i).elim failure (tailWith K circuits settings D g i (operators i) b) = X i >>= k g i := by
    intro g i hi
    obtain ⟨keys, hk⟩ := Option.isSome_iff_exists.1 (halive i hi).1
    obtain ⟨top, ht⟩ := Option.isSome_iff_exists.1 (halive i hi).2
    simp only [X, k]
    rcases heads i with _ | x
    · simp only [Option.elim, failure_bind]
    · simp only [Option.elim, tailWith, hk, ht]
  have hnone : (fun i => (heads i).elim failure (CheckTiming.bottomTail K circuits settings i (operators i) b)) =
      fun i => (heads i).elim failure (tailWith K circuits settings D none i (operators i) b) := by
    funext i
    rw [show tailWith K circuits settings D none i (operators i) b =
      CheckTiming.bottomTail K circuits settings i (operators i) b from
      funext (tailWith_none K circuits settings D i _ b)]
  rw [hnone, executePhase_congr_honest D net _ _ _ _ (hprog f), executePhase_congr_honest D net _ _ _ _ (hprog none)]
  refine executePhase_dead_congr D net _ _ X _ _ i₀ hi₀ (by simp only [X, hn₀, Option.elim]) fun i _ => ?_
  simp only [X]
  rcases heads i with _ | x
  · exact startsWithRound_failure
  · exact startsWithRound_prssSetup i

/-- A private draw whose value is not read keeps the law. -/
theorem JEq.free_const {D : C.Coalition} {α β : Type} (g : ProbComp α) (Y : OracleComp (WorldSpec C) β) :
    JEq prims D (free (liftComp g (LocalSpec C)) >>= fun _ => Y) Y := fun w => by
  simp only [simulateQ_bind, StateT.run_bind, jointKeyWorld_sample_run, bind_map_left]
  exact EvalDistEq.bind_const _ _

/-- The pause at a live second setup in hybrid `j + 1`. The draw of the fresh keys of slot `j` moves
after the head and the setup. -/
theorem pause_liveSecondFresh (j forge : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (p : BottomPause C A.net.State) (hp : PauseInRange runLimit forge j p) (halive : AliveAtStart D p.state)
    (hc : slotParity runLimit j ≠ 0)
    (hpar : ∀ i, i ∉ D.1 → ∀ keys, (p.state.operators i).keys = some keys → keys.parameter = stateParameter D p.state)
    (split : BottomHeadSplit K circuits settings prims) (h : ℕ) (hh : h = j + 1) :
    JEq prims D ((fixedTreeRun K circuits settings runLimit h (wrongOutput D) D A.net (.bottom p.b)).run p.state >>=
        fun x => resumeAfter K circuits settings runLimit j D A p x.2)
      (pauseAt K circuits settings runLimit j D A p >>= cutRest K circuits settings runLimit (freshPost D) j D A) := by
  have hslot : fixedSlot runLimit p.state.runs (.bottom p.b) + 1 = j := by
    have h1 := hp.1
    have h2 : slotParity runLimit j < 2 := Nat.mod_lt _ (by omega)
    generalize fixedSlot runLimit p.state.runs (.bottom p.b) = x at h1 ⊢
    generalize slotParity runLimit j = c at h1 hc h2
    omega
  have hF := headRounds_add_le circuits settings (stateParameter D p.state) p.b
  rw [fixedTreeRun_unfold]
  unfold pauseAt
  rw [ite_eq_right (not_not.2 halive), ite_eq_right hc]
  change JEq prims D ((free (liftComp ((List.range 2).mapM fun c => sampleSlot (C := C) h
      (fixedSlot runLimit p.state.runs (.bottom p.b) + c)) (LocalSpec C)) >>= _) >>= _)
    ((free (liftComp ((List.range 2).mapM fun c => sampleSlot (C := C) j
      (fixedSlot runLimit p.state.runs (.bottom p.b) + c)) (LocalSpec C)) >>= _) >>= _)
  rw [mapM_two_sampleSlot_bothFresh h _ (by omega), mapM_two_sampleSlot_firstFresh j _ hslot, liftComp_map,
    map_eq_bind_pure_comp, liftComp_bind, ThresholdLeanXmssSecurity.free_bind, ThresholdLeanXmssSecurity.free_bind]
  simp only [bind_assoc, liftComp_bind, ThresholdLeanXmssSecurity.free_bind, Function.comp_apply, liftComp_pure,
    ThresholdLeanXmssSecurity.free_pure, pure_bind]
  refine JEq.bind prims (JEq.of_eq prims rfl) fun f₀ => ?_
  refine (JEq.bind prims (JEq.of_eq prims rfl) fun f₁ => JEq.bind prims
    (Y := executePhase worldRoles D A.net noFunctionality
      (CheckTiming.firstRounds circuits settings (stateParameter D p.state) (.bottom p.b)) p.state.adversary
      (fun i => headWith K circuits settings D (some f₀) i (p.state.operators i) p.b) >>= fun r =>
        executePhase worldRoles D A.net noFunctionality
          (treeFuel circuits settings - CheckTiming.firstRounds circuits settings (stateParameter D p.state) (.bottom p.b))
          r.1 fun i => (r.2 i).elim failure (tailWith K circuits settings D (some f₁) i (p.state.operators i) p.b))
    (fun w => split D A.net p.state.adversary (fun c => [some f₀, some f₁].getD c none) p.state.operators p.b w
      (stateParameter D p.state) hpar) fun so => JEq.of_eq prims rfl).trans prims ?_
  simp only [bind_assoc]
  refine (freeDraw_commutes prims D _ _ _).trans prims ?_
  have e0 : ([some f₀, none].getD 0 none : Option (FreshKeys C)) = some f₀ := rfl
  rw [e0]
  refine JEq.bind prims (JEq.of_eq prims rfl) fun r => ?_
  by_cases hall : ∀ i, i ∉ D.1 → (r.2 i).isSome
  · rw [ite_eq_left hall, pure_bind]
    have hfuel : treeFuel circuits settings - headRounds circuits settings D p =
        setupRounds + (treeFuel circuits settings - headRounds circuits settings D p - setupRounds) := by
      unfold headRounds
      omega
    change JEq prims D (free (liftComp sampleFresh (LocalSpec C)) >>= fun f₁ =>
      executePhase worldRoles D A.net noFunctionality (treeFuel circuits settings - headRounds circuits settings D p)
        r.1 _ >>= _) _
    rw [hfuel]
    simp only [tailPhase_liveFresh K circuits settings D _ A.net r.1 p.state.operators p.b r.2 halive hall, bind_assoc]
    refine (freeDraw_commutes prims D _ _ _).trans prims (JEq.bind prims (JEq.of_eq prims rfl) fun r' => ?_)
    apply JEq.of_eq
    rw [freshPost_eq, liftComp_map, map_eq_bind_pure_comp, ThresholdLeanXmssSecurity.free_bind, bind_assoc]
    refine bind_congr fun f₁ => ?_
    simp only [Function.comp_apply, ThresholdLeanXmssSecurity.free_pure, pure_bind, bottomRest, hc, ite_false,
      bind_assoc, finishRun]
  · rw [ite_eq_right hall, pure_bind]
    simp only [tailPhase_skip_congr K circuits settings D _ A.net r.1 p.state.operators p.b r.2 halive hall]
    refine (JEq.free_const prims _ _).trans prims (JEq.of_eq prims ?_)
    simp only [cutRest, bottomRest, bind_assoc, finishRun, pure_bind]
    rfl

/-- The game side of the fresh law, from the head split and the parameter of the seed generation. -/
theorem bottomGameCutFresh (split : BottomHeadSplit K circuits settings prims)
    (agree : ∀ D : C.Coalition, SeedParameterAgreeJoint (E := E) prims D) :
    BottomGameCutFresh K circuits settings runLimit prims := by
  intro D A forge hforge j hlo _
  have key : ∀ h, h = j + 1 → JEq prims D ((fun _ => ()) <$> fixedGame K circuits settings runLimit h D A)
      (bottomCutGameWith K circuits settings runLimit (freshPost D) j D A) := by
    intro h hh
    refine fixedGame_bottomCut K circuits settings runLimit prims h (freshPost D) D A forge j hforge hlo (by omega)
      (fun w z hz => oneParameter_start prims D (agree D) A w z hz) fun p hp hm hone => ?_
    have hk := bottomRuns_of_pauseInRange runLimit forge j p hp
    have hsig : ∀ (oa : OracleComp (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) Forgery) st
        (s : RealState C A.net.State), (j - runLimit) / 2 + 1 ≤ bottomRuns s.runs →
        ((simulateQ (signingImpl K circuits settings runLimit h D A) oa).run st).run s =
          ((simulateQ (signingImpl K circuits settings runLimit (j + 1) D A) oa).run st).run s := by
      intro oa st s _
      rw [hh]
    rw [walkRest_pause K circuits settings runLimit h j D A p hm hsig hk]
    by_cases halive : AliveAtStart D p.state
    · by_cases hc : slotParity runLimit j = 0
      · exact pause_liveFirstFresh K circuits settings runLimit prims j forge D A p hp halive hc h hh
      · exact pause_liveSecondFresh K circuits settings runLimit prims j forge D A p hp halive hc
          (oneParameter_stateParameter D p.state hone) split h hh
    · exact pause_dead K circuits settings runLimit prims h j (freshPost D) D A p halive
  unfold fixedProb
  rw [usedHitProb_unit]
  unfold usedHitProb
  rw [((JEq.map prims (fun _ => true) (key (j + 1) rfl)) keyJointInitial).prEvent_eq]

/-- `BottomLawFresh` from the head split and the parameter of the seed generation in `jointKeyWorld`. -/
theorem bottomLawFresh_of_split (split : BottomHeadSplit K circuits settings prims)
    (agree : ∀ D : C.Coalition, SeedParameterAgreeJoint (E := E) prims D) :
    BottomLawFresh K circuits settings runLimit prims :=
  bottomLawFresh_of_cut K circuits settings runLimit prims
    (bottomGameCutFresh K circuits settings runLimit prims split agree)

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.bottomLawReal_of_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.bottomLawReal_of_split

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.bottomLawFresh_of_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.bottomLawFresh_of_split
