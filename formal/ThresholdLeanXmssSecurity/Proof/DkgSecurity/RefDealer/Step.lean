import ThresholdLeanXmssSecurity.Proof.DkgSecurity.RefDealer.Split

/-!
# The step of `GhostCouple`

`ghostStep` proves `GhostStep`. Each call of the signing phase with the ghost calls of the dealer and
the same call with the answers of the dealer keep `GhostRel`, with equal answers, or the left side
has the flag. A computation of the world, a corruption and the cell are one program on both sides. A
request of the first round answers with the same part. In a request of the second round and in a
request of a bottom tree, the ghost build of the bottom tree and the build of the dealer are one
computation, or the ghost build gives the cached tree again with no change of the world, and with no
flag its result is the held tree of each honest holder.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The step of `GhostCouple` -/

section Step

attribute [local irreducible] MonadAttach.support

variable (D : C.Coalition) {σ : Type}

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A run in `loggedWorld` grows the stream state. -/
theorem loggedWorld_le {α : Type} (oa : OracleComp (WorldSpec C) α) (w : LogState C) :
    ∀ z ∈ support ((simulateQ (loggedWorld prims D) oa).run w), w.1 ≤ z.2.1 := fun z hz =>
  streamWorld_le prims D oa w.1 _ (loggedWorld_support_stream prims D oa w z hz)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- An honest holder of bottom tree `b` gives a held bottom tree of an honest holder. -/
theorem heldBottom_some {operators : C.Party → OperatorState C} {b : Fin (2 ^ layerHeight)} {j : C.Party}
    (hj : j ∉ D.1) (hb : ((operators j).bottom b).isSome) :
    ∃ k bt, k ∉ D.1 ∧ (operators k).bottom b = some bt ∧ heldBottom D operators b = some bt := by
  unfold heldBottom
  rcases hk : C.parties.find? (fun i => i ∉ D.1 ∧ ((operators i).bottom b).isSome) with _ | k
  · have := List.find?_eq_none.1 hk j (List.mem_finRange j)
    simp [hj, hb] at this
  · have hk' := List.find?_some hk
    simp only [decide_eq_true_eq] at hk'
    obtain ⟨bt, hbt⟩ := Option.isSome_iff_exists.1 hk'.2
    exact ⟨k, bt, hk'.1, hbt, by simp [hbt]⟩

omit [Fintype E] [DecidableEq E] in
/-- With the invariant and no flag, the dealer build of a bottom tree that an honest operator holds
gives that held tree. -/
theorem refBottom_held {keys : C.Party → Option (Keys C)} {s : RealState C σ} {w : LogState C}
    (hinv : RefInv prims keys D s w) (hflag : s.flag = false) {top : TopTree} {i : C.Party} (hi : i ∉ D.1)
    (hti : (s.operators i).top = some top) {k : C.Party} {b : Fin (2 ^ layerHeight)} {bt : BottomTree}
    (hk : k ∉ D.1) (hbt : (s.operators k).bottom b = some bt) (hf : Query C → HashOutput) (hg : Good prims hf)
    (ha : Agrees hf w.1.1) :
    ThresholdLeanXmssSecurity.D prims hf (refBottom (gameParameter D keys) (gameSeeds D keys) top b) = some bt := by
  have hout := hinv.2.2 hflag
  have hkeys : (fun i => (s.operators i).keys) = keys := funext hinv.1
  obtain ⟨t, htk, hD⟩ := (hout.2 k hk hf hg ha).2 b bt hbt
  have h1 := (hout.2 k hk hf hg ha).1 t htk
  have h2 := (hout.2 i hi hf hg ha).1 top hti
  rw [h1] at h2
  simp only [Option.some.injEq, TreeOutput.top.injEq] at h2
  subst h2
  unfold refBottom
  rw [D_map, ← hkeys, hD]
  rfl


omit [Fintype E] [DecidableEq E] in
theorem ghostRel_mk {keys : C.Party → Option (Keys C)} {top : TopTree} {stT stF : TsigState C} {s : RealState C σ}
    {w : LogState C} (hc : stT.corrupt = stF.corrupt) (hb : stT.bound = stF.bound) (hr : stT.released = stF.released)
    (hinv : RefInv prims keys D s w) (hflag : s.flag = false) (htop : ∃ i, i ∉ D.1 ∧ (s.operators i).top = some top)
    (htrees : ∀ b r, stF.trees b = some r → ∀ z ∈ support ((simulateQ (loggedWorld prims D)
      (free (liftComp (refBottom (gameParameter D keys) (gameSeeds D keys) top b) (LocalSpec C)))).run w), z = (r, w))
    (hcorD : stT.corrupt = D.1)
    (hrel : ∀ x ∈ stT.released, x.2.2 ∉ D.1 ∧ ((s.operators x.2.2).bottom (treeOf x.1)).isSome) :
    GhostRel prims keys D top (stT, s, w) (stF, s, w) :=
  ⟨rfl, hc, hb, hr, hinv, hflag, htop, htrees, hcorD, hrel⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A run of `refBottom` that keeps the world keeps it from a larger world. -/
theorem refBottom_replay {keys : C.Party → Option (Keys C)} {top : TopTree} {b : Fin (2 ^ layerHeight)}
    {r : Option BottomTree} {w w' : LogState C}
    (h : ∀ z ∈ support ((simulateQ (loggedWorld prims D) (free (liftComp (refBottom (gameParameter D keys)
      (gameSeeds D keys) top b) (LocalSpec C)))).run w), z = (r, w)) (hle : w.1 ≤ w'.1) :
    ∀ z ∈ support ((simulateQ (loggedWorld prims D) (free (liftComp (refBottom (gameParameter D keys)
      (gameSeeds D keys) top b) (LocalSpec C)))).run w'), z = (r, w') := by
  intro z hz
  obtain ⟨z0, hz0⟩ := OracleComp.support_nonempty ((simulateQ (loggedWorld prims D) (free (liftComp
    (refBottom (gameParameter D keys) (gameSeeds D keys) top b) (LocalSpec C)))).run w)
  have e0 := h z0 hz0
  have e1 := loggedFree_replay prims D _ (onlySign_refBottom _ _ _ _) w z0 hz0 w' (by rw [e0]; exact hle) z hz
  rw [e1, e0]

omit [Fintype E] [DecidableEq E] in
/-- The relation stays when the world grows with no input of the MPC. -/
theorem ghostRel_world {keys : C.Party → Option (Keys C)} {top : TopTree} {stT stF : TsigState C}
    {s : RealState C σ} {w w' : LogState C} (h : GhostRel prims keys D top (stT, s, w) (stF, s, w))
    (hle : w.1 ≤ w'.1) (hmpc : NoMpc w'.1.1) : GhostRel prims keys D top (stT, s, w') (stF, s, w') := by
  obtain ⟨-, hc, hb, hr, hinv, hflag, htop, htrees, hcorD, hrel⟩ := h
  refine ⟨rfl, hc, hb, hr, refInv_mono prims D hinv hle.1 hmpc, hflag, htop, fun b r hr' z hz => ?_, hcorD, hrel⟩
  obtain ⟨z0, hz0⟩ := OracleComp.support_nonempty ((simulateQ (loggedWorld prims D) (free (liftComp
    (refBottom (gameParameter D keys) (gameSeeds D keys) top b) (LocalSpec C)))).run w)
  have e0 := htrees b r hr' z0 hz0
  have e1 := loggedFree_replay prims D _ (onlySign_refBottom _ _ _ _) w z0 hz0 w' (by rw [e0]; exact hle) z hz
  rw [e1, e0]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem runSig_liftWorld {α : Type} (Y : StateT (LogState C) ProbComp α) (st : TsigState C) (s : RealState C σ)
    (w : LogState C) :
    runSig (StateT.lift (StateT.lift Y) : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) (st, s, w) =
      (fun p => (p.1, (st, s, p.2))) <$> Y.run w := by
  simp [runSig, StateT.run_lift]

/-- The relation of the step, with the escape of a flag on the left. -/
abbrev StepRel (keys : C.Party → Option (Keys C)) (top : TopTree) {α : Type}
    (oT oF : α × (TsigState C × RealState C σ × LogState C)) : Prop :=
  oT.2.2.1.flag = true ∨ (oT.1 = oF.1 ∧ GhostRel prims keys D top oT.2 oF.2)

omit [Fintype E] [DecidableEq E] in
/-- A computation of the world on both sides. -/
theorem ghostStep_world (keys : C.Party → Option (Keys C)) (top : TopTree) {α : Type}
    (oa : OracleComp (WorldSpec C) α) :
    LeArrow (GhostRel prims keys D top (σ := σ))
      (runSig (StateT.lift (inWorld (loggedWorld prims D) oa) :
        StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α))
      (runSig (StateT.lift (inWorld (loggedWorld prims D) oa) :
        StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α))
      (StepRel prims D keys top) := by
  rintro ⟨stT, s, w⟩ ⟨stF, s', w'⟩ h
  have e := h.1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  refine leArrow_common (fun _ _ _ => ⟨_, (simulateQ (loggedWorld prims D) oa).run w, fun p => (p.1, (stT, s, p.2)),
    fun p => (p.1, (stF, s, p.2)), runSig_liftWorld _ _ _ _, runSig_liftWorld _ _ _ _, fun p hp => Or.inr ⟨rfl,
      ghostRel_world prims D h (loggedWorld_le prims D oa w p hp) (loggedWorld_noMpc prims D oa w h.2.2.2.2.1.2.1 p hp)⟩⟩)
    _ _ h

omit [Fintype E] [DecidableEq E] in
/-- A pure answer on both sides. -/
theorem ghostStep_pure (keys : C.Party → Option (Keys C)) (top : TopTree) {α : Type} (a : α) :
    LeArrow (GhostRel prims keys D top (σ := σ))
      (runSig (pure a : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α))
      (runSig (pure a : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α))
      (StepRel prims D keys top) :=
  leArrow_common fun uT uF h => ⟨Unit, pure (), fun _ => (a, uT), fun _ => (a, uF), by simp [runSig_pure],
    by simp [runSig_pure], fun _ _ => Or.inr ⟨rfl, h⟩⟩

omit [Fintype E] [DecidableEq E] in
/-- The cell of the state of the adversary on both sides. -/
theorem ghostStep_cell (keys : C.Party → Option (Keys C)) (top : TopTree) (q : StateQuery σ) :
    LeArrow (GhostRel prims keys D top (σ := σ)) (runSig (sigCell (C := C) (M := ProbComp) (W := LogState C) σ q))
      (runSig (sigCell (C := C) (M := ProbComp) (W := LogState C) σ q)) (StepRel prims D keys top) := by
  rintro ⟨stT, s, w⟩ ⟨stF, s', w'⟩ h
  have e := h.1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  intro γ δ kT kF ET EF hk
  rcases q with _ | state
  · simp only [runSig, sigCell]
    exact hk _ _ (Or.inr ⟨rfl, h⟩)
  · simp only [runSig, sigCell]
    obtain ⟨-, hc, hb, hr, hinv, hflag, htop, htrees, hcorD, hrel⟩ := h
    exact hk _ _ (Or.inr ⟨rfl, rfl, hc, hb, hr, hinv, hflag, htop, htrees, hcorD, hrel⟩)

omit [Fintype E] [DecidableEq E] in
/-- The closure of a tree keeps the relation. -/
theorem ghostRel_closed {keys : C.Party → Option (Keys C)} {top : TopTree} {stT stF : TsigState C}
    {s : RealState C σ} {w : LogState C} (h : GhostRel prims keys D top (stT, s, w) (stF, s, w))
    (closed : Fin (2 ^ layerHeight) → Bool) :
    GhostRel prims keys D top (stT, { s with closed := closed }, w) (stF, { s with closed := closed }, w) := by
  obtain ⟨-, hc, hb, hr, hinv, hflag, htop, htrees, hcorD, hrel⟩ := h
  exact ⟨rfl, hc, hb, hr, hinv, hflag, htop, htrees, hcorD, hrel⟩

/-- `probEvent_bind_le_of_support` for an event that `simp` moved into the continuations. -/
theorem prEvent_bind_le_of_support' {α : Type} (oa : ProbComp α) (f g : α → ProbComp Prop)
    (h : ∀ a ∈ support oa, prEvent (f a) ≤ prEvent (g a)) : prEvent (oa >>= f) ≤ prEvent (oa >>= g) := by
  have := probEvent_bind_le_of_support oa f g (fun z => z) (fun z => z) (by simpa using h)
  simpa using this

/-- A bind whose first program has one outcome. -/
theorem prEvent_bind_le_of_eq {α : Type} (oa : ProbComp α) (f : α → ProbComp Prop) (a : α)
    (h : ∀ z ∈ support oa, z = a) (Y : ℝ≥0∞) (hY : prEvent (f a) ≤ Y) : prEvent (oa >>= f) ≤ Y := by
  have := prEvent_bind_le_of_forall_le_of_support oa f (fun z => z) (ε := Y) fun z hz => by
    rw [h z hz]; simpa using hY
  simpa using this

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem tsigSpec_round1 (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) :
    (TsigSpec C).Range (.round1 i J e message) = Option Digest := rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem tsigSpec_tree (b : Fin (2 ^ layerHeight)) :
    (TsigSpec C).Range (.tree b) = Option (BottomTree × Digest) := rfl

omit [Fintype E] [DecidableEq E] in
/-- A signing request of the first round on both sides. -/
theorem ghostStep_round1 (keys : C.Party → Option (Keys C)) (top : TopTree) (net : Adversary C E Unit PEmpty PEmpty)
    (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) :
    LeArrow (GhostRel prims keys D top (σ := net.State))
      (runSig (ghostOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst D net (gameParameter D keys)
        (gameSeeds D keys) (fun i => (keys i).getD noKeys) top (.round1 i J e message)))
      (runSig (sharedDealerOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D net
        (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys) (fun _ => none)
        (coupleDealer prims keys D net.State top) (.round1 i J e message)))
      (StepRel prims D keys top) := by
  rintro ⟨stT, s, w⟩ ⟨stF, s', w'⟩ h
  have e := h.1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  intro γ δ kT kF ET EF hk
  simp only [runSig, ghostOracles, sharedOwnOracles, sharedDealerOracles, StateT.run_bind, StateT.run_lift,
    StateT.run_modify, StateT.run_get, pure_bind, bind_assoc]
  have h1 := ghostRel_closed prims D h (Function.update s.closed (treeOf e) true)
  unfold operatorAnswer
  rcases hk1 : (s.operators i).keys with _ | k
  · simp only [StateT.run_pure, map_pure, pure_bind]
    exact hk _ _ (Or.inr ⟨rfl, h1⟩)
  rcases ht1 : (s.operators i).top with _ | tp
  · simp only [StateT.run_pure, map_pure, pure_bind]
    exact hk _ _ (Or.inr ⟨rfl, h1⟩)
  rcases hb1 : (s.operators i).bottom (treeOf e) with _ | bt
  · simp only [StateT.run_pure, map_pure, pure_bind]
    exact hk _ _ (Or.inr ⟨rfl, h1⟩)
  simp only [ownAnswer, tsigOracles, StateT.run_bind, StateT.run_modify, StateT.run_get, pure_bind]
  obtain ⟨-, hc', hb', hr', hinv, hflag, htop, htrees, hcorD, hrel⟩ := h1
  have hc : stT.corrupt = stF.corrupt := hc'
  have hb : stT.bound = stF.bound := hb'
  have hr : stT.released = stF.released := hr'
  have hkey : (keys i).getD noKeys = k := by rw [← h.2.2.2.2.1.1 i, hk1]; rfl
  simp only [breaksOneMessagePerKey, ← hc, ← hb, ← hr]
  split_ifs with hcond
  · exact hk _ _ (Or.inr ⟨rfl, rfl, hc', hb', hr', hinv, hflag, htop, htrees, hcorD, hrel⟩)
  simp only [coupleDealer, dealtWith, hkey, liftM, sharedLift, inWorld, StateT.run_bind, StateT.run_set,
    pure_bind, map_bind, bind_map_left]
  dsimp only [tsigSpec_round1] at kT kF hk ⊢
  simp only [StateT.run_map, StateT.run_monadLift, map_bind, pure_bind, monadLift_self, StateT.run_bind,
    StateT.run_lift, map_pure, bind_assoc, StateT.run_pure]
  refine prEvent_bind_le_of_support' _ _ _ fun p hp => ?_
  exact hk _ _ (Or.inr ⟨rfl, ghostRel_world prims D ⟨rfl, rfl, rfl, rfl, hinv, hflag, htop, htrees, hcorD, hrel⟩
    (loggedWorld_le prims D _ w p hp) (loggedWorld_noMpc prims D _ w hinv.2.1 p hp)⟩)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The bottom tree of the dealer on the free copy is the local computation `refBottom`. -/
theorem dealtWith_bottom_shared (parameter : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight)) :
    (dealtWith (sharedLift (σ := σ) (loggedWorld prims D)) parameter keys top
      (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x))).bottom b =
      sharedLift (loggedWorld prims D) (refBottom parameter seeds top b) := by
  have h := SeedHitProof.hom_referenceTree (roHom prims D σ) tweakable (prfValue seeds) parameter top (.bottom b)
  have hm := SeedHitProof.hom_map (roHom prims D σ) bottomOf
    (referenceTree tweakable (prfValue seeds) parameter top (.bottom b))
  change _ = roHom prims D σ (bottomOf <$> referenceTree tweakable (prfValue seeds) parameter top (.bottom b))
  rw [hm, h]
  unfold dealtWith
  dsimp only
  exact congrArg (fun f => f <$> (referenceTree (fun oa => sharedLift (σ := σ) (loggedWorld prims D) (tweakable oa))
    (fun x => sharedLift (σ := σ) (loggedWorld prims D) (prfValue seeds x)) parameter top (.bottom b) :
      SharedM C ProbComp (LogState C) σ (Option TreeOutput)))
    (funext fun x => by rcases x with _ | (_ | _) <;> rfl)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem sharedLift_map {α β : Type} (f : α → β) (X : OracleComp (RoSpec C) α) :
    sharedLift (σ := σ) (loggedWorld prims D) (f <$> X) = f <$> sharedLift (loggedWorld prims D) X :=
  SeedHitProof.hom_map (roHom prims D σ) f X

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A local computation of the honest operators keeps the state of the game. -/
theorem sharedLift_run {α : Type} (X : OracleComp (RoSpec C) α) (s : RealState C σ) (w : LogState C) :
    ((sharedLift (loggedWorld prims D) X : SharedM C ProbComp (LogState C) σ α).run s).run w =
      (fun p => ((p.1, s), p.2)) <$> (simulateQ (loggedWorld prims D) (free (liftComp X (LocalSpec C)))).run w := by
  simp [sharedLift, inWorld, StateT.run_lift]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The second round of signing on the free copy is one local computation. -/
theorem signRound2With_shared (part : Point → OracleComp (RoSpec C) Digest) (parameter : PublicParameter)
    (J : C.Quorum) (commitment : Digest) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    signRound2With (sharedLift (σ := σ) (loggedWorld prims D)) (fun x => sharedLift (loggedWorld prims D) (part x))
        parameter J commitment e message parts =
      sharedLift (loggedWorld prims D) (signRound2With (fun oa => oa) part parameter J commitment e message parts) :=
  (SeedHitProof.hom_signRound2With (roHom prims D σ) (fun oa => oa) part parameter J commitment e message parts).symm

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The outcome of a free computation is its value on each good `H` that agrees with the end cache. -/
theorem loggedFree_value {γ : Type} (oa : OracleComp (RoSpec C) γ) (h : GameCount.OnlySign oa) (w : LogState C)
    (z : γ × LogState C) (hz : z ∈ support ((simulateQ (loggedWorld prims D) (free (liftComp oa (LocalSpec C)))).run w))
    (hf : Query C → HashOutput) (hg : Good prims hf) (ha : Agrees hf z.2.1.1) :
    ThresholdLeanXmssSecurity.D prims hf oa = z.1 := by
  obtain ⟨y, hy, rfl⟩ := loggedFree_support prims D oa h w z hz
  exact ((roRun_support prims oa w.1.1 y hy).2.2 hf hg ha).symm

omit [Fintype E] [DecidableEq E] in
/-- A signing request of the second round on both sides. -/
theorem ghostStep_round2 (keys : C.Party → Option (Keys C)) (top : TopTree) (net : Adversary C E Unit PEmpty PEmpty)
    (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    LeArrow (GhostRel prims keys D top (σ := net.State))
      (runSig (ghostOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst D net (gameParameter D keys)
        (gameSeeds D keys) (fun i => (keys i).getD noKeys) top (.round2 i J e message parts)))
      (runSig (sharedDealerOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D net
        (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys) (fun _ => none)
        (coupleDealer prims keys D net.State top) (.round2 i J e message parts)))
      (StepRel prims D keys top) := by
  rintro ⟨stT, s, w⟩ ⟨stF, s', w'⟩ h
  have e := h.1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  intro γ δ kT kF ET EF hk
  have h1 := ghostRel_closed prims D h (Function.update s.closed (treeOf e) true)
  have hc : stT.corrupt = stF.corrupt := h.2.1
  have hb : stT.bound = stF.bound := h.2.2.1
  have hr : stT.released = stF.released := h.2.2.2.1
  simp only [runSig, ghostOracles, sharedOwnOracles, sharedDealerOracles, StateT.run_bind, StateT.run_lift,
    StateT.run_modify, StateT.run_get, StateT.run_pure, pure_bind]
  unfold operatorAnswer
  rcases hk1 : (s.operators i).keys with _ | k
  · simp only [hk1, Option.isSome_none, Bool.false_eq_true, false_and, ↓reduceIte, StateT.run_bind, StateT.run_lift,
      StateT.run_modify, StateT.run_get, StateT.run_pure, pure_bind]
    exact hk _ _ (Or.inr ⟨rfl, h1⟩)
  rcases ht1 : (s.operators i).top with _ | tp
  · simp only [hk1, ht1, Option.isSome_none, Bool.false_eq_true, false_and, and_false, ↓reduceIte, StateT.run_bind,
      StateT.run_lift, StateT.run_modify, StateT.run_get, StateT.run_pure, pure_bind]
    exact hk _ _ (Or.inr ⟨rfl, h1⟩)
  rcases hb1 : (s.operators i).bottom (treeOf e) with _ | bt
  · simp only [hk1, ht1, hb1, Option.isSome_none, Bool.false_eq_true, false_and, and_false, ↓reduceIte, StateT.run_bind,
      StateT.run_lift, StateT.run_modify, StateT.run_get, StateT.run_pure, pure_bind]
    exact hk _ _ (Or.inr ⟨rfl, h1⟩)
  simp only [Option.isSome_some, true_and]
  clear h
  obtain ⟨-, hc', hb', hr', hinv, hflag, htop, htrees, hcorD, hrel⟩ := h1
  by_cases hcond : i ∈ stT.corrupt ∨ i ∉ J.1 ∨ stT.bound e ≠ some message
  · simp only [hcond, not_true_eq_false, ↓reduceIte, ownAnswer, tsigOracles, ← hc, ← hb, StateT.run_bind,
      StateT.run_lift, StateT.run_modify, StateT.run_get, StateT.run_pure, pure_bind, hk1, ht1, hb1]
    exact hk _ _ (Or.inr ⟨rfl, rfl, hc', hb', hr', hinv, hflag, htop, htrees, hcorD, hrel⟩)
  simp only [hcond, not_false_eq_true, ↓reduceIte, ownAnswer, tsigOracles, ← hc, ← hb, StateT.run_bind,
    StateT.run_lift, StateT.run_modify, StateT.run_get, StateT.run_pure, pure_bind, bottomOnce,
    sharedLift_map]
  have hkey : (keys i).getD noKeys = k := by rw [← hinv.1 i, hk1]; rfl
  rcases htr : stF.trees (treeOf e) with _ | r0
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, coupleDealer, dealtWith_bottom_shared,
      StateT.run_map, sharedLift_run, liftM, StateT.run_monadLift, monadLift_self, map_bind, bind_map_left,
      bind_assoc, StateT.run_modify, StateT.run_pure, hk1, ht1, hb1, hcond, ite_false]
    have hpar : k.parameter = gameParameter D keys :=
      parameter_eq_gameParameter D keys (by have := (hinv.2.2 hflag).1; rwa [show (fun j => (s.operators j).keys) = keys
        from funext hinv.1] at this) i (hcorD ▸ fun h => hcond (Or.inl h)) k (by rw [← hinv.1 i]; exact hk1)
    refine prEvent_bind_le_of_support' _ _ _ fun a ha => ?_
    obtain ⟨r, w1⟩ := a
    have hr1 : r = some bt := by
      obtain ⟨i', hi', hti'⟩ := htop
      exact loggedFree_determined prims D _ (onlySign_refBottom _ _ _ _) w hinv.2.1 _
        (fun hf hg ha => refBottom_held prims D hinv hflag hi' hti' (hcorD ▸ fun h => hcond (Or.inl h)) hb1 hf hg ha)
        _ ha
    subst hr1
    simp only [dealtWith, hkey, ← hpar, signRound2With_shared, sharedLift_run, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, bind_map_left, bind_assoc, pure_bind]
    refine prEvent_bind_le_of_support' _ _ _ fun a2 ha2 => ?_
    refine prEvent_bind_le_of_support' _ _ _ fun a3 ha3 => ?_
    have hle1 := loggedWorld_le prims D _ w _ ha
    have hle2 := loggedWorld_le prims D _ w1 _ ha2
    have hle3 := loggedWorld_le prims D _ a2.2 _ ha3
    have hmpc := loggedWorld_noMpc prims D _ a2.2 (loggedWorld_noMpc prims D _ w1
      (loggedWorld_noMpc prims D _ w hinv.2.1 _ ha) _ ha2) _ ha3
    have hle : w.1 ≤ a3.2.1 := le_trans hle1 (le_trans hle2 hle3)
    have hiD : i ∉ D.1 := hcorD ▸ fun h => hcond (Or.inl h)
    have htrees' : ∀ b r, (Function.update stF.trees (treeOf e) (some (some bt))) b = some r →
        ∀ z ∈ support ((simulateQ (loggedWorld prims D) (free (liftComp (refBottom (gameParameter D keys)
          (gameSeeds D keys) top b) (LocalSpec C)))).run a3.2), z = (r, a3.2) := by
      intro b r hb' z hz
      by_cases hbe : b = treeOf e
      · subst hbe
        rw [Function.update_self, Option.some.injEq] at hb'
        subst hb'
        exact loggedFree_replay prims D _ (onlySign_refBottom _ _ _ _) w _ ha a3.2 (le_trans hle2 hle3) z hz
      · rw [Function.update_of_ne hbe] at hb'
        exact refBottom_replay prims D (htrees b r hb') hle z hz
    obtain ⟨v, w3⟩ := a3
    rcases v with _ | values
    · dsimp only
      exact hk _ _ (Or.inr ⟨rfl, ghostRel_mk prims D hc hb hr (refInv_mono prims D hinv hle.1 hmpc) hflag htop
        htrees' hcorD hrel⟩)
    · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
      refine hk _ _ (Or.inr ⟨rfl, ghostRel_mk prims D hc hb (by rw [hr]) (refInv_mono prims D hinv hle.1 hmpc) hflag
        htop htrees' hcorD fun x hx => ?_⟩)
      rcases List.mem_append.1 hx with hx | hx
      · exact hrel x hx
      · simp only [List.mem_singleton] at hx
        subst hx
        exact ⟨hiD, by simp [hb1]⟩
  have hiD : i ∉ D.1 := hcorD ▸ fun h => hcond (Or.inl h)
  have hpar : k.parameter = gameParameter D keys :=
    parameter_eq_gameParameter D keys (by have := (hinv.2.2 hflag).1; rwa [show (fun j => (s.operators j).keys) = keys
      from funext hinv.1] at this) i hiD k (by rw [← hinv.1 i]; exact hk1)
  have hr0 : r0 = some bt := by
    obtain ⟨z0, hz0⟩ := OracleComp.support_nonempty ((simulateQ (loggedWorld prims D) (free (liftComp
      (refBottom (gameParameter D keys) (gameSeeds D keys) top (treeOf e)) (LocalSpec C)))).run w)
    obtain ⟨i', hi', hti'⟩ := htop
    have := loggedFree_determined prims D _ (onlySign_refBottom _ _ _ _) w hinv.2.1 _
      (fun hf hg ha => refBottom_held prims D hinv hflag hi' hti' hiD hb1 hf hg ha) z0 hz0
    rw [htrees _ _ htr z0 hz0] at this
    exact this
  subst hr0
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_map, sharedLift_run, liftM,
    StateT.run_monadLift, monadLift_self, map_bind, bind_map_left, bind_assoc, StateT.run_modify, StateT.run_pure,
    hk1, ht1, hb1, hcond, ite_false]
  refine prEvent_bind_le_of_eq _ _ _ (htrees _ _ htr) _ ?_
  simp only [dealtWith, hkey, ← hpar, signRound2With_shared, sharedLift_run, 
    bind_map_left]
  refine prEvent_bind_le_of_support' _ _ _ fun a2 ha2 => ?_
  refine prEvent_bind_le_of_support' _ _ _ fun a3 ha3 => ?_
  have hle2 := loggedWorld_le prims D _ w _ ha2
  have hle3 := loggedWorld_le prims D _ a2.2 _ ha3
  have hmpc := loggedWorld_noMpc prims D _ a2.2 (loggedWorld_noMpc prims D _ w hinv.2.1 _ ha2) _ ha3
  have hle : w.1 ≤ a3.2.1 := le_trans hle2 hle3
  have htrees' := fun b r hb' => refBottom_replay prims D (htrees b r hb') hle
  obtain ⟨v, w3⟩ := a3
  rcases v with _ | values
  · dsimp only
    exact hk _ _ (Or.inr ⟨rfl, ghostRel_mk prims D hc hb hr (refInv_mono prims D hinv hle.1 hmpc) hflag htop
      htrees' hcorD hrel⟩)
  · simp only [StateT.run_bind, StateT.run_modify, pure_bind]
    refine hk _ _ (Or.inr ⟨rfl, ghostRel_mk prims D hc hb (by rw [hr]) (refInv_mono prims D hinv hle.1 hmpc) hflag
      htop htrees' hcorD fun x hx => ?_⟩)
    rcases List.mem_append.1 hx with hx | hx
    · exact hrel x hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hiD, by simp [hb1]⟩

omit [Fintype E] [DecidableEq E] in
/-- Real runs of a bottom tree grow the world, keep the top trees and keep each held bottom tree. -/
theorem sharedRuns_bottom (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (b : Fin (2 ^ layerHeight)) :
    ∀ (count : ℕ) (s : RealState C net.State) (w : LogState C),
      ∀ z ∈ support (((sharedRuns K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D net
          parameter seeds dealt emu (.bottom b) count).run s).run w),
        w.1 ≤ z.2.1 ∧ ∀ i, (z.1.2.operators i).top = (s.operators i).top ∧
          ∀ b' bt, (s.operators i).bottom b' = some bt → (z.1.2.operators i).bottom b' = some bt
  | 0, s, w, z, hz => by
    simp only [sharedRuns, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, fun i => ⟨rfl, fun _ _ h => h⟩⟩
  | count + 1, s, w, z, hz => by
    simp only [sharedRuns, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split_ifs at hz with hmay
    · rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      rw [sharedRun_real, StateT.run_bind, StateT.run_get, pure_bind] at hy
      obtain ⟨r, hr, v, hv, hy2, hy1⟩ := sharedRunWith_support prims K circuits settings D net _ (.bottom b) s w y hy
      obtain ⟨hle, hops⟩ := sharedRuns_bottom net parameter seeds dealt emu b count y.1.2 y.2 z hz
      refine ⟨le_trans (le_trans (loggedWorld_le prims D _ w r hr) (hy2 ▸ loggedWorld_le prims D _ r.2 v hv)) hle,
        fun i => ⟨?_, fun b' bt hb' => ?_⟩⟩
      · rw [(hops i).1, hy1]
        rfl
      · refine (hops i).2 b' bt ?_
        rw [hy1]
        simp only [OperatorState.keep]
        by_cases hbb : b' = b
        · subst hbb
          rw [Function.update_self, hb']
          rfl
        · rw [Function.update_of_ne hbb, hb']
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨le_rfl, fun i => ⟨rfl, fun _ _ h => h⟩⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem sharedLift_bind {α β : Type} (X : OracleComp (RoSpec C) α) (f : α → OracleComp (RoSpec C) β) :
    sharedLift (σ := σ) (loggedWorld prims D) (X >>= f) =
      sharedLift (loggedWorld prims D) X >>= fun a => sharedLift (loggedWorld prims D) (f a) :=
  (roHom prims D σ).toFun_bind' X f

/-- A bind whose first program gives outcomes with a bound on their continuations. -/
theorem prEvent_bind_le_of_forall {α : Type} (oa : ProbComp α) (f : α → ProbComp Prop) (Y : ℝ≥0∞)
    (h : ∀ z ∈ support oa, prEvent (f z) ≤ Y) : prEvent (oa >>= f) ≤ Y := by
  have := prEvent_bind_le_of_forall_le_of_support oa f (fun z => z) (ε := Y) fun z hz => by simpa using h z hz
  simpa using this

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A held bottom tree is the bottom tree of an honest holder. -/
theorem heldBottom_eq_some {operators : C.Party → OperatorState C} {b : Fin (2 ^ layerHeight)} {t : BottomTree}
    (h : heldBottom D operators b = some t) : ∃ k, k ∉ D.1 ∧ (operators k).bottom b = some t := by
  unfold heldBottom at h
  rcases hk : C.parties.find? (fun i => i ∉ D.1 ∧ ((operators i).bottom b).isSome) with _ | k
  · rw [hk] at h
    cases h
  · have hk' := List.find?_some hk
    simp only [decide_eq_true_eq] at hk'
    rw [hk, Option.bind_some] at h
    exact ⟨k, hk'.1, h⟩

omit [Fintype E] [DecidableEq E] in
/-- A request of a bottom tree on both sides. -/
theorem ghostStep_tree (keeps : RefRunKeeps prims K circuits settings) (batch : 0 < settings.batchSize)
    (compute : CircuitsCompute circuits prims.Th) (keys : C.Party → Option (Keys C)) (top : TopTree)
    (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight)) :
    LeArrow (GhostRel prims keys D top (σ := net.State))
      (runSig (ghostOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst D net (gameParameter D keys)
        (gameSeeds D keys) (fun i => (keys i).getD noKeys) top (.tree b)))
      (runSig (sharedDealerOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D net
        (gameParameter D keys) (gameSeeds D keys) (fun i => (keys i).getD noKeys) (fun _ => none)
        (coupleDealer prims keys D net.State top) (.tree b)))
      (StepRel prims D keys top) := by
  rintro ⟨stT, s, w⟩ ⟨stF, s', w'⟩ h
  have e := h.1
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  intro γ δ kT kF ET EF hk
  have hc : stT.corrupt = stF.corrupt := h.2.1
  have hb : stT.bound = stF.bound := h.2.2.1
  have hr : stT.released = stF.released := h.2.2.2.1
  obtain ⟨-, -, -, -, hinv, hflag, htop, htrees, hcorD, hrel⟩ := h
  simp only [runSig, ghostOracles, sharedOwnOracles, sharedDealerOracles, tsigOracles, bottomOnce, ghostTreeRo,
    sharedLift_bind, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_pure, pure_bind, sharedLift_run,
    map_bind, bind_map_left, bind_assoc, liftM, coupleDealer,
    dealtWith_bottom_shared]
  dsimp only [tsigSpec_tree] at kT kF hk ⊢
  rcases htr : stF.trees b with _ | r0
  · simp only [htr, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, sharedLift_run, 
      bind_map_left, bind_assoc, StateT.run_monadLift, monadLift_self, StateT.run_modify]
    refine prEvent_bind_le_of_support' _ _ _ fun a ha => ?_
    obtain ⟨r, w1⟩ := a
    have hle1 := loggedWorld_le prims D _ w _ ha
    have hmpc1 := loggedWorld_noMpc prims D _ w hinv.2.1 _ ha
    rcases r with _ | bt0
    · simp only [liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure, pure_bind, Mode.real, true_or,
        ite_true, StateT.run_bind, StateT.run_lift, StateT.run_get, bind_assoc]
      refine prEvent_bind_le_of_support' _ _ _ fun z hz => ?_
      have hinvz := sharedRuns_keeps prims K circuits settings runLimit keeps batch compute keys D net _ _ _ _
        (.bottom b) 1 s w1 (refInv_mono prims D hinv hle1.1 hmpc1) z hz
      obtain ⟨hlez, hopz⟩ := sharedRuns_bottom prims K circuits settings runLimit D net _ _ _ _ b 1 s w1 z hz
      have htopz : ∃ i, i ∉ D.1 ∧ (z.1.2.operators i).top = some top := by
        obtain ⟨i', hi', hti'⟩ := htop
        exact ⟨i', hi', (hopz i').1.trans hti'⟩
      cases hflz : z.1.2.flag
      · have hheld : heldBottom D z.1.2.operators b = none := by
          rcases hh : heldBottom D z.1.2.operators b with _ | t
          · rfl
          exfalso
          obtain ⟨k, hkD, hkb⟩ := heldBottom_eq_some D hh
          obtain ⟨i', hi', hti'⟩ := htopz
          obtain ⟨hf, hg, haf⟩ := exists_good_agrees prims hinvz.2.1
          have h1 := refBottom_held prims D hinvz hflz hi' hti' hkD hkb hf hg haf
          have h2 := loggedFree_value prims D _ (onlySign_refBottom _ _ _ _) w _ ha hf hg (Agrees.mono hlez.1 haf)
          rw [h1] at h2
          cases h2
        simp only [hheld, StateT.run_pure]
        refine hk _ _ (Or.inr ⟨rfl, ghostRel_mk prims D hc hb hr hinvz hflz htopz (fun b' r hb' z' hz' => ?_) hcorD
          fun x hx => ⟨(hrel x hx).1, ?_⟩⟩)
        · dsimp only at hb' hz' ⊢
          by_cases hbe : b' = b
          · subst hbe
            rw [Function.update_self, Option.some.injEq] at hb'
            subst hb'
            exact loggedFree_replay prims D _ (onlySign_refBottom _ _ _ _) w _ ha z.2 hlez z' hz'
          · rw [Function.update_of_ne hbe] at hb'
            exact refBottom_replay prims D (htrees b' r hb') (le_trans hle1 hlez) z' hz'
        · obtain ⟨bt, hbt⟩ := Option.isSome_iff_exists.1 (hrel x hx).2
          rw [(hopz _).2 _ _ hbt]
          rfl
      · rcases hh : heldBottom D z.1.2.operators b with _ | t
        · simp only [StateT.run_pure]
          exact hk _ _ (Or.inl hflz)
        · simp only [StateT.run_bind, sharedLift_run, bind_map_left, StateT.run_pure, bind_assoc, pure_bind]
          exact prEvent_bind_le_of_forall _ _ _ fun p _ => hk _ _ (Or.inl hflz)
    · simp only [dealtWith, free_bind, liftComp_bind, simulateQ_bind, StateT.run_bind, free_pure, liftComp_pure,
        simulateQ_pure, StateT.run_pure, pure_bind, bind_assoc, sharedLift_run, StateT.run_monadLift, monadLift_self,
        bind_map_left, Mode.real, true_or, ite_true, StateT.run_lift, StateT.run_get]
      refine prEvent_bind_le_of_support' _ _ _ fun p hp => ?_
      have hle2 := loggedWorld_le prims D _ w1 _ hp
      have hmpc2 := loggedWorld_noMpc prims D _ w1 hmpc1 _ hp
      refine prEvent_bind_le_of_support' _ _ _ fun z hz => ?_
      have hinvz := sharedRuns_keeps prims K circuits settings runLimit keeps batch compute keys D net _ _ _ _
        (.bottom b) 1 s p.2 (refInv_mono prims D hinv (le_trans hle1 hle2).1 hmpc2) z hz
      obtain ⟨hlez, hopz⟩ := sharedRuns_bottom prims K circuits settings runLimit D net _ _ _ _ b 1 s p.2 z hz
      have htopz : ∃ i, i ∉ D.1 ∧ (z.1.2.operators i).top = some top := by
        obtain ⟨i', hi', hti'⟩ := htop
        exact ⟨i', hi', (hopz i').1.trans hti'⟩
      have htreesz : ∀ b' r, (Function.update stF.trees b (some (some bt0))) b' = some r →
          ∀ z' ∈ support ((simulateQ (loggedWorld prims D) (free (liftComp (refBottom (gameParameter D keys)
            (gameSeeds D keys) top b') (LocalSpec C)))).run z.2), z' = (r, z.2) := by
        intro b' r hb' z' hz'
        by_cases hbe : b' = b
        · subst hbe
          rw [Function.update_self, Option.some.injEq] at hb'
          subst hb'
          exact loggedFree_replay prims D _ (onlySign_refBottom _ _ _ _) w _ ha z.2 (le_trans hle2 hlez) z' hz'
        · rw [Function.update_of_ne hbe] at hb'
          exact refBottom_replay prims D (htrees b' r hb') (le_trans hle1 (le_trans hle2 hlez)) z' hz'
      have hrelz : ∀ x ∈ stT.released, x.2.2 ∉ D.1 ∧ ((z.1.2.operators x.2.2).bottom (treeOf x.1)).isSome := by
        intro x hx
        obtain ⟨bt, hbt⟩ := Option.isSome_iff_exists.1 (hrel x hx).2
        exact ⟨(hrel x hx).1, by rw [(hopz _).2 _ _ hbt]; rfl⟩
      cases hflz : z.1.2.flag
      · rcases hh : heldBottom D z.1.2.operators b with _ | t
        · simp only [StateT.run_pure]
          exact hk _ _ (Or.inr ⟨rfl, ghostRel_mk prims D hc hb hr hinvz hflz htopz htreesz hcorD hrelz⟩)
        · have hkz : (fun i => (z.1.2.operators i).keys) = keys := funext hinvz.1
          simp only [StateT.run_bind, sharedLift_run, bind_map_left, StateT.run_pure, bind_assoc, pure_bind,
            hkz]
          refine prEvent_bind_le_of_eq _ _ _ (loggedFree_replay prims D _ (GameCount.onlySign_prfValue _ _) w1 p hp
            z.2 hlez) _ ?_
          exact hk _ _ (Or.inr ⟨rfl, ghostRel_mk prims D hc hb hr hinvz hflz htopz htreesz hcorD hrelz⟩)
      · rcases hh : heldBottom D z.1.2.operators b with _ | t
        · simp only [StateT.run_pure]
          exact hk _ _ (Or.inl hflz)
        · simp only [StateT.run_bind, sharedLift_run, bind_map_left, StateT.run_pure, bind_assoc, pure_bind]
          exact prEvent_bind_le_of_forall _ _ _ fun p _ => hk _ _ (Or.inl hflz)
  simp only [htr, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, 
    bind_assoc]
  refine prEvent_bind_le_of_eq _ _ _ (htrees _ _ htr) _ ?_
  obtain ⟨z0, hz0⟩ := OracleComp.support_nonempty ((simulateQ (loggedWorld prims D) (free (liftComp
    (refBottom (gameParameter D keys) (gameSeeds D keys) top b) (LocalSpec C)))).run w)
  have ha0 := hz0
  rw [htrees _ _ htr z0 hz0] at ha0
  rcases r0 with _ | bt0
  · simp only [liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure, pure_bind, Mode.real, true_or,
      ite_true, StateT.run_bind, StateT.run_lift, StateT.run_get, bind_assoc]
    refine prEvent_bind_le_of_support' _ _ _ fun z hz => ?_
    have hinvz := sharedRuns_keeps prims K circuits settings runLimit keeps batch compute keys D net _ _ _ _
      (.bottom b) 1 s w hinv z hz
    obtain ⟨hlez, hopz⟩ := sharedRuns_bottom prims K circuits settings runLimit D net _ _ _ _ b 1 s w z hz
    have htopz : ∃ i, i ∉ D.1 ∧ (z.1.2.operators i).top = some top := by
      obtain ⟨i', hi', hti'⟩ := htop
      exact ⟨i', hi', (hopz i').1.trans hti'⟩
    cases hflz : z.1.2.flag
    · have hheld : heldBottom D z.1.2.operators b = none := by
        rcases hh : heldBottom D z.1.2.operators b with _ | t
        · rfl
        exfalso
        obtain ⟨k, hkD, hkb⟩ := heldBottom_eq_some D hh
        obtain ⟨i', hi', hti'⟩ := htopz
        obtain ⟨hf, hg, haf⟩ := exists_good_agrees prims hinvz.2.1
        have h1 := refBottom_held prims D hinvz hflz hi' hti' hkD hkb hf hg haf
        have h2 := loggedFree_value prims D _ (onlySign_refBottom _ _ _ _) w _ ha0 hf hg (Agrees.mono hlez.1 haf)
        rw [h1] at h2
        cases h2
      simp only [hheld, StateT.run_pure]
      refine hk _ _ (Or.inr ⟨rfl, ghostRel_mk prims D hc hb hr hinvz hflz htopz (fun b' r hb' z' hz' => ?_) hcorD
        fun x hx => ⟨(hrel x hx).1, ?_⟩⟩)
      · dsimp only at hb' hz' ⊢
        exact refBottom_replay prims D (htrees b' r hb') hlez z' hz'
      · obtain ⟨bt, hbt⟩ := Option.isSome_iff_exists.1 (hrel x hx).2
        rw [(hopz _).2 _ _ hbt]
        rfl
    · rcases hh : heldBottom D z.1.2.operators b with _ | t
      · simp only [StateT.run_pure]
        exact hk _ _ (Or.inl hflz)
      · simp only [StateT.run_bind, sharedLift_run, bind_map_left, StateT.run_pure, bind_assoc, pure_bind]
        exact prEvent_bind_le_of_forall _ _ _ fun p _ => hk _ _ (Or.inl hflz)
  · simp only [dealtWith, free_bind, liftComp_bind, simulateQ_bind, StateT.run_bind, free_pure, liftComp_pure,
      simulateQ_pure, StateT.run_pure, pure_bind, bind_assoc, sharedLift_run, StateT.run_monadLift, monadLift_self,
      bind_map_left, Mode.real, true_or, ite_true, StateT.run_lift, StateT.run_get]
    refine prEvent_bind_le_of_support' _ _ _ fun p hp => ?_
    have hle2 := loggedWorld_le prims D _ w _ hp
    have hmpc2 := loggedWorld_noMpc prims D _ w hinv.2.1 _ hp
    refine prEvent_bind_le_of_support' _ _ _ fun z hz => ?_
    have hinvz := sharedRuns_keeps prims K circuits settings runLimit keeps batch compute keys D net _ _ _ _
      (.bottom b) 1 s p.2 (refInv_mono prims D hinv hle2.1 hmpc2) z hz
    obtain ⟨hlez, hopz⟩ := sharedRuns_bottom prims K circuits settings runLimit D net _ _ _ _ b 1 s p.2 z hz
    have htopz : ∃ i, i ∉ D.1 ∧ (z.1.2.operators i).top = some top := by
      obtain ⟨i', hi', hti'⟩ := htop
      exact ⟨i', hi', (hopz i').1.trans hti'⟩
    have htreesz : ∀ b' r, stF.trees b' = some r →
        ∀ z' ∈ support ((simulateQ (loggedWorld prims D) (free (liftComp (refBottom (gameParameter D keys)
          (gameSeeds D keys) top b') (LocalSpec C)))).run z.2), z' = (r, z.2) := fun b' r hb' =>
      refBottom_replay prims D (htrees b' r hb') (le_trans hle2 hlez)
    have hrelz : ∀ x ∈ stT.released, x.2.2 ∉ D.1 ∧ ((z.1.2.operators x.2.2).bottom (treeOf x.1)).isSome := by
      intro x hx
      obtain ⟨bt, hbt⟩ := Option.isSome_iff_exists.1 (hrel x hx).2
      exact ⟨(hrel x hx).1, by rw [(hopz _).2 _ _ hbt]; rfl⟩
    cases hflz : z.1.2.flag
    · rcases hh : heldBottom D z.1.2.operators b with _ | t
      · simp only [StateT.run_pure]
        exact hk _ _ (Or.inr ⟨rfl, ghostRel_mk prims D hc hb hr hinvz hflz htopz htreesz hcorD hrelz⟩)
      · have hkz : (fun i => (z.1.2.operators i).keys) = keys := funext hinvz.1
        simp only [StateT.run_bind, sharedLift_run, bind_map_left, StateT.run_pure, bind_assoc, pure_bind,
          hkz]
        refine prEvent_bind_le_of_eq _ _ _ (loggedFree_replay prims D _ (GameCount.onlySign_prfValue _ _) w p hp
          z.2 hlez) _ ?_
        exact hk _ _ (Or.inr ⟨rfl, ghostRel_mk prims D hc hb hr hinvz hflz htopz htreesz hcorD hrelz⟩)
    · rcases hh : heldBottom D z.1.2.operators b with _ | t
      · simp only [StateT.run_pure]
        exact hk _ _ (Or.inl hflz)
      · simp only [StateT.run_bind, sharedLift_run, bind_map_left, StateT.run_pure, bind_assoc, pure_bind]
        exact prEvent_bind_le_of_forall _ _ _ fun p _ => hk _ _ (Or.inl hflz)

omit [Fintype E] [DecidableEq E] in
/-- `GhostStep` holds for each call of the signing phase, with the ghosts and with the dealer. -/
theorem ghostStep : GhostStep prims K circuits settings runLimit := by
  intro keeps batch compute keys D A top t
  rcases t with t | q | q
  · exact ghostStep_world prims D keys top (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))
  · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
    · exact ghostStep_pure prims D keys top (noAnswer (.corrupt i))
    · exact ghostStep_tree prims K circuits settings runLimit D keeps batch compute keys top A.net b
    · exact ghostStep_round1 prims K circuits settings runLimit D keys top A.net i J e message
    · exact ghostStep_round2 prims K circuits settings runLimit D keys top A.net i J e message parts
  · exact ghostStep_cell prims D keys top q

end Step

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.ghostStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.ghostStep
