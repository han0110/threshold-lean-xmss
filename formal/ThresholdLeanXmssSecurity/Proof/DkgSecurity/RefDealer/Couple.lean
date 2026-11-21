import ThresholdLeanXmssSecurity.Proof.DkgSecurity.RefDealer.Erase
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.RefDealer.Step

/-!
# The glue and the win test of `GhostCouple`

`ghostCouple_of_parts` proves `GhostCouple` from `GhostStep`, the step of one call of the signing
phase, and `GhostWin`, the step of the win test. `ghostWin` proves `GhostWin`. With `t` signers of a
key, an honest operator released a chain part at that key, so it holds the bottom tree of the key,
and with no flag the dealer builds that tree. `sharedRefDealer_of_step` proves `SharedRefDealer` from
`PassWrongCheck` and `GhostStep`, and `sharedRefDealer_of_wrong` from `PassWrongCheck` with
`ghostStep`.
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

/-! ## The glue of `GhostCouple` -/

section Glue

attribute [local irreducible] MonadAttach.support

variable (D : C.Coalition) {σ : Type}

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The honest signature on held bottom trees keeps the flag. -/
theorem flagUp_heldHonest (parameter : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (seeds : C.Term → HashOutput) (held : Fin (2 ^ layerHeight) → Option BottomTree) (e : KeyIndex)
    (message : Message) :
    FlagUp (honestSignature (sharedLift (σ := σ) (loggedWorld prims D))
      { dealtWith (m := SharedM C ProbComp (LogState C) σ) (sharedLift (loggedWorld prims D)) parameter keys top
          (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)) with
        bottom := fun b => pure (held b) } e message) := by
  rw [← hmap_heldDealt prims D σ parameter keys top seeds held]
  have h := hom_honestSignature (roHom prims D σ) (fun oa => oa) (heldDealt parameter keys top seeds held) e message
  have h' : honestSignature (sharedLift (σ := σ) (loggedWorld prims D))
      (SeedHitProof.Dealt.hmap (roHom prims D σ) (heldDealt parameter keys top seeds held)) e message =
      roHom prims D σ (honestSignature (fun oa => oa) (heldDealt parameter keys top seeds held) e message) := h.symm
  rw [h']
  exact flagUp_sharedLift prims D _

omit [Fintype E] [DecidableEq E] in
/-- The win test with the ghosts keeps the flag. -/
theorem flagUp_ghostWinTest (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (keysT : Keys C) (p : Forgery × TsigState C) :
    FlagUp (ghostWinTest (σ := σ) (loggedWorld prims D) D parameter seeds top keysT p) := by
  unfold ghostWinTest
  refine flagUp_get_bind fun s => ?_
  unfold forgeryWins
  refine FlagUp.bind (flagUp_sharedLift prims D _) fun verified => ?_
  split_ifs
  · exact FlagUp.bind (flagUp_pure _) fun _ => flagUp_pure _
  · have e : honestSignature (sharedLift (σ := σ) (loggedWorld prims D))
        { dealtWith (m := SharedM C ProbComp (LogState C) σ) (sharedLift (loggedWorld prims D)) keysT.parameter
            (fun i => ((s.operators i).keys).getD noKeys) top
            (fun x => sharedLift (loggedWorld prims D) (prfValue (gameSeeds D fun i => (s.operators i).keys) x)) with
          bottom := fun b => do
            sharedLift (loggedWorld prims D) ((fun _ => ()) <$> refBottom parameter seeds top b)
            pure (heldBottom D s.operators b) } p.1.signature.leafIndex p.1.message =
        sharedLift (loggedWorld prims D) ((fun _ => ()) <$> refBottom parameter seeds top (treeOf p.1.signature.leafIndex))
          >>= fun _ =>
          honestSignature (sharedLift (σ := σ) (loggedWorld prims D))
            { dealtWith (m := SharedM C ProbComp (LogState C) σ) (sharedLift (loggedWorld prims D)) keysT.parameter
                (fun i => ((s.operators i).keys).getD noKeys) top
                (fun x => sharedLift (loggedWorld prims D) (prfValue (gameSeeds D fun i => (s.operators i).keys) x)) with
              bottom := fun b => pure (heldBottom D s.operators b) } p.1.signature.leafIndex p.1.message := by
      unfold honestSignature
      simp only [bind_assoc, pure_bind]
    rw [e]
    simp only [bind_assoc]
    exact FlagUp.bind (flagUp_sharedLift prims D _) fun _ => FlagUp.bind (flagUp_heldHonest prims D _ _ _ _ _ _ _)
      fun _ => FlagUp.bind (flagUp_pure _) fun _ => flagUp_pure _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- From a state with the flag, a program that keeps the flag ends with no flag with probability 0. -/
theorem prEvent_noFlag_eq_zero {α : Type} {x : SharedM C ProbComp (LogState C) σ α} (hx : FlagUp x)
    (s : RealState C σ) (w : LogState C) (hs : s.flag = true) (P : α → Prop) :
    Pr{let z ← (x.run s).run w}[P z.1.1 ∧ z.1.2.flag = false] = 0 := by
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => ?_
  simp [hx s w hs z hz]

omit [Fintype E] [DecidableEq E] in
/-- The continuation of `GhostCouple` after the top tree of the dealer, with a held top tree and no
flag. -/
theorem ghostCouple_noFlag (step : GhostStep prims K circuits settings runLimit) (win : GhostWin (C := C) prims)
    (keeps : RefRunKeeps prims K circuits settings) (batch : 0 < settings.batchSize)
    (compute : CircuitsCompute circuits prims.Th) (keys : C.Party → Option (Keys C)) (A : DkgTsigAdversary C E)
    (s : RealState C A.net.State) (w : LogState C) (hinv : RefInv prims keys D s w) (keysT : Keys C) (top : TopTree)
    (htop : topHolder D s.operators = some (keysT, top)) (o : Option TreeOutput) (w' : LogState C)
    (hfree : (o, w') ∈ support ((simulateQ (loggedWorld prims D) (free (liftComp (referenceTree tweakable
      (prfValue (gameSeeds D keys)) (gameParameter D keys) emptyTop .top) (LocalSpec C)))).run w))
    (hflag : s.flag = false) :
    Pr{let z ← (((simulateQ (ghostHandlers prims K circuits settings runLimit keys D A top)
          (A.forge ⟨top.root, keysT.parameter⟩ top)).run (startSig D) >>=
            ghostWinTest (loggedWorld prims D) D (gameParameter D keys) (gameSeeds D keys) top keysT).run s).run w'}[
        z.1.1 = true ∧ z.1.2.flag = false] ≤
      Pr{let z ← (((simulateQ (dealerHandlers prims K circuits settings runLimit keys D A
            (coupleDealer prims keys D A.net.State ((TreeOutput.topTree o).getD emptyTop)))
          (A.forge ⟨((TreeOutput.topTree o).getD emptyTop).root, gameParameter D keys⟩
            ((TreeOutput.topTree o).getD emptyTop))).run (startSig D) >>= fun q =>
            forgeryWins (sharedLift (loggedWorld prims D))
              (coupleDealer prims keys D A.net.State ((TreeOutput.topTree o).getD emptyTop)) q.2 q.1).run s).run w'}[
        z.1.1 = true ∧ z.1.2.flag = false] := by
  obtain ⟨i, hi, hki, hti⟩ := topHolder_some htop
  have hout := hinv.2.2 hflag
  have hkeys : (fun i => (s.operators i).keys) = keys := funext hinv.1
  have hp1 : o = some (.top top) := by
    refine loggedFree_determined prims D _ (GameCount.onlySign_referenceTree _ _ _ _) w hinv.2.1 _
      (fun hf hg ha => ?_) (o, w') hfree
    have h := (hout.2 i hi hf hg ha).1 top hti
    rwa [hkeys] at h
  have hpar : keysT.parameter = gameParameter D keys :=
    parameter_eq_gameParameter D keys (hkeys ▸ hout.1) i hi keysT (by rw [← hinv.1 i]; exact hki)
  subst hp1
  rw [hpar, run_bind_runSig, run_bind_runSig]
  have hle : w.1.1 ≤ w'.1.1 := loggedWorld_cache_le prims D _ w _ hfree
  have hmpc : NoMpc w'.1.1 := loggedWorld_noMpc prims D _ w hinv.2.1 _ hfree
  refine leArrow_simulateQ (ghostHandlers prims K circuits settings runLimit keys D A top)
    (dealerHandlers prims K circuits settings runLimit keys D A (coupleDealer prims keys D A.net.State top))
    (fun u => u.2.1.flag = true) (GhostRel prims keys D top)
    (fun t => step keeps batch compute keys D A top t) (fun t u hu o ho => ?_) _ _ _
    (Or.inr ⟨rfl, rfl, rfl, rfl, refInv_mono prims D hinv hle hmpc, hflag, ⟨i, hi, hti⟩,
      fun b r h => by simp [startSig] at h, rfl, fun r h => by simp [startSig] at h⟩) _ _ _ _ _ _
    fun oT oF hrel => ?_
  · obtain ⟨z, hz, rfl⟩ := runSig_support _ u o ho
    exact flagUpT_ghostHandlers prims K circuits settings runLimit D A keys top t u.1 u.2.1 u.2.2 hu z hz
  · rcases hrel with hL | ⟨hans, hG⟩
    · exact (prEvent_noFlag_eq_zero (flagUp_ghostWinTest prims D (gameParameter D keys) (gameSeeds D keys) top keysT
        (oT.1, oT.2.1)) _ _ hL (fun b => b = true)).le.trans zero_le
    · obtain ⟨oT1, uT⟩ := oT
      obtain ⟨oF1, uF⟩ := oF
      dsimp only at hans hG ⊢
      subst hans
      exact win keys D A.net.State top keysT uT uF oT1 hG hpar

omit [Fintype E] [DecidableEq E] in
/-- `GhostCouple` from the step of one call and the step of the win test. -/
theorem ghostCouple_of_parts (step : GhostStep prims K circuits settings runLimit)
    (win : GhostWin (C := C) prims) : GhostCouple prims K circuits settings runLimit := by
  intro keeps batch compute keys D A s w hinv
  rcases htop : topHolder D s.operators with _ | ⟨keysT, top⟩
  · have e : ((ghostSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst D A (gameParameter D keys)
        (gameSeeds D keys) (fun i => (keys i).getD noKeys)).run s).run w = pure ((false, s), w) := by
      unfold ghostSigning
      simp only [StateT.run_bind, StateT.run_get, pure_bind, htop, StateT.run_pure]
    rw [e]
    simp
  rw [ghostSigning_run_some prims K circuits settings runLimit keys D A s w keysT top htop,
    dealerSigning_run_some prims K circuits settings runLimit keys D A s w keysT top htop]
  refine probEvent_bind_le_of_support _ _ _ _ _ fun p hp => ?_
  obtain ⟨hps, hpfree⟩ := sharedLift_run_support prims D (referenceTree tweakable (prfValue (gameSeeds D keys))
    (gameParameter D keys) emptyTop .top) s w p (by with_reducible exact hp)
  rw [hps]
  cases hflag : s.flag
  · exact ghostCouple_noFlag prims K circuits settings runLimit D step win keeps batch compute keys A s w hinv keysT
      top htop p.1.1 p.2 (by with_reducible exact hpfree) hflag
  · exact (prEvent_noFlag_eq_zero (x := (simulateQ (ghostHandlers prims K circuits settings runLimit keys D A top)
        (A.forge ⟨top.root, keysT.parameter⟩ top)).run (startSig D) >>=
          ghostWinTest (loggedWorld prims D) D (gameParameter D keys) (gameSeeds D keys) top keysT)
      (FlagUp.bind (flagUpT_simulateQ _ (flagUpT_ghostHandlers prims K circuits settings
      runLimit D A keys top) _ _) fun q => flagUp_ghostWinTest prims D _ _ _ _ q) s p.2 hflag
      (fun b => b = true)).le.trans zero_le

end Glue

/-! ## The win test of `GhostCouple` -/

section Win

attribute [local irreducible] MonadAttach.support

variable (D : C.Coalition) {σ : Type}

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A local computation of the honest operators and its continuation, from a state of the game. -/
theorem sharedLift_bind_run {α β : Type} (X : OracleComp (RoSpec C) α) (f : α → SharedM C ProbComp (LogState C) σ β)
    (s : RealState C σ) (w : LogState C) :
    ((sharedLift (loggedWorld prims D) X >>= f).run s).run w =
      (simulateQ (loggedWorld prims D) (free (liftComp X (LocalSpec C)))).run w >>= fun p => ((f p.1).run s).run p.2 := by
  simp [sharedLift, inWorld, StateT.run_bind, StateT.run_lift]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The honest signature reads the bottom tree of the key once, at its start. -/
theorem honestSignature_bottom {m : Type → Type} [Monad m] [LawfulMonad m]
    (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) (dealt : Dealt C m) (e : KeyIndex) (message : Message) :
    honestSignature lift dealt e message = dealt.bottom (treeOf e) >>= fun tree =>
      honestSignature lift { dealt with bottom := fun _ => pure tree } e message := by
  unfold honestSignature
  simp only [pure_bind]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The signers of a key depend only on the corrupt operators and the releases. -/
theorem signersAt_congr {st st' : TsigState C} (hc : st.corrupt = st'.corrupt) (hr : st.released = st'.released)
    (e : KeyIndex) (message : Message) : signersAt st e message = signersAt st' e message := by
  unfold signersAt
  rw [hc, hr]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- With the coalition as the corrupt operators, `t` signers of a key include an honest release. -/
theorem exists_release {st : TsigState C} (hc : st.corrupt = D.1) {e : KeyIndex} {message : Message}
    (hcard : ¬ (signersAt st e message).card < C.t) :
    ∃ r ∈ st.released, r.1 = e ∧ r.2.1 = message ∧ r.2.2 ∉ D.1 := by
  by_contra h
  push Not at h
  apply hcard
  have hsub : signersAt st e message ⊆ D.1 := by
    intro x hx
    unfold signersAt at hx
    rcases Finset.mem_union.1 hx with hx | hx
    · rwa [hc] at hx
    · simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
      obtain ⟨r, ⟨hr, he, hm⟩, rfl⟩ := hx
      exact h r hr he hm
  have := Finset.card_le_card hsub
  have := D.2
  have := C.one_le_t
  omega

omit [Fintype E] [DecidableEq E] in
theorem ghostWin : GhostWin (C := C) prims := by
  intro keys D σ top keysT uT uF forgery hG hpar
  obtain ⟨huu, hcor, -, hrel, hinv, hflag, ⟨i, hi, hti⟩, -, hcorD, hreleased⟩ := hG
  obtain ⟨st, s, w⟩ := uT
  obtain ⟨stF, sF, wF⟩ := uF
  simp only [Prod.mk.injEq] at huu
  obtain ⟨rfl, rfl⟩ := huu
  dsimp only at hcor hrel hinv hflag hti hcorD hreleased ⊢
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hinv.1, hpar]
  unfold forgeryWins
  rw [sharedLift_bind_run, sharedLift_bind_run]
  refine probEvent_bind_le_of_support _ _ _ _ _ fun p hp => ?_
  rw [signersAt_congr hcor hrel]
  split_ifs with hc
  · exact le_rfl
  rw [honestSignature_bottom, honestSignature_bottom, dealtWith_bottom_shared]
  dsimp only
  simp only [bind_assoc, pure_bind]
  rw [sharedLift_map, bind_map_left, sharedLift_bind_run, sharedLift_bind_run]
  refine probEvent_bind_le_of_support _ _ _ _ _ fun q hq => ?_
  have hc' : ¬ (signersAt st forgery.signature.leafIndex forgery.message).card < C.t := by
    rwa [signersAt_congr hcor hrel]
  obtain ⟨r, hr, he, -, -⟩ := exists_release D hcorD hc'
  obtain ⟨hrD, hrb⟩ := hreleased r hr
  rw [he] at hrb
  obtain ⟨k, bt, hk, hbt, hheld⟩ := heldBottom_some D hrD hrb
  have hle : w.1.1 ≤ p.2.1.1 := loggedWorld_cache_le prims D _ w _ hp
  have hmpc : NoMpc p.2.1.1 := loggedWorld_noMpc prims D _ w hinv.2.1 _ hp
  have hq1 : q.1 = some bt := loggedFree_determined prims D _ (onlySign_refBottom _ _ _ _) p.2 hmpc _
    (fun hf hg ha => refBottom_held prims D hinv hflag hi hti hk hbt hf hg (Agrees.mono hle ha)) q hq
  rw [hq1, hheld]

omit [Fintype E] [DecidableEq E] in
/-- `GhostCouple` from the step of one call. -/
theorem ghostCouple_of_step (step : GhostStep prims K circuits settings runLimit) :
    GhostCouple prims K circuits settings runLimit :=
  ghostCouple_of_parts prims K circuits settings runLimit step (ghostWin prims)

end Win

omit [Fintype E] [DecidableEq E] in
/-- `SharedRefDealer` from a wrong output and the step of one call. -/
theorem sharedRefDealer_of_step (wrong : PassWrongCheck prims K circuits settings)
    (step : GhostStep prims K circuits settings runLimit) : SharedRefDealer prims K circuits settings runLimit :=
  sharedRefDealer_of_couple prims K circuits settings runLimit (passCleanOutput_of prims K circuits settings wrong)
    (ghostCouple_of_step prims K circuits settings runLimit step)

omit [Fintype E] [DecidableEq E] in
/-- `SharedRefDealer` from a wrong output of one run. -/
theorem sharedRefDealer_of_wrong (wrong : PassWrongCheck prims K circuits settings) :
    SharedRefDealer prims K circuits settings runLimit :=
  sharedRefDealer_of_step prims K circuits settings runLimit wrong
    (ghostStep prims K circuits settings runLimit)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.ghostCouple_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.ghostCouple_of_step

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_step

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_wrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedRefDealer_of_wrong
