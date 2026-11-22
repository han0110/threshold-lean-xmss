import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Shape

/-!
# `ShapeStage`

`givenAnswerGame` and `forgerWorldGame` both start with the keys of the dealer and its top tree,
which always exists (`referenceTree_top`). The corruption calls of the forger give the keys of the
coalition (`corrupt_run`). `SeedGenShape` states that the seed generation of the forger in the world,
with its log dropped, is the start of `A` and `seedGenTail`. After the seed generation `Rel` relates the
two rests (`rel_answerRest`), and the forger wins at least as often, because it also wins with no top
holder when the idle forgery wins.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The top tree -/

/-- The top tree of `referenceTree`. -/
def topTreeWith {m : Type → Type} [Monad m] (lift : ∀ {α : Type}, OracleComp HashSpec α → m α)
    (F : Point → m Digest) (parameter : PublicParameter) : m TopTree := do
  let outputs ← topJobs.mapM (referenceJob lift F parameter)
  let keys := (List.finRange (2 ^ layerHeight)).flatMap fun b =>
    (List.finRange chainCount).map fun l => (topKey b, l)
  let chainEnd := fun (e : KeyIndex) (l : ChainIndex) => digestAt (outputs.getD (keys.idxOf (e, l)) []) 0
  let root ← lift (merkleNode parameter topLayer chainEnd layerHeight 0)
  pure ⟨chainEnd, root⟩

/-- `referenceTree` always gives a top tree for `.top`. -/
theorem referenceTree_top {m : Type → Type} [Monad m] [LawfulMonad m]
    (lift : ∀ {α : Type}, OracleComp HashSpec α → m α) (F : Point → m Digest) (parameter : PublicParameter)
    (top : TopTree) :
    referenceTree lift F parameter top .top =
      (fun t => some (TreeOutput.top t)) <$> topTreeWith lift F parameter := by
  simp [referenceTree, ceremonyOutput, topTreeWith, map_bind]

/-- The top tree of the dealer on the free copy. -/
def topW (parameter : PublicParameter) (seeds : C.Term → HashOutput) : OracleComp (WorldSpec C) TopTree :=
  topTreeWith (fun oa => free (liftComp (tweakable (C := C) oa) (LocalSpec C)))
    (fun x => free (liftComp (prfValue seeds x) (LocalSpec C))) parameter

theorem dealerTop_eq (parameter : PublicParameter) (seeds : C.Term → HashOutput) :
    dealerTop (C := C) parameter seeds = (fun t => some (TreeOutput.top t)) <$> topW parameter seeds := by
  unfold dealerTop topW
  rw [DkgCompletenessProof.freeHom_referenceTree, referenceTree_top]

/-- The dealer of `forgerWorldGame` on the keys `r` and the top tree `t`. -/
def dealtOf (r : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C)) (t : TopTree) :
    Dealt C (OracleComp (WorldSpec C)) :=
  dealtWith (fun oa => free (liftComp oa _)) r.1 r.2.2 t (fun x => free (liftComp (prfValue r.2.1 x) _))

theorem dealerKeyGen_eq :
    dealerKeyGen (C := C) = (do
      let r ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
      let t ← topW r.1 r.2.1
      pure (some (dealtOf r t))) := by
  unfold dealerKeyGen dealerKeyGenWith
  refine bind_congr fun r => ?_
  obtain ⟨parameter, seeds, keys⟩ := r
  simp only [referenceTree_top, bind_map_left]
  rfl

theorem dealerOf_eq_hmap {σ : Type} (r : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C))
    (t : TopTree) :
    dealerOf (σ := σ) r (some (TreeOutput.top t)) = SeedHitProof.Dealt.hmap (stLiftHom σ) (dealtOf r t) := by
  unfold dealerOf dealtOf
  rw [hmap_dealtWith_hom]
  rfl

theorem corrupt_init (D : C.Coalition) (dealt : Dealt C (OracleComp (WorldSpec C))) (log : CallLog C) :
    ((OverPermutation.sequenceFin fun i => if i ∈ D.1 then worldTsig dealt (.corrupt i)
        else (pure none : WorldM C (Option (Keys C)))).run log).run SigningCoreProof.tsigInit =
      pure ((fun i => if i ∈ D.1 then some (dealt.keys i) else none, log), ⟨D.1, fun _ => none, [], fun _ => none⟩) := by
  have hset : (∅ : Finset C.Party) ∪ (Finset.univ.filter fun j : C.Party => j ∈ D.1).image (fun j => j) = D.1 := by
    ext x
    simp
  have h := corrupt_run (D := D) dealt (fun j : C.Party => j) ∅ (by rw [hset]) log
  rw [hset] at h
  exact h

/-! ## The games after the top tree -/

section Games

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings) (runLimit : ℕ) (D : C.Coalition)

/-- The seed generation of the forger in the world, with its log dropped, is the start of `A` and
`seedGenTail`, and it keeps the state of the signing game. -/
def SeedGenShape : Prop :=
  ∀ (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter) (k : C.Party → Keys C)
    (st : TsigState C),
    (fun z => (z.1.1, z.2)) <$>
        ((seedGenWorld D parameter (fun i => if i ∈ D.1 then some (k i) else none) net).run []).run st =
      (fun te => (te, st)) <$> (observe (net.start (corruptInputs D fun _ => ()) []) >>= fun o =>
        seedGenTail D net o.1 o.2 parameter k)

/-- The state of the forger after the seed generation. -/
def startR {σ : Type} (te : σ × (C.Party → Option (Keys C))) : RealState C σ :=
  ⟨te.1, fun i => ⟨te.2 i, none, fun _ => none⟩, fun _ => 0, fun _ => false, false⟩

/-- The body of the forger after the seed generation. -/
def forgerTail (dealt : Dealt C (OracleComp (WorldSpec C))) (A : DkgTsigAdversary C E) (pk : PublicKey)
    (top : TopTree) : RedW C A.net.State Forgery := do
  emulatedRunsW K circuits settings runLimit D A.net (topLeak settings top) 0 .top runLimit
  match topHolder D (← get).operators with
  | none => pure idleForgery
  | some _ => simulateQ (forgeOraclesW K circuits settings runLimit D dealt A.net) (A.forge pk top)

theorem bodyW_run (dealt : Dealt C (OracleComp (WorldSpec C))) (A : DkgTsigAdversary C E) (pk : PublicKey)
    (top : TopTree) :
    ((bodyW K circuits settings runLimit D dealt A pk top).run []).run SigningCoreProof.tsigInit =
      ((seedGenWorld D pk.parameter (fun i => if i ∈ D.1 then some (dealt.keys i) else none) A.net).run []).run
          ⟨D.1, fun _ => none, [], fun _ => none⟩ >>= fun z =>
        (((forgerTail K circuits settings runLimit D dealt A pk top).run' (startR z.1.1)).run z.1.2).run z.2 := by
  unfold bodyW
  rw [StateT.run_bind, StateT.run_bind, corrupt_init, pure_bind]
  simp only [StateT.run_bind]
  rfl

theorem givenAnswerGame_eq (A : DkgTsigAdversary C E) :
    givenAnswerGame K circuits settings runLimit D A = (do
      let r ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
      let t ← topW r.1 r.2.1
      let te ← observe (A.net.start (corruptInputs D fun _ => ()) []) >>= fun o =>
        seedGenTail D A.net o.1 o.2 r.1 r.2.2
      (secRestC K circuits settings runLimit D ⟨true, fun _ => runLimit⟩ A (dealerOf r (some (.top t))) te.2).run'
        (startState D te.1 (keysOf r.2.2 te.2))) := by
  unfold givenAnswerGame
  simp only [dealerTop_eq, bind_map_left, bind_assoc]

theorem forgerWorldGame_eq (A : DkgTsigAdversary C E) :
    forgerWorldGame K circuits settings runLimit D A = (do
      let r ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
      let t ← topW r.1 r.2.1
      let z ← ((bodyW K circuits settings runLimit D (dealtOf r t) A ⟨t.root, r.1⟩ t).run []).run
        SigningCoreProof.tsigInit
      forgeryWins (fun oa => SigningCoreProof.honestLift oa) (dealtOf r t) z.2 z.1.1) := by
  unfold forgerWorldGame
  rw [dealerKeyGen_eq]
  simp only [bind_assoc, pure_bind]
  rfl

/-! ## The probability of a win -/

variable (prims : Primitives)

/-- The probability that `P` gives `true` in `streamWorld` from the cache `w`. -/
def evt (P : OracleComp (WorldSpec C) Bool) (w : HashCache C × HiddenCache C) : ENNReal :=
  Pr{let z ← (simulateQ (streamWorld prims D) P).run w}[z.1 = true]

theorem evt_bind_mono {α : Type} (x : OracleComp (WorldSpec C) α) {f g : α → OracleComp (WorldSpec C) Bool}
    (h : ∀ a w, evt D prims (f a) w ≤ evt D prims (g a) w) (w : HashCache C × HiddenCache C) :
    evt D prims (x >>= f) w ≤ evt D prims (x >>= g) w := by
  unfold evt
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  exact prEvent_bind_mono_of_support _ _ _ fun a _ => h a.1 a.2

theorem forgerRest_le (dealt : Dealt C (OracleComp (WorldSpec C))) (A : DkgTsigAdversary C E)
    (rs : RealState C A.net.State) (log : CallLog C) (st : TsigState C) (w : HashCache C × HiddenCache C) :
    Pr{let z ← semFW prims D (forgerRest K circuits settings runLimit D A dealt) rs log st w}[z.1.1.1.1 = true] ≤
      Pr{let z ← (simulateQ (streamWorld prims D) ((((forgerTail K circuits settings runLimit D dealt A
        ⟨dealt.top.root, dealt.parameter⟩ dealt.top).run' rs).run log).run st >>= fun z =>
          forgeryWins (fun oa => SigningCoreProof.honestLift oa) dealt z.2 z.1.1)).run w}[z.1 = true] := by
  unfold semFW forgerRest forgerTail
  simp only [StateT.run_bind, StateT.run'_eq, StateT.run_map, simulateQ_bind, map_bind, bind_assoc,
    bind_map_left, StateT.run_get, pure_bind]
  refine prEvent_bind_mono_of_support _ _ _ fun a _ => ?_
  cases topHolder D a.1.1.1.2.operators with
  | none => simp
  | some holder =>
    simp only [StateT.run_bind, StateT.run_lift, simulateQ_bind, map_bind, bind_assoc, StateT.run_get, pure_bind,
      toWorld, simulateQ_pure, StateT.run_pure, map_pure]
    simp only [bind_pure_comp]
    exact le_of_eq rfl

theorem post_le (A : DkgTsigAdversary C E) (r : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C))
    (t : TopTree) (te : A.net.State × (C.Party → Option (Keys C))) (log : CallLog C)
    (w : HashCache C × HiddenCache C) :
    evt D prims ((secRestC K circuits settings runLimit D ⟨true, fun _ => runLimit⟩ A (dealerOf r (some (.top t)))
        te.2).run' (startState D te.1 (keysOf r.2.2 te.2))) w ≤
      Pr{let z ← (simulateQ (streamWorld prims D) ((((forgerTail K circuits settings runLimit D (dealtOf r t) A
        ⟨t.root, r.1⟩ t).run' (startR te)).run log).run ⟨D.1, fun _ => none, [], fun _ => none⟩ >>= fun z =>
          forgeryWins (fun oa => SigningCoreProof.honestLift oa) (dealtOf r t) z.2 z.1.1)).run w}[z.1 = true] := by
  refine le_trans (le_of_eq ?_)
    (forgerRest_le K circuits settings runLimit D prims (dealtOf r t) A (startR te) log _ w)
  rw [secRestC_eq, dealerOf_eq_hmap]
  have hrel := (rel_answerRest (prims := prims) (D := D) (k := r.2.2) (fl := seedsDiffer D (keysOf r.2.2 te.2))
    (emu := te.2) K circuits settings runLimit A (dealt := dealtOf r t) (startR te) log
    ⟨D.1, fun _ => none, [], fun _ => none⟩ w (fun _ => rfl)).1
  have e1 : evt D prims ((Prod.fst <$> (answerRest K circuits settings runLimit D te.2 A
      (SeedHitProof.Dealt.hmap (stLiftHom A.net.State) (dealtOf r t))).run
        ⟨D.1, fun _ => none, [], fun _ => none⟩).run' (startState D te.1 (keysOf r.2.2 te.2))) w =
      Pr{let z ← semGL prims D (answerRest K circuits settings runLimit D te.2 A
        (SeedHitProof.Dealt.hmap (stLiftHom A.net.State) (dealtOf r t))) ⟨D.1, fun _ => none, [], fun _ => none⟩
          (keysProj r.2.2 (seedsDiffer D (keysOf r.2.2 te.2)) (startR te)) w}[z.1.1.1 = true] := by
    unfold evt semGL
    simp only [StateT.run'_eq, StateT.run_map, simulateQ_map, Functor.map_map]
    rfl
  rw [e1, hrel.prEvent_eq, prEvent_map]
  rfl

theorem rest_le (hseed : SeedGenShape (E := E) D) (A : DkgTsigAdversary C E)
    (r : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C)) (t : TopTree)
    (w : HashCache C × HiddenCache C) :
    evt D prims ((observe (A.net.start (corruptInputs D fun _ => ()) []) >>= fun o =>
        seedGenTail D A.net o.1 o.2 r.1 r.2.2) >>= fun te =>
      (secRestC K circuits settings runLimit D ⟨true, fun _ => runLimit⟩ A (dealerOf r (some (.top t))) te.2).run'
        (startState D te.1 (keysOf r.2.2 te.2))) w ≤
      evt D prims (((bodyW K circuits settings runLimit D (dealtOf r t) A ⟨t.root, r.1⟩ t).run []).run
        SigningCoreProof.tsigInit >>= fun z =>
          forgeryWins (fun oa => SigningCoreProof.honestLift oa) (dealtOf r t) z.2 z.1.1) w := by
  have hs := hseed A.net r.1 r.2.2 ⟨D.1, fun _ => none, [], fun _ => none⟩
  have hL : (observe (A.net.start (corruptInputs D fun _ => ()) []) >>= fun o =>
      seedGenTail D A.net o.1 o.2 r.1 r.2.2) =
      (fun z => z.1.1) <$> ((seedGenWorld D r.1 (fun i => if i ∈ D.1 then some (r.2.2 i) else none) A.net).run
        []).run ⟨D.1, fun _ => none, [], fun _ => none⟩ := by
    have h1 := congrArg (fun c => Prod.fst <$> c) hs
    simpa using h1.symm
  rw [hL, bodyW_run, bind_assoc]
  unfold evt
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind, map_bind, map_bind, simulateQ_map,
    StateT.run_map, bind_map_left]
  refine prEvent_bind_mono_of_support _ _ _ fun q hq => ?_
  have hst : q.1.2 = ⟨D.1, fun _ => none, [], fun _ => none⟩ := by
    have h2 := congrArg (fun c => (simulateQ (streamWorld prims D) c).run w) hs
    simp only [simulateQ_map, StateT.run_map] at h2
    have hmem : ((q.1.1.1, q.1.2), q.2) ∈ support ((fun z => ((z.1.1.1, z.1.2), z.2)) <$>
        (simulateQ (streamWorld prims D) (((seedGenWorld D r.1 (fun i => if i ∈ D.1 then some (r.2.2 i) else none)
          A.net).run []).run ⟨D.1, fun _ => none, [], fun _ => none⟩)).run w) := by
      rw [support_map]
      exact ⟨q, hq, rfl⟩
    rw [h2, support_map] at hmem
    obtain ⟨p, -, hp⟩ := hmem
    simp only [Prod.mk.injEq] at hp
    exact hp.1.2.symm
  have h := post_le K circuits settings runLimit D prims A r t q.1.1.1 q.1.1.2 q.2
  rw [← hst] at h
  exact h

end Games

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (runLimit : ℕ) (prims : Primitives)

/-- `ShapeStage` from `SeedGenShape`. -/
theorem shapeStage_of_seedGenShape (hseed : ∀ D : C.Coalition, SeedGenShape (E := E) D) :
    ShapeStage K circuits settings runLimit prims := fun _ D A => by
  unfold streamAccepts
  refine ENNReal.toReal_mono (prEvent_ne_top _) ?_
  rw [givenAnswerGame_eq, forgerWorldGame_eq]
  exact evt_bind_mono D prims _ (fun r w => evt_bind_mono D prims _
    (fun t w => rest_le K circuits settings runLimit D prims (hseed D) A r t w) w) (∅, ∅)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.shapeStage_of_seedGenShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.shapeStage_of_seedGenShape
