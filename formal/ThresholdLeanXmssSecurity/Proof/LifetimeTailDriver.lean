import ThresholdLeanXmssSecurity.Proof.LifetimeTailKernel
import ThresholdLeanXmssSecurity.Proof.LifetimeSetupBridge

/-!
# The lifetime continuation at a selected PRSS reveal

The driver retains each operator's top tree, the complete suspended lifetime
state and the continuation receiving the reveal's visible outboxes. Only the
selected ceremony uses the free honest interface; subsequent ceremonies use
the counted interface. Settlement and the forgery test are the lifetime's own.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace ThresholdLeanXmssSecurity.LifetimeTailDriver

open LifetimeTailKernel LifetimeRunBoundary LifetimeSetupBridge LifetimeIdealBad

attribute [local instance] Classical.propDecidable
variable {C : Committee} {E σ : Type}

structure TailSeed (C : Committee) (E : Type) where
  keys : C.Party → Keys C
  h : C.Party
  tree : ThresholdLeanXmss.Tree
  state : LifetimeState C E
  rest : Option (Sent C E) → Program C E

def tailRoles (n r : ℕ) : Roles C (OracleComp (WorldSpec C)) :=
  if r = n then worldRoles else ⟨worldRoles.adversary, worldRoles.adversary⟩

def roW {α : Type} (p : OracleComp (RoSpec C) α) : OracleComp (WorldSpec C) α :=
  worldRoles.honest (liftComp p _)

def valueW (D : C.Coalition) (keys : C.Party → Keys C) (x : Point) :
    OracleComp (WorldSpec C) Digest := roW (prfValue (honestSeeds D keys) x)

def forgerW : QueryImpl (LocalSpec C) (StateT (LifetimeState C E) (OracleComp (WorldSpec C))) :=
  fun t => StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))

def finishW (D : C.Coalition) (keys : C.Party → Keys C) (h : C.Party)
    (r : Forgery × LifetimeState C E) : OracleComp (WorldSpec C) Bool :=
  if ¬ ∀ i, i ∉ D.1 → (r.2.top i).isSome then pure false else do
  let some (_, top) := r.2.publicKey (keys h).parameter h | pure false
  forgeryWins roW (dealtWith roW (keys h).parameter keys top (valueW D keys)) r.2.sign r.1

variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (n : ℕ)

def oraclesW (keys : C.Party → Keys C) (h : C.Party) :
    QueryImpl (LocalSpec C + LifetimeSpec C E) (StateT (LifetimeState C E) (OracleComp (WorldSpec C))) :=
  (forgerW (C := C) (E := E)) + lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles D keys (valueW D keys) h

def lifeDriver (seed : σ → Option (TailSeed C E)) : TailDriver C E σ where
  keys s := (seed s).map TailSeed.keys |>.getD (fun _ => default)
  top s i := ((seed s).bind (fun t => t.state.top i)).getD emptyTop
  tree s := ((seed s).map TailSeed.tree).getD .top
  stop _ := pure false
  run s steps := match seed s with
    | none => pure false
    | some t => if CountIs (n + 1) t.state then
        (simulateQ (oraclesW K circuits settings attempts D n t.keys t.h)
          (t.rest (some (toCoalition D steps)))).run
          (LifetimeState.settle D { t.state with running := some (t.tree, ceremonyFuel circuits settings - 2, steps) }) >>= finishW D t.keys t.h
      else pure false

/-- A non-round request preserves the complete running suspension. -/
theorem nonround_runningW (keys : C.Party → Keys C) (h : C.Party)
    (st : LifetimeState C E) (hrun : st.running ≠ none) (q : LifetimeQuery C E)
    (hq : ∀ sent, q ≠ .round sent) (r : _ × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles
      D keys (valueW D keys) h q).run st)) : r.2.running = st.running := by
  cases q with
  | sign q =>
    cases q with
    | corrupt i => have he : r = (none, st) := hr; rw [he]
    | tree b =>
      rw [LifetimeProof.run_sign_tree] at hr
      exact (LifetimeProof.signAs_frame worldRoles keys (valueW D keys) h (.tree b) st r hr).2
    | round1 i J e message =>
      rw [LifetimeProof.run_round1] at hr
      split at hr
      · have he : r = (none, st) := hr; rw [he]
      · exact (LifetimeProof.signAs_frame worldRoles keys (valueW D keys) i
          (.round1 i J e message) _ r hr).2
    | round2 i J e message parts =>
      rw [LifetimeProof.run_round2] at hr
      split at hr
      · have he : r = (none, st) := hr; rw [he]
      · exact (LifetimeProof.signAs_frame worldRoles keys (valueW D keys) i
          (.round2 i J e message parts) _ r hr).2
  | publicKey => have he : r = (st.publicKey (keys h).parameter h, st) := hr; rw [he]
  | start tree =>
    rw [LifetimeProof.run_start, if_pos (fun hc => hrun hc.1)] at hr
    have he : r = (none, st) := hr
    rw [he]
  | round sent => exact False.elim (hq sent rfl)

/-- Non-round requests cannot change the chronological index while a run is suspended. -/
theorem nonround_countW (keys : C.Party → Keys C) (h : C.Party)
    (st : LifetimeState C E) (hrun : st.running ≠ none) (q : LifetimeQuery C E)
    (hq : ∀ sent, q ≠ .round sent) (r : _ × LifetimeState C E)
    (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles
      D keys (valueW D keys) h q).run st)) : r.2.runCount = st.runCount := by
  have hc := LifetimeProof.lifetimeOracles_runCount K circuits settings attempts (tailRoles n)
    worldRoles D keys (valueW D keys) h q st r hr
  cases q with
  | start tree =>
    rw [LifetimeProof.run_start, if_pos (fun hc => hrun hc.1)] at hr
    have he : r = (none, st) := hr
    rw [he]
  | _ => simpa [LifetimeProof.newRun] using hc

omit [Field E] [Algebra Bit E] in
theorem finishW_replaceSteps (keys : C.Party → Keys C) (h : C.Party)
    (steps : C.Party → Step C E RealSpec TreeOutput) (f : Forgery) (st : LifetimeState C E) :
    finishW D keys h (f, replaceSteps steps st) = finishW D keys h (f, st) := rfl

/-- Until the first round, non-round answers agree exactly; that round makes the states equal. -/
theorem continuation_alike (keys : C.Party → Keys C) (h : C.Party)
    (first second : C.Party → Step C E RealSpec TreeOutput) (ha : RoundAlike D first second)
    (prog : Program C E) (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (hrun : st.running = some (tree, fuel, first)) (hc : st.runCount = n + 1) :
    ((simulateQ (oraclesW K circuits settings attempts D n keys h) prog).run st >>= finishW D keys h) =
    ((simulateQ (oraclesW K circuits settings attempts D n keys h) prog).run
      (replaceSteps second st) >>= finishW D keys h) := by
  induction prog using OracleComp.inductionOn generalizing st with
  | pure f => simp only [simulateQ_pure, StateT.run_pure, pure_bind, finishW_replaceSteps]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases t with t | q
    · have hh : ∀ s : LifetimeState C E,
          (oraclesW K circuits settings attempts D n keys h (.inl t)).run s =
            (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun a => pure (a, s)) :=
          fun _ => rfl
      simp only [hh, bind_assoc, pure_bind]
      exact bind_congr fun a => ih a st hrun hc
    · by_cases hq : ∃ sent, q = .round sent
      · obtain ⟨sent, rfl⟩ := hq
        change ((lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles D keys
          (valueW D keys) h (.round sent)).run st >>= _) =
          ((lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles D keys
          (valueW D keys) h (.round sent)).run (replaceSteps second st) >>= _)
        rw [LifetimeProof.run_round, LifetimeProof.run_round]
        simp only [replaceSteps, hrun, Option.map_some]
        have hc0 : st.topRuns + ∑ b, st.bottomRuns b = n + 1 := hc
        simp only [LifetimeState.runCount, hc0, Nat.add_sub_cancel, tailRoles, if_true]
        have he := stepRound_alike D (roundAdversary (I := Keys C) sent) () first second ha
        change stepRound worldRoles D (roundAdversary (I := PEmpty) sent) noFunctionality () first =
          stepRound worldRoles D (roundAdversary (I := PEmpty) sent) noFunctionality () second at he
        rw [he]
      · change ((lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles D keys
          (valueW D keys) h q).run st >>= _) =
          ((lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles D keys
          (valueW D keys) h q).run (replaceSteps second st) >>= _)
        have hn : st.running ≠ none := by rw [hrun]; simp
        rw [request_replaceSteps worldRoles keys (valueW D keys) K circuits settings attempts
          (tailRoles n) D h second st hn q (fun sent he => hq ⟨sent, he⟩)]
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
        apply OracleComp.bind_congr_of_forall_mem_support
        intro r hr
        exact ih r.1 r.2
          ((nonround_runningW K circuits settings attempts D n keys h st hn q
            (fun sent he => hq ⟨sent, he⟩) r hr).trans hrun)
          ((nonround_countW K circuits settings attempts D n keys h st hn q
            (fun sent he => hq ⟨sent, he⟩) r hr).trans hc)

/-- The driver observes exactly the pointwise round interface, including the final outboxes. -/
theorem lifeDriver_alike (seed : σ → Option (TailSeed C E)) (s : σ)
    (first second : C.Party → Step C E RealSpec TreeOutput) (ha : RoundAlike D first second) :
    (lifeDriver K circuits settings attempts D n seed).run s first =
      (lifeDriver K circuits settings attempts D n seed).run s second := by
  simp only [lifeDriver]
  cases hs : seed s with
  | none => rfl
  | some t =>
    dsimp only
    split
    · rename_i hc
      rw [ha.visible]
      have hd : (∀ i, i ∉ D.1 → (first i).isDone) ↔ ∀ i, i ∉ D.1 → (second i).isDone := ha.done
      simp only [LifetimeState.settle]
      by_cases done : ceremonyFuel circuits settings - 2 = 0 ∨ ∀ i, i ∉ D.1 → (first i).isDone
      · have done' := done.imp id hd.mp
        simp only [if_pos done, if_pos done']
        cases t.tree <;> simp only [ha.output]
      · have done' : ¬ (ceremonyFuel circuits settings - 2 = 0 ∨ ∀ i, i ∉ D.1 → (second i).isDone) :=
          fun hh => done (hh.imp id hd.mpr)
        simp only [if_neg done, if_neg done']
        exact continuation_alike K circuits settings attempts D n t.keys t.h first second ha
            (t.rest (some (toCoalition D second)))
            { t.state with running := some (t.tree, ceremonyFuel circuits settings - 2, first) }
            t.tree (ceremonyFuel circuits settings - 2) rfl hc
    · rfl

/-- Signing uses neither a PRSS setup hash nor a stream query. -/
def RoUnsafe : (RoSpec C).Domain → Prop
  | .inl q => aimedSetupQuery q
  | .inr _ => True

theorem hash_setupQuiet (q : Query C) (hq : ¬ RoUnsafe (.inl q)) :
    IsQueryBoundP (hashQuery q) RoUnsafe 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h hq

/-- The signing walk of `LifetimeStreamKeyQuiet`, with both PRSS setup hash
constructors and streams excluded. Its combinators are VCV query-bound rules. -/
theorem tweakable_setupQuiet {α : Type} (p : OracleComp HashSpec α) :
    IsQueryBoundP (tweakable (C := C) p) RoUnsafe 0 :=
  LifetimeKeygenPrograms.qb0_simulateQ _ (fun _ => hash_setupQuiet _ id) p

theorem prfValue_setupQuiet (seeds : C.Term → HashOutput) (x : Point) :
    IsQueryBoundP (prfValue seeds x) RoUnsafe 0 := by
  unfold prfValue
  apply zero_bind RoUnsafe (zero_mapM _ _ _ fun _ => ?_) fun _ _ => isQueryBoundP_pure _ _ _
  exact (isQueryBoundP_map_iff _ _ _).2 (hash_setupQuiet _ id)

theorem eval_setupQuiet (keys : Keys C) (i : C.Party) (J : C.Quorum) (x : Point) (message : Message) :
    IsQueryBoundP (eval keys i J x message) RoUnsafe 0 := by
  unfold eval
  refine zero_bind RoUnsafe (zero_mapM _ _ _ fun _ => ?_) fun _ _ => ?_
  · exact (isQueryBoundP_map_iff _ _ _).2 (hash_setupQuiet _ id)
  exact zero_bind RoUnsafe (zero_mapM _ _ _ fun _ =>
    (isQueryBoundP_map_iff _ _ _).2 (hash_setupQuiet _ id)) fun _ _ => isQueryBoundP_pure _ _ _

section Signing

variable {ι : Type} {spec : OracleSpec ι} (P : ι → Prop)
variable (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → OracleComp spec α)
variable (hlift : ∀ {α : Type} (p : OracleComp (RoSpec C) α),
  IsQueryBoundP p RoUnsafe 0 → IsQueryBoundP (lift p) P 0)

include hlift

theorem signRound2With_setupQuiet (part : Point → OracleComp spec Digest)
    (hp : ∀ x, IsQueryBoundP (part x) P 0) (parameter : PublicParameter) (J : C.Quorum)
    (commitment : Digest) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    IsQueryBoundP (signRound2With lift part parameter J commitment e message parts) P 0 := by
  unfold signRound2With
  apply zero_bind P (hlift _ (tweakable_setupQuiet _))
  rintro (_ | ⟨randomness, encoding⟩) _
  · exact isQueryBoundP_pure _ _ _
  apply zero_bind P (zero_sequenceFin _ _ fun l => ?_) fun _ _ => isQueryBoundP_pure _ _ _
  split
  · exact (isQueryBoundP_map_iff _ _ _).2 (hp _)
  · exact isQueryBoundP_pure _ _ _

theorem referenceJob_setupQuiet (value : Point → OracleComp spec Digest)
    (hv : ∀ x, IsQueryBoundP (value x) P 0) (parameter : PublicParameter) (job : Job) :
    IsQueryBoundP (referenceJob (fun p => lift (tweakable p)) value parameter job) P 0 := by
  unfold referenceJob
  apply zero_bind P (zero_mapM _ _ _ hv)
  intro values _
  cases job.kind with
  | chainEnd key l => exact (isQueryBoundP_map_iff _ _ _).2 (hlift _ (tweakable_setupQuiet _))
  | chainRow key l =>
    exact zero_bind P (hlift _ (tweakable_setupQuiet _)) fun _ _ =>
      zero_bind P (hlift _ (tweakable_setupQuiet _)) fun _ _ =>
        zero_bind P (hlift _ (tweakable_setupQuiet _)) fun _ _ => isQueryBoundP_pure _ _ _
  | chainValue key l p => exact (isQueryBoundP_map_iff _ _ _).2 (hlift _ (tweakable_setupQuiet _))
  | commitment key => exact (isQueryBoundP_map_iff _ _ _).2 (hlift _ (tweakable_setupQuiet _))
  | randomizer => exact isQueryBoundP_pure _ _ _

theorem referenceTree_setupQuiet (value : Point → OracleComp spec Digest)
    (hv : ∀ x, IsQueryBoundP (value x) P 0) (parameter : PublicParameter) (top : TopTree) (tree : Tree) :
    IsQueryBoundP (referenceTree (fun p => lift (tweakable p)) value parameter top tree) P 0 :=
  ceremonyOutput_quiet P _ (fun p => hlift _ (tweakable_setupQuiet p)) _
    (fun _js => (isQueryBoundP_map_iff _ _ _).2
      (zero_mapM _ _ _ fun job => referenceJob_setupQuiet P lift hlift value hv parameter job))
    parameter top tree

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
theorem dealtWith_setupQuiet (parameter : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (value : Point → OracleComp spec Digest) (hv : ∀ x, IsQueryBoundP (value x) P 0) :
    DealtQuiet P (dealtWith lift parameter keys top value) := by
  refine ⟨hv, fun i J x message => hlift _ (eval_setupQuiet _ _ _ _ _), fun b => ?_⟩
  change IsQueryBoundP (_ <$> referenceTree (fun p => lift (tweakable p)) value parameter top (.bottom b)) P 0
  with_reducible exact ((isQueryBoundP_map_iff _ _ _).2
    (referenceTree_setupQuiet P lift hlift value hv parameter top (.bottom b)))

theorem honestSignature_setupQuiet (dealt : Dealt C (OracleComp spec)) (hd : DealtQuiet P dealt)
    (e : KeyIndex) (message : Message) : IsQueryBoundP (honestSignature lift dealt e message) P 0 := by
  unfold honestSignature
  apply zero_bind P (hd.bottom _)
  rintro (_ | tree) _
  · exact isQueryBoundP_pure _ _ _
  apply zero_bind P (hd.value _)
  intro rho _
  apply zero_bind P (hlift _ (tweakable_setupQuiet _))
  rintro (_ | ⟨randomness, encoding⟩) _
  · exact isQueryBoundP_pure _ _ _
  refine zero_bind P (zero_sequenceFin _ _ fun l => ?_) (fun values _ => ?_)
  · split
    · exact hd.value _
    · exact isQueryBoundP_pure _ _ _
    · exact zero_bind P (hd.value _) fun _ _ => isQueryBoundP_pure _ _ _
  · exact zero_bind P (hlift _ (tweakable_setupQuiet _)) fun _ _ => isQueryBoundP_pure _ _ _

theorem forgeryWins_setupQuiet (dealt : Dealt C (OracleComp spec)) (hd : DealtQuiet P dealt)
    (st : TsigState C) (forgery : Forgery) : IsQueryBoundP (forgeryWins lift dealt st forgery) P 0 := by
  unfold forgeryWins
  apply zero_bind P (hlift _ (tweakable_setupQuiet _))
  intro verified _
  split
  · exact isQueryBoundP_pure _ _ _
  · exact zero_bind P (honestSignature_setupQuiet P lift hlift dealt hd _ _) fun _ _ =>
      isQueryBoundP_pure _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- One signing oracle step asks no `P` query, when the dealt values and `lift` ask none. -/
theorem tsig_setupQuiet (dealt : Dealt C (OracleComp spec)) (hd : DealtQuiet P dealt)
    (q : (TsigSpec C).Domain) (st : TsigState C) :
    IsQueryBoundP ((tsigOracles lift dealt q).run st) P 0 := by
  cases q with
  | corrupt i =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact isQueryBoundP_pure _ _ _
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure]
      exact isQueryBoundP_pure _ _ _
  | tree b =>
    simp only [tsigOracles, StateT.run_bind]
    apply zero_bind P (bottomOnce_quiet P dealt hd _ st)
    rintro ⟨_ | tree, st'⟩ _
    · exact isQueryBoundP_pure _ _ _
    · simp only [StateT.run_bind, run_liftM, bind_map_left, StateT.run_pure]
      exact zero_bind P (hd.value _) fun _ _ => isQueryBoundP_pure _ _ _
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact isQueryBoundP_pure _ _ _
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_map, run_liftM, Functor.map_map]
      exact (isQueryBoundP_map_iff _ _ _).2 (hd.part _ _ _ _)
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact isQueryBoundP_pure _ _ _
    · apply zero_bind P (bottomOnce_quiet P dealt hd _ st)
      rintro ⟨_ | tree, st'⟩ _
      · exact isQueryBoundP_pure _ _ _
      · change IsQueryBoundP (StateT.run _ st') P 0
        simp only [StateT.run_bind, run_liftM, bind_map_left]
        apply zero_bind P (hd.part _ _ _ _)
        intro own _
        apply zero_bind P (signRound2With_setupQuiet P lift hlift _ (hd.part i J · message) _ _ _ _ _ _)
        rintro (_ | values) _
        · exact isQueryBoundP_pure _ _ _
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact isQueryBoundP_pure _ _ _

end Signing

section Quiet

variable (P : (WorldSpec C).Domain → Prop)
variable (hro : ∀ {α : Type} (p : OracleComp (RoSpec C) α),
  IsQueryBoundP p RoUnsafe 0 → IsQueryBoundP (roW p) P 0)

omit [Field E] [Algebra Bit E] in
theorem roW_quiet {α : Type} (p : OracleComp (RoSpec C) α) (hp : IsQueryBoundP p RoUnsafe 0)
    (hq : ∀ t, ¬ RoUnsafe t → ¬ P (.inr (.inr t))) : IsQueryBoundP (roW p) P 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have ht : ¬ RoUnsafe t := hp.1.resolve_right (by omega)
    simp only [roW, worldRoles, liftComp_bind, free_bind]
    erw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (hq t ht), fun u => ?_⟩
    change IsQueryBoundP (roW (k u)) P (if P (.inr (.inr t)) then 0 - 1 else 0)
    simpa only [if_neg (hq t ht)] using ih u (by simpa [ht] using hp.2 u)

include hro in
theorem valueW_quiet (keys : C.Party → Keys C) (x : Point) :
    IsQueryBoundP (valueW D keys x) P 0 := hro _ (prfValue_setupQuiet _ _)

include hro in
theorem signAs_quietW (keys : C.Party → Keys C) (i : C.Party) (q : TsigQuery C)
    (st : LifetimeState C E) :
    IsQueryBoundP (LifetimeProof.signAs worldRoles keys (valueW D keys) i q st) P 0 := by
  unfold LifetimeProof.signAs
  exact zero_bind P (tsig_setupQuiet P roW hro _
    ⟨fun x => valueW_quiet D P hro keys x, fun _ _ _ _ => hro _ (eval_setupQuiet _ _ _ _ _),
      fun _ => isQueryBoundP_pure _ _ _⟩ q st.sign) fun _ _ => isQueryBoundP_pure _ _ _

include hro in
theorem finishW_quiet (keys : C.Party → Keys C) (h : C.Party) (r : Forgery × LifetimeState C E) :
    IsQueryBoundP (finishW D keys h r) P 0 := by
  unfold finishW
  split
  · exact isQueryBoundP_pure _ _ _
  · split
    · exact forgeryWins_setupQuiet P roW hro _
        (dealtWith_setupQuiet P roW hro _ _ _ _ (valueW_quiet D P hro keys)) _ _
    · exact isQueryBoundP_pure _ _ _

include hro in
theorem request_quietW (keys : C.Party → Keys C) (h : C.Party) (q : LifetimeQuery C E)
    (st : LifetimeState C E)
    (hs : ∀ tree, q = .start tree → LifetimeProof.canStart attempts D st tree →
      IsQueryBoundP (startSteps (tailRoles n st.runCount) D fun i =>
        (ceremony K circuits settings i (keys i) ((st.top i).getD emptyTop) tree :
          PartyM C E RealSpec TreeOutput)) P 0)
    (hr : ∀ sent tree fuel steps, q = .round sent → st.running = some (tree, fuel, steps) →
      IsQueryBoundP (stepRound (tailRoles n (st.runCount - 1)) D
        (roundAdversary (I := PEmpty) sent) noFunctionality () steps) P 0) :
    IsQueryBoundP ((lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles
      D keys (valueW D keys) h q).run st) P 0 := by
  cases q with
  | sign q =>
    cases q with
    | corrupt i => exact isQueryBoundP_pure _ _ _
    | tree b => exact signAs_quietW D P hro keys h (.tree b) st
    | round1 i J e message =>
      rw [LifetimeProof.run_round1]
      split
      · exact isQueryBoundP_pure _ _ _
      · exact signAs_quietW D P hro keys i (.round1 i J e message) _
    | round2 i J e message parts =>
      rw [LifetimeProof.run_round2]
      split
      · exact isQueryBoundP_pure _ _ _
      · exact signAs_quietW D P hro keys i (.round2 i J e message parts) _
  | publicKey => exact isQueryBoundP_pure _ _ _
  | start tree =>
    rw [LifetimeProof.run_start]
    split
    · exact isQueryBoundP_pure _ _ _
    · rename_i hc
      exact zero_bind P (hs tree rfl (not_not.mp hc)) fun _ _ => isQueryBoundP_pure _ _ _
  | round sent =>
    rw [LifetimeProof.run_round]
    cases hh : st.running with
    | none => exact isQueryBoundP_pure _ _ _
    | some x =>
      obtain ⟨tree, fuel, steps⟩ := x
      exact zero_bind P (hr sent tree fuel steps rfl hh) fun _ _ => isQueryBoundP_pure _ _ _

/-- The real-role execution walk of `LifetimeRunBoundary`, on the two world copies. -/
def RolesQuietW (Ro : Roles C (OracleComp (WorldSpec C))) : Prop :=
  ∀ {α : Type} (p : OracleComp (LocalSpec C) α),
    IsQueryBoundP (Ro.adversary p) P 0 ∧ IsQueryBoundP (Ro.honest p) P 0

theorem startSteps_quietW (Ro : Roles C (OracleComp (WorldSpec C))) (hR : RolesQuietW P Ro)
    {α : Type} (program : C.Party → PartyM C E RealSpec α) :
    IsQueryBoundP (startSteps Ro D program) P 0 := by
  apply isQueryBoundP_sequenceFin
  intro i
  split
  · exact isQueryBoundP_pure _ _ _
  · exact (hR _).2

theorem stepRound_quietW (Ro : Roles C (OracleComp (WorldSpec C))) (hR : RolesQuietW P Ro)
    {α I : Type} (A : Adversary C E I PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    IsQueryBoundP (stepRound Ro D A noFunctionality state steps) P 0 := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real])]
  refine zero_bind P (hR _).1 fun r _ => zero_bind P (zero_sequenceFin _ _ fun j => ?_)
    fun _ _ => isQueryBoundP_pure _ _ _
  cases steps j with
  | done out => exact isQueryBoundP_pure _ _ _
  | wait out resume =>
    dsimp only
    split
    · exact isQueryBoundP_pure _ _ _
    · exact (hR _).2
  | call input _ => exact input.elim

end Quiet

set_option maxRecDepth 4000 in
theorem lifeDriver_noProgram (seed : σ → Option (TailSeed C E)) (s : σ)
    (steps : C.Party → Step C E RealSpec TreeOutput) :
    IsQueryBoundP ((lifeDriver K circuits settings attempts D n seed).run s steps) AimedProgramCall 0 := by
  have hro : ∀ {α : Type} (p : OracleComp (RoSpec C) α),
      IsQueryBoundP p RoUnsafe 0 → IsQueryBoundP (roW p) AimedProgramCall 0 :=
    fun p _ => aimed_noProgram_free _
  have hroles (r) : RolesQuietW (C := C) AimedProgramCall (tailRoles n r) := by
    intro α p
    unfold tailRoles
    split
    · exact ⟨aimed_noProgram_adversary _, aimed_noProgram_free _⟩
    · exact ⟨aimed_noProgram_adversary _, aimed_noProgram_adversary _⟩
  have hstep (keys : C.Party → Keys C) (h : C.Party)
      (q : (LocalSpec C + LifetimeSpec C E).Domain) (st : LifetimeState C E) :
      IsQueryBoundP ((oraclesW K circuits settings attempts D n keys h q).run st) AimedProgramCall 0 := by
    rcases q with t | q
    · exact zero_bind _ (aimed_noProgram_adversary _) fun _ _ => isQueryBoundP_pure _ _ _
    · exact request_quietW K circuits settings attempts D n _ hro keys h q st
        (fun tree _ _ => startSteps_quietW D _ _ (hroles _) _)
        (fun sent tree fuel steps _ _ => stepRound_quietW D _ _ (hroles _) _ _ _)
  simp only [lifeDriver]
  cases seed s with
  | none => exact isQueryBoundP_pure _ _ _
  | some t =>
    dsimp only
    by_cases hc : CountIs (n + 1) t.state
    · rw [if_pos hc]
      exact zero_bind _ (LifetimeIdealBad.simulate_run_quiet _ _ (hstep t.keys t.h) _ _)
        fun r _ => finishW_quiet D _ hro t.keys t.h r
    · rw [if_neg hc]
      exact isQueryBoundP_pure _ _ _

theorem nonstart_runningW (keys : C.Party → Keys C) (h : C.Party) (q : LifetimeQuery C E)
    (hq : ∀ tree, q ≠ .start tree) (hr : ∀ sent, q ≠ .round sent) (st : LifetimeState C E)
    (r : _ × LifetimeState C E)
    (hmem : r ∈ support ((lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles D keys
      (valueW D keys) h q).run st)) : r.2.running = st.running := by
  cases q with
  | sign q =>
    cases q with
    | corrupt i =>
      have heq : r = (none, st) := hmem
      rw [heq]
    | tree b =>
      rw [LifetimeProof.run_sign_tree] at hmem
      exact (LifetimeProof.signAs_frame worldRoles keys (valueW D keys) h (.tree b) st r hmem).2
    | round1 i J e message =>
      rw [LifetimeProof.run_round1] at hmem
      split at hmem
      · have heq : r = (none, st) := hmem
        rw [heq]
      · exact (LifetimeProof.signAs_frame worldRoles keys (valueW D keys) i (.round1 i J e message) _ r hmem).2
    | round2 i J e message parts =>
      rw [LifetimeProof.run_round2] at hmem
      split at hmem
      · have heq : r = (none, st) := hmem
        rw [heq]
      · exact (LifetimeProof.signAs_frame worldRoles keys (valueW D keys) i (.round2 i J e message parts) _ r
          hmem).2
  | publicKey =>
    have heq : r = (st.publicKey (keys h).parameter h, st) := hmem
    rw [heq]
  | start tree => exact absurd rfl (hq tree)
  | round sent => exact absurd rfl (hr sent)

/-- The selected run retains its allowed continuations until it ends. -/
def AllowedState (rows : RevealRows C) (st : LifetimeState C E) : Prop :=
  n + 1 ≤ st.runCount ∧ ∀ tree fuel steps, st.running = some (tree, fuel, steps) →
    st.runCount = n + 1 → ∀ i, AimedSetupDomain.StepOk rows (steps i)

omit [Field E] [Algebra Bit E] in
theorem roW_allowed (rows : RevealRows C) {α : Type} (p : OracleComp (RoSpec C) α)
    (hp : IsQueryBoundP p RoUnsafe 0) :
    IsQueryBoundP (roW p) (AimedSetupDomain.Unallowed rows) 0 := by
  refine roW_quiet _ p hp fun t ht => ?_
  cases t with
  | inl q => exact not_not.mpr ht
  | inr x => exact False.elim (ht trivial)

set_option maxRecDepth 4000 in
theorem oraclesW_allowed (rows : RevealRows C) (keys : C.Party → Keys C) (h : C.Party)
    (t : (LocalSpec C + LifetimeSpec C E).Domain) (st : LifetimeState C E)
    (hs : AllowedState n rows st) :
    IsQueryBoundP ((oraclesW K circuits settings attempts D n keys h t).run st)
      (AimedSetupDomain.Unallowed rows) 0 ∧
    ∀ r ∈ support ((oraclesW K circuits settings attempts D n keys h t).run st), AllowedState n rows r.2 := by
  have hlater (r) (hr : n < r) : RolesQuietW (AimedSetupDomain.Unallowed rows) (tailRoles n r) := by
    simp only [tailRoles, if_neg (by omega : r ≠ n)]
    exact fun p => ⟨AimedSetupDomain.qb0_adversary_unallowed _ _,
      AimedSetupDomain.qb0_adversary_unallowed _ _⟩
  rcases t with t | q
  · constructor
    · exact zero_bind _ (AimedSetupDomain.qb0_adversary_unallowed _ _) fun _ _ => isQueryBoundP_pure _ _ _
    · intro r hr
      change r ∈ support (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun a => pure (a, st)) at hr
      obtain ⟨a, _, he⟩ := (mem_support_bind_iff _ _ _).mp hr
      have he' : r = (a, st) := he
      rw [he']
      exact hs
  · change IsQueryBoundP ((lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles
      D keys (valueW D keys) h q).run st) _ 0 ∧
      ∀ r ∈ support ((lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles
        D keys (valueW D keys) h q).run st), AllowedState n rows r.2
    have hc (r) (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts (tailRoles n)
        worldRoles D keys (valueW D keys) h q).run st)) :=
      LifetimeProof.lifetimeOracles_runCount K circuits settings attempts (tailRoles n) worldRoles
        D keys (valueW D keys) h q st r hr
    cases q with
    | start tree =>
      refine ⟨request_quietW K circuits settings attempts D n _ (roW_allowed rows) keys h _ st
        (fun tree _ _ => startSteps_quietW D _ _ (hlater _ (by have := hs.1; omega)) _)
        (fun _ _ _ _ he _ => by cases he), fun r hr => ?_⟩
      have hc' := hc r hr
      rw [LifetimeProof.run_start] at hr
      split at hr
      · have he : r = (none, st) := hr
        rw [he]; exact hs
      · obtain ⟨steps, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
        have he : r = (some (toCoalition D steps),
            ({ LifetimeProof.increment st tree with running := some (tree, ceremonyFuel circuits settings, steps) }).settle D) := hr
        have hc'' : r.2.runCount = st.runCount + 1 := by
          simpa only [he, LifetimeProof.newRun, Option.map_some, Option.toList_some, List.length_singleton] using hc'
        have hn := hs.1
        exact ⟨by omega, fun _ _ _ _ hec => by omega⟩
    | round sent =>
      rw [LifetimeProof.run_round]
      cases hrun : st.running with
      | none =>
        refine ⟨isQueryBoundP_pure _ _ _, fun r hr => ?_⟩
        have he : r = (none, st) := hr
        rw [he]; exact hs
      | some x =>
        obtain ⟨tree, fuel, steps⟩ := x
        dsimp only
        by_cases hcount : st.runCount = n + 1
        · have hr : st.runCount - 1 = n := by omega
          rw [hr]
          simp only [tailRoles, if_true]
          have hok := AimedSetupDomain.stepRound_ok rows D (roundAdversary (I := Keys C) sent) ()
            steps (hs.2 tree fuel steps hrun hcount)
          change IsQueryBoundP (stepRound worldRoles D (roundAdversary (I := PEmpty) sent)
            noFunctionality () steps) _ 0 ∧ _ at hok
          refine ⟨zero_bind _ hok.1 fun _ _ => isQueryBoundP_pure _ _ _, fun r hr => ?_⟩
          obtain ⟨y, hy, he⟩ := (mem_support_bind_iff _ _ _).mp hr
          have he' : r = (some (toCoalition D y.2.1),
            ({ st with running := some (tree, fuel - 1, y.2.1) }).settle D) := he
          rw [he']
          refine ⟨by rw [runCount_round]; exact hs.1, fun tree' fuel' steps' hrun' _ => ?_⟩
          have he := LifetimeProof.settle_running D _ (by rw [hrun']; simp)
          rw [hrun'] at he
          simp only [Option.some.injEq, Prod.mk.injEq] at he
          rw [he.2.2]
          exact hok.2 y hy
        · have hlt : n < st.runCount - 1 := by have := hs.1; omega
          refine ⟨zero_bind _ (stepRound_quietW D _ _ (hlater _ hlt) _ _ _) fun _ _ =>
            isQueryBoundP_pure _ _ _, fun r hr => ?_⟩
          obtain ⟨y, _, he⟩ := (mem_support_bind_iff _ _ _).mp hr
          have he' : r = (some (toCoalition D y.2.1),
            ({ st with running := some (tree, fuel - 1, y.2.1) }).settle D) := he
          rw [he']
          refine ⟨by rw [runCount_round]; exact hs.1, fun _ _ _ _ hec => ?_⟩
          exact False.elim (hcount (by simpa only [runCount_round] using hec))
    | sign q | publicKey =>
      all_goals
        refine ⟨request_quietW K circuits settings attempts D n _ (roW_allowed rows) keys h _ st
          (fun _ he _ => by cases he) (fun _ _ _ _ he _ => by cases he), fun r hr => ?_⟩
        have hc' : r.2.runCount = st.runCount := by simpa [LifetimeProof.newRun] using hc r hr
        refine ⟨by rw [hc']; exact hs.1, fun tree fuel steps hrun hcount => ?_⟩
        have hrunning := nonstart_runningW K circuits settings attempts D n keys h _
          (fun _ => by simp) (fun _ => by simp) st r hr
        exact hs.2 tree fuel steps (hrunning.symm.trans hrun) (hc'.symm.trans hcount)

theorem lifeDriver_allowed (seed : σ → Option (TailSeed C E)) (rows : RevealRows C) (s : σ)
    (steps : C.Party → Step C E RealSpec TreeOutput) (hs : ∀ i, AimedSetupDomain.StepOk rows (steps i)) :
    IsQueryBoundP ((lifeDriver K circuits settings attempts D n seed).run s steps)
      (AimedSetupDomain.Unallowed rows) 0 := by
  simp only [lifeDriver]
  cases seed s with
  | none => exact isQueryBoundP_pure _ _ _
  | some t =>
    dsimp only
    by_cases hc : CountIs (n + 1) t.state
    · rw [if_pos hc]
      refine zero_bind _ (simulate_quietP _ (AllowedState n rows)
        (oraclesW_allowed K circuits settings attempts D n rows t.keys t.h) _ _ ?_)
        fun r _ => finishW_quiet D _ (roW_allowed rows) t.keys t.h r
      refine ⟨by rw [runCount_round]; exact Nat.le_of_eq hc.symm, fun tree fuel next hr _ => ?_⟩
      have he := LifetimeProof.settle_running D _ (by rw [hr]; simp)
      rw [hr] at he
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      rw [he.2.2]
      exact hs
    · rw [if_neg hc]
      exact isQueryBoundP_pure _ _ _

section Rename

variable (a b : HashOutput)

/-- Only the selected ceremony's suspended programs are renamed. -/
def renameState (st : LifetimeState C E) : LifetimeState C E :=
  if CountIs (n + 1) st then
    { st with running := st.running.map fun r =>
      (r.1, r.2.1, fun i => renameStep D a b (r.2.2 i)) }
  else st

omit [Field E] [Algebra Bit E] in
theorem renameState_count (st : LifetimeState C E) :
    (renameState D n a b st).runCount = st.runCount := by
  unfold renameState
  split <;> rfl

omit [Field E] [Algebra Bit E] in
theorem renameState_none (st : LifetimeState C E) (hr : st.running = none) :
    renameState D n a b st = st := by
  unfold renameState
  split
  · simp only [hr, Option.map_none]
    cases st
    simp_all
  · rfl

omit [Field E] [Algebra Bit E] in
theorem renameState_later (st : LifetimeState C E) (hc : st.runCount ≠ n + 1) :
    renameState D n a b st = st := if_neg hc

omit [Field E] [Algebra Bit E] in
theorem renameState_replace (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (steps : C.Party → Step C E RealSpec TreeOutput) (hr : st.running = some (tree, fuel, steps))
    (hc : st.runCount = n + 1) :
    renameState D n a b st = replaceSteps (fun i => renameStep D a b (steps i)) st := by
  simp only [renameState, if_pos (show CountIs (n + 1) st from hc), replaceSteps, hr, Option.map_some]

omit [Field E] [Algebra Bit E] in
theorem renameState_settle (st : LifetimeState C E) :
    renameState D n a b (st.settle D) = (renameState D n a b st).settle D := by
  by_cases hc : CountIs (n + 1) st
  · have hc' : CountIs (n + 1) (st.settle D) := by
      change (st.settle D).runCount = n + 1
      rw [LifetimeProof.settle_runCount]; exact hc
    simp only [renameState, if_pos hc, if_pos hc']
    cases hr : st.running with
    | none => simp [LifetimeState.settle, hr]
    | some r =>
      obtain ⟨tree, fuel, steps⟩ := r
      simp only [LifetimeState.settle, hr, Option.map_some, renameStep_isDone, renameStep_output]
      split
      · cases tree <;> rfl
      · simp only [hr, Option.map_some]
  · have hc' : ¬ CountIs (n + 1) (st.settle D) := by
      change (st.settle D).runCount ≠ n + 1
      rwa [LifetimeProof.settle_runCount]
    simp only [renameState, if_neg hc, if_neg hc']

omit [Field E] [Algebra Bit E] in
theorem finishW_renameState (keys : C.Party → Keys C) (h : C.Party)
    (f : Forgery) (st : LifetimeState C E) :
    finishW D keys h (f, renameState D n a b st) = finishW D keys h (f, st) := by
  unfold renameState
  split <;> rfl

/-- The free stream queries, the only queries changed by the world renaming. -/
def FreeStreamW : (WorldSpec C).Domain → Prop
  | .inr (.inr (.inr _)) => True
  | _ => False

omit [Field E] [Algebra Bit E] in
theorem rename_quiet {α : Type} (p : OracleComp (WorldSpec C) α)
    (hp : IsQueryBoundP p FreeStreamW 0) : simulateQ (worldStreamRename D a b) p = p := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have ht : ¬ FreeStreamW t := hp.1.resolve_right (by omega)
    simp only [simulateQ_bind, simulateQ_spec_query]
    have he : worldStreamRename D a b t = OracleComp.lift (OracleSpec.query t) := by
      rcases t with ((u | q | x) | p) | (u | q | x)
      all_goals try rfl
      exact False.elim (ht trivial)
    rw [he]
    exact bind_congr fun u => ih u (by simpa only [if_neg ht] using hp.2 u)

omit [Field E] [Algebra Bit E] in
theorem roW_streamQuiet {α : Type} (p : OracleComp (RoSpec C) α)
    (hp : IsQueryBoundP p RoUnsafe 0) : IsQueryBoundP (roW p) FreeStreamW 0 := by
  refine roW_quiet _ p hp fun t ht => ?_
  cases t with
  | inl q => exact id
  | inr x => exact False.elim (ht trivial)

omit [Field E] [Algebra Bit E] in
theorem adv_streamQuiet {α : Type} (p : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (worldRoles.adversary p) FreeStreamW 0 :=
by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [worldRoles, counted, liftComp_pure]; exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, adversary_query]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl not_false, fun u => by simpa only [Nat.zero_sub, ite_self] using ih u⟩



omit [Field E] [Algebra Bit E] in
theorem roles_later_streamQuiet (r : ℕ) (hr : n < r) : RolesQuietW (C := C) FreeStreamW (tailRoles n r) := by
  simp only [tailRoles, if_neg (by omega : r ≠ n)]
  exact fun p => ⟨adv_streamQuiet _, adv_streamQuiet _⟩

/-- Every request preserves or increments the chronological index. -/
theorem oraclesW_count_mono (keys : C.Party → Keys C) (h : C.Party)
    (q : (LocalSpec C + LifetimeSpec C E).Domain) (st : LifetimeState C E)
    (r : _ × LifetimeState C E)
    (hr : r ∈ support ((oraclesW K circuits settings attempts D n keys h q).run st)) :
    st.runCount ≤ r.2.runCount := by
  rcases q with t | q
  · change r ∈ support (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun a => pure (a, st)) at hr
    obtain ⟨a, _, he⟩ := (mem_support_bind_iff _ _ _).mp hr
    have he' : r = (a, st) := he
    rw [he']
  · have hc := LifetimeProof.lifetimeOracles_runCount K circuits settings attempts (tailRoles n) worldRoles
      D keys (valueW D keys) h q st r hr
    omega

omit [Field E] [Algebra Bit E] in
theorem map_renameState_eq {α : Type} (p : OracleComp (WorldSpec C) (α × LifetimeState C E))
    (hp : ∀ r ∈ support p, renameState D n a b r.2 = r.2) :
    (fun r => (r.1, renameState D n a b r.2)) <$> p = p := by
  rw [map_eq_bind_pure_comp]
  conv_rhs => rw [← bind_pure p]
  exact OracleComp.bind_congr_of_forall_mem_support _ fun r hr => by simp [hp r hr]

omit [Field E] [Algebra Bit E] in
theorem renameState_update (st : LifetimeState C E) (hc : st.runCount = n + 1)
    (tree : ThresholdLeanXmss.Tree) (fuel : ℕ) (steps : C.Party → Step C E RealSpec TreeOutput) :
    renameState D n a b { st with running := some (tree, fuel, steps) } =
      { renameState D n a b st with running := some (tree, fuel, fun i => renameStep D a b (steps i)) } := by
  have hc0 : st.topRuns + ∑ b, st.bottomRuns b = n + 1 := hc
  simp only [renameState, CountIs, LifetimeState.runCount, hc0, if_true, Option.map_some]

/-- A non-round signing or public-key request commutes with renaming the saved steps. -/
theorem nonstart_rename (keys : C.Party → Keys C) (h : C.Party)
    (q : LifetimeQuery C E) (hq : ∀ tree, q ≠ .start tree) (hrq : ∀ sent, q ≠ .round sent)
    (st : LifetimeState C E) (hc : st.runCount = n + 1) :
    (lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles D keys (valueW D keys) h q).run
      (renameState D n a b st) =
    (fun r => (r.1, renameState D n a b r.2)) <$>
      simulateQ (worldStreamRename D a b)
        ((lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles
          D keys (valueW D keys) h q).run st) := by
  have hquiet := request_quietW K circuits settings attempts D n FreeStreamW roW_streamQuiet keys h q st
    (fun _ he _ => False.elim (hq _ he)) (fun _ _ _ _ he _ => False.elim (hrq _ he))
  rw [rename_quiet D a b _ hquiet]
  have hcount (r) (hr : r ∈ support ((lifetimeOraclesWith K circuits settings attempts (tailRoles n)
      worldRoles D keys (valueW D keys) h q).run st)) : r.2.runCount = n + 1 := by
    have hh := LifetimeProof.lifetimeOracles_runCount K circuits settings attempts (tailRoles n) worldRoles
      D keys (valueW D keys) h q st r hr
    cases q <;> simp_all [LifetimeProof.newRun]
  cases hs : st.running with
  | none =>
    rw [renameState_none D n a b st hs]
    symm
    apply map_renameState_eq
    intro r hr
    exact renameState_none D n a b r.2
      ((nonstart_runningW K circuits settings attempts D n keys h q hq hrq st r hr).trans hs)
  | some r =>
    obtain ⟨tree, fuel, steps⟩ := r
    rw [renameState_replace D n a b st tree fuel steps hs hc]
    rw [request_replaceSteps worldRoles keys (valueW D keys) K circuits settings attempts (tailRoles n)
      D h _ st (by rw [hs]; simp) q hrq]
    simp only [map_eq_bind_pure_comp]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro r hr
    simp only [Function.comp_def]
    rw [renameState_replace D n a b r.2 tree fuel steps
      ((nonstart_runningW K circuits settings attempts D n keys h q hq hrq st r hr).trans hs) (hcount r hr)]

/-- A selected round transports the entire next step family and its final visible outbox. -/
theorem round_rename (keys : C.Party → Keys C) (h : C.Party) (sent : Sent C E)
    (st : LifetimeState C E) (hc : st.runCount = n + 1) :
    (lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles D keys (valueW D keys) h
      (.round sent)).run (renameState D n a b st) =
    (fun r => (r.1, renameState D n a b r.2)) <$>
      simulateQ (worldStreamRename D a b)
        ((lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles
          D keys (valueW D keys) h (.round sent)).run st) := by
  cases hs : st.running with
  | none =>
    rw [renameState_none D n a b st hs, LifetimeProof.run_round]
    simp only [hs, simulateQ_pure, map_pure, renameState_none D n a b st hs]
  | some r =>
    obtain ⟨tree, fuel, steps⟩ := r
    have hc0 : st.topRuns + ∑ b, st.bottomRuns b = n + 1 := hc
    have hn := renameState_replace D n a b st tree fuel steps hs hc
    rw [hn, LifetimeProof.run_round, LifetimeProof.run_round]
    simp only [replaceSteps, hs, Option.map_some, LifetimeState.runCount, hc0,
      Nat.add_sub_cancel, tailRoles, if_true, simulateQ_bind, simulateQ_pure, map_bind, map_pure]
    have he := stepRound_rename D a b (roundAdversary (I := Keys C) sent) () steps
    change stepRound worldRoles D (roundAdversary (I := PEmpty) sent) noFunctionality ()
        (fun i => renameStep D a b (steps i)) = _ at he
    rw [he, bind_map_left]
    apply bind_congr
    intro r
    have vis : toCoalition D (fun i => renameStep D a b (r.2.1 i)) = toCoalition D r.2.1 := by
      funext c i
      simp only [toCoalition, renameStep_outbox]
    simp only [vis]
    rw [renameState_settle, renameState_update D n a b st hc]
    rw [hn]
    rfl

/-- Starts after the selected reveal use the counted copy. -/
theorem start_rename (keys : C.Party → Keys C) (h : C.Party) (tree : ThresholdLeanXmss.Tree)
    (st : LifetimeState C E) (hc : st.runCount = n + 1) :
    (lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles D keys (valueW D keys) h
      (.start tree)).run (renameState D n a b st) =
    (fun r => (r.1, renameState D n a b r.2)) <$>
      simulateQ (worldStreamRename D a b)
        ((lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles
          D keys (valueW D keys) h (.start tree)).run st) := by
  cases hs : st.running with
  | some running =>
    obtain ⟨tree', fuel, steps⟩ := running
    rw [renameState_replace D n a b st tree' fuel steps hs hc]
    have hn : st.running ≠ none := by rw [hs]; simp
    rw [request_replaceSteps worldRoles keys (valueW D keys) K circuits settings attempts (tailRoles n)
      D h _ st hn (.start tree) (fun _ => by simp)]
    rw [LifetimeProof.run_start, if_pos (fun hh => hn hh.1)]
    simp only [simulateQ_pure, map_pure]
    rw [renameState_replace D n a b st tree' fuel steps hs hc]
  | none =>
    rw [renameState_none D n a b st hs]
    have hquiet := request_quietW K circuits settings attempts D n FreeStreamW roW_streamQuiet keys h
      (.start tree) st
      (fun tree _ _ => startSteps_quietW D _ _ (roles_later_streamQuiet n _ (by omega)) _)
      (fun _ _ _ _ he _ => by cases he)
    rw [rename_quiet D a b _ hquiet]
    symm
    apply map_renameState_eq
    intro r hr
    have hcount := LifetimeProof.lifetimeOracles_runCount K circuits settings attempts (tailRoles n) worldRoles
      D keys (valueW D keys) h (.start tree) st r hr
    rw [LifetimeProof.run_start] at hr
    split at hr
    · have he : r = (none, st) := hr
      rw [he]; exact renameState_none D n a b st hs
    · obtain ⟨steps, _, he⟩ := (mem_support_bind_iff _ _ _).mp hr
      have he' : r = (some (toCoalition D steps),
        ({ LifetimeProof.increment st tree with running := some (tree, ceremonyFuel circuits settings, steps) }).settle D) := he
      have hcount' : r.2.runCount = st.runCount + 1 := by
        simpa only [he', LifetimeProof.newRun, Option.map_some, Option.toList_some, List.length_singleton] using hcount
      exact renameState_later D n a b _ (by omega)

/-- The world renaming commutes with each actual lifetime oracle request. -/
theorem oraclesW_rename (keys : C.Party → Keys C) (h : C.Party)
    (q : (LocalSpec C + LifetimeSpec C E).Domain) (st : LifetimeState C E)
    (hc : n + 1 ≤ st.runCount) :
    (oraclesW K circuits settings attempts D n keys h q).run (renameState D n a b st) =
    (fun r => (r.1, renameState D n a b r.2)) <$>
      simulateQ (worldStreamRename D a b) ((oraclesW K circuits settings attempts D n keys h q).run st) := by
  rcases q with t | q
  · have hh : ∀ s : LifetimeState C E,
        (oraclesW K circuits settings attempts D n keys h (.inl t)).run s =
          (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun x => pure (x, s)) :=
        fun _ => rfl
    simp only [hh, simulateQ_bind, worldStreamRename_adversary, simulateQ_pure, map_bind, map_pure]
  · change (lifetimeOraclesWith K circuits settings attempts (tailRoles n) worldRoles D keys
        (valueW D keys) h q).run (renameState D n a b st) =
        (fun r => (r.1, renameState D n a b r.2)) <$>
          simulateQ (worldStreamRename D a b) ((lifetimeOraclesWith K circuits settings attempts
            (tailRoles n) worldRoles D keys (valueW D keys) h q).run st)
    by_cases he : st.runCount = n + 1
    · cases q with
      | start tree => exact start_rename K circuits settings attempts D n a b keys h tree st he
      | round sent => exact round_rename K circuits settings attempts D n a b keys h sent st he
      | sign q =>
        exact nonstart_rename K circuits settings attempts D n a b keys h (.sign q)
          (fun _ => by simp) (fun _ => by simp) st he
      | publicKey =>
        exact nonstart_rename K circuits settings attempts D n a b keys h .publicKey
          (fun _ => by simp) (fun _ => by simp) st he
    · rw [renameState_later D n a b st he]
      have hquiet := request_quietW K circuits settings attempts D n FreeStreamW roW_streamQuiet keys h q st
        (fun tree _ _ => startSteps_quietW D _ _ (roles_later_streamQuiet n _ (by omega)) _)
        (fun _ _ _ _ _ _ => stepRound_quietW D _ _ (roles_later_streamQuiet n _ (by omega)) _ _ _)
      rw [rename_quiet D a b _ hquiet]
      symm
      apply map_renameState_eq
      intro r hr
      have hh := LifetimeProof.lifetimeOracles_runCount K circuits settings attempts (tailRoles n) worldRoles
        D keys (valueW D keys) h q st r hr
      exact renameState_later D n a b _ (by omega)

/-- The state transport lifts over the actual adaptive continuation. -/
theorem continuation_rename (keys : C.Party → Keys C) (h : C.Party) (prog : Program C E)
    (st : LifetimeState C E) (hc : n + 1 ≤ st.runCount) :
    (simulateQ (oraclesW K circuits settings attempts D n keys h) prog).run (renameState D n a b st) >>=
        finishW D keys h =
      simulateQ (worldStreamRename D a b)
        ((simulateQ (oraclesW K circuits settings attempts D n keys h) prog).run st >>= finishW D keys h) := by
  induction prog using OracleComp.inductionOn generalizing st with
  | pure f =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, finishW_renameState]
    exact (rename_quiet D a b _ (finishW_quiet D _ roW_streamQuiet keys h (f, st))).symm
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rw [oraclesW_rename K circuits settings attempts D n a b keys h q st hc]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro r hr
    simpa only [simulateQ_bind] using ih r.1 r.2 (hc.trans (oraclesW_count_mono K circuits settings attempts D n keys h q st r
      (support_simulateQ_subset _ _ hr)))

theorem lifeDriver_rename (seed : σ → Option (TailSeed C E)) (s : σ)
    (steps : C.Party → Step C E RealSpec TreeOutput) :
    simulateQ (worldStreamRename D a b) ((lifeDriver K circuits settings attempts D n seed).run s steps) =
      (lifeDriver K circuits settings attempts D n seed).run s (fun i => renameStep D a b (steps i)) := by
  simp only [lifeDriver]
  cases seed s with
  | none => rfl
  | some t =>
    dsimp only
    by_cases hc : CountIs (n + 1) t.state
    · simp only [if_pos hc]
      have hv : toCoalition D (fun i => renameStep D a b (steps i)) = toCoalition D steps := by
        funext c i
        simp only [toCoalition, renameStep_outbox]
      rw [hv]
      rw [← continuation_rename K circuits settings attempts D n a b t.keys t.h _ _
        (by rw [runCount_round]; exact Nat.le_of_eq hc.symm)]
      rw [renameState_settle, renameState_update D n a b t.state hc]
      have he : { renameState D n a b t.state with running := some (t.tree, ceremonyFuel circuits settings - 2, fun i => renameStep D a b (steps i)) } =
          { t.state with running := some (t.tree, ceremonyFuel circuits settings - 2, fun i => renameStep D a b (steps i)) } := by
        simp only [renameState, if_pos hc]
      rw [he]
    · simp only [if_neg hc, simulateQ_pure]

end Rename

/-- The actual lifetime continuation satisfies every law of the generic tail kernel. -/
theorem lifeDriver_lawful (seed : σ → Option (TailSeed C E)) :
    TailDriver.Lawful D (lifeDriver K circuits settings attempts D n seed) where
  noProgram := lifeDriver_noProgram K circuits settings attempts D n seed
  noProgramStop _ := isQueryBoundP_pure _ _ _
  rename a b := lifeDriver_rename K circuits settings attempts D n a b seed
  renameStop _ _ _ := rfl
  allowed := fun rows s steps hs => lifeDriver_allowed K circuits settings attempts D n seed rows s steps hs
  allowedStop _ _ := isQueryBoundP_pure _ _ _
  alike := lifeDriver_alike K circuits settings attempts D n seed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailDriver.continuation_alike' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms continuation_alike

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailDriver.lifeDriver_noProgram' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lifeDriver_noProgram

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailDriver.lifeDriver_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lifeDriver_allowed

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailDriver.oraclesW_rename' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms oraclesW_rename

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailDriver.lifeDriver_rename' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lifeDriver_rename

/-- info: 'ThresholdLeanXmssSecurity.LifetimeTailDriver.lifeDriver_lawful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lifeDriver_lawful

end ThresholdLeanXmssSecurity.LifetimeTailDriver
