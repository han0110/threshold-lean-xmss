import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Replay

/-!
# The replay of the bottom trees

`givenAnswerGame` is `givenDealerGame` where a request of bottom tree `b` passes the answer of the
dealer to the run of the tree, as `emulatedTreeRequest` does, in the place of `dealerTree`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof ThresholdLeanXmssSecurity.DkgCorrectnessProof.WorldSplit

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]
  (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (D : C.Coalition)

/-- `secRunD` with the answer `answer` of the dealer in the place of `dealerTree`. -/
def secRunC (m : Mode) (net : Adversary C E Unit PEmpty PEmpty) (dealer : Dealt C (RealM C net.State))
    (emu : C.Party → Option (Keys C)) (tree : Tree) (answer : Option (BottomTree × Digest)) :
    RealM C net.State Unit := do
  let s ← get
  if s.runs tree < m.emulated tree then do
    match tree with
    | .top => worldEmulatedRun K circuits settings D net emu (topLeak settings dealer.top) 0 .top
    | .bottom b => do
      match answer with
      | some (bottom, ρ) =>
          worldEmulatedRun K circuits settings D net emu (bottomLeak settings b bottom ρ)
            bottom.topSignature.randomizer (.bottom b)
      | none => pure ()
  else treeRun K circuits settings noMonitor D net tree

/-- `secRunsD` with the answer `answer`. -/
def secRunsC (m : Mode) (net : Adversary C E Unit PEmpty PEmpty) (dealer : Dealt C (RealM C net.State))
    (emu : C.Party → Option (Keys C)) (tree : Tree) (answer : Option (BottomTree × Digest)) :
    ℕ → RealM C net.State Unit
  | 0 => pure ()
  | count + 1 => do
    if mayRun runLimit D (← get) tree then
      secRunC K circuits settings D m net dealer emu tree answer
      secRunsC m net dealer emu tree answer count

/-- `secTreeRequestD` with the answer of the dealer passed to the run. -/
def secTreeRequestC (m : Mode) (net : Adversary C E Unit PEmpty PEmpty) (dealer : Dealt C (RealM C net.State))
    (emu : C.Party → Option (Keys C)) (b : Fin (2 ^ layerHeight)) :
    StateT (TsigState C) (RealM C net.State) (Option (BottomTree × Digest)) := do
  let answer : Option (BottomTree × Digest) ← tsigOracles realLift dealer (.tree b)
  if m.skip = false ∨ answer.isSome then
    StateT.lift (secRunsC K circuits settings runLimit D m net dealer emu (.bottom b) answer 1)
  let s ← StateT.lift get
  match heldBottom D s.operators b, answer with
  | some tree, some (_, ρ) => pure (some (tree, ρ))
  | _, _ => pure none

/-- `secOraclesD` with `secTreeRequestC`. -/
def secOraclesC (m : Mode) (net : Adversary C E Unit PEmpty PEmpty) (dealer : Dealt C (RealM C net.State))
    (emu : C.Party → Option (Keys C)) :
    QueryImpl (TsigSpec C) (StateT (TsigState C) (RealM C net.State)) := fun q =>
  match q with
  | .corrupt i => pure (noAnswer (.corrupt i))
  | .tree b => secTreeRequestC K circuits settings runLimit D m net dealer emu b
  | .round1 i J e message => secSignRequest dealer i e (.round1 i J e message)
  | .round2 i J e message parts => secSignRequest dealer i e (.round2 i J e message parts)

/-- `secSigningD` with `secOraclesC`. -/
def secSigningC (m : Mode) (A : DkgTsigAdversary C E) (dealer : Dealt C (RealM C A.net.State))
    (emu : C.Party → Option (Keys C)) : RealM C A.net.State Bool := do
  let s ← get
  match topHolder D s.operators with
  | none => pure false
  | some _ => do
    let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (RealM C A.net.State)) :=
      fun t => StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
    let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
      match q with
      | .read => StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _))
      | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
    let (forgery, st) ← (simulateQ
      (forger + (secOraclesC K circuits settings runLimit D m A.net dealer emu + cell))
      (A.forge ⟨dealer.top.root, dealer.parameter⟩ dealer.top)).run ⟨D.1, fun _ => none, [], fun _ => none⟩
    forgeryWins realLift dealer st forgery

/-- `secRestD` with `secSigningC`. -/
def secRestC (m : Mode) (A : DkgTsigAdversary C E) (dealer : Dealt C (RealM C A.net.State))
    (emu : C.Party → Option (Keys C)) : RealM C A.net.State Bool := do
  let s ← get
  let (state, ok) ← StateT.lift (voteRound worldRoles D A.net s.adversary fun i =>
    ((s.operators i).keys).map seedVote)
  set (votedStart D s state ok)
  secRunsC K circuits settings runLimit D m A.net dealer (committed ok emu) .top none runLimit
  secSigningC K circuits settings runLimit D m A dealer (committed ok emu)

/-- `givenDealerGame` with the answer of a tree request passed to the run. -/
def givenAnswerGame (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Bool := do
  let r ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
  let output ← dealerTop r.1 r.2.1
  let o ← observe (A.net.start (corruptInputs D fun _ => ()) [])
  let te ← seedGenTail D A.net o.1 o.2 r.1 r.2.2
  (secRestC K circuits settings runLimit D ⟨true, fun _ => runLimit⟩ A (dealerOf r output) te.2).run'
    (startState D te.1 (keysOf r.2.2 te.2))

theorem secRunsD_top (m : Mode) (net : Adversary C E Unit PEmpty PEmpty) (dealer : Dealt C (RealM C net.State))
    (emu : C.Party → Option (Keys C)) : ∀ count,
    secRunsD K circuits settings runLimit D m net dealer emu .top count =
      secRunsC K circuits settings runLimit D m net dealer emu .top none count
  | 0 => rfl
  | count + 1 => by
    simp only [secRunsD, secRunsC, secRunsD_top m net dealer emu count]
    rfl

/-! ## The replay of a computation of `H` on the real state -/

section RealLift

variable (prims : Primitives) {σ : Type}

/-- The value `v` of the computation `X` of `H` is fixed by the cache of `w`. -/
def RoDet {α : Type} (X : OracleComp (RoSpec C) α) (v : α) (w : HashCache C × HiddenCache C) : Prop :=
  ∃ c z, z ∈ support ((simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) X).run c) ∧ z.1 = v ∧
    z.2 ≤ w.1

variable {prims}

theorem RoDet.mono {α : Type} {X : OracleComp (RoSpec C) α} {v : α} {w w' : HashCache C × HiddenCache C}
    (h : RoDet prims X v w) (hle : w.1 ≤ w'.1) : RoDet prims X v w' := by
  obtain ⟨c, z, hz, hv, hc⟩ := h
  exact ⟨c, z, hz, hv, hc.trans hle⟩

theorem realLift_replay (D : C.Coalition) {α : Type} {X : OracleComp (RoSpec C) α}
    (hsafe : AllQueriesSatisfy (free (liftComp X (LocalSpec C))) WorldSafe) {v : α}
    {w : HashCache C × HiddenCache C} (h : RoDet prims X v w) (rs : RealState C σ) :
    (simulateQ (streamWorld prims D) ((realLift X : RealM C σ α).run rs)).run w = pure ((v, rs), w) := by
  obtain ⟨c, z, hz, rfl, hle⟩ := h
  obtain ⟨c', h'⟩ := w
  simp only [realLift, StateT.run_lift, simulateQ_bind, StateT.run_bind]
  rw [streamWorld_safe hsafe, baseAnswer_freeLift,
    replay_simulateQ (grows_roAnswer prims) (replays_roAnswer prims) X c z hz c' hle]
  simp

theorem realLift_support (D : C.Coalition) {α : Type} {X : OracleComp (RoSpec C) α}
    (hsafe : AllQueriesSatisfy (free (liftComp X (LocalSpec C))) WorldSafe) (rs : RealState C σ)
    (w : HashCache C × HiddenCache C) (z : (α × RealState C σ) × (HashCache C × HiddenCache C))
    (hz : z ∈ support ((simulateQ (streamWorld prims D) ((realLift X : RealM C σ α).run rs)).run w)) :
    RoDet prims X z.1.1 z.2 ∧ z.1.2 = rs ∧ w.1 ≤ z.2.1 := by
  obtain ⟨c, h⟩ := w
  simp only [realLift, StateT.run_lift, simulateQ_bind, StateT.run_bind] at hz
  rw [streamWorld_safe hsafe, baseAnswer_freeLift] at hz
  simp only [bind_map_left, simulateQ_pure, StateT.run_pure, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨⟨c, y, hy, rfl, le_rfl⟩, rfl, Grows.simulateQ (grows_roAnswer prims) X c y hy⟩

end RealLift

/-- Bottom tree `b` of the dealer on the parameter and the seeds of `r` and the top tree `top`, as a
computation of `H`. -/
@[irreducible] def bottomRo (r : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C)) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) : OracleComp (RoSpec C) (Option BottomTree) :=
  (fun | some (.bottom tree) => some tree | _ => none) <$>
    referenceTree (fun oa => tweakable oa) (prfValue r.2.1) r.1 top (.bottom b)

theorem dealerOf_bottom {σ : Type} (r : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C))
    (output : Option TreeOutput) (b : Fin (2 ^ layerHeight)) :
    (dealerOf (σ := σ) r output).bottom b = realLift (bottomRo r ((TreeOutput.topTree output).getD emptyTop) b) := by
  unfold dealerOf bottomRo
  simp only [dealtWith]
  have e := SeedHitProof.hom_referenceTree (realLiftHom (C := C) σ) (fun oa => tweakable oa) (prfValue r.2.1)
    r.1 ((TreeOutput.topTree output).getD emptyTop) (.bottom b)
  change _ = referenceTree (m := RealM C σ) (fun oa => realLift (tweakable oa)) (fun x => realLift (prfValue r.2.1 x))
    r.1 _ (.bottom b) at e
  rw [← e]
  exact (SeedHitProof.hom_map (realLiftHom (C := C) σ) _ _).symm

theorem bottomRo_safe (r : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C)) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) : AllQueriesSatisfy (free (liftComp (bottomRo r top b) (LocalSpec C))) WorldSafe := by
  unfold bottomRo
  rw [liftComp_map, show ∀ {α β : Type} (f : α → β) (x : OracleComp (LocalSpec C) α), free (f <$> x) = f <$> free x
    from fun f x => by simp [free], DkgCompletenessProof.freeHom_referenceTree]
  generalize Tree.bottom b = tree
  exact map_safe _ (referenceTree_safe freeLift_safe (fun x => freeLift_safe _ (prfValue_safe r.2.1 x)) _ _ _)

/-! ## Runs of the signing phase under an invariant -/

section Inv

variable (prims : Primitives) (D : C.Coalition) {σ : Type} (Inv : TsigState C → HashCache C × HiddenCache C → Prop)

/-- Two computations of the signing phase with the same law from each state that satisfies `Inv`. -/
def RunEqI {α : Type} (x y : StateT (TsigState C) (RealM C σ) α) : Prop :=
  ∀ st rs w, Inv st w →
    (simulateQ (streamWorld prims D) ((x.run st).run rs)).run w =ᵈ
      (simulateQ (streamWorld prims D) ((y.run st).run rs)).run w

/-- A computation of the signing phase that keeps `Inv`. -/
def PresI {α : Type} (y : StateT (TsigState C) (RealM C σ) α) : Prop :=
  ∀ st rs w, Inv st w → ∀ z ∈ support ((simulateQ (streamWorld prims D) ((y.run st).run rs)).run w), Inv z.1.1.2 z.2

/-- A computation of the signing phase that keeps `Inv` from the state `a`. -/
def PresAt {α : Type} (a : TsigState C) (y : StateT (TsigState C) (RealM C σ) α) : Prop :=
  ∀ rs w, Inv a w → ∀ z ∈ support ((simulateQ (streamWorld prims D) ((y.run a).run rs)).run w), Inv z.1.1.2 z.2

variable {prims D Inv}

theorem RunEqI.refl {α : Type} (x : StateT (TsigState C) (RealM C σ) α) : RunEqI prims D Inv x x :=
  fun _ _ _ _ => .rfl

theorem RunEqI.bind_support {α β : Type} {x y : StateT (TsigState C) (RealM C σ) α}
    {f g : α → StateT (TsigState C) (RealM C σ) β} (h : RunEqI prims D Inv x y)
    (hfg : ∀ st rs w, Inv st w → ∀ z ∈ support ((simulateQ (streamWorld prims D) ((y.run st).run rs)).run w),
      (simulateQ (streamWorld prims D) (((f z.1.1.1).run z.1.1.2).run z.1.2)).run z.2 =ᵈ
        (simulateQ (streamWorld prims D) (((g z.1.1.1).run z.1.1.2).run z.1.2)).run z.2) :
    RunEqI prims D Inv (x >>= f) (y >>= g) := fun st rs w hw => by
  simp only [StateT.run_bind, simulateQ_bind]
  refine ((h st rs w hw).bind_left _).trans ?_
  exact OracleComp.EvalDistEq.bind_congr_of_support _ fun z hz => hfg st rs w hw z hz

theorem RunEqI.bind {α β : Type} {x y : StateT (TsigState C) (RealM C σ) α}
    {f g : α → StateT (TsigState C) (RealM C σ) β} (h : RunEqI prims D Inv x y) (hp : PresI prims D Inv y)
    (hfg : ∀ a, RunEqI prims D Inv (f a) (g a)) : RunEqI prims D Inv (x >>= f) (y >>= g) :=
  h.bind_support fun st rs w hw z hz => hfg z.1.1.1 z.1.1.2 z.1.2 z.2 (hp st rs w hw z hz)

theorem PresI.pure {α : Type} (a : α) : PresI prims D Inv (Pure.pure a : StateT (TsigState C) (RealM C σ) α) := by
  intro st rs w hw z hz
  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact hw

theorem PresI.bind {α β : Type} {y : StateT (TsigState C) (RealM C σ) α} {g : α → StateT (TsigState C) (RealM C σ) β}
    (hp : PresI prims D Inv y) (hg : ∀ a, PresI prims D Inv (g a)) : PresI prims D Inv (y >>= g) := by
  intro st rs w hw z hz
  simp only [StateT.run_bind, simulateQ_bind, support_bind, Set.mem_iUnion] at hz
  obtain ⟨p, hpz, hz⟩ := hz
  exact hg p.1.1.1 p.1.1.2 p.1.2 p.2 (hp st rs w hw p hpz) z hz

theorem PresI.lift (hmono : ∀ st w w', Inv st w → w.1 ≤ w'.1 → Inv st w') {α : Type} (x : RealM C σ α) :
    PresI prims D Inv (StateT.lift x : StateT (TsigState C) (RealM C σ) α) := by
  intro st rs w hw z hz
  simp only [StateT.run_lift, StateT.run_bind, simulateQ_bind, simulateQ_pure, StateT.run_pure, support_bind,
    Set.mem_iUnion] at hz
  obtain ⟨p, hpz, hz⟩ := hz
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact hmono st w p.2 hw (streamWorld_run_mono prims D _ w p hpz)

theorem PresAt.of {α : Type} {y : StateT (TsigState C) (RealM C σ) α} (h : PresI prims D Inv y) (a : TsigState C) :
    PresAt prims D Inv a y := fun rs w hw z hz => h a rs w hw z hz

theorem PresI.get_bind {α : Type} {g : TsigState C → StateT (TsigState C) (RealM C σ) α}
    (h : ∀ a, PresAt prims D Inv a (g a)) : PresI prims D Inv (get >>= g) := by
  intro st rs w hw z hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  exact h st rs w hw z hz

theorem PresAt.set_bind {α : Type} {a b : TsigState C} {k : PUnit → StateT (TsigState C) (RealM C σ) α}
    (hab : ∀ w, Inv a w → Inv b w) (h : PresAt prims D Inv b (k ())) : PresAt prims D Inv a (set b >>= k) := by
  intro rs w hw z hz
  simp only [StateT.run_bind, StateT.run_set, pure_bind] at hz
  exact h rs w (hab w hw) z hz

theorem PresI.map {α β : Type} (f : α → β) {y : StateT (TsigState C) (RealM C σ) α} (h : PresI prims D Inv y) :
    PresI prims D Inv (f <$> y) := by
  intro st rs w hw z hz
  simp only [StateT.run_map, simulateQ_map, support_map, Set.mem_image] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  exact h st rs w hw p hp

theorem PresI.modify {f : TsigState C → TsigState C} (hf : ∀ st w, Inv st w → Inv (f st) w) :
    PresI prims D Inv (modify f : StateT (TsigState C) (RealM C σ) PUnit) := by
  intro st rs w hw z hz
  simp only [StateT.run_modify, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact hf st w hw

theorem RunEqI.simulateQ {ι : Type} {spec : OracleSpec ι} {implL implR : QueryImpl spec (StateT (TsigState C) (RealM C σ))}
    (h : ∀ t, RunEqI prims D Inv (implL t) (implR t)) (hp : ∀ t, PresI prims D Inv (implR t)) {α : Type}
    (oa : OracleComp spec α) :
    RunEqI prims D Inv (simulateQ implL oa) (simulateQ implR oa) ∧ PresI prims D Inv (simulateQ implR oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using ⟨RunEqI.refl (pure a), PresI.pure a⟩
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    exact ⟨(h t).bind (hp t) fun u => (ih u).1, (hp t).bind fun u => (ih u).2⟩

end Inv

/-! ## The invariant of the stored bottom trees -/

section Trees

variable (prims : Primitives) (D : C.Coalition) {σ : Type}
  (r : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C)) (output : Option TreeOutput)

/-- Each stored bottom tree is the bottom tree of the dealer, fixed by the cache. -/
def TreesInv (st : TsigState C) (w : HashCache C × HiddenCache C) : Prop :=
  ∀ b v, st.trees b = some v → RoDet prims (bottomRo r ((TreeOutput.topTree output).getD emptyTop) b) v w

variable {prims D r output}

theorem TreesInv.mono {st : TsigState C} {w w' : HashCache C × HiddenCache C} (h : TreesInv prims r output st w)
    (hle : w.1 ≤ w'.1) : TreesInv prims r output st w' := fun b v hb => (h b v hb).mono hle

theorem presI_bottomOnce (b : Fin (2 ^ layerHeight)) :
    PresI prims D (TreesInv prims r output) (bottomOnce (dealerOf (σ := σ) r output) b) := by
  intro st rs w hw z hz
  simp only [bottomOnce, StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hb : st.trees b with
  | some t =>
    simp only [hb, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw
  | none =>
    simp only [hb, dealerOf_bottom, liftM, monadLift, MonadLift.monadLift, StateT.run_bind, StateT.run_lift,
      StateT.run_modify, StateT.run_pure, bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure, support_bind,
      support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    obtain ⟨hdet, -, hle⟩ := realLift_support D (bottomRo_safe r _ b) rs w p hp
    intro b' v hb'
    by_cases e : b' = b
    · subst e
      simp only [Function.update_self, Option.some.injEq] at hb'
      subst hb'
      exact hdet
    · simp only [Function.update_of_ne e] at hb'
      exact (hw b' v hb').mono hle

theorem dealerOf_value (x : Point) :
    (dealerOf (σ := σ) r output).value x = realLift (prfValue r.2.1 x) := rfl

theorem prfValue_worldSafe (x : Point) :
    AllQueriesSatisfy (free (liftComp (prfValue r.2.1 x) (LocalSpec C))) WorldSafe :=
  freeLift_safe _ (prfValue_safe r.2.1 x)

theorem liftM_tsig {α : Type} (x : RealM C σ α) :
    (liftM x : StateT (TsigState C) (RealM C σ) α) = StateT.lift x := rfl

/-- The answer of the dealer to `tree b`, as `tsigOracles` computes it. -/
def treeStep (b : Fin (2 ^ layerHeight)) : StateT (TsigState C) (RealM C σ) (Option (BottomTree × Digest)) := do
  let some tree ← bottomOnce (dealerOf (σ := σ) r output) b | pure none
  pure (some (tree, ← StateT.lift (realLift (prfValue r.2.1 (.randomizer topLayer (topKey b))))))

theorem tsigOracles_tree (b : Fin (2 ^ layerHeight)) :
    (tsigOracles realLift (dealerOf (σ := σ) r output) (.tree b) :
      StateT (TsigState C) (RealM C σ) (Option (BottomTree × Digest))) = treeStep (σ := σ) (r := r) (output := output) b := rfl

theorem treesInv_init (w : HashCache C × HiddenCache C) :
    TreesInv prims r output (⟨D.1, fun _ => none, [], fun _ => none⟩ : TsigState C) w := by
  intro b v h
  simp at h

/-- The answer of the dealer to `tree b` is fixed by the cache after it. -/
theorem treeAnswer_det (b : Fin (2 ^ layerHeight)) (st : TsigState C) (rs : RealState C σ)
    (w : HashCache C × HiddenCache C) (hw : TreesInv prims r output st w)
    (z : ((Option (BottomTree × Digest) × TsigState C) × RealState C σ) × (HashCache C × HiddenCache C))
    (hz : z ∈ support ((simulateQ (streamWorld prims D)
      (((treeStep (σ := σ) (r := r) (output := output) b).run st).run rs)).run w))
    (t : BottomTree) (ρ : Digest) (ht : z.1.1.1 = some (t, ρ)) :
    RoDet prims (bottomRo r ((TreeOutput.topTree output).getD emptyTop) b) (some t) z.2 ∧
      RoDet prims (prfValue r.2.1 (.randomizer topLayer (topKey b))) ρ z.2 := by
  simp only [treeStep, bottomOnce, StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases hb : st.trees b with
  | some v =>
    simp only [hb, StateT.run_pure, pure_bind] at hz
    cases v with
    | none =>
      simp at hz
      subst hz
      simp at ht
    | some t' =>
      simp only [StateT.run_bind, StateT.run_lift,
        bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
      obtain ⟨p, hp, hz⟩ := hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨hdet, -, hle⟩ := realLift_support D (prfValue_worldSafe (r := r) _) rs w p hp
      simp only [Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      exact ⟨(hw b _ hb).mono hle, hdet⟩
  | none =>
    simp only [hb, dealerOf_bottom, liftM_tsig, StateT.run_bind,
      StateT.run_lift, StateT.run_modify, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    obtain ⟨hdet1, -, hle1⟩ := realLift_support D (bottomRo_safe r _ b) rs w p hp
    rcases hv : p.1.1 with _ | t'
    · simp [hv] at hz
      subst hz
      simp at ht
    · simp only [hv, StateT.run_pure,
        simulateQ_pure] at hz
      obtain ⟨q, hq, hz⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hq
      subst hq
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hz
      obtain ⟨q, hq, hz⟩ := hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      obtain ⟨hdet2, -, hle2⟩ := realLift_support D (prfValue_worldSafe (r := r) _) p.1.2 p.2 q hq
      simp only [Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      rw [hv] at hdet1
      exact ⟨hdet1.mono hle2, hdet2⟩

/-- With the answer fixed by the cache, `dealerTree` gives the answer again and changes no state. -/
theorem dealerTree_replay (b : Fin (2 ^ layerHeight)) {t : BottomTree} {ρ : Digest} {w : HashCache C × HiddenCache C}
    (h1 : RoDet prims (bottomRo r ((TreeOutput.topTree output).getD emptyTop) b) (some t) w)
    (h2 : RoDet prims (prfValue r.2.1 (.randomizer topLayer (topKey b))) ρ w) (s : RealState C σ) :
    (simulateQ (streamWorld prims D) ((dealerTree (dealerOf (σ := σ) r output) b).run s)).run w =
      pure ((some (t, ρ), s), w) := by
  unfold dealerTree
  rw [dealerOf_bottom, StateT.run_bind, simulateQ_bind, StateT.run_bind, realLift_replay D (bottomRo_safe r _ b) h1,
    pure_bind]
  dsimp only
  rw [dealerOf_value, StateT.run_bind, simulateQ_bind, StateT.run_bind, realLift_replay D (prfValue_worldSafe (r := r) _) h2,
    pure_bind]
  simp

variable {K circuits settings runLimit}

theorem presI_tsigOracles (q : TsigQuery C) :
    PresI prims D (TreesInv prims r output) (tsigOracles realLift (dealerOf (σ := σ) r output) q) := by
  have hmono : ∀ st w w', TreesInv prims r output st w → w.1 ≤ w'.1 → TreesInv prims r output st w' :=
    fun _ _ _ h hle => h.mono hle
  cases q with
  | corrupt i =>
    dsimp only [tsigOracles]
    refine PresI.get_bind fun a => ?_
    split
    · exact PresAt.of (PresI.pure _) a
    · exact PresAt.set_bind (fun _ h => h) (PresAt.of (PresI.pure _) _)
  | tree b =>
    dsimp only [tsigOracles]
    refine PresI.bind (presI_bottomOnce b) fun o => ?_
    rcases o with _ | tree
    · exact PresI.pure _
    · exact PresI.bind (PresI.lift hmono _) fun _ => PresI.pure _
  | round1 i J e message =>
    dsimp only [tsigOracles]
    refine PresI.get_bind fun a => ?_
    split
    · exact PresAt.of (PresI.pure _) a
    · refine PresAt.set_bind (fun _ h => h) (PresAt.of ?_ _)
      exact PresI.map _ (PresI.lift hmono _)
  | round2 i J e message parts =>
    dsimp only [tsigOracles]
    refine PresI.get_bind fun a => ?_
    split
    · exact PresAt.of (PresI.pure _) a
    · refine PresAt.of ?_ a
      refine PresI.bind (presI_bottomOnce _) fun o => ?_
      rcases o with _ | tree
      · exact PresI.pure _
      · refine PresI.bind (PresI.lift hmono _) fun own => ?_
        refine PresI.bind (PresI.lift hmono _) fun o => ?_
        rcases o with _ | values
        · exact PresI.pure _
        · exact PresI.bind (PresI.modify fun _ _ h => h) fun _ => PresI.pure _

theorem presI_secSignRequest (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    PresI prims D (TreesInv prims r output) (secSignRequest (dealerOf (σ := σ) r output) i e q) := by
  have hmono : ∀ st w w', TreesInv prims r output st w → w.1 ≤ w'.1 → TreesInv prims r output st w' :=
    fun _ _ _ h hle => h.mono hle
  unfold secSignRequest
  refine PresI.bind (PresI.lift hmono _) fun _ => PresI.bind (PresI.lift hmono _) fun s => ?_
  split
  · exact presI_tsigOracles q
  · exact PresI.pure _

end Trees

section Stage

variable {K circuits settings runLimit}

variable (prims : Primitives) (D : C.Coalition) (r : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C))
  (output : Option TreeOutput)

theorem secRunsD_answer (m : Mode) (net : Adversary C E Unit PEmpty PEmpty) (emu : C.Party → Option (Keys C))
    (b : Fin (2 ^ layerHeight)) {t : BottomTree} {ρ : Digest} {w : HashCache C × HiddenCache C}
    (h1 : RoDet prims (bottomRo r ((TreeOutput.topTree output).getD emptyTop) b) (some t) w)
    (h2 : RoDet prims (prfValue r.2.1 (.randomizer topLayer (topKey b))) ρ w) (rs : RealState C net.State) :
    (simulateQ (streamWorld prims D)
      ((secRunsD K circuits settings runLimit D m net (dealerOf r output) emu (.bottom b) 1).run rs)).run w =
    (simulateQ (streamWorld prims D)
      ((secRunsC K circuits settings runLimit D m net (dealerOf r output) emu (.bottom b) (some (t, ρ)) 1).run rs)).run w := by
  simp only [secRunsD, secRunsC, secRunD, secRunC, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · by_cases hlt : rs.runs (.bottom b) < m.emulated (.bottom b)
    · simp only [StateT.run_get, simulateQ_pure, StateT.run_pure, pure_bind, hlt, ite_true, StateT.run_bind,
        simulateQ_bind, dealerTree_replay (D := D) b h1 h2]
    · simp only [StateT.run_get, simulateQ_pure, StateT.run_pure, pure_bind, hlt, ite_false, StateT.run_bind,
        simulateQ_bind]
  · rfl

theorem runEqI_secTreeRequest (m : Mode) (hskip : m.skip = true) (net : Adversary C E Unit PEmpty PEmpty)
    (emu : C.Party → Option (Keys C)) (b : Fin (2 ^ layerHeight)) :
    RunEqI prims D (TreesInv prims r output)
      (secTreeRequestD K circuits settings runLimit D m net (dealerOf r output) emu b)
      (secTreeRequestC K circuits settings runLimit D m net (dealerOf r output) emu b) := by
  unfold secTreeRequestD secTreeRequestC
  rw [tsigOracles_tree]
  refine RunEqI.bind_support (RunEqI.refl _) fun st rs w hw z hz => ?_
  obtain ⟨⟨⟨answer, st'⟩, rs'⟩, w'⟩ := z
  rcases answer with _ | ⟨t, ρ⟩
  · simp [hskip]
  · obtain ⟨h1, h2⟩ := treeAnswer_det b st rs w hw _ hz t ρ rfl
    simp only [hskip, Option.isSome_some, or_true, ite_true, StateT.run_bind, StateT.run_lift, simulateQ_bind,
      bind_assoc]
    rw [secRunsD_answer prims D r output m net emu b h1 h2]
    exact EvalDistEq.refl _

theorem presI_secTreeRequestC (m : Mode) (net : Adversary C E Unit PEmpty PEmpty)
    (emu : C.Party → Option (Keys C)) (b : Fin (2 ^ layerHeight)) :
    PresI prims D (TreesInv prims r output)
      (secTreeRequestC K circuits settings runLimit D m net (dealerOf r output) emu b) := by
  have hmono : ∀ st w w', TreesInv prims r output st w → w.1 ≤ w'.1 → TreesInv prims r output st w' :=
    fun _ _ _ h hle => h.mono hle
  unfold secTreeRequestC
  refine PresI.bind (presI_tsigOracles _) fun answer => ?_
  have hk : ∀ s : RealState C net.State, PresI prims D (TreesInv prims r output)
      (match heldBottom D s.operators b, answer with
        | some tree, some (_, ρ) => (pure (some (tree, ρ)) : StateT (TsigState C) (RealM C net.State) _)
        | _, _ => pure none) := fun s => by
    split <;> exact PresI.pure _
  dsimp only
  split
  · exact PresI.bind (PresI.lift hmono _) fun _ => PresI.bind (PresI.lift hmono _) hk
  · exact PresI.bind (PresI.lift hmono _) hk

theorem secSigning_bottom (A : DkgTsigAdversary C E) (emu : C.Party → Option (Keys C))
    (rs : RealState C A.net.State) (w : HashCache C × HiddenCache C) :
    (simulateQ (streamWorld prims D)
      ((secSigningD K circuits settings runLimit D ⟨true, fun _ => runLimit⟩ A (dealerOf r output) emu).run rs)).run w =ᵈ
    (simulateQ (streamWorld prims D)
      ((secSigningC K circuits settings runLimit D ⟨true, fun _ => runLimit⟩ A (dealerOf r output) emu).run rs)).run w := by
  have hmono : ∀ st w w', TreesInv prims r output st w → w.1 ≤ w'.1 → TreesInv prims r output st w' :=
    fun _ _ _ h hle => h.mono hle
  unfold secSigningD secSigningC
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  generalize topHolder D rs.operators = o
  rcases o with _ | holder
  · exact EvalDistEq.refl _
  · simp only [StateT.run_bind, simulateQ_bind]
    refine EvalDistEq.bind_left ?_ _
    refine (RunEqI.simulateQ (fun t => ?_) (fun t => ?_) _).1 _ rs w (treesInv_init (prims := prims) (D := D) (r := r) (output := output) w)
    · rcases t with t | q | q
      · simp only [QueryImpl.add_apply_inl]
        exact RunEqI.refl _
      · simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
        rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
        · exact RunEqI.refl _
        · exact runEqI_secTreeRequest prims D r output _ rfl A.net emu b
        · exact RunEqI.refl _
        · exact RunEqI.refl _
      · simp only [QueryImpl.add_apply_inr]
        exact RunEqI.refl _
    · rcases t with t | q | q
      · simp only [QueryImpl.add_apply_inl]
        exact PresI.lift hmono _
      · simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
        rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
        · exact PresI.pure _
        · exact presI_secTreeRequestC prims D r output _ A.net emu b
        · exact presI_secSignRequest i e _
        · exact presI_secSignRequest i e _
      · simp only [QueryImpl.add_apply_inr]
        rcases q with _ | _
        · exact PresI.lift hmono _
        · exact PresI.lift hmono _

end Stage

variable (prims : Primitives)

/-- `givenDealerGame` and `givenAnswerGame` win with the same probability. -/
def BottomStage : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    streamAccepts prims D (givenDealerGame K circuits settings runLimit D A) =
      streamAccepts prims D (givenAnswerGame K circuits settings runLimit D A)

/-- `givenAnswerGame` wins at most as often as `forgerWorldGame`, for a positive run limit. -/
def ShapeStage : Prop :=
  0 < runLimit → ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    streamAccepts prims D (givenAnswerGame K circuits settings runLimit D A) ≤
      streamAccepts prims D (forgerWorldGame K circuits settings runLimit D A)

theorem bottomStage : BottomStage K circuits settings runLimit prims := fun D A => by
  unfold streamAccepts
  suffices h : WorldRun (streamWorld prims D) (givenDealerGame K circuits settings runLimit D A)
      (givenAnswerGame K circuits settings runLimit D A) by
    rw [(h (∅, ∅)).prEvent_eq]
  unfold givenDealerGame givenAnswerGame
  refine WorldRun.bind_right _ _ fun r => WorldRun.bind_right _ _ fun output =>
    WorldRun.bind_right _ _ fun o => WorldRun.bind_right _ _ fun te => fun w => ?_
  simp only [StateT.run'_eq, secRestD, secRestC, secRunsD_top, StateT.run_bind, simulateQ_map, simulateQ_bind,
    StateT.run_map]
  refine EvalDistEq.map_congr _ ?_
  exact EvalDistEq.bind_right _ fun _ => EvalDistEq.bind_right _ fun v => EvalDistEq.bind_right _ fun _ =>
    EvalDistEq.bind_right _ fun p => secSigning_bottom prims D r output A (committed v.1.1.2 te.2) p.1.2 p.2

/-- `StructureStage` from the two stages. -/
theorem structureStage_of_stages (bottom : BottomStage K circuits settings runLimit prims)
    (shape : ShapeStage K circuits settings runLimit prims) : StructureStage K circuits settings runLimit prims :=
  fun hrun D A => (bottom D A).trans_le (shape hrun D A)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.structureStage_of_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.structureStage_of_stages

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.bottomStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.bottomStage
