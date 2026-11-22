import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Bottom
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Hops

/-!
# The runs of `givenAnswerGame` against the runs of `forgerWorldGame`

`Rel f x y` relates a computation `x` of the signing phase of `givenAnswerGame` to a computation `y`
of the forger in the world. From each state `rs` of the forger whose keys are `emu`, `x` from the
state `keysProj k fl rs` gives in `streamWorld` the image of the run of `y` under `f` and
`keysProj k fl`, and `y` keeps the keys. The log of the setup calls of the forger is dropped.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The log of the setup calls is dropped -/

theorem worldHonestCall_query (t : (LocalSpec C).Domain) (log : CallLog C) (st : TsigState C) :
    ((worldHonestCall t).run log).run st =
      (fun a => ((a, log), st)) <$> free (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t)) := by
  simp [worldHonestCall, toWorld, StateT.run_lift]

/-- A program of the two roles in the world of the forger, with its log dropped, is the program of
`worldRoles`. -/
theorem dropLog_simulateQ {α : Type} (P : OracleComp (LocalSpec C + LocalSpec C) α) (log : CallLog C)
    (st : TsigState C) :
    (fun z => (z.1.1, z.2)) <$>
        ((simulateQ (worldAdversaryCall (C := C) + worldHonestCall (C := C)) P : WorldM C α).run log).run st =
      (fun a => (a, st)) <$> simulateQ worldSplit P := by
  induction P using OracleComp.inductionOn generalizing log with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_bind, simulateQ_query, simulateQ_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    rw [StateT.run_bind, StateT.run_bind, map_bind, map_bind]
    rcases t with t | t
    · simp only [QueryImpl.add_apply_inl]
      rw [worldAdversaryCall_query, bind_map_left]
      simp only [ih]
      simp only [worldSplit, ← fst_observe, bind_map_left]
      rfl
    · simp only [QueryImpl.add_apply_inr]
      rw [worldHonestCall_query, bind_map_left]
      simp only [ih]
      rfl

section Network

variable {E I O L R Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)

theorem dropLog_executePhase (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E (CallSpec I O) α)
    (log : CallLog C) (st : TsigState C) :
    (fun z => (z.1.1, z.2)) <$> ((executePhase forgerWorldRoles D A F fuel state program).run log).run st =
      (fun a => (a, st)) <$> executePhase worldRoles D A F fuel state program := by
  rw [forgerWorldRoles_eq, worldRoles_eq, ← simulateQ_executePhase_mapRoles, ← simulateQ_executePhase_mapRoles]
  exact dropLog_simulateQ _ log st

end Network

/-! ## The relation -/

variable {σ : Type}

/-- The state of `givenAnswerGame` for the state `rs` of the forger. The keys of the dealer `k` take
the place of the keys of the emulated operators, and the flag is `fl`. -/
def keysProj (k : C.Party → Keys C) (fl : Bool) (rs : RealState C σ) : RealState C σ :=
  ⟨rs.adversary, fun i => ⟨(rs.operators i).keys.map fun _ => k i, (rs.operators i).top, (rs.operators i).bottom⟩,
    rs.runs, rs.closed, fl⟩

/-- The keys of the operators are `emu`. -/
def KeysInv (emu : C.Party → Option (Keys C)) (rs : RealState C σ) : Prop := ∀ i, (rs.operators i).keys = emu i

variable (prims : Primitives) (D : C.Coalition)

/-- The run of a computation of the signing phase of `givenAnswerGame`. -/
def semGL {α : Type} (x : StateT (TsigState C) (RealM C σ) α) (st : TsigState C) (rs : RealState C σ)
    (w : HashCache C × HiddenCache C) :=
  (simulateQ (streamWorld prims D) ((x.run st).run rs)).run w

/-- The run of a computation of the forger in the world. -/
def semFW {α : Type} (y : RedW C σ α) (rs : RealState C σ) (log : CallLog C) (st : TsigState C)
    (w : HashCache C × HiddenCache C) :=
  (simulateQ (streamWorld prims D) (((y.run rs).run log).run st)).run w

variable (k : C.Party → Keys C) (fl : Bool) (emu : C.Party → Option (Keys C))

/-- `x` gives the image of the run of `y` under `f` and `keysProj k fl`, and `y` keeps the keys. -/
def Rel {α β : Type} (f : β → α) (x : StateT (TsigState C) (RealM C σ) α) (y : RedW C σ β) : Prop :=
  ∀ rs log st w, KeysInv emu rs →
    semGL prims D x st (keysProj k fl rs) w =ᵈ
      (fun z => (((f z.1.1.1.1, z.1.2), keysProj k fl z.1.1.1.2), z.2)) <$> semFW prims D y rs log st w ∧
    ∀ z ∈ support (semFW prims D y rs log st w), KeysInv emu z.1.1.1.2

/-- `Rel` for a computation of the runs of the trees. -/
def Rel1 {α : Type} (x : RealM C σ α) (y : RedW C σ α) : Prop :=
  Rel prims D k fl emu id (StateT.lift x) y

variable {prims D k fl emu}

theorem semGL_bind {α β : Type} (x : StateT (TsigState C) (RealM C σ) α) (g : α → StateT (TsigState C) (RealM C σ) β)
    (st : TsigState C) (rs : RealState C σ) (w : HashCache C × HiddenCache C) :
    semGL prims D (x >>= g) st rs w = semGL prims D x st rs w >>= fun p => semGL prims D (g p.1.1.1) p.1.1.2 p.1.2 p.2 := by
  simp [semGL, StateT.run_bind, simulateQ_bind]

theorem semFW_bind {α β : Type} (y : RedW C σ α) (g : α → RedW C σ β) (rs : RealState C σ) (log : CallLog C)
    (st : TsigState C) (w : HashCache C × HiddenCache C) :
    semFW prims D (y >>= g) rs log st w =
      semFW prims D y rs log st w >>= fun z => semFW prims D (g z.1.1.1.1) z.1.1.1.2 z.1.1.2 z.1.2 z.2 := by
  simp [semFW, StateT.run_bind, simulateQ_bind]

theorem Rel.pure {α : Type} (a : α) :
    Rel prims D k fl emu id (Pure.pure a : StateT (TsigState C) (RealM C σ) α) (Pure.pure a) := by
  intro rs log st w hrs
  refine ⟨?_, ?_⟩
  · simp [semGL, semFW]
  · intro z hz
    simp only [semFW, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hrs

theorem Rel.bind {α β γ δ : Type} {f : β → α} {g : δ → γ} {x : StateT (TsigState C) (RealM C σ) α} {y : RedW C σ β}
    {kx : α → StateT (TsigState C) (RealM C σ) γ} {ky : β → RedW C σ δ}
    (h : Rel prims D k fl emu f x y) (hk : ∀ b, Rel prims D k fl emu g (kx (f b)) (ky b)) :
    Rel prims D k fl emu g (x >>= kx) (y >>= ky) := by
  intro rs log st w hrs
  obtain ⟨h1, h2⟩ := h rs log st w hrs
  refine ⟨?_, ?_⟩
  · rw [semGL_bind, semFW_bind, map_bind]
    refine (h1.bind_left _).trans ?_
    rw [bind_map_left]
    exact OracleComp.EvalDistEq.bind_congr_of_support _ fun z hz =>
      (hk z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2 (h2 z hz)).1
  · intro z hz
    rw [semFW_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    exact (hk p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 (h2 p hp)).2 z hz

theorem Rel.get_bind {α β : Type} {g : β → α} {kx : RealState C σ → StateT (TsigState C) (RealM C σ) α}
    {ky : RealState C σ → RedW C σ β} (hk : ∀ s, KeysInv emu s → Rel prims D k fl emu g (kx (keysProj k fl s)) (ky s)) :
    Rel prims D k fl emu g (StateT.lift (get : RealM C σ (RealState C σ)) >>= kx) (get >>= ky) := by
  intro rs log st w hrs
  have eL : semGL prims D (StateT.lift (get : RealM C σ (RealState C σ)) >>= kx) st (keysProj k fl rs) w =
      semGL prims D (kx (keysProj k fl rs)) st (keysProj k fl rs) w := by
    simp [semGL, StateT.run_bind, StateT.run_lift]
  have eR : semFW prims D ((get : RedW C σ (RealState C σ)) >>= ky) rs log st w = semFW prims D (ky rs) rs log st w := by
    simp [semFW, StateT.run_bind]
  rw [eL, eR]
  exact hk rs hrs rs log st w hrs

theorem Rel.set {a b : RealState C σ} (hab : keysProj k fl b = a) (hb : KeysInv emu b) :
    Rel prims D k fl emu id (StateT.lift (set a : RealM C σ PUnit)) (set b : RedW C σ PUnit) := by
  intro rs log st w hrs
  refine ⟨?_, ?_⟩
  · subst hab
    simp [semGL, semFW, StateT.run_lift]
  · intro z hz
    simp only [semFW, StateT.run_set, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hb

theorem Rel.liftW {α : Type} {x : OracleComp (WorldSpec C) α} {y : WorldM C α}
    (h : ∀ log st, (fun z => (z.1.1, z.2)) <$> (y.run log).run st = (fun a => (a, st)) <$> x) :
    Rel prims D k fl emu id (StateT.lift (StateT.lift x) : StateT (TsigState C) (RealM C σ) α)
      (StateT.lift y : RedW C σ α) := by
  intro rs log st w hrs
  have hw := congrArg (fun c => (simulateQ (streamWorld prims D) c).run w) (h log st)
  simp only [simulateQ_map, StateT.run_map] at hw
  refine ⟨?_, ?_⟩
  · have eL : semGL prims D (StateT.lift (StateT.lift x) : StateT (TsigState C) (RealM C σ) α) st (keysProj k fl rs) w =
        (fun q => ((q.1, keysProj k fl rs), q.2)) <$> ((fun p => ((p.1, st), p.2)) <$>
          (simulateQ (streamWorld prims D) x).run w) := by
      simp [semGL, StateT.run_lift, Functor.map_map]
    have eR : semFW prims D (StateT.lift y : RedW C σ α) rs log st w =
        (fun z => ((((z.1.1.1, rs), z.1.1.2), z.1.2), z.2)) <$>
          (simulateQ (streamWorld prims D) ((y.run log).run st)).run w := by
      simp [semFW, StateT.run_lift]
    rw [eL, eR, ← hw, Functor.map_map, Functor.map_map]
    exact EvalDistEq.refl _
  · intro z hz
    simp only [semFW, StateT.run_lift, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p, -, hz⟩ := hz
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hrs

theorem stLift_bind {α β : Type} (x : RealM C σ α) (g : α → RealM C σ β) :
    (StateT.lift (x >>= g) : StateT (TsigState C) (RealM C σ) β) = StateT.lift x >>= fun a => StateT.lift (g a) := by
  ext s
  simp [StateT.run_lift]

theorem Rel1.bind {α β : Type} {x : RealM C σ α} {y : RedW C σ α} {kx : α → RealM C σ β} {ky : α → RedW C σ β}
    (h : Rel1 prims D k fl emu x y) (hk : ∀ a, Rel1 prims D k fl emu (kx a) (ky a)) :
    Rel1 prims D k fl emu (x >>= kx) (y >>= ky) := by
  unfold Rel1
  rw [stLift_bind]
  exact Rel.bind h hk

theorem Rel1.pure {α : Type} (a : α) : Rel1 prims D k fl emu (Pure.pure a : RealM C σ α) (Pure.pure a) := by
  unfold Rel1
  rw [show (StateT.lift (Pure.pure a : RealM C σ α) : StateT (TsigState C) (RealM C σ) α) = Pure.pure a by
    ext s; simp [StateT.run_lift]]
  exact Rel.pure a

theorem Rel1.get_bind {α : Type} {kx : RealState C σ → RealM C σ α} {ky : RealState C σ → RedW C σ α}
    (hk : ∀ s, KeysInv emu s → Rel1 prims D k fl emu (kx (keysProj k fl s)) (ky s)) :
    Rel1 prims D k fl emu (get >>= kx) (get >>= ky) := by
  unfold Rel1
  rw [stLift_bind]
  exact Rel.get_bind hk

theorem Rel1.set {a b : RealState C σ} (hab : keysProj k fl b = a) (hb : KeysInv emu b) :
    Rel1 prims D k fl emu (set a : RealM C σ PUnit) (set b : RedW C σ PUnit) :=
  Rel.set hab hb

theorem Rel1.ite {α : Type} {p q : Prop} (hpq : p ↔ q) {x₁ x₂ : RealM C σ α} {y₁ y₂ : RedW C σ α}
    (h₁ : Rel1 prims D k fl emu x₁ y₁) (h₂ : Rel1 prims D k fl emu x₂ y₂) :
    Rel1 prims D k fl emu (if p then x₁ else x₂) (if q then y₁ else y₂) := by
  by_cases hp : p
  · simpa only [hp, hpq.1 hp, ite_true] using h₁
  · have hq : ¬q := fun hq => hp (hpq.2 hq)
    simpa only [hp, hq, ite_false] using h₂

theorem Rel.liftT {α : Type} (z : StateT (TsigState C) (OracleComp (WorldSpec C)) α) :
    Rel prims D k fl emu id (StateT.mk fun st => StateT.lift (z.run st) : StateT (TsigState C) (RealM C σ) α)
      (StateT.lift (StateT.lift z) : RedW C σ α) := by
  intro rs log st w hrs
  refine ⟨?_, ?_⟩
  · simp [semGL, semFW, StateT.run_lift, Functor.map_map]
  · intro z hz
    simp [semFW, StateT.run_lift] at hz
    obtain ⟨_, _, _, _, -, rfl⟩ := hz
    exact hrs

theorem Rel.modify {f g : RealState C σ → RealState C σ}
    (hfg : ∀ s, KeysInv emu s → keysProj k fl (g s) = f (keysProj k fl s) ∧ KeysInv emu (g s)) :
    Rel prims D k fl emu id (StateT.lift (modify f : RealM C σ PUnit)) (modify g : RedW C σ PUnit) := by
  intro rs log st w hrs
  refine ⟨?_, ?_⟩
  · simp [semGL, semFW, StateT.run_lift, (hfg rs hrs).1]
  · intro z hz
    simp only [semFW, StateT.run_modify, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact (hfg rs hrs).2

theorem Rel.simulateQ {ι : Type} {spec : OracleSpec ι} {implL : QueryImpl spec (StateT (TsigState C) (RealM C σ))}
    {implR : QueryImpl spec (RedW C σ)} (h : ∀ t, Rel prims D k fl emu id (implL t) (implR t)) {α : Type}
    (oa : OracleComp spec α) :
    Rel prims D k fl emu id (simulateQ implL oa) (simulateQ implR oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using Rel.pure a
  | query_bind t k' ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    exact (h t).bind ih

theorem rel1_read : Rel1 prims D k fl emu ((fun x => x.adversary) <$> (get : RealM C σ (RealState C σ)))
    ((fun x => x.adversary) <$> (get : RedW C σ (RealState C σ))) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact Rel1.get_bind fun s _ => Rel1.pure _

/-! ## The corruption calls of the forger -/

/-- A corruption call of the forger. -/
def corruptCall (dealt : Dealt C (OracleComp (WorldSpec C))) (i : C.Party) : WorldM C (Option (Keys C)) :=
  worldTsig dealt (.corrupt i)

theorem corruptCall_run (dealt : Dealt C (OracleComp (WorldSpec C))) (i : C.Party) (S : Finset C.Party)
    (hcard : ¬ C.t - 1 < (insert i S).card) (log : CallLog C) :
    ((corruptCall dealt i).run log).run ⟨S, fun _ => none, [], fun _ => none⟩ =
      pure ((some (dealt.keys i), log), ⟨insert i S, fun _ => none, [], fun _ => none⟩) := by
  change ((StateT.lift (do
      let st ← (get : StateT (TsigState C) (OracleComp (WorldSpec C)) (TsigState C))
      if C.t - 1 < (insert i st.corrupt).card then pure none else do
        set { st with corrupt := insert i st.corrupt }
        pure (some (dealt.keys i))) : WorldM C (Option (Keys C))).run log).run ⟨S, fun _ => none, [], fun _ => none⟩ = _
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_get, pure_bind, hcard, ↓reduceIte, StateT.run_set,
    StateT.run_pure, bind_assoc]

/-- The corruption calls of the forger for the operators `g` of the coalition. -/
theorem corrupt_run (dealt : Dealt C (OracleComp (WorldSpec C))) :
    ∀ {n : ℕ} (g : Fin n → C.Party) (S : Finset C.Party),
      S ∪ (Finset.univ.filter fun j => g j ∈ D.1).image g ⊆ D.1 → ∀ log : CallLog C,
      ((OverPermutation.sequenceFin fun j => if g j ∈ D.1 then worldTsig dealt (.corrupt (g j))
          else (pure none : WorldM C (Option (Keys C)))).run log).run ⟨S, fun _ => none, [], fun _ => none⟩ =
        pure ((fun j => if g j ∈ D.1 then some (dealt.keys (g j)) else none, log),
          ⟨S ∪ (Finset.univ.filter fun j => g j ∈ D.1).image g, fun _ => none, [], fun _ => none⟩)
  | 0, g, S, _, log => by
    simp only [OverPermutation.sequenceFin, StateT.run_pure]
    congr 3
    · funext j
      exact j.elim0
    · ext x
      simp
  | n + 1, g, S, hS, log => by
    have hsub : ∀ j, g j ∈ D.1 → g j ∈ S ∪ (Finset.univ.filter fun j => g j ∈ D.1).image g :=
      fun j hj => Finset.mem_union_right _ (Finset.mem_image.2 ⟨j, by simp [hj], rfl⟩)
    have hset : ∀ T : Finset C.Party, S ∪ (Finset.univ.filter fun j => g j ∈ D.1).image g =
        T ∪ (Finset.univ.filter fun j : Fin n => g j.succ ∈ D.1).image (fun j => g j.succ) →
        T ∪ (Finset.univ.filter fun j : Fin n => g j.succ ∈ D.1).image (fun j => g j.succ) ⊆ D.1 := by
      intro T hT
      rw [← hT]
      exact hS
    simp only [OverPermutation.sequenceFin, StateT.run_bind]
    by_cases h0 : g 0 ∈ D.1
    · have hcard : ¬ C.t - 1 < (insert (g 0) S).card := not_lt.2 ((Finset.card_le_card
        (Finset.insert_subset (hS (hsub 0 h0)) (Finset.union_subset_left hS))).trans D.2)
      simp only [h0, ↓reduceIte]
      rw [show worldTsig dealt (.corrupt (g 0)) = corruptCall dealt (g 0) from rfl, corruptCall_run dealt _ _ hcard,
        pure_bind]
      have heq : S ∪ (Finset.univ.filter fun j => g j ∈ D.1).image g =
          insert (g 0) S ∪ (Finset.univ.filter fun j : Fin n => g j.succ ∈ D.1).image (fun j => g j.succ) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and, Fin.exists_fin_succ]
        constructor
        · rintro (h | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> tauto
        · rintro ((rfl | h) | ⟨j, hj, rfl⟩) <;> tauto
      rw [corrupt_run dealt (fun j => g j.succ) (insert (g 0) S) (hset _ heq) log]
      simp only [pure_bind, StateT.run_pure, heq]
      congr 3
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [h0]
    · simp only [h0, ↓reduceIte, StateT.run_pure, pure_bind]
      have heq : S ∪ (Finset.univ.filter fun j => g j ∈ D.1).image g =
          S ∪ (Finset.univ.filter fun j : Fin n => g j.succ ∈ D.1).image (fun j => g j.succ) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.exists_fin_succ]
        constructor
        · rintro (h | ⟨hj, rfl⟩ | ⟨j, hj, rfl⟩)
          · exact Or.inl h
          · exact absurd hj h0
          · exact Or.inr ⟨j, hj, rfl⟩
        · rintro (h | ⟨j, hj, rfl⟩) <;> tauto
      rw [corrupt_run dealt (fun j => g j.succ) S (hset _ heq) log]
      simp only [pure_bind, heq]
      congr 3
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [h0]

/-! ## The runs of the trees -/

section Runs

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (runLimit : ℕ)

theorem rel1_emulatedRun (net : Adversary C E Unit PEmpty PEmpty) (openings : List (List (List Bit)))
    (randomizer : Randomizer) (tree : Tree) :
    Rel1 prims D k fl emu (worldEmulatedRun K circuits settings D net emu openings randomizer tree)
      (emulatedRunW K circuits settings D net openings randomizer tree) := by
  unfold worldEmulatedRun emulatedRunW
  refine Rel1.get_bind fun s hs => ?_
  have hkeys : (fun i => (s.operators i).keys) = emu := funext hs
  have hop : ∀ i, s.operators i = ⟨emu i, (s.operators i).top, (s.operators i).bottom⟩ := fun i => by
    rw [← hs i]
  refine Rel1.bind (Rel.liftW fun log st => ?_) fun p => ?_
  · rw [dropLog_executePhase, hkeys]
    have hprog : (fun i => emulatedProgram K circuits settings
        (shiftedBuildingBlocks K circuits settings D (gameParameter D emu) (gameSeeds D emu) openings) randomizer i
          (s.operators i) tree) = fun i => emulatedProgram K circuits settings
        (shiftedBuildingBlocks K circuits settings D (gameParameter D emu) (gameSeeds D emu) openings) randomizer i
          ⟨emu i, (s.operators i).top, (s.operators i).bottom⟩ tree := funext fun i => by rw [← hop i]
    rw [hprog]
    rfl
  · obtain ⟨state, outputs⟩ := p
    refine Rel1.set ?_ ?_
    · cases tree <;> rfl
    · intro i
      cases tree <;> exact hs i

theorem runs_lt_of_mayRun {s : RealState C σ} {tree : Tree} (h : mayRun runLimit D s tree) :
    s.runs tree < runLimit := by
  cases tree with
  | top => exact h.1
  | bottom b => exact h.2.1

/-- A step of `secRunsC` whose run is `run` while the tree has fewer than `runLimit` runs. -/
theorem secRunsC_succ (net : Adversary C E Unit PEmpty PEmpty) (dealer : Dealt C (RealM C net.State))
    (tree : Tree) (answer : Option (BottomTree × Digest)) (count : ℕ) (run : RealM C net.State Unit)
    (hrun : ∀ s : RealState C net.State, s.runs tree < runLimit →
      (secRunC K circuits settings D ⟨true, fun _ => runLimit⟩ net dealer emu tree answer).run s = run.run s) :
    secRunsC K circuits settings runLimit D ⟨true, fun _ => runLimit⟩ net dealer emu tree answer (count + 1) =
      get >>= fun s => if mayRun runLimit D s tree then
        (run >>= fun _ => secRunsC K circuits settings runLimit D ⟨true, fun _ => runLimit⟩ net dealer emu tree answer
          count) else pure () := by
  ext rs
  simp only [secRunsC, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with h
  · rw [StateT.run_bind, StateT.run_bind, hrun rs (runs_lt_of_mayRun runLimit h)]
  · rfl

theorem rel1_secRuns (net : Adversary C E Unit PEmpty PEmpty) (dealer : Dealt C (RealM C net.State))
    (tree : Tree) (answer : Option (BottomTree × Digest)) (openings : List (List (List Bit)))
    (randomizer : Randomizer)
    (hrun : ∀ s : RealState C net.State, s.runs tree < runLimit →
      (secRunC K circuits settings D ⟨true, fun _ => runLimit⟩ net dealer emu tree answer).run s =
        (worldEmulatedRun K circuits settings D net emu openings randomizer tree).run s) :
    ∀ count, Rel1 prims D k fl emu
      (secRunsC K circuits settings runLimit D ⟨true, fun _ => runLimit⟩ net dealer emu tree answer count)
      (emulatedRunsW K circuits settings runLimit D net openings randomizer tree count)
  | 0 => Rel1.pure ()
  | count + 1 => by
    rw [secRunsC_succ K circuits settings runLimit net dealer tree answer count _ hrun]
    simp only [emulatedRunsW]
    refine Rel1.get_bind fun s _ => Rel1.ite Iff.rfl ?_ (Rel1.pure ())
    exact Rel1.bind (rel1_emulatedRun K circuits settings net openings randomizer tree) fun _ =>
      rel1_secRuns net dealer tree answer openings randomizer hrun count

/-! ## The signing phase -/

/-- `StateT.lift` as a monad map. -/
def stLiftHom (σ : Type) : OracleComp (WorldSpec C) →ᵐ RealM C σ where
  toFun _ x := StateT.lift x
  toFun_pure' a := by ext; simp [StateT.run_lift]
  toFun_bind' _ _ := by ext; simp [StateT.run_lift]

variable {net : Adversary C E Unit PEmpty PEmpty} {dealer : Dealt C (RealM C net.State)}
  {dealt : Dealt C (OracleComp (WorldSpec C))}

omit [Field E] [Algebra Bit E] in
theorem rel_tsig (hdl : dealer = SeedHitProof.Dealt.hmap (stLiftHom net.State) dealt) (q : TsigQuery C) :
    Rel prims D k fl emu id (tsigOracles realLift dealer q) (StateT.lift (worldTsig dealt q) : RedW C net.State _) := by
  have e : (tsigOracles realLift dealer q : StateT (TsigState C) (RealM C net.State) _) =
      StateT.mk fun st => StateT.lift ((tsigOracles (fun oa => SigningCoreProof.honestLift oa) dealt q).run st) := by
    refine StateT.ext fun st => ?_
    rw [StateT.run_mk]
    subst hdl
    exact (SeedHitProof.hom_tsigOracles (stLiftHom net.State) (fun oa => SigningCoreProof.honestLift oa) dealt q st).symm
  rw [e]
  exact Rel.liftT _

omit [Field E] [Algebra Bit E] in
theorem rel_signRequest (hdl : dealer = SeedHitProof.Dealt.hmap (stLiftHom net.State) dealt) (i : C.Party) (e : KeyIndex)
    (q : TsigQuery C) :
    Rel prims D k fl emu id (secSignRequest dealer i e q) (emulatedSignRequestW dealt i e q) := by
  unfold secSignRequest emulatedSignRequestW
  refine Rel.bind (Rel.modify fun s hs => ⟨rfl, hs⟩) fun _ => ?_
  refine Rel.get_bind fun s hs => ?_
  simp only [keysProj]
  cases (s.operators i).keys <;> cases (s.operators i).top <;> cases (s.operators i).bottom (treeOf e) <;>
    simp only [Option.map] <;> first | exact Rel.pure _ | exact rel_tsig hdl q

theorem rel_treeRequest (hdl : dealer = SeedHitProof.Dealt.hmap (stLiftHom net.State) dealt) (b : Fin (2 ^ layerHeight)) :
    Rel prims D k fl emu id
      (secTreeRequestC K circuits settings runLimit D ⟨true, fun _ => runLimit⟩ net dealer emu b)
      (emulatedTreeRequestW K circuits settings runLimit D dealt net b) := by
  unfold secTreeRequestC emulatedTreeRequestW
  refine Rel.bind (rel_tsig hdl (.tree b)) fun answer => ?_
  have hend : ∀ answer : Option (BottomTree × Digest), Rel prims D k fl emu id
      (StateT.lift (get : RealM C net.State _) >>= fun s =>
        match heldBottom D s.operators b, answer with
        | some tree, some (_, ρ) => (pure (some (tree, ρ)) : StateT (TsigState C) (RealM C net.State) _)
        | _, _ => pure none)
      ((get : RedW C net.State _) >>= fun s =>
        match heldBottom D s.operators b, answer with
        | some tree, some (_, ρ) => pure (some (tree, ρ))
        | _, _ => pure none) := fun answer => by
    refine Rel.get_bind fun s _ => ?_
    change Rel prims D k fl emu id (match heldBottom D s.operators b, answer with
        | some tree, some (_, ρ) => (pure (some (tree, ρ)) : StateT (TsigState C) (RealM C net.State) _)
        | _, _ => pure none) _
    split <;> exact Rel.pure _
  rcases answer with _ | ⟨bt, ρ⟩
  · simp only [id, Option.isSome_none, Bool.false_eq_true]
    simpa using hend none
  · have hruns := rel1_secRuns (prims := prims) (D := D) (k := k) (fl := fl) (emu := emu) K circuits settings runLimit net dealer
      (.bottom b) (some (bt, ρ)) (bottomLeak settings b bt ρ) bt.topSignature.randomizer
      (fun s h => by simp [secRunC, StateT.run_bind, h]) 1
    simp only [id, Option.isSome_some]
    exact Rel.bind hruns fun _ => hend (some (bt, ρ))

/-- The oracles of the signing phase of `givenAnswerGame`. -/
def answerOracles (D : C.Coalition) (emu : C.Party → Option (Keys C)) (A : DkgTsigAdversary C E)
    (dealer : Dealt C (RealM C A.net.State)) :
    QueryImpl (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) (StateT (TsigState C) (RealM C A.net.State)) :=
  let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) (RealM C A.net.State)) :=
    fun t => StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
  let cell : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (RealM C A.net.State)) := fun q =>
    match q with
    | .read => StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _))
    | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
  HAdd.hAdd forger (HAdd.hAdd (secOraclesC K circuits settings runLimit D ⟨true, fun _ => runLimit⟩ A.net dealer emu) cell)

theorem rel_oracles (A : DkgTsigAdversary C E) {dealer : Dealt C (RealM C A.net.State)}
    (hdl : dealer = SeedHitProof.Dealt.hmap (stLiftHom A.net.State) dealt) (t : (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Domain) :
    Rel prims D k fl emu id (answerOracles K circuits settings runLimit D emu A dealer t)
      (forgeOraclesW K circuits settings runLimit D dealt A.net t) := by
  rcases t with t | q | q
  · refine Rel.liftW fun log st => ?_
    rw [worldAdversaryCall_query, ← fst_observe, Functor.map_map, Functor.map_map]
  · simp only [answerOracles, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
    · dsimp only [forgeOraclesW, secOraclesC]
      exact Rel.pure _
    · exact rel_treeRequest K circuits settings runLimit hdl b
    · exact rel_signRequest hdl i e _
    · exact rel_signRequest hdl i e _
  · simp only [answerOracles, QueryImpl.add_apply_inr]
    rcases q with _ | state
    · dsimp only [forgeOraclesW]
      exact rel1_read
    · dsimp only [forgeOraclesW]
      exact Rel.modify fun s hs => ⟨rfl, hs⟩

omit [Field E] [Algebra Bit E] in
theorem topHolder_keysProj (s : RealState C σ) :
    (topHolder D (keysProj k fl s).operators).isSome = (topHolder D s.operators).isSome := by
  unfold topHolder keysProj
  dsimp only
  split <;> rename_i h
  · rename_i i
    have h' : C.parties.find? (fun i => i ∉ D.1 ∧ (s.operators i).top.isSome) = some i := h
    rw [h']
    dsimp only
    cases (s.operators i).keys <;> cases (s.operators i).top <;> rfl
  · have h' : C.parties.find? (fun i => i ∉ D.1 ∧ (s.operators i).top.isSome) = none := h
    rw [h']

/-- The rest of `givenAnswerGame` after the seed generation, on the state of the signing game. -/
def answerRest (D : C.Coalition) (emu : C.Party → Option (Keys C)) (A : DkgTsigAdversary C E) (dealer : Dealt C (RealM C A.net.State)) :
    StateT (TsigState C) (RealM C A.net.State) Bool := do
  StateT.lift (secRunsC K circuits settings runLimit D ⟨true, fun _ => runLimit⟩ A.net dealer emu .top none runLimit)
  let s ← StateT.lift (get : RealM C A.net.State _)
  match topHolder D s.operators with
  | none => pure false
  | some _ => do
    let forgery ← simulateQ (answerOracles K circuits settings runLimit D emu A dealer)
      (A.forge ⟨dealer.top.root, dealer.parameter⟩ dealer.top)
    let st ← get
    StateT.lift (forgeryWins realLift dealer st forgery)

/-- The rest of `forgerWorldGame` after the seed generation, with the win test inside and no win
with no top holder. -/
def forgerRest (D : C.Coalition) (A : DkgTsigAdversary C E) (dealt : Dealt C (OracleComp (WorldSpec C))) :
    RedW C A.net.State Bool := do
  emulatedRunsW K circuits settings runLimit D A.net (topLeak settings dealt.top) 0 .top runLimit
  let s ← get
  match topHolder D s.operators with
  | none => pure false
  | some _ => do
    let forgery ← simulateQ (forgeOraclesW K circuits settings runLimit D dealt A.net)
      (A.forge ⟨dealt.top.root, dealt.parameter⟩ dealt.top)
    let st ← (StateT.lift (StateT.lift get) : RedW C A.net.State (TsigState C))
    StateT.lift (toWorld (forgeryWins (fun oa => SigningCoreProof.honestLift oa) dealt st forgery))

theorem rel_answerRest (A : DkgTsigAdversary C E) {dealt : Dealt C (OracleComp (WorldSpec C))} :
    Rel prims D k fl emu id (answerRest K circuits settings runLimit D emu A
        (SeedHitProof.Dealt.hmap (stLiftHom A.net.State) dealt))
      (forgerRest K circuits settings runLimit D A dealt) := by
  unfold answerRest forgerRest
  have hruns := rel1_secRuns (prims := prims) (D := D) (k := k) (fl := fl) (emu := emu) K circuits settings
    runLimit A.net (SeedHitProof.Dealt.hmap (stLiftHom A.net.State) dealt) .top none (topLeak settings dealt.top) 0
    (fun s h => by simp [secRunC, StateT.run_bind, h]; rfl) runLimit
  refine Rel.bind hruns fun _ => Rel.get_bind fun s _ => ?_
  have hh := topHolder_keysProj (D := D) (k := k) (fl := fl) s
  cases h : topHolder D s.operators <;> cases h' : topHolder D (keysProj k fl s).operators <;>
    simp only [h, h', Option.isSome_none, Option.isSome_some, Bool.false_eq_true, Bool.true_eq_false] at hh
  · exact Rel.pure false
  · refine Rel.bind (Rel.simulateQ (rel_oracles K circuits settings runLimit A rfl) _) fun forgery => ?_
    have hget : (get : StateT (TsigState C) (RealM C A.net.State) (TsigState C)) =
        StateT.mk fun st => StateT.lift ((get : StateT (TsigState C) (OracleComp (WorldSpec C)) _).run st) := by
      ext st; simp [StateT.run_lift]
    rw [hget]
    refine Rel.bind (Rel.liftT _) fun st => ?_
    have hwin : (StateT.lift (forgeryWins realLift (SeedHitProof.Dealt.hmap (stLiftHom A.net.State) dealt) st forgery) :
        StateT (TsigState C) (RealM C A.net.State) Bool) =
        StateT.lift (StateT.lift (forgeryWins (fun oa => SigningCoreProof.honestLift oa) dealt st forgery)) := by
      exact congrArg StateT.lift
        (hom_forgeryWins (stLiftHom A.net.State) (fun oa => SigningCoreProof.honestLift oa) dealt st forgery).symm
    simp only [id]
    rw [hwin]
    exact Rel.liftW fun log st' => by simp [toWorld, StateT.run_lift]

theorem secRestC_eq (A : DkgTsigAdversary C E) (dealer : Dealt C (RealM C A.net.State)) :
    secRestC K circuits settings runLimit D ⟨true, fun _ => runLimit⟩ A dealer emu =
      Prod.fst <$> (answerRest K circuits settings runLimit D emu A dealer).run ⟨D.1, fun _ => none, [], fun _ => none⟩ := by
  unfold secRestC secSigningC answerRest answerOracles
  simp only [StateT.run_bind, StateT.run_lift, map_bind, bind_assoc, pure_bind]
  refine bind_congr fun _ => bind_congr fun s => ?_
  rcases h : topHolder D s.operators with _ | holder
  · simp
  · simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, map_bind, pure_bind, map_pure,
      bind_pure]
    rfl

end Runs

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.rel_answerRest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.rel_answerRest
