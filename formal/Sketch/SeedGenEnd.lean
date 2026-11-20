import Sketch.TopRuns

/-!
# The start cache after the honest seed generation

`seedGenEnd` proves `SeedGenEnd`. The honest seed generation makes no query of a coin key or of an
expansion, so from the empty cache it ends in a cache with `StartInvariant`. `topRunsHop` is then
`TopRunsHop` with no premise.

`SafeProg` is the property of a program of an operator that every local query on every path is no
coin query. `advance_safe` and `honestRounds_safe` carry `StartInvariant` through the honest network
for programs with this property.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmss.Sketch

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## Programs with no coin query -/

/-- A query of the local oracles that is no coin key and no expansion. -/
def LocalSafe : (LocalSpec C).Domain → Prop
  | .inl _ => True
  | .inr (.inl q) => ¬ IsCoin q
  | .inr (.inr _) => True

/-- A query of the program of an operator whose local part is `LocalSafe`. -/
def PartySafe {ι : Type} {G : OracleSpec ι} : (PartySpec C E G).Domain → Prop
  | .inl (.inl t) => LocalSafe t
  | _ => True

/-- A program of an operator that makes no coin query on any path. -/
def SafeProg {ι : Type} {G : OracleSpec ι} {α : Type} (p : OracleComp (PartySpec C E G) α) : Prop :=
  AllQueriesSatisfy p (PartySafe (C := C) (E := E) (G := G))

/-- A step whose continuation makes no coin query on any path. -/
def StepSafe {ι : Type} {G : OracleSpec ι} {α : Type} : Step C E G α → Prop
  | .done _ => True
  | .wait _ k => ∀ m, SafeProg (k m)
  | .call _ k => ∀ r, SafeProg (k r)

/-- A local query that is no coin query keeps `StartInvariant`. -/
theorem localAnswer_startInvariant (prims : Primitives) (t : (LocalSpec C).Domain) (ht : LocalSafe t)
    (s : HashCache C) (hs : StartInvariant s) (z : (LocalSpec C).Range t × HashCache C)
    (hz : z ∈ support ((localAnswer prims t).run s)) : StartInvariant z.2 := by
  refine ⟨(localAnswer_support (prims := prims) (fun _ => 0) t s z hz).2.1 hs.1, cacheOK_of_frame hs.2 ?_⟩
  rcases t with n | q | x
  · change z ∈ support ((unifFwdImpl (Query C →ₒ HashOutput) n).run s) at hz
    simp [unifFwdImpl] at hz
    obtain ⟨a, rfl⟩ := hz
    exact fun _ _ => rfl
  · have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (ThresholdLeanXmss.hashQuery q) =
        hashAnswer prims q := (simulateQ_query _ _).trans (id_map _)
    exact FrameR.hashQuery (prims := prims) ht s z (by rw [h1]; exact hz)
  · have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
        (query (spec := RoSpec C) (.inr x) : OracleComp (RoSpec C) Bit) = prgAnswer prims x :=
      (simulateQ_query _ _).trans (id_map _)
    exact FrameR.prg (prims := prims) x s z (by rw [h1]; exact hz)

/-- `advance` of a program with no coin query keeps `StartInvariant` and stops at a step whose
continuation makes no coin query. -/
theorem advance_safe (prims : Primitives) {ι : Type} {G : OracleSpec ι} {α : Type}
    (p : OracleComp (PartySpec C E G) (Option α)) (hp : SafeProg p) :
    ∀ (s : HashCache C) (z : Step C E G α × HashCache C), StartInvariant s →
      z ∈ support ((simulateQ (localAnswer prims) (advance p)).run s) → StartInvariant z.2 ∧ StepSafe z.1 := by
  induction p using OracleComp.inductionOn with
  | pure x =>
    intro s z hs hz
    change z ∈ support ((simulateQ (localAnswer prims) (pure (Step.done x))).run s) at hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hs, trivial⟩
  | query_bind t k ih =>
    intro s z hs hz
    rw [SafeProg, allQueriesSatisfy_query_bind_iff] at hp
    rcases t with (t | outbox) | input
    · change z ∈ support ((simulateQ (localAnswer prims)
        (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t) >>= fun r => advance (k r))).run s) at hz
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      have hy' : y ∈ support ((localAnswer prims t).run s) := by
        simpa [simulateQ_query] using hy
      exact ih y.1 (hp.2 y.1) y.2 z (localAnswer_startInvariant prims t hp.1 s hs y hy') hz
    · change z ∈ support ((simulateQ (localAnswer prims) (pure (Step.wait outbox k))).run s) at hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hs, hp.2⟩
    · change z ∈ support ((simulateQ (localAnswer prims) (pure (Step.call input k))).run s) at hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hs, hp.2⟩

/-- Local computations that keep an invariant and give results with a property, in sequence. -/
theorem sequenceFin_inv (prims : Primitives) {β : Type} (Inv : HashCache C → Prop) (Q : β → Prop) :
    ∀ {n : ℕ} (f : Fin n → OracleComp (LocalSpec C) β),
      (∀ i s z, Inv s → z ∈ support ((simulateQ (localAnswer prims) (f i)).run s) → Inv z.2 ∧ Q z.1) →
      ∀ s z, Inv s → z ∈ support ((simulateQ (localAnswer prims) (OverPermutation.sequenceFin f)).run s) →
        Inv z.2 ∧ ∀ i, Q (z.1 i)
  | 0, f, _, s, z, hs, hz => by
    simp only [OverPermutation.sequenceFin, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hs, fun i => i.elim0⟩
  | n + 1, f, hf, s, z, hs, hz => by
    simp only [OverPermutation.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, w, hw, rfl⟩ := hz
    obtain ⟨hy1, hy2⟩ := hf 0 s y hs hy
    obtain ⟨hw1, hw2⟩ := sequenceFin_inv prims Inv Q (fun i : Fin n => f i.succ) (fun i => hf i.succ) y.2 w hy1 hw
    refine ⟨hw1, fun i => ?_⟩
    cases i using Fin.cases with
    | zero => exact hy2
    | succ i => exact hw2 i

/-- One honest step of programs with no coin query keeps `StartInvariant`, and the next steps make no
coin query. -/
theorem honestStep_safe (prims : Primitives) {α : Type} (reply : PEmpty → PEmpty)
    (steps : C.Party → Step C E RealSpec α) (hsteps : ∀ i, StepSafe (steps i)) (s : HashCache C)
    (z : (C.Party → Step C E RealSpec α) × HashCache C) (hs : StartInvariant s)
    (hz : z ∈ support ((simulateQ (localAnswer prims) (honestStep noFunctionality reply steps)).run s)) :
    StartInvariant z.2 ∧ ∀ i, StepSafe (z.1 i) := by
  unfold honestStep at hz
  split_ifs at hz with hcall
  · obtain ⟨⟨i, hi⟩, -⟩ := hcall
    revert hi
    cases steps i with
    | done _ => simp [Step.callInput]
    | wait _ _ => simp [Step.callInput]
    | call input _ => exact input.elim
  · refine sequenceFin_inv prims StartInvariant StepSafe _ (fun j s' z' hs' hz' => ?_) s z hs hz
    have hj := hsteps j
    split at hz'
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz'
      subst hz'
      exact ⟨hs', trivial⟩
    · rename_i heq
      rw [heq] at hj
      exact advance_safe prims _ (hj _) s' z' hs' hz'
    · rename_i input _ _
      exact input.elim

/-- The honest rounds of programs with no coin query keep `StartInvariant`. -/
theorem honestRounds_safe (prims : Primitives) {α : Type} (reply : PEmpty → PEmpty) :
    ∀ (fuel : ℕ) (steps : C.Party → Step C E RealSpec α), (∀ i, StepSafe (steps i)) →
      ∀ s z, StartInvariant s →
        z ∈ support ((simulateQ (localAnswer prims) (honestRounds noFunctionality reply fuel steps)).run s) →
          StartInvariant z.2
  | 0, steps, _, s, z, hs, hz => by
    simp only [honestRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hs
  | fuel + 1, steps, hsteps, s, z, hs, hz => by
    unfold honestRounds at hz
    split_ifs at hz
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs
    · rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      obtain ⟨hy1, hy2⟩ := honestStep_safe prims reply steps hsteps s y hs hy
      exact honestRounds_safe prims reply fuel y.1 hy2 y.2 z hy1 hz

/-! ## The programs of the seed generation -/

/-- A query of `H` and `PRG` that is no coin query. -/
def RoSafe : (RoSpec C).Domain → Prop
  | .inl q => ¬ IsCoin q
  | .inr _ => True

/-- A program of an operator with no coin query on any path, as a program of `PartyM`. -/
def SafeM {ι : Type} {G : OracleSpec ι} {α : Type} (x : PartyM C E G α) : Prop := SafeProg x.run

theorem liftComp_local_safe {ι : Type} {G : OracleSpec ι} {β : Type} (oa : OracleComp (LocalSpec C) β)
    (h : AllQueriesSatisfy oa LocalSafe) :
    SafeProg (E := E) (liftComp oa (PartySpec C E G)) := by
  refine AllQueriesSatisfy.simulateQ h fun t ht => ?_
  rw [liftM_query_local]
  exact (allQueriesSatisfy_query_iff (spec := PartySpec C E G) (.inl (.inl t)) _).2 ht

theorem liftComp_ro_safe {β : Type} (oa : OracleComp (RoSpec C) β) (h : AllQueriesSatisfy oa RoSafe) :
    AllQueriesSatisfy (liftComp oa (LocalSpec C)) LocalSafe := by
  refine AllQueriesSatisfy.simulateQ h fun t ht => ?_
  rcases t with q | x
  · exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inr (.inl q)) _).2 ht
  · exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inr (.inr x)) _).2 trivial

theorem liftComp_prob_safe {β : Type} (oa : ProbComp β) :
    AllQueriesSatisfy (liftComp oa (LocalSpec C)) LocalSafe := by
  refine AllQueriesSatisfy.simulateQ (allQueriesSatisfy_of_forall (P := fun _ => True) (fun _ => trivial) oa)
    fun t _ => ?_
  exact (allQueriesSatisfy_query_iff (spec := LocalSpec C) (.inl t) _).2 trivial

section SafeM

variable {ι : Type} {G : OracleSpec ι}

theorem SafeM.pure {α : Type} (a : α) : SafeM (C := C) (E := E) (G := G) (Pure.pure a : PartyM C E G α) := by
  unfold SafeM SafeProg
  rw [OptionT.run_pure]
  exact allQueriesSatisfy_pure _ _

theorem SafeM.failure {α : Type} : SafeM (C := C) (E := E) (G := G) (Alternative.failure : PartyM C E G α) := by
  unfold SafeM SafeProg
  rw [OptionT.run_failure]
  exact allQueriesSatisfy_pure _ _

theorem SafeM.bind {α β : Type} {x : PartyM C E G α} {f : α → PartyM C E G β} (hx : SafeM x)
    (hf : ∀ a, SafeM (f a)) : SafeM (x >>= f) := by
  unfold SafeM SafeProg at *
  rw [OptionT.run_bind]
  refine allQueriesSatisfy_bind hx fun o => ?_
  cases o with
  | none => exact allQueriesSatisfy_pure _ _
  | some a => exact hf a

theorem SafeM.localStep {β : Type} {oa : OracleComp (LocalSpec C) β} (h : AllQueriesSatisfy oa LocalSafe) :
    SafeM (C := C) (E := E) (G := G) (localStep oa) := by
  unfold SafeM SafeProg ThresholdLeanXmss.localStep
  simp only [OptionT.run_lift]
  exact allQueriesSatisfy_bind (liftComp_local_safe oa h) fun _ => allQueriesSatisfy_pure _ _

theorem SafeM.oracleStep {β : Type} {oa : OracleComp (RoSpec C) β} (h : AllQueriesSatisfy oa RoSafe) :
    SafeM (C := C) (E := E) (G := G) (oracleStep oa) :=
  SafeM.localStep (liftComp_ro_safe oa h)

theorem SafeM.exchange (outbox : Mail C E) : SafeM (C := C) (E := E) (G := G) (exchange outbox) := by
  unfold SafeM SafeProg ThresholdLeanXmss.exchange
  simp only [OptionT.run_bind, OptionT.run_lift]
  refine allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff (spec := PartySpec C E G) (.inl (.inr outbox)) _).2
    trivial) fun inbox => ?_
  rcases inbox with _ | x
  · exact allQueriesSatisfy_pure _ _
  · dsimp only [Option.elim]
    split_ifs
    exacts [SafeM.failure (C := C) (E := E) (G := G) (α := Mail C E), SafeM.pure (C := C) (E := E) (G := G) x]

theorem SafeM.require (c : Prop) : SafeM (C := C) (E := E) (G := G) (require c) := by
  unfold ThresholdLeanXmss.require
  split_ifs
  · exact SafeM.pure _
  · exact SafeM.failure

end SafeM

theorem mapM_safe {ι : Type} {spec : OracleSpec ι} {α β : Type} (P : ι → Prop) (f : α → OracleComp spec β)
    (hf : ∀ a, AllQueriesSatisfy (f a) P) : ∀ l : List α, AllQueriesSatisfy (l.mapM f) P
  | [] => allQueriesSatisfy_pure _ _
  | a :: l => by
    rw [List.mapM_cons]
    exact allQueriesSatisfy_bind (hf a) fun _ =>
      allQueriesSatisfy_bind (mapM_safe P f hf l) fun _ => allQueriesSatisfy_pure _ _

theorem hashQuery_safe {q : Query C} (hq : ¬ IsCoin q) : AllQueriesSatisfy (ThresholdLeanXmss.hashQuery q) RoSafe :=
  (allQueriesSatisfy_query_iff (spec := RoSpec C) (.inl q) _).2 hq

theorem deriveKeys_safe (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    AllQueriesSatisfy (deriveKeys phase i view) RoSafe := by
  unfold ThresholdLeanXmss.deriveKeys
  have hq : ∀ (k : KeyKind) (l : List HashOutput),
      AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.derive phase k l)) RoSafe :=
    fun _ _ => hashQuery_safe (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h)
  have hrest : ∀ parameter : HashOutput, AllQueriesSatisfy (do
      let term ← C.terms.mapM fun T => if i ∈ C.holders T then
        ThresholdLeanXmss.hashQuery (C := C)
          (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T))
        else Pure.pure 0
      let pair ← C.parties.mapM fun j => if h : j = i then Pure.pure 0 else
        let p := C.pairOf i j (Ne.symm h)
        ThresholdLeanXmss.hashQuery (C := C) (.derive phase .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1])
      Pure.pure (parameter, fun T => term.getD (C.terms.idxOf T) 0, fun (j : C.Party) => pair.getD j.val 0))
      RoSafe := fun parameter =>
    allQueriesSatisfy_bind (mapM_safe _ _ (fun T => by split_ifs; exacts [hq _ _, allQueriesSatisfy_pure _ _]) _)
      fun _ => allQueriesSatisfy_bind
        (mapM_safe _ _ (fun j => by split_ifs; exacts [allQueriesSatisfy_pure _ _, hq _ _]) _)
        fun _ => allQueriesSatisfy_pure _ _
  split_ifs
  · exact allQueriesSatisfy_bind (hq _ _) hrest
  · exact allQueriesSatisfy_bind (allQueriesSatisfy_pure _ _) hrest

theorem commitRevealEcho_safe {ι : Type} {G : OracleSpec ι} (phase : Phase) (i : C.Party) (own : Parts C) :
    SafeM (C := C) (E := E) (G := G) (commitRevealEcho phase i own) := by
  have hc : ∀ a b l, AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.commit phase a b l)) RoSafe :=
    fun _ _ _ => hashQuery_safe (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h)
  have hs : ∀ l, AllQueriesSatisfy (ThresholdLeanXmss.hashQuery (C := C) (.sharedKeys phase l)) RoSafe :=
    fun _ => hashQuery_safe (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h)
  unfold commitRevealEcho
  refine SafeM.bind (SafeM.oracleStep (mapM_safe _ _ (fun _ => hc _ _ _) _)) fun commitments => ?_
  refine SafeM.bind (SafeM.exchange _) fun committed => ?_
  refine SafeM.bind (SafeM.exchange _) fun revealed => ?_
  refine SafeM.bind (SafeM.oracleStep (mapM_safe _ _ (fun _ => hc _ _ _) _)) fun opens => ?_
  refine SafeM.bind (SafeM.require _) fun _ => ?_
  refine SafeM.bind (SafeM.oracleStep (deriveKeys_safe _ _ _)) fun keys => ?_
  refine SafeM.bind (SafeM.oracleStep (mapM_safe _ _ (fun _ => hs _) _)) fun shared => ?_
  refine SafeM.bind (SafeM.exchange _) fun received => ?_
  refine SafeM.bind (SafeM.require _) fun _ => ?_
  exact SafeM.pure _

theorem seedGen_safe (i : C.Party) : SafeProg (seedGen (E := E) (G := RealSpec) i).run := by
  change SafeM (seedGen (E := E) (G := RealSpec) i)
  unfold seedGen seedGenWith
  refine SafeM.bind (SafeM.localStep (liftComp_prob_safe _)) fun own => ?_
  refine SafeM.bind (commitRevealEcho_safe _ _ _) fun keys => ?_
  exact SafeM.pure _

/-! ## The start cache and the top hop -/

section Hop

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The honest seed generation from the empty cache ends in a cache with `StartInvariant`. -/
theorem seedGenEnd (prims : Primitives) : SeedGenEnd (C := C) (E := E) prims := by
  intro z hz
  unfold honestStart at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  obtain ⟨hy1, hy2⟩ := sequenceFin_inv prims StartInvariant StepSafe _
    (fun i s w hs hw => advance_safe prims _ (seedGen_safe i) s w hs hw) ∅ y ⟨noMpc_empty, cacheOK_empty⟩ hy
  exact honestRounds_safe prims _ setupRounds y.1 hy2 y.2 z hy1 hz

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- Hop C5a holds. -/
theorem topRunsHop : TopRunsHop K circuits settings runLimit :=
  topRunsHop_of_seedGenEnd K circuits settings runLimit seedGenEnd

end Hop

/-- info: 'ThresholdLeanXmss.Sketch.topRunsHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms topRunsHop

end ThresholdLeanXmss.Sketch
