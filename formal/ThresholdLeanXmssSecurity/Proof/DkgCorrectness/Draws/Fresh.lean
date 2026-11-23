import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Draws.OneKey
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.RecordedRun
import ThresholdLeanXmssSecurity.Proof.SeedGen
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.BatchRecords

/-!
# The fresh part of one ceremony

`ghostFix` is the ghost run of one ceremony in which the designated contributor `h` of a hidden name
runs its PRSS setup with the fixed parts `own` in the place of its own draw. The designated
contributor of a term is its first holder, and of a pair its first end. `FreshFixed` states that the
ghost run with fixed parts has no outcome where an honest operator holds an old derived key under
the hidden name with no global event, when the coordinate of `own` in the derive input of the name
differs from the first coordinate of the old derive input. `freshOne_of_fixed` proves `FreshOne` from
`FreshFixed`. The ghost run is the draw of the parts of `h` and then the ghost run with these parts,
so the probability is at most the probability that one uniform coordinate takes one fixed value.
`freshFixed` proves `FreshFixed` from the trace of the commit round and the reveal round of the ghost
run, and `freshOne` is the leaf.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The designated contributor -/

/-- The designated contributor of a name, the first holder of a term or the first end of a pair. -/
def designated : KeyName C → Option C.Party
  | .parameter => none
  | .term T => (C.parties.filter (· ∈ C.holders T)).head?
  | .pair p => some p.1.1

/-- The coordinate of the parts `own` of the designated contributor in the derive input of a name. -/
def coordOf : KeyName C → Parts C → HashOutput
  | .parameter, own => own.parameter
  | .term T, own => own.term T
  | .pair p, own => own.pair p.1.2

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-! ## The ghost run with fixed parts -/

/-- `recRun` with the parts `own` in the place of the draw of the PRSS setup. -/
def recRunWith (i : C.Party) (keys : Keys C) (jobs : List Job) (own : Parts C) :
    StateT (ℕ × ℕ) (RecM C E) (Option (List (List Bit))) := do
  let prss ← RecM.liftS (StateT.lift (prssSetupWith i own))
  batched settings.batchSize (recBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter) jobs

/-- `recCeremony` with the parts `own` in the place of the draw of the PRSS setup. -/
def recCeremonyWith (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (own : Parts C) : RecM C E CeremonyResult :=
  match c.keys i with
  | some keys => (recRunWith K circuits settings i keys c.jobs own).run c.counters >>= fun p =>
      p.1.elim failure fun outputs => pure (outputs, p.2)
  | none => failure

/-- The ghost run of one ceremony where operator `h` runs its PRSS setup with the parts `own`. -/
def ghostFix (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (h : C.Party) (own : Parts C) :
    StateT (StreamState C) ProbComp (net.State × CeremonySteps C E) :=
  simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality ([] : Record C E) rounds
    c.adversary fun i => if i = h then (recCeremonyWith K circuits settings i c own).run.run
      else (recCeremony K circuits settings i c).run.run)

/-- The fixed part. In the ghost run where the designated contributor `h` of a hidden name runs its
setup with the parts `own`, no honest operator holds the key `key` under that name with no global
event, when `key` has the old derive cell `(kind, parts)` and the coordinate of `own` in the derive
input of the name differs from the first coordinate of `parts`. -/
def FreshFixed : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (name : KeyName C) (key : HashOutput)
    (h : C.Party) (kind : KeyKind) (parts : List HashOutput),
    Hidden D name → designated name = some h → world.1 (.derive .prss kind parts) = some key →
    ∀ own, coordOf name own ≠ parts.getD 0 0 →
      ∀ ω ∈ support ((ghostFix prims K circuits settings D net rounds c h own).run world),
        ¬ (UsesKey D name key ω.1.2 ∧ ¬ GlobalEvent ω.2)

/-! ## The draw of the designated contributor comes first -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem recM_lift_bind {α β : Type} (x : PartyM C E RealSpec α) (g : α → PartyM C E RealSpec β) :
    RecM.lift (x >>= g) = RecM.lift x >>= fun a => RecM.lift (g a) := by
  apply OptionT.ext
  simp only [RecM.lift, OptionT.run_mk, OptionT.run_bind, Option.elimM, WriterT.liftM_def', WriterT.bind_def',
    WriterT.run_mk, map_bind, bind_map_left]
  refine bind_congr fun o => ?_
  cases o with
  | none => rfl
  | some a =>
    show _ = (Prod.map id fun x => x) <$> ((fun x => (x, [])) <$> OptionT.run (g a))
    rw [Functor.map_map]
    rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem recM_lift_pure {α : Type} (a : α) : RecM.lift (pure a : PartyM C E RealSpec α) = pure a := rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem liftS_lift_bind {S α β : Type} (x : PartyM C E RealSpec α) (g : α → PartyM C E RealSpec β) :
    RecM.liftS (StateT.lift (x >>= g) : StateT S (PartyM C E RealSpec) β) =
      RecM.liftS (StateT.lift x) >>= fun a => RecM.liftS (StateT.lift (g a)) := by
  apply StateT.ext
  intro s
  simp only [RecM.liftS, StateT.run_mk, StateT.run_bind, StateT.run_lift, bind_assoc, recM_lift_bind,
    recM_lift_pure, pure_bind]

omit [Fintype E] [DecidableEq E] in
theorem recRun_eq_sample (i : C.Party) (keys : Keys C) (jobs : List Job) :
    recRun K circuits settings i keys jobs =
      RecM.liftS (StateT.lift (localStep (liftComp sampleParts _))) >>= fun own =>
        recRunWith K circuits settings i keys jobs own := by
  unfold recRun recRunWith
  rw [show (prssSetup i : PartyM C E RealSpec (PrssKeys C)) =
    localStep (liftComp sampleParts _) >>= fun own => prssSetupWith i own from rfl, liftS_lift_bind, bind_assoc]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem recM_run_localStep_bind {α β : Type} (oa : OracleComp (LocalSpec C) α) (G : α → RecM C E β) :
    (RecM.lift (localStep oa) >>= G).run.run = liftComp oa (PartySpec C E RealSpec) >>= fun a => (G a).run.run := by
  simp [RecM.lift, localStep, OptionT.run_bind, OptionT.lift, Option.elimM, WriterT.liftM_def', WriterT.bind_def']
  refine bind_congr fun a => ?_
  have e : (Prod.map id fun x => x : Option β × List (RecEvent C E) → Option β × List (RecEvent C E)) = id :=
    funext fun _ => rfl
  rw [e]
  exact id_map ((G a).run.run)

omit [Fintype E] [DecidableEq E] in
theorem recCeremony_run (h : C.Party) {σ : Type} (c : CeremonyStart C σ) (keys : Keys C) (hk : c.keys h = some keys) :
    (recCeremony K circuits settings h c).run.run =
      liftComp (liftComp sampleParts (LocalSpec C)) (PartySpec C E RealSpec) >>= fun own =>
        (recCeremonyWith K circuits settings h c own).run.run := by
  simp only [recCeremony, recCeremonyWith, hk]
  rw [recRun_eq_sample]
  simp only [StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift, bind_assoc, recM_lift_bind,
    recM_lift_pure, pure_bind]
  rw [recM_run_localStep_bind]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem advanceR_liftComp_bind {α β ρ : Type} (oa : OracleComp (LocalSpec C) β)
    (f : β → OracleComp (PartySpec C E RealSpec) (Option α × ρ)) :
    advanceR (liftComp oa (PartySpec C E RealSpec) >>= f) = oa >>= fun b => advanceR (f b) := by
  induction oa using OracleComp.inductionOn with
  | pure b => simp
  | query_bind t k ih =>
    simp only [liftComp_bind, liftComp_query, bind_assoc]
    have hq : ((OracleSpec.query t).cont <$> liftM (OracleSpec.query (OracleSpec.query t).input) :
        OracleComp (PartySpec C E RealSpec) _) =
        OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (Sum.inl (Sum.inl t))) := by
      rw [← liftM_query_local]; rfl
    rw [hq]
    change advanceR (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (Sum.inl (Sum.inl t))) >>=
      fun x => (k x).liftComp (PartySpec C E RealSpec) >>= f) = _
    refine (rfl : _ = OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t) >>= fun r =>
      advanceR ((k r).liftComp (PartySpec C E RealSpec) >>= f)).trans ?_
    simp only [ih]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A sequence with a draw at index `h` is a prefix, the draw and a rest. The same sequence with the
computation at `h` fixed to a continuation `r u` of the draw is the prefix and the rest at `u`. -/
theorem sequenceFin_split {m : Type → Type} [Monad m] [LawfulMonad m] {β U γ : Type} :
    ∀ {n : ℕ} (f : Fin n → m β) (h : Fin n) (S : m U) (r : U → m β), f h = S >>= r →
      ∀ g : (Fin n → β) → m γ, ∃ (Y : m (List β)) (Z : List β → U → m γ),
        (OverPermutation.sequenceFin f >>= g = Y >>= fun y => S >>= Z y) ∧
          ∀ u, OverPermutation.sequenceFin (Function.update f h (r u)) >>= g = Y >>= fun y => Z y u
  | 0, _, h, _, _, _, _ => h.elim0
  | n + 1, f, h, S, r, hf, g => by
    cases h using Fin.cases with
    | zero =>
      refine ⟨pure [], fun _ u => r u >>= fun a => OverPermutation.sequenceFin (fun i : Fin n => f i.succ) >>=
        fun as => g (Fin.cases a as), ?_, fun u => ?_⟩
      · simp only [OverPermutation.sequenceFin, hf, bind_assoc, pure_bind]
      · have hs : (fun i : Fin n => Function.update f 0 (r u) i.succ) = fun i : Fin n => f i.succ :=
          funext fun i => Function.update_of_ne (Fin.succ_ne_zero i) _ _
        simp only [OverPermutation.sequenceFin, bind_assoc, pure_bind, Function.update_self, hs]
    | succ h' =>
      have ih := fun a => sequenceFin_split (fun i : Fin n => f i.succ) h' S r hf
        (fun as => g (Fin.cases a as))
      choose Y Z hY using ih
      refine ⟨f 0 >>= fun a => Y a >>= fun ys => pure (a :: ys), fun l u => match l with
        | a :: ys => Z a ys u
        | [] => f 0 >>= fun a => Z a [] u, ?_, fun u => ?_⟩
      · simp only [OverPermutation.sequenceFin, bind_assoc, pure_bind]
        refine bind_congr fun a => ?_
        exact (hY a).1
      · have h0 : Function.update f h'.succ (r u) 0 = f 0 := Function.update_of_ne (Fin.succ_ne_zero h').symm _ _
        have hs : (fun i : Fin n => Function.update f h'.succ (r u) i.succ) =
            Function.update (fun i : Fin n => f i.succ) h' (r u) := by
          funext i
          by_cases hi : i = h'
          · subst hi
            simp
          · rw [Function.update_of_ne (fun h => hi (Fin.succ_injective _ h)), Function.update_of_ne hi]
        simp only [OverPermutation.sequenceFin, bind_assoc, pure_bind, h0, hs]
        refine bind_congr fun a => ?_
        exact (hY a).2 u

/-! ## The probability of one fixed coordinate -/

variable (D : C.Coalition)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem streamWorld_inr_inl (t : unifSpec.Domain) (s : StreamState C) :
    (simulateQ (streamWorld prims D) (liftM ((WorldSpec C).query (.inr (.inl t))) : OracleComp (WorldSpec C) _)).run s =
      (fun a => (a, s)) <$> (liftM (unifSpec.query t) : ProbComp _) := by
  rw [simulateQ_query]
  simp [streamWorld, localAnswer, unifFwdImpl, onHash]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation of the stream world that only draws keeps the world. -/
theorem streamWorld_free_liftComp {α : Type} (p : ProbComp α) (s : StreamState C) :
    (simulateQ (streamWorld prims D) (free (C := C) (liftComp p (LocalSpec C)))).run s = (fun a => (a, s)) <$> p := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t oa ih =>
    rw [liftComp_bind, free_bind, simulateQ_bind, free_liftComp_query, StateT.run_bind, streamWorld_inr_inl]
    simp only [bind_map_left, ih, map_bind]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- One coordinate of the parts of one operator is uniform, when a shift of that coordinate shifts
`X`. -/
theorem probEvent_sampleParts_shift (X : Parts C → HashOutput) (term : Option C.Term) (pair : Option C.Party)
    (hX : ∀ c own, X (shiftParts own term pair c) = X own ^^^ c) (v : HashOutput) :
    Pr{let own ← sampleParts (C := C)}[X own = v] = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have huniform : ((fun own => X own ^^^ v) <$> sampleParts (C := C)) =ᵈ $ᵗ HashOutput := by
    refine evalDist_eq_uniform_of_probOutput_eq _ fun u w => ?_
    have hshift : ((fun own => X own ^^^ v) <$> sampleParts (C := C)) =ᵈ
        ((fun d => d ^^^ (u ^^^ w)) <$> ((fun own => X own ^^^ v) <$> sampleParts (C := C))) :=
      calc ((fun own => X own ^^^ v) <$> sampleParts (C := C) : ProbComp HashOutput)
          =ᵈ ((fun own => X own ^^^ v) <$> ((fun own => shiftParts own term pair (u ^^^ w)) <$>
              sampleParts (C := C)) : ProbComp HashOutput) :=
            ((evalDist_shift_sampleParts term pair (u ^^^ w)).map _).symm
        _ = _ := by
            rw [Functor.map_map, Functor.map_map]
            congr 2
            funext own
            simp only [hX, BitVec.xor_assoc, BitVec.xor_comm (u ^^^ w) v]
    have hu : u = w ^^^ (u ^^^ w) := by
      rw [BitVec.xor_comm u w, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    have key := prEvent_map_injective ((fun own => X own ^^^ v) <$> sampleParts (C := C))
      (xor_bijective (u ^^^ w)).1 w
    rw [← hu] at key
    exact (hshift.prEvent_eq _).trans key
  have : Pr{let own ← sampleParts (C := C)}[X own = v] =
      Pr{let z ← (fun own => X own ^^^ v) <$> sampleParts (C := C)}[z = 0] := by
    rw [prEvent_map]
    exact prEvent_congr _ _ _ fun own => BitVec.xor_eq_zero_iff.symm
  rw [this, huniform.prEvent_eq, SampleableType.prEvent_uniformSample_eq_singleton]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A draw followed by a computation. The event has probability at most the probability of `Bad` on
the draw, when no outcome after a draw that is not bad has the event. -/
theorem probEvent_draw_le {X σ U Y : Type} (mA : ProbComp (X × σ)) (p : ProbComp U)
    (B : X → U → σ → ProbComp Y) (ev : Y → Prop) (Bad : U → Prop)
    (hB : ∀ xs ∈ support mA, ∀ u, ¬ Bad u → ∀ z ∈ support (B xs.1 u xs.2), ¬ ev z) :
    Pr{let z ← mA >>= fun xs => p >>= fun u => B xs.1 u xs.2}[ev z] ≤ Pr{let u ← p}[Bad u] := by
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun xs hxs => ?_
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_eq_tsum_ite]
  refine tsum_le_tsum fun u => ?_
  by_cases hb : Bad u
  · simp only [hb, ↓reduceIte]
    exact mul_le_of_le_one_right' (prEvent_le_one _)
  · simp only [hb, ↓reduceIte]
    rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hz' => hB xs hxs u hb z hz hz', mul_zero]

/-! ## The glue -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The designated contributor of a hidden name is honest. -/
theorem designated_honest {D : C.Coalition} {name : KeyName C} {h : C.Party} (hN : Hidden D name)
    (hh : designated name = some h) : h ∉ D.1 := by
  cases name with
  | parameter => exact hN.elim
  | term T =>
    have hmem := List.mem_of_mem_head? hh
    have hhT : h ∈ C.holders T := by simpa using (List.mem_filter.1 hmem).2
    exact fun hD => hN ⟨h, hD, hhT⟩
  | pair p =>
    simp only [designated, Option.some.injEq] at hh
    subst hh
    exact hN.1

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A shift of the coordinate of a name shifts `coordOf`. -/
theorem coordOf_shift {D : C.Coalition} {name : KeyName C} (hN : Hidden D name) :
    ∃ term pair, ∀ c own, coordOf name (shiftParts own term pair c) = coordOf name own ^^^ c := by
  cases name with
  | parameter => exact hN.elim
  | term T => exact ⟨some T, none, fun c own => by simp [coordOf, shiftParts]⟩
  | pair p => exact ⟨none, some p.1.2, fun c own => by simp [coordOf, shiftParts]⟩

omit [Fintype E] [DecidableEq E] in
/-- `FreshOne` from `FreshFixed`. The ghost run is the draw of the parts of the designated contributor
and then the ghost run with fixed parts. -/
theorem freshOne_of_fixed (hfix : FreshFixed prims K circuits settings) : FreshOne prims K circuits settings := by
  intro D net rounds c world name key hN ⟨kind, parts, hcell⟩
  rcases hdes : designated name with _ | h
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun ω _ hω => ?_) zero_le
    obtain ⟨⟨i, -, b, -, hk⟩, -⟩ := hω
    cases name with
    | parameter => exact hN.elim
    | pair p => simp [designated] at hdes
    | term T =>
      rcases hk with ⟨T', hT', hname, -⟩ | ⟨j, hj, hname, -⟩
      · cases hname
        have hmem : i ∈ C.parties.filter (· ∈ C.holders T) :=
          List.mem_filter.2 ⟨List.mem_finRange i, by simpa using hT'⟩
        simp only [designated, List.head?_eq_none_iff] at hdes
        rw [hdes] at hmem
        exact List.not_mem_nil hmem
      · cases hname
  have hhD := designated_honest hN hdes
  obtain ⟨term, pair, hX⟩ := coordOf_shift hN
  have hbad : Pr{let own ← sampleParts (C := C)}[coordOf name own = parts.getD 0 0] = ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
    rw [probEvent_sampleParts_shift (coordOf name) term pair hX, card_hashOutput]
    norm_num
  rcases hk : c.keys h with _ | keys
  · let own₀ : Parts C := ⟨parts.getD 0 0 ^^^ 1, fun _ => parts.getD 0 0 ^^^ 1, fun _ => parts.getD 0 0 ^^^ 1⟩
    have hown : coordOf name own₀ ≠ parts.getD 0 0 := by
      intro he
      have : coordOf name own₀ = parts.getD 0 0 ^^^ 1 := by cases name <;> rfl
      rw [this] at he
      have h1 : (1 : HashOutput) = 0 := by
        have := congrArg (fun x => parts.getD 0 0 ^^^ x) he
        simp at this
      exact absurd h1 (by decide)
    have heq : ghostFix prims K circuits settings D net rounds c h own₀ =
        ghostCeremony prims K circuits settings D net rounds c := by
      unfold ghostFix ghostCeremony
      congr 2
      funext i
      split_ifs with hih
      · subst hih
        simp only [recCeremonyWith, recCeremony, hk]
      · rfl
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun ω hω hev => ?_) zero_le
    rw [← heq] at hω
    exact hfix D net rounds c world name key h kind parts hN hdes hcell own₀ hown ω hω hev
  let f : C.Party → OracleComp (WorldSpec C) (RStep C E RealSpec CeremonyResult (Record C E)) := fun i =>
    if i ∈ D.1 then pure (RStep.done none []) else
      worldRoles.honest (advanceR (recCeremony K circuits settings i c).run.run)
  let r : Parts C → OracleComp (WorldSpec C) (RStep C E RealSpec CeremonyResult (Record C E)) := fun own =>
    free (advanceR (recCeremonyWith K circuits settings h c own).run.run)
  have hf : f h = free (liftComp sampleParts (LocalSpec C)) >>= r := by
    simp only [f, r, hhD, ↓reduceIte]
    rw [recCeremony_run K circuits settings h c keys hk, advanceR_liftComp_bind]
    exact free_bind _ _
  obtain ⟨Y, Z, h1, h2⟩ := sequenceFin_split f h _ r hf
    (fun steps => executeRoundsR worldRoles D net noFunctionality ([] : Record C E) rounds c.adversary steps)
  have hghost : ghostCeremony prims K circuits settings D net rounds c =
      simulateQ (streamWorld prims D) (Y >>= fun y => free (liftComp sampleParts (LocalSpec C)) >>= Z y) := by
    rw [← h1]
    rfl
  have hfixEq : ∀ own, ghostFix prims K circuits settings D net rounds c h own =
      simulateQ (streamWorld prims D) (Y >>= fun y => Z y own) := by
    intro own
    rw [← h2 own]
    unfold ghostFix executePhaseR startStepsR
    congr 3
    funext i
    by_cases hih : i = h
    · subst hih
      simp [f, r, hhD]
    · simp [f, hih]
  rw [hghost]
  simp only [simulateQ_bind, StateT.run_bind, streamWorld_free_liftComp, bind_map_left]
  rw [← hbad]
  refine probEvent_draw_le _ _ (fun y own w => (simulateQ (streamWorld prims D) (Z y own)).run w) _ _
    fun xs hxs own hown z hz hev => ?_
  refine hfix D net rounds c world name key h kind parts hN hdes hcell own hown z ?_ hev
  rw [hfixEq own, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨xs, hxs, hz⟩

/-! ## The ghost steps of a program that starts with a plain program -/

section Compose

variable {β α ρ : Type}

/-- The ghost step of `x >>= F` from the step `st` of the plain program `x`. -/
def composeR (F : Option β → OracleComp (PartySpec C E RealSpec) (Option α × ρ)) :
    Step C E RealSpec β → OracleComp (LocalSpec C) (RStep C E RealSpec α ρ)
  | .done o => advanceR (F o)
  | .wait ob k => pure (.wait ob fun inbox => k inbox >>= F)
  | .call input k => pure (.call input fun r => k r >>= F)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem advanceR_bind (x : OracleComp (PartySpec C E RealSpec) (Option β))
    (F : Option β → OracleComp (PartySpec C E RealSpec) (Option α × ρ)) :
    advanceR (x >>= F) = advance x >>= composeR F := by
  induction x using OracleComp.inductionOn with
  | pure o => rfl
  | query_bind t k ih =>
    rcases t with (q | ob) | input
    · change advanceR (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (Sum.inl (Sum.inl q))) >>=
        fun r => k r >>= F) = advance (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
          (Sum.inl (Sum.inl q))) >>= k) >>= composeR F
      rw [advance_query_bind, bind_assoc]
      refine (rfl : _ = OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r =>
        advanceR (k r >>= F)).trans ?_
      simp only [ih]
    · rfl
    · rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem recM_run_lift_bind {α β : Type} (p : PartyM C E RealSpec α) (G : α → RecM C E β) :
    (RecM.lift p >>= G).run.run = p.run >>= fun o => o.elim (pure (none, [])) fun a => (G a).run.run := by
  simp [RecM.lift, OptionT.run_bind, Option.elimM, WriterT.liftM_def', WriterT.bind_def']
  refine bind_congr fun o => ?_
  rcases o with _ | a
  · rfl
  · have e : (Prod.map id fun x => x : Option β × List (RecEvent C E) → Option β × List (RecEvent C E)) = id :=
      funext fun _ => rfl
    simp only [Option.elim]
    rw [e]
    exact id_map ((G a).run.run)

/-- The program of operator `i` after its PRSS setup, with its record. -/
def bodyR (i : C.Party) (keys : Keys C) {σ : Type} (c : CeremonyStart C σ) (prss : PrssKeys C) :
    OracleComp (PartySpec C E RealSpec) (Option CeremonyResult × Record C E) :=
  ((batched settings.batchSize (recBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter) c.jobs).run c.counters >>=
    fun p => p.1.elim failure fun outputs => pure (outputs, p.2)).run.run

/-- The rest of the program of operator `i` after the output of its PRSS setup. -/
def finR (i : C.Party) (keys : Keys C) {σ : Type} (c : CeremonyStart C σ) :
    Option (PrssKeys C) → OracleComp (PartySpec C E RealSpec) (Option CeremonyResult × Record C E)
  | none => pure (none, [])
  | some prss => bodyR K circuits settings i keys c prss

omit [Fintype E] [DecidableEq E] in
theorem recCeremonyWith_run (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (keys : Keys C)
    (hk : c.keys i = some keys) (own : Parts C) :
    (recCeremonyWith K circuits settings i c own).run.run =
      (prssSetupWith i own : PartyM C E RealSpec _).run >>= finR K circuits settings i keys c := by
  simp only [recCeremonyWith, hk, recRunWith, StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift,
    bind_assoc, recM_lift_bind, recM_lift_pure, pure_bind]
  rw [recM_run_lift_bind]
  refine bind_congr fun o => ?_
  rcases o with _ | prss
  · rfl
  · rfl

end Compose

/-! ## The recorded starts carry the keys of the setup -/

section Records

/-- Each start in a record of each outcome of `y`, for each answer, has `P`. -/
def RecStarts (P : BatchStart C → Prop) {β : Type} (y : RecM C E β) : Prop :=
  ∀ z ∈ support y.run.run, ∀ b ∈ startsOf z.2, P b

/-- `RecStarts` from each counter state. -/
def RecStartsS (P : BatchStart C → Prop) {β : Type} (x : StateT (ℕ × ℕ) (RecM C E) β) : Prop :=
  ∀ st, RecStarts P (x.run st)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem recStarts_bind {P : BatchStart C → Prop} {β γ : Type} {x : RecM C E β} {f : β → RecM C E γ}
    (hx : RecStarts P x) (hf : ∀ b, RecStarts P (f b)) : RecStarts P (x >>= f) := by
  intro z hz b hb
  rw [OptionT.run_bind, Option.elimM, WriterT.run_bind', mem_support_bind_iff] at hz
  obtain ⟨z₁, h₁, hz⟩ := hz
  rcases z₁ with ⟨_ | a, w⟩
  · simp only [Option.elim, WriterT.run_pure', support_map, support_pure, Set.image_singleton,
      Set.mem_singleton_iff] at hz
    subst hz
    simp only [Prod.map, id] at hb
    exact hx _ h₁ b (by simpa using hb)
  · simp only [Option.elim, support_map, Set.mem_image] at hz
    obtain ⟨z₂, h₂, rfl⟩ := hz
    simp only [Prod.map, id, BatchCounters.startsOf_append, List.mem_append] at hb
    rcases hb with hb | hb
    · exact hx _ h₁ b hb
    · exact hf a _ h₂ b hb

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem recStarts_pure {P : BatchStart C → Prop} {β : Type} (b : β) : RecStarts P (pure b : RecM C E β) := by
  intro z hz b' hb'
  simp only [OptionT.run_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hz
  subst hz
  simp [startsOf] at hb'

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem recStarts_lift {P : BatchStart C → Prop} {β : Type} (p : PartyM C E RealSpec β) :
    RecStarts P (RecM.lift p) := by
  intro z hz b hb
  change z ∈ support (liftM p.run : WriterT (List (RecEvent C E)) _ _).run at hz
  rw [WriterT.run_liftM, support_map] at hz
  obtain ⟨o, -, rfl⟩ := hz
  simp [startsOf] at hb

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem recStarts_record {P : BatchStart C → Prop} (events : List (RecEvent C E))
    (h : ∀ b, RecEvent.start b ∈ events → P b) : RecStarts P (RecM.record events) := by
  intro z hz b hb
  simp [RecM.record, OptionT.run_lift, WriterT.run_tell] at hz
  subst hz
  simp only [startsOf, List.mem_filterMap] at hb
  obtain ⟨e, he, hbe⟩ := hb
  rcases e with b' | _ | _
  · simp only [Option.some.injEq] at hbe
    subst hbe
    exact h _ he
  · cases hbe
  · cases hbe

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem recStartsS_bind {P : BatchStart C → Prop} {β γ : Type} {x : StateT (ℕ × ℕ) (RecM C E) β}
    {f : β → StateT (ℕ × ℕ) (RecM C E) γ} (hx : RecStartsS P x) (hf : ∀ b, RecStartsS P (f b)) :
    RecStartsS P (x >>= f) := fun st => by
  rw [StateT.run_bind]
  exact recStarts_bind (hx st) fun a => hf a.1 a.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem recStartsS_pure {P : BatchStart C → Prop} {β : Type} (b : β) :
    RecStartsS P (pure b : StateT (ℕ × ℕ) (RecM C E) β) := fun _ => recStarts_pure _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem recStartsS_liftS {P : BatchStart C → Prop} {β : Type} (x : StateT (ℕ × ℕ) (PartyM C E RealSpec) β) :
    RecStartsS P (RecM.liftS x) := fun _ => recStarts_lift _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem recStartsS_record {P : BatchStart C → Prop} (events : List (RecEvent C E))
    (h : ∀ b, RecEvent.start b ∈ events → P b) :
    RecStartsS P (StateT.lift (RecM.record events) : StateT (ℕ × ℕ) (RecM C E) PUnit) := fun st => by
  rw [StateT.run_lift]
  exact recStarts_bind (recStarts_record events h) fun _ => recStarts_pure _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem recStartsS_get {P : BatchStart C → Prop} : RecStartsS P (get : StateT (ℕ × ℕ) (RecM C E) (ℕ × ℕ)) :=
  fun _ => recStarts_pure _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem recStartsS_set {P : BatchStart C → Prop} (t : ℕ × ℕ) :
    RecStartsS P (set t : StateT (ℕ × ℕ) (RecM C E) PUnit) := fun _ => recStarts_pure _

omit [Fintype E] [DecidableEq E] in
/-- Each recorded start of a batch has the context of the batch. -/
theorem recStartsS_recBatch (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    RecStartsS (fun b => b.ctx = ctx) (recBatch K circuits settings ctx parameter jobs) := by
  unfold recBatch recCheckOpen
  refine recStartsS_bind recStartsS_get fun lk => ?_
  refine recStartsS_bind (recStartsS_liftS _) fun inputs => ?_
  refine recStartsS_bind (recStartsS_liftS _) fun r1 => ?_
  refine recStartsS_bind (recStartsS_liftS _) fun r2 => ?_
  refine recStartsS_bind (recStartsS_record _ fun b hb => ?_) fun _ => ?_
  · simp only [List.mem_singleton, RecEvent.start.injEq] at hb
    subst hb
    rfl
  refine recStartsS_bind (recStartsS_liftS _) fun r3 => ?_
  refine recStartsS_bind (recStartsS_liftS _) fun digests => ?_
  refine recStartsS_bind (recStartsS_liftS _) fun inbox => ?_
  refine recStartsS_bind (recStartsS_record _ fun b hb => by simp at hb) fun _ => ?_
  refine recStartsS_bind (recStartsS_liftS _) fun opened => ?_
  refine recStartsS_bind (recStartsS_record _ fun b hb => by simp at hb) fun _ => ?_
  exact recStartsS_bind (recStartsS_set _) fun _ => recStartsS_pure _

omit [Fintype E] [DecidableEq E] in
/-- Each recorded start of the program after the setup has the PRSS keys of the setup. -/
theorem bodyR_starts (i : C.Party) (keys : Keys C) {σ : Type} (c : CeremonyStart C σ) (prss : PrssKeys C) :
    ∀ z ∈ support (bodyR K circuits settings i keys c prss), ∀ b ∈ startsOf z.2, b.ctx.prss = prss := by
  have hb := closed_batched (m := StateT (ℕ × ℕ) (RecM C E)) (fun x => RecStartsS (fun b => b.ctx = ⟨i, keys, prss⟩) x)
    (fun b => recStartsS_pure b) (fun x f hx hf => recStartsS_bind hx hf) settings.batchSize
    (recBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter)
    (fun js => recStartsS_recBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter js) c.jobs
  intro z hz b hzb
  have h := recStarts_bind (hb c.counters) (fun p => ?_) z hz b hzb
  · rw [h]
  · rcases p with ⟨_ | outputs, counters⟩
    · intro z' hz' b' hb'
      simp [Option.elim] at hz'
      subst hz'
      simp [startsOf] at hb'
    · exact recStarts_pure _

end Records

/-! ## The ghost rounds of a setup -/

section GhostRounds

attribute [local instance] Set.monad

open SetupAgree (cacheAnswer StepNext free_cache)

variable {β α : Type}

/-- The ghost step `g` is the plain step `ps` composed with the rest `F`. An abort has the empty
record. -/
def Composed (F : Option β → OracleComp (PartySpec C E RealSpec) (Option α × Record C E))
    (ps : Step C E RealSpec β) (g : RStep C E RealSpec α (Record C E)) : Prop :=
  (ps = .done none ∧ g = .done none []) ∨
    ∃ ob k, ps = .wait ob k ∧ g = .wait ob fun inbox => k inbox >>= F

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem Composed.delivered {F : Option β → OracleComp (PartySpec C E RealSpec) (Option α × Record C E)}
    {ps : Step C E RealSpec β} {g : RStep C E RealSpec α (Record C E)} (h : Composed F ps g) :
    g.delivered = ps.delivered := by
  rcases h with ⟨rfl, rfl⟩ | ⟨ob, k, rfl, rfl⟩ <;> rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem Composed.record {F : Option β → OracleComp (PartySpec C E RealSpec) (Option α × Record C E)}
    {ps : Step C E RealSpec β} {g : RStep C E RealSpec α (Record C E)} (h : Composed F ps g) :
    g.record [] = [] := by
  rcases h with ⟨rfl, rfl⟩ | ⟨ob, k, rfl, rfl⟩ <;> rfl

variable (prims : Primitives) (D : C.Coalition)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- One ghost round of composed steps. Each honest plain step takes its next plain step with the
answers of each larger cache, and the ghost step stays composed, or the plain step ends with a value. -/
theorem stepRoundR_composed (B : Adversary C E Unit PEmpty PEmpty) (st : B.State)
    (steps : C.Party → RStep C E RealSpec α (Record C E)) (ps : C.Party → Step C E RealSpec β)
    (F : C.Party → Option β → OracleComp (PartySpec C E RealSpec) (Option α × Record C E))
    (hF : ∀ j, F j none = pure (none, [])) (hc : ∀ j, j ∉ D.1 → Composed (F j) (ps j) (steps j))
    (w : StreamState C)
    (q : (B.State × (C.Party → RStep C E RealSpec α (Record C E)) × (C.Party → C.Party → Option (Msg E))) ×
      StreamState C)
    (hq : q ∈ support ((simulateQ (streamWorld prims D)
      (stepRoundR worldRoles D B noFunctionality ([] : Record C E) st steps)).run w)) :
    w.1 ≤ q.2.1 ∧ ∀ j, j ∉ D.1 → ∀ s', q.2.1 ≤ s' → ∃ ps', StepNext s' (roundInbox D q.1.2.2 ps j) (ps j) ps' ∧
      (Composed (F j) ps' (q.1.2.1 j) ∨ ∃ o, ps' = .done (some o)) := by
  have hcall : ∀ i, (steps i).callInput = none := fun i => by
    rcases steps i with _ | _ | ⟨input, _⟩
    · rfl
    · rfl
    · exact input.elim
  have hno : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := fun ⟨⟨i, _, hi⟩, _⟩ => by
    rw [hcall i] at hi
    cases hi
  unfold stepRoundR at hq
  rw [ite_eq_right hno] at hq
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hq
  obtain ⟨a, ha, v, hv, rfl⟩ := hq
  have hinbox : ∀ j, (fun k => if k ∈ D.1 then a.1.2 k j else (steps k).delivered j) = roundInbox D a.1.2 ps j := by
    intro j
    funext k
    by_cases hk : k ∈ D.1
    · simp [roundInbox, hk]
    · simp [roundInbox, hk, (hc k hk).delivered]
  have hseq := sequenceFin_streamWorld prims D (fun j next c => j ∉ D.1 → ∀ s', c ≤ s' → ∃ ps',
      StepNext s' (roundInbox D a.1.2 ps j) (ps j) ps' ∧ (Composed (F j) ps' next ∨ ∃ o, ps' = .done (some o))) _
    (fun j b c c' hq hle hj s' hs' => hq hj s' (hle.trans hs')) (fun j w' u hu hj s' hs' => ?_) a.2 v hv
  · exact ⟨(streamWorld_run_mono prims D _ w a ha).trans (streamWorld_run_mono prims D _ a.2 v hv),
      fun j hj s' hs' => hseq j hj s' hs'⟩
  rcases hc j hj with ⟨hps, hst⟩ | ⟨ob, k, hps, hst⟩
  · simp only [hst, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    subst hu
    rw [hps]
    exact ⟨.done none, rfl, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  · simp only [hst, hj, ↓reduceIte] at hu
    rw [hinbox j, worldRoles, advanceR_bind] at hu
    simp only [free_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hu
    obtain ⟨y, hy, hu⟩ := hu
    obtain ⟨hle, hcache⟩ := free_cache prims D _ w' y hy
    have hy' := streamWorld_run_mono prims D _ y.2 u hu
    refine ⟨y.1, by rw [hps]; exact hcache s' (hy'.trans hs'), ?_⟩
    rcases hy1 : y.1 with o | ⟨ob', k'⟩ | ⟨input, k'⟩
    · rw [hy1] at hu
      rcases o with _ | o
      · refine Or.inl (Or.inl ⟨rfl, ?_⟩)
        simp only [composeR, hF, free] at hu
        rw [hu]
      · exact Or.inr ⟨o, rfl⟩
    · rw [hy1] at hu
      simp only [composeR, free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
      rw [hu]
      exact Or.inl (Or.inr ⟨ob', k', rfl, rfl⟩)
    · exact input.elim

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem advance_prssSetupWith (i : C.Party) (own : Parts C) :
    advance (prssSetupWith i own : PartyM C E RealSpec (PrssKeys C)).run =
      liftComp (commitQueries .prss i own) (LocalSpec C) >>= fun commitments =>
        pure (Draws.commitStepK i own commitments pure) := by
  have h : (prssSetupWith i own : PartyM C E RealSpec (PrssKeys C)) =
      commitRevealEcho .prss i own >>= fun keys => pure (SetupAgree.prssOf keys) := rfl
  rw [h, advance_setup_start]
  rfl

/-- The rest of operator `i` after its setup, or an abort with the empty record for an operator with
no keys. -/
def restOf (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    Option (PrssKeys C) → OracleComp (PartySpec C E RealSpec) (Option CeremonyResult × Record C E) :=
  match c.keys i with
  | some keys => finR K circuits settings i keys c
  | none => fun _ => pure (none, [])

omit [Fintype E] [DecidableEq E] in
theorem restOf_none (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    restOf K circuits settings i c none = pure (none, []) := by
  unfold restOf
  rcases c.keys i with _ | keys <;> rfl

/-- The ghost programs of `ghostFix`. -/
def fixPrograms (h : C.Party) {σ : Type} (c : CeremonyStart C σ) (own : Parts C) :
    C.Party → OracleComp (PartySpec C E RealSpec) (Option CeremonyResult × Record C E) := fun i =>
  if i = h then (recCeremonyWith K circuits settings i c own).run.run else (recCeremony K circuits settings i c).run.run

omit [Fintype E] [DecidableEq E] in
theorem restOf_some (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (keys : Keys C) (hk : c.keys i = some keys) :
    restOf K circuits settings i c = finR K circuits settings i keys c := by
  unfold restOf
  rw [hk]

omit [Fintype E] [DecidableEq E] in
/-- The first ghost steps of `ghostFix`. Each honest operator aborted at once, or it waits at the
commit round of its setup, with the fixed parts at `h`. -/
theorem fixPrograms_start (h : C.Party) {σ : Type} (c : CeremonyStart C σ) (own : Parts C) (j : C.Party)
    (step : RStep C E RealSpec CeremonyResult (Record C E))
    (hstep : step ∈ support (advanceR (fixPrograms K circuits settings h c own j))) :
    ∃ ps, Composed (restOf K circuits settings j c) ps step ∧
      (ps = .done none ∨ ∃ own' commitments, (j = h → own' = own) ∧ ps = Draws.commitStepK j own' commitments pure) := by
  have hsetup : ∀ (keys : Keys C), c.keys j = some keys → ∀ own' (st : RStep C E RealSpec CeremonyResult (Record C E)),
      st ∈ support (advanceR (recCeremonyWith K circuits settings j c own').run.run) →
      ∃ ps, Composed (restOf K circuits settings j c) ps st ∧
        ∃ commitments, ps = Draws.commitStepK j own' commitments pure := by
    intro keys hk own' st hst
    rw [recCeremonyWith_run K circuits settings j c keys hk, advanceR_bind, advance_prssSetupWith] at hst
    simp only [bind_assoc, pure_bind, mem_support_bind_iff] at hst
    obtain ⟨commitments, -, hst⟩ := hst
    simp only [Draws.commitStepK, composeR, support_pure, Set.mem_singleton_iff] at hst
    refine ⟨_, Or.inr ⟨_, _, rfl, ?_⟩, commitments, rfl⟩
    rw [hst, restOf_some K circuits settings j c keys hk]
  unfold fixPrograms at hstep
  rcases hk : c.keys j with _ | keys
  · have hrun : (if j = h then (recCeremonyWith K circuits settings j c own).run.run
        else (recCeremony K circuits settings j c).run.run) = pure (none, []) := by
      split_ifs <;> simp [recCeremonyWith, recCeremony, hk]
    rw [hrun] at hstep
    change step ∈ support (pure (RStep.done none []) : OracleComp (LocalSpec C) _) at hstep
    simp only [support_pure, Set.mem_singleton_iff] at hstep
    subst hstep
    exact ⟨.done none, Or.inl ⟨rfl, rfl⟩, Or.inl rfl⟩
  by_cases hjh : j = h
  · subst hjh
    simp only [↓reduceIte] at hstep
    obtain ⟨ps, hps, commitments, rfl⟩ := hsetup keys hk own step hstep
    exact ⟨_, hps, Or.inr ⟨own, commitments, fun _ => rfl, rfl⟩⟩
  · simp only [hjh, ↓reduceIte] at hstep
    rw [recCeremony_run K circuits settings j c keys hk, advanceR_liftComp_bind, mem_support_bind_iff] at hstep
    obtain ⟨own', -, hstep⟩ := hstep
    obtain ⟨ps, hps, commitments, rfl⟩ := hsetup keys hk own' step hstep
    exact ⟨_, hps, Or.inr ⟨own', commitments, fun h' => absurd h' hjh, rfl⟩⟩

end GhostRounds

/-! ## The end of the ghost run after the reveal round -/

section GhostEnd

open BatchCounters (OnPathR OnPathFree)

variable {α ρ : Type}

/-- The program that a ghost step stands for. -/
def progOfR : RStep C E RealSpec α ρ → OracleComp (PartySpec C E RealSpec) (Option α × ρ)
  | .done o r => pure (o, r)
  | .wait ob k => OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (Sum.inl (Sum.inr ob))) >>= k
  | .call input k => OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (Sum.inr input)) >>= k

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem onPathR_progOfR (g : RStep C E RealSpec α ρ) : OnPathR (progOfR g) g := by
  intro a ha
  rcases g with ⟨o, r⟩ | ⟨ob, k⟩ | ⟨input, k⟩
  · simpa [progOfR, GhostBatch.toStep, stepProgram] using ha
  · simpa [progOfR, GhostBatch.toStep, stepProgram, map_bind] using ha
  · exact input.elim

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The echo of a setup ends with an abort or with the PRSS keys of its derived keys. -/
theorem echo_support (i : C.Party) (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (shared : List HashOutput) (inbox : Mail C E) (o : Option (PrssKeys C))
    (ho : o ∈ support (exchangeResume (fun received => require (echoCheck .prss i keys shared received) >>=
      fun _ => (pure (SetupAgree.prssOf keys) : PartyM C E RealSpec (PrssKeys C))) inbox)) :
    o = none ∨ o = some (SetupAgree.prssOf keys) := by
  unfold exchangeResume at ho
  split_ifs at ho
  · simp at ho
    exact Or.inl ho
  · by_cases hc : echoCheck .prss i keys shared inbox
    · simp [ThresholdLeanXmss.require, hc] at ho
      exact Or.inr ho
    · simp [ThresholdLeanXmss.require, hc] at ho
      exact Or.inl ho

omit [Fintype E] [DecidableEq E] in
/-- After a composed echo step, each recorded start has the PRSS keys of the derived keys. -/
theorem starts_after_echo (i : C.Party) {σ : Type} (c : CeremonyStart C σ)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (shared : List HashOutput)
    (g : RStep C E RealSpec CeremonyResult (Record C E))
    (hg : Composed (restOf K circuits settings i c) (Draws.echoStepK i keys shared pure) g)
    (z : Option CeremonyResult × Record C E) (hz : z ∈ support (progOfR g)) :
    ∀ b ∈ startsOf z.2, b.ctx.prss = SetupAgree.prssOf keys := by
  rcases hg with ⟨h, -⟩ | ⟨ob, k, hps, rfl⟩
  · cases h
  simp only [Draws.echoStepK, Step.wait.injEq] at hps
  obtain ⟨rfl, rfl⟩ := hps
  simp only [progOfR, mem_support_bind_iff] at hz
  obtain ⟨inbox, -, o, ho, hz⟩ := hz
  intro b hb
  rcases echo_support i keys shared inbox o ho with rfl | rfl
  · rw [restOf_none] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp [startsOf] at hb
  · rcases hkc : c.keys i with _ | keys'
    · simp only [restOf, hkc, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp [startsOf] at hb
    · simp only [restOf, hkc, finR] at hz
      exact bodyR_starts K circuits settings i keys' c _ z hz b hb

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Two derive cells of PRSS setups with one value at two inputs are a derive collision. -/
theorem deriveCollision_of {cache : HashCache C} {k₁ k₂ : KeyKind} {l₁ l₂ : List HashOutput} {v : HashOutput}
    (h₁ : cache (.derive .prss k₁ l₁) = some v) (h₂ : cache (.derive .prss k₂ l₂) = some v)
    (hne : Query.derive (C := C) .prss k₁ l₁ ≠ .derive .prss k₂ l₂) : DomainCollision DeriveDomain cache := by
  refine ⟨_, _, v, v, hne, ?_, ?_, HEq.rfl⟩
  · simp only [splitRegionCache, QueryCache.ofFn_apply, DeriveDomain, ↓reduceIte]
    exact h₁
  · simp only [splitRegionCache, QueryCache.ofFn_apply, DeriveDomain, ↓reduceIte]
    exact h₂

variable (prims : Primitives) (D : C.Coalition)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem executeRoundsR_cases {α : Type} (B : Adversary C E Unit PEmpty PEmpty) (n : ℕ) (st : B.State)
    (steps : C.Party → RStep C E RealSpec α (Record C E)) (w : StreamState C)
    (z : (B.State × (C.Party → RStep C E RealSpec α (Record C E))) × StreamState C)
    (hz : z ∈ support ((simulateQ (streamWorld prims D)
      (executeRoundsR worldRoles D B noFunctionality ([] : Record C E) (n + 1) st steps)).run w)) :
    z.1.2 = steps ∨ ∃ q ∈ support ((simulateQ (streamWorld prims D)
      (stepRoundR worldRoles D B noFunctionality ([] : Record C E) st steps)).run w),
      z ∈ support ((simulateQ (streamWorld prims D)
        (executeRoundsR worldRoles D B noFunctionality ([] : Record C E) n q.1.1 q.1.2.1)).run q.2) := by
  rw [executeRoundsR] at hz
  split_ifs at hz
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl rfl
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨q, hq, hz⟩ := hz
    exact Or.inr ⟨q, hq, hz⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem executeRoundsR_zero {α : Type} (B : Adversary C E Unit PEmpty PEmpty) (st : B.State)
    (steps : C.Party → RStep C E RealSpec α (Record C E)) (w : StreamState C)
    (z : (B.State × (C.Party → RStep C E RealSpec α (Record C E))) × StreamState C)
    (hz : z ∈ support ((simulateQ (streamWorld prims D)
      (executeRoundsR worldRoles D B noFunctionality ([] : Record C E) 0 st steps)).run w)) : z.1.2 = steps := by
  simp only [executeRoundsR, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rfl

end GhostEnd

/-! ## The proof of `FreshFixed` -/

section Fixed

attribute [local instance] Set.monad

open SetupAgree (cacheAnswer StepNext)

omit [Fintype E] [DecidableEq E] in
/-- The first ghost steps of `ghostFix` with their plain steps. -/
theorem fixStart (h : C.Party) {σ : Type} (c : CeremonyStart C σ) (own : Parts C)
    (w : StreamState C) (a : (C.Party → RStep C E RealSpec CeremonyResult (Record C E)) × StreamState C)
    (ha : a ∈ support ((simulateQ (streamWorld prims D) (startStepsR worldRoles D ([] : Record C E)
      (fixPrograms K circuits settings h c own))).run w)) :
    ∀ j, j ∉ D.1 → ∃ ps, Composed (restOf K circuits settings j c) ps (a.1 j) ∧
      (ps = .done none ∨ ∃ own' commitments, (j = h → own' = own) ∧ ps = Draws.commitStepK j own' commitments pure) := by
  unfold startStepsR at ha
  refine sequenceFin_streamWorld prims D (fun j v _ => j ∉ D.1 → ∃ ps, Composed (restOf K circuits settings j c) ps v ∧
      (ps = .done none ∨ ∃ own' commitments, (j = h → own' = own) ∧ ps = Draws.commitStepK j own' commitments pure)) _
    (fun _ _ _ _ h _ => h) (fun j w' u hu hj => ?_) w a ha
  simp only [hj, ↓reduceIte] at hu
  have hmem : u.1 ∈ support (advanceR (fixPrograms K circuits settings h c own j)) :=
    support_simulateQ_subset _ _ (support_simulateQ_run'_subset (streamWorld prims D) _ w' (by
      rw [StateT.run'_eq, support_map]
      exact ⟨u, hu, rfl⟩))
  exact fixPrograms_start K circuits settings h c own j u.1 hmem

omit [Fintype E] [DecidableEq E] in
/-- The commit round of `ghostFix`. Each honest operator aborted, or it waits at its reveal with its
own parts, and these are the fixed parts at `h`. -/
theorem fixCommit (net : Adversary C E Unit PEmpty PEmpty) (h : C.Party) {σ : Type}
    (c : CeremonyStart C σ) (own : Parts C) (st : net.State)
    (a : (C.Party → RStep C E RealSpec CeremonyResult (Record C E)) × StreamState C)
    (h0 : ∀ j, j ∉ D.1 → ∃ ps, Composed (restOf K circuits settings j c) ps (a.1 j) ∧
      (ps = .done none ∨ ∃ own' commitments, (j = h → own' = own) ∧ ps = Draws.commitStepK j own' commitments pure))
    (q1 : (net.State × (C.Party → RStep C E RealSpec CeremonyResult (Record C E)) × (C.Party → C.Party → Option (Msg E))) ×
      StreamState C)
    (hq1 : q1 ∈ support ((simulateQ (streamWorld prims D)
      (stepRoundR worldRoles D net noFunctionality ([] : Record C E) st a.1)).run a.2)) :
    ∀ j, j ∉ D.1 → ∃ ps, Composed (restOf K circuits settings j c) ps (q1.1.2.1 j) ∧
      (ps = .done none ∨ ∃ own' committed, (j = h → own' = own) ∧ ps = Draws.revealStepK j own' committed pure) := by
  classical
  have : Nonempty (Step C E RealSpec (PrssKeys C)) := ⟨.done none⟩
  choose! ps0 hps0 using h0
  obtain ⟨-, hr1⟩ := stepRoundR_composed prims D net st a.1 ps0 (fun j => restOf K circuits settings j c)
    (fun j => restOf_none K circuits settings j c) (fun j hj => (hps0 j hj).1) a.2 q1 hq1
  intro j hj
  obtain ⟨ps', hnext, hcomp⟩ := hr1 j hj q1.2.1 le_rfl
  rcases (hps0 j hj).2 with hd | ⟨own', commitments, hown', he⟩
  · rw [hd] at hnext
    change ps' = .done none at hnext
    subst hnext
    rcases hcomp with hcomp | ⟨o, ho⟩
    · exact ⟨_, hcomp, Or.inl rfl⟩
    · cases ho
  · rw [he] at hnext
    rcases Draws.commit_nextK q1.2.1 _ j own' commitments pure ps' hnext with rfl | rfl
    · rcases hcomp with hcomp | ⟨o, ho⟩
      · exact ⟨_, hcomp, Or.inl rfl⟩
      · cases ho
    · rcases hcomp with hcomp | ⟨o, ho⟩
      · exact ⟨_, hcomp, Or.inr ⟨own', _, hown', rfl⟩⟩
      · cases ho

omit [Fintype E] [DecidableEq E] in
/-- The commit round and the reveal round of `ghostFix`. Each honest operator aborted, or it waits at
its echo with keys derived from its view, its own parts are the fixed parts at `h`, and it read the
reveal of `h` with the fixed parts. -/
theorem fixRounds (net : Adversary C E Unit PEmpty PEmpty) (h : C.Party) {σ : Type}
    (c : CeremonyStart C σ) (own : Parts C) (hhD : h ∉ D.1) (st : net.State)
    (a : (C.Party → RStep C E RealSpec CeremonyResult (Record C E)) × StreamState C)
    (h0 : ∀ j, j ∉ D.1 → ∃ ps, Composed (restOf K circuits settings j c) ps (a.1 j) ∧
      (ps = .done none ∨ ∃ own' commitments, (j = h → own' = own) ∧ ps = Draws.commitStepK j own' commitments pure))
    (q1 : (net.State × (C.Party → RStep C E RealSpec CeremonyResult (Record C E)) × (C.Party → C.Party → Option (Msg E))) ×
      StreamState C)
    (hq1 : q1 ∈ support ((simulateQ (streamWorld prims D)
      (stepRoundR worldRoles D net noFunctionality ([] : Record C E) st a.1)).run a.2))
    (q2 : (net.State × (C.Party → RStep C E RealSpec CeremonyResult (Record C E)) × (C.Party → C.Party → Option (Msg E))) ×
      StreamState C)
    (hq2 : q2 ∈ support ((simulateQ (streamWorld prims D)
      (stepRoundR worldRoles D net noFunctionality ([] : Record C E) q1.1.1 q1.1.2.1)).run q1.2)) :
    ∀ j, j ∉ D.1 → ∃ ps, Composed (restOf K circuits settings j c) ps (q2.1.2.1 j) ∧
      (ps = .done none ∨ ∃ keys shared own', ∃ inbox : Mail C E, ps = Draws.echoStepK j keys shared pure ∧
        keys ∈ simulateQ (cacheAnswer q2.2.1) (liftComp (deriveKeys .prss j (setupView .prss j own' inbox)) (LocalSpec C)) ∧
        (j = h → own' = own) ∧ (h ≠ j → inbox h = revealOutbox .prss h own j)) := by
  classical
  have : Nonempty (Step C E RealSpec (PrssKeys C)) := ⟨.done none⟩
  have h1 := fixCommit prims K circuits settings D net h c own st a h0 q1 hq1
  choose! ps1 hps1 using h1
  obtain ⟨-, hr2⟩ := stepRoundR_composed prims D net q1.1.1 q1.1.2.1 ps1 (fun j => restOf K circuits settings j c)
    (fun j => restOf_none K circuits settings j c) (fun j hj => (hps1 j hj).1) q1.2 q2 hq2
  intro j hj
  obtain ⟨ps', hnext, hcomp⟩ := hr2 j hj q2.2.1 le_rfl
  have hcomp' : ps' = .done none ∨ (∃ keys shared, ps' = Draws.echoStepK j keys shared pure) →
      Composed (restOf K circuits settings j c) ps' (q2.1.2.1 j) := by
    intro hps
    rcases hcomp with hcomp | ⟨o, rfl⟩
    · exact hcomp
    · rcases hps with hps | ⟨keys, shared, hps⟩ <;> cases hps
  rcases (hps1 j hj).2 with hd | ⟨own', committed, hown', he⟩
  · rw [hd] at hnext
    change ps' = .done none at hnext
    exact ⟨ps', hcomp' (Or.inl hnext), Or.inl hnext⟩
  rw [he] at hnext
  rcases Draws.reveal_nextK q2.2.1 _ j own' committed pure ps' hnext with hd | ⟨habort, keys, shared, hkeys, hecho⟩
  · exact ⟨ps', hcomp' (Or.inl hd), Or.inl hd⟩
  refine ⟨ps', hcomp' (Or.inr ⟨keys, shared, hecho⟩),
    Or.inr ⟨keys, shared, own', _, hecho, hkeys, hown', fun hhj => ?_⟩⟩
  rcases (hps1 h hhD).2 with hd' | ⟨own'', committed', hown'', he'⟩
  · exfalso
    have hab : Msg.isAbort (roundInbox D q2.1.2.2 ps1 j h) = true := by
      simp [roundInbox, hhD, hd', Msg.isAbort]
    have := List.any_eq_false.1 habort h (List.mem_finRange h)
    rw [hab] at this
    exact this rfl
  · rw [hown'' rfl] at he'
    simp [roundInbox, hhD, he', Draws.revealStepK]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A key of operator `i` under a name with the designated contributor `h` has a derive cell whose
first coordinate is the coordinate of the parts of `h`. -/
theorem newCell (s : HashCache C) (h i : C.Party) (own own' : Parts C) (inbox : Mail C E)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hkeys : keys ∈ simulateQ (cacheAnswer s) (liftComp (deriveKeys .prss i (setupView .prss i own' inbox)) (LocalSpec C)))
    (hown : i = h → own' = own) (hrev : h ≠ i → inbox h = revealOutbox .prss h own i)
    (name : KeyName C) (key : HashOutput) (hdes : designated name = some h)
    (hnk : NameKey i (SetupAgree.prssOf keys) name key) :
    ∃ kind l, s (.derive .prss kind l) = some key ∧ l.getD 0 0 = coordOf name own := by
  rcases hnk with ⟨T, hT, rfl, rfl⟩ | ⟨j', hj', rfl, rfl⟩
  · refine ⟨.term, _, Draws.term_cached i _ keys hkeys T hT, ?_⟩
    simp only [designated] at hdes
    obtain ⟨tl, htl⟩ := List.head?_eq_some_iff.1 hdes
    have hhT : h ∈ C.holders T := by
      have hmem : h ∈ C.parties.filter (· ∈ C.holders T) := by rw [htl]; exact List.mem_cons_self
      simpa using (List.mem_filter.1 hmem).2
    rw [htl]
    simp only [List.map_cons, List.getD_cons_zero, coordOf]
    by_cases hhi : h = i
    · subst hhi
      simp [setupView, hown rfl]
    · exact Draws.setupView_term i h hhi own' own inbox (hrev hhi) T hT hhT
  · refine ⟨.pair, _, SetupAgree.pair_cached i _ keys hkeys j' hj', ?_⟩
    simp only [designated, Option.some.injEq] at hdes
    simp only [List.getD_cons_zero, coordOf]
    rcases Draws.pairOf_ends i j' (Ne.symm hj') with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
      rw [e1] at hdes
      subst hdes
      simp [setupView, hown rfl]
    · rw [e1, e2]
      rw [e1] at hdes
      subst hdes
      exact SetupAgree.setupView_pair i j' (Ne.symm hj') own' own inbox (hrev hj') i

omit [Fintype E] [DecidableEq E] in
/-- After the commit round and the reveal round of `ghostFix`, the record of each honest operator at
the end of the run has only starts with the PRSS keys of its setup. -/
theorem fixRecord (net : Adversary C E Unit PEmpty PEmpty) (n : ℕ) {σ : Type} (c : CeremonyStart C σ) (i : C.Party)
    (q2 : (net.State × (C.Party → RStep C E RealSpec CeremonyResult (Record C E)) × (C.Party → C.Party → Option (Msg E))) ×
      StreamState C)
    (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((simulateQ (streamWorld prims D)
      (executeRoundsR worldRoles D net noFunctionality ([] : Record C E) n q2.1.1 q2.1.2.1)).run q2.2))
    (hi : i ∉ D.1) (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (shared : List HashOutput)
    (ps : Step C E RealSpec (PrssKeys C)) (hc : Composed (restOf K circuits settings i c) ps (q2.1.2.1 i))
    (hps : ps = .done none ∨ ps = Draws.echoStepK i keys shared pure)
    (b : BatchStart C) (hb : b ∈ startsOf (ceremonyRecord ω.1.2 i)) :
    ps ≠ .done none ∧ b.ctx.prss = SetupAgree.prssOf keys := by
  have hpath := BatchCounters.executeRoundsR_onPathR prims D D net ([] : Record C E) (fun j => progOfR (q2.1.2.1 j)) n
    q2.1.1 q2.1.2.1 q2.2 ω hω (fun j _ => onPathR_progOfR _) i hi
  rcases hωi : ω.1.2 i with ⟨out, r⟩ | ⟨ob, k⟩ | ⟨input, k⟩
  · rw [hωi] at hpath
    have hmem := hpath.done
    simp only [ceremonyRecord, hωi, RStep.record] at hb
    rcases hps with rfl | rfl
    · rcases hc with ⟨-, hg⟩ | ⟨ob, k, hd, -⟩
      · rw [hg] at hmem
        simp only [progOfR, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rw [hmem.2] at hb
        simp [startsOf] at hb
      · cases hd
    · exact ⟨(fun hd => by simp [Draws.echoStepK] at hd), starts_after_echo K circuits settings i c keys shared _ hc _ hmem b hb⟩
  · simp [ceremonyRecord, hωi, RStep.record, startsOf] at hb
  · exact input.elim

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A composed step of an abort or of a wait at the start of a setup has the empty record. -/
theorem composed_noStart {F : Option (PrssKeys C) → OracleComp (PartySpec C E RealSpec) (Option CeremonyResult × Record C E)}
    {ps : Step C E RealSpec (PrssKeys C)} {g : RStep C E RealSpec CeremonyResult (Record C E)} (hc : Composed F ps g)
    (b : BatchStart C) (hb : b ∈ startsOf (g.record [])) : False := by
  rw [hc.record] at hb
  simp [startsOf] at hb

omit [Fintype E] [DecidableEq E] in
/-- `FreshFixed` holds. A key of an honest operator under the hidden name has a derive cell in the
cache after the reveal round with the coordinate of the fixed parts first, so it differs from the old
cell with the same answer, and this is a collision of derive inputs. -/
theorem freshFixed : FreshFixed prims K circuits settings := by
  intro D net rounds c world name key h kind parts hN hdes hold own hcoord ω hω ⟨⟨i, hi, b, hb, hnk⟩, hng⟩
  have hhD : h ∉ D.1 := designated_honest hN hdes
  unfold ghostFix executePhaseR at hω
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hω
  obtain ⟨a, ha, hω⟩ := hω
  have h0 := fixStart prims K circuits settings D h c own world a ha
  rcases rounds with _ | _ | n
  · rw [executeRoundsR_zero prims D net _ _ _ _ hω] at hb
    obtain ⟨ps, hc, -⟩ := h0 i hi
    exact composed_noStart hc b hb
  · rcases executeRoundsR_cases prims D net 0 _ _ _ _ hω with he | ⟨q1, hq1, hω⟩
    · rw [he] at hb
      obtain ⟨ps, hc, -⟩ := h0 i hi
      exact composed_noStart hc b hb
    · rw [executeRoundsR_zero prims D net _ _ _ _ hω] at hb
      obtain ⟨ps, hc, -⟩ := fixCommit prims K circuits settings D net h c own _ a h0 q1 hq1 i hi
      exact composed_noStart hc b hb
  rcases executeRoundsR_cases prims D net (n + 1) _ _ _ _ hω with he | ⟨q1, hq1, hω⟩
  · rw [he] at hb
    obtain ⟨ps, hc, -⟩ := h0 i hi
    exact composed_noStart hc b hb
  rcases executeRoundsR_cases prims D net n _ _ _ _ hω with he | ⟨q2, hq2, hω⟩
  · rw [he] at hb
    obtain ⟨ps, hc, -⟩ := fixCommit prims K circuits settings D net h c own _ a h0 q1 hq1 i hi
    exact composed_noStart hc b hb
  obtain ⟨ps, hc, hps⟩ := fixRounds prims K circuits settings D net h c own hhD _ a h0 q1 hq1 q2 hq2 i hi
  rcases hps with hd | ⟨keys, shared, own', inbox, he, hkeys, hown, hrev⟩
  · exact (fixRecord prims K circuits settings D net n c i q2 ω hω hi (0, fun _ => 0, fun _ => 0) [] ps hc
      (Or.inl hd) b hb).1 hd
  have hctx := (fixRecord prims K circuits settings D net n c i q2 ω hω hi keys shared ps hc (Or.inr he) b hb).2
  rw [hctx] at hnk
  obtain ⟨kind', l, hl, hlc⟩ := newCell q2.2.1 h i own own' inbox keys hkeys hown hrev name key hdes hnk
  have hmono : world.1 ≤ q2.2.1 := (streamWorld_run_mono prims D _ world a ha).trans
    ((streamWorld_run_mono prims D _ a.2 q1 hq1).trans (streamWorld_run_mono prims D _ q1.2 q2 hq2))
  have hcol := deriveCollision_of (hmono hold) hl fun heq => by
    simp only [Query.derive.injEq] at heq
    exact hcoord (by rw [heq.2.2, hlc])
  exact hng (Or.inr (Or.inl (SetupAgree.domainCollision_mono (streamWorld_run_mono prims D _ q2.2 ω hω) hcol)))

omit [Fintype E] [DecidableEq E] in
/-- The leaf `FreshOne`. -/
theorem freshOne : FreshOne prims K circuits settings :=
  freshOne_of_fixed prims K circuits settings (freshFixed prims K circuits settings)

end Fixed

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.freshOne_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.freshOne_of_fixed

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.freshFixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.freshFixed

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.freshOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.freshOne
