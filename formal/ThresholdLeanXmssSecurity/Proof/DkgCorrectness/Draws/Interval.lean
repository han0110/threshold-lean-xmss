import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Draws.OneKey
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutWalk
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.BatchRecords

/-!
# The labels of the hidden draws of a prefix of one ceremony

`Draws.executePhase_cellsBelow` states that a phase whose honest programs draw under hidden names only
at labels below `L` writes no new hidden cell at a label at or above `L`. `PrefixLabels` states that
the program of an honest operator in the prefix of one ceremony up to the check of batch `k` draws
under hidden names only at labels below `stopLabel`, the label of its stop. `ceremonyInterval_of_prefixLabels`
proves `CeremonyInterval` from `PrefixLabels`. `prefixLabels` proves `PrefixLabels` by a walk of the
labels (`Draws.WithinAt` for one batch, `CutLate` for the batches up to the stop), and
`ceremonyInterval` is the leaf.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace Draws

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

variable (D : C.Coalition)

/-! ## The walk of the labels of the new hidden cells -/

section Late

variable (prims : Primitives)

/-- Each hidden cell of `w` is a cell of `w₀` or has a label below `L`. -/
def CellsBelow (w₀ : StreamState C) (L : ℕ) (w : StreamState C) : Prop :=
  ∀ name key ρ idx position, w.2 ((name, key), ρ, idx, position) ≠ none →
    w₀.2 ((name, key), ρ, idx, position) ≠ none ∨ ρ < L

/-- A free `PRG` call under a hidden name at a label at or above `L`. -/
def LateDraw (L : ℕ) : (LocalSpec C).Domain → Prop
  | .inr (.inr x) => Hidden D x.1 ∧ L ≤ x.2.2.1
  | _ => False

/-- A local call of an operator that is a late draw. -/
def PartyLate (L : ℕ) : (PartySpec C E RealSpec).Domain → Prop
  | .inl (.inl t) => LateDraw D L t
  | _ => False

/-- A late draw is a call in class `stream`. -/
theorem lateDraw_stream {L : ℕ} (t : (LocalSpec C).Domain) (h : LateDraw D L t) : InClass .stream t := by
  rcases t with _ | _ | _
  · exact h.elim
  · exact h.elim
  · rfl

theorem streamWorld_cellsBelow (w₀ : StreamState C) (L : ℕ) (t : (WorldSpec C).Domain)
    (ht : ¬ SetupBudgets.HonestP (LateDraw D L) t) (w : StreamState C) (hw : CellsBelow w₀ L w) :
    ∀ y ∈ support ((streamWorld prims D t).run w), CellsBelow w₀ L y.2 := by
  intro y hy
  rcases t with ((u | p) | (u | q | x))
  · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hy
    exact hw
  · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hy
    exact hw
  · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hy
    exact hw
  · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hy
    exact hw
  · change y ∈ support ((if Hidden D x.1 then _ else _ : StateT (StreamState C) ProbComp _).run w) at hy
    split_ifs at hy with hx
    · simp only [StateT.run_mk, support_map, Set.mem_image] at hy
      obtain ⟨r, hr, rfl⟩ := hy
      intro name key ρ idx position hcell
      rcases FirstCounts.randomOracle_cells _ _ r hr _ hcell with h | h
      · exact hw name key ρ idx position h
      · have h3 : ρ = x.2.2.1 := congrArg (fun y => y.2.1) h
        subst h3
        exact Or.inr (Nat.lt_of_not_le fun hL => ht ⟨hx, hL⟩)
    · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hy
      exact hw

end Late

/-! ## A phase with no late draw -/

section Phase

variable (prims : Primitives)

/-- A phase whose honest programs make no late draw writes each new hidden cell at a label below
`L`. -/
theorem executePhase_cellsBelow {Ia α : Type} (L : ℕ) (B : Adversary C E Ia PEmpty PEmpty) (fuel : ℕ) (st : B.State)
    (program : C.Party → PartyM C E RealSpec α) (hp : ∀ j, j ∉ D.1 → IsQueryBoundP (program j).run (PartyLate D L) 0)
    (w : StreamState C) :
    ∀ z ∈ support ((simulateQ (streamWorld prims D) (executePhase worldRoles D B noFunctionality fuel st program)).run w),
      CellsBelow w L z.2 := by
  intro z hz
  unfold executePhase at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨a, ha, hz⟩ := hz
  unfold startSteps at ha
  have hstart := sequenceFin_keeps D prims (CellsBelow w L) w (fun j v _ => j ∉ D.1 → StepNo (LateDraw D L) v) _
    (fun _ _ _ _ h _ => h) (fun j w' u _ hw' hu => ?_) w a le_rfl (fun _ _ _ _ _ h => Or.inl h) ha
  · exact executeRounds_inv D (streamWorld_cellsBelow D prims w L) (lateDraw_stream D) B fuel st a.1 a.2 hstart.2
      hstart.1 z hz
  by_cases hj : j ∈ D.1
  · simp only [hj, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    subst hu
    exact ⟨hw', fun h => absurd hj h⟩
  · simp only [hj, ↓reduceIte] at hu
    obtain ⟨h1, h2⟩ := advance_no (LateDraw D L) _ (hp j hj)
    refine ⟨inv_of_noCall D (streamWorld_cellsBelow D prims w L) _ (fun _ h => h) _ (free_honestP _ _ h1) w' hw' u hu,
      fun _ => h2 _ ?_⟩
    exact mem_support_advance_of_handler (streamWorld prims D) _ w' _ (by
      rw [StateT.run'_eq, support_map]
      exact ⟨u, hu, rfl⟩)

open BatchCounters (OnPathFree) in
/-- A round keeps each honest step on the path of its program. -/
theorem stepRound_onPathFree {Ia α : Type} (B : Adversary C E Ia PEmpty PEmpty) (st : B.State)
    (steps : C.Party → Step C E RealSpec α) (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α))
    (s : StreamState C)
    (y : (B.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E))) × StreamState C)
    (hy : y ∈ support ((simulateQ (streamWorld prims D) (stepRound worldRoles D B noFunctionality st steps)).run s)) :
    (∀ i, i ∉ D.1 → OnPathFree (program i) (steps i)) → ∀ i, i ∉ D.1 → OnPathFree (program i) (y.1.2.1 i) := by
  have hcall : ∀ i, (steps i).callInput = none := fun i => by
    rcases steps i with _ | _ | ⟨input, _⟩
    · rfl
    · rfl
    · exact input.elim
  have hno : ¬ ((∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := fun ⟨⟨i, _, hi⟩, _⟩ => by
    rw [hcall i] at hi
    cases hi
  unfold stepRound at hy
  rw [ite_eq_right hno] at hy
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨a, -, w, hw, rfl⟩ := hy
  have hseq := sequenceFin_streamWorld prims D (fun j v _ => j ∉ D.1 →
      OnPathFree (program j) (steps j) → OnPathFree (program j) v) _
    (fun j b c c' hq _ => hq) (fun j s' y hy hj hon => ?_) a.2 w hw
  · exact fun hon i hi => hseq i hi (hon i hi)
  rcases hsj : steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · simp only [hsj, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rw [← hsj]
    exact hon
  · simp only [hsj, hj, ↓reduceIte] at hy
    have hpath := BatchCounters.advance_onPathFree prims D _ s' y hy
    intro a' hmem
    rw [hsj] at hon
    refine hon a' ?_
    simp only [stepProgram]
    rw [mem_support_bind_iff]
    exact ⟨_, mem_support_query _ _, hpath a' hmem⟩
  · exact input.elim

open BatchCounters (OnPathFree) in
/-- Each honest output of a phase is an output of the program of that operator. -/
theorem executePhase_output {Ia α : Type} (B : Adversary C E Ia PEmpty PEmpty) (fuel : ℕ) (st : B.State)
    (program : C.Party → PartyM C E RealSpec α) (w : StreamState C)
    (z : (B.State × (C.Party → Option α)) × StreamState C)
    (hz : z ∈ support ((simulateQ (streamWorld prims D) (executePhase worldRoles D B noFunctionality fuel st program)).run w)) :
    ∀ i, i ∉ D.1 → ∀ a, z.1.2 i = some a → some a ∈ support (program i).run := by
  unfold executePhase at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  unfold startSteps at hy
  have hstart := sequenceFin_streamWorld prims D (fun j v _ => j ∉ D.1 → OnPathFree (program j).run v) _
    (fun j b c c' hq _ => hq) (fun j s' u hu hj => ?_) w y hy
  · have hout : ∀ (fuel : ℕ) (st : B.State) (steps : C.Party → Step C E RealSpec α) (s : StreamState C),
        (∀ i, i ∉ D.1 → OnPathFree (program i).run (steps i)) →
        ∀ z ∈ support ((simulateQ (streamWorld prims D) (executeRounds worldRoles D B noFunctionality fuel st steps)).run s),
          ∀ i, i ∉ D.1 → ∀ a, z.1.2 i = some a → some a ∈ support (program i).run := by
      intro fuel
      induction fuel with
      | zero =>
        intro st steps s hon z hz i hi a ha
        simp only [executeRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hon i hi a (by
          change (steps i).output = some a at ha
          rcases hs : steps i with out | _ | _ <;> rw [hs] at ha <;> cases ha
          simp [stepProgram])
      | succ fuel ih =>
        intro st steps s hon z hz i hi a ha
        unfold executeRounds at hz
        split_ifs at hz
        · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact hon i hi a (by
            change (steps i).output = some a at ha
            rcases hs : steps i with out | _ | _ <;> rw [hs] at ha <;> cases ha
            simp [stepProgram])
        · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
          obtain ⟨q, hq, hz⟩ := hz
          exact ih q.1.1 q.1.2.1 q.2 (stepRound_onPathFree D prims B st steps _ s q hq hon) z hz i hi a ha
    exact hout fuel st y.1 y.2 (fun i hi => hstart i hi) z hz
  simp only [hj, ↓reduceIte] at hu
  exact BatchCounters.advance_onPathFree prims D _ s' u hu

end Phase

/-! ## The labels of the draws of one operator -/

section Labels

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map noCall_mapM noCall_query)
open DigestBudgets (ClassBound StateBound)

/-- A call of `H` or `PRG` that is a late draw. -/
def RoLate (L : ℕ) : (RoSpec C).Domain → Prop := fun t => LateDraw D L (.inr t)

variable {D}

/-- From the run state `st`, each path of `p` ends at a label at most `st.label + n`, and each hidden
draw of `p` is at a label below `st.label + n`. -/
def WithinAt {α : Type} (n : ℕ) (p : RunM C E RealSpec α) (st : RunState C) : Prop :=
  (∀ r, some r ∈ support (p.run st).run → r.2.label ≤ st.label + n) ∧
    IsQueryBoundP (p.run st).run (PartyLate (E := E) D (st.label + n)) 0

theorem partyLate_mono {L L' : ℕ} (h : L ≤ L') {γ : Type} {x : OracleComp (PartySpec C E RealSpec) γ}
    (hx : IsQueryBoundP x (PartyLate D L) 0) : IsQueryBoundP x (PartyLate D L') 0 :=
  IsQueryBoundP.of_imp (fun t ht => by
    rcases t with ((_ | _ | x) | _) | _
    · exact ht.elim
    · exact ht.elim
    · exact ⟨ht.1, le_trans h ht.2⟩
    · exact ht.elim
    · exact ht.elim) hx

theorem WithinAt.mono {α : Type} {n m : ℕ} {p : RunM C E RealSpec α} {st : RunState C}
    (h : WithinAt (D := D) n p st) (hnm : n ≤ m) : WithinAt (D := D) m p st :=
  ⟨fun r hr => (h.1 r hr).trans (by omega), partyLate_mono (by omega) h.2⟩

theorem withinAt_bind {α β : Type} {n m : ℕ} {p : RunM C E RealSpec α} {q : α → RunM C E RealSpec β}
    {st : RunState C} (hp : WithinAt (D := D) n p st)
    (hq : ∀ a s, some (a, s) ∈ support (p.run st).run → WithinAt (D := D) m (q a) s) :
    WithinAt (D := D) (n + m) (p >>= q) st := by
  refine ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨a, ha, hr⟩ := mem_support_run_bind p q st r hr
    have h1 := hp.1 a ha
    have h2 := (hq a.1 a.2 ha).1 r hr
    omega
  · rw [StateT.run_bind, OptionT.run_bind]
    unfold Option.elimM
    refine isQueryBoundP_bind (n := 0) (m := 0) (partyLate_mono (by omega) hp.2) fun o ho => ?_
    rcases o with _ | ⟨a, s⟩
    · exact isQueryBoundP_pure _ _ _
    · have hs := hp.1 (a, s) ho
      exact partyLate_mono (by simp only at hs ⊢; omega) (hq a s ho).2

theorem withinAt_bind_zero {α β : Type} {m : ℕ} {p : RunM C E RealSpec α} {q : α → RunM C E RealSpec β}
    {st : RunState C} (hp : WithinAt (D := D) 0 p st)
    (hq : ∀ a s, some (a, s) ∈ support (p.run st).run → WithinAt (D := D) m (q a) s) :
    WithinAt (D := D) m (p >>= q) st :=
  (withinAt_bind hp hq).mono (by omega)

theorem withinAt_pure {α : Type} (a : α) (st : RunState C) :
    WithinAt (D := D) 0 (pure a : RunM C E RealSpec α) st := by
  refine ⟨fun r hr => ?_, isQueryBoundP_pure _ _ _⟩
  obtain rfl := mem_support_run_pure a st r hr
  simp

theorem partyLate_of_stream {L : ℕ} {γ : Type} {x : OracleComp (PartySpec C E RealSpec) γ}
    (h : IsQueryBoundP x (DigestBudgets.PartyIn .stream) 0) : IsQueryBoundP x (PartyLate D L) 0 :=
  IsQueryBoundP.of_imp (fun t ht => by
    rcases t with ((_ | _ | x) | _) | _
    · exact ht.elim
    · exact ht.elim
    · rfl
    · exact ht.elim
    · exact ht.elim) h

/-- A program with no stream call that adds `n` to the label. -/
theorem withinAt_of_class {α : Type} {n : ℕ} {p : RunM C E RealSpec α} (h : StateBound (E := E) .stream p 0)
    (hm : Moves (LabelAdds n) p) (st : RunState C) : WithinAt (D := D) n p st :=
  ⟨fun r hr => le_of_eq (moves_support hm st r hr), partyLate_of_stream (h st)⟩

theorem liftComp_ro_late {L : ℕ} {α : Type} (oa : OracleComp (RoSpec C) α) :
    IsQueryBoundP oa (RoLate D L) 0 → IsQueryBoundP (liftComp oa (LocalSpec C)) (LateDraw D L) 0 :=
  SetupBudgets.liftComp_roP oa 0

theorem liftComp_party_late {L : ℕ} {α : Type} (oa : OracleComp (LocalSpec C) α) :
    IsQueryBoundP oa (LateDraw D L) 0 →
      IsQueryBoundP (liftComp oa (PartySpec C E RealSpec)) (PartyLate D L) 0 :=
  SetupBudgets.liftComp_partyP oa 0

/-- A local step of `H` and `PRG` with no draw at a label at or above the label of the state. -/
theorem withinAt_lift_oracle {α : Type} {oa : OracleComp (RoSpec C) α} (st : RunState C)
    (h : NoCall (RoLate D st.label) oa) :
    WithinAt (D := D) 0 (StateT.lift (ThresholdLeanXmss.oracleStep oa) : RunM C E RealSpec α) st := by
  refine ⟨fun r hr => ?_, ?_⟩
  · rw [StateT.run_lift] at hr
    rcases mem_support_optionT_bind _ _ _ hr with h' | ⟨a, -, hr⟩
    · cases h'
    · have : r = (a, st) := by simpa using hr
      subst this
      simp
  · rw [StateT.run_lift, OptionT.run_bind]
    unfold Option.elimM
    refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun o _ => ?_
    · unfold ThresholdLeanXmss.oracleStep ThresholdLeanXmss.localStep
      change IsQueryBoundP (liftComp (liftComp oa (LocalSpec C)) (PartySpec C E RealSpec) >>= fun a => Pure.pure (some a)) _ _
      exact isQueryBoundP_bind (n := 0) (m := 0) (partyLate_mono (by omega)
        (liftComp_party_late _ (liftComp_ro_late _ ((noCall_iff _ _).1 h)))) fun _ _ => isQueryBoundP_pure _ _ _
    · rcases o with _ | a <;> exact isQueryBoundP_pure _ _ _

theorem noCall_prgBits_late {L : ℕ} (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) (hρ : ρ < L) :
    NoCall (RoLate D L) (prgBits name key ρ idx count) := by
  unfold prgBits
  exact noCall_bind _ (noCall_mapM _ _ _ fun _ => noCall_query _ _ fun h => by
    have := h.2
    simp only at this
    omega) fun _ => noCall_pure _ _

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C)

omit [Field E] [Algebra Bit E] in
theorem withinAt_prssRandomness {R : Type} [Zero R] (codec : Codec C E R)
    (hdraw : ∀ name key ρ idx count L, ρ < L → NoCall (RoLate D L) (codec.draw name key ρ idx count))
    (idx count : ℕ) (st : RunState C) :
    WithinAt (D := D) 1 (prssRandomness ctx codec idx count : RunM C E RealSpec _) st := by
  unfold prssRandomness
  refine withinAt_bind (n := 1) (m := 0) (withinAt_of_class (p := freshLabel)
    (DigestBudgets.StateBound.modifyGet _) moves_freshLabel st) fun ρ s hs => ?_
  have hs' : (ρ, s) = (st.label, { st with label := st.label + 1 }) := by simpa [freshLabel] using hs
  cases hs'
  refine withinAt_bind (n := 0) (m := 0) (withinAt_lift_oracle _ (noCall_mapM _ _ _ fun T => ?_)) fun r s' hs' => ?_
  · split_ifs
    · exact hdraw _ _ _ _ _ _ (by simp)
    · exact noCall_pure _ _
  have hs'' : s' = { st with label := st.label + 1 } := by
    rw [StateT.run_lift] at hs'
    rcases mem_support_optionT_bind _ _ _ hs' with h' | ⟨a, -, hr⟩
    · cases h'
    · simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at hr
      exact hr.2
  subst hs''
  refine withinAt_bind (n := 0) (m := 0) (withinAt_lift_oracle _ (noCall_mapM _ _ _ fun j => ?_))
    fun _ _ _ => withinAt_pure _ _
  split
  · exact noCall_pure _ _
  · exact hdraw _ _ _ _ _ _ (by simp)

theorem withinAt_elements (idx count : ℕ) (st : RunState C) :
    WithinAt (D := D) 1 (prssRandomness ctx (elementCodec K) idx count : RunM C E RealSpec _) st :=
  withinAt_prssRandomness ctx _ (fun name key ρ idx _ _ hρ =>
    noCall_bind _ (noCall_prgBits_late name key ρ idx _ hρ) fun _ => noCall_pure _ _) idx count st

omit [Field E] [Algebra Bit E] in
theorem withinAt_bits (idx count : ℕ) (st : RunState C) :
    WithinAt (D := D) 1 (prssRandomness ctx bitCodec idx count : RunM C E RealSpec _) st :=
  withinAt_prssRandomness ctx _ (fun name key ρ idx count _ hρ => noCall_prgBits_late name key ρ idx count hρ)
    idx count st

omit [Field E] [Algebra Bit E] in
theorem noCall_late_of_stream {L : ℕ} {α : Type} {oa : OracleComp (RoSpec C) α}
    (h : NoCall (DigestBudgets.RoIn .stream) oa) : NoCall (RoLate D L) oa := by
  rw [noCall_iff] at h ⊢
  exact IsQueryBoundP.of_imp (fun t ht => by
    rcases t with _ | x
    · exact ht.elim
    · rfl) h

omit [Field E] [Algebra Bit E] in
theorem withinAt_foldlM {α γ : Type} (f : α → γ → RunM C E RealSpec α) (c : ℕ)
    (hf : ∀ a g st, WithinAt (D := D) c (f a g) st) :
    ∀ (l : List γ) (a : α) (st : RunState C), WithinAt (D := D) (l.length * c) (l.foldlM f a) st
  | [], a, st => by simpa using withinAt_pure (D := D) a st
  | g :: l, a, st => by
    rw [List.foldlM_cons]
    exact (withinAt_bind (hf a g st) fun a' s _ => withinAt_foldlM f c hf l a' s).mono (by
      simp only [List.length_cons]; ring_nf; omega)

theorem withinAt_coin (count : ℕ) (st : RunState C) :
    WithinAt (D := D) 1 ((realCheckBuildingBlocks K ctx).coin count : RunM C E RealSpec _) st := by
  unfold realCheckBuildingBlocks
  refine withinAt_bind (n := 1) (m := 0) (withinAt_elements K ctx _ _ st) fun r s _ => ?_
  refine withinAt_of_class ?_ (moves_coinWith K ctx _ _) s
  unfold coinWith
  exact DigestBudgets.StateBound.bind_zero (DigestBudgets.StateBound.lift_zero (DigestBudgets.openSh_bound K ctx _ _))
    fun _ => DigestBudgets.StateBound.pure _

theorem withinAt_extendMult (products : List (Product C E)) (st : RunState C) :
    WithinAt (D := D) 1 ((realCheckBuildingBlocks K ctx).extendMult products : RunM C E RealSpec _) st := by
  unfold realCheckBuildingBlocks
  exact withinAt_bind (n := 1) (m := 0) (withinAt_elements K ctx _ _ st) fun r s _ =>
    withinAt_of_class (DigestBudgets.reshare_bound K ctx _ _ _ _) (moves_reshare K ctx _ _ _ _) s

theorem withinAt_coinKey (st : RunState C) :
    WithinAt (D := D) 1 (coinKey K (realCheckBuildingBlocks K ctx) : RunM C E RealSpec _) st := by
  unfold coinKey
  refine withinAt_bind (n := 0) (m := 1) (withinAt_of_class DigestBudgets.StateBound.get
    (moves_get labelAdds_zero) st) fun _ s _ => ?_
  exact withinAt_bind (n := 1) (m := 0) (withinAt_coin K ctx 2 s) fun _ s' _ =>
    withinAt_lift_oracle s' (noCall_query _ _ fun h => h)

theorem withinAt_challenge (st : RunState C) :
    WithinAt (D := D) 1 (challenge K (realCheckBuildingBlocks K ctx) : RunM C E RealSpec _) st := by
  unfold challenge
  refine withinAt_bind (n := 1) (m := 0) (withinAt_coinKey K ctx st) fun key s _ => ?_
  refine withinAt_bind (n := 0) (m := 0) (withinAt_lift_oracle s (noCall_late_of_stream
    (DigestBudgets.noCall_findChallenge K (by decide) key _ _))) fun r s' _ => ?_
  split
  · exact withinAt_pure _ _
  · exact withinAt_of_class (DigestBudgets.StateBound.lift_zero DigestBudgets.ClassBound.failure)
      (moves_lift labelAdds_zero _) s'

theorem withinAt_sliceStep (τ : List E) (count : ℕ) (x : Shares C E × Shares C E × E) (j : ℕ) (st : RunState C) :
    WithinAt (D := D) 2 (sliceStep K ctx (realCheckBuildingBlocks K ctx) τ count x j) st := by
  obtain ⟨xs, ys, d⟩ := x
  unfold sliceStep
  exact withinAt_bind (n := 1) (m := 1) (withinAt_extendMult K ctx _ st) fun _ s _ =>
    withinAt_bind (n := 1) (m := 0) (withinAt_challenge K ctx s) fun _ s' _ => withinAt_pure _ _

theorem withinAt_halvingStep (width : ℕ) (x : (ℕ → E) × (ℕ → E) × E) (j : ℕ) (st : RunState C) :
    WithinAt (D := D) 2 (halvingStep K ctx (realCheckBuildingBlocks K ctx) width x j) st := by
  obtain ⟨A, B, d⟩ := x
  unfold halvingStep
  exact withinAt_bind (n := 1) (m := 1) (withinAt_extendMult K ctx _ st) fun _ s _ =>
    withinAt_bind (n := 1) (m := 0) (withinAt_challenge K ctx s) fun _ s' _ => withinAt_pure _ _

theorem withinAt_finalStep (x : (ℕ → E) × (ℕ → E) × E) (st : RunState C) :
    WithinAt (D := D) 4 (finalStep K ctx (realCheckBuildingBlocks K ctx) x) st := by
  obtain ⟨A, B, d⟩ := x
  unfold finalStep
  refine withinAt_bind (n := 1) (m := 3) (withinAt_elements K ctx _ _ st) fun w s _ => ?_
  refine withinAt_bind (n := 1) (m := 2) (withinAt_extendMult K ctx _ s) fun q s₁ _ => ?_
  refine withinAt_bind (n := 1) (m := 1) (withinAt_bits ctx _ _ s₁) fun salts s₂ _ => ?_
  refine withinAt_bind (n := 0) (m := 1) (withinAt_of_class ((DigestBudgets.compareDigests_bound ctx _).mono
    (by simp [DigestBudgets.digestCost])) (moves_compareDigests ctx _) s₂) fun _ s₃ _ => ?_
  refine withinAt_bind (n := 1) (m := 0) (withinAt_challenge K ctx s₃) fun r s₄ _ => ?_
  exact withinAt_bind (n := 0) (m := 0) (withinAt_of_class (DigestBudgets.StateBound.lift_zero
    (DigestBudgets.openSh_bound K ctx _ _)) (moves_lift labelAdds_zero _) s₄) fun _ s₅ _ =>
      withinAt_of_class (DigestBudgets.StateBound.lift_zero (DigestBudgets.ClassBound.require _))
        (moves_lift labelAdds_zero _) s₅

theorem withinAt_check (tuples : List (Tuple C)) (st : RunState C) :
    WithinAt (D := D) (checkLabels (tuples.map (·.count)).sum)
      (check K ctx (realCheckBuildingBlocks K ctx) tuples : RunM C E RealSpec Unit) st := by
  by_cases h : (tuples.map (·.count)).sum = 0
  · refine ⟨fun r hr => ?_, ?_⟩
    · rw [check_run_zero K ctx tuples h] at hr
      have : r = ((), st) := by simpa using hr
      subst this
      simp
    · rw [check_run_zero K ctx tuples h]
      exact isQueryBoundP_pure _ _ _
  have hs : sliceBits ≤ halvings (tuples.map (·.count)).sum := Nat.le_add_right _ _
  rw [check_eq K ctx _ tuples h]
  refine (withinAt_bind (n := 1) (m := 2 * halvings (tuples.map (·.count)).sum + 4)
    (withinAt_coinKey K ctx st) fun key s _ => ?_).mono ?_
  rotate_left
  · unfold checkLabels
    simp only [h, ↓reduceIte]
    omega
  refine withinAt_bind_zero
    (withinAt_of_class (DigestBudgets.expand_bound (c := .stream) K (by decide) key _)
      (by unfold expand; exact moves_lift labelAdds_zero _) s) fun τ s₁ _ => ?_
  refine withinAt_bind_zero
    (withinAt_of_class (DigestBudgets.StateBound.lift_zero (DigestBudgets.ClassBound.require _))
      (moves_lift labelAdds_zero _) s₁) fun _ s₂ _ => ?_
  have hsl : ∀ a st, WithinAt (D := D) (sliceBits * 2) ((List.range sliceBits).foldlM
      (sliceStep K ctx (realCheckBuildingBlocks K ctx) τ (tuples.map (·.count)).sum) a) st := by
    intro a st
    have h3 : ∀ a g st, WithinAt (D := D) 2 (sliceStep K ctx (realCheckBuildingBlocks K ctx) τ
        (tuples.map (·.count)).sum a g) st := fun a g st => withinAt_sliceStep K ctx τ _ a g st
    have h4 := withinAt_foldlM (D := D) _ 2 h3 (List.range sliceBits) a st
    rw [List.length_range] at h4
    exact h4
  have hhv : ∀ a st, WithinAt (D := D) ((halvings (tuples.map (·.count)).sum - sliceBits) * 2)
      ((List.range (halvings (tuples.map (·.count)).sum - sliceBits)).foldlM
        (halvingStep K ctx (realCheckBuildingBlocks K ctx) (sliceWidth (tuples.map (·.count)).sum)) a) st := by
    intro a st
    have h3 : ∀ a g st, WithinAt (D := D) 2 (halvingStep K ctx (realCheckBuildingBlocks K ctx)
        (sliceWidth (tuples.map (·.count)).sum) a g) st := fun a g st => withinAt_halvingStep K ctx _ a g st
    have h4 := withinAt_foldlM (D := D) _ 2 h3 (List.range (halvings (tuples.map (·.count)).sum - sliceBits)) a st
    rw [List.length_range] at h4
    exact h4
  refine (withinAt_bind (hsl _ s₂) fun p s₃ _ =>
    withinAt_bind (hhv _ s₃) fun p' s₄ _ => withinAt_finalStep K ctx p' s₄).mono ?_
  omega

theorem moves_reshareCollector (randomness : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    Moves (LabelAdds 0) (reshareCollector (G := RealSpec) K ctx randomness v count) := by
  obtain ⟨r, Z⟩ := randomness
  unfold reshareCollector record
  exact moves_label_bind (moves_lift labelAdds_zero _) (fun _ => moves_label_bind (a := 0) (b := 0)
    (moves_lift labelAdds_zero _) (fun _ => moves_label_bind (a := 0) (b := 0)
      (moves_modify _ fun _ => rfl) (fun _ => moves_pure labelAdds_zero _) rfl) rfl) rfl

theorem withinAt_mult (mode : ReshareMode) (x y : Shares C Bit) (count : ℕ) (st : RunState C) :
    WithinAt (D := D) 1 ((realRunBuildingBlocks K ctx mode).mult x y count : RunM C E RealSpec _) st := by
  unfold realRunBuildingBlocks reshareWith
  refine withinAt_bind (n := 1) (m := 0) (withinAt_bits ctx _ _ st) fun r s _ => ?_
  cases mode
  · exact withinAt_of_class (DigestBudgets.reshare_bound K ctx _ _ _ _) (moves_reshare K ctx _ _ _ _) s
  · exact withinAt_of_class (DigestBudgets.reshareCollector_bound K ctx _ _ _) (moves_reshareCollector K ctx _ _ _) s

theorem withinAt_rerand (mode : ReshareMode) (v : Shares C Bit) (count : ℕ) (st : RunState C) :
    WithinAt (D := D) 1 ((realRunBuildingBlocks K ctx mode).rerand v count : RunM C E RealSpec _) st := by
  unfold realRunBuildingBlocks
  exact withinAt_bind (n := 1) (m := 0) (withinAt_bits ctx _ _ st) fun r s _ =>
    withinAt_of_class (DigestBudgets.reshare_bound K ctx _ _ _ _) (moves_reshare K ctx _ _ _ _) s

theorem withinAt_runJobsHead (mode : ReshareMode) (jobs : List Circuit) (inputs : List (C.Term → List Bit))
    (st : RunState C) :
    WithinAt (D := D) (headCounts jobs).length
      (runJobsHead K (realRunBuildingBlocks K ctx mode) jobs inputs : RunM C E RealSpec _) st := by
  rw [runJobsHead_eq]
  have h3 : ∀ a g st, WithinAt (D := D) 1 (layerBody K (realRunBuildingBlocks K ctx mode) jobs a g) st :=
    fun a g st => by
      unfold layerBody
      exact withinAt_bind (n := 1) (m := 0) (withinAt_mult K ctx mode _ _ _ st) fun _ _ _ => withinAt_pure _ _
  have h4 := withinAt_foldlM (D := D) _ 1 h3 (List.range (depth jobs)) (inputs, []) st
  rw [List.length_range] at h4
  refine (withinAt_bind h4 fun p s _ => withinAt_bind (withinAt_rerand K ctx mode _ _ s)
    fun _ _ _ => withinAt_pure _ _).mono ?_
  simp [headCounts]

theorem withinAt_runJobs (mode : ReshareMode) (jobs : List Circuit) (inputs : List (C.Term → List Bit))
    (L tg : ℕ) :
    WithinAt (D := D) (batchLabel jobs)
      (runJobs K (realRunBuildingBlocks K ctx mode) jobs inputs : RunM C E RealSpec _) ⟨fun _ => [], L, tg⟩ := by
  rw [runJobs_eq_head]
  refine withinAt_bind (n := (headCounts jobs).length) (m := checkLabels (headCounts jobs).sum)
    (withinAt_runJobsHead K ctx mode jobs inputs _) fun hd s hs => ?_
  have hc := (runJobsHead_support K ctx mode jobs inputs L tg (hd, s) hs).2
  have hcheck := withinAt_check (D := D) K ctx hd.1 s
  rw [hc] at hcheck
  refine (withinAt_bind hcheck fun _ s' _ => withinAt_bind_zero
    (withinAt_of_class (DigestBudgets.StateBound.lift_zero ((DigestBudgets.openRep_bound K ctx _ _).mono
      (by simp [DigestBudgets.copyCost]))) (moves_lift labelAdds_zero _) s') fun _ _ _ => withinAt_pure _ _).mono le_rfl

end Labels

end Draws

/-! ## The prefix of one ceremony -/

section Prefix

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] Classical.propDecidable

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The label at the start of the check of batch `k` of one ceremony under the parameter
`parameter`. It is the label of the start, the labels of the batches before `k`, and one label for
each tuple of the head of batch `k`. -/
def stopLabel (parameter : PublicParameter) {σ : Type} (c : CeremonyStart C σ) (k : ℕ) : ℕ :=
  c.counters.1 + (((chunks settings.batchSize c.jobs).take k).map (jobLabel circuits parameter)).sum +
    (headCounts (((chunks settings.batchSize c.jobs).getD k []).map (circuits parameter ·.kind))).length

/-- The labels of the prefix of one ceremony. The program of an operator with keys in the prefix up
to the check of batch `k` draws under hidden names only at labels below `stopLabel`. -/
def PrefixLabels : Prop :=
  ∀ (D : C.Coalition) {σ : Type} (c : CeremonyStart C σ) (k : ℕ), k < (chunks settings.batchSize c.jobs).length →
    ∀ i keys, c.keys i = some keys →
      IsQueryBoundP (cutCeremony K circuits settings k i c).run
        (Draws.PartyLate D (stopLabel circuits settings keys.parameter c k)) 0

/-- The stop of the prefix of one ceremony is at `stopLabel`. -/
theorem cutCeremony_stopLabel {σ : Type} (c : CeremonyStart C σ) (k : ℕ) (i : C.Party) (keys : Keys C)
    (hkeys : c.keys i = some keys) (point : CheckPoint C) (rest : RunState C → PartyM C E RealSpec RunResult)
    (ho : some (.inr (point, rest)) ∈ support (cutCeremony K circuits settings k i c).run) :
    point.state.label = stopLabel circuits settings keys.parameter c k := by
  simp only [cutCeremony, hkeys] at ho
  obtain ⟨prss, pre, js, suf, hchunks, hlen, hpoint⟩ :=
    (cutWalk_cutRun K circuits settings (c.counters.2 + k) i keys c.jobs c.counters _ ho).2 point rest rfl
  have hk : pre.length = k := by omega
  obtain ⟨-, hcounts, hstate⟩ := hpoint
  rw [hstate]
  unfold stopLabel
  have hg : (pre ++ js :: suf).getD pre.length [] = js := by simp
  rw [hchunks, ← hk, List.take_left' rfl, hg, ← hcounts, List.length_map]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A joint start of a check has the world of the prefix, the PRSS keys of the stops, and the label of
the stop of an honest operator. -/
theorem jointStop_lead {α : Type} {D : C.Coalition} {σ : Type} {r : σ × (C.Party → Option (CutOf C E α))}
    {world : StreamState C} {start : CheckStart C σ} (h : jointStop D r world = some start) :
    start.world = world ∧ (∀ i, start.prss i = (stopPoint i (r.2 i)).ctx.prss) ∧
      ∃ j point rest, j ∉ D.1 ∧ r.2 j = some (.inr (point, rest)) ∧ start.L = point.state.label := by
  unfold jointStop at h
  split_ifs at h with hall
  split at h
  · rename_i j hj
    cases h
    have hjD : j ∉ D.1 := by simpa using (List.find?_some hj)
    obtain ⟨point, rest, hp⟩ := hall j hjD
    exact ⟨rfl, fun _ => rfl, j, point, rest, hjD, hp, by simp [stopPoint, hp]⟩
  · cases h

/-- `CeremonyInterval` from the labels of the prefix. Each new hidden cell of the prefix has a label
below the common stop label, and `KeysFresh` excludes an old cell under a key of the start. -/
theorem ceremonyInterval_of_prefixLabels (h : PrefixLabels K circuits settings) :
    CeremonyInterval prims K circuits settings := by
  intro D net rounds ℓ c world hready k hk z hz start hstart _ hfresh
  unfold ceremonyPrefix at hz
  have hp : ∀ j, j ∉ D.1 → IsQueryBoundP (cutCeremony K circuits settings k j c).run
      (Draws.PartyLate D (stopLabel circuits settings (gameParameter D c.keys) c k)) 0 := by
    intro j hj
    rcases hkj : c.keys j with _ | kj
    · simp only [cutCeremony, hkj]
      exact isQueryBoundP_pure _ _ _
    · have := h D c k hk j kj hkj
      rwa [parameter_eq_gameParameter D c.keys hready.1 j hj kj hkj] at this
  have hcells := Draws.executePhase_cellsBelow D prims _ net rounds c.adversary _ hp world z hz
  obtain ⟨hw, -, j, point, rest, hjD, hjp, hL⟩ := jointStop_lead hstart
  have hout := Draws.executePhase_output D prims net rounds c.adversary _ world z hz j hjD _ hjp
  have hlabel : start.L = stopLabel circuits settings (gameParameter D c.keys) c k := by
    rcases hkj : c.keys j with _ | kj
    · simp [cutCeremony, hkj] at hout
    · rw [hL, cutCeremony_stopLabel K circuits settings c k j kj hkj point rest hout,
        parameter_eq_gameParameter D c.keys hready.1 j hjD kj hkj]
  rw [hw]
  intro i hi ρ hρ idx position
  rw [hlabel] at hρ
  have hnone : ∀ name key, NameKey i (start.prss i) name key → Hidden D name →
      z.2.2 ((name, key), ρ, idx, position) = none := by
    intro name key hk' hN
    by_contra hne
    rcases hcells name key ρ idx position hne with hold | hlt
    · exact hold (hfresh i hi name key hk' hN ρ idx position)
    · omega
  exact ⟨fun T hT hN => hnone _ _ (Or.inl ⟨T, hT, rfl, rfl⟩) hN,
    fun j' hj' hN => hnone _ _ (Or.inr ⟨j', hj', rfl, rfl⟩) hN⟩

/-! ## The labels of the draws of the prefix of one ceremony -/

section CutLabels

variable {D : C.Coalition} {K}

/-- The program on the counters from `st` makes no hidden draw at a label at or above `L` before its
stop. -/
def CutLate (L : ℕ) {α : Type} (x : CutM K α) (st : ℕ × ℕ) : Prop :=
  IsQueryBoundP ((x.run st).run).run (Draws.PartyLate (E := E) D L) 0

/-- The program on the counters from `st` makes no hidden draw at a label at or above `L`. -/
def StateLate (L : ℕ) {α : Type} (y : StateT (ℕ × ℕ) (PartyM C E RealSpec) α) (st : ℕ × ℕ) : Prop :=
  IsQueryBoundP (y.run st).run (Draws.PartyLate (E := E) D L) 0

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem partyLate_bind {L : ℕ} {α β : Type} {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β}
    (hp : IsQueryBoundP p.run (Draws.PartyLate (E := E) D L) 0)
    (hf : ∀ a, some a ∈ support p.run → IsQueryBoundP (f a).run (Draws.PartyLate (E := E) D L) 0) :
    IsQueryBoundP (p >>= f).run (Draws.PartyLate (E := E) D L) 0 := by
  rw [OptionT.run_bind]
  unfold Option.elimM
  refine isQueryBoundP_bind (n := 0) (m := 0) hp fun o ho => ?_
  rcases o with _ | a
  · exact isQueryBoundP_pure _ _ _
  · exact hf a ho

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem stateLate_bind {L : ℕ} {α β : Type} {y : StateT (ℕ × ℕ) (PartyM C E RealSpec) α}
    {f : α → StateT (ℕ × ℕ) (PartyM C E RealSpec) β} {st : ℕ × ℕ} (hy : StateLate (D := D) L y st)
    (hf : ∀ a s, some (a, s) ∈ support (y.run st).run → StateLate (D := D) L (f a) s) :
    StateLate (D := D) L (y >>= f) st := by
  unfold StateLate
  rw [StateT.run_bind]
  exact partyLate_bind hy fun a ha => hf a.1 a.2 ha

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem stateLate_pure {L : ℕ} {α : Type} (a : α) (st : ℕ × ℕ) :
    StateLate (D := D) L (pure a : StateT (ℕ × ℕ) (PartyM C E RealSpec) α) st := isQueryBoundP_pure _ _ _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem stateLate_lift {L : ℕ} {α : Type} {x : PartyM C E RealSpec α}
    (hx : IsQueryBoundP x.run (Draws.PartyLate (E := E) D L) 0) (st : ℕ × ℕ) :
    StateLate (D := D) L (StateT.lift x : StateT (ℕ × ℕ) (PartyM C E RealSpec) α) st := by
  unfold StateLate
  change IsQueryBoundP (x >>= fun a => Pure.pure (a, st)).run _ _
  exact partyLate_bind hx fun _ _ => isQueryBoundP_pure _ _ _

omit [Fintype E] [DecidableEq E] in
theorem cutLate_bind {L : ℕ} {α β : Type} {x : CutM K α} {f : α → CutM K β} {st : ℕ × ℕ}
    (hx : CutLate (D := D) L x st)
    (hf : ∀ a s, some (.inl (a, s)) ∈ support ((x.run st).run).run → CutLate (D := D) L (f a) s) :
    CutLate (D := D) L (x >>= f) st := by
  unfold CutLate
  rw [StateT.run_bind, Paused.run_bind]
  refine partyLate_bind hx fun o ho => ?_
  rcases o with ⟨a, s⟩ | ⟨point, rest⟩
  · exact hf a s ho
  · exact isQueryBoundP_pure _ _ _

omit [Fintype E] [DecidableEq E] in
theorem cutLate_pure {L : ℕ} {α : Type} (a : α) (st : ℕ × ℕ) : CutLate (D := D) L (pure a : CutM K α) st :=
  isQueryBoundP_pure _ _ _

omit [Fintype E] [DecidableEq E] in
theorem cutLate_lift {L : ℕ} {α : Type} {y : StateT (ℕ × ℕ) (PartyM C E RealSpec) α} {st : ℕ × ℕ}
    (hy : StateLate (D := D) L y st) : CutLate (D := D) L (CutM.lift (K := K) y) st := by
  unfold CutLate
  rw [CutM.lift_run]
  unfold Paused.lift
  rw [OptionT.run_map]
  exact (isQueryBoundP_map_iff _ _ _).2 hy

omit [Fintype E] [DecidableEq E] in
theorem cutLate_stop_bind {L : ℕ} {β : Type} (point : CheckPoint C) (f : RunState C → CutM K β) (st : ℕ × ℕ) :
    CutLate (D := D) L (StateT.lift (Paused.stop point) >>= f) st := by
  refine cutLate_bind (isQueryBoundP_pure _ _ _) fun a s ha => ?_
  rw [StateT.run_lift, Paused.run_bind] at ha
  simp [Paused.stop] at ha

omit [Fintype E] [DecidableEq E] in
/-- A full real batch from the label `st.1` draws only below `st.1` plus `jobLabel`. -/
theorem stateLate_realBatch (ctx : Context C) (parameter : PublicParameter) (js : List Job) (st : ℕ × ℕ) (L : ℕ)
    (hL : st.1 + jobLabel circuits parameter js ≤ L) :
    StateLate (D := D) L (realBatch K circuits settings.mode ctx parameter js) st := by
  unfold realBatch
  refine stateLate_bind (stateLate_pure _ _) fun lk s hs => ?_
  have hs' : (lk, s) = (st, st) := by simpa using hs
  cases hs'
  refine stateLate_bind (stateLate_lift (Draws.partyLate_of_stream ((DigestBudgets.ClassBound.mapM _ 0
    (fun job => DigestBudgets.inputShares_bound _ (by decide) job) _).mono (by simp))) _) fun inputs s' hs' => ?_
  refine stateLate_bind (stateLate_lift (Draws.partyLate_mono hL
    (Draws.withinAt_runJobs (D := D) K ctx settings.mode _ inputs st.1 st.2).2) _) fun r s'' _ => ?_
  exact stateLate_bind (stateLate_pure _ _) fun _ _ _ => stateLate_pure _ _

omit [Fintype E] [DecidableEq E] in
/-- The batch of the stop from the label `st.1` draws only below `st.1` plus the head of the batch. -/
theorem cutLate_cutBatch (ctx : Context C) (parameter : PublicParameter) (js : List Job) (st : ℕ × ℕ) :
    CutLate (D := D) (st.1 + (headCounts (js.map (circuits parameter ·.kind))).length)
      (cutBatch K circuits settings ctx parameter js) st := by
  unfold cutBatch
  refine cutLate_bind (cutLate_pure _ _) fun lk s hs => ?_
  have hs' : (lk, s) = (st, st) := by simpa [Paused.run_pure] using hs
  cases hs'
  refine cutLate_bind (cutLate_lift (stateLate_lift (Draws.partyLate_of_stream ((DigestBudgets.ClassBound.mapM _ 0
    (fun job => DigestBudgets.inputShares_bound _ (by decide) job) _).mono (by simp))) _)) fun inputs s' hs' => ?_
  refine cutLate_bind (cutLate_lift (stateLate_lift (Draws.withinAt_runJobsHead (D := D) K ctx settings.mode _ inputs
    ⟨fun _ => [], st.1, st.2⟩).2 _)) fun r s'' _ => ?_
  exact cutLate_stop_bind _ _ _

omit [Fintype E] [DecidableEq E] in
/-- A walk over the batches up to the stop in batch `kk` from the tag `st.2`. Each batch before the
stop draws below its end label, and the batch of the stop draws below the label of the stop. -/
theorem cutLate_mapM {β : Type} (body : List Job → CutM K β) (k : ℕ) (f g : List Job → ℕ)
    (hlate : ∀ js st, (st.2 = k → CutLate (D := D) (st.1 + g js) (body js) st) ∧
      (st.2 ≠ k → ∀ L, st.1 + f js ≤ L → CutLate (D := D) L (body js) st))
    (hwalk : ∀ js st a s, some (.inl (a, s)) ∈ support (((body js).run st).run).run →
      st.2 ≠ k ∧ s = (st.1 + f js, st.2 + 1)) :
    ∀ (l : List (List Job)) (st : ℕ × ℕ) (kk : ℕ), kk < l.length → st.2 + kk = k →
      CutLate (D := D) (st.1 + ((l.take kk).map f).sum + g (l.getD kk [])) (l.mapM body) st
  | [], _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | b :: l, st, kk, hk, hkk => by
    rw [List.mapM_cons]
    rcases kk with _ | kk
    · simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, List.getD_cons_zero]
      refine cutLate_bind ((hlate b st).1 (by omega)) fun a s ha => ?_
      have := (hwalk b st a s ha).1
      omega
    · have hle : st.1 + f b ≤ st.1 + (((b :: l).take (kk + 1)).map f).sum + g ((b :: l).getD (kk + 1) []) := by
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        omega
      refine cutLate_bind ((hlate b st).2 (by omega) _ hle) fun a s ha => ?_
      obtain ⟨-, rfl⟩ := hwalk b st a s ha
      have hk' : kk < l.length := by
        simp only [List.length_cons] at hk
        omega
      have hkk' : (st.1 + f b, st.2 + 1).2 + kk = k := by
        show st.2 + 1 + kk = k
        omega
      have ih := cutLate_mapM body k f g hlate hwalk l (st.1 + f b, st.2 + 1) kk hk' hkk'
      have e : st.1 + f b + ((l.take kk).map f).sum + g (l.getD kk []) =
          st.1 + (((b :: l).take (kk + 1)).map f).sum + g ((b :: l).getD (kk + 1) []) := by
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getD_cons_succ]
        omega
      rw [← e]
      exact cutLate_bind ih fun _ _ _ => cutLate_pure _ _

end CutLabels

/-- The labels of the prefix of one ceremony. The setup draws nothing, each batch before the stop
draws below its end label, and the batch of the stop draws below the label of the stop. -/
theorem prefixLabels : PrefixLabels K circuits settings := by
  intro D σ c k hk i keys hkeys
  simp only [cutCeremony, hkeys]
  change CutLate (D := D) _ (cutRun K circuits settings (c.counters.2 + k) i keys c.jobs) c.counters
  rw [SetupCut.cutRun_eq]
  refine cutLate_bind (cutLate_lift (stateLate_lift (Draws.partyLate_of_stream
    (DigestBudgets.prssSetup_bound (c := .stream) (by decide) i)) _)) fun prss s hs => ?_
  have hs' : s = c.counters :=
    (mem_support_lift_run _ _ _ (((cutWalk_lift (K := K) _ (fun _ _ => False)) c.counters _ hs).1 (prss, s) rfl)).1
  subst hs'
  unfold SetupCut.cutBatches batched
  let body : List Job → CutM K (Option (List (List Bit))) := fun js => do
    let (_, tag) ← get
    if tag = c.counters.2 + k then cutBatch K circuits settings ⟨i, keys, prss⟩ keys.parameter js
    else CutM.lift (realBatch K circuits settings.mode ⟨i, keys, prss⟩ keys.parameter js)
  have hwalk' : ∀ js, CutWalk (fun st _ => st.2 ≠ c.counters.2 + k) (fun _ _ => True) (body js) := by
    intro js
    refine cutWalk_mono (cutWalk_bind (cutWalk_get (fun _ _ => False)) (P₂ := fun p _ _ => p.2 ≠ c.counters.2 + k)
      (Q₂ := fun _ _ _ => True) fun p => ?_) ?_ ?_
    · rcases p with ⟨_, tag⟩
      dsimp only
      split_ifs with h
      · exact cutWalk_mono (cutWalk_cutBatch K circuits settings i keys prss js) (fun _ _ h => h.elim)
          (fun _ _ _ => trivial)
      · exact cutWalk_mono (cutWalk_lift _ _) (fun _ _ _ => h) (fun _ _ h => h)
    · rintro st r ⟨a, rfl, h⟩
      exact h
    · intros
      trivial
  have hmap := cutLate_mapM (D := D) body (c.counters.2 + k) (jobLabel circuits keys.parameter)
    (fun js => (headCounts (js.map (circuits keys.parameter ·.kind))).length)
    (fun js st => by
      refine ⟨fun hst => ?_, fun hst L hL => ?_⟩
      · refine cutLate_bind (cutLate_pure _ _) fun lk s' hs' => ?_
        have e : (lk, s') = (st, st) := by simpa [Paused.run_pure] using hs'
        cases e
        dsimp only
        simp only [hst, ↓reduceIte]
        exact cutLate_cutBatch circuits settings _ _ _ st
      · refine cutLate_bind (cutLate_pure _ _) fun lk s' hs' => ?_
        have e : (lk, s') = (st, st) := by simpa [Paused.run_pure] using hs'
        cases e
        dsimp only
        simp only [hst, ↓reduceIte]
        exact cutLate_lift (stateLate_realBatch circuits settings _ _ _ st L hL))
    (fun js st a s' ha => ⟨((hwalk' js) st _ ha).1 (a, s') rfl,
      ((cutWalk_batch K circuits settings (c.counters.2 + k) i keys prss js) st _ ha).1 (a, s') rfl⟩)
    (chunks settings.batchSize c.jobs) c.counters k hk rfl
  exact cutLate_bind hmap fun _ _ _ => cutLate_pure _ _

/-- The label freshness of one ceremony. -/
theorem ceremonyInterval : CeremonyInterval prims K circuits settings :=
  ceremonyInterval_of_prefixLabels prims K circuits settings (prefixLabels K circuits settings)

end Prefix

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyInterval_of_prefixLabels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyInterval_of_prefixLabels

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyInterval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyInterval
