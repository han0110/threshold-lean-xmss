import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Records.Records
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.SharesAgree
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Statements
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.BatchRecords
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.OpeningDigests
import ThresholdLeanXmssSecurity.Proof.Pilot.Final

/-!
# The stream cells of the draws on the recorded run

`Holds P hist p` states that on each path the program `p` ends with a leaf in `P`, where `hist` holds
the answers of the reads of `PRG` on the path. `executePhaseR_holds` follows it through a ghost phase
in `streamWorld`, where each read of an honest operator leaves its stream cell. `holds_recCeremony`
gives it for the record of one ceremony, with the shares after `Rerand` of each term with no filler
as reads at the label of `Rerand`.

The namespace `DigestRound` walks the ghost run to the digest round of a check (`DigestWait`,
`checkReach`, `reachD_recCeremony`). `ghost_digestRound` gives the digest lists that an honest operator
with a result compared, which agree on the honest holders of each term and are the honest digests
of the starts. `recordedRerandDraws` and `recordedDigests` are two parts of the agreement of the
opened outputs, and `ceremonyOutputsAgree_of_rest` reduces `CeremonyOutputsAgree` to the ghost path,
the start of each check and the term keys.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace RerandCells

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## The reads of `PRG` on a path -/

section Holds

variable {C : Committee} {E : Type}

/-- The answer of a local query as a list of reads of `PRG`. It is one pair for a read, and it is
empty for each other query. -/
def streamLog : (q : (LocalSpec C).Domain) → (LocalSpec C).Range q → List (PrgInput C × Bit)
  | .inr (.inr x), r => [(x, r)]
  | _, _ => []

/-- On each path, the program ends with a leaf in `P` at the reads `hist` of the path. -/
inductive Holds {γ : Type} (P : List (PrgInput C × Bit) → γ → Prop) :
    List (PrgInput C × Bit) → OracleComp (PartySpec C E RealSpec) γ → Prop
  | pure (hist : List (PrgInput C × Bit)) (x : γ) (h : P hist x) : Holds P hist (pure x)
  | queryLocal (hist : List (PrgInput C × Bit)) (q : (LocalSpec C).Domain)
      (k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) γ)
      (h : ∀ r, Holds P (streamLog q r ++ hist) (k r)) : Holds P hist (.liftBind (.inl (.inl q)) k)
  | round (hist : List (PrgInput C × Bit)) (out : Mail C E) (k : Mail C E → OracleComp (PartySpec C E RealSpec) γ)
      (h : ∀ r, Holds P hist (k r)) : Holds P hist (.liftBind (.inl (.inr out)) k)

variable {γ δ : Type}

theorem holds_bind {P : List (PrgInput C × Bit) → δ → Prop} {Q : List (PrgInput C × Bit) → γ → Prop}
    {hist : List (PrgInput C × Bit)} {p : OracleComp (PartySpec C E RealSpec) γ}
    {g : γ → OracleComp (PartySpec C E RealSpec) δ} (hp : Holds Q hist p)
    (hg : ∀ h y, Q h y → Holds P h (g y)) : Holds P hist (p >>= g) := by
  induction hp with
  | pure hist x hx => rw [pure_bind]; exact hg hist x hx
  | queryLocal hist q k _ ih => exact Holds.queryLocal hist q _ ih
  | round hist out k _ ih => exact Holds.round hist out _ ih

theorem Holds.imp {P P' : List (PrgInput C × Bit) → γ → Prop} {hist : List (PrgInput C × Bit)}
    {p : OracleComp (PartySpec C E RealSpec) γ} (hp : Holds P hist p) (h : ∀ hist x, P hist x → P' hist x) :
    Holds P' hist p := by
  induction hp with
  | pure hist x hx => exact Holds.pure hist x (h hist x hx)
  | queryLocal hist q k _ ih => exact Holds.queryLocal hist q _ ih
  | round hist out k _ ih => exact Holds.round hist out _ ih

/-- The reads only grow along a path. -/
theorem holds_grow {P : List (PrgInput C × Bit) → γ → Prop} {hist : List (PrgInput C × Bit)}
    {p : OracleComp (PartySpec C E RealSpec) γ} (hp : Holds P hist p) :
    Holds (fun h x => hist ⊆ h ∧ P h x) hist p := by
  induction hp with
  | pure hist x hx => exact Holds.pure hist x ⟨List.Subset.refl _, hx⟩
  | queryLocal hist q k _ ih =>
    exact Holds.queryLocal hist q _ fun r => (ih r).imp fun h y hy =>
      ⟨fun a ha => hy.1 (List.mem_append_right _ ha), hy.2⟩
  | round hist out k _ ih => exact Holds.round hist out _ ih

/-- A leaf of a path is in the support of the program. -/
theorem holds_support {P : List (PrgInput C × Bit) → γ → Prop} {hist : List (PrgInput C × Bit)}
    {p : OracleComp (PartySpec C E RealSpec) γ} (hp : Holds P hist p) :
    Holds (fun h x => x ∈ support p ∧ P h x) hist p := by
  induction hp with
  | pure hist x hx => exact Holds.pure hist x ⟨by simp, hx⟩
  | queryLocal hist q k _ ih =>
    exact Holds.queryLocal hist q _ fun r => (ih r).imp fun h y hy =>
      ⟨(mem_support_bind_iff (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
        (Sum.inl (Sum.inl q)))) k y).2 ⟨r, by simp, hy.1⟩, hy.2⟩
  | round hist out k _ ih =>
    exact Holds.round hist out _ fun r => (ih r).imp fun h y hy =>
      ⟨(mem_support_bind_iff (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
        (Sum.inl (Sum.inr out)))) k y).2 ⟨r, by simp, hy.1⟩, hy.2⟩

/-- A program whose leaves have `P` at each larger list of reads. -/
theorem holds_of_support {P : List (PrgInput C × Bit) → γ → Prop} (p : OracleComp (PartySpec C E RealSpec) γ) :
    ∀ hist, (∀ x ∈ support p, ∀ h, hist ⊆ h → P h x) → Holds P hist p := by
  induction p using OracleComp.inductionOn with
  | pure x => exact fun hist h => Holds.pure hist x (h x (by simp) hist (List.Subset.refl _))
  | query_bind t k ih =>
    intro hist h
    rcases t with (q | out) | input
    · exact Holds.queryLocal hist q _ fun r => ih r _ fun x hx h' hsub =>
        h x ((mem_support_bind_iff _ _ _).2 ⟨r, by simp, hx⟩) h' fun a ha => hsub (List.mem_append_right _ ha)
    · exact Holds.round hist out _ fun r => ih r _ fun x hx h' hsub =>
        h x ((mem_support_bind_iff _ _ _).2 ⟨r, by simp, hx⟩) h' hsub
    · exact input.elim

end Holds

/-! ## The walk of the ghost executor -/

section Walk

variable {C : Committee} {E : Type} {α ρ : Type} (prims : Primitives) (Dw : C.Coalition)

/-- Each read of `hist` has its stream cell in the world `w`. -/
def Celled (hist : List (PrgInput C × Bit)) (w : HashCache C × HiddenCache C) : Prop :=
  ∀ p ∈ hist, StreamCell prims Dw p.1 w p.2

variable {prims Dw}

theorem Celled.mono {hist : List (PrgInput C × Bit)} {w w' : HashCache C × HiddenCache C}
    (h : Celled prims Dw hist w) (hle : w ≤ w') : Celled prims Dw hist w' :=
  fun p hp => (h p hp).mono prims Dw (Prod.mk_le_mk.1 hle).1 (Prod.mk_le_mk.1 hle).2

variable (prims Dw)

/-- A ghost step that is done with a leaf in `P`, or that waits with a continuation that holds `P`,
with reads whose cells are in `w`. -/
def StepHolds (P : List (PrgInput C × Bit) → Option α × ρ → Prop) (w : HashCache C × HiddenCache C) :
    RStep C E RealSpec α ρ → Prop
  | .done out record => ∃ hist, Celled prims Dw hist w ∧ P hist (out, record)
  | .wait _ resume => ∃ hist, Celled prims Dw hist w ∧ ∀ inbox, Holds P hist (resume inbox)
  | .call _ _ => False

variable {prims Dw}

theorem StepHolds.mono {P : List (PrgInput C × Bit) → Option α × ρ → Prop} {w w' : HashCache C × HiddenCache C}
    {s : RStep C E RealSpec α ρ} (h : StepHolds prims Dw P w s) (hle : w ≤ w') : StepHolds prims Dw P w' s := by
  cases s with
  | done out record => obtain ⟨hist, hc, hp⟩ := h; exact ⟨hist, hc.mono hle, hp⟩
  | wait outbox resume => obtain ⟨hist, hc, hp⟩ := h; exact ⟨hist, hc.mono hle, hp⟩
  | call input resume => exact h

variable (prims Dw)

/-- A local query in `streamWorld` leaves the stream cell of its read. -/
theorem streamWorld_streamLog (q : (LocalSpec C).Domain) (s : HashCache C × HiddenCache C)
    (y : (LocalSpec C).Range q × (HashCache C × HiddenCache C))
    (hy : y ∈ support ((streamWorld prims Dw (.inr q)).run s)) : Celled prims Dw (streamLog q y.1) y.2 := by
  rcases q with n | q | x
  · intro p hp
    simp [streamLog] at hp
  · intro p hp
    simp [streamLog] at hp
  · intro p hp
    simp only [streamLog, List.mem_singleton] at hp
    subst hp
    exact freeRead_cell prims Dw x s y hy

/-- The local steps of a program in `streamWorld` from a world with the cells of `hist` stop at a
step that holds `P` with reads whose cells are in the new world. -/
theorem holds_advanceR {P : List (PrgInput C × Bit) → Option α × ρ → Prop} {hist : List (PrgInput C × Bit)}
    {p : OracleComp (PartySpec C E RealSpec) (Option α × ρ)} (h : Holds P hist p) :
    ∀ s z, Celled prims Dw hist s → z ∈ support ((simulateQ (streamWorld prims Dw) (free (advanceR p))).run s) →
      StepHolds prims Dw P z.2 z.1 := by
  induction h with
  | pure hist x hx =>
    intro s z hc hz
    change z ∈ support ((simulateQ (streamWorld prims Dw) (free (pure (RStep.done x.1 x.2)))).run s) at hz
    simp only [free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hist, hc, hx⟩
  | queryLocal hist q k _ ih =>
    intro s z hc hz
    change z ∈ support ((simulateQ (streamWorld prims Dw) (free (OracleComp.lift
      (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advanceR (k r)))).run s) at hz
    simp only [free, simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    rw [simulateQ_HasQuery_query] at hy
    have hle : s ≤ y.2 := streamWorld_le prims Dw (liftM ((WorldSpec C).query (.inr q))) s y (by
      rw [simulateQ_query]; simpa using hy)
    refine ih y.1 y.2 z ?_ hz
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact streamWorld_streamLog prims Dw q s y hy a ha
    · exact (hc a ha).mono prims Dw (Prod.mk_le_mk.1 hle).1 (Prod.mk_le_mk.1 hle).2
  | round hist out k h _ =>
    intro s z hc hz
    change z ∈ support ((simulateQ (streamWorld prims Dw) (free (pure (RStep.wait out k)))).run s) at hz
    simp only [free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hist, hc, h⟩

/-- Each computation of a sequence in `streamWorld` from a world above `w₀` gives a value with a
property that a larger world keeps. Then the sequence gives each value with the property at the end
world. -/
theorem sequenceFin_world {β : Type} (w₀ : HashCache C × HiddenCache C) :
    ∀ {n : ℕ} (Q : Fin n → β → (HashCache C × HiddenCache C) → Prop) (f : Fin n → OracleComp (WorldSpec C) β),
      (∀ i b w w', Q i b w → w ≤ w' → Q i b w') →
      (∀ i s y, w₀ ≤ s → y ∈ support ((simulateQ (streamWorld prims Dw) (f i)).run s) → Q i y.1 y.2) →
      ∀ s z, w₀ ≤ s → z ∈ support ((simulateQ (streamWorld prims Dw) (OverPermutation.sequenceFin f)).run s) →
        ∀ i, Q i (z.1 i) z.2
  | 0, _, _, _, _, _, _, _, _, i => i.elim0
  | n + 1, Q, f, hmono, hf, s, z, hs, hz, i => by
    simp only [OverPermutation.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, w, hw, rfl⟩ := hz
    cases i using Fin.cases with
    | zero => exact hmono 0 _ _ _ (hf 0 s y hs hy) (streamWorld_le prims Dw _ y.2 w hw)
    | succ i =>
      exact sequenceFin_world w₀ (fun i => Q i.succ) (fun i => f i.succ) (fun i => hmono i.succ)
        (fun i => hf i.succ) y.2 w (hs.trans (streamWorld_le prims Dw _ s y hy)) hw i

variable {Ia : Type} (D' : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (blank : ρ)
  (P : C.Party → List (PrgInput C × Bit) → Option α × ρ → Prop)

/-- A round of the ghost executor in `streamWorld` keeps each honest step holding its leaf property. -/
theorem stepRoundR_holds (st : A.State) (steps : C.Party → RStep C E RealSpec α ρ)
    (s : HashCache C × HiddenCache C) (h : ∀ i, i ∉ D'.1 → StepHolds prims Dw (P i) s (steps i))
    (y : (A.State × (C.Party → RStep C E RealSpec α ρ) × (C.Party → C.Party → Option (Msg E))) ×
      (HashCache C × HiddenCache C))
    (hy : y ∈ support ((simulateQ (streamWorld prims Dw)
      (stepRoundR worldRoles D' A noFunctionality blank st steps)).run s)) :
    ∀ i, i ∉ D'.1 → StepHolds prims Dw (P i) y.2 (y.1.2.1 i) := by
  have hcall : ∀ i, (steps i).callInput = none := fun i => by
    rcases steps i with _ | _ | ⟨input, _⟩
    · rfl
    · rfl
    · exact input.elim
  have hno : ¬ ((∃ i, i ∉ D'.1 ∧ (steps i).callInput.isSome) ∧
      ∀ i, i ∉ D'.1 → (steps i).callInput.isSome ∨ (steps i).isDone) := fun ⟨⟨i, _, hi⟩, _⟩ => by
    rw [hcall i] at hi
    cases hi
  unfold stepRoundR at hy
  rw [ite_eq_right hno] at hy
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨a, ha, w, hw, rfl⟩ := hy
  refine sequenceFin_world prims Dw s (fun j v c => j ∉ D'.1 → StepHolds prims Dw (P j) c v) _
    (fun j b c c' hq hle hj => (hq hj).mono hle) (fun j s' y hs' hy hj => ?_) a.2 w
    (streamWorld_le prims Dw _ s a ha) hw
  have hj' := h j hj
  rcases hsj : steps j with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · simp only [hsj, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rw [hsj] at hj'
    exact hj'.mono hs'
  · simp only [hsj, hj, ↓reduceIte] at hy
    rw [hsj] at hj'
    obtain ⟨hist, hc, hr⟩ := hj'
    exact holds_advanceR prims Dw (hr _) s' y (hc.mono hs') hy
  · exact input.elim

/-- The rounds of the ghost executor in `streamWorld` keep each honest step holding its leaf property. -/
theorem executeRoundsR_holds : ∀ (fuel : ℕ) (st : A.State) (steps : C.Party → RStep C E RealSpec α ρ)
    (s : HashCache C × HiddenCache C), (∀ i, i ∉ D'.1 → StepHolds prims Dw (P i) s (steps i)) →
    ∀ z ∈ support ((simulateQ (streamWorld prims Dw)
      (executeRoundsR worldRoles D' A noFunctionality blank fuel st steps)).run s),
      ∀ i, i ∉ D'.1 → StepHolds prims Dw (P i) z.2 (z.1.2 i)
  | 0, st, steps, s, h, z, hz => by
    simp only [executeRoundsR, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact h
  | fuel + 1, st, steps, s, h, z, hz => by
    unfold executeRoundsR at hz
    split_ifs at hz
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨r, hr, hz⟩ := hz
    exact executeRoundsR_holds fuel r.1.1 r.1.2.1 r.2 (stepRoundR_holds prims Dw D' A blank P st steps s h r hr) z hz

/-- A ghost phase in `streamWorld` ends with each honest step holding its leaf property, with reads
whose cells are in the end world. -/
theorem executePhaseR_holds (fuel : ℕ) (st : A.State)
    (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (h : ∀ i, i ∉ D'.1 → Holds (P i) [] (program i)) (s : HashCache C × HiddenCache C) :
    ∀ z ∈ support ((simulateQ (streamWorld prims Dw)
      (executePhaseR worldRoles D' A noFunctionality blank fuel st program)).run s),
      ∀ i, i ∉ D'.1 → StepHolds prims Dw (P i) z.2 (z.1.2 i) := by
  intro z hz
  unfold executePhaseR at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  unfold startStepsR at hy
  refine executeRoundsR_holds prims Dw D' A blank P fuel st y.1 y.2 (fun i hi => ?_) z hz
  refine sequenceFin_world prims Dw s (fun j v c => j ∉ D'.1 → StepHolds prims Dw (P j) c v) _
    (fun j b c c' hq hle hj => (hq hj).mono hle) (fun j s' w _ hw hj => ?_) s y le_rfl hy i hi
  simp only [hj, ↓reduceIte] at hw
  exact holds_advanceR prims Dw (h j hj) s' w (fun _ hp => absurd hp List.not_mem_nil) hw

end Walk

/-! ## The reads of the draws -/

section Draws

variable {C : Committee} {E : Type} {γ : Type}

/-- One read of `PRG`. -/
def readBit (x : PrgInput C) : OracleComp (RoSpec C) Bit := query (spec := RoSpec C) (.inr x)

theorem liftComp_read (x : PrgInput C) :
    liftComp (liftComp (readBit x) (LocalSpec C)) (PartySpec C E RealSpec) =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl (.inr (.inr x))))) :=
  rfl

/-- The reads of `PRG` at the positions of a list put their answers into the reads of the path. -/
theorem holds_reads_bind {P : List (PrgInput C × Bit) → γ → Prop} (name : KeyName C) (key : HashOutput)
    (ρ idx : ℕ) :
    ∀ (l : List ℕ) (hist : List (PrgInput C × Bit)) (k : List Bit → OracleComp (PartySpec C E RealSpec) γ),
      (∀ bs h, hist ⊆ h → List.Forall₂ (fun position b => ((name, key, ρ, idx, position), b) ∈ h) l bs →
        Holds P h (k bs)) →
      Holds P hist (liftComp (liftComp (l.mapM fun position => readBit (name, key, ρ, idx, position))
          (LocalSpec C)) (PartySpec C E RealSpec) >>= k)
  | [], hist, k, hk => by
    simpa using hk [] hist (List.Subset.refl _) .nil
  | position :: l, hist, k, hk => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
    rw [liftComp_read]
    refine Holds.queryLocal hist _ _ fun r => ?_
    exact holds_reads_bind name key ρ idx l _ (fun bs => k (r :: bs)) fun bs h hsub hfor =>
      hk (r :: bs) h (fun a ha => hsub (List.mem_append_right _ ha))
        (.cons (hsub (List.mem_append_left _ (List.mem_singleton_self _))) hfor)

theorem forall₂_getD {R : ℕ → Bit → Prop} : ∀ {l : List ℕ} {bs : List Bit}, List.Forall₂ R l bs →
    ∀ m (hm : m < l.length), R l[m] (bs.getD m 0)
  | _, _, .nil, m, hm => absurd hm (Nat.not_lt_zero m)
  | _, _, .cons h _, 0, _ => h
  | _, _, .cons _ t, m + 1, hm => forall₂_getD t m (by simpa using hm)

/-- The reads of `prgBits` put the stream cells of its bits into the reads of the path. -/
theorem holds_prgBits_bind {P : List (PrgInput C × Bit) → γ → Prop} (name : KeyName C) (key : HashOutput)
    (ρ idx count : ℕ) (hist : List (PrgInput C × Bit)) (k : (ℕ → Bit) → OracleComp (PartySpec C E RealSpec) γ)
    (hk : ∀ bits h, hist ⊆ h → (∀ g < count, ((name, key, ρ, idx, g), bits g) ∈ h) → Holds P h (k bits)) :
    Holds P hist (liftComp (liftComp (prgBits name key ρ idx count) (LocalSpec C)) (PartySpec C E RealSpec) >>= k) := by
  have hp : prgBits name key ρ idx count = ((List.range count).mapM fun position =>
      readBit (name, key, ρ, idx, position)) >>= fun bits => pure fun g => bits.getD g 0 := rfl
  rw [hp]
  simp only [liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
  refine holds_reads_bind name key ρ idx (List.range count) hist _ fun bs h hsub hfor => hk _ h hsub fun g hg => ?_
  have := forall₂_getD hfor g (by simpa using hg)
  simp only [List.getElem_range] at this
  exact this

/-- The draws of the held terms put the stream cells of their bits into the reads of the path. -/
theorem holds_termDraws_bind {P : List (PrgInput C × Bit) → γ → Prop} (self : C.Party) (keyOf : C.Term → HashOutput)
    (ρ idx count : ℕ) :
    ∀ (l : List C.Term) (hist : List (PrgInput C × Bit)) (k : List (ℕ → Bit) → OracleComp (PartySpec C E RealSpec) γ),
      (∀ rs h, hist ⊆ h → (∀ m (hm : m < l.length), self ∈ C.holders l[m] → ∀ g < count,
          ((.term l[m], keyOf l[m], ρ, idx, g), (rs.getD m fun _ => 0) g) ∈ h) → Holds P h (k rs)) →
      Holds P hist (liftComp (liftComp (l.mapM fun T => if self ∈ C.holders T then
          prgBits (.term T) (keyOf T) ρ idx count else pure fun _ => 0) (LocalSpec C)) (PartySpec C E RealSpec) >>= k)
  | [], hist, k, hk => by
    simpa using hk [] hist (List.Subset.refl _) fun m hm => absurd hm (Nat.not_lt_zero m)
  | T :: l, hist, k, hk => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
    by_cases hT : self ∈ C.holders T
    · simp only [hT, ↓reduceIte]
      refine holds_prgBits_bind _ _ ρ idx count hist _ fun bits h hsub hcells => ?_
      refine holds_termDraws_bind self keyOf ρ idx count l h (fun rs => k (bits :: rs))
        fun rs h' hsub' hrest => hk _ h' (List.Subset.trans hsub hsub') fun m hm hmT g hg => ?_
      rcases m with _ | m
      · exact hsub' (hcells g hg)
      · exact hrest m (by simpa using hm) hmT g hg
    · simp only [hT, ↓reduceIte, liftComp_pure, pure_bind]
      refine holds_termDraws_bind self keyOf ρ idx count l hist (fun rs => k ((fun _ => 0) :: rs))
        fun rs h hsub hrest => hk _ h hsub fun m hm hmT g hg => ?_
      rcases m with _ | m
      · exact absurd hmT hT
      · exact hrest m (by simpa using hm) hmT g hg

variable [Field E] [Algebra Bit E] (K : Constants C E)

/-- The output of a reshare at a held term with no filler is the randomness of that term. -/
theorem reshare_unfilled (ctx : Context C) (rnd : PrssOutput C Bit) (w : ℕ → Bit) (n : ℕ) (s : RunState C) :
    ∀ o ∈ support ((reshare (G := RealSpec) K ctx bitCodec rnd w n).run s).run, ∀ a, o = some a →
      ∀ T, T ∉ filledTerms K → ctx.self ∈ C.holders T → ∀ g < n, a.1 T g = rnd.1 T g := by
  intro o ho a hoa T hT hself g hg
  subst hoa
  unfold reshare at ho
  simp only [StateT.run_bind, StateT.run_lift, record, StateT.run_modify, StateT.run_pure, OptionT.run_bind,
    Option.elimM, bind_assoc, pure_bind] at ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨o, -, ho⟩ := ho
  rcases o with _ | inbox
  · simp at ho
  · simp only [Option.elim, OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] at ho
    subst ho
    simp [hself, hT, Nat.not_le.2 hg]

/-- The draws of `Rerand`. On each path the share of each held term with no filler is the read of the
stream of its PRSS key at the label of the start of `Rerand`. -/
theorem holds_rerand (ctx : Context C) (mode : ReshareMode) (v : Shares C Bit) (n : ℕ) (st : RunState C)
    (hist : List (PrgInput C × Bit)) :
    Holds (fun h o => ∀ a, o = some a → ∀ T, T ∉ filledTerms K → ctx.self ∈ C.holders T → ∀ g < n,
        ((.term T, ctx.prss.term T, st.label, 0, g), a.1 T g) ∈ h) hist
      (((realRunBuildingBlocks (G := RealSpec) K ctx mode).rerand v n).run st).run := by
  simp only [realRunBuildingBlocks, prssRandomness, freshLabel, StateT.run_bind, StateT.run_modifyGet,
    StateT.run_lift, pure_bind, bind_assoc, oracleStep, localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM]
  refine holds_termDraws_bind ctx.self ctx.prss.term st.label 0 n C.terms hist _ fun rs h hsub hcells => ?_
  simp only [Option.elim]
  refine holds_of_support _ h fun o ho h' hsub' a hoa T hT hself g hg => ?_
  rw [mem_support_bind_iff] at ho
  obtain ⟨Z, -, ho⟩ := ho
  rw [reshare_unfilled K ctx _ _ n _ o ho a hoa T hT hself g hg]
  have hm : C.terms.idxOf T < C.terms.length := List.idxOf_lt_length_of_mem (mem_terms T)
  have hc := hcells _ hm
  simp only [List.getElem_idxOf] at hc
  exact hsub' (hc hself g hg)

end Draws

/-! ## The draws of `Rerand` in the record of one ceremony -/

section Record

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- Each start of the record has the shares after `Rerand` of each held term with no filler as reads
of `hist`, at the label of the start less one. -/
def GoodRec {α : Type} (hist : List (PrgInput C × Bit)) (x : Option α × Record C E) : Prop :=
  ∀ b ∈ startsOf x.2, ∀ T, T ∉ filledTerms K → b.ctx.self ∈ C.holders T → ∀ g < (outputsOf b.circuits).length,
    ((.term T, b.ctx.prss.term T, b.state.label - 1, 0, g), b.v' T g) ∈ hist

variable {K}

theorem GoodRec.mono {α : Type} {hist h : List (PrgInput C × Bit)} {x : Option α × Record C E}
    (hx : GoodRec K hist x) (hsub : hist ⊆ h) : GoodRec K h x :=
  fun b hb T hT hself g hg => hsub (hx b hb T hT hself g hg)

theorem goodRec_nil {α : Type} (hist : List (PrgInput C × Bit)) (o : Option α) : GoodRec K hist (o, []) := by
  intro b hb
  simp [startsOf] at hb

variable (K)

/-- A recorded bind keeps the property of the starts. -/
theorem holds_recBind {α β : Type} {hist : List (PrgInput C × Bit)} {x : RecM C E α} {f : α → RecM C E β}
    (hx : Holds (GoodRec K) hist x.run.run) (hf : ∀ a h, Holds (GoodRec K) h (f a).run.run) :
    Holds (GoodRec K) hist (x >>= f).run.run := by
  rw [RecordedOpening.run_recBind]
  refine holds_bind (holds_grow hx) fun h y hy => ?_
  rcases y with ⟨_ | a, w⟩
  · exact Holds.pure h _ hy.2
  · show Holds _ h ((fun y => (y.1, w ++ y.2)) <$> (f a).run.run)
    rw [map_eq_bind_pure_comp]
    refine holds_bind (holds_grow (hf a h)) fun h' y' hy' => Holds.pure h' _ ?_
    intro b hb
    rw [RecordedOpening.startsOf_append, List.mem_append] at hb
    rcases hb with hb | hb
    · exact hy.2.mono hy'.1 b hb
    · exact hy'.2 b hb

/-- A program with no record and then a recorded continuation. -/
theorem holds_recLift_bind {α β : Type} {Q : List (PrgInput C × Bit) → Option α → Prop}
    {hist : List (PrgInput C × Bit)} {p : PartyM C E RealSpec α} {f : α → RecM C E β}
    (hp : Holds Q hist p.run) (hf : ∀ h a, Q h (some a) → Holds (GoodRec K) h (f a).run.run) :
    Holds (GoodRec K) hist (RecM.lift p >>= f).run.run := by
  rw [RecordedOpening.run_recLift_bind]
  refine holds_bind hp fun h o ho => ?_
  rcases o with _ | a
  · exact Holds.pure h _ (goodRec_nil h none)
  · exact hf h a ho

omit [Field E] [Algebra Bit E] in
theorem holds_true {γ : Type} (p : OracleComp (PartySpec C E RealSpec) γ) (hist : List (PrgInput C × Bit)) :
    Holds (fun _ _ => True) hist p :=
  holds_of_support p hist fun _ _ _ _ => trivial

omit [Field E] [Algebra Bit E] in
theorem holds_pair {α σ : Type} {Q : List (PrgInput C × Bit) → Option α → Prop} {hist : List (PrgInput C × Bit)}
    {p : PartyM C E RealSpec α} (hp : Holds Q hist p.run) (st : σ) :
    Holds (fun h o => ∃ o', Q h o' ∧ o = o'.map (·, st)) hist (p >>= fun a => pure (a, st)).run := by
  rw [OptionT.run_bind, Option.elimM]
  refine holds_bind hp fun h o ho => ?_
  rcases o with _ | a
  · exact Holds.pure h _ ⟨none, ho, rfl⟩
  · exact Holds.pure h _ ⟨some a, ho, rfl⟩

variable (circuits : Circuits) (settings : Settings)

/-- One recorded batch records a start whose shares after `Rerand` are reads of the path. -/
theorem holds_recBatch (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) (st : ℕ × ℕ)
    (hist : List (PrgInput C × Bit)) :
    Holds (GoodRec K) hist ((recBatch K circuits settings ctx parameter jobs).run st).run.run := by
  obtain ⟨label, k⟩ := st
  simp only [recBatch, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, RecM.liftS, StateT.run_mk]
  refine holds_recLift_bind K (holds_true _ _) fun h p _ => ?_
  refine holds_recLift_bind K (holds_true _ _) fun h p₁ _ => ?_
  refine holds_recLift_bind K (holds_pair (holds_support (holds_rerand K ctx settings.mode _ _ p₁.1.2 h)) _)
    fun h p₂ hp₂ => ?_
  obtain ⟨o', ⟨hmem, hcells⟩, ho⟩ := hp₂
  rcases o' with _ | a
  · cases ho
  simp only [Option.map_some, Option.some.injEq] at ho
  subst ho
  have hstate := rerand_support K ctx settings.mode _ _ p₁.1.2 a hmem
  refine holds_of_support _ h fun x hx h' hsub b hb T hT hself g hg => ?_
  rw [(BatchCounters.recCheckOpen_counters K _ k _ x hx).1, List.mem_singleton] at hb
  subst hb
  simp only [hstate, afterReply, Nat.add_sub_cancel]
  exact hsub (hcells a rfl T hT hself g hg)

/-- The batches of a ceremony and the ceremony itself record only such starts. -/
theorem holds_recRun (i : C.Party) (keys : Keys C) (jobs : List Job) (st : ℕ × ℕ)
    (hist : List (PrgInput C × Bit)) :
    Holds (GoodRec K) hist ((recRun K circuits settings i keys jobs).run st).run.run := by
  simp only [recRun, StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift]
  refine holds_recLift_bind K (holds_true _ _) fun h p _ => ?_
  exact closed_batched (m := StateT (ℕ × ℕ) (RecM C E))
    (fun x => ∀ st hist, Holds (GoodRec K) hist ((x.run st).run.run))
    (fun b st hist => by simpa using Holds.pure hist _ (goodRec_nil hist _))
    (fun x f hx hf st hist => by
      rw [StateT.run_bind]
      exact holds_recBind K (hx st hist) fun q h => hf q.1 q.2 h)
    _ _ (fun js st hist => holds_recBatch K circuits settings _ _ js st hist) jobs p.2 h

theorem holds_recCeremony (i : C.Party) {σ : Type} (c : CeremonyStart C σ) (hist : List (PrgInput C × Bit)) :
    Holds (GoodRec K) hist (recCeremony K circuits settings i c).run.run := by
  unfold recCeremony
  split
  · refine holds_recBind K (holds_recRun K circuits settings i _ c.jobs c.counters hist) fun p h => ?_
    refine holds_of_support _ h fun x hx h' _ => ?_
    rcases p with ⟨_ | outputs, st⟩
    · simp at hx
      rw [hx]
      exact goodRec_nil h' none
    · simp at hx
      rw [hx]
      exact goodRec_nil h' _
  · exact Holds.pure hist _ (goodRec_nil hist none)

variable (prims : Primitives)

/-- The draws of `Rerand` on the ghost run of one ceremony. The share after `Rerand` of each held term
with no filler at each start that an honest operator recorded has the stream cell of the PRSS key of
that term, at the label of the start less one, in the end world. -/
theorem ghost_rerandCells (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (j : C.Party)
    (hj : j ∉ D.1) (b : BatchStart C) (hb : b ∈ startsOf (ceremonyRecord ω.1.2 j)) (T : C.Term)
    (hT : T ∉ filledTerms K) (hself : b.ctx.self ∈ C.holders T) (g : ℕ) (hg : g < (outputsOf b.circuits).length) :
    StreamCell prims D (.term T, b.ctx.prss.term T, b.state.label - 1, 0, g) ω.2 (b.v' T g) := by
  unfold ghostCeremony at hω
  have hstep := executePhaseR_holds prims D D net ([] : Record C E) (fun _ => GoodRec K) rounds c.adversary
    (fun i => (recCeremony K circuits settings i c).run.run)
    (fun i _ => holds_recCeremony K circuits settings i c []) world ω hω j hj
  unfold ceremonyRecord at hb
  rcases hs : ω.1.2 j with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at hstep hb
  · obtain ⟨hist, hc, hgood⟩ := hstep
    exact hc _ (hgood b hb T hT hself g hg)
  · simp [RStep.record, startsOf] at hb
  · exact hstep.elim

end Record

end RerandCells

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end


section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace DigestRound

open LiveRounds CachedOpening RecordedOpening OpeningDigests

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## The digest round of a check -/

section Wait

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) {α β : Type}

/-- The digest list of operator `l` that operator `i` compares, from its own `digests` and its mail. -/
def digestOf (i : C.Party) (digests : List HashOutput) (inbox : Mail C E) (l : C.Party) : List HashOutput :=
  if l = i then digests else Msg.hashesOf (inbox l)

/-- The mail of the digest round passes the test of operator `i`. It holds no abort frame, and the
holders of each term sent one digest of it. -/
def DigestAgree (i : C.Party) (digests : List HashOutput) (inbox : Mail C E) : Prop :=
  (∀ c, inbox c ≠ some .abort) ∧ ∀ T, ∀ l ∈ C.holders T, ∀ l' ∈ C.holders T,
    (digestOf i digests inbox l)[C.terms.idxOf T]? = (digestOf i digests inbox l')[C.terms.idxOf T]? ∧
      ((digestOf i digests inbox l)[C.terms.idxOf T]?).isSome

/-- The digests of operator `i` with the running history above `history`. For each held term the
digest is the answer of `.digest salt hh` in `hist`, where `hh` is the answer of `.history` of a
history that extends `history`. -/
def DigestSent (i : C.Party) (history : C.Term → List Bit) (hist : List (Query C × HashOutput))
    (digests : List HashOutput) : Prop :=
  ∃ h : C.Term → List Bit, (∀ T, history T <+: h T) ∧ ∀ T, i ∈ C.holders T → ∃ salt hh d,
    ((.history (h T) : Query C), hh) ∈ hist ∧ ((.digest salt hh : Query C), d) ∈ hist ∧
      digests[C.terms.idxOf T]? = some d

/-- The exchange of the digest round of the check with index `k` at operator `j`. The outbox holds
the digests of the start `b`. Each later record holds `b` at index `k` and an opening at index `k` if
the program gives a result, and an opening at index `k` needs the test of the digest round. -/
def DigestWait (j : C.Party) (k : ℕ) (hist : List (Query C × HashOutput)) (out : Mail C E)
    (resume : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α × Record C E)) : Prop :=
  ∃ (b : BatchStart C) (digests : List HashOutput),
    out = (fun l => if l = j then none else some (.hashes digests)) ∧ DigestSent j b.state.history hist digests ∧
    ∀ inbox, ∀ x ∈ support (resume inbox), (startsOf x.2)[k]? = some b ∧
      (x.1.isSome → k < (openingsOf x.2).length) ∧ (k < (openingsOf x.2).length → DigestAgree j digests inbox)

omit [Field E] [Algebra Bit E] in
/-- The stable wait keeps its form under a later recorded continuation. -/
theorem DigestWait.bind {j : C.Party} {k : ℕ} {hist : List (Query C × HashOutput)} {out : Mail C E}
    {resume : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α × Record C E)} (f : α → RecM C E β)
    (h : DigestWait j k hist out resume) : DigestWait j k hist out fun r => resume r >>= recCont f := by
  obtain ⟨b, digests, hout, hsent, h⟩ := h
  refine ⟨b, digests, hout, hsent, fun inbox x hx => ?_⟩
  rw [mem_support_bind_iff] at hx
  obtain ⟨y, hy, hx⟩ := hx
  obtain ⟨h1, h2, h3⟩ := h inbox y hy
  rcases y with ⟨_ | a, w⟩
  · simp only [recCont, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨h1, h2, h3⟩
  · simp only [recCont, support_map, Set.mem_image] at hx
    obtain ⟨z, -, rfl⟩ := hx
    have hks : k < (startsOf w).length := (List.getElem?_eq_some_iff.1 h1).1
    have hko : k < (openingsOf w).length := h2 rfl
    refine ⟨?_, fun _ => ?_, fun _ => h3 hko⟩
    · rw [RecordedOpening.startsOf_append, List.getElem?_append_left hks]
      exact h1
    · rw [openingsOf_append, List.length_append]
      omega

omit [Field E] [Algebra Bit E] in
/-- The stable wait after a prefix record with `k'` starts and `k'` openings is at index `k' + k`. -/
theorem DigestWait.shift {j : C.Party} {k k' : ℕ} {hist : List (Query C × HashOutput)} {out : Mail C E}
    {resume : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α × Record C E)} (w : Record C E)
    (hs : (startsOf w).length = k') (ho : (openingsOf w).length = k')
    (h : DigestWait j k hist out resume) :
    DigestWait j (k' + k) hist out fun r => (fun y => (y.1, w ++ y.2)) <$> resume r := by
  obtain ⟨b, digests, hout, hsent, h⟩ := h
  refine ⟨b, digests, hout, hsent, fun inbox x hx => ?_⟩
  rw [support_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨h1, h2, h3⟩ := h inbox y hy
  refine ⟨?_, fun hsome => ?_, fun hlt => h3 ?_⟩
  · rw [RecordedOpening.startsOf_append, List.getElem?_append_right (by omega), hs, Nat.add_sub_cancel_left]
    exact h1
  · rw [openingsOf_append, List.length_append, ho]
    have := h2 hsome
    omega
  · rw [openingsOf_append, List.length_append, ho] at hlt
    omega

omit [Field E] [Algebra Bit E] in
/-- A recorded program that reaches its stable wait keeps it with any continuation. -/
theorem reachD_recBind_left {j : C.Party} {k n : ℕ} {hist : List (Query C × HashOutput)} {x : RecM C E α}
    (f : α → RecM C E β) (hx : ReachH (Stop k) (DigestWait j k) n hist x.run.run) :
    ReachH (Stop k) (DigestWait j k) n hist (x >>= f).run.run := by
  rw [run_recBind]
  refine reachH_bind_left hx (fun y hy => ?_) fun hist out resume h => h.bind f
  rcases y with ⟨_ | a, w⟩
  · exact ⟨(none, w), rfl, rfl, hy.2⟩
  · exact absurd hy.1 (by simp)

omit [Field E] [Algebra Bit E] in
/-- A timed recorded prefix with `k'` starts and `k'` openings, and then a continuation that reaches
its stable wait of index `k` from each history, reach the stable wait of index `k' + k`. -/
theorem reachD_recBind {x : RecM C E α} {f : α → RecM C E β} {j : C.Party} {m n a₁ k' k kk : ℕ}
    (hx : TimedLog (Stop a₁) (RecordedOpening.Full k' k') m x.run.run)
    (hf : ∀ hist c, ReachH (Stop k) (DigestWait j k) n hist (f c).run.run) (ha : a₁ ≤ kk) (hk : k' + k = kk)
    (hist : List (Query C × HashOutput)) :
    ReachH (Stop kk) (DigestWait j kk) (m + n) hist (x >>= f).run.run := by
  subst hk
  rw [run_recBind]
  refine timedLog_reachH_bind hx (fun y hy => ?_) (fun hist y hy => ?_) hist
  · rcases y with ⟨_ | c, w⟩
    · exact ⟨(none, w), rfl, rfl, le_trans hy.2 ha⟩
    · exact absurd hy.1 (by simp)
  · rcases y with ⟨_ | c, w⟩
    · exact absurd hy.1 (by simp)
    obtain ⟨-, hs₁, ho₁⟩ := hy
    dsimp only at hs₁ ho₁
    show ReachH _ _ n hist ((fun y => (y.1, w ++ y.2)) <$> (f c).run.run)
    refine reachH_map _ (hf hist c) (fun z hz => ⟨hz.1, ?_⟩) fun hist out resume h => h.shift w hs₁ ho₁
    simp only [openingsOf_append, List.length_append]
    have := hz.2
    omega

end Wait


/-! ## The digest round in the recorded program -/

section Rec

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)

/-- The check of a start reaches its digest round. From each state, on each path, the check of
tuples with a positive count ends with an abort before the exchange of its digests, or it reaches
that exchange after `checkLabels` less three rounds. There its outbox holds digests of the running
history, and each later result of the check needs the test of the digest round. -/
def CheckReach (ctx : Context C) : Prop :=
  ∀ (tuples : List (Tuple C)), (tuples.map (·.count)).sum ≠ 0 → ∀ (st : RunState C) {γ : Type} (P : γ → Prop)
    (g : Option (Unit × RunState C) → OracleComp (PartySpec C E RealSpec) γ), (∃ y, g none = pure y ∧ P y) →
    ∀ hist, ReachH P (fun hist out resume => ∃ digests,
        out = (fun l => if l = ctx.self then none else some (.hashes digests)) ∧
        DigestRound.DigestSent ctx.self st.history hist digests ∧
        ∀ inbox, ∀ x ∈ support (resume inbox), x ∈ support (g none) ∨
          (DigestRound.DigestAgree ctx.self digests inbox ∧ ∃ r, x ∈ support (g (some r))))
      (checkLabels (tuples.map (·.count)).sum - 3) hist
      (((check K ctx (realCheckBuildingBlocks K ctx) tuples).run st).run >>= g)

omit [Fintype E] [DecidableEq E] in
theorem reachD_recCheckOpen (j : C.Party) (b : BatchStart C) (hj : b.ctx.self = j)
    (htup : tupleCount b.circuits ≠ 0) (hcheck : CheckReach K b.ctx) (k : ℕ) (st : ℕ × ℕ)
    (hist : List (Query C × HashOutput)) :
    ReachH (Stop 0) (DigestRound.DigestWait j 0) (checkLabels (tupleCount b.circuits) - 3) hist
      ((recCheckOpen K b k).run st).run.run := by
  simp only [recCheckOpen, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, RecM.liftS, StateT.run_mk,
    StateT.run_set, StateT.run_pure]
  rw [run_recRecord_bind, run_recLift_bind]
  refine reachH_map _ (P := Stop 0) (Q := fun hist out resume => ∃ digests : List HashOutput,
      out = (fun l => if l = j then none else some (.hashes digests)) ∧
      DigestRound.DigestSent j b.state.history hist digests ∧
      ∀ inbox, ∀ x ∈ support (resume inbox), (x.1.isSome → 0 < (openingsOf x.2).length) ∧
        (0 < (openingsOf x.2).length → DigestRound.DigestAgree j digests inbox))
    ?_ (fun z hz => ⟨hz.1, ?_⟩) fun hist out resume h => ?_
  rotate_left
  · have := hz.2
    simp only [length_openingsOf_append, length_openingsOf_event]
    omega
  · obtain ⟨digests, hout, hsent, h⟩ := h
    refine ⟨b, digests, hout, hsent, fun inbox x hx => ?_⟩
    rw [support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := h inbox y hy
    have ho : openingsOf ([RecEvent.start b] ++ y.2) = openingsOf y.2 := by
      rw [openingsOf_append]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [RecordedOpening.startsOf_append]
      rfl
    · rw [ho]
      exact h1
    · rw [ho]
      exact h2
  have htup' : ((batchTuples K b.mode b.circuits b.inputs b.zs b.v').map (·.count)).sum ≠ 0 := by
    rw [sum_batchTuples]
    exact htup
  rw [OptionT.run_bind, Option.elimM, bind_assoc, ← sum_batchTuples K b]
  refine reachH_mono (hcheck (batchTuples K b.mode b.circuits b.inputs b.zs b.v') htup' b.state (Stop 0) _ ?_ hist)
    (fun x hx => hx) fun hist out resume h => ?_
  · exact ⟨(none, []), by simp, rfl, by simp [openingsOf]⟩
  obtain ⟨digests, hout, hsent, h⟩ := h
  refine ⟨digests, by rw [hout, hj], by rw [← hj]; exact hsent, fun inbox x hx => ?_⟩
  rcases h inbox x hx with hnone | ⟨hagree, r, hr⟩
  · simp at hnone
    subst hnone
    simp [openingsOf]
  · refine ⟨fun hsome => ?_, fun _ => hj ▸ hagree⟩
    simp only [Option.elim, OptionT.run_pure, pure_bind] at hr
    rcases mem_support_lift_bind _ _ x hr with rfl | ⟨p, z₂, h₂, rfl⟩
    · cases hsome
    rcases mem_support_lift_bind _ _ _ h₂ with rfl | ⟨p₁, z₃, h₃, rfl⟩
    · cases hsome
    obtain ⟨z₄, -, rfl⟩ := mem_support_record_bind _ _ _ h₃
    simp [openingsOf]


variable (circuits : Circuits) (settings : Settings)

/-- The depth of the digest round of a batch of the circuits `cs`. -/
def digestDepth (mode : ReshareMode) (cs : List Circuit) : ℕ :=
  0 + (depth cs * mode.rounds + (1 + (checkLabels (tupleCount cs) - 3)))

omit [Fintype E] [DecidableEq E] in
theorem reachD_recBatch (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) (st : ℕ × ℕ)
    (hist : List (Query C × HashOutput)) (htup : tupleCount (jobs.map (circuits parameter ·.kind)) ≠ 0)
    (hcheck : CheckReach K ctx) :
    ReachH (Stop 0) (DigestRound.DigestWait ctx.self 0)
      (digestDepth settings.mode (jobs.map (circuits parameter ·.kind))) hist
      ((recBatch K circuits settings ctx parameter jobs).run st).run.run := by
  obtain ⟨label, k⟩ := st
  simp only [recBatch, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, RecM.liftS, StateT.run_mk]
  unfold digestDepth
  refine reachH_lift_bind (timed_pair (timed_inputShares ctx jobs) _) ⟨rfl, by simp [openingsOf]⟩
    (fun hist p => ?_) hist
  refine reachH_lift_bind (timed_pair (runTimed_recLayers K ctx settings.mode _ _ _ _) _)
    ⟨rfl, by simp [openingsOf]⟩ (fun hist p₁ => ?_) hist
  refine reachH_lift_bind (timed_pair (runTimed_realRerand K ctx settings.mode _ _ _) _)
    ⟨rfl, by simp [openingsOf]⟩ (fun hist p₂ => ?_) hist
  exact reachD_recCheckOpen K ctx.self ⟨(realRunBuildingBlocks K ctx settings.mode).mode, jobs, parameter,
    jobs.map (circuits parameter ·.kind), p.1, p₁.1.1, p₂.1.1, ctx, p₂.1.2⟩ rfl htup hcheck k p₂.2 hist

omit [Fintype E] [DecidableEq E] in
theorem reachD_recBatches (ctx : Context C) (parameter : PublicParameter) (js : List (List Job)) (k : ℕ)
    (hk : k < js.length) (st : ℕ × ℕ) (hist : List (Query C × HashOutput))
    (htup : tupleCount (js[k].map (circuits parameter ·.kind)) ≠ 0) (hcheck : CheckReach K ctx) :
    ReachH (Stop k) (DigestRound.DigestWait ctx.self k)
      (((js.take k).map fun batch =>
        CheckTiming.exactBatchRounds settings.mode (batch.map (circuits parameter ·.kind))).sum +
        digestDepth settings.mode (js[k].map (circuits parameter ·.kind))) hist
      ((js.mapM (recBatch K circuits settings ctx parameter)).run st).run.run := by
  have hsplit : js = js.take k ++ js[k] :: js.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hmap : js.mapM (recBatch K circuits settings ctx parameter) =
      (js.take k ++ js[k] :: js.drop (k + 1)).mapM (recBatch K circuits settings ctx parameter) :=
    congrArg (List.mapM _) hsplit
  have hlen : (js.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hk.le]
  rw [hmap, List.mapM_append, StateT.run_bind]
  refine DigestRound.reachD_recBind (k := 0) (timedLog_recBatches K circuits settings ctx parameter (js.take k) st)
    (fun hist c => ?_) hlen.le (by rw [hlen, Nat.add_zero]) hist
  rw [StateT.run_bind]
  refine DigestRound.reachD_recBind_left _ ?_
  rw [List.mapM_cons, StateT.run_bind]
  exact DigestRound.reachD_recBind_left _ (reachD_recBatch K circuits settings ctx parameter js[k] c.2 hist htup hcheck)

omit [Fintype E] [DecidableEq E] in
/-- `recCeremony` at operator `l` reaches the digest round of batch `k` at the depth of the parameter
`P` of its keys. A dead operator aborts with the empty record. -/
theorem reachD_recCeremony (l : C.Party) {σ : Type} (c : CeremonyStart C σ) (P : PublicParameter)
    (hP : ∀ keys, c.keys l = some keys → keys.parameter = P) (k : ℕ)
    (hk : k < (chunks settings.batchSize c.jobs).length)
    (htup : tupleCount (((chunks settings.batchSize c.jobs)[k]).map (circuits P ·.kind)) ≠ 0)
    (hcheck : ∀ ctx : Context C, ctx.self = l → CheckReach K ctx) :
    ReachH (Stop k) (DigestRound.DigestWait l k)
      (setupRounds + ((((chunks settings.batchSize c.jobs).take k).map fun batch =>
        CheckTiming.exactBatchRounds settings.mode (batch.map (circuits P ·.kind))).sum +
        digestDepth settings.mode (((chunks settings.batchSize c.jobs)[k]).map (circuits P ·.kind)))) []
      (recCeremony K circuits settings l c).run.run := by
  unfold recCeremony
  split
  · rename_i keys hkeys
    rw [← hP keys hkeys] at htup ⊢
    refine DigestRound.reachD_recBind_left _ ?_
    simp only [recRun, StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift]
    refine reachH_lift_bind (timed_pair (timed_prssSetup l) c.counters)
      ⟨rfl, by simp [openingsOf]⟩ (fun hist p => ?_) []
    simp only [batched, StateT.run_bind]
    exact DigestRound.reachD_recBind_left _
      (reachD_recBatches K circuits settings ⟨l, keys, p.1⟩ keys.parameter _ k hk p.2 hist htup (hcheck _ rfl))
  · rw [run_recFailure]
    exact CachedOpening.ReachH.early _ _ _ ⟨rfl, by simp [openingsOf]⟩


omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Each outcome of a timed program is a leaf of one of its two kinds. -/
theorem timedLog_support {γ : Type} {A B : γ → Prop} {m : ℕ} {p : OracleComp (PartySpec C E RealSpec) γ}
    (h : TimedLog A B m p) : ∀ x ∈ support p, A x ∨ B x := by
  induction h with
  | stop m x hx => intro y hy; simp at hy; subst hy; exact Or.inl hx
  | done x hx => intro y hy; simp at hy; subst hy; exact Or.inr hx
  | queryLocal m q k _ ih =>
    intro y hy
    obtain ⟨r, -, hr⟩ := (mem_support_bind_iff (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
      (Sum.inl (Sum.inl q)))) k y).1 hy
    exact ih r y hr
  | round m out k _ ih =>
    intro y hy
    obtain ⟨r, -, hr⟩ := (mem_support_bind_iff (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
      (Sum.inl (Sum.inr out)))) k y).1 hy
    exact ih r y hr

omit [Fintype E] [DecidableEq E] in
/-- A result of `recRun` records one start and one opening for each batch of the job list. -/
theorem recRun_full (i : C.Party) (keys : Keys C) (jobs : List Job) (st : ℕ × ℕ)
    (z : Option (Option (List (List Bit)) × (ℕ × ℕ)) × Record C E)
    (hz : z ∈ support ((recRun K circuits settings i keys jobs).run st).run.run) (hsome : z.1.isSome) :
    (openingsOf z.2).length = (chunks settings.batchSize jobs).length := by
  have htimed : ∃ m, TimedLog (Stop (chunks settings.batchSize jobs).length)
      (RecordedOpening.Full (chunks settings.batchSize jobs).length (chunks settings.batchSize jobs).length) m
      ((recRun K circuits settings i keys jobs).run st).run.run := by
    simp only [recRun, StateT.run_bind, RecM.liftS, StateT.run_mk, StateT.run_lift]
    refine ⟨_, timedLog_lift_bind (n := ((chunks settings.batchSize jobs).map fun batch =>
      CheckTiming.exactBatchRounds settings.mode (batch.map (circuits keys.parameter ·.kind))).sum + 0)
      (timed_pair (timed_prssSetup i) st) ⟨rfl, by simp [openingsOf]⟩ fun p => ?_⟩
    simp only [batched, StateT.run_bind]
    refine timedLog_recBind (a₂ := 0) (s₂ := 0) (o₂ := 0) (n := 0)
      (timedLog_recBatches K circuits settings ⟨i, keys, p.1⟩ keys.parameter _ p.2) (fun q => ?_) (le_refl _)
      (by omega) (by omega) (by omega)
    rw [StateT.run_pure, run_recPure]
    exact TimedLog.done _ ⟨rfl, rfl, rfl⟩
  obtain ⟨m, hm⟩ := htimed
  rcases timedLog_support hm z hz with h | h
  · rw [h.1] at hsome
    cases hsome
  · exact h.2.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Digests sent with their cells in a cache are the honest digests of the start. -/
theorem honestDigests_of_sent {cache : HashCache C} {hist : List (Query C × HashOutput)} {j : C.Party}
    {b : BatchStart C} {digests : List HashOutput} (hc : Cached hist cache)
    (hsent : DigestRound.DigestSent j b.state.history hist digests) : PassedShares.HonestDigests cache j b digests := by
  obtain ⟨h, hpre, hcells⟩ := hsent
  refine ⟨h, fun T hT => ⟨hpre T, ?_⟩⟩
  obtain ⟨salt, hh, d, h1, h2, h3⟩ := hcells T hT
  exact ⟨salt, hh, d, hc _ h1 (by rintro ⟨_, he, -⟩; cases he), hc _ h2 (by rintro ⟨_, he, -⟩; cases he), h3⟩

variable (prims : Primitives)

omit [Fintype E] [DecidableEq E] in
/-- The digest round on the ghost run of one ceremony. When the honest operator `i` recorded the
opening of batch `k`, the digest lists that `i` compared agree on the honest holders of each term,
and the list of each honest operator with a start of check `k` is its honest digests in the end hash
cache. -/
theorem ghost_digests (hcheck : ∀ ctx : Context C, CheckReach K ctx) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (c : CeremonyStart C net.State) (world : StreamState C)
    (hseeds : seedsDiffer D c.keys = false) (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (k : ℕ)
    (hk : k < (chunks settings.batchSize c.jobs).length)
    (htup : tupleCount (((chunks settings.batchSize c.jobs)[k]).map (circuits (gameParameter D c.keys) ·.kind)) ≠ 0)
    (i : C.Party) (hi : i ∉ D.1) (hopen : k < (openingsOf (ceremonyRecord ω.1.2 i)).length) :
    ∃ ds : C.Party → List HashOutput,
      (∀ T j j', j ∉ D.1 → j' ∉ D.1 → j ∈ C.holders T → j' ∈ C.holders T →
        (ds j)[C.terms.idxOf T]? = (ds j')[C.terms.idxOf T]?) ∧
      ∀ j b, j ∉ D.1 → (startsOf (ceremonyRecord ω.1.2 j))[k]? = some b →
        PassedShares.HonestDigests ω.2.1 j b (ds j) := by
  unfold ghostCeremony at hω
  have hne : ceremonyRecord ω.1.2 i ≠ [] := fun h => by simp [h, openingsOf] at hopen
  have hreach := fun l (hl : l ∉ D.1) => reachD_recCeremony K circuits settings l c (gameParameter D c.keys)
    (fun keys hkeys => parameter_eq_gameParameter D c.keys hseeds l hl keys hkeys) k hk htup fun ctx _ => hcheck ctx
  rcases CachedOpening.executePhaseR_reachH prims D D net ([] : Record C E) (fun _ => Stop k)
    (fun l => DigestRound.DigestWait l k) _ rounds c.adversary _ hreach world ω hω with
    hstop | ⟨steps₀, sent, cache, hle, hsteps, hrest⟩
  · exfalso
    rcases hstop i hi with h | ⟨out, hout⟩
    · exact hne h
    · have := hout.2
      change (openingsOf (ceremonyRecord ω.1.2 i)).length ≤ k at this
      omega
  obtain ⟨out, hout⟩ : ∃ out, (out, ceremonyRecord ω.1.2 i) ∈
      support (LiveRounds.nextR ([] : Record C E) (steps₀ i) (LiveRounds.roundInbox D steps₀ sent i)) := by
    rcases hrest i hi with h | h
    · exact absurd h hne
    · exact h
  have hsi := hsteps i hi
  rcases hs : steps₀ i with ⟨out', r'⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at hsi hout
  · simp only [LiveRounds.nextR, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
    have := hsi.2
    rw [← hout.2] at this
    change (openingsOf (ceremonyRecord ω.1.2 i)).length ≤ k at this
    omega
  swap
  · exact input.elim
  obtain ⟨hist, hc, bi, digests, -, hsent, hwait⟩ := hsi
  have hagree := (hwait _ _ hout).2.2 hopen
  refine ⟨DigestRound.digestOf i digests (LiveRounds.roundInbox D steps₀ sent i),
    fun T j j' hj hj' hjT hj'T => (hagree.2 T j hjT j' hj'T).1, fun j b hj hb => ?_⟩
  have hnej : ceremonyRecord ω.1.2 j ≠ [] := fun h => by simp [h, startsOf] at hb
  by_cases hji : j = i
  · subst hji
    have hbi : b = bi := Option.some.inj (hb.symm.trans (hwait _ _ hout).1)
    subst hbi
    have : DigestRound.digestOf j digests (LiveRounds.roundInbox D steps₀ sent j) j = digests := by
      simp [DigestRound.digestOf]
    rw [this]
    exact honestDigests_of_sent (hc.mono hle) hsent
  have hsj := hsteps j hj
  have hinj : LiveRounds.roundInbox D steps₀ sent i j = (steps₀ j).delivered i := by
    simp [LiveRounds.roundInbox, hj]
  rcases hsj' : steps₀ j with ⟨out', r'⟩ | ⟨outbox', resume'⟩ | ⟨input, resume'⟩ <;> rw [hsj'] at hsj hinj
  · exfalso
    have h1 : out' = none := hsj.1
    subst h1
    exact hagree.1 j hinj
  · obtain ⟨hist', hc', bj, digests', hout', hsent', hwait'⟩ := hsj
    have hbj : b = bj := by
      rcases hrest j hj with h | ⟨out'', hout''⟩
      · exact absurd h hnej
      · rw [hsj'] at hout''
        exact Option.some.inj (hb.symm.trans (hwait' _ _ hout'').1)
    subst hbj
    have : DigestRound.digestOf i digests (LiveRounds.roundInbox D steps₀ sent i) j = digests' := by
      simp only [DigestRound.digestOf, hji, ↓reduceIte, hinj, RStep.delivered, hout', Ne.symm hji]
      rfl
    rw [this]
    exact honestDigests_of_sent (hc'.mono hle) hsent'
  · exact input.elim


end Rec

/-! ## The walk of the check to its digest round -/

section CheckWalk

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C)

/-- The running history of the state `s'` extends the history of `s` at each term. -/
def HistGrows (s s' : RunState C) : Prop := ∀ T, s.history T <+: s'.history T

omit [Field E] [Algebra Bit E] in
theorem histGrows_refl (s : RunState C) : HistGrows s s := fun _ => List.prefix_refl _

omit [Field E] [Algebra Bit E] in
theorem histGrows_trans (s₁ s₂ s₃ : RunState C) (h₁ : HistGrows s₁ s₂) (h₂ : HistGrows s₂ s₃) : HistGrows s₁ s₃ :=
  fun T => (h₁ T).trans (h₂ T)

omit [Field E] [Algebra Bit E] in
theorem moves_hist_lift {α : Type} (x : PartyM C E RealSpec α) : Moves HistGrows (StateT.lift x : RunM C E RealSpec α) :=
  moves_lift histGrows_refl x

omit [Field E] [Algebra Bit E] in
theorem moves_hist_bind {α β : Type} {p : RunM C E RealSpec α} {q : α → RunM C E RealSpec β}
    (hp : Moves HistGrows p) (hq : ∀ a, Moves HistGrows (q a)) : Moves HistGrows (p >>= q) :=
  moves_bind hp hq histGrows_trans

omit [Field E] [Algebra Bit E] in
theorem moves_hist_pure {α : Type} (a : α) : Moves HistGrows (pure a : RunM C E RealSpec α) :=
  moves_pure histGrows_refl a

omit [Field E] [Algebra Bit E] in
theorem moves_hist_foldlM {α β : Type} (f : α → β → RunM C E RealSpec α) (hf : ∀ a b, Moves HistGrows (f a b)) :
    ∀ (l : List β) (init : α), Moves HistGrows (l.foldlM f init)
  | [], init => by simpa using moves_hist_pure init
  | b :: l, init => by
    rw [List.foldlM_cons]
    exact moves_hist_bind (hf init b) fun a => moves_hist_foldlM f hf l a

omit [Field E] [Algebra Bit E] in
theorem moves_hist_prssRandomness {R : Type} [Zero R] (codec : Codec C E R) (idx count : ℕ) :
    Moves HistGrows (prssRandomness (G := RealSpec) ctx codec idx count) := by
  unfold prssRandomness freshLabel
  exact moves_hist_bind (moves_modifyGet _ fun s => histGrows_refl s) fun _ => moves_hist_bind (moves_hist_lift _)
    fun _ => moves_hist_bind (moves_hist_lift _) fun _ => moves_hist_pure _

theorem moves_hist_reshare {R : Type} [Field R] (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R)
    (count : ℕ) : Moves HistGrows (reshare (G := RealSpec) K ctx codec randomness v count) := by
  obtain ⟨r, Z⟩ := randomness
  unfold reshare record
  refine moves_hist_bind (moves_hist_lift _) fun _ => moves_hist_bind (moves_modify _ fun s T => ?_)
    fun _ => moves_hist_pure _
  dsimp only
  by_cases h : ctx.self ∈ C.holders T
  · rw [ite_eq_left h]
    exact List.prefix_append _ _
  · rw [ite_eq_right h]

theorem moves_hist_coin (count : ℕ) : Moves HistGrows ((realCheckBuildingBlocks (G := RealSpec) K ctx).coin count) := by
  refine moves_hist_bind (moves_hist_prssRandomness ctx _ 1 count) fun _ => ?_
  unfold coinWith
  exact moves_hist_bind (moves_hist_lift _) fun _ => moves_hist_pure _

theorem moves_hist_extendMult (products : List (Product C E)) :
    Moves HistGrows ((realCheckBuildingBlocks (G := RealSpec) K ctx).extendMult products) :=
  moves_hist_bind (moves_hist_prssRandomness ctx _ 0 _) fun _ => moves_hist_reshare K ctx _ _ _ _

theorem moves_hist_coinKey : Moves HistGrows (coinKey K (realCheckBuildingBlocks (G := RealSpec) K ctx)) := by
  unfold coinKey
  exact moves_hist_bind (moves_get histGrows_refl) fun _ => moves_hist_bind (moves_hist_coin K ctx 2)
    fun _ => moves_hist_lift _

theorem moves_hist_challenge : Moves HistGrows (challenge K (realCheckBuildingBlocks (G := RealSpec) K ctx)) := by
  unfold challenge
  refine moves_hist_bind (moves_hist_coinKey K ctx) fun _ => moves_hist_bind (moves_hist_lift _) fun r => ?_
  rcases r with _ | r
  · exact moves_hist_lift _
  · exact moves_hist_pure _

theorem moves_hist_sliceStep (τ : List E) (count : ℕ) (p : Shares C E × Shares C E × E) (j : ℕ) :
    Moves HistGrows (sliceStep K ctx (realCheckBuildingBlocks (G := RealSpec) K ctx) τ count p j) := by
  obtain ⟨xs, ys, D⟩ := p
  unfold sliceStep
  exact moves_hist_bind (moves_hist_extendMult K ctx _) fun _ =>
    moves_hist_bind (moves_hist_challenge K ctx) fun _ => moves_hist_pure _

theorem moves_hist_halvingStep (width : ℕ) (p : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    Moves HistGrows (halvingStep K ctx (realCheckBuildingBlocks (G := RealSpec) K ctx) width p j) := by
  obtain ⟨A, B, D⟩ := p
  unfold halvingStep
  exact moves_hist_bind (moves_hist_extendMult K ctx _) fun _ =>
    moves_hist_bind (moves_hist_challenge K ctx) fun _ => moves_hist_pure _

omit [Field E] [Algebra Bit E] in
/-- A timed program ends with an abort, or with a result in its support after exactly `m` rounds. -/
theorem timedLog_of_timed {α : Type} {m : ℕ} {oa : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : Timed m oa) : ∀ B : Option α → Prop, (∀ o ∈ support oa, o.isSome → B o) →
      TimedLog (fun o => o = none) B m oa := by
  induction h with
  | abort n => exact fun B _ => TimedLog.stop n none rfl
  | done a => exact fun B hB => TimedLog.done _ (hB _ (by simp) rfl)
  | queryLocal n q k _ ih =>
    exact fun B hB => TimedLog.queryLocal n q k fun r => ih r B fun o ho hs =>
      hB o ((mem_support_bind_iff (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
        (Sum.inl (Sum.inl q)))) k o).2 ⟨r, by simp, ho⟩) hs
  | round n out k _ ih =>
    exact fun B hB => TimedLog.round n out k fun r => ih r B fun o ho hs =>
      hB o ((mem_support_bind_iff (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
        (Sum.inl (Sum.inr out)))) k o).2 ⟨r, by simp, ho⟩) hs
  | call n input k _ ih => exact input.elim

omit [Field E] [Algebra Bit E] in
/-- A timed step of a run and then a continuation that reaches its wait of depth `n` from each state
of the support reach that wait at depth `m + n`. -/
theorem reachH_runBind {α β γ : Type} {P : γ → Prop}
    {Q : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) γ) → Prop}
    {m n : ℕ} {p : RunM C E RealSpec α} {q : α → RunM C E RealSpec β} {st : RunState C}
    {g : Option (β × RunState C) → OracleComp (PartySpec C E RealSpec) γ} (hp : RunTimed m p)
    (hnone : ∃ y, g none = pure y ∧ P y)
    (hq : ∀ hist a s, some (a, s) ∈ support (p.run st).run → ReachH P Q n hist (((q a).run s).run >>= g))
    (hist : List (Query C × HashOutput)) : ReachH P Q (m + n) hist ((((p >>= q).run st).run) >>= g) := by
  rw [StateT.run_bind, OptionT.run_bind, Option.elimM, bind_assoc]
  refine timedLog_reachH_bind (timedLog_of_timed (hp st) (fun o => o ∈ support (p.run st).run ∧ o.isSome)
    fun o ho hs => ⟨ho, hs⟩) (fun x hx => ?_) (fun hist x hx => ?_) hist
  · subst hx
    obtain ⟨y, hy, hPy⟩ := hnone
    exact ⟨y, by simp [hy], hPy⟩
  · rcases x with _ | ⟨a, s⟩
    · cases hx.2
    · simpa only [Option.elim] using hq hist a s hx.1


omit [Field E] [Algebra Bit E] in
theorem reachH_hash_bind {γ : Type} {P : γ → Prop}
    {Q : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) γ) → Prop}
    {n : ℕ} (q : Query C) (hist : List (Query C × HashOutput)) (k : HashOutput → OracleComp (PartySpec C E RealSpec) γ)
    (hk : ∀ r, ReachH P Q n ((q, r) :: hist) (k r)) :
    ReachH P Q n hist (liftComp (liftComp (hashQuery q) (LocalSpec C)) (PartySpec C E RealSpec) >>= k) := by
  rw [liftComp_hashQuery]
  exact ReachH.queryLocal n hist _ _ hk

omit [Field E] [Algebra Bit E] in
/-- The digest hashes of the held terms put the `.history` and `.digest` answers into the history. -/
theorem reachH_digests_bind {γ : Type} {P : γ → Prop}
    {Q : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) γ) → Prop}
    (n : ℕ) (i : C.Party) (h : C.Term → List Bit) (salts : Shares C Bit) :
    ∀ (l : List C.Term) (hist : List (Query C × HashOutput)) (k : List HashOutput → OracleComp (PartySpec C E RealSpec) γ),
      (∀ ds hist', hist ⊆ hist' → ds.length = l.length → (∀ m (hm : m < l.length), i ∈ C.holders l[m] → ∃ hh,
          ((.history (h l[m]) : Query C), hh) ∈ hist' ∧ ((.digest (vector 256 (salts l[m])) hh : Query C), ds.getD m 0) ∈ hist') →
        ReachH P Q n hist' (k ds)) →
      ReachH P Q n hist (liftComp (liftComp (l.mapM fun T => if i ∈ C.holders T then
          (hashQuery ((.history (h T) : Query C)) >>= fun hh => hashQuery ((.digest (vector 256 (salts T)) hh : Query C)))
        else (pure 0 : OracleComp (RoSpec C) HashOutput)) (LocalSpec C)) (PartySpec C E RealSpec) >>= k)
  | [], hist, k, hk => by
    simpa using hk [] hist (List.Subset.refl _) rfl fun m hm => absurd hm (Nat.not_lt_zero m)
  | T :: l, hist, k, hk => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
    by_cases hT : i ∈ C.holders T
    · simp only [hT, ↓reduceIte, liftComp_bind, bind_assoc]
      refine reachH_hash_bind _ hist _ fun hh => reachH_hash_bind _ _ _ fun d => ?_
      refine reachH_digests_bind n i h salts l _ (fun ds => k (d :: ds)) fun ds hist' hsub hlen hcells =>
        hk _ hist' (fun a ha => hsub (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha))) (by simp [hlen])
          fun m hm hmT => ?_
      rcases m with _ | m
      · exact ⟨hh, hsub (by simp), hsub (by simp)⟩
      · exact hcells m (by simpa using hm) hmT
    · simp only [hT, ↓reduceIte, liftComp_pure, pure_bind]
      refine reachH_digests_bind n i h salts l hist (fun ds => k (0 :: ds)) fun ds hist' hsub hlen hcells =>
        hk _ hist' hsub (by simp [hlen]) fun m hm hmT => ?_
      rcases m with _ | m
      · exact absurd hmT hT
      · exact hcells m (by simpa using hm) hmT


omit [Field E] [Algebra Bit E] in
/-- The digest round from the state `s` reaches its exchange at once. Each later result of a
continuation needs the test of the digest round. -/
theorem reachH_compareDigests {β γ : Type} {P : γ → Prop} (salts : Shares C Bit) (s : RunState C)
    (rest : Unit → RunM C E RealSpec β) (g : Option (β × RunState C) → OracleComp (PartySpec C E RealSpec) γ)
    (hist : List (Query C × HashOutput)) :
    ReachH P (fun hist out resume => ∃ digests,
        out = (fun l => if l = ctx.self then none else some (.hashes digests)) ∧
        DigestRound.DigestSent ctx.self s.history hist digests ∧
        ∀ inbox, ∀ x ∈ support (resume inbox), x ∈ support (g none) ∨
          (DigestRound.DigestAgree ctx.self digests inbox ∧ ∃ r, x ∈ support (g (some r))))
      0 hist ((((compareDigests (E := E) ctx salts >>= rest).run s).run) >>= g) := by
  unfold compareDigests
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc, OptionT.run_bind,
    Option.elimM, oracleStep, localStep, OptionT.run_lift]
  refine reachH_digests_bind 0 ctx.self s.history salts C.terms hist _ fun ds hist' hsub hlen hcells => ?_
  simp only [Option.elim, exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk, pure_bind,
    Option.elimM]
  refine ReachH.here hist' _ _ ⟨ds, rfl, ⟨s.history, fun T => List.prefix_refl _, fun T hT => ?_⟩,
    fun inbox x hx => ?_⟩
  · have hm : C.terms.idxOf T < C.terms.length := List.idxOf_lt_length_of_mem (mem_terms T)
    have hc := hcells _ hm
    simp only [List.getElem_idxOf] at hc
    obtain ⟨hh, h1, h2⟩ := hc hT
    refine ⟨_, hh, _, h1, h2, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
  · change x ∈ support (OptionT.run (if (C.parties.any fun j => Msg.isAbort (inbox j)) = true then failure
      else pure inbox) >>= _) at hx
    by_cases hab : (C.parties.any fun j => Msg.isAbort (inbox j)) = true
    · left
      simp only [hab, ↓reduceIte, OptionT.run_failure, pure_bind] at hx
      exact hx
    simp only [hab, Bool.false_eq_true, ↓reduceIte, OptionT.run_pure, pure_bind] at hx
    by_cases hreq : ∀ (T : C.Term), ∀ j ∈ C.holders T, ∀ j' ∈ C.holders T,
        (if j = ctx.self then ds else Msg.hashesOf (inbox j))[List.idxOf T C.terms]? =
            (if j' = ctx.self then ds else Msg.hashesOf (inbox j'))[List.idxOf T C.terms]? ∧
          (if j = ctx.self then ds else Msg.hashesOf (inbox j))[List.idxOf T C.terms]?.isSome = true
    · simp only [require] at hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨o, -, hx⟩ := hx
      rcases o with _ | r
      · exact Or.inl hx
      · refine Or.inr ⟨⟨fun c hc => hab ?_, fun T l hl l' hl' => hreq T l hl l' hl'⟩, r, hx⟩
        rw [List.any_eq_true]
        exact ⟨c, List.mem_finRange c, by rw [hc]; rfl⟩
    · left
      simp only [require, hreq, ↓reduceIte, OptionT.run_failure, pure_bind] at hx
      exact hx


/-- `CheckReach` holds. The check reaches its digest round after the coin key, the slice steps, the
halving steps and one `extendMult`, and the running history only grows on the way. -/
theorem checkReach : CheckReach K ctx := by
  intro tuples htup st γ P g hnone hist
  rw [check_eq K ctx _ tuples htup]
  have hdepth : checkLabels ((tuples.map (·.count)).sum) - 3 =
      1 + (0 + (0 + ((List.range sliceBits).length * 2 +
        ((List.range (halvings ((tuples.map (·.count)).sum) - sliceBits)).length * 2 + (0 + (1 + (0 + 0))))))) := by
    rw [checkLabels, ite_eq_right htup, List.length_range, List.length_range, halvings]
    omega
  rw [hdepth]
  have hcoin := runTimed_realCoin (G := RealSpec) K ctx
  have hextend := runTimed_realExtendMult (G := RealSpec) K ctx
  have grow : ∀ {α : Type} {p : RunM C E RealSpec α} {s s' : RunState C} {a : α}, Moves HistGrows p →
      some (a, s') ∈ support (p.run s).run → HistGrows s s' := fun hp h => moves_support hp _ _ h
  refine reachH_runBind (runTimed_coinKey K _ hcoin) hnone (fun hist key s₁ hs₁ => ?_) hist
  refine reachH_runBind (runTimed_expand K key _) hnone (fun hist τ s₂ hs₂ => ?_) hist
  refine reachH_runBind (RunTimed.lift (timed_require _)) hnone (fun hist u s₃ hs₃ => ?_) hist
  refine reachH_runBind (RunTimed.foldlM _ (runTimed_sliceStep K ctx _ hcoin hextend τ _) _ _) hnone
    (fun hist p s₄ hs₄ => ?_) hist
  refine reachH_runBind (RunTimed.foldlM _ (runTimed_halvingStep K ctx _ hcoin hextend _) _ _) hnone
    (fun hist p' s₅ hs₅ => ?_) hist
  obtain ⟨A, B, D⟩ := p'
  unfold finalStep
  dsimp only
  refine reachH_runBind (runTimed_prssRandomness ctx _ 1 2) hnone (fun hist w s₆ hs₆ => ?_) hist
  refine reachH_runBind (hextend _) hnone (fun hist q s₇ hs₇ => ?_) hist
  refine reachH_runBind (runTimed_prssRandomness ctx _ 2 256) hnone (fun hist salts s₈ hs₈ => ?_) hist
  refine reachH_mono (reachH_compareDigests ctx salts.1 s₈ _ g hist) (fun x hx => hx)
    fun hist out resume h => ?_
  obtain ⟨digests, hout, ⟨hh, hpre, hcells⟩, hres⟩ := h
  have h₁ := grow (moves_hist_coinKey K ctx) hs₁
  have h₂ := grow (by unfold expand; exact moves_hist_lift _) hs₂
  have h₃ := grow (moves_hist_lift _) hs₃
  have h₄ := grow (moves_hist_foldlM _ (moves_hist_sliceStep K ctx τ _) _ _) hs₄
  have h₅ := grow (moves_hist_foldlM _ (moves_hist_halvingStep K ctx _) _ _) hs₅
  have h₆ := grow (moves_hist_prssRandomness ctx _ 1 2) hs₆
  have h₇ := grow (moves_hist_extendMult K ctx _) hs₇
  have h₈ := grow (moves_hist_prssRandomness ctx _ 2 256) hs₈
  refine ⟨digests, hout, ⟨hh, fun T => ?_, hcells⟩, hres⟩
  exact (h₁ T).trans ((h₂ T).trans ((h₃ T).trans ((h₄ T).trans ((h₅ T).trans ((h₆ T).trans
    ((h₇ T).trans ((h₈ T).trans (hpre T))))))))

end CheckWalk



section Ghost

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
/-- An honest operator with a result in the ghost run of one ceremony recorded one opening for each
batch of the job list. -/
theorem ghost_openings (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (i : C.Party)
    (hi : i ∉ D.1) (hout : (ω.1.2 i).output.isSome) :
    (openingsOf (ceremonyRecord ω.1.2 i)).length = (chunks settings.batchSize c.jobs).length := by
  unfold ghostCeremony at hω
  have hpath := BatchCounters.executePhaseR_onPathR prims D D net ([] : Record C E) rounds c.adversary
    (fun i => (recCeremony K circuits settings i c).run.run) world ω hω i hi
  unfold ceremonyRecord
  rcases hs : ω.1.2 i with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at hpath hout
  · obtain ⟨o, rfl⟩ := Option.isSome_iff_exists.1 hout
    have hmem := hpath.done
    unfold recCeremony at hmem
    split at hmem
    · obtain ⟨z₁, h₁, ⟨-, heq⟩ | ⟨a, ha, z₂, h₂, heq⟩⟩ := mem_support_recM_bind _ _ _ hmem
      · cases heq
      · rcases a with ⟨_ | outputs, st'⟩
        · simp at h₂
          subst h₂
          cases heq
        · simp at h₂
          subst h₂
          simp only [Prod.mk.injEq] at heq
          rw [RStep.record, heq.2, List.append_nil]
          exact recRun_full K circuits settings i _ c.jobs c.counters z₁ h₁ (by rw [ha]; rfl)
    · simp at hmem
  · cases hout
  · cases hout

omit [Fintype E] [DecidableEq E] in
/-- The digest round on the ghost run of one ceremony, with no premise on the check. -/
theorem ghost_digestRound (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (hseeds : seedsDiffer D c.keys = false)
    (ω : (net.State × CeremonySteps C E) × StreamState C)
    (hω : ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world)) (k : ℕ)
    (hk : k < (chunks settings.batchSize c.jobs).length)
    (htup : tupleCount (((chunks settings.batchSize c.jobs)[k]).map (circuits (gameParameter D c.keys) ·.kind)) ≠ 0)
    (i : C.Party) (hi : i ∉ D.1) (hout : (ω.1.2 i).output.isSome) :
    ∃ ds : C.Party → List HashOutput,
      (∀ T j j', j ∉ D.1 → j' ∉ D.1 → j ∈ C.holders T → j' ∈ C.holders T →
        (ds j)[C.terms.idxOf T]? = (ds j')[C.terms.idxOf T]?) ∧
      ∀ j b, j ∉ D.1 → (startsOf (ceremonyRecord ω.1.2 j))[k]? = some b →
        PassedShares.HonestDigests ω.2.1 j b (ds j) :=
  ghost_digests K circuits settings prims (fun ctx => checkReach K ctx) D net rounds c world hseeds ω hω k hk htup i hi
    (by rw [ghost_openings prims K circuits settings D net rounds c world ω hω i hi hout]; exact hk)

end Ghost

end DigestRound

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.RerandCells.ghost_rerandCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.RerandCells.ghost_rerandCells


section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace CeremonyRecords

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
/-- `RecordedRerandDraws` holds. -/
theorem recordedRerandDraws : RecordedRerandDraws prims K circuits settings :=
  fun D net rounds c world ω hω j hj b hb T hT hself g hg =>
    RerandCells.ghost_rerandCells K circuits settings prims D net rounds c world ω hω j hj b hb T hT hself g hg

omit [Fintype E] [DecidableEq E] in
/-- `RecordedDigests` holds. -/
theorem recordedDigests : RecordedDigests prims K circuits settings :=
  fun D net rounds _ c world hready ω hω k hk htup i hi hout =>
    DigestRound.ghost_digestRound prims K circuits settings D net rounds c world hready.1 ω hω k hk htup i hi hout

/-- `CeremonyOutputsAgree` from the ghost path, the start of each check and the term keys. -/
theorem ceremonyOutputsAgree_of_rest (hpath : GhostOnPath (C := C) (E := E) prims)
    (hstarted : CeremonyStarted prims K circuits settings) (hkeys : RecordedTermKeys prims K circuits settings) :
    CeremonyOutputsAgree prims K circuits settings :=
  ceremonyOutputsAgree_of_parts prims K circuits settings hpath hstarted hkeys
    (recordedRerandDraws prims K circuits settings) (recordedDigests prims K circuits settings)

end CeremonyRecords

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestRound.ghost_digestRound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.DigestRound.ghost_digestRound

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyOutputsAgree_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CeremonyRecords.ceremonyOutputsAgree_of_rest
