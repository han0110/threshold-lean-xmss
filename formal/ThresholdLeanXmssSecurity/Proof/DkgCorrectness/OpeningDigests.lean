import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.OpeningReach

/-!
# The hash cells of an opening on the recorded run

The section `CachedOpening` adds the hash cells to the walk of the rounds (`ReachH`, `StepReachH`) and
follows them through a phase (`executePhaseR_reachH`). The section `OpeningDigests` gives the same
walk for a recorded batch and for the batches of a ceremony (`reachH_recBatch`, `reachH_recBatches`).
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace CachedOpening

open LiveRounds

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## The wait of depth `n` with the answers of `H` -/

section Reach

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α ρ : Type}

/-- The answer of a local query as a list of answers of `H`. It is one pair for a query of `H`, and it
is empty for each other query. -/
def hashLog : (q : (LocalSpec C).Domain) → (LocalSpec C).Range q → List (Query C × HashOutput)
  | .inr (.inl q), r => [(q, r)]
  | _, _ => []

/-- Each pair of `hist` at an input that `H` does not fix has its cell in `cache`. -/
def Cached (hist : List (Query C × HashOutput)) (cache : HashCache C) : Prop :=
  ∀ p ∈ hist, ¬ IsFixed p.1 → cache p.1 = some p.2

theorem Cached.mono {hist : List (Query C × HashOutput)} {cache cache' : HashCache C} (h : Cached hist cache)
    (hle : cache ≤ cache') : Cached hist cache' :=
  fun p hp hfix => hle (h p hp hfix)

theorem cached_nil (cache : HashCache C) : Cached [] cache := fun _ hp => absurd hp List.not_mem_nil

theorem Cached.append {hist hist' : List (Query C × HashOutput)} {cache : HashCache C} (h : Cached hist cache)
    (h' : Cached hist' cache) : Cached (hist ++ hist') cache := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h p hp
  · exact h' p hp

/-- On each path, the program ends with a leaf in `P` before its wait of depth `n`, or it reaches
its wait of depth `n`, and the answers `hist` of `H` on the path, the outbox and the continuation of
that wait are in `Q`. -/
inductive ReachH {γ : Type} (P : γ → Prop)
    (Q : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E G) γ) → Prop) :
    ℕ → List (Query C × HashOutput) → OracleComp (PartySpec C E G) γ → Prop
  | early (n : ℕ) (hist : List (Query C × HashOutput)) (x : γ) (h : P x) : ReachH P Q n hist (pure x)
  | queryLocal (n : ℕ) (hist : List (Query C × HashOutput)) (q : (LocalSpec C).Domain)
      (k : (LocalSpec C).Range q → OracleComp (PartySpec C E G) γ)
      (h : ∀ r, ReachH P Q n (hashLog q r ++ hist) (k r)) : ReachH P Q n hist (.liftBind (.inl (.inl q)) k)
  | here (hist : List (Query C × HashOutput)) (out : Mail C E) (k : Mail C E → OracleComp (PartySpec C E G) γ)
      (h : Q hist out k) : ReachH P Q 0 hist (.liftBind (.inl (.inr out)) k)
  | round (n : ℕ) (hist : List (Query C × HashOutput)) (out : Mail C E)
      (k : Mail C E → OracleComp (PartySpec C E G) γ)
      (h : ∀ r, ReachH P Q n hist (k r)) : ReachH P Q (n + 1) hist (.liftBind (.inl (.inr out)) k)

/-- A ghost step that is done with a leaf in `P`, or that waits at depth `n` of its program with a
history of `H` whose cells are in `cache`. -/
def StepReachH (P : Option α × ρ → Prop)
    (Q : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E G) (Option α × ρ)) → Prop)
    (n : ℕ) (cache : HashCache C) : RStep C E G α ρ → Prop
  | .done out record => P (out, record)
  | .wait outbox resume => ∃ hist, Cached hist cache ∧ match n with
    | 0 => Q hist outbox resume
    | n + 1 => ∀ inbox, ReachH P Q n hist (resume inbox)
  | .call _ _ => False

theorem StepReachH.mono {P : Option α × ρ → Prop}
    {Q : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E G) (Option α × ρ)) → Prop}
    {n : ℕ} {cache cache' : HashCache C} {s : RStep C E G α ρ} (h : StepReachH P Q n cache s)
    (hle : cache ≤ cache') : StepReachH P Q n cache' s := by
  cases s with
  | done out record => exact h
  | wait outbox resume =>
    obtain ⟨hist, hc, hq⟩ := h
    exact ⟨hist, hc.mono hle, hq⟩
  | call input resume => exact h

end Reach

/-! ## The local steps in `streamWorld` -/

section World

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α ρ : Type} (prims : Primitives)
  (Dw : C.Coalition)

/-- A local query in `streamWorld` puts its answer of `H` at an input that `H` does not fix into the
hash cache. -/
theorem streamWorld_hashLog (q : (LocalSpec C).Domain) (s : HashCache C × HiddenCache C)
    (y : (LocalSpec C).Range q × (HashCache C × HiddenCache C))
    (hy : y ∈ support ((streamWorld prims Dw (.inr q)).run s)) : Cached (hashLog q y.1) y.2.1 := by
  rcases q with n | q | x
  · exact cached_nil _
  · obtain ⟨r, hr, rfl⟩ := mem_support_onHash _ s y hy
    intro p hp hfix
    simp only [hashLog, List.mem_singleton] at hp
    subst hp
    change r ∈ support ((hashAnswer prims q).run s.1) at hr
    rw [hashAnswer_of_not_isFixed prims hfix] at hr
    exact (randomOracle_support q s.1 r hr).2.1
  · exact cached_nil _

/-- The local steps of a program in `streamWorld` from a cache with the cells of `hist` stop at a
step that is done with a leaf in `P` or waits at depth `n` with a history whose cells are in the new
cache. -/
theorem reachH_advanceR {P : Option α × ρ → Prop}
    {Q : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E G) (Option α × ρ)) → Prop}
    {n : ℕ} {hist : List (Query C × HashOutput)} {p : OracleComp (PartySpec C E G) (Option α × ρ)}
    (h : ReachH P Q n hist p) :
    ∀ s z, Cached hist s.1 → z ∈ support ((simulateQ (streamWorld prims Dw) (free (advanceR p))).run s) →
      StepReachH P Q n z.2.1 z.1 := by
  induction h with
  | early n hist x hx =>
    intro s z _ hz
    change z ∈ support ((simulateQ (streamWorld prims Dw) (free (pure (RStep.done x.1 x.2)))).run s) at hz
    simp only [free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hx
  | queryLocal n hist q k _ ih =>
    intro s z hc hz
    change z ∈ support ((simulateQ (streamWorld prims Dw) (free (OracleComp.lift
      (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advanceR (k r)))).run s) at hz
    simp only [free, simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    rw [simulateQ_HasQuery_query] at hy
    exact ih y.1 y.2 z ((streamWorld_hashLog prims Dw q s y hy).append
      (hc.mono (streamWorld_mono prims Dw (.inr q) s y hy))) hz
  | here hist out k hq =>
    intro s z hc hz
    change z ∈ support ((simulateQ (streamWorld prims Dw) (free (pure (RStep.wait out k)))).run s) at hz
    simp only [free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hist, hc, hq⟩
  | round n hist out k h _ =>
    intro s z hc hz
    change z ∈ support ((simulateQ (streamWorld prims Dw) (free (pure (RStep.wait out k)))).run s) at hz
    simp only [free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hist, hc, h⟩

end World

/-! ## The lockstep of the ghost executor in `streamWorld` -/

section Lockstep

variable {C : Committee} {E : Type} {α ρ : Type} (prims : Primitives) (Dw : C.Coalition)

/-- Each computation of a sequence in `streamWorld` from a cache above `c₀` gives a value with a
property that a larger cache keeps. Then the sequence from a cache above `c₀` gives each value with the
property at the end cache. -/
theorem sequenceFin_from {β : Type} (c₀ : HashCache C) :
    ∀ {n : ℕ} (Q : Fin n → β → HashCache C → Prop) (f : Fin n → OracleComp (WorldSpec C) β),
      (∀ i b c c', Q i b c → c ≤ c' → Q i b c') →
      (∀ i s y, c₀ ≤ s.1 → y ∈ support ((simulateQ (streamWorld prims Dw) (f i)).run s) → Q i y.1 y.2.1) →
      ∀ s z, c₀ ≤ s.1 → z ∈ support ((simulateQ (streamWorld prims Dw) (OverPermutation.sequenceFin f)).run s) →
        ∀ i, Q i (z.1 i) z.2.1
  | 0, _, _, _, _, _, _, _, _, i => i.elim0
  | n + 1, Q, f, hmono, hf, s, z, hs, hz, i => by
    simp only [OverPermutation.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, w, hw, rfl⟩ := hz
    cases i using Fin.cases with
    | zero => exact hmono 0 _ _ _ (hf 0 s y hs hy) (streamWorld_run_mono prims Dw _ y.2 w hw)
    | succ i =>
      exact sequenceFin_from c₀ (fun i => Q i.succ) (fun i => f i.succ) (fun i => hmono i.succ)
        (fun i => hf i.succ) y.2 w (hs.trans (streamWorld_run_mono prims Dw _ s y hy)) hw i

/-- The value of a computation in `streamWorld` is in the support of the computation. -/
theorem fst_mem_support {β : Type} (oa : OracleComp (WorldSpec C) β) (s : HashCache C × HiddenCache C)
    (z : β × (HashCache C × HiddenCache C)) (hz : z ∈ support ((simulateQ (streamWorld prims Dw) oa).run s)) :
    z.1 ∈ support oa :=
  support_simulateQ_run'_subset (streamWorld prims Dw) oa s
    (by rw [StateT.run'_eq, support_map]; exact ⟨z, hz, rfl⟩)

variable {Ia : Type} (D' : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (blank : ρ)
  (P : C.Party → Option α × ρ → Prop)
  (Q : C.Party → List (Query C × HashOutput) → Mail C E →
    (Mail C E → OracleComp (PartySpec C E RealSpec) (Option α × ρ)) → Prop)

/-- A round of the ghost executor in `streamWorld` takes each honest step from depth `n + 1` to depth
`n`, and keeps the cells of its history in the hash cache. -/
theorem stepRoundR_reachH (n : ℕ) (st : A.State) (steps : C.Party → RStep C E RealSpec α ρ)
    (s : HashCache C × HiddenCache C) (h : ∀ i, i ∉ D'.1 → StepReachH (P i) (Q i) (n + 1) s.1 (steps i))
    (y : (A.State × (C.Party → RStep C E RealSpec α ρ) × (C.Party → C.Party → Option (Msg E))) ×
      (HashCache C × HiddenCache C))
    (hy : y ∈ support ((simulateQ (streamWorld prims Dw)
      (stepRoundR worldRoles D' A noFunctionality blank st steps)).run s)) :
    ∀ i, i ∉ D'.1 → StepReachH (P i) (Q i) n y.2.1 (y.1.2.1 i) := by
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
  refine sequenceFin_from prims Dw s.1 (fun j v c => j ∉ D'.1 → StepReachH (P j) (Q j) n c v) _
    (fun j b c c' hq hle hj => (hq hj).mono hle) (fun j s' y hs' hy hj => ?_) a.2 w
    (streamWorld_run_mono prims Dw _ s a ha) hw
  have hj' := h j hj
  rcases hsj : steps j with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · simp only [hsj, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rw [hsj] at hj'
    exact hj'
  · simp only [hsj, hj, ↓reduceIte] at hy
    rw [hsj] at hj'
    obtain ⟨hist, hc, hr⟩ := hj'
    exact reachH_advanceR prims Dw (hr _) s' y (hc.mono hs') hy
  · exact input.elim

/-- The lockstep of the ghost executor in `streamWorld`. Let each honest step be done with a leaf in
`P` or wait at depth `n` with a history whose cells are in the cache. Then at the end each honest
record is `blank` or a record of a leaf in `P`, or there is a step vector `steps₀` of the round of
depth `n`, with the messages `sent` of the corrupt operators and a cache below the final cache that
holds the cells of the histories of `steps₀`, and each final honest record is `blank` or a record of
an output of the rest of the program of `steps₀` on the mail of that round. -/
theorem executeRoundsR_reachH :
    ∀ (n fuel : ℕ) (st : A.State) (steps : C.Party → RStep C E RealSpec α ρ) (s : HashCache C × HiddenCache C),
      (∀ i, i ∉ D'.1 → StepReachH (P i) (Q i) n s.1 (steps i)) →
      ∀ z ∈ support ((simulateQ (streamWorld prims Dw)
        (executeRoundsR worldRoles D' A noFunctionality blank fuel st steps)).run s),
        (∀ i, i ∉ D'.1 → (z.1.2 i).record blank = blank ∨ ∃ out, P i (out, (z.1.2 i).record blank)) ∨
        ∃ (steps₀ : C.Party → RStep C E RealSpec α ρ) (sent : C.Party → C.Party → Option (Msg E))
          (cache : HashCache C), cache ≤ z.2.1 ∧ (∀ i, i ∉ D'.1 → StepReachH (P i) (Q i) 0 cache (steps₀ i)) ∧
          ∀ i, i ∉ D'.1 → (z.1.2 i).record blank = blank ∨
            ∃ out, (out, (z.1.2 i).record blank) ∈ support (nextR blank (steps₀ i) (LiveRounds.roundInbox D' steps₀ sent i)) := by
  have hstop : ∀ (n : ℕ) (cache : HashCache C) (steps : C.Party → RStep C E RealSpec α ρ),
      (∀ i, i ∉ D'.1 → StepReachH (P i) (Q i) n cache (steps i)) →
      ∀ i, i ∉ D'.1 → (steps i).record blank = blank ∨ ∃ out, P i (out, (steps i).record blank) := by
    intro n cache steps h i hi
    have hs := h i hi
    revert hs
    cases steps i with
    | done out record => exact fun hs => Or.inr ⟨out, hs⟩
    | wait outbox resume => exact fun _ => Or.inl rfl
    | call input resume => exact fun _ => Or.inl rfl
  have hself : ∀ (step : RStep C E RealSpec α ρ) (inbox : Mail C E),
      step.record blank = blank ∨ ∃ out, (out, step.record blank) ∈ support (nextR blank step inbox) := by
    intro step inbox
    cases step with
    | done out record => exact Or.inr ⟨out, by simp [RStep.record, nextR]⟩
    | wait outbox resume => exact Or.inl rfl
    | call input resume => exact Or.inl rfl
  intro n
  induction n with
  | zero =>
    intro fuel st steps s h z hz
    right
    have hle := streamWorld_run_mono prims Dw _ s z hz
    rcases fuel with _ | fuel
    · simp only [executeRoundsR, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨steps, fun _ _ => none, s.1, le_rfl, h, fun i _ => hself (steps i) _⟩
    unfold executeRoundsR at hz
    split_ifs at hz with hall
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨steps, fun _ _ => none, s.1, le_rfl, h, fun i _ => hself (steps i) _⟩
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨r, hr, hz⟩ := hz
    have hr' := fst_mem_support prims Dw _ s r hr
    have hz' := fst_mem_support prims Dw _ r.2 z hz
    refine ⟨steps, r.1.2.2, s.1, hle, h, fun i hi => ?_⟩
    have hpath := executeRoundsR_freePath D' A noFunctionality blank
      (fun i => nextR blank (steps i) (LiveRounds.roundInbox D' steps r.1.2.2 i)) fuel r.1.1 r.1.2.1
      (fun j hj => freePath_stepNext blank (steps j) _ _
        (stepRoundR_next D' A noFunctionality blank st steps r.1 hr' j hj)) z.1 hz' i hi
    exact hpath.record blank
  | succ n ih =>
    intro fuel st steps s h z hz
    rcases fuel with _ | fuel
    · simp only [executeRoundsR, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl (hstop _ _ steps h)
    unfold executeRoundsR at hz
    split_ifs at hz with hall
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl (hstop _ _ steps h)
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨r, hr, hz⟩ := hz
    exact ih fuel r.1.1 r.1.2.1 r.2 (stepRoundR_reachH prims Dw D' A blank P Q n st steps s h r hr) z hz

/-- The lockstep from the start of a ghost phase in `streamWorld`, with the depth `n` for each honest
program. -/
theorem executePhaseR_reachH (n fuel : ℕ) (st : A.State)
    (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option α × ρ))
    (h : ∀ i, i ∉ D'.1 → ReachH (P i) (Q i) n [] (program i)) (s : HashCache C × HiddenCache C) :
    ∀ z ∈ support ((simulateQ (streamWorld prims Dw)
      (executePhaseR worldRoles D' A noFunctionality blank fuel st program)).run s),
      (∀ i, i ∉ D'.1 → (z.1.2 i).record blank = blank ∨ ∃ out, P i (out, (z.1.2 i).record blank)) ∨
      ∃ (steps₀ : C.Party → RStep C E RealSpec α ρ) (sent : C.Party → C.Party → Option (Msg E))
        (cache : HashCache C), cache ≤ z.2.1 ∧ (∀ i, i ∉ D'.1 → StepReachH (P i) (Q i) 0 cache (steps₀ i)) ∧
        ∀ i, i ∉ D'.1 → (z.1.2 i).record blank = blank ∨
          ∃ out, (out, (z.1.2 i).record blank) ∈ support (nextR blank (steps₀ i) (LiveRounds.roundInbox D' steps₀ sent i)) := by
  intro z hz
  unfold executePhaseR at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  unfold startStepsR at hy
  refine executeRoundsR_reachH prims Dw D' A blank P Q n fuel st y.1 y.2 (fun i hi => ?_) z hz
  refine sequenceFin_from prims Dw s.1 (fun j v c => j ∉ D'.1 → StepReachH (P j) (Q j) n c v) _
    (fun j b c c' hq hle hj => (hq hj).mono hle) (fun j s' w _ hw hj => ?_) s y le_rfl hy i hi
  simp only [hj, ↓reduceIte] at hw
  exact reachH_advanceR prims Dw (h j hj) s' w (cached_nil _) hw

end Lockstep

/-! ## The copy hashes of `OpenRep` enter the history -/

section Digests

variable {C : Committee} {E : Type}

/-- A query of `H` in an operator program is a local query. -/
theorem liftComp_hashQuery (x : Query C) :
    liftComp (liftComp (hashQuery x) (LocalSpec C)) (PartySpec C E RealSpec) =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl (.inr (.inl x))))) :=
  rfl

/-- The queries of `H` at `q T` for each term `T` of `l` put their answers into the history. The
continuation gets the answers `ds` and a larger history that holds the pair of each term with its
answer. -/
theorem reachH_hashes_bind {γ : Type} {P : γ → Prop}
    {Q : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) γ) → Prop}
    (n : ℕ) (q : C.Term → Query C) :
    ∀ (l : List C.Term) (hist : List (Query C × HashOutput)) (k : List HashOutput → OracleComp (PartySpec C E RealSpec) γ),
      (∀ ds hist', hist ⊆ hist' → List.Forall₂ (fun T d => (q T, d) ∈ hist') l ds → ReachH P Q n hist' (k ds)) →
      ReachH P Q n hist
        (liftComp (liftComp (l.mapM fun T => hashQuery (q T)) (LocalSpec C)) (PartySpec C E RealSpec) >>= k)
  | [], hist, k, hk => by
    simpa using hk [] hist (List.Subset.refl _) .nil
  | T :: l, hist, k, hk => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
    rw [liftComp_hashQuery]
    refine ReachH.queryLocal n hist (.inr (.inl (q T))) _ fun r => ?_
    exact reachH_hashes_bind n q l _ (fun ds => k (r :: ds)) fun ds hist' hsub hfor =>
      hk (r :: ds) hist' (fun p hp => hsub (List.mem_append_right _ hp))
        (.cons (hsub (List.mem_append_left _ (List.mem_singleton_self _))) hfor)

variable [Field E] [Algebra Bit E] (K : Constants C E)

end Digests

/-! ## The copy hashes of an opening of the first ceremony -/

section Opening

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (prims : Primitives)
  (budget : StartBudget)

/-- The exchange of `OpenRep` of batch `k` at operator `j` after the answers `hist` of `H`. It is
`LiveRounds.OpenWait` with the copy hashes of the outbox as answers of `H` in `hist` at the copies of
the sharing of the start `b`. -/
def OpenWaitH (j : C.Party) (k : ℕ) (hist : List (Query C × HashOutput)) (out : Mail C E)
    (resume : Mail C E → OracleComp (PartySpec C E RealSpec) (Option TreeOutput × Record C E)) : Prop :=
  (∃ (b : BatchStart C) (digests : List HashOutput),
      out = repOutbox K j b.v' (outputsOf b.circuits).length digests ∧
      List.Forall₂ (fun T d => ((.copy (vector (outputsOf b.circuits).length (b.v' T)) : Query C), d) ∈ hist)
        C.terms digests ∧
      ∀ inbox, ∀ x ∈ support (resume inbox), (startsOf x.2)[k]? = some b) ∧
    ∀ inbox, ∀ x ∈ support (resume inbox), ∀ v inbox', (openingsOf x.2)[k]? = some (v, inbox') →
      inbox' = inbox ∧ ∀ c, inbox c ≠ some .abort

end Opening

end CachedOpening

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace OpeningDigests

open LiveRounds CachedOpening RecordedOpening

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## The combinators with the history -/

section Generic

variable {C : Committee} {E : Type} {γ δ : Type}

/-- A timed program and then a continuation that reaches its wait of depth `n` from each history
reach that wait at depth `m + n` from each history. -/
theorem timedLog_reachH_bind {A B : γ → Prop} {P : δ → Prop}
    {Q : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) δ) → Prop}
    {m n : ℕ} {p : OracleComp (PartySpec C E RealSpec) γ} {g : γ → OracleComp (PartySpec C E RealSpec) δ}
    (hp : TimedLog A B m p) (hA : ∀ x, A x → ∃ y, g x = pure y ∧ P y)
    (hB : ∀ hist x, B x → ReachH P Q n hist (g x)) (hist : List (Query C × HashOutput)) :
    ReachH P Q (m + n) hist (p >>= g) := by
  induction hp generalizing hist with
  | stop m x hx =>
    obtain ⟨y, hy, hy'⟩ := hA x hx
    rw [pure_bind, hy]
    exact ReachH.early _ _ y hy'
  | done x hx =>
    rw [pure_bind, Nat.zero_add]
    exact hB hist x hx
  | queryLocal m q k _ ih => exact ReachH.queryLocal (m + n) hist q _ fun r => ih r _
  | round m out k _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact ReachH.round (m + n) hist out _ fun r => ih r hist

/-- A program that reaches its wait of depth `n` keeps that wait with a continuation that keeps
its leaves. -/
theorem reachH_bind_left {P : γ → Prop} {P' : δ → Prop}
    {Q : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) γ) → Prop}
    {Q' : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) δ) → Prop}
    {n : ℕ} {hist : List (Query C × HashOutput)}
    {p : OracleComp (PartySpec C E RealSpec) γ} {g : γ → OracleComp (PartySpec C E RealSpec) δ}
    (hp : ReachH P Q n hist p) (hP : ∀ x, P x → ∃ y, g x = pure y ∧ P' y)
    (hQ : ∀ hist out resume, Q hist out resume → Q' hist out fun r => resume r >>= g) :
    ReachH P' Q' n hist (p >>= g) := by
  induction hp with
  | early n hist x hx =>
    obtain ⟨y, hy, hy'⟩ := hP x hx
    rw [pure_bind, hy]
    exact ReachH.early n hist y hy'
  | queryLocal n hist q k _ ih => exact ReachH.queryLocal n hist q _ ih
  | here hist out k hq => exact ReachH.here hist out _ (hQ hist out k hq)
  | round n hist out k _ ih => exact ReachH.round n hist out _ ih

/-- A map of the leaves keeps the wait of depth `n`. -/
theorem reachH_map {P : γ → Prop} {P' : δ → Prop}
    {Q : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) γ) → Prop}
    {Q' : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) δ) → Prop}
    {n : ℕ} {hist : List (Query C × HashOutput)} {p : OracleComp (PartySpec C E RealSpec) γ} (g : γ → δ)
    (hp : ReachH P Q n hist p) (hP : ∀ x, P x → P' (g x))
    (hQ : ∀ hist out resume, Q hist out resume → Q' hist out fun r => g <$> resume r) :
    ReachH P' Q' n hist (g <$> p) := by
  rw [map_eq_bind_pure_comp]
  refine reachH_bind_left hp (fun x hx => ⟨g x, rfl, hP x hx⟩) fun hist out resume h => ?_
  have hres : (fun r => resume r >>= pure ∘ g) = fun r => g <$> resume r :=
    funext fun r => (map_eq_bind_pure_comp _ g (resume r)).symm
  rw [hres]
  exact hQ hist out resume h

/-- A program that reaches its wait of depth `n` keeps it under weaker predicates. -/
theorem reachH_mono {P P' : γ → Prop}
    {Q Q' : List (Query C × HashOutput) → Mail C E → (Mail C E → OracleComp (PartySpec C E RealSpec) γ) → Prop}
    {n : ℕ} {hist : List (Query C × HashOutput)} {p : OracleComp (PartySpec C E RealSpec) γ}
    (hp : ReachH P Q n hist p) (hP : ∀ x, P x → P' x)
    (hQ : ∀ hist out resume, Q hist out resume → Q' hist out resume) : ReachH P' Q' n hist p := by
  induction hp with
  | early n hist x hx => exact ReachH.early n hist x (hP x hx)
  | queryLocal n hist q k _ ih => exact ReachH.queryLocal n hist q _ ih
  | here hist out k hq => exact ReachH.here hist out _ (hQ hist out k hq)
  | round n hist out k _ ih => exact ReachH.round n hist out _ ih

end Generic

/-! ## The recorded steps with the history -/

section Rec

variable {C : Committee} {E : Type} {α β : Type}

/-- A timed program with no record and then a continuation that reaches its wait of depth `n` from
each history. -/
theorem reachH_lift_bind {P : Option β × List (RecEvent C E) → Prop}
    {Q : List (Query C × HashOutput) → Mail C E →
      (Mail C E → OracleComp (PartySpec C E RealSpec) (Option β × List (RecEvent C E))) → Prop}
    {m n : ℕ} {p : PartyM C E RealSpec α} {f : α → RecM C E β} (hp : Timed m p.run) (hP : P (none, []))
    (hf : ∀ hist a, ReachH P Q n hist (f a).run.run) (hist : List (Query C × HashOutput)) :
    ReachH P Q (m + n) hist (RecM.lift p >>= f).run.run := by
  rw [run_recLift_bind]
  generalize p.run = oa at hp ⊢
  induction hp generalizing hist with
  | abort m => exact ReachH.early _ _ _ hP
  | done a => simpa only [pure_bind, Option.elim_some, Nat.zero_add] using hf hist a
  | queryLocal m q k _ ih => exact ReachH.queryLocal (m + n) hist q _ fun r => ih r _
  | round m out k _ ih =>
    rw [Nat.add_right_comm m 1 n]
    exact ReachH.round (m + n) hist out _ fun r => ih r hist
  | call m input k _ ih => exact input.elim

/-- The queries of `H` at `q T` for each term `T` of `l` with no record. The continuation gets the
answers and a history that holds the pair of each term with its answer. -/
theorem reachH_lift_hashes {σ : Type} {P : Option β × List (RecEvent C E) → Prop}
    {Q : List (Query C × HashOutput) → Mail C E →
      (Mail C E → OracleComp (PartySpec C E RealSpec) (Option β × List (RecEvent C E))) → Prop}
    (n : ℕ) (l : List C.Term) (q : C.Term → Query C) (st : σ) (f : List HashOutput × σ → RecM C E β)
    (hf : ∀ ds hist, List.Forall₂ (fun T d => (q T, d) ∈ hist) l ds → ReachH P Q n hist (f (ds, st)).run.run)
    (hist : List (Query C × HashOutput)) :
    ReachH P Q n hist
      (RecM.lift (oracleStep (l.mapM fun T => hashQuery (q T)) >>= fun a => pure (a, st)) >>= f).run.run := by
  rw [run_recLift_bind]
  have he : (oracleStep (C := C) (E := E) (G := RealSpec) (l.mapM fun T => hashQuery (q T)) >>=
      fun a => pure (a, st)).run >>= (fun o => o.elim (pure (none, [])) fun a => (f a).run.run) =
      liftComp (liftComp (l.mapM fun T => hashQuery (q T)) (LocalSpec C)) (PartySpec C E RealSpec) >>=
        fun ds => (f (ds, st)).run.run := by
    simp only [oracleStep, localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM, bind_assoc, pure_bind,
      Option.elim_some, OptionT.run_pure]
  rw [he]
  exact reachH_hashes_bind n q l hist _ fun ds hist' _ hfor => hf ds hist' hfor

/-- An exchange with no record is a wait of depth `0`. The rest aborts on an abort frame. -/
theorem reachH_lift_exchange {γ' : Type} {P : Option β × List (RecEvent C E) → Prop}
    {Q : List (Query C × HashOutput) → Mail C E →
      (Mail C E → OracleComp (PartySpec C E RealSpec) (Option β × List (RecEvent C E))) → Prop}
    (hist : List (Query C × HashOutput)) (out : Mail C E) (h : Mail C E → PartyM C E RealSpec γ')
    (f : γ' → RecM C E β)
    (hQ : Q hist out fun inbox => if C.parties.any (fun c => Msg.isAbort (inbox c)) then pure (none, [])
      else (RecM.lift (h inbox) >>= f).run.run) :
    ReachH P Q 0 hist (RecM.lift (exchange out >>= h) >>= f).run.run := by
  rw [run_recLift_bind]
  have he : (exchange (C := C) (G := RealSpec) out >>= h).run >>=
      (fun o => o.elim (pure (none, [])) fun a => (f a).run.run) =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= fun inbox =>
        if C.parties.any (fun c => Msg.isAbort (inbox c)) then pure (none, [])
        else (h inbox).run >>= fun o => o.elim (pure (none, [])) fun a => (f a).run.run := by
    simp only [exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk, pure_bind, Option.elimM]
    refine bind_congr fun inbox => ?_
    by_cases hab : C.parties.any (fun c => Msg.isAbort (inbox c))
    · simp only [Option.elim, hab, ↓reduceIte, OptionT.run_failure, pure_bind]
    · simp only [Option.elim, hab, Bool.false_eq_true, ↓reduceIte, OptionT.run_pure, pure_bind]
  rw [he]
  simp only [run_recLift_bind] at hQ
  exact ReachH.here hist out _ hQ

end Rec

/-! ## The stable wait with the copy hashes -/

section Counts

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  {α β : Type}

/-- `RecordedOpening.WaitAt` with the copy hashes of the outbox as answers of `H` in `hist`. -/
def WaitAtH (j : C.Party) (k : ℕ) (hist : List (Query C × HashOutput)) (out : Mail C E)
    (resume : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α × Record C E)) : Prop :=
  ∃ (b : BatchStart C) (digests : List HashOutput),
    out = repOutbox K j b.v' (outputsOf b.circuits).length digests ∧
    List.Forall₂ (fun T d => ((.copy (vector (outputsOf b.circuits).length (b.v' T)) : Query C), d) ∈ hist)
      C.terms digests ∧
    ∀ inbox, ∀ x ∈ support (resume inbox), (startsOf x.2)[k]? = some b ∧
      (x.1.isSome → k < (openingsOf x.2).length) ∧
      ∀ v inbox', (openingsOf x.2)[k]? = some (v, inbox') → inbox' = inbox ∧ ∀ c, inbox c ≠ some .abort

omit [Fintype E] [DecidableEq E] in
/-- The stable wait keeps its form under a later recorded continuation. -/
theorem WaitAtH.bind {j : C.Party} {k : ℕ} {hist : List (Query C × HashOutput)} {out : Mail C E}
    {resume : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α × Record C E)} (f : α → RecM C E β)
    (h : WaitAtH K j k hist out resume) : WaitAtH K j k hist out fun r => resume r >>= recCont f := by
  obtain ⟨b, digests, hout, hfor, h⟩ := h
  refine ⟨b, digests, hout, hfor, fun inbox x hx => ?_⟩
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
    refine ⟨?_, fun _ => ?_, fun v inbox' hv => h3 v inbox' ?_⟩
    · rw [startsOf_append, List.getElem?_append_left hks]
      exact h1
    · rw [openingsOf_append, List.length_append]
      omega
    · rwa [openingsOf_append, List.getElem?_append_left hko] at hv

omit [Fintype E] [DecidableEq E] in
/-- The stable wait after a prefix record with `k'` starts and `k'` openings is at index `k' + k`. -/
theorem WaitAtH.shift {j : C.Party} {k k' : ℕ} {hist : List (Query C × HashOutput)} {out : Mail C E}
    {resume : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α × Record C E)} (w : Record C E)
    (hs : (startsOf w).length = k') (ho : (openingsOf w).length = k')
    (h : WaitAtH K j k hist out resume) :
    WaitAtH K j (k' + k) hist out fun r => (fun y => (y.1, w ++ y.2)) <$> resume r := by
  obtain ⟨b, digests, hout, hfor, h⟩ := h
  refine ⟨b, digests, hout, hfor, fun inbox x hx => ?_⟩
  rw [support_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨h1, h2, h3⟩ := h inbox y hy
  refine ⟨?_, fun hsome => ?_, fun v inbox' hv => h3 v inbox' ?_⟩
  · rw [startsOf_append, List.getElem?_append_right (by omega), hs, Nat.add_sub_cancel_left]
    exact h1
  · rw [openingsOf_append, List.length_append, ho]
    have := h2 hsome
    omega
  · rwa [openingsOf_append, List.getElem?_append_right (by omega), ho, Nat.add_sub_cancel_left] at hv

omit [Fintype E] [DecidableEq E] in
/-- A recorded program that reaches its stable wait keeps it with any continuation. -/
theorem reachH_recBind_left {j : C.Party} {k n : ℕ} {hist : List (Query C × HashOutput)} {x : RecM C E α}
    (f : α → RecM C E β) (hx : ReachH (Stop k) (WaitAtH K j k) n hist x.run.run) :
    ReachH (Stop k) (WaitAtH K j k) n hist (x >>= f).run.run := by
  rw [run_recBind]
  refine reachH_bind_left hx (fun y hy => ?_) fun hist out resume h => h.bind K f
  rcases y with ⟨_ | a, w⟩
  · exact ⟨(none, w), rfl, rfl, hy.2⟩
  · exact absurd hy.1 (by simp)

omit [Fintype E] [DecidableEq E] in
/-- A map of the result keeps the stable wait. -/
theorem reachH_recMap {j : C.Party} {k n : ℕ} {hist : List (Query C × HashOutput)} {x : RecM C E α}
    (g : α → β) (hx : ReachH (Stop k) (WaitAtH K j k) n hist x.run.run) :
    ReachH (Stop k) (WaitAtH K j k) n hist (g <$> x).run.run := by
  rw [map_eq_bind_pure_comp]
  exact reachH_recBind_left K _ hx

omit [Fintype E] [DecidableEq E] in
/-- A timed recorded prefix with `k'` starts and `k'` openings, and then a continuation that reaches
its stable wait of index `k` from each history, reach the stable wait of index `k' + k`. -/
theorem reachH_recBind {x : RecM C E α} {f : α → RecM C E β} {j : C.Party} {m n a₁ k' k kk : ℕ}
    (hx : TimedLog (Stop a₁) (Full k' k') m x.run.run)
    (hf : ∀ hist c, ReachH (Stop k) (WaitAtH K j k) n hist (f c).run.run) (ha : a₁ ≤ kk) (hk : k' + k = kk)
    (hist : List (Query C × HashOutput)) :
    ReachH (Stop kk) (WaitAtH K j kk) (m + n) hist (x >>= f).run.run := by
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
    refine reachH_map _ (hf hist c) (fun z hz => ⟨hz.1, ?_⟩) fun hist out resume h => h.shift K w hs₁ ho₁
    simp only [openingsOf_append, List.length_append]
    have := hz.2
    omega

end Counts

/-! ## The recorded batch and tree with the history -/

section Batch

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
/-- The check and the opening of a recorded start at operator `j` reach the exchange of `OpenRep`
after the check rounds, with the copy hashes of the outbox in the history. -/
theorem reachH_recCheckOpen (j : C.Party) (b : BatchStart C) (hj : b.ctx.self = j) (k : ℕ) (st : ℕ × ℕ)
    (hist : List (Query C × HashOutput)) :
    ReachH (Stop 0) (WaitAtH K j 0) (checkLabels (tupleCount b.circuits)) hist
      ((recCheckOpen K b k).run st).run.run := by
  simp only [recCheckOpen, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, RecM.liftS, StateT.run_mk,
    StateT.run_set, StateT.run_pure]
  rw [run_recRecord_bind]
  refine reachH_map _ (P := Stop 0) (Q := fun hist out resume => ∃ digests : List HashOutput,
      out = repOutbox K j b.v' (outputsOf b.circuits).length digests ∧
      List.Forall₂ (fun T d => ((.copy (vector (outputsOf b.circuits).length (b.v' T)) : Query C), d) ∈ hist)
        C.terms digests ∧
      ∀ inbox, ∀ x ∈ support (resume inbox), (x.1.isSome → 0 < (openingsOf x.2).length) ∧
        ∀ v inbox', (openingsOf x.2)[0]? = some (v, inbox') → inbox' = inbox ∧ ∀ c, inbox c ≠ some .abort)
    ?_ (fun z hz => ⟨hz.1, ?_⟩) fun hist out resume h => ?_
  rotate_left
  · have := hz.2
    simp only [length_openingsOf_append, length_openingsOf_event]
    omega
  · obtain ⟨digests, hout, hfor, h⟩ := h
    refine ⟨b, digests, hout, hfor, fun inbox x hx => ?_⟩
    rw [support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := h inbox y hy
    have ho : openingsOf ([RecEvent.start b] ++ y.2) = openingsOf y.2 := by
      rw [openingsOf_append]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [startsOf_append]
      rfl
    · rw [ho]
      exact h1
    · rw [ho]
      exact h2
  have hcheck := runTimed_realCheck (G := RealSpec) K b.ctx (batchTuples K b.mode b.circuits b.inputs b.zs b.v')
    b.state
  rw [sum_batchTuples] at hcheck
  rw [show checkLabels (tupleCount b.circuits) = checkLabels (tupleCount b.circuits) + 0 by omega]
  refine reachH_lift_bind (timed_pair hcheck st) ⟨rfl, by simp [openingsOf]⟩ (fun hist p => ?_) hist
  refine reachH_lift_hashes 0 C.terms _ _ _ (fun digests hist' hfor => ?_) hist
  refine reachH_lift_exchange hist' _ _ _ ⟨digests, by rw [hj], hfor, fun inbox x hx => ?_⟩
  by_cases hab : C.parties.any (fun c => Msg.isAbort (inbox c))
  · simp only [hab, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hx
    subst hx
    simp [openingsOf]
  · simp only [hab, Bool.false_eq_true, ↓reduceIte, run_recLift_bind, OptionT.run_pure, pure_bind,
      Option.elim] at hx
    rw [run_recRecord_bind, support_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    have ho : openingsOf ([RecEvent.opened b.v' inbox] ++ y.2) = (b.v', inbox) :: openingsOf y.2 := by
      rw [openingsOf_append]
      rfl
    rw [ho]
    refine ⟨fun _ => Nat.succ_pos _, fun v inbox' hv => ?_⟩
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hv
    refine ⟨hv.2.symm, fun c hc => hab ?_⟩
    rw [List.any_eq_true]
    exact ⟨c, List.mem_finRange c, by rw [hc]; rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- A recorded batch at operator `ctx.self` reaches its exchange of `OpenRep` one round before its
end, with the copy hashes of the outbox in the history. -/
theorem reachH_recBatch (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) (st : ℕ × ℕ)
    (hist : List (Query C × HashOutput)) :
    ReachH (Stop 0) (WaitAtH K ctx.self 0)
      (CheckTiming.exactBatchRounds settings.mode (jobs.map (circuits parameter ·.kind)) - 1) hist
      ((recBatch K circuits settings ctx parameter jobs).run st).run.run := by
  obtain ⟨label, k⟩ := st
  simp only [recBatch, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, RecM.liftS, StateT.run_mk]
  have harith : CheckTiming.exactBatchRounds settings.mode (jobs.map (circuits parameter ·.kind)) - 1 =
      0 + (depth (jobs.map (circuits parameter ·.kind)) * settings.mode.rounds +
        (1 + checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))))) := by
    unfold CheckTiming.exactBatchRounds checkLabels
    split_ifs <;> omega
  rw [harith]
  refine reachH_lift_bind (timed_pair (timed_inputShares ctx jobs) _) ⟨rfl, by simp [openingsOf]⟩
    (fun hist p => ?_) hist
  refine reachH_lift_bind (timed_pair (runTimed_recLayers K ctx settings.mode _ _ _ _) _)
    ⟨rfl, by simp [openingsOf]⟩ (fun hist p₁ => ?_) hist
  refine reachH_lift_bind (timed_pair (runTimed_realRerand K ctx settings.mode _ _ _) _)
    ⟨rfl, by simp [openingsOf]⟩ (fun hist p₂ => ?_) hist
  exact reachH_recCheckOpen K ctx.self ⟨(realRunBuildingBlocks K ctx settings.mode).mode, jobs, parameter,
    jobs.map (circuits parameter ·.kind), p.1, p₁.1.1, p₂.1.1, ctx, p₂.1.2⟩ rfl k p₂.2 hist

omit [Fintype E] [DecidableEq E] in
/-- The batches of a recorded ceremony at operator `ctx.self` reach the exchange of `OpenRep` of
batch `k` after the rounds of the batches before `k`, with the copy hashes in the history. -/
theorem reachH_recBatches (ctx : Context C) (parameter : PublicParameter) (js : List (List Job)) (k : ℕ)
    (hk : k < js.length) (st : ℕ × ℕ) (hist : List (Query C × HashOutput)) :
    ReachH (Stop k) (WaitAtH K ctx.self k)
      (((js.take k).map fun batch =>
        CheckTiming.exactBatchRounds settings.mode (batch.map (circuits parameter ·.kind))).sum +
        (CheckTiming.exactBatchRounds settings.mode (js[k].map (circuits parameter ·.kind)) - 1)) hist
      ((js.mapM (recBatch K circuits settings ctx parameter)).run st).run.run := by
  have hsplit : js = js.take k ++ js[k] :: js.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hmap : js.mapM (recBatch K circuits settings ctx parameter) =
      (js.take k ++ js[k] :: js.drop (k + 1)).mapM (recBatch K circuits settings ctx parameter) :=
    congrArg (List.mapM _) hsplit
  have hlen : (js.take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hk.le]
  rw [hmap, List.mapM_append, StateT.run_bind]
  refine reachH_recBind K (k := 0) (timedLog_recBatches K circuits settings ctx parameter (js.take k) st)
    (fun hist c => ?_) hlen.le (by rw [hlen, Nat.add_zero]) hist
  rw [StateT.run_bind]
  refine reachH_recBind_left K _ ?_
  rw [List.mapM_cons, StateT.run_bind]
  exact reachH_recBind_left K _ (reachH_recBatch K circuits settings ctx parameter js[k] c.2 hist)

end Batch

end OpeningDigests

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CachedOpening.executePhaseR_reachH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CachedOpening.executePhaseR_reachH
