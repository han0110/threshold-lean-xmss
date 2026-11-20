import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Statements
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ready.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Setup

/-!
# The walk of the hidden draws

`SafeThen D post oa Q` states that each free `PRG` call of the operator program `oa` under a hidden
name has its key in `Q`, where `Q` grows by the answer of each `.derive .prss` call on the path, and
that each end of `oa` has `post` with the keys at that end. `executePhase_keepsProvenance` states
that a phase on the network keeps `HiddenProvenance` when each honest program has `SafeThen` from the
empty set of keys. The walk keeps, for each honest operator, a set of keys with a derive cell in the
hash cache, and its next step draws only under these keys.
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
/-! ## Programs that draw under derived keys -/

/-- A free `PRG` call under a hidden name with a key that `A` does not allow for that name. -/
def BadDraw (D : C.Coalition) (A : KeyName C → HashOutput → Prop) : (LocalSpec C).Domain → Prop
  | .inr (.inr x) => Hidden D x.1 ∧ ¬ A x.1 x.2.1
  | _ => False

/-- The keys after a local call with the answer `u`. A `.derive .prss` call adds its answer. -/
def addDerived : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → (HashOutput → Prop) → HashOutput → Prop
  | .inr (.inl (.derive .prss _ _)), u, Q => fun key => Q key ∨ key = u
  | _, _, Q => Q

/-- A local call of an operator that is a bad draw. -/
def PartyBad (D : C.Coalition) (A : KeyName C → HashOutput → Prop) : (PartySpec C E RealSpec).Domain → Prop
  | .inl (.inl t) => BadDraw D A t
  | _ => False

/-- The keys after a call of an operator. -/
def partyAdd : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t →
    (HashOutput → Prop) → HashOutput → Prop
  | .inl (.inl t), u, Q => addDerived t u Q
  | _, _, Q => Q

/-- Each free `PRG` call of `oa` under a hidden name has its key in the keys `Q` at the call, the
keys grow by the answer of each `.derive .prss` call, and each end has `post` with its keys. -/
def SafeThen (D : C.Coalition) {α : Type} (post : α → (HashOutput → Prop) → Prop)
    (oa : OracleComp (PartySpec C E RealSpec) α) : (HashOutput → Prop) → Prop :=
  OracleComp.construct (C := fun _ => (HashOutput → Prop) → Prop) post
    (fun t _ ih Q => ¬ PartyBad D (fun _ k => Q k) t ∧ ∀ u, ih u (partyAdd t u Q)) oa

variable (D : C.Coalition)

theorem safeThen_pure {α : Type} (post : α → (HashOutput → Prop) → Prop) (a : α) (Q : HashOutput → Prop) :
    SafeThen (E := E) D post (pure a) Q ↔ post a Q := Iff.rfl

theorem safeThen_query_bind {α : Type} (post : α → (HashOutput → Prop) → Prop) (t : (PartySpec C E RealSpec).Domain)
    (k : (PartySpec C E RealSpec).Range t → OracleComp (PartySpec C E RealSpec) α) (Q : HashOutput → Prop) :
    SafeThen D post (liftM (OracleSpec.query t) >>= k) Q ↔
      ¬ PartyBad D (fun _ k => Q k) t ∧ ∀ u, SafeThen D post (k u) (partyAdd t u Q) := Iff.rfl

theorem safeThen_bind {α β : Type} (post : β → (HashOutput → Prop) → Prop)
    (oa : OracleComp (PartySpec C E RealSpec) α) (f : α → OracleComp (PartySpec C E RealSpec) β) :
    ∀ Q, SafeThen D post (oa >>= f) Q ↔ SafeThen D (fun a Q' => SafeThen D post (f a) Q') oa Q := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro Q; rw [pure_bind]; exact Iff.rfl
  | query_bind t k ih =>
    intro Q
    rw [bind_assoc, safeThen_query_bind, safeThen_query_bind]
    exact and_congr_right fun _ => forall_congr' fun u => ih u _

theorem partyBad_anti {A A' : KeyName C → HashOutput → Prop} (hA : ∀ N k, A N k → A' N k)
    (t : (PartySpec C E RealSpec).Domain) (h : ¬ PartyBad D A t) : ¬ PartyBad D A' t := by
  rcases t with ((_ | _ | x) | _) | _
  · exact fun h' => h'
  · exact fun h' => h'
  · exact fun h' => h ⟨h'.1, fun hq => h'.2 (hA _ _ hq)⟩
  · exact fun h' => h'
  · exact fun h' => h'

theorem partyAdd_mono {Q Q' : HashOutput → Prop} (hQ : ∀ k, Q k → Q' k) (t : (PartySpec C E RealSpec).Domain)
    (u : (PartySpec C E RealSpec).Range t) : ∀ k, partyAdd t u Q k → partyAdd t u Q' k := by
  rcases t with ((_ | q | x) | _) | _
  · exact hQ
  · cases q with
    | derive phase kind parts =>
      cases phase
      · exact hQ
      · exact fun k hk => hk.imp (hQ k) id
    | _ => exact hQ
  · exact hQ
  · exact hQ
  · exact hQ

theorem le_partyAdd (t : (PartySpec C E RealSpec).Domain) (u : (PartySpec C E RealSpec).Range t)
    (Q : HashOutput → Prop) : ∀ k, Q k → partyAdd t u Q k := by
  rcases t with ((_ | q | x) | _) | _
  · exact fun _ h => h
  · cases q with
    | derive phase kind parts =>
      cases phase
      · exact fun _ h => h
      · exact fun _ h => Or.inl h
    | _ => exact fun _ h => h
  · exact fun _ h => h
  · exact fun _ h => h
  · exact fun _ h => h

theorem SafeThen.mono {α : Type} {post post' : α → (HashOutput → Prop) → Prop}
    (hpost : ∀ a P P', (∀ k, P k → P' k) → post a P → post' a P') (oa : OracleComp (PartySpec C E RealSpec) α) :
    ∀ {Q Q' : HashOutput → Prop}, (∀ k, Q k → Q' k) → SafeThen D post oa Q → SafeThen D post' oa Q' := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun hQ h => hpost a _ _ hQ h
  | query_bind t k ih =>
    intro Q Q' hQ h
    rw [safeThen_query_bind] at h ⊢
    exact ⟨partyBad_anti D (fun _ k => hQ k) t h.1, fun u => ih u (partyAdd_mono hQ t u) (h.2 u)⟩

theorem SafeThen.imp {α : Type} {post post' : α → (HashOutput → Prop) → Prop}
    (hpost : ∀ a P, post a P → post' a P) (oa : OracleComp (PartySpec C E RealSpec) α) :
    ∀ {Q : HashOutput → Prop}, SafeThen D post oa Q → SafeThen D post' oa Q := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun h => hpost a _ h
  | query_bind t k ih =>
    intro Q h
    rw [safeThen_query_bind] at h ⊢
    exact ⟨h.1, fun u => ih u (h.2 u)⟩

/-- A program with no bad draw for the keys `S` has `SafeThen` from each larger set of keys, for
each end condition that holds above those keys. -/
theorem safeThen_of_noBad {α : Type} (S : KeyName C → HashOutput → Prop) (oa : OracleComp (PartySpec C E RealSpec) α)
    (h : IsQueryBoundP oa (PartyBad D S) 0) :
    ∀ (post : α → (HashOutput → Prop) → Prop) (Q : HashOutput → Prop), (∀ N k, S N k → Q k) →
      (∀ a Q', (∀ k, Q k → Q' k) → post a Q') → SafeThen D post oa Q := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun post Q _ hpost => hpost a Q fun _ h => h
  | query_bind t k ih =>
    intro post Q hS hpost
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ PartyBad D S t := h.1.resolve_right (lt_irrefl 0)
    rw [safeThen_query_bind]
    exact ⟨partyBad_anti D hS t ht, fun u => ih u (by simpa only [ht, ite_false] using h.2 u) post _
      (fun N k hk => le_partyAdd t u Q k (hS N k hk)) fun a Q' hQ' => hpost a Q' fun k hk => hQ' k
        (le_partyAdd t u Q k hk)⟩

/-! ## The stream world -/

section World

variable (prims : Primitives)

/-- Each key of `Q` has a derive cell of a PRSS setup in the hash cache `cache`. -/
def KeysDerived (cache : HashCache C) (Q : HashOutput → Prop) : Prop :=
  ∀ key, Q key → ∃ kind parts, cache (.derive .prss kind parts) = some key

theorem KeysDerived.mono {cache cache' : HashCache C} {Q : HashOutput → Prop} (h : KeysDerived cache Q)
    (hle : cache ≤ cache') : KeysDerived cache' Q := fun key hk => by
  obtain ⟨kind, parts, h⟩ := h key hk
  exact ⟨kind, parts, hle h⟩

/-- A free derive call of a PRSS setup caches its answer. -/
theorem derive_cached (kind : KeyKind) (parts : List HashOutput) (w : StreamState C) :
    ∀ y ∈ support ((streamWorld prims D (.inr (.inr (.inl (.derive .prss kind parts))))).run w),
      y.2.1 (.derive .prss kind parts) = some y.1 := by
  intro y hy
  obtain ⟨r, hr, rfl⟩ := FirstCounts.onHash_support hy
  change r ∈ support ((hashAnswer prims (.derive .prss kind parts)).run w.1) at hr
  rw [hashAnswer_of_not_isFixed prims (by rintro ⟨_, h, _⟩; cases h)] at hr
  exact (Ready.randomOracle_support' _ _ r hr).2

/-- A free `PRG` call under a hidden name with a key with a derive cell keeps the provenance. -/
theorem streamWorld_prg_keeps (x : PrgInput C) (w : StreamState C) (hw : HiddenProvenance D w)
    (hkey : Hidden D x.1 → ∃ kind parts, w.1 (.derive .prss kind parts) = some x.2.1) :
    ∀ z ∈ support ((streamWorld prims D (.inr (.inr (.inr x)))).run w), HiddenProvenance D z.2 := by
  intro z hz
  have hle := Ready.streamWorld_le prims D _ w z hz
  change z ∈ support ((if Hidden D x.1 then _ else _ : StateT (StreamState C) ProbComp _).run w) at hz
  split_ifs at hz with hx
  · simp only [StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    intro name key ρ idx position hname hcell
    rcases FirstCounts.randomOracle_cells _ _ r hr _ hcell with h | h
    · exact hw name key ρ idx position hname h
    · have hk : key = x.2.1 := congrArg (fun y => y.1.2) h
      subst hk
      exact hkey hx
  · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hz
    exact hiddenProvenance_of_le hw hle.1 rfl

/-- A local call of an honest operator that is no bad draw keeps the provenance, and the keys with
the answer of a derive call keep their derive cells. -/
theorem streamWorld_local_safe (q : (LocalSpec C).Domain) (Q : HashOutput → Prop) (w : StreamState C)
    (hw : HiddenProvenance D w) (hQ : KeysDerived w.1 Q) (hq : ¬ BadDraw D (fun _ k => Q k) q) :
    ∀ y ∈ support ((streamWorld prims D (.inr q)).run w),
      HiddenProvenance D y.2 ∧ KeysDerived y.2.1 (addDerived q y.1 Q) := by
  intro y hy
  have hle := (Ready.streamWorld_le prims D _ w y hy).1
  rcases q with n | q | x
  · exact ⟨streamWorld_keepsProvenance prims D _ (fun _ h => by cases h) w hw y hy, hQ.mono hle⟩
  · refine ⟨streamWorld_keepsProvenance prims D _ (fun _ h => by cases h) w hw y hy, ?_⟩
    cases q with
    | derive phase kind parts =>
      cases phase
      · exact hQ.mono hle
      · rintro key (hk | rfl)
        · exact hQ.mono hle key hk
        · exact ⟨kind, parts, derive_cached D prims kind parts w y hy⟩
    | _ => exact hQ.mono hle
  · refine ⟨streamWorld_prg_keeps D prims x w hw (fun hx => hQ _ ?_) y hy, hQ.mono hle⟩
    by_contra hk
    exact hq ⟨hx, hk⟩

end World

/-! ## The network -/

section Network

variable (prims : Primitives)

/-- The continuation of a stopped program draws only under the keys `Q`. -/
def StepSafe (Q : HashOutput → Prop) {α : Type} : Step C E RealSpec α → Prop
  | .wait _ resume => ∀ inbox, SafeThen D (fun _ _ => True) (resume inbox) Q
  | _ => True

/-- The local steps of an honest operator keep the provenance and stop at a step that draws only
under keys with a derive cell. -/
theorem advance_safe {α : Type} (oa : OracleComp (PartySpec C E RealSpec) (Option α)) :
    ∀ (Q : HashOutput → Prop) (w : StreamState C), SafeThen D (fun _ _ => True) oa Q → HiddenProvenance D w →
      KeysDerived w.1 Q → ∀ z ∈ support ((simulateQ (streamWorld prims D) (free (advance oa))).run w),
        HiddenProvenance D z.2 ∧ ∃ Q', KeysDerived z.2.1 Q' ∧ StepSafe D Q' z.1 := by
  induction oa using OracleComp.inductionOn with
  | pure out =>
    intro Q w _ hw hQ z hz
    simp only [advance_pure, free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hw, Q, hQ, trivial⟩
  | query_bind t k ih =>
    intro Q w h hw hQ z hz
    rw [safeThen_query_bind] at h
    rcases t with (q | outbox) | input
    · change z ∈ support ((simulateQ (streamWorld prims D) (free (OracleComp.lift
        (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advance (k r)))).run w) at hz
      simp only [free, simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      rw [simulateQ_HasQuery_query] at hy
      obtain ⟨hw', hQ'⟩ := streamWorld_local_safe D prims q Q w hw hQ h.1 y hy
      exact ih y.1 _ y.2 (h.2 y.1) hw' hQ' z hz
    · change z ∈ support ((simulateQ (streamWorld prims D) (free (pure (Step.wait outbox k)))).run w) at hz
      simp only [free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hw, Q, hQ, fun inbox => h.2 inbox⟩
    · exact input.elim

/-- A sequence of computations from a world above `w₀` with the invariant `I` keeps it, and each
value has a property that a larger world keeps. -/
theorem sequenceFin_keeps {β : Type} (I : StreamState C → Prop) (w₀ : StreamState C) :
    ∀ {n : ℕ} (P : Fin n → β → StreamState C → Prop) (f : Fin n → OracleComp (WorldSpec C) β),
      (∀ i b w w', P i b w → w ≤ w' → P i b w') →
      (∀ i w y, w₀ ≤ w → I w → y ∈ support ((simulateQ (streamWorld prims D) (f i)).run w) →
        I y.2 ∧ P i y.1 y.2) →
      ∀ w z, w₀ ≤ w → I w →
        z ∈ support ((simulateQ (streamWorld prims D) (OverPermutation.sequenceFin f)).run w) →
        I z.2 ∧ ∀ i, P i (z.1 i) z.2
  | 0, _, _, _, _, w, z, _, hw, hz => by
    simp only [OverPermutation.sequenceFin, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hw, fun i => i.elim0⟩
  | n + 1, P, f, hmono, hf, w, z, h₀, hw, hz => by
    simp only [OverPermutation.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, v, hv, rfl⟩ := hz
    obtain ⟨hy₁, hy₂⟩ := hf 0 w y h₀ hw hy
    obtain ⟨hv₁, hv₂⟩ := sequenceFin_keeps I w₀ (fun i => P i.succ) (fun i => f i.succ) (fun i => hmono i.succ)
      (fun i => hf i.succ) y.2 v (h₀.trans (Ready.simulateQ_le prims D _ w y hy)) hy₁ hv
    refine ⟨hv₁, fun i => ?_⟩
    cases i using Fin.cases with
    | zero => exact hmono 0 _ _ _ hy₂ (Ready.simulateQ_le prims D _ y.2 v hv)
    | succ i => exact hv₂ i

/-- The world has the provenance, and each honest step draws only under keys with a derive cell. -/
def StepsOk {α : Type} (w : StreamState C) (steps : C.Party → Step C E RealSpec α) : Prop :=
  HiddenProvenance D w ∧ ∀ j, j ∉ D.1 → ∃ Q, KeysDerived w.1 Q ∧ StepSafe D Q (steps j)

/-- One round keeps `StepsOk`. -/
theorem stepRound_safe {Ia α : Type} (A : Adversary C E Ia PEmpty PEmpty) (st : A.State)
    (steps : C.Party → Step C E RealSpec α) (w : StreamState C) (hw : StepsOk D w steps)
    (y : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E))) × StreamState C)
    (hy : y ∈ support ((simulateQ (streamWorld prims D) (stepRound worldRoles D A noFunctionality st steps)).run w)) :
    StepsOk D y.2 y.1.2.1 := by
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
  obtain ⟨a, ha, v, hv, rfl⟩ := hy
  have hle : w ≤ a.2 := Ready.simulateQ_le prims D _ w a ha
  have ha' : HiddenProvenance D a.2 := provenanceCounted prims D _ w hw.1 a ha
  refine sequenceFin_keeps D prims (HiddenProvenance D) a.2 (fun j next w' => j ∉ D.1 → ∃ Q, KeysDerived w'.1 Q ∧ StepSafe D Q next) _
    (fun j b w₁ w₂ h hle₁ hj => (h hj).imp fun Q hQ => ⟨hQ.1.mono hle₁.1, hQ.2⟩) (fun j w' u hw₀ hw' hu => ?_)
    a.2 v le_rfl ha' hv
  rcases hsj : steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · simp only [hsj, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    subst hu
    exact ⟨hw', fun _ => ⟨fun _ => False, fun _ h => h.elim, trivial⟩⟩
  · by_cases hj : j ∈ D.1
    · simp only [hsj, hj, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
      subst hu
      exact ⟨hw', fun _ => ⟨fun _ => False, fun _ h => h.elim, trivial⟩⟩
    · simp only [hsj, hj, ↓reduceIte] at hu
      obtain ⟨Q, hQ, hsafe⟩ := hw.2 j hj
      rw [hsj] at hsafe
      obtain ⟨hp, Q', hQ', hs⟩ := advance_safe D prims _ Q w' (hsafe _) hw'
        (hQ.mono ((hle.trans hw₀).1)) u hu
      exact ⟨hp, fun _ => ⟨Q', hQ', hs⟩⟩
  · exact input.elim

/-- The rounds keep the provenance. -/
theorem executeRounds_safe {Ia α : Type} (A : Adversary C E Ia PEmpty PEmpty) :
    ∀ (fuel : ℕ) (st : A.State) (steps : C.Party → Step C E RealSpec α) (w : StreamState C), StepsOk D w steps →
      ∀ z ∈ support ((simulateQ (streamWorld prims D) (executeRounds worldRoles D A noFunctionality fuel st steps)).run w),
        HiddenProvenance D z.2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro st steps w hw z hz
    simp only [executeRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw.1
  | succ fuel ih =>
    intro st steps w hw z hz
    unfold executeRounds at hz
    split_ifs at hz
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hw.1
    · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      exact ih y.1.1 y.1.2.1 y.2 (stepRound_safe D prims A st steps w hw y hy) z hz

/-- A phase on the network keeps the provenance of the hidden keys when each honest program draws
only under keys that its own derive calls gave. -/
theorem executePhase_keepsProvenance {Ia α : Type} (A : Adversary C E Ia PEmpty PEmpty) (fuel : ℕ)
    (st : A.State) (program : C.Party → PartyM C E RealSpec α)
    (hp : ∀ i, i ∉ D.1 → SafeThen D (fun _ _ => True) (program i).run fun _ => False) :
    KeepsProvenance prims D (executePhase worldRoles D A noFunctionality fuel st program) := by
  intro w hw z hz
  unfold executePhase at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  unfold startSteps at hy
  have hstart := sequenceFin_keeps D prims (HiddenProvenance D) w
    (fun j v w' => j ∉ D.1 → ∃ Q, KeysDerived w'.1 Q ∧ StepSafe D Q v) _
    (fun j b w₁ w₂ h hle₁ hj => (h hj).imp fun Q hQ => ⟨hQ.1.mono hle₁.1, hQ.2⟩) (fun j w' u _ hw' hu => ?_)
    w y le_rfl hw hy
  · exact executeRounds_safe D prims A fuel st y.1 y.2 hstart z hz
  by_cases hj : j ∈ D.1
  · simp only [hj, ↓reduceIte, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    subst hu
    exact ⟨hw', fun _ => ⟨fun _ => False, fun _ h => h.elim, trivial⟩⟩
  · simp only [hj, ↓reduceIte] at hu
    obtain ⟨hq, Q', hQ', hs⟩ := advance_safe D prims _ _ w' (hp j hj) hw' (fun _ h => h.elim) u hu
    exact ⟨hq, fun _ => ⟨Q', hQ', hs⟩⟩

end Network

/-! ## The calculus on operator programs -/

section Programs

theorem safeThen_grow {α : Type} (post : α → (HashOutput → Prop) → Prop)
    (oa : OracleComp (PartySpec C E RealSpec) α) :
    ∀ Q, SafeThen D post oa Q → SafeThen D (fun a Q' => (∀ k, Q k → Q' k) ∧ post a Q') oa Q := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun Q h => ⟨fun _ hk => hk, h⟩
  | query_bind t k ih =>
    intro Q h
    rw [safeThen_query_bind] at h ⊢
    exact ⟨h.1, fun u => SafeThen.imp D (fun a P h' => ⟨fun k hk => h'.1 k (le_partyAdd t u Q k hk), h'.2⟩) _
      (ih u _ (h.2 u))⟩

/-- `SafeThen` of an operator program, with the end condition on its value. An abort ends with no
condition. -/
def PSafe {α : Type} (post : α → (HashOutput → Prop) → Prop) (p : PartyM C E RealSpec α)
    (Q : HashOutput → Prop) : Prop :=
  SafeThen D (fun o Q' => ∀ a, o = some a → post a Q') p.run Q

theorem PSafe.mono {α : Type} {post post' : α → (HashOutput → Prop) → Prop}
    (hpost : ∀ a P P', (∀ k, P k → P' k) → post a P → post' a P') (p : PartyM C E RealSpec α)
    {Q Q' : HashOutput → Prop} (hQ : ∀ k, Q k → Q' k) (h : PSafe D post p Q) : PSafe D post' p Q' :=
  SafeThen.mono D (fun _ P P' hP h' a ho => hpost a P P' hP (h' a ho)) _ hQ h

theorem PSafe.grow {α : Type} {post : α → (HashOutput → Prop) → Prop} {p : PartyM C E RealSpec α}
    {Q : HashOutput → Prop} (h : PSafe D post p Q) : PSafe D (fun a Q' => (∀ k, Q k → Q' k) ∧ post a Q') p Q :=
  SafeThen.imp D (fun _ _ h' a ho => ⟨h'.1, h'.2 a ho⟩) _ (safeThen_grow D _ _ Q h)

theorem psafe_pure {α : Type} (post : α → (HashOutput → Prop) → Prop) (a : α) (Q : HashOutput → Prop) :
    PSafe D post (pure a : PartyM C E RealSpec α) Q ↔ post a Q := by
  unfold PSafe
  exact ⟨fun h => h a rfl, fun h b hb => by cases hb; exact h⟩

theorem psafe_failure {α : Type} (post : α → (HashOutput → Prop) → Prop) (Q : HashOutput → Prop) :
    PSafe D post (failure : PartyM C E RealSpec α) Q :=
  fun _ h => by cases h

theorem psafe_bind {α β : Type} (post : β → (HashOutput → Prop) → Prop) (p : PartyM C E RealSpec α)
    (f : α → PartyM C E RealSpec β) (Q : HashOutput → Prop) (h : PSafe D (fun a Q' => PSafe D post (f a) Q') p Q) :
    PSafe D post (p >>= f) Q := by
  unfold PSafe at h ⊢
  rw [OptionT.run_bind]
  unfold Option.elimM
  rw [safeThen_bind]
  refine SafeThen.imp D (fun o P h' => ?_) _ h
  rcases o with _ | a
  · exact fun _ hb => by cases hb
  · exact h' a rfl

end Programs

/-! ## Programs with no bad draw -/

section NoBad

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map noCall_mapM noCall_query)
open DigestBudgets (ClassBound StateBound PartyIn RoIn)

/-- A call of `H` or `PRG` that is a bad draw for the keys `S`. -/
def RoBad (S : KeyName C → HashOutput → Prop) : (RoSpec C).Domain → Prop := fun t => BadDraw D S (.inr t)

/-- An operator program with no bad draw for the keys `S`. -/
def NoBad {α : Type} (S : KeyName C → HashOutput → Prop) (p : PartyM C E RealSpec α) : Prop :=
  IsQueryBoundP p.run (PartyBad D S) 0

/-- A program on a state with no bad draw for the keys `S` from each state. -/
def NoBadS {σ α : Type} (S : KeyName C → HashOutput → Prop) (p : StateT σ (PartyM C E RealSpec) α) : Prop :=
  ∀ s, NoBad D S (p.run s)

variable {D}

theorem psafe_of_noBad {α : Type} {S : KeyName C → HashOutput → Prop} {p : PartyM C E RealSpec α} (h : NoBad D S p)
    (post : α → (HashOutput → Prop) → Prop) (Q : HashOutput → Prop) (hS : ∀ N k, S N k → Q k)
    (hpost : ∀ a Q', (∀ k, Q k → Q' k) → post a Q') : PSafe D post p Q :=
  safeThen_of_noBad D S _ h _ Q hS fun _ Q' hQ' a _ => hpost a Q' hQ'

theorem NoBad.of_class {α : Type} {S : KeyName C → HashOutput → Prop} {p : PartyM C E RealSpec α}
    (h : ClassBound (E := E) .stream p 0) : NoBad D S p :=
  IsQueryBoundP.of_imp (fun t ht => by
    rcases t with ((_ | _ | x) | _) | _
    · exact ht.elim
    · exact ht.elim
    · rfl
    · exact ht.elim
    · exact ht.elim) h

theorem NoBadS.of_state {σ α : Type} {S : KeyName C → HashOutput → Prop} {p : StateT σ (PartyM C E RealSpec) α}
    (h : StateBound (E := E) .stream p 0) : NoBadS D S p := fun s => NoBad.of_class (h s)

theorem NoBad.bind {α β : Type} {S : KeyName C → HashOutput → Prop} {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β}
    (h : NoBad D S p) (hf : ∀ a, NoBad D S (f a)) : NoBad D S (p >>= f) := by
  unfold NoBad
  simp only [OptionT.run_bind]
  apply isQueryBoundP_bind (n := 0) (m := 0) h
  intro a _
  cases a with
  | none => exact isQueryBoundP_pure _ _ _
  | some a => exact hf a

theorem NoBadS.bind {σ α β : Type} {S : KeyName C → HashOutput → Prop} {p : StateT σ (PartyM C E RealSpec) α}
    {f : α → StateT σ (PartyM C E RealSpec) β} (h : NoBadS D S p) (hf : ∀ a, NoBadS D S (f a)) :
    NoBadS D S (p >>= f) := fun s =>
  NoBad.bind (h s) fun a => hf a.1 a.2

theorem NoBadS.lift {σ α : Type} {S : KeyName C → HashOutput → Prop} {p : PartyM C E RealSpec α} (h : NoBad D S p) :
    NoBadS D S (StateT.lift p : StateT σ (PartyM C E RealSpec) α) := fun s => by
  change NoBad D S (p >>= fun a => Pure.pure (a, s))
  exact NoBad.bind h fun a => isQueryBoundP_pure _ _ _

theorem NoBadS.pure {σ α : Type} {S : KeyName C → HashOutput → Prop} (a : α) :
    NoBadS D S (Pure.pure a : StateT σ (PartyM C E RealSpec) α) := fun _ => isQueryBoundP_pure _ _ _

theorem NoBadS.mapM {σ α β : Type} {S : KeyName C → HashOutput → Prop} (f : α → StateT σ (PartyM C E RealSpec) β)
    (hf : ∀ a, NoBadS D S (f a)) : ∀ xs : List α, NoBadS D S (xs.mapM f)
  | [] => by simpa using NoBadS.pure (D := D) (S := S) (σ := σ) ([] : List β)
  | a :: xs => by
    rw [List.mapM_cons]
    exact (hf a).bind fun b => (NoBadS.mapM f hf xs).bind fun bs => NoBadS.pure _

theorem NoBadS.foldlM {σ α γ : Type} {S : KeyName C → HashOutput → Prop} (f : α → γ → StateT σ (PartyM C E RealSpec) α)
    (hf : ∀ a g, NoBadS D S (f a g)) : ∀ (xs : List γ) (a : α), NoBadS D S (xs.foldlM f a)
  | [], a => by simpa using NoBadS.pure (D := D) (S := S) (σ := σ) a
  | g :: xs, a => by
    rw [List.foldlM_cons]
    exact (hf a g).bind fun a' => NoBadS.foldlM f hf xs a'

theorem liftComp_ro_noBad {S : KeyName C → HashOutput → Prop} {α : Type} (oa : OracleComp (RoSpec C) α) :
    IsQueryBoundP oa (RoBad D S) 0 → IsQueryBoundP (liftComp oa (LocalSpec C)) (BadDraw D S) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro _; trivial
  | query_bind t k ih =>
    intro h
    rw [isQueryBoundP_query_bind_iff] at h
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inr t)) : OracleComp (LocalSpec C) _) >>= fun u =>
          liftComp (k u) (LocalSpec C) := by
      rw [liftComp_bind]
      rcases t with _ | _ <;> rfl
    rw [e]
    have ht : ¬ RoBad D S t := h.1.resolve_right (lt_irrefl 0)
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl ht, fun u => by
      have hu := ih u (by simpa only [ht, ite_false] using h.2 u)
      simpa only [show ¬ BadDraw D S (.inr t) from ht, ite_false] using hu⟩

theorem liftComp_party_noBad {S : KeyName C → HashOutput → Prop} {α : Type} (oa : OracleComp (LocalSpec C) α) :
    IsQueryBoundP oa (BadDraw D S) 0 →
      IsQueryBoundP (liftComp oa (PartySpec C E RealSpec)) (PartyBad D S) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro _; trivial
  | query_bind t k ih =>
    intro h
    rw [isQueryBoundP_query_bind_iff] at h
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (PartySpec C E RealSpec) =
        (liftM ((PartySpec C E RealSpec).query (.inl (.inl t))) : OracleComp (PartySpec C E RealSpec) _) >>=
          fun u => liftComp (k u) (PartySpec C E RealSpec) := by
      rw [liftComp_bind]
      rcases t with _ | _ | _ <;> rfl
    rw [e]
    have ht : ¬ BadDraw D S t := h.1.resolve_right (lt_irrefl 0)
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl ht, fun u => by
      have hu := ih u (by simpa only [ht, ite_false] using h.2 u)
      simpa only [show ¬ PartyBad (E := E) D S (.inl (.inl t)) from ht, ite_false] using hu⟩

theorem NoBad.oracleStep {α : Type} {S : KeyName C → HashOutput → Prop} {oa : OracleComp (RoSpec C) α}
    (h : NoCall (RoBad D S) oa) : NoBad D S (ThresholdLeanXmss.oracleStep oa : PartyM C E RealSpec α) := by
  unfold NoBad ThresholdLeanXmss.oracleStep ThresholdLeanXmss.localStep
  change IsQueryBoundP (liftComp (liftComp oa (LocalSpec C)) (PartySpec C E RealSpec) >>= fun a => Pure.pure (some a)) _ _
  exact isQueryBoundP_bind (n := 0) (m := 0)
    (liftComp_party_noBad _ (liftComp_ro_noBad _ ((noCall_iff _ _).1 h))) fun _ _ => isQueryBoundP_pure _ _ _

end NoBad

/-! ## The draws of one ceremony after its setup -/

section Body

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map noCall_mapM noCall_query)
open DigestBudgets (ClassBound StateBound PartyIn RoIn)

/-- The keys of operator `i` under the PRSS keys `prss`, one for each held term and each pair. -/
def KeysOf (i : C.Party) (prss : PrssKeys C) (key : HashOutput) : Prop := ∃ name, NameKey i prss name key

variable {D}

theorem noCall_roBad_of_stream {S : KeyName C → HashOutput → Prop} {α : Type} {oa : OracleComp (RoSpec C) α}
    (h : NoCall (RoIn .stream) oa) : NoCall (RoBad D S) oa := by
  rw [noCall_iff] at h ⊢
  exact IsQueryBoundP.of_imp (fun t ht => by
    rcases t with _ | x
    · exact ht.elim
    · rfl) h

theorem noCall_prgBits {S : KeyName C → HashOutput → Prop} (name : KeyName C) (key : HashOutput) (hkey : Hidden D name → S name key)
    (ρ idx count : ℕ) : NoCall (RoBad D S) (prgBits name key ρ idx count) := by
  unfold prgBits
  exact noCall_bind _ (noCall_mapM _ _ _ fun _ => noCall_query _ _ fun h => h.2 (hkey h.1)) fun _ =>
    noCall_pure _ _

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C)

theorem noCall_elementDraw {S : KeyName C → HashOutput → Prop} (name : KeyName C) (key : HashOutput)
    (hkey : Hidden D name → S name key) (ρ idx count : ℕ) :
    NoCall (RoBad D S) ((elementCodec K).draw name key ρ idx count) :=
  noCall_bind _ (noCall_prgBits name key hkey _ _ _) fun _ => noCall_pure _ _

omit [Field E] [Algebra Bit E] in
theorem prssRandomness_noBad {R : Type} [Zero R] (codec : Codec C E R)
    (hdraw : ∀ name key, (Hidden D name → NameKey ctx.self ctx.prss name key) → ∀ ρ idx count,
      NoCall (RoBad D (NameKey ctx.self ctx.prss)) (codec.draw name key ρ idx count)) (idx count : ℕ) :
    NoBadS D (NameKey ctx.self ctx.prss) (prssRandomness ctx codec idx count : RunM C E RealSpec _) := by
  unfold prssRandomness freshLabel
  refine NoBadS.bind (NoBadS.of_state (DigestBudgets.StateBound.modifyGet _)) fun ρ => ?_
  refine NoBadS.bind (NoBadS.lift (NoBad.oracleStep (noCall_mapM _ _ _ fun T => ?_))) fun _ => ?_
  · split_ifs with hT
    · exact hdraw _ _ (fun _ => Or.inl ⟨T, hT, rfl, rfl⟩) _ _ _
    · exact noCall_pure _ _
  refine NoBadS.bind (NoBadS.lift (NoBad.oracleStep (noCall_mapM _ _ _ fun j => ?_))) fun _ => NoBadS.pure _
  split
  · exact noCall_pure _ _
  · rename_i h
    exact hdraw _ _ (fun _ => Or.inr ⟨j, h, rfl, rfl⟩) _ _ _

theorem prssElements_noBad (idx count : ℕ) :
    NoBadS D (NameKey ctx.self ctx.prss) (prssRandomness ctx (elementCodec K) idx count : RunM C E RealSpec _) :=
  prssRandomness_noBad ctx _ (fun name key hkey _ _ _ => noCall_elementDraw K name key hkey _ _ _) idx count

omit [Field E] [Algebra Bit E] in
theorem prssBits_noBad (idx count : ℕ) :
    NoBadS D (NameKey ctx.self ctx.prss) (prssRandomness ctx bitCodec idx count : RunM C E RealSpec _) :=
  prssRandomness_noBad ctx _ (fun name key hkey _ _ _ => noCall_prgBits name key hkey _ _ _) idx count

theorem coin_noBad (count : ℕ) :
    NoBadS D (NameKey ctx.self ctx.prss) ((realCheckBuildingBlocks K ctx).coin count : RunM C E RealSpec _) := by
  unfold realCheckBuildingBlocks coinWith
  exact NoBadS.bind (prssElements_noBad K ctx _ _) fun _ =>
    NoBadS.bind (NoBadS.lift (NoBad.of_class (DigestBudgets.openSh_bound K ctx _ _))) fun _ => NoBadS.pure _

theorem extendMult_noBad (products : List (Product C E)) :
    NoBadS D (NameKey ctx.self ctx.prss) ((realCheckBuildingBlocks K ctx).extendMult products : RunM C E RealSpec _) := by
  unfold realCheckBuildingBlocks
  exact NoBadS.bind (prssElements_noBad K ctx _ _) fun _ =>
    NoBadS.of_state (DigestBudgets.reshare_bound K ctx _ _ _ _)

theorem coinKey_noBad :
    NoBadS D (NameKey ctx.self ctx.prss) (coinKey K (realCheckBuildingBlocks K ctx) : RunM C E RealSpec _) := by
  unfold coinKey
  exact NoBadS.bind (NoBadS.of_state DigestBudgets.StateBound.get) fun _ =>
    NoBadS.bind (coin_noBad K ctx 2) fun _ => NoBadS.lift (NoBad.oracleStep (noCall_query _ _ fun h => h))

theorem challenge_noBad :
    NoBadS D (NameKey ctx.self ctx.prss) (challenge K (realCheckBuildingBlocks K ctx) : RunM C E RealSpec _) := by
  unfold challenge
  refine NoBadS.bind (coinKey_noBad K ctx) fun key => ?_
  refine NoBadS.bind (NoBadS.lift (NoBad.oracleStep (noCall_roBad_of_stream
    (DigestBudgets.noCall_findChallenge K (by decide) key _ _)))) fun r => ?_
  split
  · exact NoBadS.pure _
  · exact NoBadS.lift (NoBad.of_class DigestBudgets.ClassBound.failure)

theorem check_noBad (tuples : List (Tuple C)) :
    NoBadS D (NameKey ctx.self ctx.prss) (check K ctx (realCheckBuildingBlocks K ctx) tuples : RunM C E RealSpec Unit) := by
  unfold check
  dsimp only
  split_ifs with hz
  · exact NoBadS.pure _
  refine NoBadS.bind (coinKey_noBad K ctx) fun key => ?_
  refine NoBadS.bind (NoBadS.of_state (DigestBudgets.expand_bound (c := .stream) K (by decide) key _)) fun τ => ?_
  refine NoBadS.bind (NoBadS.lift (NoBad.of_class (DigestBudgets.ClassBound.require _))) fun _ => ?_
  refine NoBadS.bind (NoBadS.foldlM _ (fun v j => ?_) _ _) fun v => ?_
  · rcases v with ⟨xs, ys, d⟩
    exact NoBadS.bind (extendMult_noBad K ctx _) fun _ =>
      NoBadS.bind (challenge_noBad K ctx) fun _ => NoBadS.pure _
  rcases v with ⟨xs, ys, d⟩
  refine NoBadS.bind (NoBadS.foldlM _ (fun v j => ?_) _ _) fun v => ?_
  · rcases v with ⟨A, B, d⟩
    exact NoBadS.bind (extendMult_noBad K ctx _) fun _ =>
      NoBadS.bind (challenge_noBad K ctx) fun _ => NoBadS.pure _
  rcases v with ⟨A, B, d⟩
  refine NoBadS.bind (prssElements_noBad K ctx _ _) fun w => ?_
  refine NoBadS.bind (extendMult_noBad K ctx _) fun q => ?_
  refine NoBadS.bind (prssBits_noBad ctx _ _) fun salts => ?_
  refine NoBadS.bind (NoBadS.of_state ((DigestBudgets.compareDigests_bound ctx _).mono
    (by simp [DigestBudgets.digestCost]))) fun _ => ?_
  exact NoBadS.bind (challenge_noBad K ctx) fun _ =>
    NoBadS.bind (NoBadS.lift (NoBad.of_class (DigestBudgets.openSh_bound K ctx _ _))) fun _ =>
      NoBadS.lift (NoBad.of_class (DigestBudgets.ClassBound.require _))

theorem mult_noBad (mode : ReshareMode) (x y : Shares C Bit) (count : ℕ) :
    NoBadS D (NameKey ctx.self ctx.prss) ((realRunBuildingBlocks K ctx mode).mult x y count : RunM C E RealSpec _) := by
  unfold realRunBuildingBlocks reshareWith
  refine NoBadS.bind (prssBits_noBad ctx _ _) fun r => ?_
  cases mode
  · exact NoBadS.of_state (DigestBudgets.reshare_bound K ctx _ _ _ _)
  · exact NoBadS.of_state (DigestBudgets.reshareCollector_bound K ctx _ _ _)

theorem runJobs_noBad (mode : ReshareMode) (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    NoBadS D (NameKey ctx.self ctx.prss) (runJobs K (realRunBuildingBlocks K ctx mode) jobs inputs : RunM C E RealSpec _) := by
  unfold runJobs
  refine NoBadS.bind (NoBadS.foldlM _ (fun v layer => ?_) _ _) fun v => ?_
  · rcases v with ⟨wires, tuples⟩
    exact NoBadS.bind (mult_noBad K ctx mode _ _ _) fun _ => NoBadS.pure _
  rcases v with ⟨wires, tuples⟩
  refine NoBadS.bind (?_ : NoBadS D _ ((realRunBuildingBlocks K ctx mode).rerand _ _)) fun v' => ?_
  · unfold realRunBuildingBlocks
    exact NoBadS.bind (prssBits_noBad ctx _ _) fun _ => NoBadS.of_state (DigestBudgets.reshare_bound K ctx _ _ _ _)
  refine NoBadS.bind (check_noBad K ctx _) fun _ => ?_
  exact NoBadS.bind (NoBadS.lift (NoBad.of_class ((DigestBudgets.openRep_bound K ctx _ _).mono
    (by simp [DigestBudgets.copyCost])))) fun _ => NoBadS.pure _

end Body

/-! ## The setup gives derived keys -/

section Setup

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map noCall_mapM noCall_query)
open DigestBudgets (ClassBound StateBound PartyIn RoIn)

variable {D}

theorem psafe_noBad_bind {α β : Type} {post : β → (HashOutput → Prop) → Prop} {p : PartyM C E RealSpec α}
    {f : α → PartyM C E RealSpec β} {Q : HashOutput → Prop} (h : NoBad D (fun _ _ => False) p)
    (hf : ∀ a Q', (∀ k, Q k → Q' k) → PSafe D post (f a) Q') : PSafe D post (p >>= f) Q :=
  psafe_bind D _ _ _ _ (psafe_of_noBad h _ Q (fun _ _ h => h.elim) hf)

theorem noBad_hashes {S : KeyName C → HashOutput → Prop} {γ : Type} (l : List γ) (q : γ → Query C) :
    NoBad D S (ThresholdLeanXmss.oracleStep (l.mapM fun a => hashQuery (q a)) : PartyM C E RealSpec _) :=
  NoBad.oracleStep (noCall_mapM _ _ _ fun _ => noCall_query _ _ fun h => h)

theorem psafe_derive (post : HashOutput → (HashOutput → Prop) → Prop) (kind : KeyKind) (parts : List HashOutput)
    (Q : HashOutput → Prop) (h : ∀ u, post u fun k => Q k ∨ k = u) :
    PSafe D post (ThresholdLeanXmss.oracleStep (hashQuery (.derive .prss kind parts)) : PartyM C E RealSpec _) Q := by
  unfold PSafe
  change SafeThen D _ (liftM (OracleSpec.query (spec := PartySpec C E RealSpec)
    (.inl (.inl (.inr (.inl (.derive .prss kind parts)))))) >>= fun u => pure (some u)) Q
  rw [safeThen_query_bind]
  exact ⟨fun h => h, fun u a ha => by cases ha; exact h u⟩

theorem psafe_mapM {γ β : Type} (g : γ → PartyM C E RealSpec β) (R : γ → β → (HashOutput → Prop) → Prop)
    (hR : ∀ a b P P', (∀ k, P k → P' k) → R a b P → R a b P')
    (hg : ∀ a Q, PSafe D (fun b Q' => R a b Q') (g a) Q) :
    ∀ (l : List γ) (Q : HashOutput → Prop),
      PSafe D (fun bs Q' => List.Forall₂ (fun a b => R a b Q') l bs) (l.mapM g) Q
  | [], Q => by
    rw [List.mapM_nil]
    exact (psafe_pure D _ _ _).2 List.Forall₂.nil
  | a :: l, Q => by
    rw [List.mapM_cons]
    refine psafe_bind D _ _ _ _ (PSafe.mono D (fun b P P' hP hb => ?_) _ (fun _ hk => hk) (hg a Q))
    refine psafe_bind D _ _ _ _ (PSafe.mono D (fun bs P₁ P₂ hP₁ hbs => ?_) _ (fun _ hk => hk)
      (psafe_mapM g R hR hg l P').grow)
    exact (psafe_pure D _ _ _).2 (List.Forall₂.cons (hR a b P P₂ (fun k hk => hP₁ k (hbs.1 k (hP k hk))) hb)
      (List.Forall₂.imp (fun x y h => hR x y P₁ P₂ hP₁ h) hbs.2))

theorem oracleStep_bind' {γ β : Type} (oa : OracleComp (RoSpec C) γ) (ob : γ → OracleComp (RoSpec C) β) :
    (ThresholdLeanXmss.oracleStep (oa >>= ob) : PartyM C E RealSpec β) =
      ThresholdLeanXmss.oracleStep oa >>= fun a => ThresholdLeanXmss.oracleStep (ob a) := by
  simp only [ThresholdLeanXmss.oracleStep, localStep, liftComp_bind]
  apply OptionT.ext
  simp [OptionT.run_bind, OptionT.run_lift]

theorem oracleStep_pure' {γ : Type} (a : γ) :
    (ThresholdLeanXmss.oracleStep (pure a : OracleComp (RoSpec C) γ) : PartyM C E RealSpec γ) = pure a := by
  simp [ThresholdLeanXmss.oracleStep, localStep]

theorem oracleStep_mapM {γ β : Type} (f : γ → OracleComp (RoSpec C) β) :
    ∀ l : List γ, (ThresholdLeanXmss.oracleStep (l.mapM f) : PartyM C E RealSpec _) =
      l.mapM fun a => ThresholdLeanXmss.oracleStep (f a)
  | [] => by simp only [List.mapM_nil, oracleStep_pure']
  | a :: l => by
    simp only [List.mapM_cons, oracleStep_bind', oracleStep_mapM f l, oracleStep_pure']

theorem list_forall₂_getD {γ β : Type} {R : γ → β → Prop} {l : List γ} {bs : List β} (h : List.Forall₂ R l bs)
    (n : ℕ) (hn : n < l.length) (d : β) : R l[n] (bs.getD n d) := by
  have h' := List.forall₂_iff_get.1 h
  have hn' : n < bs.length := h'.1 ▸ hn
  rw [List.getD_eq_getElem _ _ hn']
  exact h'.2 n hn hn'

/-- `deriveKeys` of a PRSS setup gives each held term key and each pair key as the answer of a
derive call. -/
theorem psafe_deriveKeys (i : C.Party) (view : C.Party → Parts C) (Q : HashOutput → Prop) :
    PSafe D (fun keys Q' => ∀ key, KeysOf i (SetupAgree.prssOf keys) key → Q' key)
      (ThresholdLeanXmss.oracleStep (deriveKeys .prss i view) : PartyM C E RealSpec _) Q := by
  unfold deriveKeys
  simp only [reduceCtorEq, ↓reduceIte, oracleStep_bind', oracleStep_pure', pure_bind, oracleStep_mapM]
  refine psafe_bind D _ _ _ _ (PSafe.mono D (fun term P P' hP hterm => ?_) _ (fun _ hk => hk)
    (psafe_mapM _ (fun T b Q' => i ∈ C.holders T → Q' b) (fun _ _ P P' hP h hT => hP _ (h hT)) (fun T Q => ?_)
      C.terms Q))
  · refine psafe_bind D _ _ _ _ (PSafe.mono D (fun pair P₁ P₂ hP₁ hpair => ?_) _ (fun _ hk => hk)
      (psafe_mapM _ (fun j b Q' => j ≠ i → Q' b) (fun _ _ P P' hP h hj => hP _ (h hj)) (fun j Q => ?_)
        C.parties P').grow)
    · rw [psafe_pure]
      rintro key ⟨name, (⟨T, hT, -, rfl⟩ | ⟨j, hj, -, rfl⟩)⟩
      · have hmem : T ∈ C.terms := by simp [Committee.terms]
        have h := list_forall₂_getD hterm (C.terms.idxOf T) (List.idxOf_lt_length_of_mem hmem) 0
        rw [List.getElem_idxOf] at h
        exact hP₁ _ (hpair.1 _ (hP _ (h hT)))
      · have h := list_forall₂_getD hpair.2 j.val (by rw [SetupAgree.parties_length]; exact j.2) 0
        rw [SetupAgree.parties_getElem] at h
        exact hP₁ _ (h hj)
    · split
      · rename_i hji
        exact (psafe_pure D _ _ _).2 fun h => absurd hji h
      · exact psafe_derive _ _ _ Q fun u _ => Or.inr rfl
  · split_ifs with hT
    · exact psafe_derive _ _ _ Q fun u _ => Or.inr rfl
    · exact (psafe_pure D _ _ _).2 fun h => absurd h hT

/-- The PRSS setup of an operator ends with keys that its own derive calls gave. -/
theorem psafe_prssSetup (i : C.Party) (Q : HashOutput → Prop) :
    PSafe D (fun prss Q' => ∀ key, KeysOf i prss key → Q' key) (prssSetup i : PartyM C E RealSpec _) Q := by
  unfold prssSetup prssSetupWith
  rw [show (fun own => commitRevealEcho .prss i own >>= fun keys => match keys with
      | (_, term, pair) => (pure ⟨term, pair⟩ : PartyM C E RealSpec (PrssKeys C))) = fun own =>
      commitRevealEcho .prss i own >>= fun keys => pure (SetupAgree.prssOf keys) from rfl]
  simp only [commitRevealEcho_eq, bind_assoc, pure_bind]
  refine psafe_noBad_bind (NoBad.of_class (ClassBound.localStep (DigestBudgets.liftComp_prob_bound .stream _)))
    fun own Q1 _ => ?_
  refine psafe_noBad_bind (noBad_hashes _ _) fun commitments Q2 _ => ?_
  refine psafe_noBad_bind (NoBad.of_class (DigestBudgets.ClassBound.exchange _)) fun committed Q3 _ => ?_
  refine psafe_noBad_bind (NoBad.of_class (DigestBudgets.ClassBound.exchange _)) fun revealed Q4 _ => ?_
  refine psafe_noBad_bind (noBad_hashes _ _) fun opens Q5 _ => ?_
  refine psafe_noBad_bind (NoBad.of_class (DigestBudgets.ClassBound.require _)) fun _ Q6 _ => ?_
  refine psafe_bind D _ _ _ _ (PSafe.mono D (fun keys P P' hP hkeys => ?_) _ (fun _ hk => hk)
    (psafe_deriveKeys i _ Q6))
  refine psafe_noBad_bind (noBad_hashes _ _) fun shared Q7 h7 => ?_
  refine psafe_noBad_bind (NoBad.of_class (DigestBudgets.ClassBound.exchange _)) fun received Q8 h8 => ?_
  refine psafe_noBad_bind (NoBad.of_class (DigestBudgets.ClassBound.require _)) fun _ Q9 h9 => ?_
  exact (psafe_pure D _ _ _).2 fun key hk => h9 _ (h8 _ (h7 _ (hP _ (hkeys key hk))))

end Setup

/-! ## The programs of a ceremony and of a tree -/

section Trees

open DigestBudgets (ClassBound StateBound)

variable {D} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- A program on a state that draws only under keys that its own derive calls gave, from each state
and each set of keys, for each end condition that always holds. -/
def SOk {σ α : Type} (p : StateT σ (PartyM C E RealSpec) α) : Prop :=
  ∀ (post : α × σ → (HashOutput → Prop) → Prop) s Q, (∀ a Q', post a Q') → PSafe D post (p.run s) Q

omit [Field E] [Algebra Bit E] in
theorem SOk.bind {σ α β : Type} {p : StateT σ (PartyM C E RealSpec) α} {f : α → StateT σ (PartyM C E RealSpec) β}
    (h : SOk (D := D) p) (hf : ∀ a, SOk (D := D) (f a)) : SOk (D := D) (p >>= f) := by
  intro post s Q hpost
  rw [StateT.run_bind]
  exact psafe_bind D _ _ _ _ (h _ s Q fun a Q' => hf a.1 post a.2 Q' hpost)

omit [Field E] [Algebra Bit E] in
theorem SOk.of_noBad {σ α : Type} {p : StateT σ (PartyM C E RealSpec) α} (h : NoBadS D (fun _ _ => False) p) :
    SOk (D := D) p :=
  fun post s Q hpost => psafe_of_noBad (h s) post Q (fun _ _ h => h.elim) fun a Q' _ => hpost a Q'

omit [Field E] [Algebra Bit E] in
theorem SOk.pure {σ α : Type} (a : α) : SOk (D := D) (Pure.pure a : StateT σ (PartyM C E RealSpec) α) :=
  SOk.of_noBad (NoBadS.pure a)

/-- One ceremony is its PRSS setup and then a program that draws only under the keys of that setup. -/
theorem ceremonyRun_split (i : C.Party) (keys : Keys C) (jobs : List Job) :
    ∃ f : PrssKeys C → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit))),
      ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs =
        StateT.lift (prssSetup i) >>= f ∧ ∀ prss, NoBadS D (NameKey i prss) (f prss) := by
  refine ⟨_, rfl, fun prss s => ?_⟩
  refine NoBadS.bind (NoBadS.mapM _ (fun batch => ?_) _) (fun _ => NoBadS.pure _) s
  refine NoBadS.bind (NoBadS.of_state DigestBudgets.StateBound.get) fun lk => ?_
  rcases lk with ⟨label, k⟩
  refine NoBadS.bind (NoBadS.lift (NoBad.of_class ((ClassBound.mapM _ 0
    (fun job => DigestBudgets.inputShares_bound _ (by decide) job) _).mono (by simp)))) fun inputs => ?_
  refine NoBadS.bind (NoBadS.lift (runJobs_noBad (ctx := ⟨i, keys, prss⟩) K _ _ _ _)) fun r => ?_
  rcases r with ⟨outputs, state⟩
  exact NoBadS.bind (NoBadS.of_state (DigestBudgets.StateBound.set _)) fun _ => NoBadS.pure _

/-- One ceremony draws only under the keys of its own PRSS setup. -/
theorem ceremonyRun_ok (i : C.Party) (keys : Keys C) (jobs : List Job) :
    SOk (D := D) (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) _) := by
  intro post s Q hpost
  obtain ⟨f, hf, hnb⟩ := ceremonyRun_split (D := D) K circuits settings i keys jobs
  rw [hf, StateT.run_bind, StateT.run_lift, bind_assoc]
  simp only [pure_bind]
  refine psafe_bind D _ _ _ _ (PSafe.mono D (fun prss P P' hP hprss => ?_) _ (fun _ hk => hk) (psafe_prssSetup i Q))
  exact psafe_of_noBad (hnb prss s) post P' (fun N k hk => hP k (hprss k ⟨N, hk⟩)) fun a Q' _ => hpost a Q'

omit [Field E] [Algebra Bit E] in
/-- The ceremonies of a tree with local steps between them draw only under derived keys. -/
theorem ceremonyOutput_ok (lift : ∀ {α : Type}, OracleComp HashSpec α → StateT (ℕ × ℕ) (PartyM C E RealSpec) α)
    (hlift : ∀ {α : Type} (oa : OracleComp HashSpec α), SOk (D := D) (lift oa)) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit))))
    (hrun : ∀ jobs, SOk (D := D) (run jobs)) (top : TopTree) (tree : Tree) :
    SOk (D := D) (ceremonyOutput lift parameter run top tree) := by
  cases tree with
  | top =>
    unfold ceremonyOutput
    refine SOk.bind (hrun topJobs) fun out => ?_
    rcases out with _ | outputs
    · exact SOk.pure _
    · exact SOk.bind (hlift _) fun _ => SOk.pure _
  | bottom b =>
    unfold ceremonyOutput
    refine SOk.bind (hrun _) fun out => ?_
    rcases out with _ | outputs
    · exact SOk.pure _
    refine SOk.bind (hlift _) fun root => ?_
    refine SOk.bind (hlift _) fun base => ?_
    refine SOk.bind (hlift _) fun found => ?_
    rcases found with _ | ⟨randomness, encoding⟩
    · exact SOk.pure _
    refine SOk.bind (hrun _) fun out => ?_
    rcases out with _ | values
    · exact SOk.pure _
    refine SOk.bind (hlift _) fun path => ?_
    refine SOk.bind (hlift _) fun topRoot => ?_
    split_ifs
    · exact SOk.pure _
    · exact SOk.pure _

/-- The program of an operator in a run of a tree draws only under keys that its own derive calls
gave. -/
theorem treeProgram_safe (i : C.Party) (operator : OperatorState C) (tree : Tree) :
    SafeThen D (fun _ _ => True) (treeProgram K circuits settings i operator tree).run fun _ => False := by
  have hnew : ∀ keys top tree, PSafe D (fun _ _ => True) (newTree K circuits settings i keys top tree)
      fun _ => False := by
    intro keys top tree
    have hout := ceremonyOutput_ok (D := D) (fun oa => StateT.lift (ThresholdLeanXmss.oracleStep (tweakable oa)))
      (fun oa => SOk.of_noBad (NoBadS.of_state (DigestBudgets.lift_tweakable_bound (by decide) oa)))
      keys.parameter _ (fun jobs => ceremonyRun_ok K circuits settings i keys jobs) top tree
    unfold newTree StateT.run'
    rw [map_eq_bind_pure_comp, bind_assoc]
    refine psafe_bind D _ _ _ _ (hout _ _ _ fun a Q' => ?_)
    simp only [Function.comp_apply, pure_bind]
    split
    · exact (psafe_pure D _ _ _).2 trivial
    · exact psafe_failure D _ _
  refine SafeThen.imp D (fun _ _ _ => trivial) _ (?_ : PSafe D (fun _ _ => True) _ _)
  cases tree with
  | top =>
    rcases hk : operator.keys with _ | keys
    · simp only [treeProgram, hk]
      exact psafe_failure D _ _
    · simp only [treeProgram, hk]
      exact hnew _ _ _
  | bottom b =>
    rcases hk : operator.keys with _ | keys <;> rcases ht : operator.top with _ | top
    · simp only [treeProgram, hk]
      exact psafe_failure D _ _
    · simp only [treeProgram, hk]
      exact psafe_failure D _ _
    · simp only [treeProgram, hk, ht]
      exact psafe_failure D _ _
    · simp only [treeProgram, hk, ht]
      exact hnew _ _ _

/-- The program of an operator in one ceremony draws only under keys that its own derive calls gave. -/
theorem ceremonyProgram_safe (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    SafeThen D (fun _ _ => True) (ceremonyProgram K circuits settings i c).run fun _ => False := by
  refine SafeThen.imp D (fun _ _ _ => trivial) _ (?_ : PSafe D (fun _ _ => True) _ _)
  unfold ceremonyProgram
  split
  · refine psafe_bind D _ _ _ _ (ceremonyRun_ok K circuits settings i _ _ _ _ _ fun p Q' => ?_)
    rcases p with ⟨_ | outputs, counters⟩
    · exact psafe_failure D _ _
    · exact (psafe_pure D _ _ _).2 trivial
  · exact psafe_failure D _ _

end Trees

end Draws

/-! ## The provenance in one ceremony and in a run of a tree -/

section Leaves

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- One ceremony keeps the provenance of the hidden keys, also when an operator aborts. -/
theorem ceremonyProvenance : CeremonyProvenance prims K circuits settings := by
  intro D net rounds c world hw r hr
  exact Draws.executePhase_keepsProvenance D prims net rounds c.adversary _
    (fun i _ => Draws.ceremonyProgram_safe K circuits settings i c) world hw r hr

/-- The phase of a run of a tree keeps the provenance of the hidden keys, also when an operator
aborts. -/
theorem treePhaseProvenance : TreePhaseProvenance prims K circuits settings := by
  intro D net tree s
  exact Draws.executePhase_keepsProvenance D prims net _ s.adversary _
    (fun i _ => Draws.treeProgram_safe K circuits settings i (s.operators i) tree)

end Leaves

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyProvenance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyProvenance

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.treePhaseProvenance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.treePhaseProvenance
