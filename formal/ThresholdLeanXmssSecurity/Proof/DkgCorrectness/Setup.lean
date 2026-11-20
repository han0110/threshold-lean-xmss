import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Walk

/-!
# The agreement of the setups

`SetupAgree.setupPhaseAgree` states that the honest operators of one PRSS setup on the network agree on
the PRSS keys, or two echo hashes collide. `SetupParameter.seedParameterAgree` states that two honest
operators that end the seed generation with an output hold the same parameter.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace SetupAgree

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## The two statements -/

section Statements

variable (prims : Primitives) (D : C.Coalition)

/-- One PRSS setup of the honest operators in `live` on the network, answered by `streamWorld`
from each state of the adversary and each world. An honest operator outside `live` aborts at once.
Two honest operators with an output hold the same pair key and the same key of each term that both
hold, or two echo hashes of the end cache collide. -/
def SetupPhaseAgree : Prop :=
  ∀ (net : Adversary C E Unit PEmpty PEmpty) (st : net.State) (live : C.Party → Prop) (w : StreamState C),
    ∀ y ∈ support ((simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality setupRounds st
        (fun i => if live i then (prssSetup i : PartyM C E RealSpec (PrssKeys C)) else failure))).run w),
    ∀ i j Pi Pj, i ∉ D.1 → j ∉ D.1 → i ≠ j → y.1.2 i = some Pi → y.1.2 j = some Pj →
      Pi.pair j = Pj.pair i ∧
        ((∀ T, i ∈ C.holders T → j ∈ C.holders T → Pi.term T = Pj.term T) ∨ DomainCollision EchoDomain y.2.1)

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings) (budget : StartBudget)

end Statements

/-! ## Local work in `streamWorld` read from the cache -/

section Cache

attribute [local instance] Set.monad

variable (prims : Primitives) (D : C.Coalition)

/-- The answers of a local query that agree with the cache `s`. A query of `H` that `streamWorld`
caches has the cached value. Each other answer is possible. -/
def cacheAnswer (s : HashCache C) : QueryImpl (LocalSpec C) Set := fun t =>
  match t with
  | .inr (.inl q) => {v | IsFixed q ∨ s q = some v}
  | _ => Set.univ

theorem cacheAnswer_mono {s s' : HashCache C} (hle : s ≤ s') (t : (LocalSpec C).Domain) :
    cacheAnswer s t ⊆ cacheAnswer s' t := by
  rcases t with n | q | x
  · exact fun _ h => h
  · exact fun v hv => hv.imp id fun h => hle h
  · exact fun _ h => h

/-- An answer of a local query in `streamWorld` grows the hash cache, and it agrees with the new
cache. -/
theorem streamWorld_local_cache (t : (LocalSpec C).Domain) (w : StreamState C)
    (y : (LocalSpec C).Range t × StreamState C) (hy : y ∈ support ((streamWorld prims D (.inr t)).run w)) :
    w.1 ≤ y.2.1 ∧ y.1 ∈ cacheAnswer y.2.1 t := by
  refine ⟨streamWorld_mono prims D (.inr t) w y hy, ?_⟩
  rcases t with n | q | x
  · trivial
  · obtain ⟨r, hr, rfl⟩ := mem_support_onHash _ w y hy
    change r.1 ∈ {v | IsFixed q ∨ r.2 q = some v}
    by_cases hq : IsFixed q
    · exact Or.inl hq
    · change r ∈ support ((hashAnswer prims q).run w.1) at hr
      rw [hashAnswer_of_not_isFixed prims hq] at hr
      exact Or.inr (randomOracle_support q w.1 r hr).2.1
  · trivial

/-- A local computation in `streamWorld` grows the hash cache, and its result is a result of the
computation with the answers of each larger cache. -/
theorem free_cache {β : Type} (oa : OracleComp (LocalSpec C) β) :
    ∀ w z, z ∈ support ((simulateQ (streamWorld prims D) (free oa)).run w) →
      w.1 ≤ z.2.1 ∧ ∀ s', z.2.1 ≤ s' → z.1 ∈ simulateQ (cacheAnswer s') oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro w z hz
    simp only [free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, fun _ _ => rfl⟩
  | query_bind t k ih =>
    intro w z hz
    simp only [free, simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    rw [simulateQ_HasQuery_query] at hy
    obtain ⟨hle₁, hans⟩ := streamWorld_local_cache prims D t w y hy
    obtain ⟨hle₂, hrest⟩ := ih y.1 y.2 z hz
    refine ⟨hle₁.trans hle₂, fun s' hs' => ?_⟩
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    exact Set.mem_iUnion₂.2 ⟨y.1, cacheAnswer_mono (hle₂.trans hs') t hans, hrest s' hs'⟩

/-- The next step of an honest operator in a round with the inbox `inbox`, with the answers of the
cache `s`. -/
def StepNext {α : Type} (s : HashCache C) (inbox : Mail C E) : Step C E RealSpec α → Step C E RealSpec α → Prop
  | .wait _ resume, next => next ∈ simulateQ (cacheAnswer s) (advance (resume inbox))
  | .done out, next => next = .done out
  | .call _ _, next => next = .done none

/-- A round of the honest operators in `streamWorld` grows the hash cache. Each honest operator
reads the messages of the other honest operators as they deliver them, and it takes its next step
with the answers of each larger cache. -/
theorem stepRound_cache {α : Type} (A : Adversary C E Unit PEmpty PEmpty) (st : A.State)
    (steps : C.Party → Step C E RealSpec α) (w : StreamState C)
    (y : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E))) × StreamState C)
    (hy : y ∈ support ((simulateQ (streamWorld prims D) (stepRound worldRoles D A noFunctionality st steps)).run w)) :
    w.1 ≤ y.2.1 ∧ ∀ j, j ∉ D.1 → ∀ s', y.2.1 ≤ s' →
      StepNext s' (roundInbox D y.1.2.2 steps j) (steps j) (y.1.2.1 j) := by
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
  have hseq := sequenceFin_streamWorld prims D (fun j next c => j ∉ D.1 → ∀ s', c ≤ s' →
      StepNext s' (roundInbox D a.1.2 steps j) (steps j) next) _
    (fun j b c c' hq hle hj s' hs' => hq hj s' (hle.trans hs')) (fun j w' u hu hj s' hs' => ?_)
    a.2 v hv
  · exact ⟨(streamWorld_run_mono prims D _ w a ha).trans (streamWorld_run_mono prims D _ a.2 v hv),
      fun j hj s' hs' => hseq j hj s' hs'⟩
  rcases hsj : steps j with out | ⟨outbox, resume⟩ | ⟨input, resume⟩
  · simp only [hsj, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    subst hu
    rfl
  · simp only [hsj, hj, ↓reduceIte] at hu
    exact (free_cache prims D _ w' u hu).2 s' hs'
  · exact input.elim

theorem mem_setBind {β γ : Type} {s : Set β} {f : β → Set γ} {c : γ} : c ∈ (s >>= f) ↔ ∃ b ∈ s, c ∈ f b := by
  simp only [Set.bind_def, Set.mem_iUnion₂, exists_prop]

theorem mem_hashQuery {s : HashCache C} {q : Query C} {v : HashOutput}
    (hv : v ∈ simulateQ (cacheAnswer s) (liftComp (hashQuery q) (LocalSpec C))) : IsFixed q ∨ s q = some v := by
  have he : liftComp (hashQuery q) (LocalSpec C) =
      OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q))) := rfl
  rw [he, simulateQ_spec_query] at hv
  simpa [cacheAnswer] using hv

theorem mem_mapM {β γ : Type} {s : HashCache C} (f : γ → OracleComp (RoSpec C) β) :
    ∀ (l : List γ) (r : List β), r ∈ simulateQ (cacheAnswer s) (liftComp (l.mapM f) (LocalSpec C)) →
      List.Forall₂ (fun a b => b ∈ simulateQ (cacheAnswer s) (liftComp (f a) (LocalSpec C))) l r
  | [], r, h => by
    simp only [List.mapM_nil, liftComp_pure, simulateQ_pure] at h
    rw [Set.pure_def, Set.mem_singleton_iff] at h
    subst h
    exact List.Forall₂.nil
  | a :: l, r, h => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, simulateQ_bind, simulateQ_pure] at h
    obtain ⟨b, hb, h⟩ := mem_setBind.1 h
    obtain ⟨bs, hbs, h⟩ := mem_setBind.1 h
    rw [Set.pure_def, Set.mem_singleton_iff] at h
    subst h
    exact List.Forall₂.cons hb (mem_mapM f l bs hbs)

end Cache

/-! ## The steps of one PRSS setup -/

section Steps

attribute [local instance] Set.monad

/-- The PRSS keys of the derived keys of a setup. -/
def prssOf (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) : PrssKeys C :=
  ⟨keys.2.1, keys.2.2⟩

/-- The step of a setup after the reveal round, with the derived keys and the echo hashes. -/
def echoStep (i : C.Party) (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (shared : List HashOutput) : Step C E RealSpec (PrssKeys C) :=
  .wait (echoOutbox .prss i keys shared) (exchangeResume fun received =>
    require (echoCheck .prss i keys shared received) >>= fun _ => pure (prssOf keys))

/-- The step of a setup after the commit round. -/
def revealStep (i : C.Party) (own : Parts C) (committed : Mail C E) : Step C E RealSpec (PrssKeys C) :=
  .wait (revealOutbox .prss i own) (exchangeResume fun revealed =>
    setupRest .prss i own committed revealed >>= fun keys => pure (prssOf keys))

/-- The first step of a setup. -/
def commitStep (i : C.Party) (own : Parts C) (commitments : List HashOutput) : Step C E RealSpec (PrssKeys C) :=
  .wait (commitOutbox i commitments) (exchangeResume fun committed =>
    exchange (revealOutbox .prss i own) >>= fun revealed =>
      setupRest .prss i own committed revealed >>= fun keys => pure (prssOf keys))

theorem advance_prssSetup (i : C.Party) :
    advance (prssSetup i : PartyM C E RealSpec (PrssKeys C)).run =
      liftComp sampleParts (LocalSpec C) >>= fun own =>
        liftComp (commitQueries .prss i own) (LocalSpec C) >>= fun commitments =>
          pure (commitStep i own commitments) := by
  have h : (prssSetup i : PartyM C E RealSpec (PrssKeys C)) = localStep (liftComp sampleParts _) >>= fun own =>
      commitRevealEcho .prss i own >>= fun keys => pure (prssOf keys) := rfl
  rw [h, advance_localStep_bind]
  refine bind_congr fun own => ?_
  rw [advance_setup_start]
  rfl

theorem start_step (s : HashCache C) (i : C.Party) (step : Step C E RealSpec (PrssKeys C))
    (h : step ∈ simulateQ (cacheAnswer s) (advance (prssSetup i : PartyM C E RealSpec (PrssKeys C)).run)) :
    ∃ own commitments, step = commitStep i own commitments := by
  rw [advance_prssSetup] at h
  simp only [simulateQ_bind, simulateQ_pure] at h
  obtain ⟨own, -, h⟩ := mem_setBind.1 h
  obtain ⟨commitments, -, h⟩ := mem_setBind.1 h
  rw [Set.pure_def, Set.mem_singleton_iff] at h
  exact ⟨own, commitments, h⟩

theorem commit_next (s : HashCache C) (inbox : Mail C E) (i : C.Party) (own : Parts C)
    (commitments : List HashOutput) (next : Step C E RealSpec (PrssKeys C))
    (h : StepNext s inbox (commitStep i own commitments) next) :
    next = .done none ∨ next = revealStep i own inbox := by
  change next ∈ simulateQ (cacheAnswer s) (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h
  · left
    simpa only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] using h
  · right
    rw [advance_exchange_bind, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
    exact h

theorem reveal_next (s : HashCache C) (inbox : Mail C E) (i : C.Party) (own : Parts C)
    (committed : Mail C E) (next : Step C E RealSpec (PrssKeys C))
    (h : StepNext s inbox (revealStep i own committed) next) :
    next = .done none ∨ ∃ keys shared,
      keys ∈ simulateQ (cacheAnswer s) (liftComp (deriveKeys .prss i (setupView .prss i own inbox)) (LocalSpec C)) ∧
      shared ∈ simulateQ (cacheAnswer s) (liftComp (sharedQueries .prss i keys) (LocalSpec C)) ∧
      next = echoStep i keys shared := by
  change next ∈ simulateQ (cacheAnswer s) (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h
  · left
    simpa only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] using h
  · rw [advance_setupRest] at h
    simp only [simulateQ_bind] at h
    obtain ⟨opens, -, h⟩ := mem_setBind.1 h
    split_ifs at h
    · right
      simp only [simulateQ_bind, simulateQ_pure] at h
      obtain ⟨keys, hkeys, h⟩ := mem_setBind.1 h
      obtain ⟨shared, hshared, h⟩ := mem_setBind.1 h
      rw [Set.pure_def, Set.mem_singleton_iff] at h
      exact ⟨keys, shared, hkeys, hshared, h⟩
    · left
      simpa [Set.pure_def] using h

theorem echo_next (s : HashCache C) (inbox : Mail C E) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (shared : List HashOutput)
    (next : Step C E RealSpec (PrssKeys C)) (h : StepNext s inbox (echoStep i keys shared) next)
    (P : PrssKeys C) (hout : next.output = some P) :
    echoCheck .prss i keys shared inbox ∧ P = prssOf keys := by
  change next ∈ simulateQ (cacheAnswer s) (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h with ha
  · simp only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
    subst h
    cases hout
  · rw [advance_require_bind] at h
    split_ifs at h with hc
    · simp only [advance_run_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
      subst h
      simp only [Step.output, Option.some.injEq] at hout
      exact ⟨hc, hout.symm⟩
    · simp only [simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
      subst h
      cases hout

theorem mapM_getD {β γ : Type} {s : HashCache C} (f : γ → OracleComp (RoSpec C) β) (l : List γ) (r : List β)
    (hr : r ∈ simulateQ (cacheAnswer s) (liftComp (l.mapM f) (LocalSpec C))) (n : ℕ) (hn : n < l.length) (d : β) :
    r.getD n d ∈ simulateQ (cacheAnswer s) (liftComp (f l[n]) (LocalSpec C)) := by
  have h := List.forall₂_iff_get.1 (mem_mapM f l r hr)
  have hn' : n < r.length := h.1 ▸ hn
  rw [List.getD_eq_getElem _ _ hn']
  exact h.2 n hn hn'

theorem parties_getElem (j : C.Party) : C.parties[j.val]'(by simp [Committee.parties]) = j := by
  simp [Committee.parties]

theorem parties_length : C.parties.length = C.n := by
  simp [Committee.parties]

/-- The echo hash of `i` to `j` is the cached hash of the shared keys. -/
theorem shared_cached {s : HashCache C} (i : C.Party) (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (shared : List HashOutput)
    (h : shared ∈ simulateQ (cacheAnswer s) (liftComp (sharedQueries .prss i keys) (LocalSpec C))) (j : C.Party) :
    s (.sharedKeys .prss ((sharedTerms i j).map keys.2.1)) = some (shared.getD j.val 0) := by
  have hj := mapM_getD _ C.parties shared h j.val (by rw [parties_length]; exact j.2) 0
  rw [parties_getElem] at hj
  exact (mem_hashQuery hj).resolve_left fun ⟨_, hq, _⟩ => by cases hq

/-- The pair key of `i` with `j` is the cached derived key of the two parts of the pair in the view
of `i`. -/
theorem pair_cached {s : HashCache C} (i : C.Party) (view : C.Party → Parts C)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (h : keys ∈ simulateQ (cacheAnswer s) (liftComp (deriveKeys .prss i view) (LocalSpec C))) (j : C.Party)
    (hij : j ≠ i) :
    s (.derive .prss .pair [(view (C.pairOf i j (Ne.symm hij)).1.1).pair (C.pairOf i j (Ne.symm hij)).1.2,
      (view (C.pairOf i j (Ne.symm hij)).1.2).pair (C.pairOf i j (Ne.symm hij)).1.1]) = some (keys.2.2 j) := by
  unfold deriveKeys at h
  simp only [reduceCtorEq, ↓reduceIte, liftComp_bind, liftComp_pure, simulateQ_bind, simulateQ_pure, pure_bind] at h
  obtain ⟨term, -, h⟩ := mem_setBind.1 h
  obtain ⟨pair, hpair, h⟩ := mem_setBind.1 h
  rw [Set.pure_def, Set.mem_singleton_iff] at h
  subst h
  have hj := mapM_getD _ C.parties pair hpair j.val (by rw [parties_length]; exact j.2) 0
  rw [parties_getElem] at hj
  simp only [hij, ↓reduceDIte] at hj
  exact (mem_hashQuery hj).resolve_left fun ⟨_, hq, _⟩ => by cases hq

/-- The view of `i` of a pair part of `j` is the part of `j` that `j` revealed to `i`. -/
theorem setupView_pair (i j : C.Party) (hij : i ≠ j) (own own' : Parts C) (inbox : Mail C E)
    (hrev : inbox j = revealOutbox .prss j own' i) (x : C.Party) :
    (setupView .prss i own inbox j).pair x = own'.pair i := by
  have hji : j ≠ i := Ne.symm hij
  simp only [setupView, hji, ↓reduceIte, hrev, revealOutbox, hij, Msg.hashesOf, readReveal, revealTo,
    reduceCtorEq, List.nil_append, Nat.zero_add]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
  simp

/-- Both ends of a pair derive the pair key from the same two parts, so the pair keys agree. The echo
of `j` to `i` matches the echo of `i`, so the two cached echo hashes are equal. Then the shared term
keys agree, or the echo domain of the cache collides. -/
theorem agree_of_traces {s : HashCache C} (i j : C.Party) (hij : i ≠ j) (own own' : Parts C)
    (inbox inbox' echoInbox : Mail C E) (keys keys' : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (shared shared' : List HashOutput)
    (hkeys : keys ∈ simulateQ (cacheAnswer s) (liftComp (deriveKeys .prss i (setupView .prss i own inbox)) (LocalSpec C)))
    (hkeys' : keys' ∈ simulateQ (cacheAnswer s) (liftComp (deriveKeys .prss j (setupView .prss j own' inbox')) (LocalSpec C)))
    (hshared : shared ∈ simulateQ (cacheAnswer s) (liftComp (sharedQueries .prss i keys) (LocalSpec C)))
    (hshared' : shared' ∈ simulateQ (cacheAnswer s) (liftComp (sharedQueries .prss j keys') (LocalSpec C)))
    (hrev : inbox j = revealOutbox .prss j own' i) (hrev' : inbox' i = revealOutbox .prss i own j)
    (hecho : echoInbox j = echoOutbox .prss j keys' shared' i) (hcheck : echoCheck .prss i keys shared echoInbox) :
    (prssOf keys).pair j = (prssOf keys').pair i ∧
      ((∀ T, i ∈ C.holders T → j ∈ C.holders T → (prssOf keys).term T = (prssOf keys').term T) ∨
        DomainCollision EchoDomain s) := by
  have hji : j ≠ i := Ne.symm hij
  constructor
  · have h₁ := pair_cached i _ keys hkeys j hji
    have h₂ := pair_cached j _ keys' hkeys' i hij
    have hA : (setupView .prss i own inbox i).pair j = (setupView .prss j own' inbox' i).pair j := by
      rw [setupView_pair j i hji own' own inbox' hrev' j]
      simp [setupView]
    have hB : (setupView .prss i own inbox j).pair i = (setupView .prss j own' inbox' j).pair i := by
      rw [setupView_pair i j hij own own' inbox hrev i]
      simp [setupView]
    rw [← pairOf_comm i j hij] at h₂
    have hends : (C.pairOf i j hij).1.1 = i ∧ (C.pairOf i j hij).1.2 = j ∨
        (C.pairOf i j hij).1.1 = j ∧ (C.pairOf i j hij).1.2 = i := by
      unfold Committee.pairOf
      split_ifs <;> simp
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at h₁ h₂
      rw [hA, hB, h₂] at h₁
      exact (Option.some.inj h₁).symm
    · rw [h1, h2] at h₁ h₂
      rw [hA, hB, h₂] at h₁
      exact (Option.some.inj h₁).symm
  · have hs₁ := shared_cached i keys shared hshared j
    have hs₂ := shared_cached j keys' shared' hshared' i
    have hcj := hcheck j hji
    rw [hecho] at hcj
    simp only [echoOutbox, hij, ↓reduceIte, Msg.hashesOf, echoOf, reduceCtorEq, List.nil_append,
      List.cons.injEq, and_true] at hcj
    rw [hcj] at hs₂
    by_cases hq : Query.sharedKeys (C := C) .prss ((sharedTerms i j).map keys.2.1) =
        Query.sharedKeys .prss ((sharedTerms j i).map keys'.2.1)
    · left
      have hlists := (Query.sharedKeys.inj hq).2
      rw [sharedTerms_comm j i] at hlists
      intro T hi hj
      apply List.map_eq_map_iff.mp hlists T
      simp [sharedTerms, Committee.terms, hi, hj]
    · right
      refine ⟨_, _, shared.getD j.val 0, shared.getD j.val 0, hq, ?_, ?_, HEq.rfl⟩
      · simp only [splitRegionCache, QueryCache.ofFn_apply, EchoDomain, ↓reduceIte]
        exact hs₁
      · simp only [splitRegionCache, QueryCache.ofFn_apply, EchoDomain, ↓reduceIte]
        exact hs₂

/-- The steps of one operator through the three rounds of a setup that ends with an output. -/
theorem party_trace (s : HashCache C) (k : C.Party) (step0 step1 step2 step3 : Step C E RealSpec (PrssKeys C))
    (inbox1 inbox2 inbox3 : Mail C E)
    (h0 : step0 = .done none ∨ ∃ own commitments, step0 = commitStep k own commitments)
    (h1 : StepNext s inbox1 step0 step1) (h2 : StepNext s inbox2 step1 step2) (h3 : StepNext s inbox3 step2 step3)
    (P : PrssKeys C) (hout : step3.output = some P) :
    ∃ own keys shared, step1 = revealStep k own inbox1 ∧ step2 = echoStep k keys shared ∧
      keys ∈ simulateQ (cacheAnswer s) (liftComp (deriveKeys .prss k (setupView .prss k own inbox2)) (LocalSpec C)) ∧
      shared ∈ simulateQ (cacheAnswer s) (liftComp (sharedQueries .prss k keys) (LocalSpec C)) ∧
      echoCheck .prss k keys shared inbox3 ∧ P = prssOf keys := by
  have hdead : ∀ (a b : Step C E RealSpec (PrssKeys C)) (m : Mail C E), a = .done none → StepNext s m a b →
      b = .done none := by
    intro a b m ha hb
    subst ha
    exact hb
  rcases h0 with h0 | ⟨own, commitments, rfl⟩
  · have := hdead _ _ _ (hdead _ _ _ (hdead _ _ _ h0 h1) h2) h3
    subst this
    cases hout
  rcases commit_next s inbox1 k own commitments step1 h1 with h1' | rfl
  · have := hdead _ _ _ (hdead _ _ _ h1' h2) h3
    subst this
    cases hout
  rcases reveal_next s inbox2 k own inbox1 step2 h2 with h2' | ⟨keys, shared, hkeys, hshared, rfl⟩
  · have := hdead _ _ _ h2' h3
    subst this
    cases hout
  obtain ⟨hcheck, rfl⟩ := echo_next s inbox3 k keys shared step3 h3 P hout
  exact ⟨own, keys, shared, rfl, rfl, hkeys, hshared, hcheck, rfl⟩

theorem output_none_one (s : HashCache C) (k : C.Party) (step0 step1 : Step C E RealSpec (PrssKeys C))
    (inbox1 : Mail C E) (h0 : step0 = .done none ∨ ∃ own commitments, step0 = commitStep k own commitments)
    (h1 : StepNext s inbox1 step0 step1) : step1.output = none := by
  rcases h0 with rfl | ⟨own, commitments, rfl⟩
  · rw [show step1 = .done none from h1]
    rfl
  · rcases commit_next s inbox1 k own commitments step1 h1 with rfl | rfl <;> rfl

theorem output_none_two (s : HashCache C) (k : C.Party) (step0 step1 step2 : Step C E RealSpec (PrssKeys C))
    (inbox1 inbox2 : Mail C E) (h0 : step0 = .done none ∨ ∃ own commitments, step0 = commitStep k own commitments)
    (h1 : StepNext s inbox1 step0 step1) (h2 : StepNext s inbox2 step1 step2) : step2.output = none := by
  rcases h0 with rfl | ⟨own, commitments, rfl⟩
  · have e1 : step1 = .done none := h1
    subst e1
    rw [show step2 = .done none from h2]
    rfl
  · rcases commit_next s inbox1 k own commitments step1 h1 with rfl | rfl
    · rw [show step2 = .done none from h2]
      rfl
    · rcases reveal_next s inbox2 k own inbox1 step2 h2 with rfl | ⟨keys, shared, -, -, rfl⟩ <;> rfl

end Steps

/-! ## The setup on the network -/

section Network

attribute [local instance] Set.monad

variable (prims : Primitives) (D : C.Coalition)

theorem executeRounds_succ_support {α : Type} (A : Adversary C E Unit PEmpty PEmpty) (n : ℕ) (st : A.State)
    (steps : C.Party → Step C E RealSpec α) (w : StreamState C) (y : (A.State × (C.Party → Option α)) × StreamState C)
    (hy : y ∈ support ((simulateQ (streamWorld prims D)
      (executeRounds worldRoles D A noFunctionality (n + 1) st steps)).run w)) :
    y.1.2 = (fun k => (steps k).output) ∨
      ∃ q ∈ support ((simulateQ (streamWorld prims D) (stepRound worldRoles D A noFunctionality st steps)).run w),
        y ∈ support ((simulateQ (streamWorld prims D)
          (executeRounds worldRoles D A noFunctionality n q.1.1 q.1.2.1)).run q.2) := by
  rw [executeRounds] at hy
  split_ifs at hy
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact Or.inl rfl
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hy
    obtain ⟨q, hq, hy⟩ := hy
    exact Or.inr ⟨q, hq, hy⟩

theorem executeRounds_zero_support {α : Type} (A : Adversary C E Unit PEmpty PEmpty) (st : A.State)
    (steps : C.Party → Step C E RealSpec α) (w : StreamState C) (y : (A.State × (C.Party → Option α)) × StreamState C)
    (hy : y ∈ support ((simulateQ (streamWorld prims D)
      (executeRounds worldRoles D A noFunctionality 0 st steps)).run w)) :
    y.1.2 = (fun k => (steps k).output) ∧ y.2 = w := by
  simp only [executeRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
  subst hy
  exact ⟨rfl, rfl⟩

/-- The first steps of a setup phase. An honest operator waits at the commit round of its setup, or
it aborted. -/
theorem startSteps_setup (live : C.Party → Prop) (w : StreamState C)
    (a : (C.Party → Step C E RealSpec (PrssKeys C)) × StreamState C)
    (ha : a ∈ support ((simulateQ (streamWorld prims D) (startSteps worldRoles D
      (fun i => if live i then (prssSetup i : PartyM C E RealSpec (PrssKeys C)) else failure))).run w)) :
    w.1 ≤ a.2.1 ∧ ∀ k, k ∉ D.1 → a.1 k = .done none ∨ ∃ own commitments, a.1 k = commitStep k own commitments := by
  unfold startSteps at ha
  refine ⟨streamWorld_run_mono prims D _ w a ha, ?_⟩
  refine sequenceFin_streamWorld prims D (fun k v _ => k ∉ D.1 → v = (Step.done none : Step C E RealSpec (PrssKeys C)) ∨
      ∃ own commitments, v = commitStep k own commitments) _ (fun _ _ _ _ h _ => h) (fun k w' u hu hk => ?_) w a ha
  simp only [hk, ↓reduceIte, worldRoles] at hu
  by_cases hl : live k
  · simp only [hl, ↓reduceIte] at hu
    exact Or.inr (start_step u.2.1 k u.1 ((free_cache prims D _ w' u hu).2 u.2.1 le_rfl))
  · simp only [hl, ↓reduceIte, advance_run_failure] at hu
    simp only [free, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hu
    subst hu
    exact Or.inl rfl

/-- One PRSS setup on the network in `streamWorld` from each state of the adversary and each world.
Two honest operators with an output agree on their pair key, and on each shared term key unless two
cached echo hashes collide. -/
theorem setupPhaseAgree : SetupPhaseAgree (E := E) prims D := by
  intro net st live w y hy i j Pi Pj hi hj hij hPi hPj
  unfold executePhase at hy
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hy
  obtain ⟨a0, ha0, hy⟩ := hy
  obtain ⟨-, h0⟩ := startSteps_setup prims D live w a0 ha0
  rcases executeRounds_succ_support prims D net 2 st a0.1 a0.2 y hy with hout | ⟨q1, hq1, hy⟩
  · exfalso
    rcases h0 i hi with h | ⟨own, commitments, h⟩ <;>
      simp [hout, h, Step.output, commitStep] at hPi
  obtain ⟨hle1, hn1⟩ := stepRound_cache prims D net st a0.1 a0.2 q1 hq1
  rcases executeRounds_succ_support prims D net 1 q1.1.1 q1.1.2.1 q1.2 y hy with hout | ⟨q2, hq2, hy⟩
  · exfalso
    simp [hout, output_none_one q1.2.1 i _ _ _ (h0 i hi) (hn1 i hi q1.2.1 le_rfl)] at hPi
  obtain ⟨hle2, hn2⟩ := stepRound_cache prims D net q1.1.1 q1.1.2.1 q1.2 q2 hq2
  rcases executeRounds_succ_support prims D net 0 q2.1.1 q2.1.2.1 q2.2 y hy with hout | ⟨q3, hq3, hy⟩
  · exfalso
    simp [hout, output_none_two q2.2.1 i _ _ _ _ _ (h0 i hi) (hn1 i hi q2.2.1 hle2) (hn2 i hi q2.2.1 le_rfl)] at hPi
  obtain ⟨hle3, hn3⟩ := stepRound_cache prims D net q2.1.1 q2.1.2.1 q2.2 q3 hq3
  obtain ⟨hout, hw⟩ := executeRounds_zero_support prims D net q3.1.1 q3.1.2.1 q3.2 y hy
  have hs3 : q3.2.1 ≤ y.2.1 := by rw [hw]
  have hs2 : q2.2.1 ≤ y.2.1 := hle3.trans hs3
  have hs1 : q1.2.1 ≤ y.2.1 := hle2.trans hs2
  have htrace : ∀ k, k ∉ D.1 → ∀ P, y.1.2 k = some P →
      ∃ own keys shared, q1.1.2.1 k = revealStep k own (roundInbox D q1.1.2.2 a0.1 k) ∧
        q2.1.2.1 k = echoStep k keys shared ∧
        keys ∈ simulateQ (cacheAnswer y.2.1) (liftComp (deriveKeys .prss k
          (setupView .prss k own (roundInbox D q2.1.2.2 q1.1.2.1 k))) (LocalSpec C)) ∧
        shared ∈ simulateQ (cacheAnswer y.2.1) (liftComp (sharedQueries .prss k keys) (LocalSpec C)) ∧
        echoCheck .prss k keys shared (roundInbox D q3.1.2.2 q2.1.2.1 k) ∧ P = prssOf keys := by
    intro k hk P hP
    rw [hout] at hP
    exact party_trace y.2.1 k _ _ _ _ _ _ _ (h0 k hk) (hn1 k hk y.2.1 hs1) (hn2 k hk y.2.1 hs2)
      (hn3 k hk y.2.1 hs3) P hP
  obtain ⟨own, keys, shared, hr, he, hkeys, hshared, hcheck, rfl⟩ := htrace i hi Pi hPi
  obtain ⟨own', keys', shared', hr', he', hkeys', hshared', -, rfl⟩ := htrace j hj Pj hPj
  refine agree_of_traces i j hij own own' _ _ _ keys keys' shared shared' hkeys hkeys' hshared hshared'
    ?_ ?_ ?_ hcheck
  · simp [roundInbox, hj, hr', revealStep]
  · simp [roundInbox, hi, hr, revealStep]
  · simp [roundInbox, hj, he', echoStep]

end Network

end SetupAgree

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace SetupParameter

open SetupAgree

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- The keys of a seed generation from its derived keys. -/
def keysOf (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) : Keys C :=
  ⟨truncateHash keys.1, keys.2.1, keys.2.2⟩

/-- The seed generation on the network, answered by `streamWorld` from each state of the adversary
and each world. Two honest operators with an output hold the same parameter. -/
def SeedParameterAgree (prims : Primitives) (D : C.Coalition) : Prop :=
  ∀ (net : Adversary C E Unit PEmpty PEmpty) (st : net.State) (w : StreamState C),
    ∀ y ∈ support ((simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality setupRounds st
        (fun i => (seedGen i : PartyM C E RealSpec (Keys C))))).run w),
    ∀ i j Ki Kj, i ∉ D.1 → j ∉ D.1 → y.1.2 i = some Ki → y.1.2 j = some Kj → Ki.parameter = Kj.parameter

/-! ## The steps of one seed generation -/

section Steps

attribute [local instance] Set.monad

/-- The step of a seed generation after the reveal round, with the derived keys and the echo
hashes. -/
def echoStep (i : C.Party) (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (shared : List HashOutput) : Step C E RealSpec (Keys C) :=
  .wait (echoOutbox .seedGen i keys shared) (exchangeResume fun received =>
    require (echoCheck .seedGen i keys shared received) >>= fun _ => pure (keysOf keys))

/-- The step of a seed generation after the commit round. -/
def revealStep (i : C.Party) (own : Parts C) (committed : Mail C E) : Step C E RealSpec (Keys C) :=
  .wait (revealOutbox .seedGen i own) (exchangeResume fun revealed =>
    setupRest .seedGen i own committed revealed >>= fun keys => pure (keysOf keys))

/-- The first step of a seed generation. -/
def commitStep (i : C.Party) (own : Parts C) (commitments : List HashOutput) : Step C E RealSpec (Keys C) :=
  .wait (commitOutbox i commitments) (exchangeResume fun committed =>
    exchange (revealOutbox .seedGen i own) >>= fun revealed =>
      setupRest .seedGen i own committed revealed >>= fun keys => pure (keysOf keys))

theorem advance_seedGen (i : C.Party) :
    advance (seedGen i : PartyM C E RealSpec (Keys C)).run =
      liftComp sampleParts (LocalSpec C) >>= fun own =>
        liftComp (commitQueries .seedGen i own) (LocalSpec C) >>= fun commitments =>
          pure (commitStep i own commitments) := by
  have h : (seedGen i : PartyM C E RealSpec (Keys C)) = localStep (liftComp sampleParts _) >>= fun own =>
      commitRevealEcho .seedGen i own >>= fun keys => pure (keysOf keys) := rfl
  rw [h, advance_localStep_bind]
  refine bind_congr fun own => ?_
  rw [advance_setup_start]
  rfl

theorem start_step (s : HashCache C) (i : C.Party) (step : Step C E RealSpec (Keys C))
    (h : step ∈ simulateQ (cacheAnswer s) (advance (seedGen i : PartyM C E RealSpec (Keys C)).run)) :
    ∃ own commitments, step = commitStep i own commitments := by
  rw [advance_seedGen] at h
  simp only [simulateQ_bind, simulateQ_pure] at h
  obtain ⟨own, -, h⟩ := mem_setBind.1 h
  obtain ⟨commitments, -, h⟩ := mem_setBind.1 h
  rw [Set.pure_def, Set.mem_singleton_iff] at h
  exact ⟨own, commitments, h⟩

theorem commit_next (s : HashCache C) (inbox : Mail C E) (i : C.Party) (own : Parts C)
    (commitments : List HashOutput) (next : Step C E RealSpec (Keys C))
    (h : StepNext s inbox (commitStep i own commitments) next) :
    next = .done none ∨ next = revealStep i own inbox := by
  change next ∈ simulateQ (cacheAnswer s) (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h
  · left
    simpa only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] using h
  · right
    rw [advance_exchange_bind, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
    exact h

theorem reveal_next (s : HashCache C) (inbox : Mail C E) (i : C.Party) (own : Parts C)
    (committed : Mail C E) (next : Step C E RealSpec (Keys C))
    (h : StepNext s inbox (revealStep i own committed) next) :
    next = .done none ∨ ∃ keys shared, next = echoStep i keys shared := by
  change next ∈ simulateQ (cacheAnswer s) (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h
  · left
    simpa only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] using h
  · rw [advance_setupRest] at h
    simp only [simulateQ_bind] at h
    obtain ⟨opens, -, h⟩ := mem_setBind.1 h
    split_ifs at h
    · right
      simp only [simulateQ_bind, simulateQ_pure] at h
      obtain ⟨keys, -, h⟩ := mem_setBind.1 h
      obtain ⟨shared, -, h⟩ := mem_setBind.1 h
      rw [Set.pure_def, Set.mem_singleton_iff] at h
      exact ⟨keys, shared, h⟩
    · left
      simpa [Set.pure_def] using h

theorem echo_next (s : HashCache C) (inbox : Mail C E) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (shared : List HashOutput)
    (next : Step C E RealSpec (Keys C)) (h : StepNext s inbox (echoStep i keys shared) next)
    (K : Keys C) (hout : next.output = some K) :
    echoCheck .seedGen i keys shared inbox ∧ K = keysOf keys := by
  change next ∈ simulateQ (cacheAnswer s) (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h with ha
  · simp only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
    subst h
    cases hout
  · rw [advance_require_bind] at h
    split_ifs at h with hc
    · simp only [advance_run_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
      subst h
      simp only [Step.output, Option.some.injEq] at hout
      exact ⟨hc, hout.symm⟩
    · simp only [simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
      subst h
      cases hout

/-- The steps of one operator through the three rounds of a seed generation that ends with an
output. -/
theorem party_trace (s : HashCache C) (k : C.Party) (step0 step1 step2 step3 : Step C E RealSpec (Keys C))
    (inbox1 inbox2 inbox3 : Mail C E) (h0 : ∃ own commitments, step0 = commitStep k own commitments)
    (h1 : StepNext s inbox1 step0 step1) (h2 : StepNext s inbox2 step1 step2) (h3 : StepNext s inbox3 step2 step3)
    (K : Keys C) (hout : step3.output = some K) :
    ∃ keys shared, step2 = echoStep k keys shared ∧ echoCheck .seedGen k keys shared inbox3 ∧ K = keysOf keys := by
  have hdead : ∀ (a b : Step C E RealSpec (Keys C)) (m : Mail C E), a = .done none → StepNext s m a b →
      b = .done none := by
    intro a b m ha hb
    subst ha
    exact hb
  obtain ⟨own, commitments, rfl⟩ := h0
  rcases commit_next s inbox1 k own commitments step1 h1 with h1' | rfl
  · have := hdead _ _ _ (hdead _ _ _ h1' h2) h3
    subst this
    cases hout
  rcases reveal_next s inbox2 k own inbox1 step2 h2 with h2' | ⟨keys, shared, rfl⟩
  · have := hdead _ _ _ h2' h3
    subst this
    cases hout
  obtain ⟨hcheck, rfl⟩ := echo_next s inbox3 k keys shared step3 h3 K hout
  exact ⟨keys, shared, rfl, hcheck, rfl⟩

theorem output_none_one (s : HashCache C) (k : C.Party) (step0 step1 : Step C E RealSpec (Keys C))
    (inbox1 : Mail C E) (h0 : ∃ own commitments, step0 = commitStep k own commitments)
    (h1 : StepNext s inbox1 step0 step1) : step1.output = none := by
  obtain ⟨own, commitments, rfl⟩ := h0
  rcases commit_next s inbox1 k own commitments step1 h1 with rfl | rfl <;> rfl

theorem output_none_two (s : HashCache C) (k : C.Party) (step0 step1 step2 : Step C E RealSpec (Keys C))
    (inbox1 inbox2 : Mail C E) (h0 : ∃ own commitments, step0 = commitStep k own commitments)
    (h1 : StepNext s inbox1 step0 step1) (h2 : StepNext s inbox2 step1 step2) : step2.output = none := by
  obtain ⟨own, commitments, rfl⟩ := h0
  rcases commit_next s inbox1 k own commitments step1 h1 with rfl | rfl
  · rw [show step2 = .done none from h2]
    rfl
  · rcases reveal_next s inbox2 k own inbox1 step2 h2 with rfl | ⟨keys, shared, rfl⟩ <;> rfl

/-- The echo check of `i` against the echo of `j` gives equal parameter hashes. -/
theorem parameter_of_echo (i j : C.Party) (hij : i ≠ j)
    (keys keys' : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (shared shared' : List HashOutput)
    (echoInbox : Mail C E) (hecho : echoInbox j = echoOutbox .seedGen j keys' shared' i)
    (hcheck : echoCheck .seedGen i keys shared echoInbox) : keys.1 = keys'.1 := by
  have hcj := hcheck j (Ne.symm hij)
  rw [hecho] at hcj
  simp only [echoOutbox, hij, ↓reduceIte, Msg.hashesOf, echoOf, List.singleton_append, List.cons.injEq] at hcj
  exact hcj.1.symm

end Steps

/-! ## The seed generation on the network -/

section Network

attribute [local instance] Set.monad

variable (prims : Primitives) (D : C.Coalition)

/-- The first steps of a seed generation. An honest operator waits at its commit round. -/
theorem startSteps_seedGen (w : StreamState C)
    (a : (C.Party → Step C E RealSpec (Keys C)) × StreamState C)
    (ha : a ∈ support ((simulateQ (streamWorld prims D) (startSteps worldRoles D
      (fun i => (seedGen i : PartyM C E RealSpec (Keys C))))).run w)) :
    ∀ k, k ∉ D.1 → ∃ own commitments, a.1 k = commitStep k own commitments := by
  unfold startSteps at ha
  refine sequenceFin_streamWorld prims D (fun k v _ => k ∉ D.1 → ∃ own commitments, v = commitStep k own commitments)
    _ (fun _ _ _ _ h _ => h) (fun k w' u hu hk => ?_) w a ha
  simp only [hk, ↓reduceIte, worldRoles] at hu
  exact start_step u.2.1 k u.1 ((free_cache prims D _ w' u hu).2 u.2.1 le_rfl)

/-- The seed generation on the network in `streamWorld` from each state of the adversary and each
world. Two honest operators with an output hold the same parameter. -/
theorem seedParameterAgree : SeedParameterAgree (E := E) prims D := by
  intro net st w y hy i j Ki Kj hi hj hKi hKj
  by_cases hij : i = j
  · subst hij
    rw [hKi] at hKj
    rw [Option.some.inj hKj]
  unfold executePhase at hy
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hy
  obtain ⟨a0, ha0, hy⟩ := hy
  have h0 := startSteps_seedGen prims D w a0 ha0
  rcases executeRounds_succ_support prims D net 2 st a0.1 a0.2 y hy with hout | ⟨q1, hq1, hy⟩
  · exfalso
    obtain ⟨own, commitments, h⟩ := h0 i hi
    simp [hout, h, Step.output, commitStep] at hKi
  obtain ⟨hle1, hn1⟩ := stepRound_cache prims D net st a0.1 a0.2 q1 hq1
  rcases executeRounds_succ_support prims D net 1 q1.1.1 q1.1.2.1 q1.2 y hy with hout | ⟨q2, hq2, hy⟩
  · exfalso
    simp [hout, output_none_one q1.2.1 i _ _ _ (h0 i hi) (hn1 i hi q1.2.1 le_rfl)] at hKi
  obtain ⟨hle2, hn2⟩ := stepRound_cache prims D net q1.1.1 q1.1.2.1 q1.2 q2 hq2
  rcases executeRounds_succ_support prims D net 0 q2.1.1 q2.1.2.1 q2.2 y hy with hout | ⟨q3, hq3, hy⟩
  · exfalso
    simp [hout, output_none_two q2.2.1 i _ _ _ _ _ (h0 i hi) (hn1 i hi q2.2.1 hle2) (hn2 i hi q2.2.1 le_rfl)] at hKi
  obtain ⟨hle3, hn3⟩ := stepRound_cache prims D net q2.1.1 q2.1.2.1 q2.2 q3 hq3
  obtain ⟨hout, hw⟩ := executeRounds_zero_support prims D net q3.1.1 q3.1.2.1 q3.2 y hy
  have hs3 : q3.2.1 ≤ y.2.1 := by rw [hw]
  have hs2 : q2.2.1 ≤ y.2.1 := hle3.trans hs3
  have hs1 : q1.2.1 ≤ y.2.1 := hle2.trans hs2
  have htrace : ∀ k, k ∉ D.1 → ∀ K, y.1.2 k = some K →
      ∃ keys shared, q2.1.2.1 k = echoStep k keys shared ∧
        echoCheck .seedGen k keys shared (roundInbox D q3.1.2.2 q2.1.2.1 k) ∧ K = keysOf keys := by
    intro k hk K hK
    rw [hout] at hK
    exact party_trace y.2.1 k _ _ _ _ _ _ _ (h0 k hk) (hn1 k hk y.2.1 hs1) (hn2 k hk y.2.1 hs2)
      (hn3 k hk y.2.1 hs3) K hK
  obtain ⟨keys, shared, -, hcheck, rfl⟩ := htrace i hi Ki hKi
  obtain ⟨keys', shared', he', -, rfl⟩ := htrace j hj Kj hKj
  have hpar := parameter_of_echo i j hij keys keys' shared shared' _ (by simp [roundInbox, hj, he', echoStep])
    hcheck
  exact congrArg truncateHash hpar

end Network

end SetupParameter

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupAgree.setupPhaseAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupAgree.setupPhaseAgree

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupParameter.seedParameterAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupParameter.seedParameterAgree
