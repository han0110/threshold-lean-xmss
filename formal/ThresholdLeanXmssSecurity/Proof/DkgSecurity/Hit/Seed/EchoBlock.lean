import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.EchoCollide

/-!
# The block of round 2 in two passes

* `passOne D parts committed d sent j` is the first part of the local step of operator `j` in round 2.
  It makes the open calls, the open test and the derive calls. `passTwo j` is the second part, the shared key
  calls. `localBlock` is the sequence of the two parts of each operator, and `revealBlock_eq` states
  that the block of round 2 is `localBlock` on the free copy.
* `localBlock_noStream` and `passOne_avoid` state that the block makes no stream call and that pass 1
  asks no shared key cell of the seed generation.
* The support facts. A run of `compLocal` only adds values to the cache (`compLocal_run_mono`). A run with
  no call at a cell keeps its value (`compLocal_run_keep`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## The two passes -/

section Passes

variable {E : Type} (D : C.Coalition) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
  (d : C.Party → Option Unit) (sent : C.Party → C.Party → Option (Msg E))

/-- The inbox of operator `j` in round 2. -/
abbrev blockInbox (j : C.Party) : Mail C E :=
  levelInbox D d (fun i _ => revealOutbox .seedGen i (parts i)) sent j

/-- The first part of the local step of operator `j` in round 2. It makes the open calls, the open test
and the derive calls. -/
def passOne (j : C.Party) : OracleComp (LocalSpec C) (Option (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))) :=
  if j ∈ D.1 then pure none else
  match d j with
  | none => pure none
  | some _ => if anyAbort (blockInbox D parts d sent j) then pure none else
      liftComp (C.parties.mapM fun k => hashQuery (openAddress D parts j (blockInbox D parts d sent j) k)) (LocalSpec C) >>=
        fun opens =>
      if openCheck .seedGen j (parts j) (committed j) (normRevealed D parts j (blockInbox D parts d sent j)) opens then
        liftComp (deriveKeys .seedGen j (normView D parts j (blockInbox D parts d sent j))) (LocalSpec C) >>= fun keys =>
          pure (some keys)
      else pure none

/-- The second part of the local step of operator `j` in round 2, the shared key calls. -/
def passTwo (j : C.Party) :
    Option (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) →
      OracleComp (LocalSpec C) (Option (SeedGenEchoData C))
  | none => pure none
  | some keys => liftComp (C.parties.mapM fun l => hashQuery (sharedAddress j l keys.2.1)) (LocalSpec C) >>= fun sh =>
      pure (some (keys, sh))

/-- The block of round 2 on the local oracles. -/
def localBlock : OracleComp (LocalSpec C) (C.Party → Option (SeedGenEchoData C)) :=
  OverPermutation.sequenceFin fun j => passOne D parts committed d sent j >>= passTwo j

theorem revealBlock_eq : revealBlock D parts committed d sent = free (localBlock D parts committed d sent) := by
  unfold revealBlock localBlock
  rw [free_sequenceFin]
  congr 1
  funext j
  by_cases hj : j ∈ D.1
  · simp [passOne, hj, passTwo]
  rcases hd : d j with _ | u
  · simp [passOne, hj, hd, passTwo]
  by_cases ha : anyAbort (blockInbox D parts d sent j) = true
  · simp [passOne, hj, hd, ha, passTwo]
  simp only [passOne, hj, hd, ha, ite_false, Bool.false_eq_true, revealNext, bind_assoc, free_bind]
  refine bind_congr fun opens => ?_
  split_ifs
  · simp only [free_bind, bind_assoc, free_pure, pure_bind, passTwo]
  · simp only [free_pure, pure_bind, passTwo]

end Passes

/-! ## The calls of the two passes -/

section Calls

/-- A call of `H` that asks no cell with `P`. A stream call is excluded. -/
def LocalAvoid (P : Query C → Prop) : (LocalSpec C).Domain → Prop
  | .inr (.inl q) => ¬ P q
  | .inr (.inr _) => False
  | .inl _ => True

/-- A call of `H` on the oracles of `H` and of the streams that asks no cell with `P`. -/
def RoAvoid (P : Query C → Prop) : (RoSpec C).Domain → Prop
  | .inl q => ¬ P q
  | .inr _ => False

theorem noStream_of_avoid (P : Query C → Prop) (t : (LocalSpec C).Domain) (h : LocalAvoid P t) : NoStream t := by
  rcases t with n | q | x
  · trivial
  · trivial
  · exact h

theorem avoid_liftComp (P : Query C → Prop) {α : Type} (R : OracleComp (RoSpec C) α)
    (hR : AllQueriesSatisfy R (RoAvoid P)) : AllQueriesSatisfy (liftComp R (LocalSpec C)) (LocalAvoid P) := by
  induction R using OracleComp.inductionOn with
  | pure a => simp only [liftComp_pure]; exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hR
    rw [liftComp_bind]
    refine allQueriesSatisfy_bind ?_ fun a => ih a (hR.2 a)
    have e : liftComp (liftM (OracleSpec.query t) : OracleComp (RoSpec C) _) (LocalSpec C) =
        (liftM (OracleSpec.query (spec := LocalSpec C) (.inr t)) : OracleComp (LocalSpec C) _) := by
      simp
      rfl
    rw [e, allQueriesSatisfy_query_iff]
    rcases t with q | x
    · exact hR.1
    · exact hR.1

theorem avoid_hashQuery (P : Query C → Prop) (q : Query C) (hq : ¬ P q) :
    AllQueriesSatisfy (hashQuery q) (RoAvoid P) := by
  exact (allQueriesSatisfy_query_iff (spec := RoSpec C) (.inl q) _).2 hq

theorem avoid_mapM {β γ : Type} (P : Query C → Prop) (f : β → OracleComp (RoSpec C) γ)
    (hf : ∀ x, AllQueriesSatisfy (f x) (RoAvoid P)) :
    ∀ xs : List β, AllQueriesSatisfy (xs.mapM f) (RoAvoid P)
  | [] => by simp only [List.mapM_nil]; exact allQueriesSatisfy_pure _ _
  | x :: xs => by
    simp only [List.mapM_cons]
    exact allQueriesSatisfy_bind (hf x) fun a => allQueriesSatisfy_bind (avoid_mapM P f hf xs) fun _ =>
      allQueriesSatisfy_pure _ _

theorem avoid_sequenceFin {α : Type} (Q : (LocalSpec C).Domain → Prop) :
    ∀ {n : ℕ} (f : Fin n → OracleComp (LocalSpec C) α), (∀ j, AllQueriesSatisfy (f j) Q) →
      AllQueriesSatisfy (OverPermutation.sequenceFin f) Q
  | 0, f, _ => by simp only [OverPermutation.sequenceFin]; exact allQueriesSatisfy_pure _ _
  | n + 1, f, hf => by
    simp only [OverPermutation.sequenceFin]
    exact allQueriesSatisfy_bind (hf 0) fun a => allQueriesSatisfy_bind
      (avoid_sequenceFin Q (fun j : Fin n => f j.succ) fun j => hf j.succ) fun _ =>
        allQueriesSatisfy_pure _ _

/-- A shared key cell of the seed generation. -/
def SharedCell (q : Query C) : Prop := ∃ L, q = .sharedKeys .seedGen L

theorem avoid_deriveKeys {E : Type} (D : C.Coalition) (parts : C.Party → Parts C) (i : C.Party) (inbox : Mail C E) :
    AllQueriesSatisfy (deriveKeys .seedGen i (normView D parts i inbox)) (RoAvoid SharedCell) := by
  rw [deriveKeys_normView]
  refine allQueriesSatisfy_bind (avoid_hashQuery _ _ fun ⟨L, h⟩ => by cases h) fun _ => ?_
  refine allQueriesSatisfy_bind (avoid_mapM _ _ (fun T => ?_) _) fun _ => ?_
  · split_ifs
    · exact avoid_hashQuery _ _ fun ⟨L, h⟩ => by simp [termAddress] at h
    · exact allQueriesSatisfy_pure _ _
  refine allQueriesSatisfy_bind (avoid_mapM _ _ (fun j => ?_) _) fun _ => allQueriesSatisfy_pure _ _
  split_ifs
  · exact allQueriesSatisfy_pure _ _
  · exact avoid_hashQuery _ _ fun ⟨L, h⟩ => by cases h

variable {E : Type} (D : C.Coalition) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
  (d : C.Party → Option Unit) (sent : C.Party → C.Party → Option (Msg E))

theorem passOne_avoid (j : C.Party) :
    AllQueriesSatisfy (passOne D parts committed d sent j) (LocalAvoid SharedCell) := by
  unfold passOne
  by_cases hj : j ∈ D.1
  · rw [ite_eq_left hj]
    exact allQueriesSatisfy_pure _ _
  rw [ite_eq_right hj]
  rcases d j with _ | u
  · exact allQueriesSatisfy_pure _ _
  dsimp only
  by_cases ha : anyAbort (blockInbox D parts d sent j) = true
  · rw [ite_eq_left ha]
    exact allQueriesSatisfy_pure _ _
  rw [ite_eq_right ha]
  refine allQueriesSatisfy_bind (avoid_liftComp _ _ (avoid_mapM _ _ (fun k => ?_) _)) fun opens => ?_
  · exact avoid_hashQuery _ _ fun ⟨L, h⟩ => by simp [openAddress] at h
  split_ifs
  · exact allQueriesSatisfy_bind (avoid_liftComp _ _ (avoid_deriveKeys D parts j _)) fun _ => allQueriesSatisfy_pure _ _
  · exact allQueriesSatisfy_pure _ _

theorem passTwo_noStream (j : C.Party) (k : Option (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))) :
    AllQueriesSatisfy (passTwo j k) (LocalAvoid (fun _ => False)) := by
  rcases k with _ | keys
  · exact allQueriesSatisfy_pure _ _
  · exact allQueriesSatisfy_bind (avoid_liftComp _ _ (avoid_mapM _ _ (fun l => avoid_hashQuery _ _ id) _)) fun _ =>
      allQueriesSatisfy_pure _ _

theorem localBlock_noStream : AllQueriesSatisfy (localBlock D parts committed d sent) NoStream := by
  unfold localBlock
  refine avoid_sequenceFin _ _ fun j => allQueriesSatisfy_bind ?_ fun k => ?_
  · exact (passOne_avoid D parts committed d sent j).mono fun t ht => noStream_of_avoid _ t ht
  · exact (passTwo_noStream j k).mono fun t ht => noStream_of_avoid _ t ht

end Calls

/-! ## The support facts -/

section Support

theorem forall₂_getD_idxOf {α β : Type} [BEq α] [LawfulBEq α] (R : α → β → Prop) (xs : List α) (ys : List β)
    (h : List.Forall₂ R xs ys) (x : α) (hx : x ∈ xs) (d : β) : R x (ys.getD (xs.idxOf x) d) := by
  rw [List.forall₂_iff_get] at h
  obtain ⟨hlen, hget⟩ := h
  have hl : xs.idxOf x < xs.length := List.idxOf_lt_length_iff.mpr hx
  have hl' : xs.idxOf x < ys.length := hlen ▸ hl
  have e := hget (xs.idxOf x) hl hl'
  simp only [List.get_eq_getElem, List.getElem_idxOf] at e
  rw [List.getD_eq_getElem _ _ hl']
  exact e

variable (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput)

theorem localAnswer_unif_run (n : ℕ) (c : HashCache C) :
    ∀ z ∈ support ((localAnswer (C := C) prims (.inl n)).run c), z.2 = c := by
  obtain ⟨p, hp⟩ : ∃ p, localAnswer (C := C) prims (.inl n) = StateT.lift p := ⟨_, rfl⟩
  intro z hz
  rw [hp, StateT.run_lift] at hz
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
  obtain ⟨a, -, rfl⟩ := hz
  rfl

theorem compLocal_step_mono (t : (LocalSpec C).Domain) (c : HashCache C) :
    ∀ z ∈ support ((compLocal prims D parts seed t).run c), c ≤ z.2 := by
  intro z hz
  rcases t with n | q | x
  · rw [localAnswer_unif_run prims n c z hz]
  · simp only [compLocal] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
    · exact (roImpl_support prims (.inl q) c z hz).1
  · exact (roImpl_support prims (.inr x) c z hz).1

theorem compLocal_run_mono {α : Type} (X : OracleComp (LocalSpec C) α) (c : HashCache C) :
    ∀ z ∈ support ((simulateQ (compLocal prims D parts seed) X).run c), c ≤ z.2 :=
  OracleComp.simulateQ_run_preservesInv _ (fun s => c ≤ s)
    (fun t s hs z hz => le_trans hs (compLocal_step_mono prims D parts seed t s z hz)) X c le_rfl

theorem hashAnswer_keep_other (q q' : Query C) (hne : q' ≠ q) (c : HashCache C) :
    ∀ z ∈ support ((hashAnswer prims q).run c), z.2 q' = c q' := by
  intro z hz
  by_cases hf : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hf
    rw [hashAnswer_of_isFixed prims hm, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  · rw [hashAnswer_of_not_isFixed prims hf] at hz
    rcases hc : c q with _ | u
    · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc] at hz
      erw [support_map, Set.mem_image] at hz
      obtain ⟨v, -, rfl⟩ := hz
      exact QueryCache.cacheQuery_of_ne _ _ hne
    · rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]

theorem compLocal_step_keep (P : Query C → Prop) (t : (LocalSpec C).Domain) (ht : LocalAvoid P t) (c : HashCache C) :
    ∀ z ∈ support ((compLocal prims D parts seed t).run c), ∀ q, P q → z.2 q = c q := by
  intro z hz q hq
  rcases t with n | q0 | x
  · rw [localAnswer_unif_run prims n c z hz]
  · simp only [compLocal] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
    · exact hashAnswer_keep_other prims q0 q (fun e => ht (e ▸ hq)) c z hz
  · exact absurd ht id

theorem compLocal_run_keep (P : Query C → Prop) {α : Type} (X : OracleComp (LocalSpec C) α)
    (hX : AllQueriesSatisfy X (LocalAvoid P)) (c : HashCache C) :
    ∀ z ∈ support ((simulateQ (compLocal prims D parts seed) X).run c), ∀ q, P q → z.2 q = c q := by
  induction X using OracleComp.inductionOn generalizing c with
  | pure a =>
    intro z hz q _
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hX
    intro z hz q hq
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query, OracleQuery.cont_query,
      monadLift_self, support_bind, Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    rw [ih p.1 (hX.2 p.1) p.2 z hz q hq, compLocal_step_keep prims D parts seed P t hX.1 c p hp q hq]

/-- A support fact of each step of a list, kept along the later steps, holds for the whole list. -/
theorem compLocal_mapM_support {β γ : Type} (f : β → OracleComp (LocalSpec C) γ) (Q : β → γ → HashCache C → Prop)
    (hmono : ∀ x a c c', c ≤ c' → Q x a c → Q x a c')
    (hf : ∀ x c, ∀ z ∈ support ((simulateQ (compLocal prims D parts seed) (f x)).run c), Q x z.1 z.2) :
    ∀ (xs : List β) (c : HashCache C), ∀ z ∈ support ((simulateQ (compLocal prims D parts seed) (xs.mapM f)).run c),
      List.Forall₂ (fun x a => Q x a z.2) xs z.1
  | [], c, z, hz => by
    simp only [List.mapM_nil, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact List.Forall₂.nil
  | x :: xs, c, z, hz => by
    simp only [List.mapM_cons, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨p, hp, r, hr, rfl⟩ := hz
    exact List.Forall₂.cons (hmono _ _ _ _ (compLocal_run_mono prims D parts seed _ _ r hr) (hf x c p hp))
      (compLocal_mapM_support f Q hmono hf xs p.2 r hr)

/-- A support fact of each step of a sequence, kept along the later steps, holds for the sequence. -/
theorem compLocal_sequenceFin_support {γ : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp (LocalSpec C) γ) (Q : Fin n → γ → HashCache C → Prop),
    (∀ j a c c', c ≤ c' → Q j a c → Q j a c') →
    (∀ j c, ∀ z ∈ support ((simulateQ (compLocal prims D parts seed) (f j)).run c), Q j z.1 z.2) →
    ∀ (c : HashCache C), ∀ z ∈ support ((simulateQ (compLocal prims D parts seed) (OverPermutation.sequenceFin f)).run c),
      ∀ j, Q j (z.1 j) z.2
  | 0, f, Q, _, _, c, z, _, j => j.elim0
  | n + 1, f, Q, hmono, hf, c, z, hz, j => by
    simp only [OverPermutation.sequenceFin, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
      support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨p, hp, r, hr, rfl⟩ := hz
    cases j using Fin.cases with
    | zero => exact hmono 0 _ _ _ (compLocal_run_mono prims D parts seed _ _ r hr) (hf 0 c p hp)
    | succ j =>
      exact compLocal_sequenceFin_support (fun j : Fin n => f j.succ) (fun j => Q j.succ)
        (fun j => hmono j.succ) (fun j => hf j.succ) p.2 r hr j

end Support

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.compLocal_sequenceFin_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.compLocal_sequenceFin_support

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.revealBlock_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.revealBlock_eq
