import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Provenance
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Merge

/-!
# The parts of the step on the two worlds

* `addSalt_addSalt` states that the shift of a salt of 256 bits is an involution, and
  `addSalt_mem_fullHiddenSalts` moves a full hidden salt to a full hidden salt of the shifted table.
* `shiftTable δ table` is the separate table seen through the shift. Its cell `(salt, h)` is the cell
  `(salt + δ, h)` of the table, for a salt of 256 bits.
* `QueueInv` states that each queue entry with a hidden name has a term name and records the cells of
  its place from the position 0. `ProvInv` adds that each cell of the separate table is under a full
  hidden salt and that each logged digest cell has a value in the hash cache.
* `shiftedWorld` is `loggedWorld` under the rewrite `provShift`, with the queue in the state.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The shift of a salt -/

theorem length_addSalt (δ : Fin 256 → Bit) (salt : List Bit) : (addSalt δ salt).length = 256 :=
  List.length_ofFn

theorem getElem_addSalt (δ : Fin 256 → Bit) (salt : List Bit) (k : ℕ) (hk : k < (addSalt δ salt).length) :
    (addSalt δ salt)[k] = salt.getD k 0 + δ ⟨k, by rwa [length_addSalt] at hk⟩ := by
  simp only [addSalt, List.getElem_ofFn]

theorem addSalt_addSalt (δ : Fin 256 → Bit) (salt : List Bit) (h : salt.length = 256) :
    addSalt δ (addSalt δ salt) = salt := by
  refine List.ext_getElem (by rw [length_addSalt, h]) fun k h₁ h₂ => ?_
  rw [getElem_addSalt]
  have hk : k < (addSalt δ salt).length := by rw [length_addSalt]; rwa [h] at h₂
  rw [List.getD_eq_getElem _ _ hk, getElem_addSalt, List.getD_eq_getElem _ _ h₂, add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

theorem length_placeSalt (cells : HiddenCache C) (name : KeyName C) (key : HashOutput) (ρ : ℕ) :
    (placeSalt cells name key ρ).length = 256 := by
  simp [placeSalt]

theorem getElem_placeSalt (cells : HiddenCache C) (name : KeyName C) (key : HashOutput) (ρ : ℕ) (k : ℕ)
    (hk : k < 256) :
    (placeSalt cells name key ρ)[k]'(by rw [length_placeSalt]; exact hk) = (cells ((name, key), ρ, 2, k)).getD 0 := by
  have h : ∀ f : ℕ → Bit, ((List.range 256).map f)[k]'(by simpa using hk) = f k := fun f => by simp
  exact h fun position => (cells ((name, key), ρ, 2, position)).getD 0

theorem length_of_mem_fullHiddenSalts {D : C.Coalition} {hidden : HiddenCache C} {salt : List Bit}
    (h : salt ∈ fullHiddenSalts D hidden) : salt.length = 256 := by
  obtain ⟨T, key, ρ, -, -, rfl⟩ := h
  exact length_placeSalt _ _ _ _

/-- A full hidden salt plus `δ` is a full hidden salt of the table shifted by `δ`. -/
theorem addSalt_mem_fullHiddenSalts (D : C.Coalition) (δ : Fin 256 → Bit) {hidden : HiddenCache C}
    {salt : List Bit} (h : salt ∈ fullHiddenSalts D hidden) :
    addSalt δ salt ∈ fullHiddenSalts D (shiftCache (saltShift D δ) hidden) := by
  obtain ⟨T, key, ρ, hT, hfull, rfl⟩ := h
  refine ⟨T, key, ρ, hT, fun position hp => ?_, ?_⟩
  · simpa [shiftCache_apply] using hfull position hp
  · refine List.ext_getElem (by rw [length_addSalt, length_placeSalt]) fun k h₁ h₂ => ?_
    have hk : k < 256 := by rwa [length_addSalt] at h₁
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hfull k hk)
    have hσ : saltShift D δ ((.term T, key), ρ, 2, k) = δ ⟨k, hk⟩ := by
      simp [saltShift, hT, hk]
    rw [getElem_addSalt, List.getD_eq_getElem _ _ (by rw [length_placeSalt]; exact hk)]
    rw [getElem_placeSalt _ _ _ _ _ hk, getElem_placeSalt _ _ _ _ _ hk, shiftCache_apply, hv, hσ]
    rfl

/-! ## The separate table through the shift -/

/-- The separate table seen through the shift. A cell `(salt, h)` with a salt of 256 bits is the cell
`(salt + δ, h)` of the table, and each other cell is empty. -/
def shiftTable (δ : Fin 256 → Bit) (table : SaltTable) : SaltTable :=
  QueryCache.ofFn fun p => if p.1.length = 256 then table (addSalt δ p.1, p.2) else none

theorem shiftTable_apply (δ : Fin 256 → Bit) (table : SaltTable) (salt : List Bit) (history : HashOutput) :
    shiftTable δ table (salt, history) =
      if salt.length = 256 then table (addSalt δ salt, history) else none := rfl

theorem shiftTable_empty (δ : Fin 256 → Bit) : shiftTable δ (∅ : SaltTable) = ∅ := by
  refine QueryCache.ext fun p => ?_
  simp only [shiftTable, QueryCache.ofFn_apply, QueryCache.empty_apply, ite_self]

theorem shiftTable_addSalt (δ : Fin 256 → Bit) (table : SaltTable) (salt : List Bit) (history : HashOutput)
    (h : salt.length = 256) : shiftTable δ table (addSalt δ salt, history) = table (salt, history) := by
  rw [shiftTable_apply, ite_eq_left (length_addSalt δ salt), addSalt_addSalt δ salt h]

theorem shiftTable_cacheQuery (δ : Fin 256 → Bit) (table : SaltTable) (salt : List Bit) (history : HashOutput)
    (u : HashOutput) (h : salt.length = 256) :
    shiftTable δ (table.cacheQuery (salt, history) u) = (shiftTable δ table).cacheQuery (addSalt δ salt, history) u := by
  refine QueryCache.ext fun p => ?_
  obtain ⟨salt', history'⟩ := p
  by_cases e : (salt', history') = (addSalt δ salt, history)
  · cases e
    rw [QueryCache.cacheQuery_self, shiftTable_addSalt δ _ salt history h, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ e, shiftTable_apply, shiftTable_apply]
    split_ifs with hl
    · refine QueryCache.cacheQuery_of_ne _ _ fun e' => e ?_
      simp only [Prod.mk.injEq] at e' ⊢
      refine ⟨?_, e'.2⟩
      rw [← e'.1, addSalt_addSalt δ salt' hl]
    · rfl

/-- A cell of the shifted table with a value is under a full hidden salt of the shifted hidden table,
when each cell of the table is under a full hidden salt. -/
theorem mem_of_shiftTable (D : C.Coalition) (δ : Fin 256 → Bit) {table : SaltTable} {hidden : HiddenCache C}
    (hT : ∀ salt history, table (salt, history) ≠ none → salt ∈ fullHiddenSalts D hidden)
    {salt : List Bit} {history : HashOutput} (h : shiftTable δ table (salt, history) ≠ none) :
    salt ∈ fullHiddenSalts D (shiftCache (saltShift D δ) hidden) := by
  rw [shiftTable_apply] at h
  split_ifs at h with hl
  · have hm := addSalt_mem_fullHiddenSalts D δ (hT _ _ h)
    rwa [addSalt_addSalt δ salt hl] at hm
  · exact absurd rfl h

/-! ## The invariant of the queue -/

/-- The bits of a queue entry are the cells of its place in the hidden table, from the position 0. -/
def EntryCells (hidden : HiddenCache C) (entry : ((KeyName C × HashOutput) × ℕ) × List Bit) : Prop :=
  ∀ k (hk : k < entry.2.length), hidden (entry.1.1, entry.1.2, 2, k) = some entry.2[k]

/-- Each queue entry with a hidden name has a term name and records the cells of its place. -/
def QueueInv (D : C.Coalition) (hidden : HiddenCache C) (queue : ProvQueue C) : Prop :=
  ∀ entry ∈ queue, Hidden D entry.1.1.1 → (∃ T, entry.1.1.1 = .term T) ∧ EntryCells hidden entry

theorem queueInv_nil (D : C.Coalition) (hidden : HiddenCache C) : QueueInv D hidden [] :=
  fun _ h => absurd h List.not_mem_nil

theorem QueueInv.tail {D : C.Coalition} {hidden : HiddenCache C} {entry : ((KeyName C × HashOutput) × ℕ) × List Bit}
    {rest : ProvQueue C} (h : QueueInv D hidden (entry :: rest)) : QueueInv D hidden rest :=
  fun e he => h e (List.mem_cons_of_mem _ he)

theorem QueueInv.grows {D : C.Coalition} {hidden hidden' : HiddenCache C} {queue : ProvQueue C}
    (h : QueueInv D hidden queue) (hg : Grows hidden hidden') : QueueInv D hidden' queue := fun e he hH =>
  ⟨(h e he hH).1, fun k hk => hg _ _ ((h e he hH).2 k hk)⟩

/-- The salt of a private entry of the queue is a full hidden salt. -/
theorem QueueInv.mem_of_private {D : C.Coalition} {hidden : HiddenCache C} {queue : ProvQueue C}
    (h : QueueInv D hidden queue) {entry : ((KeyName C × HashOutput) × ℕ) × List Bit} (he : entry ∈ queue)
    {salt : List Bit} (hp : Private D entry salt) : salt ∈ fullHiddenSalts D hidden := by
  obtain ⟨hH, hlen, rfl⟩ := hp
  obtain ⟨⟨T, hT⟩, hc⟩ := h entry he hH
  obtain ⟨⟨⟨name, key⟩, ρ⟩, bits⟩ := entry
  simp only at hT hH hlen
  subst hT
  refine ⟨T, key, ρ, hH, fun position hp => ?_, ?_⟩
  · rw [hc position (by rw [hlen]; exact hp)]
    simp
  · refine List.ext_getElem (by rw [hlen, length_placeSalt]) fun k h₁ h₂ => ?_
    rw [getElem_placeSalt _ _ _ _ _ (by rwa [hlen] at h₁), hc k h₁]
    rfl

/-- A read of a stream keeps the invariant of the queue, when the hidden table grows and holds the
answer of a hidden read at its cell. -/
theorem QueueInv.push {D : C.Coalition} {hidden hidden' : HiddenCache C} {queue : ProvQueue C}
    (h : QueueInv D hidden queue) (hg : Grows hidden hidden') (x : PrgInput C) (b : Bit)
    (hx : Hidden D x.1 → hidden' (streamCell x) = some b) : QueueInv D hidden' (pushRead x b queue) := by
  have h' := h.grows hg
  obtain ⟨name, key, ρ, idx, pos⟩ := x
  cases name with
  | term T =>
    simp only [pushRead]
    split_ifs with h2 h0
    · subst h2 h0
      intro e he hH
      rcases List.mem_append.mp he with he | he
      · exact h' e he hH
      · rw [List.mem_singleton] at he
        subst he
        refine ⟨⟨T, rfl⟩, fun k hk => ?_⟩
        simp only [List.length_singleton, Nat.lt_one_iff] at hk
        subst hk
        exact hx hH
    · split
      · rename_i entry hlast
        split_ifs with hc
        · intro e he hH
          rcases List.mem_append.mp he with he | he
          · exact h' e (List.dropLast_subset _ he) hH
          · rw [List.mem_singleton] at he
            subst he
            obtain ⟨hT, hcells⟩ := h' entry (List.mem_of_getLast? hlast) hH
            refine ⟨hT, fun k hk => ?_⟩
            simp only [List.length_append, List.length_singleton] at hk
            rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
            · rw [List.getElem_append_left hk]
              exact hcells k hk
            · subst hk
              rw [List.getElem_append_right (le_refl _)]
              simp only [Nat.sub_self, List.getElem_singleton]
              obtain ⟨he1, he2⟩ := hc
              rw [he2, he1]
              subst h2
              exact hx (by rw [he1] at hH; exact hH)
        · exact h'
      · exact h'
    · exact h'
  | parameter => exact h'
  | pair p => exact h'

/-- The invariant of the states of `provWorld`. The queue has `QueueInv`, each cell of the separate
table is under a full hidden salt, and each logged digest cell has a value in the hash cache. -/
def ProvInv (D : C.Coalition) (st : ProvState C) : Prop :=
  QueueInv D st.1.1.2 st.2.1 ∧
    (∀ salt history, st.2.2 (salt, history) ≠ none → salt ∈ fullHiddenSalts D st.1.1.2) ∧
    ∀ salt history, Query.digest salt history ∈ st.1.2 → st.1.1.1 (.digest salt history) ≠ none

theorem provInv_provStart (D : C.Coalition) : ProvInv D (provStart : ProvState C) :=
  ⟨queueInv_nil D _, fun _ _ h => absurd rfl h, fun _ _ h => absurd h List.not_mem_nil⟩

/-! ## The calls of the two worlds -/

variable (prims : Primitives)

theorem provWorld_digest_cons (D : C.Coalition) (salt : List Bit) (history : HashOutput) (st : ProvState C)
    (entry : ((KeyName C × HashOutput) × ℕ) × List Bit) (rest : ProvQueue C) (hq : st.2.1 = entry :: rest) :
    (provWorld prims D (.inr (.inr (.inl (.digest salt history))))).run st =
      if Private D entry salt then
        (fun r => (r.1, (st.1, rest, r.2))) <$>
          ((((List Bit × HashOutput) →ₒ HashOutput).randomOracle (salt, history)).run st.2.2)
      else (fun r => (r.1, (r.2, rest, st.2.2))) <$>
        (loggedWorld prims D (.inr (.inr (.inl (.digest salt history))))).run st.1 := by
  obtain ⟨st₁, queue, table⟩ := st
  simp only at hq
  subst hq
  rfl

theorem provWorld_digest_nil (D : C.Coalition) (salt : List Bit) (history : HashOutput) (st : ProvState C)
    (hq : st.2.1 = []) :
    (provWorld prims D (.inr (.inr (.inl (.digest salt history))))).run st =
      (fun r => (r.1, (r.2, [], st.2.2))) <$> (loggedWorld prims D (.inr (.inr (.inl (.digest salt history))))).run st.1 := by
  obtain ⟨st₁, queue, table⟩ := st
  simp only at hq
  subst hq
  rfl

theorem provWorld_stream (D : C.Coalition) (x : PrgInput C) (st : ProvState C) :
    (provWorld prims D (.inr (.inr (.inr x)))).run st =
      (fun r => (r.1, (r.2, pushRead x r.1 st.2.1, st.2.2))) <$> (loggedWorld prims D (.inr (.inr (.inr x)))).run st.1 :=
  rfl

theorem provWorld_other (D : C.Coalition) (t : (WorldSpec C).Domain)
    (h₁ : ∀ salt history, t ≠ .inr (.inr (.inl (.digest salt history)))) (h₂ : ∀ x, t ≠ .inr (.inr (.inr x)))
    (st : ProvState C) :
    (provWorld prims D t).run st = (fun r => (r.1, (r.2, st.2))) <$> (loggedWorld prims D t).run st.1 := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  any_goals rfl
  · cases q
    all_goals first | rfl | exact absurd rfl (h₁ _ _)
  · exact absurd rfl (h₂ x)

/-- `loggedWorld` under the rewrite `provShift`, with the queue in the state. -/
def shiftedWorld (D : C.Coalition) (δ : Fin 256 → Bit) :
    QueryImpl (WorldSpec C) (StateT (ProvQueue C × LogState C) ProbComp) :=
  SigningCompilerUntil.fuse (provShift D δ) (loggedWorld prims D)

theorem shiftedWorld_run (D : C.Coalition) (δ : Fin 256 → Bit) (t : (WorldSpec C).Domain) (queue : ProvQueue C)
    (st : LogState C) (t' : (WorldSpec C).Domain) (f : (WorldSpec C).Range t' → (WorldSpec C).Range t × ProvQueue C)
    (h : (provShift D δ t).run queue =
      f <$> (query (spec := WorldSpec C) t' : OracleComp (WorldSpec C) ((WorldSpec C).Range t'))) :
    (shiftedWorld prims D δ t).run (queue, st) =
      (fun z => ((f z.1).1, ((f z.1).2, z.2))) <$> (loggedWorld prims D t').run st := by
  change (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ (loggedWorld prims D) ((provShift D δ t).run queue)).run st = _
  rw [h, simulateQ_map, simulateQ_HasQuery_query, StateT.run_map, Functor.map_map]

theorem shiftedWorld_digest_cons (D : C.Coalition) (δ : Fin 256 → Bit) (salt : List Bit) (history : HashOutput)
    (entry : ((KeyName C × HashOutput) × ℕ) × List Bit) (rest : ProvQueue C) (st : LogState C) :
    (shiftedWorld prims D δ (.inr (.inr (.inl (.digest salt history))))).run (entry :: rest, st) =
      (fun z => (z.1, (rest, z.2))) <$> (loggedWorld prims D (.inr (.inr (.inl
        (.digest (if Private D entry salt then addSalt δ salt else salt) history))))).run st :=
  shiftedWorld_run prims D δ (.inr (.inr (.inl (.digest salt history)))) (entry :: rest) st (.inr (.inr (.inl
    (.digest (if Private D entry salt then addSalt δ salt else salt) history)))) (fun r => (r, rest)) rfl

theorem shiftedWorld_digest_nil (D : C.Coalition) (δ : Fin 256 → Bit) (salt : List Bit) (history : HashOutput)
    (st : LogState C) :
    (shiftedWorld prims D δ (.inr (.inr (.inl (.digest salt history))))).run ([], st) =
      (fun z => (z.1, ([], z.2))) <$> (loggedWorld prims D (.inr (.inr (.inl (.digest salt history))))).run st :=
  shiftedWorld_run prims D δ (.inr (.inr (.inl (.digest salt history)))) [] st (.inr (.inr (.inl (.digest salt history))))
    (fun r => (r, [])) rfl

theorem shiftedWorld_stream (D : C.Coalition) (δ : Fin 256 → Bit) (x : PrgInput C) (queue : ProvQueue C)
    (st : LogState C) :
    (shiftedWorld prims D δ (.inr (.inr (.inr x)))).run (queue, st) =
      (fun z => (z.1, (pushRead x z.1 queue, z.2))) <$> (loggedWorld prims D (.inr (.inr (.inr x)))).run st :=
  shiftedWorld_run prims D δ (.inr (.inr (.inr x))) queue st (.inr (.inr (.inr x))) (fun b => (b, pushRead x b queue)) rfl

theorem shiftedWorld_other (D : C.Coalition) (δ : Fin 256 → Bit) (t : (WorldSpec C).Domain)
    (h₁ : ∀ salt history, t ≠ .inr (.inr (.inl (.digest salt history)))) (h₂ : ∀ x, t ≠ .inr (.inr (.inr x)))
    (queue : ProvQueue C) (st : LogState C) :
    (shiftedWorld prims D δ t).run (queue, st) = (fun z => (z.1, (queue, z.2))) <$> (loggedWorld prims D t).run st := by
  refine shiftedWorld_run prims D δ t queue st t (fun r => (r, queue)) ?_
  rcases t with ((u | q | x) | p) | (u | q | x)
  any_goals rfl
  · cases q
    all_goals first | rfl | exact absurd rfl (h₁ _ _)
  · exact absurd rfl (h₂ x)

/-! ## The growth of the state and the named shifts -/

theorem provWorld_grows (D : C.Coalition) (t : (WorldSpec C).Domain) (st : ProvState C) :
    ∀ z ∈ support ((provWorld prims D t).run st), Grows st.1.1.1 z.2.1.1.1 ∧ Grows st.1.1.2 z.2.1.1.2 := by
  intro z hz
  by_cases h₁ : ∃ salt history, t = .inr (.inr (.inl (.digest salt history)))
  · obtain ⟨salt, history, rfl⟩ := h₁
    rcases hq : st.2.1 with _ | ⟨entry, rest⟩
    · rw [provWorld_digest_nil prims D salt history st hq] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact loggedWorld_grows prims D _ _ w hw
    · rw [provWorld_digest_cons prims D salt history st entry rest hq] at hz
      split_ifs at hz
      · simp only [support_map, Set.mem_image] at hz
        obtain ⟨w, _, rfl⟩ := hz
        exact ⟨Grows.refl _, Grows.refl _⟩
      · simp only [support_map, Set.mem_image] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        exact loggedWorld_grows prims D _ _ w hw
  by_cases h₂ : ∃ x, t = .inr (.inr (.inr x))
  · obtain ⟨x, rfl⟩ := h₂
    rw [provWorld_stream] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact loggedWorld_grows prims D _ _ w hw
  push Not at h₁ h₂
  rw [provWorld_other prims D t (fun s h e => h₁ s h e) (fun x e => h₂ x e)] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact loggedWorld_grows prims D _ _ w hw

theorem Grows.shiftCache {σ : HiddenCell C → Bit} {hidden hidden' : HiddenCache C} (hg : Grows hidden hidden') :
    Grows (shiftCache σ hidden) (shiftCache σ hidden') := by
  intro c v hv
  rw [shiftCache_apply] at hv ⊢
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hv
  rw [hg c w hw]
  rfl

/-- The hash cache holds a digest cell under a full hidden salt of the hidden table shifted by `δ`.
This is the membership `δ ∈ named D st`. -/
def NamedBy (D : C.Coalition) (δ : Fin 256 → Bit) (st : ProvState C) : Prop :=
  ∃ (salt : List Bit) (history : HashOutput), st.1.1.1 (.digest salt history) ≠ none ∧
    salt ∈ fullHiddenSalts D (shiftCache (saltShift D δ) st.1.1.2)

theorem mem_named (D : C.Coalition) (δ : Fin 256 → Bit) (st : ProvState C) : δ ∈ named D st ↔ NamedBy D δ st := by
  simp only [named, Finset.mem_filter, Finset.mem_univ, true_and, NamedBy]

theorem NamedBy.of_grows {D : C.Coalition} {δ : Fin 256 → Bit} {st st' : ProvState C} (h : NamedBy D δ st)
    (gm : Grows st.1.1.1 st'.1.1.1) (gh : Grows st.1.1.2 st'.1.1.2) : NamedBy D δ st' := by
  obtain ⟨salt, history, hc, hs⟩ := h
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hc
  exact ⟨salt, history, by rw [gm _ v hv]; simp, fullHiddenSalts_mono D gh.shiftCache hs⟩

/-- A named shift stays named along a call of `provWorld`. -/
theorem namedBy_sticky (D : C.Coalition) (δ : Fin 256 → Bit) (t : (WorldSpec C).Domain) (st : ProvState C)
    (h : NamedBy D δ st) : ∀ z ∈ support ((provWorld prims D t).run st), NamedBy D δ z.2 := fun z hz =>
  h.of_grows (provWorld_grows prims D t st z hz).1 (provWorld_grows prims D t st z hz).2

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.QueueInv.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.QueueInv.push

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.shiftTable_cacheQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.shiftTable_cacheQuery
