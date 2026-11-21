import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.CountProgram

/-!
# The count of the named shifts at the end of the game in `provWorld`

A call of `provWorld` leaves the state of `loggedWorld` as it is, or moves it by one call of
`loggedWorld` (`provWorld_log`). A call of `loggedWorld` changes the hash cache only at the cell of the
call or at a key of a stream (`loggedWorld_cacheOnly`). So a world program adds at most one digest cell
for each call with a digest cell, and at most one place for each call of `SaltDraw`
(`encard_le_of_step`, a general count of a set on the state that grows by at most one at each call of
a predicate).

A named shift is fixed by a digest cell and a full hidden place. For the bits `b` of the place and the
salt `s` of the cell, `δ k = s[k] - b[k]` (`named_subset`). So the named shifts are at most the digest
cells times the places, and `saltProvCount` is `SaltProvCount`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.SetupBudgets (HonestP)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## A count of a set on the state of a world -/

/-- A set on the state that grows at each call by a set of at most one element, and by none at a call
that is not a call of `P`, grows by at most `n` along a program with at most `n` calls of `P`. -/
theorem encard_le_of_step {W X : Type} (impl : QueryImpl (WorldSpec C) (StateT W ProbComp)) (f : W → Set X)
    (P : (WorldSpec C).Domain → Prop) (G : (WorldSpec C).Domain → Set X)
    (hG : ∀ t, (G t).encard ≤ if P t then 1 else 0)
    (step : ∀ t w, ∀ z ∈ support ((impl t).run w), f z.2 ⊆ f w ∪ G t) {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∀ (n : ℕ), IsQueryBoundP oa P n → ∀ (w : W),
      ∀ z ∈ support ((simulateQ impl oa).run w), (f z.2).encard ≤ (f w).encard + n := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ w z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact le_self_add
  | query_bind t k ih =>
    intro n hn w z hz
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨r, hr, hz⟩ := hz
    have h1 : (f r.2).encard ≤ (f w).encard + if P t then 1 else 0 :=
      (Set.encard_le_encard (step t w r hr)).trans ((Set.encard_union_le _ _).trans (add_le_add le_rfl (hG t)))
    by_cases ht : P t
    · have hpos := hn.1.resolve_left (not_not.2 ht)
      have h2 := ih r.1 (n - 1) (by simpa [ht] using hn.2 r.1) r.2 z hz
      simp only [ht, ↓reduceIte] at h1
      calc (f z.2).encard ≤ (f r.2).encard + (n - 1 : ℕ) := h2
        _ ≤ (f w).encard + 1 + (n - 1 : ℕ) := add_le_add h1 le_rfl
        _ = (f w).encard + n := by
          rw [add_assoc]
          congr 1
          norm_cast
          omega
    · have h2 := ih r.1 n (by simpa [ht] using hn.2 r.1) r.2 z hz
      simp only [ht, ↓reduceIte, add_zero] at h1
      exact h2.trans (add_le_add h1 le_rfl)

/-! ## The cells that a call changes -/

variable (prims : Primitives) (D : C.Coalition)

theorem hashAnswer_other (q : Query C) (c : HashCache C) :
    ∀ z ∈ support ((hashAnswer prims q).run c), ∀ q', q' ≠ q → z.2 q' = c q' := by
  intro z hz q' hq'
  cases q with
  | hash input =>
    simp only [hashAnswer] at hz
    split_ifs at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      rfl
    · exact randomOracle_other _ _ _ hz q' hq'
  | _ => exact randomOracle_other _ _ _ hz q' hq'

theorem localAnswer_other (t : (LocalSpec C).Domain) (c : HashCache C) :
    ∀ z ∈ support ((localAnswer prims t).run c), ∀ q, z.2 q ≠ c q →
      t = .inr (.inl q) ∨ ∃ key, q = .streamKey key := by
  intro z hz q hq
  rcases t with u | q' | x
  · simp [localAnswer, unifFwdImpl] at hz
    obtain ⟨_, rfl⟩ := hz
    exact absurd rfl hq
  · left
    by_contra hne
    exact hq (hashAnswer_other prims q' c z hz q fun e => hne (by rw [e]))
  · right
    simp only [localAnswer, QueryImpl.add_apply_inr, prgAnswer, StateT.run_bind, support_bind,
      Set.mem_iUnion] at hz
    obtain ⟨w, hw, hz⟩ := hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    by_contra hne
    push Not at hne
    exact hq (hashAnswer_other prims _ c w hw q fun e => hne x.2.1 e)

theorem programAnswer_other (x : Query C × HashOutput) (c : HashCache C) :
    ∀ z ∈ support ((programAnswer x).run c), ∀ q, z.2 q ≠ c q → q = x.1 := by
  intro z hz q hq
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact absurd rfl hq
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    by_contra hne
    exact hq (QueryCache.cacheQuery_of_ne _ _ hne)

/-- A call of `loggedWorld` makes a new digest cell only at its own digest cell. -/
theorem loggedWorld_cacheOnly (t : (WorldSpec C).Domain) (w : LogState C) :
    ∀ z ∈ support ((loggedWorld prims D t).run w), ∀ (salt : List Bit) (history : HashOutput),
      z.2.1.1 (.digest salt history) ≠ w.1.1 (.digest salt history) → callCell t = some (salt, history) := by
  intro z hz salt history hd
  simp only [loggedWorld, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  rcases t with (u | p) | u
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    rw [localProgram_inl] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    rcases localAnswer_other prims u _ r' hr' _ hd with rfl | ⟨key, hk⟩
    · rfl
    · cases hk
  · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
    rw [localProgram_inr] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    have e := programAnswer_other p _ r' hr' _ hd
    obtain ⟨q, v⟩ := p
    dsimp only at e
    subst e
    rfl
  · rcases u with n | q | x
    · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      rcases localAnswer_other prims (Sum.inl n) _ r' hr' _ hd with h | ⟨key, hk⟩
      · cases h
      · cases hk
    · simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      rcases localAnswer_other prims (Sum.inr (Sum.inl q)) _ r' hr' _ hd with h | ⟨key, hk⟩
      · cases h
        rfl
      · cases hk
    · simp only [streamWorld] at hr
      split_ifs at hr
      · simp only [StateT.run_mk, support_map, Set.mem_image] at hr
        obtain ⟨r', -, rfl⟩ := hr
        exact absurd rfl hd
      · simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hr
        obtain ⟨r', hr', rfl⟩ := hr
        rcases localAnswer_other prims (Sum.inr (Sum.inr x)) _ r' hr' _ hd with h | ⟨key, hk⟩
        · cases h
        · cases hk

/-- A call of `provWorld` leaves the state of `loggedWorld` as it is, or moves it by one call of
`loggedWorld`. -/
theorem provWorld_log (t : (WorldSpec C).Domain) (st : ProvState C) :
    ∀ z ∈ support ((provWorld prims D t).run st),
      z.2.1 = st.1 ∨ ∃ w ∈ support ((loggedWorld prims D t).run st.1), z.2.1 = w.2 := by
  intro z hz
  unfold provWorld at hz
  split at hz
  · simp only [StateT.run_mk] at hz
    split at hz
    · split_ifs at hz
      · simp only [support_map, Set.mem_image] at hz
        obtain ⟨r, -, rfl⟩ := hz
        exact Or.inl rfl
      · simp only [support_map, Set.mem_image] at hz
        obtain ⟨r, hr, rfl⟩ := hz
        exact Or.inr ⟨r, hr, rfl⟩
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      exact Or.inr ⟨r, hr, rfl⟩
  · simp only [StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    exact Or.inr ⟨r, hr, rfl⟩
  · simp only [StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    exact Or.inr ⟨r, hr, rfl⟩

/-! ## The two counts on `provWorld` -/

/-- The digest cells of a hash cache. -/
def digestCells (cache : HashCache C) : Set (List Bit × HashOutput) := {p | cache (.digest p.1 p.2) ≠ none}

/-- The place of a call of `SaltDraw`. -/
def drawPlace (t : (WorldSpec C).Domain) : Set ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) :=
  {d | ∃ x, t = .inr (.inr (.inr x)) ∧ SaltPoint d ∧ d = ((x.1, x.2.1), x.2.2)}

omit prims D in
theorem drawPlace_encard (t : (WorldSpec C).Domain) :
    (drawPlace t).encard ≤ if HonestP SaltDraw t then 1 else 0 := by
  by_cases hP : HonestP SaltDraw t
  · simp only [hP, ↓reduceIte]
    refine Set.encard_le_one_iff.2 fun a b ha hb => ?_
    obtain ⟨x, rfl, -, rfl⟩ := ha
    obtain ⟨y, hy, -, rfl⟩ := hb
    cases hy
    rfl
  · simp only [hP, ↓reduceIte, nonpos_iff_eq_zero, Set.encard_eq_zero]
    refine Set.eq_empty_iff_forall_notMem.2 fun d hd => ?_
    obtain ⟨x, rfl, hs, rfl⟩ := hd
    exact hP hs

omit prims D in
theorem callCell_encard (t : (WorldSpec C).Domain) :
    ({p | callCell t = some p} : Set (List Bit × HashOutput)).encard ≤ if Charged t then 1 else 0 := by
  by_cases hP : Charged t
  · simp only [hP, ↓reduceIte]
    refine Set.encard_le_one_iff.2 fun a b ha hb => ?_
    exact Option.some_injective _ (ha.symm.trans hb)
  · simp only [hP, ↓reduceIte, nonpos_iff_eq_zero, Set.encard_eq_zero]
    refine Set.eq_empty_iff_forall_notMem.2 fun p hp => hP ?_
    change callCell t = some p at hp
    unfold Charged
    rw [hp]
    exact Option.some_ne_none _

theorem provWorld_places (t : (WorldSpec C).Domain) (st : ProvState C) :
    ∀ z ∈ support ((provWorld prims D t).run st), places z.2.1.1.2 ⊆ places st.1.1.2 ∪ drawPlace t := by
  intro z hz d hd
  rcases provWorld_log prims D t st z hz with he | ⟨w, hw, he⟩
  · rw [he] at hd
    exact Or.inl hd
  · rw [he] at hd
    by_cases hdw : w.2.1.2 d = st.1.1.2 d
    · exact Or.inl ⟨hd.1, hdw ▸ hd.2⟩
    · obtain ⟨x, rfl, rfl⟩ := loggedWorld_hidden prims D _ _ w hw d hdw
      exact Or.inr ⟨x, rfl, hd.1, rfl⟩

theorem provWorld_digests (t : (WorldSpec C).Domain) (st : ProvState C) :
    ∀ z ∈ support ((provWorld prims D t).run st),
      digestCells z.2.1.1.1 ⊆ digestCells st.1.1.1 ∪ {p | callCell t = some p} := by
  intro z hz p hp
  rcases provWorld_log prims D t st z hz with he | ⟨w, hw, he⟩
  · rw [he] at hp
    exact Or.inl hp
  · rw [he] at hp
    by_cases hdw : w.2.1.1 (.digest p.1 p.2) = st.1.1.1 (.digest p.1 p.2)
    · exact Or.inl (show st.1.1.1 (.digest p.1 p.2) ≠ none from hdw ▸ hp)
    · exact Or.inr (loggedWorld_cacheOnly prims D t st.1 w hw p.1 p.2 hdw)

/-! ## A named shift is fixed by a digest cell and a place -/

omit prims in
/-- The shift that a digest cell and a place name, with the bits of the place in the table `hidden`. -/
def namedShift (hidden : HiddenCache C) (x : (List Bit × HashOutput) × ((KeyName C × HashOutput) × ℕ × ℕ × ℕ)) :
    Fin 256 → Bit :=
  fun k => x.1.1.getD k.val 0 - (hidden (x.2.1, x.2.2.1, 2, k.val)).getD 0

omit prims D in
theorem placeSalt_getD (cells : HiddenCache C) (name : KeyName C) (key : HashOutput) (ρ k : ℕ) (hk : k < 256) :
    (placeSalt cells name key ρ).getD k 0 = (cells ((name, key), ρ, 2, k)).getD 0 := by
  unfold placeSalt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

omit prims in
theorem named_subset (st : ProvState C) :
    (↑(named D st) : Set (Fin 256 → Bit)) ⊆ namedShift st.1.1.2 '' (digestCells st.1.1.1 ×ˢ places st.1.1.2) := by
  simp only [named, Finset.coe_filter, Finset.mem_univ, true_and]
  intro δ hδ
  obtain ⟨salt, history, hc, T, key, ρ, hT, hfull, rfl⟩ := hδ
  have hcell : ∀ k : Fin 256, ∃ b, st.1.1.2 ((.term T, key), ρ, 2, k.val) = some b := fun k => by
    have h := hfull k.val k.isLt
    simp only [shiftCache_apply, ne_eq, Option.map_eq_none_iff] at h
    exact Option.ne_none_iff_exists'.mp h
  refine ⟨((placeSalt (shiftCache (saltShift D δ) st.1.1.2) (.term T) key ρ, history), ((.term T, key), ρ, 2, 0)),
    ⟨hc, ⟨⟨T, rfl⟩, rfl, rfl⟩, ?_⟩, ?_⟩
  · obtain ⟨b, hb⟩ := hcell ⟨0, by norm_num⟩
    simp only at hb
    rw [hb]
    exact Option.some_ne_none _
  · funext k
    obtain ⟨b, hb⟩ := hcell k
    have hs : saltShift D δ ((.term T, key), ρ, 2, k.val) = δ k := by
      have h : ¬ KnownTo D.1 T ∧ (2 : ℕ) = 2 ∧ k.val < 256 := ⟨hT, rfl, k.isLt⟩
      simp only [saltShift, h, not_false_eq_true, and_self, ↓reduceDIte]
    change (placeSalt (shiftCache (saltShift D δ) st.1.1.2) (.term T) key ρ).getD k.val 0 -
      (st.1.1.2 ((.term T, key), ρ, 2, k.val)).getD 0 = δ k
    rw [placeSalt_getD _ _ _ _ _ k.isLt, shiftCache_apply, hb, hs, Option.map_some, Option.getD_some,
      Option.getD_some]
    ring

/-! ## The count -/

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
/-- At the end of the game in `provWorld` with the budget `q`, the named shifts are at most
`(q + gameBatches * n * termCount C) * (gameBatches * n * termCount C)`. -/
theorem saltProvCount : SaltProvCount prims K circuits settings runLimit := by
  intro D A q bounded y hy
  have hA := encard_le_of_step (provWorld prims D) (fun st => digestCells st.1.1.1) Charged
    (fun t => {p | callCell t = some p}) callCell_encard (provWorld_digests prims D) _ _
    (charged_dealtRun K circuits settings runLimit D ⟨true, fun _ => 0⟩ (fun _ => rfl) A q bounded) provStart y hy
  have hB := encard_le_of_step (provWorld prims D) (fun st => places st.1.1.2) (HonestP SaltDraw) drawPlace
    drawPlace_encard (provWorld_places prims D) _ _
    (salt_dealtRun K circuits settings runLimit D ⟨true, fun _ => 0⟩ (fun _ => rfl) A) provStart y hy
  have hA0 : digestCells (provStart : ProvState C).1.1.1 = ∅ := by
    ext p
    simp [digestCells, provStart]
  have hB0 : places (provStart : ProvState C).1.1.2 = ∅ := by
    ext d
    simp [places, provStart]
  simp only [hA0, hB0, Set.encard_empty, zero_add] at hA hB
  have h := (Set.encard_le_encard (named_subset D y.2)).trans (Set.encard_image_le _ _)
  rw [Set.encard_prod, Set.encard_coe_eq_coe_finsetCard] at h
  have h' := h.trans (mul_le_mul' hA hB)
  exact_mod_cast h'

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.saltProvCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.saltProvCount
