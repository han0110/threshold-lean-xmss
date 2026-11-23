import ThresholdLeanXmssSecurity.Proof.List
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.EchoBlock

/-!
# The bound for the pairs in the block of round 2

* `passTwo_good` states that each shared key answer of pass 2 is the value of the cache at its cell.
* `passOne_good` states that the seed of a hidden term in the keys of pass 1 is `heldSeed`.
* `PairEvent D ks p c` states that for the unordered pair `p` of honest operators that share a hidden
  term, the two shared key cells are distinct and hold one value in the cache `c`.
* `blockBound` proves `BlockBound`. The block has the law of pass 1 of all operators and then pass 2 of
  all operators. After pass 1 the two cells of each pair are fixed. A cell that has a value at the start
  is in the log by `CacheInv`, and then `EchoPrior` holds. Else the two cells hold one value with
  probability at most `1 / 2^256` (`prEvent_collide_le`). The union over the pairs gives `C(n,2) / 2^256`.
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

theorem hiddenTermOf_shared (D : C.Coalition) (parts : C.Party → Parts C) (L : List HashOutput) :
    hiddenTermOf D parts (.sharedKeys .seedGen L) = none := by
  unfold hiddenTermOf
  rw [dite_eq_right]
  rintro ⟨T, -, h⟩
  simp [hiddenInput] at h

section Facts

variable (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput)

/-- The support fact of pass 2 of operator `j` with the keys `k` of pass 1. -/
def PassTwoGood (j : C.Party) (k : Option (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)))
    (a : Option (SeedGenEchoData C)) (c : HashCache C) : Prop :=
  match k with
  | none => a = none
  | some keys => ∃ sh, a = some (keys, sh) ∧ ∀ l : C.Party, c (sharedAddress j l keys.2.1) = some (sh.getD l.val 0)

theorem passTwoGood_mono (j : C.Party) (k : Option (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)))
    (a : Option (SeedGenEchoData C)) (c c' : HashCache C) (h : c ≤ c') :
    PassTwoGood j k a c → PassTwoGood j k a c' := by
  rcases k with _ | keys
  · exact id
  · rintro ⟨sh, ha, hc⟩
    exact ⟨sh, ha, fun l => h (hc l)⟩

theorem shared_run (L : List HashOutput) (c : HashCache C) :
    ∀ z ∈ support ((simulateQ (compLocal prims D parts seed)
      (liftComp (hashQuery (C := C) (.sharedKeys .seedGen L)) (LocalSpec C))).run c),
      z.2 (.sharedKeys .seedGen L) = some z.1 := by
  have e : liftComp (hashQuery (C := C) (.sharedKeys .seedGen L)) (LocalSpec C) =
      (liftM (OracleSpec.query (spec := LocalSpec C) (.inr (.inl (.sharedKeys .seedGen L)))) :
        OracleComp (LocalSpec C) _) := by
    simp [hashQuery]
    rfl
  intro z hz
  rw [e] at hz
  simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, compLocal,
    hiddenTermOf_shared] at hz
  have hf : ¬ IsFixed (C := C) (.sharedKeys .seedGen L) := fun ⟨_, h, _⟩ => by cases h
  change z ∈ support ((hashAnswer prims (.sharedKeys .seedGen L)).run c) at hz
  rw [hashAnswer_of_not_isFixed prims hf] at hz
  exact (Ready.randomOracle_support' _ _ _ hz).2

theorem passTwo_good (j : C.Party) (k : Option (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)))
    (c : HashCache C) :
    ∀ z ∈ support ((simulateQ (compLocal prims D parts seed) (passTwo j k)).run c), PassTwoGood j k z.1 z.2 := by
  intro z hz
  rcases k with _ | keys
  · simp only [passTwo, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    rfl
  · simp only [passTwo, seedGen_liftComp_mapM, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
      support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    refine ⟨p.1, rfl, fun l => ?_⟩
    have hF := compLocal_mapM_support prims D parts seed _
      (fun l v c => c (sharedAddress j l keys.2.1) = some v) (fun _ _ _ _ h hv => h hv)
      (fun l c z hz => shared_run prims D parts seed _ c z hz) C.parties c p hp
    exact SigningOwnWalkBuild.forall₂_finRange 0 hF l

/-- The support fact of pass 1 of operator `j`. -/
def PassOneGood (j : C.Party) (a : Option (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))) : Prop :=
  ∀ keys, a = some keys → ∀ T, ¬ KnownTo D.1 T → j ∈ C.holders T → keys.2.1 T = heldSeed D parts seed T

theorem derive_hidden {E : Type} (j : C.Party) (inbox : Mail C E) (c : HashCache C) :
    ∀ z ∈ support ((simulateQ (compLocal prims D parts seed)
      (liftComp (deriveKeys .seedGen j (normView D parts j inbox)) (LocalSpec C))).run c),
      ∀ T, ¬ KnownTo D.1 T → j ∈ C.holders T → z.1.2.1 T = heldSeed D parts seed T := by
  rw [deriveKeys_normView]
  simp only [liftComp_bind, liftComp_pure, seedGen_liftComp_mapM]
  intro z hz T hT hj
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, support_bind, Set.mem_iUnion,
    support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨p1, -, p2, hp2, p3, -, rfl⟩ := hz
  have hF := compLocal_mapM_support prims D parts seed _
    (fun T v _ => ¬ KnownTo D.1 T → j ∈ C.holders T → v = heldSeed D parts seed T) (fun _ _ _ _ _ h => h)
    (fun T c z hz => ?_) C.terms p1.2 p2 hp2
  · exact forall₂_getD_idxOf _ _ _ hF T (by simp [Committee.terms]) 0 hT hj
  · intro hT hj
    rw [ite_eq_left hj, termAddress_hidden D parts j inbox T hT] at hz
    obtain ⟨T', hT'⟩ : ∃ T', hiddenTermOf D parts (hiddenInput parts T) = some T' := by
      unfold hiddenTermOf
      rw [dite_eq_left ⟨T, hT, rfl⟩]
      exact ⟨_, rfl⟩
    have e : liftComp (hashQuery (C := C) (hiddenInput parts T)) (LocalSpec C) =
        (liftM (OracleSpec.query (spec := LocalSpec C) (.inr (.inl (hiddenInput parts T)))) :
          OracleComp (LocalSpec C) _) := by
      simp [hashQuery]
      rfl
    rw [e] at hz
    simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, compLocal, hT',
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    simp only [heldSeed, hT']

theorem passOne_good {E : Type} (committed : C.Party → Mail C E) (d : C.Party → Option Unit)
    (sent : C.Party → C.Party → Option (Msg E)) (j : C.Party) (c : HashCache C) :
    ∀ z ∈ support ((simulateQ (compLocal prims D parts seed) (passOne D parts committed d sent j)).run c),
      PassOneGood D parts seed j z.1 := by
  intro z hz keys hk
  unfold passOne at hz
  by_cases hj : j ∈ D.1
  · rw [ite_eq_left hj] at hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz] at hk
    cases hk
  rw [ite_eq_right hj] at hz
  rcases hd : d j with _ | u
  · simp only [hd, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz] at hk
    cases hk
  simp only [hd] at hz
  by_cases ha : anyAbort (blockInbox D parts d sent j) = true
  · rw [ite_eq_left ha] at hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz] at hk
    cases hk
  rw [ite_eq_right ha] at hz
  simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
  obtain ⟨p, -, hz⟩ := hz
  split_ifs at hz
  · simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, support_bind, Set.mem_iUnion,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    cases hk
    exact derive_hidden prims D parts seed j _ p.2 r hr
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz] at hk
    cases hk

end Facts

/-! ## The assembly -/

section Assembly

/-- For the unordered pair `p` of honest operators that share a hidden term, with keys `ks` of pass 1,
the two shared key cells are distinct and hold one value in the cache `c`. -/
def PairEvent (D : C.Coalition) (ks : C.Party → Option (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)))
    (p : C.Pair) (c : HashCache C) : Prop :=
  ∃ ki kj, p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1 ∧ SharesHidden D p.1.1 p.1.2 ∧ ks p.1.1 = some ki ∧ ks p.1.2 = some kj ∧
    sharedAddress p.1.1 p.1.2 ki.2.1 ≠ sharedAddress p.1.2 p.1.1 kj.2.1 ∧
    c (sharedAddress p.1.1 p.1.2 ki.2.1) ≠ none ∧
    c (sharedAddress p.1.1 p.1.2 ki.2.1) = c (sharedAddress p.1.2 p.1.1 kj.2.1)

/-- On the support of pass 2, `EchoBad` gives `PairEvent` for one unordered pair. -/
theorem pairEvent_of_bad (D : C.Coalition)
    (ks : C.Party → Option (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)))
    (z : (C.Party → Option (SeedGenEchoData C)) × HashCache C) (hgood : ∀ j, PassTwoGood j (ks j) (z.1 j) z.2)
    (hb : EchoBad D (.inr ((0 : ℕ), (), z.1) : EchoPoint C Unit)) :
    ∃ p ∈ (Finset.univ : Finset C.Pair), PairEvent D ks p z.2 := by
  obtain ⟨i, j, x, y, hi, hj, hij, hs, hx, hy, hne⟩ := hb
  change z.1 i = some x at hx
  change z.1 j = some y at hy
  have gi := hgood i
  have gj := hgood j
  rcases hki : ks i with _ | ki
  · simp only [PassTwoGood, hki] at gi
    rw [gi] at hx
    cases hx
  rcases hkj : ks j with _ | kj
  · simp only [PassTwoGood, hkj] at gj
    rw [gj] at hy
    cases hy
  simp only [PassTwoGood, hki, hkj] at gi gj
  obtain ⟨shi, hxi, hci⟩ := gi
  obtain ⟨shj, hyj, hcj⟩ := gj
  rw [hxi] at hx
  rw [hyj] at hy
  cases hx
  cases hy
  have hca := hci j
  have hcb := hcj i
  have hL : (echoList i j (ki, shi) = echoList j i (kj, shj)) ↔
      ki.1 = kj.1 ∧ sharedAddress i j ki.2.1 = sharedAddress j i kj.2.1 := by
    simp only [echoList, sharedAddress, List.cons.injEq, Query.sharedKeys.injEq, true_and]
  have hH : (echoOf .seedGen ki shi j = echoOf .seedGen kj shj i) ↔
      ki.1 = kj.1 ∧ shi.getD j.val 0 = shj.getD i.val 0 := by
    simp [echoOf]
  rw [hL, hH] at hne
  have key : sharedAddress i j ki.2.1 ≠ sharedAddress j i kj.2.1 ∧ z.2 (sharedAddress i j ki.2.1) ≠ none ∧
      z.2 (sharedAddress i j ki.2.1) = z.2 (sharedAddress j i kj.2.1) := by
    by_cases hP : ki.1 = kj.1
    · by_cases hab : sharedAddress i j ki.2.1 = sharedAddress j i kj.2.1
      · exfalso
        refine hne ⟨fun _ => ⟨hP, ?_⟩, fun _ => ⟨hP, hab⟩⟩
        rw [hab, hcb] at hca
        exact (Option.some.inj hca).symm
      · have hsh : shi.getD j.val 0 = shj.getD i.val 0 := by
          by_contra h
          exact hne ⟨fun h' => absurd h'.2 hab, fun h' => absurd h'.2 h⟩
        refine ⟨hab, by rw [hca]; simp, by rw [hca, hcb, hsh]⟩
    · exfalso
      exact hne ⟨fun h => absurd h.1 hP, fun h => absurd h.1 hP⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨⟨(i, j), h⟩, Finset.mem_univ _, ki, kj, hi, hj, hs, hki, hkj, key⟩
  · refine ⟨⟨(j, i), h⟩, Finset.mem_univ _, kj, ki, hj, hi, sharesHidden_symm D hi hs, hkj, hki, Ne.symm key.1, ?_,
      key.2.2.symm⟩
    rw [← key.2.2]
    exact key.2.1

/-- A shared key cell of an honest pair that share a hidden term, with a value in the cache of a state
with `CacheInv`, gives `EchoPrior`. -/
theorem echoPrior_of_cached (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput)
    (s : LogState C) (hinv : CacheInv s) {i j : C.Party} (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hi : i ∉ D.1) (hj : j ∉ D.1) (hij : i ≠ j) (hs : SharesHidden D i j)
    (hgood : PassOneGood D parts seed i (some keys))
    (hc : s.1.1 (sharedAddress i j keys.2.1) ≠ none) : EchoPrior D parts seed s := by
  obtain ⟨-, T0, hT0, hk0⟩ := hs
  obtain ⟨T, hT⟩ : ∃ T, (sharedTerms i j).find? (fun T' => ¬ KnownTo D.1 T') = some T :=
    Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨T0, hT0, by simpa using hk0⟩)
  have hmem := List.mem_of_find?_eq_some hT
  have hp := List.find?_some hT
  simp only [decide_eq_true_eq] at hp
  have hiT : i ∈ C.holders T := by
    simp only [sharedTerms, List.mem_filter, decide_eq_true_eq] at hmem
    exact hmem.2.1
  refine ⟨_, hinv _ hc, _, i, j, T, hi, hj, hij, hT, rfl, ?_⟩
  rw [list_map_getD_idxOf _ _ _ _ hmem]
  exact hgood keys rfl T hp hiT

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The bound for the pairs in the block of round 2. -/
theorem blockBound : BlockBound (C := C) (E := E) prims := by
  intro D parts seed committed d sent s hinv
  rw [revealBlock_eq, compWorld_free_run prims D parts seed _ (localBlock_noStream D parts committed d sent) s,
    prEvent_map]
  by_cases hEP : EchoPrior D parts seed s
  · exact le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun r _ hr => hr.2 hEP) zero_le
  refine (prEvent_mono _ _ _ fun r hr => hr.1).trans ?_
  have hsplit := runEq_sequenceFin_split (commutes_compLocal prims D parts seed)
    (passOne D parts committed d sent) passTwo s.1.1
  unfold localBlock
  rw [hsplit.prEvent_eq]
  simp only [simulateQ_bind, StateT.run_bind]
  rw [prEvent_bind_wp]
  refine (wp_mono_of_support _ fun p hp => ?_).trans_eq (wp_const _ _)
  have hF1 : ∀ L, p.2 (.sharedKeys .seedGen L) = s.1.1 (.sharedKeys .seedGen L) := fun L =>
    compLocal_run_keep prims D parts seed SharedCell _
      (avoid_sequenceFin _ _ (passOne_avoid D parts committed d sent)) s.1.1 p hp _ ⟨L, rfl⟩
  have hF2 : ∀ j, PassOneGood D parts seed j (p.1 j) :=
    compLocal_sequenceFin_support prims D parts seed _ (fun j a _ => PassOneGood D parts seed j a)
      (fun _ _ _ _ _ h => h) (fun j c z hz => passOne_good prims D parts seed committed d sent j c z hz) s.1.1 p hp
  refine (prEvent_mono_of_support _ _ (fun z => ∃ q ∈ (Finset.univ : Finset C.Pair), PairEvent D p.1 q z.2)
    fun z hz hb => ?_).trans ?_
  · exact pairEvent_of_bad D p.1 z (compLocal_sequenceFin_support prims D parts seed _
      (fun j a c => PassTwoGood j (p.1 j) a c) (fun j a c c' h => passTwoGood_mono j (p.1 j) a c c' h)
      (fun j c z hz => passTwo_good prims D parts seed j (p.1 j) c z hz) p.2 z hz) hb
  refine (prEvent_exists_finset_le_card_mul (ε := (Fintype.card HashOutput : ℝ≥0∞)⁻¹) _ _ _
    fun q _ => ?_).trans (le_of_eq ?_)
  · by_cases hst : ∃ ki kj, q.1.1 ∉ D.1 ∧ q.1.2 ∉ D.1 ∧ SharesHidden D q.1.1 q.1.2 ∧ p.1 q.1.1 = some ki ∧
        p.1 q.1.2 = some kj
    · obtain ⟨ki, kj, hi, hj, hs, hki, hkj⟩ := hst
      by_cases hab : sharedAddress q.1.1 q.1.2 ki.2.1 = sharedAddress q.1.2 q.1.1 kj.2.1
      · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z _ hz => ?_) zero_le
        obtain ⟨ki', kj', -, -, -, hki', hkj', hne, -⟩ := hz
        rw [hki] at hki'
        rw [hkj] at hkj'
        cases hki'
        cases hkj'
        exact hne hab
      have ha : p.2 (sharedAddress q.1.1 q.1.2 ki.2.1) = none := by
        rw [sharedAddress, hF1]
        by_contra hc
        exact hEP (echoPrior_of_cached D parts seed s hinv ki hi hj (ne_of_lt q.2) hs (hki ▸ hF2 q.1.1) hc)
      refine (prEvent_mono _ _ _ fun z hz => ?_).trans (prEvent_collide_le prims D parts seed _ _ _ hab p.2 ha)
      obtain ⟨ki', kj', -, -, -, hki', hkj', -, h1, h2⟩ := hz
      rw [hki] at hki'
      rw [hkj] at hkj'
      cases hki'
      cases hkj'
      exact ⟨h1, h2⟩
    · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z _ hz => ?_) zero_le
      obtain ⟨ki, kj, hi, hj, hs, hki, hkj, -⟩ := hz
      exact hst ⟨ki, kj, hi, hj, hs, hki, hkj⟩
  · have hcard : (Fintype.card HashOutput : ℝ≥0∞) = 2 ^ 256 := by
      simp
      norm_num
    rw [Finset.card_univ, TprfSecurityProof.card_pair, hcard, div_eq_mul_inv]

end Assembly

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.blockBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.blockBound
