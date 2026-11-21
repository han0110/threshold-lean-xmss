import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Parts
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Search
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.Move

/-!
# The bound of `SeedClash` on the seed generation

`hitClash` proves `HitClash`. `dealtProb_seedClash_le` bounds `SeedClash` in the game with the keys of the dealer by
`2 * (n * termCount C ^ 2) / 2^256`. The proof gives `2 * termCount C ^ 2 / 2^256`
(`wp_worldSeedGen_clash`), a mean over the seeds of the dealer and the lazy cells.

* `cellPot L s c` is `2^-256` when the cache `c` has no value at the cell `L`, and the indicator of
  `c L = some s` otherwise. Each call of the world keeps it in the mean, except a programming call at
  `L` (`wp_cellPot_simulateQ`). A cell that the adversary set before the draw of the seeds meets a
  seed with probability `2^-256` too (`wp_prawnsKeyGen_cellPot`).
* `hiddenInput parts T` is the derive input of each honest holder of the hidden term `T`.
  `AliasPair` states that the honest coordinate of the programming input of a known term meets it at
  the same place, with probability `2^-256` (`probEvent_aliasPair`). With no alias the rest of the
  seed generation makes no programming call at `hiddenInput parts T` (`programOff_seedGenRest`).
* `termCached` states that an honest holder of a hidden term with keys holds the end value of the
  cache at `hiddenInput parts T`. An honest holder that aborts sends an abort frame, so a holder with
  keys read the reveal of each other holder.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_bind noCall_pure noCall_map
  noCall_query noCall_mapM noCall_sequenceFin)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The potential of the cell `L` against the value `s`. -/
def cellPot (L : Query C) (s : HashOutput) (c : HashCache C) : ℝ≥0∞ :=
  match c L with
  | none => (Fintype.card HashOutput : ℝ≥0∞)⁻¹
  | some v => if v = s then 1 else 0

/-- A call of the world that is no programming call at the cell `L`. -/
def ProgramOff (L : Query C) : (WorldSpec C).Domain → Prop
  | .inl (.inr x) => x.1 ≠ L
  | _ => True

theorem cellPot_cacheQuery {L q : Query C} (hq : q ≠ L) (s v : HashOutput) (c : HashCache C) :
    cellPot L s (c.cacheQuery q v) = cellPot L s c := by
  unfold cellPot
  rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hq)]

theorem wp_cellPot_randomOracle (L : Query C) (s : HashOutput) (q : Query C) (c : HashCache C) :
    wp (((Query C →ₒ HashOutput).randomOracle q).run c) (fun z => cellPot L s z.2) ≤ cellPot L s c := by
  rw [randomOracle.run_eq]
  rcases hc : c q with _ | u
  · simp only [wp_bind, wp_pure]
    by_cases hq : q = L
    · subst hq
      have e : (fun u : HashOutput => cellPot q s (c.cacheQuery q u)) = fun u => if u = s then 1 else 0 := by
        funext u
        simp [cellPot]
      rw [e, ← prEvent_eq_wp_indicator]
      simp only [cellPot, hc]
      rw [SampleableType.prEvent_uniformSample_eq_singleton]
    · simp only [cellPot_cacheQuery hq, wp_const, le_refl]
  · simp

theorem wp_cellPot_hashAnswer (L : Query C) (s : HashOutput) (q : Query C) (c : HashCache C) :
    wp ((hashAnswer prims q).run c) (fun z => cellPot L s z.2) ≤ cellPot L s c := by
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    rw [hashAnswer_of_isFixed prims hm]
    simp
  · rw [hashAnswer_of_not_isFixed prims hq]
    exact wp_cellPot_randomOracle L s q c

theorem wp_cellPot_local (L : Query C) (s : HashOutput) (t : (LocalSpec C).Domain) (c : HashCache C) :
    wp ((localAnswer prims t).run c) (fun z => cellPot L s z.2) ≤ cellPot L s c := by
  rcases t with n | q | x
  · change wp ((unifFwdImpl (Query C →ₒ HashOutput) n).run c) _ ≤ _
    simp [unifFwdImpl]
  · exact wp_cellPot_hashAnswer prims L s q c
  · change wp ((prgAnswer prims x).run c) _ ≤ _
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, wp_bind, wp_pure]
    exact wp_cellPot_hashAnswer prims L s _ c

theorem wp_cellPot_streamWorld (D : C.Coalition) (L : Query C) (s : HashOutput) (t : (WorldSpec C).Domain)
    (ht : ProgramOff L t) (w : StreamState C) :
    wp ((streamWorld prims D t).run w) (fun z => cellPot L s z.2.1) ≤ cellPot L s w.1 := by
  rcases t with (t | x) | t
  · exact (wp_onHash _ w _).trans_le (wp_cellPot_local prims L s t w.1)
  · simp only [streamWorld]
    rw [wp_onHash]
    change wp ((programAnswer x).run w.1) _ ≤ _
    unfold programAnswer
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, wp_pure]
      exact (cellPot_cacheQuery ht s x.2 w.1).le
  · rcases t with n | q | x
    · exact (wp_onHash _ w _).trans_le (wp_cellPot_local prims L s _ w.1)
    · exact (wp_onHash _ w _).trans_le (wp_cellPot_local prims L s _ w.1)
    · simp only [streamWorld]
      split_ifs
      · simp only [StateT.run_mk, wp_map]
        simp [Function.comp_def]
      · exact (wp_onHash _ w _).trans_le (wp_cellPot_local prims L s _ w.1)

/-- A world computation with no programming call at `L` keeps the potential of `L` in the mean. -/
theorem wp_cellPot_simulateQ (D : C.Coalition) (L : Query C) (s : HashOutput) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (hoa : AllQueriesSatisfy oa (ProgramOff L))
    (w : StreamState C × List (Query C)) :
    wp ((simulateQ (loggedWorld prims D) oa).run w) (fun z => cellPot L s z.2.1.1) ≤ cellPot L s w.1.1 :=
  wp_simulateQ_le (loggedWorld prims D) (ProgramOff L) (fun w => cellPot L s w.1.1)
    (fun t ht w => by
      simp only [loggedWorld, StateT.run_mk, wp_map]
      exact wp_cellPot_streamWorld prims D L s t ht w.1) oa hoa w

/-- The potential is at least the indicator of the value `s` at `L`. -/
theorem cellPot_of_eq {L : Query C} {s : HashOutput} {c : HashCache C} (h : c L = some s) : cellPot L s c = 1 := by
  simp [cellPot, h]

/-! ## The aliases of a hidden derive input -/


/-- The holders of `T` in operator order. -/
def holdersList (T : C.Term) : List C.Party := C.parties.filter (· ∈ C.holders T)

/-- The derive input of the term `T` on the parts `parts`. -/
def hiddenInput (parts : C.Party → Parts C) (T : C.Term) : Query C :=
  .derive .seedGen .term ((holdersList T).map fun k => (parts k).term T)

/-- The first honest operator in `S`, as `worldSeedGen` picks it. -/
def firstHonestOf (D : C.Coalition) (S : Finset C.Party) : C.Party :=
  (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)

theorem firstHonestOf_spec (D : C.Coalition) (T : C.Term) :
    firstHonestOf D (C.holders T) ∈ C.holders T ∧ firstHonestOf D (C.holders T) ∉ D.1 := by
  obtain ⟨a, ha, hD⟩ := exists_honest_holder D T
  unfold firstHonestOf
  rcases hf : C.parties.find? (fun i => i ∈ C.holders T ∧ i ∉ D.1) with _ | k
  · rw [List.find?_eq_none] at hf
    exact absurd (hf a (by simp [Committee.parties])) (by simp [ha, hD])
  · have := List.find?_some hf
    simpa using this

/-- The holder of `T` at the place of the first honest holder of `T'`. -/
def aliasPartner (D : C.Coalition) (T T' : C.Term) : Option C.Party :=
  (holdersList T)[(holdersList T').idxOf (firstHonestOf D (C.holders T'))]?

/-- The honest coordinate of the programming input of `T'` meets the coordinate of the derive input
of `T` at its place. -/
def AliasPair (D : C.Coalition) (parts : C.Party → Parts C) (T T' : C.Term) : Prop :=
  ∃ h, aliasPartner D T T' = some h ∧ (parts h).term T = (parts (firstHonestOf D (C.holders T'))).term T'

/-- Some hidden term meets some known term. -/
def AnyAlias (D : C.Coalition) (parts : C.Party → Parts C) : Prop :=
  ∃ T T', ¬ KnownTo D.1 T ∧ KnownTo D.1 T' ∧ AliasPair D parts T T'

theorem probEvent_aliasPair (D : C.Coalition) {T T' : C.Term} (hne : T ≠ T') :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[AliasPair D parts T T'] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  rcases hp : aliasPartner D T T' with _ | h
  · simp [AliasPair, hp]
  · calc _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
          (parts h).term T = (parts (firstHonestOf D (C.holders T'))).term T'] :=
          prEvent_mono _ _ _ fun parts hx => by
            obtain ⟨h', hh', e⟩ := hx
            rw [hp] at hh'
            cases hh'
            exact e
      _ = _ := probEvent_parts_collision (fun parts => (parts h).term T)
          (fun parts => (parts (firstHonestOf D (C.holders T'))).term T') h (some T) none
          (fun c parts => by simp [shiftAt, shiftParts])
          (fun c parts => by
            by_cases e : firstHonestOf D (C.holders T') = h
            · simp [shiftAt, shiftParts, e, fun h : T = T' => hne h]
            · simp [shiftAt, e])

theorem probEvent_anyAlias (D : C.Coalition) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[AnyAlias D parts] ≤
      ((termCount C ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have h : Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      ∃ p : C.Term × C.Term, ¬ KnownTo D.1 p.1 ∧ KnownTo D.1 p.2 ∧ AliasPair D parts p.1 p.2] ≤
      Fintype.card (C.Term × C.Term) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    refine prEvent_exists_le_card_mul _ _ fun p => ?_
    by_cases hp : ¬ KnownTo D.1 p.1 ∧ KnownTo D.1 p.2
    · have hne : p.1 ≠ p.2 := fun e => hp.1 (e ▸ hp.2)
      exact (prEvent_mono _ _ _ fun parts hx => hx.2.2).trans (probEvent_aliasPair D hne)
    · exact (prEvent_eq_zero_of_forall_mem_support _ _ fun parts _ hx => hp ⟨hx.1, hx.2.1⟩).trans_le zero_le
  refine (prEvent_mono _ _ _ fun parts hx => ?_).trans (h.trans_eq ?_)
  · obtain ⟨T, T', h₁, h₂, h₃⟩ := hx
    exact ⟨(T, T'), h₁, h₂, h₃⟩
  · rw [Fintype.card_prod, card_term, termCount]
    push_cast
    ring


/-! ## The rest of the seed generation after the parts -/

section Rest

variable [Field E] [Algebra Bit E]

/-- `seedGenTail` after the draw of the parts. -/
def seedGenRest (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State) (early : CallLog C)
    (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    OracleComp (WorldSpec C) (net.State × (C.Party → Option (Keys C))) := do
  let steps ← startSteps worldRoles D fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))
  let ((state, steps, sent), calls) ← (stepRound observedRoles D net noFunctionality state steps).run
  let log := early ++ calls
  let firstHonest := fun (S : Finset C.Party) => (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)
  let view := fun (i j : C.Party) =>
    if j ∈ D.1 then readReveal .seedGen (extractReveal .seedGen log sent j i) i j else parts j
  let high ← free (liftComp ($ᵗ HashOutput) _)
  let _ ← program (.derive .seedGen .parameter (C.parties.map fun j => (view (firstHonest Finset.univ) j).parameter))
    (high >>> digestBits <<< digestBits ||| parameter.setWidth 256)
  let _ ← C.terms.mapM fun T => match (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
    | some j =>
      program (.derive .seedGen .term ((C.parties.filter (· ∈ C.holders T)).map fun k =>
        (view (firstHonest (C.holders T)) k).term T)) ((dealt j).seed T)
    | none => pure true
  let _ ← C.parties.mapM fun j => C.parties.mapM fun i =>
    if h : j ∈ D.1 ∧ i ∉ D.1 then
      let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
      program (.derive .seedGen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1]) ((dealt j).pairKey i)
    else pure true
  let ((state, keys), _) ← (executeRounds observedRoles D net noFunctionality (setupRounds - 1) state steps).run
  pure (state, keys)

theorem seedGenTail_eq_rest (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) :
    seedGenTail D net state early parameter dealt = (do
      let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) => (sampleParts : ProbComp (Parts C))) _)
      seedGenRest D net state early parameter dealt parts) := rfl

theorem programOff_program {q L : Query C} (hq : q ≠ L) (value : HashOutput) :
    AllQueriesSatisfy (program q value) (ProgramOff L) :=
  AllQueriesSatisfy.simulateQ (P := fun t => ∀ x, t = .inr x → x.1 ≠ L)
    ((allQueriesSatisfy_query_iff (spec := SimulatorSpec C) (.inr (q, value)) _).2
      fun x hx => by cases hx; exact hq)
    fun t ht => by
      rcases t with t | x
      · exact (allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inl (.inl t)) _).2 trivial
      · exact (allQueriesSatisfy_query_iff (spec := WorldSpec C) (.inl (.inr x)) _).2 (ht x rfl)

theorem programOff_of_noCall {α : Type} {oa : OracleComp (WorldSpec C) α} (h : NoCall WorldProgramQuery oa)
    (L : Query C) : AllQueriesSatisfy oa (ProgramOff L) :=
  (UsedHit.allQueries_of_noCall h).mono fun t ht => by
    rcases t with (t | x) | t
    · trivial
    · exact absurd trivial ht
    · trivial

omit [Field E] [Algebra Bit E] in
/-- With no alias of the hidden term `T`, the rest of the seed generation makes no programming call
at the derive input of `T`. -/
theorem programOff_seedGenRest (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (T : C.Term) (hno : ∀ T', KnownTo D.1 T' → ¬ AliasPair D parts T T') :
    AllQueriesSatisfy (seedGenRest D net state early parameter dealt parts) (ProgramOff (hiddenInput parts T)) := by
  unfold seedGenRest
  refine allQueriesSatisfy_bind (programOff_of_noCall (noProgram_startSteps D _) _) fun steps => ?_
  refine allQueriesSatisfy_bind (programOff_of_noCall (noProgram_stepRound_observed D net state steps) _) fun r => ?_
  obtain ⟨⟨state', steps', sent⟩, calls⟩ := r
  refine allQueriesSatisfy_bind (programOff_of_noCall (Collision.noProgram_free _) _) fun high => ?_
  refine allQueriesSatisfy_bind (programOff_program (by simp [hiddenInput]) _) fun _ => ?_
  refine allQueriesSatisfy_bind (UsedHit.mapM_satisfy _ _ (fun T' => ?_) _) fun _ => ?_
  · split
    · rename_i j hj
      refine programOff_program (fun e => ?_) _
      have hk : KnownTo D.1 T' := by
        have := List.find?_some hj
        simp only [decide_eq_true_eq] at this
        exact ⟨j, this.1, this.2⟩
      refine hno T' hk ?_
      obtain ⟨hk0, hk0D⟩ := firstHonestOf_spec D T'
      have hmem : firstHonestOf D (C.holders T') ∈ holdersList T' := by
        simp [holdersList, Committee.parties, hk0]
      have hlt := List.idxOf_lt_length_of_mem hmem
      simp only [hiddenInput, Query.derive.injEq, true_and] at e
      have e2 := congrArg (fun l => l[(holdersList T').idxOf (firstHonestOf D (C.holders T'))]?) e
      change ((holdersList T').map _)[_]? = ((holdersList T).map _)[_]? at e2
      rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_idxOf] at e2
      rcases hp : aliasPartner D T T' with _ | h
      · simp only [aliasPartner] at hp
        rw [hp] at e2
        simp at e2
      · simp only [aliasPartner] at hp
        rw [hp] at e2
        simp only [Option.map_some, Option.some.injEq] at e2
        refine ⟨h, by simp [aliasPartner, hp], ?_⟩
        rw [← e2]
        simp only [hk0D, ↓reduceIte]
    · exact allQueriesSatisfy_pure _ _
  refine allQueriesSatisfy_bind (UsedHit.mapM_satisfy _ _ (fun j => UsedHit.mapM_satisfy _ _ (fun i => ?_) _) _)
    fun _ => ?_
  · split
    · exact programOff_program (by simp [hiddenInput]) _
    · exact allQueriesSatisfy_pure _ _
  refine allQueriesSatisfy_bind (programOff_of_noCall (noProgram_executeRounds_observed D net _ _ _) _) fun _ => ?_
  exact allQueriesSatisfy_pure _ _

end Rest


/-! ## The seeds of the dealer against a fixed cell -/

/-- One coordinate of a uniform function is uniform. -/
theorem probEvent_uniform_apply_eq {ι P : Type} [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P]
    [SampleableType P] [SampleableType (ι → P)] (j : ι) (x : P) :
    Pr{let s ← $ᵗ (ι → P)}[s j = x] = (Fintype.card P : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample]
  have hfil : (Finset.univ.filter fun s : ι → P => s j = x).card = Fintype.card P ^ (Fintype.card ι - 1) := by
    have := Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset P) j (Finset.mem_univ x)
    simpa using this
  have hk : Fintype.card ι = (Fintype.card ι - 1) + 1 := by
    have := Fintype.card_pos_iff.2 ⟨j⟩
    omega
  have hP : (Fintype.card P : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card P := Fintype.card_pos_iff.2 ⟨x⟩
    exact_mod_cast this.ne'
  rw [hfil, Fintype.card_fun, hk, pow_succ, Nat.cast_mul, Nat.add_sub_cancel]
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by exact_mod_cast (pow_ne_zero _ (by exact_mod_cast hP))))
    (Or.inl (by simp))]
  rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast (pow_ne_zero _ (by exact_mod_cast hP)))
    (ENNReal.natCast_ne_top _), one_mul]

/-- The mean of the potential of a fixed cell against one seed of the dealer is `2^-256`. -/
theorem wp_prawnsKeyGen_cellPot (L : Query C) (T : C.Term) (c : HashCache C) :
    wp (prawnsKeyGen (C := C)) (fun x => cellPot L (x.2.1 T) c) ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  rcases hc : c L with _ | u
  · simp [cellPot, hc]
  · simp only [cellPot, hc]
    unfold prawnsKeyGen
    simp only [wp_bind, wp_pure]
    refine (wp_mono _ fun _ => ?_).trans_eq (wp_const _ _)
    have e : ∀ x : C.Term → HashOutput, (wp ($ᵗ (C.Pair → HashOutput)) fun _ => if u = x T then (1 : ℝ≥0∞) else 0) =
        if u = x T then 1 else 0 := fun x => wp_const _ _
    simp only [e]
    rw [← prEvent_eq_wp_indicator, prEvent_congr _ _ _ fun s => eq_comm, probEvent_uniform_apply_eq]

/-! ## The bound of `SeedClash` on the seed generation -/

section Assembly

variable [Field E] [Algebra Bit E]

/-- An honest holder of a hidden term with keys holds the end value of the cache at the derive input
of the term. -/
def TermCached (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) : Prop :=
  ∀ (state : net.State) (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C)
    (parts : C.Party → Parts C) (w : LogState C),
    ∀ z ∈ support ((simulateQ (loggedWorld prims D) (seedGenRest D net state early parameter dealt parts)).run w),
      ∀ (i : C.Party) (keys : Keys C) (T : C.Term), i ∉ D.1 → z.1.2 i = some keys → i ∈ C.holders T →
        ¬ KnownTo D.1 T → z.2.1.1 (hiddenInput parts T) = some (keys.seed T)

/-- The sum of the potentials of the derive inputs of the hidden terms against the seeds. -/
def clashSum (D : C.Coalition) (parts : C.Party → Parts C) (seeds : C.Term → HashOutput) (c : HashCache C) :
    ℝ≥0∞ :=
  ∑ T : C.Term, ∑ T' : C.Term, if KnownTo D.1 T then 0 else cellPot (hiddenInput parts T) (seeds T') c

omit [Field E] [Algebra Bit E] in
theorem one_le_clashSum {D : C.Coalition} {parts : C.Party → Parts C} {seeds : C.Term → HashOutput}
    {c : HashCache C} {T T' : C.Term} (hT : ¬ KnownTo D.1 T) (h : c (hiddenInput parts T) = some (seeds T')) :
    1 ≤ clashSum D parts seeds c := by
  unfold clashSum
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ T))
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ T'))
  simp only [hT, ↓reduceIte, cellPot_of_eq h, le_refl]

omit [Field E] [Algebra Bit E] in
theorem wp_seedGenRest_clash (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (cached : TermCached prims D net) (state : net.State) (early : CallLog C) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (parts : C.Party → Parts C) (w : LogState C) :
    wp ((simulateQ (loggedWorld prims D) (seedGenRest D net state early parameter dealt parts)).run w)
        (fun z => if SeedClash D seeds z.1.2 then 1 else 0) ≤
      (if AnyAlias D parts then 1 else 0) + clashSum D parts seeds w.1.1 := by
  by_cases ha : AnyAlias D parts
  · simp only [ha, ↓reduceIte]
    exact (wp_le_one _ _ fun z => by split_ifs <;> simp).trans le_self_add
  · simp only [ha, ↓reduceIte, zero_add]
    calc _ ≤ wp ((simulateQ (loggedWorld prims D) (seedGenRest D net state early parameter dealt parts)).run w)
          (fun z => clashSum D parts seeds z.2.1.1) := wp_mono_of_support _ fun z hz => by
          split_ifs with h
          · obtain ⟨i, keys, T, T', hi, he, hh, hT, hs⟩ := h
            have hc := cached state early parameter dealt parts w z hz i keys T hi he hh hT
            rw [hs] at hc
            exact one_le_clashSum hT hc
          · exact zero_le
      _ ≤ _ := by
          unfold clashSum
          rw [wp_finsetSum]
          refine Finset.sum_le_sum fun T _ => ?_
          rw [wp_finsetSum]
          refine Finset.sum_le_sum fun T' _ => ?_
          by_cases hT : KnownTo D.1 T
          · simp only [hT, ↓reduceIte, wp_const, le_refl]
          · simp only [hT, ↓reduceIte]
            exact wp_cellPot_simulateQ prims D _ _ _ (programOff_seedGenRest D net state early parameter dealt
              parts T fun T'' hk ha' => ha ⟨T, T'', hT, hk, ha'⟩) w

theorem wp_worldSeedGen_clash (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (cached : TermCached prims D net) :
    wp ((simulateQ (loggedWorld prims D) (worldSeedGen D net)).run ((∅, ∅), []))
        (fun z => if SeedClash D z.1.2.2.1 z.1.2.2.2.2 then 1 else 0) ≤
      2 * ((termCount C ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  rw [worldSeedGen_eq]
  simp only [seedGenTail_eq_rest, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, wp_bind, wp_pure]
  refine (wp_mono _ fun a => ?_).trans_eq (wp_const _ _)
  have hsum : ∀ (parts : C.Party → Parts C),
      wp (prawnsKeyGen (C := C)) (fun x => clashSum D parts x.2.1 a.2.1.1) ≤
        ((termCount C ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := fun parts => by
    unfold clashSum
    rw [wp_finsetSum]
    calc _ ≤ ∑ _T : C.Term, ∑ _T' : C.Term, (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
          refine Finset.sum_le_sum fun T _ => ?_
          rw [wp_finsetSum]
          refine Finset.sum_le_sum fun T' _ => ?_
          by_cases hT : KnownTo D.1 T
          · simp only [hT, ↓reduceIte, wp_const, zero_le]
          · simp only [hT, ↓reduceIte]
            exact wp_prawnsKeyGen_cellPot _ T' _
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, card_term, nsmul_eq_mul, termCount]
          push_cast
          ring
  simp only [loggedWorld_free_liftComp, wp_map, Function.comp_def]
  calc _ ≤ wp (prawnsKeyGen (C := C)) (fun x => wp (OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C))
        (fun parts => (if AnyAlias D parts then 1 else 0) + clashSum D parts x.2.1 a.2.1.1)) :=
        wp_mono _ fun x => wp_mono _ fun parts =>
          wp_seedGenRest_clash prims D net cached a.1.1 a.1.2 x.1 x.2.1 x.2.2 parts a.2
    _ = wp (OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
          (if AnyAlias D parts then 1 else 0) + wp (prawnsKeyGen (C := C)) (fun x => clashSum D parts x.2.1 a.2.1.1)) := by
        rw [wp_swap]
        refine congrArg _ (funext fun parts => ?_)
        rw [wp_add, wp_const]
    _ ≤ wp (OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)) (fun parts =>
          (if AnyAlias D parts then 1 else 0) + ((termCount C ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹) :=
        wp_mono _ fun parts => add_le_add le_rfl (hsum parts)
    _ ≤ _ := by
        rw [wp_add, wp_const, ← prEvent_eq_wp_indicator, two_mul, add_mul]
        exact add_le_add (probEvent_anyAlias D) le_rfl

/-- The bound of `SeedClash` in the game with the keys of the dealer, for each mode. -/
theorem dealtProb_seedClash_le [Fintype E] [DecidableEq E] (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (runLimit : ℕ) (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (cached : TermCached prims D A.net) :
    dealtProb prims K circuits settings runLimit m D A (fun r => SeedClash D r.1.2.2.1 r.1.2.2.2.2) ≤
      ((2 * (C.n * termCount C ^ 2) : ℕ) : ℝ) / 2 ^ 256 := by
  unfold dealtProb
  have h : Pr{let r ← (sharedDealt prims K circuits settings runLimit m D A).run ((∅, ∅), [])}[
      SeedClash D r.1.2.2.1 r.1.2.2.2.2] ≤
      2 * ((termCount C ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    rw [prEvent_eq_wp_indicator]
    refine le_trans ?_ (wp_worldSeedGen_clash prims D A.net cached)
    unfold sharedDealt
    simp only [StateT.run_bind, wp_bind]
    refine wp_mono _ fun z => ?_
    simp only [StateT.run_pure, wp_pure]
    by_cases hS : SeedClash D z.1.2.2.1 z.1.2.2.2.2
    · simp only [hS, ↓reduceIte, wp_const, le_refl]
    · simp only [hS, ↓reduceIte, wp_const, le_refl]
  have hcard : (Fintype.card HashOutput : ℝ≥0∞) = 2 ^ 256 := by
    simp
    norm_num
  rw [hcard] at h
  have hn : (1 : ℝ≥0∞) ≤ C.n := by
    have := C.one_le_t
    exact_mod_cast (by unfold Committee.n; omega : 1 ≤ C.n)
  have h' : 2 * ((termCount C ^ 2 : ℕ) : ℝ≥0∞) * (2 ^ 256)⁻¹ ≤
      ((2 * (C.n * termCount C ^ 2) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [div_eq_mul_inv]
    refine mul_le_mul_left ?_ _
    push_cast
    calc (2 : ℝ≥0∞) * (termCount C : ℝ≥0∞) ^ 2 = 2 * (1 * (termCount C : ℝ≥0∞) ^ 2) := by ring
      _ ≤ 2 * ((C.n : ℝ≥0∞) * (termCount C : ℝ≥0∞) ^ 2) := by gcongr
  have hfin : ((2 * (C.n * termCount C ^ 2) : ℕ) : ℝ≥0∞) / 2 ^ 256 ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)
  refine (ENNReal.toReal_mono hfin (h.trans h')).trans_eq ?_
  rw [ENNReal.toReal_div]
  simp

end Assembly

/-! ## The steps of one seed generation with the answers of a cache -/

section Trace

attribute [local instance] Set.monad

open SetupAgree (cacheAnswer StepNext mem_setBind mapM_getD mem_hashQuery stepRound_cache)
open SetupParameter (commitStep revealStep echoStep anyAnswer)

variable [Field E] [Algebra Bit E]

omit [Field E] [Algebra Bit E] in
theorem advance_seedGenWith (i : C.Party) (own : Parts C) :
    advance (seedGenWith i own : PartyM C E RealSpec (Keys C)).run =
      liftComp (commitQueries .seedGen i own) (LocalSpec C) >>= fun commitments =>
        pure (commitStep i own commitments) := by
  have h : (seedGenWith i own : PartyM C E RealSpec (Keys C)) =
      commitRevealEcho .seedGen i own >>= fun keys => pure (SetupParameter.keysOf keys) := rfl
  rw [h, advance_setup_start]
  rfl

omit [Field E] [Algebra Bit E] in
theorem start_any_with (i : C.Party) (own : Parts C) (step : Step C E RealSpec (Keys C))
    (h : step ∈ simulateQ (anyAnswer (C := C)) (advance (seedGenWith i own : PartyM C E RealSpec (Keys C)).run)) :
    ∃ commitments, step = commitStep i own commitments := by
  rw [advance_seedGenWith] at h
  simp only [simulateQ_bind, simulateQ_pure] at h
  obtain ⟨commitments, -, h⟩ := mem_setBind.1 h
  rw [Set.pure_def, Set.mem_singleton_iff] at h
  exact ⟨commitments, h⟩

omit [Field E] [Algebra Bit E] in
theorem commit_next_seedGen (s : HashCache C) (inbox : Mail C E) (i : C.Party) (own : Parts C)
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

omit [Field E] [Algebra Bit E] in
theorem reveal_next_seedGen (s : HashCache C) (inbox : Mail C E) (i : C.Party) (own : Parts C)
    (committed : Mail C E) (next : Step C E RealSpec (Keys C))
    (h : StepNext s inbox (revealStep i own committed) next) :
    next = .done none ∨ (C.parties.any fun j => Msg.isAbort (inbox j)) = false ∧ ∃ keys shared,
      keys ∈ simulateQ (cacheAnswer s) (liftComp (deriveKeys .seedGen i (setupView .seedGen i own inbox)) (LocalSpec C)) ∧
      next = echoStep i keys shared := by
  change next ∈ simulateQ (cacheAnswer s) (advance (exchangeResume _ inbox)) at h
  unfold exchangeResume at h
  split_ifs at h with habort
  · left
    simpa only [advance_pure, simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] using h
  · rw [advance_setupRest] at h
    simp only [simulateQ_bind] at h
    obtain ⟨opens, -, h⟩ := mem_setBind.1 h
    split_ifs at h
    · right
      refine ⟨by simpa using habort, ?_⟩
      simp only [simulateQ_bind, simulateQ_pure] at h
      obtain ⟨keys, hkeys, h⟩ := mem_setBind.1 h
      obtain ⟨shared, -, h⟩ := mem_setBind.1 h
      rw [Set.pure_def, Set.mem_singleton_iff] at h
      exact ⟨keys, shared, hkeys, h⟩
    · left
      simpa [Set.pure_def] using h

omit [Field E] [Algebra Bit E] in
theorem echo_next_seedGen (s : HashCache C) (inbox : Mail C E) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (shared : List HashOutput)
    (next : Step C E RealSpec (Keys C)) (h : StepNext s inbox (echoStep i keys shared) next)
    (K : Keys C) (hout : next.output = some K) : K = SetupParameter.keysOf keys := by
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
      exact hout.symm
    · simp only [simulateQ_pure, Set.pure_def, Set.mem_singleton_iff] at h
      subst h
      cases hout

omit [Field E] [Algebra Bit E] in
/-- The key of a held term is the cached derived key of the parts of the term in the view. -/
theorem term_cached_seedGen {s : HashCache C} (i : C.Party) (view : C.Party → Parts C)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (h : keys ∈ simulateQ (cacheAnswer s) (liftComp (deriveKeys .seedGen i view) (LocalSpec C))) (T : C.Term)
    (hT : i ∈ C.holders T) :
    s (.derive .seedGen .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T)) =
      some (keys.2.1 T) := by
  unfold deriveKeys at h
  simp only [↓reduceIte, liftComp_bind, liftComp_pure, simulateQ_bind, simulateQ_pure] at h
  obtain ⟨parameter, -, h⟩ := mem_setBind.1 h
  obtain ⟨term, hterm, h⟩ := mem_setBind.1 h
  obtain ⟨pair, -, h⟩ := mem_setBind.1 h
  rw [Set.pure_def, Set.mem_singleton_iff] at h
  subst h
  have hmem : T ∈ C.terms := by simp [Committee.terms]
  have hj := mapM_getD _ C.terms term hterm (C.terms.idxOf T) (List.idxOf_lt_length_of_mem hmem) 0
  rw [List.getElem_idxOf] at hj
  simp only [hT, ↓reduceIte] at hj
  exact (mem_hashQuery hj).resolve_left fun ⟨_, hq, _⟩ => by cases hq

omit [Field E] [Algebra Bit E] in
/-- The view of `i` of a term part of `h` is the part of `h` that `h` revealed to `i`. -/
theorem setupView_term_seedGen (i h : C.Party) (hhi : h ≠ i) (own own' : Parts C) (inbox : Mail C E)
    (hrev : inbox h = revealOutbox .seedGen h own' i) (T : C.Term) (hi : i ∈ C.holders T)
    (hh : h ∈ C.holders T) : (setupView .seedGen i own inbox h).term T = own'.term T := by
  have hmem : T ∈ sharedTerms h i := by simp [sharedTerms, Committee.terms, hi, hh]
  simp only [setupView, hhi, ↓reduceIte, hrev, revealOutbox, Ne.symm hhi, Msg.hashesOf, readReveal, revealTo]
  have hlt := List.idxOf_lt_length_of_mem hmem
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega),
    List.getElem_append_right (by simp)]
  simp

theorem mem_eraseLog {α : Type} (D : C.Coalition) (X : WriterT (CallLog C) (OracleComp (WorldSpec C)) α)
    (w : StreamState C) (r : (α × CallLog C) × StreamState C)
    (hr : r ∈ support ((simulateQ (streamWorld prims D) X.run).run w)) :
    (r.1.1, r.2) ∈ support ((simulateQ (streamWorld prims D) (seedGenEraseLog X)).run w) := by
  unfold seedGenEraseLog
  rw [simulateQ_map, StateT.run_map, support_map]
  exact ⟨r, hr, rfl⟩

omit [Field E] [Algebra Bit E] in
theorem termCached_stream (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (w : StreamState C)
    (y : (net.State × (C.Party → Option (Keys C))) × StreamState C)
    (hy : y ∈ support ((simulateQ (streamWorld prims D) (seedGenRest D net state early parameter dealt parts)).run w))
    (i : C.Party) (keys : Keys C) (T : C.Term) (hi : i ∉ D.1) (hk : y.1.2 i = some keys) (hiT : i ∈ C.holders T)
    (hT : ¬ KnownTo D.1 T) : y.2.1 (hiddenInput parts T) = some (keys.seed T) := by
  unfold seedGenRest at hy
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hy
  obtain ⟨a0, ha0, r1, hr1, b, hb, c, hc, d, hd, e, he, f, hf, rfl⟩ := hy
  have h0 : ∀ k, k ∉ D.1 → ∃ commitments, a0.1 k = commitStep k (parts k) commitments := by
    unfold startSteps at ha0
    refine SetupParameter.sequenceFin_any (streamWorld prims D)
      (fun k v => k ∉ D.1 → ∃ commitments, v = commitStep k (parts k) commitments) _ (fun k w' u hu hk => ?_) w a0 ha0
    simp only [hk, ↓reduceIte, worldRoles] at hu
    exact start_any_with k (parts k) u.1 (SetupParameter.free_any (streamWorld prims D) _ w' u hu)
  have hq1 := mem_eraseLog prims D _ _ _ hr1
  rw [seedGenEraseLog_stepRound] at hq1
  obtain ⟨hle1, hn1⟩ := stepRound_cache prims D net state a0.1 a0.2 _ hq1
  simp only at hle1 hn1
  have hlb := streamWorld_run_mono prims D _ _ _ hb
  have hlc := streamWorld_run_mono prims D _ _ _ hc
  have hld := streamWorld_run_mono prims D _ _ _ hd
  have hle := streamWorld_run_mono prims D _ _ _ he
  have hqE := mem_eraseLog prims D _ _ _ hf
  rw [seedGenEraseLog_executeRounds] at hqE
  have hlf := streamWorld_run_mono prims D _ _ _ hqE
  simp only at hk ⊢
  rcases SetupParameter.executeRounds_succ_any (streamWorld prims D) D net 1 r1.1.1.1 r1.1.1.2.1 e.2 (f.1.1, f.2)
    hqE with hout | ⟨q2, hq2, hy⟩
  · exfalso
    obtain ⟨cm, hc0⟩ := h0 i hi
    have hs := hn1 i hi f.2.1 (hlb.trans (hlc.trans (hld.trans (hle.trans hlf))))
    rw [hc0] at hs
    have ho := congrFun hout i
    simp only [hk] at ho
    rcases commit_next_seedGen _ _ i (parts i) cm _ hs with h | h <;>
      simp [h, Step.output, revealStep] at ho
  obtain ⟨hle2, hn2⟩ := stepRound_cache prims D net _ _ _ q2 hq2
  have hm2 := streamWorld_run_mono prims D _ _ _ hy
  simp only at hle2 hn2 hm2
  have hs1 : r1.2.1 ≤ f.2.1 := hlb.trans (hlc.trans (hld.trans (hle.trans (hle2.trans hm2))))
  have hstep1 : ∀ k, k ∉ D.1 → r1.1.1.2.1 k = .done none ∨
      r1.1.1.2.1 k = revealStep k (parts k) (roundInbox D r1.1.1.2.2 a0.1 k) := fun k hk' => by
    obtain ⟨cm, hc0⟩ := h0 k hk'
    have hs := hn1 k hk' f.2.1 hs1
    rw [hc0] at hs
    exact commit_next_seedGen _ _ k (parts k) cm _ hs
  have hi2 : q2.1.2.1 i = .done none ∨ (C.parties.any fun j => Msg.isAbort (roundInbox D q2.1.2.2 r1.1.1.2.1 i j)) =
      false ∧ ∃ keys' shared, keys' ∈ simulateQ (cacheAnswer f.2.1) (liftComp (deriveKeys .seedGen i
        (setupView .seedGen i (parts i) (roundInbox D q2.1.2.2 r1.1.1.2.1 i))) (LocalSpec C)) ∧
        q2.1.2.1 i = echoStep i keys' shared := by
    have hs := hn2 i hi f.2.1 hm2
    rcases hstep1 i hi with h | h
    · rw [h] at hs
      exact Or.inl hs
    · rw [h] at hs
      exact reveal_next_seedGen _ _ i (parts i) _ _ hs
  rcases SetupParameter.executeRounds_succ_any (streamWorld prims D) D net 0 q2.1.1 q2.1.2.1 q2.2 (f.1.1, f.2)
    hy with hout | ⟨q3, hq3, hy⟩
  · exfalso
    have ho := congrFun hout i
    simp only [hk] at ho
    rcases hi2 with h | ⟨-, keys', shared, -, h⟩ <;> simp [h, Step.output, echoStep] at ho
  obtain ⟨hle3, hn3⟩ := stepRound_cache prims D net _ _ _ q3 hq3
  have hout := SetupParameter.executeRounds_zero_any (streamWorld prims D) D net q3.1.1 q3.1.2.1 q3.2 (f.1.1, f.2) hy
  have hlf3 := streamWorld_run_mono prims D _ _ _ hy
  simp only at hout hlf3 hle3 hn3
  have ho := congrFun hout i
  simp only [hk] at ho
  have hs3 := hn3 i hi f.2.1 hlf3
  rcases hi2 with h | ⟨habort, keys', shared, hkeys', h⟩
  · exfalso
    rw [h] at hs3
    change q3.1.2.1 i = .done none at hs3
    simp [hs3, Step.output] at ho
  rw [h] at hs3
  have hK := echo_next_seedGen _ _ i keys' shared _ hs3 keys ho.symm
  subst hK
  have hc := term_cached_seedGen i _ keys' hkeys' T hiT
  have hview : ((C.parties.filter (· ∈ C.holders T)).map fun j =>
      (setupView .seedGen i (parts i) (roundInbox D q2.1.2.2 r1.1.1.2.1 i) j).term T) =
      (holdersList T).map fun j => (parts j).term T := by
    refine List.map_congr_left fun j hj => ?_
    have hjT : j ∈ C.holders T := by simpa using (List.mem_filter.1 hj).2
    have hjD : j ∉ D.1 := fun h => hT ⟨j, h, hjT⟩
    by_cases hji : j = i
    · subst hji
      simp [setupView]
    · have hrev : roundInbox D q2.1.2.2 r1.1.1.2.1 i j = revealOutbox .seedGen j (parts j) i := by
        rcases hstep1 j hjD with h1 | h1
        · exfalso
          have ha : Msg.isAbort (roundInbox D q2.1.2.2 r1.1.1.2.1 i j) = true := by
            simp [roundInbox, hjD, h1, Step.delivered, Msg.isAbort]
          have hany := List.any_eq_false.1 habort j (by simp [Committee.parties])
          exact hany ha
        · simp [roundInbox, hjD, h1, Step.delivered, revealStep]
      exact setupView_term_seedGen i j hji (parts i) (parts j) _ hrev T hiT hjT
  rw [hview] at hc
  exact hc

omit [Field E] [Algebra Bit E] in
/-- `TermCached` holds for each coalition and each adversary. -/
theorem termCached (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) : TermCached prims D net := by
  intro state early parameter dealt parts w z hz i keys T hi hk hiT hT
  have h := withLog_run (streamWorld prims D) countedCells (seedGenRest D net state early parameter dealt parts) w.1 w.2
  rw [← loggedWorld_eq] at h
  have hz' : (z.1, z.2.1) ∈ support ((simulateQ (streamWorld prims D)
      (seedGenRest D net state early parameter dealt parts)).run w.1) := by
    rw [← h, support_map]
    exact ⟨z, hz, rfl⟩
  exact termCached_stream prims D net state early parameter dealt parts w.1 _ hz' i keys T hi hk hiT hT

end Trace

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings) (runLimit : ℕ)

/-- `HitClash` from `TermCached` for each coalition and each adversary. -/
theorem hitClash_of_termCached
    (cached : ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty), TermCached prims D net) :
    HitClash prims K circuits settings runLimit := fun D A _ _ =>
  dealtProb_seedClash_le prims K circuits settings runLimit _ D A (cached D A.net)

/-- The bound of `SeedClash` in the game with the keys of the dealer and no emulated run. -/
theorem hitClash : HitClash prims K circuits settings runLimit :=
  hitClash_of_termCached prims K circuits settings runLimit (termCached prims)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.hitClash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.hitClash
