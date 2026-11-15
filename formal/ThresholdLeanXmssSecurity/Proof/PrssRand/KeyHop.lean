import ThresholdLeanXmssSecurity.Proof.PrssRand.Runs
import ThresholdLeanXmssSecurity.Proof.PrssRand.KeyInvariant
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# The PRSS streams from dealt keys, the stream-key event

`prssRand_keyHop` bounds the stream-key event of `keyWorld_coupling` on the real run. The bound is in
the world with one independent AES key for each hidden PRSS key (`probBad_streamKey_eq_ideal`). There
the calls of the adversary do not depend on the hidden key values.

1. `prssRandReal_eq_keyed` shows the dealt keys of the real run.
2. `prssRandRealAfter_allowed` and `jointKeyWorld_run_inv` give that a raised flag comes with a hit
   of a hidden dealt key, when the dealt keys are apart.
3. `prob_dealt_keys_equal_le` bounds the probability that the dealt keys are not apart.
4. `prob_prssRand_keyHit_le` bounds a hit when the dealt keys are apart.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## Uniform tables -/

/-- A search of at most `q` candidates from an observation that does not depend on one coordinate of
a uniform table guesses that coordinate with probability at most `q / 2^256`. -/
theorem prob_uniformTable_guess_le {Ω V : Type} [Finite Ω] [DecidableEq Ω]
    [SampleableType (Ω → HashOutput)] (x : Ω) (view : (Ω → HashOutput) → V)
    (hv : ∀ table u, view (Function.update table x u) = view table)
    (search : V → ProbComp (Finset HashOutput)) (q : ℕ)
    (hq : ∀ v s, s ∈ support (search v) → s.card ≤ q) :
    Pr{let z ← ($ᵗ (Ω → HashOutput)) >>= fun table =>
      search (view table) >>= fun s => pure (decide (table x ∈ s))}[z = true] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
  have he := (seedGenUniform_update_bind x (fun table =>
    search (view table) >>= fun s => pure (decide (table x ∈ s)))).symm
  simp only [hv, Function.update_self] at he
  have hs := he.trans ((OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans
    (EvalDistEq.bind_right _ fun table => OracleComp.EvalDistEq.bind_bind_swap _ _ _))
  rw [hs.prEvent_eq (· = true)]
  apply prEvent_bind_le_of_forall_le_of_support
  intro table _
  apply prEvent_bind_le_of_forall_le_of_support
  intro candidates hc
  have hm : (($ᵗ HashOutput) >>= fun u => pure (decide (u ∈ candidates)) : ProbComp Bool) =
      (fun u : HashOutput => decide (u ∈ candidates)) <$> ($ᵗ HashOutput) := by
    rw [map_eq_bind_pure_comp]
    rfl
  rw [hm, prEvent_map]
  simp only [decide_eq_true_eq, SampleableType.prEvent_uniformSample]
  have hb := hq (view table) candidates hc
  norm_num [HashOutput]
  gcongr

/-- A search of at most `q` candidates, whose law does not depend on one coordinate of a uniform
table, guesses that coordinate with probability at most `q / 2^256`. -/
private theorem prob_uniformTable_search_le {Ω : Type} [Finite Ω] [DecidableEq Ω]
    [SampleableType (Ω → HashOutput)] (x : Ω) (search : (Ω → HashOutput) → ProbComp (Finset HashOutput))
    (hs : ∀ table u, search (Function.update table x u) =ᵈ search table) (q : ℕ)
    (hq : ∀ table s, s ∈ support (search table) → s.card ≤ q) :
    Pr{let z ← ($ᵗ (Ω → HashOutput)) >>= fun table =>
      search table >>= fun s => pure (decide (table x ∈ s))}[z = true] ≤ (q : ℝ≥0∞) / 2 ^ 256 := by
  have he := (seedGenUniform_update_bind x (fun table =>
    search table >>= fun s => pure (decide (table x ∈ s)))).symm
  simp only [Function.update_self] at he
  have hu := he.trans ((EvalDistEq.bind_right _ fun y => EvalDistEq.bind_right _ fun table =>
      EvalDistEq.bind_left (hs table y) _).trans ((OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans
    (EvalDistEq.bind_right _ fun table => OracleComp.EvalDistEq.bind_bind_swap _ _ _)))
  rw [hu.prEvent_eq (· = true)]
  apply prEvent_bind_le_of_forall_le_of_support
  intro table _
  apply prEvent_bind_le_of_forall_le_of_support
  intro candidates hc
  have hm : (($ᵗ HashOutput) >>= fun u => pure (decide (u ∈ candidates)) : ProbComp Bool) =
      (fun u : HashOutput => decide (u ∈ candidates)) <$> ($ᵗ HashOutput) := by
    rw [map_eq_bind_pure_comp]
    rfl
  rw [hm, prEvent_map]
  simp only [decide_eq_true_eq, SampleableType.prEvent_uniformSample]
  have hb := hq table candidates hc
  norm_num [HashOutput]
  gcongr

/-- One coordinate of a uniform table is equal to a value that does not depend on it with
probability at most `1 / 2^256`. -/
private theorem prob_uniformTable_coord_eq_le {Ω : Type} [Finite Ω] [DecidableEq Ω]
    [SampleableType (Ω → HashOutput)] (x : Ω) (other : (Ω → HashOutput) → HashOutput)
    (ho : ∀ table u, other (Function.update table x u) = other table) :
    Pr{let table ← $ᵗ (Ω → HashOutput)}[table x = other table] ≤ 1 / 2 ^ 256 := by
  have h := prob_uniformTable_guess_le x other ho (fun v => pure {v}) 1 (by simp)
  simp only [pure_bind] at h
  simpa [← Function.comp_def pure, ← map_eq_bind_pure_comp, prEvent_map] using h

/-- The dealt keys of two names are equal with probability at most `1 / 2^256`. -/
private theorem prob_dealtKey_eq_le (n n' : KeyName C) :
    Pr{let r ← (do
        let term ← $ᵗ (C.Term → HashOutput)
        let pair ← $ᵗ (C.Pair → HashOutput)
        pure (term, pair) : ProbComp ((C.Term → HashOutput) × (C.Pair → HashOutput)))}[
      n ≠ n' ∧ ∃ k, dealtKey r.1 r.2 n = some k ∧ dealtKey r.1 r.2 n' = some k] ≤ 1 / 2 ^ 256 := by
  rcases n with _ | T | p <;> rcases n' with _ | T' | p' <;>
    simp only [dealtKey, reduceCtorEq, false_and, exists_false, and_false, Option.some.injEq,
      exists_eq_left', ne_eq, KeyName.term.injEq, KeyName.pair.injEq, not_false_eq_true, true_and]
  all_goals try simp only [prEvent_false, zero_le]
  · rw [((OracleComp.EvalDistEq.bind_bind_swap _ _ _)).prEvent_eq]
    apply prEvent_bind_le_of_forall_le_of_support
    intro pair _
    simp only [← Function.comp_def pure, ← map_eq_bind_pure_comp, prEvent_map]
    by_cases h : T = T'
    · simp [h]
    · simpa [h] using prob_uniformTable_coord_eq_le T' (fun term => term T)
        fun _ _ => Function.update_of_ne h _ _
  all_goals
    apply prEvent_bind_le_of_forall_le_of_support
    intro term _
    simp only [← Function.comp_def pure, ← map_eq_bind_pure_comp, prEvent_map]
  · exact prob_uniformTable_coord_eq_le p' (fun _ => term T) fun _ _ => rfl
  · simpa only [eq_comm] using prob_uniformTable_coord_eq_le p (fun _ => term T') fun _ _ => rfl
  · by_cases h : p = p'
    · simp [h]
    · simpa [h] using prob_uniformTable_coord_eq_le p' (fun pair => pair p)
        fun _ _ => Function.update_of_ne h _ _

/-- Two dealt keys are equal, and one of them is hidden, with probability at most `k² / 2^256`. -/
theorem prob_dealt_keys_equal_le (D : C.Coalition) :
    Pr{let r ← (do
        let term ← $ᵗ (C.Term → HashOutput)
        let pair ← $ᵗ (C.Pair → HashOutput)
        pure (term, pair) : ProbComp ((C.Term → HashOutput) × (C.Pair → HashOutput)))}[
      ∃ n n' k, Hidden D n ∧ n ≠ n' ∧ dealtKey r.1 r.2 n = some k ∧ dealtKey r.1 r.2 n' = some k] ≤
      ((prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let name : C.Term ⊕ C.Pair → KeyName C := Sum.elim .term .pair
  let names := Finset.univ.image name
  have hname : ∀ (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) n k,
      dealtKey term pair n = some k → n ∈ names := by
    intro term pair n k h
    rcases n with _ | T | p
    · simp [dealtKey] at h
    · exact Finset.mem_image.2 ⟨.inl T, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.2 ⟨.inr p, Finset.mem_univ _, rfl⟩
  have hcard : names.card ≤ prssKeyCount C := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_sum, card_term C, prssKeyCount, termCount]
    exact Nat.add_le_add_left (card_pair_le C) _
  calc _ ≤ Pr{let r ← (do
        let term ← $ᵗ (C.Term → HashOutput)
        let pair ← $ᵗ (C.Pair → HashOutput)
        pure (term, pair) : ProbComp ((C.Term → HashOutput) × (C.Pair → HashOutput)))}[
      ∃ e ∈ names ×ˢ names, e.1 ≠ e.2 ∧
        ∃ k, dealtKey r.1 r.2 e.1 = some k ∧ dealtKey r.1 r.2 e.2 = some k] := by
        refine prEvent_mono _ _ _ fun r hr => ?_
        obtain ⟨n, n', k, -, hne, hn, hn'⟩ := hr
        exact ⟨(n, n'), Finset.mem_product.2 ⟨hname _ _ _ _ hn, hname _ _ _ _ hn'⟩, hne, k, hn, hn'⟩
    _ ≤ ∑ e ∈ names ×ˢ names, Pr{let r ← (do
        let term ← $ᵗ (C.Term → HashOutput)
        let pair ← $ᵗ (C.Pair → HashOutput)
        pure (term, pair) : ProbComp ((C.Term → HashOutput) × (C.Pair → HashOutput)))}[
      e.1 ≠ e.2 ∧ ∃ k, dealtKey r.1 r.2 e.1 = some k ∧ dealtKey r.1 r.2 e.2 = some k] :=
        prEvent_exists_finset_le _ _ _
    _ ≤ ∑ _e ∈ names ×ˢ names, (1 : ℝ≥0∞) / 2 ^ 256 :=
        Finset.sum_le_sum fun e _ => prob_dealtKey_eq_le e.1 e.2
    _ ≤ _ := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul, mul_one_div, sq]
        gcongr

/-! ## The dealt keys of the real run -/

/-- `k` is the dealt key of the name `n`. -/
def DealtKey (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (n : KeyName C) (k : HashOutput) : Prop :=
  dealtKey term pair n = some k

/-- A counted computation makes no free call. -/
private theorem isQueryBoundP_counted_unallowed (key : KeyName C → HashOutput → Prop) {α : Type}
    (oa : OracleComp (SimulatorSpec C) α) : IsQueryBoundP (counted oa) (Unallowed key) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    have e : counted (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inl t)) : OracleComp (WorldSpec C) _) >>= fun u => counted (k u) := by
      rw [counted_bind]
      rfl
    rw [e]
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl not_false, fun u => ?_⟩
    simpa using ih u

/-- A free computation of allowed calls makes no unallowed call. -/
private theorem isQueryBoundP_free_unallowed (key : KeyName C → HashOutput → Prop) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (h : IsQueryBoundP oa (fun t => ¬ KeyAllowed key t) 0) :
    IsQueryBoundP (free oa) (Unallowed key) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have e : free (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= fun u => free (k u) := by
      rw [free_bind]
      rfl
    rw [e]
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨h.1, fun u => ?_⟩
    simpa using ih u (by simpa using h.2 u)

/-- A computation of `H` and `PRG` with no call of `P` keeps this bound in the local oracles. -/
private theorem isQueryBoundP_liftComp_ro (P : (LocalSpec C).Domain → Prop) [DecidablePred P] {α : Type}
    (oa : OracleComp (RoSpec C) α) (h : IsQueryBoundP oa (fun t => P (.inr t)) 0) :
    IsQueryBoundP (liftComp oa (LocalSpec C)) P 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inr t)) : OracleComp (LocalSpec C) _) >>= fun u =>
          liftComp (k u) (LocalSpec C) := by
      rw [liftComp_bind]
      rfl
    rw [e]
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨h.1, fun u => ?_⟩
    simpa using ih u (by simpa using h.2 u)

/-- The bits of a PRG under a key of its name make only allowed calls. -/
private theorem isQueryBoundP_prgBits_allowed (key : KeyName C → HashOutput → Prop) (name : KeyName C)
    (k : HashOutput) (hk : key name k) (ρ idx count : ℕ) :
    IsQueryBoundP (prgBits name k ρ idx count) (fun t => ¬ KeyAllowed key (.inr t)) 0 := by
  unfold prgBits
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind ?_ fun _ _ => isQueryBoundP_pure _ _ 0
  simpa using queryBound_mapM (fun t => ¬ KeyAllowed key (.inr t)) (fun position =>
    (query (spec := RoSpec C) (.inr (name, k, ρ, idx, position)) : OracleComp (RoSpec C) Bit)) 0
    (List.range count) fun position _ =>
      (isQueryBoundP_query_iff (fun t => ¬ KeyAllowed key (.inr t)) _ _).2 fun h => absurd hk h

/-- The streams of operator `i` under its dealt keys make only allowed calls. -/
private theorem isQueryBoundP_prssStreams_allowed {R : Type} [Zero R] (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (stream : KeyName C → HashOutput → OracleComp (RoSpec C) (ℕ → R))
    (hs : ∀ name k, DealtKey term pair name k →
      IsQueryBoundP (stream name k) (fun t => ¬ KeyAllowed (DealtKey term pair) (.inr t)) 0)
    (i : C.Party) :
    IsQueryBoundP (prssStreams stream (dealtPrssKeys term pair i) i)
      (fun t => ¬ KeyAllowed (DealtKey term pair) (.inr t)) 0 := by
  unfold prssStreams
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind ?_ fun _ _ => ?_
  · simpa using queryBound_mapM _ _ 0 C.terms fun T _ => by
      split_ifs with hT
      · exact hs _ _ (by simp [DealtKey, dealtKey, dealtPrssKeys, hT])
      · exact isQueryBoundP_pure _ _ 0
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind ?_ fun _ _ => isQueryBoundP_pure _ _ 0
  simpa using queryBound_mapM _ _ 0 C.parties fun j _ => by
    split_ifs with hj
    · exact isQueryBoundP_pure _ _ 0
    · exact hs _ _ (by simp [DealtKey, dealtKey, dealtPrssKeys, hj])

omit [Fintype E] [DecidableEq E] in
/-- The calls of operator `i` under its dealt keys make only allowed calls. -/
private theorem isQueryBoundP_randStreams_allowed [SampleableType E] (K : Constants C E)
    (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (i : C.Party) :
    ∀ (ρ : ℕ) (calls : List RandCall),
    IsQueryBoundP (randStreams K prgBits (dealtPrssKeys term pair i) i ρ calls)
      (fun t => ¬ KeyAllowed (DealtKey term pair) (.inr t)) 0
  | _, [] => isQueryBoundP_pure _ _ 0
  | ρ, call :: calls => by
    unfold randStreams
    rw [← Nat.zero_add 0]
    refine isQueryBoundP_bind ?_ fun _ _ => ?_
    · cases call with
      | elements idx count =>
        refine (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_prssStreams_allowed term pair _
          (fun name k hk => (isQueryBoundP_map_iff _ _ _).2
            (isQueryBoundP_prgBits_allowed _ name k hk ρ idx _)) i)
      | bits idx count =>
        exact (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_prssStreams_allowed term pair _
          (fun name k hk => isQueryBoundP_prgBits_allowed _ name k hk ρ idx _) i)
    rw [← Nat.zero_add 0]
    exact isQueryBoundP_bind (isQueryBoundP_randStreams_allowed K term pair i (ρ + 1) calls)
      fun _ _ => isQueryBoundP_pure _ _ 0

section Keyed

variable [SampleableType E] (K : Constants C E) (label : ℕ) (calls : List RandCall) (D : C.Coalition)
  (A : Adversary C E Unit (C.Party → Option (PrssKeys C)) (Finset C.Party)) (x : C.Party → Unit) (z : Aux)
  (Z : Distinguisher C A.State (List (RandOutput C E)))

/-- The real run after the deal of the keys `term` and `pair`, with the distinguisher. -/
def prssRandRealAfter (st : A.State) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) :
    OracleComp (WorldSpec C) Bool := do
  let a ← counted (liftComp (A.answer st fun i =>
    if i ∈ D.1 then some (dealtPrssKeys term pair i) else none) (SimulatorSpec C))
  let outputs ← free (honestStreams K prgBits (honestReceivers D a.2) term pair label calls)
  counted (liftComp (Z (a.1, outputs)) (SimulatorSpec C))

/-- The real run with its distinguisher, which also gives the dealt keys. -/
def prssRandRealKeyed :
    OracleComp (WorldSpec C) ((C.Term → HashOutput) × (C.Pair → HashOutput) × Bool) := do
  let st ← counted (liftComp (A.start (corruptInputs D x) z) (SimulatorSpec C))
  let term ← free (liftComp ($ᵗ (C.Term → HashOutput)) (LocalSpec C))
  let pair ← free (liftComp ($ᵗ (C.Pair → HashOutput)) (LocalSpec C))
  let b ← prssRandRealAfter K label calls D A Z st term pair
  pure (term, pair, b)

/-- The real run is the keyed run without the dealt keys. -/
theorem prssRandReal_eq_keyed :
    prssRandReal K label calls D A x z Z = (fun r => r.2.2) <$> prssRandRealKeyed K label calls D A x z Z := by
  unfold prssRandReal prssRandRealKeyed prssRandRealAfter distinguish
  rw [realExecution_prssRand]
  simp [worldRoles]

/-- After the deal, each free stream of the real run uses the dealt key of its name. No free call is
a hash of a stream key. -/
theorem prssRandRealAfter_allowed (st : A.State) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) :
    IsQueryBoundP (prssRandRealAfter K label calls D A Z st term pair)
      (Unallowed (DealtKey term pair)) 0 := by
  unfold prssRandRealAfter
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (isQueryBoundP_counted_unallowed _ _) fun a _ => ?_
  rw [← Nat.zero_add 0]
  refine isQueryBoundP_bind (isQueryBoundP_free_unallowed _ _ ?_) fun _ _ =>
    isQueryBoundP_counted_unallowed _ _
  refine isQueryBoundP_sequenceFin _ fun j => by
    split_ifs
    · exact (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_liftComp_ro _ _
        (isQueryBoundP_randStreams_allowed K term pair j label calls))
    · exact isQueryBoundP_pure _ _ 0

end Keyed

/-! ## The calls do not depend on a hidden key value -/

/-- Swap two key values at one name. -/
def nameKeySwap (n₀ : KeyName C) (a b : HashOutput) (x : KeyName C × HashOutput) : KeyName C × HashOutput :=
  if x.1 = n₀ then (x.1, Equiv.swap a b x.2) else x

/-- Swap two key values in the free streams of one name. Every other call stays. -/
def worldNameRename (n₀ : KeyName C) (a b : HashOutput) :
    QueryImpl (WorldSpec C) (OracleComp (WorldSpec C)) := fun q =>
  match q with
  | .inr (.inr (.inr x)) => OracleComp.lift (OracleSpec.query (spec := WorldSpec C)
      (.inr (.inr (.inr ((nameKeySwap n₀ a b (x.1, x.2.1)).1, (nameKeySwap n₀ a b (x.1, x.2.1)).2, x.2.2)))))
  | q => OracleComp.lift (OracleSpec.query q)

private theorem nameKeySwap_involutive (n₀ : KeyName C) (a b : HashOutput) :
    Function.Involutive (nameKeySwap n₀ a b) := by
  rintro ⟨n, k⟩
  by_cases h : n = n₀ <;> simp [nameKeySwap, h]

/-- One world query with the swap at a hidden name is the query with the key cache swapped. -/
private theorem lazyKeyWorld_query_renameName (prims : Primitives) (D : C.Coalition) (n₀ : KeyName C)
    (h₀ : Hidden D n₀) (a b : HashOutput) (q : (WorldSpec C).Domain) (st : HashCache C × KeyCache C) :
    Prod.map id (fun st => (st.1, involutionCache (nameKeySwap n₀ a b) st.2)) <$>
      (lazyKeyWorld prims D q).run st =
      (simulateQ (lazyKeyWorld prims D) (worldNameRename n₀ a b q)).run
        (st.1, involutionCache (nameKeySwap n₀ a b) st.2) := by
  rcases q with ((u | q | x) | p) | (u | q | x)
  all_goals try (simp [worldNameRename, lazyKeyWorld, Functor.map_map, Prod.map]; done)
  by_cases hx : Hidden D x.1
  · have hx' : Hidden D (nameKeySwap n₀ a b (x.1, x.2.1)).1 := by
      unfold nameKeySwap; split_ifs <;> exact hx
    simp only [worldNameRename]
    try erw [simulateQ_spec_query]
    simp only [lazyKeyWorld, ite_eq_left hx, ite_eq_left hx', StateT.run_mk]
    have hm := congrArg (fun p : ProbComp (Digest × KeyCache C) =>
      (fun r => (prims.aes.eval r.1 x.2.2, (st.1, r.2))) <$> p)
      (randomOracle_involution _ (nameKeySwap_involutive n₀ a b) (x.1, x.2.1) st.2)
    simpa only [Functor.map_map, Function.comp_def, Prod.map, id_eq, Prod.eta] using hm
  · have hn : x.1 ≠ n₀ := fun e => hx (e ▸ h₀)
    have hs : nameKeySwap n₀ a b (x.1, x.2.1) = (x.1, x.2.1) := by simp [nameKeySwap, hn]
    simp only [worldNameRename]
    try erw [simulateQ_spec_query]
    simp only [lazyKeyWorld, hs, ite_eq_right hx, StateT.run_mk, Functor.map_map]
    simp only [nameKeySwap]
    rw [ite_eq_right hn]
    rfl

/-- With independent AES keys, a swap of two key values at one hidden name keeps the law of the
result and of the hash cache. -/
theorem evalDist_lazyKeyWorld_renameName (prims : Primitives) (D : C.Coalition) (n₀ : KeyName C)
    (h₀ : Hidden D n₀) (a b : HashOutput) {α : Type} (game : OracleComp (WorldSpec C) α)
    (s : HashCache C) :
    ((fun r => (r.1, r.2.1)) <$> (simulateQ (lazyKeyWorld prims D) game).run (s, ∅)) =ᵈ
      ((fun r => (r.1, r.2.1)) <$>
        (simulateQ (lazyKeyWorld prims D) (simulateQ (worldNameRename n₀ a b) game)).run (s, ∅)) := by
  have h : (Prod.map id (fun st => (st.1, involutionCache (nameKeySwap n₀ a b) st.2)) <$>
      (simulateQ (lazyKeyWorld prims D) game).run (s, ∅)) =ᵈ
      (simulateQ (lazyKeyWorld prims D) (simulateQ (worldNameRename n₀ a b) game)).run
        (s, involutionCache (nameKeySwap n₀ a b) ∅) := by
    rw [← QueryImpl.simulateQ_compose]
    apply evalDist_simulateQ_state_projection
    intro q state
    rw [QueryImpl.apply_compose, lazyKeyWorld_query_renameName prims D n₀ h₀]
  rw [involutionCache_empty] at h
  have hm := EvalDistEq.map_congr (fun r : α × HashCache C × KeyCache C => (r.1, r.2.1)) h
  simpa only [Functor.map_map, Function.comp_def, Prod.map, id_eq] using hm

/-- The swap of `worldNameRename` on the oracles of `H` and `PRG`. -/
private def roNameRename (n₀ : KeyName C) (a b : HashOutput) :
    QueryImpl (RoSpec C) (OracleComp (RoSpec C)) := fun q => match q with
  | .inl q => query (spec := RoSpec C) (.inl q)
  | .inr x => query (spec := RoSpec C)
      (.inr ((nameKeySwap n₀ a b (x.1, x.2.1)).1, (nameKeySwap n₀ a b (x.1, x.2.1)).2, x.2.2))

/-- The swap of `worldNameRename` on the local oracles. -/
private def localNameRename (n₀ : KeyName C) (a b : HashOutput) :
    QueryImpl (LocalSpec C) (OracleComp (LocalSpec C)) := fun q => match q with
  | .inl u => OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inl u))
  | .inr q => liftComp (roNameRename n₀ a b q) _

private theorem localNameRename_ro (n₀ : KeyName C) (a b : HashOutput) {α : Type}
    (p : OracleComp (RoSpec C) α) :
    simulateQ (localNameRename n₀ a b) (liftComp p (LocalSpec C)) =
      liftComp (simulateQ (roNameRename n₀ a b) p) (LocalSpec C) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp
  | query_bind q k ih =>
    simp only [liftComp_bind, simulateQ_bind, ih]
    congr 1
    change simulateQ (localNameRename n₀ a b)
      (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr q))) =
      liftComp (simulateQ (roNameRename n₀ a b) (OracleComp.lift (OracleSpec.query q))) _
    rw [simulateQ_spec_query, simulateQ_spec_query]
    rfl

private theorem worldNameRename_counted (n₀ : KeyName C) (a b : HashOutput) {α : Type}
    (oa : OracleComp (SimulatorSpec C) α) :
    simulateQ (worldNameRename n₀ a b) (counted oa) = counted oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [counted_pure]
  | query_bind t k ih =>
    rw [counted_bind, simulateQ_bind]
    simp only [ih]
    rfl

private theorem worldNameRename_free (n₀ : KeyName C) (a b : HashOutput) {α : Type}
    (oa : OracleComp (LocalSpec C) α) :
    simulateQ (worldNameRename n₀ a b) (free oa) = free (simulateQ (localNameRename n₀ a b) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [free_bind, simulateQ_bind, simulateQ_bind, free_bind]
    simp only [ih]
    rcases t with u | q | x <;> rfl

private theorem roNameRename_prgBits (n₀ : KeyName C) (a b : HashOutput) (name : KeyName C)
    (key : HashOutput) (ρ idx count : ℕ) :
    simulateQ (roNameRename n₀ a b) (prgBits name key ρ idx count) =
      prgBits (nameKeySwap n₀ a b (name, key)).1 (nameKeySwap n₀ a b (name, key)).2 ρ idx count := by
  unfold prgBits
  erw [simulateQ_bind, simulateQ_list_mapM]
  rfl

/-- The streams of operator `i` agree when each used stream agrees. -/
private theorem prssStreams_congr {R : Type} [Zero R]
    (s₁ s₂ : KeyName C → HashOutput → OracleComp (RoSpec C) (ℕ → R)) (p₁ p₂ : PrssKeys C) (i : C.Party)
    (ht : ∀ T, i ∈ C.holders T → s₁ (.term T) (p₁.term T) = s₂ (.term T) (p₂.term T))
    (hp : ∀ j (h : j ≠ i), s₁ (.pair (C.pairOf i j (Ne.symm h))) (p₁.pair j) =
      s₂ (.pair (C.pairOf i j (Ne.symm h))) (p₂.pair j)) :
    prssStreams s₁ p₁ i = prssStreams s₂ p₂ i := by
  simp (config := { contextual := true }) only [prssStreams, ht, hp, ne_eq, not_false_eq_true]

omit [Fintype E] [DecidableEq E] in
/-- The calls of operator `i` agree when each used stream agrees. -/
private theorem randStreams_congr [SampleableType E] (K : Constants C E)
    (b₁ b₂ : KeyName C → HashOutput → ℕ → ℕ → ℕ → OracleComp (RoSpec C) (ℕ → Bit))
    (p₁ p₂ : PrssKeys C) (i : C.Party)
    (ht : ∀ T, i ∈ C.holders T → b₁ (.term T) (p₁.term T) = b₂ (.term T) (p₂.term T))
    (hp : ∀ j (h : j ≠ i), b₁ (.pair (C.pairOf i j (Ne.symm h))) (p₁.pair j) =
      b₂ (.pair (C.pairOf i j (Ne.symm h))) (p₂.pair j)) :
    ∀ (ρ : ℕ) (calls : List RandCall), randStreams K b₁ p₁ i ρ calls = randStreams K b₂ p₂ i ρ calls
  | _, [] => rfl
  | ρ, call :: calls => by
    simp only [randStreams, randStreams_congr K b₁ b₂ p₁ p₂ i ht hp (ρ + 1) calls]
    congr 1
    cases call with
    | elements idx count =>
      simp only [callStreams]
      rw [prssStreams_congr (fun name key => (fun b g => K.encode.symm fun e => b (elementBits * g + e)) <$>
          b₁ name key ρ idx (elementBits * count))
        (fun name key => (fun b g => K.encode.symm fun e => b (elementBits * g + e)) <$>
          b₂ name key ρ idx (elementBits * count)) p₁ p₂ i
        (fun T hT => by simp only [ht T hT]) (fun j h => by simp only [hp j h])]
    | bits idx count =>
      simp only [callStreams]
      rw [prssStreams_congr (fun name key => b₁ name key ρ idx count) (fun name key => b₂ name key ρ idx count)
        p₁ p₂ i (fun T hT => by simp only [ht T hT]) (fun j h => by simp only [hp j h])]

omit [Fintype E] [DecidableEq E] in
/-- The rename on the calls of operator `i` renames the key of each stream. -/
private theorem roNameRename_randStreams [SampleableType E] (K : Constants C E) (n₀ : KeyName C)
    (a b : HashOutput) (prss : PrssKeys C) (i : C.Party) :
    ∀ (ρ : ℕ) (calls : List RandCall),
    simulateQ (roNameRename n₀ a b) (randStreams K prgBits prss i ρ calls) =
      randStreams K (fun name key => prgBits (nameKeySwap n₀ a b (name, key)).1 (nameKeySwap n₀ a b (name, key)).2) prss i ρ calls
  | _, [] => by simp [randStreams]
  | ρ, call :: calls => by
    cases call <;> simp [randStreams, callStreams, prssStreams, simulateQ_list_mapM, simulateQ_ite,
      simulateQ_dite, roNameRename_prgBits, roNameRename_randStreams K n₀ a b prss i (ρ + 1) calls]

omit [Fintype E] [DecidableEq E] in
/-- The rename on the honest streams is the honest streams with the renamed table of keys. -/
private theorem localNameRename_honestStreams [SampleableType E] (K : Constants C E) (n₀ : KeyName C)
    (a b : HashOutput) (drawers : Finset C.Party) (term term' : C.Term → HashOutput)
    (pair pair' : C.Pair → HashOutput) (label : ℕ) (calls : List RandCall)
    (h : ∀ i, randStreams K (fun name key => prgBits (nameKeySwap n₀ a b (name, key)).1 (nameKeySwap n₀ a b (name, key)).2)
      (dealtPrssKeys term pair i) i label calls =
      randStreams K prgBits (dealtPrssKeys term' pair' i) i label calls) :
    simulateQ (localNameRename n₀ a b) (honestStreams K prgBits drawers term pair label calls) =
      honestStreams K prgBits drawers term' pair' label calls := by
  unfold honestStreams
  rw [simulateQ_sequenceFin]
  congr 1
  funext j
  split_ifs
  · rw [simulateQ_map, localNameRename_ro, roNameRename_randStreams, h]
  · simp

section Rename

variable [SampleableType E] (K : Constants C E) (label : ℕ) (calls : List RandCall) (D : C.Coalition)
  (A : Adversary C E Unit (C.Party → Option (PrssKeys C)) (Finset C.Party))
  (Z : Distinguisher C A.State (List (RandOutput C E)))

/-- For a hidden term, the run after the deal with the key of the term swapped in its free streams
is the run with the new key in the table. The leak holds no key of a hidden term. -/
theorem prssRandRealAfter_rename_term (st : A.State) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (T : C.Term) (hT : Hidden D (.term T)) (u : HashOutput) :
    simulateQ (worldNameRename (.term T) (term T) u) (prssRandRealAfter K label calls D A Z st term pair) =
      prssRandRealAfter K label calls D A Z st (Function.update term T u) pair := by
  have hleak : ∀ i ∈ D.1, dealtPrssKeys (Function.update term T u) pair i = dealtPrssKeys term pair i := by
    intro i hi
    simp only [dealtPrssKeys, PrssKeys.mk.injEq, and_true]
    funext T'
    by_cases hT' : T' = T
    · subst hT'
      have : i ∉ C.holders T' := fun h => hT ⟨i, hi, h⟩
      simp [this]
    · simp [Function.update_of_ne hT']
  unfold prssRandRealAfter
  simp only [simulateQ_bind, worldNameRename_counted, worldNameRename_free]
  have hl : (fun i => if i ∈ D.1 then some (dealtPrssKeys (Function.update term T u) pair i) else none) =
      (fun i => if i ∈ D.1 then some (dealtPrssKeys term pair i) else none) := by
    funext i
    split_ifs with hi
    · rw [hleak i hi]
    · rfl
  rw [hl]
  refine bind_congr' _ fun r => ?_
  rw [localNameRename_honestStreams K _ _ _ _ term (Function.update term T u) pair pair]
  intro i
  refine randStreams_congr K _ _ _ _ i (fun T' hT' => ?_) (fun j h => ?_) label calls
  · by_cases hT'' : T' = T
    · subst hT''
      simp [dealtPrssKeys, hT', nameKeySwap]
    · simp [dealtPrssKeys, hT', nameKeySwap, hT'']
  · simp [dealtPrssKeys, h, nameKeySwap]

/-- For a hidden pair, the run after the deal with the key of the pair swapped in its free streams
is the run with the new key in the table. The leak holds no key of a hidden pair. -/
theorem prssRandRealAfter_rename_pair (st : A.State) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (p : C.Pair) (hp : Hidden D (.pair p)) (u : HashOutput) :
    simulateQ (worldNameRename (.pair p) (pair p) u) (prssRandRealAfter K label calls D A Z st term pair) =
      prssRandRealAfter K label calls D A Z st term (Function.update pair p u) := by
  have hleak : ∀ i ∈ D.1, dealtPrssKeys term (Function.update pair p u) i = dealtPrssKeys term pair i := by
    intro i hi
    simp only [dealtPrssKeys, PrssKeys.mk.injEq, true_and]
    funext j
    split_ifs with hj
    · rfl
    · refine Function.update_of_ne (fun he => ?_) _ _
      rcases pairOf_left_or_right i j (Ne.symm hj) with h1 | h1 <;> rw [he] at h1
      · exact hp.1 (h1 ▸ hi)
      · exact hp.2 (h1 ▸ hi)
  unfold prssRandRealAfter
  simp only [simulateQ_bind, worldNameRename_counted, worldNameRename_free]
  have hl : (fun i => if i ∈ D.1 then some (dealtPrssKeys term (Function.update pair p u) i) else none) =
      (fun i => if i ∈ D.1 then some (dealtPrssKeys term pair i) else none) := by
    funext i
    split_ifs with hi
    · rw [hleak i hi]
    · rfl
  rw [hl]
  refine bind_congr' _ fun r => ?_
  rw [localNameRename_honestStreams K _ _ _ _ term term pair (Function.update pair p u)]
  intro i
  refine randStreams_congr K _ _ _ _ i (fun T' hT' => ?_) (fun j h => ?_) label calls
  · simp [dealtPrssKeys, hT', nameKeySwap]
  · by_cases he : C.pairOf i j (Ne.symm h) = p
    · subst he
      simp [dealtPrssKeys, h, nameKeySwap]
    · simp [dealtPrssKeys, h, nameKeySwap, he]

end Rename

/-! ## The bound -/

section Bound

variable [SampleableType E] (K : Constants C E) (label : ℕ) (calls : List RandCall) (D : C.Coalition)
  (A : Adversary C E Unit (C.Party → Option (PrssKeys C)) (Finset C.Party)) (x : C.Party → Unit) (z : Aux)
  (Z : Distinguisher C A.State (List (RandOutput C E))) (prims : Primitives)

/-- The real run up to the deal of the keys. -/
private def prssRandPrefix :
    OracleComp (WorldSpec C) (A.State × (C.Term → HashOutput) × (C.Pair → HashOutput)) := do
  let st ← counted (liftComp (A.start (corruptInputs D x) z) (SimulatorSpec C))
  let term ← free (liftComp ($ᵗ (C.Term → HashOutput)) (LocalSpec C))
  let pair ← free (liftComp ($ᵗ (C.Pair → HashOutput)) (LocalSpec C))
  pure (st, term, pair)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
private theorem prssRandRealKeyed_eq_prefix :
    prssRandRealKeyed K label calls D A x z Z = prssRandPrefix D A x z >>= fun p =>
      (fun b => (p.2.1, p.2.2, b)) <$> prssRandRealAfter K label calls D A Z p.1 p.2.1 p.2.2 := by
  simp [prssRandRealKeyed, prssRandPrefix, bind_assoc, map_eq_bind_pure_comp]

/-- A private sampling makes only calls of the sampling oracle. -/
private theorem isQueryBoundP_liftComp_prob (key : KeyName C → HashOutput → Prop) {α : Type}
    (p : ProbComp α) : IsQueryBoundP (liftComp p (LocalSpec C)) (fun t => ¬ KeyAllowed key t) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inl t)) : OracleComp (LocalSpec C) _) >>= fun u =>
          liftComp (k u) (LocalSpec C) := by
      rw [liftComp_bind]
      rfl
    rw [e]
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl fun h => h trivial, fun u => ?_⟩
    simpa only [Nat.zero_sub, ite_self] using ih u

/-- The relation with no key. -/
private def NoKey : KeyName C → HashOutput → Prop := fun _ _ => False

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
private theorem prssRandPrefix_allowed :
    IsQueryBoundP (prssRandPrefix D A x z) (Unallowed (NoKey (C := C))) 0 := by
  have hs {α : Type} (p : ProbComp α) :
      IsQueryBoundP (free (liftComp p (LocalSpec C))) (Unallowed (NoKey (C := C))) 0 :=
    isQueryBoundP_free_unallowed NoKey _ (isQueryBoundP_liftComp_prob NoKey p)
  unfold prssRandPrefix
  generalize ($ᵗ (C.Term → HashOutput) : ProbComp _) = pt
  generalize ($ᵗ (C.Pair → HashOutput) : ProbComp _) = pp
  show IsQueryBoundP _ _ (0 + 0)
  apply isQueryBoundP_bind
  · exact isQueryBoundP_counted_unallowed _ _
  intro st _
  show IsQueryBoundP _ _ (0 + 0)
  apply isQueryBoundP_bind
  · exact hs _
  intro term _
  show IsQueryBoundP _ _ (0 + 0)
  apply isQueryBoundP_bind
  · exact hs _
  intro pair _
  exact isQueryBoundP_pure _ _ 0

/-- A raised flag of the keyed run gives dealt keys that are not apart, or apart keys and a hit. -/
private theorem prssRandKeyed_bad (r : ((C.Term → HashOutput) × (C.Pair → HashOutput) × Bool) × KeyJointState C)
    (hr : r ∈ support ((simulateQ (jointKeyWorld prims D false)
      (prssRandRealKeyed K label calls D A x z Z)).run keyJointInitial)) (hb : r.2.bad = true) :
    ¬ KeysApart D (DealtKey r.1.1 r.1.2.1) ∨
      (KeysApart D (DealtKey r.1.1 r.1.2.1) ∧ KeyHit D (DealtKey r.1.1 r.1.2.1) r.2.hash) := by
  rw [prssRandRealKeyed_eq_prefix, simulateQ_bind, StateT.run_bind] at hr
  obtain ⟨p, hp, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
  have h0 := (jointKeyWorld_run_inv prims D NoKey (fun _ _ _ _ h => h.elim) _
    (prssRandPrefix_allowed D A x z) keyJointInitial (by simp [JointInv, keyJointInitial, NoKey]) p hp).1
  rw [simulateQ_map, StateT.run_map, support_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  by_cases hk : KeysApart D (DealtKey p.1.2.1 p.1.2.2)
  · refine Or.inr ⟨hk, ?_⟩
    have hs : JointInv D (DealtKey p.1.2.1 p.1.2.2) p.2 :=
      ⟨fun k n h => (h0.1 k n h).2.1.elim, fun h => by obtain ⟨_, _, hf, -⟩ := h0.2 h; exact hf.elim⟩
    exact (jointKeyWorld_run_inv prims D _ hk _ (prssRandRealAfter_allowed K label calls D A Z _ _ _)
      p.2 hs r' hr').1.2 hb
  · exact Or.inl hk

/-- A private sampling in the joint world draws a uniform value and keeps the state. -/
private theorem jointKeyWorld_free_prob {α : Type} (p : ProbComp α) (s : KeyJointState C) :
    (simulateQ (jointKeyWorld prims D false) (free (liftComp p (LocalSpec C)))).run s =ᵈ
      (fun a => (a, s)) <$> p := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    have e : (simulateQ (jointKeyWorld prims D false)
        (free (liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C)))).run s =
        (liftM (unifSpec.query t) : ProbComp _) >>= fun u =>
          (simulateQ (jointKeyWorld prims D false) (free (liftComp (k u) (LocalSpec C)))).run s := by
      have hq : (simulateQ (jointKeyWorld prims D false)
          (free (liftComp (liftM (OracleSpec.query t) : ProbComp _) (LocalSpec C)))).run s =
          (fun u => (u, s)) <$> (liftM (unifSpec.query t) : ProbComp _) := by
        simp only [free]
        change (simulateQ (jointKeyWorld prims D false)
          (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr (.inl t))))).run s = _
        rw [simulateQ_spec_query]
        simp [jointKeyWorld, jointKeyWorldCore, jointLocal, onJointHash, keyJointRisk, unifFwdImpl,
          StateT.run_mk]
      rw [liftComp_bind, free_bind, simulateQ_bind, StateT.run_bind, hq, bind_map_left]
    rw [e, map_bind]
    exact EvalDistEq.bind_right _ fun u => ih u s

/-- The keys whose stream key the hash cache holds. -/
def streamCells (h : HashCache C) : Finset HashOutput := Finset.univ.filter fun k => h (.streamKey k) ≠ none

/-- The hash inputs that one world call can add to the hash cache of the joint world. -/
private def worldCells (D : C.Coalition) : (WorldSpec C).Domain → List (Query C)
  | .inl (.inl u) => prssCountedHashInputs u
  | .inl (.inr x) => [x.1]
  | .inr (.inr (.inr x)) => if Hidden D x.1 then [] else [.streamKey x.2.1]
  | .inr u => prssCountedHashInputs u

/-- One call of the joint world changes the hash cache only at its own inputs. -/
private theorem jointKeyWorld_query_other (prims : Primitives) (D : C.Coalition) (t : (WorldSpec C).Domain)
    (s : KeyJointState C) (r : (WorldSpec C).Range t × KeyJointState C)
    (hr : r ∈ support ((jointKeyWorld prims D false t).run s)) (target : Query C)
    (ht : target ∉ worldCells D t) : r.2.hash target = s.hash target := by
  have hloc : ∀ (u : (LocalSpec C).Domain) (r : (LocalSpec C).Range u × KeyJointState C),
      r ∈ support ((jointLocal prims false u).run s) → target ∉ prssCountedHashInputs u →
        r.2.hash target = s.hash target := by
    intro u r hr ht
    rw [jointLocal_false] at hr
    simp only [onJointHash, StateT.run_mk, support_map, Set.mem_image] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    exact prssLocalAnswer_other prims u target ht s.hash r' hr'
  simp only [jointKeyWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  change r'.2.hash target = s.hash target
  rcases t with (u | x) | u
  · exact hloc u r' hr' ht
  · have hne : target ≠ x.1 := by simpa [worldCells] using ht
    simp only [jointKeyWorldCore, jointProgram, StateT.run_mk] at hr'
    have hp : ∀ r ∈ support ((onJointHash (programAnswer x)).run s), r.2.hash target = s.hash target := by
      intro r hr
      simp only [onJointHash, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨r'', hr'', rfl⟩ := hr
      simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hr''
      split_ifs at hr''
      · simp at hr''
        rw [hr'']
      · simp at hr''
        rw [hr'']
        exact QueryCache.cacheQuery_of_ne _ _ hne
    split at hr'
    · simp only [Bool.false_and, Bool.false_eq_true, ite_false] at hr'
      exact hp r' hr'
    · exact hp r' hr'
  · rcases u with u | q | x
    · exact hloc (.inl u) r' hr' (by simpa [worldCells] using ht)
    · exact hloc (.inr (.inl q)) r' hr' (by simpa [worldCells] using ht)
    · by_cases hx : Hidden D x.1
      · simp only [jointKeyWorldCore, hx, ite_true] at hr'
        simp only [StateT.run_bind, StateT.run_pure, support_bind, Set.mem_iUnion, support_pure,
          Set.mem_singleton_iff] at hr'
        obtain ⟨p, hp, rfl⟩ := hr'
        simp only [jointHidden, StateT.run_mk] at hp
        split at hp
        · simp at hp
          rw [hp]
        · simp only [Bool.false_eq_true, ite_false, support_bind, Set.mem_iUnion, support_pure,
            Set.mem_singleton_iff] at hp
          obtain ⟨_, _, rfl⟩ := hp
          rfl
      · simp only [jointKeyWorldCore, hx, ite_false] at hr'
        exact hloc (.inr (.inr x)) r' hr' (by simpa [worldCells, hx, prssCountedHashInputs] using ht)

private theorem card_streamKey_mem_le (L : List (Query C)) :
    (Finset.univ.filter fun k : HashOutput => Query.streamKey k ∈ L).card ≤ L.length := by
  refine (Finset.card_le_card_of_injOn (fun k => Query.streamKey k) (by
    intro k hk
    exact List.mem_toFinset.2 (Finset.mem_filter.1 hk).2) (by
    intro a _ b _ h
    exact Query.streamKey.inj h)).trans (List.toFinset_card_le L)

/-- One allowed call adds at most one stream key to the hash cache, and none when it is free, apart
from the keys of known names. -/
private theorem jointKeyWorld_query_newCells (prims : Primitives) (D : C.Coalition)
    (key : KeyName C → HashOutput → Prop) (t : (WorldSpec C).Domain) (ht : ¬ Unallowed key t)
    (s : KeyJointState C) (r : (WorldSpec C).Range t × KeyJointState C)
    (hr : r ∈ support ((jointKeyWorld prims D false t).run s)) :
    ((streamCells r.2.hash \ streamCells s.hash).filter fun k => ∀ n', ¬ Hidden D n' → ¬ key n' k).card ≤
      if WorldCounted t then 1 else 0 := by
  refine (Finset.card_le_card (t := Finset.univ.filter fun k =>
    Query.streamKey k ∈ worldCells D t ∧ ∀ n', ¬ Hidden D n' → ¬ key n' k) fun k hk => ?_).trans ?_
  · simp only [Finset.mem_filter, Finset.mem_sdiff, streamCells, Finset.mem_univ, true_and, not_not] at hk
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, hk.2⟩
    by_contra hc
    exact hk.1.1 ((jointKeyWorld_query_other prims D t s r hr _ hc).trans hk.1.2)
  · rcases t with (u | x) | u
    · refine (Finset.card_le_card fun k hk => ?_).trans
        ((card_streamKey_mem_le (worldCells D (.inl (.inl u)))).trans ?_)
      · simp only [Finset.mem_filter] at hk ⊢
        exact ⟨hk.1, hk.2.1⟩
      rw [worldCells, prssCountedHashInputs_length]
      rfl
    · refine (Finset.card_le_card fun k hk => ?_).trans
        ((card_streamKey_mem_le (worldCells D (.inl (.inr x)))).trans ?_)
      · simp only [Finset.mem_filter] at hk ⊢
        exact ⟨hk.1, hk.2.1⟩
      simp [worldCells, WorldCounted]
    · rw [show WorldCounted (Sum.inr u : (WorldSpec C).Domain) = False from rfl, ite_eq_right not_false]
      refine le_of_eq (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun k _ hk' => ?_))
      obtain ⟨hk, hP⟩ := hk'
      simp only [Unallowed, not_not] at ht
      rcases u with u | q | x
      · simp [worldCells, prssCountedHashInputs] at hk
      · simp only [worldCells, prssCountedHashInputs] at hk
        split_ifs at hk
        · exact ht k (List.mem_singleton.1 hk).symm
        · simp at hk
      · simp only [worldCells] at hk
        split_ifs at hk with hx
        · simp at hk
        · have hk' := List.mem_singleton.1 hk
          simp only [Query.streamKey.injEq] at hk'
          subst hk'
          exact hP x.1 hx ht

/-- A hit cell is a cell of a counted call. In the world with independent AES keys, a run of at most
`n` counted calls adds at most `n` stream keys to the hash cache, apart from the keys of known names
that the free streams use. -/
theorem jointKeyWorld_streamCells_le (prims : Primitives) (D : C.Coalition)
    (key : KeyName C → HashOutput → Prop) {α : Type} (oa : OracleComp (WorldSpec C) α) (n : ℕ)
    (hn : IsQueryBoundP oa WorldCounted n) (hoa : IsQueryBoundP oa (Unallowed key) 0) (s : KeyJointState C) :
    ∀ r ∈ support ((simulateQ (jointKeyWorld prims D false) oa).run s),
      ((streamCells r.2.hash \ streamCells s.hash).filter fun k => ∀ n', ¬ Hidden D n' → ¬ key n' k).card ≤ n := by
  induction oa using OracleComp.inductionOn generalizing s n with
  | pure a =>
    intro r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp
  | query_bind t k ih =>
    intro r hr
    rw [isQueryBoundP_query_bind_iff] at hn hoa
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query] at hr
    obtain ⟨p, hp, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
    have ht : ¬ Unallowed key t := hoa.1.resolve_right (lt_irrefl 0)
    have h1 := jointKeyWorld_query_newCells prims D key t ht s p hp
    have h2 := ih p.1 _ (hn.2 p.1) (by simpa using hoa.2 p.1) p.2 r hr
    refine (Finset.card_le_card fun c hc => ?_).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add h1 h2)) |>.trans ?_
    · simp only [Finset.mem_filter, Finset.mem_sdiff] at hc
      by_cases hc' : c ∈ streamCells p.2.hash
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hc', hc.1.2⟩, hc.2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hc.1.1, hc'⟩, hc.2⟩)
    · rcases hn.1 with h | h <;> split_ifs <;> omega

/-- From an empty table of private keys, the hash cache of the joint world has the law of the hash
cache of the world with independent AES keys. -/
private theorem jointKeyWorld_hash_eq_lazy (prims : Primitives) (D : C.Coalition) {α : Type}
    (game : OracleComp (WorldSpec C) α) (s : KeyJointState C) (hs : s.keys = ∅) :
    ((fun r => r.2.hash) <$> (simulateQ (jointKeyWorld prims D false) game).run s) =ᵈ
      ((fun r => r.2.1) <$> (simulateQ (lazyKeyWorld prims D) game).run (s.hash, ∅)) := by
  have h := evalDist_simulateQ_state_projection (jointKeyWorld prims D false) (lazyKeyWorld prims D)
    keyJointIdealProjection (jointKeyWorld_false_query_projection prims D) game s
  have hp : keyJointIdealProjection s = (s.hash, ∅) := by
    simp only [keyJointIdealProjection, hs, Prod.mk.injEq, true_and]
    rfl
  rw [hp] at h
  have hm := EvalDistEq.map_congr (fun r : α × HashCache C × KeyCache C => r.2.1) h
  simpa only [Functor.map_map, Function.comp_def, Prod.map, keyJointIdealProjection, id_eq] using hm

/-- The swap at one hidden name keeps the law of the hash cache of the world with independent AES
keys. -/
private theorem lazyKeyWorld_hash_renameName (prims : Primitives) (D : C.Coalition) (n₀ : KeyName C)
    (h₀ : Hidden D n₀) (a b : HashOutput) {α : Type} (game : OracleComp (WorldSpec C) α) (s : HashCache C) :
    ((fun r => r.2.1) <$> (simulateQ (lazyKeyWorld prims D) (simulateQ (worldNameRename n₀ a b) game)).run (s, ∅)) =ᵈ
      ((fun r => r.2.1) <$> (simulateQ (lazyKeyWorld prims D) game).run (s, ∅)) := by
  have hm := EvalDistEq.map_congr (fun r : α × HashCache C => r.2)
    (evalDist_lazyKeyWorld_renameName prims D n₀ h₀ a b game s)
  simpa only [Functor.map_map, Function.comp_def] using hm.symm

/-- The law of the hash cache of the run after the deal does not depend on the key of a hidden term. -/
theorem evalDist_prssRandRealAfter_hash_update_term (st : A.State) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (T : C.Term) (hT : Hidden D (.term T)) (u : HashOutput)
    (s : KeyJointState C) (hs : s.keys = ∅) :
    ((fun r => r.2.hash) <$> (simulateQ (jointKeyWorld prims D false)
      (prssRandRealAfter K label calls D A Z st (Function.update term T u) pair)).run s) =ᵈ
      ((fun r => r.2.hash) <$> (simulateQ (jointKeyWorld prims D false)
        (prssRandRealAfter K label calls D A Z st term pair)).run s) := by
  rw [← prssRandRealAfter_rename_term K label calls D A Z st term pair T hT u]
  exact (jointKeyWorld_hash_eq_lazy prims D _ s hs).trans ((lazyKeyWorld_hash_renameName prims D _ hT _ _ _
    s.hash).trans (jointKeyWorld_hash_eq_lazy prims D _ s hs).symm)

/-- The law of the hash cache of the run after the deal does not depend on the key of a hidden pair. -/
theorem evalDist_prssRandRealAfter_hash_update_pair (st : A.State) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (p : C.Pair) (hp : Hidden D (.pair p)) (u : HashOutput)
    (s : KeyJointState C) (hs : s.keys = ∅) :
    ((fun r => r.2.hash) <$> (simulateQ (jointKeyWorld prims D false)
      (prssRandRealAfter K label calls D A Z st term (Function.update pair p u))).run s) =ᵈ
      ((fun r => r.2.hash) <$> (simulateQ (jointKeyWorld prims D false)
        (prssRandRealAfter K label calls D A Z st term pair)).run s) := by
  rw [← prssRandRealAfter_rename_pair K label calls D A Z st term pair p hp u]
  exact (jointKeyWorld_hash_eq_lazy prims D _ s hs).trans ((lazyKeyWorld_hash_renameName prims D _ hp _ _ _
    s.hash).trans (jointKeyWorld_hash_eq_lazy prims D _ s hs).symm)

/-- A counted computation keeps the table of private AES keys of the joint world. -/
private theorem jointKeyWorld_counted_keys (prims : Primitives) (D : C.Coalition) {α : Type}
    (oa : OracleComp (SimulatorSpec C) α) (s : KeyJointState C) :
    ∀ r ∈ support ((simulateQ (jointKeyWorld prims D false) (counted oa)).run s), r.2.keys = s.keys := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro r hr
    simp [counted_pure] at hr
    rw [hr]
  | query_bind t k ih =>
    intro r hr
    rw [counted_bind, simulateQ_bind, StateT.run_bind] at hr
    obtain ⟨p, hp, hr⟩ := (mem_support_bind_iff _ _ _).1 hr
    refine (ih p.1 p.2 r hr).trans ?_
    change p ∈ support ((simulateQ (jointKeyWorld prims D false)
      (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inl t)))).run s) at hp
    rw [simulateQ_spec_query] at hp
    rcases t with q | x
    · simp [jointKeyWorld, jointKeyWorldCore, jointLocal_false, onJointHash] at hp
      obtain ⟨_, _, _, rfl⟩ := hp
      rfl
    · simp only [jointKeyWorld, jointKeyWorldCore, jointProgram, StateT.run_mk] at hp
      have hx : ∀ r ∈ support ((onJointHash (programAnswer x)).run s), r.2.keys = s.keys := by
        intro r hr
        simp only [onJointHash, StateT.run_mk, support_map, Set.mem_image] at hr
        obtain ⟨_, _, rfl⟩ := hr
        rfl
      rw [support_map] at hp
      obtain ⟨r', hr', rfl⟩ := hp
      split at hr'
      · simp only [Bool.false_and, Bool.false_eq_true, ite_false] at hr'
        exact hx r' hr'
      · exact hx r' hr'

/-- The candidates for a hidden dealt key in a hash cache, namely each stream key of the cache that
is not the key of a known name. -/
private def hitCandidates (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (h : HashCache C) : Finset HashOutput :=
  (streamCells h).filter fun k => ∀ n', ¬ Hidden D n' → ¬ DealtKey term pair n' k

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem hitCandidates_update_term (D : C.Coalition) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (T : C.Term) (hT : Hidden D (.term T)) (u : HashOutput) (h : HashCache C) :
    hitCandidates D (Function.update term T u) pair h = hitCandidates D term pair h := by
  unfold hitCandidates
  refine Finset.filter_congr fun k _ => forall_congr' fun n' => imp_congr_right fun hn' => ?_
  rcases n' with _ | T' | p'
  · rfl
  · have hne : T' ≠ T := fun e => hn' (e ▸ hT)
    simp [DealtKey, dealtKey, Function.update_of_ne hne]
  · rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem hitCandidates_update_pair (D : C.Coalition) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (p : C.Pair) (hp : Hidden D (.pair p)) (u : HashOutput) (h : HashCache C) :
    hitCandidates D term (Function.update pair p u) h = hitCandidates D term pair h := by
  unfold hitCandidates
  refine Finset.filter_congr fun k _ => forall_congr' fun n' => imp_congr_right fun hn' => ?_
  rcases n' with _ | T' | p'
  · rfl
  · rfl
  · have hne : p' ≠ p := fun e => hn' (e ▸ hp)
    simp [DealtKey, dealtKey, Function.update_of_ne hne]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- With apart keys, a hit of a hidden dealt key is a candidate. -/
private theorem mem_hitCandidates (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (h : HashCache C) (hk : KeysApart D (DealtKey term pair)) (n : KeyName C) (k : HashOutput)
    (hn : DealtKey term pair n k) (hh : Hidden D n) (hc : h (.streamKey k) ≠ none) :
    k ∈ hitCandidates D term pair h := by
  simp only [hitCandidates, streamCells, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hc, fun n' hn' hd => hk n k n' k hn hh hd (fun e => hn' (e ▸ hh)) rfl⟩

/-- After a start of at most `start` stream keys, the run after the deal leaves at most
`start + step + final` candidates. -/
private theorem card_hitCandidates_le (prims : Primitives) (st : A.State) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (start n : ℕ)
    (hn : IsQueryBoundP (prssRandRealAfter K label calls D A Z st term pair) WorldCounted n)
    (s : KeyJointState C) (hs : (streamCells s.hash).card ≤ start)
    (x : Bool × KeyJointState C)
    (hx : x ∈ support ((simulateQ (jointKeyWorld prims D false)
      (prssRandRealAfter K label calls D A Z st term pair)).run s)) :
    (hitCandidates D term pair x.2.hash).card ≤ start + n := by
  have h := jointKeyWorld_streamCells_le prims D (DealtKey term pair) _ n hn
    (prssRandRealAfter_allowed K label calls D A Z st term pair) s x hx
  refine (Finset.card_le_card fun k hk => ?_).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hs h))
  simp only [hitCandidates, Finset.mem_filter] at hk
  by_cases hs' : k ∈ streamCells s.hash
  · exact Finset.mem_union_left _ hs'
  · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hk.1, hs'⟩, hk.2⟩)

set_option linter.constructorNameAsVariable false in
/-- Assume that the dealt keys are apart. Then the hash cache of the run with independent AES keys
holds the stream key of a hidden dealt key with probability at most `q k / 2^256`. Only a counted
call can put it there, and the counted calls do not depend on the hidden key values. -/
theorem prob_prssRand_keyHit_le (q : ℕ) (hq : IsQueryBounded A Z prssRandRounds q) :
    Pr{let r ← (simulateQ (jointKeyWorld prims D false)
        (prssRandRealKeyed K label calls D A x z Z)).run keyJointInitial}[
      KeysApart D (DealtKey r.1.1 r.1.2.1) ∧ KeyHit D (DealtKey r.1.1 r.1.2.1) r.2.hash] ≤
      ((q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  obtain ⟨start, step, final, hsum, hs, -, ha, hz⟩ := hq
  simp only [prssRandRounds, one_mul] at hsum
  have hafter : ∀ st term pair, IsQueryBoundP (prssRandRealAfter K label calls D A Z st term pair)
      WorldCounted (step + final) := fun st term pair =>
    isQueryBoundP_bind (isQueryBoundP_adversary _ _ (ha _ _)) fun _ _ =>
      (isQueryBoundP_bind (isQueryBoundP_free _ 0) fun _ _ =>
        isQueryBoundP_adversary _ _ (hz _)).mono (by omega)
  rw [prssRandRealKeyed_eq_prefix]
  unfold prssRandPrefix
  generalize hpt : ($ᵗ (C.Term → HashOutput) : ProbComp _) = pt
  generalize hpp : ($ᵗ (C.Pair → HashOutput) : ProbComp _) = pp
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p1 hp1 => ?_
  have hkeys : p1.2.keys = ∅ := jointKeyWorld_counted_keys prims D _ keyJointInitial p1 hp1
  have hcells : (streamCells p1.2.hash).card ≤ start := by
    have h := jointKeyWorld_streamCells_le prims D NoKey _ start
      (isQueryBoundP_adversary _ _ (hs _ _)) (isQueryBoundP_counted_unallowed _ _) keyJointInitial p1 hp1
    simpa [streamCells, keyJointInitial, NoKey] using h
  have h := EvalDistEq.bind_congr (jointKeyWorld_free_prob D prims pt p1.2)
    (f := fun t => (simulateQ (jointKeyWorld prims D false) (free (liftComp pp (LocalSpec C)))).run t.2 >>=
      fun r => (simulateQ (jointKeyWorld prims D false) ((fun b => (t.1, r.1, b)) <$>
        prssRandRealAfter K label calls D A Z p1.1 t.1 r.1)).run r.2)
    fun t => EvalDistEq.bind_left (jointKeyWorld_free_prob D prims pp t.2) _
  rw [h.prEvent_eq]
  simp only [bind_map_left, simulateQ_map, StateT.run_map]
  subst hpt hpp
  let name : C.Term ⊕ C.Pair → KeyName C := Sum.elim .term .pair
  let Ev : C.Term ⊕ C.Pair → ((C.Term → HashOutput) × (C.Pair → HashOutput) × Bool) × KeyJointState C →
      Prop := fun e r => Hidden D (name e) ∧
    ∃ k, DealtKey r.1.1 r.1.2.1 (name e) k ∧ k ∈ hitCandidates D r.1.1 r.1.2.1 r.2.hash
  refine (prEvent_mono _ _ (fun r => ∃ e ∈ (Finset.univ : Finset (C.Term ⊕ C.Pair)), Ev e r)
    fun r hr => ?_).trans ((prEvent_exists_finset_le _ _ _).trans
      ((Finset.sum_le_sum (g := fun _ => (q : ℝ≥0∞) / 2 ^ 256) fun e _ => ?_).trans ?_))
  · obtain ⟨hk, n, k, hn, hh, hc⟩ := hr
    rcases n with _ | T | p
    · simp [DealtKey, dealtKey] at hn
    · exact ⟨.inl T, Finset.mem_univ _, hh, k, hn, mem_hitCandidates D _ _ _ hk _ k hn hh hc⟩
    · exact ⟨.inr p, Finset.mem_univ _, hh, k, hn, mem_hitCandidates D _ _ _ hk _ k hn hh hc⟩
  · rcases e with T | p
    · by_cases hT : Hidden D (.term T)
      swap
      · exact le_trans (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun r _ hr => hT hr.1))
          zero_le
      let search : (C.Term → HashOutput) → ProbComp (Finset HashOutput) := fun term =>
        $ᵗ (C.Pair → HashOutput) >>= fun pair => (fun x => hitCandidates D term pair x.2.hash) <$>
          (simulateQ (jointKeyWorld prims D false) (prssRandRealAfter K label calls D A Z p1.1 term pair)).run p1.2
      refine (prEvent_mono _ _ (fun r => decide (r.1.1 T ∈ hitCandidates D r.1.1 r.1.2.1 r.2.hash) = true)
        fun r hr => ?_).trans ((le_of_eq ?_).trans (prob_uniformTable_search_le T search ?_ q ?_))
      · obtain ⟨-, k, hk, hm⟩ := hr
        simp only [name, Sum.elim_inl, DealtKey, dealtKey, Option.some.injEq] at hk
        subst hk
        simpa using hm
      · have e : (($ᵗ (C.Term → HashOutput)) >>= fun table => search table >>= fun s =>
            (pure (decide (table T ∈ s)) : ProbComp Bool)) =
            (fun r : ((C.Term → HashOutput) × (C.Pair → HashOutput) × Bool) × KeyJointState C =>
              decide (r.1.1 T ∈ hitCandidates D r.1.1 r.1.2.1 r.2.hash)) <$>
            (($ᵗ (C.Term → HashOutput)) >>= fun a => ($ᵗ (C.Pair → HashOutput)) >>= fun a_1 =>
              (fun p => ((a, a_1, p.1), p.2)) <$> (simulateQ (jointKeyWorld prims D false)
                (prssRandRealAfter K label calls D A Z p1.1 a a_1)).run p1.2) := by
          simp [search, map_bind, Functor.map_map]
        rw [e, prEvent_map]
      · intro term u
        refine EvalDistEq.bind_right _ fun pair => ?_
        simp only [hitCandidates_update_term D term pair T hT u]
        have hm := EvalDistEq.map_congr (fun h => hitCandidates D term pair h)
          (evalDist_prssRandRealAfter_hash_update_term K label calls D A Z prims p1.1 term pair T hT u p1.2 hkeys)
        simpa only [Functor.map_map, Function.comp_def] using hm
      · intro term s hs'
        simp only [search, support_bind, support_map, Set.mem_iUnion, Set.mem_image] at hs'
        obtain ⟨pair, -, x, hx, rfl⟩ := hs'
        exact (card_hitCandidates_le K label calls D A Z prims p1.1 term pair start _ (hafter _ _ _) p1.2
          hcells x hx).trans (by omega)
    · by_cases hp : Hidden D (.pair p)
      swap
      · exact le_trans (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun r _ hr => hp hr.1))
          zero_le
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun term _ => ?_
      let search : (C.Pair → HashOutput) → ProbComp (Finset HashOutput) := fun pair =>
        (fun x => hitCandidates D term pair x.2.hash) <$>
          (simulateQ (jointKeyWorld prims D false) (prssRandRealAfter K label calls D A Z p1.1 term pair)).run p1.2
      refine (prEvent_mono _ _ (fun r => decide (r.1.2.1 p ∈ hitCandidates D r.1.1 r.1.2.1 r.2.hash) = true)
        fun r hr => ?_).trans ((le_of_eq ?_).trans (prob_uniformTable_search_le p search ?_ q ?_))
      · obtain ⟨-, k, hk, hm⟩ := hr
        simp only [name, Sum.elim_inr, DealtKey, dealtKey, Option.some.injEq] at hk
        subst hk
        simpa using hm
      · have e : (($ᵗ (C.Pair → HashOutput)) >>= fun table => search table >>= fun s =>
            (pure (decide (table p ∈ s)) : ProbComp Bool)) =
            (fun r : ((C.Term → HashOutput) × (C.Pair → HashOutput) × Bool) × KeyJointState C =>
              decide (r.1.2.1 p ∈ hitCandidates D r.1.1 r.1.2.1 r.2.hash)) <$>
            (($ᵗ (C.Pair → HashOutput)) >>= fun a_1 =>
              (fun x => ((term, a_1, x.1), x.2)) <$> (simulateQ (jointKeyWorld prims D false)
                (prssRandRealAfter K label calls D A Z p1.1 term a_1)).run p1.2) := by
          simp [search, map_bind, Functor.map_map]
        rw [e, prEvent_map]
      · intro pair u
        simp only [search, hitCandidates_update_pair D term pair p hp u]
        have hm := EvalDistEq.map_congr (fun h => hitCandidates D term pair h)
          (evalDist_prssRandRealAfter_hash_update_pair K label calls D A Z prims p1.1 term pair p hp u p1.2 hkeys)
        simpa only [Functor.map_map, Function.comp_def] using hm
      · intro pair s hs'
        simp only [search, support_map, Set.mem_image] at hs'
        obtain ⟨x, hx, rfl⟩ := hs'
        exact (card_hitCandidates_le K label calls D A Z prims p1.1 term pair start _ (hafter _ _ _) p1.2
          hcells x hx).trans (by omega)
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_div_assoc]
    gcongr
    have hc : Fintype.card (C.Term ⊕ C.Pair) ≤ prssKeyCount C := by
      rw [Fintype.card_sum, card_term C, prssKeyCount, termCount]
      exact Nat.add_le_add_left (card_pair_le C) _
    rw [mul_comm]
    exact_mod_cast Nat.mul_le_mul_left q hc

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The dealt keys of the keyed run are not apart with probability at most `k² / 2^256`. -/
private theorem prob_prssRandKeyed_not_apart_le :
    Pr{let r ← (simulateQ (jointKeyWorld prims D false)
        (prssRandRealKeyed K label calls D A x z Z)).run keyJointInitial}[
      ¬ KeysApart D (DealtKey r.1.1 r.1.2.1)] ≤ ((prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [prssRandRealKeyed_eq_prefix, simulateQ_bind, StateT.run_bind]
  refine (prEvent_bind_le_prEvent_add _ _ (fun p => ¬ KeysApart D (DealtKey p.1.2.1 p.1.2.2)) _
    (ε := 0) fun p hp => le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun r hr hc => hp ?_)).trans ?_
  · rw [simulateQ_map, StateT.run_map, support_map] at hr
    obtain ⟨r', -, rfl⟩ := hr
    exact hc
  rw [add_zero]
  unfold prssRandPrefix
  have hk := prob_dealt_keys_equal_le D
  generalize ($ᵗ (C.Term → HashOutput) : ProbComp _) = pt at hk ⊢
  generalize ($ᵗ (C.Pair → HashOutput) : ProbComp _) = pp at hk ⊢
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun st _ => ?_
  have h := EvalDistEq.bind_congr (jointKeyWorld_free_prob D prims pt st.2)
    (f := fun t => (simulateQ (jointKeyWorld prims D false)
      (free (liftComp pp (LocalSpec C)))).run t.2 >>= fun r =>
        pure ((st.1, t.1, r.1), r.2))
    fun t => EvalDistEq.bind_left (jointKeyWorld_free_prob D prims pp t.2) _
  rw [h.prEvent_eq]
  refine le_trans (le_of_eq ?_) hk
  have e : ((fun a => (a, st.2)) <$> pt >>= fun t => (fun a => (a, t.2)) <$> pp >>= fun r =>
      (pure ((st.1, t.1, r.1), r.2) : ProbComp _)) =
      (fun r => ((st.1, r.1, r.2), st.2)) <$> (pt >>= fun term => pp >>= fun pair => pure (term, pair)) := by
    simp [map_bind, bind_map_left]
  rw [e, prEvent_map]
  refine prEvent_congr _ _ _ fun r => ?_
  simp only [KeysApart, DealtKey]
  push Not
  constructor
  · rintro ⟨n, k, n', k', h1, h2, h3, h4, rfl⟩
    exact ⟨n, n', k, h2, h4, h1, h3⟩
  · rintro ⟨n, n', k, h2, h4, h1, h3⟩
    exact ⟨n, k, n', k, h1, h2, h3, h4, rfl⟩

/-- The stream-key event of the real run has probability at most `prssRandHashError`. -/
theorem prssRand_keyHop (q : ℕ) (hq : IsQueryBounded A Z prssRandRounds q) :
    probBad_streamKey prims D (prssRandReal K label calls D A x z Z) ≤ prssRandHashError C q := by
  have hb : Pr{let r ← (simulateQ (jointKeyWorld prims D false)
      (prssRandRealKeyed K label calls D A x z Z)).run keyJointInitial}[r.2.bad = true] ≤
      ((prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
    (prEvent_mono_of_support _ _ _ fun r hr hb => prssRandKeyed_bad K label calls D A x z Z prims r hr hb).trans
      ((prEvent_or_le _ _ _).trans (add_le_add (prob_prssRandKeyed_not_apart_le K label calls D A x z Z prims)
        (prob_prssRand_keyHit_le K label calls D A x z Z prims q hq)))
  rw [probBad_streamKey_eq_ideal, prssRandReal_eq_keyed, simulateQ_map, StateT.run_map, prEvent_map]
  have hsum : ((prssKeyCount C ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((q * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 =
      ((prssKeyCount C * (q + prssKeyCount C) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [ENNReal.div_add_div_same]
    congr 1
    push_cast
    ring
  rw [hsum] at hb
  refine (ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)) hb).trans
    (le_of_eq ?_)
  rw [prssRandHashError, ENNReal.toReal_div]
  simp [ENNReal.toReal_add]

end Bound

end ThresholdLeanXmssSecurity
