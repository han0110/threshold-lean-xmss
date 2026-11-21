import ThresholdLeanXmssSecurity.Proof.SeedHit
import ThresholdLeanXmssSecurity.Proof.SigningOwnForger

/-!
# The gate of a top key with the number of the edges

- `LayeredGraph.size` is the number of the edges of the observed graph. `sizeDiscounted` divides
  the graph potential by `growth` to that number, so it reads no call counter.
- `step_sizeDiscounted` shows that a graph query does not raise `sizeDiscounted`. A fresh query adds
  one edge, and a cached query changes nothing.
- `sizeTerminal_probability_of_expected` and `terminal_probability_size` bound a terminal graph with
  at most `q` edges, for a public program with any number of other calls.
- `afterSelected_topChainBound` bounds the chain calls of top key `b` in the stopped continuation by
  the own budget and `topChainSlack`.
- `run_size_le` shows that a run of the counted posterior adds at most one edge for each chain call.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningOwnGate

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof
open SigningHitProof SigningHitLaneProof SigningCostProof

variable {C : Committee} (prims : Primitives)

namespace LayeredGraph

open SigningHitProof.LayeredGraph

variable {State : Type} [DecidableEq State] [Fintype State] [Nonempty State]
  {Index : Type} [Fintype Index] [DecidableEq Index]

/-- The number of the edges of the observed graph. -/
def size (rows : Index → List (State → Option State)) : ℕ :=
  ∑ i, ∑ layer : Fin 3, (Finset.univ.filter fun input : State => (edge (rows i) layer.val input).isSome).card

/-- `Terminal` with the number of the edges in place of the count of the calls. -/
def SizeTerminal (target : Index → State) (q : ℕ) (rows : Index → List (State → Option State)) : Prop :=
  size rows ≤ q ∧
  (∀ i, Set.InjOn (fun v : Fin 3 × State => v.1.val) (component (rows i) 3 3 (target i))) ∧
  68 ≤ ∑ i, (component (rows i) 3 3 (target i)).card

/-- The potential over `growth` to the number of the edges. It reads no counter. -/
def sizeDiscounted (target : Index → State) (rows : Index → List (State → Option State)) : ℝ≥0∞ :=
  potential rows target / growth State ^ size rows

omit [DecidableEq State] [Nonempty State] [DecidableEq Index] in
theorem size_eq_sum (rows : Index → List (State → Option State)) :
    size rows = ∑ i, ∑ layer : Fin 3, ∑ input : State,
      if (edge (rows i) layer.val input).isSome then 1 else 0 := by
  simp only [size, Finset.card_filter]

omit [Fintype State] [Nonempty State] [Fintype Index] in
theorem edge_update_insertEdge (rows : Index → List (State → Option State)) (l : Index) (k : Fin 3)
    (v output : State) (hlen : (rows l).length = 3) (i : Index) (layer : ℕ) (input : State) :
    edge (Function.update rows l (insertEdge (rows l) k.val v output) i) layer input =
      if i = l ∧ layer = k.val ∧ input = v then some output else edge (rows i) layer input := by
  by_cases hi : i = l
  · subst i
    rw [Function.update_self, edge_insertEdge _ _ _ _ (by rw [hlen]; exact k.isLt)]
    simp
  · simp [hi]

omit [Nonempty State] in
/-- An inserted edge raises `size` by one when it is fresh and leaves it fixed otherwise. -/
theorem size_update_insertEdge (rows : Index → List (State → Option State)) (l : Index) (k : Fin 3)
    (v output : State) (hlen : (rows l).length = 3) :
    size (Function.update rows l (insertEdge (rows l) k.val v output)) =
      size rows + if (edge (rows l) k.val v).isSome then 0 else 1 := by
  classical
  have hpoint (i : Index) (layer : Fin 3) (input : State) :
      (if (edge (Function.update rows l (insertEdge (rows l) k.val v output) i) layer.val input).isSome
        then 1 else 0) =
      (if (edge (rows i) layer.val input).isSome then 1 else 0) +
        if i = l then (if layer = k then (if input = v then
          (if (edge (rows l) k.val v).isSome then 0 else 1) else 0) else 0) else 0 := by
    rw [edge_update_insertEdge rows l k v output hlen]
    by_cases hi : i = l
    · subst i
      by_cases hk : layer = k
      · subst layer
        by_cases hv : input = v
        · subst input
          cases (edge (rows l) k.val v).isSome <;> simp
        · simp [hv]
      · have hk' : layer.val ≠ k.val := fun h => hk (Fin.ext h)
        simp [hk, hk']
    · simp [hi]
  rw [size_eq_sum, size_eq_sum]
  simp only [hpoint, Finset.sum_add_distrib]
  congr 1
  simp [Finset.sum_ite_eq']

omit [DecidableEq Index] in
theorem sizeTerminal_discounted (target : Index → State) (q : ℕ)
    (rows : Index → List (State → Option State)) (h : SizeTerminal target q rows) :
    (5 : ℝ≥0∞) ^ 68 / growth State ^ q ≤ sizeDiscounted target rows := by
  apply ENNReal.div_le_div
  · have hN : (0 : ℝ) < Fintype.card State := by exact_mod_cast Fintype.card_pos
    simpa only [potential, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 5), ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal (productWeight_terminal _ hN rows target h.2.1 h.2.2)
  · exact pow_le_pow_right₀ growth_one_le h.1

variable [SampleableType State]

/-- A graph query does not raise `sizeDiscounted`. A fresh query adds one edge, and a cached query
changes nothing. -/
theorem step_sizeDiscounted (t : Index × Fin 3 × State) (s : GraphState Index State) (hs : Valid s)
    (target : Index → State) :
    (∑' r, Pr{let z ← LayeredGraph.step t s}[z = r] * sizeDiscounted target r.2.1) ≤ sizeDiscounted target s.1 := by
  unfold LayeredGraph.step
  split
  · rw [OracleComp.tsum_prEvent_pure_mul]
  · rename_i hfresh
    rw [OracleComp.tsum_prEvent_map_mul]
    have hl : t.2.1.val < (s.1 t.1).length := by rw [hs]; exact t.2.1.isLt
    have hf : (s.1 t.1)[t.2.1.val] t.2.2 = none := by
      simpa only [edge, List.getElem?_eq_getElem hl, Option.bind_some] using hfresh
    have hsize (output : State) :
        size (Function.update s.1 t.1 (insertEdge (s.1 t.1) t.2.1.val t.2.2 output)) = size s.1 + 1 := by
      rw [size_update_insertEdge s.1 t.1 t.2.1 t.2.2 output (hs t.1), hfresh]
      rfl
    calc
      _ = (∑' output : State, Pr{let z ← $ᵗ State}[z = output] *
            potential (Function.update s.1 t.1 (insertEdge (s.1 t.1) t.2.1.val t.2.2 output)) target) /
            growth State ^ (size s.1 + 1) := by
        simp only [sizeDiscounted, hsize, div_eq_mul_inv, ← mul_assoc]
        rw [ENNReal.tsum_mul_right]
      _ ≤ (growth State * potential s.1 target) / growth State ^ (size s.1 + 1) :=
        ENNReal.div_le_div_right (potential_mean_step s.1 target t.1 (hs t.1) _ hl _ hf) _
      _ = sizeDiscounted target s.1 := by
        rw [pow_succ, mul_comm (growth State),
          ENNReal.mul_div_mul_right _ _ growth_ne_zero growth_ne_top]
        rfl

omit [SampleableType State] in
/-- `terminal_probability_of_expected` with the number of the edges. -/
theorem sizeTerminal_probability_of_expected {α : Type}
    (run : ProbComp (α × (Index → List (State → Option State)))) (target : Index → State) (q : ℕ)
    (hmean : (∑' r, Pr{let z ← run}[z = r] * sizeDiscounted target r.2) ≤ 1) :
    Pr{let r ← run}[SizeTerminal target q r.2] ≤ growth State ^ q / (5 : ℝ≥0∞) ^ 68 := by
  classical
  have hmass : Pr{let r ← run}[SizeTerminal target q r.2] *
      ((5 : ℝ≥0∞) ^ 68 / growth State ^ q) ≤ 1 := by
    calc
      _ = ∑' r, (if SizeTerminal target q r.2 then Pr{let z ← run}[z = r] else 0) *
          ((5 : ℝ≥0∞) ^ 68 / growth State ^ q) := by
        rw [OracleComp.prEvent_eq_tsum_ite, ENNReal.tsum_mul_right]
      _ ≤ ∑' r, Pr{let z ← run}[z = r] * sizeDiscounted target r.2 := by
        apply ENNReal.tsum_le_tsum
        intro r
        split_ifs with hr
        · exact mul_le_mul_right (sizeTerminal_discounted target q r.2 hr) _
        · simp only [zero_mul, zero_le]
      _ ≤ 1 := hmean
  rw [← mul_div_assoc] at hmass
  have hmul := (ENNReal.div_le_iff (pow_ne_zero _ growth_ne_zero)
    (ENNReal.pow_ne_top growth_ne_top)).mp hmass
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
  simpa only [one_mul] using hmul

end LayeredGraph

namespace PublicContinuation

open SigningHitProof.PublicContinuation

/-- The potential of a public state with the number of the edges of its observed rows. -/
def sizePotential (target : ChainIndex → Digest) (s : State C) : ℝ≥0∞ :=
  LayeredGraph.sizeDiscounted target (rows s.1)

set_option backward.isDefEq.respectTransparency false in
theorem chain_query_sizeDiscounted (record : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (target : ChainIndex → Digest) (l : ChainIndex) (k : Fin 3) (v : Digest) :
    (∑' r, Pr{let z ← ((ProtectedSlot C →ₒ HashOutput).randomOracle (.inr (l, k, v))).run record}[z = r] *
      LayeredGraph.sizeDiscounted target (rows r.2)) ≤
      LayeredGraph.sizeDiscounted target (rows record) := by
  have hp := chain_query_projection record 0 l k v
  have hm := congrArg (fun f : Digest × LayeredGraph.GraphState ChainIndex Digest → ℝ≥0∞ => ∑' r, f r)
    (funext fun r => congrArg (· * LayeredGraph.sizeDiscounted target r.2.1) (hp.prEvent_eq (· = r)))
  simp only [OracleComp.tsum_prEvent_map_mul] at hm
  rw [hm]
  exact LayeredGraph.step_sizeDiscounted (l, k, v) (rows record, 0)
    (fun i => rows_length record i) target

set_option backward.isDefEq.respectTransparency false in
theorem slot_query_sizeDiscounted (record : QueryCache (ProtectedSlot C →ₒ HashOutput))
    (target : ChainIndex → Digest) (slot : TprfSecurityProof.Slot C) :
    (∑' r, Pr{let z ← ((ProtectedSlot C →ₒ HashOutput).randomOracle (.inl slot)).run record}[z = r] *
      LayeredGraph.sizeDiscounted target (rows r.2)) ≤
      LayeredGraph.sizeDiscounted target (rows record) := by
  classical
  cases hc : record (.inl slot) with
  | some value =>
    rw [show ((ProtectedSlot C →ₒ HashOutput).randomOracle (.inl slot)).run record =
      pure (value, record) from QueryImpl.withCaching_run_some _ hc,
      OracleComp.tsum_prEvent_pure_mul]
  | none =>
    rw [show ((ProtectedSlot C →ₒ HashOutput).randomOracle (.inl slot)).run record =
      (fun value => (value, record.cacheQuery (.inl slot) value)) <$> ($ᵗ HashOutput) from
        QueryImpl.withCaching_run_none _ hc, OracleComp.tsum_prEvent_map_mul]
    simp only [rows_update_slot]
    rw [OracleComp.tsum_prEvent_mul_of_const_on_support _ (fun _ _ => rfl)]

set_option backward.isDefEq.respectTransparency false in
theorem query_sizeDiscounted (target : ChainIndex → Digest) (t : (Spec C).Domain) (s : State C) :
    (∑' r, Pr{let z ← (implementation t).run s}[z = r] * sizePotential target r.2) ≤
      sizePotential target s := by
  classical
  rcases t with (slot | ⟨l, k, v⟩) | n | input
  · simpa only [implementation, StateT.run, OracleComp.tsum_prEvent_map_mul, sizePotential] using
      slot_query_sizeDiscounted s.1 target slot
  · simpa only [implementation, StateT.run, OracleComp.tsum_prEvent_map_mul, sizePotential] using
      chain_query_sizeDiscounted s.1 target l k v
  · simp only [implementation, StateT.run, OracleComp.tsum_prEvent_map_mul]
    exact le_of_eq (OracleComp.tsum_prEvent_mul_of_const_on_support _ (fun _ _ => rfl))
  · simp only [implementation, StateT.run, OracleComp.tsum_prEvent_map_mul, sizePotential]
    exact le_of_eq (OracleComp.tsum_prEvent_mul_of_const_on_support _ (fun _ _ => rfl))

theorem expected_sizePotential {α : Type} (oa : OracleComp (Spec C) α)
    (target : ChainIndex → Digest) (s : State C) :
    XmssSecurity.expectedFinal implementation (sizePotential target) oa s ≤ sizePotential target s := by
  have hz (oa : OracleComp (Spec C) α) (s : State C) :
      XmssSecurity.expectedSimulatedCost implementation (fun _ _ => 0) oa s = 0 := by
    induction oa using OracleComp.inductionOn generalizing s with
    | pure value => rfl
    | query_bind t k ih =>
      simp only [XmssSecurity.expectedSimulatedCost_query_bind, ih, mul_zero, tsum_zero, add_zero]
  have h := XmssSecurity.expectedFinal_le implementation (Inv := fun _ => True)
    (fun _ _ _ _ _ => trivial) (sizePotential target) (fun _ _ => 0)
    (fun t s _ => by simpa only [add_zero] using query_sizeDiscounted target t s) oa s trivial
  simpa only [hz, add_zero] using h

/-- `terminal_probability` with the number of the edges. The count of the state is not read, so the
bound holds for a program with any number of other calls. -/
theorem terminal_probability_size {α : Type} (oa : OracleComp (Spec C) α)
    (target : ChainIndex → Digest) (s : State C)
    (hempty : rows s.1 = LayeredGraph.emptyRows) (q : ℕ) (hq : q < 2 ^ 127) :
    Pr{let r ←
      (simulateQ implementation oa).run s}[LayeredGraph.SizeTerminal target q (rows r.2.1)] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  let run := (fun r => (r.1, rows r.2.1)) <$> (simulateQ implementation oa).run s
  have hmean : (∑' r, Pr{let z ← run}[z = r] * LayeredGraph.sizeDiscounted target r.2) ≤ 1 := by
    rw [OracleComp.tsum_prEvent_map_mul]
    apply le_trans (expected_sizePotential oa target s)
    simp only [sizePotential, LayeredGraph.sizeDiscounted, hempty, SigningHitProof.LayeredGraph.potential,
      SigningHitProof.LayeredGraph.productWeight_empty, ENNReal.ofReal_one]
    calc
      _ ≤ (1 : ℝ≥0∞) / 1 :=
        ENNReal.div_le_div le_rfl (one_le_pow₀ SigningHitProof.LayeredGraph.growth_one_le)
      _ = 1 := by simp
  have h := LayeredGraph.sizeTerminal_probability_of_expected run target q hmean
  rw [prEvent_map] at h
  exact h.trans (SigningHitProof.LayeredGraph.growth_query_cap q hq
    (show Fintype.card Digest = 2 ^ 128 by simp [digestBits]))

end PublicContinuation

/-- A local call of `H` at a chain position of top key `b`. -/
def TopChainCall (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex) :
    (LocalSpec C).Domain → Prop
  | .inr (.inl input) => ∃ l step value, input = protectedInput x b (.inr (l, step, value))
  | _ => False

/-- The chain calls at one top key that the stopped continuation can make beyond the own calls, the
verification with `174` calls and one more build with `348` calls. -/
def topChainSlack : ℕ := 522

section TopChain

open Classical

variable (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)

/-- A raw hash input at a chain position of top key `b`. -/
def HashTop (input : HashInput) : Prop :=
  ∃ l step value, input = XmssSecurity.Concrete.CacheView.topChainInput x.1 b l step value

theorem topChainInput_eq (l : ChainIndex) (k : ChainStep) (v : Digest) :
    XmssSecurity.Concrete.CacheView.topChainInput x.1 b l k v =
      tweakableHashInput x.1 (.chain topLayer (topKey b) k) (Verification.chainPayload l v) := by
  erw [XmssSecurity.Bridge.topChain_input]
  rfl

theorem tweakableHashInput_topChain {domain : LeanXmss.HashDomain} {payload : HashInput}
    {l : ChainIndex} {k : ChainStep} {v : Digest}
    (h : tweakableHashInput x.1 domain payload =
      XmssSecurity.Concrete.CacheView.topChainInput x.1 b l k v) :
    domain = .chain topLayer (topKey b) k := by
  erw [topChainInput_eq] at h
  have hf := (fieldInput_injective (by
    simpa only [tweakableHashInput, tweakBytes, List.append_assoc] using h)).1
  cases domain with
  | chain lay key step => exact hashDomainFields_injective trivial trivial hf
  | _ =>
    have ht := congrArg (fun f => f.tag.toNat) hf
    norm_num [hashDomainFields, tweakFields] at ht

theorem tweakableHash_bound (domain : LeanXmss.HashDomain) (payload : HashInput) (n : ℕ)
    (hn : (∃ k, domain = .chain topLayer (topKey b) k) → 0 < n) :
    (Verification.tweakableHashWithHash x.1 domain payload : OracleComp HashSpec Digest).IsQueryBoundP
      (HashTop x b) n := by
  unfold Verification.tweakableHashWithHash Verification.thWithHash Verification.oracleHashWithHash
  simp only [bind_pure_comp, isQueryBoundP_map_iff, HasQuery.instOfMonadLift_query,
    isQueryBoundP_query_iff]
  rintro ⟨l, k, v, h⟩
  exact hn ⟨k, tweakableHashInput_topChain x b h⟩

theorem oracleHash_zero (input : HashInput) (h : ¬HashTop x b input) :
    (Verification.oracleHashWithHash input : OracleComp HashSpec HashOutput).IsQueryBoundP (HashTop x b) 0 := by
  unfold Verification.oracleHashWithHash
  simp only [HasQuery.instOfMonadLift_query, isQueryBoundP_query_iff]
  exact fun h' => (h h').elim

theorem sequenceFin_bound {ι : Type} {spec : OracleSpec ι} {α : Type} (p : ι → Prop)
    [DecidablePred p] (m : ℕ) :
    ∀ {n : ℕ} (f : Fin n → OracleComp spec α), (∀ a, (f a).IsQueryBoundP p m) →
      (OverPermutation.sequenceFin f).IsQueryBoundP p (n * m) := by
  intro n
  induction n with
  | zero => intro f _; simp [OverPermutation.sequenceFin]
  | succ n ih =>
    intro f hf
    rw [OverPermutation.sequenceFin, show (n + 1) * m = m + (n * m + 0) by ring]
    exact isQueryBoundP_bind (hf 0) fun _ _ =>
      isQueryBoundP_bind (ih (fun a => f a.succ) fun a => hf a.succ) fun _ _ => by simp

theorem mapM_bound {ι : Type} {spec : OracleSpec ι} {α β : Type} (p : ι → Prop) [DecidablePred p]
    (cost : α → ℕ) (f : α → OracleComp spec β) :
    ∀ items : List α, (∀ a ∈ items, (f a).IsQueryBoundP p (cost a)) →
      (items.mapM f).IsQueryBoundP p (items.map cost).sum := by
  intro items
  induction items with
  | nil => intro _; simp
  | cons a rest ih =>
    intro h
    rw [List.mapM_cons, List.map_cons, List.sum_cons]
    exact (isQueryBoundP_bind (n := cost a) (m := (rest.map cost).sum + 0) (h a (by simp)) fun _ _ =>
      isQueryBoundP_bind (m := 0) (ih fun a ha => h a (by simp [ha])) fun _ _ => by simp).mono
        (by simp)

theorem chainWalk_bound (lay : Layer) (key : KeyIndex) (l : ChainIndex) (start : ℕ) :
    ∀ steps v, (Verification.chainWalkWithHash x.1 lay key l start steps v : OracleComp HashSpec Digest).IsQueryBoundP
      (HashTop x b) (if lay = topLayer ∧ key = topKey b then steps else 0) := by
  intro steps
  induction steps with
  | zero => intro v; simp [Verification.chainWalkWithHash, OverPermutation.walkChain]
  | succ steps ih =>
    intro v
    rw [Verification.chainWalkWithHash, show (if lay = topLayer ∧ key = topKey b then steps + 1 else 0) =
      (if lay = topLayer ∧ key = topKey b then steps else 0) +
        (if lay = topLayer ∧ key = topKey b then 1 else 0) by split_ifs <;> rfl]
    apply isQueryBoundP_bind (ih v)
    intro previous _
    by_cases hstep : start + steps < chainLength - 1
    · rw [dite_eq_left hstep]
      apply tweakableHash_bound
      rintro ⟨k, hk⟩
      obtain ⟨rfl, rfl, -⟩ := LeanXmss.HashDomain.chain.inj hk
      simp
    · rw [dite_eq_right hstep]
      simp

theorem recoverChain_bound (lay : Layer) (key : KeyIndex) (l : ChainIndex) (digit : WinternitzDigit)
    (v : Digest) :
    (Verification.recoverChainWithHash x.1 lay key l digit v : OracleComp HashSpec Digest).IsQueryBoundP
      (HashTop x b) (if lay = topLayer ∧ key = topKey b then 3 else 0) :=
  (chainWalk_bound x b lay key l _ _ v).mono (by split_ifs <;> simp [chainLength, winternitzBits])

theorem leafHash_zero (lay : Layer) (key : KeyIndex) (endpoints : ChainIndex → Digest) :
    (Verification.leafHashWithHash x.1 lay key endpoints : OracleComp HashSpec Digest).IsQueryBoundP
      (HashTop x b) 0 :=
  tweakableHash_bound x b _ _ 0 fun ⟨_, h⟩ => by cases h

theorem messageDigest_zero (lay : Layer) (key : KeyIndex) (message : HashInput)
    (randomness : Randomizer) :
    (Verification.messageDigestWithHash x.1 lay key message randomness : OracleComp HashSpec Digest).IsQueryBoundP
      (HashTop x b) 0 :=
  tweakableHash_bound x b _ _ 0 fun ⟨_, h⟩ => by cases h

theorem treeFold_zero (lay : Layer) (key : KeyIndex) (path : Fin layerHeight → Digest) :
    ∀ levels v, (Verification.treeFoldWithHash x.1 lay key path levels v : OracleComp HashSpec Digest).IsQueryBoundP
      (HashTop x b) 0 := by
  intro levels
  induction levels with
  | zero => intro v; simp [Verification.treeFoldWithHash, OverPermutation.foldPath]
  | succ levels ih =>
    intro v
    rw [Verification.treeFoldWithHash]
    apply isQueryBoundP_bind (n := 0) (m := 0) (ih v)
    intro current _
    split_ifs <;> exact tweakableHash_bound x b _ _ 0 fun ⟨_, h⟩ => by cases h

theorem otsLeaf_bound (lay : Layer) (key : KeyIndex) (message : HashInput) (randomness : Randomizer)
    (values : ChainIndex → Digest) :
    (Verification.otsLeafWithHash x.1 lay key message randomness values : OracleComp HashSpec (Option Digest)).IsQueryBoundP
      (HashTop x b) (if lay = topLayer ∧ key = topKey b then 174 else 0) := by
  unfold Verification.otsLeafWithHash
  refine (isQueryBoundP_bind (n := 0) (m := (if lay = topLayer ∧ key = topKey b then 174 else 0)) (messageDigest_zero x b lay key message randomness)
    fun digest _ => ?_).mono (by simp)
  split
  · refine (isQueryBoundP_bind (m := 0) (sequenceFin_bound _ _ _ fun chainIdx =>
      recoverChain_bound x b lay key chainIdx _ _) fun _ _ => ?_).mono ?_
    · simpa using leafHash_zero x b lay key _
    · split_ifs <;> simp [chainCount]
  · simp

theorem layerRoot_bound (lay : Layer) (key : KeyIndex) (message : HashInput)
    (part : LayerSignature) :
    (Verification.layerRootWithHash x.1 lay key message part : OracleComp HashSpec (Option Digest)).IsQueryBoundP
      (HashTop x b) (if lay = topLayer ∧ key = topKey b then 174 else 0) := by
  unfold Verification.layerRootWithHash
  refine (isQueryBoundP_bind (m := 0) (otsLeaf_bound x b lay key message _ _) fun leaf _ => ?_).mono
    (by simp)
  split
  · rw [bind_pure_comp, isQueryBoundP_map_iff]
    have h := treeFold_zero x b lay key part.authenticationPath
    exact h _ _
  · simp

theorem verify_bound (root : Digest) (message : Message) (signature : Signature) :
    (Verification.verifyWithHash ⟨root, x.1⟩ message signature : OracleComp HashSpec Bool).IsQueryBoundP
      (HashTop x b) 174 := by
  unfold Verification.verifyWithHash
  refine (isQueryBoundP_bind (n := 0) (m := 174) ((layerRoot_bound x b bottomLayer _ _ _).mono
    (by simp [bottomLayer, topLayer])) fun bottomRoot _ => ?_).mono (by simp)
  split
  · refine (isQueryBoundP_bind (m := 0) (layerRoot_bound x b topLayer _ _ _) fun _ _ => ?_).mono
      (by split_ifs <;> simp)
    split <;> simp
  · simp

theorem merkleNode_zero (lay : Layer) (chainEnd : KeyIndex → ChainIndex → Digest) :
    ∀ level idx, (merkleNode x.1 lay chainEnd level idx).IsQueryBoundP (HashTop x b) 0 := by
  intro level
  induction level with
  | zero => intro idx; exact leafHash_zero x b _ _ _
  | succ level ih =>
    intro idx
    rw [merkleNode]
    exact isQueryBoundP_bind (n := 0) (m := 0) (ih _) fun _ _ =>
      isQueryBoundP_bind (n := 0) (m := 0) (ih _) fun _ _ =>
        tweakableHash_bound x b _ _ 0 fun ⟨_, h⟩ => by cases h

theorem merklePath_zero (lay : Layer) (chainEnd : KeyIndex → ChainIndex → Digest) (key : KeyIndex) :
    (merklePath x.1 lay chainEnd key).IsQueryBoundP (HashTop x b) 0 := by
  unfold merklePath
  simpa using sequenceFin_bound (HashTop x b) 0 _ fun level => merkleNode_zero x b lay chainEnd _ _

theorem grind_zero (lay : Layer) (key : KeyIndex) (message : HashInput) (base : Randomizer) :
    ∀ attempts trial, (grind x.1 lay key message base attempts trial).IsQueryBoundP (HashTop x b) 0 := by
  intro attempts
  induction attempts with
  | zero => intro trial; simp [grind]
  | succ attempts ih =>
    intro trial
    rw [grind]
    apply isQueryBoundP_bind (n := 0) (m := 0) (messageDigest_zero x b lay key message _)
    intro digest _
    split
    · simp
    · exact ih _

theorem not_hashTop_commitment (e : KeyIndex) (ρ : Digest) :
    ¬HashTop x b (commitmentInput x.1 e ρ) := by
  rintro ⟨l, k, v, h⟩
  erw [topChainInput_eq] at h
  exact SigningGuessProof.commitmentInput_ne_tweakableHashInput _ _ _ _ _ _ h

theorem not_hashTop_randomizer (lay : Layer) (e : KeyIndex) (ρ : Digest) (message : HashInput) :
    ¬HashTop x b (randomizerInput x.1 lay e ρ message) := by
  rintro ⟨l, k, v, h⟩
  erw [topChainInput_eq] at h
  exact SigningGuessLinkProof.randomizerInput_ne_tweakableHashInput _ _ _ _ _ _ _ _ h

/-- A call of `H` at a chain position of top key `b`, in the signing oracle. -/
def RoTop : (RoSpec C).Domain → Prop
  | .inl input => ∃ l step value, input = protectedInput x b (.inr (l, step, value))
  | .inr _ => False

theorem tweakable_bound {α : Type} (oa : OracleComp HashSpec α) (n : ℕ)
    (h : oa.IsQueryBoundP (HashTop x b) n) : (tweakable (C := C) oa).IsQueryBoundP (RoTop x b) n := by
  let : OracleSpec.UniformAnswerMeasure (RoSpec C) := OracleSpec.UniformAnswerMeasure.ofFiniteNonempty _
  apply h.simulateQ_of_step
  · intro input _
    exact (isQueryBoundP_query_iff (spec := RoSpec C) (RoTop x b) (.inl (.hash input)) 1).mpr
      fun _ => Nat.zero_lt_one
  · intro input hn
    refine (isQueryBoundP_query_iff (spec := RoSpec C) (RoTop x b) (.inl (.hash input)) 0).mpr ?_
    rintro ⟨l, k, v, he⟩
    exact (hn ⟨l, k, v, Query.hash.inj he⟩).elim

theorem hashQuery_zero (input : Query C) (h : ∀ l k v, input ≠ protectedInput x b (.inr (l, k, v))) :
    (hashQuery input).IsQueryBoundP (RoTop x b) 0 := by
  refine (isQueryBoundP_query_iff (spec := RoSpec C) (RoTop x b) (.inl input) 0).mpr ?_
  rintro ⟨l, k, v, he⟩
  exact (h l k v he).elim

theorem prf_zero (seed : HashOutput) (point : Point) : (prf (C := C) seed point).IsQueryBoundP (RoTop x b) 0 := by
  unfold prf
  rw [isQueryBoundP_map_iff]
  exact hashQuery_zero x b _ fun _ _ _ h => by cases h

theorem prfValue_zero (seeds : C.Term → HashOutput) (point : Point) :
    (prfValue seeds point).IsQueryBoundP (RoTop x b) 0 := by
  unfold prfValue
  exact isQueryBoundP_bind (n := 0) (m := 0)
    (by simpa using mapM_bound (RoTop x b) (fun _ => 0) _ C.terms fun T _ => prf_zero x b _ _)
    fun _ _ => by simp

theorem eval_zero (keys : Keys C) (i : C.Party) (J : C.Quorum) (point : Point) (message : Message) :
    (eval keys i J point message).IsQueryBoundP (RoTop x b) 0 := by
  unfold eval
  refine isQueryBoundP_bind (n := 0) (m := 0)
    (by simpa using mapM_bound (RoTop x b) (fun _ => 0) _ _ fun T _ => prf_zero x b _ _) fun _ _ => ?_
  have hmask (j : C.Party) : (truncateHash <$> hashQuery (.mask (keys.pairKey j) point message J) :
      OracleComp (RoSpec C) Digest).IsQueryBoundP (RoTop x b) 0 := by
    rw [isQueryBoundP_map_iff]
    exact hashQuery_zero x b _ fun _ _ _ h => by cases h
  exact isQueryBoundP_bind (n := 0) (m := 0)
    (by simpa using mapM_bound (RoTop x b) (fun _ => 0) _ _ fun j _ => hmask j) fun _ _ => by simp

theorem signCodeword_zero (commitment : Digest) (e : KeyIndex) (message : Message) (ρ : Digest) :
    (signCodeword x.1 commitment e message ρ : OracleComp (RoSpec C) _).IsQueryBoundP (RoTop x b) 0 := by
  unfold signCodeword
  apply tweakable_bound
  refine isQueryBoundP_bind (n := 0) (m := 0) (oracleHash_zero x b _ (not_hashTop_commitment x b _ _))
    fun _ _ => ?_
  dsimp only
  split_ifs
  · simp
  · exact isQueryBoundP_bind (n := 0) (m := 0) (oracleHash_zero x b _ (not_hashTop_randomizer x b _ _ _ _))
      fun _ _ => grind_zero x b _ _ _ _ _ _

/-- The chain calls at top key `b` that one job makes. -/
def jobCost (job : Job) : ℕ :=
  match job.kind with
  | .chainEnd e _ => if e = topKey b then 3 else 0
  | .chainValue e _ _ => if e = topKey b then 3 else 0
  | _ => 0

theorem referenceJob_bound (job : Job) :
    (referenceJob tweakable (prfValue x.2.1) x.1 job : OracleComp (RoSpec C) _).IsQueryBoundP
      (RoTop x b) (jobCost b job) := by
  unfold referenceJob
  refine (isQueryBoundP_bind (n := 0) (m := jobCost b job)
    (by simpa using mapM_bound (RoTop x b) (fun _ => 0) _ _ fun p _ => prfValue_zero x b _ p)
    fun values _ => ?_).mono (by simp)
  rcases job with ⟨kind, points⟩
  cases kind with
  | chainEnd e l =>
    rw [isQueryBoundP_map_iff]
    exact tweakable_bound x b _ _ ((chainWalk_bound x b _ _ _ _ _ _).mono (by simp [jobCost]))
  | chainRow e l =>
    refine isQueryBoundP_bind (n := 0) (m := 0) (tweakable_bound x b _ _ ?_) fun _ _ =>
      isQueryBoundP_bind (n := 0) (m := 0) (tweakable_bound x b _ _ ?_) fun _ _ =>
        isQueryBoundP_bind (n := 0) (m := 0) (tweakable_bound x b _ _ ?_) fun _ _ => by simp
    all_goals exact (chainWalk_bound x b _ _ _ _ _ _).mono (by simp [bottomLayer, topLayer])
  | chainValue e l digit =>
    rw [isQueryBoundP_map_iff]
    refine tweakable_bound x b _ _ ((chainWalk_bound x b _ _ _ _ _ _).mono ?_)
    have hd : digit.val ≤ 3 := by
      have h := digit.isLt
      simp only [chainLength, winternitzBits] at h
      omega
    simp only [jobCost, true_and]
    split_ifs <;> omega
  | commitment e =>
    rw [isQueryBoundP_map_iff]
    exact tweakable_bound x b _ _ (oracleHash_zero x b _ (not_hashTop_commitment x b _ _))
  | randomizer => simp

theorem topKey_eq_iff (b' : XmssSecurity.TopIndex) : topKey b' = topKey b ↔ b' = b :=
  ⟨fun h => Fin.ext (by simpa [topKey] using congrArg Fin.val h), fun h => h ▸ rfl⟩

theorem bottomJobs_cost (b' : XmssSecurity.TopIndex) : ∀ job ∈ bottomJobs b', jobCost b job = 0 := by
  intro job hj
  simp only [bottomJobs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and, List.mem_singleton] at hj
  rcases hj with (⟨k, l, rfl⟩ | ⟨k, rfl⟩) | rfl <;> rfl

theorem jobs_bound (items : List Job) (cost : ℕ) (h : ∀ job ∈ items, jobCost b job ≤ cost) :
    (items.mapM (referenceJob tweakable (prfValue x.2.1) x.1) : OracleComp (RoSpec C) _).IsQueryBoundP
      (RoTop x b) (items.length * cost) := by
  simpa using mapM_bound (RoTop x b) (fun _ => cost) _ items fun job hj =>
    (referenceJob_bound x b job).mono (h job hj)

-- The proof times out unless these recursive programs are irreducible.
set_option maxRecDepth 100000 in
attribute [local irreducible] merkleNode merklePath grind Verification.treeFoldWithHash Verification.chainWalkWithHash in
/-- A build of bottom tree `b'` makes `348` chain calls at top key `b` when `b' = b`, and none
otherwise. -/
theorem ceremony_bottom_bound (top : TopTree) (b' : XmssSecurity.TopIndex) :
    (referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom b') : OracleComp (RoSpec C) _).IsQueryBoundP
      (RoTop x b) (if b' = b then 348 else 0) := by
  simp only [referenceTree, ceremonyOutput]
  generalize List.flatMap (fun k => List.map (fun l => (bottomKey b' k, l)) (List.finRange chainCount))
    (List.finRange (2 ^ layerHeight)) = keys
  refine (isQueryBoundP_bind (n := 0) (m := if b' = b then 348 else 0) ?_ fun o ho => ?_).mono
    (by simp)
  rotate_left
  · clear ho
    cases o with
    | none =>
      dsimp only
      exact isQueryBoundP_pure _ _ _
    | some outputs =>
      dsimp only
      refine (isQueryBoundP_bind (n := 0) (m := if b' = b then 348 else 0) ?_ fun root _ => ?_).mono
        (by simp)
      · apply tweakable_bound
        apply merkleNode_zero
      refine (isQueryBoundP_bind (n := 0) (m := if b' = b then 348 else 0) ?_ fun base _ => ?_).mono
        (by simp)
      · apply tweakable_bound
        rw [isQueryBoundP_map_iff]
        exact oracleHash_zero x b _ (not_hashTop_randomizer x b _ _ _ _)
      refine (isQueryBoundP_bind (n := 0) (m := if b' = b then 348 else 0) ?_ fun g hg => ?_).mono
        (by simp)
      · apply tweakable_bound
        apply grind_zero
      clear hg
      rcases g with _ | ⟨randomness, encoding⟩
      · dsimp only
        exact isQueryBoundP_pure _ _ _
      dsimp only
      refine (isQueryBoundP_bind (n := if b' = b then 174 else 0) (m := if b' = b then 174 else 0)
        ?_ fun v hv => ?_).mono (by split_ifs <;> simp)
      · rw [isQueryBoundP_map_iff]
        refine (jobs_bound x b (signJobs b' encoding) (if b' = b then 3 else 0) ?_).mono ?_
        · intro job hj
          obtain ⟨l, _, rfl⟩ := List.mem_map.mp hj
          simp only [jobCost, topKey_eq_iff]
          exact le_rfl
        · split_ifs
          · simp only [signJobs, List.length_map]
            decide
          · simp
      clear hv
      rcases v with _ | values
      · dsimp only
        exact isQueryBoundP_pure _ _ _
      dsimp only
      refine (isQueryBoundP_bind (n := 0) (m := if b' = b then 174 else 0) ?_ fun path _ => ?_).mono
        (by simp)
      · apply tweakable_bound
        apply merklePath_zero
      refine (isQueryBoundP_bind (n := if b' = b then 174 else 0) (m := 0) ?_ fun _ _ => ?_).mono
        (by simp)
      · apply tweakable_bound
        refine (layerRoot_bound x b _ _ _ _).mono ?_
        simp [topKey_eq_iff]
      · split_ifs
        · exact isQueryBoundP_pure _ _ _
        · exact isQueryBoundP_pure _ _ _
  · rw [isQueryBoundP_map_iff]
    have h := jobs_bound x b (bottomJobs b') 0 fun job hj => (bottomJobs_cost b b' job hj).le
    rw [Nat.mul_zero] at h
    exact h

/-- A call of `H` at a chain position of top key `b`, on either copy of the world. -/
def WorldTop : (WorldSpec C).Domain → Prop
  | .inl (.inl t) => TopChainCall x b t
  | .inl (.inr _) => False
  | .inr t => TopChainCall x b t

theorem liftFree_bound {α : Type} (ro : OracleComp (RoSpec C) α) (n : ℕ)
    (h : ro.IsQueryBoundP (RoTop x b) n) :
    (SigningSecurityProof.liftFree ro).IsQueryBoundP (WorldTop x b) n := by
  let : OracleSpec.UniformAnswerMeasure (LocalSpec C) := OracleSpec.UniformAnswerMeasure.ofFiniteNonempty _
  have hl : (liftComp ro (LocalSpec C)).IsQueryBoundP (TopChainCall x b) n := by
    rw [liftComp_def]
    apply h.simulateQ_of_step
    · intro t _
      exact (isQueryBoundP_query_iff (spec := LocalSpec C) (TopChainCall x b) (.inr t) 1).mpr
        fun _ => Nat.zero_lt_one
    · intro t ht
      refine (isQueryBoundP_query_iff (spec := LocalSpec C) (TopChainCall x b) (.inr t) 0).mpr ?_
      rcases t with input | p
      · exact fun hc => (ht hc).elim
      · exact fun hc => hc.elim
  unfold SigningSecurityProof.liftFree free
  apply hl.simulateQ_of_step
  · intro t _
    exact (isQueryBoundP_query_iff (spec := WorldSpec C) (WorldTop x b) (.inr t) 1).mpr
      fun _ => Nat.zero_lt_one
  · intro t ht
    exact (isQueryBoundP_query_iff (spec := WorldSpec C) (WorldTop x b) (.inr t) 0).mpr
      fun hc => (ht hc).elim

theorem localize_bound {α : Type} (oa : OracleComp (WorldSpec C) α) (n : ℕ)
    (h : oa.IsQueryBoundP (WorldTop x b) n) :
    (simulateQ worldLocalize oa).IsQueryBoundP (TopChainCall x b) n := by
  let : OracleSpec.UniformAnswerMeasure (LocalSpec C) := OracleSpec.UniformAnswerMeasure.ofFiniteNonempty _
  apply h.simulateQ_of_step
  · rintro ((t | t) | t) _
    · exact (isQueryBoundP_query_iff (spec := LocalSpec C) (TopChainCall x b) t 1).mpr
        fun _ => Nat.zero_lt_one
    · simp [worldLocalize]
    · exact (isQueryBoundP_query_iff (spec := LocalSpec C) (TopChainCall x b) t 1).mpr
        fun _ => Nat.zero_lt_one
  · rintro ((t | t) | t) ht
    · exact (isQueryBoundP_query_iff (spec := LocalSpec C) (TopChainCall x b) t 0).mpr
        fun hc => (ht hc).elim
    · simp [worldLocalize]
    · exact (isQueryBoundP_query_iff (spec := LocalSpec C) (TopChainCall x b) t 0).mpr
        fun hc => (ht hc).elim

theorem adversary_bound (t : (LocalSpec C).Domain) :
    (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) :
      OracleComp (WorldSpec C) _).IsQueryBoundP (WorldTop x b) (if TopChainCall x b t then 1 else 0) := by
  have he : (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) : OracleComp (WorldSpec C) _) =
      liftM ((WorldSpec C).query (.inl (.inl t))) := by
    simp only [worldRoles, counted, liftComp_query]
    rcases t with t | t | t <;> exact (simulateQ_query _ _).trans (id_map _)
  rw [he]
  refine (isQueryBoundP_query_iff (spec := WorldSpec C) (WorldTop x b) (.inl (.inl t)) _).mpr ?_
  intro ht
  change TopChainCall x b t at ht
  simp [ht]

theorem value_bound (top : TopTree) (p : Point) :
    ((actualDealt x top).value p).IsQueryBoundP (WorldTop x b) 0 :=
  liftFree_bound x b _ _ (prfValue_zero x b _ p)

theorem part_bound (top : TopTree) (i : C.Party) (J : C.Quorum) (p : Point) (message : Message) :
    ((actualDealt x top).part i J p message).IsQueryBoundP (WorldTop x b) 0 :=
  liftFree_bound x b _ _ (eval_zero x b _ i J p message)

set_option maxRecDepth 100000 in
theorem bottom_bound (top : TopTree) (b' : XmssSecurity.TopIndex) :
    ((actualDealt x top).bottom b').IsQueryBoundP (WorldTop x b) (if b' = b then 348 else 0) := by
  simp only [dealtWith]
  rw [isQueryBoundP_map_iff, show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 top (.bottom b') =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom b')) from
    referenceTree_φ _ _ _ _]
  exact liftFree_bound x b _ _ (ceremony_bottom_bound x b top b')

set_option maxRecDepth 100000 in
theorem bottomOnce_bound (top : TopTree) (b' : XmssSecurity.TopIndex) (st : TsigState C) :
    ((bottomOnce (actualDealt x top) b').run st).IsQueryBoundP (WorldTop x b)
      (if b' = b then 348 else 0) := by
  simp only [bottomOnce, StateT.run_bind, StateT.run_get, pure_bind]
  cases ht : st.trees b' with
  | some tree => simp
  | none =>
    simp only [StateT.run_bind]
    refine (isQueryBoundP_bind (n := if b' = b then 348 else 0) (m := 0) ?_ fun _ _ => ?_).mono
      (by simp)
    · change ((actualDealt x top).bottom b' >>= fun a => pure (a, st)).IsQueryBoundP (WorldTop x b) _
      exact isQueryBoundP_bind (n := if b' = b then 348 else 0) (m := 0) (bottom_bound x b top b')
        fun _ _ => isQueryBoundP_pure _ _ _
    · simp

set_option synthInstance.maxHeartbeats 400000 in
theorem run_liftM_bound {α : Type} (oa : OracleComp (WorldSpec C) α) (s : TsigState C) (n : ℕ)
    (h : oa.IsQueryBoundP (WorldTop x b) n) :
    ((liftM oa : StateT (TsigState C) (OracleComp (WorldSpec C)) α).run s).IsQueryBoundP (WorldTop x b) n := by
  change (oa >>= fun a => pure (a, s)).IsQueryBoundP (WorldTop x b) _
  exact isQueryBoundP_bind (n := n) (m := 0) h fun _ _ => isQueryBoundP_pure _ _ _

theorem signRound2_bound (top : TopTree) (i : C.Party) (J : C.Quorum) (commitment : Digest)
    (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    (signRound2With (fun oa => SigningCoreProof.honestLift oa)
      (fun y => (actualDealt x top).part i J y message) x.1 J commitment e message parts).IsQueryBoundP
      (WorldTop x b) 0 := by
  unfold signRound2With
  refine isQueryBoundP_bind (n := 0) (m := 0)
    (liftFree_bound x b _ _ (signCodeword_zero x b _ _ _ _)) fun codeword _ => ?_
  rcases codeword with _ | ⟨_, encoding⟩
  · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun _ _ => isQueryBoundP_pure _ _ _
    simpa using sequenceFin_bound (WorldTop x b) 0 _ fun l => by
      split_ifs
      · rw [isQueryBoundP_map_iff]
        exact part_bound x b top i J _ message
      · exact isQueryBoundP_pure _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- A signing oracle that opens no tree at `b` makes no chain call at top key `b`. -/
theorem tsig_step_zero (top : TopTree) (q : (TsigSpec C).Domain) (st : TsigState C)
    (hclosed : ¬Opens b st (.inr q)) :
    ((tsigOracles (fun oa => SigningCoreProof.honestLift oa) (actualDealt x top) q).run st).IsQueryBoundP
      (WorldTop x b) 0 := by
  cases q with
  | corrupt i =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs <;> simp
  | tree b' =>
    have hne : b' ≠ b := hclosed
    simp only [tsigOracles, StateT.run_bind]
    refine (isQueryBoundP_bind (n := 0) (m := 0) ((bottomOnce_bound x b top b' st).mono (le_of_eq (ite_eq_right hne)))
      fun r _ => ?_)
    rcases r with ⟨_ | tree, st'⟩
    · exact isQueryBoundP_pure _ _ _
    · simp only [StateT.run_bind]
      exact isQueryBoundP_bind (n := 0) (m := 0) (run_liftM_bound x b _ _ _ (value_bound x b top _))
        fun _ _ => by simp
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp
    · simp only [StateT.run_bind]
      refine isQueryBoundP_bind (n := 0) (m := 0) (by simp) fun _ _ => ?_
      rw [StateT.run_map, isQueryBoundP_map_iff]
      exact run_liftM_bound x b _ _ _ (part_bound x b top i J _ message)
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs with hguard
    · simp
    · have hne : treeOf e ≠ b := fun he => hclosed ⟨he, hguard⟩
      simp only [StateT.run_bind]
      refine isQueryBoundP_bind (n := 0) (m := 0)
        ((bottomOnce_bound x b top (treeOf e) st).mono (le_of_eq (ite_eq_right hne))) fun r _ => ?_
      rcases r with ⟨_ | tree, st'⟩
      · exact isQueryBoundP_pure _ _ _
      · simp only [StateT.run_bind]
        refine isQueryBoundP_bind (n := 0) (m := 0)
          (run_liftM_bound x b _ _ _ (part_bound x b top i J _ message)) fun r _ => ?_
        refine isQueryBoundP_bind (n := 0) (m := 0)
          (run_liftM_bound x b _ _ _ (signRound2_bound x b top i J _ e message _)) fun v _ => ?_
        rcases v with ⟨_ | values, st''⟩
        · exact isQueryBoundP_pure _ _ _
        · simp

theorem topChainCall_counted (t : (LocalSpec C).Domain) (h : TopChainCall x b t) :
    SigningOwnCounted (C := C) (.inl t) := by
  rcases t with t | t | t
  · exact h.elim
  · trivial
  · exact h.elim

theorem flagged_step (top : TopTree) (t : (LocalSpec C + TsigSpec C).Domain) (p : TsigState C × Bool)
    (hclosed : ¬Opens b p.1 t) :
    ((SigningCoreProof.flaggedOracles x (actualDealt x top) t).run p).IsQueryBoundP (WorldTop x b)
      (if SigningOwnCounted t then 1 else 0) := by
  rcases t with t | q
  · simp only [SigningCoreProof.flaggedOracles, StateT.run_mk]
    rw [isQueryBoundP_map_iff]
    refine (adversary_bound x b t).mono ?_
    by_cases ht : TopChainCall x b t
    · simp [ht, topChainCall_counted x b t ht]
    · simp [ht]
  · simp only [SigningCoreProof.flaggedOracles, StateT.run_mk]
    rw [isQueryBoundP_map_iff]
    exact (tsig_step_zero x b top q p.1 hclosed).mono (Nat.zero_le _)

/-- The forger in the stopped run makes no more chain calls at top key `b` than own calls. -/
theorem unopened_bound (top : TopTree) {α : Type} (oa : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ (n : ℕ) (p : TsigState C × Bool), oa.IsQueryBoundP SigningOwnCounted n →
      (unopenedRun x top b oa p).IsQueryBoundP (WorldTop x b) n := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n p _
    exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    intro n p h
    rw [isQueryBoundP_query_bind_iff] at h
    change (if Opens b p.1 t then pure none else
      (SigningCoreProof.flaggedOracles x (actualDealt x top) t).run p >>= fun r =>
        unopenedRun x top b (k r.1) r.2).IsQueryBoundP _ n
    split_ifs with ho
    · exact isQueryBoundP_pure _ _ _
    · refine (isQueryBoundP_bind (flagged_step x b top t p ho) fun r _ => ih r.1 _ r.2 (h.2 r.1)).mono ?_
      by_cases hc : SigningOwnCounted t
      · have hn := h.1.resolve_left (not_not.mpr hc)
        simp only [hc, ite_true]
        omega
      · simp [hc]

theorem verify_world (top : TopTree) (r : Forgery × TsigState C × Bool) :
    (PublicVerification.verify x top r).IsQueryBoundP (WorldTop x b) 174 := by
  unfold PublicVerification.verify
  rw [isQueryBoundP_map_iff]
  exact liftFree_bound x b _ _ (tweakable_bound x b _ _ (verify_bound x b _ _ _))

set_option maxRecDepth 100000 in
theorem honest_bound (top : TopTree) (e : KeyIndex) (message : Message) :
    (honestSignature (fun oa => SigningSecurityProof.liftFree oa) (actualDealt x top) e message).IsQueryBoundP
      (WorldTop x b) 348 := by
  unfold honestSignature
  refine (isQueryBoundP_bind (n := 348) (m := 0) ((bottom_bound x b top (treeOf e)).mono
    (by split_ifs <;> simp)) fun tree _ => ?_).mono (by simp)
  rcases tree with _ | tree
  · exact isQueryBoundP_pure _ _ _
  refine isQueryBoundP_bind (n := 0) (m := 0) (value_bound x b top _) fun ρ _ => ?_
  refine isQueryBoundP_bind (n := 0) (m := 0)
    (liftFree_bound x b _ _ (signCodeword_zero x b _ _ _ _)) fun codeword _ => ?_
  rcases codeword with _ | ⟨randomness, encoding⟩
  · exact isQueryBoundP_pure _ _ _
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun values _ => ?_
  · simpa using sequenceFin_bound (WorldTop x b) 0 _ fun l => by
      split
      · exact value_bound x b top _
      · exact isQueryBoundP_pure _ _ _
      · exact (isQueryBoundP_map_iff _ _ _).mpr (value_bound x b top _)
  · exact isQueryBoundP_bind (n := 0) (m := 0)
      (liftFree_bound x b _ _ (tweakable_bound x b _ _ (merklePath_zero x b _ _ _))) fun _ _ =>
        isQueryBoundP_pure _ _ _

set_option maxRecDepth 100000 in
theorem freshness_bound (output : PublicVerification.Output C) :
    (PublicVerification.freshness x output).IsQueryBoundP (WorldTop x b) 348 := by
  rcases output with ⟨flags, _ | ⟨top, st, forgery⟩⟩
  · exact isQueryBoundP_pure _ _ _
  · simp only [PublicVerification.freshness]
    split_ifs
    · simp
    · exact (isQueryBoundP_bind (m := 0) (honest_bound x b top _ _) fun _ _ => by simp).mono
        (le_of_eq (Nat.add_zero _))

theorem tail_bound (A : TsigAdversary C) (q : ℕ) (hown : HasSigningOwnBound A q)
    (output : Option TreeOutput) :
    (PublicVerification.tail A x b output).IsQueryBoundP (WorldTop x b) (q + 174) := by
  rcases output with _ | top | bottom
  · exact isQueryBoundP_pure _ _ _
  · simp only [PublicVerification.tail]
    refine isQueryBoundP_bind (unopened_bound x b top _ q _ (hown _ _)) fun r _ => ?_
    rcases r with _ | r
    · exact (isQueryBoundP_pure _ _ _)
    · exact verify_world x b top r
  · exact isQueryBoundP_pure _ _ _

attribute [local irreducible] merkleNode in
theorem finish_bound (outputs : List (List Bit)) :
    (SigningSecurityProof.liftFree (SelectedKeygen.finish (tweakable (C := C)) x.1 outputs)).IsQueryBoundP
      (WorldTop x b) 0 := by
  apply liftFree_bound
  unfold SelectedKeygen.finish
  exact isQueryBoundP_bind (n := 0) (m := 0) (tweakable_bound x b _ _ (merkleNode_zero x b _ _ _ _))
    fun _ _ => isQueryBoundP_pure _ _ _

theorem after_jobs_bound (after : List XmssSecurity.TopIndex) (hb : b ∉ after) :
    (SigningSecurityProof.liftFree ((after.flatMap SelectedKeygen.jobs).mapM
      (referenceJob tweakable (prfValue x.2.1) x.1))).IsQueryBoundP (WorldTop x b) 0 := by
  apply liftFree_bound
  refine (jobs_bound x b _ 0 fun job hj => ?_).mono (Nat.le_of_eq (Nat.mul_zero _))
  obtain ⟨b', hb', hj⟩ := List.mem_flatMap.mp hj
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hj
  have hne : b' ≠ b := fun he => hb (he ▸ hb')
  simp [jobCost, topKey_eq_iff, hne]

end TopChain

attribute [local irreducible] merkleNode merklePath grind Verification.treeFoldWithHash Verification.chainWalkWithHash in
open Classical in
/-- The stopped continuation after the selected block makes at most `q + topChainSlack` calls of `H`
at a chain position of top key `b`, on every path. -/
theorem afterSelected_topChainBound (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C)
    (b : XmssSecurity.TopIndex) (after : List XmssSecurity.TopIndex) (hb : b ∉ after)
    (left : List (List Bit)) (target : ChainIndex → Digest) (hown : HasSigningOwnBound A q) :
    (PublicVerification.afterSelected A x b after left target).IsQueryBoundP (TopChainCall x b)
      (q + topChainSlack) := by
  unfold PublicVerification.afterSelected
  apply localize_bound
  unfold PublicVerification.afterOutputs PublicVerification.checkedTail
  refine (isQueryBoundP_bind (n := 0) (m := q + topChainSlack) (after_jobs_bound x b after hb)
    fun _ _ => ?_).mono (by simp)
  refine (isQueryBoundP_bind (n := 0) (m := q + topChainSlack) (finish_bound x b _)
    fun output _ => ?_).mono (by simp)
  exact (isQueryBoundP_bind (tail_bound x b A q hown output) fun r _ => freshness_bound x b r).mono
    (by simp [topChainSlack])

set_option backward.isDefEq.respectTransparency false in
/-- An eager routed call leaves the record fixed, or records the one protected slot of its input. -/
theorem eager_route_record (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (table : ProtectedSlot C → HashOutput)
    (e : Query C) (s : QueryCache (ProtectedSlot C →ₒ HashOutput) × HashCache C) (r)
    (hr : r ∈ support ((simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
      (ProtectedRouting.routeWithSampling (protectedInput x b) e)).run s)) :
    r.2.1 = s.1 ∨ ∃ d, protectedInput x b d = e ∧ r.2.1 = s.1.cacheQuery d (table d) := by
  classical
  have hinj := protectedInput_injective x b hno
  by_cases h : ∃ d, protectedInput x b d = e
  · obtain ⟨d, rfl⟩ := h
    rw [ProtectedRouting.routeWithSampling_in _ hinj] at hr
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      FinitePosterior.eager, StateT.run, mem_support_pure_iff] at hr
    subst r
    exact Or.inr ⟨d, rfl, rfl⟩
  · have hroute : ProtectedRouting.routeWithSampling (R := HashOutput) (protectedInput x b) e =
        liftM (((ProtectedSlot C →ₒ HashOutput) + (unifSpec + (Query C →ₒ HashOutput))).query
          (.inr (.inr e))) := by
      simp only [ProtectedRouting.routeWithSampling, ProtectedRouting.route, dite_eq_right h,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        ProtectedRouting.extend]
    rw [hroute] at hr
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      FinitePosterior.eager] at hr
    exact Or.inl (ProtectedRouting.samplingAux_preserves (.inr e) s r hr)

open Classical in
/-- A recorded protected slot adds at most one edge, and only a chain slot adds one. -/
theorem size_cacheQuery_le (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (record : QueryCache (ProtectedSlot C →ₒ HashOutput)) (d : ProtectedSlot C) (value : HashOutput) :
    LayeredGraph.size (PublicContinuation.rows (record.cacheQuery d value)) ≤
      LayeredGraph.size (PublicContinuation.rows record) +
        if TopChainCall x b (.inr (.inl (protectedInput x b d))) then 1 else 0 := by
  rcases d with slot | ⟨l, k, v⟩
  · rw [PublicContinuation.rows_update_slot]
    exact Nat.le_add_right _ _
  · have hcall : TopChainCall x b (.inr (.inl (protectedInput x b (.inr (l, k, v))))) :=
      ⟨l, k, v, rfl⟩
    rw [ite_eq_left hcall]
    erw [PublicContinuation.rows_update_chain]
    have h := LayeredGraph.size_update_insertEdge (PublicContinuation.rows record) l k v
      (truncateHash value) (PublicContinuation.rows_length record l)
    exact le_trans (le_of_eq h) (Nat.add_le_add_left (by split_ifs <;> simp) _)

open Classical in
set_option backward.isDefEq.respectTransparency false in
/-- One local call of the eager protected handler adds at most one edge, and only a chain call
adds one. -/
theorem protectedLocal_size_le (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (table : ProtectedSlot C → HashOutput)
    (t : (LocalSpec C).Domain) (s : QueryCache (ProtectedSlot C →ₒ HashOutput) × HashCache C) (r)
    (hr : r ∈ support ((simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
      (protectedLocal prims x b t)).run s)) :
    LayeredGraph.size (PublicContinuation.rows r.2.1) ≤
      LayeredGraph.size (PublicContinuation.rows s.1) + if TopChainCall x b t then 1 else 0 := by
  rcases t with n | u | p
  · simp only [protectedLocal, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, FinitePosterior.eager, ProtectedRouting.samplingAux, StateT.run, support_map,
      Set.mem_image] at hr
    obtain ⟨v, _, rfl⟩ := hr
    exact Nat.le_add_right _ _
  · rcases eager_route_record x b hno table u s r hr with he | ⟨d, rfl, he⟩
    · rw [he]
      exact Nat.le_add_right _ _
    · rw [he]
      exact size_cacheQuery_le x b s.1 d (table d)
  · simp only [protectedLocal, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    rcases eager_route_record x b hno table _ s v hv with he | ⟨d, hd, he⟩
    · rw [he]
      exact Nat.le_add_right _ _
    · rw [he]
      rcases d with slot | ⟨l, k, w⟩
      · rw [PublicContinuation.rows_update_slot]
        exact Nat.le_add_right _ _
      · cases hd

open Classical in
theorem protectedRun_size_le {α : Type} (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (table : ProtectedSlot C → HashOutput)
    (oa : OracleComp (LocalSpec C) α) :
    ∀ (n : ℕ) (s : QueryCache (ProtectedSlot C →ₒ HashOutput) × HashCache C),
      oa.IsQueryBoundP (TopChainCall x b) n →
      ∀ r ∈ support ((simulateQ (FinitePosterior.eager table ProtectedRouting.samplingAux)
        (simulateQ (protectedLocal prims x b) oa)).run s),
        LayeredGraph.size (PublicContinuation.rows r.2.1) ≤
          LayeredGraph.size (PublicContinuation.rows s.1) + n := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n s _ r hr
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact Nat.le_add_right _ _
  | query_bind t k ih =>
    intro n s hbound r hr
    rw [isQueryBoundP_query_bind_iff] at hbound
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨v, hv, hr⟩ := hr
    have hstep := protectedLocal_size_le prims x b hno table t s v hv
    have hrest := ih v.1 _ v.2 (hbound.2 v.1) r hr
    split_ifs at hstep hrest with hp
    · have hn : 0 < n := hbound.1.resolve_left (not_not.mpr hp)
      omega
    · omega

open Classical in
/-- A run of the counted posterior adds at most one edge for each chain call. -/
theorem run_size_le {α : Type} (x : SigningSecurityProof.Keys3 C) (b : XmssSecurity.TopIndex)
    (hno : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (table : ProtectedSlot C → HashOutput) (oa : OracleComp (LocalSpec C) α)
    (s : PublicContinuation.State C) (n : ℕ) (hbound : oa.IsQueryBoundP (TopChainCall x b) n) :
    ∀ r ∈ support (CountedPosterior.run prims x b table oa s),
      LayeredGraph.size (PublicContinuation.rows r.2.1) ≤
        LayeredGraph.size (PublicContinuation.rows s.1) + n := by
  intro r hr
  have hforget : (r.1, r.2.1, r.2.2.1) ∈ support ((simulateQ
      (FinitePosterior.eager table ProtectedRouting.samplingAux)
      (simulateQ (protectedLocal prims x b) oa)).run (s.1, s.2.1)) := by
    rw [CountedPosterior.eager_forget_run prims x b table oa s, support_map]
    exact ⟨r, hr, rfl⟩
  have h := protectedRun_size_le prims x b hno table oa n (s.1, s.2.1) hbound _ hforget
  dsimp only at h
  exact h

end ThresholdLeanXmssSecurity.SigningOwnGate

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGate.LayeredGraph.step_sizeDiscounted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGate.LayeredGraph.step_sizeDiscounted

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGate.LayeredGraph.sizeTerminal_probability_of_expected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGate.LayeredGraph.sizeTerminal_probability_of_expected

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGate.PublicContinuation.terminal_probability_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGate.PublicContinuation.terminal_probability_size

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGate.afterSelected_topChainBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGate.afterSelected_topChainBound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnGate.run_size_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOwnGate.run_size_le
