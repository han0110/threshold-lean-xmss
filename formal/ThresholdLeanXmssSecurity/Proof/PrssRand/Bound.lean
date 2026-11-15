import ThresholdLeanXmssSecurity.Proof.PrssRand.Runs

/-!
# The PRSS streams from dealt keys, the calls of the ideal run

`prssRand_queryBound` counts the calls of the ideal run. The simulator makes the calls of the
adversary and the stream calls of `knownStreams`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

private theorem isQueryBoundP_liftComp_mapM {α β : Type} (f : α → OracleComp (RoSpec C) β) (n : ℕ)
    (l : List α) (h : ∀ a ∈ l, IsQueryBoundP (liftComp (f a) (LocalSpec C)) Counted n) :
    IsQueryBoundP (liftComp (l.mapM f) (LocalSpec C)) Counted (l.length * n) := by
  rw [seedGen_liftComp_mapM]
  exact queryBound_mapM Counted _ n l h

/-- `count` bits of a PRG make at most `count` counted calls. -/
private theorem isQueryBoundP_prgBits (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    IsQueryBoundP (liftComp (prgBits name key ρ idx count) (LocalSpec C)) Counted count := by
  unfold prgBits
  rw [liftComp_bind]
  show IsQueryBoundP _ _ (count + 0)
  refine isQueryBoundP_bind ?_ fun _ _ => by erw [liftComp_pure]; exact isQueryBoundP_pure _ _ 0
  simpa using isQueryBoundP_liftComp_mapM (fun position =>
    (query (spec := RoSpec C) (.inr (name, key, ρ, idx, position)) : OracleComp (RoSpec C) Bit))
    1 (List.range count) fun position _ => by
      have e : liftComp (query (spec := RoSpec C) (.inr (name, key, ρ, idx, position)) :
          OracleComp (RoSpec C) Bit) (LocalSpec C) =
          (liftM ((LocalSpec C).query (.inr (.inr (name, key, ρ, idx, position)))) :
            OracleComp (LocalSpec C) _) >>= pure := by
        rw [bind_pure]
        rfl
      erw [e]
      exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The known streams make at most `bound` counted calls for each term and each cell of the pair
table, when one stream makes at most `bound` counted calls. -/
private theorem isQueryBoundP_knownStreams {R : Type} [Zero R] (D : C.Coalition)
    (receivers : Finset C.Party) (codec : Codec C E R) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (ρ idx count bound : ℕ)
    (hdraw : ∀ name key, IsQueryBoundP (liftComp (codec.draw name key ρ idx count) (LocalSpec C))
      Counted bound) :
    IsQueryBoundP (liftComp (knownStreams D receivers codec term pair ρ idx count) (LocalSpec C))
      Counted ((termCount C + C.n ^ 2) * bound) := by
  have hpure {α : Type} (a : α) : IsQueryBoundP (liftComp (pure a : OracleComp (RoSpec C) α)
      (LocalSpec C)) Counted bound := by
    rw [liftComp_pure]
    exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le _)
  have hterm := isQueryBoundP_liftComp_mapM (fun T => if KnownTo D.1 T ∧ ∃ i ∈ receivers, i ∉ D.1 ∧ i ∈ C.holders T then
    codec.draw (.term T) (term T) ρ idx count else pure fun _ => 0) bound C.terms fun T _ => by
      split_ifs
      · exact hdraw _ _
      · exact hpure _
  have hpair := isQueryBoundP_liftComp_mapM (fun j => C.parties.mapM fun i =>
    if h : j ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers then
      codec.draw (.pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1))))
        (pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1)))) ρ idx count
    else pure fun _ => 0) (C.parties.length * bound) C.parties fun j _ =>
      isQueryBoundP_liftComp_mapM _ bound C.parties fun i _ => by
        split_ifs
        · exact hdraw _ _
        · exact hpure _
  unfold knownStreams
  rw [liftComp_bind]
  refine (isQueryBoundP_bind (m := C.parties.length * (C.parties.length * bound) + 0) hterm
    fun _ _ => ?_).mono ?_
  · rw [liftComp_bind]
    exact isQueryBoundP_bind hpair fun _ _ => by rw [liftComp_pure]; exact isQueryBoundP_pure _ _ 0
  · simp only [check_terms_length, termCount, Committee.parties, List.length_finRange, Nat.add_zero]
    apply le_of_eq
    ring

/-- The known streams of a call of `count` bits make at most `count` calls for each term and for
each cell of the pair table. -/
theorem isQueryBoundP_knownStreams_bits (D : C.Coalition) (receivers : Finset C.Party)
    (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (ρ idx count : ℕ) :
    IsQueryBoundP (liftComp (knownStreams D receivers (bitCodec (E := E)) term pair ρ idx count) (LocalSpec C))
      Counted ((termCount C + C.n ^ 2) * count) :=
  isQueryBoundP_knownStreams D receivers bitCodec term pair ρ idx count count fun name key =>
    isQueryBoundP_prgBits name key ρ idx count

/-- The known streams of a call of `count` elements make at most `elementBits * count` calls for
each term and for each cell of the pair table. -/
theorem isQueryBoundP_knownStreams_elements (K : Constants C E) (D : C.Coalition)
    (receivers : Finset C.Party) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (ρ idx count : ℕ) :
    IsQueryBoundP (liftComp (knownStreams D receivers (elementCodec K) term pair ρ idx count) (LocalSpec C))
      Counted ((termCount C + C.n ^ 2) * (elementBits * count)) := by
  refine isQueryBoundP_knownStreams D receivers (elementCodec K) term pair ρ idx count _ fun name key => ?_
  show IsQueryBoundP (liftComp (prgBits name key ρ idx (elementBits * count) >>= _) _) _
    (elementBits * count + 0)
  rw [liftComp_bind]
  exact isQueryBoundP_bind (isQueryBoundP_prgBits name key ρ idx _) fun _ _ => by
    rw [liftComp_pure]; exact isQueryBoundP_pure _ _ 0

variable [SampleableType E] (K : Constants C E) (label : ℕ) (calls : List RandCall) (D : C.Coalition)
  (A : Adversary C E Unit (C.Party → Option (PrssKeys C)) (Finset C.Party)) (x : C.Party → Unit) (z : Aux)
  (Z : Distinguisher C A.State (List (RandOutput C E))) (prims : Primitives)

/-- The calls of `F_rand` in the ideal run make at most `prssRandOverhead` counted calls. -/
private theorem costLe_idealCalls (receivers : Finset C.Party) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) : ∀ (ρ : ℕ) (calls : List RandCall),
    CostLe prims (idealCalls K D receivers term pair ρ calls) (prssRandOverhead C calls)
  | _, [] => CostLe.pure prims _
  | ρ, call :: calls => by
    have hcall : CostLe prims (idealCall K D receivers term pair ρ call)
        ((termCount C + C.n ^ 2) * call.streamBits) := by
      cases call with
      | elements idx count =>
        refine (CostLe.bind prims (CostLe.of_counted prims _ _
          (isQueryBoundP_knownStreams_elements K D receivers term pair ρ idx count)) fun _ =>
          CostLe.bind prims (CostLe.free_sample prims _) fun _ =>
          CostLe.bind prims (CostLe.free_sample prims _) fun _ => CostLe.pure prims _).mono prims ?_
        simp [RandCall.streamBits]
      | bits idx count =>
        refine (CostLe.bind prims (CostLe.of_counted prims _ _
          (isQueryBoundP_knownStreams_bits D receivers term pair ρ idx count)) fun _ =>
          CostLe.bind prims (CostLe.free_sample prims _) fun _ =>
          CostLe.bind prims (CostLe.free_sample prims _) fun _ => CostLe.pure prims _).mono prims ?_
        simp [RandCall.streamBits]
    refine (CostLe.bind prims hcall fun _ => CostLe.bind prims
      (costLe_idealCalls receivers term pair (ρ + 1) calls) fun _ => CostLe.pure prims _).mono prims ?_
    simp only [prssRandOverhead, List.map_cons, List.sum_cons]
    ring_nf
    rfl

/-- The ideal run makes the calls of the adversary and of the distinguisher, and the stream calls
of the simulator. -/
theorem prssRand_queryBound (q : ℕ) (hq : IsQueryBounded A Z prssRandRounds q) :
    HasHashQueryBound (runWorld prims (prssRandIdeal K label calls D A x z Z))
      (q + prssRandOverhead C calls) := by
  obtain ⟨start, step, final, hsum, hs, -, ha, hz⟩ := hq
  simp only [prssRandRounds] at hsum
  apply hasHashQueryBound_of_costLe
  unfold prssRandIdeal distinguish
  rw [idealExecution_FrandCalls]
  simp only [worldRoles, bind_assoc, pure_bind]
  exact CostLe.mono prims (CostLe.bind prims (CostLe.of_counted prims _ _ (hs _ _)) fun st =>
    CostLe.bind prims (CostLe.counted_sample prims _) fun term =>
    CostLe.bind prims (CostLe.counted_sample prims _) fun pair =>
    CostLe.bind prims (CostLe.of_counted prims _ _ (ha _ _)) fun a =>
    CostLe.bind prims (costLe_idealCalls K D prims a.2 term pair label calls) fun outputs =>
    CostLe.of_counted prims _ _ (hz _)) (by omega)

end ThresholdLeanXmssSecurity
