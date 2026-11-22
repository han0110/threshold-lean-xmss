import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.BatchRecords
import ThresholdLeanXmssSecurity.Proof.Pilot.Final

/-!
# The agreement of the opened outputs and of the input shares

`blockOutputs_agree_of_cache` states that two honest operators with the same copies in the cache open
the same outputs of a block. The section `PassedShares` gives the histories of the honest operators
on a recorded run (`Histories`, `histories_recRun`). `streamWorld_free_jobInputs` states that the
input shares of a job are the PRF cells of the seeds in the cache, and `jobInputs_eq_batchInputs`
gives the same for the jobs of a batch.
-/

section

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-! ## Two lengths of the outputs of a list of circuits -/

theorem main_length_flatMap_zipIdx {β : Type} (f : Circuit → List β) :
    ∀ (jobs : List Circuit) (n : ℕ),
      ((jobs.zipIdx n).flatMap fun p => (f p.1).map fun a => (p.2, a)).length = (jobs.map fun j => (f j).length).sum
  | [], _ => by simp
  | j :: js, n => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, main_length_flatMap_zipIdx f js (n + 1)]
    simp

theorem main_outputsOf_length (jobs : List Circuit) :
    (outputsOf jobs).length = (jobs.map (·.outputs.length)).sum :=
  main_length_flatMap_zipIdx (·.outputs) jobs 0

end ThresholdLeanXmssSecurity

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace OpenedAgreement

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- `assemble` reads the opened values only below the count of the outputs. -/
theorem assemble_congr (jobs : List Circuit) (opened opened' : ℕ → Bit)
    (hopened : ∀ g < (outputsOf jobs).length, opened g = opened' g) :
    ThresholdLeanXmssSecurity.assemble jobs opened = ThresholdLeanXmssSecurity.assemble jobs opened' := by
  unfold ThresholdLeanXmssSecurity.assemble
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨width, k⟩ := p
  refine GhostBatch.vector_congr width _ _ fun g hg => hopened _ ?_
  rw [main_outputsOf_length]
  set L := jobs.map (·.outputs.length)
  obtain ⟨hk, hw⟩ := List.mem_zipIdx_iff_getElem?.1 hp |> fun h => (List.getElem?_eq_some_iff.1 h)
  simp only at hk hw
  have h1 := List.sum_take_succ L k hk
  have h2 : (L.take (k + 1)).sum ≤ L.sum := List.Sublist.sum_le_sum (List.take_sublist _ _) (by simp)
  omega

/-- The equal batch outputs on two blocks of the form `GhostBatch.BlockShape` with `H` fixed to one `h`. Two honest
operators with the same circuits in their blocks, with the sharing `vr` after `Rerand` that agrees
with `w`, the honest messages of `OpenRep` as sent and no copy collision, have the same batch
outputs. -/
theorem blockOutputs_agree (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (h : Query C → HashOutput) (w : Shares C Bit) (vr : C.Party → Shares C Bit) (i i' : C.Party)
    (hiD : i ∉ D.1) (hiD' : i' ∉ D.1) (keys keys' : Keys C) (x y : BatchStart C × Mail C E × List (List Bit))
    (hx : GhostBatch.BlockShape K circuits settings h i keys x)
    (hy : GhostBatch.BlockShape K circuits settings h i' keys' y)
    (hcircuits : x.1.circuits = y.1.circuits) (hvx : x.1.v' = vr i) (hvy : y.1.v' = vr i')
    (hvr : ∀ j T g, j ∉ D.1 → j ∈ C.holders T → g < (outputsOf x.1.circuits).length → vr j T g = w T g)
    (hinbox : ∀ j, j ∉ D.1 → j ≠ i → x.2.1 j = repOutbox K j (vr j) (outputsOf x.1.circuits).length
      (copyHashes h (vr j) (outputsOf x.1.circuits).length) i)
    (hinbox' : ∀ j, j ∉ D.1 → j ≠ i' → y.2.1 j = repOutbox K j (vr j) (outputsOf x.1.circuits).length
      (copyHashes h (vr j) (outputsOf x.1.circuits).length) i')
    (hcopy : CopySound K D h vr (outputsOf x.1.circuits).length i x.2.1)
    (hcopy' : CopySound K D h vr (outputsOf x.1.circuits).length i' y.2.1) :
    x.2.2 = y.2.2 := by
  have hcheck := hx.2.1
  have hcheck' := hy.2.1
  rw [hvx] at hcheck
  rw [hvy, ← hcircuits] at hcheck'
  rw [hx.2.2, hy.2.2, hvx, hvy, ← hcircuits]
  refine assemble_congr _ _ _ fun g hg => ?_
  obtain ⟨h1, h2⟩ := openedSums_agree K D h w vr _ hvr i i' hiD hiD' x.2.1 y.2.1 hinbox hinbox' hcheck hcheck'
    hcopy hcopy' g hg
  rw [h1, h2]

/-- The honest message of `OpenRep` with the copy hashes that a hash cache holds is the message with
the copy hashes of each `h` that agrees with the cache. -/
theorem inbox_of_cached (cache : HashCache C) (h : Query C → HashOutput) (hagr : Agrees h cache)
    (j i : C.Party) (v : Shares C Bit) (count : ℕ) (message : Option (Msg E)) (digests : List HashOutput)
    (hmessage : message = repOutbox K j v count digests i)
    (hcells : List.Forall₂ (fun T d => cache (.copy (vector count (v T))) = some d) C.terms digests) :
    message = repOutbox K j v count (copyHashes h v count) i := by
  rw [hmessage, GhostBatch.forall₂_cached cache h hagr _ hcells]
  rfl

variable (prims : Primitives)

/-- The received copy of a term with a corrupt owner has a cell in the hash cache. The hash check of
`OpenRep` at `i` holds for each good `h'` that agrees with the cache, and an honest holder `j` that
is not the owner sent the copy hash of `h`. A value of `h'` off the cache at the received copy breaks
the check. -/
theorem receivedCopy_cached (cache : HashCache C) (h : Query C → HashOutput) (hgood : Good prims h)
    (hagr : Agrees h cache) (i : C.Party) (v : Shares C Bit) (count : ℕ) (inbox : Mail C E)
    (hchecks : ∀ h', Good prims h' → Agrees h' cache →
      repCheck K i inbox (copyHashes h' (repCopy K i v count inbox) count))
    (j : C.Party) (vj : Shares C Bit) (hinbox : inbox j = repOutbox K j vj count (copyHashes h vj count) i)
    (T : C.Term) (hiT : i ∉ C.holders T) (hjT : j ∈ C.holders T) (hne : j ≠ K.owner T) :
    (cache (.copy (vector count (repCopy K i v count inbox T)))).isSome := by
  by_contra hnone
  simp only [Option.not_isSome_iff_eq_none] at hnone
  let h' := Function.update h (.copy (vector count (repCopy K i v count inbox T)))
    (if h (.copy (vector count (vj T))) = 0 then 1 else 0)
  have hne' : h' (.copy (vector count (repCopy K i v count inbox T))) ≠ h (.copy (vector count (vj T))) := by
    simp only [h', Function.update_self]
    split_ifs with h0
    · rw [h0]; decide
    · exact Ne.symm h0
  have hg' : Good prims h' := fun x hx => by
    simp only [h']
    rw [Function.update_of_ne (by simp)]
    exact hgood x hx
  have ha' : Agrees h' cache := fun q u hq => by
    by_cases hq' : q = .copy (vector count (repCopy K i v count inbox T))
    · rw [hq', hnone] at hq
      cases hq
    · simp only [h']
      rw [Function.update_of_ne hq']
      exact hagr q u hq
  have hc := hchecks h' hg' ha' T hiT j hjT hne
  dsimp only at hc
  rw [hinbox, main_open_hash_sent K i j vj count _ (by simp [copyHashes]) T hiT hjT hne,
    lookup_zip_idxOf C.terms _ (by simp [copyHashes]) T (mem_terms T), copyHashes_idxOf,
    copyHashes_idxOf] at hc
  exact hne' (Option.some.inj hc).symm

/-- The premise `CopySound` from a hash cache with no collision in `CopyDomain`. The hash check of
`OpenRep` at `i` holds for each good `h'` that agrees with the cache, and the inbox holds the message
of each other honest operator with the copy hashes that the cache holds. -/
theorem copySound_of_cache (D : C.Coalition) (cache : HashCache C) (h : Query C → HashOutput)
    (hgood : Good prims h) (hagr : Agrees h cache) (w : Shares C Bit) (vr : C.Party → Shares C Bit)
    (count : ℕ) (hvr : ∀ j T g, j ∉ D.1 → j ∈ C.holders T → g < count → vr j T g = w T g)
    (i : C.Party) (hiD : i ∉ D.1) (inbox : Mail C E)
    (hchecks : ∀ h', Good prims h' → Agrees h' cache →
      repCheck K i inbox (copyHashes h' (repCopy K i (vr i) count inbox) count))
    (hdeliver : ∀ j, j ∉ D.1 → j ≠ i → ∃ digests, inbox j = repOutbox K j (vr j) count digests i ∧
      List.Forall₂ (fun T d => cache (.copy (vector count (vr j T))) = some d) C.terms digests)
    (hcollision : ¬ DomainCollision CopyDomain cache) :
    CopySound K D h vr count i inbox := by
  have hinbox : ∀ j, j ∉ D.1 → j ≠ i → inbox j = repOutbox K j (vr j) count (copyHashes h (vr j) count) i := by
    intro j hj hji
    obtain ⟨digests, hin, hcells⟩ := hdeliver j hj hji
    exact inbox_of_cached K cache h hagr j i (vr j) count _ digests hin hcells
  intro T j hj hjT hh
  by_cases hiT : i ∈ C.holders T
  · refine GhostBatch.vector_congr count _ _ fun g hg => ?_
    simp only [repCopy, hiT, ↓reduceIte]
    exact (hvr j T g hj hjT hg).trans (hvr i T g hiD hiT hg).symm
  by_cases hown : K.owner T ∉ D.1
  · refine GhostBatch.vector_congr count _ _ fun g hg => ?_
    have hne : i ≠ K.owner T := fun e => hiT (e ▸ K.owner_held T)
    simp only [repCopy, hiT, hinbox _ hown (Ne.symm hne), repOutbox, hne, ↓reduceIte,
      Msg.part, List.getElem?_cons_zero, Msg.bitAt]
    rw [getD_flatMap_vector _ _ _ T (List.mem_filter.2 ⟨mem_terms T, by simp [hiT]⟩)
      (terms_nodup.filter _) g hg]
    exact (hvr j T g hj hjT hg).trans (hvr _ T g hown (K.owner_held T) hg).symm
  have hne : j ≠ K.owner T := fun e => hown (e ▸ hj)
  have hji : j ≠ i := fun e => hiT (e ▸ hjT)
  obtain ⟨digests, -, hcells⟩ := hdeliver j hj hji
  obtain ⟨d, hd⟩ : ∃ d : HashOutput, cache (.copy (vector count (vr j T))) = some d :=
    Option.isSome_iff_exists.1 (GhostBatch.forall₂_cell cache _ hcells T (mem_terms T))
  obtain ⟨vb, hvb⟩ : ∃ vb : HashOutput, cache (.copy (vector count (repCopy K i (vr i) count inbox T))) = some vb :=
    Option.isSome_iff_exists.1 (receivedCopy_cached K prims cache h hgood hagr i (vr i) count inbox hchecks j (vr j)
      (hinbox j hj hji) T hiT hjT hne)
  by_contra hvec
  apply hcollision
  unfold DomainCollision CacheHasCollision
  refine ⟨.copy (vector count (vr j T)), .copy (vector count (repCopy K i (vr i) count inbox T)), d, vb,
    fun e => hvec (Query.copy.inj e), ?_, ?_, heq_of_eq ?_⟩
  · simp [splitRegionCache, CopyDomain, hd]
  · simp [splitRegionCache, CopyDomain, hvb]
  · rw [← hagr _ _ hd, ← hagr _ _ hvb, hh]

/-- The equal batch outputs in the cache form of the ghost run. Two honest operators `i` and `i'` hold blocks with the
same circuits that have the form `GhostBatch.BlockShape` for each good `h'` that agrees with the hash
cache. Their sharing `vr` after `Rerand` agrees with `w`, each inbox holds the message of each other
honest operator with the copy hashes of the cache, and the cache has no collision in `CopyDomain`.
Then the two batch outputs are equal. -/
theorem blockOutputs_agree_of_cache (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (cache : HashCache C) (h : Query C → HashOutput) (hgood : Good prims h) (hagr : Agrees h cache)
    (w : Shares C Bit) (vr : C.Party → Shares C Bit) (i i' : C.Party) (hiD : i ∉ D.1) (hiD' : i' ∉ D.1)
    (keys keys' : Keys C) (x y : BatchStart C × Mail C E × List (List Bit))
    (hx : ∀ h', Good prims h' → Agrees h' cache → GhostBatch.BlockShape K circuits settings h' i keys x)
    (hy : ∀ h', Good prims h' → Agrees h' cache → GhostBatch.BlockShape K circuits settings h' i' keys' y)
    (hcircuits : x.1.circuits = y.1.circuits) (hvx : x.1.v' = vr i) (hvy : y.1.v' = vr i')
    (hvr : ∀ j T g, j ∉ D.1 → j ∈ C.holders T → g < (outputsOf x.1.circuits).length → vr j T g = w T g)
    (hdeliver : ∀ j, j ∉ D.1 → j ≠ i → ∃ digests,
      x.2.1 j = repOutbox K j (vr j) (outputsOf x.1.circuits).length digests i ∧
      List.Forall₂ (fun T d => cache (.copy (vector (outputsOf x.1.circuits).length (vr j T))) = some d)
        C.terms digests)
    (hdeliver' : ∀ j, j ∉ D.1 → j ≠ i' → ∃ digests,
      y.2.1 j = repOutbox K j (vr j) (outputsOf x.1.circuits).length digests i' ∧
      List.Forall₂ (fun T d => cache (.copy (vector (outputsOf x.1.circuits).length (vr j T))) = some d)
        C.terms digests)
    (hcollision : ¬ DomainCollision CopyDomain cache) :
    x.2.2 = y.2.2 := by
  have hchecks : ∀ h', Good prims h' → Agrees h' cache → repCheck K i x.2.1
      (copyHashes h' (repCopy K i (vr i) (outputsOf x.1.circuits).length x.2.1) (outputsOf x.1.circuits).length) :=
    fun h' hg' ha' => hvx ▸ (hx h' hg' ha').2.1
  have hchecks' : ∀ h', Good prims h' → Agrees h' cache → repCheck K i' y.2.1
      (copyHashes h' (repCopy K i' (vr i') (outputsOf x.1.circuits).length y.2.1) (outputsOf x.1.circuits).length) := by
    intro h' hg' ha'
    have := (hy h' hg' ha').2.1
    rwa [hvy, ← hcircuits] at this
  have hinbox : ∀ j, j ∉ D.1 → j ≠ i → x.2.1 j = repOutbox K j (vr j) (outputsOf x.1.circuits).length
      (copyHashes h (vr j) (outputsOf x.1.circuits).length) i := fun j hj hji => by
    obtain ⟨digests, hin, hcells⟩ := hdeliver j hj hji
    exact inbox_of_cached K cache h hagr j i (vr j) _ _ digests hin hcells
  have hinbox' : ∀ j, j ∉ D.1 → j ≠ i' → y.2.1 j = repOutbox K j (vr j) (outputsOf x.1.circuits).length
      (copyHashes h (vr j) (outputsOf x.1.circuits).length) i' := fun j hj hji => by
    obtain ⟨digests, hin, hcells⟩ := hdeliver' j hj hji
    exact inbox_of_cached K cache h hagr j i' (vr j) _ _ digests hin hcells
  exact blockOutputs_agree K circuits settings D h w vr i i' hiD hiD' keys keys' x y (hx h hgood hagr)
    (hy h hgood hagr) hcircuits hvx hvy hvr hinbox hinbox'
    (copySound_of_cache K prims D cache h hgood hagr w vr _ hvr i hiD x.2.1 hchecks hdeliver hcollision)
    (copySound_of_cache K prims D cache h hgood hagr w vr _ hvr i' hiD' y.2.1 hchecks' hdeliver' hcollision)

end OpenedAgreement

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace PassedShares

attribute [local instance] Classical.propDecidable

/-! ## The step with no run -/

section Core

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- A peer reshare fills each position of a filled term. -/
theorem filter_filled (T : C.Term) (hT : T ∈ filledTerms K) (count : ℕ) :
    (List.range count).filter (fun g => (filler K .peer T g).isSome) = List.range count := by
  obtain ⟨p, -, hp⟩ := Finset.mem_map.1 hT
  refine List.filter_eq_self.2 fun g _ => ?_
  simp only [filler, List.find?_isSome, decide_eq_true_eq]
  exact ⟨p, by simp [Committee.parties], hp⟩

/-- The filled history of the tuples of a batch at a filled term is the filled history of its AND
layers followed by `v'` at each output position. -/
theorem filledHistory_batchTuples (i : C.Party) (T : C.Term) (hiT : i ∈ C.holders T) (hT : T ∈ filledTerms K)
    (mode : ReshareMode) (cs : List Circuit) (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit)
    (v' : Shares C Bit) :
    filledHistory K i (batchTuples K mode cs inputs zs v') T =
      filledHistory K i (layerPrefix K mode cs inputs zs (depth cs)).2 T ++
        (List.range (outputsOf cs).length).map (v' T) := by
  simp only [batchTuples, filledHistory, hiT, ↓reduceIte, List.flatMap_append, List.flatMap_singleton,
    filter_filled K T hT]

/-- The filled history of the AND layers of a batch at a held term has a length that depends only on
the mode and the circuits. -/
theorem layerHistory_length (i i' : C.Party) (T : C.Term) (hiT : i ∈ C.holders T) (hiT' : i' ∈ C.holders T)
    (mode : ReshareMode) (cs : List Circuit) (inputs inputs' : List (C.Term → List Bit))
    (zs zs' : ℕ → Shares C Bit) :
    (filledHistory K i (layerPrefix K mode cs inputs zs (depth cs)).2 T).length =
      (filledHistory K i' (layerPrefix K mode cs inputs' zs' (depth cs)).2 T).length := by
  simp only [filledHistory, hiT, hiT', ↓reduceIte, List.length_flatMap, List.length_map, layerPrefix_tuples,
    List.map_map, Function.comp_def]

/-- The step with no run. Two starts with one mode and one circuit list and with the same filled
history of a filled term `T` hold the same `v'` at `T` below the output count. -/
theorem filled_agree (i i' : C.Party) (T : C.Term) (hiT : i ∈ C.holders T) (hiT' : i' ∈ C.holders T)
    (hT : T ∈ filledTerms K) (mode : ReshareMode) (cs : List Circuit) (inputs inputs' : List (C.Term → List Bit))
    (zs zs' : ℕ → Shares C Bit) (v v' : Shares C Bit)
    (h : filledHistory K i (batchTuples K mode cs inputs zs v) T =
      filledHistory K i' (batchTuples K mode cs inputs' zs' v') T) :
    ∀ g < (outputsOf cs).length, v T g = v' T g := by
  rw [filledHistory_batchTuples K i T hiT hT, filledHistory_batchTuples K i' T hiT' hT] at h
  have hseg := (List.append_inj h (layerHistory_length K i i' T hiT hiT' mode cs inputs inputs' zs zs')).2
  intro g hg
  have := congrArg (·[g]?) hseg
  simpa [List.getElem?_map, List.getElem?_range hg] using this

/-- Equal digest cells give equal histories when the hash cache has no collision in
`SplitHashDomain`. -/
theorem history_eq_of_digests (cache : HashCache C) (hno : ¬ DomainCollision SplitHashDomain cache)
    (h h' : List Bit) (salt salt' : List Bit) (hh hh' d : HashOutput)
    (c₁ : cache (.history h) = some hh) (c₂ : cache (.digest salt hh) = some d)
    (c₁' : cache (.history h') = some hh') (c₂' : cache (.digest salt' hh') = some d) : h = h' := by
  by_contra hne
  apply hno
  unfold DomainCollision CacheHasCollision
  by_cases hhh : hh = hh'
  · subst hhh
    refine ⟨.history h, .history h', hh, hh, fun e => hne (Query.history.inj e), ?_, ?_, HEq.rfl⟩
    · simp [splitRegionCache, SplitHashDomain, c₁]
    · simp [splitRegionCache, SplitHashDomain, c₁']
  · refine ⟨.digest salt hh, .digest salt' hh', d, d, fun e => hhh (Query.digest.inj e).2, ?_, ?_, HEq.rfl⟩
    · simp [splitRegionCache, SplitHashDomain, c₂]
    · simp [splitRegionCache, SplitHashDomain, c₂']

end Core

/-! ## The history at each recorded start -/

section Walk

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings)

/-- The history of a start is the filled history of the tuples of its batch. -/
def StartHistory (b : BatchStart C) : Prop :=
  b.state.history = filledHistory K b.ctx.self (batchTuples K b.mode b.circuits b.inputs b.zs b.v')

/-- The layers and `Rerand` of a recorded batch end at the filled history of the tuples of the batch. -/
theorem head_history (ctx : Context C) (mode : ReshareMode) (cs : List Circuit) (inputs : List (C.Term → List Bit))
    (L k : ℕ) (q₁ : (ℕ → Shares C Bit) × RunState C)
    (h₁ : some q₁ ∈ support ((recLayers K (realRunBuildingBlocks (G := RealSpec) K ctx mode) cs inputs
      (depth cs)).run ⟨fun _ => [], L, k⟩).run)
    (q₂ : Shares C Bit × RunState C)
    (h₂ : some q₂ ∈ support (((realRunBuildingBlocks (G := RealSpec) K ctx mode).rerand (outputShares K cs
      (layerPrefix K mode cs inputs q₁.1 (depth cs)).1) (outputsOf cs).length).run q₁.2).run) :
    q₂.2.history = filledHistory K ctx.self (batchTuples K mode cs inputs q₁.1 q₂.1) := by
  have hf := foldlM_layerBody_eq K (realRunBuildingBlocks (G := RealSpec) K ctx mode) cs inputs (depth cs)
  have h₁' : some (layerPrefix K mode cs inputs q₁.1 (depth cs), q₁.2) ∈ support
      ((((List.range (depth cs)).foldlM (layerBody K (realRunBuildingBlocks (G := RealSpec) K ctx mode) cs)
        (inputs, [])).run ⟨fun _ => [], L, k⟩).run) := by
    rw [hf, StateT.run_map]
    simp only [OptionT.run_map, support_map, Set.mem_image]
    exact ⟨some q₁, h₁, rfl⟩
  have he : (⟨fun _ => [], L, k⟩ : RunState C) =
      ⟨filledHistory K ctx.self ([] : List (Tuple C)), L + ([] : List (Tuple C)).length, k⟩ := by
    congr 1
    funext T
    simp [filledHistory]
  rw [he] at h₁'
  obtain ⟨hs, -⟩ := layers_support K ctx mode cs _ (inputs, []) L k _ h₁'
  have hr := rerand_support K ctx mode _ _ _ q₂ h₂
  dsimp only at hs
  rw [hr, hs]
  have hrec := record_history K ctx.self (layerPrefix K mode cs inputs q₁.1 (depth cs)).2
    ⟨outputShares K cs (layerPrefix K mode cs inputs q₁.1 (depth cs)).1, one K, q₂.1, (outputsOf cs).length, .peer⟩
    (L + (layerPrefix K mode cs inputs q₁.1 (depth cs)).2.length) k
  simp only at hrec
  rw [hrec]
  rfl

/-- One recorded batch records only starts with `StartHistory`. -/
theorem recBatch_history (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) (L k : ℕ) (z)
    (hz : z ∈ support ((recBatch K circuits settings ctx parameter jobs).run (L, k)).run.run) :
    ∀ b ∈ startsOf z.2, StartHistory K b := by
  simp only [recBatch, StateT.run_bind, StateT.run_get, pure_bind, RecM.liftS, StateT.run_mk, StateT.run_lift] at hz
  rcases BatchCounters.mem_support_lift_bind _ _ z hz with rfl | ⟨p, -, h₂⟩
  · simp [startsOf]
  rcases BatchCounters.mem_support_lift_bind _ _ _ h₂ with rfl | ⟨p₁, hp₁, h₃⟩
  · simp [startsOf]
  rcases BatchCounters.mem_support_lift_bind _ _ _ h₃ with rfl | ⟨p₂, hp₂, h₄⟩
  · simp [startsOf]
  obtain ⟨-, hq₁⟩ := mem_support_lift_run _ _ _ hp₁
  obtain ⟨-, hq₂⟩ := mem_support_lift_run _ _ _ hp₂
  have hh := head_history K ctx settings.mode _ p.1 L k p₁.1 hq₁ p₂.1 hq₂
  obtain ⟨hstarts, -⟩ := BatchCounters.recCheckOpen_counters K _ k _ z h₄
  intro b hb
  rw [hstarts, List.mem_singleton] at hb
  subst hb
  exact hh

/-- Each start that a recorded program on the counters records has `StartHistory`. -/
def Histories {β : Type} (x : StateT (ℕ × ℕ) (RecM C E) β) : Prop :=
  ∀ st z, z ∈ support ((x.run st).run.run) → ∀ b ∈ startsOf z.2, StartHistory K b

theorem histories_pure {β : Type} (b : β) : Histories K (pure b : StateT (ℕ × ℕ) (RecM C E) β) := by
  intro st z hz
  simp at hz
  subst hz
  simp [startsOf]

theorem histories_bind {β γ : Type} (x : StateT (ℕ × ℕ) (RecM C E) β) (f : β → StateT (ℕ × ℕ) (RecM C E) γ)
    (hx : Histories K x) (hf : ∀ b, Histories K (f b)) : Histories K (x >>= f) := by
  intro st z hz
  rw [StateT.run_bind] at hz
  obtain ⟨z₁, h₁, ⟨-, rfl⟩ | ⟨a, -, z₂, h₂, rfl⟩⟩ := mem_support_recM_bind _ _ z hz
  · exact hx st z₁ h₁
  · intro b hb
    rw [BatchCounters.startsOf_append, List.mem_append] at hb
    rcases hb with hb | hb
    · exact hx st z₁ h₁ b hb
    · exact hf a.1 a.2 z₂ h₂ b hb

theorem histories_liftS {β : Type} (y : PartyM C E RealSpec β) :
    Histories K (RecM.liftS (StateT.lift y : StateT (ℕ × ℕ) (PartyM C E RealSpec) β)) := by
  intro st z hz
  rw [(BatchCounters.mem_support_lift _ z hz).1]
  simp [startsOf]

theorem histories_recRun (i : C.Party) (keys : Keys C) (jobs : List Job) :
    Histories K (recRun K circuits settings i keys jobs) :=
  histories_bind K _ _ (histories_liftS K _) fun _ =>
    closed_batched (m := StateT (ℕ × ℕ) (RecM C E)) (fun x => Histories K x) (histories_pure K) (histories_bind K) _ _
      (fun js => fun ⟨L, k⟩ z hz => recBatch_history K circuits settings _ _ js L k z hz) jobs

theorem histories_ceremonyOutput (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    Histories K
      (ceremonyOutput (m := StateT (ℕ × ℕ) (RecM C E)) (fun oa => RecM.liftS (StateT.lift (oracleStep (tweakable oa))))
        keys.parameter (recRun K circuits settings i keys) top tree) :=
  closed_ceremonyOutput (m := StateT (ℕ × ℕ) (RecM C E)) (fun x => Histories K x) (histories_pure K) (histories_bind K) _
    (fun _ => histories_liftS K _) _ (histories_recRun K circuits settings i keys) _ top tree

theorem histories_of_silent {β γ : Type} (x : RecM C E β) (f : β → RecM C E γ)
    (hf : ∀ b, ∀ w ∈ support (f b).run.run, w.2 = []) (z : Option γ × List (RecEvent C E))
    (hz : z ∈ support (x >>= f).run.run) (hx : ∀ z₁ ∈ support x.run.run, ∀ b ∈ startsOf z₁.2, StartHistory K b) :
    ∀ b ∈ startsOf z.2, StartHistory K b := by
  obtain ⟨z₁, h₁, hlog⟩ := BatchCounters.record_of_bind_silent _ _ hf z hz
  rw [hlog]
  exact hx z₁ h₁

end Walk

/-! ## The history on the ghost run -/

section Ghost

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (prims : Primitives)
  (budget : StartBudget)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The first ceremony of `firstBatches` is the first ceremony of `BatchCounters`. -/
theorem firstJobs_eq (tree : Tree) : CheckTiming.firstJobs tree = BatchCounters.firstJobs tree := by
  cases tree <;> rfl

end Ghost

/-! ## The agreement of the shares after `Rerand` -/

section Agreement

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (prims : Primitives)
  (budget : StartBudget)

/-- The digests that operator `j` with the start `b` sends in the digest round. For each held term
`T` the digest is the cell `.digest salt hh` of the cache, where `hh` is the cell `.history` of a
history that extends the history of `b`. -/
def HonestDigests (cache : HashCache C) (j : C.Party) (b : BatchStart C) (digests : List HashOutput) : Prop :=
  ∃ hist : C.Term → List Bit, ∀ T, j ∈ C.holders T → b.state.history T <+: hist T ∧
    ∃ salt hh d, cache (.history (hist T)) = some hh ∧ cache (.digest salt hh) = some d ∧
      digests[C.terms.idxOf T]? = some d

omit [Field E] [Algebra Bit E] in
/-- Two prefixes of one list with one length are equal. -/
theorem prefix_eq {α : Type} {l₁ l₂ l : List α} (h₁ : l₁ <+: l) (h₂ : l₂ <+: l) (hlen : l₁.length = l₂.length) :
    l₁ = l₂ :=
  (List.prefix_of_prefix_length_le h₁ h₂ hlen.le).eq_of_length hlen

end Agreement

end PassedShares

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- The PRF value `F(seed, x)` in the cell `.prf seed x` of a hash cache. -/
def prfCell (cache : HashCache C) (seed : HashOutput) (x : Point) : Digest :=
  truncateHash ((cache (.prf seed x)).getD 0)

/-- The bits of the PRF values of `seed` at `points` in a hash cache. -/
def prfBits (cache : HashCache C) (seed : HashOutput) (points : List Point) : List Bit :=
  points.flatMap fun x => bitsOfDigest (prfCell cache seed x)

/-- The cells `.prf seed x` of the points are in a hash cache. -/
def PrfCached (cache : HashCache C) (seed : HashOutput) (points : List Point) : Prop :=
  ∀ x ∈ points, (cache (.prf seed x)).isSome

theorem prfCell_of_le {c c' : HashCache C} (hle : c ≤ c') {seed : HashOutput} {x : Point}
    (hx : (c (.prf seed x)).isSome) : prfCell c' seed x = prfCell c seed x := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hx
  simp only [prfCell, hu, hle hu]

theorem prfBits_of_le {c c' : HashCache C} (hle : c ≤ c') {seed : HashOutput} {points : List Point}
    (h : PrfCached c seed points) : prfBits c' seed points = prfBits c seed points := by
  unfold prfBits
  exact List.flatMap_congr fun x hx => by rw [prfCell_of_le hle (h x hx)]

theorem PrfCached.mono {c c' : HashCache C} (hle : c ≤ c') {seed : HashOutput} {points : List Point}
    (h : PrfCached c seed points) : PrfCached c' seed points := fun x hx => by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (h x hx)
  simp [hle hu]

theorem free_map {α β : Type} (f : α → β) (oa : OracleComp (LocalSpec C) α) :
    free (f <$> oa) = f <$> free oa :=
  simulateQ_map _ _ _

/-- A free call of `H` on an input that the MPC does not evaluate leaves its answer in the hash cache. -/
theorem streamWorld_free_hash {q : Query C} (hq : ¬ IsFixed q) (s : HashCache C × HiddenCache C) :
    ∀ z ∈ support ((simulateQ (streamWorld prims D) (free (liftComp (hashQuery q) (LocalSpec C)))).run s),
      s ≤ z.2 ∧ z.2.1 q = some z.1 := by
  intro z hz
  refine ⟨streamWorld_le prims D _ s z hz, ?_⟩
  obtain ⟨h, hc⟩ := s
  rw [show free (liftComp (hashQuery q) (LocalSpec C)) =
      (liftM ((WorldSpec C).query (.inr (.inr (.inl q)))) : OracleComp (WorldSpec C) _) from rfl,
    simulateQ_query, streamWorld_apply_of_not prims D _ (by simp [FreeHiddenStream])] at hz
  simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map, onHash_run, support_map,
    Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  exact hashAnswer_cached prims hq h r hr

/-- A free call of `F(seed, x)` leaves its cell in the hash cache and returns `prfCell` of it. -/
theorem streamWorld_free_prf (seed : HashOutput) (x : Point) (s : HashCache C × HiddenCache C) :
    ∀ z ∈ support ((simulateQ (streamWorld prims D) (free (liftComp (prf (C := C) seed x) (LocalSpec C)))).run s),
      s ≤ z.2 ∧ (z.2.1 (.prf seed x)).isSome ∧ z.1 = prfCell z.2.1 seed x := by
  intro z hz
  simp only [prf, liftComp_map, free, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  obtain ⟨hle, hr⟩ := streamWorld_free_hash prims D (q := .prf seed x) (by rintro ⟨_, h, _⟩; cases h) s r hr
  exact ⟨hle, by simp [hr], by simp [prfCell, hr]⟩

/-- A free call of the bits of `F(seed, x)` at the points leaves their cells in the hash cache and
returns `prfBits` of them. -/
theorem streamWorld_free_prfBits (seed : HashOutput) :
    ∀ (points : List Point) (s : HashCache C × HiddenCache C),
      ∀ z ∈ support ((simulateQ (streamWorld prims D) (free (liftComp
          (points.flatMapM fun x => bitsOfDigest <$> prf (C := C) seed x) (LocalSpec C)))).run s),
        s ≤ z.2 ∧ PrfCached z.2.1 seed points ∧ z.1 = prfBits z.2.1 seed points
  | [], s, z, hz => by
    simp only [List.flatMapM_nil, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, fun x hx => by simp at hx, rfl⟩
  | x :: points, s, z, hz => by
    simp only [List.flatMapM_cons, liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    rw [liftComp_map, free_map, simulateQ_map, StateT.run_map, support_map] at ha
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨hle₁, hcell, ha⟩ := streamWorld_free_prf prims D seed x s a ha
    obtain ⟨hle₂, hcached, hb⟩ := streamWorld_free_prfBits seed points a.2 b hb
    refine ⟨hle₁.trans hle₂, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact (PrfCached.mono hle₂.1 (points := [y]) fun _ h => by
          rw [List.mem_singleton.1 h]; exact hcell) y (List.mem_singleton_self y)
      · exact hcached y hy
    · simp only [prfBits, List.flatMap_cons] at hb ⊢
      rw [hb, ha, prfCell_of_le hle₂.1 hcell]

/-- The shares of an operator of the terms of a list, as `inputQuery` computes them. -/
theorem streamWorld_free_termShares (ctx : Context C) (job : Job) :
    ∀ (terms : List C.Term) (s : HashCache C × HiddenCache C),
      ∀ z ∈ support ((simulateQ (streamWorld prims D) (free (liftComp (terms.mapM fun T =>
          if ctx.self ∈ C.holders T then job.points.flatMapM fun x => bitsOfDigest <$> prf (C := C) (ctx.keys.seed T) x
          else pure []) (LocalSpec C)))).run s),
        s ≤ z.2 ∧ (∀ T ∈ terms, ctx.self ∈ C.holders T → PrfCached z.2.1 (ctx.keys.seed T) job.points) ∧
          z.1 = terms.map fun T => if ctx.self ∈ C.holders T then prfBits z.2.1 (ctx.keys.seed T) job.points else []
  | [], s, z, hz => by
    simp only [List.mapM_nil, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, fun T hT => by simp at hT, rfl⟩
  | T :: terms, s, z, hz => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    obtain ⟨hle₂, hcached, hb⟩ := streamWorld_free_termShares ctx job terms a.2 b hb
    have hhead : s ≤ a.2 ∧ (ctx.self ∈ C.holders T → PrfCached a.2.1 (ctx.keys.seed T) job.points) ∧
        a.1 = if ctx.self ∈ C.holders T then prfBits a.2.1 (ctx.keys.seed T) job.points else [] := by
      by_cases hT : ctx.self ∈ C.holders T
      · simp only [hT, ↓reduceIte] at ha ⊢
        obtain ⟨hle, hc, he⟩ := streamWorld_free_prfBits prims D _ _ s a ha
        exact ⟨hle, fun _ => hc, he⟩
      · simp only [hT, ↓reduceIte, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at ha ⊢
        subst ha
        exact ⟨le_rfl, fun h => h.elim, rfl⟩
    obtain ⟨hle₁, hc₁, he₁⟩ := hhead
    refine ⟨hle₁.trans hle₂, ?_, ?_⟩
    · intro T' hT' hself
      rcases List.mem_cons.1 hT' with rfl | hT'
      · exact (hc₁ hself).mono hle₂.1
      · exact hcached T' hT' hself
    · simp only [List.map_cons, hb, he₁]
      congr 1
      split_ifs with hT
      · exact (prfBits_of_le hle₂.1 (hc₁ hT)).symm
      · rfl

/-- The input shares of a job at an operator, by the free calls of `inputQuery`. Each held term is
`prfBits` on the seed of the operator in the cache after the call, and these cells are in the cache. -/
theorem streamWorld_free_inputQuery (ctx : Context C) (job : Job) (s : HashCache C × HiddenCache C) :
    ∀ z ∈ support ((simulateQ (streamWorld prims D) (free (liftComp (inputQuery ctx job) (LocalSpec C)))).run s),
      s ≤ z.2 ∧ ∀ T, (ctx.self ∈ C.holders T → PrfCached z.2.1 (ctx.keys.seed T) job.points) ∧
        z.1 T = if ctx.self ∈ C.holders T then prfBits z.2.1 (ctx.keys.seed T) job.points else [] := by
  intro z hz
  simp only [inputQuery, liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  obtain ⟨hle, hc, he⟩ := streamWorld_free_termShares prims D ctx job C.terms s a ha
  refine ⟨hle, fun T => ⟨hc T (mem_terms T), ?_⟩⟩
  simp only [he]
  exact getD_terms_idxOf _ _ T

/-- The input shares of a list of jobs at an operator, by the free calls of `inputQuery`. -/
theorem streamWorld_free_jobInputs (ctx : Context C) :
    ∀ (jobs : List Job) (s : HashCache C × HiddenCache C),
      ∀ z ∈ support ((simulateQ (streamWorld prims D)
          (free (liftComp (jobs.mapM (inputQuery ctx)) (LocalSpec C)))).run s),
        s ≤ z.2 ∧ (∀ job ∈ jobs, ∀ T, ctx.self ∈ C.holders T → PrfCached z.2.1 (ctx.keys.seed T) job.points) ∧
          z.1 = jobs.map fun job T =>
            if ctx.self ∈ C.holders T then prfBits z.2.1 (ctx.keys.seed T) job.points else []
  | [], s, z, hz => by
    simp only [List.mapM_nil, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, fun job hjob => by simp at hjob, rfl⟩
  | job :: jobs, s, z, hz => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
      simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    obtain ⟨hle₁, ha⟩ := streamWorld_free_inputQuery prims D ctx job s a ha
    obtain ⟨hle₂, hcached, hb⟩ := streamWorld_free_jobInputs ctx jobs a.2 b hb
    refine ⟨hle₁.trans hle₂, ?_, ?_⟩
    · intro job' hjob' T hT
      rcases List.mem_cons.1 hjob' with rfl | hjob'
      · exact ((ha T).1 hT).mono hle₂.1
      · exact hcached job' hjob' T hT
    · simp only [List.map_cons, hb]
      congr 1
      funext T
      rw [(ha T).2]
      split_ifs with hT
      · exact (prfBits_of_le hle₂.1 ((ha T).1 hT)).symm
      · rfl

/-- The input shares of a list of jobs at an honest operator, in a cache `c` after the call. When the
seeds do not differ, they are `batchInputs` on the table of `c` and the seeds of the game. So the
honest inputs of a batch are the inputs of `batchInputs_main`, which have `MainInputs`. -/
theorem jobInputs_eq_batchInputs (keys : C.Party → Option (Keys C)) (hsame : seedsDiffer D keys = false)
    (ctx : Context C) (hi : ctx.self ∉ D.1) (hkeys : keys ctx.self = some ctx.keys) (jobs : List Job)
    (s : HashCache C × HiddenCache C) (z : List (C.Term → List Bit) × (HashCache C × HiddenCache C))
    (hz : z ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (jobs.mapM (inputQuery ctx)) (LocalSpec C)))).run s))
    (c : HashCache C) (hc : z.2.1 ≤ c) :
    z.1 = batchInputs (fun q => (c q).getD 0) (gameSeeds D keys) jobs ctx.self := by
  obtain ⟨-, hcached, he⟩ := streamWorld_free_jobInputs prims D ctx jobs s z hz
  rw [he]
  unfold batchInputs
  refine List.map_congr_left fun job hjob => ?_
  funext T
  split_ifs with hT
  · rw [← prfBits_of_le hc (hcached job hjob T hT), seed_eq_gameSeeds D keys hsame _ hi _ hkeys T hT]
    rfl
  · rfl

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.OpenedAgreement.blockOutputs_agree_of_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.OpenedAgreement.blockOutputs_agree_of_cache

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.jobInputs_eq_batchInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.jobInputs_eq_batchInputs

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.streamWorld_free_jobInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.streamWorld_free_jobInputs
