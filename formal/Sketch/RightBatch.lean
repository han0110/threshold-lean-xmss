import Sketch.TreeOutput

/-!
# Right tuples and a good opening give a right batch output

This file proves the hop H11 of `DkgCorrectness` on the program of one batch of an honest
operator.

* `refHolder D T` is the first honest holder of term `T`. `reconstruct_honest` shows that
  `reconstruct` on the honest views reads term `T` from it.
* `shares_agree_of_multVerifyAgree` gives the agreement of the honest copies of the opened sharing
  from `MultVerifyAgree`, the form that the case split of the pilot gives.
* `batchTuples` are the tuples that `runJobs` gives to the check, from the inputs, the products of
  the AND layers and the sharing after `Rerand`. The layer step reads each term alone, so
  `tupleAt_glued` shows that the reconstructed tuples are the tuples of one glued trace.
* `layerInv_layerPrefix` gives the invariant `LayerInv` of the honest run to a trace with product
  tuples. `repCopy_sound` is `main_openCopy_sound` with `H` fixed to `h`.
* `opened_right` is the hop on the values. Right tuples, agreeing parameters and seeds, agreeing
  copies of the opened sharing, the honest messages of `OpenRep` as sent and no copy collision give
  the circuit values on the PRF values of the seeds.
* `holds_realBatch` is the path of one real batch with `H` fixed to `h`, and `realBatch_rightBatch`
  is the hop on the program of one batch, with the conclusion `RightBatch`.
* The agreement of the PRSS keys and the agreement of the tuples of the AND layers are no premise.
  The PRSS keys change only the products and the sharing after `Rerand`, which are free values of
  the trace, and the glued trace reads each term from one holder.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity ENNReal

noncomputable section

namespace ThresholdLeanXmss.Sketch

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The holder that `reconstruct` reads -/

section Glue

/-- The first honest holder of term `T` in the order of `C.parties`. `reconstruct` on the honest
views reads term `T` from it. -/
def refHolder (D : C.Coalition) (T : C.Term) : C.Party :=
  (C.parties.find? fun j => j ∈ C.holders T ∧ j ∉ D.1).get (by
    obtain ⟨j, hj, hjD⟩ := exists_honest_holder D T
    exact List.find?_isSome.2 ⟨j, List.mem_finRange j, by simp [hj, hjD]⟩)

theorem refHolder_spec (D : C.Coalition) (T : C.Term) : refHolder D T ∈ C.holders T ∧ refHolder D T ∉ D.1 := by
  unfold refHolder
  generalize_proofs hp
  have h := List.find?_some (Option.some_get hp).symm
  simpa using h

theorem reconstruct_honest {α : Type} [Inhabited α] (D : C.Coalition) (views : C.Party → Option (C.Term → α))
    (f : C.Party → C.Term → α) (hv : ∀ j, views j = if j ∈ D.1 then none else some (f j)) (T : C.Term) :
    reconstruct views T = f (refHolder D T) T := by
  have key : ∀ l : List C.Party,
      ((l.filterMap fun i => if i ∈ C.holders T then views i else none).head?.map (· T)) =
        (l.find? fun j => j ∈ C.holders T ∧ j ∉ D.1).map fun j => f j T := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      by_cases ha : a ∈ C.holders T ∧ a ∉ D.1
      · simp [hv a, ha.1, ha.2, List.find?_cons_of_pos]
      · rw [List.find?_cons_of_neg (by simpa using ha), ← ih, List.filterMap_cons]
        by_cases h1 : a ∈ C.holders T
        · have h2 : a ∈ D.1 := by tauto
          simp [h1, hv a, h2]
        · simp [h1]
  unfold reconstruct refHolder
  rw [key, Option.map_eq_some_iff.2 ⟨_, Option.some_get _ |>.symm, rfl⟩]
  rfl

end Glue

/-! ## The trace of one batch at one operator -/

section Trace

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (mode : ReshareMode) (jobs : List Circuit)

/-- One AND layer of `runJobs` with the products `zs l` of layer `l`. -/
def layerStep (zs : ℕ → Shares C Bit) (p : List (C.Term → List Bit) × List (Tuple C)) (l : ℕ) :
    List (C.Term → List Bit) × List (Tuple C) :=
  (appendLayer jobs l p.1 (zs l),
    p.2 ++ [⟨layerX K jobs l p.1, layerY K jobs l p.1, zs l, (gatesAt jobs l).length, mode⟩])

/-- The wires and the tuples after the first `d` AND layers of `runJobs` on `inputs`, with the
products `zs`. -/
def layerPrefix (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (d : ℕ) :
    List (C.Term → List Bit) × List (Tuple C) :=
  (List.range d).foldl (layerStep K mode jobs zs) (inputs, [])

/-- The tuples that `runJobs` on `inputs` gives to the check, with the products `zs` of the layers
and the sharing `v'` after `Rerand`. -/
def batchTuples (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (v' : Shares C Bit) :
    List (Tuple C) :=
  (layerPrefix K mode jobs inputs zs (depth jobs)).2 ++
    [⟨outputShares K jobs (layerPrefix K mode jobs inputs zs (depth jobs)).1, one K, v', (outputsOf jobs).length, .peer⟩]

theorem layerPrefix_succ (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (d : ℕ) :
    layerPrefix K mode jobs inputs zs (d + 1) = layerStep K mode jobs zs (layerPrefix K mode jobs inputs zs d) d := by
  simp [layerPrefix, List.range_succ, List.foldl_append]

theorem layerPrefix_tuples (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (d : ℕ) :
    (layerPrefix K mode jobs inputs zs d).2 = (List.range d).map fun l =>
      ⟨layerX K jobs l (layerPrefix K mode jobs inputs zs l).1, layerY K jobs l (layerPrefix K mode jobs inputs zs l).1,
        zs l, (gatesAt jobs l).length, mode⟩ := by
  induction d with
  | zero => rfl
  | succ d ih => rw [layerPrefix_succ, layerStep, ih, List.range_succ, List.map_append, List.map_singleton]

theorem length_layerPrefix (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (d : ℕ) :
    (layerPrefix K mode jobs inputs zs d).1.length = inputs.length := by
  induction d with
  | zero => rfl
  | succ d ih => rw [layerPrefix_succ, layerStep, length_appendLayer, ih]

theorem length_batchTuples (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (v' : Shares C Bit) :
    (batchTuples K mode jobs inputs zs v').length = depth jobs + 1 := by
  simp [batchTuples, layerPrefix_tuples]

theorem batchTuples_layer (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (v' : Shares C Bit) (l : ℕ)
    (hl : l < depth jobs) :
    (batchTuples K mode jobs inputs zs v')[l]? = some ⟨layerX K jobs l (layerPrefix K mode jobs inputs zs l).1,
      layerY K jobs l (layerPrefix K mode jobs inputs zs l).1, zs l, (gatesAt jobs l).length, mode⟩ := by
  rw [batchTuples, List.getElem?_append_left (by simpa [layerPrefix_tuples] using hl), layerPrefix_tuples]
  simp [List.getElem?_range hl]

theorem batchTuples_output (inputs : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (v' : Shares C Bit) :
    (batchTuples K mode jobs inputs zs v')[depth jobs]? = some ⟨outputShares K jobs
      (layerPrefix K mode jobs inputs zs (depth jobs)).1, one K, v', (outputsOf jobs).length, .peer⟩ := by
  rw [batchTuples, List.getElem?_append_right (by simp [layerPrefix_tuples])]
  simp [layerPrefix_tuples]

/-- Two traces agree on term `T`. -/
def AgreeAt (T : C.Term) (p q : List (C.Term → List Bit) × List (Tuple C)) : Prop :=
  p.1.length = q.1.length ∧ (∀ k, (p.1.getD k fun _ => []) T = (q.1.getD k fun _ => []) T) ∧
    p.2.length = q.2.length ∧ ∀ m : ℕ, (p.2[m]?).map (fun τ : Tuple C => (τ.x T, τ.y T, τ.z T)) =
      (q.2[m]?).map fun τ : Tuple C => (τ.x T, τ.y T, τ.z T)

theorem agreeAt_layerStep (T : C.Term) (zs zs' : ℕ → Shares C Bit) (p q : List (C.Term → List Bit) × List (Tuple C))
    (l : ℕ) (h : AgreeAt T p q) (hz : zs l T = zs' l T) :
    AgreeAt T (layerStep K mode jobs zs p l) (layerStep K mode jobs zs' q l) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by simp [layerStep, length_appendLayer, h1], fun k => ?_, by simp [layerStep, h3], fun m => ?_⟩
  · simp only [layerStep, getD_appendLayer, h1]
    split_ifs
    · simp only [newWires, hz, h2 k]
    · rfl
  · simp only [layerStep, List.getElem?_append, h3]
    split_ifs
    · exact h4 m
    · simp only [List.getElem?_singleton]
      split_ifs
      · simp [layerX_congr K jobs l p.1 q.1 T h2, layerY_congr K jobs l p.1 q.1 T h2, hz]
      · rfl

theorem agreeAt_layerPrefix (T : C.Term) (I I' : List (C.Term → List Bit)) (zs zs' : ℕ → Shares C Bit)
    (hI : I.length = I'.length) (hIT : ∀ k, (I.getD k fun _ => []) T = (I'.getD k fun _ => []) T)
    (hz : ∀ l, zs l T = zs' l T) (d : ℕ) :
    AgreeAt T (layerPrefix K mode jobs I zs d) (layerPrefix K mode jobs I' zs' d) := by
  induction d with
  | zero => exact ⟨hI, hIT, rfl, fun _ => rfl⟩
  | succ d ih => rw [layerPrefix_succ, layerPrefix_succ]; exact agreeAt_layerStep K mode jobs T zs zs' _ _ d ih (hz d)

theorem batchTuples_agreeAt (T : C.Term) (I I' : List (C.Term → List Bit)) (zs zs' : ℕ → Shares C Bit)
    (v v'' : Shares C Bit) (h : AgreeAt T (layerPrefix K mode jobs I zs (depth jobs)) (layerPrefix K mode jobs I' zs' (depth jobs)))
    (hv : v T = v'' T) (m : ℕ) :
    ((batchTuples K mode jobs I zs v)[m]?).map (fun τ : Tuple C => (τ.x T, τ.y T, τ.z T)) =
      ((batchTuples K mode jobs I' zs' v'')[m]?).map fun τ : Tuple C => (τ.x T, τ.y T, τ.z T) := by
  obtain ⟨-, h2, h3, h4⟩ := h
  simp only [batchTuples, List.getElem?_append, h3]
  split_ifs
  · exact h4 m
  · simp only [List.getElem?_singleton]
    split_ifs
    · simp [outputShares_congr K jobs _ _ T h2, hv]
    · rfl

theorem batchTuples_shape (I : List (C.Term → List Bit)) (zs : ℕ → Shares C Bit) (v : Shares C Bit) :
    (batchTuples K mode jobs I zs v).map (fun τ : Tuple C => (τ.count, τ.mode)) =
      (List.range (depth jobs)).map (fun l => ((gatesAt jobs l).length, mode)) ++ [((outputsOf jobs).length, .peer)] := by
  simp [batchTuples, layerPrefix_tuples]

end Trace

/-! ## The tuples that `reconstruct` reads are one glued trace -/

section Glued

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (mode : ReshareMode) (jobs : List Circuit)

/-- The first honest view is the view of an honest operator. -/
theorem firstInput_honest {α : Type} [Inhabited α] (D : C.Coalition) (x : C.Party → α) :
    ∃ j, j ∉ D.1 ∧ firstInput (fun i => if i ∈ D.1 then none else some (x i)) = x j := by
  obtain ⟨T₀, -⟩ := lackedTerm_empty (C := C)
  obtain ⟨j₀, -, hj₀⟩ := exists_honest_holder D T₀
  unfold firstInput
  rcases hl : C.parties.filterMap (fun i => if i ∈ D.1 then none else some (x i)) with _ | ⟨a, rest⟩
  · have : x j₀ ∈ C.parties.filterMap (fun i => if i ∈ D.1 then none else some (x i)) :=
      List.mem_filterMap.2 ⟨j₀, List.mem_finRange j₀, by simp [hj₀]⟩
    rw [hl] at this
    simp at this
  · have : a ∈ C.parties.filterMap (fun i => if i ∈ D.1 then none else some (x i)) := by
      rw [hl]; exact List.mem_cons_self
    obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 this
    split_ifs at hj with hjD
    exact ⟨j, hjD, (Option.some.inj hj).symm⟩

/-- The glued products, each term from its holder `refHolder D T`. -/
def gluedProducts (D : C.Coalition) (zs : C.Party → ℕ → Shares C Bit) : ℕ → Shares C Bit :=
  fun l T => zs (refHolder D T) l T

/-- The glued sharing after `Rerand`, each term from its holder `refHolder D T`. -/
def gluedShares (D : C.Coalition) (v' : C.Party → Shares C Bit) : Shares C Bit :=
  fun T => v' (refHolder D T) T

/-- `reconstruct` on the honest views of the tuples of the honest traces reads the glued trace. The
glued inputs `I` agree with the inputs of the holder of each term. -/
theorem tupleAt_glued (D : C.Coalition) (inputs : C.Party → List (C.Term → List Bit))
    (zs : C.Party → ℕ → Shares C Bit) (v' : C.Party → Shares C Bit) (x : C.Party → List (Tuple C))
    (hx : ∀ j, j ∉ D.1 → x j = batchTuples K mode jobs (inputs j) (zs j) (v' j)) (I : List (C.Term → List Bit))
    (hI : ∀ T, I.length = (inputs (refHolder D T)).length ∧
      ∀ k, (I.getD k fun _ => []) T = ((inputs (refHolder D T)).getD k fun _ => []) T)
    (m : ℕ) (τ : Tuple C) (hτ : (batchTuples K mode jobs I (gluedProducts D zs) (gluedShares D v'))[m]? = some τ) :
    (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).x = τ.x ∧
      (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).y = τ.y ∧
      (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).z = τ.z ∧
      (tupleAt (fun i => if i ∈ D.1 then none else some (x i)) m).count = τ.count := by
  have hm : m < depth jobs + 1 := by
    rw [← length_batchTuples K mode jobs I (gluedProducts D zs) (gluedShares D v')]
    exact (List.getElem?_eq_some_iff.1 hτ).1
  have hsome : ∀ j, j ∉ D.1 → ∃ σ, (x j)[m]? = some σ := fun j hj =>
    ⟨(x j)[m]'(by rw [hx j hj, length_batchTuples]; exact hm), List.getElem?_eq_getElem _⟩
  have hagree : ∀ T, ((x (refHolder D T))[m]?).map (fun σ : Tuple C => (σ.x T, σ.y T, σ.z T)) =
      some (τ.x T, τ.y T, τ.z T) := by
    intro T
    have h := batchTuples_agreeAt K mode jobs T I (inputs (refHolder D T)) (gluedProducts D zs)
      (zs (refHolder D T)) (gluedShares D v') (v' (refHolder D T))
      (agreeAt_layerPrefix K mode jobs T _ _ (gluedProducts D zs) (zs (refHolder D T)) (hI T).1 (hI T).2
        (fun l => rfl) _) rfl m
    rw [hx _ (refHolder_spec D T).2, ← h, hτ]
    rfl
  have hrec : ∀ (part : Tuple C → Shares C Bit) (hpart : ∀ T, ((x (refHolder D T))[m]?).map (fun σ => part σ T) =
      some (part τ T)),
      reconstruct (fun i => ((if i ∈ D.1 then none else some (x i)).bind (·[m]?)).map part) = part τ := by
    intro part hpart
    funext T
    rw [reconstruct_honest D _ (fun j => (((x j)[m]?).map part).getD fun _ _ => 0) (fun j => ?_) T]
    · have := hpart T
      rcases h : (x (refHolder D T))[m]? with _ | σ
      · rw [h] at this; cases this
      · rw [h] at this
        simpa using this
    · by_cases hj : j ∈ D.1
      · simp [hj]
      · obtain ⟨σ, hσ⟩ := hsome j hj
        simp [hj, hσ]
  have hpart : ∀ T, ∃ σ, (x (refHolder D T))[m]? = some σ ∧ σ.x T = τ.x T ∧ σ.y T = τ.y T ∧ σ.z T = τ.z T := by
    intro T
    have := hagree T
    rcases h : (x (refHolder D T))[m]? with _ | σ
    · simp [h] at this
    · simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      exact ⟨σ, rfl, this⟩
  refine ⟨hrec _ fun T => ?_, hrec _ fun T => ?_, hrec _ fun T => ?_, ?_⟩
  · obtain ⟨σ, hσ, h⟩ := hpart T; simp [hσ, h.1]
  · obtain ⟨σ, hσ, h⟩ := hpart T; simp [hσ, h.2.1]
  · obtain ⟨σ, hσ, h⟩ := hpart T; simp [hσ, h.2.2]
  · obtain ⟨j, hj, hfirst⟩ := firstInput_honest D x
    unfold tupleAt
    simp only [hfirst]
    have h1 := congrArg (·[m]?) (batchTuples_shape K mode jobs (inputs j) (zs j) (v' j))
    have h2 := congrArg (·[m]?) (batchTuples_shape K mode jobs I (gluedProducts D zs) (gluedShares D v'))
    simp only [List.getElem?_map, hτ, ← hx j hj] at h1 h2
    rw [← h2] at h1
    rcases hxj : (x j)[m]? with _ | σ
    · rw [hxj] at h1; cases h1
    · rw [hxj] at h1
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
      simp [h1.1]

/-- The agreement of the copies of `F_multVerify` gives the agreement of the honest copies of the
sharing after `Rerand`, which is `z` of the last tuple. -/
theorem shares_agree_of_multVerifyAgree (D : C.Coalition) (inputs : C.Party → List (C.Term → List Bit))
    (zs : C.Party → ℕ → Shares C Bit) (v' : C.Party → Shares C Bit) (x : C.Party → List (Tuple C))
    (hx : ∀ j, j ∉ D.1 → x j = batchTuples K mode jobs (inputs j) (zs j) (v' j))
    (hagree : MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i))) :
    ∀ T j j', j ∉ D.1 → j' ∉ D.1 → j ∈ C.holders T → j' ∈ C.holders T →
      ∀ g < (outputsOf jobs).length, v' j T g = v' j' T g := by
  intro T j j' hj hj' hjT hj'T g hg
  obtain ⟨j₀, hj₀, hfirst⟩ := firstInput_honest D x
  have hlast : ∀ k, k ∉ D.1 → (x k)[depth jobs]? = some ⟨outputShares K jobs
      (layerPrefix K mode jobs (inputs k) (zs k) (depth jobs)).1, one K, v' k, (outputsOf jobs).length, .peer⟩ :=
    fun k hk => by rw [hx k hk, batchTuples_output]
  have hcount : (((List.range (firstInput (fun i => if i ∈ D.1 then none else some (x i))).length).map
      (tupleAt (fun i => if i ∈ D.1 then none else some (x i)))).getD (depth jobs)
        ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, .peer⟩).count = (outputsOf jobs).length := by
    rw [hfirst, hx j₀ hj₀, length_batchTuples, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, tupleAt, hfirst, hlast j₀ hj₀]
  have h := hagree (depth jobs) (by rw [hfirst, hx j₀ hj₀, length_batchTuples]; omega) T j hjT j' hj'T hj hj' g
    (by rw [hcount]; exact hg)
  simp only [hj, hj', ↓reduceIte, Option.bind_some, hlast j hj, hlast j' hj', Option.map_some, Option.some.injEq,
    Prod.mk.injEq] at h
  exact h.2.2

end Glued

/-! ## The values of one trace with product tuples -/

section Values

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (mode : ReshareMode) (jobs : List Circuit)

/-- `appendLayer` reads the products only at the gates of the layer. -/
theorem appendLayer_congr (l : ℕ) (w : List (C.Term → List Bit)) (z z' : Shares C Bit)
    (h : ∀ T g, g < (gatesAt jobs l).length → z T g = z' T g) :
    appendLayer jobs l w z = appendLayer jobs l w z' := by
  unfold appendLayer
  refine List.map_congr_left fun p _ => funext fun T => ?_
  obtain ⟨w', k⟩ := p
  dsimp only
  congr 1
  refine List.map_congr_left fun q hq => ?_
  obtain ⟨hq, -⟩ := List.mem_filter.1 hq
  have hlt := List.snd_lt_of_mem_zipIdx hq
  obtain ⟨a, g⟩ := q
  exact h T g (by simpa using hlt)

variable (x : C.Party → List (C.Term → List Bit))

/-- With product tuples, the wires of a trace from the common inputs keep the invariant `LayerInv`
of the honest run. -/
theorem layerInv_layerPrefix (hx : MainInputs jobs noCoalition x) (Z : ℕ → Shares C Bit)
    (hprod : ∀ l < depth jobs, ∀ g < (gatesAt jobs l).length, shareValue (Z l) g =
      shareValue (layerX K jobs l (layerPrefix K mode jobs
        ((List.range jobs.length).map fun k => reconstruct fun i => (x i)[k]?) Z l).1) g *
      shareValue (layerY K jobs l (layerPrefix K mode jobs
        ((List.range jobs.length).map fun k => reconstruct fun i => (x i)[k]?) Z l).1) g) :
    ∀ d ≤ depth jobs, ∃ p Ts, LayerInv jobs x d p (layerPrefix K mode jobs
      ((List.range jobs.length).map fun k => reconstruct fun i => (x i)[k]?) Z d).1 Ts := by
  intro d
  induction d with
  | zero => exact fun _ => ⟨_, _, layerInv_zero jobs x hx⟩
  | succ d ih =>
    intro hd
    obtain ⟨p, Ts, hinv⟩ := ih (by omega)
    set W := (layerPrefix K mode jobs ((List.range jobs.length).map fun k => reconstruct fun i => (x i)[k]?) Z d).1
    set n := (gatesAt jobs d).length
    have hX : ∀ i T, i ∈ C.holders T → ∀ g, layerX K jobs d (p i).1 T g = layerX K jobs d W T g :=
      fun i T h g => by rw [layerX_congr K jobs d _ _ T (hinv.agree i T h)]
    have hY : ∀ i T, i ∈ C.holders T → ∀ g, layerY K jobs d (p i).1 T g = layerY K jobs d W T g :=
      fun i T h g => by rw [layerY_congr K jobs d _ _ T (hinv.agree i T h)]
    have hz : ∀ g, ∑ T, (fun T g => if g < n then Z d T g else 0) T g =
        ∑ i, mulRep K (localContext i) (layerX K jobs d (p i).1) (layerY K jobs d (p i).1) g := by
      intro g
      rw [mulRep_views_sum K _ _ (layerX K jobs d W) (layerY K jobs d W) g (fun i T h => hX i T h g)
        (fun i T h => hY i T h g)]
      by_cases hg : g < n
      · simp only [hg, ite_true]
        exact hprod d (by omega) g hg
      · have h0 : ∀ T, layerX K jobs d W T g = 0 := fun T => by
          simp [layerX, List.getElem?_eq_none (show (gatesAt jobs d).length ≤ g by omega)]
        simp [hg, shareValue, h0]
    have := layerInv_step K jobs x mode d p W Ts hinv _ hz
    rw [layerPrefix_succ, layerStep]
    dsimp only
    rw [appendLayer_congr jobs d W (Z d) _ fun T g hg => (show Z d T g = if g < n then
      (fun T g => if g < n then Z d T g else 0) T g else 0 by simp [n, hg])]
    exact ⟨_, _, this⟩

end Values

/-! ## The opening -/

section Opening

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

/-- The copy hashes that operator `j` sends in `OpenRep` of `v` with `H` fixed to `h`. -/
def copyHashes (h : Query C → HashOutput) (v : Shares C Bit) (count : ℕ) : List HashOutput :=
  C.terms.map fun T => h (.copy (vector count (v T)))

theorem copyHashes_idxOf (h : Query C → HashOutput) (v : Shares C Bit) (count : ℕ) (T : C.Term) :
    (copyHashes h v count)[C.terms.idxOf T]? = some (h (.copy (vector count (v T)))) := by
  rw [copyHashes, List.getElem?_map, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem (mem_terms T))]
  simp

/-- A copy of `OpenRep` at an honest operator that passes the hash check is the agreed sharing `w`.
The honest messages arrive as sent, and no received copy has the hash of a different honest copy of
the same term. It is `main_openCopy_sound` of `Proof/Main.lean` with `H` fixed to `h` in place of a
cache. -/
theorem repCopy_sound (D : C.Coalition) (h : Query C → HashOutput) (w : Shares C Bit)
    (vr : C.Party → Shares C Bit) (count : ℕ)
    (hvr : ∀ j T g, j ∉ D.1 → j ∈ C.holders T → g < count → vr j T g = w T g)
    (i : C.Party) (hiD : i ∉ D.1) (inbox : Mail C E)
    (hinbox : ∀ j, j ∉ D.1 → j ≠ i → inbox j = repOutbox K j (vr j) count (copyHashes h (vr j) count) i)
    (hcheck : repCheck K i inbox (copyHashes h (repCopy K i (vr i) count inbox) count))
    (hcopy : ∀ T j, j ∉ D.1 → j ∈ C.holders T →
      h (.copy (vector count (vr j T))) = h (.copy (vector count (repCopy K i (vr i) count inbox T))) →
      vector count (vr j T) = vector count (repCopy K i (vr i) count inbox T))
    (T : C.Term) (g : ℕ) (hg : g < count) :
    repCopy K i (vr i) count inbox T g = w T g := by
  by_cases hiT : i ∈ C.holders T
  · simpa only [repCopy, hiT, ↓reduceIte] using hvr i T g hiD hiT hg
  by_cases hown : K.owner T ∉ D.1
  · have hne : i ≠ K.owner T := fun e => hiT (e ▸ K.owner_held T)
    simp only [repCopy, hiT, hinbox _ hown (Ne.symm hne), repOutbox, hne, ↓reduceIte,
      Msg.part, List.getElem?_cons_zero, Msg.bitAt]
    rw [getD_flatMap_vector _ _ _ T (List.mem_filter.2 ⟨mem_terms T, by simp [hiT]⟩)
      (terms_nodup.filter _) g hg]
    exact hvr _ T g hown (K.owner_held T) hg
  · obtain ⟨j, hjT, hjD⟩ := exists_honest_holder D T
    have hne : j ≠ K.owner T := fun e => hown (e ▸ hjD)
    have hc := hcheck T hiT j hjT hne
    dsimp only at hc
    rw [hinbox j hjD (fun e => hiT (e ▸ hjT)), main_open_hash_sent K i j (vr j) count _ (by simp [copyHashes]) T hiT hjT hne,
      lookup_zip_idxOf C.terms _ (by simp [copyHashes]) T (mem_terms T), copyHashes_idxOf,
      copyHashes_idxOf] at hc
    have heq := hcopy T j hjD hjT (Option.some.inj hc)
    have heqg := congrArg (fun l : List Bit => l.getD g 0) heq
    have hvec : ∀ f : ℕ → Bit, (vector count f).getD g 0 = f g := by
      intro f
      simp [vector, List.getD_eq_getElem?_getD, List.getElem?_range hg]
    rw [hvec, hvec] at heqg
    exact heqg.symm.trans (hvr j T g hjD hjT hg)

end Opening

/-! ## The opened outputs of a batch -/

section Output

variable {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) (K : Constants C E) (mode : ReshareMode)
  (circuits : Circuits)

theorem batchInputs_congr (h : Query C → HashOutput) (seed seeds : C.Term → HashOutput) (jobs : List Job)
    (j : C.Party) (hseed : ∀ T, j ∈ C.holders T → seed T = seeds T) :
    batchInputs h seed jobs j = batchInputs h seeds jobs j := by
  unfold batchInputs
  refine List.map_congr_left fun job _ => funext fun T => ?_
  split_ifs with hj
  · simp [inputBits, hseed T hj]
  · rfl

/-- Hop H11 on the values. Take the tuples `x` of the honest operators, each from the inputs of its
keys, its products `zs j` and its sharing `v' j` after `Rerand`, the inbox of `OpenRep` at the honest
operator `i` and the hash check that `i` passes. Assume right tuples, agreeing parameters and seeds,
copies of `v'` that agree among the honest holders, the honest messages of `OpenRep` as sent, and no
copy collision. Then the opened outputs of `i` are the circuit values on the PRF values of `seeds`. -/
theorem opened_right (parameter : PublicParameter) (jobs : List Job) (D : C.Coalition) (i : C.Party)
    (hiD : i ∉ D.1) (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (keys : C.Party → Keys C)
    (zs : C.Party → ℕ → Shares C Bit) (v' : C.Party → Shares C Bit) (x : C.Party → List (Tuple C))
    (inbox : Mail C E)
    (hshape : ∀ j, j ∉ D.1 → x j = batchTuples K mode (jobs.map (circuits (keys j).parameter ·.kind))
      (batchInputs h (keys j).seed jobs j) (zs j) (v' j))
    (hparameter : ∀ j, j ∉ D.1 → (keys j).parameter = parameter)
    (hseed : ∀ j T, j ∉ D.1 → j ∈ C.holders T → (keys j).seed T = seeds T)
    (hright : RightTuples D x)
    (hagree : ∀ T j j', j ∉ D.1 → j' ∉ D.1 → j ∈ C.holders T → j' ∈ C.holders T →
      ∀ g < (outputsOf (jobs.map (circuits parameter ·.kind))).length, v' j T g = v' j' T g)
    (hinbox : ∀ j, j ∉ D.1 → j ≠ i → inbox j = repOutbox K j (v' j) (outputsOf (jobs.map (circuits parameter ·.kind))).length
      (copyHashes h (v' j) (outputsOf (jobs.map (circuits parameter ·.kind))).length) i)
    (hcheck : repCheck K i inbox (copyHashes h (repCopy K i (v' i) (outputsOf (jobs.map (circuits parameter ·.kind))).length
      inbox) (outputsOf (jobs.map (circuits parameter ·.kind))).length))
    (hcopy : ∀ T j, j ∉ D.1 → j ∈ C.holders T →
      h (.copy (vector (outputsOf (jobs.map (circuits parameter ·.kind))).length (v' j T))) =
        h (.copy (vector (outputsOf (jobs.map (circuits parameter ·.kind))).length
          (repCopy K i (v' i) (outputsOf (jobs.map (circuits parameter ·.kind))).length inbox T))) →
      vector (outputsOf (jobs.map (circuits parameter ·.kind))).length (v' j T) =
        vector (outputsOf (jobs.map (circuits parameter ·.kind))).length
          (repCopy K i (v' i) (outputsOf (jobs.map (circuits parameter ·.kind))).length inbox T)) :
    ThresholdLeanXmssSecurity.assemble (jobs.map (circuits parameter ·.kind))
        (fun g => ∑ T, repCopy K i (v' i) (outputsOf (jobs.map (circuits parameter ·.kind))).length inbox T g) =
      jobs.map fun job => ThresholdLeanXmssSecurity.D prims h (evalJob circuits parameter seeds job) := by
  set circs := jobs.map (circuits parameter ·.kind) with hcircs
  set n := (outputsOf circs).length with hn
  set x0 := batchInputs h seeds jobs with hx0
  set W0 := (List.range circs.length).map fun k => reconstruct fun j => (x0 j)[k]? with hW0def
  set Z := gluedProducts D zs
  set V := gluedShares D v'
  have hshape' : ∀ j, j ∉ D.1 → x j = batchTuples K mode circs (x0 j) (zs j) (v' j) := fun j hj => by
    rw [hshape j hj, hparameter j hj, batchInputs_congr h _ seeds jobs j (hseed j · hj)]
  have hlen0 : ∀ j, (x0 j).length = jobs.length := fun j => by simp [hx0, batchInputs]
  have hW0 : ∀ k (hk : k < jobs.length) T, (W0.getD k fun _ => []) T = inputBits h seeds jobs[k] T := by
    intro k hk T
    rw [hW0def, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by simpa [circs] using hk)]
    simp only [Option.map_some, Option.getD_some]
    refine reconstruct_of_agree _ T _ fun j hj =>
      ⟨fun T => if j ∈ C.holders T then inputBits h seeds jobs[k] T else [], ?_, by simp [hj]⟩
    simp [hx0, batchInputs, List.getElem?_eq_getElem hk]
  have hI : ∀ T, W0.length = (x0 (refHolder D T)).length ∧
      ∀ k, (W0.getD k fun _ => []) T = ((x0 (refHolder D T)).getD k fun _ => []) T := by
    intro T
    refine ⟨by simp [hW0def, circs, hlen0], fun k => ?_⟩
    rcases Nat.lt_or_ge k jobs.length with hk | hk
    · rw [hW0 k hk T, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen0]; exact hk)]
      simp [hx0, batchInputs, (refHolder_spec D T).1]
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [W0, circs]; omega),
        List.getElem?_eq_none (by rw [hlen0]; exact hk)]
  -- The glued tuples are products.
  have hprod : ∀ (m : ℕ) (τ : Tuple C), (batchTuples K mode circs W0 Z V)[m]? = some τ → ∀ g < τ.count,
      shareValue τ.z g = shareValue τ.x g * shareValue τ.y g := by
    intro m τ hτ g hg
    obtain ⟨hxe, hye, hze, hce⟩ := tupleAt_glued K mode circs D x0 zs v' x hshape' W0 hI m τ hτ
    by_contra hne
    refine hright ⟨m, ?_, g, by rw [hce]; exact hg, ?_⟩
    · obtain ⟨j, hj, hfirst⟩ := firstInput_honest D x
      rw [hfirst, hshape' j hj, length_batchTuples]
      have := (List.getElem?_eq_some_iff.1 hτ).1
      rwa [length_batchTuples] at this
    · rw [hxe, hye, hze]
      exact sub_ne_zero.2 hne
  obtain ⟨p, Ts, hinv⟩ := layerInv_layerPrefix K mode circs x0 (batchInputs_main h seeds circuits parameter jobs) Z
    (fun l hl g hg => hprod l _ (batchTuples_layer K mode circs W0 Z V l hl) g hg) (depth circs) le_rfl
  rw [← mainOutputs_batch prims h seeds circuits parameter jobs]
  refine assemble_eq K circs x0 p _ Ts hinv _ fun g hg => ?_
  have hopen : ∀ T, repCopy K i (v' i) n inbox T g = V T g := fun T =>
    repCopy_sound K D h V v' n (fun j T g hj hjT hg => hagree T j (refHolder D T) hj (refHolder_spec D T).2 hjT
      (refHolder_spec D T).1 g hg) i hiD inbox hinbox hcheck hcopy T g hg
  have hout := hprod (depth circs) _ (batchTuples_output K mode circs W0 Z V) g hg
  simp only [shareValue_one, mul_one] at hout
  simp only [hopen]
  exact hout

end Output

/-! ## The outcomes of a program with `H` fixed -/

section Holds

variable {E : Type} (h : Query C → HashOutput)

/-- Each outcome `some a` of `x` with `H` fixed to `h` has `P a`. The rounds, `PRG` and the sampling
stay free. -/
def Holds {α : Type} (P : α → Prop) (x : PartyM C E RealSpec α) : Prop :=
  ∀ z ∈ support (simulateQ (fixHash h) x.run), ∀ a, z = some a → P a

theorem holds_true {α : Type} (x : PartyM C E RealSpec α) : Holds h (fun _ => True) x :=
  fun _ _ _ _ => trivial

theorem holds_pure {α : Type} (P : α → Prop) (a : α) (ha : P a) : Holds h P (pure a : PartyM C E RealSpec α) := by
  intro z hz b hb
  simp at hz
  subst hz
  cases hb
  exact ha

theorem holds_bind {α β : Type} (Q : α → Prop) (P : β → Prop) (x : PartyM C E RealSpec α)
    (f : α → PartyM C E RealSpec β) (hx : Holds h Q x) (hf : ∀ a, Q a → Holds h P (f a)) :
    Holds h P (x >>= f) := by
  intro z hz b hb
  subst hb
  rw [OptionT.run_bind, Option.elimM, simulateQ_bind, mem_support_bind_iff] at hz
  obtain ⟨o, ho, hz⟩ := hz
  rcases o with _ | a
  · simp at hz
  · exact hf a (hx _ ho a rfl) _ hz b rfl

theorem holds_require (c : Prop) : Holds h (fun _ => c) (require c : PartyM C E RealSpec Unit) := by
  intro z hz a ha
  unfold require at hz
  split_ifs at hz with hc
  · exact hc
  · simp [OptionT.run_failure] at hz
    subst hz
    cases ha

end Holds

section Pins

variable {E : Type} [Field E] [Algebra Bit E] (h : Query C → HashOutput) (prims : Primitives)

/-- A step of `H` calls has the value with `H` fixed to `h`. -/
def Pins {β : Type} (oa : OracleComp (RoSpec C) β) : Prop :=
  Holds (E := E) h (· = ThresholdLeanXmssSecurity.D prims h oa) (oracleStep oa)

theorem pins_pure {β : Type} (b : β) : Pins (E := E) h prims (pure b : OracleComp (RoSpec C) β) := by
  unfold Pins
  rw [oracleStep_pure]
  exact holds_pure h _ b rfl

theorem pins_bind {β γ : Type} (oa : OracleComp (RoSpec C) β) (f : β → OracleComp (RoSpec C) γ)
    (ha : Pins (E := E) h prims oa) (hf : ∀ b, Pins (E := E) h prims (f b)) : Pins (E := E) h prims (oa >>= f) := by
  unfold Pins at *
  rw [oracleStep_bind]
  refine holds_bind h _ _ _ _ ha fun b hb => ?_
  subst hb
  rw [D_bind]
  exact hf _

omit [Field E] [Algebra Bit E] in
theorem fixHash_oracleStep_hashQuery (q : Query C) :
    simulateQ (fixHash (E := E) (G := RealSpec) h) (oracleStep (hashQuery q) : PartyM C E RealSpec HashOutput).run =
      pure (some (h q)) := by
  rw [show hashQuery q = (query (spec := RoSpec C) (.inl q) >>= pure : OracleComp (RoSpec C) HashOutput) by
    simp [hashQuery]]
  simp only [oracleStep, localStep]
  simp [OptionT.run_lift]
  rfl

omit [Field E] [Algebra Bit E] in
theorem pins_hashQuery (q : Query C) : Pins (E := E) h prims (hashQuery q) := by
  intro z hz a ha
  subst ha
  rw [D_hashQuery, fixHash_oracleStep_hashQuery] at *
  simp at hz
  exact hz

theorem pins_mapM {α β : Type} (f : α → OracleComp (RoSpec C) β) (hf : ∀ a, Pins (E := E) h prims (f a)) :
    ∀ l : List α, Pins (E := E) h prims (l.mapM f)
  | [] => pins_pure h prims _
  | a :: l => by
    rw [List.mapM_cons]
    exact pins_bind h prims _ _ (hf a) fun _ => pins_bind h prims _ _ (pins_mapM f hf l) fun _ => pins_pure h prims _

end Pins

/-! ## The path of one batch -/

section Path

variable {E : Type} [Field E] [Algebra Bit E] (h : Query C → HashOutput) (prims : Primitives) (K : Constants C E)
  (mode : ReshareMode) (jobs : List Circuit)

/-- `Holds` on each start state of a program on the state of a run. -/
def HoldsR {α : Type} (P : α → Prop) (x : RunM C E RealSpec α) : Prop :=
  ∀ s, Holds h (fun r => P r.1) (x.run s)

omit [Field E] [Algebra Bit E] in
theorem holdsR_bind {α β : Type} (Q : α → Prop) (P : β → Prop) (x : RunM C E RealSpec α)
    (f : α → RunM C E RealSpec β) (hx : HoldsR h Q x) (hf : ∀ a, Q a → HoldsR h P (f a)) :
    HoldsR h P (x >>= f) := fun s => by
  rw [StateT.run_bind]
  exact holds_bind h _ _ _ _ (hx s) fun p hp => hf p.1 hp p.2

omit [Field E] [Algebra Bit E] in
theorem holdsR_pure {α : Type} (P : α → Prop) (a : α) (ha : P a) : HoldsR h P (pure a : RunM C E RealSpec α) :=
  fun s => by rw [StateT.run_pure]; exact holds_pure h _ _ ha

omit [Field E] [Algebra Bit E] in
theorem holdsR_true {α : Type} (x : RunM C E RealSpec α) : HoldsR h (fun _ => True) x :=
  fun _ => holds_true h _

omit [Field E] [Algebra Bit E] in
theorem holdsR_lift {α : Type} (P : α → Prop) (y : PartyM C E RealSpec α) (hy : Holds h P y) :
    HoldsR h P (StateT.lift y : RunM C E RealSpec α) := fun s => by
  rw [StateT.run_lift]
  exact holds_bind h _ _ _ _ hy fun a ha => holds_pure h _ _ ha

include prims in
/-- Each outcome of `OpenRep` at operator `ctx.self` with `H` fixed to `h` is the sum of the copies of
an inbox that passes the hash check. -/
theorem holds_openRep (ctx : Context C) (v : Shares C Bit) (count : ℕ) :
    Holds h (fun opened => ∃ inbox : Mail C E, repCheck K ctx.self inbox (copyHashes h (repCopy K ctx.self v count inbox) count) ∧
      opened = fun g => ∑ T, repCopy K ctx.self v count inbox T g) (openRep K ctx v count) := by
  rw [show openRep K ctx v count = openRep (G := RealSpec) K (localContext ctx.self) v count from rfl, openRep_eq]
  refine holds_bind h (fun _ => True) _ _ _ (holds_true h _) fun _ _ => ?_
  refine holds_bind h (fun _ => True) _ _ _ (holds_true h _) fun inbox _ => ?_
  refine holds_bind h _ _ _ _ (pins_mapM h prims _ (fun T => pins_hashQuery h prims _) _) fun cds hcds => ?_
  refine holds_bind h _ _ _ _ (holds_require h _) fun _ hcheck => holds_pure h _ _ ⟨inbox, ?_, rfl⟩
  rw [hcds, D_mapM] at hcheck
  simpa [D_hashQuery, copyHashes] using hcheck

include prims in
/-- Each outcome of the tail of a real run is an opening that passes the hash check. -/
theorem holdsR_tail (ctx : Context C) (p : List (C.Term → List Bit) × List (Tuple C)) :
    HoldsR h (fun outs => ∃ (v' : Shares C Bit) (inbox : Mail C E),
      repCheck K ctx.self inbox (copyHashes h (repCopy K ctx.self v' (outputsOf jobs).length inbox) (outputsOf jobs).length) ∧
      outs = ThresholdLeanXmssSecurity.assemble jobs fun g => ∑ T, repCopy K ctx.self v' (outputsOf jobs).length inbox T g)
      (tailBody K (realRunBuildingBlocks K ctx mode) jobs p) := by
  rw [tailBody_apply]
  refine holdsR_bind h (fun _ => True) _ _ _ (holdsR_true h _) fun v' _ => ?_
  refine holdsR_bind h (fun _ => True) _ _ _ (holdsR_true h _) fun _ _ => ?_
  refine holdsR_bind h _ _ _ _ (holdsR_lift h _ _ (holds_openRep h prims K ctx v' _)) fun opened ⟨inbox, hc, ho⟩ => ?_
  exact holdsR_pure h _ _ ⟨v', inbox, hc, by rw [ho]⟩

include prims in
/-- Each outcome of one real batch at operator `ctx.self` with `H` fixed to `h` is the opening of a
sharing `v'` with an inbox that passes the hash check. -/
theorem holds_realBatch [Fintype E] [DecidableEq E] (circuits : Circuits) (ctx : Context C) (parameter : PublicParameter) (jobs : List Job)
    (st : ℕ × ℕ) :
    Holds h (fun r => ∃ (v' : Shares C Bit) (inbox : Mail C E),
      repCheck K ctx.self inbox (copyHashes h (repCopy K ctx.self v'
        (outputsOf (jobs.map (circuits parameter ·.kind))).length inbox)
        (outputsOf (jobs.map (circuits parameter ·.kind))).length) ∧
      r.1 = some (ThresholdLeanXmssSecurity.assemble (jobs.map (circuits parameter ·.kind)) fun g =>
        ∑ T, repCopy K ctx.self v' (outputsOf (jobs.map (circuits parameter ·.kind))).length inbox T g))
      ((realBatch K circuits mode ctx parameter jobs).run st) := by
  rw [realBatch_run]
  refine holds_bind h (fun _ => True) _ _ _ (holds_true h _) fun inputs _ => ?_
  rw [runJobs_eq, StateT.run_bind, bind_assoc]
  refine holds_bind h (fun _ => True) _ _ _ (holds_true h _) fun p _ => ?_
  refine holds_bind h _ _ _ _ (holdsR_tail h prims K mode _ ctx p.1 p.2) fun r ⟨v', inbox, hc, hr⟩ => ?_
  exact holds_pure h _ _ ⟨v', inbox, hc, by rw [hr]⟩

end Path

/-! ## Hop H11 on the program of one batch -/

section Hop

variable {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) (K : Constants C E) (mode : ReshareMode)
  (circuits : Circuits)

/-- Hop H11 on the program of one batch of the honest operator `ctx.self`, with `H` fixed to `h`.
Each outcome of the batch is the opening of a sharing `v'` with an inbox of `OpenRep` that passes
the hash check. Take the tuples `x`
of the honest operators, each from the inputs of its keys, its products and its sharing after
`Rerand`, with the sharing `v'` at `ctx.self`. If the tuples are right, the honest parameters and
seeds agree, the honest copies of the opened sharing agree, the honest messages of `OpenRep` arrive
as sent, and no received copy has the hash of a different honest copy, then the batch output is a
`RightBatch`. -/
theorem realBatch_rightBatch [Fintype E] [DecidableEq E] (h : Query C → HashOutput) (ctx : Context C) (parameter : PublicParameter)
    (jobs : List Job) (st : ℕ × ℕ)
    (z : Option (Option (List (List Bit)) × (ℕ × ℕ)))
    (hz : z ∈ support (simulateQ (fixHash h) ((realBatch K circuits mode ctx parameter jobs).run st).run))
    (o : Option (List (List Bit))) (st' : ℕ × ℕ) (hzo : z = some (o, st')) :
    ∃ (v'self : Shares C Bit) (inbox : Mail C E),
      repCheck K ctx.self inbox (copyHashes h (repCopy K ctx.self v'self
        (outputsOf (jobs.map (circuits parameter ·.kind))).length inbox)
        (outputsOf (jobs.map (circuits parameter ·.kind))).length) ∧
      o = some (ThresholdLeanXmssSecurity.assemble (jobs.map (circuits parameter ·.kind)) fun g =>
        ∑ T, repCopy K ctx.self v'self (outputsOf (jobs.map (circuits parameter ·.kind))).length inbox T g) ∧
      ∀ (D : C.Coalition) (seeds : C.Term → HashOutput)
      (keys : C.Party → Keys C) (zs : C.Party → ℕ → Shares C Bit) (v' : C.Party → Shares C Bit)
      (x : C.Party → List (Tuple C)),
      ctx.self ∉ D.1 → v' ctx.self = v'self →
      (∀ j, j ∉ D.1 → x j = batchTuples K mode (jobs.map (circuits (keys j).parameter ·.kind))
        (batchInputs h (keys j).seed jobs j) (zs j) (v' j)) →
      (∀ j, j ∉ D.1 → (keys j).parameter = parameter) →
      (∀ j T, j ∉ D.1 → j ∈ C.holders T → (keys j).seed T = seeds T) →
      RightTuples D x →
      (∀ T j j', j ∉ D.1 → j' ∉ D.1 → j ∈ C.holders T → j' ∈ C.holders T →
        ∀ g < (outputsOf (jobs.map (circuits parameter ·.kind))).length, v' j T g = v' j' T g) →
      (∀ j, j ∉ D.1 → j ≠ ctx.self → inbox j = repOutbox K j (v' j) (outputsOf (jobs.map (circuits parameter ·.kind))).length
        (copyHashes h (v' j) (outputsOf (jobs.map (circuits parameter ·.kind))).length) ctx.self) →
      (∀ T j, j ∉ D.1 → j ∈ C.holders T →
        h (.copy (vector (outputsOf (jobs.map (circuits parameter ·.kind))).length (v' j T))) =
          h (.copy (vector (outputsOf (jobs.map (circuits parameter ·.kind))).length
            (repCopy K ctx.self (v' ctx.self) (outputsOf (jobs.map (circuits parameter ·.kind))).length inbox T))) →
        vector (outputsOf (jobs.map (circuits parameter ·.kind))).length (v' j T) =
          vector (outputsOf (jobs.map (circuits parameter ·.kind))).length
            (repCopy K ctx.self (v' ctx.self) (outputsOf (jobs.map (circuits parameter ·.kind))).length inbox T)) →
      RightBatch prims circuits h parameter seeds jobs o := by
  obtain ⟨v'self, inbox, hcheck, ho⟩ := holds_realBatch h prims K mode circuits ctx parameter jobs st z hz _ hzo
  refine ⟨v'self, inbox, hcheck, ho, fun D seeds keys zs v' x hiD hv' hshape hparameter hseed hright hagree hinbox hcopy => ?_⟩
  subst hv'
  rw [RightBatch, show o = _ from ho, opened_right prims K mode circuits parameter jobs D ctx.self hiD h seeds keys zs v' x inbox
    hshape hparameter hseed hright hagree hinbox hcheck hcopy]

end Hop

end ThresholdLeanXmss.Sketch

/-- info: 'ThresholdLeanXmss.Sketch.realBatch_rightBatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmss.Sketch.realBatch_rightBatch

/-- info: 'ThresholdLeanXmss.Sketch.opened_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmss.Sketch.opened_right
