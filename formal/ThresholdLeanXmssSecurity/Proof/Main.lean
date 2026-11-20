import ThresholdLeanXmssSecurity.Base.DkgClaims
import ThresholdLeanXmssSecurity.Proof.Execution
import ThresholdLeanXmssSecurity.Proof.Lemmas
import VCVio.OracleComp.QueryTracking.Birthday

/-!
# A batch

The outputs of a batch, the program of one operator, the steps of `OpenRep` and the values of the
layers of an honest batch.
-/

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- The outputs of `F_main` on the inputs of a run with no coalition. -/
def mainOutputs (jobs : List Circuit) (x : C.Party → List (C.Term → List Bit)) : List (List Bit) :=
  jobs.zipIdx.map fun p => p.1.eval (inputValue (reconstruct fun i => (x i)[p.2]?))

omit [Fintype E] [DecidableEq E] in
/-- The `MulRep` shares of views that agree with one sharing on the held terms sum to the product of
the shared values (CDI05, Section 4). -/
theorem mulRep_views_sum {R : Type} [CommRing R] (K : Constants C E) (xv yv : C.Party → Shares C R)
    (x y : Shares C R) (g : ℕ) (hx : ∀ i T, i ∈ C.holders T → xv i T g = x T g)
    (hy : ∀ i T, i ∈ C.holders T → yv i T g = y T g) :
    ∑ i, mulRep K (localContext i) (xv i) (yv i) g = shareValue x g * shareValue y g := by
  have h : ∀ i, mulRep K (localContext i) (xv i) (yv i) g = ∑ AB ∈ K.pairs i, x AB.1 g * y AB.2 g := by
    intro i
    refine Finset.sum_congr rfl fun AB hAB => ?_
    obtain ⟨h1, h2⟩ := K.pairs_held i AB hAB
    rw [hx i AB.1 h1, hy i AB.2 h2]
  simp_rw [h]
  rw [sum_sum_pairs K (fun AB => x AB.1 g * y AB.2 g), shareValue, shareValue, Finset.sum_mul_sum,
    ← Finset.sum_product', Finset.univ_product_univ]

/-- The empty coalition lacks a term, so `F_mult` puts the product in it. -/
theorem lackedTerm_empty_isSome : (lackedTerm (∅ : Finset C.Party)).isSome := by
  classical
  obtain ⟨T⟩ : Nonempty C.Term := by
    obtain ⟨T, -, hT⟩ := Finset.exists_superset_card_eq (s := (∅ : Finset C.Party))
      (n := C.t - 1) (by simp) (by simp [Committee.n]; omega)
    exact ⟨⟨T, hT⟩⟩
  rw [lackedTerm, List.find?_isSome]
  exact ⟨T, Finset.mem_toList.2 (Finset.mem_univ T), by simp [KnownTo]⟩

/-- The sum of the shares of an affine function is its value on the shared wires, since only
`publicTerm` adds the constant. -/
theorem sum_affine_share (a : Affine) (w : C.Term → List Bit) (publicTerm : C.Term) (plain : List Bit)
    (hplain : ∀ k, plain.getD k 0 = ∑ T, (w T).getD k 0) :
    ∑ T, a.share w publicTerm T = a.eval plain := by
  simp only [Affine.share, Affine.eval, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, hplain]
  congr 1
  induction a.wires with
  | nil => simp
  | cons k ks ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- A copy at its place in the bundle of an owner (MPClan, App. B). -/
theorem getD_flatMap_vector (owned : List C.Term) (v : Shares C Bit) (count : ℕ) (T : C.Term)
    (hT : T ∈ owned) (hnodup : owned.Nodup) (g : ℕ) (hg : g < count) :
    (owned.flatMap fun T' => vector count (v T')).getD (count * owned.idxOf T + g) 0 = v T g := by
  induction owned with
  | nil => simp at hT
  | cons T' rest ih =>
    rw [List.flatMap_cons]
    by_cases h : T' = T
    · subst h
      simp [vector, List.getD_eq_getElem?_getD, List.getElem?_append_left, hg]
    · have hT : T ∈ rest := (List.mem_cons.1 hT).resolve_left (Ne.symm h)
      rw [List.idxOf_cons_ne _ h, List.getD_eq_getElem?_getD, List.getElem?_append_right
        (by simp [vector]; nlinarith), ← List.getD_eq_getElem?_getD]
      have := ih hT (List.nodup_cons.1 hnodup).2
      simp only [vector, List.length_map, List.length_range, Nat.mul_succ] at this ⊢
      rw [show count * List.idxOf T rest + count + g - count = count * List.idxOf T rest + g by omega]
      exact this

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

/-! ## The program of one operator -/

section Program

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}

def gatesAt (jobs : List Circuit) (layer : ℕ) : List (ℕ × Affine × Affine) :=
  jobs.zipIdx.flatMap fun (job, k) => (job.layers.getD layer []).map fun ab => (k, ab)

def layerX (K : Constants C E) (jobs : List Circuit) (layer : ℕ) (wires : List (C.Term → List Bit)) : Shares C Bit :=
  fun T g => match (gatesAt jobs layer)[g]? with
    | some (k, ab) => ab.1.share (wires.getD k fun _ => []) K.publicTerm T | none => 0

def layerY (K : Constants C E) (jobs : List Circuit) (layer : ℕ) (wires : List (C.Term → List Bit)) : Shares C Bit :=
  fun T g => match (gatesAt jobs layer)[g]? with
    | some (k, ab) => ab.2.share (wires.getD k fun _ => []) K.publicTerm T | none => 0

def appendLayer (jobs : List Circuit) (layer : ℕ) (wires : List (C.Term → List Bit)) (z : Shares C Bit) :
    List (C.Term → List Bit) :=
  wires.zipIdx.map fun (w, k) T => w T ++ (((gatesAt jobs layer).zipIdx.filter (·.1.1 = k)).map fun (_, g) => z T g)

def layerBody (K : Constants C E) (buildingBlocks : RunBuildingBlocks C E G) (jobs : List Circuit) :
    List (C.Term → List Bit) × List (Tuple C) → ℕ → RunM C E G (List (C.Term → List Bit) × List (Tuple C)) :=
  fun p layer => do
    let z ← buildingBlocks.mult (layerX K jobs layer p.1) (layerY K jobs layer p.1)
        (gatesAt jobs layer).length
    pure (appendLayer jobs layer p.1 z,
      p.2 ++ [⟨layerX K jobs layer p.1, layerY K jobs layer p.1, z, (gatesAt jobs layer).length, buildingBlocks.mode⟩])

def outputsOf (jobs : List Circuit) : List (ℕ × Affine) := jobs.zipIdx.flatMap fun (job, k) => job.outputs.map fun a => (k, a)

def outputShares (K : Constants C E) (jobs : List Circuit) (wires : List (C.Term → List Bit)) : Shares C Bit :=
  fun T g => match (outputsOf jobs)[g]? with
    | some (k, a) => a.share (wires.getD k fun _ => []) K.publicTerm T | none => 0

def assemble (jobs : List Circuit) (opened : ℕ → Bit) : List (List Bit) :=
  (jobs.map (·.outputs.length)).zipIdx.map fun (width, k) =>
    vector width fun g => opened (((jobs.map (·.outputs.length)).take k).sum + g)

def tailBody (K : Constants C E) (buildingBlocks : RunBuildingBlocks C E G) (jobs : List Circuit) :
    List (C.Term → List Bit) × List (Tuple C) → RunM C E G (List (List Bit)) := fun p => do
  let v' ← buildingBlocks.rerand (outputShares K jobs p.1) (outputsOf jobs).length
  buildingBlocks.verify (p.2 ++ [⟨outputShares K jobs p.1, one K, v', (outputsOf jobs).length, .peer⟩])
  let opened ← buildingBlocks.output v' (outputsOf jobs).length
  pure (assemble jobs opened)

theorem runJobs_eq (K : Constants C E) (buildingBlocks : RunBuildingBlocks C E G) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    runJobs K buildingBlocks jobs inputs =
      (List.range (depth jobs)).foldlM (layerBody K buildingBlocks jobs) (inputs, []) >>= tailBody K buildingBlocks jobs := by
  rfl

end Program

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

section FunctionalitiesHonest

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- `reconstruct` returns a value on which every holder agrees. -/
theorem reconstruct_of_agree {α : Type} [Inhabited α] (views : C.Party → Option (C.Term → α)) (T : C.Term) (V : α)
    (h : ∀ i, i ∈ C.holders T → ∃ f, views i = some f ∧ f T = V) : reconstruct views T = V := by
  obtain ⟨i₀, hi₀⟩ := exists_holder T
  unfold reconstruct
  rcases hl : (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) with _ | ⟨f, rest⟩
  · exfalso
    obtain ⟨f, hf, -⟩ := h i₀ hi₀
    have : f ∈ (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) :=
      List.mem_filterMap.2 ⟨i₀, List.mem_finRange i₀, by simp [hi₀, hf]⟩
    rw [hl] at this
    simp at this
  · have hmem : f ∈ (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) := by
      rw [hl]; exact List.mem_cons_self
    obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hmem
    split_ifs at hi with hiT
    obtain ⟨f', hf', hV⟩ := h i hiT
    rw [hf'] at hi
    cases hi
    simp [hV]

/-- Tuple `τ` agrees with `τ'` on the terms that operator `i` holds. -/
def TupleAgrees (i : C.Party) (τ τ' : Tuple C) : Prop :=
  (∀ T, i ∈ C.holders T → τ.x T = τ'.x T ∧ τ.y T = τ'.y T ∧ τ.z T = τ'.z T) ∧ τ.count = τ'.count ∧ τ.mode = τ'.mode

/-- A tuple whose shared values multiply. -/
def IsProduct (τ : Tuple C) : Prop := ∀ g < τ.count, shareValue τ.z g = shareValue τ.x g * shareValue τ.y g

end FunctionalitiesHonest

section Lists

variable {β : Type}

/-- The entries of some lists, each with the index of its list from `s`. -/
def flatIdx (L : List (List β)) (s : ℕ) : List (ℕ × β) := (L.zipIdx s).flatMap fun p => p.1.map fun b => (p.2, b)

theorem flatIdx_cons (xs : List β) (L : List (List β)) (s : ℕ) :
    flatIdx (xs :: L) s = xs.map (fun b => (s, b)) ++ flatIdx L (s + 1) := by
  simp [flatIdx]

theorem length_flatIdx (L : List (List β)) (s : ℕ) : (flatIdx L s).length = (L.map List.length).sum := by
  induction L generalizing s with
  | nil => simp [flatIdx]
  | cons xs L ih => simp [flatIdx_cons, ih]

theorem getElem?_flatIdx (L : List (List β)) (s k j : ℕ) (hk : k < L.length) (hj : j < (L[k]).length) :
    (flatIdx L s)[((L.take k).map List.length).sum + j]? = some (s + k, L[k][j]) := by
  induction L generalizing s k with
  | nil => simp at hk
  | cons xs L ih =>
    rw [flatIdx_cons]
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at hj
      rw [List.getElem?_append_left (by simpa using hj)]
      simp [hj]
    | succ k =>
      have hk' : k < L.length := by simpa using hk
      rw [List.getElem?_append_right (by simp; omega)]
      have := ih (s + 1) k hk' (by simpa using hj)
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.length_map] at this ⊢
      rw [show xs.length + (List.map List.length (List.take k L)).sum + j - xs.length =
        (List.map List.length (List.take k L)).sum + j by omega, this]
      simp [Nat.add_assoc, Nat.add_comm 1 k]

theorem filter_zipIdx_flatIdx (L : List (List β)) (s t k : ℕ) :
    ((flatIdx L s).zipIdx t).filter (fun p => decide (p.1.1 = k)) =
      if s ≤ k then ((L.getD (k - s) []).zipIdx).map
        (fun p => ((k, p.1), t + ((L.take (k - s)).map List.length).sum + p.2)) else [] := by
  induction L generalizing s t with
  | nil => simp [flatIdx]
  | cons xs L ih =>
    rw [flatIdx_cons, List.zipIdx_append, List.filter_append, ih, List.zipIdx_map]
    by_cases hsk : s = k
    · subst hsk
      have h1 : List.filter (fun p => decide (p.1.1 = s)) (List.map (Prod.map (fun b => (s, b)) id) (xs.zipIdx t)) =
          List.map (Prod.map (fun b => (s, b)) id) (xs.zipIdx t) := List.filter_eq_self.2 (by simp; intros; simp_all)
      rw [h1, if_neg (by omega), if_pos le_rfl, List.zipIdx_eq_map_add]
      simp [Function.comp_def]
    · have h1 : List.filter (fun p => decide (p.1.1 = k)) (List.map (Prod.map (fun b => (s, b)) id) (xs.zipIdx t)) =
          [] := List.filter_eq_nil_iff.2 (by simp; omega)
      rw [h1, List.nil_append]
      by_cases hle : s ≤ k
      · rw [if_pos (by omega), if_pos hle]
        obtain ⟨d, hd⟩ : ∃ d, k - s = d + 1 := ⟨k - s - 1, by omega⟩
        rw [hd, show k - (s + 1) = d by omega]
        simp [Nat.add_assoc]
      · rw [if_neg (by omega), if_neg hle]

theorem filterMap_zip_idxOf {α : Type} [BEq α] [LawfulBEq α] (L : List α) (hL : L.Nodup) (P : α → Prop) [DecidablePred P]
    (ds : List β) (hds : ds.length = L.length) (T : α) (hT : T ∈ L) (hP : P T) :
    ((L.zip ds).filterMap fun p => if P p.1 then some p.2 else none)[(L.filter P).idxOf T]? = ds[L.idxOf T]? := by
  induction L generalizing ds with
  | nil => simp at hT
  | cons a L ih =>
    obtain _ | ⟨d, ds⟩ := ds
    · simp at hds
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hds
    rw [List.zip_cons_cons, List.filterMap_cons]
    rcases Classical.em (a = T) with ha | ha
    · subst ha
      simp [hP]
    · have hT' : T ∈ L := (List.mem_cons.1 hT).resolve_left (Ne.symm ha)
      have := ih (List.nodup_cons.1 hL).2 ds hds hT'
      rw [List.idxOf_cons_ne _ ha]
      by_cases hPa : P a
      · rw [List.filter_cons_of_pos (by simpa using hPa), List.idxOf_cons_ne _ ha]
        simpa [hPa] using this
      · rw [List.filter_cons_of_neg (by simpa using hPa)]
        simpa [hPa] using this

theorem lookup_zip_idxOf {α : Type} [BEq α] [LawfulBEq α] (L : List α) (ds : List β) (hds : ds.length = L.length)
    (T : α) (hT : T ∈ L) : (L.zip ds).lookup T = ds[L.idxOf T]? := by
  induction L generalizing ds with
  | nil => simp at hT
  | cons a L ih =>
    obtain _ | ⟨d, ds⟩ := ds
    · simp at hds
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hds
    rw [List.zip_cons_cons, List.lookup_cons]
    rcases Classical.em (a = T) with ha | ha
    · subst ha
      simp
    · have hT' : T ∈ L := (List.mem_cons.1 hT).resolve_left (Ne.symm ha)
      rw [List.idxOf_cons_ne _ ha]
      have : (T == a) = false := by simpa using Ne.symm ha
      simp [this, ih ds hds hT']

theorem getD_append_of_lt (l l' : List β) (d : β) (n : ℕ) (h : n < l.length) : (l ++ l').getD n d = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_of_le (l l' : List β) (d : β) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

end Lists

/-! ## The steps of `OpenRep` -/

section OpenRep

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) {ι : Type} {G : OracleSpec ι}
  (i : C.Party) (v : Shares C Bit) (count : ℕ)

/-- The message of operator `i` in `OpenRep`. -/
def repOutbox (digests : List HashOutput) : Mail C E := fun j => if j = i then none else some (.bundle [
    .bits ((C.terms.filter fun T => j ∉ C.holders T ∧ K.owner T = i).flatMap fun T => vector count (v T)),
    .hashes ((C.terms.zip digests).filterMap fun (T, d) =>
      if j ∉ C.holders T ∧ i ∈ C.holders T ∧ K.owner T ≠ i then some d else none)])

/-- The copy of each term at operator `i` after `OpenRep`. -/
def repCopy (inbox : Mail C E) : Shares C Bit := fun T g =>
  if i ∈ C.holders T then v T g else
    let owned := C.terms.filter fun T' => i ∉ C.holders T' ∧ K.owner T' = K.owner T
    Msg.bitAt (Msg.part (inbox (K.owner T)) 0) (count * owned.idxOf T + g)

/-- The hash check of `OpenRep` at operator `i`. -/
def repCheck (inbox : Mail C E) (copyDigests : List HashOutput) : Prop :=
  ∀ T : C.Term, i ∉ C.holders T → ∀ h ∈ C.holders T, h ≠ K.owner T →
    let sent := C.terms.filter fun T' => i ∉ C.holders T' ∧ h ∈ C.holders T' ∧ K.owner T' ≠ h
    (Msg.hashesOf (Msg.part (inbox h) 1))[sent.idxOf T]? = (C.terms.zip copyDigests).lookup T

open Classical in
theorem openRep_eq : openRep (G := G) K (localContext i) v count = (do
    let digests ← oracleStep (C.terms.mapM fun T => hashQuery (.copy (vector count (v T))))
    let inbox ← exchange (repOutbox (E := E) K i v count digests)
    let copyDigests ← oracleStep (C.terms.mapM fun T => hashQuery (.copy (vector count (repCopy K i v count inbox T))))
    require (repCheck K i inbox copyDigests)
    pure fun g => ∑ T, repCopy K i v count inbox T g) := rfl

open Classical in
/-- The steps of `OpenRep` after the round. -/
def repRest (inbox : Mail C E) : PartyM C E G (ℕ → Bit) := do
  let copyDigests ← oracleStep (C.terms.mapM fun T => hashQuery (.copy (vector count (repCopy K i v count inbox T))))
  require (repCheck K i inbox copyDigests)
  pure fun g => ∑ T, repCopy K i v count inbox T g

/-- In an honest `OpenRep`, each copy is the shared value. -/
theorem openCopy_eq (w : Shares C Bit) (vr : C.Party → Shares C Bit)
    (hvr : ∀ i T g, i ∈ C.holders T → g < count → vr i T g = w T g) (ds : C.Party → List HashOutput)
    (T : C.Term) (g : ℕ) (hg : g < count) :
    repCopy K i (vr i) count (fun k => repOutbox (E := E) K k (vr k) count (ds k) i) T g = w T g := by
  unfold repCopy
  split_ifs with hi
  · exact hvr i T g hi hg
  · have hne : i ≠ K.owner T := fun h => hi (h ▸ K.owner_held T)
    simp only [repOutbox, if_neg hne, Msg.part, List.getElem?_cons_zero, Msg.bitAt]
    rw [getD_flatMap_vector _ _ _ T (List.mem_filter.2 ⟨mem_terms T, by simp [hi]⟩)
      (terms_nodup.filter _) g hg]
    exact hvr _ T g (K.owner_held T) hg

/-- In an honest `OpenRep`, the hash check passes. -/
theorem repCheck_honest (vr : C.Party → Shares C Bit) (ds : C.Party → List HashOutput) (val : C.Term → HashOutput)
    (hlen : ∀ h, (ds h).length = C.terms.length)
    (hds : ∀ h T, h ∈ C.holders T → (ds h)[C.terms.idxOf T]? = some (val T)) :
    repCheck K i (fun k => repOutbox (E := E) K k (vr k) count (ds k) i) (C.terms.map val) := by
  intro T hiT h hh hown
  have hne : i ≠ h := fun e => hiT (e ▸ hh)
  simp only [repOutbox, if_neg hne, Msg.part, List.getElem?_cons_succ, List.getElem?_cons_zero, Msg.hashesOf]
  have h1 := filterMap_zip_idxOf C.terms terms_nodup
    (fun T' => i ∉ C.holders T' ∧ h ∈ C.holders T' ∧ K.owner T' ≠ h) (ds h) (hlen h) T (mem_terms T) ⟨hiT, hh, Ne.symm hown⟩
  rw [lookup_zip_idxOf C.terms (C.terms.map val) (by simp) T (mem_terms T)]
  rw [List.getElem?_map,
    List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem (mem_terms T))]
  simp only [Option.map_some, List.getElem_idxOf]
  rw [← hds h T hh, ← h1]

end OpenRep

/-! ## The values of the layers -/

section Values

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (jobs : List Circuit)

/-- One layer of a circuit on its plain wires. -/
def plainLayer (job : Circuit) (w : List Bit) (layer : ℕ) : List Bit :=
  w ++ (job.layers.getD layer []).map fun ab => ab.1.eval w * ab.2.eval w

/-- The plain wires of a circuit after `l` layers. -/
def plainAt (job : Circuit) (input : List Bit) (l : ℕ) : List Bit := (List.range l).foldl (plainLayer job) input

/-- The plain input wires of job `k`. -/
def plainInput (x : C.Party → List (C.Term → List Bit)) (k : ℕ) : List Bit := inputValue (reconstruct fun i => (x i)[k]?)

theorem plainAt_succ (job : Circuit) (input : List Bit) (l : ℕ) :
    plainAt job input (l + 1) = plainLayer job (plainAt job input l) l := by
  simp [plainAt, List.range_succ, List.foldl_append]

theorem gatesAt_eq (l : ℕ) : gatesAt jobs l = flatIdx (jobs.map fun job => job.layers.getD l []) 0 := by
  simp only [gatesAt, flatIdx, List.zipIdx_map, List.flatMap_map]
  rfl

theorem outputsOf_eq : outputsOf jobs = flatIdx (jobs.map (·.outputs)) 0 := by
  simp only [outputsOf, flatIdx, List.zipIdx_map, List.flatMap_map]
  rfl

/-- The wires that layer `l` appends to job `k`. -/
def newWires (l k : ℕ) (z : Shares C Bit) (T : C.Term) : List Bit :=
  ((gatesAt jobs l).zipIdx.filter (·.1.1 = k)).map fun (_, g) => z T g

/-- The first gate of job `k` in layer `l`. -/
def gateOffset (l k : ℕ) : ℕ := (((jobs.map fun job => job.layers.getD l []).take k).map List.length).sum

theorem newWires_eq (l k : ℕ) (hk : k < jobs.length) (z : Shares C Bit) (T : C.Term) :
    newWires jobs l k z T = (List.range (jobs[k].layers.getD l []).length).map fun j => z T (gateOffset jobs l k + j) := by
  unfold newWires
  rw [gatesAt_eq, filter_zipIdx_flatIdx, if_pos (Nat.zero_le k)]
  simp only [Nat.sub_zero, List.map_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
  simp only [Option.map_some, Option.getD_some]
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp [gateOffset]

theorem getD_appendLayer (l : ℕ) (wires : List (C.Term → List Bit)) (z : Shares C Bit) (k : ℕ) :
    (appendLayer jobs l wires z).getD k (fun _ => []) =
      if k < wires.length then fun T => (wires.getD k fun _ => []) T ++ newWires jobs l k z T else fun _ => [] := by
  unfold appendLayer newWires
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx]
  split_ifs with hk
  · rw [List.getElem?_eq_getElem hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    simp
  · rw [List.getElem?_eq_none (by omega)]
    rfl

theorem length_appendLayer (l : ℕ) (wires : List (C.Term → List Bit)) (z : Shares C Bit) :
    (appendLayer jobs l wires z).length = wires.length := by
  simp [appendLayer]

/-- `layerX` reads only the held wires. -/
theorem layerX_congr (l : ℕ) (w w' : List (C.Term → List Bit)) (T : C.Term)
    (h : ∀ k, (w.getD k fun _ => []) T = (w'.getD k fun _ => []) T) :
    layerX K jobs l w T = layerX K jobs l w' T := by
  funext g
  unfold layerX
  split
  · simp only [Affine.share, h]
  · rfl

theorem layerY_congr (l : ℕ) (w w' : List (C.Term → List Bit)) (T : C.Term)
    (h : ∀ k, (w.getD k fun _ => []) T = (w'.getD k fun _ => []) T) :
    layerY K jobs l w T = layerY K jobs l w' T := by
  funext g
  unfold layerY
  split
  · simp only [Affine.share, h]
  · rfl

theorem outputShares_congr (w w' : List (C.Term → List Bit)) (T : C.Term)
    (h : ∀ k, (w.getD k fun _ => []) T = (w'.getD k fun _ => []) T) :
    outputShares K jobs w T = outputShares K jobs w' T := by
  funext g
  unfold outputShares
  split
  · simp only [Affine.share, h]
  · rfl

theorem gatesAt_offset (l k j : ℕ) (hk : k < jobs.length) (hj : j < (jobs[k].layers.getD l []).length) :
    (gatesAt jobs l)[gateOffset jobs l k + j]? = some (k, (jobs[k].layers.getD l [])[j]) := by
  rw [gatesAt_eq, gateOffset]
  have := getElem?_flatIdx (jobs.map fun job => job.layers.getD l []) 0 k j (by simpa using hk) (by simpa using hj)
  simpa using this

theorem gateOffset_lt (l k j : ℕ) (hk : k < jobs.length) (hj : j < (jobs[k].layers.getD l []).length) :
    gateOffset jobs l k + j < (gatesAt jobs l).length := by
  have h := gatesAt_offset jobs l k j hk hj
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

variable (x : C.Party → List (C.Term → List Bit))

/-- The state of the operators after `l` layers. Each operator agrees with the common wires `W` and
the common tuples `Ts` on its held terms, `W` shares the plain wires, and each tuple of `Ts` is a product. -/
structure LayerInv (l : ℕ) (p : C.Party → List (C.Term → List Bit) × List (Tuple C)) (W : List (C.Term → List Bit))
    (Ts : List (Tuple C)) : Prop where
  length_wires : ∀ i, (p i).1.length = jobs.length
  length_W : W.length = jobs.length
  agree : ∀ i T, i ∈ C.holders T → ∀ k, ((p i).1.getD k fun _ => []) T = (W.getD k fun _ => []) T
  length_plain : ∀ k (hk : k < jobs.length) T,
    ((W.getD k fun _ => []) T).length = (plainAt jobs[k] (plainInput x k) l).length
  sum_plain : ∀ k (hk : k < jobs.length) g,
    (plainAt jobs[k] (plainInput x k) l).getD g 0 = ∑ T, ((W.getD k fun _ => []) T).getD g 0
  length_tuples : ∀ i, (p i).2.length = Ts.length
  agree_tuples : ∀ i m (hm : m < Ts.length), TupleAgrees i ((p i).2[m]'(by rw [length_tuples]; exact hm)) Ts[m]
  product : ∀ τ ∈ Ts, IsProduct τ

theorem tupleAgrees_append (i : C.Party) (vs Ts : List (Tuple C)) (v τ : Tuple C) (hlen : vs.length = Ts.length)
    (hag : ∀ m (hm : m < Ts.length), TupleAgrees i (vs[m]'(by rw [hlen]; exact hm)) Ts[m]) (hv : TupleAgrees i v τ) :
    ∀ m (hm : m < (Ts ++ [τ]).length), TupleAgrees i ((vs ++ [v])[m]'(by simp [hlen] at hm ⊢; exact hm)) (Ts ++ [τ])[m] := by
  intro m hm
  simp only [List.length_append, List.length_singleton] at hm
  rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
  · rw [List.getElem_append_left (by omega), List.getElem_append_left hm]
    exact hag m hm
  · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    simpa [hlen] using hv

/-- One layer keeps the invariant, with an output `z` of `F_mult` that sums to the products. -/
theorem layerInv_step (mode : ReshareMode) (l : ℕ) (p : C.Party → List (C.Term → List Bit) × List (Tuple C))
    (W : List (C.Term → List Bit)) (Ts : List (Tuple C)) (hinv : LayerInv jobs x l p W Ts) (z : Shares C Bit)
    (hz : ∀ g, ∑ T, z T g = ∑ i, mulRep K (localContext i) (layerX K jobs l (p i).1) (layerY K jobs l (p i).1) g) :
    LayerInv jobs x (l + 1)
      (fun i => (appendLayer jobs l (p i).1 fun T g => if i ∈ C.holders T ∧ g < (gatesAt jobs l).length then z T g else 0,
        (p i).2 ++ [⟨layerX K jobs l (p i).1, layerY K jobs l (p i).1,
          fun T g => if i ∈ C.holders T ∧ g < (gatesAt jobs l).length then z T g else 0, (gatesAt jobs l).length, mode⟩]))
      (appendLayer jobs l W fun T g => if g < (gatesAt jobs l).length then z T g else 0)
      (Ts ++ [⟨layerX K jobs l W, layerY K jobs l W, fun T g => if g < (gatesAt jobs l).length then z T g else 0,
        (gatesAt jobs l).length, mode⟩]) := by
  set n := (gatesAt jobs l).length with hn
  have hX : ∀ i T, i ∈ C.holders T → layerX K jobs l (p i).1 T = layerX K jobs l W T :=
    fun i T h => layerX_congr K jobs l _ _ T (hinv.agree i T h)
  have hY : ∀ i T, i ∈ C.holders T → layerY K jobs l (p i).1 T = layerY K jobs l W T :=
    fun i T h => layerY_congr K jobs l _ _ T (hinv.agree i T h)
  have hprod : ∀ g, ∑ T, z T g = shareValue (layerX K jobs l W) g * shareValue (layerY K jobs l W) g := fun g => by
    rw [hz g]
    exact mulRep_views_sum K _ _ _ _ g (fun i T h => by rw [hX i T h]) (fun i T h => by rw [hY i T h])
  have hplain : ∀ k (hk : k < jobs.length), ∀ g, (plainAt jobs[k] (plainInput x k) l).getD g 0 =
      ∑ T, ((W.getD k fun _ => []) T).getD g 0 := hinv.sum_plain
  refine ⟨fun i => ?_, ?_, fun i T hi k => ?_, fun k hk T => ?_, fun k hk g => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · simp [length_appendLayer, hinv.length_wires]
  · simp [length_appendLayer, hinv.length_W]
  · rw [getD_appendLayer, getD_appendLayer, hinv.length_wires, hinv.length_W]
    split_ifs with hk
    · simp only [hinv.agree i T hi k, newWires, hi, true_and]
    · rfl
  · rw [getD_appendLayer, hinv.length_W, if_pos hk, plainAt_succ, plainLayer]
    have := hinv.length_plain k hk T
    rw [List.getD_eq_getElem?_getD] at this
    simp [this, newWires_eq jobs l k hk]
  · rw [getD_appendLayer, hinv.length_W, if_pos hk, plainAt_succ, plainLayer]
    simp only [newWires_eq jobs l k hk]
    set w := plainAt jobs[k] (plainInput x k) l with hw
    by_cases hg : g < w.length
    · rw [getD_append_of_lt _ _ _ _ hg, hplain k hk g]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [getD_append_of_lt _ _ _ _ (by rw [hinv.length_plain k hk T]; exact hg)]
    · push_neg at hg
      obtain ⟨j, rfl⟩ : ∃ j, g = w.length + j := ⟨g - w.length, by omega⟩
      rw [getD_append_of_le _ _ _ _ (by omega)]
      have hT : ∀ T, ((W.getD k fun _ => []) T ++ (List.range (jobs[k].layers.getD l []).length).map
          fun j => (if gateOffset jobs l k + j < n then z T (gateOffset jobs l k + j) else 0)).getD (w.length + j) 0 =
          ((List.range (jobs[k].layers.getD l []).length).map
            fun j => (if gateOffset jobs l k + j < n then z T (gateOffset jobs l k + j) else 0)).getD j 0 := fun T => by
        rw [getD_append_of_le _ _ _ _ (by rw [hinv.length_plain k hk T]; omega), hinv.length_plain k hk T, ← hw,
          Nat.add_sub_cancel_left]
      simp only [hT, Nat.add_sub_cancel_left]
      by_cases hj : j < (jobs[k].layers.getD l []).length
      · have e1 : ((jobs[k].layers.getD l []).map fun ab => ab.1.eval w * ab.2.eval w).getD j 0 =
            ((jobs[k].layers.getD l [])[j]).1.eval w * ((jobs[k].layers.getD l [])[j]).2.eval w := by
          generalize jobs[k].layers.getD l [] = L at hj ⊢
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        have e2 : ∀ T, ((List.range (jobs[k].layers.getD l []).length).map
            fun j => (if gateOffset jobs l k + j < n then z T (gateOffset jobs l k + j) else 0)).getD j 0 =
            z T (gateOffset jobs l k + j) := fun T => by
          have hlt := gateOffset_lt jobs l k j hk hj
          generalize jobs[k].layers.getD l [] = L at hj ⊢
          simp [List.getD_eq_getElem?_getD, List.getElem?_range hj, hn ▸ hlt]
        rw [e1]
        simp only [e2]
        rw [hprod, shareValue, shareValue]
        simp only [layerX, layerY, gatesAt_offset jobs l k j hk hj]
        rw [sum_affine_share _ _ _ _ (hplain k hk), sum_affine_share _ _ _ _ (hplain k hk)]
      · have e1 : ((jobs[k].layers.getD l []).map fun ab => ab.1.eval w * ab.2.eval w).getD j 0 = 0 := by
          generalize jobs[k].layers.getD l [] = L at hj ⊢
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hj)]
        have e2 : ∀ T, ((List.range (jobs[k].layers.getD l []).length).map
            fun j => (if gateOffset jobs l k + j < n then z T (gateOffset jobs l k + j) else 0)).getD j 0 = 0 :=
          fun T => by
            generalize jobs[k].layers.getD l [] = L at hj ⊢
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega : (List.range L.length).length ≤ j)]
        rw [e1]
        simp only [e2, Finset.sum_const_zero]
  · simp [hinv.length_tuples]
  · refine tupleAgrees_append i _ _ _ _ (hinv.length_tuples i) (hinv.agree_tuples i) ⟨fun T hT => ?_, rfl, rfl⟩
    refine ⟨hX i T hT, hY i T hT, ?_⟩
    funext g
    simp [hT]
  · intro τ hτ
    rcases List.mem_append.1 hτ with hτ | hτ
    · exact hinv.product τ hτ
    · simp only [List.mem_singleton] at hτ
      subst hτ
      intro g hg
      simp only [shareValue, if_pos hg]
      exact hprod g

theorem le_foldl_max (l : List ℕ) : ∀ init, init ≤ l.foldl max init ∧ ∀ a ∈ l, a ≤ l.foldl max init := by
  induction l with
  | nil => simp
  | cons b l ih =>
    intro init
    obtain ⟨h1, h2⟩ := ih (max init b)
    refine ⟨(le_max_left _ _).trans h1, fun a ha => ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · exact (le_max_right _ _).trans h1
    · exact h2 a ha

theorem foldl_max_const (l : List ℕ) (w : ℕ) (hl : l ≠ []) (h : ∀ a ∈ l, a = w) : l.foldl max 0 = w := by
  have key : ∀ (l : List ℕ) init, (∀ a ∈ l, a = w) → l.foldl max init = if l = [] then init else max init w := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih =>
      intro init h
      have hb := h b List.mem_cons_self
      subst hb
      rw [List.foldl_cons, ih _ fun a ha => h a (List.mem_cons_of_mem _ ha)]
      split_ifs <;> simp_all
  rw [key l 0 h, if_neg hl]
  simp

theorem plainAt_of_le (job : Circuit) (w : List Bit) : ∀ d, job.layers.length ≤ d →
    plainAt job w d = plainAt job w job.layers.length := by
  intro d hd
  induction d with
  | zero => rw [Nat.le_zero.1 hd]
  | succ d ih =>
    rcases Nat.lt_or_ge job.layers.length (d + 1) with h | h
    · rw [plainAt_succ, plainLayer, ih (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show job.layers.length ≤ d by omega)]
    · rw [show d + 1 = job.layers.length by omega]

theorem plainAt_length (job : Circuit) (w : List Bit) :
    plainAt job w job.layers.length =
      job.layers.foldl (fun w layer => w ++ layer.map fun ab => ab.1.eval w * ab.2.eval w) w := by
  have hl : (List.range job.layers.length).map (fun l => job.layers.getD l []) = job.layers :=
    List.ext_getElem (by simp) fun k h₁ h₂ => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
  conv_rhs => rw [← hl]
  rw [List.foldl_map]
  rfl

theorem layers_le_depth (k : ℕ) (hk : k < jobs.length) : jobs[k].layers.length ≤ depth jobs :=
  (le_foldl_max _ 0).2 _ (List.mem_map.2 ⟨jobs[k], List.getElem_mem hk, rfl⟩)

theorem shareValue_one (g : ℕ) : shareValue (one (R := Bit) K) g = 1 := by
  simp [shareValue, one]

/-- The opened outputs of a batch are the outputs of `F_main`. -/
theorem assemble_eq (p : C.Party → List (C.Term → List Bit) × List (Tuple C)) (W : List (C.Term → List Bit))
    (Ts : List (Tuple C)) (hinv : LayerInv jobs x (depth jobs) p W Ts) (V : ℕ → Bit)
    (hV : ∀ g < (outputsOf jobs).length, V g = shareValue (outputShares K jobs W) g) :
    assemble jobs V = mainOutputs jobs x := by
  unfold assemble mainOutputs
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  simp only [List.length_zipIdx, List.length_map] at h₁ h₂
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  rw [Circuit.eval, ← plainAt_length, ← plainAt_of_le _ _ _ (layers_le_depth jobs k h₂)]
  refine List.ext_getElem (by simp [vector]) fun g hg₁ hg₂ => ?_
  simp only [vector, List.getElem_map, List.getElem_range, List.length_map] at hg₁ ⊢
  have hoff : ((jobs.map (·.outputs)).take k).map List.length = (jobs.map (·.outputs.length)).take k := by
    simp [List.map_take]
    rfl
  have hget := getElem?_flatIdx (jobs.map (·.outputs)) 0 k g (by simpa using h₂) (by simpa using hg₁)
  rw [hoff, ← outputsOf_eq] at hget
  have hlt : ((jobs.map (·.outputs.length)).take k).sum + g < (outputsOf jobs).length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  rw [hV _ hlt, shareValue]
  simp only [outputShares, hget]
  simp only [Nat.zero_add, List.getElem_map]
  exact sum_affine_share _ _ _ _ (hinv.sum_plain k h₂)

/-- The inputs of a batch give the invariant before the layers. -/
theorem layerInv_zero (hx : MainInputs jobs noCoalition x) :
    LayerInv jobs x 0 (fun i => (x i, [])) ((List.range jobs.length).map fun k => reconstruct fun i => (x i)[k]?) [] := by
  obtain ⟨widths, -, hwidth, hcons⟩ := hx
  have hlen : ∀ i, (x i).length = jobs.length := fun i => (hwidth i (by simp [noCoalition])).1
  have hW : ∀ k (hk : k < jobs.length),
      ((List.range jobs.length).map fun k => reconstruct fun i => (x i)[k]?).getD k (fun _ => []) =
        reconstruct fun i => (x i)[k]? := fun k hk => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_range hk]
  have hrec : ∀ k (hk : k < jobs.length) i T, i ∈ C.holders T →
      (reconstruct fun i => (x i)[k]?) T = ((x i)[k]'(by rw [hlen]; exact hk)) T := fun k hk i T hi =>
    reconstruct_of_agree _ T _ fun j hj => ⟨(x j)[k]'(by rw [hlen]; exact hk),
      List.getElem?_eq_getElem _, by
        have := hcons k T j hj i hi (by simp [noCoalition]) (by simp [noCoalition])
        simpa [List.getElem?_eq_getElem (by rw [hlen]; exact hk : k < (x j).length),
          List.getElem?_eq_getElem (by rw [hlen]; exact hk : k < (x i).length)] using this⟩
  have hlenT : ∀ k (hk : k < jobs.length) T, ((reconstruct fun i => (x i)[k]?) T).length = widths.getD k 0 := by
    intro k hk T
    obtain ⟨h, hh⟩ := exists_holder T
    rw [hrec k hk h T hh]
    have := (hwidth h (by simp [noCoalition])).2 k hk T
    simpa [List.getElem?_eq_getElem (by rw [hlen]; exact hk : k < (x h).length), hh] using this
  have hinput : ∀ k (hk : k < jobs.length), (plainInput x k).length = widths.getD k 0 := by
    intro k hk
    unfold plainInput inputValue
    rw [List.length_map, List.length_range]
    refine foldl_max_const _ _ ?_ fun a ha => ?_
    · obtain ⟨T₀, -⟩ := Option.isSome_iff_exists.1 (lackedTerm_empty_isSome (C := C))
      exact List.ne_nil_of_mem (List.mem_map_of_mem (mem_terms T₀))
    · obtain ⟨T, -, rfl⟩ := List.mem_map.1 ha
      exact hlenT k hk T
  refine ⟨fun i => hlen i, by simp, fun i T hi k => ?_, fun k hk T => ?_, fun k hk g => ?_, fun i => rfl,
    fun i m hm => absurd hm (by simp), fun τ hτ => absurd hτ (by simp)⟩
  · rcases Nat.lt_or_ge k jobs.length with hk | hk
    · rw [hW k hk, hrec k hk i T hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hk)]
      rfl
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen i]; exact hk),
        List.getElem?_eq_none (by simpa using hk)]
  · rw [hW k hk, hlenT k hk T, plainAt, List.range_zero, List.foldl_nil, hinput k hk]
  · rw [hW k hk, plainAt, List.range_zero, List.foldl_nil]
    unfold plainInput inputValue
    rcases Nat.lt_or_ge g ((C.terms.map fun T => ((reconstruct fun i => (x i)[k]?) T).length).foldl max 0) with hg | hg
    · simp [List.getD_eq_getElem?_getD, List.getElem?_range hg]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hg)]
      symm
      refine Finset.sum_eq_zero fun T _ => ?_
      have := hinput k hk
      unfold plainInput inputValue at this
      rw [List.length_map, List.length_range] at this
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlenT k hk T, ← this]; exact hg)]
      rfl

end Values

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- Each replicated term has an honest holder. -/
theorem main_exists_honest_holder (D : C.Coalition) (T : C.Term) :
    ∃ i, i ∈ C.holders T ∧ i ∉ D.1 := by
  have hcard : D.1.card < (C.holders T).card := by
    rw [Committee.holders, Finset.card_compl, T.2, Fintype.card_fin]
    have := D.2
    have := C.one_le_t
    simp only [Committee.n]
    omega
  obtain ⟨i, hi, hiD⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨i, hi, hiD⟩

/-- The honest hash sent for one term has its original index in the digest list. -/
theorem main_open_hash_sent (K : Constants C E) (i h : C.Party) (v : Shares C Bit)
    (count : ℕ) (ds : List HashOutput) (hlen : ds.length = C.terms.length)
    (T : C.Term) (hiT : i ∉ C.holders T) (hhT : h ∈ C.holders T) (hown : h ≠ K.owner T) :
    (Msg.hashesOf (Msg.part (repOutbox K h v count ds i) 1))[
      (C.terms.filter fun T' => i ∉ C.holders T' ∧ h ∈ C.holders T' ∧ K.owner T' ≠ h).idxOf T]? =
      ds[C.terms.idxOf T]? := by
  have hne : i ≠ h := fun e => hiT (e ▸ hhT)
  simp only [repOutbox, if_neg hne, Msg.part, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Msg.hashesOf]
  exact filterMap_zip_idxOf C.terms terms_nodup
    (fun T' => i ∉ C.holders T' ∧ h ∈ C.holders T' ∧ K.owner T' ≠ h)
    ds hlen T (mem_terms T) ⟨hiT, hhT, Ne.symm hown⟩

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- The pivot exists for every allowed coalition. -/
theorem main_lacked_exists (D : C.Coalition) : ∃ T : C.Term, lackedTerm D.1 = some T := by
  obtain ⟨T, hDT, hT⟩ := Finset.exists_superset_card_eq D.2
    (by simp [Committee.n]; have := C.one_le_t; omega)
  have hunknown : ¬ KnownTo D.1 (⟨T, hT⟩ : C.Term) := by
    rintro ⟨j, hj, hh⟩
    have hmem := hDT hj
    simp [Committee.holders, hmem] at hh
  have hsome : (lackedTerm D.1).isSome := by
    rw [lackedTerm, List.find?_isSome]
    exact ⟨⟨T, hT⟩, mem_terms _, by simpa using hunknown⟩
  exact Option.isSome_iff_exists.mp hsome

end ThresholdLeanXmssSecurity
