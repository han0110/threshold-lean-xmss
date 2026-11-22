import ThresholdLeanXmssSecurity.Proof.BatchCheck.Streams
import ThresholdLeanXmssSecurity.Proof.Pilot.Pilot

/-!
# The check on drawn tables

The pilot runs the real check in `streamWorld`. This file moves that run to the form of the check on
drawn tables, writes the join in its output form (`pilotJoinOut`), and gives the handler
rows and the prefetch row of the join.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The keys of the honest operators -/

/-- The key of a term at its first honest holder. -/
def pilotTermKey (D : C.Coalition) (prss : C.Party → PrssKeys C) (T : C.Term) : HashOutput :=
  (prss (ThresholdLeanXmssSecurity.refHolder D T)).term T

/-- The key of a pair at its first end if that end is honest, and at its second end if not. -/
def pilotPairKey (D : C.Coalition) (prss : C.Party → PrssKeys C) (p : C.Pair) : HashOutput :=
  if p.1.1 ∉ D.1 then (prss p.1.1).pair p.1.2 else (prss p.1.2).pair p.1.1

/-- The pair of two operators in order is the pair of its two ends. -/
theorem pairOf_of_lt (p : C.Pair) (h : p.1.1 ≠ p.1.2) : C.pairOf p.1.1 p.1.2 h = p := by
  unfold Committee.pairOf
  simp only [p.2, dite_true]

/-- Under `PrssKeysAgree`, each honest operator holds the keys `pilotTermKey` and `pilotPairKey`. -/
theorem holdsDealt_pilot {D : C.Coalition} {prss : C.Party → PrssKeys C} (hagree : PrssKeysAgree D prss)
    (i : C.Party) (hi : i ∉ D.1) :
    RealNetworkE1s.HoldsDealt (pilotTermKey D prss) (pilotPairKey D prss) i (prss i) := by
  refine ⟨fun T hT => ?_, fun j hj => ?_⟩
  · simp only [dealtPrssKeys, hT, ite_true, pilotTermKey]
    exact hagree.1 T i (ThresholdLeanXmssSecurity.refHolder D T) hi (ThresholdLeanXmssSecurity.refHolder_spec D T).2 hT
      (ThresholdLeanXmssSecurity.refHolder_spec D T).1
  · simp only [dealtPrssKeys, hj, dite_false, pilotPairKey]
    unfold Committee.pairOf
    by_cases hij : i < j
    · simp only [hij, dite_true, hi, not_false_eq_true, ite_true]
    · simp only [hij, dite_false]
      by_cases hjD : j ∈ D.1
      · simp only [hjD, not_true_eq_false, ite_false]
      · simp only [hjD, not_false_eq_true, ite_true]
        exact hagree.2 i j hi hjD (Ne.symm hj)

/-! ## The cells of the rows of the check -/

/-- The index of a cell of the rows of the check. It is a hidden name with a position of a row over
`E` or a position of the salts. -/
abbrev RowIx (D : C.Coalition) (count : ℕ) :=
  {name : KeyName C // Hidden D name} ×
    ((Fin (RealNetworkV3.checkLabels count) × Fin (elementBits * 2)) ⊕ Fin 256)

/-- The cell of an index, under the keys `term` and `pair`, from the label `L`. The row at position
`k` reads the stream `checkStream`, and the salts read the stream 2, as `rowTables` reads them. -/
def rowCell (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (L count : ℕ) :
    RowIx D count → (KeyName C × HashOutput) × ℕ × ℕ × ℕ
  | (name, .inl (k, g)) => ((name.1, (dealtKey term pair name.1).getD 0), L + k.val,
      RealNetworkE1g.checkStream (halvings count) k.val, g.val)
  | (name, .inr g) => ((name.1, (dealtKey term pair name.1).getD 0), L + (2 * halvings count + 3), 2, g.val)

/-- The cells of the rows, in the order of `Fintype.equivFin`. -/
def rowAddr (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (L count : ℕ) :
    Fin (Fintype.card (RowIx D count)) → (KeyName C × HashOutput) × ℕ × ℕ × ℕ :=
  rowCell D term pair L count ∘ (Fintype.equivFin (RowIx D count)).symm

theorem checkStream_lt_two (R n : ℕ) : RealNetworkE1g.checkStream R n < 2 := by
  unfold RealNetworkE1g.checkStream
  split_ifs <;> omega

theorem rowCell_injective (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (L count : ℕ) : Function.Injective (rowCell D term pair L count) := by
  rintro ⟨⟨n₁, h₁⟩, a₁⟩ ⟨⟨n₂, h₂⟩, a₂⟩ h
  rcases a₁ with ⟨k₁, g₁⟩ | g₁ <;> rcases a₂ with ⟨k₂, g₂⟩ | g₂ <;>
    simp only [rowCell, Prod.mk.injEq] at h
  · obtain ⟨⟨rfl, -⟩, hk, -, hg⟩ := h
    have hk' : k₁ = k₂ := Fin.ext (by omega)
    subst hk'
    rw [Fin.ext hg]
  · exact absurd h.2.2.1 (ne_of_lt (checkStream_lt_two _ _))
  · exact absurd h.2.2.1.symm (ne_of_lt (checkStream_lt_two _ _))
  · obtain ⟨⟨rfl, -⟩, -, -, hg⟩ := h
    rw [Fin.ext hg]

theorem rowAddr_injective (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (L count : ℕ) : Function.Injective (rowAddr D term pair L count) :=
  (rowCell_injective D term pair L count).comp (Fintype.equivFin _).symm.injective

/-- `StreamsFresh` gives each cell of the rows no value in the hidden cache. -/
theorem rowCell_fresh {D : C.Coalition} {L : ℕ} {prss : C.Party → PrssKeys C} {hidden : HiddenCache C}
    (hfresh : StreamsFresh D L prss hidden) (count : ℕ) (ix : RowIx D count) :
    hidden (rowCell D (pilotTermKey D prss) (pilotPairKey D prss) L count ix) = none := by
  obtain ⟨⟨name, hn⟩, a⟩ := ix
  have hcell : ∀ ρ idx pos, L ≤ ρ →
      hidden ((name, (dealtKey (pilotTermKey D prss) (pilotPairKey D prss) name).getD 0), ρ, idx, pos) = none := by
    intro ρ idx pos hρ
    cases name with
    | parameter => exact hn.elim
    | term T =>
      obtain ⟨hT, hTD⟩ := ThresholdLeanXmssSecurity.refHolder_spec D T
      exact ((hfresh (ThresholdLeanXmssSecurity.refHolder D T) hTD ρ hρ idx pos).1 T hT hn)
    | pair p =>
      have hne : p.1.2 ≠ p.1.1 := ne_of_gt p.2
      have h := (hfresh p.1.1 hn.1 ρ hρ idx pos).2 p.1.2 hne
      rw [pairOf_of_lt p (Ne.symm hne)] at h
      simp only [dealtKey, Option.getD_some, pilotPairKey]
      rw [ite_eq_left hn.1]
      exact h hn
  rcases a with ⟨k, g⟩ | g
  · exact hcell _ _ _ (Nat.le_add_right L k.val)
  · exact hcell _ _ _ (Nat.le_add_right L _)

/-! ## The exit from the world with uniform streams -/

/-- The program of the check of operator `i` in `pilotRun`. -/
def pilotProgram (K : Constants C E) (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C)
    (x : C.Party → List (Tuple C)) (L tg : ℕ) (i : C.Party) : PartyM C E RealSpec Unit :=
  (check K (pilotContext keys prss i) (realCheckBuildingBlocks K (pilotContext keys prss i)) (x i)).run'
    ⟨filledHistory K i (x i), L, tg⟩

variable (prims : Primitives)

omit [Field E] [Algebra Bit E] in
/-- A phase on the world with the table `c` on the free copy is the phase on the local oracles with
the table in each honest program. -/
theorem worldTable_executePhase (D : C.Coalition) (c : HiddenCache C) {O Lk Rk Ia α : Type}
    (A : Adversary C E Ia Lk Rk) (F : Functionality C PEmpty O Lk Rk) (fuel : ℕ) (st : A.State)
    (p : C.Party → PartyM C E (CallSpec PEmpty O) α) :
    simulateQ (worldAnswer prims) (simulateQ (RealNetworkN3.tableImpl D c) (executePhase worldRoles D A F fuel st p)) =
      simulateQ (localAnswer prims)
        (executePhase localRoles D A F fuel st fun i => RealNetworkN3.tableProgram D c (p i)) := by
  have hroles : mapRoles (worldAnswer (C := C) prims) (mapRoles (RealNetworkN3.tableImpl D c) worldRoles) =
      mapRoles (localAnswer prims) (RealNetworkN3.tableRoles D c) := by
    unfold mapRoles
    congr 1
    · funext β oa
      change simulateQ (worldAnswer prims) (simulateQ (RealNetworkN3.tableImpl D c) (worldRoles.adversary oa)) =
        simulateQ (localAnswer prims) oa
      rw [RealNetworkN3.tableImpl_adversary, simulateQ_world_adversary']
    · funext β oa
      change simulateQ (worldAnswer prims) (simulateQ (RealNetworkN3.tableImpl D c) (free oa)) =
        simulateQ (localAnswer prims) (simulateQ (RealNetworkN3.tableLocal D c) oa)
      rw [RealNetworkN3.tableImpl_free]
      exact simulateQ_free _ _ _
  rw [simulateQ_executePhase_mapRoles, simulateQ_executePhase_mapRoles, hroles,
    ← simulateQ_executePhase_mapRoles, RealNetworkN3.tablePush]

/-- The exit from `streamWorld`. The cells of the rows of the check under the honest keys and a finite
set of other cells are drawn first. Then each honest program reads its hidden streams from that table,
on the local oracles. -/
theorem pilotOutputs_table (K : Constants C E) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (counts : List ℕ)
    (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State) (cache : HashCache C)
    (hidden : HiddenCache C) (hfresh : StreamsFresh D L prss hidden) :
    ∃ (m : ℕ) (extra : Fin m → (KeyName C × HashOutput) × ℕ × ℕ × ℕ),
      pilotOutputs prims K D net keys prss counts x L tg st cache hidden =ᵈ
        (($ᵗ (Fin m → Bit)) >>= fun junk => ($ᵗ (Fin (Fintype.card (RowIx D counts.sum)) → Bit)) >>= fun vals =>
          (simulateQ (localAnswer prims) (executePhase localRoles D net noFunctionality (checkRounds counts.sum) st
            fun i => RealNetworkN3.tableProgram D
              (cacheFin (rowAddr D (pilotTermKey D prss) (pilotPairKey D prss) L counts.sum) vals
                (cacheFin extra junk hidden)) (pilotProgram K keys prss x L tg i))).run' cache) := by
  obtain ⟨m, extra, -, -, -, h⟩ := RealNetworkN3.streamWorld_exit prims D
    (pilotRun K D net keys prss counts x L tg st) (rowAddr D (pilotTermKey D prss) (pilotPairKey D prss) L counts.sum)
    (rowAddr_injective _ _ _ _ _) cache hidden (fun j => rowCell_fresh hfresh _ _)
  refine ⟨m, extra, ?_⟩
  have h' := h.map Prod.fst
  simp only [Functor.map_map, map_bind] at h'
  unfold pilotOutputs
  rw [StateT.run'_eq]
  refine h'.trans (EvalDistEq.bind_right _ fun junk => EvalDistEq.bind_right _ fun vals => ?_)
  rw [StateT.run'_eq, pilotRun, worldTable_executePhase]
  rfl

/-! ## The phase of the check as a phase of the join -/

omit [Field E] [Algebra Bit E] in
/-- A map of each honest program is a map of the outputs of the phase. -/
theorem executePhase_map {I O Lk Rk Ia α β : Type} (D : C.Coalition) (A : Adversary C E Ia Lk Rk)
    (F : Functionality C I O Lk Rk) (fuel : ℕ) (st : A.State) (p : C.Party → PartyM C E (CallSpec I O) α)
    (f : α → β) :
    executePhase localRoles D A F fuel st (fun i => f <$> p i) =
      (fun r => (r.1, fun i => (r.2 i).map f)) <$> executePhase localRoles D A F fuel st p := by
  unfold executePhase
  rw [startSteps_map localRoles (fun _ _ => rfl), bind_map_left, map_bind]
  exact bind_congr fun steps => executeRounds_map localRoles (fun _ _ => rfl) D A F f fuel st steps

omit [Field E] [Algebra Bit E] in
/-- The table form of a map is the map of the table form. -/
theorem tableProgram_map {ι : Type} {G : OracleSpec ι} (D : C.Coalition) (c : HiddenCache C) {α β : Type}
    (p : PartyM C E G α) (f : α → β) :
    RealNetworkN3.tableProgram D c (f <$> p) = f <$> RealNetworkN3.tableProgram D c p := by
  rw [map_eq_bind_pure_comp, RealNetworkN3.tableProgram_bind, map_eq_bind_pure_comp]
  refine bind_congr fun a => ?_
  unfold RealNetworkN3.tableProgram
  apply OptionT.ext
  simp

/-- The start state of the check of operator `v`. -/
def pilotStart (K : Constants C E) (x : C.Party → List (Tuple C)) (L tg : ℕ) (v : C.Party) : RunState C :=
  ⟨filledHistory K v (x v), L, tg⟩

/-- The outputs of a phase of the join as the outputs of the pilot. -/
def pilotOut {σ β : Type} (r : σ × (C.Party → Option β)) : σ × (C.Party → Option Unit) :=
  (r.1, fun i => (r.2 i).map fun _ => ())

/-- The phase of the pilot on a table is the left phase `realCheckPhase` of the join, with each
operator as its own input. -/
theorem pilotPhase_eq (K : Constants C E) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (table : HiddenCache C) (fuel : ℕ)
    (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State) :
    executePhase localRoles D net noFunctionality fuel st
        (fun i => RealNetworkN3.tableProgram D table (pilotProgram K keys prss x L tg i)) =
      pilotOut <$> RealNetworkE1join.realCheckPhase K D net noFunctionality keys table fuel (fun i => some i) x
        (pilotStart K x L tg) prss st := by
  unfold RealNetworkE1join.realCheckPhase pilotOut
  rw [← executePhase_map]
  refine executePhase_congr _ _ _ _ _ _ _ fun i _ => ?_
  simp only [Option.elim_some, RealNetworkE1s.tableProgram_eq, tableProgram_map, pilotProgram, StateT.run'_eq]
  rw [← tableProgram_map, ← tableProgram_map]
  congr 1
  simp [pilotStart, pilotContext]

/-! ## The join and the tables -/

variable (K : Constants C E)

/-- The tables of the check, drawn uniform, as a computation with no oracle. It is `drawTables`. -/
def drawTablesProb [SampleableType E] (m : ℕ) : ProbComp (RealNetworkV3.DrawTables C E m) := do
  let freshE ← $ᵗ (Fin m → C.Term → Fin 2 → E)
  let freshPairE ← $ᵗ (Fin m → C.Pair → Fin 2 → E)
  let freshB ← $ᵗ (C.Term → Fin 256 → Bit)
  let freshPairB ← $ᵗ (C.Pair → Fin 256 → Bit)
  pure ⟨freshE, freshPairE, freshB, freshPairB⟩

/-- Uniform cells of the rows of the check give the drawn tables, for a use that reads the
tables only at the hidden names. The cells are under the keys `term` and `pair` from the label `L`. -/
def RowTablesUniform [SampleableType E] : Prop :=
  ∀ (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (L count : ℕ) (β : Type)
    (G : RealNetworkV3.DrawTables C E (RealNetworkV3.checkLabels count) → ProbComp β),
    (∀ t t', RealNetworkE1join.HiddenAgree D t t' → G t = G t') →
    (($ᵗ (Fin (Fintype.card (RowIx D count)) → Bit)) >>= fun vals =>
        G (RealNetworkE1o.rowTables K (cacheFin (rowAddr D term pair L count) vals ∅) term pair L count)) =ᵈ
      (drawTablesProb (RealNetworkV3.checkLabels count) >>= G)

omit [Field E] [Algebra Bit E] in
/-- The table with the cells of the rows has the value `vals` at each cell of the rows. -/
theorem cacheFin_rowCell (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (L count : ℕ) (vals : Fin (Fintype.card (RowIx D count)) → Bit) (c : HiddenCache C) (ix : RowIx D count) :
    cacheFin (rowAddr D term pair L count) vals c (rowCell D term pair L count ix) =
      some (vals (Fintype.equivFin _ ix)) := by
  have h : rowCell D term pair L count ix = rowAddr D term pair L count (Fintype.equivFin _ ix) := by
    simp only [rowAddr, Function.comp_apply, Equiv.symm_apply_apply]
  rw [h]
  exact cacheFin_at _ (rowAddr_injective D term pair L count) vals c _

omit [Field E] [Algebra Bit E] in
/-- A bit of a row over `E` of the table with the cells of the rows. -/
theorem tableBit_rowE (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (L count : ℕ) (vals : Fin (Fintype.card (RowIx D count)) → Bit) (c : HiddenCache C)
    (name : {name : KeyName C // Hidden D name}) (k : Fin (RealNetworkV3.checkLabels count)) (pos : ℕ)
    (hp : pos < elementBits * 2) :
    tableBit (cacheFin (rowAddr D term pair L count) vals c) term pair name.1 (L + k.val)
        (RealNetworkE1g.checkStream (halvings count) k.val) pos =
      vals (Fintype.equivFin _ (name, .inl (k, ⟨pos, hp⟩))) := by
  have h := cacheFin_rowCell D term pair L count vals c (name, .inl (k, ⟨pos, hp⟩))
  simp only [rowCell] at h
  simp only [tableBit, h, Option.getD_some]

omit [Field E] [Algebra Bit E] in
/-- A bit of the row of the salts of the table with the cells of the rows. -/
theorem tableBit_rowB (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (L count : ℕ) (vals : Fin (Fintype.card (RowIx D count)) → Bit) (c : HiddenCache C)
    (name : {name : KeyName C // Hidden D name}) (g : Fin 256) :
    tableBit (cacheFin (rowAddr D term pair L count) vals c) term pair name.1 (L + (2 * halvings count + 3)) 2
        g.val = vals (Fintype.equivFin _ (name, .inr g)) := by
  have h := cacheFin_rowCell D term pair L count vals c (name, .inr g)
  simp only [rowCell] at h
  simp only [tableBit, h, Option.getD_some]

/-- The positions of two elements. -/
theorem elementPos_two (g : Fin 2) (e : Fin elementBits) : elementBits * g.val + e.val < elementBits * 2 := by
  have hg : g.val + 1 ≤ 2 := g.2
  have he := e.2
  calc elementBits * g.val + e.val < elementBits * g.val + elementBits := by omega
    _ = elementBits * (g.val + 1) := by ring
    _ ≤ elementBits * 2 := Nat.mul_le_mul_left _ hg

/-- The rows of a table read only the cells of the rows at the hidden names. So the cells of the
table outside the rows do not change them there. -/
theorem rowTables_hiddenAgree (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (L count : ℕ) (vals : Fin (Fintype.card (RowIx D count)) → Bit) (c : HiddenCache C) :
    RealNetworkE1join.HiddenAgree D
      (RealNetworkE1o.rowTables K (cacheFin (rowAddr D term pair L count) vals c) term pair L count)
      (RealNetworkE1o.rowTables K (cacheFin (rowAddr D term pair L count) vals ∅) term pair L count) := by
  have hbitE := tableBit_rowE D term pair L count vals
  have hbitB := tableBit_rowB D term pair L count vals
  have hpos := elementPos_two
  refine ⟨fun k T hT => ?_, fun k p hp => ?_, fun T hT => ?_, fun p hp => ?_⟩
  · funext g
    exact congrArg K.encode.symm (funext fun e =>
      (hbitE c ⟨.term T, hT⟩ k _ (hpos g e)).trans (hbitE ∅ ⟨.term T, hT⟩ k _ (hpos g e)).symm)
  · funext g
    exact congrArg K.encode.symm (funext fun e =>
      (hbitE c ⟨.pair p, hp⟩ k _ (hpos g e)).trans (hbitE ∅ ⟨.pair p, hp⟩ k _ (hpos g e)).symm)
  · funext g
    dsimp only [RealNetworkE1o.rowTables]
    exact (hbitB c ⟨.term T, hT⟩ g).trans (hbitB ∅ ⟨.term T, hT⟩ g).symm
  · funext g
    dsimp only [RealNetworkE1o.rowTables]
    exact (hbitB c ⟨.pair p, hp⟩ g).trans (hbitB ∅ ⟨.pair p, hp⟩ g).symm

/-! ## The uniform tables -/

/-- A hidden term. -/
abbrev HiddenTerm (D : C.Coalition) := {T : C.Term // Hidden D (.term T)}

/-- A hidden pair. -/
abbrev HiddenPair (D : C.Coalition) := {p : C.Pair // Hidden D (.pair p)}

/-- The tables with the values `hE`, `hP`, `hB` and `hPB` at the hidden names, and zero at the other
names. -/
def hiddenTables (D : C.Coalition) {m : ℕ} (hE : Fin m → HiddenTerm D → Fin 2 → E)
    (hP : Fin m → HiddenPair D → Fin 2 → E) (hB : HiddenTerm D → Fin 256 → Bit) (hPB : HiddenPair D → Fin 256 → Bit) :
    RealNetworkV3.DrawTables C E m where
  freshE k T g := if h : Hidden D (.term T) then hE k ⟨T, h⟩ g else 0
  freshPairE k p g := if h : Hidden D (.pair p) then hP k ⟨p, h⟩ g else 0
  freshB T g := if h : Hidden D (.term T) then hB ⟨T, h⟩ g else 0
  freshPairB p g := if h : Hidden D (.pair p) then hPB ⟨p, h⟩ g else 0

omit [Field E] [Algebra Bit E] in
/-- A uniform sample that is read through the first part of a bijection with a product is a uniform
sample of that part. -/
theorem uniform_fst_bind {X Y Z β : Type} [SampleableType X] [SampleableType Y] [SampleableType Z]
    (φ : X ≃ Y × Z) (F : Y → ProbComp β) :
    (($ᵗ X) >>= fun x => F (φ x).1) =ᵈ (($ᵗ Y) >>= F) := by
  have h1 := SampleableType.map_uniformSample_evalDistEq_of_bijective φ.bijective
  have e : (($ᵗ X) >>= fun x => F (φ x).1) = ((φ <$> ($ᵗ X)) >>= fun p => F p.1) := by rw [bind_map_left]
  rw [e]
  refine (EvalDistEq.bind_left h1 _).trans ?_
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  exact EvalDistEq.bind_right _ fun y => OracleComp.EvalDistEq.bind_const _ _

/-- The split of each row of a table into its hidden part and its other part. -/
def rowSplit {I A B : Type} (σ : I ≃ A × B) (m : ℕ) : (Fin m → I) ≃ (Fin m → A) × (Fin m → B) :=
  (Equiv.arrowCongr (Equiv.refl _) σ).trans (Equiv.arrowProdEquivProdArrow _ _ _)

/-- The split of a table of the terms into the hidden terms and the other terms. -/
def termSplit (D : C.Coalition) (Y : Type) :
    (C.Term → Y) ≃ (HiddenTerm D → Y) × ({T : C.Term // ¬ Hidden D (.term T)} → Y) :=
  Equiv.piEquivPiSubtypeProd (fun T => Hidden D (.term T)) fun _ => Y

/-- The split of a table of the pairs into the hidden pairs and the other pairs. -/
def pairSplit (D : C.Coalition) (Y : Type) :
    (C.Pair → Y) ≃ (HiddenPair D → Y) × ({p : C.Pair // ¬ Hidden D (.pair p)} → Y) :=
  Equiv.piEquivPiSubtypeProd (fun p => Hidden D (.pair p)) fun _ => Y

omit [Algebra Bit E] in
/-- The drawn tables, for a use that reads them only at the hidden names, are uniform values at the
hidden names. -/
theorem drawTables_hidden [SampleableType E] (D : C.Coalition) (m : ℕ) {β : Type}
    (G : RealNetworkV3.DrawTables C E m → ProbComp β)
    (hG : ∀ t t', RealNetworkE1join.HiddenAgree D t t' → G t = G t') :
    (drawTablesProb m >>= G) =ᵈ
      (($ᵗ (Fin m → HiddenTerm D → Fin 2 → E)) >>= fun hE => ($ᵗ (Fin m → HiddenPair D → Fin 2 → E)) >>= fun hP =>
        ($ᵗ (HiddenTerm D → Fin 256 → Bit)) >>= fun hB => ($ᵗ (HiddenPair D → Fin 256 → Bit)) >>= fun hPB =>
          G (hiddenTables D hE hP hB hPB)) := by
  have hagree : ∀ fE fP fB fPB, G ⟨fE, fP, fB, fPB⟩ =
      G (hiddenTables D (fun k T => fE k T.1) (fun k p => fP k p.1) (fun T => fB T.1) (fun p => fPB p.1)) :=
    fun fE fP fB fPB => hG _ _ ⟨fun k T hT => by simp [hiddenTables, hT], fun k p hp => by simp [hiddenTables, hp],
      fun T hT => by simp [hiddenTables, hT], fun p hp => by simp [hiddenTables, hp]⟩
  have e : (drawTablesProb m >>= G) = (($ᵗ (Fin m → C.Term → Fin 2 → E)) >>= fun fE =>
      ($ᵗ (Fin m → C.Pair → Fin 2 → E)) >>= fun fP => ($ᵗ (C.Term → Fin 256 → Bit)) >>= fun fB =>
        ($ᵗ (C.Pair → Fin 256 → Bit)) >>= fun fPB =>
          G (hiddenTables D (fun k T => fE k T.1) (fun k p => fP k p.1) (fun T => fB T.1) (fun p => fPB p.1))) := by
    simp only [drawTablesProb, bind_assoc, pure_bind]
    exact bind_congr fun fE => bind_congr fun fP => bind_congr fun fB => bind_congr fun fPB => hagree fE fP fB fPB
  rw [e]
  refine (uniform_fst_bind (rowSplit (termSplit D (Fin 2 → E)) m) fun hE =>
    ($ᵗ (Fin m → C.Pair → Fin 2 → E)) >>= fun fP => ($ᵗ (C.Term → Fin 256 → Bit)) >>= fun fB =>
      ($ᵗ (C.Pair → Fin 256 → Bit)) >>= fun fPB =>
        G (hiddenTables D hE (fun k p => fP k p.1) (fun T => fB T.1) (fun p => fPB p.1))).trans ?_
  refine EvalDistEq.bind_right _ fun hE => ?_
  refine (uniform_fst_bind (rowSplit (pairSplit D (Fin 2 → E)) m) fun hP =>
    ($ᵗ (C.Term → Fin 256 → Bit)) >>= fun fB => ($ᵗ (C.Pair → Fin 256 → Bit)) >>= fun fPB =>
      G (hiddenTables D hE hP (fun T => fB T.1) (fun p => fPB p.1))).trans ?_
  refine EvalDistEq.bind_right _ fun hP => ?_
  refine (uniform_fst_bind (termSplit D (Fin 256 → Bit)) fun hB =>
    ($ᵗ (C.Pair → Fin 256 → Bit)) >>= fun fPB => G (hiddenTables D hE hP hB (fun p => fPB p.1))).trans ?_
  refine EvalDistEq.bind_right _ fun hB => ?_
  exact uniform_fst_bind (pairSplit D (Fin 256 → Bit)) fun hPB => G (hiddenTables D hE hP hB hPB)

/-- The cells of the rows at the hidden terms or at the hidden pairs, for the positions `X`. -/
def namePart (D : C.Coalition) (X : Type) :
    {name : KeyName C // Hidden D name} × X ≃ HiddenTerm D × X ⊕ HiddenPair D × X :=
  (Equiv.prodCongr (hiddenNameSum D) (Equiv.refl X)).trans (Equiv.sumProdDistrib _ _ X)

/-- The cells of the rows in four parts. They are the rows over `E` and the salts, each at the hidden
terms and at the hidden pairs. -/
def rowParts (D : C.Coalition) (count : ℕ) :
    RowIx D count ≃
      (HiddenTerm D × (Fin (RealNetworkV3.checkLabels count) × Fin (elementBits * 2)) ⊕
        HiddenPair D × (Fin (RealNetworkV3.checkLabels count) × Fin (elementBits * 2))) ⊕
      (HiddenTerm D × Fin 256 ⊕ HiddenPair D × Fin 256) :=
  (Equiv.prodSumDistrib _ _ _).trans (Equiv.sumCongr (namePart D _) (namePart D _))

/-- The bits of the rows over `E` of the names `I`, decoded into two elements at each label. -/
def rowDecodeE (K : Constants C E) (I : Type) (m : ℕ) :
    (I × (Fin m × Fin (elementBits * 2)) → Bit) ≃ (Fin m → I → Fin 2 → E) :=
  (Equiv.curry I _ Bit).trans ((Equiv.arrowCongr (Equiv.refl I)
    ((Equiv.curry (Fin m) (Fin (elementBits * 2)) Bit).trans
      (Equiv.arrowCongr (Equiv.refl _) (elementSplit K 2)))).trans (Equiv.piComm _))

/-- The uniform bits of the cells of the rows as the values of the tables at the hidden names. -/
def rowDecode (K : Constants C E) (D : C.Coalition) (count : ℕ) :
    (Fin (Fintype.card (RowIx D count)) → Bit) ≃
      (Fin (RealNetworkV3.checkLabels count) → HiddenTerm D → Fin 2 → E) ×
        (Fin (RealNetworkV3.checkLabels count) → HiddenPair D → Fin 2 → E) ×
          (HiddenTerm D → Fin 256 → Bit) × (HiddenPair D → Fin 256 → Bit) :=
  (Equiv.arrowCongr ((Fintype.equivFin _).symm.trans (rowParts D count)) (Equiv.refl Bit)).trans
    (((Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr (Equiv.sumArrowEquivProdArrow _ _ _)
      (Equiv.sumArrowEquivProdArrow _ _ _))).trans
      ((Equiv.prodCongr (Equiv.prodCongr (rowDecodeE K _ _) (rowDecodeE K _ _))
        (Equiv.prodCongr (Equiv.curry _ _ Bit) (Equiv.curry _ _ Bit))).trans (Equiv.prodAssoc _ _ _)))

theorem rowDecode_term (D : C.Coalition) (count : ℕ) (vals : Fin (Fintype.card (RowIx D count)) → Bit)
    (k : Fin (RealNetworkV3.checkLabels count)) (T : HiddenTerm D) :
    (rowDecode K D count vals).1 k T =
      elementSplit K 2 (fun j => vals (Fintype.equivFin _ (⟨.term T.1, T.2⟩, .inl (k, j)))) := rfl

theorem rowDecode_pair (D : C.Coalition) (count : ℕ) (vals : Fin (Fintype.card (RowIx D count)) → Bit)
    (k : Fin (RealNetworkV3.checkLabels count)) (p : HiddenPair D) :
    (rowDecode K D count vals).2.1 k p =
      elementSplit K 2 (fun j => vals (Fintype.equivFin _ (⟨.pair p.1, p.2⟩, .inl (k, j)))) := rfl

theorem rowDecode_termB (D : C.Coalition) (count : ℕ) (vals : Fin (Fintype.card (RowIx D count)) → Bit)
    (T : HiddenTerm D) (g : Fin 256) :
    (rowDecode K D count vals).2.2.1 T g = vals (Fintype.equivFin _ (⟨.term T.1, T.2⟩, .inr g)) := rfl

theorem rowDecode_pairB (D : C.Coalition) (count : ℕ) (vals : Fin (Fintype.card (RowIx D count)) → Bit)
    (p : HiddenPair D) (g : Fin 256) :
    (rowDecode K D count vals).2.2.2 p g = vals (Fintype.equivFin _ (⟨.pair p.1, p.2⟩, .inr g)) := rfl

/-- The rows of the table with the cells of the rows agree at the hidden names with the decoded
values of the cells. -/
theorem rowTables_rowDecode (D : C.Coalition) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (L count : ℕ) (vals : Fin (Fintype.card (RowIx D count)) → Bit) :
    RealNetworkE1join.HiddenAgree D
      (RealNetworkE1o.rowTables K (cacheFin (rowAddr D term pair L count) vals ∅) term pair L count)
      (hiddenTables D (rowDecode K D count vals).1 (rowDecode K D count vals).2.1
        (rowDecode K D count vals).2.2.1 (rowDecode K D count vals).2.2.2) := by
  refine ⟨fun k T hT => ?_, fun k p hp => ?_, fun T hT => ?_, fun p hp => ?_⟩
  · funext g
    dsimp only [RealNetworkE1o.rowTables, hiddenTables]
    rw [dite_eq_left_of_eq_true (eq_true hT), rowDecode_term, elementSplit_apply]
    exact congrArg K.encode.symm (funext fun e =>
      tableBit_rowE D term pair L count vals ∅ ⟨.term T, hT⟩ k _ (elementPos_two g e))
  · funext g
    dsimp only [RealNetworkE1o.rowTables, hiddenTables]
    rw [dite_eq_left_of_eq_true (eq_true hp), rowDecode_pair, elementSplit_apply]
    exact congrArg K.encode.symm (funext fun e =>
      tableBit_rowE D term pair L count vals ∅ ⟨.pair p, hp⟩ k _ (elementPos_two g e))
  · funext g
    dsimp only [RealNetworkE1o.rowTables, hiddenTables]
    rw [dite_eq_left_of_eq_true (eq_true hT), rowDecode_termB]
    exact tableBit_rowB D term pair L count vals ∅ ⟨.term T, hT⟩ g
  · funext g
    dsimp only [RealNetworkE1o.rowTables, hiddenTables]
    rw [dite_eq_left_of_eq_true (eq_true hp), rowDecode_pairB]
    exact tableBit_rowB D term pair L count vals ∅ ⟨.pair p, hp⟩ g

omit [Algebra Bit E] in
/-- A uniform sample of four parts is the four uniform samples in order. -/
theorem uniform_four_bind {A B Cc Dd β : Type} [SampleableType A] [SampleableType B] [SampleableType Cc]
    [SampleableType Dd] (F : A × B × Cc × Dd → ProbComp β) :
    (($ᵗ (A × B × Cc × Dd)) >>= F) =
      (($ᵗ A) >>= fun a => ($ᵗ B) >>= fun b => ($ᵗ Cc) >>= fun c => ($ᵗ Dd) >>= fun d => F (a, b, c, d)) := by
  simp only [SampleableType.uniformSample_prod_eq_bind, bind_assoc, pure_bind]

/-- The uniform cells of the rows, for a use that reads the tables only at the hidden names, are
uniform values at the hidden names. -/
theorem rowVals_hidden [SampleableType E] (D : C.Coalition) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (L count : ℕ) {β : Type}
    (G : RealNetworkV3.DrawTables C E (RealNetworkV3.checkLabels count) → ProbComp β)
    (hG : ∀ t t', RealNetworkE1join.HiddenAgree D t t' → G t = G t') :
    (($ᵗ (Fin (Fintype.card (RowIx D count)) → Bit)) >>= fun vals =>
        G (RealNetworkE1o.rowTables K (cacheFin (rowAddr D term pair L count) vals ∅) term pair L count)) =ᵈ
      (($ᵗ (Fin (RealNetworkV3.checkLabels count) → HiddenTerm D → Fin 2 → E)) >>= fun hE =>
        ($ᵗ (Fin (RealNetworkV3.checkLabels count) → HiddenPair D → Fin 2 → E)) >>= fun hP =>
        ($ᵗ (HiddenTerm D → Fin 256 → Bit)) >>= fun hB => ($ᵗ (HiddenPair D → Fin 256 → Bit)) >>= fun hPB =>
          G (hiddenTables D hE hP hB hPB)) := by
  have e : (($ᵗ (Fin (Fintype.card (RowIx D count)) → Bit)) >>= fun vals =>
        G (RealNetworkE1o.rowTables K (cacheFin (rowAddr D term pair L count) vals ∅) term pair L count)) =
      ((rowDecode K D count <$> ($ᵗ (Fin (Fintype.card (RowIx D count)) → Bit))) >>= fun h =>
        G (hiddenTables D h.1 h.2.1 h.2.2.1 h.2.2.2)) := by
    rw [bind_map_left]
    exact bind_congr fun vals => hG _ _ (rowTables_rowDecode K D term pair L count vals)
  rw [e]
  refine (EvalDistEq.bind_left
    (SampleableType.map_uniformSample_evalDistEq_of_bijective (rowDecode K D count).bijective) _).trans ?_
  rw [uniform_four_bind]

/-- `RowTablesUniform` holds. -/
theorem rowTablesUniform [SampleableType E] : RowTablesUniform K := by
  intro D term pair L count β G hG
  exact (rowVals_hidden K D term pair L count G hG).trans (drawTables_hidden D _ G hG).symm

/-- The check on drawn values is the right phase of the join, with each operator as its
own input. -/
theorem drawnPhase_eq {Ia : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    {m : ℕ} (tables : RealNetworkV3.DrawTables C E m) (fuel : ℕ) (x : C.Party → List (Tuple C)) (L tg : ℕ)
    (st : A.State) :
    executePhase localRoles D A noFunctionality fuel st (RealNetworkV3.drawnCheckAt K D L tg knownE knownB tables x) =
      pilotOut <$> executePhase localRoles D A noFunctionality fuel st
        (fun i => (some i : Option C.Party).elim failure fun v =>
          RealNetworkE1o.drawnCheckFrom K D L knownE knownB tables i (x v) (pilotStart K x L tg v) >>=
            fun h => pure (v, h)) := by
  refine Eq.trans ?_ (executePhase_map D A noFunctionality fuel st _ _)
  refine executePhase_congr _ _ _ _ _ _ _ fun i _ => ?_
  simp only [Option.elim_some, RealNetworkE1o.drawnCheckAt_eq, map_bind, map_pure, pilotStart]
  rw [map_eq_bind_pure_comp]
  rfl

/-- An equality of two computations is an equality of their laws. -/
theorem evalDistEq_of_eq {α : Type} {mx my : ProbComp α} (h : mx = my) : mx =ᵈ my := h ▸ EvalDistEq.rfl

omit [Field E] [Algebra Bit E] in
/-- `drawTables` under the local oracles is `drawTablesProb`. -/
theorem drawTables_run' [SampleableType E] (m : ℕ) {β : Type}
    (Y : RealNetworkV3.DrawTables C E m → OracleComp (LocalSpec C) β) (s : HashCache C) :
    (simulateQ (localAnswer prims) (RealNetworkV3.drawTables m >>= Y)).run' s =
      drawTablesProb m >>= fun t => (simulateQ (localAnswer prims) (Y t)).run' s := by
  simp only [RealNetworkV3.drawTables, drawTablesProb, bind_assoc, pure_bind, simulateQ_bind, StateT.run'_eq,
    StateT.run_bind, run_liftComp_prob, map_bind, bind_map_left]

/-! ## The step -/

/-- The run in the form of the hybrid step of one check. The known rows of the check under the keys
`pilotTermKey` and `pilotPairKey` are read first from the hash oracle at the cache `cache`. Then `c1Real`
draws the tables and runs the check on drawn values. -/
def pilotDrawn [SampleableType E] (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (prss : C.Party → PrssKeys C) (counts : List ℕ) (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State)
    (cache : HashCache C) : ProbComp (net.State × (C.Party → Option Unit)) :=
  (simulateQ (localAnswer prims)
    (RealNetworkE1o.knownRowsE K D (RealNetworkGP.liveSet D fun i : C.Party => some i) (pilotTermKey D prss)
        (pilotPairKey D prss) L counts.sum >>= fun knownE =>
      RealNetworkE1o.knownRowsB (E := E) D (RealNetworkGP.liveSet D fun i : C.Party => some i)
          (pilotTermKey D prss) (pilotPairKey D prss) L counts.sum >>= fun knownB =>
        RealNetworkC1s.c1Real K D (RealNetworkE1r.checkAdversary net) knownE knownB counts L tg x st)).run' cache

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

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E)

/-! ## The output form of the join -/

/-- The join for the pilot in its output form. From the start cache `cache`, the outputs `pilotOut` of
the real check on one table have the law of the outputs of the check on drawn values with the known
rows read first and the tables `rowTables` of that table. -/
def PilotJoinOut (D : C.Coalition) : Prop :=
  ∀ (net : Adversary C E Unit PEmpty PEmpty) (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C)
    (table : HiddenCache C) (counts : List ℕ) (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State)
    (cache : HashCache C),
    counts.sum ≠ 0 → (∀ i, i ∉ D.1 → (x i).map (·.count) = counts) → PrssKeysAgree D prss →
    (simulateQ (localAnswer prims) (pilotOut <$> RealNetworkE1join.realCheckPhase K D net noFunctionality keys
        table (checkRounds counts.sum) (fun i => some i) x (pilotStart K x L tg) prss st)).run' cache =ᵈ
      (simulateQ (localAnswer prims) (pilotOut <$> RealNetworkE1join.drawnCheckPhase K D net L counts.sum
        (pilotTermKey D prss) (pilotPairKey D prss)
        (RealNetworkE1o.rowTables K table (pilotTermKey D prss) (pilotPairKey D prss) L counts.sum)
        (checkRounds counts.sum) (fun i => some i) x (pilotStart K x L tg) st)).run' cache

/-- The outputs of the pilot on drawn tables, from the premise `PilotJoinOut`. -/
theorem pilotOutputs_drawn_out [SampleableType E] (D : C.Coalition) (hjoin : PilotJoinOut prims K D)
    (net : Adversary C E Unit PEmpty PEmpty) (keys : C.Party → Keys C)
    (prss : C.Party → PrssKeys C) (counts : List ℕ) (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State)
    (cache : HashCache C) (hidden : HiddenCache C) (hpos : counts.sum ≠ 0)
    (hcounts : ∀ i, i ∉ D.1 → (x i).map (·.count) = counts) (hagree : PrssKeysAgree D prss)
    (hfresh : StreamsFresh D L prss hidden) :
    pilotOutputs prims K D net keys prss counts x L tg st cache hidden =ᵈ
      pilotDrawn prims K D net prss counts x L tg st cache := by
  obtain ⟨m, extra, h1⟩ := pilotOutputs_table prims K D net keys prss counts x L tg st cache hidden hfresh
  refine h1.trans ?_
  let Y : RealNetworkV3.DrawTables C E (RealNetworkV3.checkLabels counts.sum) →
      OracleComp (LocalSpec C) (net.State × (C.Party → Option Unit)) := fun t =>
    RealNetworkE1join.drawnCheckPhase K D net L counts.sum (pilotTermKey D prss) (pilotPairKey D prss) t
      (checkRounds counts.sum) (fun i => some i) x (pilotStart K x L tg) st >>= fun r => pure (pilotOut r)
  have hY : ∀ t t', RealNetworkE1join.HiddenAgree D t t' → Y t = Y t' := fun t t' h => by
    simp only [Y]
    rw [RealNetworkE1join.drawnCheckPhase_hidden K D net L counts.sum _ _ t t' h]
  have h2 : ∀ junk vals,
      (simulateQ (localAnswer prims) (executePhase localRoles D net noFunctionality (checkRounds counts.sum) st
        fun i => RealNetworkN3.tableProgram D
          (cacheFin (rowAddr D (pilotTermKey D prss) (pilotPairKey D prss) L counts.sum) vals
            (cacheFin extra junk hidden)) (pilotProgram K keys prss x L tg i))).run' cache =ᵈ
      (simulateQ (localAnswer prims) (Y (RealNetworkE1o.rowTables K
        (cacheFin (rowAddr D (pilotTermKey D prss) (pilotPairKey D prss) L counts.sum) vals ∅)
        (pilotTermKey D prss) (pilotPairKey D prss) L counts.sum))).run' cache := by
    intro junk vals
    rw [pilotPhase_eq,
      ← hY _ _ (rowTables_hiddenAgree K D _ _ L counts.sum vals (cacheFin extra junk hidden))]
    simp only [Y, bind_pure_comp]
    exact hjoin net keys prss _ counts x L tg st cache hpos hcounts hagree
  refine (EvalDistEq.bind_right _ fun junk => EvalDistEq.bind_right _ fun vals => h2 junk vals).trans ?_
  refine (EvalDistEq.bind_const _ _).trans ?_
  refine (rowTablesUniform K D (pilotTermKey D prss) (pilotPairKey D prss) L counts.sum _
    (fun t => (simulateQ (localAnswer prims) (Y t)).run' cache) fun t t' h => by rw [hY t t' h]).trans ?_
  rw [← drawTables_run']
  have h3 := RealNetworkE1join.drawnBranch_c1Real prims K D net counts L tg (pilotTermKey D prss)
    (pilotPairKey D prss) (fun i => some i) x (pilotStart K x L tg) st x (fun r => pure (pilotOut r)) pure
    fun knownE knownB tables => by
      have e := drawnPhase_eq K D (RealNetworkE1r.checkAdversary net) knownE knownB tables
        (checkRounds counts.sum) x L tg st
      exact (congrArg (· >>= pure) e).trans ((bind_pure _).trans (map_eq_bind_pure_comp _ _ _)) ▸
        SameRun.refl prims _
  exact ((h3 cache).map Prod.fst).trans (evalDistEq_of_eq (congrArg
    (fun z => Prod.fst <$> (simulateQ (localAnswer prims) z).run cache)
    (bind_congr fun knownE => bind_congr fun knownB => bind_pure _)))

/-- The accept event of the pilot on drawn tables, from the premise `PilotJoinOut`. -/
theorem pilotAccept_drawn_out [SampleableType E] (D : C.Coalition) (hjoin : PilotJoinOut prims K D)
    (net : Adversary C E Unit PEmpty PEmpty) (keys : C.Party → Keys C)
    (prss : C.Party → PrssKeys C) (counts : List ℕ) (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State)
    (cache : HashCache C) (hidden : HiddenCache C) (hpos : counts.sum ≠ 0)
    (hcounts : ∀ i, i ∉ D.1 → (x i).map (·.count) = counts) (hagree : PrssKeysAgree D prss)
    (hfresh : StreamsFresh D L prss hidden) :
    Pr{let out ← pilotOutputs prims K D net keys prss counts x L tg st cache hidden}[∃ i, i ∉ D.1 ∧
        out.2 i = some ()] =
      Pr{let out ← pilotDrawn prims K D net prss counts x L tg st cache}[∃ i, i ∉ D.1 ∧ out.2 i = some ()] :=
  (pilotOutputs_drawn_out prims K D hjoin net keys prss counts x L tg st cache hidden hpos hcounts hagree
    hfresh).prEvent_eq _

/-! ## The objects of the rows -/

/-- The known rows of the pilot under the keys `pilotTermKey` and `pilotPairKey`, for each honest
receiver. -/
def pilotPrefetch (D : C.Coalition) (prss : C.Party → PrssKeys C) (L count : ℕ) :
    OracleComp (LocalSpec C)
      ((ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) × (Shares C Bit × (C.Party → C.Party → ℕ → Bit))) :=
  RealNetworkE1o.knownRowsE K D (RealNetworkGP.liveSet D fun i : C.Party => some i) (pilotTermKey D prss)
      (pilotPairKey D prss) L count >>= fun knownE =>
    RealNetworkE1o.knownRowsB (E := E) D (RealNetworkGP.liveSet D fun i : C.Party => some i)
        (pilotTermKey D prss) (pilotPairKey D prss) L count >>= fun knownB => pure (knownE, knownB)

/-- The known rows `known` are the values of the prefetch at the cache `s`. A new prefetch from `s`
makes no new cell and returns `known`. -/
def PrefetchAt (D : C.Coalition) (prss : C.Party → PrssKeys C) (L count : ℕ) (s : HashCache C)
    (known : (ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) × (Shares C Bit × (C.Party → C.Party → ℕ → Bit))) :
    Prop :=
  (simulateQ (localAnswer prims) (pilotPrefetch K D prss L count)).run s = pure (known, s)

/-- The local oracles with each stream position whose key has a cell in the cache `s` answered from
that cell. Each other query does not change. -/
def freezeLocal (s : HashCache C) : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C)) := fun t =>
  match t with
  | .inr (.inr x) =>
      match s (.streamKey x.2.1) with
      | some u => pure (prims.aes.eval (truncateHash u) x.2.2)
      | none => (query (spec := LocalSpec C) (.inr (.inr x)) : OracleComp (LocalSpec C) Bit)
  | t => (query (spec := LocalSpec C) t : OracleComp (LocalSpec C) _)

/-- The roles with the map `m` on the local queries of each honest operator. -/
def mapRolesLocal (m : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C))) : Roles C (OracleComp (LocalSpec C)) :=
  ⟨fun oa => oa, fun oa => simulateQ m oa⟩

/-- The map `m` on the local queries of a program. The other queries do not change. -/
def partyMap {ι : Type} {G : OracleSpec ι} (m : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C))) :
    QueryImpl (PartySpec C E G) (OracleComp (PartySpec C E G)) := fun t =>
  match t with
  | .inl (.inl t) => liftComp (m t) (PartySpec C E G)
  | t => (query (spec := PartySpec C E G) t : OracleComp (PartySpec C E G) _)

/-- The program `p` with the map `m` on its local queries. -/
def mapProgram {ι : Type} {G : OracleSpec ι} (m : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C))) {α : Type}
    (p : PartyM C E G α) : PartyM C E G α :=
  OptionT.mk (simulateQ (partyMap m) p.run)

/-- The program `p` with its hidden streams read from the table `table` and its other streams read
from the cells of the cache `s`. -/
def freezeProgram (D : C.Coalition) (s : HashCache C) (table : HiddenCache C) {α : Type}
    (p : PartyM C E RealSpec α) : PartyM C E RealSpec α :=
  mapProgram (freezeLocal prims s) (RealNetworkN3.tableProgram D table p)

/-- The building blocks `B` with `freezeProgram` on each call. -/
def freezeBlocks (D : C.Coalition) (s : HashCache C) (table : HiddenCache C)
    (B : CheckBuildingBlocks C E RealSpec) : CheckBuildingBlocks C E RealSpec where
  coin n := StateT.mk fun st => freezeProgram prims D s table ((B.coin n).run st)
  extendMult products := StateT.mk fun st => freezeProgram prims D s table ((B.extendMult products).run st)
  randElements n := StateT.mk fun st => freezeProgram prims D s table ((B.randElements n).run st)
  randBits n := StateT.mk fun st => freezeProgram prims D s table ((B.randBits n).run st)

/-- The PRSS output `o` at its first `n` positions, with the state after it. -/
def clipRun {R : Type} [Zero R] (n : ℕ) (r : PrssOutput C R × RunState C) : PrssOutput C R × RunState C :=
  (clipOutput n r.1, r.2)

/-- Two families of building blocks agree on the calls that a check of the count `count` from the
label `L` makes. A coin and a call of `extendMult` with two products agree at each offset of the
labels below `checkLabels count` with the stream 1 and 0 of `checkStream`. A draw of two elements
agrees at the first two positions at each offset with the stream 1. A draw of 256 bits agrees at the
first 256 positions at the offset `2 * halvings count + 3`. -/
structure BlocksAgree {ι : Type} {G : OracleSpec ι} (L count : ℕ) (B B' : CheckBuildingBlocks C E G) : Prop where
  coin : ∀ st : RunState C, L ≤ st.label → st.label - L < RealNetworkV3.checkLabels count →
    RealNetworkE1g.checkStream (halvings count) (st.label - L) = 1 → (B.coin 2).run st = (B'.coin 2).run st
  extendMult : ∀ (st : RunState C) (products : List (Product C E)), products.length = 2 → L ≤ st.label →
    st.label - L < RealNetworkV3.checkLabels count → RealNetworkE1g.checkStream (halvings count) (st.label - L) = 0 →
    (B.extendMult products).run st = (B'.extendMult products).run st
  randElements : ∀ st : RunState C, L ≤ st.label → st.label - L < RealNetworkV3.checkLabels count →
    RealNetworkE1g.checkStream (halvings count) (st.label - L) = 1 →
    clipRun 2 <$> (B.randElements 2).run st = clipRun 2 <$> (B'.randElements 2).run st
  randBits : ∀ st : RunState C, st.label = L + (2 * halvings count + 3) →
    clipRun 256 <$> (B.randBits 256).run st = clipRun 256 <$> (B'.randBits 256).run st

/-! ## The rows -/

variable (C E) in
/-- The adversary `checkAdversary net` of a network with no leak runs each phase as `net`. -/
def RowJ1 (D : C.Coalition) : Prop :=
  ∀ (net : Adversary C E Unit PEmpty PEmpty) (fuel : ℕ) (st : net.State) {α : Type}
    (p : C.Party → PartyM C E RealSpec α),
    executePhase localRoles D (RealNetworkE1r.checkAdversary net) noFunctionality fuel st p =
      executePhase localRoles D net noFunctionality fuel st p

/-- At each outcome of the prefetch, with its next cache `r.2`, the known rows are the values
of the prefetch at `r.2`. -/
def RowJ2 (D : C.Coalition) : Prop :=
  ∀ (prss : C.Party → PrssKeys C) (L count : ℕ) (cache : HashCache C),
    ∀ r ∈ support ((simulateQ (localAnswer prims) (pilotPrefetch K D prss L count)).run cache),
      PrefetchAt prims K D prss L count r.2 r.1

/-- Two implementations that agree on each state of an invariant, which the first keeps, give
the same run from each state of the invariant. It is `map_run_simulateQ_eq_of_query_map_eq_inv'` of
VCV-io with the identity projection. -/
def RowJ3 : Prop :=
  ∀ {ι : Type} {spec : OracleSpec ι} {σ α : Type} (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (inv : σ → Prop), (∀ t s, inv s → ∀ y ∈ support ((impl₁ t).run s), inv y.2) →
    (∀ t s, inv s → (impl₁ t).run s = (impl₂ t).run s) →
    ∀ (oa : OracleComp spec α) (s : σ), inv s → (simulateQ impl₁ oa).run s = (simulateQ impl₂ oa).run s

variable (C E) in
/-- A map of the local queries of the honest operators moves from the roles into each honest
program. It is `tablePush` for each map. -/
def RowJ4 (D : C.Coalition) : Prop :=
  ∀ (m : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C))) {O Lk Rk Ia α : Type} (A : Adversary C E Ia Lk Rk)
    (F : Functionality C PEmpty O Lk Rk) (fuel : ℕ) (st : A.State) (p : C.Party → PartyM C E (CallSpec PEmpty O) α),
    executePhase (mapRolesLocal m) D A F fuel st p = executePhase localRoles D A F fuel st fun i => mapProgram m (p i)

/-- From each cache above `s'`, a phase has the law of the phase whose honest stream reads
under a key with a cell in `s'` are answered from that cell. The calls of the adversary do not change.
The next cache is kept. -/
def RowJ5 (D : C.Coalition) : Prop :=
  ∀ {O Lk Rk Ia α : Type} (A : Adversary C E Ia Lk Rk) (F : Functionality C PEmpty O Lk Rk) (fuel : ℕ)
    (st : A.State) (p : C.Party → PartyM C E (CallSpec PEmpty O) α) (s' s : HashCache C), s' ≤ s →
    (simulateQ (localAnswer prims) (executePhase localRoles D A F fuel st p)).run s =ᵈ
      (simulateQ (localAnswer prims) (executePhase (mapRolesLocal (freezeLocal prims s')) D A F fuel st p)).run s

/-- The label range of the check. From a state with the label `L`, the check calls its
building blocks only where `BlocksAgree` compares them. So blocks that agree with the blocks on drawn
values there give the same run, with the same end state. -/
def RowJ6 (D : C.Coalition) : Prop :=
  ∀ (ctx : Context C) (L : ℕ) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) {m : ℕ} (tables : RealNetworkV3.DrawTables C E m)
    (i : C.Party) (B : CheckBuildingBlocks C E RealSpec) (tuples : List (Tuple C)) (rs : RunState C),
    (tuples.map (·.count)).sum ≠ 0 → rs.label = L →
    BlocksAgree L (tuples.map (·.count)).sum B (RealNetworkV3.drawnCheckBuildingBlocks K D L knownE knownB tables i) →
    (check K ctx B tuples).run rs =
      (check K ctx (RealNetworkV3.drawnCheckBuildingBlocks K D L knownE knownB tables i) tuples).run rs

/-- `freezeProgram` of a check is the check on the building blocks with `freezeProgram`. The
body of the check reads no stream. -/
def RowJ7 (D : C.Coalition) : Prop :=
  ∀ (s : HashCache C) (table : HiddenCache C) (ctx : Context C) (B : CheckBuildingBlocks C E RealSpec)
    (tuples : List (Tuple C)) (rs : RunState C),
    freezeProgram prims D s table ((check K ctx B tuples).run rs) =
      (check K ctx (freezeBlocks prims D s table B) tuples).run rs

variable (C E) in
/-- The body of the check reads only the operator of its context. -/
def RowJ8b : Prop :=
  ∀ {ι : Type} {G : OracleSpec ι} (K : Constants C E) (ctx : Context C) (B : CheckBuildingBlocks C E G)
    (tuples : List (Tuple C)), check K ctx B tuples = check K (localContext ctx.self) B tuples

/-- At the known rows of a cache, the real building blocks of an honest operator with
`freezeProgram` agree with the blocks on drawn values with the tables `rowTables`. The outputs of the
two draws agree at the positions that the check reads. -/
def RowJ8 (D : C.Coalition) : Prop :=
  ∀ (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (table : HiddenCache C) (L count : ℕ)
    (s : HashCache C) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (i : C.Party),
    count ≠ 0 → i ∉ D.1 → PrssKeysAgree D prss → PrefetchAt prims K D prss L count s (knownE, knownB) →
    BlocksAgree L count (freezeBlocks prims D s table (realCheckBuildingBlocks K (pilotContext keys prss i)))
      (RealNetworkV3.drawnCheckBuildingBlocks K D L knownE knownB
        (RealNetworkE1o.rowTables K table (pilotTermKey D prss) (pilotPairKey D prss) L count) i)

/-- A prefetch in front of a run with its result unused does not change the law of the result
of the run. -/
def RowJ9 (D : C.Coalition) : Prop :=
  ∀ (prss : C.Party → PrssKeys C) (L count : ℕ) {β : Type} (R : OracleComp (LocalSpec C) β) (cache : HashCache C),
    (simulateQ (localAnswer prims) R).run' cache =ᵈ
      (simulateQ (localAnswer prims) (pilotPrefetch K D prss L count >>= fun _ => R)).run' cache

/-! ## The short rows -/

omit [Field E] [Algebra Bit E] in
/-- `RowJ1` holds. -/
theorem rowJ1 (D : C.Coalition) : RowJ1 C E D := by
  intro net fuel st α p
  obtain ⟨State, start, round, answer⟩ := net
  obtain rfl : answer = fun s l => pure (s, PEmpty.elim l) := funext fun _ => funext fun l => l.elim
  rfl

/-- `RowJ3` holds. -/
theorem rowJ3 : RowJ3 := by
  intro ι spec σ α impl₁ impl₂ inv hinv h oa s hs
  have e := map_run_simulateQ_eq_of_query_map_eq_inv' impl₁ impl₂ inv id hinv
    (fun t s hs => by simpa using h t s hs) oa s hs
  simpa using e

/-- `RowJ8b` holds. -/
theorem rowJ8b : RowJ8b C E := by
  intro ι G K ctx B tuples
  obtain ⟨self, keys, prss⟩ := ctx
  rfl

/-- `RowJ9` holds. It is `unused_run_drop`. -/
theorem rowJ9 (D : C.Coalition) : RowJ9 prims K D := fun prss L count _ R cache =>
  (RealNetworkE1join.unused_run_drop prims (pilotPrefetch K D prss L count) R cache).symm

/-! ## The assembly -/

omit [Field E] [Algebra Bit E] in
/-- The map form of a program commutes with a bind. It is `tableProgram_bind` for each map. -/
theorem mapProgram_bind {ι : Type} {G : OracleSpec ι} (m : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C)))
    {α β : Type} (p : PartyM C E G α) (f : α → PartyM C E G β) :
    mapProgram m (p >>= f) = mapProgram m p >>= fun a => mapProgram m (f a) := by
  unfold mapProgram
  apply OptionT.ext
  simp only [OptionT.run_bind, OptionT.run_mk, Option.elimM, simulateQ_bind]
  refine bind_congr fun o => ?_
  cases o <;> simp only [Option.elim_none, Option.elim_some, simulateQ_pure]

omit [Field E] [Algebra Bit E] in
/-- The map form of a program commutes with a map of the result. -/
theorem mapProgram_map {ι : Type} {G : OracleSpec ι} (m : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C)))
    {α β : Type} (p : PartyM C E G α) (f : α → β) : mapProgram m (f <$> p) = f <$> mapProgram m p := by
  rw [map_eq_bind_pure_comp, mapProgram_bind, map_eq_bind_pure_comp]
  refine bind_congr fun a => ?_
  unfold mapProgram
  apply OptionT.ext
  simp

omit [Field E] [Algebra Bit E] in
/-- `freezeProgram` commutes with a map of the result. -/
theorem freezeProgram_map (D : C.Coalition) (s : HashCache C) (table : HiddenCache C) {α β : Type}
    (p : PartyM C E RealSpec α) (f : α → β) :
    freezeProgram prims D s table (f <$> p) = f <$> freezeProgram prims D s table p := by
  unfold freezeProgram
  rw [tableProgram_map, mapProgram_map]

/-- The rows give `PilotJoinOut`. -/
theorem pilotJoinOut_of_rows (D : C.Coalition) (h2 : RowJ2 prims K D) (h4 : RowJ4 C E D)
    (h5 : RowJ5 (E := E) prims D) (h6 : RowJ6 K D) (h7 : RowJ7 prims K D) (h8 : RowJ8 prims K D) :
    PilotJoinOut prims K D := by
  intro net keys prss table counts x L tg st cache hpos hcounts hagree
  rw [← pilotPhase_eq]
  have hR : pilotOut <$> RealNetworkE1join.drawnCheckPhase K D net L counts.sum
      (pilotTermKey D prss) (pilotPairKey D prss)
      (RealNetworkE1o.rowTables K table (pilotTermKey D prss) (pilotPairKey D prss) L counts.sum)
      (checkRounds counts.sum) (fun i => some i) x (pilotStart K x L tg) st =
      pilotPrefetch K D prss L counts.sum >>= fun r =>
        executePhase localRoles D net noFunctionality (checkRounds counts.sum) st
          (RealNetworkV3.drawnCheckAt K D L tg r.1 r.2
            (RealNetworkE1o.rowTables K table (pilotTermKey D prss) (pilotPairKey D prss) L counts.sum) x) := by
    unfold RealNetworkE1join.drawnCheckPhase pilotPrefetch
    simp only [map_bind, bind_assoc, pure_bind]
    refine bind_congr fun knownE => ?_
    erw [map_bind]
    refine bind_congr fun knownB => ?_
    rw [← rowJ1 D net]
    exact (drawnPhase_eq K D (RealNetworkE1r.checkAdversary net) knownE knownB _ _ x L tg st).symm
  rw [hR]
  refine (rowJ9 prims K D prss L counts.sum _ cache).trans ?_
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine EvalDistEq.bind_congr_of_support _ fun r hr => ?_
  have hp := h2 prss L counts.sum cache r hr
  refine ((h5 net noFunctionality (checkRounds counts.sum) st _ r.2 r.2 le_rfl).map Prod.fst).trans ?_
  rw [h4]
  refine evalDistEq_of_eq (congrArg (fun z => Prod.fst <$> (simulateQ (localAnswer prims) z).run r.2)
    (executePhase_congr _ _ _ _ _ _ _ fun i hi => ?_))
  change freezeProgram prims D r.2 table (pilotProgram K keys prss x L tg i) = _
  unfold pilotProgram RealNetworkV3.drawnCheckAt
  rw [StateT.run'_eq, StateT.run'_eq, freezeProgram_map, h7, rowJ8b]
  congr 1
  have h6' := h6 (localContext i) L r.1.1 r.1.2
    (RealNetworkE1o.rowTables K table (pilotTermKey D prss) (pilotPairKey D prss) L counts.sum) i
    (freezeBlocks prims D r.2 table (realCheckBuildingBlocks K (pilotContext keys prss i))) (x i)
    ⟨filledHistory K i (x i), L, tg⟩
  rw [hcounts i hi] at h6'
  exact h6' hpos rfl (h8 keys prss table L counts.sum r.2 r.1.1 r.1.2 i hpos hi hagree hp)

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
attribute [local irreducible] MonadAttach.support

section Push

/-! The steps below are the steps of `tablePush` with the map `m` in the place of the table. -/

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}
  (m : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C)))

/-- A stopped program with the map `m` in its rest. -/
def Step.mapLocal {α : Type} : Step C E G α → Step C E G α
  | .done out => .done out
  | .wait outbox resume => .wait outbox fun inbox => simulateQ (partyMap m) (resume inbox)
  | .call input resume => .call input fun r => simulateQ (partyMap m) (resume r)

theorem advance_mapLocal {α : Type} (p : OracleComp (PartySpec C E G) (Option α)) :
    advance (simulateQ (partyMap m) p) = Step.mapLocal m <$> simulateQ m (advance p) := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    rcases t with (q | outbox) | input
    · change advance (liftComp (m q) (PartySpec C E G) >>= _) =
        Step.mapLocal m <$> simulateQ m
          (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advance (k r))
      rw [advance_liftComp_bind, simulateQ_bind, simulateQ_spec_query, map_bind]
      exact bind_congr ih
    · rfl
    · rfl

section Step

variable {α : Type}

theorem Step.outbox_mapLocal (s : Step C E G α) : (Step.mapLocal m s).outbox = s.outbox := by
  cases s <;> rfl

theorem Step.delivered_mapLocal (s : Step C E G α) : (Step.mapLocal m s).delivered = s.delivered := by
  rcases s with (_ | _) | _ | _ <;> rfl

theorem Step.callInput_mapLocal (s : Step C E G α) : (Step.mapLocal m s).callInput = s.callInput := by
  cases s <;> rfl

theorem Step.isDone_mapLocal (s : Step C E G α) : (Step.mapLocal m s).isDone = s.isDone := by
  cases s <;> rfl

theorem Step.output_mapLocal (s : Step C E G α) : (Step.mapLocal m s).output = s.output := by
  cases s <;> rfl

end Step

section Rounds

variable (D : C.Coalition) {O L R Ia α : Type}

theorem startSteps_mapLocal (p : C.Party → PartyM C E (CallSpec PEmpty O) α) :
    startSteps localRoles D (fun i => mapProgram m (p i)) =
      (fun steps i => Step.mapLocal m (steps i)) <$> startSteps (mapRolesLocal m) D p := by
  unfold startSteps
  have h : ∀ i : C.Party, (if i ∈ D.1 then pure (Step.done none) else
        localRoles.honest (advance (mapProgram m (p i)).run)) =
      ((if i ∈ D.1 then pure (Step.done none) else (mapRolesLocal m).honest (advance (p i).run)) >>=
        fun s => pure (Step.mapLocal m s)) := by
    intro i
    split_ifs
    · simp [Step.mapLocal]
    · simp only [localRoles, mapRolesLocal, mapProgram, OptionT.run_mk, advance_mapLocal, map_eq_bind_pure_comp]
      rfl
  simp only [h]
  rw [sequenceFin_bind_pure, map_eq_bind_pure_comp]
  rfl

theorem stepRound_mapLocal (A : Adversary C E Ia L R) (F : Functionality C PEmpty O L R) (state : A.State)
    (steps : C.Party → Step C E (CallSpec PEmpty O) α) :
    stepRound localRoles D A F state (fun i => Step.mapLocal m (steps i)) =
      (fun r => (r.1, (fun i => Step.mapLocal m (r.2.1 i)), r.2.2)) <$>
        stepRound (mapRolesLocal m) D A F state steps := by
  have hno : ¬ ∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome := by
    rintro ⟨i, -, h⟩
    obtain ⟨x, -⟩ := Option.isSome_iff_exists.1 h
    exact x.elim
  unfold stepRound
  simp only [Step.callInput_mapLocal, Step.isDone_mapLocal, Step.outbox_mapLocal, Step.delivered_mapLocal]
  rw [ite_eq_right fun h => hno h.1, ite_eq_right fun h => hno h.1]
  simp only [map_bind, map_pure]
  refine bind_congr fun r => ?_
  rw [sequenceFin_map_bind (g := Step.mapLocal m) (k := fun steps' => pure (r.1, steps', r.2))]
  congr 2
  funext j
  cases hs : steps j with
  | done out => simp [Step.mapLocal]
  | wait outbox resume =>
    simp only [Step.mapLocal]
    split_ifs
    · simp [Step.mapLocal]
    · simp only [localRoles, mapRolesLocal, advance_mapLocal]
  | call input resume => simp [Step.mapLocal]

theorem executeRounds_mapLocal (A : Adversary C E Ia L R) (F : Functionality C PEmpty O L R) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec PEmpty O) α),
    executeRounds localRoles D A F fuel state (fun i => Step.mapLocal m (steps i)) =
      executeRounds (mapRolesLocal m) D A F fuel state steps
  | 0, state, steps => by simp [executeRounds, Step.output_mapLocal]
  | fuel + 1, state, steps => by
    simp only [executeRounds, Step.isDone_mapLocal]
    split_ifs
    · simp [Step.output_mapLocal]
    · rw [stepRound_mapLocal, bind_map_left]
      refine bind_congr fun r => ?_
      exact executeRounds_mapLocal A F fuel r.1 r.2.1

end Rounds

end Push

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

omit [Field E] [Algebra Bit E] in
/-- `RowJ4` holds. -/
theorem rowJ4 (D : C.Coalition) : RowJ4 C E D := by
  intro m O L R Ia α A F fuel st p
  unfold executePhase
  rw [startSteps_mapLocal, bind_map_left]
  exact bind_congr fun steps => (executeRounds_mapLocal m D A F fuel st steps).symm

variable (prims : Primitives)

/-- The world with `freezeLocal` on the free copy. The counted copy answers as in `worldAnswer`. -/
def freezeWorld (s' : HashCache C) : QueryImpl (WorldSpec C) (StateT (HashCache C) ProbComp) :=
  (localAnswer (C := C) prims + programAnswer (C := C) : QueryImpl (SimulatorSpec C) _) +
    fun t => simulateQ (localAnswer prims) (freezeLocal prims s' t)

/-- On the world, `freezeWorld` gives the roles of `mapRolesLocal` with `freezeLocal`. -/
theorem mapRoles_freezeWorld (s' : HashCache C) :
    mapRoles (freezeWorld prims s') worldRoles =
      mapRoles (localAnswer prims) (mapRolesLocal (freezeLocal prims s')) := by
  unfold mapRoles
  congr 1
  · funext β oa
    change simulateQ (freezeWorld prims s') (counted (liftComp oa (SimulatorSpec C))) =
      simulateQ (localAnswer prims) oa
    rw [freezeWorld, simulateQ_counted, ← simulateQ_world_adversary' prims oa]
    exact (simulateQ_counted _ _ _).symm
  · funext β oa
    change simulateQ (freezeWorld prims s') (free oa) =
      simulateQ (localAnswer prims) (simulateQ (freezeLocal prims s') oa)
    rw [freezeWorld, simulateQ_free, ← QueryImpl.simulateQ_compose]
    rfl

/-- On each cache above `s'`, each query of the world has the same run under `worldAnswer` and under
`freezeWorld`. -/
theorem worldAnswer_run_eq_freezeWorld (s' s : HashCache C) (hle : s' ≤ s) (t : (WorldSpec C).Domain) :
    (worldAnswer prims t).run s = (freezeWorld prims s' t).run s := by
  rcases t with (t | t) | t
  · rfl
  · rfl
  · change (localAnswer prims t).run s = (simulateQ (localAnswer prims) (freezeLocal prims s' t)).run s
    rcases t with n | q | x
    · exact congrArg (fun z => StateT.run z s) ((simulateQ_query _ _).trans (id_map _)).symm
    · exact congrArg (fun z => StateT.run z s) ((simulateQ_query _ _).trans (id_map _)).symm
    · have hfix : ¬ IsFixed (Query.streamKey (C := C) x.2.1) := by simp [IsFixed]
      rcases h : s' (.streamKey x.2.1) with _ | u
      · have e : freezeLocal prims s' (.inr (.inr x)) = query (spec := LocalSpec C) (.inr (.inr x)) := by
          simp only [freezeLocal, h]
        rw [e]
        exact congrArg (fun z => StateT.run z s) ((simulateQ_query _ _).trans (id_map _)).symm
      · have e : freezeLocal prims s' (.inr (.inr x)) = pure (prims.aes.eval (truncateHash u) x.2.2) := by
          simp only [freezeLocal, h]
        rw [e, simulateQ_pure, StateT.run_pure]
        change (prgAnswer prims x).run s = _
        rw [prgAnswer, StateT.run_bind, hashAnswer_run_cached prims hfix (hle h), pure_bind]
        rfl

omit [Field E] [Algebra Bit E] in
/-- `RowJ5` holds. The two runs are equal. -/
theorem rowJ5 (D : C.Coalition) : RowJ5 (E := E) prims D := by
  intro O Lk Rk Ia α A F fuel st p s' s hle
  refine evalDistEq_of_eq ?_
  have h1 : simulateQ (localAnswer prims) (executePhase localRoles D A F fuel st p) =
      simulateQ (worldAnswer prims) (executePhase worldRoles D A F fuel st p) := by
    rw [simulateQ_executePhase_mapRoles, simulateQ_executePhase_mapRoles, mapRoles_world]
  have h2 : simulateQ (localAnswer prims) (executePhase (mapRolesLocal (freezeLocal prims s')) D A F fuel st p) =
      simulateQ (freezeWorld prims s') (executePhase worldRoles D A F fuel st p) := by
    rw [simulateQ_executePhase_mapRoles, simulateQ_executePhase_mapRoles, mapRoles_freezeWorld]
  rw [h1, h2]
  exact rowJ3 (worldAnswer prims) (freezeWorld prims s') (fun s => s' ≤ s)
    (fun t s hs y hy => hs.trans (grows_worldAnswer prims t s y hy))
    (fun t s hs => worldAnswer_run_eq_freezeWorld prims s' s hs t) _ s hle

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

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-- Each step of `impl` gives its result again from each cache that contains its next cache, and it
keeps that cache. -/
def Replays {κ : Type} {spec : OracleSpec κ} (impl : QueryImpl spec (StateT (HashCache C) ProbComp)) : Prop :=
  ∀ t s, ∀ z ∈ support ((impl t).run s), ∀ s', z.2 ≤ s' → (impl t).run s' = pure (z.1, s')

/-- A run of an implementation that grows the cache and replays each step gives its result again
from each cache that contains its next cache, and it keeps that cache. -/
theorem replay_simulateQ {κ : Type} {spec : OracleSpec κ} {impl : QueryImpl spec (StateT (HashCache C) ProbComp)}
    (hgrow : Grows impl) (hreplay : Replays impl) {α : Type} (oa : OracleComp spec α) :
    ∀ s, ∀ z ∈ support ((simulateQ impl oa).run s), ∀ s', z.2 ≤ s' →
      (simulateQ impl oa).run s' = pure (z.1, s') := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s z hz s' _
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz ⊢
    subst hz
    rfl
  | query_bind t k ih =>
    intro s z hz s' hs'
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hz ⊢
    obtain ⟨p, hp, hz⟩ := hz
    rw [hreplay t s p hp s' ((Grows.simulateQ hgrow (k p.1) p.2 z hz).trans hs'), pure_bind]
    exact ih p.1 p.2 z hz s' hs'

omit [Field E] [Algebra Bit E] in
/-- A query of `H` gives its answer again from each cache that contains its next cache. -/
theorem replays_hashAnswer (prims : Primitives) : Replays (hashAnswer (C := C) prims) := by
  intro q s z hz s' hs'
  by_cases hq : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hq
    rw [hashAnswer_of_isFixed prims hm, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hashAnswer_of_isFixed prims hm, StateT.run_pure, hz]
  · exact hashAnswer_run_cached prims hq (hs' (hashAnswer_cached prims hq s z hz))

omit [Field E] [Algebra Bit E] in
/-- The queries of `H` and `PRG` give their answers again from each cache that contains their next
cache. -/
theorem replays_roAnswer (prims : Primitives) :
    Replays (hashAnswer (C := C) prims + prgAnswer (C := C) prims) := by
  rintro (q | x) s z hz s' hs'
  · exact replays_hashAnswer prims q s z hz s' hs'
  · change (prgAnswer prims x).run s' = _
    change z ∈ support ((prgAnswer prims x).run s) at hz
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at hz ⊢
    obtain ⟨p, hp, rfl⟩ := hz
    rw [replays_hashAnswer prims _ s p hp s' hs', pure_bind]

omit [Field E] [Algebra Bit E] in
/-- The queries of `H` and `PRG` only add cells to the cache. -/
theorem grows_roAnswer (prims : Primitives) : Grows (hashAnswer (C := C) prims + prgAnswer (C := C) prims) := by
  rintro (q | x) s z hz
  · exact grows_hashAnswer prims q s z hz
  · change z ∈ support ((prgAnswer prims x).run s) at hz
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    exact grows_hashAnswer prims _ s p hp

variable (prims : Primitives) (K : Constants C E)

/-- The prefetch from the next cache of a prefetch returns the same rows and keeps the
cache. -/
theorem rowJ2 (D : C.Coalition) : RowJ2 prims K D := by
  intro prss L count cache r hr
  have e : pilotPrefetch K D prss L count = liftComp
      ((fun rows n => rows.getD n (fun _ _ => 0, fun _ _ _ => 0)) <$>
        (List.range (RealNetworkV3.checkLabels count)).mapM (fun n =>
          knownStreams D (RealNetworkGP.liveSet D fun i : C.Party => some i) (elementCodec K)
            (pilotTermKey D prss) (pilotPairKey D prss) (L + n)
            (RealNetworkE1g.checkStream (halvings count) n) 2) >>= fun knownE =>
        knownStreams D (RealNetworkGP.liveSet D fun i : C.Party => some i) (bitCodec (E := E))
            (pilotTermKey D prss) (pilotPairKey D prss) (L + (2 * halvings count + 3)) 2 256 >>= fun knownB =>
          pure (knownE, knownB)) (LocalSpec C) := by
    simp only [pilotPrefetch, RealNetworkE1o.knownRowsE, RealNetworkE1o.knownRowsB, liftComp_bind, liftComp_map,
      liftComp_pure, liftComp_mapM_local]
  unfold PrefetchAt
  rw [e, simulateQ_localAnswer_liftComp] at hr ⊢
  exact replay_simulateQ (grows_roAnswer prims) (replays_roAnswer prims) _ cache r hr r.2 le_rfl

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.rowJ4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.rowJ4

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.rowJ5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.rowJ5
