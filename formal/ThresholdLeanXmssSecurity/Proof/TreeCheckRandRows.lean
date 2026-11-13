import ThresholdLeanXmssSecurity.Proof.TreeCheckKernelCoupling
import ThresholdLeanXmssSecurity.Proof.Check

/-! # Named random rows and the exact gadget observations
Uniform term and pair tables come from one named table. The field-row
identification is restricted to positions below the requested count; no
property of the codec's padding value is assumed.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckRandRows
open TreeCheckWalkRecipe TreeCheckWalkTransport
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E R α : Type} {count : ℕ}

def termTable (vals : KeyName C → Fin count → R) (T : C.Term) := vals (.term T)
def pairTable (vals : KeyName C → Fin count → R) (p : C.Pair) := vals (.pair p)

def derivedKey (D : C.Coalition) (prss : C.Party → PrssKeys C)
    (cache0 : HashCache C) (name : KeyName C) : HashOutput :=
  (cache0 (.streamKey (streamKey D prss name))).getD 0

-- Verbatim port of KeygenHalves.uniformSample_prod_bind: no keygen import.
private theorem uniformSample_prod_bind {α β γ : Type} [SampleableType α] [SampleableType β]
    (f : α × β → ProbComp γ) :
    ($ᵗ (α × β)) >>= f = ($ᵗ α) >>= fun a => ($ᵗ β) >>= fun b => f (a, b) := by
  change ((·, ·) <$> ($ᵗ α) <*> ($ᵗ β)) >>= f = _
  simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]

/-- The term and pair coordinates of one uniform named table are independent. -/
theorem evalDist_keyName_tables [Finite R] [Nonempty R] [SampleableType R] (count : ℕ) :
    𝒟[(fun vals : KeyName C → Fin count → R => (termTable vals, pairTable vals)) <$>
      ($ᵗ (KeyName C → Fin count → R))] =
    𝒟[(do
      let terms ← $ᵗ (C.Term → Fin count → R)
      let pairs ← $ᵗ (C.Pair → Fin count → R)
      pure (terms, pairs))] := by
  let inject : C.Term ⊕ C.Pair → KeyName C := fun
    | .inl T => .term T
    | .inr p => .pair p
  have hi : Function.Injective inject := by
    intro a b h
    cases a <;> cases b <;> simp_all [inject]
  let e : ((C.Term ⊕ C.Pair) → Fin count → R) ≃
      (C.Term → Fin count → R) × (C.Pair → Fin count → R) :=
    Equiv.sumArrowEquivProdArrow C.Term C.Pair (Fin count → R)
  have restrict := evalDist_uniformSample_map_comp_injective (R := Fin count → R) hi
  rw [bind_pure_comp] at restrict
  calc
    _ = 𝒟[e <$> ((fun vals : KeyName C → Fin count → R => vals ∘ inject) <$>
        ($ᵗ (KeyName C → Fin count → R)))] := by
      simp only [Functor.map_map]
      rfl
    _ = 𝒟[e <$> ($ᵗ ((C.Term ⊕ C.Pair) → Fin count → R))] := by
      rw [evalDist_map, restrict, ← evalDist_map]
    _ = 𝒟[$ᵗ ((C.Term → Fin count → R) × (C.Pair → Fin count → R))] :=
      evalDist_map_bijective_uniform_cross (α := (C.Term ⊕ C.Pair) → Fin count → R) e e.bijective
    _ = _ := by
      have h := uniformSample_prod_bind
        (f := fun p : (C.Term → Fin count → R) × (C.Pair → Fin count → R) => pure p)
      simpa only [bind_pure] using congrArg evalDist h

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)

/-- Visible rows are unchanged, and hidden field padding is irrelevant below count. -/
theorem prssRows_frandShare_below (prss : C.Party → PrssKeys C) (cache0 : HashCache C)
    (label idx count : ℕ) (vals : KeyName C → Fin count → E)
    (i : C.Party) (honest : i ∉ D.1) (g : ℕ) (below : g < count) :
    (∀ T, (treeSimCheckPrssRows prims K D (derivedKey D prss cache0) label idx count vals i).1 T g =
      (frandShare D count (knownRows D (fieldRow prims K D prss cache0 label idx count)).1
        (knownRows D (fieldRow prims K D prss cache0 label idx count)).2
        (termTable vals) (pairTable vals) i).1 T g) ∧
    (∀ j, (treeSimCheckPrssRows prims K D (derivedKey D prss cache0) label idx count vals i).2 j g =
      (frandShare D count (knownRows D (fieldRow prims K D prss cache0 label idx count)).1
        (knownRows D (fieldRow prims K D prss cache0 label idx count)).2
        (termTable vals) (pairTable vals) i).2 j g) := by
  constructor
  · intro T
    by_cases held : i ∈ C.holders T
    · by_cases known : KnownTo D.1 T <;>
        simp [treeSimCheckPrssRows, treeSimCheckPrssRow, Hidden, frandShare, knownRows,
          held, known, treeSimCheckFieldPad, below, termTable, fieldRow, derivedKey]
    · simp [treeSimCheckPrssRows, frandShare, held]
  · intro j
    by_cases same : i = j
    · subst j
      simp [treeSimCheckPrssRows, frandShare]
    · by_cases corrupt : j ∈ D.1
      · have visible := pair_visible D i j same corrupt
        simp [treeSimCheckPrssRows, treeSimCheckPrssRow, frandShare, knownRows,
          same, Ne.symm same, corrupt, visible, fieldRow, derivedKey]
      · have hidden : Hidden D (.pair (C.pairOf i j same)) := by
          unfold Hidden Committee.pairOf
          split_ifs <;> exact ⟨by assumption, by assumption⟩
        simp [treeSimCheckPrssRows, treeSimCheckPrssRow, frandShare, knownRows,
          same, Ne.symm same, corrupt, hidden, treeSimCheckFieldPad, below, pairTable]

/-- Conversion observes only the requested share position. -/
theorem conv_below (ctx : Context C) (x y : Shares C E)
    (agree : ∀ T g, g < count → x T g = y T g) (g : ℕ) (below : g < count) :
    conv K ctx x g = conv K ctx y g := by
  simp only [conv, agree _ _ below]

private theorem openOut_below (i : C.Party) (v w : ℕ → E)
    (agree : ∀ g < count, v g = w g) : openOut i v count = openOut i w count := by
  unfold openOut
  rw [vector_congr' count v w agree]

private theorem openShareN_below (i j : C.Party) (v w : ℕ → E) (inbox : Mail C E)
    (agree : ∀ g < count, v g = w g) (g : ℕ) (below : g < count) :
    openShareN i v inbox j g = openShareN i w inbox j g := by
  simp only [openShareN, agree g below]

private theorem openAgreesN_below (i : C.Party) (v w : ℕ → E) (inbox : Mail C E)
    (agree : ∀ g < count, v g = w g) :
    OpenAgreesN K i v count inbox ↔ OpenAgreesN K i w count inbox := by
  unfold OpenAgreesN
  apply forall_congr'
  intro j
  apply forall_congr'
  intro g
  apply forall_congr'
  intro below
  simp only [openShareN_below i _ v w inbox agree g below]

private theorem openValueN_vector_below (i : C.Party) (v w : ℕ → E)
    (inbox : Mail C E) (agree : ∀ g < count, v g = w g) :
    vector count (openValueN K i v inbox) = vector count (openValueN K i w inbox) := by
  apply vector_congr'
  intro g below
  simp only [openValueN, openShareN_below i _ v w inbox agree g below]

/-- Coin messages contain only the requested conversion positions. -/
theorem coinOut_below (i : C.Party) (x y : PrssOutput C E)
    (agree : ∀ T g, g < count → x.1 T g = y.1 T g) :
    coinOut K i count x = coinOut K i count y := by
  exact openOut_below i _ _ (conv_below K (localContext i) x.1 y.1 agree)

/-- Only the bounded vector of an opening is observed; its padded function need not agree. -/
theorem coinRes_below (i : C.Party) (x y : PrssOutput C E) (inbox : Mail C E)
    (agree : ∀ T g, g < count → x.1 T g = y.1 T g) :
    coinRes K i count x inbox = coinRes K i count y inbox := by
  have hc := conv_below K (localContext i) x.1 y.1 agree
  have ha := propext (openAgreesN_below K i _ _ inbox hc)
  have hv := openValueN_vector_below K i _ _ inbox hc
  unfold coinRes
  split
  · rfl
  · change (if OpenAgreesN K i (conv K (localContext i) x.1) count inbox then
        some (openValueN K i (conv K (localContext i) x.1) inbox) else none).map (vector count) =
      (if OpenAgreesN K i (conv K (localContext i) y.1) count inbox then
        some (openValueN K i (conv K (localContext i) y.1) inbox) else none).map (vector count)
    rw [ha]
    split <;> simp only [Option.map_some, Option.map_none, hv]

/-- The complete waiting step observes the same bounded opening and messages. -/
theorem treeSimCoinStep_below (ctx : Context C) (x y : PrssOutput C E)
    (st : RunState C) (k : List E × RunState C → PartyM C E RealSpec α)
    (agree : ∀ T g, g < count → x.1 T g = y.1 T g) :
    treeSimCoinStep K ctx x count st k = treeSimCoinStep K ctx y count st k := by
  have hc := conv_below K ctx x.1 y.1 agree
  dsimp only [treeSimCoinStep]
  rw [openOut_below ctx.self _ _ hc]
  congr 1
  apply congrArg exchangeResume
  funext inbox
  rw [propext (openAgreesN_below K ctx.self _ _ inbox hc),
    openValueN_vector_below K ctx.self _ _ inbox hc]

private theorem reshareU_below [Field R] (ctx : Context C) (x y : PrssOutput C R)
    (v w : ℕ → R) (rows : ∀ T g, g < count → x.1 T g = y.1 T g)
    (pairs : ∀ j g, g < count → x.2 j g = y.2 j g)
    (values : ∀ g < count, v g = w g) (g : ℕ) (below : g < count) :
    reshareU K ctx x.1 x.2 v g = reshareU K ctx y.1 y.2 w g := by
  simp only [reshareU, rows _ _ below, pairs _ _ below, values g below]

/-- Reshare messages depend only on positions below the requested count. -/
theorem reshareOut_below [Field R] (ctx : Context C) (codec : Codec C E R)
    (x y : PrssOutput C R) (v w : ℕ → R)
    (rows : ∀ T g, g < count → x.1 T g = y.1 T g)
    (pairs : ∀ j g, g < count → x.2 j g = y.2 j g)
    (values : ∀ g < count, v g = w g) :
    reshareOut K ctx codec x.1 x.2 v count = reshareOut K ctx codec y.1 y.2 w count := by
  unfold reshareOut
  rw [vector_congr' count _ _ (reshareU_below K ctx x y v w rows pairs values)]

/-- Reshare explicitly zeros positions above count, so the complete output agrees. -/
theorem reshareZ_below [Field R] (ctx : Context C) (codec : Codec C E R)
    (x y : PrssOutput C R) (v w : ℕ → R) (inbox : Mail C E)
    (rows : ∀ T g, g < count → x.1 T g = y.1 T g)
    (pairs : ∀ j g, g < count → x.2 j g = y.2 j g)
    (values : ∀ g < count, v g = w g) :
    reshareZ K ctx codec x.1 x.2 v count inbox =
      reshareZ K ctx codec y.1 y.2 w count inbox := by
  funext T g
  by_cases below : g < count
  · simp only [reshareZ, rows T g below,
      reshareU_below K ctx x y v w rows pairs values g below]
  · simp [reshareZ, Nat.le_of_not_gt below]

/-- A retained derived-key cell fixes its complete deterministic field row. -/
theorem fieldRow_extend (prss : C.Party → PrssKeys C) (cache0 h : HashCache C)
    (grow : cache0 ≤ h) (name : KeyName C) (key : HashOutput)
    (cached : cache0 (.streamKey (streamKey D prss name)) = some key)
    (label idx count : ℕ) :
    fieldRow prims K D prss h label idx count name =
      fieldRow prims K D prss cache0 label idx count name := by
  funext g
  simp only [fieldRow, grow cached, cached]

/-- The same retained cell fixes the padded bit row. -/
theorem bitRow_extend (prss : C.Party → PrssKeys C) (cache0 h : HashCache C)
    (grow : cache0 ≤ h) (name : KeyName C) (key : HashOutput)
    (cached : cache0 (.streamKey (streamKey D prss name)) = some key)
    (label idx count : ℕ) :
    bitRow prims D prss h label idx count name =
      bitRow prims D prss cache0 label idx count name := by
  funext g
  simp only [bitRow, grow cached, cached]

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckRandRows.evalDist_keyName_tables' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms evalDist_keyName_tables

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckRandRows.prssRows_frandShare_below' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms prssRows_frandShare_below

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckRandRows.coinRes_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coinRes_below

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckRandRows.treeSimCoinStep_below' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms treeSimCoinStep_below

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckRandRows.reshareZ_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reshareZ_below

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckRandRows.fieldRow_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fieldRow_extend

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckRandRows.bitRow_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bitRow_extend

end ThresholdLeanXmssSecurity.TreeCheckRandRows
