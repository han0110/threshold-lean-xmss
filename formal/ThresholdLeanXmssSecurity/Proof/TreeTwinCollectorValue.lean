import ThresholdLeanXmssSecurity.Proof.TreeTwinValueLink

/-! # Tuple values retained by collector records

Successful collector outputs exclude abort forwarding. Their actual records
and the common masks yield termwise product agreement and preserve ValueLink.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinCollectorValue
open TreeTwinValueLink TreeTwinSavedSchedule TreeCheckWalkConsistent TreeCheckWalkTranscript
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

theorem colOuts_value (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (sent sent' : C.Party → Mail C E) (i : C.Party) (z : Shares C Bit)
    (out : colOuts K D count rnd v sent sent' i = some z) :
    i ∉ D.1 ∧ z = colZ K i (rnd i).1 (rnd i).2 (v i) count
      (colInbox K D count rnd v sent i)
      (fun k => if k ∈ D.1 then sent' k i else
        colOut2 K k (rnd k).1 (rnd k).2 (v k) count (colInbox K D count rnd v sent k) i) := by
  unfold colOuts at out
  split_ifs at out with first
  dsimp only at out
  split_ifs at out with second
  have hi : i ∉ D.1 := fun h => first (Or.inl h)
  have clear : ∀ k, k ∉ D.1 → anyAbort (colInbox K D count rnd v sent k) ≠ true := by
    intro k hk aborted
    apply second
    -- The finite abort witness is the collector-transcript argument of TreeSim:4842.
    unfold anyAbort
    rw [List.any_eq_true]
    refine ⟨k, by simp [Committee.parties], ?_⟩
    unfold anyAbort at aborted
    dsimp only
    rw [if_neg hk, if_pos aborted]
    rfl
  refine ⟨hi, ?_⟩
  have value := (Option.some.inj out).symm
  rw [value]
  congr 1
  funext k
  by_cases hk : k ∈ D.1
  · simp only [if_pos hk]
  · simp only [if_neg hk, if_neg (clear k hk)]

theorem collectorRecorded_some (count : ℕ) (st : C.Party → RunState C)
    (i : C.Party) (o : Option (Shares C Bit)) (x : Shares C Bit × RunState C)
    (out : treeSimCollectorRecorded K count st i o = some x) :
    o = some x.1 ∧ x.2.history = recordMode K .collector i (st i).history x.1 count := by
  cases o with
  | none => simp [treeSimCollectorRecorded] at out
  | some z =>
    simp only [treeSimCollectorRecorded, Option.map_some, Option.some.injEq] at out
    subst x
    exact ⟨rfl, rfl⟩

theorem collectorOutputs_agree (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C) (sent sent' : C.Party → Mail C E)
    (x : C.Party → Shares C Bit × RunState C)
    (out : ∀ i, i ∉ D.1 → treeSimCollectorRecorded K count st i
      (colOuts K D count rnd v sent sent' i) = some (x i))
    (masks : MaskAgree D count rnd) (hist : AllHistory D (fun i => (x i).2)) :
    AllHistory D st ∧ ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (x i).1 T = (x j).1 T := by
  have recorded i hi := collectorRecorded_some K count st i _ (x i) (out i hi)
  have value i hi := (colOuts_value K D count rnd v sent sent' i (x i).1 (recorded i hi).1).2
  have records := allHistory_of_records K D .collector count st (fun i => (x i).2)
    (fun i => (x i).1) (fun i hi => (recorded i hi).2) hist
  refine ⟨records.1, zAgree_full K D .collector count (fun i => (x i).1) ?_ records.2 ?_⟩
  · intro T i j heldI heldJ hi hj g hg unfilled
    change (x i).1 T g = (x j).1 T g
    rw [value i hi, value j hj]
    exact collector_agree K D localContext (fun _ _ => rfl) rnd v count sent sent' masks
      T i j heldI heldJ hi hj g hg unfilled
  · intro i hi T g hg
    rw [value i hi]
    simp only [colZ, show i ∉ C.holders T ∨ count ≤ g from Or.inr hg, if_true]

theorem valueLink_collectorLayer (D : C.Coalition) (jobs : List Circuit) (layer : ℕ)
    (p : C.Party → MainInput C × List (Tuple C)) (st : C.Party → RunState C)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (sent sent' : C.Party → Mail C E) (x : C.Party → Shares C Bit × RunState C)
    (out : ∀ i, i ∉ D.1 → treeSimCollectorRecorded K (gatesAt jobs layer).length st i
      (colOuts K D (gatesAt jobs layer).length rnd v sent sent' i) = some (x i))
    (masks : MaskAgree D (gatesAt jobs layer).length rnd)
    (values : ValueLink D p st) (shape : TupleShape D p) :
    let p' := fun i => (appendLayer jobs layer (p i).1 (x i).1,
      (p i).2 ++ [⟨layerX K jobs layer (p i).1, layerY K jobs layer (p i).1,
        (x i).1, (gatesAt jobs layer).length, .collector⟩])
    ValueLink D p' (fun i => (x i).2) ∧ TupleShape D p' := by
  dsimp only
  refine ⟨?_, entryCounts_append D _ shape _ _ _ _ _⟩
  intro hist
  have outputs := collectorOutputs_agree K D _ rnd v st sent sent' x out masks hist
  have old := values outputs.1
  refine ⟨appendLayer_wireAgree D jobs layer _ _ old.1 outputs.2,
    entryTuplesAgree_append D _ shape old.2 _ _ _ _ _ ?_⟩
  intro T i j hi hj heldI heldJ
  exact ⟨TreeCheckWalkConsistent.layerX_congr K jobs layer T (old.1 T i j hi hj heldI heldJ),
    TreeCheckWalkConsistent.layerY_congr K jobs layer T (old.1 T i j hi hj heldI heldJ),
    outputs.2 T i j hi hj heldI heldJ⟩

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinCollectorValue.colOuts_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms colOuts_value

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinCollectorValue.collectorRecorded_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collectorRecorded_some

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinCollectorValue.collectorOutputs_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collectorOutputs_agree

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinCollectorValue.valueLink_collectorLayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms valueLink_collectorLayer

end ThresholdLeanXmssSecurity.TreeTwinCollectorValue
