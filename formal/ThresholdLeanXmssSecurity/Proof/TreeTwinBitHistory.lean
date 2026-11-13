import ThresholdLeanXmssSecurity.Proof.TreeTwinCollectorValue

/-! # Common histories of actual bit records

Live honest holders of the distinguished hidden term retain one history through
peer and collector records and through the first check coin after Rerand.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinBitHistory
open TreeTwinLinked2 TreeTwinSavedSchedule TreeTwinHistoryRecords TreeTwinValueLink
  TreeTwinCollectorValue
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

theorem commonHistory_antitone (D : C.Coalition) (live live' : C.Party → Bool)
    (st : C.Party → RunState C)
    (sub : ∀ i, i ∉ D.1 → live' i = true → live i = true)
    (hist : CommonHistory D live st) : CommonHistory D live' st := by
  intro T ht i j hi hj li lj hit hjt
  exact hist T ht i j hi hj (sub i hi li) (sub j hj lj) hit hjt

theorem commonHistory_peerRecords {α : Type} (D : C.Coalition)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (count : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (live live' : C.Party → Bool)
    (x : C.Party → Shares C Bit × RunState C)
    (sub : ∀ i, i ∉ D.1 → live' i = true → live i = true)
    (out : ∀ i, i ∉ D.1 → live' i = true →
      treeSimPeerOutputs K D ctx count rnd v st k sent i = some (x i))
    (hist : CommonHistory D live st) :
    CommonHistory D live' (fun i => (x i).2) := by
  intro T ht i j hi hj li lj hit hjt
  rw [peerOutputs_history K D ctx count rnd v st k sent i (x i) (out i hi li),
    peerOutputs_history K D ctx count rnd v st k sent j (x j) (out j hj lj),
    self i hi, self j hj, recordPeer_bit_eq, recordPeer_bit_eq,
    recordMode_eq_append K .peer i _ _ count T hit,
    recordMode_eq_append K .peer j _ _ count T hjt,
    commonHistory_antitone D live live' st sub hist T ht i j hi hj li lj hit hjt]
  congr 1
  apply List.map_congr_left
  intro g hg
  have hgcount := List.mem_range.mp (List.mem_filter.mp hg).1
  have filled : T ∈ filledTerms K := by
    by_contra hf
    have hsome := (List.mem_filter.mp hg).2
    simp [filler_none K T hf g] at hsome
  have honest (l : C.Party) (hl : K.filled l = T) : l ∉ D.1 := by
    intro corrupt
    exact lackedTerm_unknown D T ht ⟨l, corrupt, hl ▸ K.filled_held l⟩
  rw [peerOutputs_value K D ctx count rnd v st k sent i hi (x i) (out i hi li),
    peerOutputs_value K D ctx count rnd v st k sent j hj (x j) (out j hj lj),
    treeSim_reshareZ_value K D ctx self rnd v count sent i hi,
    treeSim_reshareZ_value K D ctx self rnd v count sent j hj]
  simp only [hit, hjt, not_true_eq_false, Nat.not_le.mpr hgcount, or_self, if_false,
    treeSimPeerValue, if_pos filled]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [if_neg (honest l (Finset.mem_filter.mp hl).2)]

theorem commonHistory_collectorRecords (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C) (sent sent' : C.Party → Mail C E)
    (live live' : C.Party → Bool) (x : C.Party → Shares C Bit × RunState C)
    (sub : ∀ i, i ∉ D.1 → live' i = true → live i = true)
    (out : ∀ i, i ∉ D.1 → live' i = true → treeSimCollectorRecorded K count st i
      (colOuts K D count rnd v sent sent' i) = some (x i))
    (hist : CommonHistory D live st) :
    CommonHistory D live' (fun i => (x i).2) := by
  intro T ht i j hi hj li lj hit hjt
  have ei := collectorRecorded_some K count st i _ (x i) (out i hi li)
  have ej := collectorRecorded_some K count st j _ (x j) (out j hj lj)
  rw [ei.2, ej.2, recordMode_eq_append K .collector i _ _ count T hit,
    recordMode_eq_append K .collector j _ _ count T hjt,
    commonHistory_antitone D live live' st sub hist T ht i j hi hj li lj hit hjt]
  congr 1
  apply List.map_congr_left
  intro g hg
  have hgcount := List.mem_range.mp (List.mem_filter.mp hg).1
  have filled : (K.collector g).1 = T := by
    have hsome := (List.mem_filter.mp hg).2
    simpa only [filler, Option.isSome_ite, Option.isSome_some, Option.isSome_none,
      Bool.ite_eq_true_distrib, Bool.true_eq, Bool.false_eq_true, and_true, and_false,
      or_false] using hsome
  have honest : (K.collector g).2 ∉ D.1 := by
    intro corrupt
    exact lackedTerm_unknown D T ht
      ⟨(K.collector g).2, corrupt, filled ▸ K.collector_held g⟩
  rw [(colOuts_value K D count rnd v sent sent' i (x i).1 ei.1).2,
    (colOuts_value K D count rnd v sent sent' j (x j).1 ej.1).2]
  have vi := treeSim_colZ_value K D count rnd v sent sent' (fun _ => false)
    (fun _ _ => rfl) i hi T hit g hgcount
  have vj := treeSim_colZ_value K D count rnd v sent sent' (fun _ => false)
    (fun _ _ => rfl) j hj T hjt g hgcount
  simp only [Bool.false_eq_true, if_false, if_pos filled.symm, if_neg honest] at vi vj
  exact vi.trans vj.symm

theorem commonHistory_rerandCoin (D : C.Coalition) (d : TreeSimPeerData K D)
    (tail : TreeStagesRerandTail K D d)
    (keys : ∀ i, i ∉ D.1 → (d.ctx₁ i).prss = (d.ctx₂ i).prss)
    (verify₁ : ∀ i, i ∉ D.1 → (tail.gadgets₁ i).verify =
      check K (d.ctx₁ i) (realCheckGadgets K (d.ctx₁ i)))
    (verify₂ : ∀ i, i ∉ D.1 → (tail.gadgets₂ i).verify =
      check K (d.ctx₂ i) (realCheckGadgets K (d.ctx₂ i)))
    (nonzero₁ : ∀ i, i ∉ D.1 →
      ((tail.p₁ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0)
    (nonzero₂ : ∀ i, i ∉ D.1 →
      ((tail.p₂ i).2.map (·.count)).sum + (outputsOf tail.circs).length ≠ 0)
    (sent : C.Party → Mail C E) (live : C.Party → Bool)
    (sub : ∀ i, i ∉ D.1 →
      (tail.coinNext K D d keys verify₁ verify₂ nonzero₁ nonzero₂ sent).live i = true →
      live i = true)
    (hist₁ : CommonHistory D live d.st₁) (hist₂ : CommonHistory D live d.st₂) :
    let n := tail.coinNext K D d keys verify₁ verify₂ nonzero₁ nonzero₂ sent
    CommonHistory D n.live n.st₁ ∧ CommonHistory D n.live n.st₂ := by
  dsimp only
  let n := tail.coinNext K D d keys verify₁ verify₂ nonzero₁ nonzero₂ sent
  constructor
  · change CommonHistory D n.live (fun i => (n.x₁ i).2)
    apply commonHistory_peerRecords K D d.ctx₁ d.self₁ d.count d.rnd₁ d.v₁ d.st₁
      d.k₁ sent live n.live n.x₁ sub _ hist₁
    intro i hi hl
    simpa only [if_neg hi, hl, ↓reduceIte] using n.shape₁ i
  · change CommonHistory D n.live (fun i => (n.x₂ i).2)
    apply commonHistory_peerRecords K D d.ctx₂ d.self₂ d.count d.rnd₂ d.v₂ d.st₂
      d.k₂ sent live n.live n.x₂ sub _ hist₂
    intro i hi hl
    simpa only [if_neg hi, hl, ↓reduceIte] using n.shape₂ i

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBitHistory.commonHistory_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms commonHistory_antitone

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBitHistory.commonHistory_peerRecords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms commonHistory_peerRecords

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBitHistory.commonHistory_collectorRecords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms commonHistory_collectorRecords

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinBitHistory.commonHistory_rerandCoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms commonHistory_rerandCoin

end ThresholdLeanXmssSecurity.TreeTwinBitHistory
