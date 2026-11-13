import ThresholdLeanXmssSecurity.Proof.TreeCheckGadgetExtend

/-! # The final mask after a shared hash prefix

`coupled_finalMask_prefix` factors the challenge's hash prefix before the
actual two mask draws and their peer exchange. Both sampled blocks remain
in the hidden cache used by the continuation. The first mask is observed
only through its scalar conversions at positions zero and one.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckGadgetMaskPrefix
open TreeCheckKernelCoupling TreeCheckWalkRecipe TreeCheckWalkCoupling
open TreeCheckGadgetBlocks TreeCheckGadgetPass TreeCheckRandRows
attribute [local instance] Classical.propDecidable inhabitedField
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)
variable (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (x : C.Party → Keys C) (prss : C.Party → PrssKeys C) (cache0 : HashCache C) (label0 : ℕ)
local instance : SampleableType E := SampleableType.ofFintype E

/-- The hybrid mask draw suspends before running its arbitrary continuation. -/
theorem randElements_pure (i : C.Party) (st : RunState C)
    (k : PrssOutput C E → RunM C E (CheckSpec C E) Unit) :
    ∃ step, advance (((hybridCheckGadgets K i).randElements 2 >>= k).run' st).run = pure step := by
  rw [randElements_run', advance_call_bind]
  exact ⟨_,rfl⟩

set_option maxHeartbeats 1000000 in
/-- Two retained field blocks allow the actual mask program's hash prefix to be factored out. -/
theorem realRun_mask_prefix {X β : Type} [Inhabited X]
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (terms : ∀ i, i ∉ D.1 → ∀ T, (ctx i).self ∈ C.holders T →
      (ctx i).prss.term T = streamKey D prss (.term T))
    (pairs : ∀ i, i ∉ D.1 → ∀ j (hj : j ≠ (ctx i).self),
      (ctx i).prss.pair j = streamKey D prss (.pair (C.pairOf (ctx i).self j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (label n : ℕ) (stA : A.State)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X) (live : C.Party → X → Prop)
    (products : C.Party → X → E → E → List (Product C E))
    (width : ∀ i, i ∉ D.1 → ∀ a wa wb, (products i a wa wb).length = 2)
    (st : C.Party → X → RunState C) (labels : ∀ i, i ∉ D.1 → ∀ a, (st i a).label = label)
    (kR : C.Party → X → E → E → Shares C E × RunState C → PartyM C E RealSpec β)
    (h : HashCache C) (c : HiddenCache C) (grow : cache0 ≤ h) (fresh : TreeSimFutureEmpty label c) :
    𝒟[realRun prims D A n stA
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= fun a => if live i a then
        TreeCheckGadgetExtend.maskProgram K (ctx i) (st i a) (products i a) (kR i a) else failure) (h,c)] =
    𝒟[(simulateQ (localAnswer prims) (hashPrefix D W)).run h >>= fun r =>
      realRun prims D A n stA (fun i => let a := (r.1 i).getD default
        if live i a then TreeCheckGadgetExtend.maskProgram K (ctx i) (st i a) (products i a) (kR i a)
        else failure) (r.2,c)] := by
  let P := fun i a => if live i a then
    TreeCheckGadgetExtend.maskProgram K (ctx i) (st i a) (products i a) (kR i a) else failure
  let known := knownRows D (fieldRow prims K D prss cache0 label 1 2)
  let inst := fun vals => treeSimCheckPrssCache K D (streamKey D prss) label 1 2 vals c
  let rnd := fun vals => frandShare D 2 known.1 known.2 (termTable vals) (pairTable vals)
  let wa := fun vals i => conv K (localContext i) (rnd vals i).1 0
  let wb := fun vals i => conv K (localContext i) (rnd vals i).1 1
  let Q := fun vals i a => if live i a then
    ((realCheckGadgets K (ctx i)).extendMult (products i a (wa vals i) (wb vals i))).run
      (nextLabel (st i a)) >>= kR i a (wa vals i) (wb vals i) else failure
  have same : ∀ vals i, i ∉ D.1 → ∀ a s, cache0 ≤ s.1 → inst vals ≤ s.2 →
      (simulateQ (streamWorld prims D) (worldRoles.honest (advance (P i a).run))).run s =
      (simulateQ (streamWorld prims D) (worldRoles.honest (advance (Q vals i a).run))).run s := by
    intro vals i hi a s hg hc
    by_cases hl : live i a
    · simp only [P,Q,if_pos hl]
      exact TreeCheckGadgetExtend.mask_pass prims K D prss cache0 (ctx i) i hi (self i hi)
        (terms i hi) (pairs i hi) cached label vals (st i a) (labels i hi a) (products i a) (kR i a)
        s.1 c s.2 hg hc
    · simp only [P,Q,if_neg hl]
  have factor : ∀ vals,
      𝒟[realRun prims D A n stA (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= Q vals i) (h,inst vals)] =
      𝒟[(simulateQ (localAnswer prims) (hashPrefix D W)).run h >>= fun r =>
        realRun prims D A n stA (fun i => Q vals i ((r.1 i).getD default)) (r.2,inst vals)] := by
    intro vals
    let known₂ := knownRows D (fieldRow prims K D prss cache0 (label+1) 0 2)
    let R := fun vals₂ i a => if live i a then TreeCheckGadgetExtend.peerProgram K i
      (frandShare D 2 known₂.1 known₂.2 (termTable vals₂) (pairTable vals₂) i)
      (contextProductValues K (localContext i) (products i a (wa vals i) (wb vals i)))
      (nextLabel (st i a)) (kR i a (wa vals i) (wb vals i)) else failure
    have pureR : ∀ vals₂ i a, ∃ step, advance (R vals₂ i a).run = pure step := by
      intro vals₂ i a
      by_cases hl : live i a
      · simp only [R, if_pos hl, TreeCheckGadgetExtend.peerProgram_advance]
        exact ⟨_,rfl⟩
      · simp only [R, if_neg hl, advance_run_failure]
        exact ⟨_,rfl⟩
    apply TreeCheckGadgetExtend.realRun_field_prefix prims K D A cache0 n stA W (Q vals)
      (streamKey D prss) (label+1) 0 2 h (inst vals) grow
      (futureEmpty_block K D (streamKey D prss) label 1 2 vals c fresh)
      R (fun vals₂ i a => (pureR vals₂ i a).choose) (fun vals₂ i a => (pureR vals₂ i a).choose_spec)
    intro vals₂ i hi a s hg hc
    by_cases hl : live i a
    · simp only [Q,R,if_pos hl]
      exact TreeCheckGadgetExtend.extend_pass prims K D prss cache0 (ctx i) i hi (self i hi)
        (fun T ht => terms i hi T ((self i hi).symm ▸ ht))
        (by simpa only [self i hi] using pairs i hi) cached (label+1) vals₂
        (products i a (wa vals i) (wb vals i)) (width i hi a _ _) (nextLabel (st i a))
        (by simp only [nextLabel, labels i hi a]) (kR i a (wa vals i) (wb vals i))
        s.1 (inst vals) s.2 hg hc
    · simp only [Q,R,if_neg hl]
  calc
    _ = 𝒟[($ᵗ (KeyName C → Fin 2 → E)) >>= fun vals =>
        realRun prims D A n stA (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= Q vals i) (h,inst vals)] := by
      rw [realRun_presample_fields prims K D A n stA _ (streamKey D prss) label 1 2 h c fresh]
      apply evalDist_bind_congr' _
      intro vals
      rw [realRun_localPass_congr prims D A cache0 (inst vals) _ _ (by
        intro i hi s hg hc
        exact TreeCheckGadgetExtend.prefix_pass_congr prims D cache0 (inst vals) (W i) (P i) (Q vals i)
          (same vals i hi) s hg hc) n stA (h,inst vals) grow le_rfl]
    _ = 𝒟[($ᵗ (KeyName C → Fin 2 → E)) >>= fun vals =>
        (simulateQ (localAnswer prims) (hashPrefix D W)).run h >>= fun r =>
          realRun prims D A n stA (fun i => Q vals i ((r.1 i).getD default)) (r.2,inst vals)] :=
      evalDist_bind_congr' _ factor
    _ = 𝒟[(simulateQ (localAnswer prims) (hashPrefix D W)).run h >>= fun r =>
        ($ᵗ (KeyName C → Fin 2 → E)) >>= fun vals =>
          realRun prims D A n stA (fun i => Q vals i ((r.1 i).getD default)) (r.2,inst vals)] :=
      prefix_sample_comm prims D W h _
    _ = _ := by
      apply evalDist_bind_congr
      intro r hr
      have hg := grow.trans ((grows_localAnswer prims).simulateQ _ h r hr)
      symm
      rw [realRun_presample_fields prims K D A n stA _ (streamKey D prss) label 1 2 r.2 c fresh]
      apply evalDist_bind_congr' _
      intro vals
      rw [realRun_localPass_congr prims D A cache0 (inst vals) _ _ (by
        intro i hi s hs hc
        exact same vals i hi _ s hs hc) n stA (r.2,inst vals) hg le_rfl]

set_option maxHeartbeats 1000000 in
/-- The actual final-mask segment after a shared hash prefix, including every abort branch. -/
theorem coupled_finalMask_prefix {X β : Type} [Inhabited X]
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (terms : ∀ i, i ∉ D.1 → ∀ T, (ctx i).self ∈ C.holders T →
      (ctx i).prss.term T = streamKey D prss (.term T))
    (pairs : ∀ i, i ∉ D.1 → ∀ j (hj : j ≠ (ctx i).self),
      (ctx i).prss.pair j = streamKey D prss (.pair (C.pairOf (ctx i).self j (Ne.symm hj))))
    (cached : UsedKeysCached D prss cache0) (n n' label : ℕ)
    (W : C.Party → OracleComp (Query C →ₒ HashOutput) X) (live : C.Party → X → Prop)
    (products : C.Party → X → E → E → List (Product C E))
    (width : ∀ i, i ∉ D.1 → ∀ a wa wb, (products i a wa wb).length = 2)
    (st hs : C.Party → X → RunState C) (labels : ∀ i, i ∉ D.1 → ∀ a, (st i a).label = label)
    (kR : C.Party → X → E → E → Shares C E × RunState C → PartyM C E RealSpec β)
    (kH : C.Party → X → E → E → Shares C E → RunM C E (CheckSpec C E) Unit)
    (next : ∀ (xs : C.Party → X) (wa wb : C.Party → E) (out : C.Party → Option (Shares C E)),
      Coupled prims K D A x prss cache0 label0 n n' (label + 2)
        (TreeCheckGadgetExtend.resumeReal K (fun i => nextLabel (st i (xs i)))
          (fun i => kR i (xs i) (wa i) (wb i)) out)
        (fun i => afterExtend K i (products i (xs i) (wa i) (wb i)).length (nextLabel (hs i (xs i)))
          (kH i (xs i) (wa i) (wb i)) (out i))) :
    Coupled prims K D A x prss cache0 label0 (n + 1) (n' + 2) label
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= fun a =>
        if live i a then TreeCheckGadgetExtend.maskProgram K (ctx i) (st i a) (products i a) (kR i a)
        else failure)
      (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= fun a =>
        if live i a then ((hybridCheckGadgets K i).randElements 2 >>= fun rnd =>
          let wa := conv K (localContext i) rnd.1 0
          let wb := conv K (localContext i) rnd.1 1
          (hybridCheckGadgets K i).extendMult (products i a wa wb) >>= kH i a wa wb).run' (hs i a)
        else failure) := by
  intro stA h c grow fresh
  let H := fun i a => if live i a then
    ((hybridCheckGadgets K i).randElements 2 >>= fun rnd =>
      let wa := conv K (localContext i) rnd.1 0
      let wb := conv K (localContext i) rnd.1 1
      (hybridCheckGadgets K i).extendMult (products i a wa wb) >>= kH i a wa wb).run' (hs i a)
    else failure
  have pureH : ∀ i a, ∃ step, advance (H i a).run = pure step := by
    intro i a
    by_cases hl : live i a
    · simp only [H,if_pos hl]
      exact randElements_pure K i _ _
    · simp only [H,if_neg hl,advance_run_failure]
      exact ⟨_,rfl⟩
  apply relTriple_of_evalDist_eq_left (realRun_mask_prefix prims K D A prss cache0
    ctx self terms pairs cached label (n+1) stA W live products width st labels kR h c grow fresh)
  change RelTriple _ (hybRun prims K D (adapter prims K D A x prss cache0 label0) (n'+2)
    (stA,label) (fun i => oracleStep (liftComp (W i) (RoSpec C)) >>= H i) h) (Final D A)
  rw [TreeCheckGadgetExtend.hybRun_pure_prefix prims K D (adapter prims K D A x prss cache0 label0)
    (n'+2) (stA,label) W H (fun i a => (pureH i a).choose) (fun i a => (pureH i a).choose_spec)]
  apply relTriple_bind (relTriple_support_left (relTriple_refl _)
    (P := fun r => h ≤ r.2) (fun r hr => (grows_localAnswer prims).simulateQ _ h r hr))
  rintro r _ ⟨rfl,hg⟩
  exact TreeCheckGadgetExtend.coupled_finalMask prims K D A x prss cache0 label0
    ctx self terms pairs cached n n' label (fun i => live i ((r.1 i).getD default))
    (fun i => products i ((r.1 i).getD default)) (fun i hi => width i hi _)
    (fun i => st i ((r.1 i).getD default)) (fun i => hs i ((r.1 i).getD default))
    (fun i hi => labels i hi _) (fun i => kR i ((r.1 i).getD default))
    (fun i => kH i ((r.1 i).getD default)) (next (fun i => (r.1 i).getD default))
    stA r.2 c (grow.trans hg) fresh

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetMaskPrefix.randElements_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms randElements_pure

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetMaskPrefix.realRun_mask_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realRun_mask_prefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckGadgetMaskPrefix.coupled_finalMask_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupled_finalMask_prefix

end ThresholdLeanXmssSecurity.TreeCheckGadgetMaskPrefix
