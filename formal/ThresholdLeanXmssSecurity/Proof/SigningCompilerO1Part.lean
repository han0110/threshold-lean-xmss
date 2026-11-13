import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Pre
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Programs

/-! # The part of an honest signer inside a handler

- `part_frame` couples the part of an honest signer at a constrained point. The relation inside the
  handler holds after it, with the reveal map of the source.
- `part_sync` couples one chain part of an honest signer at a chain with its row of pending answers.
  The reveal map of the source stays.
- `keepsRevealed_part` states that the compiler part at a chain point keeps the reveal map of the
  source.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Part
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync
open XmssSecurity.CappedChain
open SigningCompilerO1Frame SigningCompilerO1Pre SigningCompilerO1Programs
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-! ## The reveal map of the source -/

/-- A hash call off the bottom randomizer points keeps the reveal map of the source. -/
theorem keepsRevealed_hash (P : PublicParameter) (seeds : C.Term → HashOutput) (input : Query C)
    (h : ∀ seed e, input ≠ .prf seed (.randomizer bottomLayer e)) :
    SourceKeepsX (fun src : SourceState C => src.revealed) (sourceHashX P seeds input) := by
  unfold sourceHashX
  dsimp only
  split
  · rename_i seed lay e
    split
    · rename_i hlay
      subst hlay
      exact (h seed e rfl).elim
    · exact (SourceKeepsX.pure PUnit.unit).bind _ fun _ => SourceKeepsX.lift _
  · exact (SourceKeepsX.pure ()).bind _ fun _ => SourceKeepsX.lift _

/-- A program run of a `mapM` keeps a field when each run of its body keeps it. -/
theorem keeps_roMapM {ι α β : Type} (prims : Primitives) (P : PublicParameter)
    (seeds : C.Term → HashOutput) (field : SourceState C → β) (l : List ι)
    (f : ι → OracleComp (RoSpec C) α)
    (h : ∀ k ∈ l, SourceKeepsX field (sourceRoProgramX prims P seeds (f k))) :
    SourceKeepsX field (sourceRoProgramX prims P seeds (l.mapM f)) := by
  induction l with
  | nil =>
    rw [List.mapM_nil, sourceRoProgramX, simulateQ_pure]
    exact SourceKeepsX.pure []
  | cons k l ih =>
    rw [List.mapM_cons, sourceRoProgramX, simulateQ_bind]
    refine (h k List.mem_cons_self).bind _ fun v => ?_
    rw [simulateQ_bind]
    refine (ih fun k' hk' => h k' (List.mem_cons_of_mem _ hk')).bind _ fun vs => ?_
    rw [simulateQ_pure]
    exact SourceKeepsX.pure _

/-- The compiler part at a chain point keeps the reveal map of the source. -/
theorem keepsRevealed_part (prims : Primitives) (x : Keys3 C) (i : C.Party) (J : C.Quorum)
    (lay : Layer) (e : KeyIndex) (l : ChainIndex) (d : Digit) (message : Message) :
    SourceKeepsX (fun src : SourceState C => src.revealed)
      (sourcePartX prims x i J (.chain lay e l d) message) := by
  have hread : ∀ input : Query C, (∀ seed e, input ≠ .prf seed (.randomizer bottomLayer e)) →
      SourceKeepsX (fun src : SourceState C => src.revealed)
        (sourceRoProgramX prims x.1 x.2.1 (truncateHash <$> hashQuery input)) := by
    intro input hin
    have he : sourceRoProgramX prims x.1 x.2.1 (truncateHash <$> hashQuery input) =
        sourceHashX x.1 x.2.1 input >>= fun v => pure (truncateHash v) := by
      simp [sourceRoProgramX, hashQuery, sourceRoX, map_eq_bind_pure_comp]
    rw [he]
    exact (keepsRevealed_hash x.1 x.2.1 input hin).bind _ fun _ => SourceKeepsX.pure _
  unfold sourcePartX eval
  rw [sourceRoProgramX_bind]
  refine (keeps_roMapM prims x.1 x.2.1 _ _ _ fun T _ => hread _ fun seed e' h => ?_).bind _
    fun ts => ?_
  · cases h
  rw [sourceRoProgramX_bind]
  refine (keeps_roMapM prims x.1 x.2.1 _ _ _ fun j _ => hread _ fun seed e' h => ?_).bind _
    fun ms => ?_
  · cases h
  rw [sourceRoProgramX_pure]
  exact SourceKeepsX.pure _

section Waiting
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The part of an honest signer at a constrained point. A bottom chain point has its row of pending
answers. The relation inside the handler holds after the part, with the reveal map of the source. -/
theorem part_frame (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (i : C.Party) (J : C.Quorum) (p : Point) (message : Message)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (htime : cTime.1.1.bound = cCore.1.1.bound) (hp : Constrained p)
    (hrow : ∀ e l (d : XmssSecurity.ChainStep), Point.chain bottomLayer e l (chainStepDigit d) = p →
      ∀ d' : XmssSecurity.ChainStep, (dataOf x b.2).pending (.bottom e l d') ≠ none)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false)
    (ra : Digest × RealState C)
    (hra : ra ∈ support ((realHonest prims x s pads u rest
      (eval (dealtKeys x.1 x.2.1 x.2.2 i) i J p message)).run a))
    (rb : (Digest × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (sourcePartX prims x i J p message) b.1.base b.2)) :
    InPost prims x q s pads u rest noise top cCore cTime a b (fun rb => rb.1.2.revealed)
      (fun va vb => va = vb) ra rb := by
  have hbound : b.1.base.signing.bound = cCore.1.1.bound := hs.1.1.1.bound
  rcases eval_sync prims x q s pads u rest noise hkeys cCore i J p message a b.1.base b.2 hs.1 ha hb
      hmark ra (by with_reducible exact hra) rb hrb with h | h | ⟨hv, hcore, hf, hm⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  have hx := ExtraOpen.frame prims x top s _ (fun _ _ => False) (fun _ _ => False)
    b.1.base.revealed rb.1.2.revealed cTime a ra.2 b (⟨rb.1.2, b.1.starts⟩, rb.2) hs.2.1 hf rfl
    (fun k hk => by rw [hf.revealed k hk]; exact hk)
    (fun k hk => by
      by_cases h0 : b.1.base.revealed k = none
      · obtain ⟨e', he', hb'⟩ := hf.opened k h0 hk
        exact Or.inr ⟨e', he', by rw [htime, ← hbound]; exact hb'⟩
      · exact Or.inl h0)
    (fun _ _ _ hseen => by rcases hseen with ⟨T, hT⟩ | ⟨seed, J', hT⟩ <;> cases hT)
    (fun _ _ _ hseen => by rcases hseen with ⟨T, hT⟩ | ⟨seed, J', hT⟩ <;> cases hT)
    (fun T p' hseen => by
      rcases hseen with ⟨T', hT⟩ | ⟨seed, J', hT⟩
      · injection hT with _ hT
        subst hT
        exact Or.inr hp
      · cases hT)
    (fun T e l d hseen => by
      rcases hseen with ⟨T', hT⟩ | ⟨seed, J', hT⟩
      · injection hT with _ hT
        exact Or.inr (Or.inr fun d' => hf.pending _ (hrow e l d hT d'))
      · cases hT)
    (fun _ _ h => h)
  exact Or.inr (Or.inr ⟨hv,
    ⟨hcore, hx, TopO1.frame prims x top _ a ra.2 b (⟨rb.1.2, b.1.starts⟩, rb.2) hs.2.2.1 hf,
      backend_padsFixed x q s pads u rest noise _ b.2 hs.2.2.2 rb hrb⟩,
    hf.signing, hf.trees, hf.exposed, hf.candidates, hm, hf.carried, hf.log⟩)

/-- One chain part of an honest signer on both sides, at a chain with its row of pending answers.
The reveal map of the source stays. -/
theorem part_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (i : C.Party) (J : C.Quorum) (e : KeyIndex) (l : ChainIndex)
    (d : Digit) (message : Message) (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (htime : cTime.1.1.bound = cCore.1.1.bound) (hd : d.val < chainLength - 1)
    (hrows : ∀ d' : XmssSecurity.ChainStep, (dataOf x b.2).pending (.bottom e l d') ≠ none)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false)
    (ra : Digest × RealState C)
    (hra : ra ∈ support ((simulateQ (realWorld prims x s pads u rest)
      ((SigningJointEagerProof.dealtOf x top).part i J (.chain bottomLayer e l d) message)).run a))
    (rb : (Digest × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (sourcePartX prims x i J (.chain bottomLayer e l d) message) b.1.base b.2)) :
    InPost prims x q s pads u rest noise top cCore cTime a b (fun rb => rb.1.2.revealed)
      (fun va vb => va = vb ∧ rb.1.2.revealed = b.1.base.revealed) ra rb := by
  have hpart : (SigningJointEagerProof.dealtOf x top).part i J (.chain bottomLayer e l d) message =
      SigningSecurityProof.liftFree (eval (dealtKeys x.1 x.2.1 x.2.2 i) i J
        (.chain bottomLayer e l d) message) := rfl
  rw [hpart] at hra
  have hkeep : rb.1.2.revealed = b.1.base.revealed :=
    SourceKeepsX.run (keepsRevealed_part prims x i J bottomLayer e l d message) _ b.1.base b.2 rb hrb
  have hd3 : d.val < 3 := hd
  rcases part_frame prims x q s pads u rest noise hkeys top cCore cTime i J
      (.chain bottomLayer e l d) message a b hs htime (Or.inl ⟨rfl, hd3⟩)
      (fun e' l' d' h d'' => by
        injection h with _ he hl _
        subst he hl
        exact hrows d'')
      ha hb hmark ra (by with_reducible exact hra) rb hrb with h | h | ⟨hv, hrest⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨⟨hv, hkeep⟩, hrest⟩)

end Waiting

end ThresholdLeanXmssSecurity.SigningCompilerO1Part

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Part.keepsRevealed_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Part.keepsRevealed_hash

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Part.keeps_roMapM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Part.keeps_roMapM

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Part.keepsRevealed_part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Part.keepsRevealed_part

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Part.part_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Part.part_frame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Part.part_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Part.part_sync
