import ThresholdLeanXmssSecurity.Proof.TreeTwinEntryReplay
import ThresholdLeanXmssSecurity.Proof.TreeTwinValueLink
import ThresholdLeanXmssSecurity.Proof.TreeTwinDrawReplay

/-! # Value sources at actual batch entries

The setup rows supply holder keys outside the existing bad event. Their real
continuation uses exactly those contexts, and cached inputs and replayed masks
supply the initial value relation for a batch.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinEntrySource
open TreeTwinHolderKeys TreeTwinEntryReplay TreeTwinValueLink TreeTwinDrawReplay
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E α : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- The actual logged continuation carries setup agreement or the original bad event. -/
theorem setup_holderKeys_or_bad3 (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (s : TreeSimState C) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (u : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : u ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality
      3 state (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s))
    (prog : OracleComp (WorldSpec C) α) (r : α × TreeSimState C)
    (later : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) prog).run u.2)) :
    TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z r.2.2 ∨
      HolderKeys D (fun i => (u.1.2 i).isSome) parameter (setupCtx parameter seeds pairs u.1.2) := by
  by_cases bad : TreeSimBad3 prims K circuits settings top tree D A
      (dealtKeys parameter seeds pairs) z r.2.2
  · exact Or.inl bad
  · exact Or.inr (holderKeys_setup_of_bad3 prims K circuits settings top tree D A state s
      parameter seeds pairs z u run r.2.2 (treeSimLoggedWorld_prefix prims D prog u.2 r later) bad)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem continueStep_done_congr {β : Type}
    (k k' : α → PartyM C E RealSpec β) (row : Option α)
    (same : ∀ a, row = some a → k a = k' a) :
    continueStep k (.done row) = continueStep k' (.done row) := by
  cases row with
  | none => rfl
  | some a =>
    simp only [continueStep]
    rw [same a rfl]

/-- Absent rows stay stopped; present rows use their own concrete setup keys. -/
theorem realContinue_setupCtx (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (rows : C.Party → Option (PrssKeys C)) :
    treeSimContinue (treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs)) rows =
      treeSimContinue (fun i _ => ceremonyAfterSetup K circuits settings
        (setupCtx parameter seeds pairs rows i) top tree) rows := by
  unfold treeSimContinue
  apply congrArg free
  apply congrArg Concrete.sequenceFin
  funext i
  apply continueStep_done_congr
  intro keys h
  exact (setupCtx_realCont K circuits settings top tree parameter seeds pairs rows i keys h).symm

/-- The actual cached batch inputs, with empty tuple lists, satisfy the value relation. -/
theorem batchStart_value (D : C.Coalition) (live : C.Party → Prop)
    (parameter : PublicParameter) (ctx : C.Party → Context C)
    (keys : HolderKeys D live parameter ctx) (all : ∀ i, i ∉ D.1 → live i)
    (base : HashCache C) (jobs : List Job) (st : C.Party → RunState C) :
    ValueLink D (fun i => (jobs.map (treeStagesCachedInputs base (ctx i)), [])) st ∧
      TupleShape D (fun i => (jobs.map (treeStagesCachedInputs base (ctx i)), [])) := by
  refine ⟨valueLink_entry D _ st ?_, tupleShape_entry D _⟩
  intro T i k hi hk heldI heldK
  exact wiresAt_cachedInputs keys base jobs T i k heldI heldK hi hk (all i hi) (all k hk)

/-- Index-zero answers at the same real cache give agreeing masks at honest holders. -/
theorem maskAgree_of_answered (prims : Primitives) (D : C.Coalition)
    (live : C.Party → Prop) (parameter : PublicParameter) (cache : HashCache C × HiddenCache C)
    (ctx : C.Party → Context C) (keys : HolderKeys D live parameter ctx)
    (all : ∀ i, i ∉ D.1 → live i) (label count : ℕ) (rnd : C.Party → PrssOutput C Bit)
    (answers : ∀ i, i ∉ D.1 → DrawAnswered prims D cache (ctx i) label 0 count (rnd i)) :
    TreeCheckWalkTranscript.MaskAgree D count rnd := by
  apply maskAgree_of_coherent prims D live parameter cache ctx keys all label count rnd
  exact drawCoherent_of_answered prims D live cache ctx label count rnd keys.self
    (fun i hi _ => answers i hi)

end ThresholdLeanXmssSecurity.TreeTwinEntrySource

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinEntrySource.setup_holderKeys_or_bad3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinEntrySource.setup_holderKeys_or_bad3

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinEntrySource.realContinue_setupCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinEntrySource.realContinue_setupCtx

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinEntrySource.batchStart_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinEntrySource.batchStart_value

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinEntrySource.maskAgree_of_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinEntrySource.maskAgree_of_answered
