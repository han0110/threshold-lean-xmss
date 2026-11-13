import ThresholdLeanXmssSecurity.Proof.TreeSetupKeys
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkTranscript
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkSync
import ThresholdLeanXmssSecurity.Proof.TreeLockstepOpenedFinal
import ThresholdLeanXmssSecurity.Proof.TreeEvents3
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkRecipe

/-!
# Holder keys and real value replay

The actual setup rows retain dealt seeds and agreeing PRSS term keys at live
honest holders. Replaying PRSS draws and input reads against one cache gives
term-mask and input-wire agreement on those same parties.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false

noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeTwinHolderKeys

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- Key information at live honest operators; no tuple agreement is assumed. -/
structure HolderKeys (D : C.Coalition) (live : C.Party → Prop)
    (parameter : PublicParameter) (ctx : C.Party → Context C) : Prop where
  self : ∀ i, i ∉ D.1 → live i → (ctx i).self = i
  parameter_eq : ∀ i, i ∉ D.1 → live i → (ctx i).keys.parameter = parameter
  seeds : ∀ T i k, i ∈ C.holders T → k ∈ C.holders T →
    i ∉ D.1 → k ∉ D.1 → live i → live k → (ctx i).keys.seed T = (ctx k).keys.seed T
  terms : ∀ T i k, i ∈ C.holders T → k ∈ C.holders T →
    i ∉ D.1 → k ∉ D.1 → live i → live k → (ctx i).prss.term T = (ctx k).prss.term T

def setupCtx (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (rows : C.Party → Option (PrssKeys C))
    (i : C.Party) : Context C :=
  ⟨i, dealtKeys parameter seeds pairs i, TreeCheckWalkRecipe.setupKeys rows i⟩

theorem setupCtx_real (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (rows : C.Party → Option (PrssKeys C))
    (i : C.Party) (keys : PrssKeys C) (present : rows i = some keys) :
    setupCtx parameter seeds pairs rows i = ⟨i, dealtKeys parameter seeds pairs i, keys⟩ := by
  simp only [setupCtx, TreeCheckWalkRecipe.setupKeys_some rows i keys present]

theorem holderKeys_setup (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (s : TreeSimState C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (u : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : u ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality
      3 state (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s))
    (good : ¬ TreeSimHashBudgetCollision u.2.2) :
    HolderKeys D (fun i => (u.1.2 i).isSome) parameter (setupCtx parameter seeds pairs u.1.2) := by
  refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, ?_, ?_⟩
  · intro T i k hi hk _ _ _ _
    simp only [setupCtx, dealtKeys, if_pos hi, if_pos hk]
  · intro T i k hi hk _ _ li lk
    obtain ⟨ki, hki⟩ := Option.isSome_iff_exists.mp li
    obtain ⟨kk, hkk⟩ := Option.isSome_iff_exists.mp lk
    change (TreeCheckWalkRecipe.setupKeys u.1.2 i).term T =
      (TreeCheckWalkRecipe.setupKeys u.1.2 k).term T
    rw [TreeCheckWalkRecipe.setupKeys_some _ _ _ hki,
      TreeCheckWalkRecipe.setupKeys_some _ _ _ hkk]
    exact treeSetup_phase_agree prims D A state s u run good i k ki kk hki hkk T hi hk

section Field
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

theorem setupCtx_realCont (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (rows : C.Party → Option (PrssKeys C))
    (i : C.Party) (keys : PrssKeys C) (present : rows i = some keys) :
    ceremonyAfterSetup K circuits settings (setupCtx parameter seeds pairs rows i) top tree =
      treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs) i keys := by
  rw [setupCtx_real _ _ _ _ _ _ present]
  rfl

theorem holderKeys_setup_of_bad3 (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (s : TreeSimState C) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (u : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : u ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality
      3 state (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s))
    (L : TreeSimLog C) (hprefix : u.2.2 <+: L)
    (good : ¬ TreeSimBad3 prims K circuits settings top tree D A
      (dealtKeys parameter seeds pairs) z L) :
    HolderKeys D (fun i => (u.1.2 i).isSome) parameter (setupCtx parameter seeds pairs u.1.2) := by
  apply holderKeys_setup prims D A state s parameter seeds pairs u run
  exact fun h => not_budgetCollision_of_not_bad3 prims K circuits settings top tree D A
    _ z L good (treeSimHashBudgetCollision_mono hprefix h)

end Field

/-- The actual masks are stream answers at one cache and one label. -/
def DrawCoherent (prims : Primitives) (D : C.Coalition) (live : C.Party → Prop)
    (cache : HashCache C × HiddenCache C) (ctx : C.Party → Context C)
    (label count : ℕ) (rnd : C.Party → PrssOutput C Bit) : Prop :=
  ∀ i, i ∉ D.1 → live i → ∀ T, i ∈ C.holders T → ∀ g < count,
    TreeLockstepStreamAnswer prims D cache (.term T, (ctx i).prss.term T, label, 0, g)
      ((rnd i).1 T g)

section Replay
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- Lift removal and term replay, as in `TreeCheckWalkTranscript.draw_masks`. -/
theorem drawCoherent_of_replay (prims : Primitives) (D : C.Coalition)
    (live : C.Party → Prop) (cache : HashCache C × HiddenCache C)
    (allowed : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Prop)
    (streams : ∀ x u, allowed (.inr (.inr (.inr x))) u →
      TreeLockstepStreamAnswer prims D cache x u)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → live i → (ctx i).self = i)
    (label count : ℕ) (rnd : C.Party → PrssOutput C Bit)
    (each : ∀ i, i ∉ D.1 → live i → TreeSimCheckAllowed (fun t u => allowed (.inr t) u)
      (liftComp (prssDraw (ctx i) (bitCodec (E := E)) label 0 count) (LocalSpec C)) (rnd i)) :
    DrawCoherent prims D live cache ctx label count rnd := by
  intro i hi li T held g hg
  have ro : TreeSimCheckAllowed (fun t u => allowed (.inr (.inr t)) u)
      (prssDraw (ctx i) (bitCodec (E := E)) label 0 count) (rnd i) :=
    TreeSimCheckAllowed.simulate_inv
      (fun t => OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (Sum.inr t)))
      (fun t u => allowed (.inr t) u) _
      (fun t u hu => TreeSimCheckAllowed.query_inv
        (allowed := fun t u => allowed (.inr t) u) (Sum.inr t) u hu) _ _ (each i hi li)
  exact TreeCheckWalkTranscript.term_mask prims D cache _ (fun x u h => streams x u h) (ctx i) label 0 count
    (rnd i) ro T (by rw [self i hi li]; exact held) g hg

theorem maskAgree_of_coherent (prims : Primitives) (D : C.Coalition)
    (live : C.Party → Prop) (parameter : PublicParameter) (cache : HashCache C × HiddenCache C)
    (ctx : C.Party → Context C) (keys : HolderKeys D live parameter ctx)
    (allLive : ∀ i, i ∉ D.1 → live i) (label count : ℕ) (rnd : C.Party → PrssOutput C Bit)
    (coherent : DrawCoherent prims D live cache ctx label count rnd) :
    TreeCheckWalkTranscript.MaskAgree D count rnd := by
  intro T i k hiT hkT hi hk g hg
  have ai := coherent i hi (allLive i hi) T hiT g hg
  have ak := coherent k hk (allLive k hk) T hkT g hg
  rw [keys.terms T i k hiT hkT hi hk (allLive i hi) (allLive k hk)] at ai
  exact TreeCheckWalkTranscript.streamAnswer_unique prims D ai ak

/-- Input replay on the actual input values; the output is explicit wire equality. -/
theorem inputsAgree_of_replay (prims : Primitives) (D : C.Coalition)
    (live : C.Party → Prop) (parameter : PublicParameter) (ctx : C.Party → Context C)
    (keys : HolderKeys D live parameter ctx) (hash : Query C → HashOutput)
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (hashes : ∀ q u, allowed (.inl (.inl (.inr (.inl q)))) u → hash q = u)
    (jobs : List Job) (inputs : C.Party → MainInput C)
    (each : ∀ i, i ∉ D.1 → live i → TreeSimCheckAllowed allowed
      (jobs.mapM (inputShares (ctx i)) : PartyM C E RealSpec _).run (some (inputs i))) :
    ∀ T i k, i ∈ C.holders T → k ∈ C.holders T → i ∉ D.1 → k ∉ D.1 → live i → live k →
      TreeCheckWalkConsistent.wiresAt T (inputs i) = TreeCheckWalkConsistent.wiresAt T (inputs k) := by
  intro T i k hiT hkT hi hk li lk
  rw [treeCheck_inputShares_replay prims hash allowed hashes (ctx i) jobs (inputs i) (each i hi li),
    treeCheck_inputShares_replay prims hash allowed hashes (ctx k) jobs (inputs k) (each k hk lk)]
  unfold TreeCheckWalkConsistent.wiresAt
  simp only [List.map_map]
  apply List.map_congr_left
  intro job _
  simp only [Function.comp_apply, keys.self i hi li, keys.self k hk lk, if_pos hiT, if_pos hkT,
    inputBits, keys.seeds T i k hiT hkT hi hk li lk]

end Replay
/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHolderKeys.setupCtx_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms setupCtx_real

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHolderKeys.holderKeys_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holderKeys_setup

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHolderKeys.setupCtx_realCont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms setupCtx_realCont

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHolderKeys.holderKeys_setup_of_bad3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holderKeys_setup_of_bad3

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHolderKeys.drawCoherent_of_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms drawCoherent_of_replay

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHolderKeys.maskAgree_of_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms maskAgree_of_coherent

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinHolderKeys.inputsAgree_of_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inputsAgree_of_replay

end TreeTwinHolderKeys
end ThresholdLeanXmssSecurity
