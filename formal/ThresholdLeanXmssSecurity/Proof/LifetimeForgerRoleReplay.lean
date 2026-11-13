import ThresholdLeanXmssSecurity.Proof.LifetimeForgerMerge
import ThresholdLeanXmssSecurity.Proof.LifetimeSlotCoupling
import ThresholdLeanXmssSecurity.Proof.LifetimeForgerSourceParts

/-! # Exact projections of own-table and replay roles

The original own-table starts and rounds agree with the original replay-role
programs under direct interpretation. Suspended steps, the own stream table,
the shared hash cache, and the unchanged external signing state are retained.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeForgerRoleReplay
open LifetimeForgerMerge LifetimeSlotTransport LifetimeSlotCoupling
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
variable {C : Committee} {E : Type}

/-- The existing log erasure followed by the original world embedding. -/
def replayHom : EmulationM C →ᵐ StateT (StreamCache C) (OracleComp (ReplaySpec C)) where
  toFun _ p := StateT.mk fun own => inWorld ((treeSimErase p).run own)
  toFun_pure' a := by
    apply StateT.ext
    intro own
    simp only [treeSimErase_pure, StateT.run_mk, StateT.run_pure, inWorld, simulateQ_pure]
  toFun_bind' p f := by
    apply StateT.ext
    intro own
    simp only [treeSimErase_bind, StateT.run_mk, StateT.run_bind, inWorld, simulateQ_bind]

/-- The projection maps both original emulated roles to the original replay roles. -/
theorem replayHom_roles (D : C.Coalition) :
    LifetimeEmulatedBudget.RolesHom (replayHom (C := C)) (emulatedRoles D) (replayRoles D) := by
  constructor
  · intro α p
    apply StateT.ext
    intro own
    change inWorld (((treeSimErasedRoles D).adversary p).run own) = _
    rw [treeSimErase_adversary]
    simp only [replayRoles, StateT.run_lift, bind_pure_comp, inWorld, simulateQ_map]
  · intro α p
    rfl

/-- The role projection preserves the external signer and the actual shared cache. -/
theorem own_replay (d : LifetimeBridge.Dealing C) (top : TopTree) (prims : Primitives)
    {α : Type} (p : EmulationM C α) (own : StreamCache C)
    (w : WorldState C) (st : TsigState C) :
    (fun r => ((r.1, st), r.2.2.1)) <$>
      (evalEmulation prims ((ownHom p).run own)).run w =
    directRun prims d top ((replayHom p).run own) st w.2.1 := by
  rw [evalEmulation_own]
  simp only [directRun, replayHom, StateT.run_mk, LifetimeForgerSourceParts.direct_inWorld,
    simulateQ_map, StateT.run_map, evalEmulation, treeSimErase, keygenEraseLog,
    Functor.map_map]

/-- Exact original role projection for a ceremony's initial suspended steps. -/
theorem own_replay_start (D : C.Coalition) (d : LifetimeBridge.Dealing C) (top : TopTree)
    (prims : Primitives) {O : Type}
    (program : C.Party → PartyM C E RealSpec O) (own : StreamCache C)
    (w : WorldState C) (st : TsigState C) :
    (fun r => ((r.1, st), r.2.2.1)) <$>
      (evalEmulation prims ((startSteps (LifetimeSlots.ownRoles D) D program).run own)).run w =
    directRun prims d top ((startSteps (replayRoles D) D program).run own) st w.2.1 := by
  rw [← hom_startSteps ownHom _ _ (ownHom_roles D),
    ← hom_startSteps replayHom _ _ (replayHom_roles D)]
  exact own_replay d top prims _ own w st

/-- Exact original role projection for a real round, including all returned steps. -/
theorem own_replay_round (D : C.Coalition) (d : LifetimeBridge.Dealing C) (top : TopTree)
    (prims : Primitives) {O : Type}
    (steps : C.Party → Step C E RealSpec O) (sent : C.Party → C.Party → Option (Msg E))
    (own : StreamCache C) (w : WorldState C) (st : TsigState C) :
    (fun r => ((r.1, st), r.2.2.1)) <$>
      (evalEmulation prims
        ((stepRound (LifetimeSlots.ownRoles D) D (roundAdversary (I := PEmpty) sent)
          noFunctionality () steps).run own)).run w =
    directRun prims d top
      ((stepRound (replayRoles D) D (roundAdversary (I := PEmpty) sent)
        noFunctionality () steps).run own) st w.2.1 := by
  rw [own_stepRound, ← hom_stepRound replayHom _ _ (replayHom_roles D)]
  exact own_replay d top prims _ own w st

end ThresholdLeanXmssSecurity.LifetimeForgerRoleReplay

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerRoleReplay.replayHom_roles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerRoleReplay.replayHom_roles

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerRoleReplay.own_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerRoleReplay.own_replay

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerRoleReplay.own_replay_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerRoleReplay.own_replay_start

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerRoleReplay.own_replay_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerRoleReplay.own_replay_round
