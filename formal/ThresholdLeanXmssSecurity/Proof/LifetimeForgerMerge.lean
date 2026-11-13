import ThresholdLeanXmssSecurity.Proof.LifetimeSigningFrame

/-! # Private keygen-table merge for the actual lifetime replay

The actual forger interpreter and the direct world/signing interpreter have
identical full output laws after merging the private keygen table with the
external cache. The external signing state is retained. The sole restriction
on a replay program is that it never programs a non-keygen point.

World queries use the original local compiler merge law. Signing queries
preserve the private table and use the actual fixed-dealing operation's
keygen-domain frame. Structural induction composes these query laws without
requiring equality at unused keygen entries.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeForgerMerge
open LifetimeSigningFrame LifetimeJointLink
attribute [local instance] Classical.propDecidable
variable {C : Committee}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

abbrev SigningM (C : Committee) := StateT (TsigState C) (OracleComp (WorldSpec C))
def initialSign (D : Finset C.Party) : TsigState C := ⟨D, fun _ => none, [], fun _ => none⟩
def publicHandler (d : LifetimeBridge.Dealing C) (top : TopTree) :
    QueryImpl (ForgerSpec C) (SigningM C) :=
  (fun t => (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) :
    SigningM C ((LocalSpec C).Range t))) +
    tsigOracles worldRo (fixedDealt d top)
def directHandler (d : LifetimeBridge.Dealing C) (top : TopTree) :
    QueryImpl (ReplaySpec C) (SigningM C) :=
  (fun t => (StateT.lift (OracleComp.lift (OracleSpec.query t)) :
    SigningM C ((WorldSpec C).Range t))) +
    tsigOracles worldRo (fixedDealt d top)
def OtherReplayProgram : (ReplaySpec C).Domain → Prop
  | .inl t => LifetimeJointLink.OtherProgram t
  | .inr _ => False

def privateRun (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    {α : Type} (p : OracleComp (ReplaySpec C) α) (privateCache : HashCache C)
    (st : TsigState C) (externalCache : HashCache C) :
    ProbComp (((α × HashCache C) × TsigState C) × HashCache C) :=
  (simulateQ (worldAnswer prims)
    ((simulateQ (publicHandler d top) ((simulateQ forgerWorld p).run privateCache)).run st)).run externalCache

def directRun (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    {α : Type} (p : OracleComp (ReplaySpec C) α) (st : TsigState C) (c : HashCache C) :
    ProbComp ((α × TsigState C) × HashCache C) :=
  (simulateQ (worldAnswer prims) ((simulateQ (directHandler d top) p).run st)).run c


theorem privateRun_pure (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    {α : Type} (a : α) (pc ec : HashCache C) (st : TsigState C) :
    privateRun prims d top (pure a) pc st ec = pure (((a, pc), st), ec) := by
  simp [privateRun]

theorem directRun_pure (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    {α : Type} (a : α) (c : HashCache C) (st : TsigState C) :
    directRun prims d top (pure a) st c = pure ((a, st), c) := by
  simp [directRun]

theorem privateRun_bind (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    {α β : Type} (p : OracleComp (ReplaySpec C) α) (next : α → OracleComp (ReplaySpec C) β)
    (pc ec : HashCache C) (st : TsigState C) :
    privateRun prims d top (p >>= next) pc st ec =
      privateRun prims d top p pc st ec >>= fun r =>
        privateRun prims d top (next r.1.1.1) r.1.1.2 r.1.2 r.2 := by
  simp only [privateRun, simulateQ_bind, StateT.run_bind]

theorem directRun_bind (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    {α β : Type} (p : OracleComp (ReplaySpec C) α) (next : α → OracleComp (ReplaySpec C) β)
    (c : HashCache C) (st : TsigState C) :
    directRun prims d top (p >>= next) st c =
      directRun prims d top p st c >>= fun r =>
        directRun prims d top (next r.1.1) r.1.2 r.2 := by
  simp only [directRun, simulateQ_bind, StateT.run_bind]

private theorem prob_lift_twice {α : Type} (p : ProbComp α) :
    liftComp (liftComp p (LocalSpec C)) (ForgerSpec C) = liftComp p (ForgerSpec C) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t next ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, ih]
    rfl

private theorem public_local (d : LifetimeBridge.Dealing C) (top : TopTree)
    {α : Type} (p : OracleComp (LocalSpec C) α) (st : TsigState C) :
    (simulateQ (publicHandler d top) (liftComp p (ForgerSpec C))).run st =
      (fun a => (a, st)) <$> worldRoles.adversary p := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure a => simp only [liftComp_pure, simulateQ_pure, StateT.run_pure]; rfl
  | query_bind t next ih =>
    have query : simulateQ (publicHandler d top)
        (liftComp (OracleComp.lift (OracleSpec.query t)) (ForgerSpec C)) =
        StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) := by
      rw [liftComp_def, simulateQ_query]
      simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
      erw [simulateQ_query]
      rcases t with u | q | x <;> rfl
    simp only [liftComp_bind, simulateQ_bind, query, StateT.run_bind, StateT.run_lift,
      bind_assoc, pure_bind, ih]
    simp only [worldRoles, counted, liftComp_bind, simulateQ_bind, map_bind]

private theorem forger_world (t : (WorldSpec C).Domain) (pc : HashCache C) :
    (forgerWorld (.inl t)).run pc = liftComp ((compileWorld t).run pc) (ForgerSpec C) := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals dsimp only [forgerWorld, compileWorld, compileLocal, QueryImpl.add, tableStep]
  · rfl
  · change (if KeygenPoint q then
        StateT.mk (fun s => liftComp (((Query C →ₒ HashOutput).randomOracle q).run s) (ForgerSpec C))
      else StateT.lift (OracleComp.lift (OracleSpec.query (spec := ForgerSpec C) (.inl (.inr (.inl q)))))).run pc =
      liftComp ((if KeygenPoint q then tableStep ((Query C →ₒ HashOutput).randomOracle q)
        else StateT.lift (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q))))).run pc)
        (ForgerSpec C)
    by_cases h : KeygenPoint q
    · simp only [if_pos h, tableStep, StateT.run_mk, prob_lift_twice]
    · simp only [if_neg h, StateT.run_lift, liftComp_bind, liftComp_pure]
      rfl
  · rfl
  · exact (prob_lift_twice _).symm
  · rfl
  · change (if KeygenPoint q then
        StateT.mk (fun s => liftComp (((Query C →ₒ HashOutput).randomOracle q).run s) (ForgerSpec C))
      else StateT.lift (OracleComp.lift (OracleSpec.query (spec := ForgerSpec C) (.inl (.inr (.inl q)))))).run pc =
      liftComp ((if KeygenPoint q then tableStep ((Query C →ₒ HashOutput).randomOracle q)
        else StateT.lift (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q))))).run pc)
        (ForgerSpec C)
    by_cases h : KeygenPoint q
    · simp only [if_pos h, tableStep, StateT.run_mk, prob_lift_twice]
    · simp only [if_neg h, StateT.run_lift, liftComp_bind, liftComp_pure]
      rfl
  · rfl

/-- One world request runs the original local compiler and preserves the signing state. -/
theorem privateRun_world (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    (t : (WorldSpec C).Domain) (pc ec : HashCache C) (st : TsigState C) :
    privateRun prims d top (OracleComp.lift (OracleSpec.query (.inl t))) pc st ec =
      (fun r => (((r.1.1, r.1.2), st), r.2)) <$>
        (simulateQ (localAnswer prims) ((compileWorld t).run pc)).run ec := by
  unfold privateRun
  rw [simulateQ_spec_query, forger_world, public_local]
  simp only [simulateQ_map, StateT.run_map, LifetimePrfTransportProof.world_adversary]
  rfl

/-- Direct world requests preserve the external signing state. -/
theorem directRun_world (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    (t : (WorldSpec C).Domain) (ec : HashCache C) (st : TsigState C) :
    directRun prims d top (OracleComp.lift (OracleSpec.query (.inl t))) st ec =
      (fun r => ((r.1, st), r.2)) <$> (worldAnswer prims t).run ec := by
  unfold directRun
  rw [simulateQ_spec_query]
  change (simulateQ (worldAnswer prims)
    ((StateT.lift (OracleComp.lift (OracleSpec.query t)) : SigningM C _).run st)).run ec = _
  simp only [StateT.run_lift, bind_pure_comp]
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map]

/-- A signing query leaves the private table unchanged and retains its full state result. -/
theorem privateRun_signing (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    (q : (TsigSpec C).Domain) (pc ec : HashCache C) (st : TsigState C) :
    privateRun prims d top (OracleComp.lift (OracleSpec.query (.inr q))) pc st ec =
      (fun r => (((r.1.1, pc), r.1.2), r.2)) <$>
        (simulateQ (worldAnswer prims) ((tsigOracles worldRo (fixedDealt d top) q).run st)).run ec := by
  unfold privateRun
  rw [simulateQ_spec_query]
  change (simulateQ (worldAnswer prims) ((simulateQ (publicHandler d top)
    ((StateT.lift (OracleComp.lift (OracleSpec.query (spec := ForgerSpec C) (.inr q))) :
      StateT (HashCache C) (OracleComp (ForgerSpec C)) _).run pc)).run st)).run ec = _
  simp only [StateT.run_lift, bind_pure_comp]
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map]
  rfl

/-- The direct signing query is the actual fixed-dealing operation. -/
theorem directRun_signing (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    (q : (TsigSpec C).Domain) (ec : HashCache C) (st : TsigState C) :
    directRun prims d top (OracleComp.lift (OracleSpec.query (.inr q))) st ec =
      (simulateQ (worldAnswer prims) ((tsigOracles worldRo (fixedDealt d top) q).run st)).run ec := by
  unfold directRun
  rw [simulateQ_spec_query]
  rfl

/-- Merging the two actual caches recovers one allowed world request. -/
theorem world_merge (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    (t : (WorldSpec C).Domain) (safe : ¬ OtherProgram t)
    (pc ec : HashCache C) (st : TsigState C) :
    (fun r => ((r.1.1.1, r.1.2), mergedCache (r.1.1.2, r.2))) <$>
      privateRun prims d top (OracleComp.lift (OracleSpec.query (.inl t))) pc st ec =
      directRun prims d top (OracleComp.lift (OracleSpec.query (.inl t))) st (mergedCache (pc, ec)) := by
  rw [privateRun_world, directRun_world, Functor.map_map]
  have law := compile_merged_run prims (OracleComp.lift (OracleSpec.query t))
    ((isQueryBoundP_query_iff OtherProgram t 0).2 (fun h => absurd h safe)) (pc, ec)
  have lifted := congrArg ((fun r : (WorldSpec C).Range t × HashCache C => ((r.1, st), r.2)) <$> ·) law
  simpa only [simulateQ_spec_query, runLocal, StateT.run_mk, Functor.map_map,
    Prod.map_apply, id_eq, Function.comp_apply] using lifted

/-- Signing frames the private keygen domain without equating unused entries. -/
theorem signing_merge (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    (q : (TsigSpec C).Domain) (pc ec : HashCache C) (st : TsigState C) :
    (fun r => ((r.1.1.1, r.1.2), mergedCache (r.1.1.2, r.2))) <$>
      privateRun prims d top (OracleComp.lift (OracleSpec.query (.inr q))) pc st ec =
      directRun prims d top (OracleComp.lift (OracleSpec.query (.inr q))) st (mergedCache (pc, ec)) := by
  rw [privateRun_signing, directRun_signing, Functor.map_map]
  have frame := signing_frame prims d top q st ec pc
  simpa only [mergedCache, mergeOn_not, Function.comp_apply, Prod.eta] using frame

/-- One guarded replay query preserves the full result under cache merge. -/
theorem query_merge (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    (t : (ReplaySpec C).Domain) (safe : ¬ OtherReplayProgram t)
    (pc ec : HashCache C) (st : TsigState C) :
    (fun r => ((r.1.1.1, r.1.2), mergedCache (r.1.1.2, r.2))) <$>
      privateRun prims d top (OracleComp.lift (OracleSpec.query t)) pc st ec =
      directRun prims d top (OracleComp.lift (OracleSpec.query t)) st (mergedCache (pc, ec)) := by
  cases t with
  | inl t => exact world_merge prims d top t safe pc ec st
  | inr q => exact signing_merge prims d top q pc ec st

/-- The original guarded replay retains its output, external signing state and merged cache. -/
theorem private_direct_merge (prims : Primitives) (d : LifetimeBridge.Dealing C) (top : TopTree)
    {α : Type} (p : OracleComp (ReplaySpec C) α)
    (safe : IsQueryBoundP p OtherReplayProgram 0)
    (privateCache externalCache : HashCache C) (st : TsigState C) :
    (fun r => ((r.1.1.1, r.1.2), mergedCache (r.1.1.2, r.2))) <$>
      privateRun prims d top p privateCache st externalCache =
      directRun prims d top p st (mergedCache (privateCache, externalCache)) := by
  induction p using OracleComp.inductionOn generalizing privateCache externalCache st with
  | pure a => simp only [privateRun_pure, directRun_pure, map_pure]
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at safe
    have ht : ¬ OtherReplayProgram t := by simpa using safe.1
    rw [privateRun_bind, directRun_bind, map_bind,
      ← query_merge prims d top t ht privateCache externalCache st, bind_map_left]
    apply bind_congr
    rintro ⟨⟨⟨a, pc⟩, st'⟩, ec⟩
    exact ih a (by simpa using safe.2 a) pc ec st'

end ThresholdLeanXmssSecurity.LifetimeForgerMerge

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerMerge.privateRun_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerMerge.privateRun_pure

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerMerge.directRun_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerMerge.directRun_pure

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerMerge.privateRun_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerMerge.privateRun_bind

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerMerge.directRun_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerMerge.directRun_bind

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerMerge.privateRun_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerMerge.privateRun_world

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerMerge.directRun_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerMerge.directRun_world

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerMerge.privateRun_signing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerMerge.privateRun_signing

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerMerge.directRun_signing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerMerge.directRun_signing

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerMerge.world_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerMerge.world_merge

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerMerge.signing_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerMerge.signing_merge

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerMerge.query_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerMerge.query_merge

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerMerge.private_direct_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeForgerMerge.private_direct_merge
