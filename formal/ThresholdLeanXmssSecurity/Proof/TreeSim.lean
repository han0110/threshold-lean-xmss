import ThresholdLeanXmssSecurity.Proof.Tree
import ThresholdLeanXmssSecurity.Proof.Coupling

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-!
# The logged stream world

This module holds the log of the stream world and one lemma on the draw order of a list. The signing
proof and `TreeCheckKernelCoupling` read them. The library does not hold the simulation hop of a
ceremony.
-/

/-- Complete query/answer history of the concrete stream-world execution. -/
abbrev TreeSimLog (C : Committee) := List ((t : (WorldSpec C).Domain) × (WorldSpec C).Range t)

abbrev TreeSimState (C : Committee) := (HashCache C × HiddenCache C) × TreeSimLog C

/-- Logging as state makes the actual transcript available to the round
invariant and to a sticky union of bad events. -/
def treeSimLoggedWorld (D : C.Coalition) : QueryImpl (WorldSpec C) (StateT (TreeSimState C) ProbComp) :=
  fun t => StateT.mk fun s =>
    (fun r => (r.1, r.2, s.2 ++ [⟨t, r.1⟩])) <$> (streamWorld prims D t).run s.1

/-- The stateful log and the writer log are exactly the same instrumentation,
including an existing prefix and both final caches. -/
theorem treeSimLoggedWorld_run {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (cache : HashCache C × HiddenCache C) (log : TreeSimLog C) :
    (simulateQ (treeSimLoggedWorld prims D) p).run (cache, log) =
      (fun r => (r.1.1, r.2, log ++ r.1.2)) <$>
        (simulateQ ((streamWorld prims D).withTraceAppend (fun t u => ([⟨t, u⟩] : TreeSimLog C))) p).run.run cache := by
  induction p using OracleComp.inductionOn generalizing cache log with
  | pure a => simp [StateT.run_pure, WriterT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, treeSimLoggedWorld, StateT.run_bind,
      StateT.run_mk, QueryImpl.withTraceAppend_apply, WriterT.run_bind, WriterT.run_liftM,
      WriterT.run_tell, StateT.run_map, map_bind, bind_map_left,
      pure_bind, bind_assoc, Functor.map_map, ih]
    simp [List.append_assoc]

/-- Every supported execution extends the actual transcript, including adaptive queries. -/
theorem treeSimLoggedWorld_prefix {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (s : TreeSimState C)
    (r : α × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) :
    s.2 <+: r.2.2 := by
  rw [treeSimLoggedWorld_run] at hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨a, _, rfl⟩ := hr
  exact ⟨a.1.2, rfl⟩

/-- `sequenceFin` and the protocol's list traversal use the same draw order. -/
theorem treeSim_sequenceFin_mapM {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    {n : ℕ} (f : Fin n → m α) :
    List.ofFn <$> OverPermutation.sequenceFin f = (List.finRange n).mapM f := by
  induction n with
  | zero => simp [OverPermutation.sequenceFin, List.finRange]
  | succ n ih =>
    simp only [OverPermutation.sequenceFin, List.finRange_succ, List.mapM_cons, List.mapM_map,
      map_bind, map_pure, List.ofFn_succ]
    rw [← ih]
    simp only [bind_map_left, pure_bind]
    rfl

end ThresholdLeanXmssSecurity
