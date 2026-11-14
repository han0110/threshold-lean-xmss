import ThresholdLeanXmssSecurity.Proof.SigningOwnLedger

/-!
# The walk of the O1 source over the ledger

`runSourceL` runs an O1 source program over the capped hybrid with the ledger. `WalkInv` is the
joint invariant of the walk. Each clause holds on every run, with the hidden-key flag up or down.
`SourceCharges` states that a program keeps `WalkInv` and makes at most a given count of charged
calls.

The combinators of this file give `SourceCharges` for `pure`, `get`, `modify`, `bind`, `map`,
`mapM`, `sequenceFin` and a lifted step of the base source. The charges add up at `bind`.
`SourceCharges.simulateQ_bound` states that a forger with at most `n` counted queries makes at
most `n` charged calls, when each handler makes at most one charged call at a counted query and
none at another query.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningOwnWalk

open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Clean SigningOwnLedger

variable {C : Committee}

attribute [local instance] Classical.propDecidable

set_option linter.constructorNameAsVariable false

/-- A run of an O1 source program over the hybrid with the ledger. -/
def runSourceL {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput) (Q : ℕ)
    (s : HiddenKey → Digest) (oa : SourceMO1 C α) (src : SourceStateO1 C)
    (st : CappedCompilerState C × OwnGhost) :
    ProbComp ((α × SourceStateO1 C) × (CappedCompilerState C × OwnGhost)) :=
  (simulateQ (ownHybrid P seeds Q s) (oa.run src)).run st

/-- Each chain value of the top signature of a tree is a known value or a secret that is no bottom
opening. -/
def TopShape (tree : DeferredBottomTree) : Prop :=
  ∀ l k, tree.topSignature.chainValue l = .secret k → ∀ e, k ≠ .opening bottomLayer e

/-- The joint invariant of the walk. Each clause holds on every run, with the hidden-key flag up
or down. -/
structure WalkInv (P : PublicParameter) (seeds : C.Term → HashOutput) (src : SourceStateO1 C)
    (st : CappedCompilerState C × OwnGhost) : Prop where
  /-- The source and the hybrid hold the same revealed secrets. -/
  reveal : src.base.revealed = st.1.2.1
  /-- The backend holds the bound map of the source. -/
  bound : st.1.1.1.bound = src.base.signing.bound
  /-- A bound key with each term virtual or cached has a revealed opening. -/
  ready : ∀ e, OpeningReady seeds st.1.1.1.data src.base.signing e →
    src.base.revealed (.opening bottomLayer e) ≠ none
  /-- A commitment answer has the virtual terms of its key. -/
  commitTerms : ∀ e, st.1.1.1.data.pending (.commitment e) ≠ none →
    ∀ T, (T, Point.randomizer bottomLayer e) ∈ st.1.1.1.data.virtual
  /-- A stored tree has the commitment answer of each of its keys, and a successful tree holds its
  low half. -/
  treeCommit : ∀ b, src.base.trees b ≠ none → ∀ k,
    ∃ c, st.1.1.1.data.pending (.commitment (bottomKey b k)) = some c ∧
      ∀ tree, src.base.trees b = some (some tree) →
        c.low = .known (tree.commitment (bottomKey b k))
  /-- A revealed bottom opening has each term cached. -/
  revealedCached : ∀ e, src.base.revealed (.opening bottomLayer e) ≠ none →
    SigningGuessProof.RandomizerCached seeds st.1.1.1.data.cache e
  /-- Each release record is at the bound message of its key. -/
  releasedBound : SigningGuessProof.ReleasedBound src.base.signing
  /-- At most `t - 1` operators are corrupt. So a key with `t` signers has a release record. -/
  corruptBound : src.base.signing.corrupt.card ≤ C.t - 1
  /-- The backend is reachable. -/
  reachable : CompilerReachable P seeds st.1.1
  /-- A dirty state has a second opening. -/
  dirtySecond : st.2.dirty = true → SecondOpening P seeds st.1.1.1.data
  /-- Each stored successful tree has `TopShape`. -/
  storedTopShape : ∀ b tree, src.base.trees b = some (some tree) → TopShape tree

/-- A source program keeps the invariant of the walk from each state of `Pre`, and it makes at most
`c` charged calls on each run. -/
def SourceCharges {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput) (Q : ℕ)
    (s : HiddenKey → Digest) (Pre : SourceStateO1 C → Prop) (c : ℕ) (oa : SourceMO1 C α) : Prop :=
  ∀ src st, WalkInv P seeds src st → Pre src →
    ∀ r ∈ support (runSourceL P seeds Q s oa src st),
      WalkInv P seeds r.1.2 r.2 ∧ r.2.2.ledger ≤ st.2.ledger + c

section Runs
variable (P : PublicParameter) (seeds : C.Term → HashOutput) (Q : ℕ) (s : HiddenKey → Digest)

theorem runSourceL_pure {α : Type} (a : α) (src : SourceStateO1 C)
    (st : CappedCompilerState C × OwnGhost) :
    runSourceL P seeds Q s (pure a) src st = pure ((a, src), st) := by
  simp only [runSourceL, StateT.run_pure, simulateQ_pure, StateT.run_pure]

theorem runSourceL_get (src : SourceStateO1 C) (st : CappedCompilerState C × OwnGhost) :
    runSourceL P seeds Q s get src st = pure ((src, src), st) := by
  simp only [runSourceL, StateT.run_get, simulateQ_pure, StateT.run_pure]

theorem runSourceL_modify (f : SourceStateO1 C → SourceStateO1 C) (src : SourceStateO1 C)
    (st : CappedCompilerState C × OwnGhost) :
    runSourceL P seeds Q s (modify f) src st = pure (((), f src), st) := by
  simp only [runSourceL, StateT.run_modify, simulateQ_pure, StateT.run_pure]

theorem runSourceL_bind {α β : Type} (oa : SourceMO1 C α) (f : α → SourceMO1 C β)
    (src : SourceStateO1 C) (st : CappedCompilerState C × OwnGhost) :
    runSourceL P seeds Q s (oa >>= f) src st =
      runSourceL P seeds Q s oa src st >>= fun r => runSourceL P seeds Q s (f r.1.1) r.1.2 r.2 := by
  simp only [runSourceL, StateT.run_bind, simulateQ_bind, StateT.run_bind]

theorem runSourceL_liftBase {α : Type} (oa : SourceM C α) (src : SourceStateO1 C)
    (st : CappedCompilerState C × OwnGhost) :
    runSourceL P seeds Q s (liftBase oa) src st =
      (fun r => ((r.1.1, { src with base := r.1.2 }), r.2)) <$>
        (simulateQ (ownHybrid P seeds Q s) (oa.run src.base)).run st := by
  simp [runSourceL, liftBase, simulateQ_map, StateT.run_map]

end Runs

namespace SourceCharges
variable {P : PublicParameter} {seeds : C.Term → HashOutput} {Q : ℕ} {s : HiddenKey → Digest}
  {Pre : SourceStateO1 C → Prop}

theorem mono {α : Type} {oa : SourceMO1 C α} {Pre' : SourceStateO1 C → Prop} {c d : ℕ}
    (h : SourceCharges P seeds Q s Pre c oa) (hPre : ∀ src, Pre' src → Pre src) (hcd : c ≤ d) :
    SourceCharges P seeds Q s Pre' d oa := by
  intro src st hw hp r hr
  obtain ⟨hw', hl⟩ := h src st hw (hPre src hp) r hr
  exact ⟨hw', by omega⟩

theorem pure {α : Type} (value : α) : SourceCharges P seeds Q s Pre 0 (Pure.pure value) := by
  intro src st hw _ r hr
  rw [runSourceL_pure, mem_support_pure_iff] at hr
  subst r
  exact ⟨hw, le_rfl⟩

theorem get : SourceCharges P seeds Q s Pre 0 (get : SourceMO1 C (SourceStateO1 C)) := by
  intro src st hw _ r hr
  rw [runSourceL_get, mem_support_pure_iff] at hr
  subst r
  exact ⟨hw, le_rfl⟩

theorem modify (f : SourceStateO1 C → SourceStateO1 C)
    (hf : ∀ src st, WalkInv P seeds src st → Pre src → WalkInv P seeds (f src) st) :
    SourceCharges P seeds Q s Pre 0 (modify f : SourceMO1 C Unit) := by
  intro src st hw hp r hr
  rw [runSourceL_modify, mem_support_pure_iff] at hr
  subst r
  exact ⟨hf src st hw hp, le_rfl⟩

theorem bind {α β : Type} {oa : SourceMO1 C α} {c d : ℕ} (h : SourceCharges P seeds Q s Pre c oa)
    (next : α → SourceMO1 C β) (hn : ∀ value, SourceCharges P seeds Q s (fun _ => True) d (next value)) :
    SourceCharges P seeds Q s Pre (c + d) (oa >>= next) := by
  intro src st hw hp r hr
  rw [runSourceL_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  obtain ⟨hwa, hla⟩ := h src st hw hp a ha
  obtain ⟨hwr, hlr⟩ := hn a.1.1 a.1.2 a.2 hwa trivial r hr
  exact ⟨hwr, by omega⟩

theorem map {α β : Type} {oa : SourceMO1 C α} {c : ℕ} (h : SourceCharges P seeds Q s Pre c oa)
    (f : α → β) : SourceCharges P seeds Q s Pre c (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact SourceCharges.bind h _ fun value => SourceCharges.pure (f value)

theorem mapM {α β : Type} {c : ℕ} (items : List α) (oa : α → SourceMO1 C β)
    (h : ∀ a ∈ items, SourceCharges P seeds Q s (fun _ => True) c (oa a)) :
    SourceCharges P seeds Q s (fun _ => True) (items.length * c) (items.mapM oa) := by
  induction items with
  | nil => exact SourceCharges.mono (SourceCharges.pure []) (fun _ h => h) (Nat.zero_le _)
  | cons a items ih =>
      rw [List.mapM_cons]
      refine SourceCharges.mono (SourceCharges.bind (h a (List.mem_cons_self ..)) _ fun head =>
        SourceCharges.bind (ih fun b hb => h b (List.mem_cons_of_mem _ hb)) _ fun tail =>
          SourceCharges.pure _) (fun _ h => h) ?_
      simp only [List.length_cons]
      nlinarith

theorem sequenceFin {α : Type} {c : ℕ} (n : ℕ) (oa : Fin n → SourceMO1 C α)
    (h : ∀ i, SourceCharges P seeds Q s (fun _ => True) c (oa i)) :
    SourceCharges P seeds Q s (fun _ => True) (n * c) (OverPermutation.sequenceFin oa) := by
  induction n with
  | zero => exact SourceCharges.mono (SourceCharges.pure _) (fun _ h => h) (Nat.zero_le _)
  | succ n ih =>
      simp only [OverPermutation.sequenceFin]
      refine SourceCharges.mono (SourceCharges.bind (h 0) _ fun head =>
        SourceCharges.bind (ih (fun i => oa i.succ) fun i => h i.succ) _ fun tail =>
          SourceCharges.pure _) (fun _ h => h) ?_
      nlinarith

/-- A step of the base source keeps the walk when each run of it over the ledger keeps the walk
with the recorded digits of the O1 state. -/
theorem liftBase {α : Type} {oa : SourceM C α} {c : ℕ}
    (h : ∀ src st, WalkInv P seeds src st → Pre src →
      ∀ r ∈ support ((simulateQ (ownHybrid P seeds Q s) (oa.run src.base)).run st),
        WalkInv P seeds { src with base := r.1.2 } r.2 ∧ r.2.2.ledger ≤ st.2.ledger + c) :
    SourceCharges P seeds Q s Pre c (liftBase oa) := by
  intro src st hw hp r hr
  rw [runSourceL_liftBase, support_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  exact h src st hw hp a ha

/-- A forger with at most `n` counted queries makes at most `n` charged calls, when each handler
makes at most one charged call at a counted query and none at another query. -/
theorem simulateQ_bound {ι α : Type} {spec : OracleSpec ι} (P : PublicParameter)
    (seeds : C.Term → HashOutput) (Q : ℕ) (s : HiddenKey → Digest)
    (impl : QueryImpl spec (SourceMO1 C)) (p : ι → Prop)
    (step : ∀ t, SourceCharges P seeds Q s (fun _ => True) (if p t then 1 else 0) (impl t))
    (oa : OracleComp spec α) (n : ℕ) (hn : IsQueryBoundP oa p n) :
    SourceCharges P seeds Q s (fun _ => True) n (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure value =>
      simpa only [simulateQ_pure] using
        SourceCharges.mono (SourceCharges.pure value) (fun _ h => h) (Nat.zero_le n)
  | query_bind t next ih =>
      rw [isQueryBoundP_query_bind_iff] at hn
      simp only [simulateQ_bind, simulateQ_spec_query]
      refine SourceCharges.mono (SourceCharges.bind (step t) _ fun u => ih u _ (hn.2 u))
        (fun _ h => h) ?_
      by_cases hp : p t
      · have := hn.1.resolve_left (not_not.2 hp)
        simp only [if_pos hp]
        omega
      · simp only [if_neg hp]
        omega

end SourceCharges

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.runSourceL_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runSourceL_pure

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.runSourceL_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runSourceL_get

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.runSourceL_modify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runSourceL_modify

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.runSourceL_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runSourceL_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.runSourceL_liftBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms runSourceL_liftBase

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.SourceCharges.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SourceCharges.mono

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.SourceCharges.pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SourceCharges.pure

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.SourceCharges.get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SourceCharges.get

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.SourceCharges.modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SourceCharges.modify

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.SourceCharges.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SourceCharges.bind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.SourceCharges.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SourceCharges.map

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.SourceCharges.mapM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SourceCharges.mapM

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.SourceCharges.sequenceFin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SourceCharges.sequenceFin

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.SourceCharges.liftBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SourceCharges.liftBase

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnWalk.SourceCharges.simulateQ_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms SourceCharges.simulateQ_bound

end ThresholdLeanXmssSecurity.SigningOwnWalk
