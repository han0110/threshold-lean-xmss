import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkCoverage

/-!
# The `Unreached` clause of the fixed source walk

This file concerns `WalkUnreached` of `TreeCheckWalkCoverage`, for the fixed
family `family` of `TreeCheckWalkRecipe`. The family, its decoder and its
witness are not changed.

## Lemmas

* `walk_terminal_finish` shows that a finished outcome of the walk is an
  outcome of the original run from the start state. So each fact about the
  actual logged run applies to a finished outcome.
* `walk_no_terminal` shows that the walk has no finished outcome when the
  decoder recognizes every state that `prepare` gives at the start.
* `firstChunks_ne_nil` and `initial_room` give the two premises of
  `initial_decode_hit` for every tree and every first index.
* `initial_no_terminal` and `unreached_first` give the `Unreached` clause of
  batch `0`. The decoder recognizes the state after the setup, so the walk
  stops there.
* `WalkUnreachedLater` is the `Unreached` clause of the fixed family for the
  batches after the first one. `walkUnreached_of_later` gives `WalkUnreached`
  from it.

## What a hit at a later batch needs

The cut of a batch `j` after the first one is in the local pass after an
exchange. A counted bad result has an honest party with more than `j`
records. A backward argument from this result must find a walk state at the
start of batch `j` where `Fits` holds. `Fits` needs these facts.

* `CallerLengths`. Each honest party holds `j` records, and the outputs of
  the current batched call before batch `j`.
* Each honest program at that state equals the caller program.
  `openResume_tail` gives the normal form after an `openRep` exchange. A party
  that receives an abort frame has the program `failure`, and the caller tail
  `pure none` gives the same program.
* The actual counters equal `(lockstepStart … j, j)`.
* The live honest parties use one encoding, because `Caller` has one
  `encoding` field. `treeLockstepEncoding` gives one salt schedule on the
  reachable configurations of `TreeStagesReach`, without a budget collision.
  It does not state equality of the encodings in the programs of walk states.
* The remaining fuel holds the rounds of batch `j`.
* At `j = (firstChunks settings tree).length`, the `fixed` premise of
  `selected_signing_decode_hit` for each live honest party.

The fields `outputs`, `records`, `root`, `randomness` and `tail` of `Caller`
are per party. A wrong copy at one party changes only these fields, until it
enters the public choice of the signing run.

Peer reshares record the filled values in `h_T`, and `compareDigests` compares
the digests of all holders of a term. This check runs in `verify`, before the
outputs open. Two honest holders with different values thus abort, except for
a `.history` or `.digest` collision. The counted bad event excludes these
collisions by `TreeSimHashBudgetCollision`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace TreeCheckWalkUnreached

open TreeCheckWalkRecipe TreeCheckWalkCoverage

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)
variable (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C)) (j : ℕ)
variable (Z : Distinguisher C A.State TreeOutput)

section Walk

/-- A finished outcome of the walk is an outcome of the original run. -/
theorem walk_terminal_finish (fuel : ℕ) (p : TreeCheckWalkDef.Pending A) (r : TreeCheckTailResult A)
    (run : .inr r ∈ support (walk prims K D A circuits settings top tree x setup j Z fuel p)) :
    r ∈ support (TreeCheckWalkDef.finish prims D Z {p with fuel := fuel}) := by
  rw [TreeCheckWalkRecipe.walk_split prims K D A circuits settings top tree x setup j Z fuel p, mem_support_bind_iff]
  exact ⟨.inr r, run, by simp⟩

/-- A walk whose start states are all recognized has no finished outcome. -/
theorem walk_no_terminal (fuel : ℕ) (p : TreeCheckWalkDef.Pending A)
    (hit : ∀ current ∈ support (prepare prims K D A circuits settings top tree x setup j
      {p with fuel := fuel}), (decode prims K D A circuits settings top tree x setup j current).isSome)
    (r : TreeCheckTailResult A) :
    .inr r ∉ support (walk prims K D A circuits settings top tree x setup j Z fuel p) := by
  intro run
  cases fuel with
  | zero =>
      simp only [TreeCheckWalkRecipe.walk, mem_support_bind_iff] at run
      obtain ⟨current, hc, run⟩ := run
      rw [dif_pos (hit current hc), mem_support_pure_iff] at run
      cases run
  | succ fuel =>
      simp only [TreeCheckWalkRecipe.walk, mem_support_bind_iff] at run
      obtain ⟨current, hc, run⟩ := run
      rw [dif_pos (hit current hc), mem_support_pure_iff] at run
      cases run

end Walk

section First

/-- The first run has at least one batch. -/
theorem firstChunks_ne_nil (hb : 0 < settings.batchSize) (index : Fin (treeBatches settings tree))
    (zero : index.val = 0) : firstChunks settings tree ≠ [] := by
  intro empty
  have length : (firstChunks settings tree).length = 0 := by rw [empty, List.length_nil]
  cases tree with
  | top =>
      have bound := index.isLt
      change index.val < (chunks settings.batchSize topJobs).length at bound
      change (chunks settings.batchSize topJobs).length = 0 at length
      omega
  | bottom b =>
      change (chunks settings.batchSize (bottomJobs b)).length = 0 at length
      rw [length_chunks] at length
      have jobs : 0 < (bottomJobs b).length := by
        simp [bottomJobs]
      have := Nat.div_pos (show settings.batchSize ≤ (bottomJobs b).length + settings.batchSize - 1 by
        omega) hb
      omega

/-- The fuel after the setup holds the rounds of the first batch. -/
theorem initial_room (index : Fin (treeBatches settings tree))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (head : List Job) (rest : List (List Job)) (chunked : firstChunks settings tree = head :: rest) :
    depth (head.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) *
      settings.mode.rounds + 1 ≤ (TreeCheckWalkDef.initial K circuits settings top tree x p).fuel := by
  have mem : head ∈ firstChunks settings tree := by rw [chunked]; exact List.mem_cons_self
  have bounded : runRounds settings.mode
      (runCircuits circuits (x (refHolder D K.publicTerm)).parameter head) ≤
        maxBatch circuits settings (runRounds settings.mode) := by
    cases tree with
    | top =>
        exact measure_le_maxBatch circuits settings (runRounds settings.mode)
          (x (refHolder D K.publicTerm)).parameter ⟨0, Nat.two_pow_pos _⟩ (fun _ => digit 0) head
          (Or.inl mem)
    | bottom b =>
        exact measure_le_maxBatch circuits settings (runRounds settings.mode)
          (x (refHolder D K.publicTerm)).parameter b (fun _ => digit 0) head (Or.inr (Or.inl mem))
  have batches : 1 ≤ ceremonyBatches settings :=
    (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) index.isLt)).trans
      (treeBatches_le_ceremonyBatches settings tree)
  change _ ≤ ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode)
  have rounds : depth (head.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) *
      settings.mode.rounds + 1 ≤ runRounds settings.mode
        (runCircuits circuits (x (refHolder D K.publicTerm)).parameter head) := by
    unfold runRounds runCircuits
    omega
  calc _ ≤ maxBatch circuits settings (runRounds settings.mode) := rounds.trans bounded
    _ = 1 * maxBatch circuits settings (runRounds settings.mode) := (one_mul _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ batches

/-- The walk of the first batch has no finished outcome. -/
theorem initial_no_terminal (hb : 0 < settings.batchSize) (index : Fin (treeBatches settings tree))
    (zero : index.val = 0)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) (r : TreeCheckTailResult A) :
    .inr r ∉ support (walk prims K D A circuits settings top tree x p.1.2 0 Z
      (TreeCheckWalkDef.initial K circuits settings top tree x p).fuel
      (TreeCheckWalkDef.initial K circuits settings top tree x p)) := by
  obtain ⟨head, rest, chunked⟩ := List.exists_cons_of_ne_nil
    (firstChunks_ne_nil settings tree hb index zero)
  refine walk_no_terminal prims K D A circuits settings top tree x p.1.2 0 Z _ _ ?_ r
  intro current hc
  have same : current = TreeCheckWalkDef.initial K circuits settings top tree x p := by
    unfold prepare at hc
    cases tree with
    | top => simpa only [mem_support_pure_iff] using hc
    | bottom b =>
        have notFirst : ¬ (0 = (firstChunks settings (.bottom b)).length) := by
          rw [chunked]
          simp
        simp only [if_neg notFirst, mem_support_pure_iff] at hc
        exact hc
  subst same
  exact initial_decode_hit prims K D A circuits settings top tree x p head rest chunked
    (initial_room K D A circuits settings top tree x index p head rest chunked)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 2000 in
/-- The `Unreached` clause of the first batch. The decoder recognizes the
state after the setup, so the walk has no finished outcome. -/
theorem unreached_first (hb : 0 < settings.batchSize) (z : Aux) (q : ℕ)
    (bounded : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (index : Fin (treeBatches settings tree)) (zero : index.val = 0)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    (family prims K circuits settings top tree D A x Z q bounded index p).Unreached
      prims K circuits settings D top tree x z index := by
  intro r run
  have none := initial_no_terminal prims K D A circuits settings top tree x Z hb index zero p r
  rw [← zero] at none
  with_reducible exact absurd run none

end First

section Assembly

/-- The `Unreached` clause of the fixed family for the batches after the
first one. -/
def WalkUnreachedLater : Prop :=
  AtWalk prims K circuits settings fun top tree D _ x z _ _ _ j _ W =>
    j.val ≠ 0 → W.Unreached prims K circuits settings D top tree x z j

/-- `WalkUnreached` from the clause of the later batches. -/
theorem walkUnreached_of_later (later : WalkUnreachedLater prims K circuits settings) :
    WalkUnreached prims K circuits settings := by
  intro hb top tree D A x z Z q dealt bounded small j p hp
  by_cases zero : j.val = 0
  · exact unreached_first prims K D A circuits settings top tree x Z hb z q bounded j zero p
  · exact later hb top tree D A x z Z q dealt bounded small j p hp zero

end Assembly

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkUnreached.walk_terminal_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walk_terminal_finish

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkUnreached.walk_no_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walk_no_terminal

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkUnreached.firstChunks_ne_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstChunks_ne_nil

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkUnreached.initial_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initial_room

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkUnreached.unreached_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unreached_first

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkUnreached.initial_no_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initial_no_terminal

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkUnreached.walkUnreached_of_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkUnreached_of_later

end TreeCheckWalkUnreached
end ThresholdLeanXmssSecurity
