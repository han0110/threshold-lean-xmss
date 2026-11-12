import ThresholdLeanXmssSecurity.Proof.TreeSaltPairsFinal

/-!
# The run can steer the stage-2 table after a hidden stage-1 salt

`TreeSaltPairsFinal.PairBoundsFrom` bounds each pair `i < j` of the fixed tables
`Fin.append (enumerate firstSet) (enumerate (secondSet m))` by `2^-256`. The direct proof uses one
fixed stage-2 address at index `j`. That address depends on `m` through
`TreeSaltPairsFinal.encoding`. The trace below shows that the run can change `encoding` of a bottom
tree after a hidden stage-1 salt `s₁` is read, and that this change can depend on the digest of
`s₁`. So the address at index `j` is not independent of `s₁`, and the fixed-address coupling does
not apply.

## The trace

1. Let `t = 3`, so `n = 5`, the terms are the ten 2-subsets, and the holders of `T` are `Tᶜ`. Each
   party lies in four terms. The five filled terms `K.filled i` hold only ten party slots, so some
   party `d` lies in an unfilled term `T`. Let `D = {d}`. Then `T` has no corrupt
   holder, so `T` is hidden. Let `settings.mode = .peer` and `settings.batchSize = 1`, so the first
   run of `.bottom b` has more than one batch.
2. Each batch starts with the histories `fun _ => []` (`ceremonyWith`). In peer mode only `record`
   writes a history, and it writes only the filled terms (`record_peer_history`). So at the check
   of a first-run batch `k`, the history of `T` is `[]`, and `hist = H(.history [])` is a public
   value.
3. The check of batch `k` reads the hidden salt `s₁ = Rand(ρ, 2)` of `T`. This address is in
   `firstSet`. `compareDigests` sends `d_T = H(.digest s₁ hist)` to every operator, and so to `d`.
4. The adversary queries `H(.digest g hist)` for a value `g` and compares the answer with `d_T`.
   Outside a budget collision, equal answers give `s₁ = g`. Different answers give `s₁ ≠ g`. A
   query with `g = s₁` is `TreeSimSaltGuess`, which `PairBoundsFrom` does not exclude.
5. In batch `k + 1`, which is still in the first run, `d` decides from step 4 whether it adds a
   nonzero error to its value `u` of an AND gate of its filled term `K.filled d`. It sends the same
   value to every other holder, so `compareDigests` agrees. The GS20 check accepts a nonzero error
   for some challenge values, and the challenges are answers of `H`. So the run accepts a wrong
   output of batch `k + 1` with positive probability. `TreeSimWrongOutput` names this event.
6. A wrong first-run output changes `cpk`, the commitments or `ρ`. So it changes the root, the
   message, `grind` and the encoding of `signJobs b`. `TreeSaltPairsFinal.encoding` reads this
   encoding from the honest programs at `m`. The labels of the second run, `secondSet m`, and the
   `Finset.equivFin` order then change. So the address at index `j`, and its known salt
   `PRG(key, label)`, depend on the decision in step 5.

The decision in step 5 depends on `s₁` through `d_T`. The address at index `j` depends on that
decision. So the run steers which address lands at index `j` after `s₁` is fixed. This trace does
not show that `PairBoundsFrom` is false. It shows only that a per-pair bound needs an argument over
the wrong-output and guess branches, and not a fixed stage-2 address.

## Lemmas

* `filler_peer_eq_none` states that a term outside `filledTerms K` has no filler in peer mode.
* `record_peer_history` states that a peer `record` keeps the history of such a term.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.TreeSaltPairsBound

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}
variable (K : Constants C E) (ctx : Context C)

theorem filler_peer_eq_none (T : C.Term) (hT : T ∉ filledTerms K) (g : ℕ) :
    filler K .peer T g = none := by
  simp only [filler, List.find?_eq_none, decide_eq_true_eq]
  intro i _ eq
  exact hT (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, eq⟩)

theorem record_peer_history {R : Type} (codec : Codec C E R) (z : Shares C R) (count : ℕ)
    (T : C.Term) (hT : T ∉ filledTerms K) (s : RunState C) :
    ∃ s' : RunState C, (record (G := G) K ctx codec .peer z count).run s = pure ((), s') ∧
      s'.history T = s.history T := by
  refine ⟨_, rfl, ?_⟩
  simp only [filler_peer_eq_none K T hT, Option.isSome_none, List.filter_false, List.flatMap_nil,
    List.append_nil, ite_self]

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltPairsBound.filler_peer_eq_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms filler_peer_eq_none

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltPairsBound.record_peer_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms record_peer_history

end ThresholdLeanXmssSecurity.TreeSaltPairsBound
