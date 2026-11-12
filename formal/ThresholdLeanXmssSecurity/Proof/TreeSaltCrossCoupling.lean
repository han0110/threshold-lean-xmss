import ThresholdLeanXmssSecurity.Proof.TreeSaltGuardedPairBound

/-!
# The cross pairs of a hidden stage-1 salt

`TreeSaltGuardedPairBound.CrossHiddenBound` bounds the guarded least-reuse event of a hidden
stage-1 entry `i` and a stage-2 entry `j` of A66's tables on the actual paired run by exactly
`2^-256`. This module checks that the exact bound is true, and removes the stage-2 run from it.

## Truth audit

Let `a` be the address at `i`, and let `s₁` be its salt. The event is
`¬ TreeSimHashBudgetCollision ∧ ¬ TreeSimSaltGuess D ∧ TreeSaltLeastPairReuse D table i j` on the
final log. These facts come from the definitions.

* `TreeSaltLeastPairReuse` compares two table entries `i' < j'` with one hidden side. It holds for
  `(i, j)` and fails for every pair with `j' < j`. Since `j ≥ n₁`, it fails for every pair of two
  stage-1 entries.
* The pair `(i, j)` is in the event both when the entry `j` is hidden and when it is known.
  `TreeSaltPairReuse` needs only one hidden side.
* `TreeSimSaltGuess` holds when the log has a counted `.digest s₁ h` for any history `h`. The
  query can come before or after the read of `s₁`. The counted part of the log includes the
  retained prefix, because `prefixState` runs `pre` as the adversary.

The view `m` at the stage point can depend on `s₁` only through these channels.

1. The adversary can make a counted `.digest v h` with `v = s₁`. This is `TreeSimSaltGuess`.
2. An honest operator can make a free `.digest v h` with `v = s₁` at another address. `compareDigests`
   (`Scheme.lean`) is the only honest use of `.digest`, and its salt is a read of index 2. Outside a
   budget collision, `first_agreement_from` puts every such read before `m` into `firstSet`. So a
   hit is a reuse of two stage-1 entries, which the least-reuse event excludes.
3. No part of the run programs `H`. `worldRoles` lifts only `LocalSpec` into the counted copy,
   so the prefix, the setup and both stages never send `.inl (.inr _)`.
4. No other part of the run uses the salt. `randBits 256` feeds only `compareDigests`, which sends
   only the digests. A counted PRG query of a hidden name is AES under `H(.streamKey key)`, not
   the hidden stream. `prssRandomness` reads the salt with `oracleStep` only, and `compareDigests`
   makes the digest query before its `exchange`. So the salt reads and the digest query are in one
   round, no continuation after `compareDigests` uses the salt, and no honest step state at a round
   boundary holds a salt.

The table `Fin.append (enumerate firstSet) (enumerate (secondSet m))` depends on the run only
through `m`. `encoding` reads the honest step states `m.1.2` only through `SegmentsStep` and
`TreeLateScheduleShape`, which constrain the labels and rounds of later reads. Let `I` be the run
that answers the honest digests at `a` from an independent table. The real run and `I` are equal
until a hit of channel 1 or 2. The view `m` itself holds `s₁`, in the hidden cache, in the log and
in the hash-cache key `.digest s₁ h`. But in `I` the value `s₁` does not change the step states,
the answers of `H`, or any other hidden stream. The salt at `j` is a fresh hidden value at another
address or AES of a fixed label under `H(.streamKey key)`. So in `I` the salt at `j` equals `s₁`
with probability exactly `2^-256`. The guarded real event is a subset of the event of `I` on the
runs with no hit.

A failed guess `v` tells the adversary that `s₁ ≠ v`. This does not raise the bound. The view `m`
holds `s₁` itself, so the bound does not condition on `m`. It fixes the information that does not
depend on `s₁` in `I`: the selected address at `j`, its branch and its key weights. In `I` these
are independent of `s₁`, so their expected potential is at most `2^-256`. The guards are an
indicator at most `1`, so the guarded real event has probability at most `2^-256`. A guess of `s₁`
is excluded by the guard, so it adds nothing. The A116 steering trace needs a successful guess,
so the guard removes it. Thus the exact bound holds with no slack. This argument is on paper, and
Lean does not check it.

## Lemmas

* `treeSimSaltGuess_mono` and `treeSaltPairReuse_mono` state that both events persist when the log
  grows.
* `FirstClean` is the part of the guards that the log at the stage point fixes. `crossWeight` is
  a potential that bounds the probability that the salt at `b` equals the salt at `a` after the
  state `c`. It is the pair potential of two hidden salts, or `knownPotential` for a known `b`.
* `hidden_le_weight` and `known_le_weight` bound the reuse by these two potentials from any
  coherent state.
* `rest_le_weight` bounds the reuse of `a` and `b` in the run after the stage point by
  `crossWeight` at the stage point.
* `CrossFirstStage` states that the expected `stageWeight` over the first stage is at most
  `2^-256`. `stageWeight` is `crossWeight` of the entry `j` of `secondSet m` on the views where
  `FirstClean` holds, and `0` otherwise.
* `crossHiddenBound_of_firstStage` proves `CrossHiddenBound` from `CrossFirstStage`.

`CrossFirstStage` keeps the hidden and the known stage-2 branch in one sum. It drops the guards of
the stage-2 run, so it bounds a larger event than `CrossHiddenBound`. It is true by the audit, on
paper. On a view with `FirstClean`, the real stage-1 run equals `I` up to a hit, and the
`FirstClean` indicator is at most `1` in `I`. Besides the points of `a`, `stageWeight` reads the
step states for the table, the cache at `.streamKey b.2.1` and the hidden points of `b`. In `I`
these do not depend on `s₁`. For a uniform `s₁` the expected `crossWeight` is then exactly
`2^-256` in both branches. Each open or cached position of a hidden `b` matches with probability
`1/2`. For a known `b`, each candidate key gives `2^-256`, and `keyWeight_sum` sums the key
weights to `1`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.TreeSaltCrossCoupling

open TreeSaltGuardedPairBound

attribute [local instance] Classical.propDecidable

variable {C : Committee}

theorem treeSimSaltGuess_mono {D : C.Coalition} {a b : TreeSimLog C} (hab : a <+: b) :
    TreeSimSaltGuess D a → TreeSimSaltGuess D b := by
  have mem : ∀ {v}, v ∈ a → v ∈ b := fun hv => hab.sublist.subset hv
  rintro ⟨salt, hist, h, ⟨hl, T, key, label, hT, hs⟩, hq⟩
  exact ⟨salt, hist, h, ⟨hl, T, key, label, hT, fun g => mem (hs g)⟩, mem hq⟩

theorem treeSaltPairReuse_mono {D : C.Coalition} {n : ℕ} {addr : Fin n → C.Term × HashOutput × ℕ}
    {i j : ℕ} {a b : TreeSimLog C} (hab : a <+: b) :
    TreeSaltPairReuse D addr i j a → TreeSaltPairReuse D addr i j b := by
  have mem : ∀ {v}, v ∈ a → v ∈ b := fun hv => hab.sublist.subset hv
  rintro ⟨hi, hj, salt, hl, hk, hsa, hsb⟩
  exact ⟨hi, hj, salt, hl, hk, fun g => mem (hsa g), fun g => mem (hsb g)⟩

/-- The guards of the cross event that the log at the stage point fixes, with the stage-1 table
`addr`. -/
def FirstClean (D : C.Coalition) {n : ℕ} (addr : Fin n → C.Term × HashOutput × ℕ)
    (log : TreeSimLog C) : Prop :=
  ¬ TreeSimHashBudgetCollision log ∧ ¬ TreeSimSaltGuess D log ∧
    ∀ i' j' : ℕ, i' < j' → ¬ TreeSaltPairReuse D addr i' j' log

/-- The probability that the salt at `b` equals the hidden salt at `a` after the state `c`. -/
def crossWeight (prims : Primitives) (D : C.Coalition) (a b : C.Term × HashOutput × ℕ)
    (c : HashCache C × HiddenCache C) : ℝ≥0∞ :=
  if KnownTo D.1 b.1 then knownPotential prims a b c
  else saltPairWeight (fun g => .inl (saltPoint a g)) (fun g => .inl (saltPoint b g)) c.2

/-- Two hidden addresses read the same salt with probability at most their pair potential.
The first part of `hidden_pair_le` (`TreeSaltGuardedPairBound.lean`), with no open address. -/
theorem hidden_le_weight (prims : Primitives) (D : C.Coalition) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (s : TreeSimState C) (hs : HiddenCoherent D s)
    (a b : C.Term × HashOutput × ℕ) (hab : a ≠ b)
    (ha : ¬ KnownTo D.1 a.1) (hb : ¬ KnownTo D.1 b.1) :
    Pr[fun r => SameSalt r.2.2 a b | (simulateQ (treeSimLoggedWorld prims D) oa).run s] ≤
      saltPairWeight (fun g => .inl (saltPoint a g)) (fun g => .inl (saltPoint b g)) s.1.2 := by
  let u : Fin 256 → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) ⊕ Bit := fun g => .inl (saltPoint a g)
  let v : Fin 256 → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) ⊕ Bit := fun g => .inl (saltPoint b g)
  have point : ∀ (c c' : C.Term × HashOutput × ℕ) (g g' : Fin 256),
      saltPoint c g = saltPoint c' g' → c = c' ∧ g = g' := by
    intro c c' g g' h
    simp only [saltPoint, Prod.mk.injEq, KeyName.term.injEq] at h
    exact ⟨Prod.ext h.1.1 (Prod.ext h.1.2 h.2.1), Fin.ext h.2.2.2⟩
  have hd : SaltPairDistinct u v := by
    rintro (g | g) (g' | g') d hx hy <;>
      simp only [Sum.elim_inl, Sum.elim_inr, u, v, Sum.inl.injEq] at hx hy <;>
      obtain ⟨hc, hg⟩ := point _ _ _ _ (hx.trans hy.symm)
    · rw [hg]
    · exact (hab hc).elim
    · exact (hab hc.symm).elim
    · rw [hg]
  have mono : Pr[fun r => SameSalt r.2.2 a b | (simulateQ (treeSimLoggedWorld prims D) oa).run s] ≤
      Pr[fun r => SaltPairEqual u v r.2.1.2 | (simulateQ (treeSimLoggedWorld prims D) oa).run s] := by
    apply probEvent_mono
    rintro r hr ⟨salt, -, hsa, hsb⟩ g
    have coh := hiddenCoherent_run prims D oa s hs r hr
    refine ⟨salt.getD g.val 0, ?_, ?_⟩
    · exact (coh (.term a.1, a.2.1, a.2.2, 2, g.val) _ ha).mp (hsa g)
    · exact (coh (.term b.1, b.2.1, b.2.2, 2, g.val) _ hb).mp (hsb g)
  exact mono.trans (treeSimLogged_saltPair_le D hd oa s)

/-- A hidden salt and a known salt are equal with probability at most `knownPotential`.
The first part of `known_pair_le` (`TreeSaltGuardedPairBound.lean`), with no open address. -/
theorem known_le_weight (prims : Primitives) (a b : C.Term × HashOutput × ℕ) (D : C.Coalition)
    {α : Type} (g : OracleComp (LocalSpec C + LocalSpec C) α) (s : TreeSimState C)
    (hs : HiddenCoherent D s) (hpub : PublicCoherent prims D s)
    (ha : ¬ KnownTo D.1 a.1) (hb : KnownTo D.1 b.1) :
    Pr[fun r => SameSalt r.2.2 a b | (simulateQ (treeSimLoggedWorld prims D)
      (simulateQ treeSimLocalWorld g)).run s] ≤ knownPotential prims a b s.1 := by
  have mono : Pr[fun r => SameSalt r.2.2 a b | (simulateQ (treeSimLoggedWorld prims D)
      (simulateQ treeSimLocalWorld g)).run s] ≤
      Pr[fun r => 1 ≤ knownPotential prims a b r.2.1 | (simulateQ (treeSimLoggedWorld prims D)
        (simulateQ treeSimLocalWorld g)).run s] := by
    apply probEvent_mono
    rintro r hr ⟨salt, -, hsa, hsb⟩
    have hc := hiddenCoherent_run prims D _ s hs r hr
    have hp := publicCoherent_run prims D _ s hpub r hr
    have hknown : ¬ Hidden D (KeyName.term b.1) := fun h => h hb
    obtain ⟨k, hk, -⟩ := hp (.term b.1, b.2.1, b.2.2, 2, 0) _ hknown (hsb ⟨0, by norm_num⟩)
    refine le_trans ?_ (Finset.single_le_sum (fun k _ => zero_le (α := ℝ≥0∞)) (Finset.mem_univ k))
    have hw : keyWeight b r.2.1.1 k = 1 := by simp [keyWeight, hk]
    rw [hw, one_mul]
    apply saltPairWeight_of_equal
    intro g
    refine ⟨salt.getD g.val 0, (hc (.term a.1, a.2.1, a.2.2, 2, g.val) _ ha).mp (hsa g), ?_⟩
    obtain ⟨k', hk', hv⟩ := hp (.term b.1, b.2.1, b.2.2, 2, g.val) _ hknown (hsb g)
    rw [hk] at hk'
    cases hk'
    simp only [saltSideValue, keyBit, Option.some.injEq]
    exact hv.symm
  refine mono.trans ?_
  rw [← QueryImpl.simulateQ_compose]
  have key := XmssSecurity.probEvent_le_expectedFinal
    (treeSimLoggedWorld prims D ∘ₛ treeSimLocalWorld) (fun s : TreeSimState C => knownPotential prims a b s.1)
    (fun s => 1 ≤ knownPotential prims a b s.1) (fun _ h => h) g s
  refine key.trans ?_
  have h := XmssSecurity.expectedFinal_le (treeSimLoggedWorld prims D ∘ₛ treeSimLocalWorld)
    (Inv := fun _ => True) (fun _ _ _ _ _ => trivial) (fun s => knownPotential prims a b s.1)
    (fun _ _ => 0) (fun t s _ => by simpa only [add_zero] using potential_step prims a b D t s) g s trivial
  have hz : XmssSecurity.expectedSimulatedCost (treeSimLoggedWorld prims D ∘ₛ treeSimLocalWorld)
      (fun _ _ => 0) g s = 0 := by
    simpa using XmssSecurity.expectedSimulatedCost_const_mul
      (treeSimLoggedWorld prims D ∘ₛ treeSimLocalWorld) 0 (fun _ _ => 0) g s
  rw [hz, add_zero] at h
  exact h

section Parts

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The run after the stage point makes the salt at `b` equal to the hidden salt at `a` with
probability at most `crossWeight` at the stage point. -/
theorem rest_le_weight (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (TreeSaltPairsFinal.first prims K circuits settings top tree D A x p))
    (a b : C.Term × HashOutput × ℕ) (hab : a ≠ b) (ha : ¬ KnownTo D.1 a.1) :
    Pr[fun r => SameSalt r.2.2 a b | (simulateQ (treeSimLoggedWorld prims D)
      (restProgram circuits settings tree D A x Z m)).run m.2] ≤ crossWeight prims D a b m.2.1 := by
  have hcoh := hiddenCoherent_first prims K circuits settings top tree D A x p
    (hiddenCoherent_setup prims D A x z pre s hs p hp) m hm
  unfold crossWeight
  split_ifs with kb
  · rw [restProgram_local]
    exact known_le_weight prims a b D _ m.2 hcoh
      (publicCoherent_first prims K circuits settings top tree D A x p
        (publicCoherent_setup prims D A x z pre s hs p hp) m hm) ha kb
  · exact hidden_le_weight prims D _ m.2 hcoh a b hab ha kb

/-- `crossWeight` of the entry `j` of the stage-2 table of `m`, on the views where `FirstClean`
holds, and `0` otherwise. -/
def stageWeight (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C)) (i j : ℕ)
    (hi : i < (TreeSaltPairsFinal.firstSet circuits settings tree x setup).card)
    (m : TreeSimConfig A (TreeSimState C)) : ℝ≥0∞ :=
  if FirstClean D (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x setup))
      m.2.2 then
    if h : j - (TreeSaltPairsFinal.firstSet circuits settings tree x setup).card <
        (TreeSaltPairsFinal.secondSet circuits settings tree D x setup A m).card then
      crossWeight prims D
        (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x setup) ⟨i, hi⟩)
        (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.secondSet circuits settings tree D x setup A m)
          ⟨j - (TreeSaltPairsFinal.firstSet circuits settings tree x setup).card, h⟩) m.2.1
    else 0
  else 0

/-- The expected `stageWeight` over the first stage of the actual paired run is at most
`2^-256`, for a hidden stage-1 entry `i` and a stage-2 index `j`. -/
def CrossFirstStage : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ {α : Type} (pre : OracleComp (LocalSpec C) α),
    ∀ s ∈ support (LifetimeSaltFrom.prefixState prims D pre),
    ∀ p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2),
    ∀ i j : ℕ, (hi : i < (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2).card) →
      (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2).card ≤ j →
      ¬ KnownTo D.1
        (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2)
          ⟨i, hi⟩).1 →
      ∑' m, Pr[= m | TreeSaltPairsFinal.first prims K circuits settings top tree D A x p] *
          stageWeight prims circuits settings tree D A x p.1.2 i j hi m ≤ (2 ^ 256 : ℝ≥0∞)⁻¹

/-- `CrossHiddenBound` follows from the first-stage bound `CrossFirstStage`. -/
theorem crossHiddenBound_of_firstStage (stage : CrossFirstStage prims K circuits settings) :
    CrossHiddenBound prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall α pre s hs p hp i j hi hj ka
  refine le_trans ?_ (stage hb top tree D A x z Z q hx hq hsmall pre s hs p hp i j hi hj ka)
  change Pr[_ | TreeSaltPairsFinal.first prims K circuits settings top tree D A x p >>= fun m =>
    (fun r => (m, r)) <$> TreeSaltPairsFinal.rest prims circuits settings tree D A x Z m] ≤ _
  rw [probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun m => ?_
  by_cases hm : m ∈ support (TreeSaltPairsFinal.first prims K circuits settings top tree D A x p)
  swap
  · simp [probOutput_eq_zero_of_not_mem_support hm]
  refine mul_le_mul_right ?_ _
  rw [probEvent_map, TreeSaltGuardedPairBound.rest_eq, probEvent_map]
  unfold stageWeight
  set F := TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2 with hF
  set S := TreeSaltPairsFinal.secondSet circuits settings tree D x p.1.2 A m with hS
  have eF : F.card = (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2).card := rfl
  have eS : S.card = (TreeSaltPairsFinal.secondSet circuits settings tree D x p.1.2 A m).card := rfl
  simp only [Function.comp_def]
  split_ifs with clean hjS
  · refine le_trans (probEvent_mono ?_) (rest_le_weight prims K circuits settings top tree D A x z Z
      pre s hs p hp m hm _ _ ?_ ka)
    · rintro r - ⟨-, -, -, hi', hj', salt, hl, -, hsa, hsb⟩
      rw [append_left_eq _ _ i hi' hi] at hsa
      rw [append_right_eq _ _ j hj' hj] at hsb
      exact ⟨salt, hl, hsa, hsb⟩
    · intro h
      exact (Finset.mem_sdiff.mp (TreeSaltPairsFinal.enumerate_mem S _)).2
        (h ▸ TreeSaltPairsFinal.enumerate_mem F _)
  · refine le_of_eq (probEvent_eq_zero fun r _ h => ?_)
    obtain ⟨-, -, -, -, hj', -⟩ := h
    exact hjS (by omega)
  · refine le_of_eq (probEvent_eq_zero fun r hr h => clean ?_)
    have grow : m.2.2 <+: r.2.2 := treeSimLoggedWorld_prefix prims D _ m.2 r hr
    obtain ⟨hc, hg, hleast, -⟩ := h
    refine ⟨fun bad => hc (treeSimHashBudgetCollision_mono grow bad),
      fun bad => hg (treeSimSaltGuess_mono grow bad), fun i' j' hij reuse => ?_⟩
    obtain ⟨hi', hj', salt, hl, hk, hsa, hsb⟩ := treeSaltPairReuse_mono grow reuse
    refine hleast i' j' hij (by omega) ⟨by omega, by omega, salt, hl, ?_, ?_, ?_⟩
    · rwa [append_left_eq _ _ i' _ hi', append_left_eq _ _ j' _ hj']
    · rwa [append_left_eq _ _ i' _ hi']
    · rwa [append_left_eq _ _ j' _ hj']

end Parts

end ThresholdLeanXmssSecurity.TreeSaltCrossCoupling

open ThresholdLeanXmssSecurity.TreeSaltCrossCoupling in
/--
info: 'ThresholdLeanXmssSecurity.TreeSaltCrossCoupling.crossHiddenBound_of_firstStage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms crossHiddenBound_of_firstStage

/--
info: 'ThresholdLeanXmssSecurity.TreeSaltCrossCoupling.rest_le_weight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeSaltCrossCoupling.rest_le_weight
