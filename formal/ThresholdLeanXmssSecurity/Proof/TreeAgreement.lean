import ThresholdLeanXmssSecurity.Proof.TreeSaltGuard
import ThresholdLeanXmssSecurity.Proof.TreeCheckCut

/-!
# The agreement of the honest operators in the real tree run

Three open tree statements need one fact about the real run. The honest operators that did not
abort agree on the term keys, the round labels, the tag and the jobs of each batch, unless a
collision over `TreeSimHashBudgetDomain` occurs.

* `prssEchoAccepted_agree` is the setup step. Two honest operators that accept the echo agree
  on the key of each term that they both hold, outside a collision of the two `.sharedKeys`
  inputs.
* `stepRound_prssEcho_agree` lifts it to the outputs of the echo round of the logged run.
* `TreeAgreementLog` is the agreement on the honest calls of a log. Its ghost is the common term
  key and the common batches, each with its salt label.
* `treeSaltAddresses_of_agreement` gives the address cover of one run from it, with at most
  `treeBatches * termCount` addresses.
* `treeSimHashProgram_not_budgetCollision` gives the log guard from the cache guard of
  `TreeSimHashHonestBudget`.
* `TreeAgreementSetupKeys` and `TreeAgreementSaltRun` are the open steps on the logged run.

The address cover of `TreeSaltSetupAddresses` fixes the addresses at the end of the setup, for
all runs after it. The block below shows that this statement is false for a bottom tree.
-/

/-
Counterexample to `TreeSaltSetupAddresses` (TreeSaltGuard).

The statement chooses `addr` from the setup result `p` alone, and asks that it covers every run
`r` after `p` with `n ≤ treeBatches settings tree * termCount C`.

1. Take `tree = .bottom b`, `D = noCoalition`, the honest adversary, and `settings.batchSize`
   at least `(bottomJobs b).length` and at least `numChains`. Then
   `treeBatches settings (.bottom b) = 2`, one batch for each run.
2. Take `circuits` where each circuit has at least one output, so the tuple count of each
   batch is not zero and `check` reaches `randBits`. Fix a chain `l₀` at which two codewords
   differ. Let `circuits P (.chainValue e l p)` have `p.val + 1` AND layers if `l = l₀`, and one
   AND layer otherwise.
3. In batch `k`, `check` reads `Rand(ρ, 2)` (`realCheckGadgets.randBits`) at one label `ρ`.
   This label is the start label of the batch plus `depth jobs` (one label for each `mult`),
   plus one for `rerand`, plus the labels of the coins and the halving steps of the check
   (see `batchLabels`, Tree.lean). So it grows with `depth jobs`.
4. The jobs of the second run are `signJobs b encoding`. The start label of the second batch is
   fixed, since the first run has the fixed jobs `bottomJobs b`. Its depth is
   `1 + (encoding l₀).val`. The digests of `grind` are random-oracle inputs (not `MpcInput`), and
   no call before the second run asks them, so after one `p` each codeword is reachable. Two
   runs with different `encoding l₀` read the salts at two different labels.
5. With no corrupt operator, every term has an honest holder, and every honest holder reads the
   salt of its terms at the salt label of each batch. Runs with no budget collision exist for
   each codeword. So the cover needs `termCount C` addresses for the first batch and
   `2 * termCount C` for the second, which is more than `2 * termCount C`.

Steps 1 to 4 follow from the definitions. Step 5 uses that an honest run passes each check
and reaches the second run. This is deduced from the completeness of the check, and is not
proved here.

The per-run cover holds (`treeSaltAddresses_of_agreement`). A fixed cover must be chosen after
the first run, where the jobs of the second run are known.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- Two honest operators that accept the PRSS echo agree on the key of each term that they both
hold, outside a collision of their two `.sharedKeys` inputs. -/
theorem prssEchoAccepted_agree (D : C.Coalition) (active : C.Party → Prop)
    (sent : C.Party → Mail C E) (h : Query C → HashOutput)
    (keys : C.Party → C.Term → HashOutput) (i j : C.Party)
    (hi : prssEchoAccepted D active sent h keys i) (hj : prssEchoAccepted D active sent h keys j)
    (hn : prssEcho h keys i j = prssEcho h keys j i →
      Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
      Query.sharedKeys .prss ((sharedTerms j i).map (keys j))) :
    ∀ T, i ∈ C.holders T → j ∈ C.holders T → keys i T = keys j T := by
  by_cases hij : i = j
  · subst hij
    exact fun _ _ _ => rfl
  apply (prssEcho_eq_iff h keys i j hn).mp
  have hc := hi.2.2.2 j (Ne.symm hij)
  simp only [prssEchoInbox, if_neg hj.1, if_pos hj.2.1, if_neg hij, Msg.hashesOf,
    List.cons.injEq, and_true] at hc
  exact hc.symm

/-- The echo round of the PRSS setup, under any handler of the world. Two honest outputs agree
on the key of each term that both operators hold, outside a `.sharedKeys` collision of `h`. -/
theorem stepRound_prssEcho_agree {σ : Type} (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (active : C.Party → Prop)
    (h : Query C → HashOutput) (out : C.Party → PrssKeys C) (state : A.State) (s : σ)
    (r : (A.State × (C.Party → Step C E RealSpec (PrssKeys C)) × (C.Party → Mail C E)) × σ)
    (hr : r ∈ support ((simulateQ impl
      (stepRound worldRoles D A noFunctionality state (prssEchoStep D active h out))).run s))
    (hn : ∀ i j, i ∉ D.1 → j ∉ D.1 →
      prssEcho h (fun k => (out k).term) i j = prssEcho h (fun k => (out k).term) j i →
      Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (out i).term) =
      Query.sharedKeys .prss ((sharedTerms j i).map (out j).term))
    (i j : C.Party) (ki kj : PrssKeys C)
    (hi : (r.1.2.1 i).output = some ki) (hj : (r.1.2.1 j).output = some kj) :
    ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.term T = kj.term T := by
  rw [stepRound_prssEcho] at hr
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hr
  obtain ⟨adv, _, rfl⟩ := hr
  simp only [Step.output] at hi hj
  split_ifs at hi with hai
  split_ifs at hj with haj
  cases hi
  cases hj
  exact prssEchoAccepted_agree D active adv.1.2 h _ i j hai haj (hn i j hai.1 haj.1)

/-- The agreement on the honest salt reads of a log. The ghost is the common key of each term
and the salt label of each batch so far. Each honest read of `Rand(ρ, 2)` uses the common key
of its term and the salt label of one batch. -/
structure TreeAgreementLog (keys : C.Term → HashOutput) (saltLabels : List ℕ)
    (log : TreeSimLog C) : Prop where
  salt : ∀ (T : C.Term) (key : HashOutput) (label g : ℕ) (b : Bit),
    (⟨.inr (.inr (.inr (.term T, key, label, 2, g))), b⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log →
    key = keys T ∧ label ∈ saltLabels

/-- The salt addresses of a log with agreement lie in the range of one injective table with at
most `termCount` addresses for each batch. -/
theorem treeSaltAddresses_of_agreement (keys : C.Term → HashOutput) (saltLabels : List ℕ)
    (log : TreeSimLog C) (agree : TreeAgreementLog keys saltLabels log) :
    ∃ (n : ℕ) (addr : Fin n → C.Term × HashOutput × ℕ),
      Function.Injective addr ∧ n ≤ saltLabels.length * termCount C ∧
      TreeSaltAddressesCover addr log := by
  let S : Finset (C.Term × HashOutput × ℕ) :=
    ((Finset.univ : Finset C.Term) ×ˢ saltLabels.toFinset).image fun a => (a.1, keys a.1, a.2)
  refine ⟨S.card, fun k => (S.equivFin.symm k).1, ?_, ?_, ?_⟩
  · intro a b hab
    exact S.equivFin.symm.injective (Subtype.ext hab)
  · calc S.card ≤ ((Finset.univ : Finset C.Term) ×ˢ saltLabels.toFinset).card :=
          Finset.card_image_le
      _ = termCount C * saltLabels.toFinset.card := by
          rw [Finset.card_product, Finset.card_univ, card_term C, termCount]
      _ ≤ termCount C * saltLabels.length :=
          Nat.mul_le_mul_left _ (List.toFinset_card_le _)
      _ = saltLabels.length * termCount C := Nat.mul_comm _ _
  · intro T key label g b hmem
    obtain ⟨hkey, hlabel⟩ := agree.salt T key label g b hmem
    have hS : (T, key, label) ∈ S := by
      subst hkey
      exact Finset.mem_image.mpr ⟨(T, label), Finset.mem_product.mpr
        ⟨Finset.mem_univ _, List.mem_toFinset.mpr hlabel⟩, rfl⟩
    exact ⟨S.equivFin ⟨_, hS⟩, by simp⟩

/-- A log that agrees with a cache on the budget region has no budget collision when the cache
has none there. -/
theorem treeSimHashBudgetCollision_of_cache (cache : HashCache C) (log : TreeSimLog C)
    (coherent : TreeSimHashRegionCoherent TreeSimHashBudgetDomain cache log)
    (good : ¬ CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain cache)) :
    ¬ TreeSimHashBudgetCollision log := by
  rintro ⟨q, r, h, hq, hr, hne, hqh, hrh⟩
  refine good ⟨q, r, h, h, hne, ?_, ?_, HEq.rfl⟩
  · simp only [splitRegionCache, if_pos hq]
    exact coherent q h hq hqh
  · simp only [splitRegionCache, if_pos hr]
    exact coherent r h hr hrh

section Run

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The setup step on the logged run. Two honest outputs of the PRSS setup agree on the key of
each term that both operators hold, unless the setup log has a budget collision.
`stepRound_prssEcho_agree` proves it for the echo round, with the injectivity of the cache on the
two `.sharedKeys` inputs as a hypothesis. -/
def TreeAgreementSetupKeys : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux),
    ∀ p ∈ support (treeSaltSetup prims D A x z), ¬ TreeSimHashBudgetCollision p.2.2 →
      ∀ (i j : C.Party) (ki kj : PrssKeys C), p.1.2 i = some ki → p.1.2 j = some kj →
        ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.term T = kj.term T

/-- The salt agreement of the real run. The end of the PRSS setup fixes the common term keys.
Each run after it with no budget collision has the salt label of at most `treeBatches` batches.
The labels depend on the run, because the jobs of the second run of a bottom tree do. -/
def TreeAgreementSaltRun : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput), DealtInputs D x →
    ∀ p ∈ support (treeSaltSetup prims D A x z), ∃ keys : C.Term → HashOutput,
      ∀ r ∈ support (treeSaltAfterSetup prims K circuits settings top tree D A x Z p),
        ¬ TreeSimHashBudgetCollision r.2 →
        ∃ saltLabels : List ℕ, saltLabels.length ≤ treeBatches settings tree ∧
          TreeAgreementLog keys saltLabels r.2

/-- The salt agreement gives the address cover of `TreeSaltSetupAddresses` for each run. The
table depends on the run, so it does not give `TreeSaltSetupAddresses` itself. -/
theorem treeSaltRunAddresses_of_agreement
    (agree : TreeAgreementSaltRun prims K circuits settings) (hbatch : 0 < settings.batchSize)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput)
    (hx : DealtInputs D x) (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (treeSaltSetup prims D A x z))
    (r : Bool × TreeSimLog C)
    (hr : r ∈ support (treeSaltAfterSetup prims K circuits settings top tree D A x Z p))
    (good : ¬ TreeSimHashBudgetCollision r.2) :
    ∃ (n : ℕ) (addr : Fin n → C.Term × HashOutput × ℕ),
      Function.Injective addr ∧ n ≤ treeBatches settings tree * termCount C ∧
      TreeSaltAddressesCover addr r.2 := by
  obtain ⟨keys, hkeys⟩ := agree hbatch top tree D A x z Z hx p hp
  obtain ⟨saltLabels, hlen, hlog⟩ := hkeys r hr good
  obtain ⟨n, addr, hinj, hn, hcover⟩ := treeSaltAddresses_of_agreement keys saltLabels r.2 hlog
  exact ⟨n, addr, hinj, hn.trans (Nat.mul_le_mul_right _ hlen), hcover⟩

/-- The guard of `TreeSimHashHonestBudget` gives the guard of the agreement. A run of the
normalized program with no collision in its final budget cache has no budget collision in its
log. -/
theorem treeSimHashProgram_not_budgetCollision (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (r : ((Bool × TreeSimLog C) × HiddenCache C) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (treeSimHashProgram K circuits settings top tree D A x z Z)).run ∅))
    (good : ¬ CacheHasCollision (splitRegionCache TreeSimHashBudgetDomain r.2)) :
    ¬ TreeSimHashBudgetCollision r.1.1.2 :=
  treeSimHashBudgetCollision_of_cache r.2 r.1.1.2
    (treeSimHash_region_normalized_coherent prims TreeSimHashBudgetDomain
      treeSimHashBudgetDomain_not_fixed D _ ∅ ∅ r hr) good

end Run

/-- info: 'ThresholdLeanXmssSecurity.stepRound_prssEcho_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stepRound_prssEcho_agree

/-- info: 'ThresholdLeanXmssSecurity.treeSaltRunAddresses_of_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSaltRunAddresses_of_agreement

/-- info: 'ThresholdLeanXmssSecurity.treeSimHashProgram_not_budgetCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHashProgram_not_budgetCollision

end ThresholdLeanXmssSecurity
