import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkEntry

/-!
# One encoding at the start of the signing run

This file concerns the encoding of the signing run of a bottom tree, for the
fixed walk `family` of `TreeCheckWalkRecipe`. The family, its decoder and its
witness are not changed. `L` is the number of batches of the first run, and
`q` is a state that the scheduler reaches after `batchStart L` rounds.

## Statements

* `SigningHeadsAgree` is the agreement at `j = L`. Take a signing point that
  matches `q`, and two honest parties `i` and `k`. The head of `i` runs from a
  state that extends the world of `q`. The head of `k` runs later, from a
  state that extends the world after the head of `i`. If both heads succeed
  and the log after the head of `k` has no budget collision, then the two
  heads give the same public choice, so also the same encoding. A head that
  rejects gives no choice. The states between the two heads are free, so the
  statement covers the local work of other parties in the same pass.
* `SigningTailsAgree` is stated for the two opening tails `point.tail i` and
  `point.tail k`. It does not ask that the public-choice code succeeds, it
  lets the state of `k` extend the state after the tail of `i`, and it states
  that the two parties run the same public-choice code
  `treeLockstepPublicChoiceCode`. So it asks for more than `SigningHeadsAgree`.
  It holds for the actual opening tails when the parameters and the outputs of
  the first run agree. A matching point does not have to name `openTail` as
  its tail, so the step to every matching point needs a further argument.

## Lemmas

* `head_split` cuts a successful head into its successful tail and the run of
  the public-choice code after it.
* `headsAgree_of_tails` derives `SigningHeadsAgree` from `SigningTailsAgree`.
  The code of `k` repeats the code of `i` in every extension of the cache
  after the head of `i` (`publicRun_replay`, `signingHead_fixed`). The log
  after the tail of `k` is a prefix of the log after its head, so it has no
  budget collision either.

## Later signing boundaries

* `signingCont_caller` states that the program after a head with the choice
  `c` is `callerProgram L` of the caller `signingCaller` with the encoding
  `c.2.2`.
* `signing_later` applies `WalkStateSigning` to this caller. At a later
  signing boundary `j`, after `signRounds c.2.2 j` exchanges, the program is
  `callerProgram j` of a caller with the same encoding `c.2.2`. The round
  index from the start of the run is `batchStart L + signRounds c.2.2 j`.

## Scope

The statements fix one run. They do not give one choice for every extension
of the cache, as the premise `fixed` of `selected_signing_decode_hit` needs.
A fresh query of a wrong copy can still collide on a later branch.

## Route for `SigningTailsAgree`

Take a term `T` in the sum of the last opening.

* If `i` or `k` does not hold `T`, its copy comes from the owner of `T`. At
  least one honest holder of `T` is not the owner and sends the `.copy`
  digest of its share. `treeLockstep_copy_logged` turns this into equal
  copies outside a budget collision. It needs the mail of the last opening
  and the shares of the honest holders, which `point.tail` does not show.
* If both hold `T`, each one uses its own share. The check of the batch runs
  `compareDigests` on the histories `h_T` before its last coin and before
  the opening. The histories hold the values that a filler sends.
* The outputs of the earlier batches of the first run are in the logs of
  those batches, which are prefixes of the log.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace TreeCheckWalkEncoding

open TreeCheckWalkRecipe TreeCheckWalkCoverage TreeCheckWalkState

attribute [local instance] Classical.propDecidable
attribute [local irreducible] treeLockstepPublicChoiceCode

variable {C : Committee} {E : Type}

section Head

variable (prims : Primitives) (D : C.Coalition)

/-- A successful head is a successful tail and then a successful run of the
public-choice code. -/
theorem head_split (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) (gate : OracleComp (LocalSpec C) (Option Unit))
    (s after : TreeSimState C) (choice : PublicChoice)
    (run : (some choice, after) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (signingHead parameter b outputs gate))).run s)) :
    ∃ middle : TreeSimState C,
      (some (), middle) ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free gate)).run s) ∧
      (some choice, after) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (tweakable (C := C) (treeLockstepPublicChoiceCode parameter b outputs))
          (LocalSpec C)))).run middle) := by
  unfold signingHead at run
  simp only [free_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨first, hf, run⟩ := run
  cases accepted : first.1 with
  | none =>
      simp only [accepted, free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
      cases run
  | some u =>
      simp only [accepted] at run
      refine ⟨first.2, ?_, run⟩
      have eq : first = (some (), first.2) := by
        rcases first with ⟨_ | ⟨⟩, _⟩
        · cases accepted
        · rfl
      rw [← eq]
      exact hf

end Head

section Statements

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- At the start of the signing run of a bottom tree, two successful signing
heads of honest parties give the same public choice along a run whose log
after the second head has no budget collision. The second head runs from a
state that extends the world after the first head. -/
def SigningHeadsAgree : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (b : Fin (2 ^ layerHeight)) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput),
      DealtInputs D x →
      ∀ p ∈ support (treeSaltSetup prims D A x z),
      ∀ q, Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x p)
          (batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
            (firstChunks settings (.bottom b)).length) q →
      ∀ point, SigningMatches K D A circuits settings top x p.1.2
          (firstChunks settings (.bottom b)).length b q point →
      ∀ i k, i ∉ D.1 → k ∉ D.1 →
      ∀ s₁ : TreeSimState C, q.world.1.1 ≤ s₁.1.1 → q.world.2 <+: s₁.2 →
      ∀ (c₁ : PublicChoice) (a₁ : TreeSimState C),
        (some c₁, a₁) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (free (signingHead (x i).parameter b (point.outputs i) (point.tail i)))).run s₁) →
      ∀ s₂ : TreeSimState C, a₁.1.1 ≤ s₂.1.1 → a₁.2 <+: s₂.2 →
      ∀ (c₂ : PublicChoice) (a₂ : TreeSimState C),
        (some c₂, a₂) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (free (signingHead (x k).parameter b (point.outputs k) (point.tail k)))).run s₂) →
      ¬ TreeSimHashBudgetCollision a₂.2 → c₁ = c₂

/-- At the start of the signing run of a bottom tree, two successful opening
tails of honest parties lead to the same public-choice code along a run whose
log after the second tail has no budget collision. -/
def SigningTailsAgree : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (b : Fin (2 ^ layerHeight)) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput),
      DealtInputs D x →
      ∀ p ∈ support (treeSaltSetup prims D A x z),
      ∀ q, Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x p)
          (batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
            (firstChunks settings (.bottom b)).length) q →
      ∀ point, SigningMatches K D A circuits settings top x p.1.2
          (firstChunks settings (.bottom b)).length b q point →
      ∀ i k, i ∉ D.1 → k ∉ D.1 →
      ∀ s₁ : TreeSimState C, q.world.1.1 ≤ s₁.1.1 → q.world.2 <+: s₁.2 →
      ∀ t₁ : TreeSimState C,
        (some (), t₁) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (free (point.tail i))).run s₁) →
      ∀ s₂ : TreeSimState C, t₁.1.1 ≤ s₂.1.1 → t₁.2 <+: s₂.2 →
      ∀ t₂ : TreeSimState C,
        (some (), t₂) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (free (point.tail k))).run s₂) →
      ¬ TreeSimHashBudgetCollision t₂.2 →
        treeLockstepPublicChoiceCode (x i).parameter b (point.outputs i) =
          treeLockstepPublicChoiceCode (x k).parameter b (point.outputs k)

theorem headsAgree_of_tails (tails : SigningTailsAgree prims K circuits settings) :
    SigningHeadsAgree prims K circuits settings := by
  intro positive top b D A x z Z dealt p hp q reached point matching i k hi hk
    s₁ grows₁ prefix₁ c₁ a₁ run₁ s₂ grows₂ prefix₂ c₂ a₂ run₂ clean
  obtain ⟨t₁, tail₁, code₁⟩ := head_split prims D _ b _ _ s₁ a₁ c₁ run₁
  obtain ⟨t₂, tail₂, code₂⟩ := head_split prims D _ b _ _ s₂ a₂ c₂ run₂
  have same := tails positive top b D A x z Z dealt p hp q reached point matching i k hi hk
    s₁ grows₁ prefix₁ t₁ tail₁ s₂
    ((treeSim_logged_grows prims D _ t₁ _ code₁).trans grows₂)
    ((treeSimLoggedWorld_prefix prims D _ t₁ _ code₁).trans prefix₂) t₂ tail₂
    (fun bad => clean (treeSimHashBudgetCollision_mono
      (treeSimLoggedWorld_prefix prims D _ t₂ _ code₂) bad))
  obtain ⟨before, public₁⟩ := signingHead_public prims D _ b _ _ s₁ a₁ c₁ run₁
  obtain ⟨_, trace, _, ready⟩ := publicRun_replay prims D _ before (some c₁, a₁) public₁
  rw [same] at ready
  rcases signingHead_fixed prims D (x k).parameter b (point.outputs k) (point.tail k) a₁.1.1 c₁
      (fun cache grows => ⟨trace, ready cache grows⟩) s₂ grows₂ (some c₂, a₂) run₂ with
    rejected | accepted
  · cases rejected
  · exact (Option.some.inj accepted).symm

end Statements

section Later

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (D : C.Coalition) (circuits : Circuits) (settings : Settings)
variable (top : TopTree) (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C))

omit [Fintype E] [DecidableEq E] in
/-- After a head with the choice `choice`, the program of a party is the
program at the first signing batch of a caller with the encoding of
`choice`. -/
theorem signingCont_caller (b : Fin (2 ^ layerHeight))
    (outputs : C.Party → List (List Bit)) (records : C.Party → List (TreeSimCheckBatchRecord C))
    (choice : PublicChoice) (head : List Job) (rest : List (List Job))
    (hchunks : chunks settings.batchSize (signJobs b choice.2.2) = head :: rest) (i : C.Party) :
    signingCont K circuits settings ⟨i, x i, setupKeys setup i⟩ top b (outputs i) (records i)
      (signingInitial K D circuits settings (.bottom b) x) choice =
    callerProgram K D circuits settings top (.bottom b) x setup (firstChunks settings (.bottom b)).length
      (signingCaller outputs records (fun _ => pure (some choice)) choice) i := by
  rw [signingCont_head K D circuits settings top x setup b outputs records
    (fun _ => pure (some choice)) choice head rest hchunks i]
  unfold callerProgram
  simp only [signingCaller, map_pure, Option.map_some, localPrelude_some, pure_bind,
    signing_firstChunk settings b choice.2.2 head rest hchunks, signing_start circuits settings b,
    signingInitial]

omit [Fintype E] [DecidableEq E] in
/-- At a later signing boundary, the program of a party after a head with the
choice `choice` is the program of a caller with the encoding of `choice`. The
round index is `signRounds` of that encoding. -/
theorem signing_later (signing : WalkStateSigning K circuits settings) (b : Fin (2 ^ layerHeight))
    (outputs : C.Party → List (List Bit)) (records : C.Party → List (TreeSimCheckBatchRecord C))
    (choice : PublicChoice) (head : List Job) (rest : List (List Job))
    (hchunks : chunks settings.batchSize (signJobs b choice.2.2) = head :: rest) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (j : ℕ) (first : (firstChunks settings (.bottom b)).length ≤ j)
    (current : j < treeBatches settings (.bottom b))
    (Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C))))
    (h : Residual (signRounds circuits settings (x (refHolder D K.publicTerm)).parameter choice.2.2
        (.bottom b) j)
      (signingCont K circuits settings ⟨i, x i, setupKeys setup i⟩ top b (outputs i) (records i)
        (signingInitial K D circuits settings (.bottom b) x) choice).run Q) :
    ∃ caller : Caller C, caller.encoding = choice.2.2 ∧
      (caller.records i).length + (firstChunks settings (.bottom b)).length = (records i).length + j ∧
      (caller.outputs i).length + (firstChunks settings (.bottom b)).length = j ∧
      Q = (callerProgram K D circuits settings top (.bottom b) x setup j caller i).run := by
  rw [signingCont_caller K D circuits settings top x setup b outputs records choice head rest hchunks i] at h
  obtain ⟨caller, encoding, records', outputs', program⟩ := signing D top b x setup
    (signingCaller outputs records (fun _ => pure (some choice)) choice) i same j first current Q h
  refine ⟨caller, encoding, records', ?_, program⟩
  simpa [signingCaller] using outputs'

end Later

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkEncoding.head_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms head_split

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkEncoding.headsAgree_of_tails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms headsAgree_of_tails

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkEncoding.signingCont_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingCont_caller

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkEncoding.signing_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signing_later

end TreeCheckWalkEncoding
end ThresholdLeanXmssSecurity
