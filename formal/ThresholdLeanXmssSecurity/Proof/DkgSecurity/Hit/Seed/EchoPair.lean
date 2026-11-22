import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.Echo

/-!
# `EchoPair` from the block of round 2

`seedPre` is a head and then the block of the local steps of round 2 (`revealBlock`), by
`seedPre_split`. The head ends after the counted call of round 2.

* `CacheInv s` states that each shared key cell of the seed generation in the cache of `s` is in the
  log of `s`.
* `PreInv` states that the state at the end of the head of `preRun` has `CacheInv`.
* `BlockBound` states the bound for the pairs in the block, from each state with `CacheInv`. The
  bound is pointwise from each such state.
* `echoPair_of_block` gives `EchoPair` from `PreInv` and `BlockBound`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## The head and the block -/

section Head

variable {E : Type} (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)

/-- The input of the block of round 2, namely the fuel for round 3, the state of the adversary, the
inboxes of round 1 and the mail of the corrupt operators in round 2. -/
abbrev BlockIn (C : Committee) (E σ : Type) :=
  ℕ × σ × (C.Party → Mail C E) × (C.Party → C.Party → Option (Msg E))

/-- The local steps of round 2 of the honest operators with the inboxes `committed` of round 1, the
abort pattern `d` and the mail `sent` of the corrupt operators. -/
def revealBlock (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (d : C.Party → Option Unit)
    (sent : C.Party → C.Party → Option (Msg E)) : OracleComp (WorldSpec C) (C.Party → Option (SeedGenEchoData C)) :=
  OverPermutation.sequenceFin (fun j => if j ∈ D.1 then pure none else
    match d j with
    | none => pure none
    | some _ => if anyAbort (levelInbox D d (fun i _ => revealOutbox .seedGen i (parts i)) sent j) then pure none else
        free (revealNext D parts committed j (levelInbox D d (fun i _ => revealOutbox .seedGen i (parts i)) sent j)))

/-- The seed generation of the normal form to the counted call of round 2. -/
def seedHead (state : net.State) (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C)
    (parts : C.Party → Parts C) :
    OracleComp (WorldSpec C) ((net.State × (C.Party → Option (Keys C))) ⊕ BlockIn C E net.State) :=
  commitDraws D parts >>= fun commitments =>
  observe (net.round state (commitMail D commitments)) >>= fun r =>
  programBlock D (early ++ r.2) r.1.2 parameter dealt parts >>= fun _ =>
  if ∀ i, i ∉ D.1 → revealReady (commitInbox D commitments r.1.2) i = none then pure (.inl (r.1.1, fun _ => none))
  else
  counted (liftComp (net.round r.1.1 (levelMail D (revealReady (commitInbox D commitments r.1.2))
    (fun i _ => revealOutbox .seedGen i (parts i)))) _) >>= fun r2 =>
  if ∃ i, i ∉ D.1 ∧ revealReady (commitInbox D commitments r.1.2) i = none then pure (.inl (r2.1, fun _ => none))
  else pure (.inr (setupRounds - 2, r2.1, commitInbox D commitments r.1.2, r2.2))

/-- The rest of `seedPre` after the head. -/
def blockStep (parts : C.Party → Parts C) : (net.State × (C.Party → Option (Keys C))) ⊕ BlockIn C E net.State →
    OracleComp (WorldSpec C) (EchoPoint C net.State)
  | .inl e => pure (.inl e)
  | .inr b => revealBlock D parts b.2.2.1 (revealReady b.2.2.1) b.2.2.2 >>= fun d' => pure (.inr (b.1, b.2.1, d'))

theorem seedPre_split (state : net.State) (early : CallLog C) (parameter : PublicParameter)
    (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    seedPre D net state early parameter dealt parts =
      seedHead D net state early parameter dealt parts >>= blockStep D net parts := by
  unfold seedPre seedHead
  simp only [bind_assoc]
  refine bind_congr fun commitments => bind_congr fun r => bind_congr fun _ => ?_
  rw [show setupRounds - 1 = (setupRounds - 2) + 1 from rfl]
  simp only [levelPre]
  by_cases h1 : ∀ i, i ∉ D.1 → revealReady (commitInbox D commitments r.1.2) i = none
  · rw [ite_eq_left h1, ite_eq_left h1, pure_bind]
    rfl
  · rw [ite_eq_right h1, ite_eq_right h1, bind_assoc]
    refine bind_congr fun r2 => ?_
    by_cases h2 : ∃ i, i ∉ D.1 ∧ revealReady (commitInbox D commitments r.1.2) i = none
    · rw [ite_eq_left h2, ite_eq_left h2, pure_bind]
      rfl
    · rw [ite_eq_right h2, ite_eq_right h2, pure_bind]
      simp only [blockStep, revealBlock]
      congr 1
      congr 1
      funext j
      by_cases hj : j ∈ D.1
      · simp only [hj, ite_true]
      · simp only [hj, ite_false]
        rcases revealReady (commitInbox D commitments r.1.2) j with _ | u <;> rfl

end Head

/-! ## The statements -/

section Statements

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives)

/-- Each shared key cell of the seed generation in the cache is in the log. -/
def CacheInv (s : LogState C) : Prop :=
  ∀ L : List HashOutput, s.1.1 (.sharedKeys .seedGen L) ≠ none → Query.sharedKeys .seedGen L ∈ s.2

/-- `preRun` to the end of the head. -/
def headRun (D : C.Coalition) (A : DkgTsigAdversary C E) :
    ProbComp ((PrefixOut C A.net.State × LogState C) × (C.Term → HashOutput) ×
      (((A.net.State × (C.Party → Option (Keys C))) ⊕ BlockIn C E A.net.State) × LogState C)) := do
  let x ← (simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), [])
  let seed ← $ᵗ (C.Term → HashOutput)
  let e ← (simulateQ (compWorld prims D x.1.2.2 seed)
    (seedHead D A.net x.1.1.1 x.1.1.2 x.1.2.1.1 x.1.2.1.2.2 x.1.2.2)).run x.2
  pure (x, seed, e)

/-- The state at the end of the head of `preRun` has `CacheInv`. No free call and no programming call
before the block asks a shared key cell, and each counted call is in the log. -/
def PreInv : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E), ∀ z ∈ support (headRun prims D A), CacheInv z.2.2.2

/-- The bound for the pairs in the block of round 2, from each state with `CacheInv`, for each parts,
seeds, inboxes of round 1, abort pattern and mail of the corrupt operators. Two honest operators that
share a hidden term have values for which the test on the hashes and the test on the lists differ, and
no counted call asked the list of an honest pair, with probability at most `C(n,2) / 2^256`. The bound is
pointwise from each such state. -/
def BlockBound : Prop :=
  ∀ (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput) (committed : C.Party → Mail C E)
    (d : C.Party → Option Unit) (sent : C.Party → C.Party → Option (Msg E)) (s : LogState C), CacheInv s →
    Pr{let z ← (simulateQ (compWorld prims D parts seed) (revealBlock D parts committed d sent)).run s}[
      EchoBad D (.inr ((0 : ℕ), (), z.1) : EchoPoint C Unit) ∧ ¬ EchoPrior D parts seed z.2] ≤
      (C.n.choose 2 : ℝ≥0∞) / 2 ^ 256

end Statements

/-! ## The glue -/

section Glue

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem preRun_split (D : C.Coalition) (A : DkgTsigAdversary C E) :
    preRun prims D A = headRun prims D A >>= fun z =>
      (simulateQ (compWorld prims D z.1.1.2.2 z.2.1) (blockStep D A.net z.1.1.2.2 z.2.2.1)).run z.2.2.2 >>= fun e =>
        pure (z.1, z.2.1, e) := by
  unfold preRun headRun
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun x => bind_congr fun seed => ?_
  rw [seedPre_split, simulateQ_bind, StateT.run_bind, bind_assoc]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- `PreInv` and `BlockBound` give `EchoPair`. -/
theorem echoPair_of_block (inv : PreInv (C := C) (E := E) prims) (block : BlockBound (C := C) (E := E) prims) :
    EchoPair (C := C) (E := E) prims := by
  intro D A
  rw [preRun_split, prEvent_bind_wp]
  refine (wp_mono_of_support _ fun z hz => ?_).trans_eq (wp_const _ _)
  rcases z with ⟨x, seed, ⟨h | b, s⟩⟩
  · simp only [blockStep, simulateQ_pure, StateT.run_pure, pure_bind]
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun r hr' hr => ?_) zero_le
    simp only [support_pure, Set.mem_singleton_iff] at hr'
    subst hr'
    exact hr.1
  · simp only [blockStep, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
    rw [bind_pure_comp, prEvent_map]
    exact block D x.1.2.2 seed b.2.2.1 (revealReady b.2.2.1) b.2.2.2 s (inv D A _ hz)

end Glue

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.echoPair_of_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.echoPair_of_block
