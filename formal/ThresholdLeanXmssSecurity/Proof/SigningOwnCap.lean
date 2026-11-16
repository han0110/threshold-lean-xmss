import ThresholdLeanXmssSecurity.Proof.SigningOwnWalkRound2
import ThresholdLeanXmssSecurity.Proof.SigningOwnCapPotential
import ThresholdLeanXmssSecurity.Proof.SigningOwnVerify
import ThresholdLeanXmssSecurity.Proof.SigningOwnGateBlock

/-!
# The cap of the compiler run with the own budget

* `charges_oracle` states that a query of the forger makes at most one charged call when the own
  budget counts it, and none when it does not.
* `charges_game` states that the game makes at most `q + capSlack` charged calls on each run and
  keeps `WalkInv`. The forger makes at most `q`, the verification at most `capSlack`, and the setup
  and the honest-signature tail none.
* `ownCapClean` is the leaf `OwnCapClean`. It follows from `ownRun_cap` with the ledger bound of
  `ownRun_support`.
* `laneTraceCapOwn_of_clean` gives the capped lane with the own budget from the clean coupling and
  the clean leaf.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningOwnCap

open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerO1Coupling SigningCompilerCouplingProof
open SigningCompilerO1Release SigningCompilerO1Clean SigningOwnLedger SigningOwnWalk
open SigningOwnWalkBuild SigningOwnWalkHandlers SigningOwnWalkRound2 SigningOwnCapPotential
open SigningOwnVerify SigningOwnForger SigningOwnGateBlock

attribute [local instance] Classical.propDecidable

variable {C : Committee}


/-- The capped lane with the own budget. -/
def LaneTraceCapOwn (prims : Primitives) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 → HasSigningOwnBound A q →
    q + signingSlack < 2 ^ 127 →
    Pr{let z ←
      SigningLaneUnionProof.traceRun prims A x}[SigningLaneUnionProof.NoFlag (SigningLaneUnionProof.observed z) ∧
        SigningLaneUnionProof.NotChargedLogged prims x (SigningLaneUnionProof.observed z) ∧
        (SigningLaneUnionProof.LoggedInputHit prims x (SigningLaneUnionProof.observed z) ∨
          SigningLaneUnionProof.StaleBaseAt z ∨ SigningLaneUnionProof.GhostAt x z)] ≤ ((q + capSlack : ℕ) : ℝ≥0∞) / 2 ^ 128

/-- Leaf L3c. The clean event of the compiler run of a forger with the own budget `q`, at each cap
`Q`. -/
def OwnCapClean (prims : Primitives) : Prop :=
  ∀ (A : TsigAdversary C) (q Q : ℕ) (x : Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 → HasSigningOwnBound A q →
    q + signingSlack < 2 ^ 127 →
    Pr{let z ← compilerRunO1 prims A x Q}[CleanCompilerEvent x Q z] ≤
      ((q + capSlack : ℕ) : ℝ≥0∞) / 2 ^ 128

/-- Each run of the signing world has a finite count. -/
theorem worldBounded (prims : Primitives) {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∃ Q, ∀ r ∈ support (runSigningWorld prims oa), r.2 ≤ Q := by
  have hfin : (support (runSigningWorld prims oa)).Finite := OracleComp.support_finite _
  obtain ⟨Q, hQ⟩ := (hfin.image Prod.snd).bddAbove
  exact ⟨Q, fun r hr => hQ ⟨r, hr, rfl⟩⟩

set_option maxRecDepth 100000 in
/-- The capped lane with the own budget from the clean coupling and the clean leaf. -/
theorem laneTraceCapOwn_of_clean (prims : Primitives)
    (hcouple : CompilerCouplingClean (C := C) prims) (hown : OwnCapClean (C := C) prims) :
    LaneTraceCapOwn (C := C) prims := by
  intro A q x hx hkeys hq hsmall
  obtain ⟨Q, hQ⟩ := worldBounded prims (gameAfter A x)
  refine le_trans (prEvent_mono_of_support _ _ _ fun z hz hE => ?_)
    ((hcouple A Q x hx hkeys).trans (hown A q Q x hx hkeys hq hsmall))
  exact ⟨hE, SigningLaneUnionProof.traceRun_count_le prims A Q x hQ z hz⟩

/-- A query of the forger makes at most one charged call when the own budget counts it, and none
when it does not. A round-2 request makes none. -/
theorem charges_oracle (prims : Primitives) (x : Keys3 C) (Q : ℕ) (s : HiddenKey → Digest)
    (top : TopTree) (t : (LocalSpec C + TsigSpec C).Domain) :
    SourceCharges x.1 x.2.1 Q s (fun _ => True) (if SigningOwnCounted t then 1 else 0)
      (sourceOraclesO1 prims x top t) := by
  cases t with
  | inl t => exact charges_local prims x Q s top t
  | inr t =>
      cases t with
      | corrupt i => exact charges_corrupt prims x Q s top i
      | tree b => exact charges_tree prims x Q s top b
      | round1 i J e message => exact charges_round1 prims x Q s top i J e message
      | round2 i J e message parts => exact charges_round2 prims x Q s top i J e message parts

/-- A simulation keeps the signing state when each handler keeps it. -/
theorem keepsSigning_simulateQ {ι α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (SourceMO1 C)) (step : ∀ t, KeepsSigning (impl t))
    (oa : OracleComp spec α) : KeepsSigning (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using KeepsSigning.pure (C := C) value
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact (step t).bind _ ih

/-- The verification makes at most `capSlack` charged calls, keeps the invariant of the walk and
keeps the signing state. -/
theorem walk_verify (x : Keys3 C) (Q : ℕ) (s : HiddenKey → Digest) (st0 : SourceState C)
    (publicKey : PublicKey) (message : Message) (signature : Signature) :
    WalkO x.1 x.2.1 Q s (fun src st => WalkInv x.1 x.2.1 src st ∧ src.base.signing = st0.signing)
      capSlack (fun _ src st => WalkInv x.1 x.2.1 src st ∧ src.base.signing = st0.signing)
      (simulateQ (fun input => liftBase (do
        let value ← sourceHash x.1 x.2.1 (.hash input)
        modify fun (s : SourceState C) => { s with candidates :=
          s.candidates ++ SigningGuessLinkProof.callCandidates x.1 st0.signing st0.exposed input }
        pure value : SourceM C HashOutput) : QueryImpl HashSpec (SourceMO1 C))
        (Verification.verifyWithHash publicKey message signature)) := by
  refine WalkO.keeps st0.signing ?_ (WalkO.of_charges ?_)
  · apply keepsSigning_simulateQ
    intro input
    refine KeepsSigning.liftBase (((sourceControl_sourceHash x.1 x.2.1 (.hash input)).comp
      Prod.fst).bind _ fun _ => (SourceKeeps.modify _ ?_).bind _ fun _ => SourceKeeps.pure _)
    exact fun _ => rfl
  · apply SourceCharges.simulateQ_bound _ _ _ _ _ (fun _ => True) ?_ _ capSlack
      (by convert verify_bound publicKey message signature)
    intro input
    exact SourceCharges.mono (charges_verify x Q s st0 input) (fun _ h => h) (by simp)

set_option maxRecDepth 100000 in
/-- The game makes at most `q + capSlack` charged calls on each run, and it keeps the invariant of
the walk. -/
theorem charges_game (prims : Primitives) (A : TsigAdversary C) (q Q : ℕ) (x : Keys3 C)
    (s : HiddenKey → Digest) (hown : HasSigningOwnBound A q) :
    SourceCharges x.1 x.2.1 Q s (fun _ => True) (q + capSlack) (sourceGameO1 prims A x) := by
  unfold sourceGameO1
  refine SourceCharges.mono (c := 0 + (q + capSlack)) (SourceCharges.bind (charges_setup x Q s) _
    fun top => ?_) (fun _ h => h) (by omega)
  refine SourceCharges.bind (SourceCharges.simulateQ_bound x.1 x.2.1 Q s _ _
    (charges_oracle prims x Q s top) _ q (hown _ top)) _ fun forgery => ?_
  refine WalkO.to_charges (A := fun _ => True) ?_
  refine WalkO.conseq (c := 0 + (capSlack + (0 + 0 + 0))) (WalkO.bind
    (WalkO.get (Pre := fun src st => WalkInv x.1 x.2.1 src st ∧ True)) fun src0 => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h) (by omega)
  have hverify := walk_verify x Q s src0.base ⟨top.root, x.1⟩ forgery.message forgery.signature
  refine WalkO.bind (WalkO.conseq hverify (fun src st h => ?_) (fun _ _ _ h => h) le_rfl)
    fun verified => ?_
  · obtain ⟨rfl, hw, -⟩ := h
    exact ⟨hw, rfl⟩
  dsimp only
  split
  · exact WalkO.conseq (c := 0 + 0) (WalkO.bind (WalkO.pure (Post := fun _ src st =>
      WalkInv x.1 x.2.1 src st) _ fun _ _ h => h.1) fun _ => WalkO.pure _ fun _ _ h => h)
      (fun _ _ h => h) (fun _ _ _ h => h) (by omega)
  · rename_i hcard
    refine WalkO.conseq (c := 0 + (0 + 0)) (WalkO.bind (Mid := fun _ src st =>
      WalkInv x.1 x.2.1 src st) ?_ fun honest => WalkO.bind (WalkO.pure (Post := fun _ src st =>
        WalkInv x.1 x.2.1 src st) _ fun _ _ h => h) fun _ => WalkO.pure _ fun _ _ h => h)
      (fun _ _ h => h) (fun _ _ _ h => h) (by omega)
    intro src st hp r hr
    obtain ⟨hw, hl⟩ := charges_tail prims x Q s top forgery.signature.leafIndex forgery.message
      src st hp.1 (by beta_reduce; rw [hp.2]; omega) r hr
    exact ⟨hl, hw⟩

/-- The invariant of the walk holds at the start. -/
theorem walkInv_init (P : PublicParameter) (seeds : C.Term → HashOutput) :
    WalkInv (C := C) P seeds sourceInitO1 ownInit := by
  refine ⟨rfl, rfl, fun e h => absurd rfl h.1, fun e h => absurd rfl h, fun b h => absurd rfl h,
    fun e h => absurd rfl h, ?_, ?_, CompilerReachable.initial, (fun h => by cases h),
    fun _ _ h => by cases h⟩
  · exact (SigningCompilerO1Slack.guardedReleaseInvariantS_initial (fun _ => 0) seeds).2
  · exact Nat.zero_le _

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- The ledger of each run is within `q + capSlack`, and a dirty run has a second opening at its
end. -/
theorem ownRun_support (prims : Primitives) (A : TsigAdversary C) (q Q : ℕ) (x : Keys3 C)
    (hown : HasSigningOwnBound A q) (r : CompilerOutcomeO1 C × OwnGhost)
    (hr : r ∈ support (ownRun prims A x Q)) :
    r.2.ledger ≤ q + capSlack ∧ (r.2.dirty = true → SecondOpening x.1 x.2.1 r.1.2.1.1.data) := by
  simp only [ownRun, mem_support_bind_iff, support_map, Set.mem_image] at hr
  obtain ⟨s, -, a, ha, rfl⟩ := hr
  have h := charges_game prims A q Q x s hown sourceInitO1 ownInit (walkInv_init x.1 x.2.1) trivial
    ((a.1.1, a.1.2), a.2) ha
  exact ⟨by simpa [ownInit] using h.2, h.1.dirtySecond⟩

attribute [local irreducible] ownRun in
/-- Leaf L3c from the cap of the run with the ledger. -/
theorem ownCapClean (prims : Primitives) : OwnCapClean (C := C) prims := by
  intro A q Q x _ _ hown hsmall
  have hB : q + capSlack < 2 ^ 127 := by
    have h : capSlack ≤ signingSlack := by norm_num [capSlack, signingSlack]
    omega
  have hsupp := ownRun_support prims A q Q x hown
  generalize q + capSlack = B at hB hsupp ⊢
  have hproj : Pr{let z ← compilerRunO1 prims A x Q}[CleanCompilerEvent x Q z] =
      Pr{let r ← ownRun prims A x Q}[CleanCompilerEvent x Q r.1] := by
    rw [← ownRun_proj prims A x Q, prEvent_map]
  rw [hproj]
  refine le_trans (prEvent_mono_of_support _ _ _ fun r hr h => ?_) (ownRun_cap prims A x Q B hB)
  obtain ⟨hledger, hdirty⟩ := hsupp r hr
  refine ⟨?_, hledger⟩
  rcases h with ⟨-, h | ⟨hev, hclean⟩⟩ | ⟨-, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨hev, ?_⟩
    cases hd : r.2.dirty with
    | false => rfl
    | true => exact absurd (hdirty hd) hclean
  · exact Or.inl h

end ThresholdLeanXmssSecurity.SigningOwnCap

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCap.worldBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCap.worldBounded

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCap.laneTraceCapOwn_of_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCap.laneTraceCapOwn_of_clean

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCap.charges_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCap.charges_oracle

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCap.keepsSigning_simulateQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCap.keepsSigning_simulateQ

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCap.walk_verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCap.walk_verify

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCap.charges_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCap.charges_game

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCap.walkInv_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCap.walkInv_init

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCap.ownRun_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCap.ownRun_support

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCap.ownCapClean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCap.ownCapClean
