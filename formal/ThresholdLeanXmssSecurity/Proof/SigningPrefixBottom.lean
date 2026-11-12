import ThresholdLeanXmssSecurity.Proof.SigningTopCache

/-!
# Successful bottom computations before verification

A round-2 release requires a successful bottom-tree computation. The existing
receipt invariant retains that computation's actual counted subrun. We transfer
it to the verification prefix, discharging `PrefixBottomSuccess` for every key
with a recorded release, hence for every released honest key.

Neither a tree request nor a winning forgery alone asserts a successful bottom
computation. The no-release cases stay separate; the protocol builds trees lazily.
The pinned and current leanVM support/bridge lemmas were searched; the threshold
receipt invariant already supplies the stronger operational witness needed here.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningPrefixBottomProof

open SigningDescentProof SigningTopCacheProof SigningOpeningProof SigningGuardedFlagProof

variable {C : Committee} (prims : Primitives)

set_option maxRecDepth 100000 in
/-- The successful bottom subrun retained by a receipt resolves in the current cache. -/
theorem receiptRuns_prefixBottomSuccess (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (cache : HashCache C) (receipt : SigningGuessProof.Round2Receipt C) (forgery : Forgery)
    (hr : SigningGuessProof.ReceiptRuns prims x top cache receipt)
    (he : receipt.key = forgery.signature.leafIndex) :
    PrefixBottomSuccess x top forgery cache := by
  obtain ⟨tree, sTree, rTree, sCode, rCode, hTree, hTreeOut, hTreeLe, _⟩ := hr
  apply prefixBottomSuccess_of_run prims x top forgery tree sTree rTree.2 cache _ hTreeLe
  rw [← he]
  simpa only [← hTreeOut] using hTree

set_option maxRecDepth 100000 in
/-- One recorded honest release suffices; it need not form a threshold quorum. -/
theorem openingRun_prefixBottomSuccess_of_release (x : SigningSecurityProof.Keys3 C)
    (top : TopTree) {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α)
    (initial : HashCache C × ℕ)
    (q : (α × (TsigState C × Bool) × Finset (Fin (2 ^ layerHeight)) × List (HiddenKey × Digest)) ×
      HashCache C × ℕ)
    (hq : q ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((simulateQ (openingOracles x (dealtOf x top)) source).run
        ((SigningCoreProof.tsigInit, false), ∅, []))).run initial))
    (forgery : Forgery) (message : Message) (party : C.Party)
    (hrel : (forgery.signature.leafIndex, message, party) ∈ q.1.2.1.1.released) :
    PrefixBottomSuccess x top forgery q.2.1 := by
  obtain ⟨q', hq', _, hstate, hcache⟩ := SigningReleasedProof.openingRun_receipts prims x _ _
    SigningCoreProof.tsigInit false initial q hq
  have hin := SigningGuessProof.countRun_support prims _ initial q' hq'
  have hreleased : q'.1.2.1.1.released = q'.1.2.2.map SigningGuessProof.Round2Receipt.release := by
    apply SigningGuessProof.signingReceiptOracles_released _ source (q'.1.1, q'.1.2.1.1, q'.1.2.2)
    rw [← SigningGuessProof.flaggedReceiptOracles_forgetFlag x _ source
      SigningCoreProof.tsigInit false [], support_map]
    exact ⟨q'.1, hin, rfl⟩
  have hruns := SigningGuessProof.flaggedReceiptOracles_runs prims x top source
    (SigningCoreProof.tsigInit, false) [] initial
    (by simp [SigningGuessProof.StoredTreeRuns, SigningCoreProof.tsigInit]) (by simp) q' hq'
  rw [← hstate, hreleased] at hrel
  obtain ⟨receipt, hreceipt, he⟩ := List.mem_map.mp hrel
  have hekey : receipt.key = forgery.signature.leafIndex := congrArg Prod.fst he
  have hr := hruns receipt hreceipt
  rw [hcache] at hr
  exact receiptRuns_prefixBottomSuccess prims x top q.2.1 receipt forgery hr hekey

set_option maxRecDepth 100000 in
/-- A recorded release establishes the condition at the actual verification prefix. -/
theorem verificationPrefix_bottomSuccess_of_release (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C)
    (q v) (hpre : VerificationPrefix prims A x r q v)
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hm : r.1.1.2 = some (top, state, forgery)) (message : Message) (party : C.Party)
    (hrel : (forgery.signature.leafIndex, message, party) ∈ state.released) :
    PrefixBottomSuccess x top forgery q.2.1 := by
  obtain ⟨top', p, f, hp, hp1, hq, hv, hf, rfl⟩ := hpre
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl, rfl⟩ := hm
  exact openingRun_prefixBottomSuccess_of_release prims x top' _ p.2 q hq _ message party hrel

set_option maxRecDepth 100000 in
/-- A threshold of signers contains an honest receipt and its successful bottom run. -/
theorem verificationPrefix_bottomSuccess_of_signers (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C)
    (q v) (hpre : VerificationPrefix prims A x r q v)
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hm : r.1.1.2 = some (top, state, forgery)) (message : Message)
    (ht : C.t ≤ (signersAt state forgery.signature.leafIndex message).card) :
    PrefixBottomSuccess x top forgery q.2.1 := by
  obtain ⟨top', p, f, hp, hp1, hq, hv, hf, rfl⟩ := hpre
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl, rfl⟩ := hm
  obtain ⟨q', hq', _, hstate, hcache⟩ := SigningReleasedProof.openingRun_receipts prims x _ _
    SigningCoreProof.tsigInit false p.2 q hq
  obtain ⟨receipt, _, hkey, _, hruns⟩ := SigningReleasedProof.receiptRun_released prims x top' _ p.2 q'
    hq' q.1.1.signature.leafIndex message (by rw [hstate]; exact ht)
  rw [hcache] at hruns
  exact receiptRuns_prefixBottomSuccess prims x top' q.2.1 receipt q.1.1 hruns hkey

/-- A released honest key already has a successful bottom tree when verification starts. -/
theorem verificationPrefix_bottomSuccess_of_released (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C)
    (q v) (hpre : VerificationPrefix prims A x r q v)
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hm : r.1.1.2 = some (top, state, forgery)) :
    let z := SigningCostProof.finalOf x (r.1.1, r.2) top state forgery
    (z.honestKey prims).released = true → PrefixBottomSuccess x top forgery q.2.1 := by
  intro z hrel
  rw [SigningSupportProof.honestKey_released] at hrel
  unfold SigningSupportProof.releasedAt at hrel
  change (match state.bound forgery.signature.leafIndex with
    | some message => decide (C.t ≤ (signersAt state forgery.signature.leafIndex message).card)
    | none => false) = true at hrel
  cases hb : state.bound forgery.signature.leafIndex with
  | none => simp only [hb, Bool.false_eq_true] at hrel
  | some message =>
    rw [hb] at hrel
    exact verificationPrefix_bottomSuccess_of_signers prims A x r q v hpre top state forgery hm
      message (of_decide_eq_true hrel)

/-- Top-opening stability for a released honest key needs no opening-match guard. -/
theorem verificationPrefix_topOpened_eq_of_released (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C)
    (q v) (hpre : VerificationPrefix prims A x r q v)
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hm : r.1.1.2 = some (top, state, forgery)) :
    let z := SigningCostProof.finalOf x (r.1.1, r.2) top state forgery
    (z.honestKey prims).released = true →
      topOpened q.2.1 x.1 z.key (z.honestKey prims) =
        topOpened r.2.1 x.1 z.key (z.honestKey prims) := by
  intro z hrel
  exact verificationPrefix_topOpened_eq prims A x r q v hpre top state forgery hm
    (verificationPrefix_bottomSuccess_of_released prims A x r q v hpre top state forgery hm hrel)

set_option maxRecDepth 100000 in
/-- An actual verification run with a released key has the required successful prefix. -/
theorem verifyRun_bottomSuccess_of_released (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (r : SigningGuessLinkProof.LoggedOutcome C)
    (hr : r ∈ support (SigningGuessLinkProof.verifyRun prims A x))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hm : r.1.1.2 = some (top, state, forgery)) :
    let z := SigningCostProof.finalOf x (r.1.1, r.2) top state forgery
    (z.honestKey prims).released = true →
      ∃ q v, VerificationPrefix prims A x r q v ∧ PrefixBottomSuccess x top forgery q.2.1 ∧
        topOpened q.2.1 x.1 z.key (z.honestKey prims) =
          topOpened r.2.1 x.1 z.key (z.honestKey prims) := by
  intro z hrel
  obtain ⟨q, v, hpre⟩ := verificationPrefix_exists prims A x r hr top state forgery hm
  exact ⟨q, v, hpre,
    verificationPrefix_bottomSuccess_of_released prims A x r q v hpre top state forgery hm hrel,
    verificationPrefix_topOpened_eq_of_released prims A x r q v hpre top state forgery hm hrel⟩

/-- info: 'ThresholdLeanXmssSecurity.SigningPrefixBottomProof.receiptRuns_prefixBottomSuccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms receiptRuns_prefixBottomSuccess

/-- info: 'ThresholdLeanXmssSecurity.SigningPrefixBottomProof.openingRun_prefixBottomSuccess_of_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms openingRun_prefixBottomSuccess_of_release

/-- info: 'ThresholdLeanXmssSecurity.SigningPrefixBottomProof.verificationPrefix_bottomSuccess_of_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verificationPrefix_bottomSuccess_of_release

/-- info: 'ThresholdLeanXmssSecurity.SigningPrefixBottomProof.verificationPrefix_bottomSuccess_of_signers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verificationPrefix_bottomSuccess_of_signers

/-- info: 'ThresholdLeanXmssSecurity.SigningPrefixBottomProof.verificationPrefix_bottomSuccess_of_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verificationPrefix_bottomSuccess_of_released

/-- info: 'ThresholdLeanXmssSecurity.SigningPrefixBottomProof.verificationPrefix_topOpened_eq_of_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verificationPrefix_topOpened_eq_of_released

/-- info: 'ThresholdLeanXmssSecurity.SigningPrefixBottomProof.verifyRun_bottomSuccess_of_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verifyRun_bottomSuccess_of_released

end ThresholdLeanXmssSecurity.SigningPrefixBottomProof
