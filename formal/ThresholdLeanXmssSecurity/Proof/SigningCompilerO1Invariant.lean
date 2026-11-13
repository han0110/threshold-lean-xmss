import ThresholdLeanXmssSecurity.Proof.SigningLaneHybridCapO1
import ThresholdLeanXmssSecurity.Proof.SigningCompilerCoupling

/-! # Coalition-indexed release invariants for the corrected O1 source -/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Invariant
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def BottomDone (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (data : DeferredState C) (e : KeyIndex) (l : ChainIndex)
    (pos : XmssSecurity.ChainStep) : Prop :=
  (pos.val = 0 ∨ data.pads (.chain bottomLayer e l (chainStepDigit pos)) ≠ none) ∧
  PointDone seeds data (.chain bottomLayer e l (chainStepDigit pos))
    (bottomReleaseTarget s data e l pos)

def Covered (starts : KeyIndex → ChainIndex → Finset Digit)
    (e : KeyIndex) (l : ChainIndex) (pos : XmssSecurity.ChainStep) : Prop :=
  ∃ d ∈ starts e l, d.val ≤ pos.val

structure ReleaseSlackO1 (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (sig : TsigState C) (source : SourceStateO1 C) (data : DeferredState C) : Prop where
  corrupt_bound : sig.corrupt.card ≤ C.t - 1
  bottom_opening : ∀ e,
    PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) ∨
    (sig.bound e = none ∧
      LackedUncached seeds sig.corrupt data (.randomizer bottomLayer e)) ∨
    (sig.bound e ≠ none ∧ ∃ T : C.Term,
      (T, Point.randomizer bottomLayer e) ∉ data.virtual ∧
        data.cache (.prf (seeds T) (.randomizer bottomLayer e)) = none)
  bottom_chain : ∀ e l pos,
    BottomDone seeds s data e l pos ∨
    LackedUncached seeds sig.corrupt data (.chain bottomLayer e l (chainStepDigit pos)) ∨
    (chainStepDigit pos ∈ source.starts e l ∧ ∃ m, sig.bound e = some m ∧
      (signersAt sig e m).card < C.t ∧
      LackedUncached seeds (signersAt sig e m) data (.chain bottomLayer e l (chainStepDigit pos)))
  top_opening : ∀ b,
    PointDone seeds data (.randomizer topLayer (topKey b)) (s (.opening topLayer (topKey b))) ∨
    LackedUncached seeds sig.corrupt data (.randomizer topLayer (topKey b))
  top_start : ∀ b l,
    PointDone seeds data (.chain topLayer (topKey b) l (digit 0))
      (s (.topChain b l ⟨0, by decide⟩)) ∨
    LackedUncached seeds sig.corrupt data (.chain topLayer (topKey b) l (digit 0))
  bottom_released : ∀ e, source.base.revealed (.opening bottomLayer e) ≠ none →
    PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e))

  crossed_done : ∀ e m, sig.bound e = some m → C.t ≤ (signersAt sig e m).card →
    ∀ l pos, Covered source.starts e l pos → BottomDone seeds s data e l pos

def ReleaseInvariantO1 (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (sig : TsigState C) (src : SourceStateO1 C) (backend : CappedCompilerState C) : Prop :=
  ReleaseSlackO1 seeds s sig src backend.1.1.data ∧
    RevealRelation s src.base backend ∧ PendingValid backend.1.1.data

def GuardedReleaseInvariantO1 (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (src : SourceStateO1 C) (backend : CappedCompilerState C) : Prop :=
  PendingValid backend.1.1.data ∧ StoredTopShape src.base ∧
    (src.base.hiddenFlag = false → ReleaseInvariantO1 seeds s src.base.signing src backend)

theorem releaseSlack_toO1 (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (src : SourceStateO1 C) (data : DeferredState C)
    (h : ReleaseSlack seeds s src.base data)
    (hcross : ∀ e m, src.base.signing.bound e = some m →
      C.t ≤ (signersAt src.base.signing e m).card →
      ∀ l pos, Covered src.starts e l pos → BottomDone seeds s data e l pos) :
    ReleaseSlackO1 seeds s src.base.signing src data := by
  refine ⟨h.corrupt_bound, h.bottom_opening, ?_, h.top_opening, h.top_start,
    h.bottom_released, hcross⟩
  intro e l pos
  exact (h.bottom_chain e l pos).imp_right Or.inl

theorem ReleaseSlackO1.promote (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (sig sig' : TsigState C) (src : SourceStateO1 C) (data : DeferredState C)
    (h : ReleaseSlackO1 seeds s sig src data)
    (hbound : sig'.bound = sig.bound)
    (hsigners : ∀ e m, signersAt sig e m ⊆ signersAt sig' e m)
    (hcorrupt : sig.corrupt ⊆ sig'.corrupt) (hcard : sig'.corrupt.card ≤ C.t - 1)
    (hnew : ∀ e m, sig.bound e = some m →
      (signersAt sig e m).card < C.t → C.t ≤ (signersAt sig' e m).card →
      ∀ l pos, Covered src.starts e l pos → BottomDone seeds s data e l pos) :
    ReleaseSlackO1 seeds s sig' src data := by
  refine ⟨hcard, ?_, ?_, ?_, ?_, h.bottom_released, ?_⟩
  · intro e
    rcases h.bottom_opening e with hd | ⟨hb, hu⟩ | ⟨hb, hw⟩
    · exact Or.inl hd
    · exact Or.inr (Or.inl ⟨hbound ▸ hb, hu.corrupt_mono hcorrupt⟩)
    · exact Or.inr (Or.inr ⟨hbound ▸ hb, hw⟩)
  · intro e l pos
    rcases h.bottom_chain e l pos with hd | hu | ⟨hp, m, hb, hlt, hu⟩
    · exact Or.inl hd
    · exact Or.inr (Or.inl (hu.corrupt_mono hcorrupt))
    · by_cases hn : (signersAt sig' e m).card < C.t
      · exact Or.inr (Or.inr ⟨hp, m, hbound ▸ hb, hn, hu.corrupt_mono (hsigners e m)⟩)
      · apply Or.inl
        apply hnew e m hb hlt (by omega) l pos
        exact ⟨chainStepDigit pos, hp, by simp [chainStepDigit]⟩
  · intro b
    exact (h.top_opening b).imp_right (fun hu => hu.corrupt_mono hcorrupt)
  · intro b l
    exact (h.top_start b l).imp_right (fun hu => hu.corrupt_mono hcorrupt)
  · intro e m hb hn l pos hp
    have hb' : sig.bound e = some m := hbound ▸ hb
    by_cases ho : C.t ≤ (signersAt sig e m).card
    · exact h.crossed_done e m hb' ho l pos hp
    · exact hnew e m hb' (by omega) hn l pos hp


/-- Initially no canonical digit has been recorded and no point materialized. -/
theorem releaseSlackO1_initial (seeds : C.Term → HashOutput) (s : HiddenKey → Digest) :
    ReleaseSlackO1 seeds s (sourceInitO1 (C := C)).base.signing sourceInitO1 deferredInit := by
  apply releaseSlack_toO1 seeds s sourceInitO1 deferredInit (releaseSlack_initial seeds s)
  intro e m hb
  simp [sourceInitO1, sourceInit, SigningCoreProof.tsigInit] at hb

/-- The corrected source and empty backend satisfy the full guarded invariant. -/
theorem guardedReleaseInvariantO1_initial (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) :
    GuardedReleaseInvariantO1 (C := C) seeds s sourceInitO1
      ((compilerInit, 0), fun _ => none, false) := by
  have pending : PendingValid (deferredInit (C := C)) := by
    intro p value hp
    cases hp
  exact ⟨pending, storedTopShape_initial, fun _ =>
    ⟨releaseSlackO1_initial seeds s, revealRelation_initial s, pending⟩⟩

end ThresholdLeanXmssSecurity.SigningCompilerO1Invariant

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Invariant.releaseSlack_toO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Invariant.releaseSlack_toO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Invariant.ReleaseSlackO1.promote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Invariant.ReleaseSlackO1.promote

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Invariant.releaseSlackO1_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Invariant.releaseSlackO1_initial

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Invariant.guardedReleaseInvariantO1_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Invariant.guardedReleaseInvariantO1_initial
