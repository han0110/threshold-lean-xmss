import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackRun

/-! # Corruption in the O1 source

A release sweep over a list of keys keeps the invariant at a fixed coalition state, the control
fields and the recorded digits. After the sweep, each covered position of each key of the list is
complete.

Corruption keeps the invariant at the signing state of the source. The sweep runs at the signing
state from before the call. Each key that crosses the threshold by the corruption is in the sweep
list, so the promotion to the new signing state keeps the slack.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1SlackCorrupt
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Invariant SigningCompilerO1Basics SigningCompilerO1Release
open SigningCompilerO1SourceProof SigningCompilerO1Slack SigningCompilerO1SlackRun
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

section Handlers
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)

/-- A release sweep over a list of keys keeps the invariant, the control fields and the recorded
digits. After it, each covered position of each key of the list is complete. -/
theorem sourceReleaseKeys_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (sig : TsigState C) (keys : List KeyIndex)
    (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : ReleaseInvariantO1 seeds s sig src backend)
    (r : (List Unit × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 P seeds q s (keys.mapM (sourceReleaseKey P seeds))
      src backend)) :
    ReleaseInvariantO1 seeds s sig r.1.2 r.2 ∧
      sourceControl r.1.2.base = sourceControl src.base ∧ r.1.2.starts = src.starts ∧
      ∀ e ∈ keys, ∀ l pos, Covered r.1.2.starts e l pos →
        BottomDone seeds s r.2.1.1.data e l pos := by
  induction keys generalizing src backend r with
  | nil =>
      simp only [List.mapM_nil, runSourceO1_pure, mem_support_pure_iff] at hr
      subst r
      exact ⟨h, rfl, rfl, fun _ hm => (List.not_mem_nil hm).elim⟩
  | cons e keys ih =>
      simp only [List.mapM_cons, runSourceO1_bind, mem_support_bind_iff] at hr
      obtain ⟨head, hhead, tail, htail, hr⟩ := hr
      rw [runSourceO1_pure, mem_support_pure_iff] at hr
      subst r
      have hh := sourceReleaseKey_slack P seeds hinj q s sig e src backend h head hhead
      have hc := sourceReleaseKey_control q s P seeds e src backend head hhead
      have ht := ih head.1.2 head.2 hh.1 tail htail
      refine ⟨ht.1, ht.2.1.trans hc.1, ht.2.2.1.trans hc.2, ?_⟩
      intro f hf l pos hp
      rcases List.mem_cons.mp hf with rfl | hf
      · have hd := hh.2 l pos (by simpa only [ht.2.2.1] using hp)
        exact BottomDone.persist hd
          (runSourceO1_cache_le P seeds q s _ head.1.2 head.2 tail htail) ht.1.1
      · exact ht.2.2.2 f hf l pos hp

/-- Corruption keeps the invariant at the signing state of the source. -/
theorem sourceCorruptO1_stable (hinj : Function.Injective x.2.1) (top : TopTree) (i : C.Party)
    (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : ReleaseInvariantO1 x.2.1 s src.base.signing src backend)
    (r : (TsigSpec C (.corrupt i) × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 x.1 x.2.1 q s (sourceTsigO1 prims x top (.corrupt i))
      src backend)) :
    ReleaseInvariantO1 x.2.1 s r.1.2.base.signing r.1.2 r.2 := by
  simp only [sourceTsigO1, runSourceO1_bind, runSourceO1_get, pure_bind] at hr
  split at hr
  · rw [runSourceO1_pure, mem_support_pure_iff] at hr
    subst r
    exact h
  · rename_i hguard
    simp only [runSourceO1_bind, runSourceO1_modify, pure_bind, mem_support_bind_iff] at hr
    obtain ⟨sweep, hsweep, hr⟩ := hr
    rw [runSourceO1_pure, mem_support_pure_iff] at hr
    subst r
    let new : TsigState C :=
      { src.base.signing with corrupt := insert i src.base.signing.corrupt }
    have hframe : ReleaseInvariantO1 x.2.1 s src.base.signing
        { src with base := { src.base with signing := new } } backend :=
      ReleaseInvariantO1.source_frame h rfl rfl
    have hk := sourceReleaseKeys_slack q s x.1 x.2.1 hinj src.base.signing _ _ backend hframe
      sweep hsweep
    have hsig : sweep.1.2.base.signing = new := congrArg Prod.fst hk.2.1
    change ReleaseInvariantO1 x.2.1 s sweep.1.2.base.signing sweep.1.2 sweep.2
    rw [hsig]
    refine ⟨ReleaseSlackO1.promote x.2.1 s src.base.signing new sweep.1.2 sweep.2.1.1.data hk.1.1
      rfl ?_ (Finset.subset_insert _ _) (Nat.le_of_not_lt hguard) ?_, hk.1.2⟩
    · intro e m
      exact Finset.union_subset_union (Finset.subset_insert _ _) (Finset.Subset.refl _)
    · intro e m hb hold hnew l pos hcov
      exact hk.2.2.2 e (crossed_mem src.base.signing new e m hb (Nat.le_of_not_lt hguard)
        hold hnew) l pos hcov

end Handlers

end ThresholdLeanXmssSecurity.SigningCompilerO1SlackCorrupt

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackCorrupt.sourceReleaseKeys_slack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackCorrupt.sourceReleaseKeys_slack

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackCorrupt.sourceCorruptO1_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackCorrupt.sourceCorruptO1_stable
