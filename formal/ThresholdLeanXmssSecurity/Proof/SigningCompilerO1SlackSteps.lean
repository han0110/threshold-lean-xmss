import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackPure

/-! # Steps of the base source that keep the O1 slack

Each step runs on the base source at a fixed coalition state `sig` and a fixed map `starts` of
recorded digits. The terminal plants, the opening release, the virtual call, the raw hash call and
the release-aware hash call keep `ReleaseSlackO1`.

The readiness tests of the source read only the bound map. So the virtual call and the hash call
take the link `source.signing.bound = sig.bound`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Invariant SigningCompilerO1Basics SigningCompilerO1Release
open SigningCompilerO1SourceProof SigningCompilerO1Slack SigningCompilerO1SlackPure
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

section Steps
variable (P : PublicParameter) (seeds : C.Term → HashOutput) (q : ℕ) (s : HiddenKey → Digest)
  (sig : TsigState C) (starts : KeyIndex → ChainIndex → Finset Digit)

theorem sourcePlant_terminal_slackO1 (p : PendingInput)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hp : p.next = none) (hv : PendingValid backend.1.1.data)
    (hk : source.revealed p.key ≠ none)
    (hs : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ backend.1.1.data)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourcePlant P p) source backend)) :
    ReleaseSlackO1 seeds s sig ⟨r.1.2, starts⟩ r.2.1.1.data ∧
      PendingValid r.2.1.1.data ∧ r.1.2.revealed = source.revealed := by
  obtain ⟨hsource, hbackend, hcache⟩ := sourcePlant_terminal_frame
    P seeds q s p source backend hp hv hk r hr
  have hrev : r.1.2.revealed = source.revealed := by
    have hh := congrArg SourceState.revealed hsource
    exact hh
  have hdata : r.2.1.1.data = { backend.1.1.data with cache := r.2.1.1.data.cache } :=
    congrArg (fun b : CappedCompilerState C => b.1.1.data) hbackend
  have hvirtual := congrArg DeferredState.virtual hdata
  have hpads := congrArg DeferredState.pads hdata
  have hpending := congrArg DeferredState.pending hdata
  refine ⟨ReleaseSlackO1.frame hs hcache hvirtual hpads (fun e he => hrev ▸ he), ?_, hrev⟩
  intro key value hk'
  apply hv key value
  rw [hpending] at hk'
  exact hk'

set_option backward.isDefEq.respectTransparency false in
theorem sourcePlants_terminal_slackO1 (pending : List PendingInput) :
    ∀ (source : SourceState C) (backend : CappedCompilerState C),
      (∀ p ∈ pending, p.next = none ∧ source.revealed p.key ≠ none) →
      PendingValid backend.1.1.data →
      ReleaseSlackO1 seeds s sig ⟨source, starts⟩ backend.1.1.data →
      ∀ r : (List Unit × SourceState C) × CappedCompilerState C,
      r ∈ support (runSource P seeds q s (pending.mapM (sourcePlant P)) source backend) →
      ReleaseSlackO1 seeds s sig ⟨r.1.2, starts⟩ r.2.1.1.data ∧
        PendingValid r.2.1.1.data ∧ r.1.2.revealed = source.revealed := by
  induction pending with
  | nil =>
      intro source backend _ hv hs r hr
      simp only [List.mapM_nil, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact ⟨hs, hv, rfl⟩
  | cons p pending ih =>
      intro source backend hp hv hs r hr
      simp only [List.mapM_cons, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨head, hhead, tail, htail, hr⟩ := hr
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      have hhead' := sourcePlant_terminal_slackO1 P seeds q s sig starts p source backend
        (hp p (List.mem_cons_self ..)).1 hv (hp p (List.mem_cons_self ..)).2 hs head hhead
      have htail' := ih head.1.2 head.2 (by
        intro key hk
        obtain ⟨hn, hr⟩ := hp key (List.mem_cons_of_mem _ hk)
        exact ⟨hn, hhead'.2.2 ▸ hr⟩) hhead'.2.1 hhead'.1 tail htail
      exact ⟨htail'.1, htail'.2.1, htail'.2.2.trans hhead'.2.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The opening release keeps the slack and completes its bottom randomizer. The slack is given on
a comparison state that agrees with the backend apart from the virtual cells of the key. -/
theorem sourceReleaseOpening_slack_frameO1 (hinj : Function.Injective seeds) (e : KeyIndex)
    (source : SourceState C) (backend : CappedCompilerState C) (data : DeferredState C)
    (hs : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data)
    (hcache : ∀ seed point,
      backend.1.1.data.cache (.prf seed point) = data.cache (.prf seed point))
    (hvirt : ∀ f, f ≠ e → ∀ T : C.Term,
      ((T, Point.randomizer bottomLayer f) ∈ backend.1.1.data.virtual ↔
        (T, Point.randomizer bottomLayer f) ∈ data.virtual))
    (hpad : backend.1.1.data.pads = data.pads)
    (hv : PendingValid backend.1.1.data) (hrev : RevealRelation s source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReleaseOpening P seeds e) source backend)) :
    ReleaseSlackO1 seeds s sig ⟨r.1.2, starts⟩ r.2.1.1.data ∧
      PointDone seeds r.2.1.1.data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) := by
  have admissible : PointDone seeds backend.1.1.data (.randomizer bottomLayer e)
      (s (.opening bottomLayer e)) ∨
      firstUnmaterialized seeds backend.1.1.data (.randomizer bottomLayer e) ≠ none := by
    rcases ReleaseSlackO1.bottom_opening_admissible hs e with hd | hm
    · exact Or.inl (hd.of_cache_eq (fun T => hcache _ _))
    · have hf : firstUnmaterialized seeds backend.1.1.data (.randomizer bottomLayer e) =
          firstUnmaterialized seeds data (.randomizer bottomLayer e) := by
        simp only [firstUnmaterialized, hcache]
      exact Or.inr (hf ▸ hm)
  cases hk : source.revealed (.opening bottomLayer e) with
  | some value =>
      simp only [sourceReleaseOpening, runSource_bind, runSource_get, pure_bind,
        hk, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, runSource_pure,
        mem_support_pure_iff] at hr
      subst r
      have hd := (hs.bottom_released e (by
        change source.revealed (.opening bottomLayer e) ≠ none
        rw [hk]; exact Option.some_ne_none value)).of_cache_eq (fun T => hcache _ _)
      exact ⟨ReleaseSlackO1.complete_bottom hs e (fun seed point _ => hcache seed point)
        hvirt hpad (fun _ _ he => he) hd, hd⟩
  | none =>
      have hb : backend.2.1 (.opening bottomLayer e) = none := hrev.1 ▸ hk
      simp only [sourceReleaseOpening, runSource_bind, runSource_get, pure_bind,
        hk, Option.isNone_none, ↓reduceIte,
        runSource_sourceReveal_fresh P seeds q s (.opening bottomLayer e) source backend hk,
        hb, Option.getD_none, runSource_modify, runSource_pure,
        mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨completed, hcompleted, planted, hplanted, rfl⟩ := hr
      have hc := completePrf_done_or_missing P seeds hinj q s
        (.randomizer bottomLayer e) (s (.opening bottomLayer e)) _
        (backend.1, Function.update backend.2.1 (.opening bottomLayer e)
          (some (s (.opening bottomLayer e))), backend.2.2)
        admissible completed hcompleted
      have hf := completePrf_frame P seeds q s
        (.randomizer bottomLayer e) (s (.opening bottomLayer e)) _ _ completed hcompleted
      have hdata := congrArg (fun b : CappedCompilerState C => b.1.1.data) hf.2.1
      have hpending := congrArg DeferredState.pending hdata
      have hvirtual := congrArg DeferredState.virtual hdata
      have hpads := congrArg DeferredState.pads hdata
      have hreveal := congrArg SourceState.revealed hf.1
      change completed.1.2.revealed = Function.update source.revealed
        (.opening bottomLayer e) (some (s (.opening bottomLayer e))) at hreveal
      change completed.2.1.1.data.pending = backend.1.1.data.pending at hpending
      change completed.2.1.1.data.virtual = backend.1.1.data.virtual at hvirtual
      change completed.2.1.1.data.pads = backend.1.1.data.pads at hpads
      have hmid : ReleaseSlackO1 seeds s sig
          ⟨{ completed.1.2 with consistent := completed.1.2.consistent && completed.1.1 }, starts⟩
          completed.2.1.1.data := by
        apply ReleaseSlackO1.complete_bottom hs (source' :=
          { completed.1.2 with consistent := completed.1.2.consistent && completed.1.1 })
          e (fun seed point hn => (hf.2.2.2 seed point hn).trans (hcache seed point))
          (fun f hfe T => by rw [hvirtual]; exact hvirt f hfe T)
          (hpads.trans hpad) ?_ hc.2
        intro f hfe hrf
        change completed.1.2.revealed (.opening bottomLayer f) ≠ none at hrf
        rw [hreveal, Function.update_of_ne (by simpa using hfe)] at hrf
        exact hrf
      have hvalid : PendingValid completed.2.1.1.data := by
        intro p answer hp
        apply hv p answer
        rw [hpending] at hp
        exact hp
      have hplants := sourcePlants_terminal_slackO1 P seeds q s sig starts _ _ _ (by
        intro p hp
        have hkey : p.key = .opening bottomLayer e := of_decide_eq_true (List.mem_filter.mp hp).2
        refine ⟨PendingInput.next_none_of_opening p bottomLayer e hkey, ?_⟩
        change completed.1.2.revealed p.key ≠ none
        rw [hreveal, hkey, Function.update_self]
        exact Option.some_ne_none _) hvalid hmid planted hplanted
      refine ⟨hplants.1, hplants.1.bottom_released e ?_⟩
      change planted.1.2.revealed (.opening bottomLayer e) ≠ none
      rw [hplants.2.2]
      change completed.1.2.revealed (.opening bottomLayer e) ≠ none
      rw [hreveal, Function.update_self]
      exact Option.some_ne_none _

theorem sourceReleaseOpening_slackO1 (hinj : Function.Injective seeds) (e : KeyIndex)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ backend.1.1.data)
    (hv : PendingValid backend.1.1.data) (hrev : RevealRelation s source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReleaseOpening P seeds e) source backend)) :
    ReleaseSlackO1 seeds s sig ⟨r.1.2, starts⟩ r.2.1.1.data ∧
      PointDone seeds r.2.1.1.data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) :=
  sourceReleaseOpening_slack_frameO1 P seeds q s sig starts hinj e source backend
    backend.1.1.data hs (fun _ _ => rfl) (fun _ _ _ => Iff.rfl) rfl hv hrev r hr

set_option backward.isDefEq.respectTransparency false in
theorem sourceVirtual_slackO1 (hinj : Function.Injective seeds) (T : C.Term) (point : Point)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hb : source.signing.bound = sig.bound)
    (hs : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ backend.1.1.data)
    (hv : PendingValid backend.1.1.data) (hrev : RevealRelation s source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceVirtual P seeds T point) source backend)) :
    ReleaseSlackO1 seeds s sig ⟨r.1.2, starts⟩ r.2.1.1.data := by
  cases point with
  | chain lay e l pos =>
      simp only [sourceVirtual, runSource_bind, runSource_virtual, pure_bind,
        runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact ReleaseSlackO1.virtual_unready hs T _ (by intro f hf; cases hf)
  | randomizer lay e =>
      by_cases hl : lay = bottomLayer
      · subst lay
        simp only [sourceVirtual, runSource_bind, runSource_virtual, pure_bind,
          ↓reduceIte, runSource_snapshot, runSource_get] at hr
        split at hr
        · let nextBackend : CappedCompilerState C :=
            (({ backend.1.1 with data := { backend.1.1.data with
                virtual := insert (T, Point.randomizer bottomLayer e) backend.1.1.data.virtual } },
              backend.1.2 + 1), backend.2)
          have hout := sourceReleaseOpening_slack_frameO1 P seeds q s sig starts hinj e source
            nextBackend backend.1.1.data hs (fun _ _ => rfl) (by
              intro f hfe U
              change ((U, Point.randomizer bottomLayer f) ∈
                insert (T, Point.randomizer bottomLayer e) backend.1.1.data.virtual ↔ _)
              simp [hfe]) rfl hv hrev r hr
          exact hout.1
        · rename_i hready
          rw [runSource_pure, mem_support_pure_iff] at hr
          subst r
          exact ReleaseSlackO1.virtual_unready hs T _ (by
            intro f hf
            have he : e = f := (Point.randomizer.inj hf).2
            subst f
            exact fun h => hready ⟨by rw [hb]; exact h.1, h.2⟩)
      · simp only [sourceVirtual, runSource_bind, runSource_virtual, pure_bind,
          hl, ↓reduceIte, runSource_pure, mem_support_pure_iff] at hr
        subst r
        exact ReleaseSlackO1.virtual_unready hs T _ (by
          intro f hf
          exact (hl (Point.randomizer.inj hf).1).elim)

set_option backward.isDefEq.respectTransparency false in
theorem sourceRawHash_slackO1 (query : Query C)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ backend.1.1.data)
    (ha : ReadAllowedO1 seeds sig starts backend.1.1.data query)
    (hready : ∀ e, (∃ seed, query = .prf seed (.randomizer bottomLayer e)) →
      PointDone seeds backend.1.1.data (.randomizer bottomLayer e) (s (.opening bottomLayer e)) ∨
        ¬ReadyAfter seeds backend.1.1.data sig e query)
    (r : (HashOutput × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s
      (liftM (deferredQuery (.hash query))) source backend)) :
    ReleaseSlackO1 seeds s sig ⟨r.1.2, starts⟩ r.2.1.1.data := by
  rw [runSource_liftM, support_map] at hr
  obtain ⟨a, ha', rfl⟩ := hr
  simp only [deferredQuery, HasQuery.instOfMonadLift_query, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, id_map,
    SigningCappedExpectProof.cappedHybrid, revealImpl, countImpl,
    StateT.run_mk, support_map] at ha'
  obtain ⟨b, ⟨c, hc, rfl⟩, rfl⟩ := ha'
  have hfields := compiler_hash_virtual_pads P seeds query backend.1.1 c hc
  exact ReleaseSlackO1.read hs query ha hready
    (compilerImpl_cache_le P seeds (.hash query) backend.1.1 c hc)
    (fun seed point hne =>
      compilerImpl_prf_frame P seeds (.hash query) backend.1.1 c hc seed point hne)
    hfields.1 hfields.2

set_option backward.isDefEq.respectTransparency false in
theorem sourceHash_slackO1 (hinj : Function.Injective seeds) (query : Query C)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hb : source.signing.bound = sig.bound)
    (hs : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ backend.1.1.data)
    (ha : ReadAllowedO1 seeds sig starts backend.1.1.data query)
    (hv : PendingValid backend.1.1.data) (hrev : RevealRelation s source backend)
    (r : (HashOutput × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceHash P seeds query) source backend)) :
    ReleaseSlackO1 seeds s sig ⟨r.1.2, starts⟩ r.2.1.1.data := by
  have raw (hn : ∀ e, ¬∃ seed, query = .prf seed (.randomizer bottomLayer e))
      (hr : r ∈ support (runSource P seeds q s (liftM (deferredQuery (.hash query)))
        source backend)) :
      ReleaseSlackO1 seeds s sig ⟨r.1.2, starts⟩ r.2.1.1.data :=
    sourceRawHash_slackO1 P seeds q s sig starts query source backend hs ha
      (fun e he => (hn e he).elim) r hr
  cases query with
  | prf seed point =>
      cases point with
      | randomizer lay e =>
          by_cases hlay : lay = bottomLayer
          · subst lay
            simp only [sourceHash, ↓reduceIte, runSource_bind, runSource_snapshot,
              runSource_get, pure_bind] at hr
            split at hr
            · rw [runSource_bind, mem_support_bind_iff] at hr
              obtain ⟨released, hreleased, hr⟩ := hr
              have hp := sourceReleaseOpening_slackO1 P seeds q s sig starts hinj e source
                backend hs hv hrev released hreleased
              have hcache := runSource_cache_le P seeds q s (sourceReleaseOpening P seeds e)
                source backend released hreleased
              refine sourceRawHash_slackO1 P seeds q s sig starts _ released.1.2 released.2
                hp.1 (ReadAllowedO1.mono ha hcache) ?_ r hr
              intro f hf
              obtain ⟨seed', he⟩ := hf
              have hef := (Point.randomizer.inj (Query.prf.inj he).2).2
              subst f
              exact Or.inl hp.2
            · rename_i hready
              refine sourceRawHash_slackO1 P seeds q s sig starts _ source backend hs ha ?_ r hr
              intro f hf
              obtain ⟨seed', he⟩ := hf
              have hef := (Point.randomizer.inj (Query.prf.inj he).2).2
              subst f
              exact Or.inr (fun h => hready ⟨by rw [hb]; exact h.1, h.2⟩)
          · apply raw
            · intro f
              rintro ⟨seed', he⟩
              exact hlay (Point.randomizer.inj (Query.prf.inj he).2).1
            · simpa only [sourceHash, hlay, ↓reduceIte, pure_bind] using hr
      | _ =>
          apply raw
          · intro e
            rintro ⟨seed', he⟩
            cases (Query.prf.inj he).2
          · simpa only [sourceHash, pure_bind] using hr
  | _ =>
      apply raw
      · intro e
        rintro ⟨seed, he⟩
        cases he
      · simpa only [sourceHash, pure_bind] using hr

end Steps

end ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps.sourcePlant_terminal_slackO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps.sourcePlant_terminal_slackO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps.sourcePlants_terminal_slackO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps.sourcePlants_terminal_slackO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps.sourceReleaseOpening_slack_frameO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps.sourceReleaseOpening_slack_frameO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps.sourceReleaseOpening_slackO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps.sourceReleaseOpening_slackO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps.sourceVirtual_slackO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps.sourceVirtual_slackO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps.sourceRawHash_slackO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps.sourceRawHash_slackO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps.sourceHash_slackO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1SlackSteps.sourceHash_slackO1
