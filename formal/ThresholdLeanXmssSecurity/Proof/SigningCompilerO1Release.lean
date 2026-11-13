import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Invariant
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Basics

/-! # Complete O1 release invariants

The bottom completion and release sweeps preserve the coalition-indexed slack,
reveal synchronization and pending validity. Covered suffixes have their pads and
exact masked PRF target sums, including when new starts are recorded at a crossing.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Release
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Invariant SigningCompilerO1Basics XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

def runSourceO1 {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (oa : SourceMO1 C α)
    (src : SourceStateO1 C) (backend : CappedCompilerState C) :
    ProbComp ((α × SourceStateO1 C) × CappedCompilerState C) :=
  (simulateQ (SigningCappedExpectProof.cappedHybrid (compilerImpl P seeds)
    (deferredInputSide P) deferredCounted (deferredKey P) (deferredPoint P) q s)
    (oa.run src)).run backend

abbrev BaseInvariant (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (sig : TsigState C) (starts : KeyIndex → ChainIndex → Finset Digit)
    (source : SourceState C) (backend : CappedCompilerState C) :=
  ReleaseInvariantO1 seeds s sig ⟨source, starts⟩ backend

theorem BottomDone.frame {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {data data' : DeferredState C} {e : KeyIndex} {l : ChainIndex} {pos : XmssSecurity.ChainStep}
    (h : BottomDone seeds s data e l pos)
    (hc : ∀ T, data'.cache (.prf (seeds T) (.chain bottomLayer e l (chainStepDigit pos))) =
      data.cache (.prf (seeds T) (.chain bottomLayer e l (chainStepDigit pos))))
    (hp : data'.pads = data.pads) : BottomDone seeds s data' e l pos := by
  refine ⟨by simpa only [hp] using h.1, ?_⟩
  simpa only [bottomReleaseTarget, hp] using h.2.of_cache_eq hc

theorem ReleaseSlackO1.bottom_chain_admissible {seeds : C.Term → HashOutput}
    {s : HiddenKey → Digest} {sig : TsigState C} {src : SourceStateO1 C} {data : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig src data) (e : KeyIndex) (l : ChainIndex)
    (pos : XmssSecurity.ChainStep) :
    PointDone seeds data (.chain bottomLayer e l (chainStepDigit pos))
      (bottomReleaseTarget s data e l pos) ∨
      firstUnmaterialized seeds data (.chain bottomLayer e l (chainStepDigit pos)) ≠ none := by
  rcases h.bottom_chain e l pos with hd | hu | ⟨_, _, _, hlt, hu⟩
  · exact Or.inl hd.2
  · exact Or.inr (hu.missing h.corrupt_bound)
  · exact Or.inr (hu.missing (by omega))

/-- Full post-slack and conservative cache growth retain the exact completed target. -/
theorem BottomDone.persist {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {sig : TsigState C} {src : SourceStateO1 C} {data data' : DeferredState C}
    {e : KeyIndex} {l : ChainIndex} {pos : XmssSecurity.ChainStep}
    (h : BottomDone seeds s data e l pos) (hc : data.cache ≤ data'.cache)
    (hs : ReleaseSlackO1 seeds s sig src data') : BottomDone seeds s data' e l pos := by
  have hfull := (firstUnmaterialized_none_iff seeds data'
    (.chain bottomLayer e l (chainStepDigit pos))).mpr (h.2.mono hc).1
  rcases hs.bottom_chain e l pos with hd | hu | ⟨_, _, _, hlt, hu⟩
  · exact hd
  · exact (hu.missing hs.corrupt_bound hfull).elim
  · exact (hu.missing (by omega) hfull).elim

/-- A fixed coalition and starts map permit ordinary source frames. -/
theorem ReleaseSlackO1.frame {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {sig : TsigState C} {starts : KeyIndex → ChainIndex → Finset Digit}
    {source source' : SourceState C} {data data' : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data)
    (hc : ∀ seed point, data'.cache (.prf seed point) = data.cache (.prf seed point))
    (hv : data'.virtual = data.virtual) (hp : data'.pads = data.pads)
    (hr : ∀ e, source'.revealed (.opening bottomLayer e) ≠ none →
      source.revealed (.opening bottomLayer e) ≠ none) :
    ReleaseSlackO1 seeds s sig ⟨source', starts⟩ data' := by
  have hu : ∀ D point, LackedUncached seeds D data point → LackedUncached seeds D data' point := by
    intro D point hh T hT
    rw [hc]
    exact hh T hT
  have hd : ∀ point target, PointDone seeds data point target → PointDone seeds data' point target :=
    fun _ _ hh => hh.of_cache_eq (fun T => hc _ _)
  refine ⟨h.corrupt_bound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    rcases h.bottom_opening e with hh | ⟨hb, hh⟩ | ⟨hb, T, ht, hh⟩
    · exact Or.inl (hd _ _ hh)
    · exact Or.inr (Or.inl ⟨hb, hu _ _ hh⟩)
    · exact Or.inr (Or.inr ⟨hb, T, hv ▸ ht, (hc _ _).trans hh⟩)
  · intro e l pos
    rcases h.bottom_chain e l pos with hh | hh | ⟨hm, m, hb, hn, hh⟩
    · exact Or.inl (BottomDone.frame hh (fun T => hc _ _) hp)
    · exact Or.inr (Or.inl (hu _ _ hh))
    · exact Or.inr (Or.inr ⟨hm, m, hb, hn, hu _ _ hh⟩)
  · intro b
    exact (h.top_opening b).imp (hd _ _) (hu _ _)
  · intro b l
    exact (h.top_start b l).imp (hd _ _) (hu _ _)
  · intro e he
    exact hd _ _ (h.bottom_released e (hr e he))
  · intro e m hb hn l pos hp'
    exact BottomDone.frame (h.crossed_done e m hb hn l pos hp') (fun T => hc _ _) hp

/-- New pads preserve the existing pad values used by every completed point. -/
theorem ReleaseSlackO1.pads_mono {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {sig : TsigState C} {src : SourceStateO1 C} {data : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig src data) (pads : Point → Option Digest)
    (hp : ∀ point value, data.pads point = some value → pads point = some value) :
    ReleaseSlackO1 seeds s sig src { data with pads := pads } := by
  have done : ∀ e l pos, BottomDone seeds s data e l pos →
      BottomDone seeds s { data with pads := pads } e l pos := by
    intro e l pos hh
    have target : bottomReleaseTarget s { data with pads := pads } e l pos =
        bottomReleaseTarget s data e l pos := by
      by_cases hz : pos.val = 0
      · simp only [bottomReleaseTarget, hz, ↓reduceIte]
      · obtain ⟨value, hv⟩ := Option.ne_none_iff_exists'.mp (hh.1.resolve_left hz)
        simp only [bottomReleaseTarget, hz, ↓reduceIte, hv, hp _ _ hv]
    refine ⟨?_, ?_⟩
    · rcases hh.1 with hz | hn
      · exact Or.inl hz
      · obtain ⟨value, hv⟩ := Option.ne_none_iff_exists'.mp hn
        exact Or.inr (by change pads _ ≠ none; rw [hp _ _ hv]; exact Option.some_ne_none value)
    · rw [target]
      exact hh.2
  refine ⟨h.corrupt_bound, h.bottom_opening, ?_, h.top_opening, h.top_start,
    h.bottom_released, ?_⟩
  · intro e l pos
    rcases h.bottom_chain e l pos with hd | hu | hu
    · exact Or.inl (done e l pos hd)
    · exact Or.inr (Or.inl hu)
    · exact Or.inr (Or.inr hu)
  · intro e m hb hn l pos hc
    exact done e l pos (h.crossed_done e m hb hn l pos hc)

/-- Completing one chain point preserves both coalition alternatives elsewhere. -/
theorem ReleaseSlackO1.complete_chain {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {sig : TsigState C} {starts : KeyIndex → ChainIndex → Finset Digit}
    {source source' : SourceState C} {data data' : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data)
    (e : KeyIndex) (l : ChainIndex) (pos : XmssSecurity.ChainStep)
    (hc : ∀ seed point, point ≠ .chain bottomLayer e l (chainStepDigit pos) →
      data'.cache (.prf seed point) = data.cache (.prf seed point))
    (hv : data'.virtual = data.virtual) (hp : data'.pads = data.pads)
    (hr : ∀ f, source'.revealed (.opening bottomLayer f) ≠ none →
      source.revealed (.opening bottomLayer f) ≠ none)
    (hd : BottomDone seeds s data' e l pos) : ReleaseSlackO1 seeds s sig ⟨source', starts⟩ data' := by
  have done : ∀ point target, point ≠ .chain bottomLayer e l (chainStepDigit pos) →
      PointDone seeds data point target → PointDone seeds data' point target :=
    fun _ _ hn hh => hh.of_cache_eq (fun T => hc _ _ hn)
  have uncache : ∀ D point, point ≠ .chain bottomLayer e l (chainStepDigit pos) →
      LackedUncached seeds D data point → LackedUncached seeds D data' point := by
    intro D point hn hh T hT
    rw [hc _ _ hn]
    exact hh T hT
  have bd : ∀ f j step, BottomDone seeds s data f j step → BottomDone seeds s data' f j step := by
    intro f j step hh
    by_cases he : Point.chain bottomLayer f j (chainStepDigit step) =
        .chain bottomLayer e l (chainStepDigit pos)
    · obtain ⟨_, he, hj, hstep⟩ := Point.chain.inj he
      have hpos : step = pos := Fin.ext (congrArg (fun d : Digit => d.val) hstep)
      subst f; subst j; subst step
      exact hd
    · exact BottomDone.frame hh (fun T => hc _ _ he) hp
  refine ⟨h.corrupt_bound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    rcases h.bottom_opening f with hh | ⟨hb, hh⟩ | ⟨hb, T, ht, hh⟩
    · exact Or.inl (done _ _ (by simp) hh)
    · exact Or.inr (Or.inl ⟨hb, uncache _ _ (by simp) hh⟩)
    · exact Or.inr (Or.inr ⟨hb, T, hv ▸ ht, (hc _ _ (by simp)).trans hh⟩)
  · intro f j step
    by_cases he : Point.chain bottomLayer f j (chainStepDigit step) =
        .chain bottomLayer e l (chainStepDigit pos)
    · obtain ⟨_, he, hj, hstep⟩ := Point.chain.inj he
      have hpos : step = pos := Fin.ext (congrArg (fun d : Digit => d.val) hstep)
      subst f; subst j; subst step
      exact Or.inl hd
    · rcases h.bottom_chain f j step with hh | hh | ⟨hm, m, hb, hn, hh⟩
      · exact Or.inl (bd f j step hh)
      · exact Or.inr (Or.inl (uncache _ _ he hh))
      · exact Or.inr (Or.inr ⟨hm, m, hb, hn, uncache _ _ he hh⟩)
  · intro b
    exact (h.top_opening b).imp (done _ _ (by simp)) (uncache _ _ (by simp))
  · intro b j
    have hn : Point.chain topLayer (topKey b) j (digit 0) ≠
        .chain bottomLayer e l (chainStepDigit pos) := by simp [topLayer, bottomLayer]
    exact (h.top_start b j).imp (done _ _ hn) (uncache _ _ hn)
  · intro f hf
    exact done _ _ (by simp) (h.bottom_released f (hr f hf))
  · intro f m hb hn j step hs
    exact bd f j step (h.crossed_done f m hb hn j step hs)

/-- A reveal may expose a bottom opening only once that opening is complete. -/
theorem ReleaseSlackO1.reveal {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {sig : TsigState C} {starts : KeyIndex → ChainIndex → Finset Digit}
    {source : SourceState C} {data : DeferredState C}
    (h : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data) (key : HiddenKey) (value : Digest)
    (ha : ∀ e, key = .opening bottomLayer e →
      PointDone seeds data (.randomizer bottomLayer e) (s (.opening bottomLayer e))) :
    ReleaseSlackO1 seeds s sig
      ⟨{ source with revealed := Function.update source.revealed key (some value) }, starts⟩ data := by
  refine ⟨h.corrupt_bound, h.bottom_opening, h.bottom_chain, h.top_opening, h.top_start, ?_, h.crossed_done⟩
  intro e he
  by_cases hk : HiddenKey.opening bottomLayer e = key
  · exact ha e hk.symm
  · apply h.bottom_released e
    change Function.update source.revealed key (some value) (.opening bottomLayer e) ≠ none at he
    simpa only [Function.update_of_ne hk] using he

theorem sourceReveal_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (sig : TsigState C)
    (starts : KeyIndex → ChainIndex → Finset Digit) (key : HiddenKey)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ backend.1.1.data)
    (ha : ∀ e, key = .opening bottomLayer e →
      PointDone seeds backend.1.1.data (.randomizer bottomLayer e) (s (.opening bottomLayer e)))
    (r : (Digest × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReveal key) source backend)) :
    ReleaseSlackO1 seeds s sig ⟨r.1.2, starts⟩ r.2.1.1.data := by
  cases hk : source.revealed key with
  | some value =>
      rw [runSource_sourceReveal_cached P seeds q s key source backend value hk, mem_support_pure_iff] at hr
      subst r
      exact hs
  | none =>
      rw [runSource_sourceReveal_fresh P seeds q s key source backend hk, mem_support_pure_iff] at hr
      subst r
      exact ReleaseSlackO1.reveal hs key _ ha

theorem sourceRevealDigest_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (sig : TsigState C)
    (starts : KeyIndex → ChainIndex → Finset Digit) (value : DeferredDigest)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ backend.1.1.data)
    (ha : ∀ e, value = .secret (.opening bottomLayer e) →
      PointDone seeds backend.1.1.data (.randomizer bottomLayer e) (s (.opening bottomLayer e)))
    (r : (Digest × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceRevealDigest value) source backend)) :
    ReleaseSlackO1 seeds s sig ⟨r.1.2, starts⟩ r.2.1.1.data := by
  cases value with
  | known digest =>
      simp only [sourceRevealDigest, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact hs
  | secret key =>
      exact sourceReveal_slack P seeds q s sig starts key source backend hs
        (fun e he => ha e (congrArg DeferredDigest.secret he)) r hr

theorem sourcePad_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (sig : TsigState C)
    (starts : KeyIndex → ChainIndex → Finset Digit) (point : Point)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ backend.1.1.data)
    (r : (Digest × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (liftM (deferredQuery (C := C) (.pad point))) source backend)) :
    ReleaseSlackO1 seeds s sig ⟨r.1.2, starts⟩ r.2.1.1.data ∧
      r.2.1.1.data.pads point = some r.1.1 ∧ r.1.2 = source ∧
      r.2 = (({ backend.1.1 with data :=
        { backend.1.1.data with pads := r.2.1.1.data.pads } }, backend.1.2), backend.2) := by
  rw [runSource_deferredQuery_no_candidate P seeds q s (.pad point) rfl] at hr
  simp only [compilerImpl, StateT.run, support_map] at hr
  obtain ⟨a, ⟨b, hb, rfl⟩, rfl⟩ := hr
  cases hp : backend.1.1.data.pads point with
  | some value =>
      simp only [deferredImpl, hp, mem_support_pure_iff] at hb
      subst b
      exact ⟨hs, hp, rfl, by simp [deferredCounted]⟩
  | none =>
      simp only [deferredImpl, hp, support_map] at hb
      obtain ⟨value, _, rfl⟩ := hb
      refine ⟨ReleaseSlackO1.pads_mono hs _ ?_, Function.update_self .., rfl, by simp [deferredCounted]⟩
      intro other previous hprevious
      by_cases he : other = point
      · subst other
        rw [hp] at hprevious
        cases hprevious
      · rw [Function.update_of_ne he]
        exact hprevious

/-- A single PRF completion installs the exact masked target and retains full O1 slack. -/
theorem completePrf_chain_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (sig : TsigState C) (starts : KeyIndex → ChainIndex → Finset Digit)
    (e : KeyIndex) (l : ChainIndex) (pos : XmssSecurity.ChainStep)
    (source : SourceState C) (backend : CappedCompilerState C)
    (hs : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ backend.1.1.data)
    (hpad : pos.val = 0 ∨ backend.1.1.data.pads (.chain bottomLayer e l (chainStepDigit pos)) ≠ none)
    (r : (Bool × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s
      (liftM (completePrf seeds (.chain bottomLayer e l (chainStepDigit pos))
        (bottomReleaseTarget s backend.1.1.data e l pos))) source backend)) :
    r.1.1 = true ∧ ReleaseSlackO1 seeds s sig ⟨r.1.2, starts⟩ r.2.1.1.data ∧
      BottomDone seeds s r.2.1.1.data e l pos := by
  have hd := completePrf_done_or_missing P seeds hinj q s _ _ source backend
    (ReleaseSlackO1.bottom_chain_admissible hs e l pos) r hr
  have hf := completePrf_frame P seeds q s _ _ source backend r hr
  have hdata := congrArg (fun b : CappedCompilerState C => b.1.1.data) hf.2.1
  have hvirtual := congrArg DeferredState.virtual hdata
  have hpads := congrArg DeferredState.pads hdata
  change r.2.1.1.data.pads = backend.1.1.data.pads at hpads
  have target : bottomReleaseTarget s r.2.1.1.data e l pos =
      bottomReleaseTarget s backend.1.1.data e l pos := by simp only [bottomReleaseTarget, hpads]
  have done : BottomDone seeds s r.2.1.1.data e l pos :=
    ⟨by simpa only [hpads] using hpad, target.symm ▸ hd.2⟩
  exact ⟨hd.1, ReleaseSlackO1.complete_chain hs e l pos
    hf.2.2.2 hvirtual hpads (fun f he => hf.1 ▸ he) done, done⟩

/-- The actual reveal-pad-complete body establishes the full masked bottom constraint. -/
theorem sourceBottomCompletion_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (sig : TsigState C) (starts : KeyIndex → ChainIndex → Finset Digit)
    (e : KeyIndex) (l : ChainIndex) (pos : XmssSecurity.ChainStep)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : BaseInvariant seeds s sig starts source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceBottomCompletion P seeds e l pos) source backend)) :
    BaseInvariant seeds s sig starts r.1.2 r.2 ∧ BottomDone seeds s r.2.1.1.data e l pos := by
  have hv := runSource_pendingValid P seeds q s _ source backend h.2.2 r hr
  rw [runSource_bottomCompletion] at hr
  simp only [mem_support_bind_iff] at hr
  obtain ⟨revealed, hreveal, offset, hoffset, completed, hcompleted, hr⟩ := hr
  have hrevealed := sourceReveal_correct P seeds q s (.bottomChain e l pos)
    source backend h.2.1 revealed hreveal
  have hslack := sourceReveal_slack P seeds q s sig starts (.bottomChain e l pos)
    source backend h.1 (by intro f hf; cases hf) revealed hreveal
  have hoff : ReleaseSlackO1 seeds s sig ⟨offset.1.2, starts⟩ offset.2.1.1.data ∧
      (pos.val = 0 ∨ offset.2.1.1.data.pads (.chain bottomLayer e l (chainStepDigit pos)) ≠ none) ∧
      revealed.1.1 ^^^ offset.1.1 = bottomReleaseTarget s offset.2.1.1.data e l pos ∧
      RevealRelation s offset.1.2 offset.2 := by
    by_cases hp : pos.val = 0
    · simp only [hp, ↓reduceIte, runSource_pure, mem_support_pure_iff] at hoffset
      subst offset
      exact ⟨hslack, Or.inl hp,
        by simp only [bottomReleaseTarget, hp, ↓reduceIte, hrevealed.1], hrevealed.2.1⟩
    · simp only [hp, ↓reduceIte] at hoffset
      have ho := sourcePad_slack P seeds q s sig starts _ revealed.1.2 revealed.2 hslack offset hoffset
      refine ⟨ho.1, Or.inr ?_, ?_, ?_⟩
      · rw [ho.2.1]
        exact Option.some_ne_none _
      · simp only [bottomReleaseTarget, hp, ↓reduceIte, hrevealed.1, ho.2.1, Option.getD_some]
      · have hsource := congrArg SourceState.revealed ho.2.2.1
        have hbackend := congrArg (fun b : CappedCompilerState C => b.2.1) ho.2.2.2
        exact hrevealed.2.1.frame hsource hbackend
  rw [hoff.2.2.1] at hcompleted
  have hcomplete := completePrf_chain_slack P seeds hinj q s sig starts e l pos
    offset.1.2 offset.2 hoff.1 hoff.2.1 completed hcompleted
  have hf := completePrf_frame P seeds q s _ _ offset.1.2 offset.2 completed hcompleted
  have hsource := congrArg SourceState.revealed hf.1
  have hbackend := congrArg (fun b : CappedCompilerState C => b.2.1) hf.2.1
  have hrev := hoff.2.2.2.frame hsource hbackend
  simp only [runSource_modify, mem_support_pure_iff] at hr
  subst r
  exact ⟨⟨ReleaseSlackO1.frame hcomplete.2.1 (fun _ _ => rfl) rfl rfl (fun _ he => he),
    hrev, hv⟩, hcomplete.2.2⟩

/-- Pending plants preserve the full O1 invariant, including all covered targets. -/
theorem sourcePlant_invariant (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (sig : TsigState C)
    (starts : KeyIndex → ChainIndex → Finset Digit) (p : PendingInput)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : BaseInvariant seeds s sig starts source backend)
    (ha : ∀ e, p.key = .opening bottomLayer e →
      PointDone seeds backend.1.1.data (.randomizer bottomLayer e) (s (.opening bottomLayer e)))
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourcePlant P p) source backend)) :
    BaseInvariant seeds s sig starts r.1.2 r.2 := by
  refine ⟨?_, sourcePlant_revealRelation P seeds q s p source backend h.2.1 r hr,
    runSource_pendingValid P seeds q s _ source backend h.2.2 r hr⟩
  simp only [sourcePlant, runSource_bind, runSource_inspect, mem_support_bind_iff] at hr
  obtain ⟨_, rfl, hr⟩ := hr
  cases hp : backend.1.1.data.pending p with
  | none =>
      simp only [hp, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact h.1
  | some answer =>
      simp only [hp, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨ri, hri, rl, hrl, rp, hrp, hr⟩ := hr
      have his := sourceReveal_slack P seeds q s sig starts p.key source backend h.1 ha ri hri
      have hls := sourceRevealDigest_slack P seeds q s sig starts answer.low ri.1.2 ri.2 his
        (fun e he => (PendingValid.low_ne_opening h.2.2 p answer hp bottomLayer e he).elim) rl hrl
      rw [runSource_plant] at hrp
      simp only [support_map] at hrp
      obtain ⟨planted, hplanted, rfl⟩ := hrp
      simp only [runSource_modify, mem_support_pure_iff] at hr
      subst r
      have hdata : planted.2 = { rl.2.1.1.data with cache := planted.2.cache } := by
        cases hc : rl.2.1.1.data.cache (PlantInput.pending P p ri.1.1).query with
        | none =>
            simp only [deferredImpl, StateT.run, hc, mem_support_pure_iff] at hplanted
            subst planted
            rfl
        | some prior =>
            simp only [deferredImpl, StateT.run, hc, mem_support_pure_iff] at hplanted
            subst planted
            rfl
      have hvirtual := congrArg DeferredState.virtual hdata
      have hpads := congrArg DeferredState.pads hdata
      apply ReleaseSlackO1.frame hls (source' := { rl.1.2 with consistent := rl.1.2.consistent && planted.1 })
        ?_ hvirtual hpads (fun _ he => he)
      intro seed point
      apply deferredImpl_prf_frame _ _ planted hplanted
      simp [WritesPrf, PlantInput.query]

/-- A traversal keeps every earlier full bottom constraint while establishing the next one. -/
theorem runSource_mapM_done (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (sig : TsigState C)
    (starts : KeyIndex → ChainIndex → Finset Digit) (e : KeyIndex) (l : ChainIndex)
    (items : List XmssSecurity.ChainStep) (oa : XmssSecurity.ChainStep → SourceM C Unit)
    (step : ∀ pos ∈ items, ∀ source backend, BaseInvariant seeds s sig starts source backend →
      ∀ r : (Unit × SourceState C) × CappedCompilerState C,
      r ∈ support (runSource P seeds q s (oa pos) source backend) →
        BaseInvariant seeds s sig starts r.1.2 r.2 ∧ BottomDone seeds s r.2.1.1.data e l pos)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : BaseInvariant seeds s sig starts source backend)
    (r : (List Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (items.mapM oa) source backend)) :
    BaseInvariant seeds s sig starts r.1.2 r.2 ∧ ∀ pos ∈ items, BottomDone seeds s r.2.1.1.data e l pos := by
  induction items generalizing source backend r with
  | nil =>
      simp only [List.mapM_nil, runSource_pure, mem_support_pure_iff] at hr
      subst r
      exact ⟨h, fun _ hm => (List.not_mem_nil hm).elim⟩
  | cons pos items ih =>
      simp only [List.mapM_cons, runSource_bind, mem_support_bind_iff] at hr
      obtain ⟨head, hhead, tail, htail, hr⟩ := hr
      rw [runSource_pure, mem_support_pure_iff] at hr
      subst r
      have hh := step pos (List.mem_cons_self ..) source backend h head hhead
      have ht := ih (fun p hp => step p (List.mem_cons_of_mem _ hp)) head.1.2 head.2 hh.1 tail htail
      refine ⟨ht.1, ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact BottomDone.persist hh.2
          (runSource_cache_le P seeds q s (items.mapM oa) head.1.2 head.2 tail htail) ht.1.1
      · exact ht.2 p hp

/-- Both actual suffix loops retain pads, target sums, and crossed coverage. -/
theorem sourceReleaseBottomSuffix_base (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (sig : TsigState C) (starts : KeyIndex → ChainIndex → Finset Digit)
    (e : KeyIndex) (l : ChainIndex) (start : Digit)
    (source : SourceState C) (backend : CappedCompilerState C)
    (h : BaseInvariant seeds s sig starts source backend)
    (r : (Unit × SourceState C) × CappedCompilerState C)
    (hr : r ∈ support (runSource P seeds q s (sourceReleaseBottomSuffix P seeds e l start) source backend)) :
    BaseInvariant seeds s sig starts r.1.2 r.2 ∧
      ∀ pos : XmssSecurity.ChainStep, start.val ≤ pos.val → BottomDone seeds s r.2.1.1.data e l pos := by
  rw [sourceReleaseBottomSuffix_eq] at hr
  simp only [runSource_bind, mem_support_bind_iff] at hr
  obtain ⟨completed, hcompleted, planted, hplanted, hr⟩ := hr
  rw [runSource_pure, mem_support_pure_iff] at hr
  subst r
  have hc := runSource_mapM_done P seeds q s sig starts e l _ (sourceBottomCompletion P seeds e l)
    (fun pos _ st b hi a ha => sourceBottomCompletion_slack P seeds hinj q s sig starts e l pos st b hi a ha)
    source backend h completed hcompleted
  have hp : BaseInvariant seeds s sig starts planted.1.2 planted.2 := by
    apply runSource_mapM_inv P seeds q s (fun pos => sourcePlant P (.bottom e l pos))
      (BaseInvariant seeds s sig starts) _ ?_ completed.1.2 completed.2 hc.1 planted hplanted
    intro pos _ st b hi a ha
    exact sourcePlant_invariant P seeds q s sig starts (.bottom e l pos) st b hi
      (by intro f hf; cases hf) a ha
  refine ⟨hp, ?_⟩
  intro pos hpos
  have hm : pos ∈ (List.finRange 3).filter (fun p => start.val ≤ p.val) := by simp [hpos]
  exact BottomDone.persist (hc.2 pos hm)
    (runSource_cache_le P seeds q s _ completed.1.2 completed.2 planted hplanted) hp.1

theorem runSourceO1_liftBase {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (oa : SourceM C α)
    (src : SourceStateO1 C) (backend : CappedCompilerState C) :
    runSourceO1 P seeds q s (liftBase oa) src backend =
      (fun r => ((r.1.1, { src with base := r.1.2 }), r.2)) <$>
        runSource P seeds q s oa src.base backend := by
  simp [runSourceO1, liftBase, runSource, simulateQ_map, StateT.run_map]

theorem runSourceO1_bind {α β : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (oa : SourceMO1 C α) (f : α → SourceMO1 C β)
    (src : SourceStateO1 C) (backend : CappedCompilerState C) :
    runSourceO1 P seeds q s (oa >>= f) src backend =
      runSourceO1 P seeds q s oa src backend >>= fun r => runSourceO1 P seeds q s (f r.1.1) r.1.2 r.2 := by
  simp only [runSourceO1, StateT.run_bind, simulateQ_bind, StateT.run_bind]

theorem runSourceO1_pure {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (a : α) (src : SourceStateO1 C) (backend : CappedCompilerState C) :
    runSourceO1 P seeds q s (pure a) src backend = pure ((a, src), backend) := by
  simp only [runSourceO1, StateT.run_pure, simulateQ_pure, StateT.run_pure]

theorem runSourceO1_get (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (src : SourceStateO1 C) (backend : CappedCompilerState C) :
    runSourceO1 P seeds q s get src backend = pure ((src, src), backend) := by
  simp only [runSourceO1, StateT.run_get, simulateQ_pure, StateT.run_pure]

theorem runSourceO1_modify (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (f : SourceStateO1 C → SourceStateO1 C)
    (src : SourceStateO1 C) (backend : CappedCompilerState C) :
    runSourceO1 P seeds q s (modify f) src backend = pure (((), f src), backend) := by
  simp only [runSourceO1, StateT.run_modify, simulateQ_pure, StateT.run_pure]

theorem runSourceO1_cache_le {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (oa : SourceMO1 C α)
    (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (r : (α × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 P seeds q s oa src backend)) :
    backend.1.1.data.cache ≤ r.2.1.1.data.cache :=
  simulateQ_sticky _ (fun st : CappedCompilerState C => backend.1.1.data.cache ≤ st.1.1.data.cache)
    (fun t st hs a ha => hs.trans (cappedCompiler_cache_le P seeds q s t st a ha))
    (oa.run src) backend le_rfl r hr

/-- The lifted original suffix satisfies the exact O1 full-strength contract. -/
theorem sourceReleaseBottomSuffix_doneO1 (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (sig : TsigState C) (e : KeyIndex) (l : ChainIndex) (start : Digit)
    (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : ReleaseInvariantO1 seeds s sig src backend)
    (r : (Unit × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 P seeds q s
      (liftBase (sourceReleaseBottomSuffix P seeds e l start)) src backend)) :
    ReleaseInvariantO1 seeds s sig r.1.2 r.2 ∧
      ∀ pos : XmssSecurity.ChainStep, start.val ≤ pos.val → BottomDone seeds s r.2.1.1.data e l pos := by
  rw [runSourceO1_liftBase, support_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  exact sourceReleaseBottomSuffix_base P seeds hinj q s sig src.starts e l start src.base backend h a ha

/-- The selected suffix may be computed against the pre-insertion starts invariant. -/
theorem sourceReleaseCovered_base (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (sig : TsigState C) (starts : KeyIndex → ChainIndex → Finset Digit)
    (e : KeyIndex) (l : ChainIndex) (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : BaseInvariant seeds s sig starts src.base backend)
    (r : (Unit × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 P seeds q s (sourceReleaseCovered P seeds e l) src backend)) :
    BaseInvariant seeds s sig starts r.1.2.base r.2 ∧ r.1.2.starts = src.starts ∧
      ∀ pos, Covered r.1.2.starts e l pos → BottomDone seeds s r.2.1.1.data e l pos := by
  simp only [sourceReleaseCovered, runSourceO1_bind, runSourceO1_get, pure_bind] at hr
  cases hf : firstStart (src.starts e l) with
  | none =>
      simp only [hf, runSourceO1_pure, mem_support_pure_iff] at hr
      subst r
      refine ⟨h, rfl, ?_⟩
      rintro pos ⟨d, hd, _⟩
      have he := (firstStart_none_iff _).mp hf
      rw [he] at hd
      exact (Finset.notMem_empty d hd).elim
  | some start =>
      simp only [hf, runSourceO1_liftBase, support_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have hs := sourceReleaseBottomSuffix_base P seeds hinj q s sig starts e l start src.base backend h a ha
      refine ⟨hs.1, rfl, ?_⟩
      rintro pos ⟨d, hd, hdp⟩
      exact hs.2 pos ((firstStart_spec _ _ hf).2 d hd |>.trans hdp)

theorem sourceReleaseCovered_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (sig : TsigState C) (e : KeyIndex) (l : ChainIndex)
    (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : ReleaseInvariantO1 seeds s sig src backend)
    (r : (Unit × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 P seeds q s (sourceReleaseCovered P seeds e l) src backend)) :
    ReleaseInvariantO1 seeds s sig r.1.2 r.2 ∧ r.1.2.starts = src.starts ∧
      ∀ pos, Covered r.1.2.starts e l pos → BottomDone seeds s r.2.1.1.data e l pos := by
  have hh := sourceReleaseCovered_base P seeds hinj q s sig src.starts e l src backend h r hr
  refine ⟨?_, hh.2⟩
  change BaseInvariant seeds s sig r.1.2.starts r.1.2.base r.2
  rw [hh.2.1]
  exact hh.1

/-- New starts are admitted at a stable boundary once their entire suffix is complete. -/
theorem ReleaseSlackO1.record_done {seeds : C.Term → HashOutput} {s : HiddenKey → Digest}
    {sig : TsigState C} {source : SourceState C} {starts : KeyIndex → ChainIndex → Finset Digit}
    {data : DeferredState C} (h : ReleaseSlackO1 seeds s sig ⟨source, starts⟩ data)
    (e : KeyIndex) (l : ChainIndex) (d : Digit)
    (hdone : ∀ pos, Covered (Function.update starts e (Function.update (starts e) l (insert d (starts e l))))
      e l pos → BottomDone seeds s data e l pos) :
    ReleaseSlackO1 seeds s sig
      ⟨source, Function.update starts e (Function.update (starts e) l (insert d (starts e l)))⟩ data := by
  have hsub : ∀ f j, starts f j ⊆
      (Function.update starts e (Function.update (starts e) l (insert d (starts e l)))) f j := by
    intro f j
    by_cases hf : f = e
    · subst f
      by_cases hj : j = l
      · subst j
        simp only [Function.update_self]
        exact Finset.subset_insert _ _
      · simp only [Function.update_self, Function.update_of_ne hj]
        exact Finset.Subset.refl _
    · simp only [Function.update_of_ne hf]
      exact Finset.Subset.refl _
  refine ⟨h.corrupt_bound, h.bottom_opening, ?_, h.top_opening, h.top_start, h.bottom_released, ?_⟩
  · intro f j pos
    rcases h.bottom_chain f j pos with hh | hh | ⟨hm, m, hb, hn, hh⟩
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr ⟨hsub f j hm, m, hb, hn, hh⟩)
  · intro f m hb hn j pos hc
    by_cases hf : f = e
    · subst f
      by_cases hj : j = l
      · subst j
        exact hdone pos hc
      · apply h.crossed_done e m hb hn j pos
        simpa only [Covered, Function.update_self, Function.update_of_ne hj] using hc
    · apply h.crossed_done f m hb hn j pos
      simpa only [Covered, Function.update_of_ne hf] using hc

/-- Recording a start and completing its coverage restores all stable O1 clauses. -/
theorem recordThenCover_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (sig : TsigState C) (e : KeyIndex) (l : ChainIndex) (d : Digit)
    (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : ReleaseInvariantO1 seeds s sig src backend)
    (r : (Unit × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 P seeds q s
      (recordStart e l d >>= fun _ => sourceReleaseCovered P seeds e l) src backend)) :
    ReleaseInvariantO1 seeds s sig r.1.2 r.2 ∧
      ∀ pos, Covered r.1.2.starts e l pos → BottomDone seeds s r.2.1.1.data e l pos := by
  simp only [runSourceO1_bind, recordStart, runSourceO1_modify, pure_bind] at hr
  have hh := sourceReleaseCovered_base P seeds hinj q s sig src.starts e l
    { src with starts := Function.update src.starts e (Function.update (src.starts e) l (insert d (src.starts e l))) }
    backend h r hr
  refine ⟨⟨?_, hh.1.2⟩, hh.2.2⟩
  change ReleaseSlackO1 seeds s sig ⟨r.1.2.base, r.1.2.starts⟩ r.2.1.1.data
  rw [hh.2.1]
  apply ReleaseSlackO1.record_done hh.1.1 e l d
  intro pos hp
  apply hh.2.2 pos
  simpa only [hh.2.1] using hp

/-- A key sweep preserves previously completed chains while visiting every recorded chain. -/
theorem sourceReleaseKey_list (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (sig : TsigState C) (e : KeyIndex) (chains : List ChainIndex)
    (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : ReleaseInvariantO1 seeds s sig src backend)
    (r : (List Unit × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 P seeds q s
      (chains.mapM fun l => sourceReleaseCovered P seeds e l) src backend)) :
    ReleaseInvariantO1 seeds s sig r.1.2 r.2 ∧ r.1.2.starts = src.starts ∧
      ∀ l ∈ chains, ∀ pos, Covered r.1.2.starts e l pos → BottomDone seeds s r.2.1.1.data e l pos := by
  induction chains generalizing src backend r with
  | nil =>
      simp only [List.mapM_nil, runSourceO1_pure, mem_support_pure_iff] at hr
      subst r
      exact ⟨h, rfl, fun _ hm => (List.not_mem_nil hm).elim⟩
  | cons l chains ih =>
      simp only [List.mapM_cons, runSourceO1_bind, mem_support_bind_iff] at hr
      obtain ⟨head, hhead, tail, htail, hr⟩ := hr
      rw [runSourceO1_pure, mem_support_pure_iff] at hr
      subst r
      have hh := sourceReleaseCovered_slack P seeds hinj q s sig e l src backend h head hhead
      have ht := ih head.1.2 head.2 hh.1 tail htail
      refine ⟨ht.1, ht.2.1.trans hh.2.1, ?_⟩
      intro j hj pos hp
      rcases List.mem_cons.mp hj with rfl | hj
      · have hd := hh.2.2 pos (by simpa only [← ht.2.1] using hp)
        exact BottomDone.persist hd
          (runSourceO1_cache_le P seeds q s _ head.1.2 head.2 tail htail) ht.1.1
      · exact ht.2.2 j hj pos hp

/-- The actual complete-key sweep establishes full coverage in every chain. -/
theorem sourceReleaseKey_slack (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (sig : TsigState C) (e : KeyIndex)
    (src : SourceStateO1 C) (backend : CappedCompilerState C)
    (h : ReleaseInvariantO1 seeds s sig src backend)
    (r : (Unit × SourceStateO1 C) × CappedCompilerState C)
    (hr : r ∈ support (runSourceO1 P seeds q s (sourceReleaseKey P seeds e) src backend)) :
    ReleaseInvariantO1 seeds s sig r.1.2 r.2 ∧
      ∀ l pos, Covered r.1.2.starts e l pos → BottomDone seeds s r.2.1.1.data e l pos := by
  simp only [sourceReleaseKey, runSourceO1_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  rw [runSourceO1_pure, mem_support_pure_iff] at hr
  subst r
  have hh := sourceReleaseKey_list P seeds hinj q s sig e _ src backend h a ha
  exact ⟨hh.1, fun l pos hp => hh.2.2 l (by simp) pos hp⟩

end ThresholdLeanXmssSecurity.SigningCompilerO1Release

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.BottomDone.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.BottomDone.frame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.ReleaseSlackO1.bottom_chain_admissible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.ReleaseSlackO1.bottom_chain_admissible

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.BottomDone.persist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.BottomDone.persist

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.ReleaseSlackO1.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.ReleaseSlackO1.frame

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.ReleaseSlackO1.pads_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.ReleaseSlackO1.pads_mono

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.ReleaseSlackO1.complete_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.ReleaseSlackO1.complete_chain

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.ReleaseSlackO1.reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.ReleaseSlackO1.reveal

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceReveal_slack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceReveal_slack

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceRevealDigest_slack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceRevealDigest_slack

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourcePad_slack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourcePad_slack

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.completePrf_chain_slack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.completePrf_chain_slack

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceBottomCompletion_slack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceBottomCompletion_slack

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourcePlant_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourcePlant_invariant

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.runSource_mapM_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.runSource_mapM_done

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceReleaseBottomSuffix_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceReleaseBottomSuffix_base

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.runSourceO1_liftBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.runSourceO1_liftBase

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.runSourceO1_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.runSourceO1_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.runSourceO1_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.runSourceO1_pure

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.runSourceO1_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.runSourceO1_get

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.runSourceO1_modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.runSourceO1_modify

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.runSourceO1_cache_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.runSourceO1_cache_le

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceReleaseBottomSuffix_doneO1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceReleaseBottomSuffix_doneO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceReleaseCovered_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceReleaseCovered_base

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceReleaseCovered_slack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceReleaseCovered_slack

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.ReleaseSlackO1.record_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.ReleaseSlackO1.record_done

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.recordThenCover_slack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.recordThenCover_slack

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceReleaseKey_list' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceReleaseKey_list

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceReleaseKey_slack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Release.sourceReleaseKey_slack
