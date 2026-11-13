import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareNoFalse
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1SlackGuarded
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Marks
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Runs

/-! # No share failure with a false tag in the O1 source

The slack `ReleaseSlackO1` fixes the sum of each fully cached constrained point to its target
`NoFalse.tau`. A point in the coalition alternative of a bottom chain is not fully cached, because
the coalition has fewer than `t` operators and lacks a term.

`BndO1` is the boundary invariant of the O1 source over the lazy share backend. Its last clause
states that a first share failure with a false tag is a lucky read. `FalseSafeO1` states that a
segment keeps `BndO1`. Each segment of the O1 game keeps it. The segments take their invariant
`GuardedReleaseInvariantS` from `SigningCompilerO1SlackGuarded`.

So a first share failure of the lazy run with a false tag is a lucky read, and its probability is
zero. The lemmas are the lemmas of `SigningCompilerShare.NoFalse` for the O1 program.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerO1Invariant SigningCompilerO1Release SigningCompilerShare
open SigningCompilerO1SourceProof SigningCompilerO1Share SigningCompilerO1Slack
open SigningCompilerO1SlackGuarded SigningCompilerO1Marks SigningCompilerO1Runs
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
variable {C : Committee}

/-- The slack of the O1 source fixes the sum of each fully cached constrained point. -/
theorem release_full_targetO1 (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (pads : Point → Digest) (sig : TsigState C)
    (src : SourceStateO1 C) (data : DeferredState C)
    (hr : ReleaseSlackO1 seeds s sig src data)
    (hpads : ∀ p v, data.pads p = some v → v = pads p)
    (p : CPoint) (hf : ∀ T, data.cache (.prf (seeds T) p.val) ≠ none) :
    termSum (cachedTerm seeds data p.val) = NoFalse.tau s pads p := by
  induction p using NoFalse.constrained_cases with
  | ho e =>
      rw [NoFalse.tau_bottom_opening]
      rcases hr.bottom_opening e with h | ⟨_, h⟩ | ⟨_, T, _, h⟩
      · exact h.2
      · exact (NoFalse.full_not_lacked seeds _ data _ hr.corrupt_bound hf h).elim
      · exact (hf T h).elim
  | hc e l pos =>
      rw [NoFalse.tau_bottom_chain]
      rcases hr.bottom_chain e l pos with ⟨hpad, hdone⟩ | h | ⟨_, m, _, hlt, h⟩
      · rw [hdone.2]
        unfold bottomReleaseTarget
        rcases hpad with hz | hne
        · simp only [hz, ↓reduceIte]
        · cases he : data.pads (.chain bottomLayer e l
            (XmssSecurity.CappedChain.chainStepDigit pos)) with
          | none => exact (hne he).elim
          | some v => rw [Option.getD_some, hpads _ v he]
      · exact (NoFalse.full_not_lacked seeds _ data _ hr.corrupt_bound hf h).elim
      · exact (NoFalse.full_not_lacked seeds _ data _ (by omega) hf h).elim
  | hto b =>
      rw [NoFalse.tau_top_opening]
      rcases hr.top_opening b with h | h
      · exact h.2
      · exact (NoFalse.full_not_lacked seeds _ data _ hr.corrupt_bound hf h).elim
  | htc b l =>
      rw [NoFalse.tau_top_start]
      rcases hr.top_start b l with h | h
      · exact h.2
      · exact (NoFalse.full_not_lacked seeds _ data _ hr.corrupt_bound hf h).elim

/-- The slack of the O1 source excludes each fully cached wrong target. -/
theorem release_noWrongO1 (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (s : HiddenKey → Digest) (pads : Point → Digest) (sig : TsigState C)
    (src : SourceStateO1 C) (bm : CappedCompilerState C) (sh : ShareState C)
    (hr : ReleaseSlackO1 seeds s sig src (merged seeds bm sh.cache).1.1.data)
    (hp : NoFalse.PadsMatch pads bm) : ¬Witness.Wrong (NoFalse.tau s pads) sh := by
  rintro ⟨p, hfull, hwrong⟩
  apply hwrong
  rw [share_sum seeds hinj bm sh p]
  apply release_full_targetO1 seeds s pads sig src _ hr hp p
  intro T
  change merge seeds bm.1.1.data.cache sh.cache (key seeds (T, p)) ≠ none
  rw [merge_key seeds hinj]
  exact hfull T

/-- A segment of the O1 source over the lazy share backend keeps the share invariant, the guarded
release invariant and the pad agreement. -/
theorem segment_guardedO1 {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (oa : SourceMXO1 C α) (oa' : SourceMO1 C α)
    (hmap : mapXO1 seeds oa = oa') (hsafe : SafeO1 oa)
    (hpres : SourcePreservesO1 P seeds q s (GuardedReleaseInvariantS seeds s) oa')
    (st : SourceStateO1 C) (bm : CappedCompilerState C × Bool) (sh : ShareState C)
    (hi : Inv seeds bm sh)
    (hg : GuardedReleaseInvariantS seeds s st (merged seeds bm.1 sh.cache))
    (hp : NoFalse.PadsMatch pads bm.1)
    (z) (hz : z ∈ support (Marks.jointRun (lazyHandler τ) P seeds q s pads (oa.run st) bm sh)) :
    Inv seeds z.1.2 z.2 ∧
      GuardedReleaseInvariantS seeds s z.1.1.2 (merged seeds z.1.2.1 z.2.cache) ∧
      NoFalse.PadsMatch pads z.1.2.1 := by
  have hj := NoFalse.joint_project P seeds hinj q s pads τ (oa.run st) (hsafe st) bm sh hi z hz
  have ha := compilerProgramPads_support P seeds q s pads _ _ _ hj.1
  have hr : (z.1.1, merged seeds z.1.2.1 z.2.cache) ∈ support
      (runSourceO1 P seeds q s oa' st (merged seeds bm.1 sh.cache)) := by
    rw [← hmap]
    exact ha
  exact ⟨hj.2, hpres st _ hg _ hr,
    compilerProgramPads_visible P seeds q s pads _ (merged seeds bm.1 sh.cache) hp
      (z.1.1, merged seeds z.1.2.1 z.2.cache) hj.1⟩

/-- The boundary invariant of the O1 source over the lazy share backend. -/
def BndO1 (seeds : C.Term → HashOutput) (s : HiddenKey → Digest) (pads : Point → Digest)
    (st : SourceStateO1 C) (bm : CappedCompilerState C × Bool) (sh : ShareState C) : Prop :=
  bm.2 = st.base.hiddenFlag ∧ Inv seeds bm sh ∧
    GuardedReleaseInvariantS seeds s st (merged seeds bm.1 sh.cache) ∧
    NoFalse.PadsMatch pads bm.1 ∧ Witness.ShareOK (NoFalse.tau s pads) sh ∧
    (∀ k l, sh.bad = some (false, k, l) → k = .read ∧ l = true)

/-- A segment of the O1 source keeps the boundary invariant. -/
def FalseSafeO1 {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (oa : SourceMXO1 C α) : Prop :=
  ∀ st bm sh, BndO1 seeds s pads st bm sh →
    ∀ z ∈ support (Marks.jointRun (lazyHandler (NoFalse.tau s pads)) P seeds q s pads
        (oa.run st) bm sh),
      BndO1 seeds s pads z.1.1.2 z.1.2 z.2

/-- At an endpoint with the flag down no target is wrong. At an endpoint with the flag up a false
tag is old. -/
theorem bnd_of_endpointO1 (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (s : HiddenKey → Digest) (pads : Point → Digest) (old sh : ShareState C)
    (st : SourceStateO1 C) (bm : CappedCompilerState C × Bool)
    (he : bm.2 = st.base.hiddenFlag) (hi : Inv seeds bm sh)
    (hg : GuardedReleaseInvariantS seeds s st (merged seeds bm.1 sh.cache))
    (hp : NoFalse.PadsMatch pads bm.1) (hs : Witness.ShareOK (NoFalse.tau s pads) sh)
    (hn : ∀ k l, old.bad = some (false, k, l) → k = .read ∧ l = true)
    (ht : ∀ r, sh.bad = some r → old.bad = some r ∨ r.1 = st.base.hiddenFlag) :
    BndO1 seeds s pads st bm sh := by
  refine ⟨he, hi, hg, hp, hs, ?_⟩
  intro k l hb
  cases hf : st.base.hiddenFlag with
  | false =>
      by_contra hnot
      exact release_noWrongO1 seeds hinj s pads st.base.signing st bm.1 sh (hg.1.2.2 hf).1 hp
        (hs.2 ⟨false, k, l, hb, hnot⟩)
  | true =>
      rcases ht (false, k, l) hb with hold | htag
      · exact hn k l hold
      · simp [hf] at htag

/-- A quiet segment of the O1 source keeps the boundary invariant. -/
theorem falseSafe_quietO1 {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (oa : SourceMXO1 C α) (oa' : SourceMO1 C α) (hmap : mapXO1 seeds oa = oa')
    (hsafe : SafeO1 oa) (hquiet : QuietO1 oa)
    (hpres : SourcePreservesO1 P seeds q s (GuardedReleaseInvariantS seeds s) oa') :
    FalseSafeO1 P seeds q s pads oa := by
  intro st bm sh h z hz
  rcases h with ⟨he, hi, hg, hp, hs, hn⟩
  have hseg := segment_guardedO1 P seeds hinj q s pads (NoFalse.tau s pads) oa oa' hmap hsafe
    hpres st bm sh hi hg hp z hz
  have hquiet' := QuietO1.at hquiet st
  have hsource := Marks.joint_support _ _ _ _ _ _ _ _ _ z hz
  have hf := hquiet'.2 z.1.1 hsource
  have hmarks := NoFalse.joint_mark_eq P seeds q s pads (NoFalse.tau s pads) _ hquiet'.1 bm sh
    z hz
  apply bnd_of_endpointO1 seeds hinj s pads sh z.2 z.1.1.2 z.1.2
    (hmarks.trans (he.trans hf.symm)) hseg.1 hseg.2.1 hseg.2.2
    (NoFalse.joint_shareOK P seeds q s pads (NoFalse.tau s pads) _ bm sh hs z hz) hn
  intro r hr
  rcases NoFalse.joint_tagFrom P seeds q s pads (NoFalse.tau s pads) _ hquiet'.1 bm sh z hz r hr
    with hold | htag
  · exact Or.inl hold
  · exact Or.inr (htag.trans (he.trans hf.symm))

/-- Each oracle call of the O1 source keeps the boundary invariant. The rest of the call after its
first mark sets the flag to that mark. -/
theorem falseSafe_oracleO1 (prims : Primitives) (x : Keys3 C) (hinj : Function.Injective x.2.1)
    (top : TopTree) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : (LocalSpec C + TsigSpec C).Domain) :
    FalseSafeO1 x.1 x.2.1 q s pads (sourceOraclesO1X prims x top t) := by
  intro st bm sh h z hz
  rcases h with ⟨he, hi, hg, hp, hs, hn⟩
  have hseg := segment_guardedO1 x.1 x.2.1 hinj q s pads (NoFalse.tau s pads)
    _ _ (mapXO1_sourceOracles prims x top t) (safe_sourceOraclesO1X prims x top t)
    (sourceOraclesO1_guardedS prims x q s hinj top t) st bm sh hi hg hp z hz
  have hshares := NoFalse.joint_shareOK x.1 x.2.1 q s pads (NoFalse.tau s pads) _ bm sh hs z hz
  rw [sourceOraclesO1X_marked, Marks.jointRun_bind, Marks.joint_mark] at hz
  simp only [pure_bind] at hz
  have hnm := callRestO1_noMark prims x top st t
  have hf := callRestO1_flag prims x top st t z.1.1
    (Marks.joint_support _ _ _ _ _ _ _ _ _ z hz)
  have hm := NoFalse.joint_mark_eq x.1 x.2.1 q s pads (NoFalse.tau s pads) _ hnm
    (bm.1, Marks.callMark x st.base t) sh z hz
  apply bnd_of_endpointO1 x.2.1 hinj s pads sh z.2 z.1.1.2 z.1.2
    (hm.trans hf.symm) hseg.1 hseg.2.1 hseg.2.2 hshares hn
  intro r hr
  rcases NoFalse.joint_tagFrom x.1 x.2.1 q s pads (NoFalse.tau s pads) _ hnm
    (bm.1, Marks.callMark x st.base t) sh z hz r hr with hold | htag
  · exact Or.inl hold
  · exact Or.inr (htag.trans hf.symm)

namespace FalseSafeO1
variable {α β : Type} {P : PublicParameter} {seeds : C.Term → HashOutput}
variable {q : ℕ} {s : HiddenKey → Digest} {pads : Point → Digest}

theorem pure (a : α) : FalseSafeO1 P seeds q s pads (Pure.pure a) := by
  intro st bm sh h z hz
  simp only [StateT.run_pure, Marks.jointRun, simulateQ_pure, mem_support_pure_iff] at hz
  subst z
  exact h

theorem bind {oa : SourceMXO1 C α} {f : α → SourceMXO1 C β}
    (h : FalseSafeO1 P seeds q s pads oa) (hf : ∀ a, FalseSafeO1 P seeds q s pads (f a)) :
    FalseSafeO1 P seeds q s pads (oa >>= f) := by
  intro st bm sh hst z hz
  rw [StateT.run_bind, Marks.jointRun_bind] at hz
  simp only [mem_support_bind_iff] at hz
  obtain ⟨mid, hm, hz⟩ := hz
  exact hf mid.1.1.1 mid.1.1.2 mid.1.2 mid.2 (h st bm sh hst mid hm) z hz

theorem map (f : α → β) {oa : SourceMXO1 C α} (h : FalseSafeO1 P seeds q s pads oa) :
    FalseSafeO1 P seeds q s pads (f <$> oa) := by
  simpa only [bind_pure_comp] using bind h (fun a => pure (f a))

theorem simulate {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (SourceMXO1 C)) (oa : OracleComp spec α)
    (h : ∀ t, FalseSafeO1 P seeds q s pads (impl t)) :
    FalseSafeO1 P seeds q s pads (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      simpa only [simulateQ_pure] using
        pure (P := P) (seeds := seeds) (q := q) (s := s) (pads := pads) a
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact bind (h t) ih

theorem get_mark (f : SourceStateO1 C → SourceMXO1 C α)
    (hf : ∀ st, FalseSafeO1 P seeds q s pads (f st)) :
    FalseSafeO1 P seeds q s pads (do
      let st ← get
      let _ ← liftM (markQ (C := C) st.base.hiddenFlag)
      f st) := by
  intro st bm sh h z hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  change z ∈ support (Marks.jointRun (lazyHandler (NoFalse.tau s pads)) P seeds q s pads
    (markQ st.base.hiddenFlag >>= fun _ => (f st).run st) bm sh) at hz
  rw [Marks.jointRun_bind, Marks.joint_mark] at hz
  simp only [pure_bind] at hz
  have hb : (bm.1, st.base.hiddenFlag) = bm := by rw [← h.1]
  rw [hb] at hz
  exact hf st st bm sh h z hz

end FalseSafeO1

attribute [local irreducible] FalseSafeO1 Queries SafeO1 QuietO1
attribute [local irreducible] sourceProgramO1X sourceProgramO1 sourceGameO1X sourceGameO1

set_option maxRecDepth 100000 in
/-- The setup keeps the boundary invariant. -/
theorem falseSafe_topO1 (x : Keys3 C) (hinj : Function.Injective x.2.1)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    FalseSafeO1 x.1 x.2.1 q s pads
      (SigningCompilerO1SourceProof.liftBaseX (sourceTopTreeX x.1 x.2.1)) :=
  falseSafe_quietO1 x.1 x.2.1 hinj q s pads _ (liftBase (sourceTopTree x.1 x.2.1))
    (by rw [mapXO1_liftBaseX, mapX_sourceTopTree])
    (safe_liftBaseX (safe_sourceTopTreeX x.1 x.2.1))
    (QuietO1.liftBaseX (Marks.quiet_sourceTopTreeX x.1 x.2.1))
    (setupO1_guardedS x q s hinj)

/-- One call of the verification keeps the boundary invariant. -/
theorem falseSafe_verifyO1 (x : Keys3 C) (hinj : Function.Injective x.2.1)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (st : SourceState C) (input : HashInput) :
    FalseSafeO1 x.1 x.2.1 q s pads (SigningCompilerO1SourceProof.liftBaseX (do
      let value ← sourceHashX x.1 x.2.1 (.hash input)
      modify fun (state : SourceState C) => { state with candidates :=
        state.candidates ++ SigningGuessLinkProof.callCandidates x.1 st.signing st.exposed input }
      pure value : SourceMX C HashOutput)) := by
  apply falseSafe_quietO1 x.1 x.2.1 hinj q s pads _
    (liftBase (do
      let value ← sourceHash x.1 x.2.1 (.hash input)
      modify fun (state : SourceState C) => { state with candidates :=
        state.candidates ++ SigningGuessLinkProof.callCandidates x.1 st.signing st.exposed input }
      pure value))
  · rw [mapXO1_liftBaseX]
    simp only [mapX_bind, mapX_sourceHash, mapX_modify, mapX_pure]
  · exact safe_liftBaseX (safe_verifyBaseX x.1 x.2.1 _ input)
  · exact QuietO1.liftBaseX (Marks.quiet_verify x.1 x.2.1 st input)
  · exact verifyO1_guardedS x q s hinj st input

set_option maxRecDepth 100000 in
/-- The honest-signature tail keeps the boundary invariant. -/
theorem falseSafe_honestO1 (prims : Primitives) (x : Keys3 C) (hinj : Function.Injective x.2.1)
    (top : TopTree) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (e : KeyIndex) (message : Message) :
    FalseSafeO1 x.1 x.2.1 q s pads
      (SigningCompilerO1SourceProof.liftBaseX (sourceHonestSignatureX prims x top e message)) :=
  falseSafe_quietO1 x.1 x.2.1 hinj q s pads _
    (liftBase (sourceHonestSignature prims x top e message))
    (by rw [mapXO1_liftBaseX, mapX_sourceHonestSignature])
    (safe_liftBaseX (safe_sourceHonestSignatureX prims x top e message))
    (QuietO1.liftBaseX (Marks.quiet_sourceHonestSignatureX prims x top e message))
    (honestO1_guardedS prims x q s hinj top e message)

/-- The complete O1 game keeps the boundary invariant. -/
theorem sourceGameO1X_falseSafe (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    FalseSafeO1 x.1 x.2.1 q s pads (sourceGameO1X prims A x) := by
  unfold sourceGameO1X
  apply FalseSafeO1.get_mark
  intro initial
  apply FalseSafeO1.bind (falseSafe_topO1 x hinj q s pads)
  intro top
  apply FalseSafeO1.bind (FalseSafeO1.simulate _ _ (falseSafe_oracleO1 prims x hinj top q s pads))
  intro forgery
  apply FalseSafeO1.get_mark
  intro st
  apply FalseSafeO1.bind (FalseSafeO1.simulate _ _ (falseSafe_verifyO1 x hinj q s pads st.base))
  intro verified
  split <;> simp only [pure_bind]
  · exact FalseSafeO1.pure _
  · exact FalseSafeO1.bind (falseSafe_honestO1 prims x hinj top q s pads _ _)
      fun _ => FalseSafeO1.pure _

/-- The initial states of the O1 source, of the compiler and of the share table satisfy the
boundary invariant. -/
theorem bndO1_initial (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (pads : Point → Digest) :
    BndO1 seeds s pads (sourceInitO1 (C := C)) (((compilerInit, 0), fun _ => none, false), false)
      (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool)) := by
  refine ⟨rfl, ?_, ?_, ?_, Witness.shareOK_init _, ?_⟩
  · constructor
    · intro query z hz
      rfl
    · simp [DoneCached, SigningShareLazy.init]
  · simpa only [merged_init] using guardedReleaseInvariantS_initial (s := s) seeds
  · intro p v hp
    cases hp
  · intro k l hb
    cases hb

section FlagRuns
variable (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest)
  (pads : Point → Digest)

/-- A first share failure of the lazy run with a false tag is a lucky read. -/
theorem lazyRunO1_noFalse (hinj : Function.Injective x.2.1)
    (z : CompilerOutcomeO1 C × ShareState C)
    (hz : z ∈ support (lazyRunO1 prims A x q s pads (NoFalse.tau s pads)))
    (k : SigningShareLazy.Kind) (l : Bool) (hb : z.2.bad = some (false, k, l)) :
    k = .read ∧ l = true := by
  change z ∈ support ((simulateQ (lazyHandler (NoFalse.tau s pads)) (do
      let result ← (simulateQ (shareBackend x.1 x.2.1 q s pads)
        (sourceProgramO1X prims A x)).run (((compilerInit, 0), fun _ => none, false), false)
      let view ← shareQuery (C := C) .view
      pure (result.1, merged x.2.1 result.2.1 view.1))).run SigningShareLazy.init) at hz
  simp only [simulateQ_bind, StateT.run_bind, lazy_view_run, pure_bind, simulateQ_pure,
    StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  have hs := sourceGameO1X_falseSafe prims A x hinj q s pads
  unfold FalseSafeO1 at hs
  have h := hs sourceInitO1 (((compilerInit, 0), fun _ => none, false), false)
    SigningShareLazy.init (bndO1_initial x.2.1 s pads) r
    (by simpa only [Marks.jointRun, sourceProgramO1X] using hr)
  exact h.2.2.2.2.2 k l hb

/-- The lazy run has no first share failure with a false tag that is not a lucky read. -/
theorem lazyRunO1_nonLucky_zero (hinj : Function.Injective x.2.1)
    (k : SigningShareLazy.Kind) (l : Bool) (hnot : ¬(k = .read ∧ l = true)) :
    Pr[fun z => z.2.bad = some (false, k, l) |
      lazyRunO1 prims A x q s pads (NoFalse.tau s pads)] = 0 :=
  probEvent_eq_zero_iff.mpr fun z hz hb =>
    hnot (lazyRunO1_noFalse prims A x q s pads hinj z hz k l hb)

/-- A lucky read with a false tag has probability zero, by the ratio of lucky reads of the lazy
run. -/
theorem lazyRunO1_luckyFalse_zero (hinj : Function.Injective x.2.1) :
    Pr[fun z => z.2.bad = some (false, .read, true) |
      lazyRunO1 prims A x q s pads (NoFalse.tau s pads)] = 0 := by
  have hr := SigningShareLazy.lazy_lucky_ratio C.terms terms_nodup mem_terms
    (NoFalse.tau s pads) (shareRunTagO1 prims A x q s pads Prod.snd)
    (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool)) rfl false
  change Pr[fun z => z.2.bad = some (false, .read, false) |
      lazyRunO1 prims A x q s pads (NoFalse.tau s pads)] =
    (Fintype.card SigningShareLazy.Digest - 1 : ℕ) *
      Pr[fun z => z.2.bad = some (false, .read, true) |
        lazyRunO1 prims A x q s pads (NoFalse.tau s pads)] at hr
  rw [lazyRunO1_nonLucky_zero prims A x q s pads hinj .read false (by simp)] at hr
  have hn : ((Fintype.card SigningShareLazy.Digest - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    have hc : Fintype.card SigningShareLazy.Digest = 2 ^ 128 := by
      change Fintype.card (BitVec 128) = 2 ^ 128
      exact card_bitVec 128
    rw [hc]
    norm_num
  exact (mul_eq_zero.mp hr.symm).resolve_left hn

/-- The lazy run has no first share failure with a false tag. -/
theorem lazyRunO1_falseBad_zero (hinj : Function.Injective x.2.1) (k : SigningShareLazy.Kind) :
    Pr[fun z => (SigningShareLazy.erase z.2).bad = some (false, k) |
      lazyRunO1 prims A x q s pads (NoFalse.tau s pads)] = 0 := by
  apply probEvent_eq_zero_iff.mpr
  intro z hz hb
  have hbad : ∃ l, z.2.bad = some (false, k, l) := by
    simp only [SigningShareLazy.erase, Option.map_eq_some_iff] at hb
    obtain ⟨⟨g, kind, l⟩, he, hval⟩ := hb
    cases hval
    exact ⟨l, he⟩
  obtain ⟨l, hl⟩ := hbad
  have hshape := lazyRunO1_noFalse prims A x q s pads hinj z hz k l hl
  rcases hshape with ⟨rfl, rfl⟩
  exact (probEvent_eq_zero_iff.mp (lazyRunO1_luckyFalse_zero prims A x q s pads hinj)) z hz hl

end FlagRuns

end ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.release_full_targetO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.release_full_targetO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.release_noWrongO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.release_noWrongO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.segment_guardedO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.segment_guardedO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.bnd_of_endpointO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.bnd_of_endpointO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.falseSafe_quietO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.falseSafe_quietO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.falseSafe_oracleO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.falseSafe_oracleO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.FalseSafeO1.pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.FalseSafeO1.pure

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.FalseSafeO1.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.FalseSafeO1.bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.FalseSafeO1.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.FalseSafeO1.map

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.FalseSafeO1.simulate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.FalseSafeO1.simulate

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.FalseSafeO1.get_mark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.FalseSafeO1.get_mark

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.falseSafe_topO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.falseSafe_topO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.falseSafe_verifyO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.falseSafe_verifyO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.falseSafe_honestO1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.falseSafe_honestO1

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.sourceGameO1X_falseSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.sourceGameO1X_falseSafe

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.bndO1_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.bndO1_initial

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.lazyRunO1_noFalse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.lazyRunO1_noFalse

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.lazyRunO1_nonLucky_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.lazyRunO1_nonLucky_zero

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.lazyRunO1_luckyFalse_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.lazyRunO1_luckyFalse_zero

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.lazyRunO1_falseBad_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1NoFalse.lazyRunO1_falseBad_zero
