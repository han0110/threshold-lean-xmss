import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareWitness
import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareTable

/-! # Guarded release targets of the lazy constrained-share compiler

The fixed target table uses the private pad table. Visible pads identify
those fixed entries at the original source's stable release boundaries.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerShare.NoFalse
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
variable {C : Committee}

/-- Fixed targets for the four constrained source shapes. -/
def tau (s : HiddenKey → Digest) (pads : Point → Digest) (p : CPoint) : Digest :=
  match p.val with
  | .randomizer lay e => s (.opening lay e)
  | .chain lay e l d =>
    if h : lay = bottomLayer ∧ d.val < 3 then
      s (.bottomChain e l ⟨d.val, h.2⟩) ^^^
        (if d.val = 0 then 0 else pads (.chain bottomLayer e l d))
    else if hb : ∃ b, e = topKey b then
      s (.topChain (Classical.choose hb) l ⟨0, by decide⟩)
    else 0

-- Ported verbatim from LifetimeEmulation.topKey_injective:107.
theorem topKey_injective : Function.Injective topKey := fun b b' h => Fin.ext (by simpa [topKey] using congrArg Fin.val h)

theorem tau_bottom_opening (s : HiddenKey → Digest) (pads : Point → Digest) (e : KeyIndex) :
    tau s pads ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩ = s (.opening bottomLayer e) := rfl

theorem tau_top_opening (s : HiddenKey → Digest) (pads : Point → Digest) (b : XmssSecurity.TopIndex) :
    tau s pads ⟨.randomizer topLayer (topKey b), constrained_top_randomizer b⟩ =
      s (.opening topLayer (topKey b)) := rfl

theorem tau_bottom_chain (s : HiddenKey → Digest) (pads : Point → Digest) (e : KeyIndex)
    (l : ChainIndex) (pos : XmssSecurity.ChainStep) :
    tau s pads ⟨.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos),
      constrained_bottom_chain e l _ pos.isLt⟩ =
      s (.bottomChain e l pos) ^^^ (if pos.val = 0 then 0 else
        pads (.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos))) := by
  dsimp only [tau]
  split
  · rfl
  · rename_i h
    exact (h ⟨rfl, pos.isLt⟩).elim

theorem tau_top_start (s : HiddenKey → Digest) (pads : Point → Digest)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) :
    tau s pads ⟨.chain topLayer (topKey b) l (digit 0), constrained_top_chain b l⟩ =
      s (.topChain b l ⟨0, by decide⟩) := by
  have layers : topLayer ≠ bottomLayer := by decide
  simp only [tau, layers, false_and, ↓reduceDIte]
  have hb : ∃ b', topKey b = topKey b' := ⟨b, rfl⟩
  rw [dif_pos hb]
  rw [← topKey_injective (Classical.choose_spec hb)]

/-- The compiler's visible pad map agrees with the fixed private table. -/
def PadsMatch (pads : Point → Digest) (bm : CappedCompilerState C) : Prop :=
  ∀ p v, bm.1.1.data.pads p = some v → v = pads p

/-- Every constrained point is one of the four source release shapes. -/
theorem constrained_cases {motive : CPoint → Prop}
    (ho : ∀ e, motive ⟨.randomizer bottomLayer e, constrained_bottom_randomizer e⟩)
    (hc : ∀ e l (pos : XmssSecurity.ChainStep), motive
      ⟨.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos),
        constrained_bottom_chain e l _ pos.isLt⟩)
    (hto : ∀ b, motive ⟨.randomizer topLayer (topKey b), constrained_top_randomizer b⟩)
    (htc : ∀ b l, motive ⟨.chain topLayer (topKey b) l (digit 0),
      constrained_top_chain b l⟩) (p : CPoint) : motive p := by
  rcases p with ⟨point, hp⟩
  cases point with
  | randomizer lay e =>
      rcases hp with rfl | ⟨rfl, b, rfl⟩
      · exact ho e
      · exact hto b
  | chain lay e l d =>
      rcases hp with ⟨rfl, hd⟩ | ⟨rfl, ⟨b, rfl⟩, rfl⟩
      · exact hc e l ⟨d.val, hd⟩
      · exact htc b l

/-- A fully cached point cannot retain all the coalition's lacked terms. -/
theorem full_not_lacked (seeds : C.Term → HashOutput) (D : Finset C.Party)
    (data : DeferredState C) (p : Point) (hD : D.card ≤ C.t - 1)
    (hf : ∀ T, data.cache (.prf (seeds T) p) ≠ none) :
    ¬LackedUncached seeds D data p := by
  obtain ⟨T, hT⟩ := exists_lacked_term D hD
  exact fun h => hf T (h T hT)

/-- Release slack fixes the sum of every fully cached constrained point. -/
theorem release_full_target (seeds : C.Term → HashOutput)
    (s : HiddenKey → Digest) (pads : Point → Digest) (source : SourceState C)
    (data : DeferredState C) (hr : ReleaseSlack seeds s source data)
    (hpads : ∀ p v, data.pads p = some v → v = pads p)
    (p : CPoint) (hf : ∀ T, data.cache (.prf (seeds T) p.val) ≠ none) :
    termSum (cachedTerm seeds data p.val) = tau s pads p := by
  induction p using constrained_cases with
  | ho e =>
      rw [tau_bottom_opening]
      rcases hr.bottom_opening e with h | ⟨_, h⟩ | ⟨_, T, _, h⟩
      · exact h.2
      · exact (full_not_lacked seeds _ data _ hr.corrupt_bound hf h).elim
      · exact (hf T h).elim
  | hc e l pos =>
      rw [tau_bottom_chain]
      rcases hr.bottom_chain e l pos with ⟨hpad, hdone⟩ | h
      · rw [hdone.2]
        unfold bottomReleaseTarget
        rcases hpad with hz | hne
        · simp only [hz, ↓reduceIte]
        · cases he : data.pads (.chain bottomLayer e l
            (XmssSecurity.CappedChain.chainStepDigit pos)) with
          | none => exact (hne he).elim
          | some v => rw [Option.getD_some, hpads _ v he]
      · exact (full_not_lacked seeds _ data _ hr.corrupt_bound hf h).elim
  | hto b =>
      rw [tau_top_opening]
      rcases hr.top_opening b with h | h
      · exact h.2
      · exact (full_not_lacked seeds _ data _ hr.corrupt_bound hf h).elim
  | htc b l =>
      rw [tau_top_start]
      rcases hr.top_start b l with h | h
      · exact h.2
      · exact (full_not_lacked seeds _ data _ hr.corrupt_bound hf h).elim

/-- Admissible source programs preserve the disjoint share/cache invariant. -/
theorem joint_inv (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (τ : CPoint → Digest) {α : Type}
    (oa : OracleComp (SpecX C) α) (ha : Queries Allowed oa)
    (bm : CappedCompilerState C × Bool) (sh : ShareState C) (hi : Inv seeds bm sh)
    (z) (hz : z ∈ support (Marks.jointRun (lazyHandler τ) P seeds q s pads oa bm sh)) :
    Inv seeds z.1.2 z.2 := by
  induction oa using OracleComp.inductionOn generalizing bm sh with
  | pure a =>
      simp only [Marks.jointRun, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff] at hz
      subst z
      exact hi
  | query_bind t next ih =>
      have hq := (isQueryBound_query_bind_iff ..).mp ha
      rw [Marks.jointRun_bind] at hz
      simp only [mem_support_bind_iff] at hz
      obtain ⟨r, hr, hz⟩ := hz
      exact ih r.1.1 (hq.2 r.1.1) r.1.2 r.2
        ((step_law P seeds hinj q s pads τ t hq.1 bm sh hi).2 r hr) hz

/-- The share interpreter projects into the actual fixed-pad compiler. -/
theorem joint_project (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest)
    (pads : Point → Digest) (τ : CPoint → Digest) {α : Type}
    (oa : OracleComp (SpecX C) α) (ha : Queries Allowed oa)
    (bm : CappedCompilerState C × Bool) (sh : ShareState C) (hi : Inv seeds bm sh)
    (z) (hz : z ∈ support (Marks.jointRun (lazyHandler τ) P seeds q s pads oa bm sh)) :
    (z.1.1, merged seeds z.1.2.1 z.2.cache) ∈ support
      (compilerProgramPads P seeds q s pads (simulateQ (expand seeds) oa)
        (merged seeds bm.1 sh.cache)) ∧ Inv seeds z.1.2 z.2 := by
  refine ⟨?_, joint_inv P seeds hinj q s pads τ oa ha bm sh hi z hz⟩
  rw [compilerProgramPads_ordinary,
    program_eq_of_steps P seeds q s pads τ (step_law P seeds hinj q s pads τ) oa ha bm sh hi]
  simp only [support_map, Set.mem_image]
  exact ⟨z, hz, rfl⟩

/-- Guarded release slack excludes every fully cached wrong target. -/
theorem release_noWrong (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (s : HiddenKey → Digest) (pads : Point → Digest) (st : SourceState C)
    (bm : CappedCompilerState C) (sh : ShareState C)
    (hr : ReleaseSlack seeds s st (merged seeds bm sh.cache).1.1.data)
    (hp : PadsMatch pads bm) : ¬Witness.Wrong (tau s pads) sh := by
  rintro ⟨p, hfull, hwrong⟩
  apply hwrong
  rw [share_sum seeds hinj bm sh p]
  apply release_full_target seeds s pads st _ hr hp p
  intro T
  change merge seeds bm.1.1.data.cache sh.cache (key seeds (T, p)) ≠ none
  rw [merge_key seeds hinj]
  exact hfull T

/-- Fixed-pad support projects into A100's actual source interpreter. -/
theorem segment_guarded {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (oa : SourceMX C α) (oa' : SourceM C α)
    (hmap : mapX seeds oa = oa') (hsafe : Safe oa)
    (hpres : SourcePreserves P seeds q s (GuardedReleaseInvariant seeds s) oa')
    (st : SourceState C) (bm : CappedCompilerState C × Bool) (sh : ShareState C)
    (hi : Inv seeds bm sh)
    (hg : GuardedReleaseInvariant seeds s st (merged seeds bm.1 sh.cache))
    (hp : PadsMatch pads bm.1)
    (z) (hz : z ∈ support (Marks.jointRun (lazyHandler τ) P seeds q s pads (oa.run st) bm sh)) :
    Inv seeds z.1.2 z.2 ∧
      GuardedReleaseInvariant seeds s z.1.1.2 (merged seeds z.1.2.1 z.2.cache) ∧
      PadsMatch pads z.1.2.1 := by
  have hj := joint_project P seeds hinj q s pads τ (oa.run st) (hsafe st) bm sh hi z hz
  have ha := compilerProgramPads_support P seeds q s pads _ _ _ hj.1
  have hr : (z.1.1, merged seeds z.1.2.1 z.2.cache) ∈ support
      (runSource P seeds q s oa' st (merged seeds bm.1 sh.cache)) := by
    rw [← hmap]
    exact ha
  exact ⟨hj.2, hpres st _ hg _ hr,
    compilerProgramPads_visible P seeds q s pads _ (merged seeds bm.1 sh.cache) hp
      (z.1.1, merged seeds z.1.2.1 z.2.cache) hj.1⟩

/-- A constant-mark segment retains old bad records or uses that mark. -/
theorem joint_tagFrom {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (τ : CPoint → Digest)
    (oa : OracleComp (SpecX C) α) (ha : Queries Marks.NoMark oa)
    (bm : CappedCompilerState C × Bool) (sh : ShareState C) (z)
    (hz : z ∈ support (Marks.jointRun (lazyHandler τ) P seeds q s pads oa bm sh)) :
    ∀ r, z.2.bad = some r → sh.bad = some r ∨ r.1 = bm.2 := by
  induction oa using OracleComp.inductionOn generalizing bm sh with
  | pure a =>
      simp only [Marks.jointRun, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
      subst z
      exact fun _ h => Or.inl h
  | query_bind t next ih =>
      have hb := (isQueryBound_query_bind_iff ..).mp ha
      rw [Marks.jointRun_bind] at hz
      simp only [mem_support_bind_iff] at hz
      obtain ⟨mid, hm, hz⟩ := hz
      have hm' : mid ∈ support ((simulateQ (lazyHandler τ)
          ((shareBackend P seeds q s pads t).run bm)).run sh) := by
        simpa only [Marks.jointRun, simulateQ_spec_query] using hm
      have hs := Marks.backend_noMark P seeds q s pads t hb.1 bm
      have he := hs.2 mid.1 (Marks.mem_support_of_simulate_run _ _ _ hm')
      intro r hr
      rcases ih mid.1.1 (hb.2 mid.1.1) mid.1.2 mid.2 hz r hr with hold | htag
      · exact Witness.simulate_tagFrom τ _ Witness.lazyFinish bm.2 _ hs.1 sh mid hm' r hold
      · exact Or.inr (htag.trans he)

/-- The share invariant is independent of the source interpreter. -/
theorem joint_shareOK {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (τ : CPoint → Digest)
    (oa : OracleComp (SpecX C) α) (bm : CappedCompilerState C × Bool)
    (sh : ShareState C) (h : Witness.ShareOK τ sh) (z)
    (hz : z ∈ support (Marks.jointRun (lazyHandler τ) P seeds q s pads oa bm sh)) :
    Witness.ShareOK τ z.2 := Witness.simulate_shareOK τ _ sh h z hz

def Bnd (seeds : C.Term → HashOutput) (s : HiddenKey → Digest) (pads : Point → Digest)
    (st : SourceState C) (bm : CappedCompilerState C × Bool) (sh : ShareState C) : Prop :=
  bm.2 = st.hiddenFlag ∧ Inv seeds bm sh ∧
    GuardedReleaseInvariant seeds s st (merged seeds bm.1 sh.cache) ∧
    PadsMatch pads bm.1 ∧ Witness.ShareOK (tau s pads) sh ∧
    (∀ k l, sh.bad = some (false, k, l) → k = .read ∧ l = true)

def FalseSafe {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (oa : SourceMX C α) : Prop :=
  ∀ st bm sh, Bnd seeds s pads st bm sh →
    ∀ z ∈ support (Marks.jointRun (lazyHandler (tau s pads)) P seeds q s pads (oa.run st) bm sh),
      Bnd seeds s pads z.1.1.2 z.1.2 z.2

/-- At a false endpoint Wrong is excluded; at a true endpoint a false tag is old. -/
theorem bnd_of_endpoint (seeds : C.Term → HashOutput) (hinj : Function.Injective seeds)
    (s : HiddenKey → Digest) (pads : Point → Digest) (old sh : ShareState C)
    (st : SourceState C) (bm : CappedCompilerState C × Bool)
    (he : bm.2 = st.hiddenFlag) (hi : Inv seeds bm sh)
    (hg : GuardedReleaseInvariant seeds s st (merged seeds bm.1 sh.cache))
    (hp : PadsMatch pads bm.1) (hs : Witness.ShareOK (tau s pads) sh)
    (hn : ∀ k l, old.bad = some (false, k, l) → k = .read ∧ l = true)
    (ht : ∀ r, sh.bad = some r → old.bad = some r ∨ r.1 = st.hiddenFlag) :
    Bnd seeds s pads st bm sh := by
  refine ⟨he, hi, hg, hp, hs, ?_⟩
  intro k l hb
  cases hf : st.hiddenFlag with
  | false =>
      by_contra hnot
      exact release_noWrong seeds hinj s pads st bm.1 sh (hg.2.2 hf).1 hp
        (hs.2 ⟨false, k, l, hb, hnot⟩)
  | true =>
      rcases ht (false, k, l) hb with hold | htag
      · exact hn k l hold
      · simp [hf] at htag

/-- Non-mark source queries retain the mark independently of existing bad tags. -/
theorem joint_mark_eq {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) (τ : CPoint → Digest)
    (oa : OracleComp (SpecX C) α) (ha : Queries Marks.NoMark oa)
    (bm : CappedCompilerState C × Bool) (sh : ShareState C) (z)
    (hz : z ∈ support (Marks.jointRun (lazyHandler τ) P seeds q s pads oa bm sh)) :
    z.1.2.2 = bm.2 := by
  induction oa using OracleComp.inductionOn generalizing bm sh with
  | pure a =>
      simp only [Marks.jointRun, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
      subst z
      rfl
  | query_bind t next ih =>
      have hb := (isQueryBound_query_bind_iff ..).mp ha
      rw [Marks.jointRun_bind] at hz
      simp only [mem_support_bind_iff] at hz
      obtain ⟨mid, hm, hz⟩ := hz
      have hm' : mid ∈ support ((simulateQ (lazyHandler τ)
          ((shareBackend P seeds q s pads t).run bm)).run sh) := by
        simpa only [Marks.jointRun, simulateQ_spec_query] using hm
      have he := (Marks.backend_noMark P seeds q s pads t hb.1 bm).2 mid.1
        (Marks.mem_support_of_simulate_run _ _ _ hm')
      exact (ih mid.1.1 (hb.2 mid.1.1) mid.1.2 mid.2 hz).trans he

/-- Quiet actual-source segments preserve the full boundary invariant. -/
theorem falseSafe_quiet {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (hinj : Function.Injective seeds) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (oa : SourceMX C α) (oa' : SourceM C α) (hmap : mapX seeds oa = oa')
    (hsafe : Safe oa) (hquiet : Marks.Quiet oa)
    (hpres : SourcePreserves P seeds q s (GuardedReleaseInvariant seeds s) oa') :
    FalseSafe P seeds q s pads oa := by
  intro st bm sh h z hz
  rcases h with ⟨he, hi, hg, hp, hs, hn⟩
  have hseg := segment_guarded P seeds hinj q s pads (tau s pads) oa oa' hmap hsafe hpres
    st bm sh hi hg hp z hz
  have hquiet' := hquiet.at st
  have hsource := Marks.joint_support _ _ _ _ _ _ _ _ _ z hz
  have hf := hquiet'.2 z.1.1 hsource
  have hmarks := joint_mark_eq P seeds q s pads (tau s pads) _ hquiet'.1 bm sh z hz
  apply bnd_of_endpoint seeds hinj s pads sh z.2 z.1.1.2 z.1.2
    (hmarks.trans (he.trans hf.symm)) hseg.1 hseg.2.1 hseg.2.2
    (joint_shareOK P seeds q s pads (tau s pads) _ bm sh hs z hz) hn
  intro r hr
  rcases joint_tagFrom P seeds q s pads (tau s pads) _ hquiet'.1 bm sh z hz r hr with hold | htag
  · exact Or.inl hold
  · exact Or.inr (htag.trans (he.trans hf.symm))

/-- The whole oracle transports release slack; its marked remainder classifies
new bad tags without assuming the intermediate mark already equals the flag. -/
theorem falseSafe_oracle (prims : Primitives) (x : Keys3 C) (hinj : Function.Injective x.2.1)
    (top : TopTree) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : (LocalSpec C + TsigSpec C).Domain) :
    FalseSafe x.1 x.2.1 q s pads (sourceOraclesX prims x top t) := by
  intro st bm sh h z hz
  rcases h with ⟨he, hi, hg, hp, hs, hn⟩
  have hseg := segment_guarded x.1 x.2.1 hinj q s pads (tau s pads)
    _ _ (mapX_sourceOracles prims x top t) (safe_sourceOraclesX prims x top t)
    (sourceOracles_guardedRelease prims x hinj top q s t) st bm sh hi hg hp z hz
  have hshares := joint_shareOK x.1 x.2.1 q s pads (tau s pads) _ bm sh hs z hz
  rw [Marks.sourceOraclesX_marked, Marks.jointRun_bind, Marks.joint_mark] at hz
  simp only [pure_bind] at hz
  have hnm := Marks.callRest_noMark prims x top st t
  have hf := Marks.callRest_flag prims x top st t z.1.1
    (Marks.joint_support _ _ _ _ _ _ _ _ _ z hz)
  have hm := joint_mark_eq x.1 x.2.1 q s pads (tau s pads) _ hnm
    (bm.1, Marks.callMark x st t) sh z hz
  apply bnd_of_endpoint x.2.1 hinj s pads sh z.2 z.1.1.2 z.1.2
    (hm.trans hf.symm) hseg.1 hseg.2.1 hseg.2.2 hshares hn
  intro r hr
  rcases joint_tagFrom x.1 x.2.1 q s pads (tau s pads) _ hnm
    (bm.1, Marks.callMark x st t) sh z hz r hr with hold | htag
  · exact Or.inl hold
  · exact Or.inr (htag.trans hf.symm)

namespace FalseSafe
variable {α β : Type} {P : PublicParameter} {seeds : C.Term → HashOutput}
variable {q : ℕ} {s : HiddenKey → Digest} {pads : Point → Digest}

theorem pure (a : α) : FalseSafe P seeds q s pads (pure a) := by
  intro st bm sh h z hz
  simp only [StateT.run_pure, Marks.jointRun, simulateQ_pure, mem_support_pure_iff] at hz
  subst z
  exact h

theorem bind {oa : SourceMX C α} {f : α → SourceMX C β}
    (h : FalseSafe P seeds q s pads oa) (hf : ∀ a, FalseSafe P seeds q s pads (f a)) :
    FalseSafe P seeds q s pads (oa >>= f) := by
  intro st bm sh hst z hz
  rw [StateT.run_bind, Marks.jointRun_bind] at hz
  simp only [mem_support_bind_iff] at hz
  obtain ⟨mid, hm, hz⟩ := hz
  exact hf mid.1.1.1 mid.1.1.2 mid.1.2 mid.2 (h st bm sh hst mid hm) z hz

theorem map (f : α → β) {oa : SourceMX C α} (h : FalseSafe P seeds q s pads oa) :
    FalseSafe P seeds q s pads (f <$> oa) := by
  simpa only [bind_pure_comp] using h.bind (fun a => pure (f a))

theorem simulate {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (SourceMX C)) (oa : OracleComp spec α)
    (h : ∀ t, FalseSafe P seeds q s pads (impl t)) :
    FalseSafe P seeds q s pads (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [simulateQ_pure] using pure (P := P) (seeds := seeds) (q := q) (s := s) (pads := pads) a
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact (h t).bind ih

theorem get_mark (f : SourceState C → SourceMX C α)
    (hf : ∀ st, FalseSafe P seeds q s pads (f st)) :
    FalseSafe P seeds q s pads (do
      let st ← get
      let _ ← liftM (markQ (C := C) st.hiddenFlag)
      f st) := by
  intro st bm sh h z hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  change z ∈ support (Marks.jointRun (lazyHandler (tau s pads)) P seeds q s pads
    (markQ st.hiddenFlag >>= fun _ => (f st).run st) bm sh) at hz
  rw [Marks.jointRun_bind, Marks.joint_mark] at hz
  simp only [pure_bind] at hz
  have hb : (bm.1, st.hiddenFlag) = bm := by rw [← h.1]
  rw [hb] at hz
  exact hf st st bm sh h z hz
end FalseSafe

attribute [local irreducible] FalseSafe Queries Safe Marks.Quiet
attribute [local irreducible] sourceProgramX sourceProgram sourceGameX sourceGame

set_option maxRecDepth 100000 in
/-- Setup uses A100's control-preserving guarded release theorem. -/
theorem falseSafe_top (x : Keys3 C) (hinj : Function.Injective x.2.1)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    FalseSafe x.1 x.2.1 q s pads (sourceTopTreeX x.1 x.2.1) :=
  falseSafe_quiet x.1 x.2.1 hinj q s pads (sourceTopTreeX x.1 x.2.1) (sourceTopTree x.1 x.2.1) (mapX_sourceTopTree x.1 x.2.1)
    (safe_sourceTopTreeX x.1 x.2.1) (Marks.quiet_sourceTopTreeX x.1 x.2.1)
    (sourceControl_guardedRelease x.1 x.2.1 q s _ (sourceControl_sourceTopTree x.1 x.2.1)
      (sourceTopTree_releaseInvariant x.1 x.2.1 hinj q s))

/-- Verification retains the actual candidate log and guarded release state. -/
theorem falseSafe_verify (x : Keys3 C) (hinj : Function.Injective x.2.1)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (st : SourceState C) (input : HashInput) :
    FalseSafe x.1 x.2.1 q s pads (do
      let value ← sourceHashX x.1 x.2.1 (.hash input)
      modify fun (state : SourceState C) => { state with candidates := state.candidates ++ SigningGuessLinkProof.callCandidates x.1 st.signing st.exposed input }
      pure value : SourceMX C HashOutput) := by
  apply falseSafe_quiet x.1 x.2.1 hinj q s pads _
    (do
      let value ← sourceHash x.1 x.2.1 (.hash input)
      modify fun (state : SourceState C) => { state with candidates := state.candidates ++ SigningGuessLinkProof.callCandidates x.1 st.signing st.exposed input }
      pure value)
  · simp only [mapX_bind, mapX_sourceHash, mapX_modify, mapX_pure]
  · exact (safe_sourceHashX x.1 x.2.1 (.hash input)).bind fun value =>
      (Safe.modify _).bind fun _ => Safe.pure value
  · exact Marks.quiet_verify x.1 x.2.1 st input
  · refine (sourceControl_guardedRelease x.1 x.2.1 q s _ (sourceControl_sourceHash x.1 x.2.1 (.hash input))
      (sourceHash_releaseInvariant x.1 x.2.1 hinj q s (.hash input) (fun _ _ he => by cases he))).bind _ fun value => ?_
    exact (sourceModify_guardedRelease x.1 x.2.1 q s
      (fun source => { source with candidates := source.candidates ++ SigningGuessLinkProof.callCandidates x.1 st.signing st.exposed input })
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).bind _ (fun _ => SourcePreserves.pure value)

set_option maxRecDepth 100000 in
theorem falseSafe_honest (prims : Primitives) (x : Keys3 C) (hinj : Function.Injective x.2.1)
    (top : TopTree) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (e : KeyIndex) (message : Message) :
    FalseSafe x.1 x.2.1 q s pads (sourceHonestSignatureX prims x top e message) :=
  falseSafe_quiet x.1 x.2.1 hinj q s pads
    (sourceHonestSignatureX prims x top e message) (sourceHonestSignature prims x top e message)
    (mapX_sourceHonestSignature prims x top e message)
    (safe_sourceHonestSignatureX prims x top e message) (Marks.quiet_sourceHonestSignatureX prims x top e message)
    (sourceControl_guardedRelease x.1 x.2.1 q s _
      (sourceControl_sourceHonestSignature prims x top e message)
      (sourceHonestSignature_releaseInvariant prims x hinj top q s e message))


/-- Every actual adaptive source-game boundary retains the lazy no-false witness. -/
theorem sourceGameX_falseSafe (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    FalseSafe x.1 x.2.1 q s pads (sourceGameX prims A x) := by
  unfold sourceGameX
  apply FalseSafe.get_mark
  intro initial
  apply FalseSafe.bind (falseSafe_top x hinj q s pads)
  intro top
  apply FalseSafe.bind (FalseSafe.simulate _ _ (falseSafe_oracle prims x hinj top q s pads))
  intro forgery
  apply FalseSafe.get_mark
  intro st
  apply FalseSafe.bind (FalseSafe.simulate _ _ (falseSafe_verify x hinj q s pads st))
  intro verified
  split <;> simp only [pure_bind]
  · exact FalseSafe.pure _
  · exact (falseSafe_honest prims x hinj top q s pads _ _).bind fun _ => FalseSafe.pure _

/-- The empty source, compiler and share table satisfy the boundary invariant. -/
theorem bnd_initial (seeds : C.Term → HashOutput) (s : HiddenKey → Digest)
    (pads : Point → Digest) :
    Bnd seeds s pads sourceInit (((compilerInit, 0), fun _ => none, false), false)
      (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool)) := by
  refine ⟨rfl, ?_, ?_, ?_, Witness.shareOK_init _, ?_⟩
  · constructor
    · intro query z hz
      rfl
    · simp [DoneCached, SigningShareLazy.init]
  · simpa only [merged_init] using guardedReleaseInvariant_initial seeds s
  · intro p v hp
    cases hp
  · intro k l hb
    cases hb

/-- A supported tag-false first bad can only be a lucky read. -/
theorem lazyRun_noFalse (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (z : CompilerOutcome C × ShareState C)
    (hz : z ∈ support (Table.lazyRun prims A x q s pads (tau s pads)))
    (k : SigningShareLazy.Kind) (l : Bool) (hb : z.2.bad = some (false, k, l)) :
    k = .read ∧ l = true := by
  simp only [Table.lazyRun, shareRun, simulateQ_bind, StateT.run_bind,
    lazy_view_run, pure_bind, simulateQ_pure, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  have hs := sourceGameX_falseSafe prims A x hinj q s pads
  unfold FalseSafe at hs
  have h := hs sourceInit (((compilerInit, 0), fun _ => none, false), false)
    SigningShareLazy.init (bnd_initial x.2.1 s pads) r
    (by simpa only [Marks.jointRun, sourceProgramX] using hr)
  exact h.2.2.2.2.2 k l hb

/-- The lazy support witness excludes every non-lucky tag-false record. -/
theorem lazyRun_nonLucky_zero (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (k : SigningShareLazy.Kind) (l : Bool) (hnot : ¬(k = .read ∧ l = true)) :
    Pr[fun z => z.2.bad = some (false, k, l) |
      Table.lazyRun prims A x q s pads (tau s pads)] = 0 :=
  probEvent_eq_zero_iff.mpr fun z hz hb => hnot (lazyRun_noFalse prims A x hinj q s pads z hz k l hb)

/-- Lucky false-tag reads have zero probability by the original lazy ratio. -/
theorem lazyRun_luckyFalse_zero (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest) :
    Pr[fun z => z.2.bad = some (false, .read, true) |
      Table.lazyRun prims A x q s pads (tau s pads)] = 0 := by
  have hr := SigningShareLazy.lazy_lucky_ratio C.terms terms_nodup mem_terms
    (tau s pads) (shareRun prims A x q s pads)
    (SigningShareLazy.init (B := SigningShareLazy.ImplBad Bool)) rfl false
  change Pr[fun z => z.2.bad = some (false, .read, false) |
      Table.lazyRun prims A x q s pads (tau s pads)] =
    (Fintype.card SigningShareLazy.Digest - 1 : ℕ) *
      Pr[fun z => z.2.bad = some (false, .read, true) |
        Table.lazyRun prims A x q s pads (tau s pads)] at hr
  rw [lazyRun_nonLucky_zero prims A x hinj q s pads .read false (by simp)] at hr
  have hn : ((Fintype.card SigningShareLazy.Digest - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    have hc : Fintype.card SigningShareLazy.Digest = 2 ^ 128 := by
      change Fintype.card (BitVec 128) = 2 ^ 128
      exact card_bitVec 128
    rw [hc]
    norm_num
  exact (mul_eq_zero.mp hr.symm).resolve_left hn

/-- Erasing lucky retains zero probability for every false-tag first-bad kind. -/
theorem lazyRun_falseBad_zero (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hinj : Function.Injective x.2.1) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (k : SigningShareLazy.Kind) :
    Pr[fun z => (SigningShareLazy.erase z.2).bad = some (false, k) |
      Table.lazyRun prims A x q s pads (tau s pads)] = 0 := by
  apply probEvent_eq_zero_iff.mpr
  intro z hz hb
  have hbad : ∃ l, z.2.bad = some (false, k, l) := by
    simp only [SigningShareLazy.erase, Option.map_eq_some_iff] at hb
    obtain ⟨⟨g, kind, l⟩, he, hval⟩ := hb
    cases hval
    exact ⟨l, he⟩
  obtain ⟨l, hl⟩ := hbad
  have hshape := lazyRun_noFalse prims A x hinj q s pads z hz k l hl
  rcases hshape with ⟨rfl, rfl⟩
  exact (probEvent_eq_zero_iff.mp (lazyRun_luckyFalse_zero prims A x hinj q s pads)) z hz hl

end ThresholdLeanXmssSecurity.SigningCompilerShare.NoFalse

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.NoFalse.release_noWrong' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.NoFalse.release_noWrong

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.NoFalse.sourceGameX_falseSafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.NoFalse.sourceGameX_falseSafe

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerShare.NoFalse.lazyRun_falseBad_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerShare.NoFalse.lazyRun_falseBad_zero
