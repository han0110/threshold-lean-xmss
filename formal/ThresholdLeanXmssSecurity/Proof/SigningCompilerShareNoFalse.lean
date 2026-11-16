import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareWitness
import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareTable

/-! # Guarded release targets of the lazy constrained-share compiler

The fixed target table uses the private pad table. Visible pads identify
those fixed entries at the original source's stable release boundaries.
-/
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal
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

attribute [local irreducible] Queries Safe Marks.Quiet
attribute [local irreducible] sourceProgramX sourceProgram sourceGameX sourceGame

end ThresholdLeanXmssSecurity.SigningCompilerShare.NoFalse
