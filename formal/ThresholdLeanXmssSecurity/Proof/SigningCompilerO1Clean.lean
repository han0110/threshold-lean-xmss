import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Events
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Cap
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Guarded
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1RealLog
import ThresholdLeanXmssSecurity.Proof.SigningCompilerPotential
import ThresholdLeanXmssSecurity.Proof.SigningLaneFinal
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Final

/-! # The clean O1 compiler coupling

`compilerCouplingClean` couples the real trace run and the O1 compiler run for each cap `q`. Its
right event also states that the final backend has no second opening of a commitment.

- `final_clean` states that at the end of two runs that did not stop, a real run with the flag down
  and with no charged event gives a compiler backend with no second opening. A second opening on the
  backend moves to the visible cache. At an unrevealed term, `prfSeen` makes the randomizer point
  constrained, so the cached randomizer is the secret, and the pending commitment answer is the
  canonical commitment hash. This gives `AlternativeCommitment` on the log cache.
- `real_le_table_clean` is `real_le_table` with the clean event.
- `tableRunCO1_le_clean` bounds the table run by the clean event of the pad run.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Clean
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Tables SigningCompilerO1Runs
open SigningCompilerO1Share SigningCompilerO1Guarded SigningCompilerO1Cap
open SigningCompilerO1Tail SigningCompilerO1Events
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigningCompilerShare.route MonadAttach.support

/-- A second opening of a commitment in the backend. A cached commitment input at a value other than
the cached randomizer of its key has the low half of the pending commitment answer of the key. -/
def SecondOpening (P : PublicParameter) (seeds : C.Term → HashOutput) (data : DeferredState C) :
    Prop :=
  ∃ (e : KeyIndex) (ρ : Digest) (v : HashOutput) (c : DeferredOutput),
    data.cache (.hash (commitmentInput P e ρ)) = some v ∧
    data.pending (.commitment e) = some c ∧ c.low = .known (truncateHash v) ∧
    SigningGuessProof.RandomizerCached seeds data.cache e ∧
    ρ ≠ SigningGuessProof.cachedRandomizer seeds data.cache e

/-- The event of the compiler run that the leaf bounds. With the hidden-key flag down it is the cap
flag or the lane 2 event with a final backend that has no second opening. With the flag up it is the
cap flag alone. -/
def CleanCompilerEvent (x : Keys3 C) (q : ℕ) (r : CompilerOutcomeO1 C) : Prop :=
  (r.1.2.base.hiddenFlag = false ∧ (r.2.2.2 = true ∨
      (compilerEvent x.1 q r.2.1 ∧ ¬SecondOpening x.1 x.2.1 r.2.1.1.data))) ∨
    (r.1.2.base.hiddenFlag = true ∧ r.2.2.2 = true)

/-- The O1 coupling for each cap, with the clean event on the right side. The real event
holds `NotChargedLogged`, which excludes a second opening of a commitment. -/
def CompilerCouplingClean (prims : Primitives) : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    Pr{let z ←
      SigningLaneUnionProof.traceRun prims A x}[(SigningLaneUnionProof.NoFlag (SigningLaneUnionProof.observed z) ∧
      SigningLaneUnionProof.NotChargedLogged prims x (SigningLaneUnionProof.observed z) ∧
      (SigningLaneUnionProof.LoggedInputHit prims x (SigningLaneUnionProof.observed z) ∨
        SigningLaneUnionProof.StaleBaseAt z ∨ SigningLaneUnionProof.GhostAt x z)) ∧
      (SigningLaneUnionProof.observed z).2.1 ≤ q] ≤
        Pr{let z ← compilerRunO1 prims A x q}[CleanCompilerEvent x q z]

/-- The good event of the compiler outcome with no second opening, with the hidden-key flag down. -/
def CleanGood (x : Keys3 C) (q : ℕ) (o : CompilerOutcomeO1 C) : Prop :=
  o.1.2.base.hiddenFlag = false ∧
    (o.2.2.2 = true ∨ (compilerEvent x.1 q o.2.1 ∧ ¬SecondOpening x.1 x.2.1 o.2.1.1.data))

/-- An `Option` traversal with an output at each element is the map of the outputs. -/
theorem mapM_eq_some_map {α β : Type} (f : α → Option β) (g : α → β) (h : ∀ a, f a = some (g a)) :
    ∀ l : List α, l.mapM f = some (l.map g)
  | [] => rfl
  | a :: l => by
    rw [List.mapM_cons, h a, mapM_eq_some_map f g h l]
    rfl

/-- With each term cached, the opening of a bottom key is the cached randomizer. -/
theorem cachedOpening_eq_cachedRandomizer (x : Keys3 C) (cache : HashCache C) (e : KeyIndex)
    (hc : SigningGuessProof.RandomizerCached x.2.1 cache e) :
    cachedOpening x cache (bottomLayer, e) =
      some (SigningGuessProof.cachedRandomizer x.2.1 cache e) := by
  unfold cachedOpening
  rw [mapM_eq_some_map _ (fun T => truncateHash
    ((cache (.prf (x.2.1 T) (.randomizer bottomLayer e))).getD 0)) (fun T => by
      obtain ⟨w, hw⟩ := hc T
      simp [hw])]
  rfl

section Final
variable (prims : Primitives) (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
  (noise : ChainNoiseIndex → HashOutput)

set_option linter.unusedVariables false in
/-- At the end of two runs that did not stop, a real run with the flag down and with no charged
event gives a compiler backend with no second opening. -/
theorem final_clean (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (z : RealFinal C) (c : CompFinal C)
    (hf : FinalFacts prims x s pads u rest noise z c) (hstop : ¬Stop c.2)
    (hflag : SigningLaneUnionProof.NoFlag (SigningLaneUnionProof.observed z.1))
    (hnc : SigningLaneUnionProof.NotChargedLogged prims x (SigningLaneUnionProof.observed z.1)) :
    ¬SecondOpening x.1 x.2.1 (SigningCompilerShareTables.finish x.2.1 c).1.2.1.1.data := by
  rintro ⟨e, ρ, v, cc, hv, hp, hlow, hrc, hne⟩
  change (dataOf x c.2).cache _ = some v at hv
  change (dataOf x c.2).pending _ = some cc at hp
  change SigningGuessProof.RandomizerCached x.2.1 (dataOf x c.2).cache e at hrc
  change ρ ≠ SigningGuessProof.cachedRandomizer x.2.1 (dataOf x c.2).cache e at hne
  obtain ⟨vlog, win, hz, ⟨⟨hfields, hcache⟩, -⟩, -, rev, -, hextra⟩ := hf
  have hle : (dataOf x c.2).cache ≤ visibleOf (realEnd z) := by
    have hdata : dataOf x ((c.1.2, c.2).1.base, (c.1.2, c.2).2).2 = dataOf x c.2 := rfl
    have hvis : visibleOf (withCandidates (realEnd z) ((realEnd z).1.2.2.2 ++ vlog)) =
        visibleOf (realEnd z) := rfl
    have h := hcache.cache_le
    rw [hdata, hvis] at h
    exact h
  have hrf : realFlag (realEnd z) = false := by
    have h1 := congrArg (fun w => w.1.1.2) hz
    exact h1.symm.trans hflag
  have hsecret : SigningGuessProof.cachedRandomizer x.2.1 (dataOf x c.2).cache e =
      s (.opening bottomLayer e) := by
    obtain ⟨T, hT⟩ := exists_lacked_term _ hextra.corruptBound
    obtain ⟨w, hw⟩ := hrc T
    have hcon : Constrained (.randomizer bottomLayer e) := by
      have hseen : visibleOf (realEnd z) (.prf (x.2.1 T) (.randomizer bottomLayer e)) ≠ none := by
        rw [hle hw]
        exact Option.some_ne_none w
      rcases hextra.prfSeen hrf T _ hseen with h | h
      · exact absurd h hT
      · exact h
    exact cachedOpening_constrained x s pads u rest noise hkeys _ _ _ hfields.realPrivate hle
      bottomLayer e hcon _ (cachedOpening_eq_cachedRandomizer x _ e hrc)
  have hrcVis : SigningGuessProof.RandomizerCached x.2.1 (visibleOf (realEnd z)) e := fun T => by
    obtain ⟨w, hw⟩ := hrc T
    exact ⟨w, hle hw⟩
  have hstable := SigningGuessProof.cachedRandomizer_stable x.2.1 _ _ e hle hrc
  have hcanon : visibleOf (realEnd z) (.hash (commitmentInput x.1 e (s (.opening bottomLayer e)))) =
      some (cc.interpret s) :=
    hcache.pending (.commitment e) cc hp
  have htrunc : truncateHash v = truncateHash (cc.interpret s) := by
    rw [SigningCompilerO1Lemmas.truncateHash_interpret, hlow]
    rfl
  have halt : SigningGuessProof.AlternativeCommitment x.2.1 x.1 (visibleOf (realEnd z)) := by
    refine ⟨e, ρ, cc.interpret s, v, hrcVis, ?_, hle hv, ?_, htrunc⟩
    · rw [← hstable, hsecret]
      exact hcanon
    · rw [← hstable]
      exact hne
  have hlog := (SigningPartnerCompareProof.alternativeCommitment_congr_of_outside x.2.1 x.1
    hextra.logAgreement.2).mp halt
  exact hnc (Or.inr (Or.inl hlog))

set_option maxRecDepth 100000 in
/-- For fixed tables, the real event with a count of at most `q` costs at most the clean compiler
event, an early cap with the flag up, or a share failure with a false tag. A changed copy of
`SigningCompilerO1Final.real_le_table`. -/
theorem real_le_table_clean (A : TsigAdversary C) (q : ℕ)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) :
    Pr{let z ←
        realRun prims A x s pads (gOf s pads u) rest noise}[RealEvent prims x z ∧ (SigningLaneUnionProof.observed z).2.1 ≤ q] ≤
      Pr{let z ←
        eagerRunTagTO1 prims A x q s pads (NoFalse.tau s pads) (gOf s pads u) noise rest}[CleanGood x q z.1 ∨ (z.1.1.2.base.hiddenFlag = true ∧ CapEarlyO1 z) ∨
          NullBad z.2] := by
  have hreal : realRun prims A x s pads (gOf s pads u) rest noise =
      Prod.fst <$> realRunRaw prims A x s pads (gOf s pads u) rest noise := rfl
  have hcomp : eagerRunTagTO1 prims A x q s pads (NoFalse.tau s pads) (gOf s pads u) noise rest =
      SigningCompilerShareTables.finish x.2.1 <$>
        (simulateQ (compBackend x q s pads u rest noise) (sourceProgramO1X prims A x)).run
          SigningCompilerShareTables.initial := rfl
  calc _ = Pr{let z ← realRun prims A x s pads (gOf s pads u) rest noise}[(RealEvent prims x z ∧ (SigningLaneUnionProof.observed z).2.1 ≤ q) ∧
          z.1.1.1.2 = z.2.2.1.2] :=
        prEvent_congr_of_support _ _ _ (fun z hz =>
          ⟨fun h => ⟨h, SigningCompilerO1Final.realRun_flag prims A x s pads hkeys u rest noise z hz⟩,
            And.left⟩)
    _ ≤ _ := by
      rw [hreal, hcomp, prEvent_map, prEvent_map]
      refine prEvent_le_of_relTriple
        (SigningCompilerO1Coupled.run_coupled prims x q s pads u rest noise A hkeys) ?_
      rintro z c hrel ⟨⟨hE, hq⟩, hfl⟩
      by_cases hstop : Stop c.2
      · rcases hstop with hnull | ⟨hcap, hbad⟩
        · exact Or.inr (Or.inr hnull)
        · cases hh : c.1.2.base.hiddenFlag
          · exact Or.inl ⟨hh, Or.inl hcap⟩
          · refine Or.inr (Or.inl ⟨hh, ?_⟩)
            rcases hbad with hb | hb
            · exact Or.inl ⟨hb, hcap⟩
            · exact Or.inr hb
      · rcases hrel with hstopReal | hstopComp | ⟨source, wrapper, hf⟩
        · rcases hstopReal with hflag | hcount
          · have h1 : (false : Bool) = true :=
              (hE.1 : z.1.1.1.1.2 = false).symm.trans (hfl.trans hflag)
            exact absurd h1 (by decide)
          · exact absurd hq (not_le.mpr hcount)
        · exact absurd hstopComp hstop
        · have hgood := (compGood_withReveal x q c source wrapper).mp
            (final_event prims x q s pads u rest noise hkeys z _ hf hstop hE hq)
          have hclean := final_clean prims x s pads u rest noise hkeys z _ hf hstop hE.1 hE.2.1
          exact Or.inl ⟨hgood.1, hgood.2.imp_right fun h => ⟨h, hclean⟩⟩

end Final

/-- A pointwise bound of two continuations bounds the two binds. -/
private theorem probEvent_bind_le_bind {α β γ : Type} (oa : ProbComp α) (f : α → ProbComp β)
    (g : α → ProbComp γ) (P : β → Prop) (Q : γ → Prop) (h : ∀ a, Pr{let z ← f a}[P z] ≤ Pr{let z ← g a}[Q z]) :
    Pr{let z ← oa >>= f}[P z] ≤ Pr{let z ← oa >>= g}[Q z] := by
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  exact tsum_le_tsum fun a => mul_le_mul' le_rfl (h a)

/-- For fixed hidden labels and pads, the right event of `real_le_table_clean` over the table run
costs at most the clean event of the pad run. -/
theorem tableRunCO1_le_clean (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C) (q : ℕ)
    (s : HiddenKey → Digest) (pads : Point → Digest) (hinj : Function.Injective x.2.1) :
    Pr{let z ←
        tableRunCO1 prims A x q s pads (NoFalse.tau s pads)}[CleanGood x q z.1 ∨ (z.1.1.2.base.hiddenFlag = true ∧ CapEarlyO1 z) ∨ NullBad z.2] ≤
      Pr{let z ← compilerRunPadsO1 prims A x q s pads}[CleanCompilerEvent x q z] := by
  let t := tableRunCO1 prims A x q s pads (NoFalse.tau s pads)
  let p := compilerRunPadsO1 prims A x q s pads
  let E : CompilerOutcomeO1 C → Prop := fun o => o.2.2.2 = true ∨
    (compilerEvent x.1 q o.2.1 ∧ ¬SecondOpening x.1 x.2.1 o.2.1.1.data)
  have hgood : Pr{let z ← t}[CleanGood x q z.1] =
      Pr{let o ← p}[E o ∧ o.1.2.base.hiddenFlag = false] := by
    rw [compilerRunPadsO1_hidden_eq_table prims A x q s pads hinj E]
    exact prEvent_congr_of_support _ _ _ fun z _ => And.comm
  have hnull : Pr{let z ← t}[NullBad z.2] = 0 :=
    tableRunCO1_falseTag_zero prims A x q s pads hinj
  have hguard : Pr{let z ← p}[CleanCompilerEvent x q z] =
      Pr{let o ← p}[E o ∧ o.1.2.base.hiddenFlag = false] +
        Pr{let o ← p}[o.1.2.base.hiddenFlag = true ∧ o.2.2.2 = true] := by
    rw [← SigningCompilerO1Cap.probEvent_or_eq]
    · exact prEvent_congr_of_support _ _ _ fun o _ => by
        simp only [CleanCompilerEvent, E, and_comm]
    · intro o h1 h2
      rw [h1.2] at h2
      exact Bool.false_ne_true h2.1
  calc _ ≤ Pr{let z ← t}[CleanGood x q z.1] +
        Pr{let z ← t}[(z.1.1.2.base.hiddenFlag = true ∧ CapEarlyO1 z) ∨ NullBad z.2] :=
          prEvent_or_le _ _ _
    _ ≤ Pr{let z ← t}[CleanGood x q z.1] +
        (Pr{let z ← t}[z.1.1.2.base.hiddenFlag = true ∧ CapEarlyO1 z] +
          Pr{let z ← t}[NullBad z.2]) := add_le_add le_rfl (prEvent_or_le _ _ _)
    _ ≤ _ := by
      rw [hgood, hnull, add_zero, hguard]
      exact add_le_add le_rfl (tableRunCO1_capEarly_le prims A x q s pads hinj)

/-- The clean coupling. -/
theorem compilerCouplingClean (prims : Primitives) : CompilerCouplingClean (C := C) prims := by
  intro A q x _ hkeys
  have hinj : Function.Injective x.2.1 := not_not.mp (not_or.mp hkeys).1
  rw [(traceRun_eq_realRun prims A x hkeys).prEvent_eq,
    (compilerRunO1_eq_padTable prims A x q).prEvent_eq]
  refine probEvent_bind_le_bind _ _ _ _ _ fun s => ?_
  refine probEvent_bind_le_bind _ _ _ _ _ fun pads => ?_
  refine le_trans ?_ (tableRunCO1_le_clean prims A x q s pads hinj)
  rw [(tableRunCO1_eq_tables prims A x q s pads hkeys _).prEvent_eq]
  refine probEvent_bind_le_bind _ _ _ _ _ fun u => ?_
  refine le_of_le_of_eq ?_ ((OracleComp.EvalDistEq.bind_bind_swap ($ᵗ (RestSlot C → HashOutput))
    ($ᵗ (ChainNoiseIndex → HashOutput)) (fun rest noise =>
      eagerRunTagTO1 prims A x q s pads (NoFalse.tau s pads) (gOf s pads u) noise rest)).prEvent_eq _)
  refine probEvent_bind_le_bind _ _ _ _ _ fun rest => ?_
  refine probEvent_bind_le_bind _ _ _ _ _ fun noise => ?_
  exact real_le_table_clean prims x s pads u rest noise A q hkeys

end ThresholdLeanXmssSecurity.SigningCompilerO1Clean

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Clean.mapM_eq_some_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Clean.mapM_eq_some_map

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Clean.cachedOpening_eq_cachedRandomizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Clean.cachedOpening_eq_cachedRandomizer

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Clean.final_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Clean.final_clean

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Clean.real_le_table_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Clean.real_le_table_clean

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Clean.tableRunCO1_le_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Clean.tableRunCO1_le_clean

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Clean.compilerCouplingClean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Clean.compilerCouplingClean
