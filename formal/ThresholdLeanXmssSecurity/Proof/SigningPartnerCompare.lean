import ThresholdLeanXmssSecurity.Proof.SigningPartnerTransfer

/-!
The cache comparison left by A26.

The extra eager calls only query bottom message inputs. On actual split-run
support, every logged answer survives in the eager cache, and every tracked
input outside that domain agrees exactly with the log cache. In particular,
the PRF answers, cached randomizers and commitment-collision event agree.

These structural facts do not assert that the selected pair is unchanged:
an extra answer can make an earlier, previously absent trial decode. The full
`PartnerCacheComparison` remains open; no counterexample to its probability
inequality has been established.

`splitRun_partner_of_selected_eq` transports the original lazy row to the
original eager event under explicit equality of the two selected pairs.
This equality is not asserted on all support points. The separate failures
of the R1 link and the global cached-selection flag do not supply it, and
do not by themselves refute the probability comparison.
-/

open OracleComp OracleSpec
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace SigningPartnerCompareProof

open LeanXmss ThresholdLeanXmss SigningCacheLogProof SigningFlatProof
open SigningFlatEagerProof SigningHitLaneProof SigningAssemblyProof

variable {C : Committee} (prims : Primitives)

attribute [local instance] Classical.propDecidable

/-- Tracked inputs outside the domain sampled by the eager grind. -/
def OutsideTrials (P : PublicParameter) (q : Query C) : Prop :=
  Tracked q ∧ ∀ e payload, q ≠ .hash (tweakableHashInput P (.message bottomLayer e) payload)

theorem outsideTrials_prf (P : PublicParameter) (seed : HashOutput) (point : Point) :
    OutsideTrials P (.prf seed point : Query C) :=
  ⟨tracked_prf _ _, fun _ _ h => by cases h⟩

theorem outsideTrials_commitment (P : PublicParameter) (e : KeyIndex) (ρ : Digest) :
    OutsideTrials P (.hash (commitmentInput P e ρ) : Query C) := by
  refine ⟨tracked_hash _, fun e' payload h => ?_⟩
  exact SigningGuessProof.commitmentInput_ne_tweakableHashInput P P e ρ
    (.message bottomLayer e') payload (Query.hash.inj h)

/-- Logged answers survive; extra answers occur only at bottom message inputs. -/
def LogAgreement (P : PublicParameter) (s : LoggedState C) : Prop :=
  logCache s.2 ≤ s.1.1 ∧ ∀ q, OutsideTrials P q → s.1.1 q = logCache s.2 q

theorem logAgreement_hash (P : PublicParameter) (q : Query C) (s : LoggedState C)
    (hs : LogAgreement P s) (w : HashOutput × HashCache C)
    (hw : w ∈ support (((Query C →ₒ HashOutput).randomOracle q).run s.1.1))
    (log : QueryLog (WorldSpec C))
    (hlog : ∀ q', logCache log q' = (logCache s.2 q').or
      (if q = q' then some w.1 else none)) (n : ℕ) :
    LogAgreement P ((w.2, n), log) := by
  obtain ⟨hle, hself, hother⟩ := randomOracle_support q s.1.1 w hw
  constructor
  · intro q' output h
    change w.2 q' = some output
    rw [hlog q'] at h
    cases hc : logCache s.2 q' with
    | some a =>
      simp only [hc, Option.or, Option.some.injEq] at h
      subst a
      exact hle (hs.1 hc)
    | none =>
      simp only [hc, Option.or] at h
      split_ifs at h with he
      · subst q'
        simpa only [Option.some.injEq] using hself.trans h
  · intro q' hq'
    change w.2 q' = logCache log q'
    rw [hlog q', ← hs.2 q' hq']
    by_cases he : q = q'
    · subst q'
      rw [if_pos rfl, hself]
      cases hc : s.1.1 q with
      | none => rfl
      | some a =>
        have ha := hle hc
        rw [hself] at ha
        rw [ha]
        rfl
    · rw [if_neg he, hother q' (Ne.symm he)]
      cases s.1.1 q' <;> rfl

/-- A logged call preserves the comparison, even when the initial eager cache
already contains answers absent from the log. -/
theorem logAgreement_step (P : PublicParameter) (t : (WorldSpec C).Domain)
    (ht : ¬IsProgram t) (s : LoggedState C) (hs : LogAgreement P s)
    (r : (WorldSpec C).Range t × LoggedState C)
    (hr : r ∈ support ((SigningCostProof.loggedImpl prims t).run s)) :
    LogAgreement P r.2 := by
  simp only [SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  simp only [SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk,
    support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hunif : ∀ n (p : unifSpec.Range n × HashCache C),
      p ∈ support ((unifFwdImpl (Query C →ₒ HashOutput) n).run s.1.1) → p.2 = s.1.1 := by
    intro n p hp
    simp [unifFwdImpl] at hp
    obtain ⟨a, rfl⟩ := hp
    rfl
  have hprg : ∀ x (p : Bit × HashCache C), p ∈ support ((prgAnswer prims x).run s.1.1) →
      s.1.1 ≤ p.2 ∧ ∀ q', Tracked q' → p.2 q' = s.1.1 q' := by
    intro x p hp
    unfold prgAnswer at hp
    rw [StateT.run_bind] at hp
    simp only [support_bind] at hp
    obtain ⟨p', hp', hp⟩ := Set.mem_iUnion₂.mp hp
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rw [hashAnswer_of_not_isFixed prims (by rintro ⟨_, h, _⟩; cases h)] at hp'
    have h := randomOracle_support _ s.1.1 p' hp'
    exact ⟨h.1, fun q' hq' => h.2.2 q' (hq' x.2.1)⟩
  have hkeep (cache : HashCache C) (n : ℕ) (log : QueryLog (WorldSpec C))
      (hle : s.1.1 ≤ cache) (heq : ∀ q', Tracked q' → cache q' = s.1.1 q')
      (hl : logCache log = logCache s.2) : LogAgreement P ((cache, n), log) := by
    constructor
    · simpa only [hl] using hs.1.trans hle
    · intro q' hq'
      exact (heq q' hq'.1).trans ((hs.2 q' hq').trans (congrFun hl q').symm)
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  · have hw' := hunif n w hw
    apply hkeep _ _ _ (by simp [hw']) (by simp [hw'])
    funext q'
    simp [logCache_logQuery, hashCall]
  · exact logAgreement_hash P q s hs w hw _ (fun _ => by rw [logCache_logQuery]; rfl) _
  · have hw' := hprg p w hw
    apply hkeep _ _ _ hw'.1 hw'.2
    funext q'
    simp [logCache_logQuery, hashCall]
  · exact (ht trivial).elim
  · have hw' := hunif n w hw
    apply hkeep _ _ _ (by simp [hw']) (by simp [hw'])
    funext q'
    simp [logCache_logQuery, hashCall]
  · exact logAgreement_hash P q s hs w hw _ (fun _ => by rw [logCache_logQuery]; rfl) _
  · have hw' := hprg p w hw
    apply hkeep _ _ _ hw'.1 hw'.2
    funext q'
    simp [logCache_logQuery, hashCall]

/-- The random-oracle run of a grind grows the cache and preserves every
tracked input outside bottom message inputs. The cache growth is the generic
leanVM `DeterministicSigning.cache_le_of_run`; the frame follows its query induction. -/
theorem grind_cache_frame (P : PublicParameter) (e : KeyIndex) (message : Message)
    (base : Randomness) : ∀ attempts trial (cache : HashCache C) z,
    z ∈ support ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput))
      (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
        (grind P bottomLayer e (bytesLE 32 message) base attempts trial))).run cache) →
    cache ≤ z.2 ∧ ∀ q, OutsideTrials P q → z.2 q = cache q := by
  intro attempts
  induction attempts with
  | zero =>
    intro trial cache z hz
    simp only [grind, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨le_rfl, fun _ _ => rfl⟩
  | succ n ih =>
    intro trial cache z hz
    simp [grind, Concrete.messageDigest, Concrete.tweakableHash, Concrete.oracleHash] at hz
    obtain ⟨answer, middle, hquery, hz⟩ := hz
    have h := randomOracle_support _ cache (answer, middle) hquery
    have heq : ∀ q, OutsideTrials P q → middle q = cache q :=
      fun q hq => h.2.2 q (hq.2 _ _)
    cases hdec : Codeword.decode (truncateHash answer) with
    | some encoding =>
      simp only [hdec, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact ⟨h.1, heq⟩
    | none =>
      simp only [hdec] at hz
      have hi := ih (trial + 1) middle z hz
      exact ⟨h.1.trans hi.1, fun q hq => (hi.2 q hq).trans (heq q hq)⟩

theorem baseGrind_cache_frame (P : PublicParameter) (e : KeyIndex)
    (message : Message) (answer : HashOutput) (cache : HashCache C) z
    (hz : z ∈ support ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput))
      (baseGrind P e message answer)).run cache)) :
    cache ≤ z.2 ∧ ∀ q, OutsideTrials P q → z.2 q = cache q := by
  simp only [baseGrind, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact grind_cache_frame P e message _ _ _ cache y hy

theorem grindExtra_cache_frame (P : PublicParameter) (ρ : KeyIndex → Digest)
    (p : FlatState C) (t : (WorldSpec C).Domain) (p' : FlatState C) z
    (hz : z ∈ support ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput))
      (grindExtra P ρ p t p')).run p'.1.1.1)) :
    p'.1.1.1 ≤ z.2 ∧ ∀ q, OutsideTrials P q → z.2 q = p'.1.1.1 q := by
  unfold grindExtra at hz
  split at hz
  · split at hz
    · split at hz
      · exact baseGrind_cache_frame _ _ _ _ _ _ hz
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst z
        exact ⟨le_rfl, fun _ _ => rfl⟩
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact ⟨le_rfl, fun _ _ => rfl⟩
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨le_rfl, fun _ _ => rfl⟩

theorem eagerWorld_logAgreement_of_frame (P : PublicParameter)
    (extra : FlatState C → (WorldSpec C).Domain → FlatState C →
      OracleComp (Query C →ₒ HashOutput) Unit)
    (hframe : ∀ p t p' z,
      z ∈ support ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput))
        (extra p t p')).run p'.1.1.1) →
      p'.1.1.1 ≤ z.2 ∧ ∀ q, OutsideTrials P q → z.2 q = p'.1.1.1 q)
    (t : (WorldSpec C).Domain) (ht : ¬IsProgram t) (p : FlatState C)
    (hp : LogAgreement P p.1) z
    (hz : z ∈ support ((eagerWorld prims extra t).run p)) :
    LogAgreement P z.2.1 := by
  simp only [eagerWorld, carry, StateT.run_mk, support_bind, support_map,
    Set.mem_iUnion, Set.mem_image] at hz
  obtain ⟨_, ⟨w, hw, rfl⟩, y, hy, rfl⟩ := hz
  dsimp only at hy ⊢
  have hlog := logAgreement_step prims P t ht p.1 hp w hw
  have hf := hframe p t (w.2, p.2) y hy
  exact ⟨hlog.1.trans hf.1, fun q hq => (hf.2 q hq).trans (hlog.2 q hq)⟩

theorem eagerWorld_logAgreement (P : PublicParameter) (ρ : KeyIndex → Digest)
    (t : (WorldSpec C).Domain) (ht : ¬IsProgram t) (p : FlatState C)
    (hp : LogAgreement P p.1) z
    (hz : z ∈ support ((eagerWorld prims (grindExtra P ρ) t).run p)) :
    LogAgreement P z.2.1 :=
  eagerWorld_logAgreement_of_frame prims P (grindExtra P ρ)
    (grindExtra_cache_frame P ρ) t ht p hp z hz

/-- The invariant rule for world programs excludes programming only at the
calls actually permitted by `ProgramFree`. -/
theorem support_programFree_inv {σ α : Type}
    (W : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (Inv : σ → Prop)
    (hW : ∀ t, ¬IsProgram t → ∀ s, Inv s → ∀ z ∈ support ((W t).run s), Inv z.2)
    (oa : OracleComp (WorldSpec C) α) (hfree : SigningHitProof.ProgramFree oa)
    (s : σ) (hs : Inv s) : ∀ z ∈ support ((simulateQ W oa).run s), Inv z.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact hs
  | query_bind t k ih =>
    have hb := (isQueryBoundP_query_bind_iff IsProgram t k 0).mp hfree
    have ht : ¬IsProgram t := by simpa using hb.1
    have hk : ∀ u, SigningHitProof.ProgramFree (k u) := by
      simpa [SigningHitProof.ProgramFree, ht] using hb.2
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    exact ih w.1 (hk w.1) w.2 (hW t ht s hs w hw) z hz

theorem flatWith_inv {ι σ : Type} {spec : OracleSpec ι}
    (W : QueryImpl (WorldSpec C) (StateT (LoggedState C × σ) ProbComp))
    (Inv : LoggedState C → Prop)
    (hW : ∀ t, ¬IsProgram t → ∀ s, Inv s.1 → ∀ z ∈ support ((W t).run s), Inv z.2.1)
    (outer : QueryImpl spec (StateT σ (OracleComp (WorldSpec C))))
    (hfree : ∀ t s, SigningHitProof.ProgramFree ((outer t).run s))
    (t : spec.Domain) (s : LoggedState C × σ) (hs : Inv s.1) z
    (hz : z ∈ support ((flatWith outer W t).run s)) : Inv z.2.1 := by
  simp only [flatWith, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact support_programFree_inv W (fun p => Inv p.1) hW _ (hfree t s.2) s hs w hw

/-- A logged-state invariant survives setup, every forger call, and verification. -/
theorem flatGame_inv
    (W : QueryImpl (WorldSpec C) (StateT (FlatState C) ProbComp))
    (Inv : LoggedState C → Prop)
    (hW : ∀ t, ¬IsProgram t → ∀ s, Inv s.1 → ∀ z ∈ support ((W t).run s), Inv z.2.1)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (s : FlatState C) (hs : Inv s.1) z
    (hz : z ∈ support ((flatGame W A x).run s)) : Inv z.2.1 := by
  have hsetup : SigningHitProof.ProgramFree (referenceTree
      (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top) := by
    rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
        SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _]
    exact SigningHitProof.programFree_liftFree _
  unfold flatGame gameWith at hz
  dsimp only at hz
  rw [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨r, hr, hz⟩ := hz
  have hi := support_programFree_inv W (fun p => Inv p.1) hW _ hsetup s hs r hr
  rcases r with ⟨_ | (top | tree), p⟩
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact hi
  · simp only [StateT.run_bind, getCarried, StateT.run_mk, pure_bind,
      mem_support_bind_iff] at hz
    obtain ⟨a, ha, w, hw, hz⟩ := hz
    have ha' := SeedHitProof.support_simulateQ_inv _ (fun p : FlatState C => Inv p.1)
      (flatWith_inv W Inv hW _ (SigningHitProof.programFree_flaggedOracles x top)) _ p hi a ha
    have hw' := support_programFree_inv W (fun p => Inv p.1) hW _
      (SigningHitProof.programFree_finish x top _) a.2 ha' w hw
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact hw'
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact hi

theorem flatEagerRun_logAgreement (P : PublicParameter) (ρ : KeyIndex → Digest)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) z
    (hz : z ∈ support (flatEagerRun prims P ρ A x)) : LogAgreement P z.2.1 := by
  exact flatGame_inv _ (LogAgreement P) (eagerWorld_logAgreement prims P ρ)
    A x flatInit (by
      constructor
      · intro q output h
        simp [flatInit, loggedInit, logCache] at h
      · intro q _
        rfl) z hz

/-- The comparison is unconditional on actual split support; it does not use
the fixed-randomizer `R1Link`, a budget, or a key-distinctness assumption. -/
theorem splitRun_logAgreement
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (P : PublicParameter) (ρ : KeyIndex → Digest) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) z
    (hz : z ∈ support (splitRun prims keyOf P ρ A x)) : LogAgreement P z.2.1.1.1 := by
  have hmon : (z.1, (z.2.1.1, z.2.2)) ∈ support (monitoredRun prims keyOf P ρ A x) := by
    rw [← splitRun_forget, support_map]
    exact ⟨z, hz, rfl⟩
  have heager : (z.1, (z.2.1.1.1, z.2.2)) ∈ support (flatEagerRun prims P ρ A x) := by
    rw [← monitoredRun_forget prims keyOf, support_map]
    exact ⟨_, hmon, rfl⟩
  exact flatEagerRun_logAgreement prims P ρ A x _ heager

theorem cachedRandomizer_eq_of_outside (seeds : C.Term → HashOutput)
    (P : PublicParameter) {a b : HashCache C}
    (h : ∀ q, OutsideTrials P q → a q = b q) :
    SigningGuessProof.cachedRandomizer seeds a = SigningGuessProof.cachedRandomizer seeds b := by
  funext e
  unfold SigningGuessProof.cachedRandomizer
  congr 1
  apply List.map_congr_left
  intro T _
  rw [h _ (outsideTrials_prf P _ _)]

theorem alternativeCommitment_congr_of_outside (seeds : C.Term → HashOutput)
    (P : PublicParameter) {a b : HashCache C}
    (h : ∀ q, OutsideTrials P q → a q = b q) :
    SigningGuessProof.AlternativeCommitment seeds P a ↔
      SigningGuessProof.AlternativeCommitment seeds P b := by
  have hr := cachedRandomizer_eq_of_outside seeds P h
  simp only [SigningGuessProof.AlternativeCommitment, SigningGuessProof.RandomizerCached,
    hr, h _ (outsideTrials_prf P _ _), h _ (outsideTrials_commitment P _ _)]
  rw [hr]

/-- Eager precomputation cannot create or remove the commitment exception. -/
theorem splitRun_alternativeCommitment
    (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (P : PublicParameter) (ρ : KeyIndex → Digest) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) z
    (hz : z ∈ support (splitRun prims keyOf P ρ A x)) :
    SigningGuessProof.AlternativeCommitment x.2.1 P z.2.1.1.1.1.1 ↔
      SigningGuessProof.AlternativeCommitment x.2.1 P (logCache z.2.1.1.1.2) :=
  alternativeCommitment_congr_of_outside x.2.1 P (splitRun_logAgreement prims keyOf P ρ A x z hz).2

open SigningDescentProof SigningCacheProof

/-- A replayed selected pair has a valid encoding, hence its input is cached
by leanVM's `encodingInput_cached_of_decode_some`. -/
theorem selected_decode (z : FinalState C) (pair : Message × Randomness)
    (hsel : z.selected prims = some pair) :
    ∃ encoding, XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.encodingHash (thView z.cache) z.keys.1 z.key pair) = some encoding := by
  cases hm : z.state.bound z.key with
  | none => simp [FinalState.selected, hm] at hsel
  | some message =>
    cases ht : z.bottomTree prims with
    | none => simp [FinalState.selected, hm, ht] at hsel
    | some tree =>
      cases hsc : D prims z.answers (signCodeword z.keys.1 (tree.commitment z.key) z.key message
          (D prims z.answers (prfValue z.keys.2.1 (.randomizer bottomLayer z.key)))) with
      | none => simp [FinalState.selected, hm, ht, hsc] at hsel
      | some selected =>
        obtain ⟨randomness, encoding⟩ := selected
        have hp : (message, randomness) = pair := by
          simpa [FinalState.selected, hm, ht, hsc] using hsel
        subst pair
        have hc := SigningGuessProof.signCodeword_some_commitment prims z.answers z.keys.1
          (tree.commitment z.key) z.key message _ _ hsc
        rw [D_signCodeword (prims := prims) _ _ _ _ _ hc.symm] at hsc
        have hdec := E_grind_spec (prims := prims) (h := z.answers) _ _ _ _ _ _ _ _ _ hsc
        rw [E_eval] at hdec
        erw [XmssSecurity.Bridge.messageDigest_bottom, XmssSecurity.Concrete.CacheReplay.eval_encodingHash,
          XmssSecurity.Bridge.decode_eq] at hdec
        exact ⟨encoding, hdec⟩

theorem encodingHash_mono_of_decode {a b : HashCache C} (hle : a ≤ b)
    (P : PublicParameter) (e : KeyIndex) (pair : Message × Randomness)
    (hvalid : ∃ encoding, XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.encodingHash (thView a) P e pair) = some encoding) :
    XmssSecurity.Concrete.CacheView.encodingHash (thView a) P e pair =
      XmssSecurity.Concrete.CacheView.encodingHash (thView b) P e pair := by
  obtain ⟨encoding, hvalid⟩ := hvalid
  obtain ⟨output, ho⟩ := XmssSecurity.Concrete.CacheView.encodingInput_cached_of_decode_some
    (thView a) P e pair.1 pair.2 encoding hvalid
  have ho' : thView b (XmssSecurity.Concrete.CacheView.encodingInput P e pair) = some output := hle ho
  unfold XmssSecurity.Concrete.CacheView.encodingHash
  exact (XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some ho).trans
    (XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some ho').symm

/-- Cache growth transports a partner when the selected pair is preserved.
Both encoding inputs are cached, so default answers cannot affect this step. -/
theorem bottomPartnerCase_of_selected_eq (x : SigningSecurityProof.Keys3 C)
    (r : Result C) (n : ℕ) {a b : HashCache C} (hle : a ≤ b)
    (hselected : ∀ top st forgery, r.2 = some (top, st, forgery) →
      (FinalState.mk x top st forgery a false).selected prims =
        (FinalState.mk x top st forgery b false).selected prims)
    (hpartner : SigningPartnerLinkProof.BottomPartnerCase prims x (r, a, n)) :
    SigningPartnerLinkProof.BottomPartnerCase prims x (r, b, n) := by
  obtain ⟨top, st, forgery, hr, pair, hs, hne, heq⟩ := hpartner
  change (FinalState.mk x top st forgery a false).selected prims = some pair at hs
  have hvalid := selected_decode prims _ pair hs
  have hs' := (hselected top st forgery hr).symm.trans hs
  have hleft := encodingHash_mono_of_decode hle x.1 forgery.signature.leafIndex pair hvalid
  have hright := encodingHash_mono_of_decode hle x.1 forgery.signature.leafIndex
    (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness) (by
      obtain ⟨enc, hv⟩ := hvalid
      exact ⟨enc, (congrArg XmssSecurity.TargetSum.decodeDigest heq).symm.trans hv⟩)
  exact ⟨top, st, forgery, hr, pair, hs', hne, hleft.symm.trans (heq.trans hright)⟩

/-- The original same-run event transport, conditional only on equality of
the selected replay. Cache inclusion and commitment transport are supplied
by the actual split execution, rather than additional assumptions. -/
theorem splitRun_partner_of_selected_eq
    (ρ : SigningSecurityProof.Keys3 C → KeyIndex → Digest)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (z : SplitOutcome C)
    (hz : z ∈ support (splitRunAt prims ρ A x))
    (hselected : ∀ top st forgery, z.1.2 = some (top, st, forgery) →
      (FinalState.mk x top st forgery (logCache z.2.1.1.1.2) false).selected prims =
        (FinalState.mk x top st forgery z.2.1.1.1.1.1 false).selected prims)
    (hlazy : SigningPartnerTransferProof.LoggedPartnerRow prims x
      (z.1, z.2.1.1.1.1.2, z.2.1.1.1.2)) :
    EagerPartner prims x z ∧
      ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1 := by
  have hcache := splitRun_logAgreement prims (XmssSecurity.encodingInputLeafIndex? x.1)
    x.1 (ρ x) A x z hz
  have halt := splitRun_alternativeCommitment prims (XmssSecurity.encodingInputLeafIndex? x.1)
    x.1 (ρ x) A x z hz
  change z.1.1 = (true, false) ∧
    ¬SigningGuessProof.ChargedOutput prims x (z.1, logCache z.2.1.1.1.2, z.2.1.1.1.1.2) ∧
    SigningPartnerLinkProof.BottomPartnerCase prims x
      (z.1, logCache z.2.1.1.1.2, z.2.1.1.1.1.2) at hlazy
  refine ⟨⟨hlazy.1, bottomPartnerCase_of_selected_eq prims x z.1 _ hcache.1 hselected hlazy.2.2⟩, ?_⟩
  exact fun he => hlazy.2.1 (Or.inr (Or.inl (halt.mp he)))

end SigningPartnerCompareProof
end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningPartnerCompareProof.splitRun_logAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningPartnerCompareProof.splitRun_logAgreement

/-- info: 'ThresholdLeanXmssSecurity.SigningPartnerCompareProof.splitRun_alternativeCommitment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningPartnerCompareProof.splitRun_alternativeCommitment

/-- info: 'ThresholdLeanXmssSecurity.SigningPartnerCompareProof.selected_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningPartnerCompareProof.selected_decode

/-- info: 'ThresholdLeanXmssSecurity.SigningPartnerCompareProof.bottomPartnerCase_of_selected_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningPartnerCompareProof.bottomPartnerCase_of_selected_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningPartnerCompareProof.splitRun_partner_of_selected_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningPartnerCompareProof.splitRun_partner_of_selected_eq
