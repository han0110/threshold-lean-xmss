import ThresholdLeanXmssSecurity.Proof.LifetimeBridge

/-!
# Fresh PRSS inputs after the joint lifetime prefix

The selector of `LifetimeBridge.JointKeyHopFrom` receives every long-term dealer key. This
does not expose the fresh PRSS parts sampled by `ceremonyWith`: signing pair keys and ceremony
stream keys are different inputs. The selector also runs in the adversary role, on which
`keyWorld` agrees with the real local oracle. No counterexample follows from those dealer keys.

We retain the complete selected input, cache and counted query log. Independently sampled fresh
PRSS parts and echo keys hit a protected point in this prefix with probability at most
`q0 * prssKeyCount C / 2^256`. The same bound covers protected points already in its cache.
Refreshing those cells during the prefix bounds the resulting event probability by the reference
probability plus this charge, with an arbitrary common continuation on the selected input. The
results permit arbitrary adaptive selection and impose no secrecy condition on dealer keys.

The pinned and current leanVM `Seeded/AdaptiveSeedGuessing.lean` and `Bridge/Program.lean` were
searched first. Their log-first guessing and joint-cache principles apply here; the existing
threshold lemmas also cover PRSS derivation and echo domains, so those are reused directly.

The whole-run interface is `LifetimeBridge.JointKeyHopFrom ... (keySplit C)`. Its
post-selection setup and continuation estimate requires an adaptive extension of the
fixed-tree `TreeKeyAimed` proof. The prefix bound below does not condition that theorem on the
selector's output and does not claim the full key hop.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeJointKey

open LifetimeBridge

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- The metadata and cache stay together; the second component records counted hash inputs. -/
def prefixLog (prims : Primitives) (pre : Selector C) :
    ProbComp ((JointInput C × HashCache C) × List (Query C)) :=
  (fun r => ((r.1.1, r.2), r.1.2)) <$>
    (simulateQ (localAnswer prims) (prssHashLog (jointPrefix pre))).run ∅

theorem prefixLog_fst (prims : Primitives) (pre : Selector C) :
    Prod.fst <$> prefixLog prims pre = jointPrefixRun prims pre := by
  have h := congrArg (fun p => (simulateQ (localAnswer prims) p).run (∅ : HashCache C))
    (prssHashLog_fst (jointPrefix pre))
  simpa only [prefixLog, jointPrefixRun, simulateQ_map, StateT.run_map, Functor.map_map,
    Function.comp_def] using h

theorem prefixLog_length (prims : Primitives) (pre : Selector C) (q0 : ℕ)
    (hq : IsQueryBoundP (jointPrefix pre) Counted q0)
    (r : (JointInput C × HashCache C) × List (Query C))
    (hr : r ∈ support (prefixLog prims pre)) : r.2.length ≤ q0 := by
  simp only [prefixLog, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  apply prssHashLog_length (jointPrefix pre) q0 hq p.1
  apply support_simulateQ_run'_subset (localAnswer prims) (prssHashLog (jointPrefix pre)) ∅
  rw [StateT.run'_eq, support_map]
  exact ⟨p, hp, rfl⟩

/-- Every cached point was queried in the same run, including the internal hash of a PRG call. -/
theorem prefixLog_cached (prims : Primitives) (pre : Selector C)
    (r : (JointInput C × HashCache C) × List (Query C))
    (hr : r ∈ support (prefixLog prims pre)) (v : Query C)
    (hv : r.1.2 v ≠ none) : v ∈ r.2 := by
  simp only [prefixLog, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  by_contra hn
  exact hv (prssHashLog_cache_other prims (jointPrefix pre) ∅ p hp v hn)

/-- Sample the actual joint prefix before the fresh parts and refreshed hidden keys. -/
def prefixFresh (prims : Primitives) (pre : Selector C) :
    ProbComp (((JointInput C × HashCache C) × List (Query C)) ×
      (C.Party → Parts C) × KeygenFresh C) := do
  let r ← prefixLog prims pre
  let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
  let u ← $ᵗ (KeygenFresh C)
  pure (r, parts, u)

/-- Fresh private parts can move before the entire prefix, without conditioning its metadata. -/
theorem prefixFresh_law (prims : Primitives) (pre : Selector C) :
    𝒟[prefixFresh prims pre] = 𝒟[(fun r => (r.1.2, r.1.1, r.2)) <$> (do
      let r ← keygenPartsKernel (fun _ => prefixLog prims pre)
      let u ← $ᵗ (KeygenFresh C)
      pure (r, u))] := by
  simp only [prefixFresh, keygenPartsKernel, map_bind, map_pure, bind_assoc, pure_bind]
  exact evalDist_bind_bind_swap _ _ _

/-- One budget pays for both canonical derivation and echo points, whose query tags are disjoint. -/
theorem prefix_protected_le (prims : Primitives) (D : C.Coalition) (pre : Selector C)
    (q0 : ℕ) (hq : IsQueryBoundP (jointPrefix pre) Counted q0) :
    Pr[fun r => ∃ v ∈ r.1.2, AimedPrefixCell D r.2.1 r.2.2 v |
      prefixFresh prims pre] ≤ ((q0 * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [probEvent_congr_evalDist (prefixFresh_law prims pre), probEvent_map]
  exact probEvent_aimedPrefixLog_kernel_le D (fun _ => prefixLog prims pre)
    ⟨by intros; rfl, by intros; rfl⟩ q0 Prod.snd
    (fun _ r hr => prefixLog_length prims pre q0 hq r hr)

/-- The same charge makes every protected PRSS point absent from the prefix's actual cache. -/
theorem prefix_cached_protected_le (prims : Primitives) (D : C.Coalition) (pre : Selector C)
    (q0 : ℕ) (hq : IsQueryBoundP (jointPrefix pre) Counted q0) :
    Pr[fun r => ∃ v, AimedPrefixCell D r.2.1 r.2.2 v ∧ r.1.1.2 v ≠ none |
      prefixFresh prims pre] ≤ ((q0 * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  refine (probEvent_mono (fun r hr h => ?_)).trans (prefix_protected_le prims D pre q0 hq)
  obtain ⟨v, hv, hc⟩ := h
  simp only [prefixFresh, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨p, hp, parts, _, u, _, rfl⟩ := hr
  exact ⟨v, prefixLog_cached prims pre p hp v hc, hv⟩

/-- The eager-oracle version needed when refreshing hidden PRSS derivation and echo cells. -/
theorem prefix_fixed_protected_le (prims : Primitives) (D : C.Coalition) (pre : Selector C)
    (h : Query C → HashOutput) (q0 : ℕ)
    (hq : IsQueryBoundP (jointPrefix pre) Counted q0) :
    Pr[fun r => ∃ v ∈ r.1.2.2, AimedPrefixCell D r.1.1 r.2 v | (do
      let r ← keygenPartsKernel (fun _ => simulateQ (prssLocalAt prims h)
        (keygenHashLog (jointPrefix pre)))
      let u ← $ᵗ (KeygenFresh C)
      pure (r, u))] ≤ ((q0 * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  apply probEvent_aimedProtectedLog_kernel_le D _ ⟨by intros; rfl, by intros; rfl⟩
  intro parts r hr
  apply aimedSetupLog_length_le _ _ _ r (support_simulateQ_subset _ _ hr)
  apply IsQueryBoundP.of_imp (p' := Counted) _ hq
  intro t ht
  rcases t with n | v | a
  · exact ht.elim
  · cases v <;> simp_all [aimedLocalSetup, aimedSetupQuery, Counted]
  · exact ht.elim

/-- Replace only protected cells during the selecting prefix, then run the same arbitrary
continuation on its actual selected input. The continuation may depend on both fresh samples. -/
theorem prefix_reprogram_le {β : Type} (prims : Primitives) (D : C.Coalition)
    (pre : Selector C) (h : Query C → HashOutput)
    (changed : (C.Party → Parts C) → KeygenFresh C → Query C → HashOutput)
    (hoff : ∀ parts u v, ¬ AimedPrefixCell D parts u v →
      prssHashAt prims (changed parts u) v = prssHashAt prims h v)
    (next : (C.Party → Parts C) → KeygenFresh C → JointInput C → ProbComp β)
    (event : β → Prop) (q0 : ℕ) (hq : IsQueryBoundP (jointPrefix pre) Counted q0) :
    Pr[event | (do
      let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
      let u ← $ᵗ (KeygenFresh C)
      let r ← simulateQ (prssLocalAt prims (changed parts u)) (jointPrefix pre)
      next parts u r)] ≤
    Pr[event | (do
      let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
      let u ← $ᵗ (KeygenFresh C)
      let r ← simulateQ (prssLocalAt prims h) (jointPrefix pre)
      next parts u r)] + ((q0 * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have hp (parts : C.Party → Parts C) (u : KeygenFresh C) :
      Pr[event | simulateQ (prssLocalAt prims (changed parts u)) (jointPrefix pre) >>= next parts u] ≤
      Pr[event | simulateQ (prssLocalAt prims h) (jointPrefix pre) >>= next parts u] +
      Pr[fun r => ∃ v ∈ r.2, AimedPrefixCell D parts u v |
        simulateQ (prssLocalAt prims h) (keygenHashLog (jointPrefix pre))] := by
    simp only [aimed_prssLocalAt_eq]
    exact probEvent_aimedPrefix_swap_le prims _ _ (AimedPrefixCell D parts u)
      (hoff parts u) (jointPrefix pre) (next parts u) event
  have ht := aimedMean_mono (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C))
    (fun parts => aimedMean_mono ($ᵗ (KeygenFresh C)) (hp parts))
  simp only [aimedMean_add] at ht
  have he : aimedMean (Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C))
      (fun parts => aimedMean ($ᵗ (KeygenFresh C)) (fun u =>
        Pr[fun r => ∃ v ∈ r.2, AimedPrefixCell D parts u v |
          simulateQ (prssLocalAt prims h) (keygenHashLog (jointPrefix pre))])) ≤
      ((q0 * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [aimedMean_parts_event]
    exact prefix_fixed_protected_le prims D pre h q0 hq
  simpa only [aimedMean_probEvent] using ht.trans (add_le_add le_rfl he)

/-- The concrete canonical-key and echo-table refresh used by `TreeKeyAimed`. No tree is fixed
before the selecting prefix, and the entire continuation uses the selected metadata. -/
theorem prefix_refresh_le {β : Type} (prims : Primitives) (D : C.Coalition)
    (pre : Selector C) (S : Finset (Query C))
    (hmem : ∀ parts n, Hidden D n → hiddenInput parts n ∈ S)
    (a echo : S → HashOutput)
    (next : (C.Party → Parts C) → KeygenFresh C → JointInput C → ProbComp β)
    (event : β → Prop) (q0 : ℕ) (hq : IsQueryBoundP (jointPrefix pre) Counted q0) :
    Pr[event | (do
      let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
      let u ← $ᵗ (KeygenFresh C)
      let r ← simulateQ (prssLocalAt prims
        (prssExtend S (aimedRefresh D S parts (hmem parts) a echo u))) (jointPrefix pre)
      next parts u r)] ≤
    Pr[event | (do
      let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
      let u ← $ᵗ (KeygenFresh C)
      let r ← simulateQ (prssLocalAt prims (prssExtend S a)) (jointPrefix pre)
      next parts u r)] + ((q0 * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  prefix_reprogram_le prims D pre (prssExtend S a) _
    (fun parts u => aimedRefresh_off prims D S parts (hmem parts) a echo u)
    next event q0 hq

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointKey.prefixLog_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prefixLog_fst

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointKey.prefixFresh_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prefixFresh_law

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointKey.prefix_protected_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prefix_protected_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointKey.prefix_cached_protected_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prefix_cached_protected_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimeJointKey.prefix_refresh_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prefix_refresh_le

end ThresholdLeanXmssSecurity.LifetimeJointKey
