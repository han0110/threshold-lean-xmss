import ThresholdLeanXmssSecurity.Proof.SigningReleasedAlign

/-!
# Cached digest preimages and the signing monitor

The monitor records every cached valid digest at an unsigned key as pending. At a signed
key, absence of a hit identifies one cached input for the target digest. These
properties track the actual digest cache, including queries preceding installation.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity.SigningSignedSeparationProof

open SigningPartnerBoundProof SigningFlatEagerProof

attribute [local instance] Classical.propDecidable

abbrev DigestCache := XmssSecurity.HashInput → Option XmssSecurity.Digest

/-- The digest part of the world cache. -/
def digestCache {C : Committee} (cache : HashCache C) : DigestCache :=
  fun input => XmssSecurity.truncateHash <$> cache (.hash input)

/-- Cache coverage, pending unsigned values, and a unique signed preimage until a hit. -/
structure CacheInvariant (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)
    (table : DigestCache) (monitor : Monitor) : Prop where
  seen : ∀ input, input ∈ monitor.seen ↔ table input ≠ none
  pending : ∀ input digest e, table input = some digest → keyOf input = some e →
    monitor.state.signed e = none → XmssSecurity.TargetSum.ValidDigest digest →
      digest ∈ monitor.state.pending e
  signed : ∀ e digest, monitor.state.signed e = some digest → monitor.hit = false →
    ∃ owner, keyOf owner = some e ∧ table owner = some digest ∧
      ∀ input, keyOf input = some e → table input = some digest → input = owner

/-- The empty monitor and empty cache satisfy all three properties. -/
theorem invariant_empty (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) :
    CacheInvariant keyOf (fun _ => none) Monitor.empty := by
  constructor
  · intro input
    simp [Monitor.empty]
  · intro input digest e h
    cases h
  · intro e digest h
    cases h

/-- Unique signed preimages imply the required collision hit on the full world cache. -/
theorem CacheInvariant.separation {C : Committee}
    {keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex}
    {cache : HashCache C} {monitor : Monitor} (h : CacheInvariant keyOf (digestCache cache) monitor)
    (e : XmssSecurity.LeafIndex) (digest : XmssSecurity.Digest)
    (hs : monitor.state.signed e = some digest)
    (left right : XmssSecurity.HashInput) (hne : left ≠ right)
    (hl : keyOf left = some e) (hr : keyOf right = some e)
    (a b : HashOutput) (ha : cache (.hash left) = some a) (hb : cache (.hash right) = some b)
    (hda : XmssSecurity.truncateHash a = digest) (hdb : XmssSecurity.truncateHash b = digest) :
    monitor.hit = true := by
  cases hh : monitor.hit with
  | true => rfl
  | false =>
    obtain ⟨owner, _, _, hu⟩ := h.signed e digest hs hh
    have hleft := hu left hl (by change Option.map _ (cache (.hash left)) = _; rw [ha]; exact congrArg some hda)
    have hright := hu right hr (by change Option.map _ (cache (.hash right)) = _; rw [hb]; exact congrArg some hdb)
    exact (hne (hleft.trans hright.symm)).elim

/-- Adding a genuinely new digest synchronizes cache membership and the seen set. -/
theorem seen_update {table : DigestCache} {seen : Set XmssSecurity.HashInput}
    (hseen : ∀ input, input ∈ seen ↔ table input ≠ none)
    (input : XmssSecurity.HashInput) (digest : XmssSecurity.Digest) :
    ∀ query, query ∈ insert input seen ↔ Function.update table input (some digest) query ≠ none := by
  intro query
  by_cases he : query = input
  · subst query
    simp
  · simp [Set.mem_insert_iff, he, hseen]

/-- Installation at a fresh valid input detects any previously cached equal digest. -/
theorem install_detects_cached
    {keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex}
    {table : DigestCache} {monitor : Monitor} (h : CacheInvariant keyOf table monitor)
    (input other : XmssSecurity.HashInput) (e : XmssSecurity.LeafIndex)
    (digest : XmssSecurity.Digest)
    (hk : keyOf input = some e) (hs : monitor.state.signed e = none)
    (hv : XmssSecurity.TargetSum.ValidDigest digest)
    (hother : table other = some digest) (hkey : keyOf other = some e) :
    (monitor.fresh keyOf input digest true).hit = true := by
  rw [monitor.fresh_unsigned keyOf input digest true e hk hs]
  simp [hv, h.pending other digest e hother hkey hs hv]

/-- A fresh installation preserves the full cache invariant. -/
theorem invariant_install
    {keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex}
    {table : DigestCache} {monitor : Monitor} (h : CacheInvariant keyOf table monitor)
    (input : XmssSecurity.HashInput) (e : XmssSecurity.LeafIndex)
    (digest : XmssSecurity.Digest)
    (hk : keyOf input = some e) (hs : monitor.state.signed e = none)
    (hv : XmssSecurity.TargetSum.ValidDigest digest) :
    CacheInvariant keyOf (Function.update table input (some digest))
      (monitor.fresh keyOf input digest true) := by
  rw [monitor.fresh_unsigned keyOf input digest true e hk hs]
  simp only [hv, if_true]
  constructor
  · exact seen_update h.seen input digest
  · intro query value f hcache hkey hunsigned hvalid
    by_cases hfe : f = e
    · subst f
      simp [XmssSecurity.EncodingMonitor.State.install] at hunsigned
    · have hqi : query ≠ input := by
        intro he
        subst query
        exact hfe (Option.some.inj (hkey.symm.trans hk))
      rw [Function.update_of_ne hqi] at hcache
      have hunsigned' : monitor.state.signed f = none := by
        simpa [XmssSecurity.EncodingMonitor.State.install, hfe] using hunsigned
      simpa [XmssSecurity.EncodingMonitor.State.install, hfe] using
        h.pending query value f hcache hkey hunsigned' hvalid
  · intro f value htarget hhit
    have hhit' : monitor.hit = false := (Bool.or_eq_false_iff.mp hhit).1
    have hnot : digest ∉ monitor.state.pending e := by
      simpa using (Bool.or_eq_false_iff.mp hhit).2
    by_cases hfe : f = e
    · subst f
      have heq : digest = value := by
        simpa [XmssSecurity.EncodingMonitor.State.install] using htarget
      subst value
      refine ⟨input, hk, by simp, ?_⟩
      intro query hkey hcache
      by_contra hqi
      rw [Function.update_of_ne hqi] at hcache
      exact hnot (h.pending query digest e hcache hkey hs hv)
    · have htarget' : monitor.state.signed f = some value := by
        simpa [XmssSecurity.EncodingMonitor.State.install, hfe] using htarget
      obtain ⟨owner, ho, hc, hu⟩ := h.signed f value htarget' hhit'
      have hone : owner ≠ input := by
        intro he
        subst owner
        exact hfe (Option.some.inj (ho.symm.trans hk))
      refine ⟨owner, ho, ?_, ?_⟩
      · rwa [Function.update_of_ne hone]
      · intro query hkey hcache
        have hqi : query ≠ input := by
          intro he
          subst query
          exact hfe (Option.some.inj (hkey.symm.trans hk))
        rw [Function.update_of_ne hqi] at hcache
        exact hu query hkey hcache

/-- A cache insertion at an unsigned key cannot alter any signed owner. -/
theorem unsigned_owner_update
    {keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex}
    {table : DigestCache} {monitor : Monitor} (h : CacheInvariant keyOf table monitor)
    (input : XmssSecurity.HashInput) (e : XmssSecurity.LeafIndex)
    (digest : XmssSecurity.Digest) (hk : keyOf input = some e)
    (hs : monitor.state.signed e = none) :
    ∀ f value, monitor.state.signed f = some value → monitor.hit = false →
      ∃ owner, keyOf owner = some f ∧
        Function.update table input (some digest) owner = some value ∧
        ∀ query, keyOf query = some f →
          Function.update table input (some digest) query = some value → query = owner := by
  intro f value htarget hhit
  have hfe : f ≠ e := by intro he; subst f; rw [hs] at htarget; cases htarget
  have hne : ∀ query, keyOf query = some f → query ≠ input := by
    intro query hq he
    subst query
    exact hfe (Option.some.inj (hq.symm.trans hk))
  obtain ⟨owner, ho, hc, hu⟩ := h.signed f value htarget hhit
  refine ⟨owner, ho, ?_, ?_⟩
  · rwa [Function.update_of_ne (hne owner ho)]
  · intro query hq hc
    rw [Function.update_of_ne (hne query hq)] at hc
    exact hu query hq hc

/-- A fresh query at an unsigned key records its valid value as pending. -/
theorem invariant_query_unsigned
    {keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex}
    {table : DigestCache} {monitor : Monitor} (h : CacheInvariant keyOf table monitor)
    (input : XmssSecurity.HashInput) (e : XmssSecurity.LeafIndex)
    (digest : XmssSecurity.Digest) (hk : keyOf input = some e)
    (hs : monitor.state.signed e = none) (honest : Bool)
    (hn : honest = false ∨ ¬XmssSecurity.TargetSum.ValidDigest digest) :
    CacheInvariant keyOf (Function.update table input (some digest))
      (monitor.fresh keyOf input digest honest) := by
  rw [monitor.fresh_unsigned keyOf input digest honest e hk hs]
  by_cases hv : XmssSecurity.TargetSum.ValidDigest digest
  · have hh : honest = false := hn.resolve_right (not_not_intro hv)
    simp only [hv, hh, if_true, Bool.false_eq_true, if_false]
    constructor
    · exact seen_update h.seen input digest
    · intro query value f hc hq hu hvalid
      by_cases hqi : query = input
      · subst query
        have hfe : f = e := Option.some.inj (hq.symm.trans hk)
        subst f
        have hd : digest = value := by simpa using hc
        subst value
        simp [XmssSecurity.EncodingMonitor.State.addPending]
      · rw [Function.update_of_ne hqi] at hc
        have hp := h.pending query value f hc hq hu hvalid
        by_cases hfe : f = e
        · subst f
          simpa [XmssSecurity.EncodingMonitor.State.addPending] using Or.inr hp
        · simpa [XmssSecurity.EncodingMonitor.State.addPending, hfe] using hp
    · exact unsigned_owner_update h input e digest hk hs
  · simp only [hv, if_false]
    constructor
    · exact seen_update h.seen input digest
    · intro query value f hc hq hu hvalid
      by_cases hqi : query = input
      · subst query
        have hd : digest = value := by simpa using hc
        exact (hv (hd ▸ hvalid)).elim
      · rw [Function.update_of_ne hqi] at hc
        exact h.pending query value f hc hq hu hvalid
    · exact unsigned_owner_update h input e digest hk hs

/-- Fresh ordinary queries compare new signed-key answers with the installed target. -/
theorem invariant_fresh_signed
    {keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex}
    {table : DigestCache} {monitor : Monitor} (h : CacheInvariant keyOf table monitor)
    (input : XmssSecurity.HashInput) (e : XmssSecurity.LeafIndex)
    (digest target : XmssSecurity.Digest) (hk : keyOf input = some e)
    (hs : monitor.state.signed e = some target) (hnew : table input = none) (honest : Bool) :
    CacheInvariant keyOf (Function.update table input (some digest))
      (monitor.fresh keyOf input digest honest) := by
  rw [monitor.fresh_signed keyOf input digest honest e hk target hs]
  constructor
  · exact seen_update h.seen input digest
  · intro query value f hc hq hu hv
    by_cases hqi : query = input
    · subst query
      have hfe : f = e := Option.some.inj (hq.symm.trans hk)
      subst f
      rw [hs] at hu
      cases hu
    · rw [Function.update_of_ne hqi] at hc
      exact h.pending query value f hc hq hu hv
  · intro f value ht hh
    have hm : monitor.hit = false := (Bool.or_eq_false_iff.mp hh).1
    have hdiff : digest ≠ target := by simpa using (Bool.or_eq_false_iff.mp hh).2
    obtain ⟨owner, ho, hc, hu⟩ := h.signed f value ht hm
    have hone : owner ≠ input := by intro he; subst owner; rw [hnew] at hc; cases hc
    refine ⟨owner, ho, by rwa [Function.update_of_ne hone], ?_⟩
    intro query hq hcache
    by_cases hqi : query = input
    · subst query
      have hfe : f = e := Option.some.inj (hq.symm.trans hk)
      subst f
      have htv : target = value := Option.some.inj (hs.symm.trans ht)
      have hdv : digest = value := by simpa using hcache
      exact (hdiff (hdv.trans htv.symm)).elim
    · rw [Function.update_of_ne hqi] at hcache
      exact hu query hq hcache

/-- Hash inputs outside the encoding domain affect only cache coverage. -/
theorem invariant_fresh_none
    {keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex}
    {table : DigestCache} {monitor : Monitor} (h : CacheInvariant keyOf table monitor)
    (input : XmssSecurity.HashInput) (digest : XmssSecurity.Digest)
    (hk : keyOf input = none) (honest : Bool) :
    CacheInvariant keyOf (Function.update table input (some digest))
      (monitor.fresh keyOf input digest honest) := by
  rw [monitor.fresh_none keyOf input digest honest hk]
  have hne : ∀ query e, keyOf query = some e → query ≠ input := by
    intro query e hq he
    subst query
    rw [hk] at hq
    cases hq
  constructor
  · exact seen_update h.seen input digest
  · intro query value e hc hq hu hv
    rw [Function.update_of_ne (hne query e hq)] at hc
    exact h.pending query value e hc hq hu hv
  · intro e value hs hh
    obtain ⟨owner, ho, hc, hu⟩ := h.signed e value hs hh
    refine ⟨owner, ho, by rwa [Function.update_of_ne (hne owner e ho)], ?_⟩
    intro query hq hc
    rw [Function.update_of_ne (hne query e hq)] at hc
    exact hu query hq hc

/-- A fresh monitored query or installation maintains the digest-cache invariant. -/
theorem invariant_fresh
    {keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex}
    {table : DigestCache} {monitor : Monitor} (h : CacheInvariant keyOf table monitor)
    (input : XmssSecurity.HashInput) (digest : XmssSecurity.Digest)
    (hnew : table input = none) (honest : Bool) :
    CacheInvariant keyOf (Function.update table input (some digest))
      (monitor.fresh keyOf input digest honest) := by
  cases hk : keyOf input with
  | none => exact invariant_fresh_none h input digest hk honest
  | some e =>
    cases hs : monitor.state.signed e with
    | some target => exact invariant_fresh_signed h input e digest target hk hs hnew honest
    | none =>
      by_cases hv : XmssSecurity.TargetSum.ValidDigest digest
      · cases honest with
        | false => exact invariant_query_unsigned h input e digest hk hs false (Or.inl rfl)
        | true => exact invariant_install h input e digest hk hs hv
      · exact invariant_query_unsigned h input e digest hk hs honest (Or.inr hv)

theorem digestCache_none_iff {C : Committee} (cache : HashCache C) (input : HashInput) :
    digestCache cache input = none ↔ cache (.hash input) = none := by
  change Option.map _ _ = none ↔ _
  exact Option.map_eq_none_iff

theorem CacheInvariant.cacheSeen {C : Committee}
    {keyOf : HashInput → Option KeyIndex} {cache : HashCache C} {monitor : Monitor}
    (h : CacheInvariant keyOf (digestCache cache) monitor) : CacheSeen cache monitor := by
  intro input hc
  exact (h.seen input).2 (fun hn => hc ((digestCache_none_iff cache input).1 hn))

/-- One lazy hash call updates exactly its digest entry. -/
theorem digestCache_query {C : Committee} (input : HashInput) (cache : HashCache C)
    (r : HashOutput × HashCache C)
    (hr : r ∈ support ((randomOracle (spec := Query C →ₒ HashOutput) (.hash input)).run cache)) :
    digestCache r.2 = Function.update (digestCache cache) input (some (XmssSecurity.truncateHash r.1)) := by
  obtain ⟨_, hself, hother⟩ := randomOracle_support (.hash input) cache r hr
  funext query
  by_cases hqi : query = input
  · subst query
    rw [Function.update_self]
    change Option.map _ (r.2 (.hash input)) = _
    rw [hself]
    rfl
  · rw [Function.update_of_ne hqi]
    unfold digestCache
    rw [hother (.hash query) (by simpa using hqi)]

/-- The ordinary-query monitor preserves the invariant on the actual lazy hash answer. -/
theorem invariant_query_hash {C : Committee}
    {keyOf : HashInput → Option KeyIndex} {cache : HashCache C} {monitor : Monitor}
    (h : CacheInvariant keyOf (digestCache cache) monitor)
    (input : HashInput) (r : HashOutput × HashCache C)
    (hr : r ∈ support ((randomOracle (spec := Query C →ₒ HashOutput) (.hash input)).run cache)) :
    CacheInvariant keyOf (digestCache r.2)
      (monitor.step keyOf (input, XmssSecurity.truncateHash r.1, false)) := by
  cases hc : cache (.hash input) with
  | some value =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc] at hr
    have heq := (mem_support_pure_iff _ _).1 hr
    subst r
    have hseen := h.cacheSeen input (by rw [hc]; exact Option.some_ne_none _)
    simpa only [Monitor.step, if_pos hseen] using h
  | none =>
    have hn : digestCache cache input = none := (digestCache_none_iff cache input).2 hc
    have hseen : input ∉ monitor.seen := fun hs => (h.seen input).1 hs hn
    rw [Monitor.step, if_neg hseen, digestCache_query input cache r hr]
    exact invariant_fresh h input _ hn false

/-- An unsigned-key trial preserves the invariant, including its possible installation. -/
theorem invariant_trial_unsigned {C : Committee}
    {keyOf : HashInput → Option KeyIndex} (input : HashInput) (e : KeyIndex)
    (hk : keyOf input = some e) (s : HashCache C × Monitor)
    (h : CacheInvariant keyOf (digestCache s.1) s.2) (hs : s.2.state.signed e = none)
    (r : HashOutput × (HashCache C × Monitor))
    (hr : r ∈ support ((monitoredOracle keyOf (.hash input)).run s)) :
    CacheInvariant keyOf (digestCache r.2.1) r.2.2 := by
  simp only [monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  cases hc : s.1 (.hash input) with
  | some value =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc] at hw
    have heq := (mem_support_pure_iff _ _).1 hw
    subst w
    have hseen := h.cacheSeen input (by rw [hc]; exact Option.some_ne_none _)
    simpa only [trialStep, if_pos hseen] using h
  | none =>
    have hn : digestCache s.1 input = none := (digestCache_none_iff s.1 input).2 hc
    have hseen : input ∉ s.2.seen := fun hi => (h.seen input).1 hi hn
    simp only [trialStep, if_neg hseen, trialFresh, hk, Option.bind, hs]
    rw [digestCache_query input s.1 w hw]
    exact invariant_fresh h input _ hn true

/-- An invalid trial at an unsigned key cannot install a target. -/
theorem trial_unsigned_invalid {C : Committee}
    {keyOf : HashInput → Option KeyIndex} (input : HashInput) (e : KeyIndex)
    (hk : keyOf input = some e) (s : HashCache C × Monitor)
    (hs : s.2.state.signed e = none) (r : HashOutput × (HashCache C × Monitor))
    (hr : r ∈ support ((monitoredOracle keyOf (.hash input)).run s))
    (hv : ¬XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash r.1)) :
    r.2.2.state.signed e = none := by
  simp only [monitoredOracle, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  simp only [trialStep]
  split_ifs with hseen
  · exact hs
  · simp only [trialFresh, hk, Option.bind, hs]
    rw [Monitor.fresh_unsigned keyOf s.2 input _ true e hk hs, if_neg hv]
    exact hs

/-- A grind starting unsigned stops at its first installation, so all of its trials preserve
cache separation. -/
theorem invariant_grind_unsigned {C : Committee} (P : PublicParameter) (e : KeyIndex)
    (message : Message) (base : Randomness) : ∀ attempts trial (s : HashCache C × Monitor),
    CacheInvariant (XmssSecurity.encodingInputLeafIndex? P) (digestCache s.1) s.2 →
    s.2.state.signed e = none → ∀ r,
    r ∈ support ((simulateQ (monitoredOracle (XmssSecurity.encodingInputLeafIndex? P))
      (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
        (grind P bottomLayer e (bytesLE 32 message) base attempts trial))).run s) →
    CacheInvariant (XmssSecurity.encodingInputLeafIndex? P) (digestCache r.2.1) r.2.2 := by
  intro attempts
  induction attempts with
  | zero =>
    intro trial s h hs r hr
    simp only [grind, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact h
  | succ n ih =>
    intro trial s h hs r hr
    simp [grind, Concrete.messageDigest, Concrete.tweakableHash, Concrete.oracleHash] at hr
    obtain ⟨answer, cache, monitor, hquery, hr⟩ := hr
    have hk := SigningLane2BridgeProof.encodingInputLeafIndex?_messageInput P e message (base + BitVec.ofNat digestBits trial)
    have hnext := invariant_trial_unsigned _ e hk s h hs (answer, cache, monitor) hquery
    cases hdec : Codeword.decode (truncateHash answer) with
    | some encoding =>
      simp only [hdec, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst r
      exact hnext
    | none =>
      simp only [hdec] at hr
      have hv : ¬XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash answer) := by
        have heq : XmssSecurity.TargetSum.ValidDigest (XmssSecurity.truncateHash answer) ↔
            ∃ encoding, Codeword.decode (truncateHash answer) = some encoding := by
          simp only [XmssSecurity.TargetSum.ValidDigest, XmssSecurity.Bridge.decode_eq]
          rfl
        rw [heq]
        simp [hdec]
      have hn := trial_unsigned_invalid _ e hk s hs (answer, cache, monitor) hquery hv
      exact ih (trial + 1) (cache, monitor) hnext hn r hr

/-- The Unit-returning base grind retains the same cache invariant. -/
theorem invariant_baseGrind_unsigned {C : Committee} (P : PublicParameter) (e : KeyIndex)
    (message : Message) (answer : HashOutput) (s : HashCache C × Monitor)
    (h : CacheInvariant (XmssSecurity.encodingInputLeafIndex? P) (digestCache s.1) s.2)
    (hs : s.2.state.signed e = none) (r : Unit × (HashCache C × Monitor))
    (hr : r ∈ support ((simulateQ (monitoredOracle (XmssSecurity.encodingInputLeafIndex? P))
      (baseGrind P e message answer)).run s)) :
    CacheInvariant (XmssSecurity.encodingInputLeafIndex? P) (digestCache r.2.1) r.2.2 := by
  simp only [baseGrind, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨g, hg, rfl⟩ := hr
  exact invariant_grind_unsigned P e message _ _ _ s h hs g hg

/-- Non-hash oracle calls leave every digest-cache entry unchanged. -/
theorem digestCache_nonhash {C : Committee} (q : Query C)
    (hq : ∀ input, q ≠ .hash input) (cache : HashCache C) (r : HashOutput × HashCache C)
    (hr : r ∈ support ((randomOracle (spec := Query C →ₒ HashOutput) q).run cache)) :
    digestCache r.2 = digestCache cache := by
  funext input
  unfold digestCache
  rw [randomOracle_cache_ne q cache r hr (.hash input) (Ne.symm (hq input))]

/-- The digest invariant is insensitive to PRF, mask and stream-key entries. -/
theorem invariant_query_oracle {C : Committee}
    {keyOf : HashInput → Option KeyIndex} {cache : HashCache C} {monitor : Monitor}
    (h : CacheInvariant keyOf (digestCache cache) monitor) (q : Query C)
    (r : HashOutput × HashCache C)
    (hr : r ∈ support ((randomOracle (spec := Query C →ₒ HashOutput) q).run cache)) :
    CacheInvariant keyOf (digestCache r.2) (monitor.after keyOf (queryEntry q r.1 false)) := by
  cases q with
  | hash input => exact invariant_query_hash h input r hr
  | _ =>
    change CacheInvariant keyOf (digestCache r.2) monitor
    rw [digestCache_nonhash _ (by intro input h; cases h) cache r hr]
    exact h

/-- Every unprogrammed logged world call preserves the pending and signed cache information. -/
theorem invariant_logged {C : Committee} (prims : Primitives)
    (keyOf : HashInput → Option KeyIndex) (t : (WorldSpec C).Domain)
    (l : SigningHitLaneProof.LoggedState C) (monitor : Monitor)
    (h : CacheInvariant keyOf (digestCache l.1.1) monitor)
    (ht : ¬SigningHitLaneProof.IsProgram t)
    (r : (WorldSpec C).Range t × SigningHitLaneProof.LoggedState C)
    (hr : r ∈ support ((SigningCostProof.loggedImpl prims t).run l)) :
    CacheInvariant keyOf (digestCache r.2.1.1)
      (queryEntryStep keyOf monitor (hashEntry ⟨t, r.1⟩)) := by
  obtain ⟨w, hw, hanswer, hcache, _⟩ := loggedImpl_support prims t l r hr
  rw [hcache, hanswer]
  have hprg : ∀ p (w : Bit × HashCache C),
      w ∈ support ((prgAnswer prims p).run l.1.1) →
      CacheInvariant keyOf (digestCache w.2) monitor := by
    intro p w hw
    simp only [prgAnswer, hashAnswer, StateT.run_bind, StateT.run_pure,
      support_bind, support_pure] at hw
    obtain ⟨a, ha, hw⟩ := Set.mem_iUnion₂.1 hw
    have hw2 : w.2 = a.2 := congrArg Prod.snd (show w = _ from hw)
    rw [hw2, digestCache_nonhash _ (by intro input he; cases he) l.1.1 a ha]
    exact h
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  · change w ∈ support ((fun u => (u, l.1.1)) <$>
      (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))) at hw
    rw [support_map] at hw
    obtain ⟨u, _, rfl⟩ := hw
    exact h
  · change w ∈ support ((randomOracle (spec := Query C →ₒ HashOutput) q).run l.1.1) at hw
    cases q
    all_goals exact invariant_query_oracle h _ w hw
  · exact hprg p w hw
  · exact (ht trivial).elim
  · change w ∈ support ((fun u => (u, l.1.1)) <$>
      (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))) at hw
    rw [support_map] at hw
    obtain ⟨u, _, rfl⟩ := hw
    exact h
  · change w ∈ support ((randomOracle (spec := Query C →ₒ HashOutput) q).run l.1.1) at hw
    cases q
    all_goals exact invariant_query_oracle h _ w hw
  · exact hprg p w hw

section Concrete

open SigningFlatProof SigningJointEagerProof SigningReleasedLinkProof SigningReleasedAlignProof
  SigningOneRunProof SigningPartnerCompareProof

/-- The completed canonical search forces a later base grind to replay cached answers. -/
theorem witness_base_rerun {C : Committee} (x : SigningSecurityProof.Keys3 C)
    (cache cache' : HashCache C) (state : TsigState C) (e : KeyIndex) (target : Digest)
    (h : SelectionWitness x cache state e target) (hle : cache ≤ cache')
    (message : Message) (hb : state.bound e = some message) (answer : HashOutput)
    (ha : cache' (.hash (randomizerInput x.1 bottomLayer e
      (SigningGuessProof.cachedRandomizer x.2.1 cache e) (bytesLE 32 message))) = some answer)
    (monitor : Monitor) (hc : CacheSeen cache' monitor) :
    (simulateQ (monitoredOracle (XmssSecurity.encodingInputLeafIndex? x.1))
      (baseGrind x.1 e message answer)).run (cache', monitor) = pure ((), (cache', monitor)) := by
  obtain ⟨_, oldMessage, oldAnswer, randomness, encoding, selectedAnswer, initial, completed,
    hbound, hbase, hrun, hcompleted, _, _⟩ := h
  have hm : oldMessage = message := Option.some.inj (hbound.symm.trans hb)
  subst oldMessage
  have hv : oldAnswer = answer := Option.some.inj ((hle hbase).symm.trans ha)
  subst oldAnswer
  apply SigningCacheLogProof.monitoredOracle_rerun _ _ initial completed cache' () _
    (hcompleted.trans hle) monitor hc
  simp only [baseGrind, simulateQ_map, StateT.run_map, support_map, Set.mem_image]
  exact ⟨(some (randomness, encoding), completed), hrun, rfl⟩

set_option linter.constructorNameAsVariable false in
/-- Each guarded extra grind starts unsigned or replays its completed signed search. -/
theorem invariant_extra {C : Committee} (x : SigningSecurityProof.Keys3 C)
    (p p' : FlatJointState C) (t : (WorldSpec C).Domain) (monitor : Monitor)
    (hle : p.1.1.1 ≤ p'.1.1.1)
    (h : CacheInvariant (XmssSecurity.encodingInputLeafIndex? x.1) (digestCache p'.1.1.1) monitor)
    (hw : ∀ e target, monitor.state.signed e = some target →
      SelectionWitness x p.1.1.1 p.2.1.1 e target)
    (r : Unit × (HashCache C × Monitor))
    (hr : r ∈ support ((simulateQ (monitoredOracle (XmssSecurity.encodingInputLeafIndex? x.1))
      (jointCachedExtra x.2.1 x.1 p t p')).run (p'.1.1.1, monitor))) :
    CacheInvariant (XmssSecurity.encodingInputLeafIndex? x.1) (digestCache r.2.1) r.2.2 := by
  have hpure (hp : r ∈ support ((simulateQ
      (monitoredOracle (XmssSecurity.encodingInputLeafIndex? x.1)) (pure ())).run
        (p'.1.1.1, monitor))) :
      CacheInvariant (XmssSecurity.encodingInputLeafIndex? x.1) (digestCache r.2.1) r.2.2 := by
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    rw [hp]
    exact h
  unfold jointCachedExtra SigningR1FixedProof.cachedExtra at hr
  split_ifs at hr with htrigger
  · unfold grindExtra at hr
    split_ifs at hr with hbase
    · cases hb : p.2.1.1.bound hbase.choose with
      | none => simp only [hb] at hr; exact hpure hr
      | some message =>
        cases ha : p'.1.1.1 (.hash (randomizerInput x.1 bottomLayer hbase.choose
            (SigningGuessProof.cachedRandomizer x.2.1 p.1.1.1 hbase.choose) (bytesLE 32 message))) with
        | none => simp only [hb, ha] at hr; exact hpure hr
        | some answer =>
          simp only [hb, ha] at hr
          cases hs : monitor.state.signed hbase.choose with
          | none =>
            exact invariant_baseGrind_unsigned x.1 hbase.choose message answer
              (p'.1.1.1, monitor) h hs r hr
          | some target =>
            rw [witness_base_rerun x p.1.1.1 p'.1.1.1 p.2.1.1 hbase.choose target
              (hw hbase.choose target hs) hle message hb answer ha monitor h.cacheSeen] at hr
            have heq := (mem_support_pure_iff _ _).1 hr
            rw [heq]
            exact h
    · exact hpure hr
  · exact hpure hr

/-- The invariant on the actual split state ignores only its counters, flags and carried ledger. -/
def SplitInvariant {C : Committee} (x : SigningSecurityProof.Keys3 C) (s : SplitState C) : Prop :=
  CacheInvariant (XmssSecurity.encodingInputLeafIndex? x.1) (digestCache s.1.1.1.1.1) s.1.1.2

set_option linter.constructorNameAsVariable false in
/-- Actual unprogrammed world calls preserve both unsigned pending values and signed separation. -/
theorem invariant_world {C : Committee} (prims : Primitives) (x : SigningSecurityProof.Keys3 C)
    (t : (WorldSpec C).Domain) (ht : ¬SigningHitLaneProof.IsProgram t)
    (s : SplitState C) (h : SplitInvariant x s) (hw : SelectionWitnesses x s)
    (r : (WorldSpec C).Range t × SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s)) : SplitInvariant x r.2 := by
  simp only [SigningReleasedLinkProof.world, keyedSplitWorld, StateT.run_mk, mem_support_bind_iff,
    support_map, Set.mem_image] at hr
  obtain ⟨called, hc, ground, hg, rfl⟩ := hr
  simp only [carry, StateT.run_mk, support_map, Set.mem_image] at hc
  obtain ⟨logged, hl, rfl⟩ := hc
  have hi := invariant_logged prims (XmssSecurity.encodingInputLeafIndex? x.1)
    t s.1.1.1 s.1.1.2 h ht logged hl
  have hcache : s.1.1.1.1.1 ≤ logged.2.1.1 := by
    have hcount := hl
    simp only [SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hcount
    obtain ⟨counted, hcounted, rfl⟩ := hcount
    exact SigningCacheProof.countImpl_grows prims t s.1.1.1.1 counted hcounted
  have hmon : (ground.1, ground.2.1) ∈ support ((simulateQ
      (monitoredOracle (XmssSecurity.encodingInputLeafIndex? x.1))
      (jointCachedExtra x.2.1 x.1 (s.1.1.1, s.2) t (logged.2, s.2))).run
        (logged.2.1.1, queryEntryStep (XmssSecurity.encodingInputLeafIndex? x.1)
          s.1.1.2 (hashEntry ⟨t, logged.1⟩))) := by
    rw [← keyedSplitOracle_run_forget _ _ _ s.1.2, support_map, Set.mem_image]
    with_reducible exact ⟨ground, hg, rfl⟩
  change CacheInvariant _ (digestCache ground.2.1.1) ground.2.1.2
  apply invariant_extra x (s.1.1.1, s.2) (logged.2, s.2) t _ hcache hi _
    (ground.1, ground.2.1) (by with_reducible exact hmon)
  intro e target hs
  rw [SigningR1FixedProof.queryEntryStep_signed] at hs
  exact hw e target hs

/-- A public world program preserves the cache invariant together with its canonical search witnesses. -/
theorem invariant_world_run {C : Committee} (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) {α : Type} (source : OracleComp (WorldSpec C) α)
    (hfree : SigningHitProof.ProgramFree source) (s : SplitState C)
    (hs : SplitInvariant x s ∧ SelectionWitnesses x s) (r : α × SplitState C)
    (hr : r ∈ support ((simulateQ (SigningReleasedLinkProof.world prims x) source).run s)) :
    SplitInvariant x r.2 ∧ SelectionWitnesses x r.2 := by
  exact support_programFree_inv (SigningReleasedLinkProof.world prims x)
    (fun s => SplitInvariant x s ∧ SelectionWitnesses x s)
    (fun t ht s hs r hr => ⟨invariant_world prims x t ht s hs.1 hs.2 r hr,
      world_witnesses prims x t s hs.2 r hr⟩) source hfree s hs r hr

/-- The adaptive opening handler changes its carried ledger without changing the digest invariant. -/
theorem invariant_forger {C : Committee} (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (s : SplitState C)
    (hs : SplitInvariant x s ∧ SelectionWitnesses x s)
    (r : (LocalSpec C + TsigSpec C).Range t × SplitState C)
    (hr : r ∈ support ((forger prims x top t).run s)) :
    SplitInvariant x r.2 ∧ SelectionWitnesses x r.2 := by
  refine ⟨?_, forger_witnesses prims x top t s hs.2 r hr⟩
  simp only [forger, flatWith, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  have hi := invariant_world_run prims x _ (programFree_openingOracles x top t s.2) s hs w hw
  exact hi.1

theorem invariant_forger_run {C : Committee} (prims : Primitives)
    (x : SigningSecurityProof.Keys3 C) (top : TopTree) {α : Type}
    (source : OracleComp (LocalSpec C + TsigSpec C) α) (s : SplitState C)
    (hs : SplitInvariant x s ∧ SelectionWitnesses x s) (r : α × SplitState C)
    (hr : r ∈ support ((simulateQ (forger prims x top) source).run s)) :
    SplitInvariant x r.2 ∧ SelectionWitnesses x r.2 := by
  exact SeedHitProof.support_simulateQ_inv _
    (fun s => SplitInvariant x s ∧ SelectionWitnesses x s)
    (fun t s hs r hr => invariant_forger prims x top t s hs r hr) source s hs r hr

set_option linter.constructorNameAsVariable false in
/-- The actual split execution retains its pending coverage and unique signed preimages. -/
theorem splitRun_invariant {C : Committee} (prims : Primitives) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (z : SplitOutcome C)
    (hz : z ∈ support (splitRunAt prims A x)) : SplitInvariant x z.2 := by
  have hsetupFree : SigningHitProof.ProgramFree (referenceTree
      (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top) := by
    rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
        SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _]
    with_reducible exact SigningHitProof.programFree_liftFree _
  unfold splitRunAt SigningOneRunProof.splitGame jointGameWith at hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨setup, hsetup, hz⟩ := hz
  have hi : SplitInvariant x
      ((SigningOneRunProof.monitoredInit.1, fun _ => false), SigningOneRunProof.monitoredInit.2) ∧
      SelectionWitnesses x
      ((SigningOneRunProof.monitoredInit.1, fun _ => false), SigningOneRunProof.monitoredInit.2) := by
    constructor
    · exact invariant_empty _
    · intro e target ht
      change (none : Option Digest) = some target at ht
      cases ht
  have hset : SplitInvariant x setup.2 ∧ SelectionWitnesses x setup.2 := by
    apply invariant_world_run prims x _ (by with_reducible exact hsetupFree) _ hi setup
    with_reducible exact hsetup
  cases hout : setup.1 with
  | none =>
    simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hset.1
  | some tree =>
    cases tree with
    | bottom tree =>
      simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hset.1
    | top top =>
      simp only [hout, StateT.run_bind, getCarried, StateT.run_mk, pure_bind,
        mem_support_bind_iff] at hz
      obtain ⟨middle, hmiddle, finished, hfinished, hz⟩ := hz
      have hm : SplitInvariant x middle.2 ∧ SelectionWitnesses x middle.2 := by
        apply invariant_forger_run prims x top _ setup.2 hset middle
        with_reducible exact hmiddle
      have hf : SplitInvariant x finished.2 ∧ SelectionWitnesses x finished.2 := by
        apply invariant_world_run prims x _ (programFree_tsigFinishLogged x top _ _) middle.2 hm finished
        with_reducible exact hfinished
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hf.1

set_option linter.constructorNameAsVariable false in
/-- Two distinct cached preimages of any installed signing target force the monitor hit. -/
theorem signedCacheSeparation {C : Committee} (prims : Primitives) :
    SigningReleasedLinkProof.SignedCacheSeparation prims (C := C) := by
  intro A x z hz e digest hs left right hne hl hr a b ha hb hda hdb
  exact (splitRun_invariant prims A x z (by with_reducible exact hz)).separation
    e digest hs left right hne hl hr a b ha hb hda hdb

end Concrete

end ThresholdLeanXmssSecurity.SigningSignedSeparationProof

/-- info: 'ThresholdLeanXmssSecurity.SigningSignedSeparationProof.invariant_install' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningSignedSeparationProof.invariant_install

/-- info: 'ThresholdLeanXmssSecurity.SigningSignedSeparationProof.invariant_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningSignedSeparationProof.invariant_fresh

/-- info: 'ThresholdLeanXmssSecurity.SigningSignedSeparationProof.invariant_grind_unsigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningSignedSeparationProof.invariant_grind_unsigned

/-- info: 'ThresholdLeanXmssSecurity.SigningSignedSeparationProof.invariant_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningSignedSeparationProof.invariant_logged

/-- info: 'ThresholdLeanXmssSecurity.SigningSignedSeparationProof.witness_base_rerun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningSignedSeparationProof.witness_base_rerun

/-- info: 'ThresholdLeanXmssSecurity.SigningSignedSeparationProof.invariant_extra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningSignedSeparationProof.invariant_extra

/-- info: 'ThresholdLeanXmssSecurity.SigningSignedSeparationProof.invariant_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningSignedSeparationProof.invariant_world

/-- info: 'ThresholdLeanXmssSecurity.SigningSignedSeparationProof.splitRun_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningSignedSeparationProof.splitRun_invariant

/-- info: 'ThresholdLeanXmssSecurity.SigningSignedSeparationProof.signedCacheSeparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningSignedSeparationProof.signedCacheSeparation
