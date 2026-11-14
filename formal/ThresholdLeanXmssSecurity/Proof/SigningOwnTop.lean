import ThresholdLeanXmssSecurity.Proof.SigningOwnCommit

/-!
# The canonical top search covers the top digest reads of a bottom ceremony

A bottom ceremony of tree `b` reads top digest inputs of key `b` only. Its first part is the setup
of `canonicalTopGrind x b`, so its search is a rerun of the canonical search. Its check reads the
selected trial of that search.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof

namespace SigningOwnTop

open SigningOwnCover SigningOwnCommit SigningSelectionProof SigningGuessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- No structural tweakable input is at a top digest address. -/
theorem structural_not_topDigest (P : PublicParameter) (key : XmssSecurity.TopIndex) (domain : HashDomain)
    (payload : HashInput) (hd : ∀ lay e, domain ≠ .message lay e) :
    ¬XmssSecurity.AtHashAddress P (.topEncoding key) (tweakableHashInput P domain payload) := by
  intro h
  cases domain with
  | message lay e => exact hd lay e rfl
  | chain lay e step =>
    exact sourceTag_not_topDigest P key
      ⟨(hashDomainFields (.chain lay e step)).tag, (hashDomainFields (.chain lay e step)).step,
        (hashDomainFields (.chain lay e step)).hi, (hashDomainFields (.chain lay e step)).lo⟩
      payload (by norm_num [hashDomainFields, tweakFields]) h
  | leaf lay e =>
    exact sourceTag_not_topDigest P key
      ⟨(hashDomainFields (.leaf lay e)).tag, (hashDomainFields (.leaf lay e)).step,
        (hashDomainFields (.leaf lay e)).hi, (hashDomainFields (.leaf lay e)).lo⟩
      payload (by norm_num [hashDomainFields, tweakFields]) h
  | node lay level idx =>
    exact sourceTag_not_topDigest P key
      ⟨(hashDomainFields (.node lay level idx)).tag, (hashDomainFields (.node lay level idx)).step,
        (hashDomainFields (.node lay level idx)).hi, (hashDomainFields (.node lay level idx)).lo⟩
      payload (by norm_num [hashDomainFields, tweakFields]) h

/-- No randomizer input is at a top digest address. -/
theorem randomizer_not_topDigest (P : PublicParameter) (key : XmssSecurity.TopIndex) (lay : Layer)
    (e : KeyIndex) (rho : Digest) (message : HashInput) :
    ¬XmssSecurity.AtHashAddress P (.topEncoding key) (randomizerInput P lay e rho message) := by
  intro h
  have he := h.1
  change (XmssSecurity.bytesLE 16 P ++ XmssSecurity.fieldBytes
    (XmssSecurity.tweakFields 7 0 (LeanXmss.layerHi lay 0) e.val) ++
    (HashSig.littleEndianBytes 16 rho ++ message)).take 32 = _ at he
  have ht := congrArg (fun xs => xs.drop 16) he
  simp only [List.take_append, XmssSecurity.length_bytesLE] at ht
  simp at ht
  rw [List.take_of_length_le (by simp)] at ht
  have hf := congrArg (fun f => f.tag.toNat) (XmssSecurity.fieldBytes_injective ht)
  norm_num [XmssSecurity.hashDomainFields, XmssSecurity.tweakFields] at hf

/-- The digest call of a top message reads only the top digest input of its trial. -/
theorem messageDigest_top_noCall (P : PublicParameter) (b : Fin (2 ^ layerHeight)) (root : Digest)
    (randomness : Randomizer) (q : HashInput → Prop)
    (hq : ¬q (XmssSecurity.Concrete.CacheView.topEncodingInput P b (root, randomness))) :
    NoCall q (Verification.messageDigestWithHash P topLayer (topKey b) (littleEndianBytes 16 root) randomness :
      OracleComp HashSpec Digest) := by
  unfold Verification.messageDigestWithHash Verification.tweakableHashWithHash
  refine noCall_bind _ (noCall_query _ _ ?_) fun _ => noCall_pure _ _
  convert hq using 2
  exact XmssSecurity.Bridge.topMessage_input P b root randomness

theorem topEncodingInput_not_other (P : PublicParameter) (key b : XmssSecurity.TopIndex) (hkb : key ≠ b)
    (payload : Digest × Randomizer) :
    ¬XmssSecurity.AtHashAddress P (.topEncoding key)
      (XmssSecurity.Concrete.CacheView.topEncodingInput P b payload) := fun h =>
  hkb (XmssSecurity.HashDomain.topEncoding.inj
    ((XmssSecurity.atHashAddress_tweakableHashInput_iff _ _ _ _).1 h)).symm

set_option maxRecDepth 100000 in
attribute [local irreducible] merkleNode merklePath grind Verification.treeFoldWithHash Verification.chainWalkWithHash in
/-- A bottom ceremony of tree `b` reads no top digest input of another key. -/
theorem bottomTree_no_topDigest (x : Keys3 C) (top : TopTree) (key : XmssSecurity.TopIndex)
    (b : Fin (2 ^ layerHeight)) (hkb : key ≠ b) :
    (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 top
      (.bottom b)).IsQueryBoundP (topDigestAddress x.1 key) 0 := by
  have hq := fun {α : Type} (oa : OracleComp HashSpec α)
      (h : NoCall (XmssSecurity.AtHashAddress x.1 (.topEncoding key)) oa) =>
    forestHash_noCall (C := C) (topDigestAddress x.1 key) oa h
  have hs := structural_not_topDigest x.1 key
  unfold referenceTree ceremonyOutput
  refine isQueryBoundP_bind (n := 0) (m := 0) ((isQueryBoundP_map_iff _ _ _).2
    (SigningHitProof.mapM_bound_zero _ _ _ fun job => referenceJob_no_topDigest x key job)) fun outputs _ => ?_
  rcases outputs with _ | outputs
  · exact isQueryBoundP_pure _ _ _
  dsimp only
  refine isQueryBoundP_bind (n := 0) (m := 0) (hq _ (merkleNode_noCall x.1 _ hs _ _ _ _)) fun root _ => ?_
  refine isQueryBoundP_bind (n := 0) (m := 0) (hq _ ?_) fun base _ => ?_
  · unfold Verification.oracleHashWithHash
    exact noCall_map _ _ (noCall_query _ _ (randomizer_not_topDigest x.1 key _ _ _ _))
  refine isQueryBoundP_bind (n := 0) (m := 0) (hq _ (grind_noCall x.1 _ _ _ _ _
    (fun r => messageDigest_top_noCall x.1 b _ r _ (topEncodingInput_not_other x.1 key b hkb _)) _ _))
    fun selected _ => ?_
  rcases selected with _ | ⟨randomness, encoding⟩
  · exact isQueryBoundP_pure _ _ _
  dsimp only
  refine isQueryBoundP_bind (n := 0) (m := 0) ((isQueryBoundP_map_iff _ _ _).2
    (SigningHitProof.mapM_bound_zero _ _ _ fun job => referenceJob_no_topDigest x key job)) fun values _ => ?_
  rcases values with _ | values
  · exact isQueryBoundP_pure _ _ _
  dsimp only
  refine isQueryBoundP_bind (n := 0) (m := 0) (hq _ (merklePath_noCall x.1 _ hs _ _ _)) fun path _ => ?_
  refine isQueryBoundP_bind (n := 0) (m := 0) (hq _ (layerRoot_noCall x.1 _ hs _ _ _ _
    (messageDigest_top_noCall x.1 b _ _ _ (topEncodingInput_not_other x.1 key b hkb _)))) fun topRoot _ => ?_
  split_ifs <;> exact isQueryBoundP_pure _ _ _

set_option maxRecDepth 100000 in
attribute [local irreducible] merkleNode merklePath grind Verification.treeFoldWithHash Verification.chainWalkWithHash in
/-- The canonical top search of a key reads each top digest input of that key in a bottom
ceremony. The ceremony of the same key is a rerun of the search. -/
theorem canonicalTopGrind_covers_bottom (x : Keys3 C) (top : TopTree) (key : XmssSecurity.TopIndex)
    (b : Fin (2 ^ layerHeight)) (cache : HashCache C)
    (z : ((Digest × Option (Randomizer × Encoding)) × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (SigningHitProof.recordReads (SigningGuessProof.canonicalTopGrind x key) ∅)).run cache))
    (w : (Option TreeOutput × HashCache C) × HashCache C)
    (hw : w ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (SigningHitProof.recordReads (referenceTree SigningHitProof.forestHash
        (SigningHitProof.forestValue x.2.1) x.1 top (.bottom b)) ∅)).run z.2))
    (input : Query C) (hrel : SigningGuessProof.topDigestInput x.1 key input)
    (hread : (w.1.2 input).isSome) : (z.1.2 input).isSome := by
  obtain ⟨hzw, -, hwrec, hR⟩ := SigningHitProof.recordReads_resolves _ ∅ z.2 (by intro i v h; cases h) w hw
  obtain ⟨-, -, hzrec, hzres⟩ :=
    SigningHitProof.recordReads_resolves _ ∅ cache (by intro i v h; cases h) z hz
  have hzfin : z.1.2 ≤ w.2 := hzrec.trans hzw
  have hzc : z.1.2 ≤ coverCacheAt (topDigestAddress x.1 key) z.1.2 w.2 := record_le_coverCacheAt _ hzfin
  have hT : ∀ input value, ¬topDigestAddress x.1 key input → w.1.2 input = some value →
      coverCacheAt (topDigestAddress x.1 key) z.1.2 w.2 input = some value :=
    fun _ _ hp hv => coverCacheAt_irrelevant _ hp (hwrec hv)
  have hrel' : topDigestAddress x.1 key input := by
    obtain ⟨payload, rfl⟩ := hrel
    exact (XmssSecurity.atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl
  have hcover : DeterministicSigning.Resolves (coverCacheAt (topDigestAddress x.1 key) z.1.2 w.2)
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 top (.bottom b))
      w.1.1 := by
    by_cases hkb : key = b
    · subst hkb
      have hq := fun {α : Type} (oa : OracleComp HashSpec α)
          (h : NoCall (XmssSecurity.AtHashAddress x.1 (.topEncoding key)) oa) =>
        forestHash_noCall (C := C) (topDigestAddress x.1 key) oa h
      have hs := structural_not_topDigest x.1 key
      have hR' := hR
      unfold referenceTree ceremonyOutput at hR' ⊢
      refine resolves_lift_bind (fun outputs houtputs => resolves_lift_bound _ _ ((isQueryBoundP_map_iff _ _ _).2
        (SigningHitProof.mapM_bound_zero _ _ _ fun job => referenceJob_no_topDigest x key job)) hT
          outputs houtputs) ?_ _ hR'
      intro outputs houtputs v hv
      rcases outputs with _ | outputs
      · rw [← hv.pure_inv]
        exact .pure _
      obtain ⟨values, hvalues, hvo⟩ := houtputs.of_map
      cases hvo
      dsimp only at hv ⊢
      refine resolves_lift_bind (fun root hroot => resolves_lift_bound _ _
        (hq _ (merkleNode_noCall x.1 _ hs _ _ _ _)) hT root hroot) (fun root hroot => ?_) _ hv
      refine resolves_lift_bind (fun base hbase => resolves_lift_bound _ _ (hq _ ?_) hT base hbase)
        (fun base hbase => ?_)
      · unfold Verification.oracleHashWithHash
        exact noCall_map _ _ (noCall_query _ _ (randomizer_not_topDigest x.1 key _ _ _ _))
      have hsetup : DeterministicSigning.Resolves w.1.2 (canonicalTopSetup x key) (root, base) := by
        unfold canonicalTopSetup canonicalTopSetupForJobs canonicalTopAfterJobs
        exact hvalues.bind (hroot.bind (hbase.bind (.pure _)))
      have hzres' := hzres
      unfold canonicalTopGrind topGrindAfter at hzres'
      obtain ⟨pair, hpair, hzg⟩ := hzres'.of_bind
      have hpe : pair = (root, base) := (hpair.mono hzfin).unique (hsetup.mono hwrec)
      subst hpe
      obtain ⟨sel, hsel, hz1⟩ := hzg.of_map
      refine resolves_lift_bind (fun selected hselected => resolves_transfer hsel hselected hzc hzfin hwrec)
        (fun selected hselected => ?_)
      have hss : selected = sel := (hselected.mono hwrec).unique (hsel.mono hzfin)
      subst hss
      rcases selected with _ | ⟨randomness, encoding⟩
      · intro v h
        rw [← h.pure_inv]
        exact .pure _
      have hz12 : z.1.1.2 = some (randomness, encoding) := by rw [← hz1]
      have hz11 : z.1.1.1 = root := by rw [← hz1]
      obtain ⟨output, hout, -⟩ := topGrindAfter_record_cached x.1 key (canonicalTopSetup x key)
        randomizerAttemptLimit cache z hz randomness encoding hz12
      rw [hz11] at hout
      have hT' : ∀ input value, ¬(topDigestAddress x.1 key input ∧ input ≠
            .hash (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key (root, randomness))) →
          w.1.2 input = some value →
          coverCacheAt (topDigestAddress x.1 key) z.1.2 w.2 input = some value := by
        intro i value hp hv
        by_cases ha : topDigestAddress x.1 key i
        · have hi : i = .hash (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key (root, randomness)) :=
            Classical.byContradiction fun h => hp ⟨ha, h⟩
          subst hi
          simp only [coverCacheAt, QueryCache.ofFn_apply]
          rw [if_pos (fun _ => by simp [hout])]
          exact hwrec hv
        · exact hT i value ha hv
      have hs' : ∀ (domain : HashDomain) (payload : HashInput), (∀ lay e, domain ≠ .message lay e) →
          ¬(fun i => topDigestAddress (C := C) x.1 key (.hash i) ∧ Query.hash (C := C) i ≠
            .hash (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key (root, randomness)))
            (tweakableHashInput x.1 domain payload) :=
        fun domain payload hd h => hs domain payload hd h.1
      dsimp only
      refine resolves_lift_bind (fun outs h => resolves_lift_bound _ _ ((isQueryBoundP_map_iff _ _ _).2
        (SigningHitProof.mapM_bound_zero _ _ _ fun job => referenceJob_no_topDigest x key job)) hT outs h)
        (fun outs _ => ?_)
      rcases outs with _ | values
      · intro v h
        rw [← h.pure_inv]
        exact .pure _
      dsimp only
      refine resolves_lift_bind (fun path h => resolves_lift_bound _ _
        (hq _ (merklePath_noCall x.1 _ hs _ _ _)) hT path h) (fun path _ => ?_)
      have hcheck := layerRoot_noCall x.1 (fun i => topDigestAddress (C := C) x.1 key (.hash i) ∧
        Query.hash (C := C) i ≠ .hash (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 key (root, randomness)))
        hs' topLayer (topKey key) (littleEndianBytes 16 root)
        ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩
        (messageDigest_top_noCall x.1 key root randomness _ (fun h => h.2 rfl))
      refine resolves_lift_bind (fun topRoot h => @resolves_lift_bound _ _ _ _ _
        (fun _ => Classical.propDecidable _) _ _ _ (forestHash_noCall _ _ hcheck) hT' topRoot h)
        (fun _ _ v h => ?_)
      split_ifs at h ⊢ <;> (rw [← h.pure_inv]; exact .pure _)
    · exact resolves_lift_bound _ _ (bottomTree_no_topDigest x top key b hkb) hT _ hR
  have hle := recordReads_le_of_resolves _ ∅ z.2 _ w.1.1 (fun _ _ h => by cases h) hcover w hw
    (coverCacheAt_le _ _ _)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hread
  exact isSome_of_coverCacheAt _ (by rw [hle hv]; rfl) hrel'

end SigningOwnTop

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTop.structural_not_topDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTop.structural_not_topDigest

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTop.randomizer_not_topDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTop.randomizer_not_topDigest

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTop.messageDigest_top_noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTop.messageDigest_top_noCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTop.topEncodingInput_not_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTop.topEncodingInput_not_other

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTop.bottomTree_no_topDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTop.bottomTree_no_topDigest

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnTop.canonicalTopGrind_covers_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnTop.canonicalTopGrind_covers_bottom
