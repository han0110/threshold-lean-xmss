import ThresholdLeanXmssSecurity.Proof.SigningOwnCover

/-!
# The commitment completion covers the commitment reads of a bottom tree

The ceremony of a bottom tree reads the commitment input `commitmentInput P e ρ` of each of its keys at the
PRF value `ρ` of the key. The commitment completion `rawCommitmentForest` reads the same input. No
other part of the ceremony reads a commitment input.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec HashSig LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss TprfSecurityProof SigningSecurityProof SigningCoreProof

namespace SigningOwnCommit

open SigningOwnCover SigningSelectionProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}
attribute [local irreducible] MonadAttach.support

section Cover

variable (p : Query C → Prop)

/-- The cache `bound` on the inputs that are not in `p` or that `record` holds. -/
def coverCacheAt (record bound : HashCache C) : HashCache C :=
  QueryCache.ofFn fun input => if p input → (record input).isSome then bound input else none

theorem coverCacheAt_le (record bound : HashCache C) : coverCacheAt p record bound ≤ bound := by
  intro input value h
  simp only [coverCacheAt, QueryCache.ofFn_apply] at h
  split_ifs at h
  · exact h

theorem record_le_coverCacheAt {record bound : HashCache C} (hle : record ≤ bound) :
    record ≤ coverCacheAt p record bound := by
  intro input value h
  simp only [coverCacheAt, QueryCache.ofFn_apply]
  rw [ite_eq_left (fun _ => by simp [h])]
  exact hle h

theorem coverCacheAt_irrelevant {record bound : HashCache C} {input : Query C} {value : HashOutput}
    (hrel : ¬p input) (h : bound input = some value) : coverCacheAt p record bound input = some value := by
  simp only [coverCacheAt, QueryCache.ofFn_apply]
  rw [ite_eq_left (fun h' => absurd h' hrel)]
  exact h

theorem isSome_of_coverCacheAt {record bound : HashCache C} {input : Query C}
    (h : (coverCacheAt p record bound input).isSome) (hrel : p input) : (record input).isSome := by
  simp only [coverCacheAt, QueryCache.ofFn_apply] at h
  split_ifs at h with hc
  · exact hc hrel
  · simp at h

end Cover

section Bounds

variable (P : PublicParameter) (p : HashInput → Prop)
  (hs : ∀ domain payload, (∀ lay key, domain ≠ .message lay key) → ¬p (tweakableHashInput P domain payload))

include hs

theorem tweakableHash_noCall (domain : HashDomain) (payload : HashInput)
    (hd : ∀ lay key, domain ≠ .message lay key) :
    NoCall p (Verification.tweakableHashWithHash P domain payload : OracleComp HashSpec Digest) := by
  unfold Verification.tweakableHashWithHash
  exact noCall_bind _ (noCall_query _ _ (hs domain payload hd)) fun _ => noCall_pure _ _

theorem chainWalk_noCall (lay : Layer) (key : KeyIndex) (chain : ChainIndex) (start steps : ℕ) (value : Digest) :
    NoCall p (Verification.chainWalkWithHash P lay key chain start steps value : OracleComp HashSpec Digest) := by
  induction steps with
  | zero => exact noCall_pure _ _
  | succ steps ih =>
    rw [Verification.chainWalkWithHash]
    refine noCall_bind _ ih fun previous => ?_
    split_ifs
    · exact tweakableHash_noCall P p hs _ _ (fun _ _ h => by cases h)
    · exact noCall_pure _ _

theorem merkleNode_noCall (lay : Layer) (ends : KeyIndex → ChainIndex → Digest) :
    ∀ level node, NoCall p (merkleNode P lay ends level node) := by
  intro level
  induction level with
  | zero =>
    intro node
    exact tweakableHash_noCall P p hs _ _ (fun _ _ h => by cases h)
  | succ level ih =>
    intro node
    rw [merkleNode]
    exact noCall_bind _ (ih _) fun _ => noCall_bind _ (ih _) fun _ =>
      tweakableHash_noCall P p hs _ _ (fun _ _ h => by cases h)

theorem merklePath_noCall (lay : Layer) (ends : KeyIndex → ChainIndex → Digest) (key : KeyIndex) :
    NoCall p (merklePath P lay ends key) :=
  noCall_sequenceFin _ _ fun _ => merkleNode_noCall P p hs lay ends _ _

theorem treeFold_noCall (lay : Layer) (key : KeyIndex) (path : Fin layerHeight → Digest) :
    ∀ levels value,
      NoCall p (Verification.treeFoldWithHash P lay key path levels value : OracleComp HashSpec Digest) := by
  intro levels
  induction levels with
  | zero => intro value; exact noCall_pure _ _
  | succ levels ih =>
    intro value
    rw [Verification.treeFoldWithHash]
    refine noCall_bind _ (ih _) fun _ => ?_
    split_ifs <;> exact tweakableHash_noCall P p hs _ _ (fun _ _ h => by cases h)

variable (lay : Layer) (key : KeyIndex) (message : HashInput)

omit hs in
theorem messageDigest_noCall (hm : ∀ payload, ¬p (tweakableHashInput P (.message lay key) payload))
    (randomness : Randomizer) :
    NoCall p (Verification.messageDigestWithHash P lay key message randomness : OracleComp HashSpec Digest) := by
  unfold Verification.messageDigestWithHash Verification.tweakableHashWithHash
  exact noCall_bind _ (noCall_query _ _ (hm _)) fun _ => noCall_pure _ _

theorem otsLeaf_noCall (randomness : Randomizer) (values : ChainIndex → Digest)
    (hmd : NoCall p (Verification.messageDigestWithHash P lay key message randomness : OracleComp HashSpec Digest)) :
    NoCall p (Verification.otsLeafWithHash P lay key message randomness values : OracleComp HashSpec _) := by
  unfold Verification.otsLeafWithHash
  refine noCall_bind _ hmd fun digest => ?_
  split
  · refine noCall_bind _ (noCall_sequenceFin _ _ fun _ => ?_) fun _ => ?_
    · unfold Verification.recoverChainWithHash; exact chainWalk_noCall P p hs _ _ _ _ _ _
    · exact noCall_map _ _ (tweakableHash_noCall P p hs _ _ (fun _ _ h => by cases h))
  · exact noCall_pure _ _

theorem layerRoot_noCall (part : LayerSignature)
    (hmd : NoCall p (Verification.messageDigestWithHash P lay key message part.randomizer : OracleComp HashSpec Digest)) :
    NoCall p (Verification.layerRootWithHash P lay key message part : OracleComp HashSpec _) := by
  unfold Verification.layerRootWithHash
  refine noCall_bind _ (otsLeaf_noCall P p hs lay key message _ _ hmd) fun leaf => ?_
  rcases leaf with _ | leaf
  · exact noCall_pure _ _
  · exact noCall_bind _ (treeFold_noCall P p hs _ _ _ _ _) fun _ => noCall_pure _ _

omit hs in
theorem grind_noCall (base : Randomizer)
    (hmd : ∀ randomness,
      NoCall p (Verification.messageDigestWithHash P lay key message randomness : OracleComp HashSpec Digest)) :
    ∀ attempts trial, NoCall p (grind P lay key message base attempts trial) := by
  intro attempts
  induction attempts with
  | zero => intro trial; exact noCall_pure _ _
  | succ attempts ih =>
    intro trial
    rw [grind]
    refine noCall_bind _ (hmd _) fun digest => ?_
    split
    · exact noCall_pure _ _
    · exact ih _

end Bounds

theorem rawCommitmentInput_hash_iff (P : PublicParameter) (input : HashInput) :
    SigningGuessProof.RawCommitmentInput (C := C) P (.hash input) ↔
      ∃ e ρ, commitmentInput P e ρ = input := by
  simp only [SigningGuessProof.RawCommitmentInput, Option.isSome_iff_exists]
  constructor
  · rintro ⟨⟨e, ρ⟩, h⟩
    exact ⟨e, ρ, (SigningGuessProof.commitmentTrial_eq_some P input e ρ).1 h⟩
  · rintro ⟨e, ρ, h⟩
    exact ⟨(e, ρ), (SigningGuessProof.commitmentTrial_eq_some P input e ρ).2 h⟩

theorem not_rawCommitment_tweakable (P P' : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    ¬SigningGuessProof.RawCommitmentInput (C := C) P (.hash (tweakableHashInput P' domain payload)) := by
  intro h
  obtain ⟨e, ρ, he⟩ := (rawCommitmentInput_hash_iff P _).1 h
  exact SigningGuessProof.commitmentInput_ne_tweakableHashInput P P' e ρ domain payload he

/-- A hash computation with no call in `q` lifts to a completion with no call in `q`. -/
theorem forestHash_noCall {α : Type} (q : Query C → Prop) (oa : OracleComp HashSpec α)
    (h : NoCall (fun input => q (.hash input)) oa) :
    (SigningHitProof.forestHash (C := C) oa).IsQueryBoundP q 0 := by
  let : OracleSpec.UniformAnswerMeasure (Query C →ₒ HashOutput) :=
    OracleSpec.UniformAnswerMeasure.ofFiniteNonempty _
  rw [noCall_iff] at h
  apply h.simulateQ_of_step
  · intro input _
    simp only [isQueryBoundP_query_iff]
    omega
  · intro input hn
    simp only [isQueryBoundP_query_iff]
    exact fun hp => (hn hp).elim

theorem forestValue_noCommitment (P : PublicParameter) (seeds : C.Term → HashOutput) (pt : Point) :
    (SigningHitProof.forestValue seeds pt).IsQueryBoundP (SigningGuessProof.RawCommitmentInput P) 0 := by
  unfold SigningHitProof.forestValue
  apply isQueryBoundP_bind (m := 0)
  · apply SigningHitProof.mapM_bound_zero
    intro T
    simp [isQueryBoundP_map_iff, isQueryBoundP_query_iff, SigningGuessProof.RawCommitmentInput]
  · intro _ _
    simp

theorem rawRandomizer_eq (seeds : C.Term → HashOutput) (e : KeyIndex) :
    SigningGuessProof.rawRandomizer seeds e = SigningHitProof.forestValue seeds (.randomizer bottomLayer e) := by
  simp [SigningGuessProof.rawRandomizer, SigningGuessProof.rawRandomizerTerms, SigningHitProof.forestValue,
    map_eq_bind_pure_comp]

theorem structural_not_commitment (P : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (_ : ∀ lay key, domain ≠ .message lay key) :
    ¬(fun input => SigningGuessProof.RawCommitmentInput (C := C) P (.hash input))
      (tweakableHashInput P domain payload) :=
  not_rawCommitment_tweakable P P domain payload

/-- A job other than a commitment job reads no commitment input. -/
theorem referenceJob_noCommitment (x : Keys3 C) (job : Job) (hk : ∀ e, job.kind ≠ .commitment e) :
    (referenceJob SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 job).IsQueryBoundP
      (SigningGuessProof.RawCommitmentInput x.1) 0 := by
  have hc := fun lay key chain start steps value =>
    forestHash_noCall _ _ (chainWalk_noCall x.1
      (fun input => SigningGuessProof.RawCommitmentInput (C := C) x.1 (.hash input))
      (structural_not_commitment x.1) lay key chain start steps value)
  unfold referenceJob
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · exact SigningHitProof.mapM_bound_zero _ _ _ fun point => forestValue_noCommitment x.1 x.2.1 point
  · intro values _
    cases hkind : job.kind with
    | chainEnd e l => exact (isQueryBoundP_map_iff _ _ _).2 (hc _ _ _ _ _ _)
    | chainRow e l =>
      exact isQueryBoundP_bind (n := 0) (m := 0) (hc _ _ _ _ _ _) fun _ _ =>
        isQueryBoundP_bind (n := 0) (m := 0) (hc _ _ _ _ _ _) fun _ _ =>
          isQueryBoundP_bind (n := 0) (m := 0) (hc _ _ _ _ _ _) fun _ _ => by simp
    | chainValue e l pos => exact (isQueryBoundP_map_iff _ _ _).2 (hc _ _ _ _ _ _)
    | commitment e => exact (hk e hkind).elim
    | randomizer => simp

/-- `SigningHitProof.mapM_bound_zero` with a premise on the members of the list only. -/
theorem mapM_bound_zero_of_mem {α β : Type} (f : α → OracleComp (Query C →ₒ HashOutput) β)
    (p : Query C → Prop) : ∀ (xs : List α), (∀ a ∈ xs, (f a).IsQueryBoundP p 0) →
      (xs.mapM f).IsQueryBoundP p 0 := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons a xs ih =>
      intro hf
      simp only [List.mapM_cons]
      exact isQueryBoundP_bind (n := 0) (m := 0) (hf a (by simp)) (fun _ _ =>
        isQueryBoundP_bind (n := 0) (m := 0) (ih fun b hb => hf b (by simp [hb])) (fun _ _ => by simp))

/-- Each job of a resolved run of a list resolves. -/
theorem resolves_mapM_mem {α β : Type} {cache : HashCache C}
    {f : α → OracleComp (Query C →ₒ HashOutput) β} :
    ∀ (xs : List α) (ys : List β), DeterministicSigning.Resolves cache (xs.mapM f) ys →
      ∀ a ∈ xs, ∃ y, DeterministicSigning.Resolves cache (f a) y := by
  intro xs
  induction xs with
  | nil => intro _ _ a ha; cases ha
  | cons head tail ih =>
    intro ys h a ha
    simp only [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := h.of_bind
    obtain ⟨ys', hys', -⟩ := h.of_bind
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨y, hy⟩
    · exact ih ys' hys' a ha

/-- The commitment job of a key resolves in a cache in which the commitment completion resolves. -/
theorem commitmentJob_resolves (x : Keys3 C) {record : HashCache C} {units : List Unit}
    (hres : DeterministicSigning.Resolves record (SigningGuessProof.rawCommitmentForest x.2.1 x.1) units)
    (e : KeyIndex) : ∃ bits, DeterministicSigning.Resolves record
      (referenceJob SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1
        ⟨.commitment e, [.randomizer bottomLayer e]⟩) bits := by
  obtain ⟨u, hu⟩ := resolves_mapM_mem _ _ hres e (by simp)
  unfold SigningGuessProof.rawCommitment at hu
  obtain ⟨ρ, hρ, hq⟩ := hu.of_bind
  obtain ⟨answer, hanswer, -⟩ := hq.query_inv
  rw [rawRandomizer_eq] at hρ
  refine ⟨(bitsOfDigest ∘ truncateHash) answer, ?_⟩
  simp only [referenceJob, List.mapM_cons, List.mapM_nil, bind_pure_comp, map_pure]
  rw [bind_map_left]
  refine hρ.bind ?_
  refine DeterministicSigning.Resolves.map (forestHash_resolves _ _ _ ?_) _
  exact .query (commitmentInput x.1 e ρ) answer
    (show SigningDescentProof.thView record _ = some answer from hanswer) _ _ (.pure _)

set_option maxRecDepth 100000 in
attribute [local irreducible] merkleNode merklePath grind Verification.treeFoldWithHash Verification.chainWalkWithHash in
/-- The commitment completion reads each commitment input of a bottom tree. -/
theorem commitmentForest_covers_bottom (x : Keys3 C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (cache : HashCache C) (z : (List Unit × HashCache C) × HashCache C)
    (hz : z ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (SigningHitProof.recordReads (SigningGuessProof.rawCommitmentForest x.2.1 x.1) ∅)).run cache))
    (w : (Option TreeOutput × HashCache C) × HashCache C)
    (hw : w ∈ support ((simulateQ (Query C →ₒ HashOutput).randomOracle
      (SigningHitProof.recordReads (referenceTree SigningHitProof.forestHash
        (SigningHitProof.forestValue x.2.1) x.1 top (.bottom b)) ∅)).run z.2))
    (input : Query C) (hrel : SigningGuessProof.RawCommitmentInput x.1 input)
    (hread : (w.1.2 input).isSome) : (z.1.2 input).isSome := by
  obtain ⟨hzw, -, hwrec, hR⟩ := SigningHitProof.recordReads_resolves _ ∅ z.2 (by intro i v h; cases h) w hw
  obtain ⟨-, -, hzrec, hzres⟩ :=
    SigningHitProof.recordReads_resolves _ ∅ cache (by intro i v h; cases h) z hz
  have hzfin : z.1.2 ≤ w.2 := hzrec.trans hzw
  have hzc : z.1.2 ≤ coverCacheAt (SigningGuessProof.RawCommitmentInput x.1) z.1.2 w.2 :=
    record_le_coverCacheAt _ hzfin
  have hT : ∀ input value, ¬SigningGuessProof.RawCommitmentInput x.1 input → w.1.2 input = some value →
      coverCacheAt (SigningGuessProof.RawCommitmentInput x.1) z.1.2 w.2 input = some value :=
    fun _ _ hp hv => coverCacheAt_irrelevant _ hp (hwrec hv)
  have hjob : ∀ job ∈ bottomJobs b, ∀ bits, DeterministicSigning.Resolves w.1.2
      (referenceJob SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 job) bits →
      DeterministicSigning.Resolves (coverCacheAt (SigningGuessProof.RawCommitmentInput x.1) z.1.2 w.2)
        (referenceJob SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 job) bits := by
    intro job hjob bits hbits
    simp only [bottomJobs, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
      List.mem_singleton] at hjob
    rcases hjob with (⟨k, l, rfl⟩ | ⟨k, rfl⟩) | rfl
    · exact resolves_lift_bound _ _ (referenceJob_noCommitment x _ fun _ h => by cases h) hT bits hbits
    · obtain ⟨u, hu⟩ := commitmentJob_resolves x hzres (bottomKey b k)
      exact resolves_transfer hu hbits hzc hzfin hwrec
    · exact resolves_lift_bound _ _ (referenceJob_noCommitment x _ fun _ h => by cases h) hT bits hbits
  have hcover : DeterministicSigning.Resolves
      (coverCacheAt (SigningGuessProof.RawCommitmentInput x.1) z.1.2 w.2)
      (referenceTree SigningHitProof.forestHash (SigningHitProof.forestValue x.2.1) x.1 top (.bottom b))
      w.1.1 := by
    have hR' := hR
    unfold referenceTree ceremonyOutput at hR' ⊢
    refine resolves_lift_bind ?_ ?_ _ hR'
    · intro outputs houtputs
      obtain ⟨values, hvalues, rfl⟩ := houtputs.of_map
      exact (resolves_mapM_lift _ _ hjob values hvalues).map some
    intro outputs _ v hv
    refine resolves_lift_bound _ _ ?_ hT v hv
    have hq := fun {α : Type} (oa : OracleComp HashSpec α)
        (h : NoCall (fun input => SigningGuessProof.RawCommitmentInput (C := C) x.1 (.hash input)) oa) =>
      forestHash_noCall _ oa h
    have hm := fun lay key payload => not_rawCommitment_tweakable (C := C) x.1 x.1 (.message lay key) payload
    rcases outputs with _ | outputs
    · exact isQueryBoundP_pure _ _ _
    dsimp only
    refine isQueryBoundP_bind (n := 0) (m := 0)
      (hq _ (merkleNode_noCall x.1 _ (structural_not_commitment x.1) _ _ _ _)) fun root _ => ?_
    refine isQueryBoundP_bind (n := 0) (m := 0) (hq _ ?_) fun base _ => ?_
    · unfold Verification.oracleHashWithHash
      refine noCall_map _ _ (noCall_query _ _ fun h => ?_)
      obtain ⟨e, ρ, he⟩ := (rawCommitmentInput_hash_iff x.1 _).1 h
      exact SigningGuessProof.commitmentInput_ne_randomizerInput x.1 e _ _ ρ _ _ he
    refine isQueryBoundP_bind (n := 0) (m := 0)
      (hq _ (grind_noCall x.1 _ _ _ _ _ (messageDigest_noCall x.1 _ _ _ _ (hm _ _)) _ _)) fun selected _ => ?_
    rcases selected with _ | ⟨randomness, encoding⟩
    · exact isQueryBoundP_pure _ _ _
    dsimp only
    refine isQueryBoundP_bind (n := 0) (m := 0) ((isQueryBoundP_map_iff _ _ _).2
      (mapM_bound_zero_of_mem _ _ _ fun job hjob => ?_)) fun values _ => ?_
    · simp only [signJobs, List.mem_map, List.mem_finRange, true_and] at hjob
      obtain ⟨l, rfl⟩ := hjob
      exact referenceJob_noCommitment x _ fun _ h => by cases h
    rcases values with _ | values
    · exact isQueryBoundP_pure _ _ _
    dsimp only
    refine isQueryBoundP_bind (n := 0) (m := 0)
      (hq _ (merklePath_noCall x.1 _ (structural_not_commitment x.1) _ _ _)) fun path _ => ?_
    refine isQueryBoundP_bind (n := 0) (m := 0)
      (hq _ (layerRoot_noCall x.1 _ (structural_not_commitment x.1) _ _ _ _ (messageDigest_noCall x.1 _ _ _ _ (hm _ _) _))) fun topRoot _ => ?_
    split_ifs <;> exact isQueryBoundP_pure _ _ _
  have hle := recordReads_le_of_resolves _ ∅ z.2 _ w.1.1 (fun _ _ h => by cases h) hcover w hw
    (coverCacheAt_le _ _ _)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hread
  exact isSome_of_coverCacheAt _ (by rw [hle hv]; rfl) hrel

end SigningOwnCommit

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.coverCacheAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.coverCacheAt_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.record_le_coverCacheAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.record_le_coverCacheAt

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.coverCacheAt_irrelevant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.coverCacheAt_irrelevant

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.isSome_of_coverCacheAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.isSome_of_coverCacheAt

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.tweakableHash_noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.tweakableHash_noCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.chainWalk_noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.chainWalk_noCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.merkleNode_noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.merkleNode_noCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.merklePath_noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.merklePath_noCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.treeFold_noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.treeFold_noCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.messageDigest_noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.messageDigest_noCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.otsLeaf_noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.otsLeaf_noCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.layerRoot_noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.layerRoot_noCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.grind_noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.grind_noCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.rawCommitmentInput_hash_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.rawCommitmentInput_hash_iff

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.not_rawCommitment_tweakable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.not_rawCommitment_tweakable

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.forestHash_noCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.forestHash_noCall

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.forestValue_noCommitment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.forestValue_noCommitment

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.rawRandomizer_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.rawRandomizer_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.structural_not_commitment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.structural_not_commitment

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.referenceJob_noCommitment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.referenceJob_noCommitment

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.mapM_bound_zero_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.mapM_bound_zero_of_mem

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.resolves_mapM_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.resolves_mapM_mem

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.commitmentJob_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.commitmentJob_resolves

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnCommit.commitmentForest_covers_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnCommit.commitmentForest_covers_bottom
