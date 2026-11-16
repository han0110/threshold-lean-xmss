import ThresholdLeanXmssSecurity.Proof.SigningUnchargedLogged
import ThresholdLeanXmssSecurity.Proof.SigningSupport

/-!
# The calls at the key of the forgery

This module holds the call bounds at the key `e` of the forgery. The `SigningOwn` modules, for
example `Proof/SigningOwnStopRun.lean`, use them.

1. `NoCall p oa` says that `oa` never calls an index in `p`. It is irreducible, so that unification
   never unfolds a deep Merkle tree. `AtKey P e` holds for the bottom message digest inputs at `e`.
   The ceremonies, `eval`, `prfValue`, the Merkle path and the top layer never call such an input
   (`referenceTree_bound`, `eval_bound`). `verify_bound` shows that the verification calls only the
   forged digest input among them.
2. `message_of_signers` gives the bound message of a key that `t` operators can sign. Fewer than `t`
   are corrupt, and each release is at the bound message (`SigningGuessProof.ReleasedBound`).
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningSelectionProof

open HashSig LeanXmss ThresholdLeanXmss SigningUnchargedLoggedProof SigningPartnerBoundProof SigningHitLaneProof
  SigningCostProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

section Logged

/-- The bottom message digest inputs at key `e` of the parameter `P`. These are the encoding inputs
whose leaf index is `e`. -/
def AtKey (P : PublicParameter) (e : KeyIndex) (input : XmssSecurity.HashInput) : Prop :=
  XmssSecurity.encodingInputLeafIndex? P input = some e

theorem not_atKey_commitment (P : PublicParameter) (e e' : KeyIndex) (ρ : Digest) :
    ¬AtKey P e (commitmentInput P e' ρ) := by
  intro h
  obtain ⟨y, hy⟩ := XmssSecurity.exists_encodingInput_of_encodingInputLeafIndex?_eq_some P _ e h
  exact SigningGuessProof.commitment_ne_modelHash P P e' ρ (.encoding e) _ hy.symm

theorem not_atKey_randomizer (P : PublicParameter) (e e' : KeyIndex) (lay : Layer) (ρ : Digest)
    (payload : HashInput) : ¬AtKey P e (randomizerInput P lay e' ρ payload) := by
  intro h
  obtain ⟨y, hy⟩ := XmssSecurity.exists_encodingInput_of_encodingInputLeafIndex?_eq_some P _ e h
  exact SigningGuessProof.encodingInput_ne_randomizerInput P e e' lay y.1 y.2 ρ payload hy

end Logged

section Domains

theorem not_atKey_fields (P : PublicParameter) (e : KeyIndex) (fields : TweakFields) (payload : HashInput)
    (h : fields.tag = BitVec.ofNat 5 12 → fields.hi = BitVec.ofNat 24 0 → False) :
    ¬AtKey P e (littleEndianBytes 16 P ++ addressBytes fields ++ payload) := by
  intro hk
  obtain ⟨y, hy⟩ := XmssSecurity.exists_encodingInput_of_encodingInputLeafIndex?_eq_some P _ e hk
  have heq : XmssSecurity.bytesLE 16 P ++ XmssSecurity.fieldBytes (XmssSecurity.hashDomainFields (.encoding e)) ++
      (XmssSecurity.Concrete.encodingPayload y.1 y.2 ++ XmssSecurity.domainSuffix (.encoding e)) =
      XmssSecurity.bytesLE 16 P ++ XmssSecurity.fieldBytes ⟨fields.tag, fields.step, fields.hi, fields.lo⟩ ++
        payload := by
    erw [← XmssSecurity.Bridge.tweakableHashInput_eq]
    exact hy
  have hf := (XmssSecurity.Bridge.prefix_inj heq).2.1
  exact h (congrArg XmssSecurity.TweakFields.tag hf).symm (congrArg XmssSecurity.TweakFields.hi hf).symm

/-- A tweakable hash off the bottom message domain is at no key. -/
theorem not_atKey_tweakable (P : PublicParameter) (e : KeyIndex) (domain : HashDomain) (payload : HashInput)
    (hd : ∀ key, domain ≠ .message bottomLayer key) :
    ¬AtKey P e (tweakableHashInput P domain payload) := by
  apply not_atKey_fields
  intro htag hhi
  cases domain with
  | chain lay key step => simp [hashDomainFields, tweakFields] at htag
  | leaf lay key => simp [hashDomainFields, tweakFields] at htag
  | node lay level idx => simp [hashDomainFields, tweakFields] at htag
  | message lay key =>
    apply hd key
    have hl := lay.isLt
    simp only [hashDomainFields, tweakFields, layerHi] at hhi
    have h2 := congrArg BitVec.toNat hhi
    simp only [BitVec.toNat_ofNat] at h2
    simp only [layerCount] at hl
    congr 1
    apply Fin.ext
    simp only [bottomLayer]
    omega

end Domains

section NoCall

/-- A computation never calls an index in `p`. It is irreducible, so that unification never
unfolds a deep computation such as a Merkle tree. -/
@[irreducible] def NoCall {ι α : Type} {spec : OracleSpec ι} (p : ι → Prop) (oa : OracleComp spec α) : Prop :=
  oa.IsQueryBoundP p 0

variable {ι : Type} {spec : OracleSpec ι} (p : ι → Prop)

theorem noCall_iff {α : Type} (oa : OracleComp spec α) : NoCall p oa ↔ oa.IsQueryBoundP p 0 := by
  unfold NoCall; rfl

theorem noCall_pure {α : Type} (a : α) : NoCall p (pure a : OracleComp spec α) := by
  rw [noCall_iff]; simp

theorem noCall_bind {α β : Type} {oa : OracleComp spec α} {f : α → OracleComp spec β} (h : NoCall p oa)
    (hf : ∀ a, NoCall p (f a)) : NoCall p (oa >>= f) := by
  rw [noCall_iff] at h ⊢
  exact isQueryBoundP_bind (n := 0) (m := 0) h fun a _ => (noCall_iff p _).1 (hf a)

theorem noCall_map {α β : Type} {oa : OracleComp spec α} (f : α → β) (h : NoCall p oa) :
    NoCall p (f <$> oa) := by
  rw [noCall_iff] at h ⊢
  exact (isQueryBoundP_map_iff _ _ _).2 h

theorem noCall_query (t : ι) (ht : ¬p t) :
    NoCall p (OracleComp.lift (OracleSpec.query (spec := spec) t)) := by
  rw [noCall_iff]
  simp only [isQueryBoundP_query_iff]
  exact fun h => (ht h).elim

theorem noCall_mono {q : ι → Prop} (hpq : ∀ t, q t → p t) {α : Type} {oa : OracleComp spec α}
    (h : NoCall p oa) : NoCall q oa := by
  rw [noCall_iff] at h ⊢
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h ⊢
    have ht : ¬p t := h.1.resolve_right (by omega)
    have hqt : ¬q t := fun hq => ht (hpq t hq)
    refine ⟨Or.inl hqt, fun u => ?_⟩
    simpa [hqt] using ih u (by simpa [ht] using h.2 u)

theorem noCall_mapM {α β : Type} (xs : List α) (f : α → OracleComp spec β) (hf : ∀ a, NoCall p (f a)) :
    NoCall p (xs.mapM f) := by
  induction xs with
  | nil => exact noCall_pure p _
  | cons a xs ih =>
    simp only [List.mapM_cons]
    exact noCall_bind p (hf a) fun _ => noCall_bind p ih fun _ => noCall_pure p _

theorem noCall_sequenceFin {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp spec α), (∀ i, NoCall p (f i)) → NoCall p (OverPermutation.sequenceFin f) := by
  intro n
  induction n with
  | zero => intro f _; exact noCall_pure p _
  | succ n ih =>
    intro f hf
    rw [OverPermutation.sequenceFin]
    exact noCall_bind p (hf 0) fun _ => noCall_bind p (ih _ fun i => hf i.succ) fun _ => noCall_pure p _

end NoCall

section Bounds

variable (P : PublicParameter) (e : KeyIndex)

theorem tweakableHash_bound (domain : HashDomain) (payload : HashInput)
    (hd : ∀ key, domain ≠ .message bottomLayer key) :
    NoCall (AtKey P e) (Verification.tweakableHashWithHash P domain payload : OracleComp HashSpec Digest) := by
  unfold Verification.tweakableHashWithHash
  refine noCall_bind _ ?_ fun _ => noCall_pure _ _
  exact noCall_query _ _ (not_atKey_tweakable P e domain payload hd)

theorem chainWalk_bound (lay : Layer) (key : KeyIndex) (chain : ChainIndex) (start steps : ℕ) (value : Digest) :
    NoCall (AtKey P e) (Verification.chainWalkWithHash P lay key chain start steps value : OracleComp HashSpec Digest) := by
  induction steps with
  | zero => exact noCall_pure _ _
  | succ steps ih =>
    rw [Verification.chainWalkWithHash]
    refine noCall_bind _ ih fun previous => ?_
    split_ifs
    · exact tweakableHash_bound P e _ _ (fun _ h => by cases h)
    · exact noCall_pure _ _

theorem merkleNode_bound (lay : Layer) (ends : KeyIndex → ChainIndex → Digest) :
    ∀ level node, NoCall (AtKey P e) (merkleNode P lay ends level node) := by
  intro level
  induction level with
  | zero =>
    intro node
    exact tweakableHash_bound P e _ _ (fun _ h => by cases h)
  | succ level ih =>
    intro node
    rw [merkleNode]
    exact noCall_bind _ (ih _) fun _ => noCall_bind _ (ih _) fun _ =>
      tweakableHash_bound P e _ _ (fun _ h => by cases h)

theorem merklePath_bound (lay : Layer) (ends : KeyIndex → ChainIndex → Digest) (key : KeyIndex) :
    NoCall (AtKey P e) (merklePath P lay ends key) :=
  noCall_sequenceFin _ _ fun _ => merkleNode_bound P e lay ends _ _

theorem treeFold_bound (lay : Layer) (key : KeyIndex) (path : Fin layerHeight → Digest) :
    ∀ levels value,
      NoCall (AtKey P e) (Verification.treeFoldWithHash P lay key path levels value : OracleComp HashSpec Digest) := by
  intro levels
  induction levels with
  | zero => intro value; exact noCall_pure _ _
  | succ levels ih =>
    intro value
    rw [Verification.treeFoldWithHash]
    refine noCall_bind _ (ih _) fun _ => ?_
    split_ifs <;> exact tweakableHash_bound P e _ _ (fun _ h => by cases h)

theorem otsLeaf_top_bound (key : KeyIndex) (message : HashInput) (randomness : Randomizer)
    (values : ChainIndex → Digest) :
    NoCall (AtKey P e) (Verification.otsLeafWithHash P topLayer key message randomness values : OracleComp HashSpec _) := by
  unfold Verification.otsLeafWithHash
  refine noCall_bind _
    (tweakableHash_bound P e _ _ (fun _ h => XmssSecurity.Bridge.topLayer_ne_bottom (HashDomain.message.inj h).1))
    fun digest => ?_
  split
  · refine noCall_bind _ (noCall_sequenceFin _ _ fun _ => ?_) fun _ => ?_
    · unfold Verification.recoverChainWithHash; exact chainWalk_bound P e _ _ _ _ _ _
    · exact noCall_map _ _ (tweakableHash_bound P e _ _ (fun _ h => by cases h))
  · exact noCall_pure _ _

theorem layerRoot_top_bound (key : KeyIndex) (message : HashInput) (part : LayerSignature) :
    NoCall (AtKey P e) (Verification.layerRootWithHash P topLayer key message part : OracleComp HashSpec _) := by
  unfold Verification.layerRootWithHash
  refine noCall_bind _ (otsLeaf_top_bound P e _ _ _ _) fun leaf => ?_
  rcases leaf with _ | leaf
  · exact noCall_pure _ _
  · exact noCall_bind _ (treeFold_bound P e _ _ _ _ _) fun _ => noCall_pure _ _

theorem grind_top_bound (key : KeyIndex) (message : HashInput) (base : Randomizer) :
    ∀ attempts trial, NoCall (AtKey P e) (grind P topLayer key message base attempts trial) := by
  intro attempts
  induction attempts with
  | zero => intro trial; exact noCall_pure _ _
  | succ attempts ih =>
    intro trial
    rw [grind]
    refine noCall_bind _
      (tweakableHash_bound P e _ _ (fun _ h => XmssSecurity.Bridge.topLayer_ne_bottom (HashDomain.message.inj h).1))
      fun digest => ?_
    split
    · exact noCall_pure _ _
    · exact ih _

end Bounds

section Lift

/-- The hash queries on inputs in `Q`. -/
def HashQ (Q : HashInput → Prop) : (RoSpec C).Domain → Prop := fun t => ∃ input, t = .inl (.hash input) ∧ Q input

theorem hashQuery_bound (Q : HashInput → Prop) (q : Query C) (hq : ∀ input, q = .hash input → ¬Q input) :
    NoCall (HashQ Q) (hashQuery q) := by
  refine noCall_query _ _ ?_
  rintro ⟨input, hinput, hQ⟩
  exact hq input (by simpa using hinput) hQ

theorem tweakable_bound {α : Type} (Q : HashInput → Prop) (oa : OracleComp HashSpec α)
    (h : NoCall Q oa) : NoCall (HashQ Q) (tweakable (C := C) oa) := by
  rw [noCall_iff] at h
  induction oa using OracleComp.inductionOn with
  | pure a => simpa [tweakable] using noCall_pure (spec := RoSpec C) (HashQ Q) a
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬Q t := h.1.resolve_right (by omega)
    have hk : ∀ u, (k u).IsQueryBoundP Q 0 := fun u => by simpa [ht] using h.2 u
    change NoCall (HashQ Q) (tweakable (C := C) (Verification.oracleHashWithHash t >>= k))
    rw [tweakable_bind, tweakable_oracleHash]
    exact noCall_bind _ (hashQuery_bound Q _ (fun input h => by cases h; exact ht)) fun u => ih u (hk u)

theorem prf_bound (Q : HashInput → Prop) (seed : HashOutput) (x : Point) :
    NoCall (HashQ Q) (prf (C := C) seed x) :=
  noCall_map _ _ (hashQuery_bound Q _ (fun _ h => by cases h))

theorem prfValue_bound (Q : HashInput → Prop) (seeds : C.Term → HashOutput) (x : Point) :
    NoCall (HashQ Q) (prfValue seeds x) := by
  unfold prfValue
  exact noCall_bind _ (noCall_mapM _ _ _ fun T => prf_bound Q _ x) fun _ => noCall_pure _ _

theorem eval_bound (Q : HashInput → Prop) (keys : Keys C) (i : C.Party) (J : C.Quorum) (x : Point)
    (message : Message) : NoCall (HashQ Q) (eval keys i J x message) := by
  unfold eval
  refine noCall_bind _ (noCall_mapM _ _ _ fun T => prf_bound Q _ x) fun _ => ?_
  refine noCall_bind _ (noCall_mapM _ _ _ fun j => ?_) fun _ => noCall_pure _ _
  exact noCall_map _ _ (hashQuery_bound Q _ (fun _ h => by cases h))

end Lift

section Ceremony

variable (P : PublicParameter) (e : KeyIndex)

theorem referenceJob_bound (seeds : C.Term → HashOutput) (job : Job) :
    NoCall (HashQ (C := C) (AtKey P e)) (referenceJob tweakable (prfValue seeds) P job) := by
  unfold referenceJob
  refine noCall_bind _ (noCall_mapM _ _ _ fun x => prfValue_bound _ seeds x) fun values => ?_
  cases job.kind with
  | chainEnd key l => exact noCall_map _ _ (tweakable_bound _ _ (chainWalk_bound P e _ _ _ _ _ _))
  | chainRow key l =>
    exact noCall_bind _ (tweakable_bound _ _ (chainWalk_bound P e _ _ _ _ _ _)) fun _ =>
      noCall_bind _ (tweakable_bound _ _ (chainWalk_bound P e _ _ _ _ _ _)) fun _ =>
      noCall_bind _ (tweakable_bound _ _ (chainWalk_bound P e _ _ _ _ _ _)) fun _ => noCall_pure _ _
  | chainValue key l p => exact noCall_map _ _ (tweakable_bound _ _ (chainWalk_bound P e _ _ _ _ _ _))
  | commitment key =>
    refine noCall_map _ _ ?_
    change NoCall _ (tweakable (C := C) (Verification.oracleHashWithHash _))
    rw [tweakable_oracleHash]
    exact hashQuery_bound _ _ (fun _ h => by cases h; exact not_atKey_commitment P e key _)
  | randomizer => exact noCall_pure _ _

theorem run_bound (seeds : C.Term → HashOutput) (jobs : List Job) :
    NoCall (HashQ (C := C) (AtKey P e)) (some <$> jobs.mapM (referenceJob tweakable (prfValue seeds) P)) :=
  noCall_map _ _ (noCall_mapM _ _ _ fun job => referenceJob_bound P e seeds job)

set_option maxRecDepth 100000 in
theorem referenceTree_bound (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree) :
    NoCall (HashQ (C := C) (AtKey P e)) (referenceTree tweakable (prfValue seeds) P top tree) := by
  unfold referenceTree ceremonyOutput
  cases tree with
  | top =>
    refine noCall_bind _ (run_bound P e seeds _) fun outputs => ?_
    rcases outputs with _ | outputs
    · exact noCall_pure _ _
    exact noCall_bind _ (tweakable_bound _ _ (merkleNode_bound P e _ _ _ _)) fun _ => noCall_pure _ _
  | bottom b =>
    refine noCall_bind _ (run_bound P e seeds _) fun outputs => ?_
    rcases outputs with _ | outputs
    · exact noCall_pure _ _
    refine noCall_bind _ (tweakable_bound _ _ (merkleNode_bound P e _ _ _ _)) fun root => ?_
    refine noCall_bind _ ?_ fun base => ?_
    · beta_reduce
      rw [tweakable_map]
      refine noCall_map _ _ ?_
      rw [tweakable_oracleHash]
      exact hashQuery_bound _ _ (fun _ h => by cases h; exact not_atKey_randomizer P e _ _ _ _)
    refine noCall_bind _ (tweakable_bound _ _ (grind_top_bound P e _ _ _ _ _)) fun found => ?_
    rcases found with _ | ⟨randomness, encoding⟩
    · exact noCall_pure _ _
    refine noCall_bind _ (run_bound P e seeds _) fun values => ?_
    rcases values with _ | values
    · exact noCall_pure _ _
    refine noCall_bind _ (tweakable_bound _ _ (merklePath_bound P e _ _ _)) fun path => ?_
    refine noCall_bind _ (tweakable_bound _ _ (layerRoot_top_bound P e _ _ _)) fun topRoot => ?_
    split_ifs <;> exact noCall_pure _ _

end Ceremony

section Verify

variable (P : PublicParameter) (e : KeyIndex)

/-- The verification calls at key `e` only the digest input of the forgery. -/
theorem verify_bound (root : Digest) (message : Message) (signature : Signature) :
    NoCall (fun input => AtKey P e input ∧ input ≠ XmssSecurity.Concrete.CacheView.encodingInput P
        signature.leafIndex (message, (signature.layers bottomLayer).randomizer))
      (Verification.verifyWithHash ⟨root, P⟩ message signature : OracleComp HashSpec Bool) := by
  unfold Verification.verifyWithHash Verification.layerRootWithHash Verification.otsLeafWithHash
  dsimp only
  simp only [XmssSecurity.Bridge.keyAt_bottom signature.leafIndex]
  refine noCall_bind _ (noCall_bind _ (noCall_bind _ ?_ fun digest => ?_) fun leaf => ?_) fun bottomRoot => ?_
  · unfold Verification.messageDigestWithHash Verification.tweakableHashWithHash
    refine noCall_bind _ (noCall_query _ _ ?_) fun _ => noCall_pure _ _
    rintro ⟨-, hne⟩
    exact hne (XmssSecurity.Bridge.message_input P _ message _)
  · split
    · refine noCall_bind _ (noCall_sequenceFin _ _ fun _ => ?_) fun _ => ?_
      · unfold Verification.recoverChainWithHash
        exact noCall_mono _ (fun _ h => h.1) (chainWalk_bound P e _ _ _ _ _ _)
      · exact noCall_map _ _ (noCall_mono _ (fun _ h => h.1) (tweakableHash_bound P e _ _ (fun _ h => by cases h)))
    · exact noCall_pure _ _
  · rcases leaf with _ | leaf
    · exact noCall_pure _ _
    · exact noCall_bind _ (noCall_mono _ (fun _ h => h.1) (treeFold_bound P e _ _ _ _ _)) fun _ => noCall_pure _ _
  · rcases bottomRoot with _ | bottomRoot
    · exact noCall_pure _ _
    · refine noCall_bind _ (noCall_mono _ (fun _ h => h.1) (layerRoot_top_bound P e _ _ _)) fun topRoot => ?_
      rcases topRoot with _ | topRoot <;> exact noCall_pure _ _

theorem loggedTweakable_bound (Q : HashInput → Prop) (st : TsigState C) (trees : Finset (Fin (2 ^ layerHeight)))
    {α : Type} (oa : OracleComp HashSpec α) (h : NoCall Q oa) :
    NoCall (HashQ Q) (SigningGuessLinkProof.loggedTweakable P st trees oa) := by
  rw [noCall_iff] at h ⊢
  unfold SigningGuessLinkProof.loggedTweakable
  refine IsQueryBoundP.simulateQ_run_StateT_of_step h (fun t s => ?_) []
  split_ifs with ht
  · simp only [SigningGuessLinkProof.logImpl, StateT.run_mk]
    rw [isQueryBoundP_map_iff]
    change (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl (.hash t)))).IsQueryBoundP _ 1
    simp only [isQueryBoundP_query_iff]
    omega
  · simp only [SigningGuessLinkProof.logImpl, StateT.run_mk]
    rw [isQueryBoundP_map_iff, ← noCall_iff]
    exact hashQuery_bound Q _ (fun _ h => by cases h; exact ht)

end Verify

section World

/-- The free-copy hash queries on inputs in `Q`. -/
def FreeQ (Q : HashInput → Prop) : (WorldSpec C).Domain → Prop :=
  fun t => ∃ input, t = .inr (.inr (.inl (.hash input))) ∧ Q input

theorem noCall_liftFree (Q : HashInput → Prop) {α : Type} (oa : OracleComp (RoSpec C) α)
    (h : NoCall (HashQ Q) oa) : NoCall (FreeQ Q) (SigningSecurityProof.liftFree oa) := by
  rw [noCall_iff] at h
  induction oa using OracleComp.inductionOn with
  | pure a =>
    have h : (SigningSecurityProof.liftFree (pure a : OracleComp (RoSpec C) α)) = pure a := by
      simp [SigningSecurityProof.liftFree, free]
    rw [noCall_iff, ← noCall_iff, h]
    exact noCall_pure _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬HashQ Q t := h.1.resolve_right (by omega)
    have hk : ∀ u, (k u).IsQueryBoundP (HashQ Q) 0 := fun u => by simpa [ht] using h.2 u
    simp only [SigningSecurityProof.liftFree, liftComp_bind, free_bind]
    refine noCall_bind _ ?_ fun u => ih u (hk u)
    rw [free]
    erw [liftComp_query, simulateQ_query]
    simp only [OracleQuery.input_query]
    refine noCall_query _ _ ?_
    rintro ⟨input, hinput, hQ⟩
    have h2 : t = .inl (.hash input) := Sum.inr_injective (Sum.inr_injective hinput)
    exact ht ⟨input, h2, hQ⟩

end World

section Round2

theorem run_liftM {ι σ α : Type} {spec : OracleSpec ι} (p : OracleComp spec α) (st : σ) :
    (liftM p : StateT σ (OracleComp spec) α).run st = (fun a => (a, st)) <$> p := by
  rw [map_eq_bind_pure_comp]; rfl

theorem receiptDealt_value (x : SigningSecurityProof.Keys3 C) (top : TopTree) (point : Point) :
    (SigningGuessProof.receiptDealt x top).value point = SigningSecurityProof.liftFree (prfValue x.2.1 point) := rfl

theorem receiptDealt_part (x : SigningSecurityProof.Keys3 C) (top : TopTree) (i : C.Party) (J : C.Quorum)
    (point : Point) (message : Message) :
    (SigningGuessProof.receiptDealt x top).part i J point message =
      SigningSecurityProof.liftFree (eval (dealtKeys x.1 x.2.1 x.2.2 i) i J point message) := rfl

theorem bottom_noCall (x : SigningSecurityProof.Keys3 C) (top : TopTree) (e : KeyIndex) (b : Fin (2 ^ layerHeight)) :
    NoCall (FreeQ (AtKey x.1 e)) ((SigningGuessProof.receiptDealt x top).bottom b) := by
  rw [SigningGuessProof.receiptDealt_bottom]
  exact noCall_map _ _ (noCall_liftFree _ _ (referenceTree_bound x.1 e x.2.1 top _))

/-- Reusing a stored bottom tree makes no calls; a fresh build has the same bound. -/
theorem bottomOnce_noCall (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (e : KeyIndex) (b : Fin (2 ^ layerHeight)) (st : TsigState C) :
    NoCall (FreeQ (AtKey x.1 e)) ((bottomOnce (SigningGuessProof.receiptDealt x top) b).run st) := by
  simp only [bottomOnce, StateT.run_bind, StateT.run_get, pure_bind]
  cases ht : st.trees b with
  | some stored => exact noCall_pure _ _
  | none =>
    simp only [StateT.run_bind, run_liftM, bind_map_left, StateT.run_modify,
      StateT.run_pure, pure_bind]
    exact noCall_bind _ (bottom_noCall x top e b) fun _ => noCall_pure _ _

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem tsigOracles_noCall (x : SigningSecurityProof.Keys3 C) (top : TopTree) (e : KeyIndex)
    (q : (TsigSpec C).Domain) (hq : ∀ i J e' message' parts, q ≠ .round2 i J e' message' parts) (st : TsigState C) :
    NoCall (FreeQ (AtKey x.1 e)) ((tsigOracles (fun oa => SigningCoreProof.honestLift oa)
      (SigningGuessProof.receiptDealt x top) q).run st) := by
  cases q with
  | corrupt i =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact noCall_pure _ _
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure]
      exact noCall_pure _ _
  | tree b =>
    simp only [tsigOracles, StateT.run_bind]
    refine noCall_bind _ (bottomOnce_noCall x top e b st) fun found => ?_
    rcases found with ⟨_ | tree, st'⟩
    · exact noCall_pure _ _
    · simp only [StateT.run_bind, run_liftM, bind_map_left, StateT.run_pure]
      refine noCall_bind _ ?_ fun _ => noCall_pure _ _
      rw [receiptDealt_value]
      exact noCall_liftFree _ _ (prfValue_bound _ _ _)
  | round1 i J e' message' =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact noCall_pure _ _
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_map, run_liftM, Functor.map_map]
      erw [StateT.run_map]
      simp only [run_liftM, Functor.map_map]
      refine noCall_map _ _ ?_
      rw [receiptDealt_part]
      exact noCall_liftFree _ _ (eval_bound _ _ _ _ _ _)
  | round2 i J e' message' parts => exact absurd rfl (hq i J e' message' parts)

theorem gameOracles_storedTreeRuns (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (st : TsigState C) (s : HashCache C × ℕ)
    (hinv : SigningGuessProof.StoredTreeRuns prims x top s.1 st)
    (r : ((LocalSpec C + TsigSpec C).Range t × TsigState C) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((SigningCoreProof.gameOracles (SigningGuessProof.receiptDealt x top) t).run st)).run s)) :
    SigningGuessProof.StoredTreeRuns prims x top r.2.1 r.1.2 := by
  rw [← SigningGuessProof.signingWithReceipt_forget] at hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨out, hout, rfl⟩ := hr
  exact SigningGuessProof.signingWithReceipt_storedTreeRuns prims x top st t s hinv out hout

end Round2

section Finish

theorem message_of_signers (st : TsigState C) (hR : SigningGuessProof.ReleasedBound st)
    (hc : st.corrupt.card ≤ C.t - 1) (e : KeyIndex) (message : Message)
    (h : ¬(signersAt st e message).card < C.t) : st.bound e = some message := by
  by_contra hb
  apply h
  have hempty : ((st.released.filter fun r => r.1 = e ∧ r.2.1 = message).map (·.2.2)).toFinset = ∅ := by
    rw [List.toFinset_eq_empty_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    rintro ⟨e', message', i⟩ hmem hd
    simp only [decide_eq_true_eq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    exact hb (hR _ _ _ hmem)
  unfold signersAt
  rw [hempty, Finset.union_empty]
  have := C.one_le_t
  omega

end Finish

section Main

theorem tsigFinishLogged_state (dealt : Dealt C (OracleComp (WorldSpec C))) (trees : Finset (Fin (2 ^ layerHeight)))
    (forgery : Forgery) (st : TsigState C)
    (r : (Bool × TsigState C × Forgery) × List (SigningOpeningProof.HiddenKey × Digest))
    (hr : r ∈ support (SigningGuessLinkProof.tsigFinishLogged dealt trees (forgery, st))) :
    r.1.2 = (st, forgery) := by
  have h : r.1 ∈ support (SigningCoreProof.tsigFinish dealt (forgery, st)) := by
    rw [← SigningGuessLinkProof.tsigFinishLogged_forget dealt trees, support_map]
    exact ⟨r, hr, rfl⟩
  exact SigningGuessProof.tsigFinish_state dealt forgery st r.1 h

end Main

end SigningSelectionProof

end ThresholdLeanXmssSecurity
