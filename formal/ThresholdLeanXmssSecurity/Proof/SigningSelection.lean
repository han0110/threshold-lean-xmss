import ThresholdLeanXmssSecurity.Proof.SigningUnchargedLogged
import ThresholdLeanXmssSecurity.Proof.SigningSupport

/-!
# The classification of the honest calls at the key of the forgery

This module proves `SigningUnchargedLoggedProof.SelectionClassification`, and with it
`hiddenCoreAt_of_flagCoupling`, which needs only `UnchargedFlagCoupling`.

`allowed_of_joint` proves a stronger form that does not need the call order. Each free-copy call at
the key `e` of the forgery with a valid digest, anywhere in the log, is on the selected input or on
the forged input, unless `AlternativeCommitment` holds.

## Steps

1. `Adds ok l l'` says that a run appends to the log only hash entries that satisfy `ok`.
2. `NoCall p oa` says that `oa` never calls an index in `p`. It is irreducible, so that unification
   never unfolds a deep Merkle tree. The ceremonies, `eval`, `prfValue`, the Merkle path and the top
   layer never call an input at a bottom key (`referenceTree_bound`, `eval_bound`).
   `verify_bound` shows that the verification calls at `e` only the forged input.
3. `adds_grind` shows that a grind trial with a valid digest is the trial that the grind returns.
   `adds_signCodeword` lifts it to `signCodeword`.
4. `Selects` says that each accepted search at `e` for the bound message selects the selected
   randomness. `selects_of_final` proves it outside `AlternativeCommitment`, with
   `SigningGuessProof.ReceiptRuns.canonical` and `SigningGuessProof.ReceiptRuns.selected`.
5. `adds_opening_step` classifies one call of `openingOracles`. Round 2 at `e` runs only for the
   message in `st.bound e`, which is write-once (`StateGrows`). `logged_simulateQ_inv` carries this
   over the adversary run.
6. `adds_finish` classifies the verification and the freshness check. `honestSignature` runs only if
   `t` operators can sign. Fewer than `t` are corrupt, and each release is at the bound message
   (`SigningGuessProof.ReleasedBound`). So it signs the bound message.

Round 1 reveals the randomizer value. The proof uses no hidden randomizer start after round 1. An
adversary call is on the counted copy, so it is never a free-copy entry.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningSelectionProof

open LeanXmss ThresholdLeanXmss SigningUnchargedLoggedProof SigningPartnerBoundProof SigningHitLaneProof
  SigningCostProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

section Logged

/-- The log grows by new calls, and each new hash entry satisfies `ok`. -/
def Adds (ok : Entry → Prop) (l l' : LoggedState C) : Prop :=
  ∃ new : QueryLog (WorldSpec C), l'.2 = l.2 ++ new ∧ ∀ entry ∈ new.filterMap hashEntry, ok entry

theorem adds_refl (ok : Entry → Prop) (l : LoggedState C) : Adds ok l l :=
  ⟨[], by simp, by simp⟩

theorem Adds.trans {ok : Entry → Prop} {l l' l'' : LoggedState C} (h : Adds ok l l') (h' : Adds ok l' l'') :
    Adds ok l l'' := by
  obtain ⟨new, hl, hok⟩ := h
  obtain ⟨new', hl', hok'⟩ := h'
  refine ⟨new ++ new', by rw [hl', hl, List.append_assoc], fun entry hentry => ?_⟩
  rw [List.filterMap_append, List.mem_append] at hentry
  rcases hentry with hentry | hentry
  · exact hok entry hentry
  · exact hok' entry hentry

theorem Adds.mono {ok ok' : Entry → Prop} (hmono : ∀ entry, ok entry → ok' entry) {l l' : LoggedState C}
    (h : Adds ok l l') : Adds ok' l l' := by
  obtain ⟨new, hl, hok⟩ := h
  exact ⟨new, hl, fun entry hentry => hmono entry (hok entry hentry)⟩

theorem logged_bind {α β : Type} (oa : OracleComp (WorldSpec C) α) (f : α → OracleComp (WorldSpec C) β)
    (l : LoggedState C) (z : β × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims) (oa >>= f)).run l)) :
    ∃ p ∈ support ((simulateQ (loggedImpl prims) oa).run l),
      z ∈ support ((simulateQ (loggedImpl prims) (f p.1)).run p.2) := by
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  exact hz

theorem logged_map {α β : Type} (oa : OracleComp (WorldSpec C) α) (f : α → β)
    (l : LoggedState C) (z : β × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims) (f <$> oa)).run l)) :
    ∃ p ∈ support ((simulateQ (loggedImpl prims) oa).run l), z = (f p.1, p.2) := by
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  exact ⟨p, hp, rfl⟩

theorem logged_count {α : Type} (oa : OracleComp (WorldSpec C) α) (l : LoggedState C)
    (z : α × LoggedState C) (hz : z ∈ support ((simulateQ (loggedImpl prims) oa).run l)) :
    (z.1, z.2.1) ∈ support ((simulateQ (SigningCacheProof.countImpl prims) oa).run l.1) := by
  rw [← SigningCoreProof.simulateQ_run_forget (loggedImpl prims) (SigningCacheProof.countImpl prims)
    (fun t s b => by simp [loggedImpl, Functor.map_map]) oa l.1 l.2, support_map]
  exact ⟨z, hz, rfl⟩

/-- One free call of `H` on a hash input adds its one entry. -/
theorem adds_hashQuery (input : XmssSecurity.HashInput) (l : LoggedState C) (z : HashOutput × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims)
      (SigningSecurityProof.liftFree (hashQuery (.hash input)))).run l)) :
    Adds (fun entry => entry = (input, XmssSecurity.truncateHash z.1, true)) l z.2 := by
  have hz' : z ∈ support ((loggedImpl prims (.inr (.inr (.inl (.hash input))))).run l) := by
    rw [SigningSecurityProof.liftFree, hashQuery, free] at hz
    erw [liftComp_query, simulateQ_query] at hz
    simp at hz
    exact hz
  simp only [loggedImpl, StateT.run_mk, support_map] at hz'
  obtain ⟨q, -, rfl⟩ := hz'
  refine ⟨QueryLog.singleton _ q.1, rfl, fun entry hentry => ?_⟩
  simp [QueryLog.singleton, hashEntry] at hentry
  exact hentry

theorem liftFree_tweakable_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    SigningSecurityProof.liftFree (tweakable (C := C) (oa >>= f)) =
      SigningSecurityProof.liftFree (tweakable (C := C) oa) >>= fun a =>
        SigningSecurityProof.liftFree (tweakable (C := C) (f a)) := by
  rw [tweakable_bind, SigningSecurityProof.liftFree, liftComp_bind, free_bind]

theorem logged_liftFree_tweakable_pure {α : Type} (a : α) (l : LoggedState C) :
    support ((simulateQ (loggedImpl prims) (SigningSecurityProof.liftFree (tweakable (C := C)
      (pure a : OracleComp HashSpec α)))).run l) = {(a, l)} := by
  simp [tweakable, SigningSecurityProof.liftFree, free]
  rfl

/-- A grind trial at key `e` with a valid digest is the trial that the grind returns. -/
theorem adds_grind (P : PublicParameter) (e : KeyIndex) (message : Message) (base : Randomness) :
    ∀ attempts trial (l : LoggedState C) z,
      z ∈ support ((simulateQ (loggedImpl prims) (SigningSecurityProof.liftFree (tweakable (C := C)
        (grind P bottomLayer e (bytesLE 32 message) base attempts trial)))).run l) →
      Adds (fun entry => entry.2.2 = true ∧ ∃ randomness,
        entry.1 = XmssSecurity.Concrete.CacheView.encodingInput P e (message, randomness) ∧
        (XmssSecurity.TargetSum.ValidDigest entry.2.1 → ∃ encoding, z.1 = some (randomness, encoding))) l z.2 := by
  intro attempts
  induction attempts with
  | zero =>
    intro trial l z hz
    simp [grind, tweakable, SigningSecurityProof.liftFree, free] at hz
    subst hz
    exact adds_refl _ _
  | succ attempts ih =>
    intro trial l z hz
    rw [grind, liftFree_tweakable_bind] at hz
    obtain ⟨p, hp, hz⟩ := logged_bind prims _ _ l z hz
    rw [Concrete.messageDigest, Concrete.tweakableHash, liftFree_tweakable_bind] at hp
    obtain ⟨q, hq, hp⟩ := logged_bind prims _ _ l p hp
    rw [logged_liftFree_tweakable_pure] at hp
    rw [tweakable_oracleHash] at hq
    have hfirst := adds_hashQuery prims _ l q hq
    subst hp
    have hinput : tweakableHashInput P (HashDomain.message bottomLayer e)
        (bytesLE 32 message ++ bytesLE 16 (base + BitVec.ofNat digestBits trial)) =
        XmssSecurity.Concrete.CacheView.encodingInput P e (message, base + BitVec.ofNat digestBits trial) :=
      XmssSecurity.Bridge.message_input P e message _
    cases hd : Codeword.decode (truncateHash q.1) with
    | some encoding =>
      simp only [hd] at hz
      rw [logged_liftFree_tweakable_pure] at hz
      subst hz
      refine hfirst.mono fun entry hentry => ?_
      subst hentry
      exact ⟨rfl, _, hinput, fun _ => ⟨encoding, rfl⟩⟩
    | none =>
      simp only [hd] at hz
      refine Adds.trans (hfirst.mono fun entry hentry => ?_) (ih _ _ z hz)
      subst hentry
      refine ⟨rfl, _, hinput, fun hvalid => ?_⟩
      obtain ⟨encoding, hencoding⟩ := hvalid
      rw [← XmssSecurity.Bridge.decode_eq] at hencoding
      exact absurd (hd.symm.trans hencoding) (by simp)

/-- The hash inputs at key `e` of the parameter `P`. -/
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

/-- A free call of `signCodeword` at key `e` with a valid digest is on its selected input. -/
theorem adds_signCodeword (P : PublicParameter) (commitment : Digest) (e' : KeyIndex) (message : Message)
    (ρ : Digest) (e : KeyIndex) (l : LoggedState C) (z : Option (Randomness × Encoding) × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims)
      (SigningSecurityProof.liftFree (signCodeword P commitment e' message ρ))).run l)) :
    Adds (fun entry => entry.2.2 = true ∧ (AtKey P e entry.1 → XmssSecurity.TargetSum.ValidDigest entry.2.1 →
      e' = e ∧ ∃ randomness encoding, z.1 = some (randomness, encoding) ∧
        entry.1 = XmssSecurity.Concrete.CacheView.encodingInput P e (message, randomness))) l z.2 := by
  unfold signCodeword at hz
  rw [liftFree_tweakable_bind] at hz
  obtain ⟨p, hp, hz⟩ := logged_bind prims _ _ l z hz
  rw [tweakable_oracleHash] at hp
  refine Adds.trans ((adds_hashQuery prims _ l p hp).mono fun entry hentry => ?_) ?_
  · subst hentry
    exact ⟨rfl, fun hk => (not_atKey_commitment P e e' ρ hk).elim⟩
  dsimp only at hz
  split_ifs at hz with hopen
  · rw [logged_liftFree_tweakable_pure] at hz
    subst hz
    exact adds_refl _ _
  rw [liftFree_tweakable_bind] at hz
  obtain ⟨q, hq, hz⟩ := logged_bind prims _ _ _ z hz
  rw [tweakable_oracleHash] at hq
  refine Adds.trans ((adds_hashQuery prims _ _ q hq).mono fun entry hentry => ?_) ?_
  · subst hentry
    exact ⟨rfl, fun hk => (not_atKey_randomizer P e e' bottomLayer ρ _ hk).elim⟩
  refine (adds_grind prims P e' message _ _ _ _ z hz).mono fun entry hentry => ?_
  obtain ⟨hfree, randomness, hinput, hresult⟩ := hentry
  refine ⟨hfree, fun hk hvalid => ?_⟩
  rw [hinput, AtKey, XmssSecurity.encodingInputLeafIndex?_encodingInput] at hk
  obtain rfl := Option.some.inj hk
  obtain ⟨encoding, henc⟩ := hresult hvalid
  exact ⟨rfl, randomness, encoding, henc, hinput⟩

end Logged

section Domains

theorem not_atKey_fields (P : PublicParameter) (e : KeyIndex) (fields : TweakFields) (payload : HashInput)
    (h : fields.tag = BitVec.ofNat 5 12 → fields.hi = BitVec.ofNat 24 0 → False) :
    ¬AtKey P e (bytesLE 16 P ++ fieldBytes fields ++ payload) := by
  intro hk
  obtain ⟨y, hy⟩ := XmssSecurity.exists_encodingInput_of_encodingInputLeafIndex?_eq_some P _ e hk
  have heq : XmssSecurity.bytesLE 16 P ++ XmssSecurity.fieldBytes (XmssSecurity.hashDomainFields (.encoding e)) ++
      (XmssSecurity.Concrete.encodingPayload y.1 y.2 ++ XmssSecurity.domainSuffix (.encoding e)) =
      XmssSecurity.bytesLE 16 P ++ XmssSecurity.fieldBytes ⟨fields.tag, fields.step, fields.hi, fields.lo⟩ ++
        payload := by
    rw [← XmssSecurity.Bridge.tweakableHashInput_eq]
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
    simp only [numLayers] at hl
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
    ∀ {n : ℕ} (f : Fin n → OracleComp spec α), (∀ i, NoCall p (f i)) → NoCall p (Concrete.sequenceFin f) := by
  intro n
  induction n with
  | zero => intro f _; exact noCall_pure p _
  | succ n ih =>
    intro f hf
    rw [Concrete.sequenceFin]
    exact noCall_bind p (hf 0) fun _ => noCall_bind p (ih _ fun i => hf i.succ) fun _ => noCall_pure p _

end NoCall

section Bounds

variable (P : PublicParameter) (e : KeyIndex)

theorem tweakableHash_bound (domain : HashDomain) (payload : HashInput)
    (hd : ∀ key, domain ≠ .message bottomLayer key) :
    NoCall (AtKey P e) (Concrete.tweakableHash P domain payload : OracleComp HashSpec Digest) := by
  unfold Concrete.tweakableHash
  refine noCall_bind _ ?_ fun _ => noCall_pure _ _
  exact noCall_query _ _ (not_atKey_tweakable P e domain payload hd)

theorem chainWalk_bound (lay : Layer) (key : KeyIndex) (chain : ChainIndex) (start steps : ℕ) (value : Digest) :
    NoCall (AtKey P e) (Concrete.chainWalk P lay key chain start steps value : OracleComp HashSpec Digest) := by
  induction steps with
  | zero => exact noCall_pure _ _
  | succ steps ih =>
    rw [Concrete.chainWalk]
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
      NoCall (AtKey P e) (Concrete.treeFold P lay key path levels value : OracleComp HashSpec Digest) := by
  intro levels
  induction levels with
  | zero => intro value; exact noCall_pure _ _
  | succ levels ih =>
    intro value
    rw [Concrete.treeFold]
    refine noCall_bind _ (ih _) fun _ => ?_
    split_ifs <;> exact tweakableHash_bound P e _ _ (fun _ h => by cases h)

theorem otsLeaf_top_bound (key : KeyIndex) (message : HashInput) (randomness : Randomness)
    (values : ChainIndex → Digest) :
    NoCall (AtKey P e) (Concrete.otsLeaf P topLayer key message randomness values : OracleComp HashSpec _) := by
  unfold Concrete.otsLeaf
  refine noCall_bind _
    (tweakableHash_bound P e _ _ (fun _ h => XmssSecurity.Bridge.topLayer_ne_bottom (HashDomain.message.inj h).1))
    fun digest => ?_
  split
  · refine noCall_bind _ (noCall_sequenceFin _ _ fun _ => ?_) fun _ => ?_
    · unfold Concrete.recoverChain; exact chainWalk_bound P e _ _ _ _ _ _
    · exact noCall_map _ _ (tweakableHash_bound P e _ _ (fun _ h => by cases h))
  · exact noCall_pure _ _

theorem layerRoot_top_bound (key : KeyIndex) (message : HashInput) (part : LayerSignature) :
    NoCall (AtKey P e) (Concrete.layerRoot P topLayer key message part : OracleComp HashSpec _) := by
  unfold Concrete.layerRoot
  refine noCall_bind _ (otsLeaf_top_bound P e _ _ _ _) fun leaf => ?_
  rcases leaf with _ | leaf
  · exact noCall_pure _ _
  · exact noCall_bind _ (treeFold_bound P e _ _ _ _ _) fun _ => noCall_pure _ _

theorem grind_top_bound (key : KeyIndex) (message : HashInput) (base : Randomness) :
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
    change NoCall (HashQ Q) (tweakable (C := C) (Concrete.oracleHash t >>= k))
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
    change NoCall _ (tweakable (C := C) (Concrete.oracleHash _))
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
        signature.leafIndex (message, (signature.layers bottomLayer).randomness))
      (Concrete.verify ⟨root, P⟩ message signature : OracleComp HashSpec Bool) := by
  unfold Concrete.verify Concrete.layerRoot Concrete.otsLeaf
  dsimp only
  simp only [XmssSecurity.Bridge.keyAt_bottom]
  refine noCall_bind _ (noCall_bind _ (noCall_bind _ ?_ fun digest => ?_) fun leaf => ?_) fun bottomRoot => ?_
  · unfold Concrete.messageDigest Concrete.tweakableHash
    refine noCall_bind _ (noCall_query _ _ ?_) fun _ => noCall_pure _ _
    rintro ⟨-, hne⟩
    exact hne (XmssSecurity.Bridge.message_input P _ message _)
  · split
    · refine noCall_bind _ (noCall_sequenceFin _ _ fun _ => ?_) fun _ => ?_
      · unfold Concrete.recoverChain
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
      simp [SigningSecurityProof.liftFree, free]; rfl
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

theorem noCall_counted (Q : HashInput → Prop) {α : Type} (oa : OracleComp (SimulatorSpec C) α) :
    NoCall (FreeQ Q) (counted (C := C) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    have h : counted (C := C) (pure a : OracleComp (SimulatorSpec C) α) = pure a := by
      simp [counted]; rfl
    rw [h]
    exact noCall_pure _ _
  | query_bind t k ih =>
    have h : counted (C := C) (liftM (OracleSpec.query t) >>= k) =
        OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inl t)) >>= fun u => counted (k u) := by
      simp [counted]; rfl
    rw [h]
    refine noCall_bind _ (noCall_query _ _ ?_) fun u => ih u
    rintro ⟨input, hinput, -⟩
    simp at hinput

/-- A world computation that never calls a `bad` free input adds only entries off `bad` on the free copy. -/
theorem adds_world (bad : HashInput → Prop) {α : Type} (oa : OracleComp (WorldSpec C) α)
    (hb : NoCall (FreeQ bad) oa) :
    ∀ l, ∀ z ∈ support ((simulateQ (loggedImpl prims) oa).run l),
      Adds (fun entry => entry.2.2 = true → ¬bad entry.1) l z.2 := by
  rw [noCall_iff] at hb
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro l z hz
    simp at hz
    subst hz
    exact adds_refl _ _
  | query_bind t k ih =>
    intro l z hz
    rw [isQueryBoundP_query_bind_iff] at hb
    have ht : ¬FreeQ bad t := hb.1.resolve_right (by omega)
    have hk : ∀ u, (k u).IsQueryBoundP (FreeQ bad) 0 := fun u => by simpa [ht] using hb.2 u
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    refine Adds.trans ?_ (ih p.1 (hk p.1) p.2 z hz)
    simp only [loggedImpl, StateT.run_mk, support_map] at hp
    obtain ⟨q, -, rfl⟩ := hp
    refine ⟨QueryLog.singleton _ q.1, rfl, fun entry hentry hfree hbad => ?_⟩
    rcases t with ((n | (((input | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) | _))) | prog) |
      (n | (((input | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) | _))) <;>
      simp [QueryLog.singleton, hashEntry] at hentry
    · subst hentry; simp at hfree
    · subst hentry; exact ht ⟨input, rfl, hbad⟩

end World

section Selects

/-- Each accepted search at key `e` for `message` from a tree of the run, with caches below
`cache`, selects `randomness`. -/
def Selects (x : SigningSecurityProof.Keys3 C) (top : TopTree) (cache : HashCache C) (e : KeyIndex)
    (message : Message) (randomness : Randomness) : Prop :=
  ∀ (tree : BottomTree) (sTree : HashCache C × ℕ) (rTree : Option TreeOutput × HashCache C × ℕ)
    (sCode : HashCache C × ℕ) (rCode : Option (Randomness × Encoding) × HashCache C × ℕ)
    (candidate : Digest) (r : Randomness) (encoding : Encoding),
    rTree ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (SigningSecurityProof.liftFree
      (referenceTree tweakable (prfValue x.2.1) x.1 top (.bottom (treeOf e))))).run sTree) →
    rTree.1 = some (.bottom tree) → rTree.2.1 ≤ cache →
    rCode ∈ support ((simulateQ (SigningCacheProof.countImpl prims) (SigningSecurityProof.liftFree
      (signCodeword x.1 (tree.commitment e) e message candidate))).run sCode) →
    rCode.1 = some (r, encoding) → rCode.2.1 ≤ cache → r = randomness

theorem bound_of_selected (z : SigningDescentProof.FinalState C) (selected : Message × Randomness)
    (h : z.selected prims = some selected) : z.state.bound z.key = some selected.1 := by
  unfold SigningDescentProof.FinalState.selected at h
  cases hb : z.state.bound z.key with
  | none => rw [hb] at h; simp at h
  | some message =>
    rw [hb] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨tree, -, chosen, -, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq] at h
    rw [← h]

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem selects_of_final (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (hw : w ∈ support (jointRun prims A x)) (hwin : w.1.1.1 = (true, false))
    (hnalt : ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 w.2.1.1)
    (top : TopTree) (state : TsigState C) (forgery : Forgery) (hm : w.1.1.2 = some (top, state, forgery))
    (selected : Message × Randomness)
    (hsel : (finalOf x (w.1.1, w.2.1) top state forgery).selected prims = some selected) :
    Selects prims x top w.2.1.1 forgery.signature.leafIndex selected.1 selected.2 := by
  intro tree sTree rTree sCode rCode candidate r encoding hTree hTreeOut hTreeLe hCode hCodeOut hCodeLe
  have ho := mem_exposedRun_of_joint prims A x w hw
  have htop : TopFacts prims (SigningCacheProof.answersOf w.2.1.1) x.2.1 x.1 top := by
    obtain ⟨top', state', forgery', hm', hg, _, _⟩ :=
      SigningCacheProof.exposedRun_facts prims A x (w.1.1, w.2.1) ho hwin
    have he : top' = top := congrArg Prod.fst (Option.some.inj (hm'.symm.trans hm))
    subst top'
    obtain ⟨generated, hgen, hchain, hroot⟩ :=
      D_refTop (prims := prims) (h := SigningCacheProof.answersOf w.2.1.1) x.1 x.2.1 emptyTop
    have he : generated = top := TreeOutput.top.inj (Option.some.inj (hgen.symm.trans hg))
    subst generated
    exact ⟨hchain, hroot⟩
  have hn : ¬SigningGuessProof.OpeningMatch prims x (w.1.1, w.2.1) := fun h =>
    hnalt (SigningGuessProof.openingMatch_alternativeCommitment prims x (w.1.1, w.2.1) h)
  have hb := bound_of_selected prims _ selected hsel
  obtain ⟨J, -, hJ⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset C.Party)) (n := C.t)
    (by simp [Committee.n]; have := C.one_le_t; omega)
  let receipt : SigningGuessProof.Round2Receipt C :=
    ⟨⟨0, by simp [Committee.n]; have := C.one_le_t; omega⟩, ⟨J, hJ⟩, forgery.signature.leafIndex, selected.1,
      r, encoding, candidate, tree.commitment forgery.signature.leafIndex, fun _ => none⟩
  have hruns : SigningGuessProof.ReceiptRuns prims x top w.2.1.1 receipt :=
    ⟨tree, sTree, rTree, sCode, rCode, hTree, hTreeOut, hTreeLe, rfl, hCode, hCodeOut, hCodeLe⟩
  have hc := (SigningGuessProof.ReceiptRuns.canonical prims x (w.1.1, w.2.1) top state forgery hm htop receipt
    hruns rfl hn).1
  have hs := SigningGuessProof.ReceiptRuns.selected prims (finalOf x (w.1.1, w.2.1) top state forgery) receipt
    hruns rfl hb hc
  rw [hsel] at hs
  exact (congrArg Prod.snd (Option.some.inj hs)).symm

end Selects

section Round2

/-- A free call at key `e` with a valid digest is on `selected`. -/
def OnSel (P : PublicParameter) (e : KeyIndex) (selected : HashInput) (entry : Entry) : Prop :=
  entry.2.2 = true → AtKey P e entry.1 → XmssSecurity.TargetSum.ValidDigest entry.2.1 → entry.1 = selected

theorem logged_grows {α : Type} (oa : OracleComp (WorldSpec C) α) (l : LoggedState C) (z : α × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims) oa).run l)) : l.1.1 ≤ z.2.1.1 :=
  SigningCacheProof.countRun_grows prims oa l.1 (z.1, z.2.1) (logged_count prims oa l z hz)

theorem adds_onSel_of_noCall (P : PublicParameter) (e : KeyIndex) (selected : HashInput) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (hb : NoCall (FreeQ (AtKey P e)) oa) (l : LoggedState C)
    (z : α × LoggedState C) (hz : z ∈ support ((simulateQ (loggedImpl prims) oa).run l)) :
    Adds (OnSel P e selected) l z.2 :=
  (adds_world prims _ oa hb l z hz).mono fun _ h hfree hk => (h hfree hk).elim

theorem run_liftM {ι σ α : Type} {spec : OracleSpec ι} (p : OracleComp spec α) (st : σ) :
    (liftM p : StateT σ (OracleComp spec) α).run st = (fun a => (a, st)) <$> p := rfl

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

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem adds_round2 (x : SigningSecurityProof.Keys3 C) (top : TopTree) (cache : HashCache C) (e : KeyIndex)
    (message : Message) (randomness : Randomness) (hsel : Selects prims x top cache e message randomness)
    (st : TsigState C) (i : C.Party) (J : C.Quorum) (e' : KeyIndex) (message' : Message) (parts : C.Party → Digest)
    (l : LoggedState C) (z : ((TsigSpec C).Range (.round2 i J e' message' parts) × TsigState C) × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims) ((tsigOracles (fun oa => SigningCoreProof.honestLift oa)
      (SigningGuessProof.receiptDealt x top) (.round2 i J e' message' parts)).run st)).run l))
    (hle : z.2.1.1 ≤ cache) (hb : ∀ message'', st.bound e = some message'' → message'' = message) :
    Adds (OnSel x.1 e (XmssSecurity.Concrete.CacheView.encodingInput x.1 e (message, randomness))) l z.2 := by
  simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split at hz
  · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact adds_refl _ _
  · rename_i hguard
    have hm : e' = e → message' = message := fun he => by
      subst he
      exact hb _ (by simp only [not_or, not_not] at hguard; exact hguard.2.2)
    simp only [StateT.run_bind, run_liftM, bind_map_left] at hz
    obtain ⟨p1, hp1, hz⟩ := logged_bind prims _ _ l z hz
    refine (adds_onSel_of_noCall prims x.1 e _ _ (bottom_noCall x top e _) l p1 hp1).trans ?_
    rcases hp1t : p1.1 with _ | tree
    · rw [hp1t] at hz
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact adds_refl _ _
    rw [hp1t] at hz
    simp only [StateT.run_bind, run_liftM, bind_map_left] at hz
    obtain ⟨p2, hp2, hz⟩ := logged_bind prims _ _ _ z hz
    refine (adds_onSel_of_noCall prims x.1 e _ _ ?_ _ p2 hp2).trans ?_
    · rw [receiptDealt_part]
      exact noCall_liftFree _ _ (eval_bound _ _ _ _ _ _)
    obtain ⟨p3, hp3, hz⟩ := logged_bind prims _ _ _ z hz
    have hz3 : z.2 = p3.2 := by
      rcases hp3t : p3.1 with _ | values
      · rw [hp3t] at hz
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
      · rw [hp3t] at hz
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure, support_pure,
          Set.mem_singleton_iff] at hz
        rw [hz]
    rw [hz3]
    have hle3 : p3.2.1.1 ≤ cache := by rw [← hz3]; exact hle
    unfold signRound2With at hp3
    obtain ⟨q, hq, hp3⟩ := logged_bind prims _ _ _ p3 hp3
    have hq3 : q.2.1.1 ≤ p3.2.1.1 := logged_grows prims _ _ p3 hp3
    refine Adds.trans ((adds_signCodeword prims _ _ _ _ _ e _ q hq).mono fun entry hentry => ?_) ?_
    · obtain ⟨hfree, hvalidCase⟩ := hentry
      intro _ hk hvalid
      obtain ⟨rfl, r, encoding, hr, hinput⟩ := hvalidCase hk hvalid
      obtain rfl := hm rfl
      rw [hinput]
      obtain ⟨p0, hp0, hp1eq⟩ := logged_map prims _ _ l p1 (by
        rw [SigningGuessProof.receiptDealt_bottom] at hp1; exact hp1)
      have hout : p0.1 = some (.bottom tree) := by
        rw [hp1eq] at hp1t
        dsimp only at hp1t
        revert hp1t
        rcases p0.1 with _ | (_ | tree')
        · intro h; exact absurd h (by simp)
        · intro h; exact absurd h (by simp)
        · intro h; simp only [Option.some.injEq] at h; rw [h]
      have hTreeLe : p0.2.1.1 ≤ cache := by
        have h1 : p0.2 = p1.2 := by rw [hp1eq]
        rw [h1]
        exact (logged_grows prims _ _ p2 hp2).trans ((logged_grows prims _ _ q hq).trans (hq3.trans hle3))
      rw [hsel tree l.1 (p0.1, p0.2.1) p2.2.1 (q.1, q.2.1) _ r encoding
        (logged_count prims _ l p0 hp0) hout hTreeLe (logged_count prims _ p2.2 q hq) hr (hq3.trans hle3)]
      rfl
    refine adds_onSel_of_noCall prims x.1 e _ _ ?_ _ p3 hp3
    rcases q.1 with _ | ⟨r, encoding⟩
    · exact noCall_pure _ _
    · refine noCall_bind _ (noCall_sequenceFin _ _ fun index => ?_) fun _ => noCall_pure _ _
      split
      · refine noCall_map _ _ ?_
        beta_reduce
        rw [receiptDealt_part]
        exact noCall_liftFree _ _ (eval_bound _ _ _ _ _ _)
      · exact noCall_pure _ _

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
    simp only [tsigOracles, StateT.run_bind, run_liftM, bind_map_left]
    refine noCall_bind _ (bottom_noCall x top e b) fun tree => ?_
    rcases tree with _ | tree
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
      refine noCall_map _ _ ?_
      rw [receiptDealt_part]
      exact noCall_liftFree _ _ (eval_bound _ _ _ _ _ _)
  | round2 i J e' message' parts => exact absurd rfl (hq i J e' message' parts)

theorem logged_support {α : Type} (oa : OracleComp (WorldSpec C) α) (l : LoggedState C) (z : α × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims) oa).run l)) : z.1 ∈ support oa := by
  apply support_simulateQ_run'_subset (loggedImpl prims) oa l
  rw [StateT.run'_eq, support_map]
  exact ⟨z, hz, rfl⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- One call of `openingOracles` adds only calls at key `e` on the selected input. -/
theorem adds_opening_step (x : SigningSecurityProof.Keys3 C) (top : TopTree) (cache : HashCache C) (e : KeyIndex)
    (message : Message) (randomness : Randomness) (hsel : Selects prims x top cache e message randomness)
    (t : (LocalSpec C + TsigSpec C).Domain)
    (s : (TsigState C × Bool) × Finset (Fin (2 ^ layerHeight)) × List (SigningOpeningProof.HiddenKey × Digest))
    (l : LoggedState C) (z : ((LocalSpec C + TsigSpec C).Range t × (TsigState C × Bool) ×
      Finset (Fin (2 ^ layerHeight)) × List (SigningOpeningProof.HiddenKey × Digest)) × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims)
      ((SigningOpeningProof.openingOracles x (SigningGuessProof.receiptDealt x top) t).run s)).run l))
    (hle : z.2.1.1 ≤ cache) (hb : ∀ message'', s.1.1.bound e = some message'' → message'' = message) :
    Adds (OnSel x.1 e (XmssSecurity.Concrete.CacheView.encodingInput x.1 e (message, randomness))) l z.2 := by
  rcases t with t | q
  · refine adds_onSel_of_noCall prims x.1 e _ _ ?_ l z hz
    simp only [SigningOpeningProof.openingOracles, StateT.run_mk, SigningCoreProof.flaggedOracles]
    exact noCall_map _ _ (noCall_map _ _ (noCall_counted _ _))
  · simp only [SigningOpeningProof.openingOracles, StateT.run_mk, SigningCoreProof.flaggedOracles,
      Functor.map_map] at hz
    obtain ⟨p, hp, rfl⟩ := logged_map prims _ _ l z hz
    by_cases hq : ∃ i J e' message' parts, q = .round2 i J e' message' parts
    · obtain ⟨i, J, e', message', parts, rfl⟩ := hq
      exact adds_round2 prims x top cache e message randomness hsel s.1.1 i J e' message' parts l p hp hle hb
    · push Not at hq
      exact adds_onSel_of_noCall prims x.1 e _ _ (tsigOracles_noCall x top e q hq s.1.1) l p hp

/-- An invariant of each step of a stateful oracle, run under `loggedImpl`, holds after the run. -/
theorem logged_simulateQ_inv {ι σ α : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT σ (OracleComp (WorldSpec C)))) (Inv : σ → LoggedState C → Prop)
    (step : ∀ input state l, Inv state l →
      ∀ result ∈ support ((simulateQ (loggedImpl prims) ((handler input).run state)).run l), Inv result.1.2 result.2)
    (source : OracleComp spec α) :
    ∀ state l, Inv state l →
      ∀ result ∈ support ((simulateQ (loggedImpl prims) ((simulateQ handler source).run state)).run l),
        Inv result.1.2 result.2 := by
  induction source using OracleComp.inductionOn with
  | pure value =>
    intro state l hinv result hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst result
    exact hinv
  | query_bind input next ih =>
    intro state l hinv result hr
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind] at hr
    simp only [mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    exact ih mid.1.1 mid.1.2 mid.2 (step input state l hinv mid hmid) result hr

end Round2

section Finish

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- The honest signature at key `e` for the bound message calls at `e` only the selected input. -/
theorem adds_honestSignature (x : SigningSecurityProof.Keys3 C) (top : TopTree) (cache : HashCache C)
    (e : KeyIndex) (message : Message) (randomness : Randomness) (hsel : Selects prims x top cache e message randomness)
    (l : LoggedState C) (z : Option Signature × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims) (honestSignature (fun oa => SigningCoreProof.honestLift oa)
      (SigningGuessProof.receiptDealt x top) e message)).run l))
    (hle : z.2.1.1 ≤ cache) :
    Adds (OnSel x.1 e (XmssSecurity.Concrete.CacheView.encodingInput x.1 e (message, randomness))) l z.2 := by
  unfold honestSignature at hz
  obtain ⟨p1, hp1, hz⟩ := logged_bind prims _ _ l z hz
  refine (adds_onSel_of_noCall prims x.1 e _ _ (bottom_noCall x top e _) l p1 hp1).trans ?_
  rcases hp1t : p1.1 with _ | tree
  · rw [hp1t] at hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact adds_refl _ _
  rw [hp1t] at hz
  obtain ⟨p2, hp2, hz⟩ := logged_bind prims _ _ _ z hz
  refine (adds_onSel_of_noCall prims x.1 e _ _ ?_ _ p2 hp2).trans ?_
  · rw [receiptDealt_value]
    exact noCall_liftFree _ _ (prfValue_bound _ _ _)
  obtain ⟨q, hq, hz⟩ := logged_bind prims _ _ _ z hz
  have hqz : q.2.1.1 ≤ cache := (logged_grows prims _ _ z hz).trans hle
  refine Adds.trans ((adds_signCodeword prims _ _ _ _ _ e _ q hq).mono fun entry hentry => ?_) ?_
  · obtain ⟨hfree, hvalidCase⟩ := hentry
    intro _ hk hvalid
    obtain ⟨-, r, encoding, hr, hinput⟩ := hvalidCase hk hvalid
    rw [hinput]
    obtain ⟨p0, hp0, hp1eq⟩ := logged_map prims _ _ l p1 (by
      rw [SigningGuessProof.receiptDealt_bottom] at hp1; exact hp1)
    have hout : p0.1 = some (.bottom tree) := by
      rw [hp1eq] at hp1t
      dsimp only at hp1t
      revert hp1t
      rcases p0.1 with _ | (_ | tree')
      · intro h; exact absurd h (by simp)
      · intro h; exact absurd h (by simp)
      · intro h; simp only [Option.some.injEq] at h; rw [h]
    have hTreeLe : p0.2.1.1 ≤ cache := by
      have h1 : p0.2 = p1.2 := by rw [hp1eq]
      rw [h1]
      exact (logged_grows prims _ _ p2 hp2).trans ((logged_grows prims _ _ q hq).trans hqz)
    rw [hsel tree l.1 (p0.1, p0.2.1) p2.2.1 (q.1, q.2.1) _ r encoding
      (logged_count prims _ l p0 hp0) hout hTreeLe (logged_count prims _ p2.2 q hq) hr hqz]
    rfl
  refine adds_onSel_of_noCall prims x.1 e _ _ ?_ _ z hz
  rcases q.1 with _ | ⟨r, encoding⟩
  · exact noCall_pure _ _
  refine noCall_bind _ (noCall_sequenceFin _ _ fun index => ?_) fun _ => ?_
  · split
    · rw [receiptDealt_value]
      exact noCall_liftFree _ _ (prfValue_bound _ _ _)
    · exact noCall_pure _ _
    · refine noCall_bind _ ?_ fun _ => noCall_pure _ _
      rw [receiptDealt_value]
      exact noCall_liftFree _ _ (prfValue_bound _ _ _)
  · refine noCall_bind _ (noCall_liftFree _ _ (tweakable_bound _ _ (merklePath_bound x.1 e _ _ _)))
      fun _ => noCall_pure _ _

/-- A free call at key `e` with a valid digest is on `selected` or on `forged`. -/
def Allowed (P : PublicParameter) (e : KeyIndex) (selected forged : HashInput) (entry : Entry) : Prop :=
  entry.2.2 = true → AtKey P e entry.1 → XmssSecurity.TargetSum.ValidDigest entry.2.1 →
    entry.1 = selected ∨ entry.1 = forged

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

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- The verification and the freshness check call at key `e` only the selected and the forged input. -/
theorem adds_finish (x : SigningSecurityProof.Keys3 C) (top : TopTree) (cache : HashCache C)
    (e : KeyIndex) (message : Message) (randomness : Randomness) (hsel : Selects prims x top cache e message randomness)
    (trees : Finset (Fin (2 ^ layerHeight))) (forgery : Forgery) (st : TsigState C)
    (hR : SigningGuessProof.ReleasedBound st) (hc : st.corrupt.card ≤ C.t - 1) (hbound : st.bound e = some message)
    (he : forgery.signature.leafIndex = e) (l : LoggedState C)
    (z : ((Bool × TsigState C × Forgery) × List (SigningOpeningProof.HiddenKey × Digest)) × LoggedState C)
    (hz : z ∈ support ((simulateQ (loggedImpl prims)
      (SigningGuessLinkProof.tsigFinishLogged (SigningGuessProof.receiptDealt x top) trees (forgery, st))).run l))
    (hle : z.2.1.1 ≤ cache) :
    Adds (Allowed x.1 e (XmssSecurity.Concrete.CacheView.encodingInput x.1 e (message, randomness))
      (XmssSecurity.Concrete.CacheView.encodingInput x.1 e
        (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness))) l z.2 := by
  subst he
  rw [SigningGuessLinkProof.tsigFinishLogged_eq] at hz
  obtain ⟨v, hv, hz⟩ := logged_bind prims _ _ l z hz
  refine Adds.trans ((adds_world prims (fun input => AtKey x.1 forgery.signature.leafIndex input ∧
      input ≠ XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex
        (forgery.message, (forgery.signature.layers bottomLayer).randomness)) _ ?_ l v hv).mono
      fun entry hentry hfree hk _ =>
    Or.inr (not_not.1 fun hne => hentry hfree ⟨hk, hne⟩)) ?_
  · exact noCall_liftFree _ _ (loggedTweakable_bound x.1 _ _ _ _ (verify_bound x.1 _ _ _ _))
  obtain ⟨f, hf, rfl⟩ := logged_map prims _ _ _ z hz
  split at hf
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hf
    subst hf
    exact adds_refl _ _
  · rename_i hsigners
    obtain rfl : forgery.message = message := Option.some.inj
      ((message_of_signers st hR hc _ _ hsigners).symm.trans hbound)
    obtain ⟨g, hg, rfl⟩ := logged_map prims _ _ _ f hf
    exact (adds_honestSignature prims x top cache _ _ randomness hsel _ g hg hle).mono
      fun entry h hfree hk hvalid => Or.inl (h hfree hk hvalid)

end Finish

section Main

theorem openingOracles_inv (x : SigningSecurityProof.Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C)))
    {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α) :
    ∀ r ∈ support ((simulateQ (SigningOpeningProof.openingOracles x dealt) source).run
      ((SigningCoreProof.tsigInit, false), ∅, [])),
      SigningGuessProof.ReleasedBound r.2.1.1 ∧ r.2.1.1.corrupt.card ≤ C.t - 1 := by
  refine SeedHitProof.support_simulateQ_inv (SigningOpeningProof.openingOracles x dealt)
    (fun s => SigningGuessProof.ReleasedBound s.1.1 ∧ s.1.1.corrupt.card ≤ C.t - 1) ?_ source _ ?_
  · intro t s hs z hz
    have hflag : (z.1, z.2.1) ∈ support ((SigningCoreProof.flaggedOracles x dealt t).run s.1) := by
      rw [← SigningOpeningProof.openingOracles_forget x dealt t s.1 s.2, support_map]
      exact ⟨z, hz, rfl⟩
    have hgame : (z.1, z.2.1.1) ∈ support ((SigningCoreProof.gameOracles dealt t).run s.1.1) := by
      rw [← SigningCoreProof.flaggedOracles_forget x dealt t s.1.1 s.1.2, support_map]
      exact ⟨_, hflag, rfl⟩
    refine ⟨?_, SigningGuessProof.gameOracles_corrupt_le dealt t s.1.1 _ hs.2 hgame⟩
    rcases t with t | q
    · change (z.1, z.2.1.1) ∈ support ((fun a => (a, s.1.1)) <$>
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) at hgame
      rw [support_map] at hgame
      obtain ⟨a, -, ha⟩ := hgame
      have hst : s.1.1 = z.2.1.1 := congrArg Prod.snd ha
      rw [← hst]
      exact hs.1
    · exact SigningGuessProof.tsigOracles_releasedBound _ dealt q s.1.1 _ hs.1 hgame
  · refine ⟨fun e message i hm => ?_, by simp [SigningCoreProof.tsigInit]⟩
    simp [SigningCoreProof.tsigInit] at hm

theorem tsigFinishLogged_state (dealt : Dealt C (OracleComp (WorldSpec C))) (trees : Finset (Fin (2 ^ layerHeight)))
    (forgery : Forgery) (st : TsigState C)
    (r : (Bool × TsigState C × Forgery) × List (SigningOpeningProof.HiddenKey × Digest))
    (hr : r ∈ support (SigningGuessLinkProof.tsigFinishLogged dealt trees (forgery, st))) :
    r.1.2 = (st, forgery) := by
  have h : r.1 ∈ support (SigningCoreProof.tsigFinish dealt (forgery, st)) := by
    rw [← SigningGuessLinkProof.tsigFinishLogged_forget dealt trees, support_map]
    exact ⟨r, hr, rfl⟩
  exact SigningGuessProof.tsigFinish_state dealt forgery st r.1 h

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- Every free call at the key of the forgery with a valid digest is on the selected input or on the
forged input, unless `ρ` comes from a commitment collision. -/
theorem allowed_of_joint (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (hw : w ∈ support (jointRun prims A x)) (hwin : w.1.1.1 = (true, false))
    (hnalt : ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 w.2.1.1)
    (top : TopTree) (state : TsigState C) (forgery : Forgery) (hm : w.1.1.2 = some (top, state, forgery))
    (selected : Message × Randomness)
    (hsel : (finalOf x (w.1.1, w.2.1) top state forgery).selected prims = some selected) :
    ∀ entry ∈ w.2.2.filterMap hashEntry, Allowed x.1 forgery.signature.leafIndex
      (XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex selected)
      (XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex
        (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness)) entry := by
  have hS := selects_of_final prims A x w hw hwin hnalt top state forgery hm selected hsel
  have hbF : state.bound forgery.signature.leafIndex = some selected.1 :=
    bound_of_selected prims (finalOf x (w.1.1, w.2.1) top state forgery) selected hsel
  have hfinal : Adds (Allowed x.1 forgery.signature.leafIndex
      (XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex selected)
      (XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex
        (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness))) loggedInit w.2 := by
    unfold jointRun SigningGuessLinkProof.verifyFinal at hw
    dsimp only at hw
    rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
        SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _] at hw
    obtain ⟨p, hp, hw⟩ := logged_bind prims _ _ _ w hw
    refine Adds.trans ((adds_world prims (AtKey x.1 forgery.signature.leafIndex) _
      (noCall_liftFree _ _ (referenceTree_bound x.1 _ x.2.1 emptyTop .top)) _ p hp).mono
        fun entry h hfree hk _ => (h hfree hk).elim) ?_
    rcases hp1 : p.1 with _ | (top' | tree)
    · rw [hp1] at hw
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
      subst hw
      simp at hm
    swap
    · rw [hp1] at hw
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
      subst hw
      simp at hm
    rw [hp1] at hw
    dsimp only at hw
    obtain ⟨q, hq, hw⟩ := logged_bind prims _ _ _ w hw
    obtain ⟨v, hv, rfl⟩ := logged_map prims _ _ _ w hw
    have hstate := tsigFinishLogged_state _ _ _ _ v.1 (logged_support prims _ _ v hv)
    simp only [Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, hst, hforgery⟩ := hm
    rw [hstate] at hst hforgery
    dsimp only at hst hforgery
    subst hst
    subst hforgery
    obtain ⟨hR, hc⟩ := openingOracles_inv x _ _ q.1 (logged_support prims _ _ q hq)
    have hqle : q.2.1.1 ≤ v.2.1.1 := logged_grows prims _ _ v hv
    have hB : Adds (OnSel x.1 q.1.1.signature.leafIndex
        (XmssSecurity.Concrete.CacheView.encodingInput x.1 q.1.1.signature.leafIndex selected)) p.2 q.2 := by
      refine logged_simulateQ_inv prims (SigningOpeningProof.openingOracles x (SigningGuessProof.receiptDealt x top'))
        (fun s l => l.1.1 ≤ v.2.1.1 → (∀ message'', s.1.1.bound q.1.1.signature.leafIndex = some message'' →
          message'' = selected.1) → Adds (OnSel x.1 q.1.1.signature.leafIndex
            (XmssSecurity.Concrete.CacheView.encodingInput x.1 q.1.1.signature.leafIndex selected)) p.2 l)
        ?_ _ _ p.2 (fun _ _ => adds_refl _ _) q hq hqle ?_
      · intro t s l hinv r hr hle hb
        have hgrow := SigningSupportProof.openingOracles_step_grows x _ t s r.1 (logged_support prims _ _ r hr)
        have hb' : ∀ message'', s.1.1.bound q.1.1.signature.leafIndex = some message'' → message'' = selected.1 :=
          fun m hm => hb m (hgrow.1.bound_eq hm)
        exact (hinv ((logged_grows prims _ _ r hr).trans hle) hb').trans
          (adds_opening_step prims x top' v.2.1.1 _ selected.1 selected.2 hS t s l r hr hle hb')
      · intro m hm
        exact Option.some.inj (hm.symm.trans hbF)
    refine (hB.mono fun entry h hfree hk hvalid => Or.inl (h hfree hk hvalid)).trans ?_
    exact adds_finish prims x top' v.2.1.1 _ selected.1 selected.2 hS q.1.2.2.1 q.1.1 q.1.2.1.1 hR hc hbF rfl
      q.2 v hv le_rfl
  obtain ⟨new, hnew, hok⟩ := hfinal
  intro entry hentry
  rw [hnew] at hentry
  simpa [loggedInit] using hok entry (by simpa [loggedInit] using hentry)

end Main

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- `SelectionClassification` holds. -/
theorem selectionClassification : SelectionClassification (C := C) prims := by
  intro A x w hw hwin hnalt top state forgery hm selected hsel pre post digest hsplit hpre entry hentry hfree hk
    hvalid
  have hmem : entry ∈ w.2.2.filterMap hashEntry := by
    rw [hsplit]
    exact List.mem_append_left _ hentry
  rcases allowed_of_joint prims A x w hw hwin hnalt top state forgery hm selected hsel entry hmem hfree hk hvalid
    with h | h
  · exact (hpre entry hentry h).elim
  · exact h

/-- The signing core from the coupling alone. -/
theorem hiddenCoreAt_of_flagCoupling (hcouple : UnchargedFlagCoupling (C := C) prims) :
    SigningCoreProof.HiddenCoreAt prims C :=
  hiddenCoreAt_of_coupling prims (selectionClassification prims) hcouple

end SigningSelectionProof

end ThresholdLeanXmssSecurity

/--
info: 'ThresholdLeanXmssSecurity.SigningSelectionProof.selectionClassification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningSelectionProof.selectionClassification

/--
info: 'ThresholdLeanXmssSecurity.SigningSelectionProof.hiddenCoreAt_of_flagCoupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningSelectionProof.hiddenCoreAt_of_flagCoupling
