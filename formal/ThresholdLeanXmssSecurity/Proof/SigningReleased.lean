import ThresholdLeanXmssSecurity.Proof.SigningSupport

/-!
# A released signature is resolved in the cache

`releasedResolved` proves `SigningSupportProof.ReleasedResolved`. Outside `OpeningMatch`, a released
final key has its selected digest input in the cache when the verification starts.

* A release needs `t` signers. The corrupt operators are at most `t - 1`, so an honest round 2
  released the chain parts at the key. Its receipt holds a supported run of `signCodeword`.
* `run_signCodeword_cached` shows that this run calls the selected digest input. It replays the run
  and uses `encodingInput_cached_of_decode_some` of leanVM.
* Outside `OpeningMatch`, the receipt has the canonical randomizer (`ReceiptRuns.canonical`), so its
  randomness is the selected randomness (`ReceiptRuns.selected`).
* `openingRun_receipts` moves the run of `openingOracles` to a run of `flaggedReceiptOracles` with
  the same state and cache.

`verifyRun_bottomOpened_eq` then holds with no hypothesis.

`topOpened_cache_eq` is the cache form of `topOpened`. It needs the same honest root on both caches
and the top digest input in the smaller cache.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningReleasedProof

open LeanXmss ThresholdLeanXmss SigningOpeningProof

variable {C : Committee}

section Grind

variable (prims : Primitives)

set_option maxRecDepth 100000 in
/-- A supported run of `signCodeword` that returns a randomness calls the digest input of that
randomness. -/
theorem run_signCodeword_cached (P : PublicParameter) (commitment : Digest) (e : KeyIndex)
    (message : Message) (candidate : Digest) (s : HashCache C × ℕ)
    (r : Option (Randomness × Encoding) × HashCache C × ℕ)
    (hr : r ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (signCodeword P commitment e message candidate))).run s))
    (randomness : Randomness) (encoding : Encoding) (hs : r.1 = some (randomness, encoding)) :
    (SigningDescentProof.thView r.2.1
      (XmssSecurity.Concrete.CacheView.encodingInput P e (message, randomness))).isSome := by
  have hd := (SigningCacheProof.run_liftFree prims _ s r hr _ (SigningCacheProof.agrees_answersOf le_rfl)).symm.trans hs
  rw [D_signCodeword (prims := prims) _ _ _ _ _ (SigningGuessProof.signCodeword_some_commitment prims _ P
    commitment e message candidate _ hd).symm] at hd
  have hdecode := E_grind_spec (prims := prims) _ _ _ _ _ _ _ _ _ hd
  rw [SigningGuessProof.E_messageDigest_cache, XmssSecurity.Bridge.decode_eq] at hdecode
  obtain ⟨output, hout⟩ := XmssSecurity.Concrete.CacheView.encodingInput_cached_of_decode_some _ P e message
    randomness encoding hdecode
  exact Option.isSome_iff_exists.mpr ⟨output, hout⟩

end Grind

section Receipts

variable (prims : Primitives)

/-- A counted run of `openingOracles` has a counted run of `flaggedReceiptOracles` with the same
result, state and cache. -/
theorem openingRun_receipts (x : SigningSecurityProof.Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C)))
    {α : Type} (source : OracleComp (LocalSpec C + TsigSpec C) α) (st : TsigState C) (flag : Bool)
    (s : HashCache C × ℕ)
    (q : (α × (TsigState C × Bool) × Finset (Fin (2 ^ layerHeight)) × List (HiddenKey × Digest)) ×
      HashCache C × ℕ)
    (hq : q ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((simulateQ (openingOracles x dealt) source).run ((st, flag), ∅, []))).run s)) :
    ∃ q' : (α × (TsigState C × Bool) × List (SigningGuessProof.Round2Receipt C)) × HashCache C × ℕ,
      q' ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
        ((simulateQ (SigningGuessProof.flaggedReceiptOracles x dealt) source).run ((st, flag), []))).run s) ∧
      q'.1.1 = q.1.1 ∧ q'.1.2.1 = q.1.2.1 ∧ q'.2 = q.2 := by
  have hopening := SigningCoreProof.simulateQ_run_forget _ _ (openingOracles_forget x dealt) source
    (st, flag) ((∅ : Finset (Fin (2 ^ layerHeight))), ([] : List (HiddenKey × Digest)))
  have hreceipt := SigningGuessProof.flaggedReceiptOracles_forget x dealt source st flag []
  have hmem : ((q.1.1, q.1.2.1), q.2) ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((simulateQ (SigningCoreProof.flaggedOracles x dealt) source).run (st, flag))).run s) := by
    rw [← hopening, simulateQ_map, StateT.run_map, support_map]
    exact ⟨q, hq, rfl⟩
  rw [← hreceipt, simulateQ_map, StateT.run_map, support_map] at hmem
  obtain ⟨q', hq', heq⟩ := hmem
  simp only [Prod.mk.injEq] at heq
  exact ⟨q', hq', heq.1.1, heq.1.2, heq.2⟩

/-- At least `t` signers at `e` for `message` hold an honest release. Its receipt has supported
runs below the cache. -/
theorem receiptRun_released (x : SigningSecurityProof.Keys3 C) (top : TopTree) {α : Type}
    (source : OracleComp (LocalSpec C + TsigSpec C) α) (s : HashCache C × ℕ)
    (q : (α × (TsigState C × Bool) × List (SigningGuessProof.Round2Receipt C)) × HashCache C × ℕ)
    (hq : q ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      ((simulateQ (SigningGuessProof.flaggedReceiptOracles x (SigningGuessProof.receiptDealt x top)) source).run
        ((SigningCoreProof.tsigInit, false), []))).run s))
    (e : KeyIndex) (message : Message) (ht : C.t ≤ (signersAt q.1.2.1.1 e message).card) :
    ∃ receipt ∈ q.1.2.2, receipt.key = e ∧ receipt.message = message ∧
      SigningGuessProof.ReceiptRuns prims x top q.2.1 receipt := by
  have hin := SigningGuessProof.countRun_support prims _ s q hq
  have hcorrupt := SigningGuessProof.flaggedReceiptOracles_corrupt_le x _ source q.1 hin
  have hreleased : q.1.2.1.1.released = q.1.2.2.map SigningGuessProof.Round2Receipt.release := by
    apply SigningGuessProof.signingReceiptOracles_released _ source (q.1.1, q.1.2.1.1, q.1.2.2)
    rw [← SigningGuessProof.flaggedReceiptOracles_forgetFlag x _ source SigningCoreProof.tsigInit false [],
      support_map]
    exact ⟨q.1, hin, rfl⟩
  have hruns := SigningGuessProof.flaggedReceiptOracles_runs prims x top source
    (SigningCoreProof.tsigInit, false) [] s (by simp) q hq
  have hhonest : (((q.1.2.1.1.released.filter fun r => r.1 = e ∧ r.2.1 = message).map
      (·.2.2)).toFinset).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    unfold signersAt at ht
    rw [hempty, Finset.union_empty] at ht
    have := C.one_le_t
    omega
  obtain ⟨i, hi⟩ := hhonest
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hi
  obtain ⟨a, ⟨ha, hae, ham⟩, -⟩ := hi
  rw [hreleased] at ha
  obtain ⟨receipt, hreceipt, rfl⟩ := List.mem_map.mp ha
  exact ⟨receipt, hreceipt, hae, ham, hruns receipt hreceipt⟩

end Receipts

section Verification

variable (prims : Primitives)

set_option maxRecDepth 100000 in
/-- Outside `OpeningMatch`, a released signature of the final key has its selected digest input in
the cache when the verification starts. -/
theorem releasedResolved : SigningSupportProof.ReleasedResolved prims (C := C) := by
  intro A x r hr top state forgery hm hn
  unfold SigningGuessLinkProof.verifyRun SigningGuessLinkProof.verifyFinal at hr
  dsimp only at hr
  obtain ⟨p, hp, hr⟩ := SigningCacheProof.run_bind_support prims _ _ _ r hr
  rcases hp1 : p.1 with _ | (top' | tree)
  · rw [hp1] at hr
    simp at hr
    subst hr
    simp at hm
  swap
  · rw [hp1] at hr
    simp at hr
    subst hr
    simp at hm
  rw [hp1] at hr
  dsimp only at hr
  obtain ⟨q, hq, hr⟩ := SigningCacheProof.run_bind_support prims _ _ _ r hr
  rw [simulateQ_map, StateT.run_map, support_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  rw [SigningGuessLinkProof.tsigFinishLogged_eq] at hw
  obtain ⟨v, hv, hw⟩ := SigningCacheProof.run_bind_support prims _ _ _ w hw
  rw [simulateQ_map, StateT.run_map, support_map] at hw
  obtain ⟨f, hf, rfl⟩ := hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl, rfl⟩ := hm
  refine ⟨_, _, _, v, hv, rfl, SigningCacheProof.countRun_grows prims _ _ f hf, ?_⟩
  intro z hrel
  have hqv : q.2.1 ≤ f.2.1 := (SigningCacheProof.countRun_grows prims _ _ v hv).trans
    (SigningCacheProof.countRun_grows prims _ _ f hf)
  rw [SigningSupportProof.honestKey_released] at hrel
  unfold SigningSupportProof.releasedAt at hrel
  clear hw
  change (match q.1.2.1.1.bound q.1.1.signature.leafIndex with
    | some message => decide (C.t ≤ (signersAt q.1.2.1.1 q.1.1.signature.leafIndex message).card)
    | none => false) = true at hrel
  cases hb : q.1.2.1.1.bound q.1.1.signature.leafIndex with
  | none =>
    rw [hb] at hrel
    cases hrel
  | some message =>
  rw [hb] at hrel
  have ht := of_decide_eq_true hrel
  obtain ⟨q', hq', -, hstate, hcache⟩ := openingRun_receipts prims x _ _ SigningCoreProof.tsigInit false
    p.2 q hq
  obtain ⟨receipt, -, hkey, hmessage, hruns⟩ := receiptRun_released prims x top' _ p.2 q' (by exact hq')
    q.1.1.signature.leafIndex message (by rw [hstate]; exact ht)
  rw [hcache] at hruns
  have htop : TopFacts prims (SigningCacheProof.answersOf f.2.1) x.2.1 x.1 top' := by
    rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
        (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
        SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
      referenceTree_φ _ _ _ _] at hp
    have hval := SigningCacheProof.run_liftFree prims _ _ p hp (SigningCacheProof.answersOf f.2.1)
      (SigningCacheProof.agrees_answersOf ((SigningCacheProof.countRun_grows prims _ _ q hq).trans hqv))
    rw [hp1] at hval
    obtain ⟨generated, hgen, hchain, hroot⟩ :=
      D_refTop (prims := prims) (h := SigningCacheProof.answersOf f.2.1) x.1 x.2.1 emptyTop
    have he : generated = top' := TreeOutput.top.inj (Option.some.inj (hgen.symm.trans hval.symm))
    subst generated
    exact ⟨hchain, hroot⟩
  have hfinal := SigningGuessProof.ReceiptRuns.mono prims x top' hqv receipt hruns
  dsimp only at hn
  have hcanon := SigningGuessProof.ReceiptRuns.canonical prims x
    (((v.1.1 && f.1, q.1.2.1.2), some (top', q.1.2.1.1, q.1.1)), f.2) top' q.1.2.1.1 q.1.1 rfl htop
    receipt hfinal hkey hn
  have hselected := SigningGuessProof.ReceiptRuns.selected prims z receipt hfinal hkey
    (by rw [hkey, hmessage]; exact hb) hcanon.1
  intro selected hmem
  have hs : selected = (receipt.message, receipt.randomness) :=
    Option.some.inj ((Option.mem_def.mp hmem).symm.trans hselected)
  subst selected
  obtain ⟨-, -, -, sCode, rCode, -, -, -, -, hCode, hCodeOut, hCodeLe⟩ := hruns
  obtain ⟨output, houtput⟩ := Option.isSome_iff_exists.mp (run_signCodeword_cached prims x.1
    receipt.commitment receipt.key receipt.message receipt.candidate sCode rCode hCode
    receipt.randomness receipt.encoding hCodeOut)
  rw [show z.key = receipt.key from hkey.symm]
  exact Option.isSome_iff_exists.mpr ⟨output, hCodeLe houtput⟩

set_option maxRecDepth 100000 in
/-- Outside `OpeningMatch`, the read of `bottomOpened` at the start of the verification is the
read on the final cache. -/
theorem verifyRun_bottomOpened_eq (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : SigningGuessLinkProof.LoggedOutcome C) (hr : r ∈ support (SigningGuessLinkProof.verifyRun prims A x))
    (top : TopTree) (state : TsigState C) (forgery : Forgery) (hm : r.1.1.2 = some (top, state, forgery))
    (hn : ¬SigningGuessProof.OpeningMatch prims x (r.1.1, r.2)) :
    ∃ s : HashCache C × ℕ, s.1 ≤ r.2.1 ∧
      let z := SigningCostProof.finalOf x (r.1.1, r.2) top state forgery
      SigningDescentProof.bottomOpened s.1 x.1 z.key (z.honestKey prims) =
        SigningDescentProof.bottomOpened r.2.1 x.1 z.key (z.honestKey prims) :=
  SigningSupportProof.verifyRun_bottomOpened_eq prims (releasedResolved prims) A x r hr top state forgery hm hn

end Verification

section Top

/-- The digest input of the honest top signature of the tree of `e` is in the cache `c`. -/
def TopSignedCached (c : HashCache C) (P : XmssSecurity.PublicParameter) (e : XmssSecurity.LeafIndex)
    (hk : SigningDescentProof.HonestKey) : Prop :=
  (SigningDescentProof.thView c (XmssSecurity.Concrete.CacheView.topEncodingInput P (XmssSecurity.topKeyOf e)
    (SigningDescentProof.topSignedInput c P e hk))).isSome

/-- If the honest root reads the same on both caches and the top digest input is in the smaller
cache, the read of `topOpened` does not change. -/
theorem topOpened_cache_eq {c c' : HashCache C} (hle : c ≤ c') (P : XmssSecurity.PublicParameter)
    (e : XmssSecurity.LeafIndex) (hk : SigningDescentProof.HonestKey)
    (hroot : SigningDescentProof.honestRoot c P e hk = SigningDescentProof.honestRoot c' P e hk)
    (hc : TopSignedCached c P e hk) :
    SigningDescentProof.topOpened c P e hk = SigningDescentProof.topOpened c' P e hk := by
  have hinput : SigningDescentProof.topSignedInput c P e hk = SigningDescentProof.topSignedInput c' P e hk := by
    unfold SigningDescentProof.topSignedInput
    rw [hroot]
  obtain ⟨output, hout⟩ := Option.isSome_iff_exists.mp hc
  have hout' : SigningDescentProof.thView c' (XmssSecurity.Concrete.CacheView.topEncodingInput P
      (XmssSecurity.topKeyOf e) (SigningDescentProof.topSignedInput c' P e hk)) = some output := by
    rw [← hinput]
    exact hle (show c (.hash _) = some output from hout)
  have henc : SigningDescentProof.topEncoding c P e hk = SigningDescentProof.topEncoding c' P e hk := by
    unfold SigningDescentProof.topEncoding
    rw [XmssSecurity.Concrete.CacheView.topEncodingHash, XmssSecurity.Concrete.CacheView.topEncodingHash,
      XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some hout,
      XmssSecurity.Concrete.CacheView.digestAt_eq_of_cache_eq_some hout']
  funext l
  unfold SigningDescentProof.topOpened
  rw [henc]

end Top

end SigningReleasedProof

end ThresholdLeanXmssSecurity

/--
info: 'ThresholdLeanXmssSecurity.SigningReleasedProof.releasedResolved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningReleasedProof.releasedResolved

/--
info: 'ThresholdLeanXmssSecurity.SigningReleasedProof.verifyRun_bottomOpened_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningReleasedProof.verifyRun_bottomOpened_eq

/--
info: 'ThresholdLeanXmssSecurity.SigningReleasedProof.topOpened_cache_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningReleasedProof.topOpened_cache_eq
