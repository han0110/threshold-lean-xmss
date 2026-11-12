import ThresholdLeanXmssSecurity.Proof.LifetimeEmulation

/-!
# The private masks of the lifetime emulator

D16 replaces the fresh masks of an honest pair by one private lazy table. Its address contains
the unordered pair, point, message and quorum; both endpoints therefore read the same entry.
Only keys of pairs with a corrupt endpoint are inputs to `privateOracles`. The PRF terms and
trees still come from the auxiliary tables of `LifetimeEmulation`.

The table laws and the adaptive pair-key guessing bound below do not assume distinct keys.
Transporting the real signing cache to this table additionally needs to account for pair-key
collisions: two equal pair keys address one real cell, even for different pairs. The final
transport goals retain this condition explicitly, rather than claiming equality for all keys.

The pinned and current leanVM hidden-value and finite-table modules were searched first.
The reusable 256-bit coordinate estimate is `TprfSecurityProof.probEvent_update_le`, and the
adaptive bound is `probEvent_flag_le` from `Coupling`; neither is duplicated here.

`PrivateSigningTransport` is the request-level equality. `PrivateMaskPrefixLaw` states
the independence condition consumed by the prefix bound; it is not a proof of that condition for
the actual lifetime. Applying it to the lifetime scheduler requires replay, independence
and budget certificates for that scheduler.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeMasks

open TprfSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- The private table has no pair key in its address. -/
abbrev MaskSlot (D : C.Coalition) :=
  {p : C.Pair // KeygenHiddenPair D p} × Point × Message × C.Quorum

abbrev MaskCache (D : C.Coalition) := (MaskSlot D →ₒ HashOutput).QueryCache

abbrev MaskM (D : C.Coalition) := StateT (MaskCache D) (OracleComp (LocalSpec C))

/-- Only the corrupt coalition's pair keys enter the emulator. -/
abbrev KnownPairs (D : C.Coalition) := {p : C.Pair // ¬ KeygenHiddenPair D p} → HashOutput

/-- Fresh entries use private randomness; repeated requests reuse the full 256-bit value. -/
def privateMask (D : C.Coalition) : QueryImpl (MaskSlot D →ₒ HashOutput) (MaskM D) :=
  QueryImpl.withCaching fun _ => liftComp ($ᵗ HashOutput) (LocalSpec C)

theorem privateMask_cached (D : C.Coalition) (s : MaskSlot D) (c : MaskCache D)
    (v : HashOutput) (hv : c s = some v) :
    (privateMask D s).run c = pure (v, c) :=
  QueryImpl.withCaching_run_some _ hv

theorem privateMask_fresh (D : C.Coalition) (s : MaskSlot D) (c : MaskCache D)
    (hc : c s = none) :
    (privateMask D s).run c =
      (fun v => (v, c.cacheQuery s v)) <$> liftComp ($ᵗ HashOutput) (LocalSpec C) :=
  QueryImpl.withCaching_run_none _ hc

/-- The private table is implemented by the usual lazy random oracle, on its own addresses. -/
theorem privateMask_run (prims : Primitives) (D : C.Coalition) (s : MaskSlot D)
    (c : MaskCache D) (g : HashCache C) :
    (simulateQ (localAnswer prims) ((privateMask D s).run c)).run g =
      (fun r => (r, g)) <$> ((MaskSlot D →ₒ HashOutput).randomOracle s).run c := by
  cases hc : c s with
  | some v =>
    rw [privateMask_cached D s c v hc, simulateQ_pure, StateT.run_pure,
      QueryImpl.withCaching_run_some _ hc, map_pure]
  | none =>
    rw [privateMask_fresh D s c hc, simulateQ_map, StateT.run_map,
      QueryImpl.withCaching_run_none _ hc]
    simp only [localAnswer, QueryImpl.simulateQ_add_liftComp_left,
      unifFwdImpl.simulateQ_run, Functor.map_map]
    rfl

/-- A mask under a revealed pair key uses the shared oracle. An honest pair uses its private cell. -/
def pairMask (D : C.Coalition) (known : KnownPairs D) (p : C.Pair)
    (x : Point) (message : Message) (J : C.Quorum) : MaskM D Digest :=
  if h : KeygenHiddenPair D p then
    truncateHash <$> privateMask D (⟨p, h⟩, x, message, J)
  else
    StateT.lift (truncateHash <$> liftComp (hashQuery (.mask (known ⟨p, h⟩) x message J)) (LocalSpec C))

theorem pairMask_hidden (D : C.Coalition) (known : KnownPairs D) (p : C.Pair)
    (hp : KeygenHiddenPair D p) (x : Point) (message : Message) (J : C.Quorum) :
    pairMask D known p x message J =
      truncateHash <$> privateMask D (⟨p, hp⟩, x, message, J) := by
  simp only [pairMask, dif_pos hp]

theorem pairMask_known (D : C.Coalition) (known : KnownPairs D) (p : C.Pair)
    (hp : ¬ KeygenHiddenPair D p) (x : Point) (message : Message) (J : C.Quorum) :
    pairMask D known p x message J =
      StateT.lift (truncateHash <$> liftComp (hashQuery (.mask (known ⟨p, hp⟩) x message J)) (LocalSpec C)) := by
  simp only [pairMask, dif_neg hp]

/-- PRAWNS uses one mask at both endpoints, including after repeated or interleaved requests. -/
theorem pairMask_comm (D : C.Coalition) (known : KnownPairs D) (i j : C.Party)
    (hij : i ≠ j) (x : Point) (message : Message) (J : C.Quorum) :
    pairMask D known (C.pairOf i j hij) x message J =
      pairMask D known (C.pairOf j i hij.symm) x message J := by
  rw [pairOf_comm i j hij]

/-- `Eval'` with cached PRF terms and lazy masks. The table of terms is supplied in `z`. -/
def privateEval (D : C.Coalition) (known : KnownPairs D) (term : C.Term → Point → Digest)
    (i : C.Party) (J : C.Quorum) (x : Point) (message : Message) : MaskM D Digest := do
  let terms := (C.terms.filter (· ∈ L J i)).map fun T => term T x
  let masks ← (C.parties.filter fun j => j ∈ J.1 ∧ j ≠ i).mapM fun j =>
    if h : j = i then pure 0 else pairMask D known (C.pairOf i j (Ne.symm h)) x message J
  pure ((terms ++ masks).foldl (· ^^^ ·) 0)

/-- The signing service data contain no honest pair key. Corruption is excluded by the static
lifetime interface, so the unused `keys` field is the same dummy field as `emulatedDealt`. -/
def privateDealt (D : C.Coalition) (known : KnownPairs D) (parameter : PublicParameter)
    (top : TopTree) (trees : Fin (2 ^ layerHeight) → Option BottomTree)
    (value : Point → Digest) (term : C.Term → Point → Digest) : Dealt C (MaskM D) :=
  ⟨fun _ => ⟨parameter, fun _ => 0, fun _ => 0⟩, parameter, top,
    fun x => pure (value x), privateEval D known term, fun b => pure (trees b)⟩

/-- The executable D16 emulator; its private table persists across signing requests. -/
def privateOracles (D : C.Coalition) (known : KnownPairs D) (parameter : PublicParameter)
    (top : TopTree) (trees : Fin (2 ^ layerHeight) → Option BottomTree)
    (value : Point → Digest) (term : C.Term → Point → Digest) :
    QueryImpl (TsigSpec C) (StateT (TsigState C) (MaskM D)) :=
  tsigOracles (fun oa => StateT.lift (liftComp oa (LocalSpec C)))
    (privateDealt D known parameter top trees value term)

/-! ## The real and private caches -/

/-- This address map is used only in the proof, never by the key-free emulator. -/
def maskInput (D : C.Coalition) (keys : C.Pair → HashOutput) (s : MaskSlot D) : Query C :=
  .mask (keys s.1.1) s.2.1 s.2.2.1 s.2.2.2

/-- Split out exactly the honest-pair masks; every other point stays in the public cache. -/
def splitMasks (D : C.Coalition) (keys : C.Pair → HashOutput) (g : HashCache C) :
    MaskCache D × HashCache C :=
  (fun s => g (maskInput D keys s),
    fun u => if ∃ s, maskInput D keys s = u then none else g u)

theorem maskInput_injective (D : C.Coalition) (keys : C.Pair → HashOutput)
    (hinj : Function.Injective keys) : Function.Injective (maskInput D keys) := by
  rintro ⟨p, x, m, J⟩ ⟨p', x', m', J'⟩ h
  simp only [maskInput, Query.mask.injEq] at h
  obtain ⟨hp, rfl, rfl, rfl⟩ := h
  have : p = p' := Subtype.ext (hinj hp)
  subst this
  rfl

/-- The two caches agree away from honest-pair mask inputs, without a freshness assumption. -/
theorem splitMasks_public (D : C.Coalition) (keys : C.Pair → HashOutput)
    (g : HashCache C) (u : Query C) (hu : ∀ s, maskInput D keys s ≠ u) :
    (splitMasks D keys g).2 u = g u := by
  simp only [splitMasks]
  rw [if_neg (fun ⟨s, hs⟩ => hu s hs)]

theorem splitMasks_prf (D : C.Coalition) (keys : C.Pair → HashOutput)
    (g : HashCache C) (seed : HashOutput) (x : Point) :
    (splitMasks D keys g).2 (.prf seed x) = g (.prf seed x) :=
  splitMasks_public D keys g _ (fun _ h => by cases h)

theorem splitMasks_update (D : C.Coalition) (keys : C.Pair → HashOutput)
    (hinj : Function.Injective keys) (s₀ : MaskSlot D) (g : HashCache C) (v : HashOutput) :
    splitMasks D keys (g.cacheQuery (maskInput D keys s₀) v) =
      ((splitMasks D keys g).1.cacheQuery s₀ v, (splitMasks D keys g).2) := by
  refine Prod.ext (funext fun s => ?_) (funext fun u => ?_)
  · by_cases hs : s = s₀
    · subst hs
      simp [splitMasks]
    · simp only [splitMasks, QueryCache.cacheQuery_of_ne _ _ hs,
        QueryCache.cacheQuery_of_ne _ _ (fun h => hs (maskInput_injective D keys hinj h))]
  · simp only [splitMasks]
    by_cases h : ∃ s, maskInput D keys s = u
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h,
        QueryCache.cacheQuery_of_ne _ _ (fun hu => h ⟨s₀, hu.symm⟩)]

/-- One real hidden-mask call and one private-table call have the same full value and split
cache. The public cache is unchanged on the private side, even on a fresh call. -/
theorem privateMask_real_run (prims : Primitives) (D : C.Coalition)
    (keys : C.Pair → HashOutput) (hinj : Function.Injective keys)
    (s : MaskSlot D) (g : HashCache C) :
    Prod.map id (splitMasks D keys) <$>
        (hashAnswer prims (maskInput D keys s)).run g =
      (fun r => (r.1.1, r.1.2, r.2)) <$>
        (simulateQ (localAnswer prims) ((privateMask D s).run (splitMasks D keys g).1)).run
          (splitMasks D keys g).2 := by
  rw [privateMask_run]
  change Prod.map id (splitMasks D keys) <$>
      ((Query C →ₒ HashOutput).randomOracle (maskInput D keys s)).run g = _
  have hc : (splitMasks D keys g).1 s = g (maskInput D keys s) := rfl
  cases hg : g (maskInput D keys s) with
  | some v =>
    rw [QueryImpl.withCaching_run_some _ hg, QueryImpl.withCaching_run_some _ (hc.trans hg)]
    simp
  | none =>
    rw [QueryImpl.withCaching_run_none _ hg, QueryImpl.withCaching_run_none _ (hc.trans hg)]
    simp only [Functor.map_map, Prod.map_apply, id_eq, splitMasks_update D keys hinj]
    rfl

/-- A public mask query whose key is not an honest pair key sees the same cache on both sides. -/
theorem splitMasks_mask_of_miss (D : C.Coalition) (keys : C.Pair → HashOutput)
    (g : HashCache C) (k : HashOutput) (x : Point) (m : Message) (J : C.Quorum)
    (hmiss : ∀ p, KeygenHiddenPair D p → keys p ≠ k) :
    (splitMasks D keys g).2 (.mask k x m J) = g (.mask k x m J) := by
  apply splitMasks_public
  intro s hs
  exact hmiss s.1.1 s.1.2 (Query.mask.inj hs).1

/-! ## Pair-key hits in a key-independent emulation -/

abbrev HiddenPair (D : C.Coalition) := {p : C.Pair // KeygenHiddenPair D p}

/-- A public call names an honest pair key. All positions and messages count, not only cells
already read by signing. This includes a guess before the private cell is first sampled. -/
def PairKeyHit (D : C.Coalition) (t : (LocalSpec C).Domain)
    (keys : HiddenPair D → HashOutput) : Prop :=
  match t with
  | .inr (.inl (.mask k _ _ _)) => ∃ p, keys p = k
  | _ => False

theorem pairKeyHit_counted (D : C.Coalition) (t : (LocalSpec C).Domain)
    (keys : HiddenPair D → HashOutput) : PairKeyHit D t keys → Counted t := by
  rcases t with n | q | x
  · exact False.elim
  · cases q <;> simp [PairKeyHit, Counted]
  · exact False.elim

theorem probEvent_pairKeyHit (D : C.Coalition) (t : (LocalSpec C).Domain) :
    Pr[PairKeyHit D t | $ᵗ (HiddenPair D → HashOutput)] ≤
      Fintype.card (HiddenPair D) / (2 ^ 256 : ℝ≥0∞) := by
  rcases t with n | q | x
  · simp [PairKeyHit]
  · cases q with
    | mask k x message J =>
      change Pr[fun keys : HiddenPair D → HashOutput => ∃ p, keys p = k | _] ≤ _
      calc
        _ = Pr[fun keys : HiddenPair D → HashOutput =>
            ∃ p ∈ (Finset.univ : Finset (HiddenPair D)), keys p = k | _] := by simp
        _ ≤ ∑ p : HiddenPair D, Pr[fun keys => keys p = k | $ᵗ (HiddenPair D → HashOutput)] :=
          probEvent_exists_finset_le_sum _ _ _
        _ ≤ ∑ _p : HiddenPair D, (2 ^ 256 : ℝ≥0∞)⁻¹ := by
          refine Finset.sum_le_sum fun p _ => probEvent_update_le _ p ?_
          intro g a b ha hb
          simpa using ha.trans hb.symm
        _ = _ := by simp [div_eq_mul_inv]
    | _ => simp [PairKeyHit]
  · simp [PairKeyHit]

/-- Adaptive public calls in any emulator independent of the hidden pair keys. The handler may
contain its private lazy mask table, signing state, prefix state and arbitrary public data. -/
theorem pairKeyHit_bound {σ α : Type} (D : C.Coalition)
    (impl : QueryImpl (LocalSpec C) (StateT σ ProbComp))
    (oa : OracleComp (LocalSpec C) α) (q : ℕ) (hq : IsQueryBoundP oa Counted q) (s : σ) :
    Pr[fun r => r.2.2 = true | $ᵗ (HiddenPair D → HashOutput) >>= fun keys =>
      (simulateQ (flagImpl impl (PairKeyHit D) keys) oa).run (s, false)] ≤
      q * Fintype.card (HiddenPair D) / (2 ^ 256 : ℝ≥0∞) := by
  simpa only [mul_div_assoc] using
    probEvent_flag_le impl (PairKeyHit D) ($ᵗ (HiddenPair D → HashOutput)) Counted
      (Fintype.card (HiddenPair D) / (2 ^ 256 : ℝ≥0∞))
      (pairKeyHit_counted D) (fun t _ => probEvent_pairKeyHit D t) oa q s hq

/-- D16's guessing term fits the fixed `seedHitError` used by each lifetime ceremony. -/
theorem pairKeyHit_bound_seedHitError {σ α : Type} (D : C.Coalition)
    (impl : QueryImpl (LocalSpec C) (StateT σ ProbComp))
    (oa : OracleComp (LocalSpec C) α) (q : ℕ) (hq : IsQueryBoundP oa Counted q) (s : σ) :
    (Pr[fun r => r.2.2 = true | $ᵗ (HiddenPair D → HashOutput) >>= fun keys =>
      (simulateQ (flagImpl impl (PairKeyHit D) keys) oa).run (s, false)]).toReal ≤ seedHitError C q := by
  have hc : Fintype.card (HiddenPair D) ≤ C.n.choose (C.t - 1) + C.n ^ 2 :=
    (Fintype.card_subtype_le _).trans ((card_pair_le C).trans
      ((choose_two_le_sq C.n).trans (Nat.le_add_left _ _)))
  have h := pairKeyHit_bound D impl oa q hq s
  have h' : Pr[fun r => r.2.2 = true | $ᵗ (HiddenPair D → HashOutput) >>= fun keys =>
      (simulateQ (flagImpl impl (PairKeyHit D) keys) oa).run (s, false)] ≤
      (((C.n.choose (C.t - 1) + C.n ^ 2) * q : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    refine h.trans ?_
    rw [Nat.cast_mul, mul_comm]
    gcongr
  exact toReal_le_div h'

/-- The symbolic lifetime prefix leaves the honest-pair keys uniform and independent of the
emulator state. The state includes the public cache, private masks, auxiliary tables and replay
state. This exact distributional obligation must be established for the lifetime prefix; it does
not follow merely from a bound on the number of queries. -/
def PrivateMaskPrefixLaw {σ : Type} (D : C.Coalition)
    (pre : ProbComp ((HiddenPair D → HashOutput) × σ)) : Prop :=
  evalDist pre = evalDist (do
    let keys ← $ᵗ (HiddenPair D → HashOutput)
    let s ← Prod.snd <$> pre
    pure (keys, s))

/-- The guessing bound after a prefix satisfying its explicit independence obligation. Both the
continuation and its initial state may depend on the complete emulator view of the prefix. -/
theorem pairKeyHit_bound_of_prefix {σ α : Type} (D : C.Coalition)
    (pre : ProbComp ((HiddenPair D → HashOutput) × σ)) (hp : PrivateMaskPrefixLaw D pre)
    (impl : QueryImpl (LocalSpec C) (StateT σ ProbComp))
    (oa : σ → OracleComp (LocalSpec C) α) (q : ℕ)
    (hq : ∀ s, IsQueryBoundP (oa s) Counted q) :
    Pr[fun r => r.2.2 = true | pre >>= fun p =>
      (simulateQ (flagImpl impl (PairKeyHit D) p.1) (oa p.2)).run (p.2, false)] ≤
      q * Fintype.card (HiddenPair D) / (2 ^ 256 : ℝ≥0∞) := by
  rw [probEvent_def, evalDist_bind, hp, ← evalDist_bind, ← probEvent_def]
  simp only [bind_assoc, bind_map_left, pure_bind]
  rw [probEvent_bind_bind_swap]
  exact probEvent_bind_le_of_forall_le fun p _ => pairKeyHit_bound D impl (oa p.2) q (hq p.2) p.2

/-- The loss for equal pair keys is bounded independently of the subsequent execution. -/
theorem pairKeyCollision_bound :
    Pr[fun keys : C.Pair → HashOutput => ¬ Function.Injective keys | $ᵗ (C.Pair → HashOutput)] ≤
      ((C.n.choose 2).choose 2 : ℝ≥0∞) / 2 ^ 256 := by
  simpa only [card_pair, div_eq_mul_inv] using
    (probEvent_not_injective (Ω := C.Pair))

/-- A budget covering the pair-key setup also covers both the collision loss and the private
emulator's guessing loss within the fixed lifetime term. -/
theorem pairKeyCollision_hit_arith (D : C.Coalition) (q : ℕ) (hq : C.n.choose 2 ≤ q) :
    (C.n.choose 2).choose 2 + q * Fintype.card (HiddenPair D) ≤
      (C.n.choose (C.t - 1) + C.n ^ 2) * q := by
  have hh : Fintype.card (HiddenPair D) ≤ C.n.choose 2 :=
    (Fintype.card_subtype_le _).trans (card_pair_le C)
  have hc : (C.n.choose 2).choose 2 ≤ (C.n.choose 2) * q := by
    have := choose_two_le_sq (C.n.choose 2)
    calc
      _ ≤ (C.n.choose 2) ^ 2 := this
      _ ≤ (C.n.choose 2) * q := by nlinarith
  have hn := two_mul_choose_two_le C.n
  have hm := Nat.mul_le_mul_left q hh
  have hnq := Nat.mul_le_mul_right q hn
  nlinarith

theorem pairKeyCollision_add_hit_bound {σ α : Type} (D : C.Coalition)
    (impl : QueryImpl (LocalSpec C) (StateT σ ProbComp))
    (oa : OracleComp (LocalSpec C) α) (q : ℕ) (hq : IsQueryBoundP oa Counted q) (s : σ)
    (hsetup : C.n.choose 2 ≤ q) :
    (Pr[fun keys : C.Pair → HashOutput => ¬ Function.Injective keys | $ᵗ (C.Pair → HashOutput)] +
      Pr[fun r => r.2.2 = true | $ᵗ (HiddenPair D → HashOutput) >>= fun keys =>
        (simulateQ (flagImpl impl (PairKeyHit D) keys) oa).run (s, false)]).toReal ≤
      seedHitError C q := by
  have h : Pr[fun keys : C.Pair → HashOutput => ¬ Function.Injective keys | $ᵗ (C.Pair → HashOutput)] +
      Pr[fun r => r.2.2 = true | $ᵗ (HiddenPair D → HashOutput) >>= fun keys =>
        (simulateQ (flagImpl impl (PairKeyHit D) keys) oa).run (s, false)] ≤
      (((C.n.choose (C.t - 1) + C.n ^ 2) * q : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    refine (add_le_add pairKeyCollision_bound (pairKeyHit_bound D impl oa q hq s)).trans ?_
    rw [← ENNReal.add_div, ← Nat.cast_mul, ← Nat.cast_add]
    gcongr
    exact pairKeyCollision_hit_arith D q hsetup
  exact toReal_le_div h

/-! ## Request transport -/

/-- The exact request-level assembly still needed by D16. This generalizes `emulatedOracles_run`:
only PRF terms must already be cached; honest-pair masks may be fresh. It compares the complete
answer, signing state, private table and public cache, so it can be iterated over requests.
The maps merely reassociate the two `StateT` states. No corruption query belongs to the static
lifetime interface. Distinct pair keys are explicit and paid by `pairKeyCollision_add_hit_bound`.
-/
def PrivateSigningTransport : Prop :=
  ∀ (prims : Primitives) (D : C.Coalition) (keys : C.Pair → HashOutput),
    Function.Injective keys →
    ∀ (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
      (trees : Fin (2 ^ layerHeight) → Option BottomTree) (value : Point → Digest)
      (term : C.Term → Point → Digest) (q : TsigQuery C) (st : TsigState C) (g : HashCache C),
      (∀ i, q ≠ .corrupt i) →
      (∀ x, RequestPoint q x → PrfValueCached g seeds x ∧
        value x = cachedPrfValue g seeds x ∧ ∀ T, term T x = cachedPrf g (seeds T) x) →
      (fun r => (r.1, (splitMasks D keys r.2).1, (splitMasks D keys r.2).2)) <$>
        (simulateQ (worldAnswer prims)
          ((tsigOracles SigningCoreProof.honestLift
            (signerDealt parameter (dealtKeys parameter seeds keys) top trees seeds) q).run st)).run g =
      (fun r => (r.1.1, r.1.2, r.2)) <$>
        (simulateQ (localAnswer prims)
          (((privateOracles D (fun p => keys p.1) parameter top trees value term q).run st).run
            (splitMasks D keys g).1)).run (splitMasks D keys g).2

/-- info: 'ThresholdLeanXmssSecurity.LifetimeMasks.pairKeyHit_bound_of_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairKeyHit_bound_of_prefix

/-- info: 'ThresholdLeanXmssSecurity.LifetimeMasks.privateMask_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms privateMask_run

/-- info: 'ThresholdLeanXmssSecurity.LifetimeMasks.pairMask_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairMask_comm

/-- info: 'ThresholdLeanXmssSecurity.LifetimeMasks.privateMask_real_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms privateMask_real_run

/-- info: 'ThresholdLeanXmssSecurity.LifetimeMasks.splitMasks_mask_of_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitMasks_mask_of_miss

/-- info: 'ThresholdLeanXmssSecurity.LifetimeMasks.pairKeyHit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairKeyHit_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeMasks.pairKeyHit_bound_seedHitError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairKeyHit_bound_seedHitError

/-- info: 'ThresholdLeanXmssSecurity.LifetimeMasks.pairKeyCollision_add_hit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairKeyCollision_add_hit_bound

end ThresholdLeanXmssSecurity.LifetimeMasks
