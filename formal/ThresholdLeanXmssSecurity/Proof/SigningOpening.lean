import ThresholdLeanXmssSecurity.Proof.SigningGuessProof
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# Fixed-cap hits for the uncharged lane of the signing proof

This module holds the tools for one capped flag of the uncharged lane and the definitions of its
events.

## The calls of the uncharged lane

`SeedHitProof.signCost` gives cost 0 only to uniform sampling. Every hash call is counted, in both
copies, the final verification included. Each call type has one target.

| Call | Target | Side |
| --- | --- | --- |
| `commitmentInput P e ρ` | `ρ_e` before the first `round1` at `e` | input |
| `randomizerInput P lay e ρ m` | `ρ` of `(lay, e)` before its release | input |
| `chainInput P e l p v` | the honest bottom chain value at `p` below the opened position | input |
| `topChainInput P b l p v` | the honest top chain value at `p` below the opened position | input |
| `encodingInput P e (m, R)` | the selected digest at `e` | output |
| `topEncodingInput P b (root, R)` | the honest top digest at `b` | output |

All rows are counted calls. The verification in `tsigFinish` makes chain and encoding calls on the
forged values, so a guess or a partner can first appear there. A `.prf` call on a hidden seed raises
the `hiddenHit` flag instead, and the lane requires that flag to stay false.

## The tools

* `probEvent_uniform_key_eq` gives the chance `1 / |T|` that one coordinate of uniform secrets
  `s : K → T` equals a fixed point.
* `countImpl` counts the calls, and `cappedCall` lets only the first `q` raise the flag.
  `revealImpl` adds a reveal oracle for the secrets. A capped input-side call hits an unrevealed
  secret, and any other capped call hits an output-side target.
* `revealImpl_run_congr`, `revealImpl_inr_run` and `sum_uniform_reveal_le` average a run over the
  secret of one key at its reveal.
* `simulateQ_sticky` keeps a sticky bad event on the state through a run.

## The events

* `hiddenCandidate` parses the one hidden value that a hash input carries.
  `SigningGuessProof.commitmentInput_key_eq` and `SigningGuessProof.randomizerInput_key_eq` fix the
  key of an opening, and the tweak bytes fix the step and the layer.
* `openingOracles` is `flaggedOracles` with a log of the unreleased candidates of the adversary
  calls (`openingOracles_forget`). The release of an opening is the first `round1` at `e` (bottom)
  or the `tree b` query (top). A chain value below the opened position is never released.
* `HiddenInputHit` compares the log with the targets at the end. An opening is read from the final
  cache by `cachedOpening`, and it is absent if a PRF term is not in the final cache.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningOpeningProof

section KeyedHit

variable {κ σ β K T : Type} {spec : OracleSpec κ}
  [Fintype K] [DecidableEq K] [Fintype T] [DecidableEq T]
  [SampleableType (K → T)]

/-- One coordinate of uniform secrets `s : K → T` equals a fixed point with probability
`1 / |T|`. -/
theorem probEvent_uniform_key_eq (key : K) (x : T) :
    Pr{let s : K → T ← $ᵗ (K → T)}[s key = x] = (Fintype.card T : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample]
  have hfil : (Finset.univ.filter fun s : K → T => s key = x).card =
      Fintype.card T ^ (Fintype.card K - 1) := by
    have := Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset T) key (Finset.mem_univ x)
    simpa using this
  have hK : Fintype.card K = (Fintype.card K - 1) + 1 := by
    have : 0 < Fintype.card K := Fintype.card_pos_iff.2 ⟨key⟩
    omega
  have hT : (Fintype.card T : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card T := Fintype.card_pos_iff.2 ⟨x⟩
    exact_mod_cast this.ne'
  have hpow : ((Fintype.card T : ℝ≥0∞) ^ (Fintype.card K - 1)) ≠ 0 := pow_ne_zero _ hT
  rw [hfil, Fintype.card_fun, hK, pow_succ, Nat.cast_mul, Nat.add_sub_cancel, Nat.cast_pow]
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hpow) (Or.inl (by simp)), mul_comm, ← mul_assoc,
    ENNReal.mul_inv_cancel hpow (by simp), one_mul]

end KeyedHit

section RevealHit

attribute [local instance] Classical.propDecidable

variable {κ σ β K T : Type} {spec : OracleSpec κ}
  [Fintype K] [DecidableEq K] [Fintype T] [DecidableEq T] [SampleableType (K → T)]

/-- The reveal oracle returns the secret of a key. -/
abbrev RevealSpec (K T : Type) : OracleSpec K := fun _ => T

/-- The handler `impl` with a reveal oracle and a flag. The state holds the revealed secrets. A
reveal stores the secret of its key and returns it. A call `t` that is `counted` in the state before
it raises the flag in one of two ways.

* An input-side call hits when the secret of `keyOf t` is not revealed yet and equals `point t`.
* Any other call hits when its answer satisfies `outHit` (an output-side target).
-/
def revealImpl (impl : QueryImpl spec (StateT σ ProbComp)) (counted : κ → σ → Prop)
    (inputSide : κ → Prop) (outHit : (t : κ) → σ → spec t × σ → Prop)
    (keyOf : κ → K) (point : κ → T) (s : K → T) :
    QueryImpl (spec + RevealSpec K T) (StateT (σ × (K → Option T) × Bool) ProbComp)
  | .inl t => StateT.mk fun st => (fun x => (x.1, (x.2, st.2.1, st.2.2 || decide (counted t st.1 ∧
      ((inputSide t ∧ st.2.1 (keyOf t) = none ∧ s (keyOf t) = point t) ∨
        (¬inputSide t ∧ outHit t st.1 x)))))) <$> (impl t).run st.1
  | .inr k => StateT.mk fun st => pure ((st.2.1 k).getD (s k),
      (st.1, Function.update st.2.1 k (some ((st.2.1 k).getD (s k))), st.2.2))

variable (impl : QueryImpl spec (StateT σ ProbComp)) (counted : κ → σ → Prop) (inputSide : κ → Prop)
  (outHit : (t : κ) → σ → spec t × σ → Prop) (p : κ → Prop) (keyOf : κ → K) (point : κ → T)

omit [Fintype K] [Fintype T] [SampleableType (K → T)] in
theorem revealImpl_query_bind_run (s : K → T) (t : κ ⊕ K)
    (k : (spec + RevealSpec K T) t → OracleComp (spec + RevealSpec K T) β) (st : σ × (K → Option T) × Bool) :
    (simulateQ (revealImpl impl counted inputSide outHit keyOf point s)
        (liftM ((spec + RevealSpec K T).query t) >>= k)).run st =
      (revealImpl impl counted inputSide outHit keyOf point s t).run st >>= fun x =>
        (simulateQ (revealImpl impl counted inputSide outHit keyOf point s) (k x.1)).run x.2 := by
  simp

omit [Fintype K] [Fintype T] [SampleableType (K → T)] in
/-- A run reads the secrets only at keys that are not revealed yet. -/
theorem revealImpl_run_congr (s s' : K → T) (oa : OracleComp (spec + RevealSpec K T) β) :
    ∀ (σ₀ : σ) (stored : K → Option T) (b : Bool), (∀ k, stored k = none → s k = s' k) →
      (simulateQ (revealImpl impl counted inputSide outHit keyOf point s) oa).run (σ₀, stored, b) =
        (simulateQ (revealImpl impl counted inputSide outHit keyOf point s') oa).run (σ₀, stored, b) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intros; simp
  | query_bind t k ih =>
    intro σ₀ stored b hs
    rw [revealImpl_query_bind_run, revealImpl_query_bind_run]
    rcases t with t | key
    · have hflag : ∀ x : spec t × σ, decide (counted t σ₀ ∧
          ((inputSide t ∧ stored (keyOf t) = none ∧ s (keyOf t) = point t) ∨
            (¬inputSide t ∧ outHit t σ₀ x))) = decide (counted t σ₀ ∧
          ((inputSide t ∧ stored (keyOf t) = none ∧ s' (keyOf t) = point t) ∨
            (¬inputSide t ∧ outHit t σ₀ x))) := by
        intro x
        by_cases h : stored (keyOf t) = none
        · rw [hs _ h]
        · simp [h]
      simp only [revealImpl, StateT.run_mk, hflag, bind_map_left]
      refine bind_congr fun x => ?_
      exact ih x.1 _ _ _ hs
    · have hv : (stored key).getD (s key) = (stored key).getD (s' key) := by
        cases h : stored key with
        | none => simp [hs _ h]
        | some v => simp
      simp only [revealImpl, StateT.run_mk, hv, pure_bind]
      refine ih _ _ _ _ fun k' hk' => hs k' ?_
      by_cases hk : k' = key
      · subst hk; simp at hk'
      · simpa [Function.update_of_ne hk] using hk'

omit [Fintype K] [Fintype T] [SampleableType (K → T)] in
/-- A reveal returns the stored secret, or else the secret itself, and stores it. -/
theorem revealImpl_inr_run (s : K → T) (key : K) (k : T → OracleComp (spec + RevealSpec K T) β)
    (σ₀ : σ) (stored : K → Option T) (b : Bool) :
    (simulateQ (revealImpl impl counted inputSide outHit keyOf point s)
        (liftM ((spec + RevealSpec K T).query (.inr key)) >>= k)).run (σ₀, stored, b) =
      (simulateQ (revealImpl impl counted inputSide outHit keyOf point s) (k ((stored key).getD (s key)))).run
        (σ₀, Function.update stored key (some ((stored key).getD (s key))), b) := by
  rw [revealImpl_query_bind_run]
  simp only [revealImpl, StateT.run_mk, pure_bind]

omit [DecidableEq T] in
/-- Averaging at a reveal. A quantity that does not read the secret of `key` and is bounded for
each fixed value of that secret is bounded when the value is the secret itself. -/
theorem sum_uniform_reveal_le (key : K) (H : T → (K → T) → ℝ≥0∞) (B : ℝ≥0∞)
    (hH : ∀ v s w, H v (Function.update s key w) = H v s)
    (hih : ∀ v, ∑ s, Pr{let z ← $ᵗ (K → T)}[z = s] * H v s ≤ B) :
    ∑ s, Pr{let z ← $ᵗ (K → T)}[z = s] * H (s key) s ≤ B := by
  have hswap : (Fintype.card T : ℝ≥0∞) * ∑ s, H (s key) s = ∑ v, ∑ s, H v s := by
    have hinv : Function.Involutive fun x : T × (K → T) => (x.2 key, Function.update x.2 key x.1) := by
      intro x
      simp
    calc (Fintype.card T : ℝ≥0∞) * ∑ s, H (s key) s = ∑ v : T, ∑ s, H (s key) s := by
          simp [Finset.sum_const, Finset.card_univ]
      _ = ∑ x : T × (K → T), H (x.2 key) x.2 := by rw [Fintype.sum_prod_type]
      _ = ∑ x : T × (K → T), H (x.2 key) (Function.update x.2 key x.1) := by
          simp only [hH]
      _ = ∑ x : T × (K → T), H x.1 x.2 := Equiv.sum_comp hinv.toPerm fun x => H x.1 x.2
      _ = ∑ v, ∑ s, H v s := by rw [Fintype.sum_prod_type]
  have hT : (Fintype.card T : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card T := Fintype.card_pos_iff.2 ⟨(Classical.arbitrary (K → T)) key⟩
    exact_mod_cast this.ne'
  rw [← ENNReal.mul_le_mul_iff_right hT (ENNReal.natCast_ne_top _)]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton] at hih ⊢
  rw [← Finset.mul_sum, mul_left_comm, hswap, Finset.mul_sum]
  calc _ ≤ ∑ _v : T, B := Finset.sum_le_sum fun v _ => by rw [Finset.mul_sum]; exact hih v
    _ = _ := by simp [Finset.sum_const, Finset.card_univ]

/-- The handler `impl` with a count of the calls that satisfy `p`. -/
def countImpl (impl : QueryImpl spec (StateT σ ProbComp)) (p : κ → Prop) :
    QueryImpl spec (StateT (σ × ℕ) ProbComp) := fun t =>
  StateT.mk fun st => (fun x => (x.1, (x.2, st.2 + if p t then 1 else 0))) <$> (impl t).run st.1

/-- The capped flag. Only the first `q` calls that satisfy `p` can raise it. -/
abbrev cappedCall (p : κ → Prop) (q : ℕ) : κ → σ × ℕ → Prop := fun t st => p t ∧ st.2 < q

end RevealHit

section TrueOpening

open HashSig LeanXmss ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- The key of an opening, a layer and a key index. The opening of `(lay, e)` is `F` at
`.randomizer lay e`. -/
abbrev OpeningKey := Layer × KeyIndex

/-- The opening of a key from a cache, or `none` if the cache misses a term of `F`. -/
def cachedOpening (x : SigningSecurityProof.Keys3 C) (cache : HashCache C) (key : OpeningKey) :
    Option Digest :=
  (fun terms : List Digest => terms.foldl (· ^^^ ·) 0) <$>
    C.terms.mapM fun T => truncateHash <$> cache (.prf (x.2.1 T) (.randomizer key.1 key.2))

/-- A hidden value of the uncharged lane that an input-side call can carry.

* `opening lay e` is `ρ` of `(lay, e)`, the input of `commitmentInput` and `randomizerInput`.
* `bottomChain e l p` and `topChain b l p` are the honest chain values at position `p`, the input
  of `chainInput` and `topChainInput`. A `Guess` forges one below the opened position.
-/
inductive HiddenKey
  | opening (lay : Layer) (e : KeyIndex)
  | bottomChain (e : XmssSecurity.LeafIndex) (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep)
  | topChain (b : XmssSecurity.TopIndex) (l : XmssSecurity.ChainIndex) (p : XmssSecurity.ChainStep)

/-- The hidden key and the candidate value that a hash input carries under the parameter `P`.
Each input carries at most one candidate. -/
def hiddenCandidate (P : PublicParameter) (input : HashInput) : Option (HiddenKey × Digest) :=
  if h : ∃ e ρ, input = commitmentInput P e ρ then some (.opening bottomLayer h.choose, h.choose_spec.choose)
  else if h : ∃ lay e ρ message, input = randomizerInput P lay e ρ message then
    some (.opening h.choose h.choose_spec.choose, h.choose_spec.choose_spec.choose)
  else if h : ∃ e l p v, input = XmssSecurity.Concrete.CacheView.chainInput P e l p v then
    some (.bottomChain h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose,
      h.choose_spec.choose_spec.choose_spec.choose)
  else if h : ∃ b l p v, input = XmssSecurity.Concrete.CacheView.topChainInput P b l p v then
    some (.topChain h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose,
      h.choose_spec.choose_spec.choose_spec.choose)
  else none

/-- The released hidden values at a call. Round 1 at a bottom key binds its message and releases
its opening. The `tree b` query releases the opening of top key `b`. A chain value is never
released at a call; its target at the end is `none` when the honest signature opened it. -/
def Released (st : TsigState C) (trees : Finset (Fin (2 ^ layerHeight))) : HiddenKey → Prop
  | .opening lay e => (lay = bottomLayer ∧ st.bound e ≠ none) ∨ (lay = topLayer ∧ ∃ b ∈ trees, topKey b = e)
  | _ => False

/-- The candidates of an adversary call that carry an unreleased hidden value. -/
def unreleasedCandidates (P : PublicParameter) (st : TsigState C) (trees : Finset (Fin (2 ^ layerHeight))) :
    (LocalSpec C).Domain → List (HiddenKey × Digest)
  | .inr (.inl (.hash input)) => match hiddenCandidate P input with
    | some c => if Released st trees c.1 then [] else [c]
    | none => []
  | _ => []

/-- The trees that a game query releases. -/
def releasedTrees (trees : Finset (Fin (2 ^ layerHeight))) : (TsigSpec C).Domain → Finset (Fin (2 ^ layerHeight))
  | .tree b => insert b trees
  | _ => trees

/-- `flaggedOracles` with the released trees and the log of the unreleased candidates of the
adversary calls. -/
def openingOracles (x : SigningSecurityProof.Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C))) :
    QueryImpl (LocalSpec C + TsigSpec C)
      (StateT ((TsigState C × Bool) × Finset (Fin (2 ^ layerHeight)) × List (HiddenKey × Digest))
        (OracleComp (WorldSpec C)))
  | .inl t => StateT.mk fun p => (fun z => (z.1, (z.2, p.2.1,
      p.2.2 ++ unreleasedCandidates dealt.parameter p.1.1 p.2.1 t))) <$>
        (SigningCoreProof.flaggedOracles x dealt (.inl t)).run p.1
  | .inr q => StateT.mk fun p => (fun z => (z.1, (z.2, releasedTrees p.2.1 q, p.2.2))) <$>
        (SigningCoreProof.flaggedOracles x dealt (.inr q)).run p.1

theorem openingOracles_forget (x : SigningSecurityProof.Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C))) (t : (LocalSpec C + TsigSpec C).Domain)
    (s : TsigState C × Bool) (b : Finset (Fin (2 ^ layerHeight)) × List (HiddenKey × Digest)) :
    (fun z => (z.1, z.2.1)) <$> (openingOracles x dealt t).run (s, b) =
      (SigningCoreProof.flaggedOracles x dealt t).run s := by
  rcases t with t | q
  · simp [openingOracles, Functor.map_map]
  · simp [openingOracles, Functor.map_map]

/-- The target of a hidden key at the end of the run. An opening is read from the final cache.
`chainTarget` gives the honest chain value at a position below the opened one, and `none` at an
opened position. -/
def hiddenTarget (x : SigningSecurityProof.Keys3 C) (chainTarget : HiddenKey → Option Digest)
    (cache : HashCache C) : HiddenKey → Option Digest
  | .opening lay e => cachedOpening x cache (lay, e)
  | key => chainTarget key

/-- The combined input-side flag of the uncharged lane. An adversary call carried a hidden value
before its release. -/
def HiddenInputHit (x : SigningSecurityProof.Keys3 C) (chainTarget : HiddenKey → Option Digest)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × List (HiddenKey × Digest)) ×
      HashCache C × ℕ) : Prop :=
  ∃ c ∈ r.1.2, hiddenTarget x chainTarget r.2.1 c.1 = some c.2

end TrueOpening

section Planting

open OracleComp.ProgramLogic.Relational

variable {ι σ α : Type} {spec : OracleSpec ι}

/-- A postcondition that holds for every right output and every left value holds on a coupling. -/
theorem relTriple_of_support_right {α' β' : Type} {oa : ProbComp α'} {ob : ProbComp β'} {R : α' → β' → Prop}
    (h : ∀ b ∈ support ob, ∀ a, R a b) : RelTriple oa ob R :=
  relTriple_symm (relTriple_of_support_left fun b hb a => h b hb a)

/-- A sticky bad event on the state survives a run. -/
theorem simulateQ_sticky (impl : QueryImpl spec (StateT σ ProbComp)) (Bad : σ → Prop)
    (hsticky : ∀ t s, Bad s → ∀ b ∈ support ((impl t).run s), Bad b.2) (oa : OracleComp spec α) :
    ∀ s, Bad s → ∀ b ∈ support ((simulateQ impl oa).run s), Bad b.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s hs b hb
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hb
    subst hb
    exact hs
  | query_bind t k ih =>
    intro s hs b hb
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hb
    obtain ⟨x, hx, hb⟩ := hb
    exact ih x.1 x.2 (hsticky t s hs x hx) b hb

variable {Q : Type} [DecidableEq Q] {hashSpec : OracleSpec Q}

end Planting

end SigningOpeningProof

end ThresholdLeanXmssSecurity
