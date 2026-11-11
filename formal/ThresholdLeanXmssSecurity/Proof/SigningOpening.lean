import ThresholdLeanXmssSecurity.Proof.SigningUncharged
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# Fixed-cap hits for the uncharged lane of the signing proof

`SigningGuessProof.UnchargedLaneBound` asks `Pr[UnchargedWin] ≤ q / 2 ^ 128` with one unit for the
whole lane. A union of one bound for each event gives `3q / 2 ^ 128`, so one capped flag must
dominate the lane. This module holds the tools for that flag and the definitions of its events.

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

* `probEvent_hit_keyed_le` and `probEvent_hit_keyed_digest_le` bound `q` calls that each aim at one
  key of uniform secrets `s : K → T` by `q / |T|`, under `IsQueryBoundP`.
* The signing budget is support-wise (`SigningCostProof.exposedRun_count_le`). It does not give
  `IsQueryBoundP`, which quantifies over every answer. The lazy oracle never gives two answers to
  one input. An adversary that asks `H(u)` twice and makes `q + 1` more calls only when the answers
  differ has a support-wise count of two, but it is not `IsQueryBoundP` for `q`.
* So the lane uses the capped form. `countImpl` counts the calls, and `cappedCall` lets only the
  first `q` raise the flag. `revealImpl` adds a reveal oracle for the secrets. A capped input-side
  call hits an unrevealed secret, and any other capped call hits an output-side target.
  `probEvent_hit_capped_le` bounds the flag by `q / |T|` with no query bound, if each output-side
  call hits with probability at most `1 / |T|` (`hout`). `probEvent_le_of_capped` is its 128-bit
  form for an event that the flag dominates.
* An output-side target fixed by the state meets a fresh 256-bit answer with probability `2^-128`.
  So the mixed step holds. The selected digest must be a target fixed by the state from the start,
  which the hybrid gives by sampling it eagerly.
* `relTriple_withCaching_planted` shows that a value planted at an unqueried point of a caching
  oracle is invisible until the other run queries that point.

## The events

* `hiddenCandidate` parses the one hidden value that a hash input carries. `commitmentInput_key_eq`
  and `randomizerInput_key_eq` fix the key of an opening, and the tweak bytes fix the step and the
  layer.
* `openingRun` is `exposedRun` with a log of the unreleased candidates of the adversary hash calls
  (`openingRun_forget`). The release of an opening is the first `round1` at `e` (bottom) or the
  `tree b` query (top). A chain value below the opened position is never released.
* `HiddenInputHit` compares the log with the targets at the end. An opening is read from the final
  cache by `cachedOpening`, and it is absent if a PRF term is not in the final cache.
  `TrueOpeningHit` is its opening part.

## The hybrid

The secrets are the openings and the hidden chain values. The output targets are the selected
digest of each bottom key and the honest top digest of each top key, sampled at the start.

* Before a release, an honest computation that reads a hidden value does not query the oracle on
  an input that carries it. It takes a fresh answer and keeps it in a pending table. The commitment
  `c_e` of `dealt.bottom` and the honest chain walks are such answers.
* At the release, the pending answers are planted at the true inputs. They agree with the real run
  until the adversary queries a planted input (`relTriple_withCaching_planted`), which is a hit.
* The opening `ρ_e = F(x)` takes its value from the secret at the release. The release picks the
  least term `T` that `st.corrupt` does not reveal at that time, samples the other terms lazily, and
  programs the entry of `.prf seed_T x` so that the sum is the secret. The upper 128 bits of that
  entry are fresh. Corruption is adaptive, so `T` cannot be fixed earlier. The two runs agree until
  `hiddenHit`.
* The honest grind at `e` returns the presampled selected digest. A partner is then a fresh answer
  that meets it.
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
    Pr[fun s : K → T => s key = x | $ᵗ (K → T)] = (Fintype.card T : ℝ≥0∞)⁻¹ := by
  rw [probEvent_uniformSample]
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

/-- A computation with at most `q` counted calls, each aimed at one key and one point, run on a
handler that never reads the uniform secrets `s : K → T`, hits its key with probability at most
`q / |T|`. -/
theorem probEvent_hit_keyed_le (impl : QueryImpl spec (StateT σ ProbComp)) (p : κ → Prop)
    [DecidablePred p] (keyOf : κ → K) (point : κ → T) (oa : OracleComp spec β) (q : ℕ)
    (hq : IsQueryBoundP oa p q) (σ₀ : σ) :
    Pr[fun r => r.2.2 = true | $ᵗ (K → T) >>= fun s =>
      (simulateQ (flagImpl impl (fun t s => p t ∧ s (keyOf t) = point t) s) oa).run (σ₀, false)] ≤
        q * (Fintype.card T : ℝ≥0∞)⁻¹ :=
  probEvent_flag_le impl _ _ p _ (fun _ _ h => h.1)
    (fun t _ => le_trans (probEvent_mono fun _ _ h => h.2)
      (le_of_eq (probEvent_uniform_key_eq (keyOf t) (point t)))) oa q σ₀ hq

/-- The 128-bit case of `probEvent_hit_keyed_le`. The bound is `q / 2 ^ 128`. -/
theorem probEvent_hit_keyed_digest_le [SampleableType (K → LeanXmss.Digest)]
    (impl : QueryImpl spec (StateT σ ProbComp)) (p : κ → Prop) [DecidablePred p]
    (keyOf : κ → K) (point : κ → LeanXmss.Digest) (oa : OracleComp spec β) (q : ℕ)
    (hq : IsQueryBoundP oa p q) (σ₀ : σ) :
    Pr[fun r => r.2.2 = true | $ᵗ (K → LeanXmss.Digest) >>= fun s =>
      (simulateQ (flagImpl impl (fun t s => p t ∧ s (keyOf t) = point t) s) oa).run (σ₀, false)] ≤
        q / 2 ^ 128 := by
  refine (probEvent_hit_keyed_le impl p keyOf point oa q hq σ₀).trans (le_of_eq ?_)
  have hcard : Fintype.card LeanXmss.Digest = 2 ^ 128 := by
    unfold LeanXmss.Digest LeanXmss.digestBits; exact card_bitVec 128
  rw [hcard, div_eq_mul_inv]
  norm_num

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
/-- A counted call raises the flag exactly when it hits. -/
theorem revealImpl_inl_run (s : K → T) (t : κ) (k : spec t → OracleComp (spec + RevealSpec K T) β)
    (σ₀ : σ) (stored : K → Option T) :
    (simulateQ (revealImpl impl counted inputSide outHit keyOf point s)
        (liftM ((spec + RevealSpec K T).query (.inl t)) >>= k)).run (σ₀, stored, false) =
      (impl t).run σ₀ >>= fun x =>
        (simulateQ (revealImpl impl counted inputSide outHit keyOf point s) (k x.1)).run
          (x.2, stored, decide (counted t σ₀ ∧
            ((inputSide t ∧ stored (keyOf t) = none ∧ s (keyOf t) = point t) ∨
              (¬inputSide t ∧ outHit t σ₀ x)))) := by
  rw [revealImpl_query_bind_run]
  simp only [revealImpl, StateT.run_mk, bind_map_left, Bool.false_or]

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
    (hih : ∀ v, ∑ s, Pr[= s | $ᵗ (K → T)] * H v s ≤ B) :
    ∑ s, Pr[= s | $ᵗ (K → T)] * H (s key) s ≤ B := by
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
  simp only [probOutput_uniformSample] at hih ⊢
  rw [← Finset.mul_sum, mul_left_comm, hswap, Finset.mul_sum]
  calc _ ≤ ∑ _v : T, B := Finset.sum_le_sum fun v _ => by rw [Finset.mul_sum]; exact hih v
    _ = _ := by simp [Finset.sum_const, Finset.card_univ]

/-- The handler `impl` with a count of the calls that satisfy `p`. -/
def countImpl (impl : QueryImpl spec (StateT σ ProbComp)) (p : κ → Prop) :
    QueryImpl spec (StateT (σ × ℕ) ProbComp) := fun t =>
  StateT.mk fun st => (fun x => (x.1, (x.2, st.2 + if p t then 1 else 0))) <$> (impl t).run st.1

/-- The capped flag. Only the first `q` calls that satisfy `p` can raise it. -/
abbrev cappedCall (p : κ → Prop) (q : ℕ) : κ → σ × ℕ → Prop := fun t st => p t ∧ st.2 < q

/-- The mixed capped bound from the count `n`. Each capped call hits with probability at most
`1 / |T|`. An input-side call hits an unrevealed uniform secret. Another call hits an output-side
target, with probability at most `1 / |T|` by `hout`. No query bound is needed. -/
theorem probEvent_capped_le_aux (q : ℕ)
    (outHit : (t : κ) → σ × ℕ → spec t × (σ × ℕ) → Prop)
    (hout : ∀ t σ₀ n, p t → ¬inputSide t →
      Pr[outHit t (σ₀, n) | (countImpl impl p t).run (σ₀, n)] ≤ (Fintype.card T : ℝ≥0∞)⁻¹)
    (oa : OracleComp (spec + RevealSpec K T) β) :
    ∀ (σ₀ : σ) (n : ℕ) (stored : K → Option T),
      Pr[fun r => r.2.2.2 = true | $ᵗ (K → T) >>= fun s =>
        (simulateQ (revealImpl (countImpl impl p) (cappedCall p q) inputSide outHit keyOf point s) oa).run
          ((σ₀, n), stored, false)] ≤ (q - n : ℕ) * (Fintype.card T : ℝ≥0∞)⁻¹ := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro σ₀ n stored
    simp [Function.comp_def]
  | query_bind t k ih =>
    intro σ₀ n stored
    rcases t with t | key
    · set ε : ℝ≥0∞ := (Fintype.card T : ℝ≥0∞)⁻¹
      set I := revealImpl (countImpl impl p) (cappedCall p q) inputSide outHit keyOf point
      set mx := (countImpl impl p t).run (σ₀, n)
      set hit : (K → T) → spec t × (σ × ℕ) → Prop := fun s x => cappedCall p q t (σ₀, n) ∧
        ((inputSide t ∧ stored (keyOf t) = none ∧ s (keyOf t) = point t) ∨
          (¬inputSide t ∧ outHit t (σ₀, n) x)) with hhitdef
      set g : (K → T) → spec t × (σ × ℕ) → ℝ≥0∞ := fun s x =>
        Pr[fun r => r.2.2.2 = true | (simulateQ (I s) (k x.1)).run (x.2, stored, false)] with hg
      have hsupp : ∀ x ∈ support mx, x.2.2 = n + if p t then 1 else 0 := by
        intro x hx
        simp only [mx, countImpl, StateT.run_mk, support_map, Set.mem_image] at hx
        obtain ⟨y, -, rfl⟩ := hx
        rfl
      have key : ∀ s, Pr[fun r => r.2.2.2 = true | (simulateQ (I s)
          (liftM ((spec + RevealSpec K T).query (.inl t)) >>= k)).run ((σ₀, n), stored, false)] ≤
          ∑' x, Pr[= x | mx] * ((if hit s x then 1 else 0) + g s x) := by
        intro s
        rw [revealImpl_inl_run, probEvent_bind_eq_tsum]
        refine ENNReal.tsum_le_tsum fun x => ?_
        gcongr
        by_cases hs : hit s x
        · rw [if_pos hs]
          exact le_trans probEvent_le_one le_self_add
        · have hs' : decide (hit s x) = false := decide_eq_false hs
          rw [if_neg hs, zero_add, hg]
          exact le_of_eq (by congr; convert hs')
      have hsum : ∑' x, Pr[= x | mx] * (∑' s, Pr[= s | $ᵗ (K → T)] * g s x) ≤
          (q - (n + if p t then 1 else 0) : ℕ) * ε := by
        calc _ ≤ ∑' x, Pr[= x | mx] * ((q - (n + if p t then 1 else 0) : ℕ) * ε) := by
              refine ENNReal.tsum_le_tsum fun x => ?_
              by_cases hx : x ∈ support mx
              · gcongr
                have := ih x.1 x.2.1 x.2.2 stored
                rw [probEvent_bind_eq_tsum] at this
                rw [← hsupp x hx]
                exact this
              · simp [probOutput_eq_zero_of_not_mem_support hx]
          _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
      have hhit : ∑' s, Pr[= s | $ᵗ (K → T)] * ∑' x, Pr[= x | mx] * (if hit s x then 1 else 0) ≤
          if cappedCall p q t (σ₀, n) then ε else 0 := by
        by_cases hc : cappedCall p q t (σ₀, n)
        · rw [if_pos hc]
          by_cases hin : inputSide t
          · calc _ ≤ ∑' s, Pr[= s | $ᵗ (K → T)] *
                  (if stored (keyOf t) = none ∧ s (keyOf t) = point t then 1 else 0) := by
                  refine ENNReal.tsum_le_tsum fun s => ?_
                  gcongr
                  calc _ ≤ ∑' x, Pr[= x | mx] *
                        (if stored (keyOf t) = none ∧ s (keyOf t) = point t then 1 else 0) := by
                        refine ENNReal.tsum_le_tsum fun x => ?_
                        gcongr
                        by_cases h : stored (keyOf t) = none ∧ s (keyOf t) = point t
                        · rw [if_pos h]
                          split_ifs <;> simp
                        · have : ¬hit s x := fun hx => hx.2.elim (fun h' => h h'.2) (fun h' => h'.1 hin)
                          simp [this]
                    _ ≤ _ := by
                        rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
              _ ≤ ε := by
                  simp only [mul_ite, mul_one, mul_zero]
                  rw [← probEvent_eq_tsum_ite]
                  exact le_trans (probEvent_mono fun s _ h => h.2)
                    (le_of_eq (probEvent_uniform_key_eq (keyOf t) (point t)))
          · calc _ ≤ ∑' s, Pr[= s | $ᵗ (K → T)] * ε := by
                  refine ENNReal.tsum_le_tsum fun s => ?_
                  gcongr
                  have hiff : ∀ x, hit s x ↔ outHit t (σ₀, n) x := fun x =>
                    ⟨fun hx => hx.2.elim (fun h => (hin h.1).elim) (fun h => h.2),
                      fun hx => ⟨hc, Or.inr ⟨hin, hx⟩⟩⟩
                  simp only [hiff, mul_ite, mul_one, mul_zero]
                  rw [← probEvent_eq_tsum_ite]
                  exact hout t σ₀ n hc.1 hin
              _ ≤ ε := by
                  rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
        · rw [if_neg hc]
          have : ∀ s x, ¬hit s x := fun s x hx => hc hx.1
          simp [this]
      calc _ = ∑' s, Pr[= s | $ᵗ (K → T)] * Pr[fun r => r.2.2.2 = true | (simulateQ (I s)
            (liftM ((spec + RevealSpec K T).query (.inl t)) >>= k)).run ((σ₀, n), stored, false)] :=
            probEvent_bind_eq_tsum _ _ _
        _ ≤ ∑' s, Pr[= s | $ᵗ (K → T)] * ∑' x, Pr[= x | mx] * ((if hit s x then 1 else 0) + g s x) :=
            ENNReal.tsum_le_tsum fun s => by gcongr; exact key s
        _ = ∑' s, Pr[= s | $ᵗ (K → T)] * ∑' x, Pr[= x | mx] * (if hit s x then 1 else 0) +
            ∑' x, Pr[= x | mx] * (∑' s, Pr[= s | $ᵗ (K → T)] * g s x) := by
            simp only [mul_add, ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
            congr 1
            rw [ENNReal.tsum_comm]
            simp only [mul_left_comm]
        _ ≤ (if cappedCall p q t (σ₀, n) then ε else 0) +
            (q - (n + if p t then 1 else 0) : ℕ) * ε := add_le_add hhit hsum
        _ ≤ (q - n : ℕ) * ε := by
            by_cases hpt : p t
            · by_cases hn : n < q
              · rw [if_pos ⟨hpt, hn⟩, if_pos hpt, ← one_add_mul]
                gcongr
                exact_mod_cast (by omega : 1 + (q - (n + 1)) ≤ q - n)
              · rw [if_neg (fun h => hn h.2), if_pos hpt, zero_add]
                gcongr
                omega
            · rw [if_neg (fun h => hpt h.1), if_neg hpt, zero_add, add_zero]
    · cases hstored : stored key with
      | some v =>
        simp only [revealImpl_inr_run, hstored, Option.getD_some]
        exact ih v σ₀ n _
      | none =>
        simp only [revealImpl_inr_run, hstored, Option.getD_none]
        set H : T → (K → T) → ℝ≥0∞ := fun v s => Pr[fun r => r.2.2.2 = true |
          (simulateQ (revealImpl (countImpl impl p) (cappedCall p q) inputSide outHit keyOf point s)
            (k v)).run ((σ₀, n), Function.update stored key (some v), false)] with hHdef
        have hH : ∀ v s w, H v (Function.update s key w) = H v s := by
          intro v s w
          simp only [hHdef]
          rw [revealImpl_run_congr (countImpl impl p) (cappedCall p q) inputSide outHit keyOf point
            (Function.update s key w) s (k v) (σ₀, n) _ false]
          intro k' hk'
          have hne : k' ≠ key := by
            rintro rfl
            simp at hk'
          exact Function.update_of_ne hne _ _
        have hih : ∀ v, ∑ s, Pr[= s | $ᵗ (K → T)] * H v s ≤
            (q - n : ℕ) * (Fintype.card T : ℝ≥0∞)⁻¹ := by
          intro v
          have := ih v σ₀ n (Function.update stored key (some v))
          rwa [probEvent_bind_eq_tsum, tsum_fintype] at this
        rw [probEvent_bind_eq_tsum, tsum_fintype]
        calc _ = ∑ s, Pr[= s | $ᵗ (K → T)] * H (s key) s := by rw [hHdef]
          _ ≤ _ := sum_uniform_reveal_le key H _ hH hih

/-- The mixed capped hit bound. Any computation, run on a handler that never reads the uniform
secrets, raises the capped flag with probability at most `q / |T|`. -/
theorem probEvent_hit_capped_le (q : ℕ) (outHit : (t : κ) → σ × ℕ → spec t × (σ × ℕ) → Prop)
    (hout : ∀ t σ₀ n, p t → ¬inputSide t →
      Pr[outHit t (σ₀, n) | (countImpl impl p t).run (σ₀, n)] ≤ (Fintype.card T : ℝ≥0∞)⁻¹)
    (oa : OracleComp (spec + RevealSpec K T) β) (σ₀ : σ) :
    Pr[fun r => r.2.2.2 = true | $ᵗ (K → T) >>= fun s =>
      (simulateQ (revealImpl (countImpl impl p) (cappedCall p q) inputSide outHit keyOf point s) oa).run
        ((σ₀, 0), fun _ => none, false)] ≤ q * (Fintype.card T : ℝ≥0∞)⁻¹ := by
  simpa using probEvent_capped_le_aux impl inputSide p keyOf point q outHit hout oa σ₀ 0 (fun _ => none)

/-- The 128-bit case of `probEvent_hit_capped_le`, as a bound on any event that the capped flag
dominates. The bound is `q / 2 ^ 128`. -/
theorem probEvent_le_of_capped {γ : Type} [SampleableType (K → LeanXmss.Digest)]
    (run : ProbComp γ) (event : γ → Prop) (keyOf : κ → K) (point : κ → LeanXmss.Digest) (q : ℕ)
    (outHit : (t : κ) → σ × ℕ → spec t × (σ × ℕ) → Prop)
    (hout : ∀ t σ₀ n, p t → ¬inputSide t →
      Pr[outHit t (σ₀, n) | (countImpl impl p t).run (σ₀, n)] ≤ (2 ^ 128 : ℝ≥0∞)⁻¹)
    (oa : OracleComp (spec + RevealSpec K LeanXmss.Digest) β) (σ₀ : σ)
    (hcouple : Pr[event | run] ≤ Pr[fun r => r.2.2.2 = true | $ᵗ (K → LeanXmss.Digest) >>= fun s =>
      (simulateQ (revealImpl (countImpl impl p) (cappedCall p q) inputSide outHit keyOf point s) oa).run
        ((σ₀, 0), fun _ => none, false)]) :
    Pr[event | run] ≤ q / 2 ^ 128 := by
  have hcard : Fintype.card LeanXmss.Digest = 2 ^ 128 := by
    unfold LeanXmss.Digest LeanXmss.digestBits; exact card_bitVec 128
  have hout' : ∀ t σ₀ n, p t → ¬inputSide t →
      Pr[outHit t (σ₀, n) | (countImpl impl p t).run (σ₀, n)] ≤
        (Fintype.card LeanXmss.Digest : ℝ≥0∞)⁻¹ := by
    intro t σ₀ n hp hin
    rw [hcard]
    exact_mod_cast hout t σ₀ n hp hin
  refine hcouple.trans ((probEvent_hit_capped_le impl inputSide p keyOf point q outHit hout' oa σ₀).trans
    (le_of_eq ?_))
  rw [hcard, div_eq_mul_inv]
  norm_num

end RevealHit

section TrueOpening

open LeanXmss ThresholdLeanXmss

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

/-- `finalRun` with the log of the unreleased candidates. -/
def openingFinal (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    OracleComp (WorldSpec C)
      (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × List (HiddenKey × Digest)) := do
  let value := fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)
  let some (.top top) ← referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa)) value x.1 emptyTop .top
    | pure (((false, false), none), [])
  let dealt := dealtWith (fun oa => SigningSecurityProof.liftFree oa) x.1 (dealtKeys x.1 x.2.1 x.2.2) top value
  let r ← (simulateQ (openingOracles x dealt) (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)).run
    ((SigningCoreProof.tsigInit, false), ∅, [])
  (fun w => (((w.1, r.2.1.2), some (top, w.2.1, w.2.2)), r.2.2.2)) <$>
    SigningCoreProof.tsigFinish dealt (r.1, r.2.1.1)

theorem openingFinal_forget (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    Prod.fst <$> openingFinal A x = SigningDescentProof.finalRun A x := by
  unfold openingFinal SigningDescentProof.finalRun
  rw [map_bind]
  refine bind_congr fun r => ?_
  rcases r with _ | (top | tree)
  · simp
  · simp only [map_bind, Functor.map_map]
    rw [← SigningCoreProof.simulateQ_run_forget _ _ (openingOracles_forget x _) _ _ (∅, []), bind_map_left]
  · simp

/-- `exposedRun` with the log of the unreleased candidates. -/
def openingRun (prims : Primitives) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    ProbComp ((((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × List (HiddenKey × Digest)) ×
      HashCache C × ℕ) :=
  (simulateQ (SeedHitProof.withCount (SeedHitProof.signImpl prims)) (openingFinal A x)).run ((∅ : HashCache C), 0)

theorem openingRun_forget (prims : Primitives) (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun r => (r.1.1, r.2)) <$> openingRun prims A x = SigningDescentProof.exposedRun prims A x := by
  unfold openingRun SigningDescentProof.exposedRun
  rw [← openingFinal_forget, simulateQ_map, StateT.run_map]

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

/-- The true-opening hit, the opening part of `HiddenInputHit`. -/
def TrueOpeningHit (x : SigningSecurityProof.Keys3 C)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × List (HiddenKey × Digest)) ×
      HashCache C × ℕ) : Prop :=
  HiddenInputHit x (fun _ => none) r

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

/-- Identical until the right run touches. Two runs of one handler from related states give equal
outputs and related states, unless a sticky event fires on the right. -/
theorem relTriple_simulateQ_until (impl : QueryImpl spec (StateT σ ProbComp)) (Bad : σ → Prop)
    (Agree : σ → σ → Prop) (hsticky : ∀ t s, Bad s → ∀ b ∈ support ((impl t).run s), Bad b.2)
    (hstep : ∀ t s₁ s₂, Agree s₁ s₂ → RelTriple ((impl t).run s₁) ((impl t).run s₂)
      fun a b => Bad b.2 ∨ (a.1 = b.1 ∧ Agree a.2 b.2))
    (oa : OracleComp spec α) :
    ∀ s₁ s₂, Bad s₂ ∨ Agree s₁ s₂ → RelTriple ((simulateQ impl oa).run s₁) ((simulateQ impl oa).run s₂)
      fun a b => Bad b.2 ∨ (a.1 = b.1 ∧ Agree a.2 b.2) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s₁ s₂ hs
    by_cases hb : Bad s₂
    · exact relTriple_of_support_right fun b hb' _ => Or.inl
        (simulateQ_sticky impl Bad hsticky (pure a) s₂ hb b hb')
    · simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (Or.inr ⟨rfl, hs.resolve_left hb⟩)
  | query_bind t k ih =>
    intro s₁ s₂ hs
    by_cases hb : Bad s₂
    · exact relTriple_of_support_right fun b hb' _ => Or.inl
        (simulateQ_sticky impl Bad hsticky _ s₂ hb b hb')
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind]
    refine relTriple_bind (hstep t s₁ s₂ (hs.resolve_left hb)) fun a b hab => ?_
    rcases hab with hbad | ⟨heq, hagree⟩
    · exact relTriple_of_support_right fun c hc _ => Or.inl
        (simulateQ_sticky impl Bad hsticky _ b.2 hbad c hc)
    · rw [heq]
      exact ih b.1 a.2 b.2 (Or.inr hagree)

variable {Q : Type} [DecidableEq Q] {hashSpec : OracleSpec Q}

/-- Two caches agree off `u`, and the right cache misses `u`. The left cache may hold a planted
value at `u`. -/
def AgreeOff (u : Q) (c₁ c₂ : hashSpec.QueryCache) : Prop :=
  c₂ u = none ∧ ∀ w, w ≠ u → c₁ w = c₂ w

/-- One step of a caching oracle keeps two caches that agree off `u` in agreement, unless the right
cache gets `u`. -/
theorem relTriple_withCaching_step (so : QueryImpl hashSpec ProbComp) (u : Q) (t : Q)
    (c₁ c₂ : hashSpec.QueryCache) (h : AgreeOff u c₁ c₂) :
    RelTriple ((so.withCaching t).run c₁) ((so.withCaching t).run c₂)
      fun a b => (b.2 u).isSome ∨ (a.1 = b.1 ∧ AgreeOff u a.2 b.2) := by
  by_cases htu : t = u
  · subst htu
    rw [QueryImpl.withCaching_run_none so h.1]
    refine relTriple_of_support_right fun b hb _ => Or.inl ?_
    simp only [support_map, Set.mem_image] at hb
    obtain ⟨v, -, rfl⟩ := hb
    simp
  · have hw := h.2 t htu
    cases hc : c₂ t with
    | some y =>
      rw [QueryImpl.withCaching_run_some so hc, QueryImpl.withCaching_run_some so (hw.trans hc)]
      exact relTriple_pure_pure (Or.inr ⟨rfl, h⟩)
    | none =>
      rw [QueryImpl.withCaching_run_none so hc, QueryImpl.withCaching_run_none so (hw.trans hc)]
      refine relTriple_map (relTriple_post_mono (relTriple_refl (so t)) fun v v' hv => ?_)
      subst hv
      refine Or.inr ⟨rfl, ?_, fun w hwu => ?_⟩
      · simp [QueryCache.cacheQuery_of_ne _ _ (Ne.symm htu), h.1]
      · by_cases hwt : w = t
        · subst hwt
          simp [QueryCache.cacheQuery_self]
        · simp [QueryCache.cacheQuery_of_ne _ _ hwt, h.2 w hwu]

/-- A value planted at an unqueried point of a caching oracle is invisible until the right run
queries that point. For a planted commitment at `commitmentInput P e ρ_e`, the point is the opening
query, so the runs agree until a true-opening hit. -/
theorem relTriple_withCaching_planted (so : QueryImpl hashSpec ProbComp) (u : Q)
    (oa : OracleComp hashSpec α) (c₁ c₂ : hashSpec.QueryCache) (h : AgreeOff u c₁ c₂) :
    RelTriple ((simulateQ so.withCaching oa).run c₁) ((simulateQ so.withCaching oa).run c₂)
      fun a b => (b.2 u).isSome ∨ (a.1 = b.1 ∧ AgreeOff u a.2 b.2) := by
  refine relTriple_simulateQ_until so.withCaching (fun c => (c u).isSome) (AgreeOff u) ?_
    (relTriple_withCaching_step so u) oa c₁ c₂ (Or.inr h)
  intro t c hc b hb
  cases ht : c t with
  | some y =>
    rw [QueryImpl.withCaching_run_some so ht, support_pure, Set.mem_singleton_iff] at hb
    subst hb
    exact hc
  | none =>
    have htu : u ≠ t := by
      rintro rfl
      simp [ht] at hc
    rw [QueryImpl.withCaching_run_none so ht, support_map, Set.mem_image] at hb
    obtain ⟨v, -, rfl⟩ := hb
    simpa [QueryCache.cacheQuery_of_ne _ _ htu] using hc

end Planting

end SigningOpeningProof

end ThresholdLeanXmssSecurity

/--
info: 'ThresholdLeanXmssSecurity.SigningOpeningProof.probEvent_hit_keyed_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOpeningProof.probEvent_hit_keyed_le

/--
info: 'ThresholdLeanXmssSecurity.SigningOpeningProof.probEvent_hit_keyed_digest_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOpeningProof.probEvent_hit_keyed_digest_le

/--
info: 'ThresholdLeanXmssSecurity.SigningOpeningProof.probEvent_hit_capped_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOpeningProof.probEvent_hit_capped_le

/--
info: 'ThresholdLeanXmssSecurity.SigningOpeningProof.probEvent_le_of_capped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOpeningProof.probEvent_le_of_capped

/--
info: 'ThresholdLeanXmssSecurity.SigningOpeningProof.openingRun_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOpeningProof.openingRun_forget

/--
info: 'ThresholdLeanXmssSecurity.SigningOpeningProof.relTriple_withCaching_planted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningOpeningProof.relTriple_withCaching_planted
