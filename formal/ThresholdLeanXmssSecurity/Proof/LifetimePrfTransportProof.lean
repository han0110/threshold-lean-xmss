import ThresholdLeanXmssSecurity.Proof.LifetimeAllowance
import ThresholdLeanXmssSecurity.Proof.LifetimeKeygenPrograms
import ThresholdLeanXmssSecurity.Proof.LifetimeLegacy


/-!
# The PRF hop of each chronological run

This module bounds the two transports of `LifetimeAllowance.LifetimePrfTransportSmallSplit`.
Each transport is identical until a bad event.

* `real_transport` bounds the real side. Hybrid `n` against the real PRF experiment of
  `lifetimeRunReductionSampled n` costs the stream-key bad event `probBad_streamKey` of hybrid `n`
  (`keyWorld_coupling`). For `n = 0`, `accepts_reductionGame_zero` shows that hybrid `0` and the
  lifetime game accept with the same probability.
* `ideal_transport` bounds the ideal side. The ideal PRF experiment of run `n` and world `n + 1`
  are the two interpretations `leftImpl` and `rightImpl` of one program `program4` with four
  copies of the local oracle (`left_world`, `right_world`). In `leftImpl` run `n` has its own
  stream table. In `rightImpl` it shares the table of the earlier runs. `ideal_coupling` bounds
  the distance by `IdealBad`. This event holds when one stream address is in both tables, or when
  a free honest step of keygen or signing draws a hidden stream.
* `shares_eq` splits `keySplit (q₀ + q)` into `realShare` and `idealShare`.
  `designCounts_le` shows that the counts of
  `.claude/review_opus_codex_a111_design_correction.md` fit the two shares when
  `keySplit (q₀ + q) < 2`.
* `RealBadBound` and `IdealBadBound` bound the two bad events by the two shares, for each `Th`.
  `smallSplit_of_bounds` gives `LifetimePrfTransportSmallSplit` from them under
  `HasLifetimeQueryBoundAll`, and `lifetimeSecurity_of_bounds` gives `LifetimeSecurityStatementSampled`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace ThresholdLeanXmssSecurity.LifetimePrfTransportProof

open LifetimeJointLink LifetimeHybridOrder

attribute [local instance] Classical.propDecidable

section Arithmetic

variable {C : Committee}

/-- The numerator of `keySplit (q₀ + q)` in the three parts of the lifetime budget. -/
theorem keySplit_budget (Q O F : ℕ) :
    keySplit C (Q + O + (F + 2) * Q) =
      ((4 * (F + 3) * Q * prssKeyCount C + 4 * O * prssKeyCount C + 4 * prssKeyCount C ^ 2 : ℕ) :
        ℝ) / 2 ^ 256 := by
  unfold keySplit
  congr 2
  ring

/-- If `keySplit q < 2`, then the committee has fewer than `2^128` PRSS keys. -/
theorem prssKeyCount_lt (q : ℕ) (h : keySplit C q < 2) : prssKeyCount C < 2 ^ 128 := by
  unfold keySplit at h
  rw [div_lt_iff₀ (by positivity)] at h
  have h1 : 4 * q * prssKeyCount C + 4 * prssKeyCount C ^ 2 < 2 * 2 ^ 256 := by
    exact_mod_cast h
  by_contra hc
  have h2 : (2 ^ 128) ^ 2 ≤ prssKeyCount C ^ 2 := Nat.pow_le_pow_left (not_lt.1 hc) 2
  rw [← pow_mul] at h2
  omega

/-- `2^(t-1) ≤ C(2t-1, t-1)`. -/
theorem two_pow_le_termCount : 2 ^ (C.t - 1) ≤ termCount C := by
  obtain ⟨s, hs⟩ : ∃ s, C.t = s + 1 := ⟨C.t - 1, by have := C.one_le_t; omega⟩
  have hn : C.n = 2 * s + 1 := by unfold Committee.n; omega
  unfold termCount
  rw [hn, hs, Nat.add_sub_cancel]
  have hmid : ∀ i, (2 * s + 1).choose i ≤ (2 * s + 1).choose s := fun i => by
    have := Nat.choose_le_middle i (2 * s + 1)
    rwa [show (2 * s + 1) / 2 = s by omega] at this
  have hsum : 2 ^ (2 * s + 1) ≤ (2 * s + 2) * (2 * s + 1).choose s := by
    rw [← Nat.sum_range_choose]
    calc ∑ i ∈ Finset.range (2 * s + 1 + 1), (2 * s + 1).choose i
        ≤ ∑ _i ∈ Finset.range (2 * s + 1 + 1), (2 * s + 1).choose s :=
          Finset.sum_le_sum fun i _ => hmid i
      _ = (2 * s + 2) * (2 * s + 1).choose s := by simp
  have hpow : 2 * s + 2 ≤ 2 ^ (s + 1) := by
    have := Nat.lt_two_pow_self (n := s)
    rw [pow_succ]
    omega
  have h1 : 2 ^ (s + 1) * 2 ^ s ≤ 2 ^ (s + 1) * (2 * s + 1).choose s := by
    calc 2 ^ (s + 1) * 2 ^ s = 2 ^ (2 * s + 1) := by rw [← pow_add]; ring_nf
      _ ≤ (2 * s + 2) * (2 * s + 1).choose s := hsum
      _ ≤ 2 ^ (s + 1) * (2 * s + 1).choose s := Nat.mul_le_mul_right _ hpow
  exact Nat.le_of_mul_le_mul_left h1 (by positivity)

/-- Each operator count is at most the term count. -/
theorem n_le_termCount : C.n ≤ termCount C := by
  obtain ⟨s, hs⟩ : ∃ s, C.t = s + 1 := ⟨C.t - 1, by have := C.one_le_t; omega⟩
  have hn : C.n = 2 * s + 1 := by unfold Committee.n; omega
  have h := two_pow_le_termCount (C := C)
  unfold termCount at h ⊢
  rw [hn, hs, Nat.add_sub_cancel] at h ⊢
  have key : ∀ k, 3 ≤ k → 2 * k + 1 ≤ 2 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k _ ih => rw [pow_succ]; omega
  rcases Nat.lt_or_ge s 3 with h3 | h3
  · interval_cases s <;> decide
  · exact (key s h3).trans h

/-- If `keySplit q < 2`, then `n ≤ 255`. -/
theorem n_le_of_keySplit (q : ℕ) (h : keySplit C q < 2) : C.n ≤ 255 := by
  have hm := prssKeyCount_lt q h
  have ht : 2 ^ (C.t - 1) < 2 ^ 128 :=
    lt_of_le_of_lt two_pow_le_termCount (lt_of_le_of_lt (by unfold prssKeyCount; omega) hm)
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 ht
  unfold Committee.n
  omega

/-- The exact count of `bottomTreeCalls`. -/
theorem bottomTreeCalls_eq : bottomTreeCalls C = 11468859 * termCount C + 4318101852 := by
  unfold bottomTreeCalls
  simp only [layerHeight, numChains, randomizerAttemptLimit]
  ring

/-- `lifetimeOverhead` pays at least `n + 1` trees in each run. -/
theorem runs_le_lifetimeOverhead (attempts Q : ℕ) :
    lifetimeRuns attempts * (C.n + 1) * bottomTreeCalls C ≤ lifetimeOverhead C attempts Q := by
  unfold lifetimeOverhead
  have : lifetimeRuns attempts * (C.n + 1) * bottomTreeCalls C =
      lifetimeRuns attempts * bottomTreeCalls C + lifetimeRuns attempts * C.n * bottomTreeCalls C := by
    ring
  rw [this]
  have : lifetimeRuns attempts * bottomTreeCalls C ≤
      (min Q (2 ^ layerHeight) + lifetimeRuns attempts) * bottomTreeCalls C :=
    Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  omega

/-- The numerator over `2^256` of the share of the real side of a hop. `F` is the ceremony
fuel. -/
def realShare (C : Committee) (attempts Q F : ℕ) : ℕ :=
  4 * (F + 2) * Q * prssKeyCount C + 3 * lifetimeOverhead C attempts Q * prssKeyCount C +
    4 * prssKeyCount C ^ 2

/-- The numerator over `2^256` of the share of the ideal side of a hop. -/
def idealShare (C : Committee) (attempts Q : ℕ) : ℕ :=
  4 * Q * prssKeyCount C + lifetimeOverhead C attempts Q * prssKeyCount C

/-- The two shares add up to `keySplit (q₀ + q)`. -/
theorem shares_eq (attempts Q F : ℕ) :
    (realShare C attempts Q F : ℝ) / 2 ^ 256 + (idealShare C attempts Q : ℝ) / 2 ^ 256 =
      keySplit C (Q + lifetimeOverhead C attempts Q + (F + 2) * Q) := by
  rw [keySplit_budget, ← add_div, ← Nat.cast_add]
  unfold realShare idealShare
  congr 2
  ring

/-- The counts of the design (`.claude/review_opus_codex_a111_design_correction.md`) fit the
two shares when `keySplit q < 2` and `1 ≤ attempts`. The real side has the cached stream-key
input `Q m`, the hits `3 Q m`, `PartsCollide` `n² a² + n⁴`, `revealPairs` `m n (a + n)`, the
row keys of the other runs `(N - 1) n (a + n) m` and the birthday bound `4 m²`. The ideal side
has the keys of the earlier runs `2 (N - 1) m` and the guess `Q m`. -/
theorem designCounts_le (attempts Q F q : ℕ) (h : keySplit C q < 2) (hattempts : 1 ≤ attempts) :
    Q * prssKeyCount C + 3 * Q * prssKeyCount C +
        (C.n ^ 2 * termCount C ^ 2 + C.n ^ 4) + prssKeyCount C * C.n * (termCount C + C.n) +
        (lifetimeRuns attempts - 1) * C.n * (termCount C + C.n) * prssKeyCount C +
        4 * prssKeyCount C ^ 2 ≤ realShare C attempts Q F ∧
      2 * (lifetimeRuns attempts - 1) * prssKeyCount C + Q * prssKeyCount C ≤
        idealShare C attempts Q := by
  have hB0 := bottomTreeCalls_eq (C := C)
  have hO0 := runs_le_lifetimeOverhead (C := C) attempts Q
  have hna : C.n ≤ termCount C := n_le_termCount
  have ham : termCount C ≤ prssKeyCount C := by unfold prssKeyCount; omega
  have hn : C.n ≤ 255 := n_le_of_keySplit q h
  have hR : 1 ≤ lifetimeRuns attempts := by
    unfold lifetimeRuns
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (Nat.succ_ne_zero _))
  obtain ⟨N, hN⟩ : ∃ N, lifetimeRuns attempts = N + 1 := ⟨_, (Nat.sub_add_cancel hR).symm⟩
  rw [hN] at hO0
  rw [hN, Nat.add_sub_cancel]
  unfold realShare idealShare
  set n := C.n
  set a := termCount C
  set m := prssKeyCount C
  set B := bottomTreeCalls C
  set O := lifetimeOverhead C attempts Q
  have hO : (N + 1) * (n + 1) * B ≤ O := hO0
  have hB : 510 * a ≤ B := by omega
  have hB2 : 2 ≤ B := by omega
  clear_value n a m B O
  clear hB0 hO0 h
  have h2na : n * (2 * a) ≤ n * B := Nat.mul_le_mul_left _ (by omega)
  have hU1 : n ^ 2 * a ^ 2 + n ^ 4 ≤ n * B * m := by
    have e1 : n ^ 4 ≤ n ^ 2 * a ^ 2 := by
      calc n ^ 4 = n ^ 2 * n ^ 2 := by ring
        _ ≤ n ^ 2 * a ^ 2 := by gcongr
    have e2 : 2 * (n ^ 2 * a ^ 2) ≤ n * B * m := by
      calc 2 * (n ^ 2 * a ^ 2) = n * (2 * n * a) * a := by ring
        _ ≤ n * (510 * a) * m := by
          gcongr
          omega
        _ ≤ n * B * m := by gcongr
    omega
  have hU2 : m * n * (a + n) ≤ n * B * m := by
    calc m * n * (a + n) ≤ m * n * (2 * a) := by gcongr; omega
      _ = n * (2 * a) * m := by ring
      _ ≤ n * B * m := Nat.mul_le_mul_right _ h2na
  have hU3 : N * n * (a + n) * m ≤ N * (n * B * m) := by
    calc N * n * (a + n) * m ≤ N * n * (2 * a) * m := by gcongr; omega
      _ = N * (n * (2 * a) * m) := by ring
      _ ≤ N * (n * B * m) := by gcongr
  have hX : (N + 2) * (n * B * m) ≤ 3 * O * m := by
    calc (N + 2) * (n * B * m) ≤ 3 * ((N + 1) * (n + 1) * B) * m := by
          have : (N + 2) * n ≤ 3 * ((N + 1) * (n + 1)) := by ring_nf; omega
          calc (N + 2) * (n * B * m) = (N + 2) * n * B * m := by ring
            _ ≤ 3 * ((N + 1) * (n + 1)) * B * m := by gcongr
            _ = 3 * ((N + 1) * (n + 1) * B) * m := by ring
      _ ≤ 3 * O * m := by gcongr
  have hI : 2 * N * m ≤ O * m := by
    have e : 2 * N ≤ (N + 1) * (n + 1) * B :=
      calc 2 * N ≤ (N + 1) * 1 * 2 := by omega
        _ ≤ (N + 1) * (n + 1) * B := by gcongr; omega
    calc 2 * N * m ≤ (N + 1) * (n + 1) * B * m := Nat.mul_le_mul_right _ e
      _ ≤ O * m := by gcongr
  constructor
  · have hF : 4 * Q * m ≤ 4 * (F + 2) * Q * m := by gcongr; omega
    have : (N + 2) * (n * B * m) = n * B * m + n * B * m + N * (n * B * m) := by ring
    linarith
  · linarith [Nat.zero_le (Q * m)]

end Arithmetic

section RealSide

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The world game of hybrid `n` for one `Th`. It is the game inside `lifetimeRunReductionSampled n`. -/
def reductionGame (values : MpcDomain → HashOutput) (n : ℕ) : OracleComp (WorldSpec C) Bool :=
  emulationGame (lifetimeGameWith K (circuitsOf (thOf values)) settings attempts
    (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A)

/-- `simulateQ` of a handler as a monad map. -/
def simulateHom {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) : OracleComp spec →ᵐ StateT σ ProbComp where
  toFun _ x := simulateQ impl x
  toFun_pure' _ := simulateQ_pure _ _
  toFun_bind' _ _ := simulateQ_bind _ _ _

/-- The roles where every step runs on the local oracle of `prims`. -/
def localRoles (prims : Primitives) : Roles C (StateT (HashCache C) ProbComp) :=
  ⟨fun p => simulateQ (localAnswer prims) p, fun p => simulateQ (localAnswer prims) p⟩

theorem world_adversary (prims : Primitives) {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (worldAnswer prims) (worldRoles.adversary p) = simulateQ (localAnswer prims) p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    change simulateQ (worldAnswer prims) (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
      fun x => worldRoles.adversary (k x)) = _
    rw [simulateQ_bind, adversary_query, simulateQ_spec_query]
    simp only [simulateQ_bind, simulateQ_spec_query, ih]
    rfl

theorem world_honest (prims : Primitives) {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (worldAnswer prims) (worldRoles.honest p) = simulateQ (localAnswer prims) p :=
  simulateQ_free _ _ p

theorem rolesHom_world (prims : Primitives) :
    LifetimeEmulatedBudget.RolesHom (simulateHom (worldAnswer prims)) worldRoles
      (localRoles (C := C) prims) :=
  ⟨fun p => world_adversary prims p, fun p => world_honest prims p⟩

theorem rolesHom_world_counted (prims : Primitives) :
    LifetimeEmulatedBudget.RolesHom (simulateHom (worldAnswer prims))
      ⟨worldRoles.adversary, worldRoles.adversary⟩ (localRoles (C := C) prims) :=
  ⟨fun p => world_adversary prims p, fun p => world_adversary prims p⟩

/-- The roles of hybrid `0` after the log erasure, on the world. -/
def zeroRoles (r : ℕ) : Roles C (OracleComp (WorldSpec C)) :=
  if r = 0 then worldRoles else ⟨worldRoles.adversary, worldRoles.adversary⟩

/-- Hybrid `0` is the lifetime with the honest steps of the later runs on the counted copy. -/
theorem reductionGame_zero (values : MpcDomain → HashOutput) :
    reductionGame K settings attempts circuitsOf D A values 0 =
      lifetimeGameWith K (circuitsOf (thOf values)) settings attempts zeroRoles worldRoles D A := by
  unfold reductionGame
  rw [LifetimeKeygenHopProof.emulationGame_erased]
  change (LifetimeEmulatedBudget.eraseHom (lifetimeGameWith K (circuitsOf (thOf values)) settings
    attempts (lifetimeHybridRoles D 0) (lifetimeHybridRoles D 0 0) D A)).run' ∅ = _
  rw [LifetimeEmulatedBudget.hom_lifetimeGameWith LifetimeEmulatedBudget.eraseHom K _ settings attempts
    _ _ (fun r => if r = 0 then LifetimeKeygenHopProof.plainRoles else
      ⟨LifetimeKeygenHopProof.plainRoles.adversary, LifetimeKeygenHopProof.plainRoles.adversary⟩)
    LifetimeKeygenHopProof.plainRoles ?_ (LifetimeKeygenPrograms.rolesHom_erase D) D A]
  · rw [← LifetimeEmulatedBudget.hom_lifetimeGameWith LifetimeEmulatedBudget.liftHom K _ settings
      attempts zeroRoles worldRoles _ _ ?_ LifetimeKeygenPrograms.rolesHom_lift D A]
    · change (StateT.lift _ : LifetimeEmulatedBudget.ErasedM C Bool).run' ∅ = _
      simp [StateT.run'_eq, StateT.run_lift]
    · intro r
      by_cases hr : r = 0
      · simp only [zeroRoles, hr, if_true]
        exact LifetimeKeygenPrograms.rolesHom_lift
      · simp only [zeroRoles, hr, if_false]
        exact ⟨fun _ => rfl, fun _ => rfl⟩
  · intro r
    by_cases hr : r = 0
    · subst hr
      simpa only [if_true] using LifetimeKeygenPrograms.rolesHom_erase D
    · have hR : lifetimeHybridRoles D 0 r =
          ⟨(emulatedRoles D).adversary, (emulatedRoles D).adversary⟩ := by
        simp [lifetimeHybridRoles, hr]
      rw [hR]
      simp only [hr, if_false]
      exact ⟨fun p => LifetimeKeygenHopProof.erase_base_adversary D p,
        fun p => LifetimeKeygenHopProof.erase_base_adversary D p⟩

/-- Hybrid `0` accepts with the probability of the lifetime game. -/
theorem accepts_reductionGame_zero (values : MpcDomain → HashOutput) :
    accepts ⟨thOf values, aes⟩ (lifetimeGame K (circuitsOf (thOf values)) settings attempts D A) =
      accepts ⟨thOf values, aes⟩ (reductionGame K settings attempts circuitsOf D A values 0) := by
  rw [reductionGame_zero, accepts_eq_probOutput, accepts_eq_probOutput]
  have h : simulateQ (worldAnswer ⟨thOf values, aes⟩) (lifetimeGame K (circuitsOf (thOf values))
      settings attempts D A) = simulateQ (worldAnswer ⟨thOf values, aes⟩) (lifetimeGameWith K
        (circuitsOf (thOf values)) settings attempts zeroRoles worldRoles D A) := by
    change simulateHom (worldAnswer _) (lifetimeGameWith K _ settings attempts (fun _ => worldRoles)
      worldRoles D A) = simulateHom (worldAnswer _) (lifetimeGameWith K _ settings attempts zeroRoles
        worldRoles D A)
    rw [LifetimeEmulatedBudget.hom_lifetimeGameWith _ K _ settings attempts _ _ (fun _ => localRoles _)
        (localRoles _) (fun _ => rolesHom_world _) (rolesHom_world _) D A,
      LifetimeEmulatedBudget.hom_lifetimeGameWith _ K _ settings attempts _ _ (fun _ => localRoles _)
        (localRoles _) (fun r => ?_) (rolesHom_world _) D A]
    by_cases hr : r = 0
    · simpa only [zeroRoles, hr, if_true] using rolesHom_world _
    · simpa only [zeroRoles, hr, if_false] using rolesHom_world_counted _
  rw [h]

/-- The chronological world `n` accepts as the world game of hybrid `n`, for each `Th`. -/
theorem accepts_chronological (values : MpcDomain → HashOutput) (n : ℕ) :
    accepts ⟨thOf values, aes⟩
        (chronologicalGame K settings attempts D A (circuitsOf (thOf values)) n) =
      accepts ⟨thOf values, aes⟩ (reductionGame K settings attempts circuitsOf D A values n) := by
  by_cases hn : n = 0
  · subst hn
    rw [chronologicalGame, if_pos rfl]
    exact accepts_reductionGame_zero K settings attempts aes circuitsOf D A values
  · rw [chronologicalGame, if_neg hn]
    rfl

/-- The real PRF experiment of `lifetimeRunReductionSampled n` is the keyed world of hybrid `n`, with the
`Th` sample first. -/
theorem reductionProbability_real (n : ℕ) :
    reductionProbability K settings attempts aes circuitsOf D A true n =
      (Pr[= true | ($ᵗ (MpcDomain → HashOutput)) >>= fun values =>
        ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
          (simulateQ (keyWorld ⟨thOf values, aes⟩ D keys)
            (reductionGame K settings attempts circuitsOf D A values n)).run' ∅]).toReal := by
  have h : (hiddenStreams aes).prfRealExp
      (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n) =
      ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
        ($ᵗ (MpcDomain → HashOutput)) >>= fun values =>
          simulateQ ((hiddenStreams aes).prfRealQueryImpl keys)
            (prgReduction ⟨thOf values, aes⟩ D
              (reductionGame K settings attempts circuitsOf D A values n)) := by
    unfold PRFScheme.prfRealExp lifetimeRunReductionSampled
    refine bind_congr fun keys => ?_
    rw [simulateQ_bind, PRFScheme.simulateQ_prfRealQueryImpl_liftComp]
    rfl
  change (Pr[= true | (hiddenStreams aes).prfRealExp
    (lifetimeRunReductionSampled K settings attempts aes circuitsOf D A n)]).toReal = _
  rw [h, probOutput_bind_bind_swap]
  congr 1
  refine probOutput_bind_congr' _ true fun values => ?_
  exact congrArg (fun m => Pr[= true | m]) (prfRealExp_prgReduction ⟨thOf values, aes⟩ D _)

/-- The average over `Th` of the stream-key bad event of hybrid `n`. -/
def realBad (n : ℕ) : ℝ :=
  ∑ values, (Pr[= values | $ᵗ (MpcDomain → HashOutput)]).toReal *
    probBad_streamKey ⟨thOf values, aes⟩ D (reductionGame K settings attempts circuitsOf D A values n)

/-- The real side of each hop is identical until the stream-key bad event of hybrid `n`
(`keyWorld_coupling`). -/
theorem real_transport (n : ℕ) :
    |chronologicalProbability K settings attempts aes circuitsOf D A n -
      reductionProbability K settings attempts aes circuitsOf D A true n| ≤
      realBad K settings attempts aes circuitsOf D A n := by
  have hpoint (values : MpcDomain → HashOutput) :
      |(Pr[fun b => b = true | (simulateQ (worldAnswer ⟨thOf values, aes⟩)
        (chronologicalGame K settings attempts D A (circuitsOf (thOf values)) n)).run' ∅]).toReal -
      (Pr[fun b => b = true | ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
        (simulateQ (keyWorld ⟨thOf values, aes⟩ D keys)
          (reductionGame K settings attempts circuitsOf D A values n)).run' ∅]).toReal| ≤
        probBad_streamKey ⟨thOf values, aes⟩ D
          (reductionGame K settings attempts circuitsOf D A values n) := by
    have h := keyWorld_coupling ⟨thOf values, aes⟩ D
      (reductionGame K settings attempts circuitsOf D A values n)
    rw [← accepts_chronological K settings attempts aes circuitsOf D A values n,
      accepts_eq_probOutput] at h
    simpa only [probEvent_eq_eq_probOutput] using h
  have havg := abs_probEvent_bind_sub_le_sum ($ᵗ (MpcDomain → HashOutput)) _ _
    (fun b => b = true) _ hpoint
  rw [reductionProbability_real]
  unfold chronologicalProbability
  have hf : (fun r : Bool × ℕ => r.1 = true) = (fun b => b = true) ∘ Prod.fst := rfl
  rw [hf, ← probEvent_map, LifetimeKeygenHopProof.lifetimeRun_output]
  simpa only [probEvent_eq_eq_probOutput, realBad] using havg

end RealSide

section Copies

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (D : C.Coalition)

/-- The observed adversary, the emulated honest operators of the earlier runs, the free honest
operators of keygen and signing, and the honest operators of run `n`. -/
abbrev Spec4 (C : Committee) := ((LocalSpec C + LocalSpec C) + LocalSpec C) + LocalSpec C

def advCopy4 {α : Type} (p : OracleComp (LocalSpec C) α) : OracleComp (Spec4 C) α :=
  simulateQ (fun t => OracleComp.lift (OracleSpec.query (spec := Spec4 C) (.inl (.inl (.inl t))))) p

def emulCopy4 {α : Type} (p : OracleComp (LocalSpec C) α) : OracleComp (Spec4 C) α :=
  simulateQ (fun t => OracleComp.lift (OracleSpec.query (spec := Spec4 C) (.inl (.inl (.inr t))))) p

def freeCopy4 {α : Type} (p : OracleComp (LocalSpec C) α) : OracleComp (Spec4 C) α :=
  simulateQ (fun t => OracleComp.lift (OracleSpec.query (spec := Spec4 C) (.inl (.inr t)))) p

def targetCopy4 {α : Type} (p : OracleComp (LocalSpec C) α) : OracleComp (Spec4 C) α :=
  simulateQ (fun t => OracleComp.lift (OracleSpec.query (spec := Spec4 C) (.inr t))) p

/-- The four copies in the emulation. The run-`n` copy uses `target`. -/
def impl4 (target : Roles C (EmulationM C)) : QueryImpl (Spec4 C) (EmulationM C) :=
  (((fun t => (emulatedRoles D).adversary (OracleComp.lift (OracleSpec.query t))) +
    (fun t => (emulatedRoles D).honest (OracleComp.lift (OracleSpec.query t)))) +
    (fun t => (lifetimeHybridRoles D 0 0).honest (OracleComp.lift (OracleSpec.query t)))) +
    (fun t => target.honest (OracleComp.lift (OracleSpec.query t)))

def H4 (target : Roles C (EmulationM C)) : OracleComp (Spec4 C) →ᵐ EmulationM C where
  toFun _ x := simulateQ (impl4 D target) x
  toFun_pure' _ := simulateQ_pure _ _
  toFun_bind' _ _ := simulateQ_bind _ _ _

theorem impl4_advCopy (target : Roles C (EmulationM C)) {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (impl4 D target) (advCopy4 p) = (emulatedRoles D).adversary p := by
  rw [LifetimeKeygenPrograms.adversary_eq, advCopy4, LifetimeEmulatedBudget.simulateQ_comp]
  congr 1
  funext t
  exact simulateQ_spec_query _ _

theorem impl4_emulCopy (target : Roles C (EmulationM C)) {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (impl4 D target) (emulCopy4 p) = (emulatedRoles D).honest p := by
  rw [LifetimeKeygenPrograms.honest_eq, emulCopy4, LifetimeEmulatedBudget.simulateQ_comp]
  congr 1
  funext t
  exact simulateQ_spec_query _ _

theorem impl4_freeCopy (target : Roles C (EmulationM C)) {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (impl4 D target) (freeCopy4 p) = (lifetimeHybridRoles D 0 0).honest p := by
  rw [LifetimeKeygenPrograms.baseHonest_eq, freeCopy4, LifetimeEmulatedBudget.simulateQ_comp]
  congr 1

theorem impl4_targetCopy_free {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (impl4 D (lifetimeHybridRoles D 0 0)) (targetCopy4 p) =
      (lifetimeHybridRoles D 0 0).honest p := by
  rw [LifetimeKeygenPrograms.baseHonest_eq, targetCopy4, LifetimeEmulatedBudget.simulateQ_comp]
  congr 1

theorem impl4_targetCopy_emul {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (impl4 D (emulatedRoles D)) (targetCopy4 p) = (emulatedRoles D).honest p := by
  rw [LifetimeKeygenPrograms.honest_eq, targetCopy4, LifetimeEmulatedBudget.simulateQ_comp]
  congr 1
  funext t
  exact simulateQ_spec_query _ _

/-- The run roles of the four-copy program. The earlier runs are emulated, run `n` has its own
copy, and the later runs use the adversary copy. -/
def roles4 (n r : ℕ) : Roles C (OracleComp (Spec4 C)) :=
  if r < n then ⟨advCopy4, emulCopy4⟩ else if r = n then ⟨advCopy4, targetCopy4⟩
  else ⟨advCopy4, advCopy4⟩

def base4 : Roles C (OracleComp (Spec4 C)) := ⟨advCopy4, freeCopy4⟩

/-- The run roles of world `n + 1` with run `n + 1` on the adversary copy. -/
def nextRoles (n r : ℕ) : Roles C (EmulationM C) :=
  if r < n + 1 then emulatedRoles D else ⟨(emulatedRoles D).adversary, (emulatedRoles D).adversary⟩

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (A : LifetimeAdversary C E)

/-- The four-copy program of hop `n`. -/
def program4 (n : ℕ) : OracleComp (Spec4 C) Bool :=
  lifetimeGameWith K circuits settings attempts (roles4 n) base4 D A

theorem rolesHom_base4 (target : Roles C (EmulationM C)) :
    LifetimeEmulatedBudget.RolesHom (H4 D target) base4 (lifetimeHybridRoles D 0 0) :=
  ⟨fun p => impl4_advCopy D target p, fun p => impl4_freeCopy D target p⟩

theorem hybridRoles_self (n : ℕ) : lifetimeHybridRoles D n n = lifetimeHybridRoles D 0 0 := by
  simp [lifetimeHybridRoles]

theorem hybridRoles_lt {n r : ℕ} (h : r < n) : lifetimeHybridRoles D n r = emulatedRoles D := by
  simp [lifetimeHybridRoles, h]

theorem hybridRoles_gt {n r : ℕ} (h1 : ¬ r < n) (h2 : r ≠ n) :
    lifetimeHybridRoles D n r = ⟨(emulatedRoles D).adversary, (emulatedRoles D).adversary⟩ := by
  simp [lifetimeHybridRoles, h1, h2]

/-- The left interpretation of the program is hybrid `n`. -/
theorem program4_left (n : ℕ) :
    simulateQ (impl4 D (lifetimeHybridRoles D 0 0)) (program4 D K circuits settings attempts A n) =
      lifetimeGameWith K circuits settings attempts (lifetimeHybridRoles D n)
        (lifetimeHybridRoles D n n) D A := by
  have hb : LifetimeEmulatedBudget.RolesHom (H4 D (lifetimeHybridRoles D 0 0)) base4
      (lifetimeHybridRoles D n n) := by
    rw [hybridRoles_self D n]
    exact rolesHom_base4 D _
  refine LifetimeEmulatedBudget.hom_lifetimeGameWith (H4 D (lifetimeHybridRoles D 0 0)) K circuits
    settings attempts _ _ _ _ (fun r => ?_) hb D A
  by_cases h1 : r < n
  · rw [hybridRoles_lt D h1]
    simp only [roles4, h1, if_true]
    exact ⟨fun p => impl4_advCopy D _ p, fun p => impl4_emulCopy D _ p⟩
  · by_cases h2 : r = n
    · subst h2
      rw [hybridRoles_self D r]
      simp only [roles4, Nat.lt_irrefl, if_false, if_true]
      exact ⟨fun p => impl4_advCopy D _ p, fun p => impl4_targetCopy_free D p⟩
    · rw [hybridRoles_gt D h1 h2]
      simp only [roles4, h1, h2, if_false]
      exact ⟨fun p => impl4_advCopy D _ p, fun p => impl4_advCopy D _ p⟩

/-- The right interpretation of the program is world `n + 1` with run `n + 1` on the adversary
copy. -/
theorem program4_right (n : ℕ) :
    simulateQ (impl4 D (emulatedRoles D)) (program4 D K circuits settings attempts A n) =
      lifetimeGameWith K circuits settings attempts (nextRoles D n)
        (lifetimeHybridRoles D 0 0) D A := by
  refine LifetimeEmulatedBudget.hom_lifetimeGameWith (H4 D (emulatedRoles D)) K circuits
    settings attempts _ _ _ _ (fun r => ?_) (rolesHom_base4 D _) D A
  unfold roles4 nextRoles
  by_cases h1 : r < n
  · simp only [h1, if_true, show r < n + 1 by omega]
    exact ⟨fun p => impl4_advCopy D _ p, fun p => impl4_emulCopy D _ p⟩
  · by_cases h2 : r = n
    · subst h2
      simp only [Nat.lt_irrefl, if_false, if_true, Nat.lt_succ_self]
      exact ⟨fun p => impl4_advCopy D _ p, fun p => impl4_targetCopy_emul D p⟩
    · simp only [h1, h2, if_false, show ¬ r < n + 1 by omega]
      exact ⟨fun p => impl4_advCopy D _ p, fun p => impl4_advCopy D _ p⟩

end Copies

section IdealWorlds

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- The address of a stream in the layout of `streamWorld`. -/
abbrev Address (C : Committee) := (KeyName C × HashOutput) × ℕ × ℕ × ℕ

def address (x : PrgInput C) : Address C := ((x.1, x.2.1), x.2.2)

/-- One lazy table draw. -/
def tableDraw (cache : HiddenCache C) (x : Address C) : ProbComp (Bit × HiddenCache C) :=
  match cache x with
  | some v => pure (v, cache)
  | none => (fun b => (b, cache.cacheQuery x b)) <$> ($ᵗ Bit)

theorem randomOracle_run (cache : HiddenCache C) (x : Address C) :
    ((Address C →ₒ Bit).randomOracle x).run cache = tableDraw cache x := by
  unfold tableDraw
  cases hc : cache x <;>
    simp [StateT.run_bind, StateT.run_get, hc, StateT.run_modifyGet, StateT.run_pure,
      bind_pure_comp, uniformSampleImpl]

/-- The hash cache, the table of the earlier runs, the table of run `n`, and a flag for a hidden
stream of a free honest step. -/
abbrev IdealState (C : Committee) := HashCache C × HiddenCache C × HiddenCache C × Bool

def onCache {α : Type} (m : StateT (HashCache C) ProbComp α) : StateT (IdealState C) ProbComp α :=
  StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$> m.run s.1

def firstTable (x : Address C) : StateT (IdealState C) ProbComp Bit :=
  StateT.mk fun s => (fun r => (r.1, (s.1, r.2, s.2.2))) <$> tableDraw s.2.1 x

def secondTable (x : Address C) : StateT (IdealState C) ProbComp Bit :=
  StateT.mk fun s => (fun r => (r.1, (s.1, s.2.1, r.2, s.2.2.2))) <$> tableDraw s.2.2.1 x

def flagged {α : Type} (m : StateT (IdealState C) ProbComp α) : StateT (IdealState C) ProbComp α :=
  StateT.mk fun s => (fun r => (r.1, (r.2.1, r.2.2.1, r.2.2.2.1, true))) <$> m.run s

/-- The draw of the merged table for the earlier runs. A hit in the table of run `n` is copied. -/
def mergedFirst (x : Address C) : StateT (IdealState C) ProbComp Bit :=
  StateT.mk fun s => match s.2.1 x, s.2.2.1 x with
  | some v, _ => pure (v, s)
  | none, some v => pure (v, (s.1, s.2.1.cacheQuery x v, s.2.2))
  | none, none => (fun b => (b, (s.1, s.2.1.cacheQuery x b, s.2.2))) <$> ($ᵗ Bit)

/-- The draw of the merged table for run `n`. A hit in the table of the earlier runs is copied. -/
def mergedSecond (x : Address C) : StateT (IdealState C) ProbComp Bit :=
  StateT.mk fun s => match s.2.1 x, s.2.2.1 x with
  | some v, _ => pure (v, (s.1, s.2.1, s.2.2.1.cacheQuery x v, s.2.2.2))
  | none, some v => pure (v, s)
  | none, none => (fun b => (b, (s.1, s.2.1, s.2.2.1.cacheQuery x b, s.2.2.2))) <$> ($ᵗ Bit)

/-- A local step on the hash cache. -/
def localImpl : QueryImpl (LocalSpec C) (StateT (IdealState C) ProbComp) :=
  fun t => onCache (localAnswer prims t)

/-- A local step whose hidden streams use `hidden`. -/
def withHidden (hidden : PrgInput C → StateT (IdealState C) ProbComp Bit) :
    QueryImpl (LocalSpec C) (StateT (IdealState C) ProbComp) := fun t =>
  match t with
  | .inr (.inr x) => if Hidden D x.1 then hidden x else onCache (localAnswer prims (.inr (.inr x)))
  | t => onCache (localAnswer prims t)

/-- The ideal side of the PRF experiment. Run `n` and the free steps use their own table. -/
def leftImpl : QueryImpl (Spec4 C) (StateT (IdealState C) ProbComp) :=
  ((localImpl (C := C) prims + withHidden prims D (fun x => firstTable (address x))) +
    withHidden prims D (fun x => flagged (secondTable (address x)))) +
    withHidden prims D (fun x => secondTable (address x))

/-- The next chronological world. Run `n` shares the table of the earlier runs, and the free
steps use the real streams. -/
def rightImpl : QueryImpl (Spec4 C) (StateT (IdealState C) ProbComp) :=
  ((localImpl (C := C) prims + withHidden prims D (fun x => mergedFirst (address x))) +
    withHidden prims D (fun x => flagged (onCache (localAnswer prims (.inr (.inr x)))))) +
    withHidden prims D (fun x => mergedSecond (address x))

/-- The bad event of the ideal side. A free honest step draws a hidden stream, or one address is in
both tables. -/
def IdealBad (s : IdealState C) : Prop :=
  s.2.2.2 = true ∨ ∃ x, (s.2.1 x).isSome ∧ (s.2.2.1 x).isSome

end IdealWorlds

section IdealCoupling

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- The flag and both tables only grow. -/
def Grows (s r : IdealState C) : Prop :=
  (s.2.2.2 = true → r.2.2.2 = true) ∧ (∀ x, (s.2.1 x).isSome → (r.2.1 x).isSome) ∧
    (∀ x, (s.2.2.1 x).isSome → (r.2.2.1 x).isSome)

theorem idealBad_of_grows {s r : IdealState C} (h : Grows s r) (hb : IdealBad s) : IdealBad r := by
  rcases hb with hb | ⟨x, h1, h2⟩
  · exact Or.inl (h.1 hb)
  · exact Or.inr ⟨x, h.2.1 x h1, h.2.2 x h2⟩

/-- Every output of `m` grows its start state. -/
def GrowsAll {α : Type} (m : StateT (IdealState C) ProbComp α) : Prop :=
  ∀ s, ∀ r ∈ support (m.run s), Grows s r.2

theorem isSome_cacheQuery (c : HiddenCache C) (x y : Address C) (v : Bit) (h : (c y).isSome) :
    ((c.cacheQuery x v) y).isSome := by
  by_cases hy : y = x
  · subst hy; simp
  · rwa [QueryCache.cacheQuery_of_ne _ _ hy]

theorem grows_refl (s : IdealState C) : Grows s s := ⟨id, fun _ => id, fun _ => id⟩

theorem growsAll_onCache {α : Type} (m : StateT (HashCache C) ProbComp α) : GrowsAll (onCache m) := by
  intro s r hr
  simp only [onCache, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨r', -, rfl⟩ := hr
  exact grows_refl s

theorem tableDraw_mem {c : HiddenCache C} {x : Address C} {r : Bit × HiddenCache C}
    (hr : r ∈ support (tableDraw c x)) : ∀ y, (c y).isSome → (r.2 y).isSome := by
  unfold tableDraw at hr
  cases hc : c x <;> simp only [hc, support_pure, Set.mem_singleton_iff, support_map,
    Set.mem_image] at hr
  · obtain ⟨b, -, rfl⟩ := hr
    exact fun y hy => isSome_cacheQuery c x y b hy
  · subst hr
    exact fun _ hy => hy

theorem growsAll_firstTable (x : Address C) : GrowsAll (firstTable x) := by
  intro s r hr
  simp only [firstTable, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  exact ⟨id, tableDraw_mem hr', fun _ => id⟩

theorem growsAll_secondTable (x : Address C) : GrowsAll (secondTable x) := by
  intro s r hr
  simp only [secondTable, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  exact ⟨id, fun _ => id, tableDraw_mem hr'⟩

theorem growsAll_flagged {α : Type} {m : StateT (IdealState C) ProbComp α} (hm : GrowsAll m) :
    GrowsAll (flagged m) := by
  intro s r hr
  simp only [flagged, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  have h := hm s r' hr'
  exact ⟨fun _ => rfl, h.2.1, h.2.2⟩

theorem flagged_bad {α : Type} (m : StateT (IdealState C) ProbComp α) (s : IdealState C) :
    ∀ r ∈ support ((flagged m).run s), IdealBad r.2 := by
  intro r hr
  simp only [flagged, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨r', -, rfl⟩ := hr
  exact Or.inl rfl

theorem growsAll_mergedFirst (x : Address C) : GrowsAll (mergedFirst x) := by
  intro s r hr
  unfold mergedFirst at hr
  simp only [StateT.run_mk] at hr
  rcases h1 : s.2.1 x with _ | v <;> rcases h2 : s.2.2.1 x with _ | w <;>
    simp only [h1, h2, support_pure, Set.mem_singleton_iff, support_map, Set.mem_image] at hr
  · obtain ⟨b, -, rfl⟩ := hr
    exact ⟨id, fun y hy => isSome_cacheQuery _ x y b hy, fun _ => id⟩
  · subst hr
    exact ⟨id, fun y hy => isSome_cacheQuery _ x y w hy, fun _ => id⟩
  · subst hr; exact grows_refl s
  · subst hr; exact grows_refl s

theorem growsAll_mergedSecond (x : Address C) : GrowsAll (mergedSecond x) := by
  intro s r hr
  unfold mergedSecond at hr
  simp only [StateT.run_mk] at hr
  rcases h1 : s.2.1 x with _ | v <;> rcases h2 : s.2.2.1 x with _ | w <;>
    simp only [h1, h2, support_pure, Set.mem_singleton_iff, support_map, Set.mem_image] at hr
  · obtain ⟨b, -, rfl⟩ := hr
    exact ⟨id, fun _ => id, fun y hy => isSome_cacheQuery _ x y b hy⟩
  · subst hr; exact grows_refl s
  · subst hr
    exact ⟨id, fun _ => id, fun y hy => isSome_cacheQuery _ x y v hy⟩
  · subst hr
    exact ⟨id, fun _ => id, fun y hy => isSome_cacheQuery _ x y v hy⟩

theorem growsAll_withHidden {hidden : PrgInput C → StateT (IdealState C) ProbComp Bit}
    (h : ∀ x, GrowsAll (hidden x)) (t : (LocalSpec C).Domain) :
    GrowsAll (withHidden prims D hidden t) := by
  rcases t with u | q | x
  · exact growsAll_onCache _
  · exact growsAll_onCache _
  · change GrowsAll (if Hidden D x.1 then hidden x else onCache (localAnswer prims (.inr (.inr x))))
    split_ifs
    · exact h x
    · exact growsAll_onCache _

theorem growsAll_leftImpl (t : (Spec4 C).Domain) : GrowsAll ((leftImpl prims D) t) := by
  rcases t with ((t | t) | t) | t
  · exact growsAll_onCache _
  · exact growsAll_withHidden prims D (fun x => growsAll_firstTable _) t
  · exact growsAll_withHidden prims D (fun x => growsAll_flagged (growsAll_secondTable _)) t
  · exact growsAll_withHidden prims D (fun x => growsAll_secondTable _) t

theorem growsAll_rightImpl (t : (Spec4 C).Domain) : GrowsAll ((rightImpl prims D) t) := by
  rcases t with ((t | t) | t) | t
  · exact growsAll_onCache _
  · exact growsAll_withHidden prims D (fun x => growsAll_mergedFirst _) t
  · exact growsAll_withHidden prims D (fun x => growsAll_flagged (growsAll_onCache _)) t
  · exact growsAll_withHidden prims D (fun x => growsAll_mergedSecond _) t

theorem probOutput_eq_of_bad {α : Type} {m₁ m₂ : ProbComp (α × IdealState C)}
    (h₁ : ∀ r ∈ support m₁, IdealBad r.2) (h₂ : ∀ r ∈ support m₂, IdealBad r.2)
    {r : α × IdealState C} (hr : ¬ IdealBad r.2) : Pr[= r | m₁] = Pr[= r | m₂] := by
  rw [(probOutput_eq_zero_iff m₁ r).2 (fun h => hr (h₁ r h)),
    (probOutput_eq_zero_iff m₂ r).2 (fun h => hr (h₂ r h))]

theorem first_step (x : Address C) (s : IdealState C) (r : Bit × IdealState C) (hr : ¬ IdealBad r.2) :
    Pr[= r | (firstTable x).run s] = Pr[= r | (mergedFirst x).run s] := by
  rcases h1 : s.2.1 x with _ | v <;> rcases h2 : s.2.2.1 x with _ | w
  · simp [firstTable, mergedFirst, tableDraw, h1, h2, Functor.map_map]
  · refine probOutput_eq_of_bad (fun r' hr' => ?_) (fun r' hr' => ?_) hr
    · simp only [firstTable, tableDraw, h1, StateT.run_mk, support_map, Set.mem_image] at hr'
      obtain ⟨_, ⟨b, -, rfl⟩, rfl⟩ := hr'
      exact Or.inr ⟨x, by simp, by simp [h2]⟩
    · simp only [mergedFirst, h1, h2, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hr'
      subst hr'
      exact Or.inr ⟨x, by simp, by simp [h2]⟩
  · simp [firstTable, mergedFirst, tableDraw, h1, h2]
  · simp [firstTable, mergedFirst, tableDraw, h1, h2]

theorem second_step (x : Address C) (s : IdealState C) (r : Bit × IdealState C) (hr : ¬ IdealBad r.2) :
    Pr[= r | (secondTable x).run s] = Pr[= r | (mergedSecond x).run s] := by
  rcases h1 : s.2.1 x with _ | v <;> rcases h2 : s.2.2.1 x with _ | w
  · simp [secondTable, mergedSecond, tableDraw, h1, h2, Functor.map_map]
  · simp [secondTable, mergedSecond, tableDraw, h1, h2]
  · refine probOutput_eq_of_bad (fun r' hr' => ?_) (fun r' hr' => ?_) hr
    · simp only [secondTable, tableDraw, h2, StateT.run_mk, support_map, Set.mem_image] at hr'
      obtain ⟨_, ⟨b, -, rfl⟩, rfl⟩ := hr'
      exact Or.inr ⟨x, by simp [h1], by simp⟩
    · simp only [mergedSecond, h1, h2, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hr'
      subst hr'
      exact Or.inr ⟨x, by simp [h1], by simp⟩
  · refine probOutput_eq_of_bad (fun r' hr' => ?_) (fun r' hr' => ?_) hr
    · simp only [secondTable, tableDraw, h2, StateT.run_mk, support_map, Set.mem_image,
        support_pure, Set.mem_singleton_iff] at hr'
      obtain ⟨_, rfl, rfl⟩ := hr'
      exact Or.inr ⟨x, by simp [h1], by simp [h2]⟩
    · simp only [mergedSecond, h1, h2, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hr'
      subst hr'
      exact Or.inr ⟨x, by simp [h1], by simp⟩

/-- Outside the bad event, the two worlds take each step with the same law. -/
theorem ideal_step (t : (Spec4 C).Domain) (s : IdealState C) (r : _ × IdealState C)
    (hr : ¬ IdealBad r.2) :
    Pr[= r | ((leftImpl prims D) t).run s] = Pr[= r | ((rightImpl prims D) t).run s] := by
  rcases t with ((t | t) | t) | t
  · rfl
  · rcases t with u | q | x
    · rfl
    · rfl
    · change Pr[= r | (if Hidden D x.1 then firstTable (address x) else
          onCache (localAnswer prims (.inr (.inr x)))).run s] =
        Pr[= r | (if Hidden D x.1 then mergedFirst (address x) else
          onCache (localAnswer prims (.inr (.inr x)))).run s]
      split_ifs
      · exact first_step _ s r hr
      · rfl
  · rcases t with u | q | x
    · rfl
    · rfl
    · change Pr[= r | (if Hidden D x.1 then flagged (secondTable (address x)) else
          onCache (localAnswer prims (.inr (.inr x)))).run s] =
        Pr[= r | (if Hidden D x.1 then flagged (onCache (localAnswer prims (.inr (.inr x)))) else
          onCache (localAnswer prims (.inr (.inr x)))).run s]
      split_ifs
      · exact probOutput_eq_of_bad (flagged_bad _ s) (flagged_bad _ s) hr
      · rfl
  · rcases t with u | q | x
    · rfl
    · rfl
    · change Pr[= r | (if Hidden D x.1 then secondTable (address x) else
          onCache (localAnswer prims (.inr (.inr x)))).run s] =
        Pr[= r | (if Hidden D x.1 then mergedSecond (address x) else
          onCache (localAnswer prims (.inr (.inr x)))).run s]
      split_ifs
      · exact second_step _ s r hr
      · rfl

/-- The ideal side and the next world differ by at most the bad event of the ideal side. -/
theorem ideal_coupling {α : Type} (game : OracleComp (Spec4 C) α) (s : IdealState C) :
    tvDist ((simulateQ (leftImpl prims D) game).run' s) ((simulateQ (rightImpl prims D) game).run' s) ≤
      Pr[IdealBad ∘ Prod.snd | (simulateQ (leftImpl prims D) game).run s].toReal :=
  tvDist_simulateQ_le_probBad_of_good_outputs _ _ IdealBad (fun t s r hr => ideal_step prims D t s r hr)
    (fun t s hs r hr => idealBad_of_grows (growsAll_leftImpl prims D t s r hr) hs)
    (fun t s hs r hr => idealBad_of_grows (growsAll_rightImpl prims D t s r hr) hs) game s

end IdealCoupling

section IdealProjection

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- The stream world on an erased emulation. The table of the emulation is the second
`HiddenCache`, and `streamWorld` keeps the first one. -/
def leftEval {α : Type} (x : StateT (StreamCache C) (OracleComp (WorldSpec C)) α) :
    StateT ((HashCache C × HiddenCache C) × HiddenCache C) ProbComp α :=
  StateT.mk fun s => (fun r => (r.1.1, (r.2, treeSimCache r.1.2))) <$>
    (simulateQ (streamWorld prims D) (x.run (treeSimCacheInv s.2))).run s.1

theorem leftEval_pure {α : Type} (a : α) : leftEval prims D (C := C) (pure a) = pure a := by
  apply StateT.ext
  intro s
  simp [leftEval]

theorem leftEval_bind {α β : Type} (x : StateT (StreamCache C) (OracleComp (WorldSpec C)) α)
    (k : α → StateT (StreamCache C) (OracleComp (WorldSpec C)) β) :
    leftEval prims D (x >>= k) = leftEval prims D x >>= fun a => leftEval prims D (k a) := by
  apply StateT.ext
  intro s
  simp [leftEval, StateT.run_bind, simulateQ_bind, bind_map_left, map_bind]

theorem leftEval_lift {α : Type} (p : OracleComp (WorldSpec C) α) (s) :
    (leftEval prims D (StateT.lift p)).run s =
      (fun r => (r.1, (r.2, s.2))) <$> (simulateQ (streamWorld prims D) p).run s.1 := by
  simp [leftEval, StateT.run_lift, simulateQ_map, Functor.map_map]

/-- The log erasure and the stream world, as one monad map. -/
def leftHom : EmulationM C →ᵐ StateT ((HashCache C × HiddenCache C) × HiddenCache C) ProbComp where
  toFun _ x := leftEval prims D (treeSimErase x)
  toFun_pure' a := by
    rw [treeSimErase_pure, leftEval_pure]
  toFun_bind' x k := by
    rw [treeSimErase_bind, leftEval_bind]

/-- `treeSimEvaluate` after the log erasure, as one monad map. -/
def rightHom : EmulationM C →ᵐ StateT (HashCache C × HiddenCache C) ProbComp where
  toFun _ x := treeSimEvaluate prims (treeSimErase x)
  toFun_pure' a := by
    rw [treeSimErase_pure, treeSimEvaluate_pure]
  toFun_bind' x k := by
    rw [treeSimErase_bind, treeSimEvaluate_bind]

theorem stream_free_query (t : (LocalSpec C).Domain) :
    simulateQ (streamWorld prims D) (free (OracleComp.lift (OracleSpec.query t))) =
      streamWorld prims D (.inr t) := by
  simp [free]

theorem stream_sample {α : Type} (p : ProbComp α) :
    simulateQ (streamWorld prims D) (free (liftComp p (LocalSpec C))) = StateT.lift p := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    apply StateT.ext
    intro s
    simp [StateT.run_lift]
  | query_bind t k ih =>
    simp only [liftComp_bind, free_bind, simulateQ_bind, ih]
    apply StateT.ext
    intro s
    simp [StateT.run_bind, StateT.run_lift, free]
    rfl

def leftProj (s : IdealState C) : (HashCache C × HiddenCache C) × HiddenCache C :=
  ((s.1, s.2.2.1), s.2.1)

theorem leftHom_adversary (t : (LocalSpec C).Domain) (s) :
    ((leftHom prims D) ((emulatedRoles D).adversary (OracleComp.lift (OracleSpec.query t)))).run s =
      (fun r => (r.1, ((r.2, s.1.2), s.2))) <$> (localAnswer prims t).run s.1.1 := by
  change (leftEval prims D (treeSimErase ((emulatedRoles D).adversary _))).run s = _
  rw [show treeSimErase ((emulatedRoles D).adversary (OracleComp.lift (OracleSpec.query t))) =
    StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) from
      treeSimErase_adversary D _, leftEval_lift, treeSim_stream_adversary]
  simp [onHash, Functor.map_map]

theorem leftHom_free (t : (LocalSpec C).Domain) (s) :
    ((leftHom prims D) ((lifetimeHybridRoles D 0 0).honest (OracleComp.lift (OracleSpec.query t)))).run s =
      (fun r => (r.1, (r.2, s.2))) <$> (streamWorld prims D (.inr t)).run s.1 := by
  change (leftEval prims D (treeSimErase ((lifetimeHybridRoles D 0 0).honest _))).run s = _
  have h : (lifetimeHybridRoles D 0 0).honest (OracleComp.lift (OracleSpec.query t)) =
      StateT.lift (liftM (free (OracleComp.lift (OracleSpec.query t)))) := by
    simp [lifetimeHybridRoles]
  rw [h, treeSimErase_lift, leftEval_lift, stream_free_query]
  rfl

theorem left_free (t : (LocalSpec C).Domain) (s : IdealState C)
    (hidden : PrgInput C → StateT (IdealState C) ProbComp Bit)
    (hhidden : ∀ x, Hidden D x.1 → Prod.map id leftProj <$> (hidden x).run s =
      (fun r => (r.1, ((s.1, r.2), s.2.1))) <$> tableDraw s.2.2.1 (address x)) :
    Prod.map id leftProj <$> (withHidden prims D hidden t).run s =
      ((leftHom prims D) ((lifetimeHybridRoles D 0 0).honest
        (OracleComp.lift (OracleSpec.query t)))).run (leftProj s) := by
  rw [leftHom_free]
  rcases t with u | q | x
  · simp [withHidden, onCache, streamWorld, onHash, leftProj, Functor.map_map]
  · simp [withHidden, onCache, streamWorld, onHash, leftProj, Functor.map_map]
  · by_cases hx : Hidden D x.1
    · change Prod.map id leftProj <$> (if Hidden D x.1 then hidden x else _).run s = _
      rw [if_pos hx, hhidden x hx]
      simp only [streamWorld, if_pos hx, StateT.run_mk, leftProj]
      rw [randomOracle_run]
      simp [Functor.map_map, address]
    · change Prod.map id leftProj <$> (if Hidden D x.1 then hidden x else _).run s = _
      rw [if_neg hx]
      simp [streamWorld, hx, onCache, onHash, leftProj, Functor.map_map]

theorem emul_honest_hidden (x : PrgInput C) (hx : Hidden D x.1) :
    (emulatedRoles D).honest (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inr x)))) =
      StateT.mk fun cache => liftM (free (liftComp (((PrgInput C →ₒ Bit).randomOracle x).run cache)
        (LocalSpec C))) := by
  simp [emulatedRoles, hx]

theorem emul_honest_other (t : (LocalSpec C).Domain) (ht : ∀ x, t = .inr (.inr x) → ¬ Hidden D x.1) :
    (emulatedRoles D).honest (OracleComp.lift (OracleSpec.query t)) =
      StateT.lift (liftM (free (OracleComp.lift (OracleSpec.query t)))) := by
  rcases t with u | q | x
  · simp [emulatedRoles]
  · simp [emulatedRoles]
  · simp [emulatedRoles, ht x rfl]

theorem leftHom_lift_free (t : (LocalSpec C).Domain) (s) :
    ((leftHom prims D) (StateT.lift (liftM (free (OracleComp.lift (OracleSpec.query t)))))).run s =
      (fun r => (r.1, (r.2, s.2))) <$> (streamWorld prims D (.inr t)).run s.1 := by
  change (leftEval prims D (treeSimErase _)).run s = _
  rw [treeSimErase_lift, leftEval_lift, stream_free_query]
  rfl

theorem leftHom_emul_hidden (x : PrgInput C) (hx : Hidden D x.1) (s) :
    ((leftHom prims D) ((emulatedRoles D).honest
      (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inr x)))))).run s =
      (fun r => (r.1, (s.1, r.2))) <$> tableDraw s.2 (address x) := by
  rw [emul_honest_hidden D x hx]
  change (leftEval prims D (treeSimErase _)).run s = _
  have he : treeSimErase (StateT.mk fun cache =>
      (liftM (free (liftComp (((PrgInput C →ₒ Bit).randomOracle x).run cache) (LocalSpec C))) :
        WriterT (CallLog C) (OracleComp (WorldSpec C)) (Bit × StreamCache C))) =
      StateT.mk fun cache => free (liftComp (((PrgInput C →ₒ Bit).randomOracle x).run cache)
        (LocalSpec C)) := by
    apply StateT.ext
    intro cache
    exact keygenEraseLog_lift _
  rw [he]
  have h := congrArg (Functor.map (fun r => (r.1, (s.1, r.2))))
    (treeSimCache_query (treeSimCacheInv s.2) x)
  rw [treeSimCache_inverse, randomOracle_run] at h
  simp only [leftEval, StateT.run_mk, stream_sample, StateT.run_lift, bind_pure_comp,
    Functor.map_map] at h ⊢
  exact h

theorem left_emul (t : (LocalSpec C).Domain) (s : IdealState C) :
    Prod.map id leftProj <$> (withHidden prims D (fun x => firstTable (address x)) t).run s =
      ((leftHom prims D) ((emulatedRoles D).honest (OracleComp.lift (OracleSpec.query t)))).run
        (leftProj s) := by
  rcases t with u | q | x
  · rw [emul_honest_other D _ (by simp), leftHom_lift_free]
    simp [withHidden, onCache, streamWorld, onHash, leftProj, Functor.map_map]
  · rw [emul_honest_other D _ (by simp), leftHom_lift_free]
    simp [withHidden, onCache, streamWorld, onHash, leftProj, Functor.map_map]
  · by_cases hx : Hidden D x.1
    · rw [leftHom_emul_hidden prims D x hx]
      change Prod.map id leftProj <$> (if Hidden D x.1 then firstTable (address x) else
        onCache (localAnswer prims (.inr (.inr x)))).run s = _
      rw [if_pos hx]
      simp [firstTable, leftProj, Functor.map_map]
    · rw [emul_honest_other D _ (by simpa using hx), leftHom_lift_free]
      change Prod.map id leftProj <$> (if Hidden D x.1 then firstTable (address x) else
        onCache (localAnswer prims (.inr (.inr x)))).run s = _
      rw [if_neg hx]
      simp [streamWorld, hx, onCache, onHash, leftProj, Functor.map_map]

/-- Each step of `leftImpl` without its flag is the step of the ideal side of the PRF
experiment. -/
theorem left_projection (t : (Spec4 C).Domain) (s : IdealState C) :
    Prod.map id leftProj <$> ((leftImpl prims D) t).run s =
      ((leftHom prims D) (impl4 D (lifetimeHybridRoles D 0 0) t)).run (leftProj s) := by
  rcases t with ((t | t) | t) | t
  · erw [leftHom_adversary]
    simp [leftImpl, localImpl, onCache, leftProj, Functor.map_map]
  · exact left_emul prims D t s
  · exact left_free prims D t s _ fun x _ => by simp [flagged, secondTable, leftProj, Functor.map_map]
  · exact left_free prims D t s _ fun x _ => by simp [secondTable, leftProj, Functor.map_map]

/-- The single table of the next world. It reads the earlier runs first, then run `n`. -/
def merge (first second : HiddenCache C) : HiddenCache C := fun x =>
  match first x with
  | some v => some v
  | none => second x

def rightProj (s : IdealState C) : HashCache C × HiddenCache C := (s.1, merge s.2.1 s.2.2.1)

theorem merge_cacheQuery_first (first second : HiddenCache C) (x : Address C) (b : Bit) :
    merge (first.cacheQuery x b) second = (merge first second).cacheQuery x b := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [merge]
  · simp [merge, QueryCache.cacheQuery_of_ne _ _ hy]

theorem merge_cacheQuery_second (first second : HiddenCache C) (x : Address C) (b : Bit)
    (h : first x = none) :
    merge first (second.cacheQuery x b) = (merge first second).cacheQuery x b := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [merge, h]
  · simp [merge, QueryCache.cacheQuery_of_ne _ _ hy]

theorem merge_cacheQuery_second_of_some (first second : HiddenCache C) (x : Address C) (v b : Bit)
    (h : first x = some v) : merge first (second.cacheQuery x b) = merge first second := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [merge, h]
  · simp [merge, QueryCache.cacheQuery_of_ne _ _ hy]

theorem cacheQuery_eq_self (c : HiddenCache C) (x : Address C) (v : Bit) (h : c x = some v) :
    c.cacheQuery x v = c := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [h]
  · simp [QueryCache.cacheQuery_of_ne _ _ hy]

theorem mergedFirst_proj (x : Address C) (s : IdealState C) :
    Prod.map id rightProj <$> (mergedFirst x).run s =
      (fun r => (r.1, (s.1, r.2))) <$> tableDraw (merge s.2.1 s.2.2.1) x := by
  rcases h1 : s.2.1 x with _ | v <;> rcases h2 : s.2.2.1 x with _ | w
  · simp [mergedFirst, tableDraw, merge, h1, h2, rightProj, Functor.map_map,
      merge_cacheQuery_first]
  · have hm : merge s.2.1 s.2.2.1 x = some w := by simp [merge, h1, h2]
    simp [mergedFirst, tableDraw, hm, h1, h2, rightProj, merge_cacheQuery_first,
      cacheQuery_eq_self _ _ _ hm]
  · have hm : merge s.2.1 s.2.2.1 x = some v := by simp [merge, h1]
    simp [mergedFirst, tableDraw, hm, h1, h2, rightProj]
  · have hm : merge s.2.1 s.2.2.1 x = some v := by simp [merge, h1]
    simp [mergedFirst, tableDraw, hm, h1, h2, rightProj]

theorem mergedSecond_proj (x : Address C) (s : IdealState C) :
    Prod.map id rightProj <$> (mergedSecond x).run s =
      (fun r => (r.1, (s.1, r.2))) <$> tableDraw (merge s.2.1 s.2.2.1) x := by
  rcases h1 : s.2.1 x with _ | v <;> rcases h2 : s.2.2.1 x with _ | w
  · simp [mergedSecond, tableDraw, merge, h1, h2, rightProj, Functor.map_map,
      merge_cacheQuery_second _ _ _ _ h1]
  · have hm : merge s.2.1 s.2.2.1 x = some w := by simp [merge, h1, h2]
    simp [mergedSecond, tableDraw, hm, h1, h2, rightProj]
  · have hm : merge s.2.1 s.2.2.1 x = some v := by simp [merge, h1]
    simp [mergedSecond, tableDraw, hm, h1, h2, rightProj,
      merge_cacheQuery_second_of_some _ _ _ _ _ h1]
  · have hm : merge s.2.1 s.2.2.1 x = some v := by simp [merge, h1]
    simp [mergedSecond, tableDraw, hm, h1, h2, rightProj,
      merge_cacheQuery_second_of_some _ _ _ _ _ h1]

theorem rightHom_adversary (t : (LocalSpec C).Domain) (s) :
    ((rightHom prims) ((emulatedRoles D).adversary (OracleComp.lift (OracleSpec.query t)))).run s =
      (fun r => (r.1, (r.2, s.2))) <$> (localAnswer prims t).run s.1 := by
  change (treeSimEvaluate prims ((treeSimErasedRoles D).adversary _)).run s = _
  rw [treeSimEvaluate_adversary, treeSim_stream_adversary]
  simp [onHash]

theorem rightHom_honest (t : (LocalSpec C).Domain) (s) :
    ((rightHom prims) ((emulatedRoles D).honest (OracleComp.lift (OracleSpec.query t)))).run s =
      (streamWorld prims D (.inr t)).run s := by
  change (treeSimEvaluate prims ((treeSimErasedRoles D).honest _)).run s = _
  rw [treeSimEvaluate_honest, stream_free_query]

theorem rightHom_free (t : (LocalSpec C).Domain) (s) :
    ((rightHom prims) ((lifetimeHybridRoles D 0 0).honest (OracleComp.lift (OracleSpec.query t)))).run s =
      (fun r => (r.1, (r.2, s.2))) <$> (localAnswer prims t).run s.1 := by
  change (treeSimEvaluate prims (treeSimErase ((lifetimeHybridRoles D 0 0).honest _))).run s = _
  have h : (lifetimeHybridRoles D 0 0).honest (OracleComp.lift (OracleSpec.query t)) =
      StateT.lift (liftM (free (OracleComp.lift (OracleSpec.query t)))) := by
    simp [lifetimeHybridRoles]
  rw [h, treeSimErase_lift, treeSimEvaluate_lift]
  simp [onHash, simulateQ_free]

theorem right_hidden (t : (LocalSpec C).Domain) (s : IdealState C)
    (hidden : Address C → StateT (IdealState C) ProbComp Bit)
    (hhidden : ∀ x, Prod.map id rightProj <$> (hidden x).run s =
      (fun r => (r.1, (s.1, r.2))) <$> tableDraw (merge s.2.1 s.2.2.1) x) :
    Prod.map id rightProj <$> (withHidden prims D (fun x => hidden (address x)) t).run s =
      (streamWorld prims D (.inr t)).run (rightProj s) := by
  rcases t with u | q | x
  · simp [withHidden, onCache, streamWorld, onHash, rightProj, Functor.map_map]
  · simp [withHidden, onCache, streamWorld, onHash, rightProj, Functor.map_map]
  · change Prod.map id rightProj <$> (if Hidden D x.1 then hidden (address x) else
      onCache (localAnswer prims (.inr (.inr x)))).run s = _
    by_cases hx : Hidden D x.1
    · rw [if_pos hx, hhidden]
      simp only [streamWorld, if_pos hx, StateT.run_mk, rightProj]
      rw [randomOracle_run]
      simp [address]
    · rw [if_neg hx]
      simp [streamWorld, hx, onCache, onHash, rightProj, Functor.map_map]

/-- Each step of `rightImpl` with its two tables merged is the step of the next world. -/
theorem right_projection (t : (Spec4 C).Domain) (s : IdealState C) :
    Prod.map id rightProj <$> ((rightImpl prims D) t).run s =
      ((rightHom prims) (impl4 D (emulatedRoles D) t)).run (rightProj s) := by
  rcases t with ((t | t) | t) | t
  · erw [rightHom_adversary prims D]
    simp [rightImpl, localImpl, onCache, rightProj, Functor.map_map]
  · erw [rightHom_honest]
    exact right_hidden prims D t s _ fun x => mergedFirst_proj x s
  · erw [rightHom_free prims D]
    rcases t with u | q | x
    · simp [rightImpl, withHidden, onCache, rightProj, Functor.map_map]
    · simp [rightImpl, withHidden, onCache, rightProj, Functor.map_map]
    · change Prod.map id rightProj <$> (if Hidden D x.1 then
        flagged (onCache (localAnswer prims (.inr (.inr x)))) else
        onCache (localAnswer prims (.inr (.inr x)))).run s = _
      split_ifs
      · simp [flagged, onCache, rightProj, Functor.map_map]
      · simp [onCache, rightProj, Functor.map_map]
  · erw [rightHom_honest]
    exact right_hidden prims D t s _ fun x => mergedSecond_proj x s

end IdealProjection

section IdealChain

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (D : C.Coalition)
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (A : LifetimeAdversary C E)

/-- The start state of the two coupled worlds. -/
def idealStart : IdealState C := (∅, ∅, ∅, false)

theorem treeSimCacheInv_empty : treeSimCacheInv (∅ : HiddenCache C) = ∅ := by
  funext x
  rfl

theorem probOutput_fst_of_projection {σ τ : Type} {α : Type} (Y : ProbComp (α × σ))
    (X : ProbComp (α × τ)) (π : σ → τ) (h : 𝒟[Prod.map id π <$> Y] = 𝒟[X]) (a : α) :
    Pr[= a | Prod.fst <$> Y] = Pr[= a | Prod.fst <$> X] := by
  have h' : 𝒟[Prod.fst <$> Y] = 𝒟[Prod.fst <$> X] := by
    have e : Prod.fst <$> Y = Prod.fst <$> (Prod.map id π <$> Y) := by
      simp [Functor.map_map]
    rw [e, evalDist_map, h, ← evalDist_map]
  rw [probOutput_def, probOutput_def, h']

/-- The ideal side of the PRF experiment of run `n` is the left coupled world. -/
theorem left_world (n : ℕ) :
    Pr[= true | (simulateQ (streamWorld prims D) (emulationGame (lifetimeGameWith K circuits settings
      attempts (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A))).run' (∅, ∅)] =
      Pr[= true | (simulateQ (leftImpl prims D) (program4 D K circuits settings attempts A n)).run'
        idealStart] := by
  rw [← program4_left, LifetimeKeygenHopProof.emulationGame_erased]
  have hY : (simulateQ (streamWorld prims D) ((treeSimErase (simulateQ (impl4 D
      (lifetimeHybridRoles D 0 0)) (program4 D K circuits settings attempts A n))).run' ∅)).run'
        (∅, ∅) = Prod.fst <$> ((leftHom prims D) (simulateQ (impl4 D (lifetimeHybridRoles D 0 0))
          (program4 D K circuits settings attempts A n))).run ((∅, ∅), ∅) := by
    change _ = Prod.fst <$> (leftEval prims D _).run ((∅, ∅), ∅)
    simp [leftEval, treeSimCacheInv_empty, StateT.run'_eq, simulateQ_map, Functor.map_map]
  rw [hY, LifetimeEmulatedBudget.hom_simulateQ]
  have hp := evalDist_simulateQ_state_projection (leftImpl prims D)
    (fun t => (leftHom prims D) (impl4 D (lifetimeHybridRoles D 0 0) t)) leftProj
    (fun t s => by rw [left_projection]) (program4 D K circuits settings attempts A n) idealStart
  exact (probOutput_fst_of_projection _ _ _ hp true).symm

/-- The run roles of world `n + 1` after `rightHom`. Run `n + 1` takes the image of the
adversary copy. -/
def rightRoles (n r : ℕ) : Roles C (StateT (HashCache C × HiddenCache C) ProbComp) :=
  if r < n + 1 then
    ⟨fun p => (rightHom prims) ((emulatedRoles D).adversary p),
      fun p => (rightHom prims) ((emulatedRoles D).honest p)⟩
  else
    ⟨fun p => (rightHom prims) ((emulatedRoles D).adversary p),
      fun p => (rightHom prims) ((emulatedRoles D).adversary p)⟩

def rightBase : Roles C (StateT (HashCache C × HiddenCache C) ProbComp) :=
  ⟨fun p => (rightHom prims) ((emulatedRoles D).adversary p),
    fun p => (rightHom prims) ((lifetimeHybridRoles D 0 0).honest p)⟩

/-- In the next world, a free honest step and an adversary step have the same law. -/
theorem rightHom_free_eq {α : Type} (p : OracleComp (LocalSpec C) α) :
    (rightHom prims) ((lifetimeHybridRoles D 0 0).honest p) =
      (rightHom prims) ((emulatedRoles D).adversary p) := by
  change treeSimEvaluate prims (treeSimErase _) = treeSimEvaluate prims ((treeSimErasedRoles D).adversary p)
  have h : (lifetimeHybridRoles D 0 0).honest p = StateT.lift (liftM (free p)) := by
    simp [lifetimeHybridRoles]
  rw [h, treeSimErase_lift, treeSimEvaluate_lift, treeSimEvaluate_adversary, treeSim_stream_adversary,
    simulateQ_free]

theorem rolesHom_next (n r : ℕ) :
    LifetimeEmulatedBudget.RolesHom (rightHom prims) (nextRoles D n r) (rightRoles prims D n r) := by
  unfold nextRoles rightRoles
  split_ifs
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem rolesHom_hybrid_next (n r : ℕ) :
    LifetimeEmulatedBudget.RolesHom (rightHom prims) (lifetimeHybridRoles D (n + 1) r)
      (rightRoles prims D n r) := by
  by_cases h1 : r < n + 1
  · rw [hybridRoles_lt D h1]
    simp only [rightRoles, h1, if_true]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · by_cases h2 : r = n + 1
    · subst h2
      rw [hybridRoles_self D]
      simp only [rightRoles, h1, if_false]
      exact ⟨fun _ => rfl, fun p => rightHom_free_eq prims D p⟩
    · rw [hybridRoles_gt D h1 h2]
      simp only [rightRoles, h1, if_false]
      exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- World `n + 1` is the right coupled world. -/
theorem right_world (n : ℕ) :
    Pr[= true | (simulateQ (worldAnswer prims) (emulationGame (lifetimeGameWith K circuits settings
      attempts (lifetimeHybridRoles D (n + 1)) (lifetimeHybridRoles D (n + 1) (n + 1)) D A))).run' ∅] =
      Pr[= true | (simulateQ (rightImpl prims D) (program4 D K circuits settings attempts A n)).run'
        idealStart] := by
  rw [LifetimeKeygenHopProof.emulationGame_erased]
  have hY : ∀ L : EmulationM C Bool, (simulateQ (worldAnswer prims) ((treeSimErase L).run' ∅)).run' ∅ =
      Prod.fst <$> ((rightHom prims) L).run (∅, ∅) := by
    intro L
    change _ = Prod.fst <$> (treeSimEvaluate prims _).run (∅, ∅)
    simp [treeSimEvaluate, treeSimCacheInv_empty, StateT.run'_eq, simulateQ_map, Functor.map_map]
  have hbase : LifetimeEmulatedBudget.RolesHom (rightHom prims)
      (lifetimeHybridRoles D (n + 1) (n + 1)) (rightBase prims D) := by
    rw [hybridRoles_self D]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  rw [hY, LifetimeEmulatedBudget.hom_lifetimeGameWith (rightHom prims) K circuits settings attempts _ _
    (rightRoles prims D n) (rightBase prims D) (rolesHom_hybrid_next prims D n) hbase D A,
    ← LifetimeEmulatedBudget.hom_lifetimeGameWith (rightHom prims) K circuits settings attempts
      (nextRoles D n) (lifetimeHybridRoles D 0 0) (rightRoles prims D n) (rightBase prims D)
      (rolesHom_next prims D n) ⟨fun _ => rfl, fun _ => rfl⟩ D A,
    ← program4_right, LifetimeEmulatedBudget.hom_simulateQ]
  have hp := evalDist_simulateQ_state_projection (rightImpl prims D)
    (fun t => (rightHom prims) (impl4 D (emulatedRoles D) t)) rightProj
    (fun t s => by rw [right_projection]) (program4 D K circuits settings attempts A n) idealStart
  have he : rightProj (idealStart (C := C)) = (∅, ∅) := by
    simp only [rightProj, idealStart]
    congr 1
  rw [he] at hp
  exact (probOutput_fst_of_projection _ _ _ hp true).symm

/-- The ideal side of hop `n` against world `n + 1`, for one fixed `Th`. -/
theorem ideal_point (n : ℕ) :
    |(Pr[= true | (simulateQ (streamWorld prims D) (emulationGame (lifetimeGameWith K circuits
      settings attempts (lifetimeHybridRoles D n) (lifetimeHybridRoles D n n) D A))).run' (∅, ∅)]).toReal -
      (Pr[= true | (simulateQ (worldAnswer prims) (emulationGame (lifetimeGameWith K circuits settings
        attempts (lifetimeHybridRoles D (n + 1)) (lifetimeHybridRoles D (n + 1) (n + 1)) D A))).run'
          ∅]).toReal| ≤
      (Pr[IdealBad ∘ Prod.snd | (simulateQ (leftImpl prims D)
        (program4 D K circuits settings attempts A n)).run idealStart]).toReal := by
  rw [left_world, right_world]
  exact (abs_probOutput_toReal_sub_le_tvDist _ _).trans (ideal_coupling prims D _ _)

end IdealChain

section IdealSide

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The ideal PRF experiment of `lifetimeRunReductionSampled n` is the stream world of hybrid `n`. -/
theorem reductionProbability_ideal (n : ℕ) :
    reductionProbability K settings attempts aes circuitsOf D A false n =
      (Pr[= true | ($ᵗ (MpcDomain → HashOutput)) >>= fun values =>
        (simulateQ (streamWorld ⟨thOf values, aes⟩ D)
          (reductionGame K settings attempts circuitsOf D A values n)).run' (∅, ∅)]).toReal := by
  unfold reductionProbability
  simp only [Bool.false_eq_true, if_false]
  congr 1
  unfold PRFScheme.prfIdealExp lifetimeRunReductionSampled
  rw [simulateQ_bind, PRFScheme.simulateQ_prfIdealQueryImpl_liftComp]
  simp only [StateT.run'_eq, StateT.run_bind, liftM, StateT.run_monadLift, monadLift_self,
    bind_pure_comp, map_bind, bind_map_left]
  refine probOutput_bind_congr' _ true fun values => ?_
  have h := prfIdealExp_prgReduction ⟨thOf values, aes⟩ D
    (reductionGame K settings attempts circuitsOf D A values n)
  unfold PRFScheme.prfIdealExp at h
  simp only [StateT.run'_eq] at h
  rw [← h]
  rfl

/-- The average over `Th` of the bad event of the ideal side of hop `n`. -/
def idealBad (n : ℕ) : ℝ :=
  ∑ values, (Pr[= values | $ᵗ (MpcDomain → HashOutput)]).toReal *
    (Pr[IdealBad ∘ Prod.snd | (simulateQ (leftImpl ⟨thOf values, aes⟩ D)
      (program4 D K (circuitsOf (thOf values)) settings attempts A n)).run idealStart]).toReal

/-- The ideal side of each hop is identical until `IdealBad`. -/
theorem ideal_transport (n : ℕ) :
    |reductionProbability K settings attempts aes circuitsOf D A false n -
      chronologicalProbability K settings attempts aes circuitsOf D A (n + 1)| ≤
      idealBad K settings attempts aes circuitsOf D A n := by
  have hpoint (values : MpcDomain → HashOutput) :
      |(Pr[fun b => b = true | (simulateQ (streamWorld ⟨thOf values, aes⟩ D)
        (reductionGame K settings attempts circuitsOf D A values n)).run' (∅, ∅)]).toReal -
      (Pr[fun b => b = true | (simulateQ (worldAnswer ⟨thOf values, aes⟩)
        (chronologicalGame K settings attempts D A (circuitsOf (thOf values)) (n + 1))).run' ∅]).toReal| ≤
        (Pr[IdealBad ∘ Prod.snd | (simulateQ (leftImpl ⟨thOf values, aes⟩ D)
          (program4 D K (circuitsOf (thOf values)) settings attempts A n)).run idealStart]).toReal := by
    have hc := accepts_chronological K settings attempts aes circuitsOf D A values (n + 1)
    rw [accepts_eq_probOutput, accepts_eq_probOutput] at hc
    simp only [probEvent_eq_eq_probOutput]
    rw [hc]
    exact ideal_point ⟨thOf values, aes⟩ D K (circuitsOf (thOf values)) settings attempts A n
  have havg := abs_probEvent_bind_sub_le_sum ($ᵗ (MpcDomain → HashOutput)) _ _
    (fun b => b = true) _ hpoint
  rw [reductionProbability_ideal]
  unfold chronologicalProbability
  have hf : (fun r : Bool × ℕ => r.1 = true) = (fun b => b = true) ∘ Prod.fst := rfl
  rw [hf, ← probEvent_map, LifetimeKeygenHopProof.lifetimeRun_output]
  simpa only [probEvent_eq_eq_probOutput, idealBad] using havg

end IdealSide

section Assembly

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The stream-key bad event of each hybrid, for each `Th`, fits the real share. -/
def RealBadBound (Q : ℕ) : Prop :=
  let F := ceremonyFuel (circuitsOf fun _ => 0) settings
  HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q →
  keySplit C (Q + lifetimeOverhead C attempts Q + (F + 2) * Q) < 2 →
  ∀ (n : Fin (lifetimeRuns attempts)) (values : MpcDomain → HashOutput),
    probBad_streamKey ⟨thOf values, aes⟩ D (reductionGame K settings attempts circuitsOf D A values n) ≤
      (realShare C attempts Q F : ℝ) / 2 ^ 256

/-- The bad event of the ideal side of each hop, for each `Th`, fits the ideal share. -/
def IdealBadBound (Q : ℕ) : Prop :=
  let F := ceremonyFuel (circuitsOf fun _ => 0) settings
  HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q →
  keySplit C (Q + lifetimeOverhead C attempts Q + (F + 2) * Q) < 2 →
  ∀ (n : Fin (lifetimeRuns attempts)) (values : MpcDomain → HashOutput),
    (Pr[IdealBad ∘ Prod.snd | (simulateQ (leftImpl ⟨thOf values, aes⟩ D)
      (program4 D K (circuitsOf (thOf values)) settings attempts A n)).run idealStart]).toReal ≤
      (idealShare C attempts Q : ℝ) / 2 ^ 256

theorem realBad_le (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ values : MpcDomain → HashOutput, probBad_streamKey ⟨thOf values, aes⟩ D
      (reductionGame K settings attempts circuitsOf D A values n) ≤ ε) :
    realBad K settings attempts aes circuitsOf D A n ≤ ε :=
  (Finset.sum_le_sum fun values _ => mul_le_mul_of_nonneg_left (h values) ENNReal.toReal_nonneg).trans
    (sum_probOutput_mul_const_le _ hε)

/-- The transport of `LifetimeAllowance` in the case `keySplit (q₀ + q) < 2`, from the two
shares. -/
theorem smallSplit_of_bounds (Q : ℕ)
    (hQ : HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q)
    (hreal : RealBadBound K settings attempts aes circuitsOf D A Q)
    (hideal : IdealBadBound K settings attempts aes circuitsOf D A Q) :
    LifetimeAllowance.LifetimePrfTransportSmallSplit K settings attempts aes circuitsOf D A Q := by
  intro hsplit n
  have h1 := (real_transport K settings attempts aes circuitsOf D A n).trans
    (realBad_le K settings attempts aes circuitsOf D A n (by positivity) (hreal hQ hsplit n))
  have h2 := (ideal_transport K settings attempts aes circuitsOf D A n).trans
    ((Finset.sum_le_sum fun values _ => mul_le_mul_of_nonneg_left (hideal hQ hsplit n values)
      ENNReal.toReal_nonneg).trans (sum_probOutput_mul_const_le _ (by positivity)))
  have he := shares_eq (C := C) attempts Q (ceremonyFuel (circuitsOf fun _ => 0) settings)
  linarith

/-- The original lifetime statement from the two shares, the keygen hop and the dealer-world
contract. -/
theorem lifetimeSecurity_of_bounds
    (hsource : (∀ Th, CircuitsCompute (circuitsOf Th) Th) → FixedShape circuitsOf →
      0 < settings.batchSize → ∀ (D : C.Coalition) (A : LifetimeAdversary C E) (Q : ℕ),
        HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q →
        RealBadBound K settings attempts aes circuitsOf D A Q ∧
        IdealBadBound K settings attempts aes circuitsOf D A Q ∧
        LifetimeHybridOrder.LifetimeKeygenHop K settings attempts aes circuitsOf D A Q ∧
        LifetimeAllowance.LifetimeAfterKeygen K settings attempts aes circuitsOf D A Q) :
    LifetimeSecurityStatementSampled K settings attempts aes circuitsOf :=
  LifetimeAllowance.lifetimeSecurity_of_smallSplit K settings attempts aes circuitsOf
    fun hcompute hshape hbatch D A Q hQ =>
      let ⟨hr, hi, hk, ha⟩ := hsource hcompute hshape hbatch D A Q hQ
      ⟨smallSplit_of_bounds K settings attempts aes circuitsOf D A Q hQ hr hi, hk, ha⟩

end Assembly

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrfTransportProof.designCounts_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designCounts_le

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrfTransportProof.real_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms real_transport

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrfTransportProof.ideal_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ideal_coupling

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrfTransportProof.ideal_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ideal_transport

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrfTransportProof.smallSplit_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms smallSplit_of_bounds

/-- info: 'ThresholdLeanXmssSecurity.LifetimePrfTransportProof.lifetimeSecurity_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimeSecurity_of_bounds

end ThresholdLeanXmssSecurity.LifetimePrfTransportProof
