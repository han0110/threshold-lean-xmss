import ThresholdLeanXmssSecurity.Proof.TreeCheckHonestDisc
import ThresholdLeanXmssSecurity.Proof.TreeLockstepOpenedRest

/-! # Exchange-indexed coin labels

A floor excludes future coin keys below its limit. The segment clock keeps
both bounds on coin labels and the expansion keys of the current local pass.
The real check uses a delayed clock because a coin key is queried after the
exchange of the coin whose initial label it records.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckCoinClock
open TreeCheckHonestDisc TreeCheckWalkState TreeSimHashCount
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E α β : Type}

def CoinBelow (limit : ℕ) : (LocalSpec C).Domain → Prop
  | .inr (.inl (.coinKey _ label _)) => label < limit
  | _ => False

def CheckFloor (limit : ℕ) (P : OracleComp (PartySpec C E RealSpec) (Option α)) : Prop :=
  IsQueryBoundP P (PartyQuery (E := E) (G := RealSpec) (CoinBelow limit)) 0

theorem CheckFloor.pure (limit : ℕ) (a : Option α) :
    CheckFloor (C := C) (E := E) limit (Pure.pure a) := isQueryBoundP_pure _ _ _

theorem CheckFloor.mono {l l' : ℕ} {P : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : CheckFloor l P) (le : l' ≤ l) : CheckFloor l' P := by
  apply IsQueryBoundP.of_imp (fun q hq => ?_) h
  rcases q with (q | out) | impossible
  · rcases q with noise | (q | prg)
    · exact hq.elim
    · cases q <;> simp only [PartyQuery, CoinBelow] at hq ⊢
      all_goals first | exact hq.elim | omega
    · exact hq.elim
  · exact hq.elim
  · exact impossible.elim

theorem CheckFloor.bind {l : ℕ} {P : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : CheckFloor l P) (f : Option α → OracleComp (PartySpec C E RealSpec) (Option β))
    (rest : ∀ a, a ∈ support P → CheckFloor l (f a)) : CheckFloor l (P >>= f) :=
  isQueryBoundP_bind h rest

theorem CheckFloor.party_bind {l : ℕ} {p : PartyM C E RealSpec α}
    {f : α → PartyM C E RealSpec β} (h : CheckFloor l p.run)
    (rest : ∀ a, some a ∈ support p.run → CheckFloor l (f a).run) :
    CheckFloor l (p >>= f).run := by
  simp only [OptionT.run_bind, Option.elimM]
  apply h.bind
  intro a ha
  cases a with
  | none => exact .pure _ _
  | some a => exact rest a ha

theorem CheckFloor.residual {l n : ℕ}
    {P Q : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : CheckFloor l P) (r : Residual n P Q) : CheckFloor l Q := by
  induction r with
  | refl => exact h
  | queryLocal n q k answer Q r ih =>
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= k) _ 0 at h
    rw [isQueryBoundP_query_bind_iff] at h
    exact ih (by simpa [CheckFloor] using h.2 answer)
  | round n out k inbox Q r ih =>
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= k) _ 0 at h
    rw [isQueryBoundP_query_bind_iff] at h
    exact ih (by simpa [CheckFloor] using h.2 inbox)
  | done => exact .pure _ _

theorem CheckFloor.of_quiet {l : ℕ} {p : PartyM C E RealSpec α}
    (h : PartyBudget CheckQuery p 0) : CheckFloor l p.run := by
  apply IsQueryBoundP.of_imp (fun q hq => ?_) h
  rcases q with (q | out) | impossible
  · rcases q with noise | (q | prg)
    · exact hq.elim
    · cases q <;> simp_all [PartyQuery, CoinBelow, CheckQuery]
    · exact hq.elim
  · exact hq.elim
  · exact impossible.elim

def ClockLocal (lab : ℕ → ℕ) (j : ℕ) (keys : Set HashOutput) : (LocalSpec C).Domain → Prop
  | .inr (.inl (.coinKey _ label _)) => lab j ≤ label ∧ label < lab (j + 1)
  | .inr (.inl (.expand key _)) => key ∈ keys
  | _ => True

inductive Clocked (lab : ℕ → ℕ) : ℕ → Set HashOutput →
    OracleComp (PartySpec C E RealSpec) (Option α) → Prop
  | pure (j keys a) : Clocked lab j keys (pure a)
  | queryLocal (j keys q k) (query : ClockLocal lab j keys q)
      (rest : ∀ r, Clocked lab j (localKeys keys q r) (k r)) :
      Clocked lab j keys (.roll (.inl (.inl q)) k)
  | round (j keys out k) (rest : ∀ inbox, Clocked lab (j + 1) ∅ (k inbox)) :
      Clocked lab j keys (.roll (.inl (.inr out)) k)

theorem ClockLocal.mono_keys {lab : ℕ → ℕ} {j : ℕ} {keys keys' : Set HashOutput}
    (le : keys ⊆ keys') {q : (LocalSpec C).Domain} (h : ClockLocal lab j keys q) :
    ClockLocal lab j keys' q := by
  rcases q with noise | (q | prg)
  · trivial
  · cases q <;> simp only [ClockLocal] at h ⊢
    all_goals first | trivial | exact h | exact le h
  · trivial

theorem Clocked.mono_keys {lab : ℕ → ℕ} {j : ℕ} {keys keys' : Set HashOutput}
    {P : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : Clocked lab j keys P) (le : keys ⊆ keys') : Clocked lab j keys' P := by
  induction h generalizing keys' with
  | pure => exact .pure _ _ _
  | queryLocal j keys q k query rest ih =>
    exact .queryLocal _ _ _ _ (query.mono_keys le) (fun r => ih r (localKeys_mono le q r))
  | round j keys out k rest ih => exact .round _ _ _ _ (fun r => ih r (Set.Subset.refl _))

theorem Clocked.local_inv {lab : ℕ → ℕ} {j : ℕ} {keys : Set HashOutput}
    {q : (LocalSpec C).Domain} {k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : Clocked lab j keys (.roll (.inl (.inl q)) k)) :
    ClockLocal lab j keys q ∧ ∀ r, Clocked lab j (localKeys keys q r) (k r) := by
  cases h with | queryLocal _ _ _ _ query rest => exact ⟨query, rest⟩

theorem Clocked.round_inv {lab : ℕ → ℕ} {j : ℕ} {keys : Set HashOutput}
    {out : Mail C E} {k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : Clocked lab j keys (.roll (.inl (.inr out)) k)) :
    ∀ inbox, Clocked lab (j + 1) ∅ (k inbox) := by
  cases h with | round _ _ _ _ rest => exact rest

theorem quiet_clock {lab : ℕ → ℕ} {j : ℕ} {keys : Set HashOutput}
    {q : (LocalSpec C).Domain} (h : ¬ CheckQuery q) : ClockLocal lab j keys q := by
  rcases q with noise | (q | prg)
  · trivial
  · cases q <;> simp_all [CheckQuery, ClockLocal]
  · trivial

-- Port of TreeCheckHonestDisc.Disc.of_quiet, with the segment index retained.
theorem Clocked.of_quiet {lab : ℕ → ℕ} {j : ℕ} {keys : Set HashOutput}
    {p : PartyM C E RealSpec α} (h : PartyBudget CheckQuery p 0) : Clocked lab j keys p.run := by
  unfold PartyBudget at h
  generalize p.run = P at h ⊢
  induction P generalizing j keys with
  | pure a => exact .pure _ _ _
  | queryBind t k ih =>
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query t) >>= k) _ 0 at h
    rw [isQueryBoundP_query_bind_iff] at h
    have noQuery : ¬ PartyQuery CheckQuery t := by simpa using h.1
    have tail : ∀ r, IsQueryBoundP (k r) (PartyQuery (E := E) (G := RealSpec) CheckQuery) 0 := by
      simpa using h.2
    rcases t with (q | out) | impossible
    · exact .queryLocal _ _ _ _ (quiet_clock noQuery) (fun r => ih r (tail r))
    · exact .round _ _ _ _ (fun r => ih r (tail r))
    · exact impossible.elim

-- Port of TreeCheckHonestDisc.CheckDisc.timed_bind.
theorem Clocked.timed_bind {lab : ℕ → ℕ} {j m : ℕ} {keys : Set HashOutput}
    {oa : OracleComp (PartySpec C E RealSpec) (Option β)}
    (timed : TreeSimCheckTimed m oa) (h : Clocked lab j keys oa)
    (f : Option β → OracleComp (PartySpec C E RealSpec) (Option α))
    (abort : f none = Pure.pure none)
    (rest : ∀ a, some a ∈ support oa → Clocked lab (j + m) ∅ (f (some a))) :
    Clocked lab j keys (oa >>= f) := by
  induction timed generalizing j keys with
  | abort m => rw [pure_bind, abort]; exact .pure _ _ _
  | done a =>
    rw [pure_bind]
    exact (rest a (by simp)).mono_keys (Set.empty_subset _)
  | queryLocal m q k hk ih =>
    refine .queryLocal _ _ _ _ h.local_inv.1 fun r => ?_
    apply ih r (h.local_inv.2 r)
    intro a ha
    apply rest a
    change some a ∈ support (OracleComp.lift (OracleSpec.query
      (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= k)
    rw [mem_support_bind_iff]
    exact ⟨r, by simp; exact Set.mem_univ _, ha⟩
  | round m out k hk ih =>
    refine .round _ _ _ _ fun inbox => ?_
    apply ih inbox (h.round_inv inbox)
    intro a ha
    apply (show Clocked lab (j + 1 + m) ∅ (f (some a)) from by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rest a (by
        change some a ∈ support (OracleComp.lift (OracleSpec.query
          (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= k)
        rw [mem_support_bind_iff]
        exact ⟨inbox, by simp; exact Set.mem_univ _, ha⟩))

theorem Clocked.timed_party_bind {lab : ℕ → ℕ} {j m : ℕ} {keys : Set HashOutput}
    {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β}
    (timed : TreeSimCheckTimed m p.run) (h : Clocked lab j keys p.run)
    (rest : ∀ a, some a ∈ support p.run → Clocked lab (j + m) ∅ (f a).run) :
    Clocked lab j keys (p >>= f).run := by
  simp only [OptionT.run_bind, Option.elimM]
  exact Clocked.timed_bind timed h _ rfl rest

theorem ClockLocal.lower {lab : ℕ → ℕ} {j : ℕ} {keys : Set HashOutput}
    {q : (LocalSpec C).Domain} (h : ClockLocal lab j keys q) : ¬ CoinBelow (lab j) q := by
  rcases q with noise | (q | prg)
  · simp [CoinBelow]
  · cases q <;> simp only [ClockLocal, CoinBelow] at h ⊢
    all_goals first | trivial | omega
  · simp [CoinBelow]

theorem ClockLocal.disc {lab : ℕ → ℕ} {j limit : ℕ} {keys : Set HashOutput}
    {q : (LocalSpec C).Domain} (h : ClockLocal lab j keys q) (le : lab (j + 1) ≤ limit) :
    LocalDisc limit keys q := by
  rcases q with noise | (q | prg)
  · trivial
  · cases q <;> simp only [ClockLocal, LocalDisc] at h ⊢
    all_goals first | trivial | exact h | omega
  · trivial

theorem Clocked.floor {lab : ℕ → ℕ} (mono : Monotone lab) {j : ℕ} {keys : Set HashOutput}
    {P : OracleComp (PartySpec C E RealSpec) (Option α)} (h : Clocked lab j keys P) :
    CheckFloor (lab j) P := by
  induction h with
  | pure => exact .pure _ _
  | queryLocal j keys q k query rest ih =>
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query
      (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= k) _ 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl query.lower, fun r => by simpa [CheckFloor] using ih r⟩
  | round j keys out k rest ih =>
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query
      (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= k) _ 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [PartyQuery]), fun r => by
      simpa [CheckFloor, PartyQuery] using (ih r).mono (mono (Nat.le_succ j))⟩

-- Port of CheckDisc.timed_bind, cutting before the timed prefix returns.
theorem Clocked.checkDisc_bind {lab : ℕ → ℕ} (mono : Monotone lab)
    {j X : ℕ} {keys : Set HashOutput} {oa : OracleComp (PartySpec C E RealSpec) (Option β)}
    (timed : TreeSimCheckTimed X oa) (h : Clocked lab j keys oa)
    (f : Option β → OracleComp (PartySpec C E RealSpec) (Option α))
    (abort : f none = Pure.pure none) (n : ℕ) (le : n ≤ X) :
    CheckDisc (lab (j + n)) n keys (oa >>= f) := by
  induction timed generalizing j keys n with
  | abort X => rw [pure_bind, abort]; exact .pure _ _ _
  | done a =>
    have : n = 0 := by omega
    subst n
    exact .zero _ _
  | queryLocal X q k hk ih =>
    cases n with
    | zero => exact .zero _ _
    | succ n =>
      exact .queryLocal _ _ _ _ (h.local_inv.1.disc (mono (by omega)))
        (fun r => ih r (h.local_inv.2 r) (n + 1) le)
  | round X out k hk ih =>
    cases n with
    | zero => exact .zero _ _
    | succ n =>
      refine .round _ _ _ _ fun r => ?_
      change CheckDisc (lab (j + (n + 1))) n ∅ (k r >>= f)
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih r (h.round_inv r) n (by omega)

theorem Clocked.floor_bind {lab : ℕ → ℕ} (mono : Monotone lab)
    {j X : ℕ} {keys : Set HashOutput} {oa : OracleComp (PartySpec C E RealSpec) (Option β)}
    (timed : TreeSimCheckTimed X oa) (h : Clocked lab j keys oa)
    (f : Option β → OracleComp (PartySpec C E RealSpec) (Option α))
    (abort : f none = Pure.pure none)
    (rest : ∀ a, some a ∈ support oa → CheckFloor (lab (j + X)) (f (some a)))
    (n : ℕ) (le : n ≤ X) {Q : OracleComp (PartySpec C E RealSpec) (Option α)}
    (run : Residual n (oa >>= f) Q) : CheckFloor (lab (j + n)) Q := by
  induction timed generalizing j keys n with
  | abort X =>
    rw [pure_bind, abort] at run
    rw [run.pure_inv]
    exact .pure _ _
  | done a =>
    have : n = 0 := by omega
    subst n
    rw [run.zero_inv, pure_bind]
    exact rest a (by simp)
  | queryLocal X q k hk ih =>
    by_cases zero : n = 0
    · subst n
      rw [run.zero_inv, Nat.add_zero]
      apply (h.floor mono).bind f
      intro a ha
      cases a with
      | none => rw [abort]; exact .pure _ _
      | some a => exact (rest a ha).mono (mono (by omega))
    · rcases run.local_inv with hz | ⟨r, hr⟩
      · exact (zero hz).elim
      apply ih r (h.local_inv.2 r) _ n le hr
      intro a ha
      apply rest a
      change some a ∈ support (OracleComp.lift (OracleSpec.query
        (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= k)
      rw [mem_support_bind_iff]
      exact ⟨r, by simp; exact Set.mem_univ _, ha⟩
  | round X out k hk ih =>
    by_cases zero : n = 0
    · subst n
      rw [run.zero_inv, Nat.add_zero]
      apply (h.floor mono).bind f
      intro a ha
      cases a with
      | none => rw [abort]; exact .pure _ _
      | some a => exact (rest a ha).mono (mono (by omega))
    · rcases run.round_inv with hz | ⟨n', inbox, count, hr⟩
      · exact (zero hz).elim
      subst n
      rw [show j + (n' + 1) = j + 1 + n' by omega]
      apply ih inbox (h.round_inv inbox) _ n' (by omega) hr
      intro a ha
      have mem : some a ∈ support (OracleComp.lift (OracleSpec.query
          (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= k) := by
        rw [mem_support_bind_iff]
        exact ⟨inbox, by simp; exact Set.mem_univ _, ha⟩
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rest a mem

set_option backward.isDefEq.respectTransparency false in
-- Port of CheckDisc.exchange_bind, retaining the segment index.
theorem Clocked.exchange_bind [Field E] [Algebra Bit E]
    (lab : ℕ → ℕ) (j : ℕ) (keys : Set HashOutput) (out : Mail C E)
    (k : Mail C E → PartyM C E RealSpec α)
    (hk : ∀ inbox, Clocked lab (j + 1) ∅ (k inbox).run) :
    Clocked lab j keys (exchange out >>= k).run := by
  have he : (exchange out >>= k).run =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>=
        exchangeResume k := by
    simp only [exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk,
      pure_bind, Option.elimM]
    apply bind_congr
    intro inbox
    simp only [Option.elim]
    unfold exchangeResume
    split <;> simp_all
  rw [he]
  apply Clocked.round
  intro inbox
  change Clocked lab (j + 1) ∅ (exchangeResume k inbox)
  unfold exchangeResume
  split_ifs
  · exact .pure _ _ _
  · simpa only [OptionT.run_pure, pure_bind, Option.elim_some] using hk inbox

-- Port of CheckDisc.oracle_bind. A local oracle computation preserves keys.
theorem Clocked.oracle_bind [Field E] [Algebra Bit E] {lab : ℕ → ℕ} {j : ℕ} {keys : Set HashOutput}
    (p : OracleComp (RoSpec C) α)
    (quiet : IsQueryBoundP p (fun q => ¬ ClockLocal lab j keys (.inr q)) 0)
    (f : α → PartyM C E RealSpec β)
    (rest : ∀ a, Clocked lab j keys (f a).run) : Clocked lab j keys (oracleStep p >>= f).run := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa only [oracleStep_pure, pure_bind] using rest a
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at quiet
    have allowed : ClockLocal lab j keys (.inr q) := by simpa using quiet.1
    have tail : ∀ r, IsQueryBoundP (k r) (fun q => ¬ ClockLocal lab j keys (.inr q)) 0 := by
      simpa using quiet.2
    rw [oracleStep_bind, bind_assoc]
    rcases q with q | q
    all_goals exact .queryLocal _ _ _ _ allowed (fun r =>
      (ih r (tail r)).mono_keys (localKeys_subset _ _ _))

section RealCheck
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

theorem hash_clocked_allowed (lab : ℕ → ℕ) (j : ℕ) (keys : Set HashOutput)
    (q : Query C) (hq : ClockLocal lab j keys (.inr (.inl q))) :
    IsQueryBoundP (hashQuery q) (fun t => ¬ ClockLocal lab j keys (.inr t)) 0 := by
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl q))) _ 0
  rw [isQueryBoundP_query_iff]
  exact fun h => (h hq).elim

-- Port of TreeCheckHonestDisc.findChallenge_allowed.
theorem findChallenge_clocked (lab : ℕ → ℕ) (j : ℕ) (keys : Set HashOutput)
    (key : HashOutput) (mem : key ∈ keys) (tries index : ℕ) :
    IsQueryBoundP (findChallenge K key tries index) (fun t => ¬ ClockLocal lab j keys (.inr t)) 0 := by
  induction tries generalizing index with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ tries ih =>
    unfold findChallenge
    refine isQueryBoundP_bind (n := 0) (m := 0)
      (hash_clocked_allowed lab j keys _ mem) (fun h _ => ?_)
    dsimp only
    split
    · exact isQueryBoundP_pure _ _ _
    · exact ih _

theorem expand_clocked (lab : ℕ → ℕ) (j : ℕ) (keys : Set HashOutput)
    (key : HashOutput) (mem : key ∈ keys) (count : ℕ) :
    IsQueryBoundP ((List.range count).mapM fun k => elementOfHash K <$> hashQuery (C := C) (.expand key k))
      (fun t => ¬ ClockLocal lab j keys (.inr t)) 0 := by
  simpa using queryBound_mapM (fun t => ¬ ClockLocal lab j keys (.inr t))
    (fun k => elementOfHash K <$> hashQuery (C := C) (.expand key k)) 0 (List.range count)
    (fun k _ => (isQueryBoundP_map_iff _ _ _).mpr (hash_clocked_allowed lab j keys _ mem))

theorem clocked_require_bind (lab : ℕ → ℕ) (j : ℕ) (keys : Set HashOutput)
    (p : Prop) (f : Unit → PartyM C E RealSpec α)
    (rest : ∀ u, Clocked lab j keys (f u).run) : Clocked lab j keys (require p >>= f).run := by
  unfold require
  split_ifs
  · simpa using rest ()
  · exact .pure _ _ _

theorem clocked_coinKey_bind (ctx : Context C) (st : RunState C) (lab : ℕ → ℕ)
    (j : ℕ) (keys : Set HashOutput) (lo : lab (j + 1) ≤ st.label)
    (hi : st.label < lab (j + 2)) (f : HashOutput → RunM C E RealSpec α)
    (rest : ∀ key mid, mid.label = st.label + 1 →
      Clocked lab (j + 1) {key} ((f key).run mid).run) :
    Clocked lab j keys ((coinKey K (realCheckGadgets (G := RealSpec) K ctx) >>= f).run st).run := by
  simp only [coinKey, StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  apply Clocked.timed_party_bind (treeLockstep_timed_coin K ctx 1 st)
    (Clocked.of_quiet ((TreeCheckHonestDisc.gadgets_zero K ctx).coin 1 st))
  rintro ⟨values, mid⟩ hmem
  change Clocked lab (j + 1) ∅ (.roll
    (.inl (.inl (.inr (.inl (.coinKey st.tag st.label
      (values.flatMap fun v => List.ofFn (K.encode v)))))))
    (fun key => ((f key).run mid).run))
  refine .queryLocal _ _ _ _ ⟨lo, ?_⟩ fun key => ?_
  · simpa only [Nat.add_assoc] using hi
  · simpa [localKeys] using rest key mid (lockstepLabels_coin K ctx 1 st values mid hmem)

theorem clocked_challenge_bind (ctx : Context C) (st : RunState C) (lab : ℕ → ℕ)
    (j : ℕ) (keys : Set HashOutput) (lo : lab (j + 1) ≤ st.label)
    (hi : st.label < lab (j + 2)) (f : E → RunM C E RealSpec α)
    (rest : ∀ r mid, mid.label = st.label + 1 →
      Clocked lab (j + 1) ∅ ((f r).run mid).run) :
    Clocked lab j keys ((challenge K (realCheckGadgets (G := RealSpec) K ctx) >>= f).run st).run := by
  unfold challenge
  simp only [bind_assoc]
  apply clocked_coinKey_bind K ctx st lab j keys lo hi
  intro key mid label
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply Clocked.oracle_bind _ (findChallenge_clocked K lab (j + 1) {key} key (by simp) _ _)
  intro result
  cases result with
  | none => exact .pure _ _ _
  | some r => exact (rest r mid label).mono_keys (Set.empty_subset _)

theorem clocked_slice_bind (ctx : Context C) (τ : List E) (count : ℕ)
    (v : Shares C E × Shares C E × E) (t : ℕ) (st : RunState C)
    (lab : ℕ → ℕ) (j : ℕ) (keys : Set HashOutput)
    (lo : lab (j + 2) ≤ st.label + 1) (hi : st.label + 1 < lab (j + 3))
    (f : (Shares C E × Shares C E × E) → RunM C E RealSpec α)
    (rest : ∀ v mid, mid.label = st.label + 2 → Clocked lab (j + 2) ∅ ((f v).run mid).run) :
    Clocked lab j keys ((sliceStep K ctx (realCheckGadgets (G := RealSpec) K ctx) τ count v t >>= f).run st).run := by
  rcases v with ⟨xs, ys, d⟩
  unfold sliceStep
  simp only [bind_assoc, pure_bind]
  rw [StateT.run_bind]
  apply Clocked.timed_party_bind (treeLockstep_timed_extendMult K ctx _ st)
    (Clocked.of_quiet ((TreeCheckHonestDisc.gadgets_zero K ctx).mult _ st))
  rintro ⟨values, mid⟩ hv
  have label := lockstepLabels_extendMult K ctx _ st values mid hv
  change Clocked lab (j + 1) ∅ ((challenge K (realCheckGadgets (G := RealSpec) K ctx) >>= _).run mid).run
  apply clocked_challenge_bind K ctx mid lab (j + 1) ∅
    (by simpa only [label, Nat.add_assoc] using lo)
    (by simpa only [label, Nat.add_assoc] using hi)
  intro r final hfinal
  simpa only [Nat.add_assoc] using rest _ final (by omega)

theorem clocked_halving_bind (ctx : Context C) (width : ℕ)
    (v : (ℕ → E) × (ℕ → E) × E) (t : ℕ) (st : RunState C)
    (lab : ℕ → ℕ) (j : ℕ) (keys : Set HashOutput)
    (lo : lab (j + 2) ≤ st.label + 1) (hi : st.label + 1 < lab (j + 3))
    (f : ((ℕ → E) × (ℕ → E) × E) → RunM C E RealSpec α)
    (rest : ∀ v mid, mid.label = st.label + 2 → Clocked lab (j + 2) ∅ ((f v).run mid).run) :
    Clocked lab j keys ((halvingStep K ctx (realCheckGadgets (G := RealSpec) K ctx) width v t >>= f).run st).run := by
  rcases v with ⟨xs, ys, d⟩
  unfold halvingStep
  simp only [bind_assoc, pure_bind]
  rw [StateT.run_bind]
  apply Clocked.timed_party_bind (treeLockstep_timed_extendMult K ctx _ st)
    (Clocked.of_quiet ((TreeCheckHonestDisc.gadgets_zero K ctx).mult _ st))
  rintro ⟨values, mid⟩ hv
  have label := lockstepLabels_extendMult K ctx _ st values mid hv
  change Clocked lab (j + 1) ∅ ((challenge K (realCheckGadgets (G := RealSpec) K ctx) >>= _).run mid).run
  apply clocked_challenge_bind K ctx mid lab (j + 1) ∅
    (by simpa only [label, Nat.add_assoc] using lo)
    (by simpa only [label, Nat.add_assoc] using hi)
  intro r final hfinal
  simpa only [Nat.add_assoc] using rest _ final (by omega)

-- Port of TreeLockstepOpenedRest.openedRest_timed_fold (private), keeping
-- the exchange offset and the successful label increment at each step.
theorem clocked_fold {δ : Type} (f : α → δ → RunM C E RealSpec α)
    (xs : List δ) (lab : ℕ → ℕ) (j L : ℕ)
    (step : ∀ t, t < xs.length → ∀ a b st keys (k : α → RunM C E RealSpec β),
      st.label = L + 2 * t →
      (∀ v mid, mid.label = L + 2 * (t + 1) →
        Clocked lab (j + 2 * (t + 1)) ∅ ((k v).run mid).run) →
      Clocked lab (j + 2 * t) keys ((f a b >>= k).run st).run)
    (a : α) (st : RunState C) (label : st.label = L) (keys : Set HashOutput)
    (k : α → RunM C E RealSpec β)
    (rest : ∀ v mid, mid.label = L + 2 * xs.length →
      Clocked lab (j + 2 * xs.length) ∅ ((k v).run mid).run) :
    Clocked lab j keys ((xs.foldlM f a >>= k).run st).run := by
  induction xs generalizing a st j L keys with
  | nil =>
    simpa using (rest a st (by simpa using label)).mono_keys (Set.empty_subset keys)
  | cons b xs ih =>
    rw [List.foldlM_cons, bind_assoc]
    have first := step 0 (by simp) a b st keys
      (fun v => xs.foldlM f v >>= k) (by simpa using label)
    simp only [Nat.mul_zero, Nat.add_zero] at first
    apply first
    intro v mid hmid
    apply ih (j := j + 2) (L := L + 2)
    · intro t ht a b st keys k hst hk
      have h := step (t + 1) (by simp only [List.length_cons]; omega) a b st keys k
        (by omega) (fun v mid hmid => by
          convert hk v mid (by omega) using 1; omega)
      convert h using 1; omega
    · simpa using hmid
    · intro v final hfinal
      convert rest v final (by simp only [List.length_cons]; omega) using 1; simp only [List.length_cons]; omega

-- The same mapM bounds as TreeCheckHonestDisc.prss_zero, on its oracle part.
theorem prssDraw_quiet {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R)
    (draw : ∀ name key label idx count, IsQueryBoundP (codec.draw name key label idx count)
      (fun t => CheckQuery (C := C) (.inr t)) 0) (label idx count : ℕ) :
    IsQueryBoundP (prssDraw ctx codec label idx count) (fun t => CheckQuery (.inr t)) 0 := by
  unfold prssDraw termDraws pairDraws
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => ?_)
  · simpa using queryBound_mapM (fun t => CheckQuery (C := C) (.inr t))
      (fun T => if ctx.self ∈ C.holders T then codec.draw (.term T) (ctx.prss.term T) label idx count
        else pure fun _ => 0) 0 C.terms (fun T _ => by
          split_ifs
          · exact draw _ _ _ _ _
          · exact isQueryBoundP_pure _ _ _)
  · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
    simpa using queryBound_mapM (fun t => CheckQuery (C := C) (.inr t))
      (fun h => if eq : h = ctx.self then pure fun _ => 0
        else codec.draw (.pair (C.pairOf ctx.self h (Ne.symm eq))) (ctx.prss.pair h) label idx count)
      0 C.parties (fun h _ => by
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · exact draw _ _ _ _ _)

theorem clocked_prss_bind {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R)
    (draw : ∀ name key label idx count, IsQueryBoundP (codec.draw name key label idx count)
      (fun t => CheckQuery (C := C) (.inr t)) 0) (idx count : ℕ)
    (st : RunState C) (lab : ℕ → ℕ) (j : ℕ) (keys : Set HashOutput)
    (f : PrssOutput C R → RunM C E RealSpec α)
    (rest : ∀ r, Clocked lab j keys ((f r).run (nextLabel st)).run) :
    Clocked lab j keys ((prssRandomness ctx codec idx count >>= f).run st).run := by
  rw [prssRandomness_run]
  apply Clocked.oracle_bind _ _ _ rest
  exact IsQueryBoundP.of_imp (fun q hn => by
    by_contra hq
    exact hn (quiet_clock hq)) (prssDraw_quiet ctx codec draw _ _ _)

theorem element_draw_quiet (name : KeyName C) (key : HashOutput) (label idx count : ℕ) :
    IsQueryBoundP ((elementCodec K).draw name key label idx count)
      (fun t => CheckQuery (C := C) (.inr t)) 0 := by
  unfold elementCodec
  exact isQueryBoundP_bind (TreeCheckHonestDisc.prg_zero name key label idx _)
    (fun _ _ => isQueryBoundP_pure _ _ 0)

theorem clocked_final (ctx : Context C) (v : (ℕ → E) × (ℕ → E) × E)
    (st : RunState C) (lab : ℕ → ℕ) (j : ℕ) (keys : Set HashOutput)
    (lo : lab (j + 3) ≤ st.label + 3) (hi : st.label + 3 < lab (j + 4)) :
    Clocked lab j keys ((finalStep K ctx (realCheckGadgets (G := RealSpec) K ctx) v).run st).run := by
  rcases v with ⟨xs, ys, d⟩
  unfold finalStep
  apply clocked_prss_bind ctx (elementCodec K) (element_draw_quiet K) 1 2 st lab j keys
  intro w
  rw [StateT.run_bind]
  apply Clocked.timed_party_bind (treeLockstep_timed_extendMult K ctx _ (nextLabel st))
    (Clocked.of_quiet ((TreeCheckHonestDisc.gadgets_zero K ctx).mult _ (nextLabel st)))
  rintro ⟨q, mid⟩ hq
  have label := lockstepLabels_extendMult K ctx _ (nextLabel st) q mid hq
  apply clocked_prss_bind ctx bitCodec TreeCheckHonestDisc.prg_zero 2 256 mid lab (j + 1) ∅
  intro salts
  rw [StateT.run_bind]
  apply Clocked.timed_party_bind (treeLockstep_timed_digest ctx salts.1 (nextLabel mid))
    (Clocked.of_quiet (compare_quiet ctx salts.1 (nextLabel mid)))
  rintro ⟨u, after⟩ hd
  have ld := lockstepLabels_compareDigests ctx salts.1 (nextLabel mid) u after hd
  have afterLabel : after.label = st.label + 3 := by
    simp only [nextLabel] at label ld
    omega
  apply clocked_challenge_bind K ctx after lab (j + 1 + 1) ∅
    (by simpa only [afterLabel, Nat.add_assoc] using lo)
    (by simpa only [afterLabel, Nat.add_assoc] using hi)
  intro r final _
  apply Clocked.of_quiet
  exact (RunBudget.lift (party_quiet_of_zero (RunBound.openSh K ctx _ 3))).bind_zero
    (fun _ => RunBudget.lift (party_quiet_of_zero (PartyBound.require _))) final

/-- A segment cutoff for coin queries, rather than the in-flight state label. -/
def checkClock (count i : ℕ) : ℕ :=
  if count = 0 then 0 else
    if i ≤ 2 * halvings count + 1 then 2 * (i / 2)
    else if i ≤ 2 * halvings count + 4 then 2 * halvings count + 4
    else 2 * halvings count + 5

theorem checkClock_zero (count : ℕ) : checkClock count 0 = 0 := by
  simp [checkClock]

theorem checkClock_mono (count : ℕ) : Monotone (checkClock count) := by
  intro i j le
  unfold checkClock
  split_ifs <;> omega

theorem checkClock_end (count : ℕ) : checkClock count (checkLabels count) = checkLabels count := by
  unfold checkClock checkLabels
  split_ifs <;> omega

theorem checkClock_le (count i : ℕ) : checkClock count i ≤ checkLabels count := by
  unfold checkClock checkLabels
  split_ifs <;> omega

theorem checkClock_first (count : ℕ) (nonzero : count ≠ 0) :
    checkClock count 1 = 0 ∧ 0 < checkClock count 2 := by
  unfold checkClock
  split_ifs <;> omega

theorem checkClock_loop (count t : ℕ) (nonzero : count ≠ 0) (lt : t < halvings count) :
    checkClock count (3 + 2 * t) ≤ 2 + 2 * t ∧
      2 + 2 * t < checkClock count (4 + 2 * t) := by
  unfold checkClock
  split_ifs <;> omega

theorem checkClock_final (count : ℕ) (nonzero : count ≠ 0) :
    checkClock count (2 * halvings count + 4) = 2 * halvings count + 4 ∧
    checkClock count (2 * halvings count + 5) = 2 * halvings count + 5 := by
  unfold checkClock
  split_ifs <;> omega

set_option maxHeartbeats 1000000 in
/-- The real check follows the delayed segment clock on every answer path. -/
theorem clocked_check (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C) :
    Clocked (fun i => st.label + checkClock (tuples.map (·.count)).sum i) 0 ∅
      ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st).run := by
  by_cases zero : (tuples.map (·.count)).sum = 0
  · simp only [check, zero, if_true]
    exact .pure _ _ _
  · set count := (tuples.map (·.count)).sum
    set lab := fun i => st.label + checkClock count i
    have hs : sliceBits ≤ halvings count := by unfold halvings; omega
    have first := checkClock_first count zero
    rw [check_eq K ctx _ tuples zero]
    rw [show (tuples.map (·.count)).sum = count from rfl]
    apply clocked_coinKey_bind K ctx st lab 0 ∅
      (by simp only [lab, Nat.zero_add, first.1, Nat.add_zero]; exact le_rfl)
      (by dsimp only [lab]; simp only [Nat.zero_add]; omega)
    intro key mid hmid
    rw [StateT.run_bind]
    simp only [expand, StateT.run_lift, bind_assoc, pure_bind]
    apply Clocked.oracle_bind _ (expand_clocked K lab 1 {key} key (by simp) _)
    intro τ
    rw [StateT.run_bind]
    simp only [StateT.run_lift, bind_assoc, pure_bind]
    apply clocked_require_bind lab 1 {key}
    intro _
    apply clocked_fold (j := 1) (L := st.label + 1)
    · intro t ht v b ss keys k hss hk
      simp only [List.length_range] at ht
      have bounds := checkClock_loop count t zero (by omega)
      apply clocked_slice_bind K ctx τ count v b ss lab (1 + 2 * t) keys
        (by dsimp only [lab]; rw [show 1 + 2 * t + 2 = 3 + 2 * t by omega]; omega)
        (by dsimp only [lab]; rw [show 1 + 2 * t + 3 = 4 + 2 * t by omega]; omega)
      intro v final hfinal
      convert hk v final (by omega) using 1; omega
    · exact hmid
    · intro v mid' hmid'
      simp only [List.length_range] at hmid' ⊢
      apply clocked_fold (j := 1 + 2 * sliceBits) (L := st.label + 1 + 2 * sliceBits)
      · intro t ht v b ss keys k hss hk
        simp only [List.length_range] at ht
        have bounds := checkClock_loop count (sliceBits + t) zero (by omega)
        apply clocked_halving_bind K ctx (sliceWidth count) v b ss lab (1 + 2 * sliceBits + 2 * t) keys
          (by dsimp only [lab]; rw [show 1 + 2 * sliceBits + 2 * t + 2 = 3 + 2 * (sliceBits + t) by omega]; omega)
          (by dsimp only [lab]; rw [show 1 + 2 * sliceBits + 2 * t + 3 = 4 + 2 * (sliceBits + t) by omega]; omega)
        intro v final hfinal
        convert hk v final (by omega) using 1; omega
      · exact hmid'
      · intro v final hfinal
        simp only [List.length_range] at hfinal ⊢
        have bounds := checkClock_final count zero
        apply clocked_final K ctx v final lab (1 + 2 * sliceBits + 2 * (halvings count - sliceBits)) ∅
          (by dsimp only [lab]; rw [show 1 + 2 * sliceBits + 2 * (halvings count - sliceBits) + 3 = 2 * halvings count + 4 by omega, bounds.1]; omega)
          (by dsimp only [lab]; rw [show 1 + 2 * sliceBits + 2 * (halvings count - sliceBits) + 4 = 2 * halvings count + 5 by omega, bounds.2]; omega)

/-- Past discipline and every residual's future floor at an arbitrary check cut. -/
theorem check_clock (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C)
    (k : Unit × RunState C → PartyM C E RealSpec α)
    (rest : ∀ a, some a ∈ support ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st).run →
      CheckFloor (st.label + checkLabels (tuples.map (·.count)).sum) (k a).run)
    (n : ℕ) (le : n ≤ checkLabels (tuples.map (·.count)).sum) :
    CheckDisc (st.label + checkClock (tuples.map (·.count)).sum n) n ∅
      ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st >>= k).run ∧
    ∀ Q, Residual n ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st >>= k).run Q →
      CheckFloor (st.label + checkClock (tuples.map (·.count)).sum n) Q := by
  have mono : Monotone (fun i => st.label + checkClock (tuples.map (·.count)).sum i) :=
    fun _ _ le => Nat.add_le_add_left (checkClock_mono _ le) _
  have timed := check_timed K ctx tuples st
  have clock := clocked_check K ctx tuples st
  simp only [OptionT.run_bind, Option.elimM]
  refine ⟨?_, ?_⟩
  · simpa only [Nat.zero_add] using Clocked.checkDisc_bind mono timed clock
      (fun a => a.elim (pure none) (fun a => (k a).run)) rfl n le
  · intro Q run
    simpa only [Nat.zero_add] using Clocked.floor_bind mono timed clock
      (fun a => a.elim (pure none) (fun a => (k a).run)) rfl
      (fun a ha => by simpa only [Nat.zero_add, checkClock_end, Option.elim_some] using rest a ha) n le run

/-- The local check itself, with a pure continuation. -/
theorem check_clock_self (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C)
    (n : ℕ) (le : n ≤ checkLabels (tuples.map (·.count)).sum) :
    CheckDisc (st.label + checkClock (tuples.map (·.count)).sum n) n ∅
      ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st).run ∧
    ∀ Q, Residual n ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st).run Q →
      CheckFloor (st.label + checkClock (tuples.map (·.count)).sum n) Q := by
  simpa only [bind_pure] using check_clock K ctx tuples st pure (fun _ _ => .pure _ _) n le

end RealCheck
end TreeCheckCoinClock
end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinClock.CheckFloor.residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinClock.CheckFloor.residual

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinClock.Clocked.timed_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinClock.Clocked.timed_bind

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinClock.Clocked.checkDisc_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinClock.Clocked.checkDisc_bind

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinClock.Clocked.floor_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinClock.Clocked.floor_bind

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinClock.clocked_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinClock.clocked_check

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinClock.check_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinClock.check_clock

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckCoinClock.check_clock_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckCoinClock.check_clock_self
