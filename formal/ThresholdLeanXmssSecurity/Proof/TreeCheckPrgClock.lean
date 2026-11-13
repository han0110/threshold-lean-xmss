import ThresholdLeanXmssSecurity.Proof.TreeCheckPrgDisc
import ThresholdLeanXmssSecurity.Proof.TreeLockstepOpenedRest
import XmssSecurity.Proof.QueryBoundSupport
import XmssSecurity.Proof.EncodingQueryAccounting

/-! # Exchange-indexed PRG labels

The clock bounds every real PRG query inside its local segment. A floor
excludes reads below a cutoff; the past discipline excludes reads above it.
PRSS advances the state label without advancing the exchange segment.
Structural proofs port TreeCheckCoinClock with its coin-key set removed.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckPrgClock
open TreeCheckPrgDisc TreeCheckPrgWindow TreeCheckWalkState TreeSimHashCount
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E α β : Type}

def PrgBelow (limit : ℕ) : (LocalSpec C).Domain → Prop
  | .inr (.inr x) => x.2.2.1 < limit
  | _ => False

def PrgFloor (limit : ℕ) (P : OracleComp (PartySpec C E RealSpec) (Option α)) : Prop :=
  IsQueryBoundP P (PartyQuery (E := E) (G := RealSpec) (PrgBelow limit)) 0

theorem PrgFloor.pure (limit : ℕ) (a : Option α) :
    PrgFloor (C := C) (E := E) limit (Pure.pure a) := isQueryBoundP_pure _ _ _

theorem PrgFloor.mono {l l' : ℕ} {P : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : PrgFloor l P) (le : l' ≤ l) : PrgFloor l' P := by
  apply IsQueryBoundP.of_imp (fun q hq => ?_) h
  rcases q with (q | out) | impossible
  · rcases q with noise | (hash | prg)
    · exact hq.elim
    · exact hq.elim
    · exact lt_of_lt_of_le hq le
  · exact hq.elim
  · exact impossible.elim

theorem PrgFloor.bind {l : ℕ} {P : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : PrgFloor l P) (f : Option α → OracleComp (PartySpec C E RealSpec) (Option β))
    (rest : ∀ a, a ∈ support P → PrgFloor l (f a)) : PrgFloor l (P >>= f) :=
  isQueryBoundP_bind h rest

theorem PrgFloor.party_bind {l : ℕ} {p : PartyM C E RealSpec α}
    {f : α → PartyM C E RealSpec β} (h : PrgFloor l p.run)
    (rest : ∀ a, some a ∈ support p.run → PrgFloor l (f a).run) :
    PrgFloor l (p >>= f).run := by
  simp only [OptionT.run_bind, Option.elimM]
  apply h.bind
  intro a ha
  cases a with
  | none => exact .pure _ _
  | some a => exact rest a ha

theorem PrgFloor.residual {l n : ℕ}
    {P Q : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : PrgFloor l P) (r : Residual n P Q) : PrgFloor l Q := by
  induction r with
  | refl => exact h
  | queryLocal n q k answer Q r ih =>
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= k) _ 0 at h
    rw [isQueryBoundP_query_bind_iff] at h
    exact ih (by simpa [PrgFloor] using h.2 answer)
  | round n out k inbox Q r ih =>
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= k) _ 0 at h
    rw [isQueryBoundP_query_bind_iff] at h
    exact ih (by simpa [PrgFloor] using h.2 inbox)
  | done => exact .pure _ _

theorem PrgFloor.of_noPrg {l : ℕ} {p : PartyM C E RealSpec α}
    (h : PartyBudget (PrgFrom 0) p 0) : PrgFloor l p.run := by
  apply IsQueryBoundP.of_imp (fun q hq => ?_) h
  rcases q with (q | out) | impossible
  · rcases q with noise | (hash | prg)
    · exact hq.elim
    · exact hq.elim
    · exact Nat.zero_le _
  · exact hq.elim
  · exact impossible.elim

def PrgClockLocal (lab : ℕ → ℕ) (j : ℕ) : (LocalSpec C).Domain → Prop
  | .inr (.inr x) => lab j ≤ x.2.2.1 ∧ x.2.2.1 < lab (j + 1)
  | _ => True

inductive PrgClocked (lab : ℕ → ℕ) : ℕ →
    OracleComp (PartySpec C E RealSpec) (Option α) → Prop
  | pure (j a) : PrgClocked lab j (pure a)
  | queryLocal (j q k) (query : PrgClockLocal lab j q)
      (rest : ∀ r, PrgClocked lab j (k r)) :
      PrgClocked lab j (.roll (.inl (.inl q)) k)
  | round (j out k) (rest : ∀ inbox, PrgClocked lab (j + 1) (k inbox)) :
      PrgClocked lab j (.roll (.inl (.inr out)) k)

theorem PrgClocked.local_inv {lab : ℕ → ℕ} {j : ℕ}
    {q : (LocalSpec C).Domain} {k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : PrgClocked lab j (.roll (.inl (.inl q)) k)) :
    PrgClockLocal lab j q ∧ ∀ r, PrgClocked lab j (k r) := by
  cases h with | queryLocal _ _ _ query rest => exact ⟨query, rest⟩

theorem PrgClocked.round_inv {lab : ℕ → ℕ} {j : ℕ}
    {out : Mail C E} {k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : PrgClocked lab j (.roll (.inl (.inr out)) k)) :
    ∀ inbox, PrgClocked lab (j + 1) (k inbox) := by
  cases h with | round _ _ _ rest => exact rest

theorem quiet_clock {lab : ℕ → ℕ} {j : ℕ}
    {q : (LocalSpec C).Domain} (h : ¬ PrgFrom 0 q) : PrgClockLocal lab j q := by
  rcases q with noise | (hash | prg)
  · trivial
  · trivial
  · exact (h (Nat.zero_le _)).elim

-- Port of TreeCheckHonestDisc.Disc.of_quiet, with the segment index retained.
theorem PrgClocked.of_noPrg {lab : ℕ → ℕ} {j : ℕ}
    {p : PartyM C E RealSpec α} (h : PartyBudget (PrgFrom 0) p 0) : PrgClocked lab j p.run := by
  unfold PartyBudget at h
  generalize p.run = P at h ⊢
  induction P generalizing j with
  | pure a => exact .pure _ _
  | queryBind t k ih =>
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query t) >>= k) _ 0 at h
    rw [isQueryBoundP_query_bind_iff] at h
    have noQuery : ¬ PartyQuery (PrgFrom 0) t := by simpa using h.1
    have tail : ∀ r, IsQueryBoundP (k r) (PartyQuery (E := E) (G := RealSpec) (PrgFrom 0)) 0 := by
      simpa using h.2
    rcases t with (q | out) | impossible
    · exact .queryLocal _ _ _ (quiet_clock noQuery) (fun r => ih r (tail r))
    · exact .round _ _ _ (fun r => ih r (tail r))
    · exact impossible.elim

-- Port of TreeCheckCoinClock.Clocked.timed_bind.
theorem PrgClocked.timed_bind {lab : ℕ → ℕ} {j m : ℕ}
    {oa : OracleComp (PartySpec C E RealSpec) (Option β)}
    (timed : TreeSimCheckTimed m oa) (h : PrgClocked lab j oa)
    (f : Option β → OracleComp (PartySpec C E RealSpec) (Option α))
    (abort : f none = Pure.pure none)
    (rest : ∀ a, some a ∈ support oa → PrgClocked lab (j + m) (f (some a))) :
    PrgClocked lab j (oa >>= f) := by
  induction timed generalizing j with
  | abort m => rw [pure_bind, abort]; exact .pure _ _
  | done a =>
    rw [pure_bind]
    exact rest a (by simp)
  | queryLocal m q k hk ih =>
    refine .queryLocal _ _ _ h.local_inv.1 fun r => ?_
    apply ih r (h.local_inv.2 r)
    intro a ha
    apply rest a
    change some a ∈ support (OracleComp.lift (OracleSpec.query
      (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= k)
    rw [mem_support_bind_iff]
    exact ⟨r, by simp; exact Set.mem_univ _, ha⟩
  | round m out k hk ih =>
    refine .round _ _ _ fun inbox => ?_
    apply ih inbox (h.round_inv inbox)
    intro a ha
    apply (show PrgClocked lab (j + 1 + m) (f (some a)) from by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rest a (by
        change some a ∈ support (OracleComp.lift (OracleSpec.query
          (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= k)
        rw [mem_support_bind_iff]
        exact ⟨inbox, by simp; exact Set.mem_univ _, ha⟩))

theorem PrgClocked.timed_party_bind {lab : ℕ → ℕ} {j m : ℕ}
    {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β}
    (timed : TreeSimCheckTimed m p.run) (h : PrgClocked lab j p.run)
    (rest : ∀ a, some a ∈ support p.run → PrgClocked lab (j + m) (f a).run) :
    PrgClocked lab j (p >>= f).run := by
  simp only [OptionT.run_bind, Option.elimM]
  exact PrgClocked.timed_bind timed h _ rfl rest

theorem PrgClockLocal.lower {lab : ℕ → ℕ} {j : ℕ}
    {q : (LocalSpec C).Domain} (h : PrgClockLocal lab j q) : ¬ PrgBelow (lab j) q := by
  rcases q with noise | (hash | prg)
  · simp [PrgBelow]
  · simp [PrgBelow]
  · exact Nat.not_lt.mpr h.1

theorem PrgClockLocal.disc {lab : ℕ → ℕ} {j limit : ℕ}
    {q : (LocalSpec C).Domain} (h : PrgClockLocal lab j q) (le : lab (j + 1) ≤ limit) :
    ¬ PrgFrom limit q := by
  rcases q with noise | (hash | prg)
  · simp [PrgFrom]
  · simp [PrgFrom]
  · exact Nat.not_le.mpr (lt_of_lt_of_le h.2 le)

theorem PrgClocked.floor {lab : ℕ → ℕ} (mono : Monotone lab) {j : ℕ}
    {P : OracleComp (PartySpec C E RealSpec) (Option α)} (h : PrgClocked lab j P) :
    PrgFloor (lab j) P := by
  induction h with
  | pure => exact .pure _ _
  | queryLocal j q k query rest ih =>
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query
      (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= k) _ 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl query.lower, fun r => by simpa [PrgFloor] using ih r⟩
  | round j out k rest ih =>
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query
      (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= k) _ 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [PartyQuery]), fun r => by
      simpa [PrgFloor, PartyQuery] using (ih r).mono (mono (Nat.le_succ j))⟩

-- Port of TreeCheckCoinClock.Clocked.checkDisc_bind onto PrgDisc.
theorem PrgClocked.prgDisc_bind {lab : ℕ → ℕ} (mono : Monotone lab)
    {j X : ℕ} {oa : OracleComp (PartySpec C E RealSpec) (Option β)}
    (timed : TreeSimCheckTimed X oa) (h : PrgClocked lab j oa)
    (f : Option β → OracleComp (PartySpec C E RealSpec) (Option α))
    (abort : f none = Pure.pure none) (n : ℕ) (le : n ≤ X) :
    PrgDisc (lab (j + n)) n (oa >>= f) := by
  induction timed generalizing j n with
  | abort X => rw [pure_bind, abort]; exact .pure _ _
  | done a =>
    have : n = 0 := by omega
    subst n
    exact .zero _
  | queryLocal X q k hk ih =>
    cases n with
    | zero => exact .zero _
    | succ n =>
      exact .queryLocal _ _ _ (h.local_inv.1.disc (mono (by omega)))
        (fun r => ih r (h.local_inv.2 r) (n + 1) le)
  | round X out k hk ih =>
    cases n with
    | zero => exact .zero _
    | succ n =>
      refine .round _ _ _ fun r => ?_
      change PrgDisc (lab (j + (n + 1))) n (k r >>= f)
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih r (h.round_inv r) n (by omega)

theorem PrgClocked.floor_bind {lab : ℕ → ℕ} (mono : Monotone lab)
    {j X : ℕ} {oa : OracleComp (PartySpec C E RealSpec) (Option β)}
    (timed : TreeSimCheckTimed X oa) (h : PrgClocked lab j oa)
    (f : Option β → OracleComp (PartySpec C E RealSpec) (Option α))
    (abort : f none = Pure.pure none)
    (rest : ∀ a, some a ∈ support oa → PrgFloor (lab (j + X)) (f (some a)))
    (n : ℕ) (le : n ≤ X) {Q : OracleComp (PartySpec C E RealSpec) (Option α)}
    (run : Residual n (oa >>= f) Q) : PrgFloor (lab (j + n)) Q := by
  induction timed generalizing j n with
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
-- Port of TreeCheckCoinClock.Clocked.exchange_bind, retaining the segment index.
theorem PrgClocked.exchange_bind [Field E] [Algebra Bit E]
    (lab : ℕ → ℕ) (j : ℕ) (out : Mail C E)
    (k : Mail C E → PartyM C E RealSpec α)
    (hk : ∀ inbox, PrgClocked lab (j + 1) (k inbox).run) :
    PrgClocked lab j (exchange out >>= k).run := by
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
  apply PrgClocked.round
  intro inbox
  change PrgClocked lab (j + 1) (exchangeResume k inbox)
  unfold exchangeResume
  split_ifs
  · exact .pure _ _
  · simpa only [OptionT.run_pure, pure_bind, Option.elim_some] using hk inbox

-- Port of TreeCheckCoinClock.Clocked.oracle_bind, without coin keys.
theorem PrgClocked.oracle_bind [Field E] [Algebra Bit E] {lab : ℕ → ℕ} {j : ℕ}
    (p : OracleComp (RoSpec C) α)
    (quiet : IsQueryBoundP p (fun q => ¬ PrgClockLocal lab j (.inr q)) 0)
    (f : α → PartyM C E RealSpec β)
    (rest : ∀ a, PrgClocked lab j (f a).run) : PrgClocked lab j (oracleStep p >>= f).run := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa only [oracleStep_pure, pure_bind] using rest a
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at quiet
    have allowed : PrgClockLocal lab j (.inr q) := by simpa using quiet.1
    have tail : ∀ r, IsQueryBoundP (k r) (fun q => ¬ PrgClockLocal lab j (.inr q)) 0 := by
      simpa using quiet.2
    rw [oracleStep_bind, bind_assoc]
    rcases q with q | q
    all_goals exact .queryLocal _ _ _ allowed (fun r =>
      ih r (tail r))

section RealCheck
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

def PrgOff (ρ : ℕ) : (LocalSpec C).Domain → Prop
  | .inr (.inr x) => x.2.2.1 ≠ ρ
  | _ => False

-- Port of TreeCheckCoinClock.prssDraw_quiet, restricting the PRG label.
theorem prssDraw_at {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R)
    (ρ idx count : ℕ)
    (draw : ∀ name key, IsQueryBoundP (codec.draw name key ρ idx count)
      (fun t => PrgOff (C := C) ρ (.inr t)) 0) :
    IsQueryBoundP (prssDraw ctx codec ρ idx count) (fun t => PrgOff ρ (.inr t)) 0 := by
  unfold prssDraw termDraws pairDraws
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => ?_)
  · simpa using queryBound_mapM (fun t => PrgOff (C := C) ρ (.inr t))
      (fun T => if ctx.self ∈ C.holders T then codec.draw (.term T) (ctx.prss.term T) ρ idx count
        else pure fun _ => 0) 0 C.terms (fun T _ => by
          split_ifs
          · exact draw _ _
          · exact isQueryBoundP_pure _ _ _)
  · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
    simpa using queryBound_mapM (fun t => PrgOff (C := C) ρ (.inr t))
      (fun h => if eq : h = ctx.self then pure fun _ => 0
        else codec.draw (.pair (C.pairOf ctx.self h (Ne.symm eq))) (ctx.prss.pair h) ρ idx count)
      0 C.parties (fun h _ => by
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · exact draw _ _)

-- Port of TreeCheckPrgWindow.prgBits_window at the exact label.
theorem bit_at (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    IsQueryBoundP (prgBits name key ρ idx count) (fun t => PrgOff (C := C) ρ (.inr t)) 0 := by
  unfold prgBits
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
  have h := queryBound_mapM (fun t => PrgOff (C := C) ρ (.inr t))
    (fun position => (query (spec := RoSpec C) (.inr (name, key, ρ, idx, position)) :
      OracleComp (RoSpec C) Bit)) 0 (List.range count) (fun position _ => ?_)
  · simpa using h
  · change IsQueryBoundP (OracleComp.lift (OracleSpec.query
      (spec := RoSpec C) (.inr (name, key, ρ, idx, position)))) _ 0
    rw [isQueryBoundP_query_iff]
    simp [PrgOff]

theorem element_at (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    IsQueryBoundP ((elementCodec K).draw name key ρ idx count)
      (fun t => PrgOff (C := C) ρ (.inr t)) 0 :=
  isQueryBoundP_bind (bit_at name key ρ idx _) (fun _ _ => isQueryBoundP_pure _ _ 0)

theorem prssDraw_clocked {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R)
    (ρ idx count : ℕ)
    (draw : ∀ name key, IsQueryBoundP (codec.draw name key ρ idx count)
      (fun t => PrgOff (C := C) ρ (.inr t)) 0)
    (lab : ℕ → ℕ) (j : ℕ) (lo : lab j ≤ ρ) (hi : ρ < lab (j + 1)) :
    IsQueryBoundP (prssDraw ctx codec ρ idx count)
      (fun t => ¬ PrgClockLocal lab j (.inr t)) 0 := by
  apply IsQueryBoundP.of_imp (fun q hn => ?_) (prssDraw_at ctx codec ρ idx count draw)
  rcases q with hash | prg
  · exact (hn trivial).elim
  · intro eq
    exact hn (by simpa only [PrgClockLocal, eq] using And.intro lo hi)

theorem PrgClocked.oracle_noPrg_bind {lab : ℕ → ℕ} {j : ℕ}
    (p : OracleComp (RoSpec C) α)
    (quiet : IsQueryBoundP p (fun q => PrgFrom (C := C) 0 (.inr q)) 0)
    (f : α → PartyM C E RealSpec β)
    (rest : ∀ a, PrgClocked lab j (f a).run) : PrgClocked lab j (oracleStep p >>= f).run := by
  apply PrgClocked.oracle_bind p _ f rest
  exact IsQueryBoundP.of_imp (fun q hn => by
    by_contra hq
    exact hn (quiet_clock hq)) quiet

-- PRSS has no exchange: the segment stays j although the state label increments.
theorem prgClocked_prss_bind {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R)
    (draw : ∀ name key ρ idx count, IsQueryBoundP (codec.draw name key ρ idx count)
      (fun t => PrgOff (C := C) ρ (.inr t)) 0) (idx count : ℕ)
    (st : RunState C) (lab : ℕ → ℕ) (j : ℕ)
    (lo : lab j ≤ st.label) (hi : st.label < lab (j + 1))
    (f : PrssOutput C R → RunM C E RealSpec α)
    (rest : ∀ r, PrgClocked lab j ((f r).run (nextLabel st)).run) :
    PrgClocked lab j ((prssRandomness ctx codec idx count >>= f).run st).run := by
  rw [prssRandomness_run]
  exact PrgClocked.oracle_bind _ (prssDraw_clocked ctx codec _ _ _ (fun _ _ => draw _ _ _ _ _) lab j lo hi) _ rest

theorem prgClocked_coin (ctx : Context C) (count : ℕ) (st : RunState C)
    (lab : ℕ → ℕ) (j : ℕ) (lo : lab j ≤ st.label) (hi : st.label < lab (j + 1)) :
    PrgClocked lab j (((realCheckGadgets (G := RealSpec) K ctx).coin count).run st).run := by
  rw [realCoin_run]
  apply PrgClocked.oracle_bind _ (prssDraw_clocked ctx _ _ _ _ (fun _ _ => element_at K _ _ _ _ _) lab j lo hi)
  intro o
  apply PrgClocked.of_noPrg
  exact (openSh_zero K 0 ctx _ count).bind (m := 0) (fun _ => .pure _)

theorem prgClocked_coinKey_bind (ctx : Context C) (st : RunState C) (lab : ℕ → ℕ)
    (j : ℕ) (lo : lab j ≤ st.label) (hi : st.label < lab (j + 1))
    (f : HashOutput → RunM C E RealSpec α)
    (rest : ∀ key mid, mid.label = st.label + 1 →
      PrgClocked lab (j + 1) ((f key).run mid).run) :
    PrgClocked lab j ((coinKey K (realCheckGadgets (G := RealSpec) K ctx) >>= f).run st).run := by
  simp only [coinKey, StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  apply PrgClocked.timed_party_bind (treeLockstep_timed_coin K ctx 1 st)
    (prgClocked_coin K ctx 1 st lab j lo hi)
  rintro ⟨values, mid⟩ hmem
  simp only [StateT.run_lift, bind_assoc, pure_bind]
  apply PrgClocked.oracle_noPrg_bind _ (hash_zero 0 _)
  intro key
  exact rest key mid (lockstepLabels_coin K ctx 1 st values mid hmem)

theorem prgClocked_challenge_bind (ctx : Context C) (st : RunState C) (lab : ℕ → ℕ)
    (j : ℕ) (lo : lab j ≤ st.label) (hi : st.label < lab (j + 1))
    (f : E → RunM C E RealSpec α)
    (rest : ∀ r mid, mid.label = st.label + 1 →
      PrgClocked lab (j + 1) ((f r).run mid).run) :
    PrgClocked lab j ((challenge K (realCheckGadgets (G := RealSpec) K ctx) >>= f).run st).run := by
  unfold challenge
  simp only [bind_assoc]
  apply prgClocked_coinKey_bind K ctx st lab j lo hi
  intro key mid label
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply PrgClocked.oracle_noPrg_bind _ (findChallenge_zero K 0 key _ _)
  intro result
  cases result with
  | none => exact .pure _ _
  | some r => exact rest r mid label

theorem prgClocked_extendMult (ctx : Context C) (products : List (Product C E))
    (st : RunState C) (lab : ℕ → ℕ) (j : ℕ)
    (lo : lab j ≤ st.label) (hi : st.label < lab (j + 1)) :
    PrgClocked lab j (((realCheckGadgets (G := RealSpec) K ctx).extendMult products).run st).run := by
  rw [realExtendMult_run]
  apply PrgClocked.oracle_bind _ (prssDraw_clocked ctx _ _ _ _ (fun _ _ => element_at K _ _ _ _ _) lab j lo hi)
  intro o
  exact PrgClocked.exchange_bind lab j _ _ (fun _ => .pure _ _)

theorem prgClocked_extendMult_bind (ctx : Context C) (products : List (Product C E))
    (st : RunState C) (lab : ℕ → ℕ) (j : ℕ)
    (lo : lab j ≤ st.label) (hi : st.label < lab (j + 1))
    (f : Shares C E → RunM C E RealSpec α)
    (rest : ∀ r mid, mid.label = st.label + 1 →
      PrgClocked lab (j + 1) ((f r).run mid).run) :
    PrgClocked lab j (((realCheckGadgets (G := RealSpec) K ctx).extendMult products >>= f).run st).run := by
  rw [StateT.run_bind]
  apply PrgClocked.timed_party_bind (treeLockstep_timed_extendMult K ctx products st)
    (prgClocked_extendMult K ctx products st lab j lo hi)
  rintro ⟨r, mid⟩ mem
  exact rest r mid (lockstepLabels_extendMult K ctx products st r mid mem)

theorem prgClocked_slice_bind (ctx : Context C) (τ : List E) (count : ℕ)
    (v : Shares C E × Shares C E × E) (t : ℕ) (st : RunState C)
    (lab : ℕ → ℕ) (j : ℕ)
    (lo : lab j ≤ st.label) (hi : st.label < lab (j + 1))
    (loNext : lab (j + 1) ≤ st.label + 1) (hiNext : st.label + 1 < lab (j + 2))
    (f : (Shares C E × Shares C E × E) → RunM C E RealSpec α)
    (rest : ∀ v mid, mid.label = st.label + 2 → PrgClocked lab (j + 2) ((f v).run mid).run) :
    PrgClocked lab j ((sliceStep K ctx (realCheckGadgets (G := RealSpec) K ctx) τ count v t >>= f).run st).run := by
  rcases v with ⟨xs, ys, d⟩
  unfold sliceStep
  simp only [bind_assoc, pure_bind]
  apply prgClocked_extendMult_bind K ctx _ st lab j lo hi
  intro values mid label
  apply prgClocked_challenge_bind K ctx mid lab (j + 1)
    (by simpa only [label, Nat.add_assoc] using loNext)
    (by simpa only [label, Nat.add_assoc] using hiNext)
  intro r final hfinal
  simpa only [Nat.add_assoc] using rest _ final (by omega)

theorem prgClocked_halving_bind (ctx : Context C) (width : ℕ)
    (v : (ℕ → E) × (ℕ → E) × E) (t : ℕ) (st : RunState C)
    (lab : ℕ → ℕ) (j : ℕ)
    (lo : lab j ≤ st.label) (hi : st.label < lab (j + 1))
    (loNext : lab (j + 1) ≤ st.label + 1) (hiNext : st.label + 1 < lab (j + 2))
    (f : ((ℕ → E) × (ℕ → E) × E) → RunM C E RealSpec α)
    (rest : ∀ v mid, mid.label = st.label + 2 → PrgClocked lab (j + 2) ((f v).run mid).run) :
    PrgClocked lab j ((halvingStep K ctx (realCheckGadgets (G := RealSpec) K ctx) width v t >>= f).run st).run := by
  rcases v with ⟨xs, ys, d⟩
  unfold halvingStep
  simp only [bind_assoc, pure_bind]
  apply prgClocked_extendMult_bind K ctx _ st lab j lo hi
  intro values mid label
  apply prgClocked_challenge_bind K ctx mid lab (j + 1)
    (by simpa only [label, Nat.add_assoc] using loNext)
    (by simpa only [label, Nat.add_assoc] using hiNext)
  intro r final hfinal
  simpa only [Nat.add_assoc] using rest _ final (by omega)

-- Port of TreeLockstepOpenedRest.openedRest_timed_fold (private), keeping
-- the exchange offset and the successful label increment at each step.
theorem prgClocked_fold {δ : Type} (f : α → δ → RunM C E RealSpec α)
    (xs : List δ) (lab : ℕ → ℕ) (j L : ℕ)
    (step : ∀ t, t < xs.length → ∀ a b st (k : α → RunM C E RealSpec β),
      st.label = L + 2 * t →
      (∀ v mid, mid.label = L + 2 * (t + 1) →
        PrgClocked lab (j + 2 * (t + 1)) ((k v).run mid).run) →
      PrgClocked lab (j + 2 * t) ((f a b >>= k).run st).run)
    (a : α) (st : RunState C) (label : st.label = L)
    (k : α → RunM C E RealSpec β)
    (rest : ∀ v mid, mid.label = L + 2 * xs.length →
      PrgClocked lab (j + 2 * xs.length) ((k v).run mid).run) :
    PrgClocked lab j ((xs.foldlM f a >>= k).run st).run := by
  induction xs generalizing a st j L with
  | nil =>
    simpa using rest a st (by simpa using label)
  | cons b xs ih =>
    rw [List.foldlM_cons, bind_assoc]
    have first := step 0 (by simp) a b st
      (fun v => xs.foldlM f v >>= k) (by simpa using label)
    simp only [Nat.mul_zero, Nat.add_zero] at first
    apply first
    intro v mid hmid
    apply ih (j := j + 2) (L := L + 2)
    · intro t ht a b st k hst hk
      have h := step (t + 1) (by simp only [List.length_cons]; omega) a b st k
        (by omega) (fun v mid hmid => by
          convert hk v mid (by omega) using 1; omega)
      convert h using 1; omega
    · simpa using hmid
    · intro v final hfinal
      convert rest v final (by simp only [List.length_cons]; omega) using 1; simp only [List.length_cons]; omega

-- Port of TreeCheckCoinClock.clocked_final with the actual PRG segments.
theorem prgClocked_final (ctx : Context C) (v : (ℕ → E) × (ℕ → E) × E)
    (st : RunState C) (lab : ℕ → ℕ) (j : ℕ)
    (lo : lab j ≤ st.label) (hi : st.label + 1 < lab (j + 1))
    (loSalt : lab (j + 1) ≤ st.label + 2) (hiSalt : st.label + 2 < lab (j + 2))
    (loCoin : lab (j + 2) ≤ st.label + 3) (hiCoin : st.label + 3 < lab (j + 3)) :
    PrgClocked lab j ((finalStep K ctx (realCheckGadgets (G := RealSpec) K ctx) v).run st).run := by
  rcases v with ⟨xs, ys, d⟩
  unfold finalStep
  apply prgClocked_prss_bind ctx (elementCodec K) (element_at K) 1 2 st lab j lo (by omega)
  intro w
  apply prgClocked_extendMult_bind K ctx _ (nextLabel st) lab j
    (by simp only [nextLabel]; omega) (by simpa only [nextLabel] using hi)
  intro q mid label
  apply prgClocked_prss_bind ctx bitCodec bit_at 2 256 mid lab (j + 1)
    (by simp only [nextLabel] at label; omega)
    (by simp only [nextLabel] at label; simpa only [Nat.add_assoc] using (show mid.label < lab (j + 2) by omega))
  intro salts
  rw [StateT.run_bind]
  apply PrgClocked.timed_party_bind (treeLockstep_timed_digest ctx salts.1 (nextLabel mid))
    (PrgClocked.of_noPrg (compare_quiet 0 ctx salts.1 (nextLabel mid)))
  rintro ⟨u, after⟩ hd
  have ld := lockstepLabels_compareDigests ctx salts.1 (nextLabel mid) u after hd
  have afterLabel : after.label = st.label + 3 := by
    simp only [nextLabel] at label ld
    omega
  apply prgClocked_challenge_bind K ctx after lab (j + 1 + 1)
    (by simpa only [afterLabel, Nat.add_assoc] using loCoin)
    (by simpa only [afterLabel, Nat.add_assoc] using hiCoin)
  intro r final _
  apply PrgClocked.of_noPrg
  exact (RunBudget.lift (openSh_zero K 0 ctx _ 3)).bind_zero
    (fun _ => RunBudget.lift (require_zero 0 _)) final

/-- The PRG cutoff at each local segment of the real check. -/
def prgCheckClock (count i : ℕ) : ℕ :=
  if count = 0 then 0 else
    if i ≤ 2 * halvings count + 1 then i
    else if i ≤ 2 * halvings count + 4 then i + 1
    else 2 * halvings count + 5

theorem prgCheckClock_zero (count : ℕ) : prgCheckClock count 0 = 0 := by
  simp [prgCheckClock]

theorem prgCheckClock_mono (count : ℕ) : Monotone (prgCheckClock count) := by
  intro i j le
  unfold prgCheckClock
  split_ifs <;> omega

theorem prgCheckClock_end (count : ℕ) : prgCheckClock count (checkLabels count) = checkLabels count := by
  unfold prgCheckClock checkLabels
  split_ifs <;> omega

theorem prgCheckClock_le (count i : ℕ) : prgCheckClock count i ≤ checkLabels count := by
  unfold prgCheckClock checkLabels
  split_ifs <;> omega

theorem prgCheckClock_first (count : ℕ) (nonzero : count ≠ 0) :
    prgCheckClock count 1 = 1 := by
  unfold prgCheckClock
  split_ifs <;> omega

theorem prgCheckClock_loop (count t : ℕ) (nonzero : count ≠ 0) (lt : t < halvings count) :
    prgCheckClock count (1 + 2 * t) = 1 + 2 * t ∧
    prgCheckClock count (2 + 2 * t) = 2 + 2 * t ∧
    prgCheckClock count (3 + 2 * t) = 3 + 2 * t := by
  unfold prgCheckClock
  split_ifs <;> omega

theorem prgCheckClock_final (count : ℕ) (nonzero : count ≠ 0) :
    prgCheckClock count (2 * halvings count + 1) = 2 * halvings count + 1 ∧
    prgCheckClock count (2 * halvings count + 2) = 2 * halvings count + 3 ∧
    prgCheckClock count (2 * halvings count + 3) = 2 * halvings count + 4 ∧
    prgCheckClock count (2 * halvings count + 4) = 2 * halvings count + 5 := by
  unfold prgCheckClock
  split_ifs <;> omega

theorem prgClocked_require_bind (lab : ℕ → ℕ) (j : ℕ)
    (p : Prop) (f : Unit → PartyM C E RealSpec α)
    (rest : ∀ u, PrgClocked lab j (f u).run) : PrgClocked lab j (require p >>= f).run := by
  unfold require
  split_ifs
  · simpa using rest ()
  · exact .pure _ _

set_option maxHeartbeats 1000000 in
/-- Every real PRG read lies in its segment interval, on every answer path. -/
theorem prgClocked_check (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C) :
    PrgClocked (fun i => st.label + prgCheckClock (tuples.map (·.count)).sum i) 0
      ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st).run := by
  by_cases zero : (tuples.map (·.count)).sum = 0
  · simp only [check, zero, if_true]
    exact .pure _ _
  · set count := (tuples.map (·.count)).sum
    set lab := fun i => st.label + prgCheckClock count i
    have hs : sliceBits ≤ halvings count := by unfold halvings; omega
    have first := prgCheckClock_first count zero
    rw [check_eq K ctx _ tuples zero]
    rw [show (tuples.map (·.count)).sum = count from rfl]
    apply prgClocked_coinKey_bind K ctx st lab 0
      (by simp [lab, prgCheckClock_zero])
      (by simp [lab, first])
    intro key mid hmid
    rw [StateT.run_bind]
    simp only [expand, StateT.run_lift, bind_assoc, pure_bind]
    apply PrgClocked.oracle_noPrg_bind
    · simpa using queryBound_mapM (fun t => PrgFrom (C := C) 0 (.inr t))
        (fun k => elementOfHash K <$> hashQuery (C := C) (.expand key k)) 0 (List.range (coins count))
        (fun k _ => (isQueryBoundP_map_iff _ _ _).mpr (hash_zero 0 _))
    intro τ
    rw [StateT.run_bind]
    simp only [StateT.run_lift, bind_assoc, pure_bind]
    apply prgClocked_require_bind lab 1
    intro _
    apply prgClocked_fold (j := 1) (L := st.label + 1)
    · intro t ht v b ss k hss hk
      simp only [List.length_range] at ht
      have bounds := prgCheckClock_loop count t zero (by omega)
      apply prgClocked_slice_bind K ctx τ count v b ss lab (1 + 2 * t)
        (by dsimp only [lab]; rw [bounds.1]; omega)
        (by dsimp only [lab]; rw [show 1 + 2 * t + 1 = 2 + 2 * t by omega, bounds.2.1]; omega)
        (by dsimp only [lab]; rw [show 1 + 2 * t + 1 = 2 + 2 * t by omega, bounds.2.1]; omega)
        (by dsimp only [lab]; rw [show 1 + 2 * t + 2 = 3 + 2 * t by omega, bounds.2.2]; omega)
      intro v final hfinal
      convert hk v final (by omega) using 1; omega
    · exact hmid
    · intro v mid' hmid'
      simp only [List.length_range] at hmid' ⊢
      apply prgClocked_fold (j := 1 + 2 * sliceBits) (L := st.label + 1 + 2 * sliceBits)
      · intro t ht v b ss k hss hk
        simp only [List.length_range] at ht
        have bounds := prgCheckClock_loop count (sliceBits + t) zero (by omega)
        apply prgClocked_halving_bind K ctx (sliceWidth count) v b ss lab (1 + 2 * sliceBits + 2 * t)
          (by dsimp only [lab]; rw [show 1 + 2 * sliceBits + 2 * t = 1 + 2 * (sliceBits + t) by omega, bounds.1]; omega)
          (by dsimp only [lab]; rw [show 1 + 2 * sliceBits + 2 * t + 1 = 2 + 2 * (sliceBits + t) by omega, bounds.2.1]; omega)
          (by dsimp only [lab]; rw [show 1 + 2 * sliceBits + 2 * t + 1 = 2 + 2 * (sliceBits + t) by omega, bounds.2.1]; omega)
          (by dsimp only [lab]; rw [show 1 + 2 * sliceBits + 2 * t + 2 = 3 + 2 * (sliceBits + t) by omega, bounds.2.2]; omega)
        intro v final hfinal
        convert hk v final (by omega) using 1; omega
      · exact hmid'
      · intro v final hfinal
        simp only [List.length_range] at hfinal ⊢
        have bounds := prgCheckClock_final count zero
        have endIndex : 1 + 2 * sliceBits + 2 * (halvings count - sliceBits) = 2 * halvings count + 1 := by omega
        apply prgClocked_final K ctx v final lab (1 + 2 * sliceBits + 2 * (halvings count - sliceBits))
        all_goals dsimp only [lab]; rw [endIndex]
        · rw [bounds.1]; omega
        · rw [show 2 * halvings count + 1 + 1 = 2 * halvings count + 2 by omega, bounds.2.1]; omega
        · rw [show 2 * halvings count + 1 + 1 = 2 * halvings count + 2 by omega, bounds.2.1]; omega
        · rw [show 2 * halvings count + 1 + 2 = 2 * halvings count + 3 by omega, bounds.2.2.1]; omega
        · rw [show 2 * halvings count + 1 + 2 = 2 * halvings count + 3 by omega, bounds.2.2.1]; omega
        · rw [show 2 * halvings count + 1 + 3 = 2 * halvings count + 4 by omega, bounds.2.2.2]; omega

/-- Past discipline and every residual's future floor at an arbitrary check cut. -/
theorem prg_check_clock (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C)
    (k : Unit × RunState C → PartyM C E RealSpec α)
    (rest : ∀ a, some a ∈ support ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st).run →
      PrgFloor (st.label + checkLabels (tuples.map (·.count)).sum) (k a).run)
    (n : ℕ) (le : n ≤ checkLabels (tuples.map (·.count)).sum) :
    PrgDisc (st.label + prgCheckClock (tuples.map (·.count)).sum n) n
      ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st >>= k).run ∧
    ∀ Q, Residual n ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st >>= k).run Q →
      PrgFloor (st.label + prgCheckClock (tuples.map (·.count)).sum n) Q := by
  have mono : Monotone (fun i => st.label + prgCheckClock (tuples.map (·.count)).sum i) :=
    fun _ _ le => Nat.add_le_add_left (prgCheckClock_mono _ le) _
  have timed := check_timed K ctx tuples st
  have clock := prgClocked_check K ctx tuples st
  simp only [OptionT.run_bind, Option.elimM]
  refine ⟨?_, ?_⟩
  · simpa only [Nat.zero_add] using PrgClocked.prgDisc_bind mono timed clock
      (fun a => a.elim (pure none) (fun a => (k a).run)) rfl n le
  · intro Q run
    simpa only [Nat.zero_add] using PrgClocked.floor_bind mono timed clock
      (fun a => a.elim (pure none) (fun a => (k a).run)) rfl
      (fun a ha => by simpa only [Nat.zero_add, prgCheckClock_end, Option.elim_some] using rest a ha) n le run

/-- The local check itself, with a pure continuation. -/
theorem prg_check_clock_self (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C)
    (n : ℕ) (le : n ≤ checkLabels (tuples.map (·.count)).sum) :
    PrgDisc (st.label + prgCheckClock (tuples.map (·.count)).sum n) n
      ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st).run ∧
    ∀ Q, Residual n ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st).run Q →
      PrgFloor (st.label + prgCheckClock (tuples.map (·.count)).sum n) Q := by
  simpa only [bind_pure] using prg_check_clock K ctx tuples st pure (fun _ _ => .pure _ _) n le

/-- Ceiling division advances before a collector's idle local segment. -/
def prefixClock (r start n : ℕ) : ℕ := start + (n + r - 1) / r

theorem rounds_pos (mode : ReshareMode) : 0 < mode.rounds := by
  cases mode <;> decide

theorem prefixClock_mono (r start : ℕ) : Monotone (prefixClock r start) := by
  intro i j le
  exact Nat.add_le_add_left (Nat.div_le_div_right (by omega : i + r - 1 ≤ j + r - 1)) _

theorem prefixClock_zero (r start : ℕ) (positive : 0 < r) : prefixClock r start 0 = start := by
  simp only [prefixClock, Nat.zero_add]
  rw [Nat.div_eq_of_lt (by omega), Nat.add_zero]

theorem prefixClock_layer (r start l : ℕ) (positive : 0 < r) :
    prefixClock r start (r * l) = start + l ∧
    prefixClock r start (r * l + 1) = start + l + 1 := by
  constructor
  · unfold prefixClock
    rw [show r * l + r - 1 = r * l + (r - 1) by omega,
      Nat.mul_add_div positive, Nat.div_eq_of_lt (by omega), Nat.add_zero]
  · unfold prefixClock
    rw [show r * l + 1 + r - 1 = r * l + r by omega,
      Nat.mul_add_div positive, Nat.div_self (by omega), Nat.add_assoc]

theorem prefixClock_pre (r start d : ℕ) (positive : 0 < r) :
    prefixClock r start (d * r + 1) = start + d + 1 := by
  simpa only [Nat.mul_comm] using (prefixClock_layer r start d positive).2

-- Port of clocked_fold, with r exchanges and one state label per layer.
theorem prgClocked_layerFold {δ : Type} (f : α → δ → RunM C E RealSpec α)
    (xs : List δ) (lab : ℕ → ℕ) (r j L : ℕ)
    (step : ∀ t, t < xs.length → ∀ a b st (k : α → RunM C E RealSpec β),
      st.label = L + t →
      (∀ v mid, mid.label = L + (t + 1) →
        PrgClocked lab (j + r * (t + 1)) ((k v).run mid).run) →
      PrgClocked lab (j + r * t) ((f a b >>= k).run st).run)
    (a : α) (st : RunState C) (label : st.label = L)
    (k : α → RunM C E RealSpec β)
    (rest : ∀ v mid, mid.label = L + xs.length →
      PrgClocked lab (j + r * xs.length) ((k v).run mid).run) :
    PrgClocked lab j ((xs.foldlM f a >>= k).run st).run := by
  induction xs generalizing a st j L with
  | nil => simpa using rest a st (by simpa using label)
  | cons b xs ih =>
    rw [List.foldlM_cons, bind_assoc]
    have first := step 0 (by simp) a b st
      (fun v => xs.foldlM f v >>= k) (by simpa using label)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_one] at first
    apply first
    intro v mid hmid
    apply ih (j := j + r) (L := L + 1)
    · intro t ht a b st k hst hk
      have h := step (t + 1) (by simp only [List.length_cons]; omega) a b st k
        (by omega) (fun v mid hmid => by
          convert hk v mid (by omega) using 1
          simp only [Nat.mul_add, Nat.mul_one]
          omega)
      convert h using 1
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    · simpa using hmid
    · intro v final hfinal
      convert rest v final (by simp only [List.length_cons]; omega) using 1
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem prgClocked_mult (ctx : Context C) (mode : ReshareMode)
    (x y : Shares C Bit) (count : ℕ) (st : RunState C)
    (lab : ℕ → ℕ) (j : ℕ) (lo : lab j ≤ st.label) (hi : st.label < lab (j + 1)) :
    PrgClocked lab j (((realRunGadgets (G := RealSpec) K ctx mode).mult x y count).run st).run := by
  change PrgClocked lab j
    (((prssRandomness ctx bitCodec 0 count >>= fun rnd =>
      reshareWith K ctx mode rnd (mulRep K ctx x y) count).run st).run)
  apply prgClocked_prss_bind ctx bitCodec bit_at 0 count st lab j lo hi
  intro rnd
  exact PrgClocked.of_noPrg (reshareWith_zero K 0 ctx mode rnd _ _ _)

theorem prgClocked_rerand (ctx : Context C) (mode : ReshareMode)
    (v : Shares C Bit) (count : ℕ) (st : RunState C)
    (lab : ℕ → ℕ) (j : ℕ) (lo : lab j ≤ st.label) (hi : st.label < lab (j + 1)) :
    PrgClocked lab j (((realRunGadgets (G := RealSpec) K ctx mode).rerand v count).run st).run := by
  change PrgClocked lab j
    (((prssRandomness ctx bitCodec 0 count >>= fun rnd =>
      reshare K ctx bitCodec rnd (ownerSum K ctx v) count).run st).run)
  apply prgClocked_prss_bind ctx bitCodec bit_at 0 count st lab j lo hi
  intro rnd
  exact PrgClocked.of_noPrg (reshare_zero K 0 ctx bitCodec rnd _ _ _)

theorem prgClocked_beforeVerify_bind (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) (st : RunState C)
    (lab : ℕ → ℕ) (j : ℕ)
    (bounds : ∀ l, l ≤ depth jobs →
      lab (j + mode.rounds * l) ≤ st.label + l ∧
        st.label + l < lab (j + mode.rounds * l + 1))
    (f : (Shares C Bit × List (Tuple C)) → RunM C E RealSpec α)
    (rest : ∀ v mid, mid.label = st.label + depth jobs + 1 →
      PrgClocked lab (j + depth jobs * mode.rounds + 1) ((f v).run mid).run) :
    PrgClocked lab j ((treeSimCheckBeforeVerify K ctx mode jobs inputs >>= f).run st).run := by
  unfold treeSimCheckBeforeVerify
  simp only [bind_assoc]
  apply prgClocked_layerFold (r := mode.rounds) (j := j) (L := st.label)
  · intro t ht a b ss k hss hk
    have interval := bounds t (by simpa only [List.length_range] using Nat.le_of_lt ht)
    unfold layerBody
    simp only [bind_assoc, pure_bind]
    rw [StateT.run_bind]
    apply PrgClocked.timed_party_bind (treeSimCheckTimed_mult K ctx mode _ _ _ ss)
      (prgClocked_mult K ctx mode _ _ _ ss lab (j + mode.rounds * t)
        (by omega) (by omega))
    rintro ⟨z, mid⟩ hz
    have label := mult_labels K ctx mode _ _ _ ss z mid hz
    convert hk _ mid (by omega) using 1
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  · rfl
  · intro p mid label
    simp only [List.length_range] at label ⊢
    simp only [pure_bind]
    rw [StateT.run_bind]
    have interval := bounds (depth jobs) le_rfl
    apply PrgClocked.timed_party_bind (treeSimCheckTimed_rerand K ctx mode _ _ mid)
      (prgClocked_rerand K ctx mode _ _ mid lab (j + mode.rounds * depth jobs)
        (by omega) (by omega))
    rintro ⟨v, final⟩ hv
    have finalLabel := rerand_labels K ctx mode _ _ mid v final hv
    simpa only [Nat.mul_comm] using rest _ final (by omega)

-- Port of TreeSimCheckTimed.local_bind, enforcing quietness at each query.
set_option backward.isDefEq.respectTransparency false in
theorem PrgClocked.local_noPrg_bind {lab : ℕ → ℕ} {j : ℕ}
    (p : OracleComp (LocalSpec C) α) (quiet : IsQueryBoundP p (PrgFrom 0) 0)
    (f : α → PartyM C E RealSpec β)
    (rest : ∀ a, PrgClocked lab j (f a).run) : PrgClocked lab j (localStep p >>= f).run := by
  simp only [localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM,
    bind_assoc, pure_bind, Option.elim_some]
  change PrgClocked lab j (liftComp p (PartySpec C E RealSpec) >>= fun a => (f a).run)
  induction p using OracleComp.inductionOn with
  | pure a => simpa only [liftComp_pure, pure_bind] using rest a
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at quiet
    have allowed : ¬ PrgFrom 0 q := by simpa using quiet.1
    have tail : ∀ r, IsQueryBoundP (k r) (PrgFrom 0) 0 := by simpa using quiet.2
    simp only [liftComp_bind, liftComp_query, bind_assoc]
    have hq : ((OracleSpec.query q).cont <$> liftM (OracleSpec.query (OracleSpec.query q).input) :
        OracleComp (PartySpec C E RealSpec) _) =
        OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl q))) := by
      rw [← liftM_query_local]
      rfl
    rw [hq]
    exact .queryLocal _ _ _ (quiet_clock allowed) (fun r => ih r (tail r))

-- The oracle part of TreeCheckPrgWindow.inputShares_zero, with its continuation retained.
theorem prgClocked_inputs_bind (ctx : Context C) (jobs : List Job)
    (lab : ℕ → ℕ) (j : ℕ) (k : List (C.Term → List Bit) → PartyM C E RealSpec α)
    (rest : ∀ inputs, PrgClocked lab j (k inputs).run) :
    PrgClocked lab j (jobs.mapM (inputShares ctx) >>= k).run := by
  have hp (seed : HashOutput) (xs : List Point) :
      IsQueryBoundP (xs.flatMapM fun x => bitsOfDigest <$> prf (C := C) seed x)
        (fun t => PrgFrom (C := C) 0 (.inr t)) 0 := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.flatMapM_cons]
      refine isQueryBoundP_bind (n := 0) (m := 0) ?_
        (fun ys _ => isQueryBoundP_bind ih (fun zs _ => isQueryBoundP_pure _ _ 0))
      simp only [prf, Functor.map_map, isQueryBoundP_map_iff]
      exact hash_zero 0 _
  induction jobs generalizing k with
  | nil => simpa only [List.mapM_nil, pure_bind] using rest []
  | cons job jobs ih =>
    simp only [List.mapM_cons, bind_assoc, inputShares, pure_bind]
    apply PrgClocked.oracle_noPrg_bind
    · simpa using queryBound_mapM (fun t => PrgFrom (C := C) 0 (.inr t))
        (fun T => if ctx.self ∈ C.holders T then job.points.flatMapM fun x => bitsOfDigest <$> prf (ctx.keys.seed T) x
          else pure []) 0 C.terms (fun T _ => by
            split_ifs
            · exact hp _ _
            · exact isQueryBoundP_pure _ _ _)
    intro terms
    exact ih _ (fun inputs => rest _)

variable (circuits : Circuits) (settings : Settings)

theorem prgClocked_batchPrefix (tail : OracleComp (LocalSpec C) (Option Unit))
    (noPrg : IsQueryBoundP tail (PrgFrom 0) 0)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    PrgClocked (prefixClock settings.mode.rounds initial.1) 0
      (treeLockstepLocalPrelude tail >>= fun _ =>
        treeSimCheckBatchPrefix K circuits settings ctx jobs initial).run := by
  unfold treeLockstepLocalPrelude
  rw [bind_assoc]
  apply PrgClocked.local_noPrg_bind tail noPrg
  intro result
  cases result with
  | none => exact .pure _ _
  | some u =>
    simp only [pure_bind]
    unfold treeSimCheckBatchPrefix
    apply prgClocked_inputs_bind
    intro inputs
    have clock : PrgClocked (prefixClock settings.mode.rounds initial.1) 0
        ((treeSimCheckBeforeVerify K ctx settings.mode
          (jobs.map (circuits ctx.keys.parameter ·.kind)) inputs).run
            ⟨fun _ => [], initial.1, initial.2⟩).run := by
      rw [← bind_pure (treeSimCheckBeforeVerify K ctx settings.mode
        (jobs.map (circuits ctx.keys.parameter ·.kind)) inputs)]
      apply prgClocked_beforeVerify_bind K ctx settings.mode _ inputs _ _ 0
      · intro l hl
        have bounds := prefixClock_layer settings.mode.rounds initial.1 l (rounds_pos settings.mode)
        simp only [Nat.zero_add, bounds.1, bounds.2]
        exact ⟨le_rfl, Nat.lt_succ_self _⟩
      · intro v mid label
        exact .pure _ _
    apply PrgClocked.timed_party_bind (treeSimCheckBeforeVerify_timed K ctx settings.mode _ inputs _) clock
    intro a ha
    exact .pure _ _

theorem prg_prefix_clock (tail : OracleComp (LocalSpec C) (Option Unit))
    (noPrg : IsQueryBoundP tail (PrgFrom 0) 0)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (k : (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C) →
      PartyM C E RealSpec α)
    (rest : ∀ a, some a ∈ support (treeLockstepLocalPrelude tail >>= fun _ =>
      treeSimCheckBatchPrefix K circuits settings ctx jobs initial).run →
      PrgFloor (initial.1 + depth (jobs.map (circuits ctx.keys.parameter ·.kind)) + 1) (k a).run)
    (n : ℕ) (le : n ≤ depth (jobs.map (circuits ctx.keys.parameter ·.kind)) * settings.mode.rounds + 1) :
    PrgDisc (prefixClock settings.mode.rounds initial.1 n) n
      ((treeLockstepLocalPrelude tail >>= fun _ => treeSimCheckBatchPrefix K circuits settings ctx jobs initial) >>= k).run ∧
    ∀ Q, Residual n
      ((treeLockstepLocalPrelude tail >>= fun _ => treeSimCheckBatchPrefix K circuits settings ctx jobs initial) >>= k).run Q →
      PrgFloor (prefixClock settings.mode.rounds initial.1 n) Q := by
  have mono := prefixClock_mono settings.mode.rounds initial.1
  have timed := treeLockstep_localPrelude_timed tail _ _
    (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs initial)
  have clock := prgClocked_batchPrefix K circuits settings tail noPrg ctx jobs initial
  simp only [OptionT.run_bind, Option.elimM] at timed clock rest ⊢
  refine ⟨?_, ?_⟩
  · simpa only [Nat.zero_add] using PrgClocked.prgDisc_bind mono timed clock
      (fun a => a.elim (pure none) (fun a => (k a).run)) rfl n le
  · intro Q run
    simpa only [Nat.zero_add] using PrgClocked.floor_bind mono timed clock
      (fun a => a.elim (pure none) (fun a => (k a).run)) rfl
      (fun a ha => by simpa only [Nat.zero_add, prefixClock_pre _ _ _ (rounds_pos settings.mode),
        Option.elim_some] using rest a ha) n le run

/-- Every party belongs to the complement of some size-(t-1) term. -/
theorem held_term (i : C.Party) : ∃ T : C.Term, i ∈ C.holders T := by
  have room : C.t - 1 ≤ (Finset.univ.erase i : Finset C.Party).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    unfold Committee.n
    have := C.one_le_t
    omega
  obtain ⟨T, subset, card⟩ := Finset.exists_subset_card_eq room
  refine ⟨⟨T, card⟩, ?_⟩
  simp only [Committee.holders, Finset.mem_compl]
  intro mem
  exact (Finset.mem_erase.mp (subset mem)).1 rfl

/-- A floor on a lifted oracle prefix constrains every oracle query before it returns. -/
theorem oracleStep_floor_left (limit : ℕ) (p : OracleComp (RoSpec C) α)
    (f : α → PartyM C E RealSpec β)
    (floor : PrgFloor limit (oracleStep p >>= f).run) :
    IsQueryBoundP p (fun t => PrgBelow (C := C) limit (.inr t)) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind q k ih =>
    rw [oracleStep_bind, bind_assoc] at floor
    cases q with
    | inl hash =>
      change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
        (.inl (.inl (.inr (.inl hash))))) >>= fun r => (oracleStep (k r) >>= f).run)
          (PartyQuery (E := E) (G := RealSpec) (PrgBelow limit)) 0 at floor
      rw [isQueryBoundP_query_bind_iff] at floor ⊢
      exact ⟨floor.1, fun r => by simpa using ih r (by simpa [PrgFloor] using floor.2 r)⟩
    | inr prg =>
      change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
        (.inl (.inl (.inr (.inr prg))))) >>= fun r => (oracleStep (k r) >>= f).run)
          (PartyQuery (E := E) (G := RealSpec) (PrgBelow limit)) 0 at floor
      rw [isQueryBoundP_query_bind_iff] at floor ⊢
      exact ⟨floor.1, fun r => by simpa using ih r (by simpa [PrgFloor] using floor.2 r)⟩

-- Port of VCVio OracleComp/QueryTracking/CostModel.exists_mem_support (private).
private theorem oracle_support_nonempty {ι : Type} {spec : OracleSpec ι}
    [∀ t, Inhabited (spec.Range t)] (p : OracleComp spec α) : (support p).Nonempty := by
  induction p using OracleComp.inductionOn with
  | pure a => exact ⟨a, by simp⟩
  | query_bind t k ih =>
    obtain ⟨a, ha⟩ := ih default
    exact ⟨a, (mem_support_bind_iff _ _ _).mpr ⟨default, mem_support_query _ _, ha⟩⟩

-- Query-bound extraction uses the pinned leanVM support-continuation law.
private theorem mapM_floor_member {δ : Type} (xs : List δ) (f : δ → OracleComp (RoSpec C) α)
    (predicate : (RoSpec C).Domain → Prop) (bound : IsQueryBoundP (xs.mapM f) predicate 0)
    (x : δ) (mem : x ∈ xs) : IsQueryBoundP (f x) predicate 0 := by
  induction xs with
  | nil => simp at mem
  | cons y ys ih =>
    rw [List.mapM_cons] at bound
    rcases List.mem_cons.mp mem with eq | mem
    · subst x
      exact IsQueryBoundP.of_bind_left bound
    · obtain ⟨a, ha⟩ := oracle_support_nonempty (f y)
      have tail := XmssSecurity.OracleComp.IsQueryBoundP.bind_right_of_mem_support bound a ha
      exact ih (IsQueryBoundP.of_bind_left tail) mem

private theorem prgBits_floor_label (name : KeyName C) (key : HashOutput) (ρ idx count limit : ℕ)
    (pos : 0 < count)
    (floor : IsQueryBoundP (prgBits name key ρ idx count)
      (fun t => PrgBelow (C := C) limit (.inr t)) 0) : limit ≤ ρ := by
  unfold prgBits at floor
  have first := mapM_floor_member (List.range count)
    (fun position => (query (spec := RoSpec C) (.inr (name, key, ρ, idx, position)) :
      OracleComp (RoSpec C) Bit)) _ (IsQueryBoundP.of_bind_left floor) 0 (by simpa using pos)
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query
    (spec := RoSpec C) (.inr (name, key, ρ, idx, 0)))) _ 0 at first
  rw [isQueryBoundP_query_iff] at first
  exact Nat.le_of_not_gt (fun h => (Nat.lt_irrefl 0) (first h))

theorem termDraws_floor_label (ctx : Context C) (ρ idx count limit : ℕ)
    (held : ∃ T : C.Term, ctx.self ∈ C.holders T) (pos : 0 < count)
    (floor : IsQueryBoundP (termDraws ctx (elementCodec K) ρ idx count)
      (fun t => PrgBelow (C := C) limit (.inr t)) 0) : limit ≤ ρ := by
  obtain ⟨T, held⟩ := held
  have term := mapM_floor_member C.terms
    (fun T => if ctx.self ∈ C.holders T then (elementCodec K).draw (.term T) (ctx.prss.term T) ρ idx count
      else pure fun _ => 0) _ floor T (by simp [Committee.terms])
  rw [if_pos held] at term
  apply prgBits_floor_label (.term T) (ctx.prss.term T) ρ idx (elementBits * count) limit
    (by unfold elementBits; omega)
  exact IsQueryBoundP.of_bind_left term

/-- The first coin reads 192 bits of a held term even when all later paths abort. -/
theorem check_prg_floor_label (ctx : Context C)
    (held : ∃ T : C.Term, ctx.self ∈ C.holders T) (st : RunState C) (tuples : List (Tuple C))
    (nonzero : (tuples.map (·.count)).sum ≠ 0) (limit : ℕ)
    (floor : PrgFloor limit
      ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st).run) :
    limit ≤ st.label := by
  rw [check_eq K ctx _ tuples nonzero] at floor
  simp only [StateT.run_bind, OptionT.run_bind, Option.elimM] at floor
  have coinFloor : PrgFloor limit
      ((coinKey K (realCheckGadgets (G := RealSpec) K ctx)).run st).run :=
    IsQueryBoundP.of_bind_left floor
  simp only [coinKey, StateT.run_bind, StateT.run_get, pure_bind] at coinFloor
  have drawFloor : PrgFloor limit (((realCheckGadgets (G := RealSpec) K ctx).coin 1).run st).run :=
    IsQueryBoundP.of_bind_left coinFloor
  rw [realCoin_run] at drawFloor
  have prssFloor := oracleStep_floor_left limit _ _ drawFloor
  unfold prssDraw at prssFloor
  exact termDraws_floor_label K ctx st.label 1 1 limit held (by decide)
    (IsQueryBoundP.of_bind_left prssFloor)

end RealCheck
end TreeCheckPrgClock
end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgClock.PrgFloor.residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgClock.PrgFloor.residual

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgClock.PrgClocked.prgDisc_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgClock.PrgClocked.prgDisc_bind

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgClock.PrgClocked.floor_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgClock.PrgClocked.floor_bind

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgClock.prgClocked_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgClock.prgClocked_check

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgClock.prg_check_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgClock.prg_check_clock

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgClock.prgClocked_batchPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgClock.prgClocked_batchPrefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgClock.prg_prefix_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgClock.prg_prefix_clock

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgClock.held_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgClock.held_term

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrgClock.check_prg_floor_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckPrgClock.check_prg_floor_label
