import ThresholdLeanXmssSecurity.Proof.TreeLockstepReach

/-!
# The round schedule of one operator

`TreeLockstepSegmentsGoal` (`TreeLockstepReach`) needs the position of the program of each honest
operator after `n` exchanges. This file gives the exact exchange count of each sub-protocol and
the exchange index of each salt read.

* `TreeSegmentRun S j n p` states that the program `p` starts after exchange `j` and makes exactly
  the exchanges up to `n`, unless it aborts. Each salt read `Rand(ρ, 2)` after exchange `j'` and
  before the next exchange satisfies `S j'`. `TreeExactExchanges n p` is the form with no
  condition on the salts. `TreeSegmentsFrom S j p` is the same with no end.
* The exact counts are `treeSegmentRun_reshare` (1), `treeSegmentRun_collector` (2),
  `treeSegmentRun_mult` (`mode.rounds` for every operator, the collector or not),
  `treeSegmentRun_openSh`, `treeSegmentRun_coin`, `treeSegmentRun_extendMult`,
  `treeSegmentRun_compareDigests`, `treeSegmentRun_challenge` and `treeSegmentRun_openRep` (1 each),
  and `treeSegmentRun_prssRandomness` (0).
* `treeSegmentRun_check` counts `checkLabels` exchanges. Its only salt reads come after
  `2 * halvings + 2` exchanges at the label `2 * halvings + 3`. A check of no tuple returns at once.
* `treeSegmentRun_ceremonyBatch` counts `batchRounds`, and `treeSegmentRun_batches` gives the
  schedule `LockstepSchedule` of a list of chunks. The salts of batch `k` come after exchange
  `lockstepSaltRound k`.
* `treeSegmentsFrom_ceremonyAfterSetup` gives the schedule of the program after the PRSS setup.
  Each read follows the schedule of some encoding (`CeremonySchedule`). The proof of the second
  run holds the fixed encoding that the operator computes, and `CeremonySchedule` forgets it.
* `segments_reach` carries the schedule to every reachable configuration after `n` rounds. Each
  honest step follows its schedule from exchange `n + 1`, and each honest salt read of the log
  after the setup comes from an exchange index of at most `n`. `treeSetup_noSalt` and
  `treeSimCommonPrefix_noSalt` show that the log before holds no honest salt read.
* `treeLockstepSegmentsGoal_of_encoding` proves `TreeLockstepSegmentsGoal` from
  `TreeLockstepEncodingGoal`, with the keys from `treeSetup_phase_agree`.

`TreeLockstepEncodingGoal` asks that the honest operators agree on the encoding of
the second run, also on aborted prefixes. It restates the schedule of `segments_reach` for one
encoding. The agreement of two operators is not a fact of one operator. A proof first keeps the
encoding of each operator in its schedule, in place of `CeremonySchedule`. It then needs the agreement on the opened
outputs of the first run (`TreeLockstepOpenedGoal` covers complete outputs only), and that the
encoding is a function of these outputs and the cache (`treeLockstepBottomEncoding`).
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

section Schedule

/-- A salt read `Rand(ρ, 2)` of term `T` with `key` at label `ρ` satisfies `S T key ρ`. -/
def SaltRead (S : C.Term → HashOutput → ℕ → Prop) (x : PrgInput C) : Prop :=
  ∀ T key label g, x = (.term T, key, label, 2, g) → S T key label

/-- The program starts after exchange `j` and makes exactly the exchanges up to `n`, unless it
aborts. Each salt read after exchange `j'` and before the next exchange satisfies `S j'`. -/
inductive TreeSegmentRun {α : Type} (S : ℕ → C.Term → HashOutput → ℕ → Prop) :
    ℕ → ℕ → OracleComp (PartySpec C E RealSpec) (Option α) → Prop
  | abort (j n : ℕ) : TreeSegmentRun S j n (pure none)
  | done (j : ℕ) (a : α) : TreeSegmentRun S j j (pure (some a))
  | queryLocal (j n : ℕ) (q : (LocalSpec C).Domain)
      (k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) (Option α))
      (hq : ∀ x, q = .inr (.inr x) → SaltRead (S j) x) (h : ∀ r, TreeSegmentRun S j n (k r)) :
      TreeSegmentRun S j n (.roll (.inl (.inl q)) k)
  | round (j n : ℕ) (out : Mail C E)
      (k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α))
      (h : ∀ r, TreeSegmentRun S (j + 1) n (k r)) :
      TreeSegmentRun S j n (.roll (.inl (.inr out)) k)

/-- The program makes exactly `n` exchanges, unless it aborts. -/
def TreeExactExchanges {α : Type} (n : ℕ) (p : OracleComp (PartySpec C E RealSpec) (Option α)) :
    Prop :=
  TreeSegmentRun (fun _ _ _ _ => True) 0 n p

/-- The program starts after exchange `j`. Each salt read after exchange `j'` and before the next
exchange satisfies `S j'`. -/
inductive TreeSegmentsFrom {α : Type} (S : ℕ → C.Term → HashOutput → ℕ → Prop) :
    ℕ → OracleComp (PartySpec C E RealSpec) (Option α) → Prop
  | pure (j : ℕ) (out : Option α) : TreeSegmentsFrom S j (pure out)
  | queryLocal (j : ℕ) (q : (LocalSpec C).Domain)
      (k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) (Option α))
      (hq : ∀ x, q = .inr (.inr x) → SaltRead (S j) x) (h : ∀ r, TreeSegmentsFrom S j (k r)) :
      TreeSegmentsFrom S j (.roll (.inl (.inl q)) k)
  | round (j : ℕ) (out : Mail C E)
      (k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α))
      (h : ∀ r, TreeSegmentsFrom S (j + 1) (k r)) :
      TreeSegmentsFrom S j (.roll (.inl (.inr out)) k)

variable {S : ℕ → C.Term → HashOutput → ℕ → Prop}

theorem TreeSegmentRun.from {α : Type} {j n : ℕ} {p : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : TreeSegmentRun S j n p) : TreeSegmentsFrom S j p := by
  induction h with
  | abort j n => exact .pure j none
  | done j a => exact .pure j (some a)
  | queryLocal j n q k hq h ih => exact .queryLocal j q k hq ih
  | round j n out k h ih => exact .round j out k ih

theorem TreeSegmentRun.bind {α β : Type} {j m n : ℕ}
    {p : PartyM C E RealSpec α} {k : α → PartyM C E RealSpec β}
    (hp : TreeSegmentRun S j m p.run)
    (hk : ∀ a, some a ∈ support p.run → TreeSegmentRun S m n (k a).run) :
    TreeSegmentRun S j n (p >>= k).run := by
  simp only [OptionT.run_bind, Option.elimM]
  change TreeSegmentRun S j n (p.run >>= fun a => a.elim (Pure.pure none) (fun a => (k a).run))
  generalize p.run = oa at hp hk ⊢
  induction hp with
  | abort j m => simpa only [pure_bind, Option.elim_none] using TreeSegmentRun.abort (S := S) j n
  | done j a => simpa only [pure_bind, Option.elim_some] using hk a (by simp)
  | queryLocal j m q f hq hf ih =>
    change TreeSegmentRun S j n (.roll (.inl (.inl q)) _)
    exact TreeSegmentRun.queryLocal j n q _ hq fun r => by
      simpa only [OracleComp.bind_def] using ih r fun a ha => hk a
        ((mem_support_bind_iff (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
          (.inl (.inl q)))) f _).mpr ⟨r, by simp; exact Set.mem_univ r, ha⟩)
  | round j m out f hf ih =>
    change TreeSegmentRun S j n (.roll (.inl (.inr out)) _)
    exact TreeSegmentRun.round j n out _ fun r => ih r fun a ha => hk a
      ((mem_support_bind_iff (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
        (.inl (.inr out)))) f _).mpr ⟨r, by simp; exact Set.mem_univ r, ha⟩)

theorem TreeSegmentRun.bind_from {α β : Type} {j m : ℕ}
    {p : PartyM C E RealSpec α} {k : α → PartyM C E RealSpec β}
    (hp : TreeSegmentRun S j m p.run)
    (hk : ∀ a, some a ∈ support p.run → TreeSegmentsFrom S m (k a).run) :
    TreeSegmentsFrom S j (p >>= k).run := by
  simp only [OptionT.run_bind, Option.elimM]
  change TreeSegmentsFrom S j (p.run >>= fun a => a.elim (Pure.pure none) (fun a => (k a).run))
  generalize p.run = oa at hp hk ⊢
  induction hp with
  | abort j m => simpa only [pure_bind, Option.elim_none] using TreeSegmentsFrom.pure (S := S) j none
  | done j a => simpa only [pure_bind, Option.elim_some] using hk a (by simp)
  | queryLocal j m q f hq hf ih =>
    change TreeSegmentsFrom S j (.roll (.inl (.inl q)) _)
    exact TreeSegmentsFrom.queryLocal j q _ hq fun r => by
      simpa only [OracleComp.bind_def] using ih r fun a ha => hk a
        ((mem_support_bind_iff (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
          (.inl (.inl q)))) f _).mpr ⟨r, by simp; exact Set.mem_univ r, ha⟩)
  | round j m out f hf ih =>
    change TreeSegmentsFrom S j (.roll (.inl (.inr out)) _)
    exact TreeSegmentsFrom.round j out _ fun r => ih r fun a ha => hk a
      ((mem_support_bind_iff (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
        (.inl (.inr out)))) f _).mpr ⟨r, by simp; exact Set.mem_univ r, ha⟩)

/-- A local computation whose salt reads satisfy `R`. It keeps every schedule of a continuation
whose segment admits `R`. -/
def LocalSalts {α : Type} (R : C.Term → HashOutput → ℕ → Prop) (oa : OracleComp (LocalSpec C) α) :
    Prop :=
  ∀ (E β : Type) (S : ℕ → C.Term → HashOutput → ℕ → Prop) (j n : ℕ) (k : α → PartyM C E RealSpec β),
    (∀ T key label, R T key label → S j T key label) →
      ((∀ a, TreeSegmentRun S j n (k a).run) → TreeSegmentRun S j n (localStep oa >>= k).run) ∧
      ((∀ a, TreeSegmentsFrom S j (k a).run) → TreeSegmentsFrom S j (localStep oa >>= k).run)

/-- A computation of `H` and `PRG` whose salt reads satisfy `R`. -/
def RoSalts {α : Type} (R : C.Term → HashOutput → ℕ → Prop) (oa : OracleComp (RoSpec C) α) : Prop :=
  LocalSalts R (liftComp oa (LocalSpec C))

theorem LocalSalts.pure {α : Type} (R : C.Term → HashOutput → ℕ → Prop) (a : α) :
    LocalSalts (C := C) R (Pure.pure a) := by
  intro E β S j n k _
  have : (localStep (Pure.pure a : OracleComp (LocalSpec C) α) >>= k : PartyM C E RealSpec β) = k a := by
    apply OptionT.ext
    simp [localStep]
  rw [this]
  exact ⟨fun hk => hk a, fun hk => hk a⟩

theorem LocalSalts.bind {α β : Type} {R : C.Term → HashOutput → ℕ → Prop}
    {oa : OracleComp (LocalSpec C) α} {f : α → OracleComp (LocalSpec C) β}
    (ha : LocalSalts R oa) (hf : ∀ a, LocalSalts R (f a)) : LocalSalts R (oa >>= f) := by
  intro E γ S j n k hR
  rw [localStep_bind_bind]
  exact ⟨fun hk => (ha E γ S j n _ hR).1 fun a => (hf a E γ S j n k hR).1 hk,
    fun hk => (ha E γ S j n _ hR).2 fun a => (hf a E γ S j n k hR).2 hk⟩

theorem LocalSalts.query {R : C.Term → HashOutput → ℕ → Prop} (q : (LocalSpec C).Domain)
    (hq : ∀ x, q = .inr (.inr x) → SaltRead R x) :
    LocalSalts R (OracleComp.lift (OracleSpec.query q)) := by
  intro E β S j n k hR
  have he : (localStep (OracleComp.lift (OracleSpec.query q)) >>= k).run =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>=
        fun a => (k a).run := by
    simp only [localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM,
      bind_assoc, pure_bind, Option.elim_some]
    change liftComp (OracleComp.lift (OracleSpec.query q)) (PartySpec C E RealSpec) >>=
      (fun a => (k a).run) = _
    simp only [liftComp_query]
    have hq' : ((OracleSpec.query q).cont <$> liftM (OracleSpec.query (OracleSpec.query q).input) :
        OracleComp (PartySpec C E RealSpec) _) =
        OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl q))) := by
      rw [← liftM_query_local]
      rfl
    rw [hq']
    rfl
  have hS : ∀ x, q = .inr (.inr x) → SaltRead (S j) x :=
    fun x hx T key label g he => hR T key label (hq x hx T key label g he)
  rw [he]
  exact ⟨fun hk => TreeSegmentRun.queryLocal j n q _ hS hk,
    fun hk => TreeSegmentsFrom.queryLocal j q _ hS hk⟩

theorem RoSalts.pure {α : Type} (R : C.Term → HashOutput → ℕ → Prop) (a : α) :
    RoSalts (C := C) R (Pure.pure a) := by
  unfold RoSalts
  rw [liftComp_pure]
  exact LocalSalts.pure R a

theorem RoSalts.bind {α β : Type} {R : C.Term → HashOutput → ℕ → Prop}
    {oa : OracleComp (RoSpec C) α} {f : α → OracleComp (RoSpec C) β}
    (ha : RoSalts R oa) (hf : ∀ a, RoSalts R (f a)) : RoSalts R (oa >>= f) := by
  unfold RoSalts
  rw [liftComp_bind]
  exact LocalSalts.bind ha hf

theorem RoSalts.query {R : C.Term → HashOutput → ℕ → Prop} (q : (RoSpec C).Domain)
    (hq : ∀ x, q = .inr x → SaltRead R x) :
    RoSalts R (OracleComp.lift (OracleSpec.query q)) := by
  unfold RoSalts
  rw [liftComp_query]
  have : ((OracleSpec.query q).cont <$> liftM (OracleSpec.query (OracleSpec.query q).input) :
      OracleComp (LocalSpec C) _) = OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr q)) := rfl
  rw [this]
  exact LocalSalts.query (.inr q) fun x he => hq x (by cases he; rfl)

theorem RoSalts.map {α β : Type} {R : C.Term → HashOutput → ℕ → Prop} {oa : OracleComp (RoSpec C) α}
    (f : α → β) (ha : RoSalts R oa) : RoSalts R (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact ha.bind fun _ => RoSalts.pure R _

theorem RoSalts.mapM {α β : Type} {R : C.Term → HashOutput → ℕ → Prop}
    (f : α → OracleComp (RoSpec C) β) (hf : ∀ a, RoSalts R (f a)) :
    ∀ xs : List α, RoSalts R (xs.mapM f)
  | [] => by simpa only [List.mapM_nil] using RoSalts.pure R []
  | x :: xs => by
    simp only [List.mapM_cons]
    exact (hf x).bind fun _ => (RoSalts.mapM f hf xs).bind fun _ => RoSalts.pure R _

theorem RoSalts.hashQuery (R : C.Term → HashOutput → ℕ → Prop) (q : Query C) :
    RoSalts R (hashQuery q) :=
  RoSalts.query (.inl q) fun x he => by cases he

theorem RoSalts.tweakable {α : Type} (R : C.Term → HashOutput → ℕ → Prop) (oa : OracleComp HashSpec α) :
    RoSalts (C := C) R (ThresholdLeanXmss.tweakable oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [ThresholdLeanXmss.tweakable, simulateQ_pure] using RoSalts.pure R a
  | query_bind q f ih =>
    simp only [ThresholdLeanXmss.tweakable, simulateQ_bind, simulateQ_spec_query] at ih ⊢
    exact (RoSalts.hashQuery R _).bind ih

theorem TreeSegmentRun.oracle_bind {α β : Type} {R : C.Term → HashOutput → ℕ → Prop} {j n : ℕ}
    {oa : OracleComp (RoSpec C) α} (ha : RoSalts R oa) (hR : ∀ T key label, R T key label → S j T key label)
    (k : α → PartyM C E RealSpec β) (hk : ∀ a, TreeSegmentRun S j n (k a).run) :
    TreeSegmentRun S j n (oracleStep oa >>= k).run :=
  (ha E β S j n k hR).1 hk

theorem TreeSegmentsFrom.oracle_bind {α β : Type} {R : C.Term → HashOutput → ℕ → Prop} {j : ℕ}
    {oa : OracleComp (RoSpec C) α} (ha : RoSalts R oa) (hR : ∀ T key label, R T key label → S j T key label)
    (k : α → PartyM C E RealSpec β) (hk : ∀ a, TreeSegmentsFrom S j (k a).run) :
    TreeSegmentsFrom S j (oracleStep oa >>= k).run :=
  (ha E β S j 0 k hR).2 hk

/-- A computation with no salt read. -/
abbrev RoNoSalt {α : Type} (oa : OracleComp (RoSpec C) α) : Prop := RoSalts (fun _ _ _ => False) oa

theorem TreeSegmentRun.pure {α : Type} (j : ℕ) (a : α) :
    TreeSegmentRun S j j (Pure.pure a : PartyM C E RealSpec α).run := by
  simpa only [OptionT.run_pure] using TreeSegmentRun.done (S := S) j a

theorem TreeSegmentRun.require_bind {α : Type} {j n : ℕ} (P : Prop)
    (k : Unit → PartyM C E RealSpec α) (hk : TreeSegmentRun S j n (k ()).run) :
    TreeSegmentRun S j n (require P >>= k).run := by
  by_cases hP : P
  · simpa only [require, if_pos hP, pure_bind] using hk
  · simp only [require, if_neg hP, failure_bind]
    exact TreeSegmentRun.abort j n

theorem TreeSegmentRun.failure {α : Type} (j n : ℕ) :
    TreeSegmentRun S j n (failure : PartyM C E RealSpec α).run := by
  simpa only [OptionT.run_failure] using TreeSegmentRun.abort (S := S) j n

set_option backward.isDefEq.respectTransparency false in
theorem TreeSegmentRun.exchange_bind {α : Type} {j n : ℕ} (out : Mail C E)
    (k : Mail C E → PartyM C E RealSpec α) (hk : ∀ inbox, TreeSegmentRun S (j + 1) n (k inbox).run) :
    TreeSegmentRun S j n (exchange out >>= k).run := by
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
  apply TreeSegmentRun.round
  intro inbox
  change TreeSegmentRun S (j + 1) n (exchangeResume k inbox)
  unfold exchangeResume
  split_ifs
  · exact TreeSegmentRun.abort _ n
  · simpa only [OptionT.run_pure, pure_bind, Option.elim_some] using hk inbox

theorem TreeSegmentRun.state_bind {σ α β : Type} {j m n : ℕ}
    {p : StateT σ (PartyM C E RealSpec) α} {k : α → StateT σ (PartyM C E RealSpec) β} {s : σ}
    (hp : TreeSegmentRun S j m (p.run s).run)
    (hk : ∀ a s', some (a, s') ∈ support (p.run s).run → TreeSegmentRun S m n ((k a).run s').run) :
    TreeSegmentRun S j n ((p >>= k).run s).run := by
  rw [StateT.run_bind]
  exact hp.bind fun a ha => hk a.1 a.2 ha

theorem TreeSegmentRun.lift {σ α : Type} {j n : ℕ} {p : PartyM C E RealSpec α}
    (hp : TreeSegmentRun S j n p.run) (s : σ) :
    TreeSegmentRun S j n ((StateT.lift p : StateT σ (PartyM C E RealSpec) α).run s).run := by
  rw [StateT.run_lift]
  exact hp.bind fun _ _ => TreeSegmentRun.pure n _

theorem TreeSegmentRun.foldlM {σ α β : Type} (step : ℕ) (f : α → β → StateT σ (PartyM C E RealSpec) α)
    (hf : ∀ j a b s, TreeSegmentRun S j (j + step) ((f a b).run s).run) :
    ∀ (xs : List β) (j : ℕ) (a : α) (s : σ),
      TreeSegmentRun S j (j + xs.length * step) ((xs.foldlM f a).run s).run
  | [], j, a, s => by
    simpa only [List.foldlM_nil, List.length_nil, Nat.zero_mul, Nat.add_zero, StateT.run_pure]
      using TreeSegmentRun.pure (S := S) j (a, s)
  | b :: xs, j, a, s => by
    simp only [List.foldlM_cons, List.length_cons]
    refine TreeSegmentRun.state_bind (hf j a b s) fun a' s' _ => ?_
    have := TreeSegmentRun.foldlM step f hf xs (j + step) a' s'
    rwa [show j + step + xs.length * step = j + (xs.length + 1) * step by ring] at this

theorem TreeSegmentRun.mono {α : Type} {S' : ℕ → C.Term → HashOutput → ℕ → Prop} {j n : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : TreeSegmentRun S j n p)
    (hS : ∀ j T key label, S j T key label → S' j T key label) : TreeSegmentRun S' j n p := by
  induction h with
  | abort j n => exact .abort j n
  | done j a => exact .done j a
  | queryLocal j n q k hq h ih =>
    exact .queryLocal j n q k (fun x hx T key label g he => hS j T key label (hq x hx T key label g he)) ih
  | round j n out k h ih => exact .round j n out k ih

theorem TreeSegmentsFrom.bind_pure {α β : Type} {j : ℕ}
    {p : PartyM C E RealSpec α} {k : α → PartyM C E RealSpec β}
    (hp : TreeSegmentsFrom S j p.run) (hk : ∀ a, ∃ o, (k a).run = Pure.pure o) :
    TreeSegmentsFrom S j (p >>= k).run := by
  simp only [OptionT.run_bind, Option.elimM]
  change TreeSegmentsFrom S j (p.run >>= fun a => a.elim (Pure.pure none) (fun a => (k a).run))
  generalize p.run = oa at hp ⊢
  induction hp with
  | pure j out =>
    rcases out with _ | a
    · simpa only [pure_bind, Option.elim_none] using TreeSegmentsFrom.pure (S := S) j none
    · obtain ⟨o, ho⟩ := hk a
      simpa only [pure_bind, Option.elim_some, ho] using TreeSegmentsFrom.pure (S := S) j o
  | queryLocal j q f hq hf ih =>
    change TreeSegmentsFrom S j (.roll (.inl (.inl q)) _)
    exact TreeSegmentsFrom.queryLocal j q _ hq fun r => by
      simpa only [OracleComp.bind_def] using ih r
  | round j out f hf ih =>
    change TreeSegmentsFrom S j (.roll (.inl (.inr out)) _)
    exact TreeSegmentsFrom.round j out _ ih

theorem TreeSegmentRun.state_bind_from {σ α β : Type} {j m : ℕ}
    {p : StateT σ (PartyM C E RealSpec) α} {k : α → StateT σ (PartyM C E RealSpec) β} {s : σ}
    (hp : TreeSegmentRun S j m (p.run s).run)
    (hk : ∀ a s', some (a, s') ∈ support (p.run s).run → TreeSegmentsFrom S m ((k a).run s').run) :
    TreeSegmentsFrom S j ((p >>= k).run s).run := by
  rw [StateT.run_bind]
  exact hp.bind_from fun a ha => hk a.1 a.2 ha

end Schedule

section Programs

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
variable {S : ℕ → C.Term → HashOutput → ℕ → Prop}

/-- The salt reads of a draw of `PRG(key, ρ, idx)` under `name`. -/
def DrawSalts (R : C.Term → HashOutput → ℕ → Prop) (name : KeyName C) (key : HashOutput) (ρ idx : ℕ) :
    Prop :=
  ∀ T, name = .term T → idx = 2 → R T key ρ

theorem roSalts_prgBits {R : C.Term → HashOutput → ℕ → Prop} (name : KeyName C) (key : HashOutput)
    (ρ idx count : ℕ) (h : DrawSalts R name key ρ idx) : RoSalts R (prgBits name key ρ idx count) := by
  unfold prgBits
  refine (RoSalts.mapM _ (fun position => ?_) _).bind fun _ => RoSalts.pure R _
  refine RoSalts.query (.inr (name, key, ρ, idx, position)) fun x he T key' label g hx => ?_
  cases he
  simp only [Prod.mk.injEq] at hx
  obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hx
  exact h T rfl rfl

theorem roSalts_draw_bit {R : C.Term → HashOutput → ℕ → Prop} (name : KeyName C) (key : HashOutput)
    (ρ idx count : ℕ) (h : DrawSalts R name key ρ idx) :
    RoSalts R ((bitCodec (C := C) (E := E)).draw name key ρ idx count) :=
  roSalts_prgBits name key ρ idx count h

theorem roSalts_draw_element {R : C.Term → HashOutput → ℕ → Prop} (name : KeyName C) (key : HashOutput)
    (ρ idx count : ℕ) (h : DrawSalts R name key ρ idx) :
    RoSalts R ((elementCodec K).draw name key ρ idx count) :=
  (roSalts_prgBits name key ρ idx _ h).bind fun _ => RoSalts.pure R _

/-- The salt reads of the PRSS draws of round `ρ` are the held terms with their keys. -/
theorem roSalts_prssDraw {R : C.Term → HashOutput → ℕ → Prop} {Rr : Type} [Zero Rr] (ctx : Context C)
    (codec : Codec C E Rr)
    (hcodec : ∀ name key ρ idx count, DrawSalts R name key ρ idx → RoSalts R (codec.draw name key ρ idx count))
    (ρ idx count : ℕ) (h : idx = 2 → ∀ T, ctx.self ∈ C.holders T → R T (ctx.prss.term T) ρ) :
    RoSalts R (prssDraw ctx codec ρ idx count) := by
  unfold prssDraw termDraws pairDraws
  refine (RoSalts.mapM _ (fun T => ?_) _).bind fun _ =>
    (RoSalts.mapM _ (fun j => ?_) _).bind fun _ => RoSalts.pure R _
  · split_ifs with hT
    · exact hcodec _ _ _ _ _ fun T' he hidx => by cases he; exact h hidx T hT
    · exact RoSalts.pure R _
  · split_ifs
    · exact RoSalts.pure R _
    · exact hcodec _ _ _ _ _ fun T' he => by cases he

theorem bitCodec_salts {R : C.Term → HashOutput → ℕ → Prop} :
    ∀ name key ρ idx count, DrawSalts R name key ρ idx →
      RoSalts R ((bitCodec (C := C) (E := E)).draw name key ρ idx count) :=
  fun name key ρ idx count h => roSalts_draw_bit name key ρ idx count h

theorem elementCodec_salts {R : C.Term → HashOutput → ℕ → Prop} :
    ∀ name key ρ idx count, DrawSalts R name key ρ idx → RoSalts R ((elementCodec K).draw name key ρ idx count) :=
  fun name key ρ idx count h => roSalts_draw_element K name key ρ idx count h

/-- `prssRandomness` makes no exchange. Its salt reads are the held terms at the current label. -/
theorem treeSegmentRun_prssRandomness {Rr : Type} [Zero Rr] (ctx : Context C) (codec : Codec C E Rr)
    (hcodec : ∀ R name key ρ idx count, DrawSalts R name key ρ idx →
      RoSalts R (codec.draw name key ρ idx count))
    (idx count j : ℕ) (st : RunState C)
    (h : idx = 2 → ∀ T, ctx.self ∈ C.holders T → S j T (ctx.prss.term T) st.label) :
    TreeSegmentRun S j j ((prssRandomness (G := RealSpec) ctx codec idx count).run st).run := by
  have hr := prssRandomness_run (G := RealSpec) ctx codec idx count pure st
  rw [bind_pure] at hr
  rw [hr]
  exact TreeSegmentRun.oracle_bind
    (roSalts_prssDraw ctx codec (hcodec _) st.label idx count h) (fun _ _ _ h => h) _
    fun _ => TreeSegmentRun.pure j _

theorem treeSegmentRun_reshare {Rr : Type} [Field Rr] (ctx : Context C) (codec : Codec C E Rr)
    (rnd : PrssOutput C Rr) (v : ℕ → Rr) (count j : ℕ) (st : RunState C) :
    TreeSegmentRun S j (j + 1) ((reshare (G := RealSpec) K ctx codec rnd v count).run st).run := by
  rw [show rnd = (rnd.1, rnd.2) from rfl, reshare_run]
  exact TreeSegmentRun.exchange_bind _ _ fun _ => TreeSegmentRun.pure _ _

theorem treeSegmentRun_collector (ctx : Context C) (rnd : PrssOutput C Bit) (v : ℕ → Bit) (count j : ℕ)
    (st : RunState C) :
    TreeSegmentRun S j (j + 2) ((reshareCollector (G := RealSpec) K ctx rnd v count).run st).run := by
  rw [show rnd = (rnd.1, rnd.2) from rfl, reshareCollector_run]
  exact TreeSegmentRun.exchange_bind _ _ fun _ => TreeSegmentRun.exchange_bind _ _ fun _ =>
    TreeSegmentRun.pure _ _

/-- A multiplication makes `mode.rounds` exchanges for every operator, the collector or not. -/
theorem treeSegmentRun_mult (ctx : Context C) (mode : ReshareMode) (x y : Shares C Bit) (count j : ℕ)
    (st : RunState C) :
    TreeSegmentRun S j (j + mode.rounds)
      ((((realRunGadgets (G := RealSpec) K ctx mode).mult x y count).run st).run) := by
  change TreeSegmentRun S j (j + mode.rounds)
    (((prssRandomness ctx bitCodec 0 count >>= fun rnd =>
      reshareWith K ctx mode rnd (mulRep K ctx x y) count).run st).run)
  rw [prssRandomness_run]
  refine TreeSegmentRun.oracle_bind (roSalts_prssDraw ctx bitCodec bitCodec_salts _ 0 count
    (R := fun _ _ _ => False) (by omega)) (fun _ _ _ h => h.elim) _ fun rnd => ?_
  cases mode with
  | peer => exact treeSegmentRun_reshare K ctx bitCodec rnd _ count j _
  | collector => exact treeSegmentRun_collector K ctx rnd _ count j _

theorem treeSegmentRun_rerand (ctx : Context C) (mode : ReshareMode) (v : Shares C Bit) (count j : ℕ)
    (st : RunState C) :
    TreeSegmentRun S j (j + 1) ((((realRunGadgets (G := RealSpec) K ctx mode).rerand v count).run st).run) := by
  change TreeSegmentRun S j (j + 1)
    (((prssRandomness ctx bitCodec 0 count >>= fun rnd =>
      reshare K ctx bitCodec rnd (ownerSum K ctx v) count).run st).run)
  rw [prssRandomness_run]
  exact TreeSegmentRun.oracle_bind (roSalts_prssDraw ctx bitCodec bitCodec_salts _ 0 count
    (R := fun _ _ _ => False) (by omega)) (fun _ _ _ h => h.elim) _ fun rnd =>
    treeSegmentRun_reshare K ctx bitCodec rnd _ count j _

theorem treeSegmentRun_openSh (ctx : Context C) (v : ℕ → E) (count j : ℕ) :
    TreeSegmentRun S j (j + 1) (openSh (G := RealSpec) K ctx v count).run := by
  unfold openSh
  exact TreeSegmentRun.exchange_bind _ _ fun _ =>
    TreeSegmentRun.require_bind _ _ (TreeSegmentRun.pure _ _)

theorem treeSegmentRun_coin (ctx : Context C) (count j : ℕ) (st : RunState C) :
    TreeSegmentRun S j (j + 1) ((((realCheckGadgets (G := RealSpec) K ctx).coin count).run st).run) := by
  change TreeSegmentRun S j (j + 1) ((prssRandomness ctx (elementCodec K) 1 count >>= fun o =>
    coinWith K ctx o count).run st).run
  rw [prssRandomness_run]
  refine TreeSegmentRun.oracle_bind (roSalts_prssDraw ctx (elementCodec K) (elementCodec_salts K) _ 1 count
    (R := fun _ _ _ => False) (by omega)) (fun _ _ _ h => h.elim) _ fun o => ?_
  unfold coinWith
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  exact (treeSegmentRun_openSh K ctx _ count j).bind fun _ _ => TreeSegmentRun.pure _ _

theorem treeSegmentRun_oracleStep {σ α : Type} {oa : OracleComp (RoSpec C) α} (ha : RoNoSalt oa) (j : ℕ)
    (s : σ) :
    TreeSegmentRun S j j ((StateT.lift (oracleStep oa) : StateT σ (PartyM C E RealSpec) α).run s).run := by
  refine TreeSegmentRun.lift ?_ s
  rw [← bind_pure (oracleStep oa)]
  exact TreeSegmentRun.oracle_bind ha (fun _ _ _ h => h.elim) _ fun _ => TreeSegmentRun.pure j _

theorem treeSegmentRun_coinKey (ctx : Context C) (j : ℕ) (st : RunState C) :
    TreeSegmentRun S j (j + 1) ((coinKey K (realCheckGadgets (G := RealSpec) K ctx)).run st).run := by
  simp only [coinKey, StateT.run_bind, StateT.run_get, pure_bind]
  exact (treeSegmentRun_coin K ctx 1 j st).bind fun _ _ =>
    treeSegmentRun_oracleStep (RoSalts.hashQuery _ _) _ _

theorem roNoSalt_findChallenge (key : HashOutput) :
    ∀ tries index, RoNoSalt (findChallenge K key tries index)
  | 0, _ => RoSalts.pure _ _
  | tries + 1, index => by
    unfold findChallenge
    refine (RoSalts.hashQuery _ _).bind fun r => ?_
    dsimp only
    split
    · exact RoSalts.pure _ _
    · exact roNoSalt_findChallenge key tries (index + 1)

theorem treeSegmentRun_challenge (ctx : Context C) (j : ℕ) (st : RunState C) :
    TreeSegmentRun S j (j + 1) ((challenge K (realCheckGadgets (G := RealSpec) K ctx)).run st).run := by
  unfold challenge
  refine TreeSegmentRun.state_bind (treeSegmentRun_coinKey K ctx j st) fun key s _ => ?_
  refine TreeSegmentRun.state_bind (treeSegmentRun_oracleStep (roNoSalt_findChallenge K key _ _) _ s)
    fun r s' _ => ?_
  cases r with
  | none =>
    simp only [StateT.run_lift, failure_bind]
    exact TreeSegmentRun.failure _ _
  | some r => exact TreeSegmentRun.pure _ _

theorem treeSegmentRun_expand (key : HashOutput) (count j : ℕ) (st : RunState C) :
    TreeSegmentRun S j j ((expand (G := RealSpec) K key count).run st).run := by
  unfold expand
  exact treeSegmentRun_oracleStep
    (RoSalts.mapM _ (fun k => RoSalts.map _ (RoSalts.hashQuery _ _)) _) j st

theorem treeSegmentRun_extendMult (ctx : Context C) (products : List (Product C E)) (j : ℕ)
    (st : RunState C) :
    TreeSegmentRun S j (j + 1)
      ((((realCheckGadgets (G := RealSpec) K ctx).extendMult products).run st).run) := by
  change TreeSegmentRun S j (j + 1) ((prssRandomness ctx (elementCodec K) 0 products.length >>= fun rnd =>
    reshare K ctx (elementCodec K) rnd _ products.length).run st).run
  rw [prssRandomness_run]
  exact TreeSegmentRun.oracle_bind (roSalts_prssDraw ctx (elementCodec K) (elementCodec_salts K) _ 0 _
    (R := fun _ _ _ => False) (by omega)) (fun _ _ _ h => h.elim) _ fun rnd =>
    treeSegmentRun_reshare K ctx (elementCodec K) rnd _ _ j _

theorem treeSegmentRun_compareDigests (ctx : Context C) (salts : Shares C Bit) (j : ℕ) (st : RunState C) :
    TreeSegmentRun S j (j + 1) ((compareDigests (E := E) (G := RealSpec) ctx salts).run st).run := by
  rw [compareDigests_run]
  refine TreeSegmentRun.oracle_bind (R := fun _ _ _ => False) ?_ (fun _ _ _ h => h.elim) _ fun _ =>
    TreeSegmentRun.exchange_bind _ _ fun _ => TreeSegmentRun.require_bind _ _ (TreeSegmentRun.pure _ _)
  unfold digestQuery
  refine RoSalts.mapM _ (fun T => ?_) _
  split_ifs
  · exact (RoSalts.hashQuery _ _).bind fun _ => RoSalts.hashQuery _ _
  · exact RoSalts.pure _ _

theorem treeSegmentRun_openRep (ctx : Context C) (v : Shares C Bit) (count j : ℕ) :
    TreeSegmentRun S j (j + 1) (openRep (G := RealSpec) K ctx v count).run := by
  unfold openRep
  exact TreeSegmentRun.oracle_bind (R := fun _ _ _ => False)
    (RoSalts.mapM _ (fun _ => RoSalts.hashQuery _ _) _) (fun _ _ _ h => h.elim) _ fun _ =>
    TreeSegmentRun.exchange_bind _ _ fun _ => TreeSegmentRun.oracle_bind (R := fun _ _ _ => False)
      (RoSalts.mapM _ (fun _ => RoSalts.hashQuery _ _) _) (fun _ _ _ h => h.elim) _ fun _ =>
      TreeSegmentRun.require_bind _ _ (TreeSegmentRun.pure _ _)

end Programs

section Check

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
variable {S : ℕ → C.Term → HashOutput → ℕ → Prop}

theorem TreeSegmentRun.label_bind {α β : Type} {c j m n : ℕ} {p : RunM C E RealSpec α}
    {k : α → RunM C E RealSpec β} {st : RunState C} (hl : LockstepLabels c p)
    (hp : TreeSegmentRun S j m (p.run st).run)
    (hk : ∀ a s', s'.label = st.label + c → TreeSegmentRun S m n ((k a).run s').run) :
    TreeSegmentRun S j n ((p >>= k).run st).run :=
  TreeSegmentRun.state_bind hp fun a s' hmem => hk a s' (hl st a s' hmem)

/-- The check of `cnt` tuples makes `checkLabels cnt` exchanges. Its only salt reads are the draws
`Rand(ρ, 2)` of the held terms after `2 * halvings cnt + 2` exchanges, at the label
`2 * halvings cnt + 3` after its start. A check of no tuple returns at once. -/
theorem treeSegmentRun_check (ctx : Context C) (tuples : List (Tuple C)) (j : ℕ) (st : RunState C)
    (h : (tuples.map (·.count)).sum ≠ 0 → ∀ T, ctx.self ∈ C.holders T →
      S (j + 2 * halvings (tuples.map (·.count)).sum + 2) T (ctx.prss.term T)
        (st.label + 2 * halvings (tuples.map (·.count)).sum + 3)) :
    TreeSegmentRun S j (j + checkLabels (tuples.map (·.count)).sum)
      ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st).run := by
  have hs : sliceBits ≤ halvings (tuples.map (·.count)).sum := by
    unfold halvings
    omega
  unfold check
  dsimp only
  split_ifs with hzero
  · simp only [hzero, checkLabels, if_pos, Nat.add_zero]
    exact TreeSegmentRun.pure j _
  have hl : checkLabels (tuples.map (·.count)).sum = 2 * halvings (tuples.map (·.count)).sum + 5 := by
    unfold checkLabels
    rw [if_neg hzero]
  rw [hl]
  replace h := h hzero
  generalize halvings (tuples.map (·.count)).sum = m at hs h ⊢
  refine TreeSegmentRun.label_bind (c := 0) (LockstepLabels.pure _) (TreeSegmentRun.pure j _)
    fun _ s0 hs0 => ?_
  refine TreeSegmentRun.label_bind (lockstepLabels_coinKey K ctx) (treeSegmentRun_coinKey K ctx j s0)
    fun key s1 hs1 => ?_
  refine TreeSegmentRun.label_bind (LockstepLabels.lift _) (treeSegmentRun_expand K key _ _ s1)
    fun τ s2 hs2 => ?_
  refine TreeSegmentRun.label_bind (LockstepLabels.lift _)
    (TreeSegmentRun.lift (by
      rw [← bind_pure (require _)]
      exact TreeSegmentRun.require_bind _ _ (TreeSegmentRun.pure (j + 1) _)) s2)
    fun _ s3 hs3 => ?_
  refine TreeSegmentRun.label_bind
    (LockstepLabels.foldlM 2 _ (fun x b => (lockstepLabels_extendMult K ctx _).le_bind
      (fun t => (lockstepLabels_challenge K ctx).le_bind (fun r => LockstepLabels.pure _) rfl) rfl) _ _)
    (TreeSegmentRun.foldlM 2 _ (fun j' x b s => TreeSegmentRun.state_bind
      (treeSegmentRun_extendMult K ctx _ j' s) fun t s' _ => TreeSegmentRun.state_bind
        (treeSegmentRun_challenge K ctx (j' + 1) s') fun r s'' _ => TreeSegmentRun.pure _ _) _ _ _ s3)
    fun x s4 hs4 => ?_
  refine TreeSegmentRun.label_bind
    (LockstepLabels.foldlM 2 _ (fun x b => (lockstepLabels_extendMult K ctx _).le_bind
      (fun t => (lockstepLabels_challenge K ctx).le_bind (fun r => LockstepLabels.pure _) rfl) rfl) _ _)
    (TreeSegmentRun.foldlM 2 _ (fun j' x b s => TreeSegmentRun.state_bind
      (treeSegmentRun_extendMult K ctx _ j' s) fun t s' _ => TreeSegmentRun.state_bind
        (treeSegmentRun_challenge K ctx (j' + 1) s') fun r s'' _ => TreeSegmentRun.pure _ _) _ _ _ s4)
    fun y s5 hs5 => ?_
  refine TreeSegmentRun.label_bind (lockstepLabels_prssRandomness ctx _ _ _)
    (treeSegmentRun_prssRandomness ctx (elementCodec K) (fun _ => elementCodec_salts K) 1 2 _ s5
      (by omega)) fun w s6 hs6 => ?_
  refine TreeSegmentRun.label_bind (lockstepLabels_extendMult K ctx _)
    (treeSegmentRun_extendMult K ctx _ _ s6) fun q s7 hs7 => ?_
  have hj : j + 1 + (List.range sliceBits).length * 2 + (List.range (m - sliceBits)).length * 2 + 1 =
      j + 2 * m + 2 := by
    simp only [List.length_range]
    omega
  have hlabel : s7.label = st.label + 2 * m + 3 := by
    simp only [List.length_range] at hs4 hs5
    omega
  refine TreeSegmentRun.label_bind (lockstepLabels_prssRandomness ctx _ _ _)
    (treeSegmentRun_prssRandomness ctx bitCodec (fun _ => bitCodec_salts) 2 256 _ s7
      (fun _ T hT => by rw [hj, hlabel]; exact h T hT)) fun salts s8 _ => ?_
  refine TreeSegmentRun.state_bind (treeSegmentRun_compareDigests ctx _ _ s8) fun _ s9 _ => ?_
  refine TreeSegmentRun.state_bind (treeSegmentRun_challenge K ctx _ s9) fun r s10 _ => ?_
  refine TreeSegmentRun.state_bind (TreeSegmentRun.lift (treeSegmentRun_openSh K ctx _ 3 _) s10)
    fun opened s11 _ => ?_
  rw [hj, show j + 2 * m + 2 + 1 + 1 + 1 = j + (2 * m + 5) by omega]
  refine TreeSegmentRun.lift ?_ s11
  rw [← bind_pure (require _)]
  exact TreeSegmentRun.require_bind _ _ (TreeSegmentRun.pure _ _)

end Check

section Batch

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (circuits : Circuits) (settings : Settings)
variable {S : ℕ → C.Term → HashOutput → ℕ → Prop}

theorem TreeSegmentRun.map {α β : Type} {j n : ℕ} (f : α → β) {p : PartyM C E RealSpec α}
    (hp : TreeSegmentRun S j n p.run) : TreeSegmentRun S j n (f <$> p).run := by
  rw [map_eq_bind_pure_comp]
  exact hp.bind fun _ _ => TreeSegmentRun.pure n _

theorem treeSegmentRun_inputs {α : Type} (ctx : Context C) (j n : ℕ) (jobs : List Job)
    (k : List (C.Term → List Bit) → PartyM C E RealSpec α)
    (hk : ∀ inputs, TreeSegmentRun S j n (k inputs).run) :
    TreeSegmentRun S j n (jobs.mapM (inputShares ctx) >>= k).run := by
  induction jobs generalizing k with
  | nil => simpa only [List.mapM_nil, pure_bind] using hk []
  | cons job jobs ih =>
    simp only [List.mapM_cons, bind_assoc, inputShares, pure_bind]
    refine TreeSegmentRun.oracle_bind (R := fun _ _ _ => False) ?_ (fun _ _ _ h => h.elim) _
      fun terms => ih _ fun inputs => hk _
    refine RoSalts.mapM _ (fun T => ?_) _
    split_ifs
    · have loop : ∀ (ys : List Point) (acc : List (List Bit)), RoNoSalt (C := C)
          (List.flatMapM.loop (fun x => bitsOfDigest <$> prf (ctx.keys.seed T) x) ys acc) := by
        intro ys
        induction ys with
        | nil => intro acc; exact RoSalts.pure _ _
        | cons y ys ih => intro acc; exact (((RoSalts.hashQuery _ _).map _).map _).bind fun _ => ih _
      exact loop _ []
    · exact RoSalts.pure _ _

theorem treeSegmentRun_beforeVerify (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) (j : ℕ) (st : RunState C) :
    TreeSegmentRun S j (j + depth jobs * mode.rounds + 1)
      ((treeSimCheckBeforeVerify K ctx mode jobs inputs).run st).run := by
  unfold treeSimCheckBeforeVerify
  refine TreeSegmentRun.state_bind (TreeSegmentRun.foldlM mode.rounds _ (fun j' p l s => by
    unfold layerBody
    exact TreeSegmentRun.state_bind (treeSegmentRun_mult K ctx mode _ _ _ j' s) fun _ _ _ =>
      TreeSegmentRun.pure _ _) _ j _ st) fun p s _ => ?_
  simp only [List.length_range]
  exact TreeSegmentRun.state_bind (treeSegmentRun_rerand K ctx mode _ _ _ s) fun _ _ _ =>
    TreeSegmentRun.pure _ _

/-- A batch makes exactly `batchRounds` exchanges. Its only salt reads are the draws of the held
terms in its check, after `depth * mode.rounds + 1 + 2 * halvings + 2` exchanges and at the label
`depth + 1 + 2 * halvings + 3` after its start. -/
theorem treeSegmentRun_ceremonyBatch (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) (j : ℕ)
    (h : batchCount circuits ctx.keys.parameter jobs ≠ 0 → ∀ T, ctx.self ∈ C.holders T →
      S (j + depth (jobs.map (circuits ctx.keys.parameter ·.kind)) * settings.mode.rounds + 1 +
          2 * halvings (batchCount circuits ctx.keys.parameter jobs) + 2) T (ctx.prss.term T)
        (initial.1 + depth (jobs.map (circuits ctx.keys.parameter ·.kind)) + 1 +
          2 * halvings (batchCount circuits ctx.keys.parameter jobs) + 3)) :
    TreeSegmentRun S j (j + batchRounds circuits settings.mode ctx.keys.parameter jobs)
      ((ceremonyBatch K circuits settings ctx jobs : StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run
        initial).run := by
  rw [← treeSimCheckBatchAudit_erase K circuits settings ctx jobs]
  change TreeSegmentRun S _ _ ((Prod.fst <$> (treeSimCheckBatchAudit K circuits settings ctx jobs).run).run
    initial).run
  rw [StateT.run_map, treeSimCheckBatchAudit_run_prefix]
  apply TreeSegmentRun.map
  have hprefix : TreeSegmentRun S j
      (j + depth (jobs.map (circuits ctx.keys.parameter ·.kind)) * settings.mode.rounds + 1)
      (treeSimCheckBatchPrefix K circuits settings ctx jobs initial).run := by
    unfold treeSimCheckBatchPrefix
    exact treeSegmentRun_inputs ctx _ _ jobs _ fun inputs =>
      (treeSegmentRun_beforeVerify K ctx settings.mode _ inputs j _).bind fun _ _ =>
        TreeSegmentRun.pure _ _
  refine hprefix.bind fun a ha => ?_
  obtain ⟨-, hlabel, -, -, -⟩ := treeSimCheckBatchPrefix_state K circuits settings ctx jobs initial a ha
  have hcount : (a.2.1.2.map (·.count)).sum = batchCount circuits ctx.keys.parameter jobs := by
    simp only [treeSimCheckBatchPrefix, OptionT.run_bind, Option.elimM] at ha
    obtain ⟨x, _, hx⟩ := (mem_support_bind_iff _ _ _).mp ha
    cases x with
    | none => simp at hx
    | some inputs =>
      obtain ⟨y, hy, hxy⟩ := (mem_support_bind_iff _ _ _).mp hx
      cases y with
      | none => simp at hxy
      | some q =>
        simp only [Option.elim_some, OptionT.run_pure, support_pure, Set.mem_singleton_iff,
          Option.some.injEq] at hxy
        subst a
        exact treeSimCheckBeforeVerify_count K ctx settings.mode _ inputs initial.1 initial.2
          q.1 q.2 hy
  unfold treeSimCheckBatchFinish treeSimCheckAfterVerify
  refine TreeSegmentRun.bind (TreeSegmentRun.bind (treeSegmentRun_check K ctx a.2.1.2 _ a.2.2 ?_)
    fun x _ => ?_) fun _ _ => TreeSegmentRun.pure _ _
  · intro hc T hT
    rw [hcount, hlabel]
    rw [hcount] at hc
    exact h hc T hT
  · obtain ⟨fst, final⟩ := x
    refine (treeSegmentRun_openRep K ctx _ _ _).bind fun _ _ => ?_
    rw [hcount]
    unfold batchRounds
    rw [show j + (depth (jobs.map (circuits ctx.keys.parameter ·.kind)) * settings.mode.rounds + 1 +
      checkLabels (batchCount circuits ctx.keys.parameter jobs) + 1) =
      j + depth (jobs.map (circuits ctx.keys.parameter ·.kind)) * settings.mode.rounds + 1 +
      checkLabels (batchCount circuits ctx.keys.parameter jobs) + 1 by ring]
    exact TreeSegmentRun.pure _ _

/-- A batch moves the label by `batchLabels` and the tag by one. -/
theorem ceremonyBatch_state (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (v : Option (List (List Bit))) (final : ℕ × ℕ)
    (h : some (v, final) ∈ support ((ceremonyBatch K circuits settings ctx jobs :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run initial).run) :
    final = (initial.1 + batchLabels circuits ctx.keys.parameter jobs, initial.2 + 1) := by
  rw [← treeSimCheckBatchAudit_erase K circuits settings ctx jobs] at h
  change some (v, final) ∈ support ((Prod.fst <$> (treeSimCheckBatchAudit K circuits settings ctx jobs).run).run
    initial).run at h
  rw [StateT.run_map, OptionT.run_map, support_map] at h
  obtain ⟨o, hmem, he⟩ := h
  rcases o with _ | ⟨⟨v', records⟩, final'⟩
  · simp at he
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  obtain ⟨_, _, _, _, hf⟩ := lockstep_batchAudit circuits K settings ctx jobs initial _ _ _ hmem
  exact hf

/-- A batch makes exactly `batchRounds` exchanges, unless it aborts. -/
theorem treeExactExchanges_ceremonyBatch (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    TreeExactExchanges (batchRounds circuits settings.mode ctx.keys.parameter jobs)
      ((ceremonyBatch K circuits settings ctx jobs : StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run
        initial).run := by
  have h := treeSegmentRun_ceremonyBatch (S := fun _ _ _ _ => True) K circuits settings ctx jobs initial 0
    fun _ _ _ => trivial
  rwa [Nat.zero_add] at h

end Batch

section Ceremony

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)
  (circuits : Circuits) (settings : Settings)

/-- The exchange index at the start of batch `k` of the chunks `js`. -/
def lockstepRoundStart (mode : ReshareMode) (parameter : PublicParameter) (js : List (List Job))
    (k : ℕ) : ℕ :=
  ((js.take k).map (batchRounds circuits mode parameter)).sum

/-- The exchange index of the salt reads of the check of batch `k`. -/
def lockstepSaltRound (mode : ReshareMode) (parameter : PublicParameter) (js : List (List Job))
    (k : ℕ) : ℕ :=
  lockstepRoundStart circuits mode parameter js k +
    depth ((js.getD k []).map (circuits parameter ·.kind)) * mode.rounds + 1 +
    2 * halvings (batchCount circuits parameter (js.getD k [])) + 2

/-- The salt reads of an operator `self` with the term keys `keys` that runs the chunks `js`. Each
read after exchange `j` is a held term with its key, at the salt label of a checked batch `k`
whose salts come after exchange `j`. -/
def LockstepSchedule (mode : ReshareMode) (parameter : PublicParameter) (keys : C.Term → HashOutput)
    (self : C.Party) (js : List (List Job)) (j : ℕ) (T : C.Term) (key : HashOutput) (label : ℕ) :
    Prop :=
  key = keys T ∧ self ∈ C.holders T ∧ ∃ k, k < js.length ∧
    batchCount circuits parameter (js.getD k []) ≠ 0 ∧
    label = lockstepSaltLabel circuits parameter js k ∧ j = lockstepSaltRound circuits mode parameter js k

theorem lockstepRoundStart_succ (mode : ReshareMode) (parameter : PublicParameter)
    (js : List (List Job)) (k : ℕ) (hk : k < js.length) :
    lockstepRoundStart circuits mode parameter js (k + 1) =
      lockstepRoundStart circuits mode parameter js k + batchRounds circuits mode parameter (js.getD k []) := by
  simp only [lockstepRoundStart, List.take_add_one, List.map_append, List.sum_append,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.toList_some, Option.getD_some,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem lockstep_drop_eq_cons {xs ys rest : List (List Job)} {o : ℕ} {x : List Job}
    (h : xs.drop o = x :: ys ++ rest) :
    o < xs.length ∧ xs.getD o [] = x ∧ xs.drop (o + 1) = ys ++ rest := by
  have hlt : o < xs.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    simp at h
  refine ⟨hlt, ?_, ?_⟩
  · have := congrArg (fun l : List (List Job) => l[0]?) h
    simp only [List.getElem?_drop, Nat.add_zero, List.cons_append, List.getElem?_cons_zero] at this
    rw [List.getD_eq_getElem?_getD, this, Option.getD_some]
  · rw [← List.drop_drop, h]
    simp

/-- The labels of the batches `cs`, which are the chunks of `js` from `o`. -/
theorem lockstep_batches_state (ctx : Context C) (js : List (List Job)) :
    ∀ (cs rest : List (List Job)) (o tag : ℕ), js.drop o = cs ++ rest →
      ∀ v final, some (v, final) ∈ support ((cs.mapM (ceremonyBatch K circuits settings ctx) :
        StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run
          (lockstepStart circuits ctx.keys.parameter js o, tag)).run →
      final.1 = lockstepStart circuits ctx.keys.parameter js (o + cs.length)
  | [], rest, o, tag, _, v, final, h => by
    simp only [List.mapM_nil, StateT.run_pure, OptionT.run_pure, support_pure, Set.mem_singleton_iff,
      Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]
    rfl
  | c :: cs, rest, o, tag, hd, v, final, h => by
    obtain ⟨hlt, hc, hd'⟩ := lockstep_drop_eq_cons hd
    simp only [List.mapM_cons, StateT.run_bind] at h
    obtain ⟨⟨a, s'⟩, ha, h⟩ := treeSimCheck_some_bind _ _ _ h
    have hs' := ceremonyBatch_state K circuits settings ctx c _ a s' ha
    obtain ⟨⟨b, s''⟩, hb, h⟩ := treeSimCheck_some_bind _ _ _ h
    simp only [StateT.run_pure, OptionT.run_pure, support_pure, Set.mem_singleton_iff,
      Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]
    dsimp only at hs' hb
    rw [hs', ← hc, ← lockstepStart_succ circuits ctx.keys.parameter js o hlt] at hb
    rw [lockstep_batches_state ctx js cs rest (o + 1) (tag + 1) hd' b s'' hb, List.length_cons]
    ring_nf

/-- The batches `cs`, the chunks of `js` from `o`, make exactly their `batchRounds` exchanges and
read their salts by the schedule of `js`. -/
theorem treeSegmentRun_batches (ctx : Context C) (js : List (List Job)) :
    ∀ (cs rest : List (List Job)) (o tag : ℕ), js.drop o = cs ++ rest →
      TreeSegmentRun (LockstepSchedule circuits settings.mode ctx.keys.parameter ctx.prss.term ctx.self js)
        (lockstepRoundStart circuits settings.mode ctx.keys.parameter js o)
        (lockstepRoundStart circuits settings.mode ctx.keys.parameter js (o + cs.length))
        ((cs.mapM (ceremonyBatch K circuits settings ctx) : StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run
          (lockstepStart circuits ctx.keys.parameter js o, tag)).run
  | [], rest, o, tag, _ => by
    simpa only [List.mapM_nil, List.length_nil, Nat.add_zero, StateT.run_pure]
      using TreeSegmentRun.pure _ _
  | c :: cs, rest, o, tag, hd => by
    obtain ⟨hlt, hc, hd'⟩ := lockstep_drop_eq_cons hd
    simp only [List.mapM_cons]
    refine TreeSegmentRun.state_bind (treeSegmentRun_ceremonyBatch K circuits settings ctx c _ _ ?_)
      fun a s' ha => ?_
    · intro hcount T hT
      refine ⟨rfl, hT, o, hlt, by rw [hc]; exact hcount, ?_, ?_⟩
      · unfold lockstepSaltLabel
        rw [hc]
        omega
      · unfold lockstepSaltRound
        rw [hc]
    · have hs' := ceremonyBatch_state K circuits settings ctx c _ a s' ha
      rw [hs', ← hc, ← lockstepStart_succ circuits ctx.keys.parameter js o hlt,
        ← lockstepRoundStart_succ circuits settings.mode ctx.keys.parameter js o hlt]
      refine TreeSegmentRun.state_bind (treeSegmentRun_batches ctx js cs rest (o + 1) (tag + 1) hd')
        fun _ _ _ => ?_
      rw [List.length_cons, show o + 1 + cs.length = o + (cs.length + 1) by ring]
      exact TreeSegmentRun.pure _ _

theorem lockstepRoundStart_first (mode : ReshareMode) (parameter : PublicParameter) (enc enc' : Encoding)
    (tree : Tree) (k : ℕ)
    (hk : ∀ b, tree = .bottom b → k ≤ (chunks settings.batchSize (bottomJobs b)).length) :
    lockstepRoundStart circuits mode parameter (lockstepChunks settings enc tree) k =
      lockstepRoundStart circuits mode parameter (lockstepChunks settings enc' tree) k := by
  cases tree with
  | top => rfl
  | bottom b =>
    simp only [lockstepRoundStart, lockstepChunks, List.take_append_of_le_length (hk b rfl)]

/-- The salt reads of the ceremony of `tree` at an operator. Each read follows the schedule of some
encoding of the second run. The encoding may differ from read to read. -/
def CeremonySchedule (mode : ReshareMode) (parameter : PublicParameter) (keys : C.Term → HashOutput)
    (self : C.Party) (tree : Tree) (j : ℕ) (T : C.Term) (key : HashOutput) (label : ℕ) : Prop :=
  ∃ enc, LockstepSchedule circuits mode parameter keys self (lockstepChunks settings enc tree) j T key label

variable {S : ℕ → C.Term → HashOutput → ℕ → Prop}

theorem treeSegmentRun_batched_bind {β : Type} (ctx : Context C) (js : List (List Job))
    (jobs : List Job) (rest : List (List Job)) (o tag n : ℕ)
    (hd : js.drop o = chunks settings.batchSize jobs ++ rest)
    (hS : ∀ j T key label, LockstepSchedule circuits settings.mode ctx.keys.parameter ctx.prss.term
      ctx.self js j T key label → S j T key label)
    (k : Option (List (List Bit)) → StateT (ℕ × ℕ) (PartyM C E RealSpec) β)
    (hk : ∀ r tag', TreeSegmentRun S
      (lockstepRoundStart circuits settings.mode ctx.keys.parameter js
        (o + (chunks settings.batchSize jobs).length)) n
      ((k r).run (lockstepStart circuits ctx.keys.parameter js
        (o + (chunks settings.batchSize jobs).length), tag')).run) :
    TreeSegmentRun S (lockstepRoundStart circuits settings.mode ctx.keys.parameter js o) n
      (((batched settings.batchSize (ceremonyBatch K circuits settings ctx) jobs) >>= k).run
        (lockstepStart circuits ctx.keys.parameter js o, tag)).run := by
  unfold batched
  rw [bind_assoc]
  refine TreeSegmentRun.state_bind ((treeSegmentRun_batches K circuits settings ctx js _ rest o tag hd).mono hS)
    fun outputs s' hmem => ?_
  have hs' := lockstep_batches_state K circuits settings ctx js _ rest o tag hd outputs s' hmem
  rw [pure_bind, show s' = (s'.1, s'.2) from rfl, hs']
  exact hk _ _

theorem treeSegmentRun_batched_bind_from {β : Type} (ctx : Context C) (js : List (List Job))
    (jobs : List Job) (rest : List (List Job)) (o tag : ℕ)
    (hd : js.drop o = chunks settings.batchSize jobs ++ rest)
    (hS : ∀ j T key label, LockstepSchedule circuits settings.mode ctx.keys.parameter ctx.prss.term
      ctx.self js j T key label → S j T key label)
    (k : Option (List (List Bit)) → StateT (ℕ × ℕ) (PartyM C E RealSpec) β)
    (hk : ∀ r tag', TreeSegmentsFrom S
      (lockstepRoundStart circuits settings.mode ctx.keys.parameter js
        (o + (chunks settings.batchSize jobs).length))
      ((k r).run (lockstepStart circuits ctx.keys.parameter js
        (o + (chunks settings.batchSize jobs).length), tag')).run) :
    TreeSegmentsFrom S (lockstepRoundStart circuits settings.mode ctx.keys.parameter js o)
      (((batched settings.batchSize (ceremonyBatch K circuits settings ctx) jobs) >>= k).run
        (lockstepStart circuits ctx.keys.parameter js o, tag)).run := by
  unfold batched
  rw [bind_assoc]
  refine TreeSegmentRun.state_bind_from
    ((treeSegmentRun_batches K circuits settings ctx js _ rest o tag hd).mono hS) fun outputs s' hmem => ?_
  have hs' := lockstep_batches_state K circuits settings ctx js _ rest o tag hd outputs s' hmem
  rw [pure_bind, show s' = (s'.1, s'.2) from rfl, hs']
  exact hk _ _

theorem treeSegmentRun_tweakable {σ α : Type} (oa : OracleComp HashSpec α) (j : ℕ) (s : σ) :
    TreeSegmentRun S j j ((StateT.lift (oracleStep (tweakable oa)) :
      StateT σ (PartyM C E RealSpec) α).run s).run :=
  treeSegmentRun_oracleStep (RoSalts.tweakable _ oa) j s

theorem TreeSegmentRun.tweakable_bind {σ α β : Type} (oa : OracleComp HashSpec α) {j n : ℕ}
    {k : α → StateT σ (PartyM C E RealSpec) β} {s : σ}
    (hk : ∀ a, TreeSegmentRun S j n ((k a).run s).run) :
    TreeSegmentRun S j n ((StateT.lift (oracleStep (tweakable oa)) >>= k).run s).run := by
  rw [StateT.run_bind, StateT.run_lift, bind_assoc]
  exact TreeSegmentRun.oracle_bind (RoSalts.tweakable (fun _ _ _ => False) oa) (fun _ _ _ h => h.elim) _
    fun a => by simpa only [pure_bind] using hk a

theorem TreeSegmentsFrom.tweakable_bind {σ α β : Type} (oa : OracleComp HashSpec α) {j : ℕ}
    {k : α → StateT σ (PartyM C E RealSpec) β} {s : σ}
    (hk : ∀ a, TreeSegmentsFrom S j ((k a).run s).run) :
    TreeSegmentsFrom S j ((StateT.lift (oracleStep (tweakable oa)) >>= k).run s).run := by
  rw [StateT.run_bind, StateT.run_lift, bind_assoc]
  exact TreeSegmentsFrom.oracle_bind (RoSalts.tweakable (fun _ _ _ => False) oa) (fun _ _ _ h => h.elim) _
    fun a => by simpa only [pure_bind] using hk a

/-- The program of an operator after the PRSS setup reads its salts by the schedule of the
ceremony, for the encoding of the second run that it computes. -/
theorem treeSegmentsFrom_ceremonyAfterSetup (ctx : Context C) (top : TopTree) (tree : Tree) :
    TreeSegmentsFrom (CeremonySchedule circuits settings settings.mode ctx.keys.parameter ctx.prss.term
      ctx.self tree) 0 (ceremonyAfterSetup K circuits settings ctx top tree : PartyM C E RealSpec TreeOutput).run := by
  unfold ceremonyAfterSetup
  refine TreeSegmentsFrom.bind_pure ?_ fun o => ?_
  swap
  · rcases o with _ | o
    · exact ⟨none, OptionT.run_failure⟩
    · exact ⟨some o, OptionT.run_pure _⟩
  rw [StateT.run'_eq, map_eq_bind_pure_comp]
  refine TreeSegmentsFrom.bind_pure ?_ fun _ => ⟨_, OptionT.run_pure _⟩
  have hS : ∀ enc j T key label, LockstepSchedule circuits settings.mode ctx.keys.parameter ctx.prss.term
      ctx.self (lockstepChunks settings enc tree) j T key label →
      CeremonySchedule circuits settings settings.mode ctx.keys.parameter ctx.prss.term ctx.self tree
        j T key label := fun enc j T key label h => ⟨enc, h⟩
  have h0 : ∀ enc, lockstepRoundStart circuits settings.mode ctx.keys.parameter
      (lockstepChunks settings enc tree) 0 = 0 ∧
      lockstepStart circuits ctx.keys.parameter (lockstepChunks settings enc tree) 0 = 0 := fun enc =>
    ⟨by simp [lockstepRoundStart], by simp [lockstepStart]⟩
  obtain ⟨hr0, hs0⟩ := h0 fun _ => digit 0
  suffices h : TreeSegmentsFrom (CeremonySchedule circuits settings settings.mode ctx.keys.parameter
      ctx.prss.term ctx.self tree)
      (lockstepRoundStart circuits settings.mode ctx.keys.parameter
        (lockstepChunks settings (fun _ => digit 0) tree) 0)
      ((ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
        (fun oa => StateT.lift (oracleStep (tweakable oa))) ctx.keys.parameter
        (batched settings.batchSize (ceremonyBatch K circuits settings ctx)) top tree).run
        (lockstepStart circuits ctx.keys.parameter (lockstepChunks settings (fun _ => digit 0) tree) 0,
          0)).run by
    rwa [hr0, hs0] at h
  cases tree with
  | top =>
    simp only [ceremonyOutput]
    refine TreeSegmentRun.from (treeSegmentRun_batched_bind K circuits settings ctx _ topJobs []
      0 0 (lockstepRoundStart circuits settings.mode ctx.keys.parameter
        (lockstepChunks settings (fun _ => digit 0) .top) (0 + (chunks settings.batchSize topJobs).length))
      (by simp [lockstepChunks]) (hS _) _ fun r tag' => ?_)
    rcases r with _ | outputs
    · exact TreeSegmentRun.pure _ _
    · exact TreeSegmentRun.state_bind (treeSegmentRun_tweakable _ _ _) fun _ _ _ =>
        TreeSegmentRun.pure _ _
  | bottom b =>
    simp only [ceremonyOutput]
    refine treeSegmentRun_batched_bind_from K circuits settings ctx _ (bottomJobs b)
      (chunks settings.batchSize (signJobs b fun _ => digit 0)) 0 0 (by simp [lockstepChunks]) (hS _) _
      fun r tag' => ?_
    rcases r with _ | outputs
    · exact TreeSegmentsFrom.pure _ _
    refine TreeSegmentsFrom.tweakable_bind _ fun root => ?_
    refine TreeSegmentsFrom.tweakable_bind _ fun base => ?_
    refine TreeSegmentsFrom.tweakable_bind _ fun g => ?_
    rcases g with _ | ⟨randomness, encoding⟩
    · exact TreeSegmentsFrom.pure _ _
    have hfirst : ∀ b', Tree.bottom b = .bottom b' →
        0 + (chunks settings.batchSize (bottomJobs b)).length ≤
          (chunks settings.batchSize (bottomJobs b')).length := by
      intro b' hb
      cases hb
      omega
    rw [lockstepRoundStart_first circuits settings settings.mode ctx.keys.parameter _ encoding _ _ hfirst,
      lockstepStart_first circuits settings ctx.keys.parameter _ encoding _ _ hfirst]
    refine TreeSegmentRun.from (treeSegmentRun_batched_bind K circuits settings ctx _ (signJobs b encoding) []
      _ tag' (lockstepRoundStart circuits settings.mode ctx.keys.parameter
        (lockstepChunks settings encoding (.bottom b))
        (0 + (chunks settings.batchSize (bottomJobs b)).length +
          (chunks settings.batchSize (signJobs b encoding)).length))
      (by simp [lockstepChunks]) (hS _) _ fun v tag'' => ?_)
    rcases v with _ | values
    · exact TreeSegmentRun.pure _ _
    refine TreeSegmentRun.tweakable_bind _ fun path => ?_
    refine TreeSegmentRun.tweakable_bind _ fun root' => ?_
    split_ifs
    · exact TreeSegmentRun.pure _ _
    · exact TreeSegmentRun.pure _ _

end Ceremony

section World

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (prims : Primitives) (D : C.Coalition)

/-- A suspended step whose resumption follows `S` from exchange `j`. -/
def SegmentsStep {α : Type} (S : ℕ → C.Term → HashOutput → ℕ → Prop) (j : ℕ) :
    Step C E RealSpec α → Prop
  | .done _ => True
  | .wait _ resume => ∀ inbox, TreeSegmentsFrom S j (resume inbox)
  | .call input _ => input.elim

theorem TreeSegmentsFrom.mono {α : Type} {S S' : ℕ → C.Term → HashOutput → ℕ → Prop} {j : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : TreeSegmentsFrom S j p)
    (hS : ∀ j T key label, S j T key label → S' j T key label) : TreeSegmentsFrom S' j p := by
  induction h with
  | pure j out => exact .pure j out
  | queryLocal j q k hq h ih =>
    exact .queryLocal j q k (fun x hx T key label g he => hS j T key label (hq x hx T key label g he)) ih
  | round j out k h ih => exact .round j out k ih

theorem TreeSegmentsFrom.advance_mem {α : Type} {S : ℕ → C.Term → HashOutput → ℕ → Prop} {j : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : TreeSegmentsFrom S j p) :
    ∀ step ∈ support (advance p), SegmentsStep S (j + 1) step := by
  induction h with
  | pure j out =>
    intro step hs
    change step ∈ support (Pure.pure (.done out) : OracleComp (LocalSpec C) (Step C E RealSpec α)) at hs
    have he : step = .done out := by simpa using hs
    subst step
    trivial
  | queryLocal j q k hq h ih =>
    intro step hs
    obtain ⟨r, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hs
    exact ih r step hr
  | round j out k h ih =>
    intro step hs
    have he : step = .wait out k := by simpa [advance] using hs
    subst step
    exact h

theorem TreeSegmentsFrom.segmentSalts {α : Type} {S : ℕ → C.Term → HashOutput → ℕ → Prop} {j : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : TreeSegmentsFrom S j p)
    {P : PrgInput C → Prop} (hP : ∀ x, SaltRead (S j) x → P x) : SegmentSalts P p := by
  induction h with
  | pure j out => exact .pure out
  | queryLocal j q k hq h ih => exact .queryLocal q k (fun x hx => hP x (hq x hx)) fun r => ih r hP
  | round j out k h ih => exact .round out k

theorem segmentsStep_round {α : Type} (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (S : C.Party → ℕ → C.Term → HashOutput → ℕ → Prop) (j : ℕ)
    (hs : ∀ i, i ∉ D.1 → SegmentsStep (S i) j (steps i)) :
    ∀ r ∈ support (stepRound worldRoles D A noFunctionality state steps),
      ∀ i, i ∉ D.1 → SegmentsStep (S i) (j + 1) (r.2.1 i) := by
  rw [stepRound_real]
  intro r hr
  obtain ⟨sent, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  obtain ⟨next, hn, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  have he : r = (sent.1, next, sent.2) := by simpa using hr
  subst r
  have hl := treeSimCheck_support_free _ hn
  intro i hi
  have hni := mem_support_sequenceFin_oc _ _ hl i
  have h := hs i hi
  revert hni h
  unfold roundLocal
  cases steps i with
  | done out =>
    intro hni _
    have : next i = .done out := by simpa using hni
    simp only [this]
    trivial
  | call input _ => exact input.elim
  | wait out resume =>
    intro hni h
    simp only [if_neg hi] at hni
    exact (h _).advance_mem _ hni

/-- A corrupt operator stays done with no output in a round of the world. It follows
`stepRound_corruptDone` of `CheckCore` for the world roles. -/
theorem world_stepRound_corruptDone {α : Type} (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (hs : ∀ i ∈ D.1, steps i = Step.done none) :
    ∀ r ∈ support (stepRound worldRoles D A noFunctionality state steps), ∀ i ∈ D.1, r.2.1 i = Step.done none := by
  intro r hr i hi
  unfold stepRound at hr
  split_ifs at hr
  · simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨⟨st, out⟩, -, steps', hsteps', rfl⟩ := hr
    have h := mem_support_sequenceFin_oc _ steps' hsteps' i
    rw [hs i hi] at h
    simpa using h
  · simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨⟨st, sent⟩, -, steps', hsteps', rfl⟩ := hr
    have h := mem_support_sequenceFin_oc _ steps' hsteps' i
    rw [hs i hi] at h
    simpa using h

theorem world_executeRounds_corrupt_none {α : Type} (A : Adversary C E (Keys C) PEmpty PEmpty) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α),
      (∀ i ∈ D.1, steps i = Step.done none) →
      ∀ r ∈ support (executeRounds worldRoles D A noFunctionality fuel state steps), ∀ i ∈ D.1, r.2 i = none
  | 0, state, steps, hs => by
    intro r hr i hi
    simp only [executeRounds, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp [hs i hi, Step.output]
  | fuel + 1, state, steps, hs => by
    intro r hr i hi
    simp only [executeRounds] at hr
    split_ifs at hr
    · simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp [hs i hi, Step.output]
    · simp only [support_bind, Set.mem_iUnion] at hr
      obtain ⟨r', hr', hr⟩ := hr
      exact world_executeRounds_corrupt_none A fuel r'.1 r'.2.1
        (world_stepRound_corruptDone D A state steps hs r' hr') r hr i hi

/-- A corrupt operator has no PRSS keys after the logged real setup. -/
theorem treeSetup_corrupt_none (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (s : TreeSimState C) (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality setupRounds state
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s)) :
    ∀ i ∈ D.1, p.1.2 i = none := by
  rw [treeSimRealRoles, ← simulateQ_executePhase] at hp
  have hp' : p.1 ∈ support (executePhase worldRoles D A noFunctionality setupRounds state
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))) := by
    apply OracleComp.support_simulateQ_run'_subset (treeSimLoggedWorld prims D)
    rw [StateT.run'_eq, support_map]
    exact ⟨p, hp, rfl⟩
  unfold executePhase at hp'
  simp only [support_bind, Set.mem_iUnion] at hp'
  obtain ⟨steps, hsteps, hr⟩ := hp'
  refine world_executeRounds_corrupt_none D A _ state steps (fun i hi => ?_) _ hr
  have h := mem_support_sequenceFin_oc _ steps hsteps i
  simpa [hi] using h

end World

section Reach

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (prims : Primitives) (K : Constants C E)
  (circuits : Circuits) (settings : Settings) (D : C.Coalition)

/-- The salt schedule of operator `i` with the setup outputs `keysOf`. -/
def OpSchedule (x : C.Party → Keys C) (tree : Tree) (keysOf : C.Party → Option (PrssKeys C)) (i : C.Party)
    (j : ℕ) (T : C.Term) (key : HashOutput) (label : ℕ) : Prop :=
  ∃ prss, keysOf i = some prss ∧
    CeremonySchedule circuits settings settings.mode (x i).parameter prss.term i tree j T key label

/-- The schedule on every reachable configuration after `n` rounds. Each honest step follows its
schedule from exchange `n + 1`. Each honest salt read that the log holds after the setup follows the
schedule of an honest operator at an exchange index of at most `n`. -/
theorem segments_reach (top : TopTree) (tree : Tree) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (state : A.State) (s : TreeSimState C) :
    ∀ n a, TreeStagesReach prims K circuits settings top tree D A x state s n a →
      ∃ p ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality setupRounds state
        (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s),
      ∃ l, a.2.2 = p.2.2 ++ l ∧
        (∀ i, i ∉ D.1 → SegmentsStep (OpSchedule circuits settings x tree p.1.2 i) (n + 1) (a.1.2 i)) ∧
        ∀ y b, (⟨.inr (.inr (.inr y)), b⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ l →
          ∃ i, i ∉ D.1 ∧ ∃ j ≤ n, SaltRead (OpSchedule circuits settings x tree p.1.2 i j) y := by
  intro n
  induction n with
  | zero =>
    intro a ha
    simp only [TreeStagesReach, treeStagesTrace, executeSteps, StateT.run_bind, StateT.run_pure,
      support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at ha
    obtain ⟨p, hp, next, hnext, rfl⟩ := ha
    have hcorrupt := treeSetup_corrupt_none prims D A state s p hp
    have hsched : ∀ i prss, p.1.2 i = some prss → TreeSegmentsFrom (OpSchedule circuits settings x tree p.1.2 i) 0
        (treeSimRealCont K circuits settings top tree x i prss).run := fun i prss hk =>
      (treeSegmentsFrom_ceremonyAfterSetup K circuits settings ⟨i, x i, prss⟩ top tree).mono
        fun j T key label h => ⟨prss, hk, h⟩
    have hworld : WorldSalts prims D (fun y => ∃ i, i ∉ D.1 ∧
        SaltRead (OpSchedule circuits settings x tree p.1.2 i 0) y)
        (treeSimContinue (treeSimRealCont K circuits settings top tree x) p.1.2) := by
      unfold treeSimContinue
      rw [free_sequenceFin]
      refine worldSalts_sequenceFin prims D _ fun i => ?_
      cases hk : p.1.2 i with
      | none =>
        simp only [continueStep, free_pure]
        exact WorldSalts.pure prims D _ _
      | some prss =>
        have hi : i ∉ D.1 := fun hi => by rw [hcorrupt i hi] at hk; cases hk
        simp only [continueStep]
        exact worldSalts_free_advance prims D ((hsched i prss hk).segmentSalts fun y hy => ⟨i, hi, hy⟩)
    obtain ⟨l, hl, hlog⟩ := hworld p.2 next hnext
    refine ⟨p, hp, l, hl, fun i hi => ?_, fun y b hy => ?_⟩
    · have hn : next.1 ∈ support (treeSimContinue (treeSimRealCont K circuits settings top tree x) p.1.2) := by
        apply OracleComp.support_simulateQ_run'_subset (treeSimLoggedWorld prims D)
        rw [StateT.run'_eq, support_map]
        exact ⟨next, hnext, rfl⟩
      have hi' := mem_support_sequenceFin_oc _ _ (treeSimCheck_support_free _ hn) i
      cases hk : p.1.2 i with
      | none =>
        simp only [hk, continueStep, support_pure, Set.mem_singleton_iff] at hi'
        show SegmentsStep _ _ (next.1 i)
        rw [hi']
        trivial
      | some prss =>
        simp only [hk, continueStep] at hi'
        exact (hsched i prss hk).advance_mem _ hi'
    · obtain ⟨i, hi, h⟩ := hlog y b hy
      exact ⟨i, hi, 0, le_rfl, h⟩
  | succ n ih =>
    intro a ha
    unfold TreeStagesReach at ha
    rw [treeStages_trace_add] at ha
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at ha
    obtain ⟨b, hb', ha⟩ := ha
    obtain ⟨p, hp, l, hl, hsteps, hlog⟩ := ih b hb'
    simp only [executeSteps] at ha
    split_ifs at ha with hdone
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at ha
      subst a
      refine ⟨p, hp, l, hl, fun i hi => ?_, fun y c hy => ?_⟩
      · have hd := hdone i hi
        revert hd
        cases b.1.2 i with
        | done out => intro _; trivial
        | wait out resume => intro hd; exact hd.elim
        | call input resume => intro hd; exact hd.elim
      · obtain ⟨i, hi, j, hj, h⟩ := hlog y c hy
        exact ⟨i, hi, j, by omega, h⟩
    · simp only [StateT.run_bind, support_bind, Set.mem_iUnion, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at ha
      obtain ⟨u, hu, rfl⟩ := ha
      have hround : (stepRound (treeSimRealRoles prims D) D A noFunctionality b.1.1 b.1.2) =
          simulateQ (treeSimLoggedWorld prims D) (stepRound worldRoles D A noFunctionality b.1.1 b.1.2) := by
        rw [simulateQ_stepRound]
        rfl
      have hu' := hu
      rw [hround] at hu'
      obtain ⟨l', hl', hlog'⟩ := worldSalts_round prims D (fun y => ∃ i, i ∉ D.1 ∧
          SaltRead (OpSchedule circuits settings x tree p.1.2 i (n + 1)) y) A b.1.1 b.1.2
        (fun i hi => by
          have h := hsteps i hi
          revert h
          cases b.1.2 i with
          | done out => intro _; trivial
          | call input _ => exact input.elim
          | wait out resume => exact fun h inbox => (h inbox).segmentSalts fun y hy => ⟨i, hi, hy⟩)
        b.2 u hu'
      refine ⟨p, hp, l ++ l', by rw [hl', hl, List.append_assoc], fun i hi => ?_, fun y c hy => ?_⟩
      · exact segmentsStep_round D A b.1.1 b.1.2 _ (n + 1) hsteps u.1
          (treeTwin_real_round_mem prims D A b.1.1 b.1.2 b.2 u hu) i hi
      · rcases List.mem_append.mp hy with hy | hy
        · obtain ⟨i, hi, j, hj, h⟩ := hlog y c hy
          exact ⟨i, hi, j, by omega, h⟩
        · obtain ⟨i, hi, h⟩ := hlog' y c hy
          exact ⟨i, hi, n + 1, le_rfl, h⟩

end Reach

section Setup

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (prims : Primitives) (D : C.Coalition)

theorem localSalts_probComp {α : Type} (R : C.Term → HashOutput → ℕ → Prop) (oa : ProbComp α) :
    LocalSalts R (liftComp oa (LocalSpec C)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [liftComp_pure] using LocalSalts.pure R a
  | query_bind q f ih =>
    rw [liftComp_bind, liftComp_query]
    have : ((OracleSpec.query q).cont <$> liftM (OracleSpec.query (OracleSpec.query q).input) :
        OracleComp (LocalSpec C) _) = OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inl q)) := rfl
    rw [this]
    exact (LocalSalts.query (.inl q) fun x he => by cases he).bind ih

theorem roNoSalt_deriveKeys (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    RoNoSalt (deriveKeys (C := C) phase i view) := by
  have rest : ∀ parameter : HashOutput,
      RoNoSalt (C := C) (α := HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (do
      let term ← C.terms.mapM fun T => if i ∈ C.holders T then
        hashQuery (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T))
        else pure 0
      let pair ← C.parties.mapM fun j => if h : j = i then pure 0 else
        let p := C.pairOf i j (Ne.symm h)
        hashQuery (.derive phase .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1])
      pure (parameter, fun (T : C.Term) => term.getD (C.terms.idxOf T) 0,
        fun (j : C.Party) => pair.getD j.val 0)) := by
    intro parameter
    refine (RoSalts.mapM _ (fun T => ?_) _).bind fun _ =>
      (RoSalts.mapM _ (fun j => ?_) _).bind fun _ => RoSalts.pure _ _
    · split_ifs
      · exact RoSalts.hashQuery _ _
      · exact RoSalts.pure _ _
    · split_ifs
      · exact RoSalts.pure _ _
      · exact RoSalts.hashQuery _ _
  unfold deriveKeys
  dsimp only
  split_ifs
  · exact (RoSalts.hashQuery _ _).bind rest
  · exact (RoSalts.pure _ _).bind rest

/-- The PRSS setup makes exactly three exchanges and reads no salt. -/
theorem treeSegmentRun_prssSetup (i : C.Party) :
    TreeSegmentRun (fun _ _ _ _ => False) 0 3 (prssSetup (E := E) (G := RealSpec) i).run := by
  unfold prssSetup commitRevealEcho
  simp only [bind_assoc]
  refine (localSalts_probComp (fun _ _ _ => False) sampleParts E _ _ 0 3 _ (fun _ _ _ h => h)).1
    fun own => ?_
  refine TreeSegmentRun.oracle_bind (RoSalts.mapM _ (fun _ => RoSalts.hashQuery _ _) _)
    (fun _ _ _ h => h) _ fun _ => ?_
  refine TreeSegmentRun.exchange_bind _ _ fun _ => TreeSegmentRun.exchange_bind _ _ fun _ => ?_
  refine TreeSegmentRun.oracle_bind (RoSalts.mapM _ (fun _ => RoSalts.hashQuery _ _) _)
    (fun _ _ _ h => h) _ fun _ => ?_
  refine TreeSegmentRun.require_bind _ _ ?_
  refine TreeSegmentRun.oracle_bind (roNoSalt_deriveKeys _ _ _) (fun _ _ _ h => h) _ fun _ => ?_
  refine TreeSegmentRun.oracle_bind (RoSalts.mapM _ (fun _ => RoSalts.hashQuery _ _) _)
    (fun _ _ _ h => h) _ fun _ => ?_
  refine TreeSegmentRun.exchange_bind _ _ fun _ => ?_
  refine TreeSegmentRun.require_bind _ _ ?_
  simp only [pure_bind]
  exact TreeSegmentRun.pure _ _

theorem WorldSalts.bind_support {β γ : Type} {P : PrgInput C → Prop} {p : OracleComp (WorldSpec C) β}
    {k : β → OracleComp (WorldSpec C) γ} (hp : WorldSalts prims D P p)
    (hk : ∀ b ∈ support p, WorldSalts prims D P (k b)) : WorldSalts prims D P (p >>= k) := by
  intro s r hr
  rw [simulateQ_bind, StateT.run_bind] at hr
  obtain ⟨x, hx, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  have hx' : x.1 ∈ support p := by
    apply OracleComp.support_simulateQ_run'_subset (treeSimLoggedWorld prims D)
    rw [StateT.run'_eq, support_map]
    exact ⟨x, hx, rfl⟩
  obtain ⟨l₁, hl₁, h₁⟩ := hp s x hx
  obtain ⟨l₂, hl₂, h₂⟩ := hk x.1 hx' x.2 r hr
  refine ⟨l₁ ++ l₂, by rw [hl₂, hl₁, List.append_assoc], fun y b hmem => ?_⟩
  rcases List.mem_append.mp hmem with hm | hm
  · exact h₁ y b hm
  · exact h₂ y b hm

theorem worldSalts_executeRounds {α : Type} (A : Adversary C E (Keys C) PEmpty PEmpty) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α) (j : ℕ),
      (∀ i, i ∉ D.1 → SegmentsStep (fun _ _ _ _ => False) j (steps i)) →
      WorldSalts prims D (SaltRead fun _ _ _ => False)
        (executeRounds worldRoles D A noFunctionality fuel state steps)
  | 0, state, steps, j, _ => by
    simp only [executeRounds]
    exact WorldSalts.pure prims D _ _
  | fuel + 1, state, steps, j, hs => by
    simp only [executeRounds]
    split_ifs
    · exact WorldSalts.pure prims D _ _
    · refine WorldSalts.bind_support prims D (worldSalts_round prims D _ A state steps fun i hi => ?_)
        fun r hr => ?_
      · have h := hs i hi
        revert h
        cases steps i with
        | done out => intro _; trivial
        | call input _ => exact input.elim
        | wait out resume => exact fun h inbox => (h inbox).segmentSalts fun y hy => hy
      · exact worldSalts_executeRounds A fuel r.1 r.2.1 (j + 1)
          (segmentsStep_round D A state steps (fun _ => fun _ _ _ _ => False) j hs r hr)

/-- The logged real setup appends no honest salt read to the log. -/
theorem treeSetup_noSalt (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (s : TreeSimState C) (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality setupRounds state
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s)) :
    ∃ l, p.2.2 = s.2 ++ l ∧ ∀ y b,
      (⟨.inr (.inr (.inr y)), b⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ l →
        SaltRead (fun _ _ _ => False) y := by
  rw [treeSimRealRoles, ← simulateQ_executePhase] at hp
  refine (?_ : WorldSalts prims D (SaltRead fun _ _ _ => False) _) s p hp
  unfold executePhase startSteps
  refine WorldSalts.bind_support prims D ?_ fun steps hsteps => ?_
  · refine worldSalts_sequenceFin prims D _ fun i => ?_
    split_ifs
    · exact WorldSalts.pure prims D _ _
    · exact worldSalts_free_advance prims D
        ((treeSegmentRun_prssSetup i).from.segmentSalts fun y hy => hy)
  · refine worldSalts_executeRounds prims D A _ state steps 1 fun i hi => ?_
    have h := mem_support_sequenceFin_oc _ steps hsteps i
    simp only [if_neg hi] at h
    exact (treeSegmentRun_prssSetup i).from.advance_mem _ (treeSimCheck_support_free _ h)

end Setup

section Goal

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (circuits : Circuits) (prims : Primitives) (K : Constants C E) (settings : Settings)

/-- The salt schedule of operator `i` for the fixed encoding `enc` of the second run. -/
def OpScheduleEnc (x : C.Party → Keys C) (tree : Tree) (enc : Encoding)
    (keysOf : C.Party → Option (PrssKeys C)) (i : C.Party) (j : ℕ) (T : C.Term) (key : HashOutput)
    (label : ℕ) : Prop :=
  ∃ prss, keysOf i = some prss ∧ LockstepSchedule circuits settings.mode (x i).parameter prss.term i
    (lockstepChunks settings enc tree) j T key label

/-- The honest operators agree on the encoding of the second run, also on aborted prefixes. On a
reachable configuration with no budget collision, every honest salt read of the log after the
setup, and every salt read of the next segment of each honest step, follows the schedule of one
encoding `enc`. The premises are the schedule of `segments_reach`, where each read has its own
encoding. -/
def TreeLockstepEncodingGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux),
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ∀ (padding : OracleComp (LocalSpec C) Unit),
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∀ n (a : TreeSimConfig A (TreeSimState C)),
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      ¬ TreeSimHashBudgetCollision a.2.2 →
      ∀ ps ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality setupRounds p.2.1
        (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run ((r.2, p.2.2.1.2), p.2.2.2)),
      ∀ l, a.2.2 = ps.2.2 ++ l →
      (∀ i, i ∉ D.1 → SegmentsStep (OpSchedule circuits settings (dealtKeys parameter seeds pairs) tree
        ps.1.2 i) (n + 1) (a.1.2 i)) →
      (∀ y b, (⟨.inr (.inr (.inr y)), b⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ l →
        ∃ i, i ∉ D.1 ∧ ∃ j ≤ n,
          SaltRead (OpSchedule circuits settings (dealtKeys parameter seeds pairs) tree ps.1.2 i j) y) →
      ∃ enc : Encoding,
        (∀ y b, (⟨.inr (.inr (.inr y)), b⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ l →
          ∃ i, i ∉ D.1 ∧ ∃ j ≤ n, SaltRead
            (OpScheduleEnc circuits settings (dealtKeys parameter seeds pairs) tree enc ps.1.2 i j) y) ∧
        ∀ i, i ∉ D.1 → SegmentSaltsStep (SaltRead
          (OpScheduleEnc circuits settings (dealtKeys parameter seeds pairs) tree enc ps.1.2 i (n + 1)))
          (a.1.2 i)

theorem lockstepRoundStart_mono (mode : ReshareMode) (parameter : PublicParameter) (js : List (List Job))
    {k k' : ℕ} (h : k ≤ k') :
    lockstepRoundStart circuits mode parameter js k ≤ lockstepRoundStart circuits mode parameter js k' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold lockstepRoundStart
  rw [List.take_add, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

/-- The salt reads of two checked batches come after different exchanges, in the order of the
batches. -/
theorem lockstepSaltRound_lt (mode : ReshareMode) (parameter : PublicParameter) (js : List (List Job))
    {k k' : ℕ} (hkk : k < k') (hk : k < js.length)
    (hcount : batchCount circuits parameter (js.getD k []) ≠ 0) :
    lockstepSaltRound circuits mode parameter js k < lockstepSaltRound circuits mode parameter js k' := by
  have h1 : lockstepSaltRound circuits mode parameter js k <
      lockstepRoundStart circuits mode parameter js (k + 1) := by
    rw [lockstepRoundStart_succ circuits mode parameter js k hk]
    have hc : checkLabels (batchCount circuits parameter (js.getD k [])) =
        2 * halvings (batchCount circuits parameter (js.getD k [])) + 5 := if_neg hcount
    unfold lockstepSaltRound batchRounds
    rw [hc]
    omega
  have h2 := lockstepRoundStart_mono circuits mode parameter js (show k + 1 ≤ k' from hkk)
  unfold lockstepSaltRound at h1 ⊢
  omega

theorem SegmentSalts.mono {α : Type} {P Q : PrgInput C → Prop}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : SegmentSalts P p) (hPQ : ∀ x, P x → Q x) :
    SegmentSalts Q p := by
  induction h with
  | pure out => exact .pure out
  | queryLocal q k hq h ih => exact .queryLocal q k (fun x hx => hPQ x (hq x hx)) ih
  | round out k => exact .round out k

/-- The log of the common prefix holds no honest salt read. -/
theorem treeSimCommonPrefix_noSalt (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (hp : p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z)) :
    ∀ y b, (⟨.inr (.inr (.inr y)), b⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ p.2.2.2 →
      SaltRead (fun _ _ _ => False) y := by
  unfold treeSimCommonPrefix at hp
  simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hp
  obtain ⟨dealt, -, start, hstart, rfl⟩ := hp
  obtain ⟨l, hl, h⟩ := worldSalts_counted prims D (SaltRead fun _ _ _ => False) _ _ start hstart
  intro y b hy
  rw [hl, List.nil_append] at hy
  exact h y b hy

/-- `TreeLockstepSegmentsGoal` from the agreement on the encoding of the second run. The round
schedule of one operator (`segments_reach`), the agreement on the keys of the setup, and the
salt-free setup give the rest. -/
theorem treeLockstepSegmentsGoal_of_encoding
    (encoding : TreeLockstepEncodingGoal circuits prims K settings) :
    TreeLockstepSegmentsGoal circuits prims K settings := by
  intro hbatch top tree D A parameter seeds pairs z p hp padding r hr n a reach good
  obtain ⟨ps, hps, l, hl, hsteps, hlog⟩ :=
    segments_reach prims K circuits settings D top tree A _ p.2.1 _ n a reach
  obtain ⟨enc, hlogE, hstepsE⟩ := encoding hbatch top tree D A parameter seeds pairs z p hp padding r hr
    n a reach good ps hps l hl hsteps hlog
  have hgood : ¬ TreeSimHashBudgetCollision ps.2.2 := fun hc =>
    good (treeSimHashBudgetCollision_mono (by rw [hl]; exact List.prefix_append _ _) hc)
  have hagree := treeSetup_phase_agree prims D A p.2.1 _ ps hps hgood
  have hkeys : ∀ T, ∃ key : HashOutput, ∀ i prss, i ∉ D.1 → ps.1.2 i = some prss →
      i ∈ C.holders T → prss.term T = key := by
    intro T
    by_cases h : ∃ i prss, i ∉ D.1 ∧ ps.1.2 i = some prss ∧ i ∈ C.holders T
    · obtain ⟨i, prss, -, hi, hT⟩ := h
      exact ⟨prss.term T, fun j kj _ hj hjT => hagree j i kj prss hj hi T hjT hT⟩
    · exact ⟨0, fun i prss hi hk hT => (h ⟨i, prss, hi, hk, hT⟩).elim⟩
  choose keys hkeys using hkeys
  have hpar : ∀ i, (dealtKeys parameter seeds pairs i).parameter = parameter := fun _ => rfl
  have hex : ∃ k, k = (lockstepChunks settings enc tree).length ∨
      (k < (lockstepChunks settings enc tree).length ∧
        batchCount circuits parameter ((lockstepChunks settings enc tree).getD k []) ≠ 0 ∧
        n < lockstepSaltRound circuits settings.mode parameter (lockstepChunks settings enc tree) k) :=
    ⟨_, Or.inl rfl⟩
  refine ⟨keys, enc, Nat.find hex, ?_, fun i hi => ?_⟩
  · intro T key label g b mem
    rw [hl] at mem
    rcases List.mem_append.mp mem with hm | hm
    · obtain ⟨l₀, hl₀, hsetup⟩ := treeSetup_noSalt prims D A p.2.1 _ ps hps
      rw [hl₀] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact (treeSimCommonPrefix_noSalt circuits prims settings top tree D A parameter seeds pairs z p hp
          _ b hm T key label g rfl).elim
      · exact (hsetup _ b hm T key label g rfl).elim
    · obtain ⟨i, hi, j, hj, h⟩ := hlogE _ b hm
      obtain ⟨prss, hk, hkey, hT, k, hklen, hcount, hlabel, hjk⟩ := h T key label g rfl
      rw [hpar] at hjk
      refine ⟨by rw [hkey]; exact hkeys T i prss hi hk hT, k, Nat.zero_le _, ?_, hklen, hcount, hlabel⟩
      by_contra hge
      push Not at hge
      rcases Nat.find_spec hex with heq | ⟨hlt, hc0, hn⟩
      · omega
      · rcases hge.lt_or_eq with hlt' | heq
        · have := lockstepSaltRound_lt circuits settings.mode parameter _ hlt' hlt hc0
          omega
        · rw [heq] at hn
          omega
  · have h := hstepsE i hi
    revert h
    cases a.1.2 i with
    | done out => intro _; trivial
    | call input _ => exact input.elim
    | wait out resume =>
      intro h inbox
      refine (h inbox).mono fun x hx T key label g he => ?_
      obtain ⟨prss, hk, hkey, hT, k, hklen, hcount, hlabel, hjk⟩ := hx T key label g he
      rw [hpar] at hjk
      refine ⟨by rw [hkey]; exact hkeys T i prss hi hk hT, k, ?_, hklen, hklen, hcount, hlabel⟩
      exact Nat.find_min' hex (Or.inr ⟨hklen, hcount, by omega⟩)

end Goal


/-- info: 'ThresholdLeanXmssSecurity.treeLockstepSegmentsGoal_of_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepSegmentsGoal_of_encoding

/-- info: 'ThresholdLeanXmssSecurity.segments_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms segments_reach

/-- info: 'ThresholdLeanXmssSecurity.treeSegmentsFrom_ceremonyAfterSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSegmentsFrom_ceremonyAfterSetup

/-- info: 'ThresholdLeanXmssSecurity.treeExactExchanges_ceremonyBatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeExactExchanges_ceremonyBatch

end ThresholdLeanXmssSecurity
