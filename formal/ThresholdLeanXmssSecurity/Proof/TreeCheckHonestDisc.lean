import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkState
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# Honest coin labels and expansion keys before a check checkpoint

`CheckDisc` records the keys returned by local coin-key queries in the current
pass. An exchange clears those keys. The zero-round predicate deliberately
places no condition on the residual program.

* `CheckDisc.residual` transports the discipline to a scheduler residual.
* `runDisc_check` composes the actual coin and expansion syntax using the
  label increments of `LockstepLabels`.
* `caller_window` carries quiet opening tails through the timed batches.
* `initial_checkDisc` and `initial_program_checkDisc` cover exactly the first
  `batchStart j + 1` passes, with cutoff `lockstepStart j`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false

noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckHonestDisc

open TreeCheckWalkState TreeCheckWalkRecipe

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E α β : Type}

/-- The condition on the next local query of an honest pass. -/
def LocalDisc (limit : ℕ) (keys : Set HashOutput) : (LocalSpec C).Domain → Prop
  | .inr (.inl (.coinKey _ label _)) => label < limit
  | .inr (.inl (.expand key _)) => key ∈ keys
  | _ => True

/-- Only a coin-key answer enlarges the current pass's set of keys. -/
def localKeys (keys : Set HashOutput) (q : (LocalSpec C).Domain)
    (r : (LocalSpec C).Range q) : Set HashOutput :=
  match q with
  | .inr (.inl (.coinKey _ _ _)) => insert r keys
  | _ => keys

/-- Syntactic discipline for the first `n` local passes. Keys reset exactly at
an exchange; a stopped program satisfies the discipline at every horizon. -/
inductive CheckDisc (limit : ℕ) : ℕ → Set HashOutput →
    OracleComp (PartySpec C E RealSpec) (Option α) → Prop
  | zero (keys P) : CheckDisc limit 0 keys P
  | pure (n keys a) : CheckDisc limit n keys (pure a)
  | queryLocal (n keys q k) (query : LocalDisc limit keys q)
      (rest : ∀ r, CheckDisc limit (n + 1) (localKeys keys q r) (k r)) :
      CheckDisc limit (n + 1) keys (.roll (.inl (.inl q)) k)
  | round (n keys out k) (rest : ∀ inbox, CheckDisc limit n ∅ (k inbox)) :
      CheckDisc limit (n + 1) keys (.roll (.inl (.inr out)) k)

theorem LocalDisc.mono {limit limit' : ℕ} {keys keys' : Set HashOutput}
    (hl : limit ≤ limit') (hk : keys ⊆ keys') {q : (LocalSpec C).Domain}
    (h : LocalDisc limit keys q) : LocalDisc limit' keys' q := by
  rcases q with noise | (q | prg)
  · trivial
  · cases q <;> simp only [LocalDisc] at h ⊢
    all_goals first | trivial | exact lt_of_lt_of_le h hl | exact hk h
  · trivial

theorem localKeys_mono {keys keys' : Set HashOutput} (hk : keys ⊆ keys')
    (q : (LocalSpec C).Domain) (r : (LocalSpec C).Range q) :
    localKeys keys q r ⊆ localKeys keys' q r := by
  rcases q with noise | (q | prg)
  · exact hk
  · cases q <;> simp only [localKeys]
    all_goals first | exact hk | exact Set.insert_subset_insert hk
  · exact hk

theorem CheckDisc.mono {limit limit' n : ℕ} {keys keys' : Set HashOutput}
    {P : OracleComp (PartySpec C E RealSpec) (Option α)} (h : CheckDisc limit n keys P)
    (hl : limit ≤ limit') (hk : keys ⊆ keys') : CheckDisc limit' n keys' P := by
  induction h generalizing keys' with
  | zero => exact .zero _ _
  | pure => exact .pure _ _ _
  | queryLocal n keys q k query rest ih =>
    exact .queryLocal n keys' q k (query.mono hl hk)
      (fun r => ih r (localKeys_mono hk q r))
  | round n keys out k rest ih => exact .round n keys' out k (fun r => ih r (Set.Subset.refl _))

theorem CheckDisc.local_inv {limit n : ℕ} {keys : Set HashOutput}
    {q : (LocalSpec C).Domain}
    {k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : CheckDisc limit (n + 1) keys (.roll (.inl (.inl q)) k)) :
    LocalDisc limit keys q ∧ ∀ r, CheckDisc limit (n + 1) (localKeys keys q r) (k r) := by
  cases h with | queryLocal _ _ _ _ query rest => exact ⟨query, rest⟩

theorem CheckDisc.round_inv {limit n : ℕ} {keys : Set HashOutput} {out : Mail C E}
    {k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : CheckDisc limit (n + 1) keys (.roll (.inl (.inr out)) k)) :
    ∀ inbox, CheckDisc limit n ∅ (k inbox) := by
  cases h with | round _ _ _ _ rest => exact rest

/-- Until the first exchange, residual transport must keep the current keys. -/
theorem CheckDisc.residual_keys {limit n k : ℕ} {keys : Set HashOutput}
    {P Q : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : CheckDisc limit n keys P) (r : Residual k P Q) (le : k ≤ n) :
    CheckDisc limit (n - k) (if k = 0 then keys else ∅) Q := by
  induction r generalizing n keys with
  | refl P => simpa using h
  | queryLocal k q cont answer Q r ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa using ih (h.local_inv.2 answer) le
  | round k out cont inbox Q r ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have next := ih (h.round_inv inbox) (by omega : k ≤ n)
    simpa only [Nat.succ_sub_succ_eq_sub, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceIte, ite_self] using next
  | done k out => exact .pure _ _ _

theorem CheckDisc.residual {limit n k : ℕ}
    {P Q : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : CheckDisc limit n ∅ P) (r : Residual k P Q) (le : k ≤ n) :
    CheckDisc limit (n - k) ∅ Q := by
  simpa using h.residual_keys r le

/-- A timed prefix ends at an exchange boundary, so the continuation starts
with no keys. This follows the structural induction of `Residual.timed_bind`. -/
theorem CheckDisc.timed_bind {limit m n : ℕ} {keys : Set HashOutput}
    {oa : OracleComp (PartySpec C E RealSpec) (Option β)}
    (timed : TreeSimCheckTimed m oa) (h : CheckDisc limit m keys oa)
    (f : Option β → OracleComp (PartySpec C E RealSpec) (Option α))
    (abort : f none = Pure.pure none)
    (rest : ∀ a, some a ∈ support oa → CheckDisc limit n ∅ (f (some a))) :
    CheckDisc limit (m + n) keys (oa >>= f) := by
  induction timed generalizing keys with
  | abort m => rw [pure_bind, abort]; exact .pure _ _ _
  | done a =>
    rw [pure_bind, Nat.zero_add]
    exact (rest a (by simp)).mono le_rfl (Set.empty_subset _)
  | queryLocal m q k hk ih =>
    rw [Nat.add_right_comm]
    refine .queryLocal _ _ _ _ h.local_inv.1 fun r => ?_
    rw [Nat.add_right_comm]
    apply ih r (h.local_inv.2 r)
    intro a ha
    apply rest a
    change some a ∈ support (OracleComp.lift (OracleSpec.query
      (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= k)
    rw [mem_support_bind_iff]
    exact ⟨r, by simp; exact Set.mem_univ _, ha⟩
  | round m out k hk ih =>
    rw [Nat.add_right_comm]
    refine .round _ _ _ _ fun inbox => ?_
    apply ih inbox (h.round_inv inbox)
    intro a ha
    apply rest a
    change some a ∈ support (OracleComp.lift (OracleSpec.query
      (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= k)
    rw [mem_support_bind_iff]
    exact ⟨inbox, by simp; exact Set.mem_univ _, ha⟩

theorem CheckDisc.antitone {limit m n : ℕ} {keys : Set HashOutput}
    {P : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : CheckDisc limit n keys P) (le : m ≤ n) : CheckDisc limit m keys P := by
  induction h generalizing m with
  | zero =>
    obtain rfl : m = 0 := by omega
    exact .zero _ _
  | pure => exact .pure _ _ _
  | queryLocal n keys q k query rest ih =>
    cases m with
    | zero => exact .zero _ _
    | succ m => exact .queryLocal _ _ _ _ query (fun r => ih r le)
  | round n keys out k rest ih =>
    cases m with
    | zero => exact .zero _ _
    | succ m => exact .round _ _ _ _ (fun r => ih r (by omega))

/-- Extend a checked prefix with the discipline of every literal residual. -/
theorem CheckDisc.of_residual {limit m n : ℕ} {keys : Set HashOutput}
    {P : OracleComp (PartySpec C E RealSpec) (Option α)} (h : CheckDisc limit m keys P)
    (rest : ∀ Q, Residual m P Q → CheckDisc limit n (if m = 0 then keys else ∅) Q) :
    CheckDisc limit (m + n) keys P := by
  induction P generalizing m keys with
  | pure a => exact .pure _ _ _
  | queryBind t k ih =>
    cases m with
    | zero => simpa using rest _ (.refl _)
    | succ m =>
      rw [Nat.add_right_comm]
      rcases t with (q | out) | impossible
      · refine .queryLocal _ _ _ _ h.local_inv.1 fun r => ?_
        rw [Nat.add_right_comm]
        apply ih r (h.local_inv.2 r)
        intro Q run
        simpa using rest Q (.queryLocal m q k r Q run)
      · refine .round _ _ _ _ fun inbox => ?_
        apply ih inbox (h.round_inv inbox)
        intro Q run
        simpa using rest Q (.round m out k inbox Q run)
      · exact impossible.elim

theorem CheckDisc.timed_party_bind {limit m n : ℕ} {keys : Set HashOutput}
    {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β}
    (timed : TreeSimCheckTimed m p.run) (h : CheckDisc limit m keys p.run)
    (rest : ∀ a, some a ∈ support p.run → CheckDisc limit n ∅ (f a).run) :
    CheckDisc limit (m + n) keys (p >>= f).run := by
  simp only [OptionT.run_bind, Option.elimM]
  exact CheckDisc.timed_bind timed h _ rfl rest

/-- The discipline for a whole program, at every finite horizon. -/
def Disc (limit : ℕ) (keys : Set HashOutput)
    (P : OracleComp (PartySpec C E RealSpec) (Option α)) : Prop :=
  ∀ n, CheckDisc limit n keys P

theorem Disc.pure (limit : ℕ) (keys : Set HashOutput) (a : Option α) :
    Disc (C := C) (E := E) limit keys (Pure.pure a) := fun n => .pure n keys a

theorem Disc.mono {limit limit' : ℕ} {keys keys' : Set HashOutput}
    {P : OracleComp (PartySpec C E RealSpec) (Option α)} (h : Disc limit keys P)
    (hl : limit ≤ limit') (hk : keys ⊆ keys') : Disc limit' keys' P :=
  fun n => (h n).mono hl hk

/-- A whole-program bind may forget keys at its return: the continuation is
required to be valid even with no saved key. Local calls themselves keep keys. -/
theorem Disc.bind {limit : ℕ} {keys : Set HashOutput}
    {P : OracleComp (PartySpec C E RealSpec) (Option α)} (h : Disc limit keys P)
    (f : Option α → OracleComp (PartySpec C E RealSpec) (Option β))
    (rest : ∀ a, a ∈ support P → Disc limit ∅ (f a)) : Disc limit keys (P >>= f) := by
  intro n
  induction P generalizing n keys with
  | pure a =>
    change CheckDisc limit n keys (f a)
    exact (rest a (by change a ∈ support (Pure.pure a : OracleComp (PartySpec C E RealSpec) _); simp) n).mono le_rfl (Set.empty_subset _)
  | queryBind t k ih =>
    cases n with
    | zero => exact .zero _ _
    | succ n =>
      rcases t with (q | out) | impossible
      · refine .queryLocal _ _ _ _ (h (n + 1)).local_inv.1 fun r => ?_
        apply ih r (fun m => ?_) (fun a ha => ?_)
        · cases m with
          | zero => exact .zero _ _
          | succ m => exact (h (m + 1)).local_inv.2 r
        · apply rest a
          change a ∈ support (OracleComp.lift (OracleSpec.query
            (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= k)
          rw [mem_support_bind_iff]
          exact ⟨r, by simp; exact Set.mem_univ _, ha⟩
      · refine .round _ _ _ _ fun inbox => ?_
        apply ih inbox (fun m => (h (m + 1)).round_inv inbox) (fun a ha => ?_)
        apply rest a
        change a ∈ support (OracleComp.lift (OracleSpec.query
          (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= k)
        rw [mem_support_bind_iff]
        exact ⟨inbox, by simp; exact Set.mem_univ _, ha⟩
      · exact impossible.elim

theorem Disc.party_bind {limit : ℕ} {keys : Set HashOutput}
    {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β}
    (h : Disc limit keys p.run)
    (rest : ∀ a, some a ∈ support p.run → Disc limit ∅ (f a).run) :
    Disc limit keys (p >>= f).run := by
  simp only [OptionT.run_bind, Option.elimM]
  apply h.bind
  intro a ha
  cases a with
  | none => exact .pure _ _ _
  | some a => exact rest a ha

open TreeSimHashCount

/-- The two local query domains whose syntax carries the check discipline. -/
def CheckQuery : (LocalSpec C).Domain → Prop
  | .inr (.inl (.coinKey _ _ _)) => True
  | .inr (.inl (.expand _ _)) => True
  | _ => False

theorem quiet_local {limit : ℕ} {keys : Set HashOutput} {q : (LocalSpec C).Domain}
    (h : ¬ CheckQuery q) : LocalDisc limit keys q := by
  rcases q with noise | (q | prg)
  · trivial
  · cases q <;> simp_all [CheckQuery, LocalDisc]
  · trivial

theorem Disc.of_quiet {limit : ℕ} {keys : Set HashOutput}
    {p : PartyM C E RealSpec α} (h : PartyBudget CheckQuery p 0) :
    Disc limit keys p.run := by
  intro n
  unfold PartyBudget at h
  generalize p.run = P at h ⊢
  induction P generalizing n keys with
  | pure a => exact .pure _ _ _
  | queryBind t k ih =>
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query t) >>= k) _ 0 at h
    rw [isQueryBoundP_query_bind_iff] at h
    have notQuery : ¬ PartyQuery CheckQuery t := by
      intro ht
      simp [ht] at h
    have tail : ∀ r, IsQueryBoundP (k r) (PartyQuery (E := E) (G := RealSpec) CheckQuery) 0 := by
      simpa [notQuery] using h.2
    cases n with
    | zero => exact .zero _ _
    | succ n =>
      rcases t with (q | out) | impossible
      · exact .queryLocal _ _ _ _ (quiet_local notQuery) (fun r => ih r _ (tail r))
      · exact .round _ _ _ _ (fun r => ih r _ (tail r))
      · exact impossible.elim

/-- A RunM component uses labels below the end of its allocated interval. -/
def RunDisc (n : ℕ) (p : RunM C E RealSpec α) : Prop :=
  ∀ st limit, st.label + n ≤ limit → Disc limit ∅ (p.run st).run

theorem RunDisc.pure (a : α) : RunDisc (C := C) (E := E) 0 (Pure.pure a) :=
  fun _ _ _ => Disc.pure _ _ _

theorem RunDisc.of_quiet {n : ℕ} {p : RunM C E RealSpec α}
    (h : RunBudget CheckQuery p 0) : RunDisc n p :=
  fun st _ _ => Disc.of_quiet (h st)

theorem RunDisc.bind {m n : ℕ} {p : RunM C E RealSpec α}
    {f : α → RunM C E RealSpec β} (h : RunDisc m p)
    (labels : LockstepLabels m p) (rest : ∀ a, RunDisc n (f a)) :
    RunDisc (m + n) (p >>= f) := by
  intro st limit le
  rw [StateT.run_bind]
  apply (h st limit (by omega)).party_bind
  rintro ⟨a, mid⟩ ha
  apply rest a mid limit
  rw [labels st a mid ha]
  omega

theorem RunDisc.le_bind {m n N : ℕ} {p : RunM C E RealSpec α}
    {f : α → RunM C E RealSpec β} (h : RunDisc m p)
    (labels : LockstepLabels m p) (rest : ∀ a, RunDisc n (f a)) (eq : m + n = N) :
    RunDisc N (p >>= f) := eq ▸ h.bind labels rest

theorem RunDisc.foldlM {δ : Type} (n : ℕ) (f : α → δ → RunM C E RealSpec α)
    (hf : ∀ a b, RunDisc n (f a b)) (hl : ∀ a b, LockstepLabels n (f a b))
    (xs : List δ) (a : α) : RunDisc (xs.length * n) (xs.foldlM f a) := by
  induction xs generalizing a with
  | nil => simpa using RunDisc.pure a
  | cons x xs ih =>
    rw [List.foldlM_cons, List.length_cons]
    exact (hf a x).le_bind (hl a x) ih (by ring)

theorem localKeys_subset (keys : Set HashOutput) (q : (LocalSpec C).Domain)
    (r : (LocalSpec C).Range q) : keys ⊆ localKeys keys q r := by
  rcases q with noise | (q | prg)
  · exact Set.Subset.refl _
  · cases q <;> simp only [localKeys]
    all_goals first | exact Set.Subset.refl _ | exact Set.subset_insert _ _
  · exact Set.Subset.refl _

/-- A local oracle computation preserves all already available keys. -/
theorem CheckDisc.oracle_bind [Field E] [Algebra Bit E] {limit n : ℕ} {keys : Set HashOutput}
    (p : OracleComp (RoSpec C) α)
    (quiet : IsQueryBoundP p (fun q => ¬ LocalDisc limit keys (.inr q)) 0)
    (f : α → PartyM C E RealSpec β)
    (rest : ∀ a, CheckDisc limit n keys (f a).run) :
    CheckDisc limit n keys (oracleStep p >>= f).run := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa only [oracleStep_pure, pure_bind] using rest a
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at quiet
    have allowed : LocalDisc limit keys (.inr q) := by simpa using quiet.1
    have tail : ∀ r, IsQueryBoundP (k r) (fun q => ¬ LocalDisc limit keys (.inr q)) 0 := by
      simpa using quiet.2
    rw [oracleStep_bind, bind_assoc]
    cases n with
    | zero => exact .zero _ _
    | succ n =>
      rcases q with q | q
      all_goals exact .queryLocal n keys _ _ allowed (fun r => (ih r (tail r)).mono le_rfl (localKeys_subset _ _ _))

theorem Disc.oracle_bind [Field E] [Algebra Bit E] {limit : ℕ} {keys : Set HashOutput}
    (p : OracleComp (RoSpec C) α)
    (quiet : IsQueryBoundP p (fun q => ¬ LocalDisc limit keys (.inr q)) 0)
    (f : α → PartyM C E RealSpec β) (rest : ∀ a, Disc limit keys (f a).run) :
    Disc limit keys (oracleStep p >>= f).run :=
  fun n => CheckDisc.oracle_bind p quiet f (fun a => rest a n)


section Gadgets

variable [Field E] [Algebra Bit E]
variable {ι : Type} {G : OracleSpec ι}

theorem checkQuery_counted (t : (LocalSpec C).Domain) (h : CheckQuery t) : Counted t := by
  rcases t with noise | q
  · exact h.elim
  · rcases q with q | prg
    · cases q <;> simp_all [CheckQuery, Counted]
    · exact h.elim

theorem party_quiet_of_zero {p : PartyM C E G α} (h : PartyBound p 0) :
    PartyBudget CheckQuery p 0 := PartyBudget.of_counted checkQuery_counted h

theorem run_quiet_of_zero {p : RunM C E G α} (h : RunBound p 0) :
    RunBudget CheckQuery p 0 := RunBudget.of_counted checkQuery_counted h

variable (K : Constants C E)

-- Port of TreeSimHashCount's zero-budget gadget proofs, with CheckQuery in
-- place of Region. This also excludes expand, which Region does not count.
theorem prg_zero (name : KeyName C) (key : HashOutput) (label idx count : ℕ) :
    IsQueryBoundP (prgBits name key label idx count)
      (fun t => CheckQuery (C := C) (.inr t)) 0 := by
  unfold prgBits
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
  have h := queryBound_mapM (fun t => CheckQuery (C := C) (.inr t))
    (fun position => (query (spec := RoSpec C) (.inr (name, key, label, idx, position)) :
      OracleComp (RoSpec C) Bit)) 0 (List.range count) (fun position _ => ?_)
  · simpa using h
  · change IsQueryBoundP (OracleComp.lift (OracleSpec.query
      (spec := RoSpec C) (.inr (name, key, label, idx, position)))) _ 0
    rw [isQueryBoundP_query_iff]
    simp [CheckQuery]

theorem prss_zero {R : Type} [Zero R] (ctx : Context C)
    (codec : Codec C E R)
    (hd : ∀ name key label idx count, IsQueryBoundP (codec.draw name key label idx count)
      (fun t => CheckQuery (C := C) (.inr t)) 0) (idx count : ℕ) :
    RunBudget CheckQuery (prssRandomness ctx codec idx count : RunM C E G _) 0 := by
  unfold prssRandomness
  refine (run_quiet_of_zero
    (RunBound.freshLabel (C := C) (E := E) (G := G))).bind (m := 0) (fun label => ?_)
  refine (RunBudget.lift (oracle_bound (n := 0) ?_)).bind
    (m := 0) (fun r => ?_)
  · simpa using queryBound_mapM (fun t => CheckQuery (C := C) (.inr t))
      (fun T => if ctx.self ∈ C.holders T then codec.draw (.term T) (ctx.prss.term T) label idx count
        else pure fun _ => 0) 0 C.terms (fun T _ => by
          split_ifs
          · exact hd _ _ _ _ _
          · exact isQueryBoundP_pure _ _ _)
  · refine (RunBudget.lift (oracle_bound (n := 0) ?_)).bind
      (m := 0) (fun Z => .pure _ 0)
    simpa using queryBound_mapM (fun t => CheckQuery (C := C) (.inr t))
      (fun j => if h : j = ctx.self then pure fun _ => 0
        else codec.draw (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) label idx count)
      0 C.parties (fun j _ => by
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · exact hd _ _ _ _ _)

theorem reshare_zero {R : Type} [Field R] (ctx : Context C)
    (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R) (count : ℕ) :
    RunBudget CheckQuery (reshare K ctx codec randomness v count : RunM C E G _) 0 := by
  apply run_quiet_of_zero
  unfold reshare
  exact (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun inbox =>
    (RunBound.record K ctx codec .peer _ count).bind (m := 0) (fun _ => RunBound.pure _))

structure GadgetBounds (gadgets : CheckGadgets C E G) : Prop where
  coin : ∀ count, RunBudget CheckQuery (gadgets.coin count) 0
  mult : ∀ products, RunBudget CheckQuery (gadgets.extendMult products) 0
  elements : ∀ count, RunBudget CheckQuery (gadgets.randElements count) 0
  bits : ∀ count, RunBudget CheckQuery (gadgets.randBits count) 0

theorem gadgets_zero (ctx : Context C) :
    GadgetBounds (realCheckGadgets K ctx : CheckGadgets C E G) := by
  have hd : ∀ name key label idx count, IsQueryBoundP
      ((elementCodec K).draw name key label idx count)
      (fun t => CheckQuery (C := C) (.inr t)) 0 := by
    intro name key label idx count
    unfold elementCodec
    exact isQueryBoundP_bind (prg_zero name key label idx _)
      (fun _ _ => isQueryBoundP_pure _ _ 0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro count
    change RunBudget CheckQuery
      (prssRandomness ctx (elementCodec K) 1 count >>= fun r => coinWith K ctx r count) 0
    refine (prss_zero ctx (elementCodec K) hd 1 count).bind (m := 0) (fun r => ?_)
    unfold coinWith
    exact (RunBudget.lift (party_quiet_of_zero (RunBound.openSh K ctx _ count))).bind
      (m := 0) (fun _ => .pure _ 0)
  · intro products
    change RunBudget CheckQuery
      (prssRandomness ctx (elementCodec K) 0 products.length >>= fun r =>
        reshare K ctx (elementCodec K) r _ products.length) 0
    exact (prss_zero ctx (elementCodec K) hd 0 products.length).bind
      (m := 0) (fun r => reshare_zero K ctx _ r _ _)
  · intro count
    exact prss_zero ctx (elementCodec K) hd 1 count
  · intro count
    exact prss_zero ctx bitCodec prg_zero 2 count

theorem hash_zero (q : Query C) (hq : ¬ CheckQuery (.inr (.inl q))) :
    IsQueryBoundP (hashQuery q) (fun t => CheckQuery (C := C) (.inr t)) 0 := by
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl q))) _ 0
  rw [isQueryBoundP_query_iff]
  exact fun h => (hq h).elim


-- The local expansion lemmas retain membership in the current pass's set.
theorem hash_allowed (limit : ℕ) (keys : Set HashOutput) (q : Query C)
    (h : LocalDisc limit keys (.inr (.inl q))) :
    IsQueryBoundP (hashQuery q) (fun t => ¬ LocalDisc limit keys (.inr t)) 0 := by
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl q))) _ 0
  rw [isQueryBoundP_query_iff]
  simpa using h

theorem expand_allowed (limit : ℕ) (keys : Set HashOutput) (key : HashOutput)
    (mem : key ∈ keys) (count : ℕ) :
    IsQueryBoundP ((List.range count).mapM fun k => elementOfHash K <$> hashQuery (C := C) (.expand key k))
      (fun t => ¬ LocalDisc limit keys (.inr t)) 0 := by
  simpa using queryBound_mapM (fun t => ¬ LocalDisc limit keys (.inr t))
    (fun k => elementOfHash K <$> hashQuery (C := C) (.expand key k)) 0 (List.range count)
    (fun k _ => (isQueryBoundP_map_iff _ _ _).mpr (hash_allowed limit keys _ mem))

theorem findChallenge_allowed (limit : ℕ) (keys : Set HashOutput) (key : HashOutput)
    (mem : key ∈ keys) (tries index : ℕ) :
    IsQueryBoundP (findChallenge K key tries index)
      (fun t => ¬ LocalDisc limit keys (.inr t)) 0 := by
  induction tries generalizing index with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ tries ih =>
    unfold findChallenge
    refine isQueryBoundP_bind (n := 0) (m := 0) (hash_allowed limit keys _ mem) (fun h _ => ?_)
    dsimp only
    split
    · exact isQueryBoundP_pure _ _ _
    · exact ih _

/-- The answer of coinKey is inserted before any local continuation runs. -/
theorem coinKey_bind_disc (ctx : Context C) (st : RunState C) (limit : ℕ)
    (bound : st.label < limit) (f : HashOutput → RunM C E RealSpec α)
    (rest : ∀ key mid, Disc limit (insert key ∅) ((f key).run mid).run) :
    Disc limit ∅ ((coinKey K (realCheckGadgets K ctx) >>= f).run st).run := by
  simp only [coinKey, StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  apply (Disc.of_quiet ((gadgets_zero (G := RealSpec) K ctx).coin 1 st)).party_bind
  rintro ⟨values, mid⟩ _
  intro n
  cases n with
  | zero => exact .zero _ _
  | succ n =>
    change CheckDisc limit (n + 1) ∅ (.roll
      (.inl (.inl (.inr (.inl (.coinKey st.tag st.label
        (values.flatMap fun v => List.ofFn (K.encode v)))))))
      (fun key => ((f key).run mid).run))
    exact .queryLocal _ _ _ _ bound (fun key => rest key mid (n + 1))

theorem runDisc_coinExpand (ctx : Context C) (count : ℕ) :
    RunDisc 1 (coinKey K (realCheckGadgets (G := RealSpec) K ctx) >>= fun key => expand K key count) := by
  intro st limit bound
  apply coinKey_bind_disc K ctx st limit (by omega)
  intro key mid
  simp only [expand, StateT.run_lift]
  exact Disc.oracle_bind _ (expand_allowed K limit (insert key ∅) key (by simp) count)
    _ (fun _ => .pure _ _ _)

theorem runDisc_challenge (ctx : Context C) :
    RunDisc 1 (challenge K (realCheckGadgets (G := RealSpec) K ctx)) := by
  intro st limit bound
  unfold challenge
  apply coinKey_bind_disc K ctx st limit (by omega)
  intro key mid
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply Disc.oracle_bind _ (findChallenge_allowed K limit (insert key ∅) key (by simp) _ _)
  intro r
  cases r <;> exact .pure _ _ _


theorem compare_quiet (ctx : Context C) (salts : Shares C Bit) :
    RunBudget CheckQuery (compareDigests ctx salts : RunM C E G _) 0 := by
  unfold compareDigests
  refine RunBudget.bind_zero (RunBudget.get) (fun s => ?_)
  refine RunBudget.bind_zero (RunBudget.lift (oracle_bound ?_)) (fun ds => ?_)
  · simpa using queryBound_mapM (fun t => CheckQuery (C := C) (.inr t)) _ 0 C.terms
      (fun T _ => by
        split_ifs
        · exact isQueryBoundP_bind (n := 0) (m := 0)
            (hash_zero _ (by simp [CheckQuery])) (fun _ _ => hash_zero _ (by simp [CheckQuery]))
        · exact isQueryBoundP_pure _ _ _)
  · exact RunBudget.bind_zero (RunBudget.lift (party_quiet_of_zero (PartyBound.exchange _))) (fun inbox =>
        RunBudget.lift (party_quiet_of_zero (PartyBound.require _)))



variable [Fintype E] [DecidableEq E]

theorem slice_labels (ctx : Context C) (τ : List E) (count : ℕ)
    (v : Shares C E × Shares C E × E) (j : ℕ) :
    LockstepLabels 2 (sliceStep K ctx (realCheckGadgets (G := RealSpec) K ctx) τ count v j) := by
  rcases v with ⟨xs, ys, d⟩
  unfold sliceStep
  exact (lockstepLabels_extendMult K ctx _).le_bind (fun _ =>
    (lockstepLabels_challenge K ctx).le_bind (fun _ => .pure _) rfl) rfl

theorem halving_labels (ctx : Context C) (width : ℕ)
    (v : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    LockstepLabels 2 (halvingStep K ctx (realCheckGadgets (G := RealSpec) K ctx) width v j) := by
  rcases v with ⟨xs, ys, d⟩
  unfold halvingStep
  exact (lockstepLabels_extendMult K ctx _).le_bind (fun _ =>
    (lockstepLabels_challenge K ctx).le_bind (fun _ => .pure _) rfl) rfl

theorem runDisc_slice (ctx : Context C) (τ : List E) (count : ℕ)
    (v : Shares C E × Shares C E × E) (j : ℕ) :
    RunDisc 2 (sliceStep K ctx (realCheckGadgets (G := RealSpec) K ctx) τ count v j) := by
  rcases v with ⟨xs, ys, d⟩
  unfold sliceStep
  exact (RunDisc.of_quiet ((gadgets_zero K ctx).mult _)).le_bind
    (lockstepLabels_extendMult K ctx _) (fun _ =>
      (runDisc_challenge K ctx).le_bind (lockstepLabels_challenge K ctx)
        (fun _ => .pure _) rfl) rfl

theorem runDisc_halving (ctx : Context C) (width : ℕ)
    (v : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    RunDisc 2 (halvingStep K ctx (realCheckGadgets (G := RealSpec) K ctx) width v j) := by
  rcases v with ⟨xs, ys, d⟩
  unfold halvingStep
  exact (RunDisc.of_quiet ((gadgets_zero K ctx).mult _)).le_bind
    (lockstepLabels_extendMult K ctx _) (fun _ =>
      (runDisc_challenge K ctx).le_bind (lockstepLabels_challenge K ctx)
        (fun _ => .pure _) rfl) rfl

theorem runDisc_final (ctx : Context C) (v : (ℕ → E) × (ℕ → E) × E) :
    RunDisc 4 (finalStep K ctx (realCheckGadgets (G := RealSpec) K ctx) v) := by
  rcases v with ⟨xs, ys, d⟩
  unfold finalStep
  refine (RunDisc.of_quiet ((gadgets_zero K ctx).elements 2)).le_bind
    (lockstepLabels_prssRandomness ctx _ _ _) (n := 3) (fun w => ?_) rfl
  refine (RunDisc.of_quiet ((gadgets_zero K ctx).mult _)).le_bind
    (lockstepLabels_extendMult K ctx _) (n := 2) (fun q => ?_) rfl
  refine (RunDisc.of_quiet ((gadgets_zero K ctx).bits _)).le_bind
    (lockstepLabels_prssRandomness ctx _ _ _) (n := 1) (fun salts => ?_) rfl
  refine (RunDisc.of_quiet (compare_quiet ctx salts.1)).le_bind
    (lockstepLabels_compareDigests ctx _) (n := 1) (fun _ => ?_) rfl
  refine (runDisc_challenge K ctx).le_bind (lockstepLabels_challenge K ctx)
    (n := 0) (fun r => ?_) rfl
  exact RunDisc.of_quiet ((RunBudget.lift (party_quiet_of_zero (RunBound.openSh K ctx _ 3))).bind_zero
    (fun _ => RunBudget.lift (party_quiet_of_zero (PartyBound.require _))))

theorem runDisc_check (ctx : Context C) (tuples : List (Tuple C)) :
    RunDisc (checkLabels (tuples.map (·.count)).sum)
      (check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples) := by
  by_cases hz : (tuples.map (·.count)).sum = 0
  · simp only [check, hz, ↓reduceIte, checkLabels]
    exact .pure _
  · rw [check_eq K ctx _ tuples hz]
    have hs : sliceBits ≤ halvings (tuples.map (·.count)).sum := by unfold halvings; omega
    have labels : LockstepLabels 1 (coinKey K (realCheckGadgets (G := RealSpec) K ctx) >>=
        fun key => expand K key (coins (tuples.map (·.count)).sum)) := (lockstepLabels_coinKey K ctx).le_bind
      (fun key => LockstepLabels.lift (oracleStep _)) (show 1 + 0 = 1 from rfl)
    rw [show checkLabels (tuples.map (·.count)).sum =
      1 + (sliceBits * 2 + ((halvings (tuples.map (·.count)).sum - sliceBits) * 2 + 4)) by
        simp only [checkLabels, if_neg hz]; omega]
    rw [← bind_assoc]
    refine (runDisc_coinExpand K ctx _).bind labels (fun τ => ?_)
    refine (RunDisc.of_quiet (RunBudget.lift (party_quiet_of_zero (PartyBound.require _)))).le_bind
      (LockstepLabels.lift _)
      (n := sliceBits * 2 + ((halvings (tuples.map (·.count)).sum - sliceBits) * 2 + 4))
      (fun _ => ?_) (by omega)
    refine (RunDisc.foldlM 2 _ (runDisc_slice K ctx τ _) (slice_labels K ctx τ _) _ _).le_bind
      (LockstepLabels.foldlM 2 _ (slice_labels K ctx τ _) _ _)
      (n := (halvings (tuples.map (·.count)).sum - sliceBits) * 2 + 4) (fun v => ?_) (by simp)
    exact (RunDisc.foldlM 2 _ (runDisc_halving K ctx _) (halving_labels K ctx _) _ _).le_bind
      (LockstepLabels.foldlM 2 _ (halving_labels K ctx _) _ _) (runDisc_final K ctx) (by simp)


-- Ported from TreeSimHashCount's corresponding zero-budget syntax lemmas.
theorem collector_zero (ctx : Context C) (r : PrssOutput C Bit)
    (v : ℕ → Bit) (count : ℕ) :
    RunBudget CheckQuery (reshareCollector K ctx r v count : RunM C E G _) 0 := by
  apply run_quiet_of_zero
  unfold reshareCollector
  exact (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun inbox =>
    (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun forward =>
      (RunBound.record K ctx bitCodec .collector _ count).bind (m := 0) (fun _ => RunBound.pure _)))

theorem reshareWith_zero (ctx : Context C) (mode : ReshareMode)
    (r : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    RunBudget CheckQuery (reshareWith K ctx mode r v count : RunM C E G _) 0 := by
  cases mode with
  | peer => exact reshare_zero K ctx _ r v count
  | collector => exact collector_zero K ctx r v count

theorem inputShares_zero (ctx : Context C) (job : Job) :
    PartyBudget CheckQuery (inputShares ctx job : PartyM C E G _) 0 := by
  have hp (seed : HashOutput) (xs : List Point) :
      IsQueryBoundP (xs.flatMapM fun x => bitsOfDigest <$> prf (C := C) seed x)
        (fun t => CheckQuery (C := C) (.inr t)) 0 := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.flatMapM_cons]
      refine isQueryBoundP_bind (n := 0) (m := 0) ?_
        (fun ys _ => isQueryBoundP_bind ih (fun zs _ => isQueryBoundP_pure _ _ 0))
      simp only [prf, Functor.map_map, isQueryBoundP_map_iff]
      exact hash_zero _ (by simp [CheckQuery])
  unfold inputShares
  refine (oracle_bound (n := 0) ?_).bind (m := 0) (fun terms => PartyBudget.pure _)
  simpa using queryBound_mapM (fun t => CheckQuery (C := C) (.inr t))
    (fun T => if ctx.self ∈ C.holders T then job.points.flatMapM fun x => bitsOfDigest <$> prf (ctx.keys.seed T) x
      else pure []) 0 C.terms (fun T _ => by
        split_ifs
        · exact hp _ _
        · exact isQueryBoundP_pure _ _ _)


theorem beforeVerify_quiet (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    RunBudget CheckQuery (treeSimCheckBeforeVerify K ctx mode jobs inputs) 0 := by
  have hm : ∀ x y count, RunBudget CheckQuery
      ((realRunGadgets (G := RealSpec) K ctx mode).mult x y count) 0 := by
    intro x y count
    exact (prss_zero ctx bitCodec prg_zero 0 count).bind_zero
      (fun r => reshareWith_zero K ctx mode r _ count)
  have hr : ∀ v count, RunBudget CheckQuery
      ((realRunGadgets (G := RealSpec) K ctx mode).rerand v count) 0 := by
    intro v count
    exact (prss_zero ctx bitCodec prg_zero 0 count).bind_zero
      (fun r => reshare_zero K ctx _ r _ count)
  unfold treeSimCheckBeforeVerify
  refine ((RunBudget.foldlM _ 0 (fun p l => ?_) _ _).mono (by simp)).bind_zero (fun p => ?_)
  · unfold layerBody
    exact (hm _ _ _).bind_zero (fun _ => .pure _ 0)
  · exact (hr _ _).bind_zero (fun _ => .pure _ 0)

theorem batchPrefix_quiet (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    PartyBudget CheckQuery (treeSimCheckBatchPrefix K circuits settings ctx jobs initial) 0 := by
  unfold treeSimCheckBatchPrefix
  have inputs : PartyBudget CheckQuery (jobs.mapM (inputShares ctx) : PartyM C E RealSpec _) 0 := by
    simpa using party_mapM (inputShares ctx) 0 (inputShares_zero ctx) jobs
  exact inputs.bind (fun inputs => (beforeVerify_quiet K ctx _ _ inputs _).bind
    (fun _ => .pure _))

theorem localPrelude_quiet (gate : OracleComp (LocalSpec C) (Option Unit))
    (quiet : IsQueryBoundP gate CheckQuery 0) :
    PartyBudget CheckQuery (treeLockstepLocalPrelude (E := E) gate) 0 := by
  unfold treeLockstepLocalPrelude
  refine (localStep_bound (E := E) (G := RealSpec) quiet).bind (m := 0) fun out => ?_
  cases out with
  | none => exact party_quiet_of_zero PartyBound.failure
  | some _ => exact .pure _

open TreeCheckWalkCoverage

/-- The actual opening tail contains only copy hashes. -/
theorem openTail_quiet (i : C.Party) (count : ℕ) (v : Shares C Bit) (inbox : Mail C E) :
    IsQueryBoundP (openTail K i count v inbox) CheckQuery 0 := by
  unfold openTail
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
  apply IsQueryBoundP.liftComp_subSpec (p := fun t => CheckQuery (C := C) (.inr t))
    (fun _ => Iff.rfl)
  unfold treeSimOpenCopyHashes
  simpa using queryBound_mapM (fun t => CheckQuery (C := C) (.inr t)) _ 0 C.terms
    (fun _ _ => hash_zero _ (by simp [CheckQuery]))

theorem quiet_allowed (limit : ℕ) (keys : Set HashOutput) (p : OracleComp (RoSpec C) α)
    (h : IsQueryBoundP p (fun q => CheckQuery (.inr q)) 0) :
    IsQueryBoundP p (fun q => ¬ LocalDisc limit keys (.inr q)) 0 :=
  IsQueryBoundP.of_imp (fun _ hnot => by
    by_contra hquiet
    exact hnot (quiet_local hquiet)) h

set_option backward.isDefEq.respectTransparency false in
-- Port of TreeSimCheckTimed.exchange_bind, retaining the syntactic query discipline.
theorem CheckDisc.exchange_bind (limit n : ℕ) (keys : Set HashOutput) (out : Mail C E)
    (k : Mail C E → PartyM C E RealSpec α)
    (hk : ∀ inbox, CheckDisc limit n ∅ (k inbox).run) :
    CheckDisc limit (n + 1) keys (exchange out >>= k).run := by
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
  apply CheckDisc.round
  intro inbox
  change CheckDisc limit n ∅ (exchangeResume k inbox)
  unfold exchangeResume
  split_ifs
  · exact .pure _ _ _
  · simpa only [OptionT.run_pure, pure_bind, Option.elim_some] using hk inbox

theorem openRep_first (ctx : Context C) (v : Shares C Bit) (count : ℕ)
    (limit : ℕ) (k : (ℕ → Bit) → PartyM C E RealSpec α) :
    CheckDisc limit 1 ∅ (openRep K ctx v count >>= k).run := by
  unfold openRep
  simp only [bind_assoc, pure_bind]
  refine CheckDisc.oracle_bind _ (quiet_allowed limit ∅ _ ?_) _ (fun _ => ?_)
  · simpa using queryBound_mapM (fun t => CheckQuery (C := C) (.inr t)) _ 0 C.terms
      (fun _ _ => hash_zero _ (by simp [CheckQuery]))
  · exact CheckDisc.exchange_bind limit 0 ∅ _ _ (fun _ => .zero _ _)

end Gadgets

section Batch

open TreeCheckWalkCoverage

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (D : C.Coalition)
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C))

/-- The first pass of any batch is quiet, including its preceding opening tail. -/
theorem caller_first (j limit : ℕ) (caller : Caller C) (i : C.Party)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0) :
    CheckDisc limit 1 ∅ (callerProgram K D circuits settings top tree x setup j caller i).run := by
  unfold callerProgram
  rw [treeSimCheckBatchAudit_run_prefix]
  let ctx : Context C := ⟨i, x i, setupKeys setup i⟩
  let jobs := (lockstepChunks settings caller.encoding tree).getD j []
  let initial := (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
    (lockstepChunks settings caller.encoding tree) j, j)
  have timed := treeLockstep_localPrelude_timed (caller.tail i) _ _
    (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs initial)
  have disc := Disc.of_quiet (limit := limit) (keys := ∅)
    ((localPrelude_quiet (E := E) _ quiet).bind
      (fun _ => batchPrefix_quiet K circuits settings ctx jobs initial))
  have first : CheckDisc limit 1 ∅
      ((treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
        treeSimCheckBatchPrefix K circuits settings ctx jobs initial) >>= fun data =>
          treeSimCheckBatchFinish K circuits ctx jobs initial data >>=
            callerCont K circuits settings top tree x setup j caller i).run :=
    (CheckDisc.timed_party_bind (n := 0) timed (disc _)
      (fun _ _ => .zero _ _)).antitone (by omega)
  simpa only [bind_assoc] using first

/-- A complete earlier batch only uses labels below the next batch start. -/
theorem caller_batch (j limit : ℕ) (current : j < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0)
    (bound : lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings tree) (j + 1) ≤ limit) :
    CheckDisc limit (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j [])) ∅
      (callerProgram K D circuits settings top tree x setup j caller i).run := by
  unfold callerProgram
  rw [TreeCheckWalkState.lockstepChunks_getD_first settings tree caller.encoding j current,
    TreeCheckWalkState.lockstepStart_first circuits settings tree _ caller.encoding j current.le,
    treeSimCheckBatchAudit_run_prefix]
  set ctx : Context C := ⟨i, x i, setupKeys setup i⟩
  set jobs := (firstChunks settings tree).getD j []
  set start := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) j
  have parameter : ctx.keys.parameter = (x (refHolder D K.publicTerm)).parameter := same
  rw [show (treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
      (treeSimCheckBatchPrefix K circuits settings ctx jobs (start, j) >>=
        treeSimCheckBatchFinish K circuits ctx jobs (start, j)) >>=
          callerCont K circuits settings top tree x setup j caller i) =
      ((treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
        treeSimCheckBatchPrefix K circuits settings ctx jobs (start, j)) >>= fun data =>
          treeSimCheckBatchFinish K circuits ctx jobs (start, j) data >>=
            callerCont K circuits settings top tree x setup j caller i) by simp only [bind_assoc]]
  have prefixTimed := treeLockstep_localPrelude_timed (caller.tail i) _ _
    (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs (start, j))
  have prefixQuiet := (localPrelude_quiet (E := E) _ quiet).bind
    (fun _ => batchPrefix_quiet K circuits settings ctx jobs (start, j))
  rw [parameter] at prefixTimed
  rw [show batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter jobs =
      (depth (jobs.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) * settings.mode.rounds + 1) +
        (checkLabels (batchCount circuits (x (refHolder D K.publicTerm)).parameter jobs) + 1) by
      unfold batchRounds; omega]
  apply CheckDisc.timed_party_bind prefixTimed (Disc.of_quiet prefixQuiet _)
  intro data hdata
  obtain ⟨-, -, hprefix⟩ := treeSimCheck_some_bind _ _ _ hdata
  obtain ⟨-, hlabel, -, -, -⟩ :=
    treeSimCheckBatchPrefix_state K circuits settings ctx jobs (start, j) data hprefix
  have hcount : (data.2.1.2.map (·.count)).sum = batchCount circuits ctx.keys.parameter jobs := by
    unfold treeSimCheckBatchPrefix at hprefix
    obtain ⟨inputs, _, hrest⟩ := treeSimCheck_some_bind _ _ _ hprefix
    obtain ⟨q, hq, he⟩ := treeSimCheck_some_bind _ _ _ hrest
    have he' : data = (inputs, q) := by simpa only [OptionT.run_pure, support_pure,
      Set.mem_singleton_iff, Option.some.injEq] using he
    subst data
    exact treeSimCheckBeforeVerify_count K ctx settings.mode _ inputs start j q.1 q.2 hq
  rw [parameter] at hcount hlabel
  unfold treeSimCheckBatchFinish treeSimCheckAfterVerify
  simp only [bind_assoc, pure_bind]
  have checkTimed := check_timed K ctx data.2.1.2 data.2.2
  have checkDisc := runDisc_check K ctx data.2.1.2 data.2.2 limit (by
    rw [hcount, hlabel]
    rw [lockstepStart_succ circuits _ _ j current] at bound
    unfold batchLabels at bound
    simpa only [start, jobs, Nat.add_assoc, Prod.fst] using bound)
  rw [hcount] at checkTimed
  apply CheckDisc.timed_party_bind checkTimed
  · simpa only [hcount] using checkDisc (checkLabels (data.2.1.2.map (·.count)).sum)
  · intro checked _
    exact openRep_first K ctx _ _ limit _


set_option maxHeartbeats 1000000 in
/-- Strengthening of `TreeCheckWalkState.residual_batch`: the constructed caller
retains the literal quiet opening tail. The source proof is copied with only
this extra certificate, rather than inferring it from its final existential. -/
theorem residual_batch_quiet (j : ℕ) (next : j + 1 < (firstChunks settings tree).length)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    {Q : OracleComp (PartySpec C E RealSpec) (Option (TreeCheckWalkDef.Output (C := C)))}
    (h : Residual (batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings tree).getD j [])) (callerProgram K D circuits settings top tree x setup j caller i).run Q) :
    Q = pure none ∨ ∃ caller' : Caller C, caller'.encoding = caller.encoding ∧
      (caller'.records i).length = (caller.records i).length + 1 ∧
      (caller'.outputs i).length = (caller.outputs i).length + 1 ∧
      IsQueryBoundP (caller'.tail i) CheckQuery 0 ∧
      Q = (callerProgram K D circuits settings top tree x setup (j + 1) caller' i).run := by
  have current : j < (firstChunks settings tree).length := by omega
  unfold callerProgram at h
  rw [TreeCheckWalkState.lockstepChunks_getD_first settings tree caller.encoding j current,
    TreeCheckWalkState.lockstepStart_first circuits settings tree _ caller.encoding j current.le,
    treeSimCheckBatchAudit_run_prefix] at h
  set ctx : Context C := ⟨i, x i, setupKeys setup i⟩
  set jobs := (firstChunks settings tree).getD j []
  set start := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) j
  have parameter : ctx.keys.parameter = (x (refHolder D K.publicTerm)).parameter := same
  rw [show (treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
      (treeSimCheckBatchPrefix K circuits settings ctx jobs (start, j) >>=
        treeSimCheckBatchFinish K circuits ctx jobs (start, j)) >>=
          callerCont K circuits settings top tree x setup j caller i) =
      ((treeLockstepLocalPrelude (caller.tail i) >>= fun _ =>
        treeSimCheckBatchPrefix K circuits settings ctx jobs (start, j)) >>= fun data =>
          treeSimCheckBatchFinish K circuits ctx jobs (start, j) data >>=
            callerCont K circuits settings top tree x setup j caller i) by
    simp only [bind_assoc]] at h
  have prefixTimed := treeLockstep_localPrelude_timed (caller.tail i) _ _
    (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs (start, j))
  rw [parameter] at prefixTimed
  rw [show batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter jobs =
      (depth (jobs.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) * settings.mode.rounds + 1) +
        (checkLabels (batchCount circuits (x (refHolder D K.publicTerm)).parameter jobs) + 1) by
      unfold batchRounds
      omega] at h
  rcases Residual.party_bind prefixTimed h with none | ⟨data, hdata, h⟩
  · exact .inl none
  obtain ⟨-, -, hprefix⟩ := treeSimCheck_some_bind _ _ _ hdata
  obtain ⟨-, hlabel, -, -, -⟩ :=
    treeSimCheckBatchPrefix_state K circuits settings ctx jobs (start, j) data hprefix
  have hcount : (data.2.1.2.map (·.count)).sum = batchCount circuits ctx.keys.parameter jobs := by
    unfold treeSimCheckBatchPrefix at hprefix
    obtain ⟨inputs, _, hrest⟩ := treeSimCheck_some_bind _ _ _ hprefix
    obtain ⟨q, hq, he⟩ := treeSimCheck_some_bind _ _ _ hrest
    have he' : data = (inputs, q) := by simpa only [OptionT.run_pure, support_pure,
      Set.mem_singleton_iff, Option.some.injEq] using he
    subst data
    exact treeSimCheckBeforeVerify_count K ctx settings.mode _ inputs start j q.1 q.2 hq
  rw [parameter] at hcount hlabel
  unfold treeSimCheckBatchFinish treeSimCheckAfterVerify at h
  simp only [bind_assoc, pure_bind] at h
  have checkTimed := check_timed K ctx data.2.1.2 data.2.2
  rw [hcount] at checkTimed
  rcases Residual.party_bind checkTimed h with none | ⟨checked, hchecked, h⟩
  · exact .inl none
  have finalLabel := lockstepLabels_check K ctx data.2.1.2 data.2.2 checked.1 checked.2 hchecked
  rw [hcount, hlabel] at finalLabel
  rcases residual_openRep K ctx _ _ _ h with none | ⟨inbox, rfl⟩
  · exact .inl none
  refine .inr ?_
  rw [callerCont_step K circuits settings top tree x setup j next caller i _ (openTail K ctx.self
      (outputsOf (List.map (fun x => circuits ctx.keys.parameter x.kind) jobs)).length data.2.1.1 inbox)]
  set count := (outputsOf (List.map (fun x => circuits ctx.keys.parameter x.kind) jobs)).length
  set value := assemble (List.map (fun x => circuits ctx.keys.parameter x.kind) jobs) fun g =>
    ∑ T, treeSimOpenCopy K ctx.self count data.2.1.1 inbox T g
  refine ⟨stepCaller caller i (some value, [⟨ctx, jobs, (start, j), data.1, data.2.1.2, data.2.2, value,
    checked.2⟩]) (openTail K ctx.self count data.2.1.1 inbox), rfl, by simp [stepCaller],
    by simp [stepCaller], openTail_quiet K ctx.self count data.2.1.1 inbox, ?_⟩
  have labels : checked.2.label =
      lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) (j + 1) := by
    rw [lockstepStart_succ circuits _ _ j current, finalLabel]
    dsimp only [start, jobs]
    unfold batchLabels
    omega
  unfold callerProgram
  rw [TreeCheckWalkState.lockstepChunks_getD_first settings tree _ (j + 1) next,
    TreeCheckWalkState.lockstepStart_first circuits settings tree _ _ (j + 1) next.le]
  simp only [stepCaller, labels]

theorem batchStart_succ (parameter : PublicParameter) (j : ℕ)
    (current : j < (firstChunks settings tree).length) :
    batchStart circuits settings tree parameter (j + 1) =
      batchStart circuits settings tree parameter j +
        batchRounds circuits settings.mode parameter ((firstChunks settings tree).getD j []) := by
  simp only [batchStart, List.take_add_one, List.map_append, List.sum_append,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem current, Option.toList_some,
    Option.getD_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem batchStart_mono (parameter : PublicParameter) {j j' : ℕ} (le : j ≤ j') :
    batchStart circuits settings tree parameter j ≤ batchStart circuits settings tree parameter j' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le le
  unfold batchStart
  rw [List.take_add, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

/-- A window through complete earlier batches and the first quiet pass of
batch `j`. The induction retains each actual opening tail at its boundary. -/
theorem caller_window (b j : ℕ) (first : j < (firstChunks settings tree).length) (le : b ≤ j)
    (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0) :
    CheckDisc (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) j)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j -
        batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter b + 1) ∅
      (callerProgram K D circuits settings top tree x setup b caller i).run := by
  by_cases equal : b = j
  · subst b
    simpa only [Nat.sub_self, Nat.zero_add] using
      caller_first K D circuits settings top tree x setup j _ caller i quiet
  · have current : b < (firstChunks settings tree).length := by omega
    have next : b + 1 < (firstChunks settings tree).length := by omega
    have before : b + 1 ≤ j := by omega
    have disc := caller_batch K D circuits settings top tree x setup b _ current caller i same quiet
      (lockstepStart_mono circuits _ _ before)
    have order := batchStart_mono circuits settings tree
      (x (refHolder D K.publicTerm)).parameter before
    have succ := batchStart_succ circuits settings tree (x (refHolder D K.publicTerm)).parameter b current
    rw [show batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j -
        batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter b + 1 =
      batchRounds circuits settings.mode (x (refHolder D K.publicTerm)).parameter
        ((firstChunks settings tree).getD b []) +
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j -
        batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter (b + 1) + 1) by omega]
    apply disc.of_residual
    intro Q run
    rcases residual_batch_quiet K D circuits settings top tree x setup b next caller i same run with
      aborted | ⟨caller', _, _, _, quiet', rfl⟩
    · rw [aborted]
      exact .pure _ _ _
    · simpa only [ite_self] using
        caller_window (b + 1) j first before caller' i same quiet'
termination_by j - b

/-- Initial-caller form, with the actual tail condition kept explicit. -/
theorem caller_initial_checkDisc (caller : Caller C) (i : C.Party)
    (same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : IsQueryBoundP (caller.tail i) CheckQuery 0)
    (j : ℕ) (first : j < (firstChunks settings tree).length) :
    CheckDisc (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) j)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j + 1) ∅
      (callerProgram K D circuits settings top tree x setup 0 caller i).run := by
  simpa only [batchStart, List.take_zero, List.map_nil, List.sum_nil, Nat.sub_zero] using
    caller_window K D circuits settings top tree x setup 0 j first (Nat.zero_le _) caller i same quiet

/-- The actual first caller satisfies the discipline through the first pass
of every first-run checkpoint. Setup rejection remains in the literal tail. -/
theorem initial_checkDisc (dealt : DealtInputs D x) (i : C.Party)
    (j : ℕ) (first : j < (firstChunks settings tree).length) :
    CheckDisc (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) j)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j + 1) ∅
      (callerProgram K D circuits settings top tree x setup 0 (firstCaller setup) i).run := by
  apply caller_initial_checkDisc K D circuits settings top tree x setup _ i _ _ j first
  · obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl
  · exact isQueryBoundP_pure _ _ _

variable (A : Adversary C E (Keys C) PEmpty PEmpty)

/-- The same certificate on the scheduler's actual initial program. -/
theorem initial_program_checkDisc
    (start : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (dealt : DealtInputs D x) (i : C.Party) (j : ℕ)
    (first : j < (firstChunks settings tree).length) :
    CheckDisc (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) j)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j + 1) ∅
      ((TreeCheckWalkDef.initial K circuits settings top tree x start).program i).run := by
  obtain ⟨head, rest, chunked⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos (by omega : 0 < (firstChunks settings tree).length))
  rw [initial_program K D A circuits settings top tree x start head rest chunked i, boundary_program]
  exact initial_checkDisc K D circuits settings top tree x start.1.2 dealt i j first

end Batch

end TreeCheckHonestDisc
end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckHonestDisc.CheckDisc.residual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckHonestDisc.CheckDisc.residual

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckHonestDisc.runDisc_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckHonestDisc.runDisc_check

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckHonestDisc.initial_checkDisc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckHonestDisc.initial_checkDisc

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckHonestDisc.initial_program_checkDisc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.TreeCheckHonestDisc.initial_program_checkDisc
