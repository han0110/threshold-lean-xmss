import ThresholdLeanXmssSecurity.Proof.LifetimeSlotCoupling
import ThresholdLeanXmssSecurity.Proof.LifetimeIdealKeyLink

/-!
# Key provenance in the separated lifetime slot world

`SlotKeyInv` follows the actual `markedKernel`: its last admitted slot controls the
mode and suspended PRSS phase; the parts history records each admitted start's
actual `prssInitialData` sample, including the dealer prefix of an ideal start.
Shared and selected rounds can extend their respective tables only under the
cached derivation answers of their own sampled parts. Every request preserves
previous hash answers, including signing, dealer, clear, and final-test calls.

The selected ghost remains active after settlement until the next admitted start,
then freezes. Historical overlap witnesses retain their parts and cached answers.
`markedGame_keyLink` carries this invariant and its supported request history
through the actual keygen prefix and adversary. `markedGame_overlap` exhibits
two distinct started selected/shared slots, their actual sampling prefixes, and
one common derivation answer in the actual final cache.

The proof uses `LifetimeIdealKeyLink`'s local phase and reveal-row facts,
`stepRound_ok`, and `LifetimeSlotCoupling`'s exact request decompositions.
Pinned/current leanVM and VCVio sources were searched for support invariants;
the threshold slot scheduler requires the source-specific induction here.
These are support statements, with no probability or query-budget transport claim.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section

namespace ThresholdLeanXmssSecurity.LifetimeSlotKeyLink

open LifetimeSlots LifetimeSlotTransport LifetimeSlotCoupling
open LifetimeIdealKeyLink (RunPhase reveal_rowKey runPhase_mono)

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

variable {C : Committee} {E : Type}

/-- New entries in a table are restricted to the specified PRG addresses. -/
def TableWithin (allowed : PrgInput C → Prop) (before after : StreamCache C) : Prop :=
  ∀ x, (after x).isSome → (before x).isSome ∨ allowed x

/-- World evaluation preserves all previous hash answers and restricts new stream entries. -/
def WorldWithin (allowed : PrgInput C → Prop) (before after : WorldState C) : Prop :=
  before.2.1 ≤ after.2.1 ∧ TableWithin allowed before.1 after.1

theorem worldWithin_refl (allowed : PrgInput C → Prop) (s : WorldState C) :
    WorldWithin allowed s s := ⟨le_rfl, fun _ h => Or.inl h⟩

theorem worldWithin_trans {allowed : PrgInput C → Prop} {s t u : WorldState C}
    (h₁ : WorldWithin allowed s t) (h₂ : WorldWithin allowed t u) :
    WorldWithin allowed s u :=
  ⟨h₁.1.trans h₂.1, fun x hx => (h₂.2 x hx).elim (h₁.2 x) Or.inr⟩

theorem streamDraw_within (s : StreamCache C) (x : PrgInput C) (r : Bit × StreamCache C)
    (hr : r ∈ support (streamDraw s x)) : TableWithin (· = x) s r.2 := by
  unfold streamDraw at hr
  cases hx : s x with
  | some b =>
    simp only [hx, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact fun _ h => Or.inl h
  | none =>
    simp only [hx, support_map, Set.mem_image] at hr
    obtain ⟨b, _, rfl⟩ := hr
    intro y hy
    by_cases he : y = x
    · exact Or.inr he
    · change ((s.cacheQuery x b) y).isSome = true at hy
      exact Or.inl (by rwa [QueryCache.cacheQuery_of_ne _ _ he] at hy)

/-- Only the emulated honest copy can add stream-table entries. -/
def Unallowed (D : C.Coalition) (allowed : PrgInput C → Prop) : (LifetimeKeygenPrograms.Spec3 C).Domain → Prop
  | .inl (.inr (.inr (.inr x))) => Hidden D x.1 ∧ ¬ allowed x
  | _ => False

/-- Every evaluated emulation preserves hash answers, including dealer and clear calls. -/
theorem evalEmulation_cache (prims : Primitives) {α : Type} (p : EmulationM C α)
    (s : WorldState C) (r : α × WorldState C)
    (hr : r ∈ support ((evalEmulation prims p).run s)) : s.2.1 ≤ r.2.2.1 := by
  simp only [evalEmulation, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  exact (grows_worldAnswer prims).simulateQ _ _ _ hu

/-- A permitted local call creates only a permitted stream entry. -/
theorem localKernel_within (prims : Primitives) (D : C.Coalition)
    (allowed : PrgInput C → Prop) (q : (LifetimeKeygenPrograms.Spec3 C).Domain)
    (hq : ¬ Unallowed D allowed q) (s : WorldState C)
    (r : (LifetimeKeygenPrograms.Spec3 C).Range q × WorldState C)
    (hr : r ∈ support ((localKernel prims D q).run s)) : WorldWithin allowed s r.2 := by
  refine ⟨evalEmulation_cache prims _ s r hr, ?_⟩
  rcases q with (q | q) | q
  · change r ∈ support ((evalEmulation prims ((emulatedRoles D).adversary _)).run s) at hr
    rw [evalEmulation_adversary] at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    exact fun _ hx => Or.inl hx
  · change r ∈ support ((evalEmulation prims ((emulatedRoles D).honest _)).run s) at hr
    by_cases hidden : ∃ x, q = .inr (.inr x) ∧ Hidden D x.1
    · obtain ⟨x, rfl, hx⟩ := hidden
      erw [evalEmulation_hidden prims D x hx] at hr
      simp only [support_map, Set.mem_image] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      have allowedX : allowed x := not_not.mp (fun hn => hq ⟨hx, hn⟩)
      intro y hy
      have hw : (s.1 y).isSome ∨ y = x := streamDraw_within _ _ _ ha y hy
      rcases hw with hy | rfl
      · exact Or.inl hy
      · exact Or.inr allowedX
    · erw [LifetimePrfTransportProof.emul_honest_other D q (by
        intro x hx hh; exact hidden ⟨x, hx, hh⟩), evalEmulation_lift] at hr
      simp only [support_map, Set.mem_image] at hr
      obtain ⟨a, _, rfl⟩ := hr
      exact fun _ hx => Or.inl hx
  · change r ∈ support ((evalEmulation prims (StateT.lift (liftM (free _)))).run s) at hr
    rw [evalEmulation_lift] at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨a, _, rfl⟩ := hr
    exact fun _ hx => Or.inl hx

/-- The local restriction composes through an arbitrary adaptive local program. -/
theorem localRun_within (prims : Primitives) (D : C.Coalition)
    (allowed : PrgInput C → Prop) {α : Type}
    (p : OracleComp (LifetimeKeygenPrograms.Spec3 C) α)
    (hp : IsQueryBoundP p (Unallowed D allowed) 0) (s : WorldState C) (r : α × WorldState C)
    (hr : r ∈ support ((simulateQ (localKernel prims D) p).run s)) : WorldWithin allowed s r.2 := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure a =>
    have he : r = (a, s) := by simpa using hr
    rw [he]
    exact worldWithin_refl _ _
  | query_bind q f ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have hq : ¬ Unallowed D allowed q := hp.1.resolve_right (by omega)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨u, hu, hr⟩ := hr
    exact worldWithin_trans (localKernel_within prims D allowed q hq s u hu)
      (ih u.1 (by simpa [hq] using hp.2 u.1) u.2 hr)

/-- Every actual tail request preserves the current hash cache. -/
theorem rawKernel_cache [Field E] [Algebra Bit E]
    (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts k : ℕ)
    (D : C.Coalition) (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)
    (sep : Bool) (q : (TailSpec C E).Domain) (s : Physical C E)
    (r : TailSpec C E q × Physical C E)
    (hr : r ∈ support ((rawKernel K circuits settings attempts k D keys h prims sep q).run s)) :
    s.2.2.1 ≤ r.2.2.2.1 := by
  change r ∈ support ((evalSlot prims (tailHandler K circuits settings attempts k D keys h sep q)).run s) at hr
  simp only [evalSlot, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  exact evalEmulation_cache prims _ s.2 u hu

theorem markedKernel_cache [Field E] [Algebra Bit E]
    (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts k : ℕ)
    (D : C.Coalition) (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)
    (q : (TailSpec C E).Domain) (s : Marked D E)
    (r : TailSpec C E q × Marked D E)
    (hr : r ∈ support ((markedKernel K circuits settings attempts k D keys h prims q).run s)) :
    s.1.2.2.1 ≤ r.2.1.2.2.1 := by
  simp only [markedKernel, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  exact rawKernel_cache K circuits settings attempts k D keys h prims true q s.1 u hu

/-- The three-copy image of a world program: its free copy uses the emulated honest table. -/
def worldTo : QueryImpl (WorldSpec C) (OracleComp (LifetimeKeygenPrograms.Spec3 C))
  | .inl (.inl t) => OracleComp.lift (OracleSpec.query (spec := LifetimeKeygenPrograms.Spec3 C) (.inl (.inl t)))
  | .inl (.inr _) => pure false
  | .inr t => OracleComp.lift (OracleSpec.query (spec := LifetimeKeygenPrograms.Spec3 C) (.inl (.inr t)))

def toWorld : OracleComp (WorldSpec C) →ᵐ OracleComp (LifetimeKeygenPrograms.Spec3 C) where
  toFun _ p := simulateQ worldTo p
  toFun_pure' _ := simulateQ_pure _ _
  toFun_bind' _ _ := simulateQ_bind _ _ _

theorem toWorld_free {α : Type} (p : OracleComp (LocalSpec C) α) :
    toWorld (free p) = LifetimeKeygenPrograms.emulCopy p := by
  change simulateQ worldTo (simulateQ _ p) = _
  rw [LifetimeEmulatedBudget.simulateQ_comp]
  congr 1

theorem toWorld_roles : LifetimeEmulatedBudget.RolesHom (toWorld (C := C))
    worldRoles LifetimeKeygenPrograms.emulRoles3 := by
  constructor
  · intro α p
    change simulateQ worldTo (worldRoles.adversary p) = _
    rw [LifetimeRealBad.worldAdversary_eq_simulateQ, LifetimeEmulatedBudget.simulateQ_comp]
    change _ = LifetimeKeygenPrograms.advCopy p
    unfold LifetimeKeygenPrograms.advCopy
    congr 1
    funext t
    rw [LifetimeRealBad.adversary_query]
    exact simulateQ_spec_query _ _
  · exact fun p => toWorld_free p

/-- The three-copy program has the actual emulated round as its evaluation. -/
theorem emulated_round [Field E] [Algebra Bit E] (D : C.Coalition)
    {α : Type} (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E RealSpec α) :
    stepRound (emulatedRoles D) D (roundAdversary (I := PEmpty) sent) noFunctionality () steps =
    LifetimeKeygenPrograms.H3 D (toWorld (stepRound worldRoles D
      (roundAdversary (I := Keys C) sent) noFunctionality () steps)) := by
  rw [hom_stepRound toWorld _ _ toWorld_roles,
    hom_stepRound (LifetimeKeygenPrograms.H3 D) _ _ (LifetimeKeygenPrograms.rolesHom_emul D)]
  rfl

/-- Calls after the reveal round can create entries only under a row key. -/
theorem toWorld_allowed (D : C.Coalition) (rows : RevealRows C) {α : Type}
    (p : OracleComp (WorldSpec C) α) (hp : IsQueryBoundP p (ThresholdLeanXmssSecurity.Unallowed rows) 0) :
    IsQueryBoundP (toWorld p) (Unallowed D (fun x => Hidden D x.1 ∧ RowKey rows x.1 x.2.1)) 0 := by
  refine qb0_simulateQ _ (fun t ht => ?_) p hp
  rcases t with (t | t) | t
  · exact (isQueryBoundP_query_iff _ _ _).2 fun hb => hb.elim
  · exact isQueryBoundP_pure _ _ _
  · apply (isQueryBoundP_query_iff _ _ _).2
    rcases t with a | q | x
    · exact False.elim
    · exact False.elim
    · intro hb
      exact (hb.2 ⟨hb.1, not_not.mp ht⟩).elim

/-- PRSS setup and reveal computations with no stream call run on the literal free copy. -/
theorem plain_noStream (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α)
    (hp : IsQueryBoundP p LocalStream 0) : Plain D p := by
  induction p using OracleComp.inductionOn with
  | pure a => exact plain_pure D a
  | query_bind q f ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have hq : ¬ LocalStream q := hp.1.resolve_right (by omega)
    apply plain_bind D _ _ ?_ (fun a => ih a (by simpa [hq] using hp.2 a))
    exact LifetimePrfTransportProof.emul_honest_other D q (by
      intro x he hx; subst he; exact hq trivial)

/-- A stream-free honest computation leaves the whole stream table and log unchanged. -/
theorem emulated_noStream (prims : Primitives) (D : C.Coalition) {α : Type}
    (p : OracleComp (LocalSpec C) α) (hp : IsQueryBoundP p LocalStream 0)
    (s : WorldState C) :
    (evalEmulation prims ((emulatedRoles D).honest p)).run s =
      (fun r => (r.1, (s.1, r.2, s.2.2))) <$>
        (simulateQ (localAnswer prims) p).run s.2.1 := by
  rw [plain_noStream D p hp]
  change (evalEmulation prims (StateT.lift (liftM (free p)))).run s = _
  rw [evalEmulation_lift]
  rw [worldAnswer, simulateQ_free]

section RoundPhase
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (D : C.Coalition) (keys : C.Party → Keys C)

theorem emulated_commit (sent : C.Party → C.Party → Option (Msg E))
    (data : C.Party → Parts C × List HashOutput)
    (cont : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput) :
    stepRound (emulatedRoles D) D (roundAdversary (I := PEmpty) sent) noFunctionality ()
      (fun i => suspendStep (cont i) (prssInitialSteps D data i)) =
    pure ((), (fun i => suspendStep (cont i) (prssRevealStep D
      (fun i => (C.parties.any fun j => Msg.isAbort (prssCommitInbox D data sent i j)) = false)
      (fun i => (data i).1) (prssCommitInbox D data sent) i)), sent) := by
  rw [emulated_round, stepRound_prssCommit_bind]
  simp [roundAdversary, worldRoles, counted, toWorld, LifetimeKeygenPrograms.H3]

theorem emulated_reveal (sent : C.Party → C.Party → Option (Msg E))
    (active : C.Party → Prop) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (cont : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput) :
    stepRound (emulatedRoles D) D (roundAdversary (I := PEmpty) sent) noFunctionality ()
      (fun i => suspendStep (cont i) (prssRevealStep D active parts committed i)) = (do
      let rows ← (emulatedRoles D).honest (prssRevealRows D active parts committed sent)
      pure ((), (fun i => suspendStep (cont i) (prssFinishStep i (rows i))), sent)) := by
  rw [emulated_round, stepRound_prssReveal_bind]
  simp only [roundAdversary, worldRoles, counted, simulateQ_pure, pure_bind,
    liftComp_pure, MonadHom.mmap_bind, MonadHom.mmap_pure, toWorld_free]
  change (do
    let rows ← simulateQ (LifetimeKeygenPrograms.impl3 D)
      (LifetimeKeygenPrograms.emulCopy (prssRevealRows D active parts committed sent))
    pure ((), (fun i => suspendStep (cont i) (prssFinishStep i (rows i))), sent)) = _
  rw [LifetimeKeygenPrograms.impl3_emulCopy]

/-- At every round, new entries have the cached derivation answer of this run's parts. -/
theorem round_phase (parts : C.Party → Parts C)
    (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E RealSpec TreeOutput) (s : WorldState C)
    (phase : RunPhase D keys parts steps s.2.1)
    (r : (Unit × (C.Party → Step C E RealSpec TreeOutput) ×
      (C.Party → C.Party → Option (Msg E))) × WorldState C)
    (hr : r ∈ support ((evalEmulation prims (stepRound (emulatedRoles D) D
      (roundAdversary (I := PEmpty) sent) noFunctionality () steps)).run s)) :
    WorldWithin (fun x => Hidden D x.1 ∧ r.2.2.1 (LifetimeIdealKeyLink.hiddenInput parts x.1) = some x.2.1) s r.2 ∧
      RunPhase D keys parts r.1.2.1 r.2.2.1 := by
  rcases phase with ⟨cont, data, hc, hp, rfl⟩ | ⟨cont, active, committed, hc, rfl⟩ |
    ⟨rows, hs, hk⟩
  · rw [emulated_commit, evalEmulation_pure] at hr
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨worldWithin_refl _ _, Or.inr (Or.inl ⟨cont, _, _, hc, by rw [hp]⟩)⟩
  · rw [emulated_reveal, evalEmulation_bind] at hr
    simp only [StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨u, hu, hr⟩ := hr
    rw [evalEmulation_pure] at hr
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rw [emulated_noStream prims D _ (qb0_prssRevealRows D active parts committed sent)] at hu
    simp only [support_map, Set.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨⟨(grows_localAnswer prims).simulateQ _ _ _ hv, fun _ hx => Or.inl hx⟩,
      Or.inr (Or.inr ⟨v.1, LifetimeIdealKeyLink.finish_stepOk keys cont hc v.1, ?_⟩)⟩
    exact fun name key hn hk => reveal_rowKey prims D active parts committed sent s.2.1 v hv name key hn hk
  · rw [emulated_round] at hr
    erw [← localRun_eq] at hr
    have hround := stepRound_ok rows D (roundAdversary (I := Keys C) sent) () steps hs
    have hw := localRun_within prims D _ _ (toWorld_allowed D rows _ hround.1) s r hr
    refine ⟨⟨hw.1, fun x hx => ?_⟩, Or.inr (Or.inr ⟨rows, ?_, ?_⟩)⟩
    · rcases hw.2 x hx with old | ⟨hn, hrow⟩
      · exact Or.inl old
      · exact Or.inr ⟨hn, hw.1 (hk x.1 x.2.1 hn hrow)⟩
    · exact hround.2 r.1 (support_simulateQ_subset _ _
        (LifetimeSlotCoupling.localRun_support prims D _ s r hr))
    · exact fun name key hn hrow => hw.1 (hk name key hn hrow)

end RoundPhase

open LifetimeJointLink (Slot slotTree)

/-- A slot whose admitted start has incremented its tree's attempt counter. -/
def Started {attempts : ℕ} (slot : Slot attempts) (st : LifetimeState C E) : Prop :=
  slotAttempt slot < LifetimeProof.runsAt st (slotTree slot)

/-- The concrete selected slot in the finite slot order. -/
def selectedSlot (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) : Slot attempts :=
  (slotOrder attempts).symm k

/-- Actual parts, indexed by the run's fixed tree and attempt. -/
abbrev PartsHistory (C : Committee) (attempts : ℕ) := Slot attempts → C.Party → Parts C

/-- The retained key-origin witness uses two distinct started slots and one actual cache. -/
def KeyOrigin (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (_D : C.Coalition)
    (parts : PartsHistory C attempts) (st : LifetimeState C E) (cache : HashCache C)
    (name : KeyName C) : Prop :=
  ∃ (shared : Slot attempts) (key : HashOutput),
    worldMode attempts k true shared = .shared ∧ shared ≠ selectedSlot attempts k ∧
    Started shared st ∧ Started (selectedSlot attempts k) st ∧
    cache (LifetimeIdealKeyLink.hiddenInput (parts shared) name) = some key ∧
    cache (LifetimeIdealKeyLink.hiddenInput (parts (selectedSlot attempts k)) name) = some key

/-- Tables and historical overlaps retain the original parts and cached answers. -/
structure Tables (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (parts : PartsHistory C attempts) (s : Marked D E) : Prop where
  shared : ∀ x, (s.1.2.1 x).isSome → Hidden D x.1 ∧
    ∃ slot, worldMode attempts k true slot = .shared ∧ Started slot s.1.1.1 ∧
      s.1.2.2.1 (LifetimeIdealKeyLink.hiddenInput (parts slot) x.1) = some x.2.1
  selected : ∀ x, (s.2.selected x).isSome → Hidden D x.1 ∧
    Started (selectedSlot attempts k) s.1.1.1 ∧
    s.1.2.2.1 (LifetimeIdealKeyLink.hiddenInput (parts (selectedSlot attempts k)) x.1) = some x.2.1
  overlaps : ∀ name ∈ s.2.overlaps, KeyOrigin attempts k D parts s.1.1.1 s.1.2.2.1 name.1

/-- The last actually started slot controls dispatch and the retained selected marker. -/
def ModeState (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (last : Option (Slot attempts)) (s : Marked D E) : Prop :=
  match last with
  | none => s.1.1.1.running = none ∧ s.1.1.2 = none ∧ s.2.active = false
  | some slot => Started slot s.1.1.1 ∧
      s.2.active = decide (slot = selectedSlot attempts k) ∧
      (worldMode attempts k true slot = .shared → s.1.1.2 = none) ∧
      (worldMode attempts k true slot = .own → s.1.1.2 = some (s.2.selected, none)) ∧
      (worldMode attempts k true slot = .ideal →
        ∃ own output, s.1.1.2 = some (own, some output))

/-- The actual boundary invariant, including phase, retained table, and accumulated witnesses. -/
structure SlotKeyInv (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (keys : C.Party → Keys C) (parts : PartsHistory C attempts)
    (last : Option (Slot attempts)) (s : Marked D E) : Prop where
  tables : Tables attempts k D parts s
  mode : ModeState attempts k D last s
  started : s.2.started = decide (Started (selectedSlot attempts k) s.1.1.1)
  phase : ∀ tree fuel steps, s.1.1.1.running = some (tree, fuel, steps) →
    ∃ slot, last = some slot ∧ slotTree slot = tree ∧
      (worldMode attempts k true slot ≠ .ideal → RunPhase D keys (parts slot) steps s.1.2.2.1)

theorem selected_mode (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) :
    worldMode attempts k true (selectedSlot attempts k) = .own := by
  simp [worldMode, selectedSlot]

theorem own_iff_selected (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (slot : Slot attempts) :
    worldMode attempts k true slot = .own ↔ slot = selectedSlot attempts k := by
  constructor
  · intro hm
    have eq : ((slotOrder attempts) slot).val = k.val := by
      by_contra hn
      simp [worldMode, hn] at hm
      split_ifs at hm
    exact (slotOrder attempts).injective (by simpa [selectedSlot] using Fin.ext eq)
  · rintro rfl
    exact selected_mode attempts k

theorem shared_ne_selected (attempts : ℕ) (k : Fin (lifetimeRuns attempts))
    (slot : Slot attempts) (hm : worldMode attempts k true slot = .shared) :
    slot ≠ selectedSlot attempts k := by
  intro he
  rw [he, selected_mode] at hm
  cases hm

/-- A currently visible overlap supplies the original two-run witness. -/
theorem overlapNames_origin (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (parts : PartsHistory C attempts) (s : Marked D E) (tables : Tables attempts k D parts s)
    (name : {name : KeyName C // Hidden D name})
    (hn : name ∈ overlapNames D s.1.2.1 s.2.selected) :
    KeyOrigin attempts k D parts s.1.1.1 s.1.2.2.1 name.1 := by
  simp only [overlapNames, Finset.mem_filter, Finset.mem_univ, true_and] at hn
  obtain ⟨key, a, b, ha, hb⟩ := hn
  obtain ⟨_, slot, hm, hs, hc⟩ := tables.shared (name.1, key, a) ha
  obtain ⟨_, hsel, hcache⟩ := tables.selected (name.1, key, b) hb
  exact ⟨slot, key, hm, shared_ne_selected attempts k slot hm, hs, hsel, hc, hcache⟩

/-- Historical overlap entries use their retained witnesses, even after a later start. -/
theorem overlap_of_inv (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (keys : C.Party → Keys C) (parts : PartsHistory C attempts)
    (last : Option (Slot attempts)) (s : Marked D E)
    (inv : SlotKeyInv attempts k D keys parts last s)
    (name : {name : KeyName C // Hidden D name}) (hn : name ∈ s.2.overlaps) :
    KeyOrigin attempts k D parts s.1.1.1 s.1.2.2.1 name.1 :=
  inv.tables.overlaps name hn

section StartSource
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (D : C.Coalition) (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)

/-- The real ceremony continuation attached to the initial setup wait. -/
def realCont (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (i : C.Party) (prss : PrssKeys C) : PartyM C E RealSpec TreeOutput :=
  ceremonyAfterSetup K circuits settings ⟨i, keys i, prss⟩ ((st.top i).getD emptyTop) tree

/-- The exact sampling decomposition of an admitted start, including the ideal dealer prefix. -/
def SampledStart (mode : RunMode) (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (cache : HashCache C)
    (r : ((C.Party → Step C E RealSpec TreeOutput) × Option (Option TreeOutput)) × HashCache C)
    (parts : C.Party → Parts C) : Prop :=
  match mode with
  | .ideal => ∃ dealer ∈ support ((simulateQ (worldAnswer prims) (free (liftComp
        (dealerCeremony circuits settings (keys h).parameter (honestSeeds D keys)
          ((st.top h).getD emptyTop) tree) (LocalSpec C)))).run cache),
      ∃ cont : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput,
        (∀ i, ceremonyWith K circuits settings
          (simGadgets K settings D dealer.1.2 ((worldEnv D circuits settings).clear
            (keys h).parameter (simSeeds D keys) tree)) i
          ⟨(keys h).parameter, simSeeds D keys, fun _ => 0⟩ ((st.top h).getD emptyTop) tree =
            prssSetup i >>= cont i) ∧
        ∃ data ∈ support ((simulateQ (localAnswer prims) (prssInitialData D)).run dealer.2),
          r = ((fun i => suspendStep (cont i) (prssInitialSteps D data.1 i), some dealer.1.1), data.2) ∧
          parts = fun i => (data.1 i).1
  | _ => ∃ data ∈ support ((simulateQ (localAnswer prims) (prssInitialData D)).run cache),
      r = ((fun i => suspendStep (realCont K circuits settings keys st tree i)
        (prssInitialSteps D data.1 i), none), data.2) ∧ parts = fun i => (data.1 i).1

/-- Supported start results expose their actual sampled setup data on the same cache path. -/
theorem startCore_sampled (mode : RunMode) (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree)
    (cache : HashCache C)
    (r : ((C.Party → Step C E RealSpec TreeOutput) × Option (Option TreeOutput)) × HashCache C)
    (hr : r ∈ support ((simulateQ (worldAnswer prims)
      (startCore K circuits settings D keys h mode st tree)).run cache)) :
    ∃ parts, SampledStart K circuits settings D keys h prims mode st tree cache r parts := by
  have setup : ∀ (cont : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput),
      simulateQ (worldAnswer prims) (startSteps worldRoles D (fun i => prssSetup i >>= cont i)) =
        (fun data i => suspendStep (cont i) (prssInitialSteps D data i)) <$>
          simulateQ (localAnswer prims) (prssInitialData D) := by
    intro cont
    rw [startSteps_prssSetup_bind, simulateQ_map, worldAnswer, simulateQ_free]
  cases mode with
  | ideal =>
    simp only [startCore, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨dealer, hd, u, hu, hr⟩ := hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    have continuation : ∃ cont : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput,
        ∀ i, ceremonyWith K circuits settings
          (simGadgets K settings D dealer.1.2 ((worldEnv D circuits settings).clear
            (keys h).parameter (simSeeds D keys) tree)) i
          ⟨(keys h).parameter, simSeeds D keys, fun _ => 0⟩ ((st.top h).getD emptyTop) tree =
          prssSetup i >>= cont i := by
      unfold ceremonyWith
      exact ⟨_, fun _ => rfl⟩
    obtain ⟨cont, hc⟩ := continuation
    simp only [hc] at hu
    rw [setup, StateT.run_map] at hu
    simp only [support_map, Set.mem_image] at hu
    obtain ⟨data, hdata, rfl⟩ := hu
    exact ⟨_, dealer, hd, cont, hc, data, hdata, rfl, rfl⟩
  | own | shared =>
    simp only [startCore, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨u, hu, hr⟩ := hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    change u ∈ support ((simulateQ (worldAnswer prims) (startSteps worldRoles D
      (fun i => prssSetup i >>= realCont K circuits settings keys st tree i))).run cache) at hu
    rw [setup, StateT.run_map] at hu
    simp only [support_map, Set.mem_image] at hu
    obtain ⟨data, hdata, rfl⟩ := hu
    exact ⟨_, data, hdata, rfl, rfl⟩

/-- Nonideal starts stop at the first wait with their actual parts and no stream draw. -/
theorem sampledStart_phase {mode : RunMode} (hm : mode ≠ .ideal)
    {st : LifetimeState C E} {tree : ThresholdLeanXmss.Tree} {cache : HashCache C}
    {r : ((C.Party → Step C E RealSpec TreeOutput) × Option (Option TreeOutput)) × HashCache C}
    {parts : C.Party → Parts C}
    (hs : SampledStart K circuits settings D keys h prims mode st tree cache r parts) :
    r.1.2 = none ∧ RunPhase D keys parts r.1.1 r.2 := by
  cases mode with
  | ideal => exact (hm rfl).elim
  | own | shared =>
    obtain ⟨data, _, rfl, rfl⟩ := hs
    exact ⟨rfl, Or.inl ⟨realCont K circuits settings keys st tree, data.1,
      fun i prss => POk.ceremonyAfterSetup K circuits settings _ tree, rfl, rfl⟩⟩

end StartSource

theorem Started.mono {attempts : ℕ} {slot : Slot attempts} {s t : LifetimeState C E}
    (counts : ∀ tree, LifetimeProof.runsAt s tree ≤ LifetimeProof.runsAt t tree)
    (hs : Started slot s) : Started slot t := lt_of_lt_of_le hs (counts _)

theorem keyOrigin_mono {attempts : ℕ} {k : Fin (lifetimeRuns attempts)} {D : C.Coalition}
    {parts parts' : PartsHistory C attempts} {s t : LifetimeState C E} {cache cache' : HashCache C}
    (counts : ∀ tree, LifetimeProof.runsAt s tree ≤ LifetimeProof.runsAt t tree)
    (grow : cache ≤ cache') (same : ∀ slot, Started slot s → parts' slot = parts slot)
    {name : KeyName C} (origin : KeyOrigin attempts k D parts s cache name) :
    KeyOrigin attempts k D parts' t cache' name := by
  obtain ⟨slot, key, hm, hn, hs, hsel, hc, hcsel⟩ := origin
  refine ⟨slot, key, hm, hn, hs.mono counts, hsel.mono counts, ?_, ?_⟩
  · rw [same slot hs]
    exact grow hc
  · rw [same _ hsel]
    exact grow hcsel

/-- New overlaps use current table origins; old overlaps retain their historical cache witnesses. -/
theorem tables_record {attempts : ℕ} {k : Fin (lifetimeRuns attempts)} {D : C.Coalition}
    {parts parts' : PartsHistory C attempts} {s t : Marked D E}
    (before : Tables attempts k D parts s)
    (counts : ∀ tree, LifetimeProof.runsAt s.1.1.1 tree ≤ LifetimeProof.runsAt t.1.1.1 tree)
    (grow : s.1.2.2.1 ≤ t.1.2.2.1)
    (same : ∀ slot, Started slot s.1.1.1 → parts' slot = parts slot)
    (shared : ∀ x, (t.1.2.1 x).isSome → Hidden D x.1 ∧
      ∃ slot, worldMode attempts k true slot = .shared ∧ Started slot t.1.1.1 ∧
        t.1.2.2.1 (LifetimeIdealKeyLink.hiddenInput (parts' slot) x.1) = some x.2.1)
    (selected : ∀ x, (t.2.selected x).isSome → Hidden D x.1 ∧
      Started (selectedSlot attempts k) t.1.1.1 ∧
      t.1.2.2.1 (LifetimeIdealKeyLink.hiddenInput (parts' (selectedSlot attempts k)) x.1) = some x.2.1)
    (seen : t.2.overlaps ⊆ s.2.overlaps ∪ overlapNames D t.1.2.1 t.2.selected) :
    Tables attempts k D parts' t := by
  refine ⟨shared, selected, fun name hn => ?_⟩
  rcases Finset.mem_union.1 (seen hn) with old | new
  · exact keyOrigin_mono counts grow same (before.overlaps name old)
  · simp only [overlapNames, Finset.mem_filter, Finset.mem_univ, true_and] at new
    obtain ⟨key, a, b, ha, hb⟩ := new
    obtain ⟨_, slot, hm, hs, hc⟩ := shared (name.1, key, a) ha
    obtain ⟨_, hsel, hcache⟩ := selected (name.1, key, b) hb
    exact ⟨slot, key, hm, shared_ne_selected attempts k slot hm, hs, hsel, hc, hcache⟩

theorem active_aux {attempts : ℕ} {k : Fin (lifetimeRuns attempts)} {D : C.Coalition}
    {last : Option (Slot attempts)} {s : Marked D E}
    (mode : ModeState attempts k D last s) (active : s.2.active = true) :
    s.1.1.2 = some (s.2.selected, none) := by
  cases last with
  | none => exact (Bool.noConfusion (mode.2.2.symm.trans active))
  | some slot =>
    have he : slot = selectedSlot attempts k := of_decide_eq_true (mode.2.1.symm.trans active)
    exact mode.2.2.2.1 ((own_iff_selected attempts k slot).2 he)

theorem active_started {attempts : ℕ} {k : Fin (lifetimeRuns attempts)} {D : C.Coalition}
    {keys : C.Party → Keys C} {parts : PartsHistory C attempts}
    {last : Option (Slot attempts)} {s : Marked D E}
    (inv : SlotKeyInv attempts k D keys parts last s) (active : s.2.active = true) :
    s.2.started = true := by
  cases last with
  | none => exact Bool.noConfusion (inv.mode.2.2.symm.trans active)
  | some slot =>
    have he : slot = selectedSlot attempts k := of_decide_eq_true (inv.mode.2.1.symm.trans active)
    rw [inv.started]
    exact decide_eq_true (he ▸ inv.mode.1)

/-- This request contains no admitted ceremony start. -/
def NoStart (attempts : ℕ) (D : C.Coalition) (q : (TailSpec C E).Domain) (st : LifetimeState C E) : Prop :=
  ∀ tree, q = .inl (.inr (.start tree)) → ¬ LifetimeProof.canStart attempts D st tree

theorem advanceGhost_keep {attempts : ℕ} {k : Fin (lifetimeRuns attempts)} {D : C.Coalition}
    {keys : C.Party → Keys C} {parts : PartsHistory C attempts}
    {last : Option (Slot attempts)} {s : Marked D E}
    (inv : SlotKeyInv attempts k D keys parts last s) (q : (TailSpec C E).Domain)
    (nostart : NoStart attempts D q s.1.1.1) (after : Physical C E)
    (aux : after.1.2 = s.1.1.2) :
    advanceGhost attempts k D q s.1 after s.2 = recordWorld D s.2 after.2 := by
  have same : (let selected := if s.2.active then
      (after.1.2.map Prod.fst).getD s.2.selected else s.2.selected
    Ghost.mk s.2.active (s.2.started || s.2.active) selected
      (s.2.overlaps ∪ overlapNames D after.2.1 selected)) = recordWorld D s.2 after.2 := by
    cases ha : s.2.active with
    | false => simp [ha, recordWorld]
    | true =>
      rw [aux, active_aux inv.mode ha]
      simp [ha, active_started inv ha, recordWorld]
  rcases q with (q | q) | q
  · exact same
  · cases q <;> try exact same
    rename_i tree
    simpa only [advanceGhost, if_neg (nostart tree rfl)] using same
  · exact same

/-- Requests that frame the running ceremony and both stream tables retain the invariant. -/
theorem quiet_inv {attempts : ℕ} {k : Fin (lifetimeRuns attempts)} {D : C.Coalition}
    {keys : C.Party → Keys C} {parts : PartsHistory C attempts}
    {last : Option (Slot attempts)} {s : Marked D E}
    (inv : SlotKeyInv attempts k D keys parts last s)
    (life : LifetimeState C E) (shared : StreamCache C) (cache : HashCache C) (log : CallLog C)
    (domain : ∀ x, (shared x).isSome → (s.1.2.1 x).isSome)
    (counts : ∀ tree, LifetimeProof.runsAt life tree = LifetimeProof.runsAt s.1.1.1 tree)
    (running : life.running = s.1.1.1.running) (grow : s.1.2.2.1 ≤ cache) :
    SlotKeyInv attempts k D keys parts last
      (((life, s.1.1.2), (shared, cache, log)), recordWorld D s.2 (shared, cache, log)) := by
  have countsLe : ∀ tree, LifetimeProof.runsAt s.1.1.1 tree ≤ LifetimeProof.runsAt life tree :=
    fun tree => le_of_eq (counts tree).symm
  have startedEq : ∀ slot : Slot attempts, Started slot life ↔ Started slot s.1.1.1 := by
    intro slot
    unfold Started
    rw [counts]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine tables_record inv.tables countsLe grow (fun _ _ => rfl) ?_ ?_ (fun _ hn => hn)
    · intro x hx
      obtain ⟨hidden, slot, hm, hs, hc⟩ := inv.tables.shared x (domain x hx)
      exact ⟨hidden, slot, hm, hs.mono countsLe, grow hc⟩
    · intro x hx
      obtain ⟨hidden, hs, hc⟩ := inv.tables.selected x hx
      exact ⟨hidden, hs.mono countsLe, grow hc⟩
  · cases last with
    | none => exact ⟨running.trans inv.mode.1, inv.mode.2⟩
    | some slot => exact ⟨inv.mode.1.mono countsLe, inv.mode.2⟩
  · change s.2.started = decide (Started _ life)
    rw [startedEq]
    exact inv.started
  · intro tree fuel steps hr
    obtain ⟨slot, hs, ht, hp⟩ := inv.phase tree fuel steps (running ▸ hr)
    exact ⟨slot, hs, ht, fun hm => runPhase_mono D keys grow (hp hm)⟩

/-- The frame needed for requests that do not advance a ceremony. -/
def QuietResult (s t : Physical C E) : Prop :=
  t.1.2 = s.1.2 ∧ (∀ tree, LifetimeProof.runsAt t.1.1 tree = LifetimeProof.runsAt s.1.1 tree) ∧
  t.1.1.running = s.1.1.running ∧ ∀ x, (t.2.1 x).isSome → (s.2.1 x).isSome

section QuietRequests
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (k : Fin (lifetimeRuns attempts))
variable (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)

theorem quiet_marked (q : (TailSpec C E).Domain) (s : Marked D E)
    (parts : PartsHistory C attempts) (last : Option (Slot attempts))
    (inv : SlotKeyInv attempts k D keys parts last s)
    (nostart : NoStart attempts D q s.1.1.1)
    (r : TailSpec C E q × Marked D E)
    (hr : r ∈ support ((markedKernel K circuits settings attempts k D keys h prims q).run s))
    (frame : ∀ u ∈ support ((rawKernel K circuits settings attempts k D keys h prims true q).run s.1),
      QuietResult s.1 u.2) : SlotKeyInv attempts k D keys parts last r.2 := by
  simp only [markedKernel, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  obtain ⟨aux, counts, running, domain⟩ := frame u hu
  rw [advanceGhost_keep inv q nostart u.2 aux]
  have hi := quiet_inv inv u.2.1.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 domain counts running
    (rawKernel_cache K circuits settings attempts k D keys h prims true q s.1 u hu)
  simpa only [← aux] using hi

/-- The free copy cannot write the shared stream table, independently of its hash calls. -/
theorem freeCopy_quiet (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (LifetimeKeygenPrograms.freeCopy p) (Unallowed D (fun _ => False)) 0 := by
  unfold LifetimeKeygenPrograms.freeCopy
  refine qb0_simulateQ (q := Unallowed D (fun _ => False)) _ (fun t _ => ?_) p (qb0_false p)
  exact (isQueryBoundP_query_iff _ _ _).2 False.elim

theorem signing3_quiet (q : TsigQuery C) (st : LifetimeState C E) :
    IsQueryBoundP (signing3 K circuits settings attempts D keys h q st)
      (Unallowed D (fun _ => False)) 0 := by
  let lift : ∀ {α : Type}, OracleComp (RoSpec C) α → OracleComp (LifetimeKeygenPrograms.Spec3 C) α :=
    fun p => LifetimeKeygenPrograms.freeCopy (liftComp p _)
  have hlift : ∀ {α : Type} (p : OracleComp (RoSpec C) α),
      IsQueryBoundP (lift p) (Unallowed D (fun _ => False)) 0 := fun p => freeCopy_quiet D _
  have hs : ∀ (i : C.Party) (q : TsigQuery C) (st : LifetimeState C E),
      IsQueryBoundP ((tsigOracles lift (ThresholdLeanXmss.signerDealt lift keys
        (fun x => lift (prfValue (honestSeeds D keys) x)) st i) q).run st.sign)
        (Unallowed D (fun _ => False)) 0 := by
    intro i q st
    exact LifetimeIdealBad.tsig_quiet _ lift (fun p _ => hlift p) _
      ⟨fun _ => hlift _, fun _ _ _ _ => hlift _, fun _ => isQueryBoundP_pure _ _ _⟩ q st.sign
  have signAs : ∀ (i : C.Party) (q : TsigQuery C) (st : LifetimeState C E),
      IsQueryBoundP (LifetimeProof.signAs LifetimeKeygenPrograms.baseRoles3 keys
        (fun x => lift (prfValue (honestSeeds D keys) x)) i q st)
        (Unallowed D (fun _ => False)) 0 := by
    intro i q st
    exact qb0_bind (hs i q st) fun _ => isQueryBoundP_pure _ _ _
  unfold signing3
  cases q with
  | corrupt i => exact isQueryBoundP_pure _ _ _
  | tree b =>
    rw [LifetimeProof.run_sign_tree]
    exact signAs h (.tree b) st
  | round1 i J e message =>
    rw [LifetimeProof.run_round1]
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact signAs i (.round1 i J e message) _
  | round2 i J e message parts =>
    rw [LifetimeProof.run_round2]
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact signAs i (.round2 i J e message parts) _

theorem signing3_frame (q : TsigQuery C) (st : LifetimeState C E)
    (r : (TsigSpec C).Range q × LifetimeState C E)
    (hr : r ∈ support (signing3 K circuits settings attempts D keys h q st)) :
    (∀ tree, LifetimeProof.runsAt r.2 tree = LifetimeProof.runsAt st tree) ∧ r.2.running = st.running := by
  unfold signing3 at hr
  cases q with
  | corrupt i =>
    simp only [lifetimeOraclesWith, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨fun _ => rfl, rfl⟩
  | tree b =>
    rw [LifetimeProof.run_sign_tree] at hr
    exact LifetimeProof.signAs_frame _ _ _ _ _ _ _ hr
  | round1 i J e message =>
    rw [LifetimeProof.run_round1] at hr
    split_ifs at hr
    · simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨fun _ => rfl, rfl⟩
    · have hf := LifetimeProof.signAs_frame _ _ _ _ _ _ _ hr
      exact hf
  | round2 i J e message parts =>
    rw [LifetimeProof.run_round2] at hr
    split_ifs at hr
    · simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨fun _ => rfl, rfl⟩
    · have hf := LifetimeProof.signAs_frame _ _ _ _ _ _ _ hr
      exact hf

theorem finish3_quiet (forgery : Forgery) (st : LifetimeState C E) :
    IsQueryBoundP (finish3 D keys h forgery st) (Unallowed D (fun _ => False)) 0 := by
  unfold finish3
  split
  · exact isQueryBoundP_pure _ _ _
  · cases hp : st.publicKey (keys h).parameter h with
    | none => exact isQueryBoundP_pure _ _ _
    | some pair =>
      rcases pair with ⟨parameter, top⟩
      exact LifetimeIdealBad.forgeryWins_quiet (Unallowed D (fun _ => False))
        (fun p => LifetimeKeygenPrograms.freeCopy (liftComp p _))
        (fun p _ => freeCopy_quiet D _) _
        (LifetimeIdealBad.dealtWith_quiet _ _ (fun p _ => freeCopy_quiet D _) _ _ _ _
          (fun _ => freeCopy_quiet D _)) _ _

end QuietRequests

theorem fresh_start {attempts : ℕ} {slot : Slot attempts} {st : LifetimeState C E}
    {tree : ThresholdLeanXmss.Tree} (hs : startSlot attempts st tree = some slot) :
    ¬ Started slot st := by
  unfold Started
  rw [startSlot_tree attempts st tree slot hs, startSlot_attempt attempts st tree slot hs]
  exact Nat.lt_irrefl _

theorem parts_update_agree {attempts : ℕ} {slot : Slot attempts} {st : LifetimeState C E}
    {tree : ThresholdLeanXmss.Tree} (hs : startSlot attempts st tree = some slot)
    (parts : PartsHistory C attempts) (new : C.Party → Parts C) :
    ∀ old, Started old st → Function.update parts slot new old = parts old := by
  intro old ho
  apply Function.update_of_ne
  intro he
  subst old
  exact fresh_start hs ho

theorem settle_running_source (D : C.Coalition) (kind : Option (Option TreeOutput))
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (steps : C.Party → Step C E RealSpec TreeOutput)
    (hr : (match kind with | none => st.settle D | some output => settleIdeal D output st).running =
      some (tree, fuel, steps)) : st.running = some (tree, fuel, steps) := by
  cases kind with
  | none =>
    exact (LifetimeProof.settle_running D st (by rw [hr]; exact Option.some_ne_none _)).symm.trans hr
  | some output =>
    unfold settleIdeal at hr
    cases hs : st.running with
    | none => simp [hs] at hr
    | some r =>
      simp only [hs] at hr
      split_ifs at hr
      · cases ht : r.1 <;> simp [ht] at hr
      · exact hs.symm.trans hr

theorem startLife_running_source (D : C.Coalition) (st : LifetimeState C E)
    (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (r : (C.Party → Step C E RealSpec TreeOutput) × Option (Option TreeOutput))
    (tree' : ThresholdLeanXmss.Tree) (fuel' : ℕ) (steps' : C.Party → Step C E RealSpec TreeOutput)
    (hr : (startLife D st tree fuel r).running = some (tree', fuel', steps')) :
    tree' = tree ∧ fuel' = fuel ∧ steps' = r.1 := by
  have he := settle_running_source D r.2
    { countStart st tree with running := some (tree, fuel, r.1) } tree' fuel' steps' hr
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  exact ⟨he.1.symm, he.2.1.symm, he.2.2.symm⟩

def startGhost (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (slot : Slot attempts) (shared : StreamCache C) (g : Ghost D) : Ghost D :=
  let active := decide (slot = selectedSlot attempts k)
  let selected := if active then ∅ else g.selected
  ⟨active, g.started || active, selected, g.overlaps ∪ overlapNames D shared selected⟩

theorem advanceGhost_start (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (tree : ThresholdLeanXmss.Tree) (slot : Slot attempts)
    (can : LifetimeProof.canStart attempts D s.1.1.1 tree)
    (hs : startSlot attempts s.1.1.1 tree = some slot)
    (life : LifetimeState C E) (kind : Option (Option TreeOutput)) (cache : HashCache C) :
    advanceGhost attempts k D (.inl (.inr (.start tree))) s.1
      ((life, startAux (worldMode attempts k true slot) kind), (s.1.2.1, cache, s.1.2.2.2)) s.2 =
    startGhost attempts k D slot s.1.2.1 s.2 := by
  simp only [advanceGhost, if_pos can, hs, Option.map_some, Option.some.injEq]
  rw [selected_test]
  by_cases he : slot = selectedSlot attempts k
  · rw [he, selected_mode]
    simp [startAux, startGhost, selectedSlot]
  · simp [startGhost, selectedSlot] at he ⊢
    simp [he]

section StartInvariant
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (k : Fin (lifetimeRuns attempts))
variable (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)

theorem start_inv (s : Marked D E) (parts : PartsHistory C attempts)
    (last : Option (Slot attempts)) (inv : SlotKeyInv attempts k D keys parts last s)
    (tree : ThresholdLeanXmss.Tree) (slot : Slot attempts)
    (hs : startSlot attempts s.1.1.1 tree = some slot)
    (r : ((C.Party → Step C E RealSpec TreeOutput) × Option (Option TreeOutput)) × HashCache C)
    (new : C.Party → Parts C)
    (sampled : SampledStart K circuits settings D keys h prims (worldMode attempts k true slot)
      s.1.1.1 tree s.1.2.2.1 r new)
    (grow : s.1.2.2.1 ≤ r.2) :
    SlotKeyInv attempts k D keys (Function.update parts slot new) (some slot)
      (((startLife D s.1.1.1 tree (ceremonyFuel circuits settings) r.1,
        startAux (worldMode attempts k true slot) r.1.2), (s.1.2.1, r.2, s.1.2.2.2)),
        startGhost attempts k D slot s.1.2.1 s.2) := by
  let life := startLife D s.1.1.1 tree (ceremonyFuel circuits settings) r.1
  have counts : ∀ other, LifetimeProof.runsAt life other = LifetimeProof.runsAt s.1.1.1 other +
      if tree = other then 1 else 0 := startLife_counts D _ _ _ _
  have countsLe : ∀ other, LifetimeProof.runsAt s.1.1.1 other ≤ LifetimeProof.runsAt life other := by
    intro other
    rw [counts]
    omega
  have started : Started slot life := by
    unfold Started
    rw [startSlot_tree attempts _ tree slot hs, counts, if_pos rfl,
      startSlot_attempt attempts _ tree slot hs]
    omega
  have agreement := parts_update_agree hs parts new
  have shared : ∀ x, (s.1.2.1 x).isSome → Hidden D x.1 ∧
      ∃ old, worldMode attempts k true old = .shared ∧ Started old life ∧
        r.2 (LifetimeIdealKeyLink.hiddenInput ((Function.update parts slot new) old) x.1) = some x.2.1 := by
    intro x hx
    obtain ⟨hh, old, hm, ho, hc⟩ := inv.tables.shared x hx
    exact ⟨hh, old, hm, ho.mono countsLe, by rw [agreement old ho]; exact grow hc⟩
  have selected : ∀ x, ((startGhost attempts k D slot s.1.2.1 s.2).selected x).isSome → Hidden D x.1 ∧
      Started (selectedSlot attempts k) life ∧
      r.2 (LifetimeIdealKeyLink.hiddenInput ((Function.update parts slot new) (selectedSlot attempts k)) x.1) = some x.2.1 := by
    intro x hx
    by_cases he : slot = selectedSlot attempts k
    · simp [startGhost, he] at hx
    · simp only [startGhost, he, decide_false, Bool.false_eq_true, ↓reduceIte] at hx
      obtain ⟨hh, ho, hc⟩ := inv.tables.selected x hx
      exact ⟨hh, ho.mono countsLe, by rw [agreement _ ho]; exact grow hc⟩
  refine ⟨tables_record inv.tables countsLe grow agreement shared selected (fun _ hn => hn), ?_, ?_, ?_⟩
  · refine ⟨started, rfl, ?_, ?_, ?_⟩
    · intro hm
      simp [hm, startAux]
    · intro hm
      have he := (own_iff_selected attempts k slot).1 hm
      have hk := (sampledStart_phase K circuits settings D keys h prims (by rw [hm]; decide) sampled).1
      simp [hk, startAux, startGhost, he, selected_mode]
    · intro hm
      rw [hm] at sampled
      obtain ⟨dealer, _, cont, _, data, _, hr, _⟩ := sampled
      rw [hr]
      exact ⟨∅, dealer.1.1, by simp [hm, startAux]⟩
  · change (s.2.started || decide (slot = selectedSlot attempts k)) = decide (Started _ life)
    rw [inv.started]
    unfold Started
    rw [counts]
    apply Bool.eq_iff_iff.mpr
    have hh := Bool.eq_iff_iff.mp (started_after attempts (selectedSlot attempts k) slot s.1.1.1 tree hs).symm
    simpa only [decide_eq_true_eq, Bool.or_eq_true] using hh
  · intro tree' fuel' steps' hr
    obtain ⟨ht, _, hsteps⟩ := startLife_running_source D s.1.1.1 tree _ r.1 tree' fuel' steps' hr
    refine ⟨slot, rfl, (startSlot_tree attempts _ tree slot hs).trans ht.symm, fun hm => ?_⟩
    rw [hsteps, Function.update_self]
    exact (sampledStart_phase K circuits settings D keys h prims hm sampled).2

end StartInvariant

theorem roundLife_running_source (D : C.Coalition) (kind : Option (Option TreeOutput))
    (st : LifetimeState C E) (tree : ThresholdLeanXmss.Tree) (fuel : ℕ)
    (steps : C.Party → Step C E RealSpec TreeOutput)
    (tree' : ThresholdLeanXmss.Tree) (fuel' : ℕ) (steps' : C.Party → Step C E RealSpec TreeOutput)
    (hr : (roundLife D kind st tree fuel steps).running = some (tree', fuel', steps')) :
    tree' = tree ∧ steps' = steps := by
  have he := settle_running_source D kind { st with running := some (tree, fuel - 1, steps) }
    tree' fuel' steps' hr
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  exact ⟨he.1.symm, he.2.2.symm⟩

section RoundInvariant
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (D : C.Coalition) (attempts : ℕ) (k : Fin (lifetimeRuns attempts))
variable (keys : C.Party → Keys C) (prims : Primitives)

theorem sharedRound_inv (s : Marked D E) (parts : PartsHistory C attempts) (slot : Slot attempts)
    (inv : SlotKeyInv attempts k D keys parts (some slot) s)
    (hm : worldMode attempts k true slot = .shared)
    (tree : ThresholdLeanXmss.Tree) (fuel : ℕ) (steps : C.Party → Step C E RealSpec TreeOutput)
    (running : s.1.1.1.running = some (tree, fuel, steps))
    (sent : C.Party → C.Party → Option (Msg E))
    (r : (Unit × (C.Party → Step C E RealSpec TreeOutput) ×
      (C.Party → C.Party → Option (Msg E))) × WorldState C)
    (hr : r ∈ support ((evalEmulation prims (stepRound (emulatedRoles D) D
      (roundAdversary (I := PEmpty) sent) noFunctionality () steps)).run s.1.2)) :
    SlotKeyInv attempts k D keys parts (some slot)
      (((roundLife D none s.1.1.1 tree fuel r.1.2.1, none), r.2), recordWorld D s.2 r.2) := by
  obtain ⟨old, hold, htree, phase⟩ := inv.phase tree fuel steps running
  have he : old = slot := (Option.some.inj hold).symm
  subst old
  have hp := phase (by rw [hm]; decide)
  obtain ⟨hw, hp'⟩ := round_phase prims D keys (parts slot) sent steps s.1.2 hp r hr
  let life := roundLife D none s.1.1.1 tree fuel r.1.2.1
  have counts := roundLife_counts D none s.1.1.1 tree fuel r.1.2.1
  have countsLe : ∀ other, LifetimeProof.runsAt s.1.1.1 other ≤ LifetimeProof.runsAt life other :=
    fun other => le_of_eq (counts other).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine tables_record inv.tables countsLe hw.1 (fun _ _ => rfl) ?_ ?_ (fun _ hn => hn)
    · intro x hx
      rcases hw.2 x hx with old | ⟨hidden, cached⟩
      · obtain ⟨hidden, old, mode, started, cached⟩ := inv.tables.shared x old
        exact ⟨hidden, old, mode, started.mono countsLe, hw.1 cached⟩
      · exact ⟨hidden, slot, hm, inv.mode.1.mono countsLe, cached⟩
    · intro x hx
      obtain ⟨hidden, started, cached⟩ := inv.tables.selected x hx
      exact ⟨hidden, started.mono countsLe, hw.1 cached⟩
  · refine ⟨inv.mode.1.mono countsLe, inv.mode.2.1, fun _ => rfl, ?_, ?_⟩
    · intro own
      rw [hm] at own
      cases own
    · intro ideal
      rw [hm] at ideal
      cases ideal
  · change s.2.started = decide (Started _ life)
    unfold Started
    rw [counts]
    exact inv.started
  · intro tree' fuel' steps' hrun
    obtain ⟨ht, hsteps⟩ := roundLife_running_source D none s.1.1.1 tree fuel r.1.2.1 tree' fuel' steps' hrun
    exact ⟨slot, rfl, htree.trans ht.symm, fun _ => hsteps ▸ hp'⟩

theorem selectedRound_inv (s : Marked D E) (parts : PartsHistory C attempts)
    (inv : SlotKeyInv attempts k D keys parts (some (selectedSlot attempts k)) s)
    (tree : ThresholdLeanXmss.Tree) (fuel : ℕ) (steps : C.Party → Step C E RealSpec TreeOutput)
    (running : s.1.1.1.running = some (tree, fuel, steps))
    (sent : C.Party → C.Party → Option (Msg E))
    (r : (Unit × (C.Party → Step C E RealSpec TreeOutput) ×
      (C.Party → C.Party → Option (Msg E))) × WorldState C)
    (hr : r ∈ support ((evalEmulation prims (stepRound (emulatedRoles D) D
      (roundAdversary (I := PEmpty) sent) noFunctionality () steps)).run (s.2.selected, s.1.2.2))) :
    SlotKeyInv attempts k D keys parts (some (selectedSlot attempts k))
      (((roundLife D none s.1.1.1 tree fuel r.1.2.1, some (r.2.1, none)), (s.1.2.1, r.2.2)),
        selectedGhost D s.2 s.1.2.1 r.2.1) := by
  obtain ⟨old, hold, htree, phase⟩ := inv.phase tree fuel steps running
  have he : old = selectedSlot attempts k := (Option.some.inj hold).symm
  subst old
  have hm := selected_mode attempts k
  have hp := phase (by rw [hm]; decide)
  obtain ⟨hw, hp'⟩ := round_phase prims D keys _ sent steps (s.2.selected, s.1.2.2) hp r hr
  let life := roundLife D none s.1.1.1 tree fuel r.1.2.1
  have counts := roundLife_counts D none s.1.1.1 tree fuel r.1.2.1
  have countsLe : ∀ other, LifetimeProof.runsAt s.1.1.1 other ≤ LifetimeProof.runsAt life other :=
    fun other => le_of_eq (counts other).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine tables_record inv.tables countsLe hw.1 (fun _ _ => rfl) ?_ ?_ (fun _ hn => hn)
    · intro x hx
      obtain ⟨hidden, old, mode, started, cached⟩ := inv.tables.shared x hx
      exact ⟨hidden, old, mode, started.mono countsLe, hw.1 cached⟩
    · intro x hx
      rcases hw.2 x hx with old | ⟨hidden, cached⟩
      · obtain ⟨hidden, started, cached⟩ := inv.tables.selected x old
        exact ⟨hidden, started.mono countsLe, hw.1 cached⟩
      · exact ⟨hidden, inv.mode.1.mono countsLe, cached⟩
  · refine ⟨inv.mode.1.mono countsLe, ?_, ?_, fun _ => rfl, ?_⟩
    · simp [selectedGhost]
    · intro shared
      rw [hm] at shared
      cases shared
    · intro ideal
      rw [hm] at ideal
      cases ideal
  · change true = decide (Started _ life)
    symm
    exact decide_eq_true (inv.mode.1.mono countsLe)
  · intro tree' fuel' steps' hrun
    obtain ⟨ht, hsteps⟩ := roundLife_running_source D none s.1.1.1 tree fuel r.1.2.1 tree' fuel' steps' hrun
    exact ⟨_, rfl, htree.trans ht.symm, fun _ => hsteps ▸ hp'⟩

theorem idealRound_inv (s : Marked D E) (parts : PartsHistory C attempts) (slot : Slot attempts)
    (inv : SlotKeyInv attempts k D keys parts (some slot) s)
    (hm : worldMode attempts k true slot = .ideal)
    (tree : ThresholdLeanXmss.Tree) (fuel : ℕ) (steps : C.Party → Step C E RealSpec TreeOutput)
    (running : s.1.1.1.running = some (tree, fuel, steps))
    (output : Option TreeOutput) (next : C.Party → Step C E RealSpec TreeOutput)
    (own : StreamCache C) (cache : HashCache C) (log : CallLog C)
    (grow : s.1.2.2.1 ≤ cache) :
    SlotKeyInv attempts k D keys parts (some slot)
      (((roundLife D (some output) s.1.1.1 tree fuel next, some (own, some output)),
        (s.1.2.1, cache, log)), recordWorld D s.2 (s.1.2.1, cache, log)) := by
  obtain ⟨old, hold, htree, _⟩ := inv.phase tree fuel steps running
  have he : old = slot := (Option.some.inj hold).symm
  subst old
  let life := roundLife D (some output) s.1.1.1 tree fuel next
  have counts := roundLife_counts D (some output) s.1.1.1 tree fuel next
  have countsLe : ∀ other, LifetimeProof.runsAt s.1.1.1 other ≤ LifetimeProof.runsAt life other :=
    fun other => le_of_eq (counts other).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine tables_record inv.tables countsLe grow (fun _ _ => rfl) ?_ ?_ (fun _ hn => hn)
    · intro x hx
      obtain ⟨hidden, old, mode, started, cached⟩ := inv.tables.shared x hx
      exact ⟨hidden, old, mode, started.mono countsLe, grow cached⟩
    · intro x hx
      obtain ⟨hidden, started, cached⟩ := inv.tables.selected x hx
      exact ⟨hidden, started.mono countsLe, grow cached⟩
  · refine ⟨inv.mode.1.mono countsLe, inv.mode.2.1, ?_, ?_, fun _ => ⟨own, output, rfl⟩⟩
    · intro shared
      rw [hm] at shared
      cases shared
    · intro own
      rw [hm] at own
      cases own
  · change s.2.started = decide (Started _ life)
    unfold Started
    rw [counts]
    exact inv.started
  · intro tree' fuel' steps' hrun
    obtain ⟨ht, _⟩ := roundLife_running_source D (some output) s.1.1.1 tree fuel next tree' fuel' steps' hrun
    exact ⟨slot, rfl, htree.trans ht.symm, fun hn => (hn hm).elim⟩

end RoundInvariant

section StepSource
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (k : Fin (lifetimeRuns attempts))
variable (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)

/-- A history update is the actual sampled start on this request's cache path.
Every request without an admitted start retains the complete history and last-slot marker. -/
def NewParts (q : (TailSpec C E).Domain) (s t : Marked D E)
    (parts parts' : PartsHistory C attempts) (last last' : Option (Slot attempts)) : Prop :=
  (∃ tree slot src new, q = .inl (.inr (.start tree)) ∧
    LifetimeProof.canStart attempts D s.1.1.1 tree ∧ startSlot attempts s.1.1.1 tree = some slot ∧
    src ∈ support ((simulateQ (worldAnswer prims)
      (startCore K circuits settings D keys h (worldMode attempts k true slot) s.1.1.1 tree)).run s.1.2.2.1) ∧
    SampledStart K circuits settings D keys h prims (worldMode attempts k true slot)
      s.1.1.1 tree s.1.2.2.1 src new ∧
    t.1 = ((startLife D s.1.1.1 tree (ceremonyFuel circuits settings) src.1,
      startAux (worldMode attempts k true slot) src.1.2), (s.1.2.1, src.2, s.1.2.2.2)) ∧
    parts' = Function.update parts slot new ∧ last' = some slot) ∨
  (NoStart attempts D q s.1.1.1 ∧ parts' = parts ∧ last' = last ∧
    ∀ tree, LifetimeProof.runsAt t.1.1.1 tree = LifetimeProof.runsAt s.1.1.1 tree)

theorem newParts_agree {q : (TailSpec C E).Domain} {s t : Marked D E}
    {parts parts' : PartsHistory C attempts} {last last' : Option (Slot attempts)}
    (new : NewParts K circuits settings attempts D k keys h prims q s t parts parts' last last') :
    ∀ slot, Started slot s.1.1.1 → parts' slot = parts slot := by
  rcases new with ⟨tree, slot, src, fresh, _, _, hs, _, _, _, rfl, _⟩ | ⟨_, rfl, _⟩
  · exact parts_update_agree hs parts fresh
  · exact fun _ _ => rfl

/-- The actual marked request preserves key provenance and records only its actual fresh parts. -/
theorem step_inv (q : (TailSpec C E).Domain) (s : Marked D E)
    (parts : PartsHistory C attempts) (last : Option (Slot attempts))
    (inv : SlotKeyInv attempts k D keys parts last s)
    (r : TailSpec C E q × Marked D E)
    (hr : r ∈ support ((markedKernel K circuits settings attempts k D keys h prims q).run s)) :
    ∃ parts' last', SlotKeyInv attempts k D keys parts' last' r.2 ∧
      NewParts K circuits settings attempts D k keys h prims q s r.2 parts parts' last last' := by
  have quiet : NoStart attempts D q s.1.1.1 →
      (∀ u ∈ support ((rawKernel K circuits settings attempts k D keys h prims true q).run s.1),
        QuietResult s.1 u.2) →
      ∃ parts' last', SlotKeyInv attempts k D keys parts' last' r.2 ∧
        NewParts K circuits settings attempts D k keys h prims q s r.2 parts parts' last last' := by
    intro hn hf
    have hc : ∀ tree, LifetimeProof.runsAt r.2.1.1.1 tree = LifetimeProof.runsAt s.1.1.1 tree := by
      simp only [markedKernel, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨u, hu, rfl⟩ := hr
      exact (hf u hu).2.1
    exact ⟨parts, last, quiet_marked K circuits settings attempts D k keys h prims q s parts last inv hn r hr hf,
      Or.inr ⟨hn, rfl, rfl, hc⟩⟩
  rcases q with (q | q) | forgery
  · apply quiet (by intro tree he; cases he)
    intro u hu
    rw [rawKernel_local K circuits settings attempts D k keys h prims true q s.1] at hu
    simp only [support_map, Set.mem_image] at hu
    obtain ⟨v, _, rfl⟩ := hu
    exact ⟨rfl, fun _ => rfl, rfl, fun _ hx => hx⟩
  · cases q with
    | publicKey =>
      apply quiet (by intro tree he; cases he)
      intro u hu
      have eq : u = (s.1.1.1.publicKey (keys h).parameter h, s.1) := by
        change u ∈ support ((evalSlot prims (pure (s.1.1.1.publicKey (keys h).parameter h))).run s.1) at hu
        simpa only [evalSlot_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] using hu
      rw [eq]
      exact ⟨rfl, fun _ => rfl, rfl, fun _ hx => hx⟩
    | sign query =>
      apply quiet (by intro tree he; cases he)
      intro u hu
      rw [rawKernel_sign K circuits settings attempts D k keys h prims true query s.1] at hu
      simp only [support_map, Set.mem_image] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      have frame := signing3_frame K circuits settings attempts D keys h query s.1.1.1 v.1
        (LifetimeSlotCoupling.localRun_support prims D _ s.1.2 v hv)
      have hw := localRun_within prims D _ _
        (signing3_quiet K circuits settings attempts D keys h query s.1.1.1) s.1.2 v hv
      exact ⟨rfl, frame.1, frame.2, fun x hx => (hw.2 x hx).resolve_right id⟩
    | start tree =>
      by_cases can : LifetimeProof.canStart attempts D s.1.1.1 tree
      · obtain ⟨slot, hs⟩ := startSlot_exists attempts D s.1.1.1 tree can
        simp only [markedKernel, StateT.run_mk, support_map, Set.mem_image] at hr
        obtain ⟨u, hu, rfl⟩ := hr
        rw [rawKernel_start_mode K circuits settings attempts D k keys h prims true tree s.1 can
          (worldMode attempts k true slot) (by rw [hs]; rfl)] at hu
        simp only [support_map, Set.mem_image] at hu
        obtain ⟨src, hsrc, rfl⟩ := hu
        obtain ⟨fresh, sampled⟩ := startCore_sampled K circuits settings D keys h prims _ _ _ _ src hsrc
        refine ⟨Function.update parts slot fresh, some slot, ?_, Or.inl ?_⟩
        · rw [advanceGhost_start attempts k D s tree slot can hs]
          exact start_inv K circuits settings attempts D k keys h prims s parts last inv tree slot hs src fresh
            sampled ((grows_worldAnswer prims).simulateQ _ _ _ hsrc)
        · exact ⟨tree, slot, src, fresh, rfl, can, hs, hsrc, sampled, rfl, rfl, rfl⟩
      · apply quiet (by intro tree' he; cases he; exact can)
        intro u hu
        rw [rawKernel_start_denied K circuits settings attempts D k keys h prims true tree s.1 can] at hu
        simp only [support_pure, Set.mem_singleton_iff] at hu
        rw [hu]
        exact ⟨rfl, fun _ => rfl, rfl, fun _ hx => hx⟩
    | round sent =>
      cases running : s.1.1.1.running with
      | none =>
        apply quiet (by intro tree he; cases he)
        intro u hu
        rw [rawKernel_round_idle K circuits settings attempts D k keys h prims true sent s.1 running] at hu
        simp only [support_pure, Set.mem_singleton_iff] at hu
        rw [hu]
        exact ⟨rfl, fun _ => rfl, rfl, fun _ hx => hx⟩
      | some run =>
        rcases run with ⟨tree, fuel, steps⟩
        obtain ⟨slot, rfl, htree, phase⟩ := inv.phase tree fuel steps running
        suffices result : SlotKeyInv attempts k D keys parts (some slot) r.2 ∧
            (∀ other, LifetimeProof.runsAt r.2.1.1.1 other = LifetimeProof.runsAt s.1.1.1 other) from
          ⟨parts, some slot, result.1, Or.inr ⟨(by intro tree he; cases he), rfl, rfl, result.2⟩⟩
        simp only [markedKernel, StateT.run_mk, support_map, Set.mem_image] at hr
        obtain ⟨u, hu, rfl⟩ := hr
        cases hm : worldMode attempts k true slot with
        | shared =>
          have aux := inv.mode.2.2.1 hm
          rw [rawKernel_round_shared K circuits settings attempts D k keys h prims true sent s.1 tree fuel steps running aux] at hu
          simp only [support_map, Set.mem_image] at hu
          obtain ⟨v, hv, rfl⟩ := hu
          have ghost := advanceGhost_keep inv (.inl (.inr (.round sent)))
            (by intro tree he; cases he) ((roundLife D none s.1.1.1 tree fuel v.1.2.1, none), v.2) aux.symm
          rw [ghost]
          exact ⟨sharedRound_inv D attempts k keys prims s parts slot inv hm tree fuel steps running sent v hv,
            roundLife_counts D none s.1.1.1 tree fuel v.1.2.1⟩
        | own =>
          have he := (own_iff_selected attempts k slot).1 hm
          subst slot
          have aux := inv.mode.2.2.2.1 hm
          rw [rawKernel_round_own K circuits settings attempts D k keys h prims true sent s.1 s.2.selected none tree fuel steps running aux] at hu
          simp only [support_map, Set.mem_image] at hu
          obtain ⟨v, hv, rfl⟩ := hu
          have active : s.2.active = true := by simpa using inv.mode.2.1
          rw [advanceGhost_round_selected attempts k D s active sent _ _ _]
          exact ⟨selectedRound_inv D attempts k keys prims s parts inv tree fuel steps running sent v hv,
            roundLife_counts D none s.1.1.1 tree fuel v.1.2.1⟩
        | ideal =>
          obtain ⟨own, output, aux⟩ := inv.mode.2.2.2.2 hm
          rw [rawKernel_round_own K circuits settings attempts D k keys h prims true sent s.1 own (some output) tree fuel steps running aux] at hu
          simp only [support_map, Set.mem_image] at hu
          obtain ⟨v, hv, rfl⟩ := hu
          have ne : slot ≠ selectedSlot attempts k := by
            intro he
            rw [he, selected_mode] at hm
            cases hm
          have inactive : s.2.active = false := by simpa [ne] using inv.mode.2.1
          have ghost : advanceGhost attempts k D (.inl (.inr (.round sent))) s.1
              ((roundLife D (some output) s.1.1.1 tree fuel v.1.2.1, some (v.2.1, some output)),
                (s.1.2.1, v.2.2)) s.2 = recordWorld D s.2 (s.1.2.1, v.2.2) := by
            simp [advanceGhost, inactive, recordWorld]
          rw [ghost]
          exact ⟨idealRound_inv D attempts k keys s parts slot inv hm tree fuel steps running output
            v.1.2.1 v.2.1 v.2.2.1 v.2.2.2 (evalEmulation_cache prims _ (own, s.1.2.2) v hv),
            roundLife_counts D (some output) s.1.1.1 tree fuel v.1.2.1⟩
  · apply quiet (by intro tree he; cases he)
    intro u hu
    rw [rawKernel_finish K circuits settings attempts D k keys h prims true forgery s.1,
      ← hom_finish3 D keys h forgery s.1.1.1, ← localRun_eq] at hu
    simp only [support_map, Set.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    have hw := localRun_within prims D _ _ (finish3_quiet D keys h forgery s.1.1.1) s.1.2 v hv
    exact ⟨rfl, fun _ => rfl, rfl, fun x hx => (hw.2 x hx).resolve_right id⟩

end StepSource

/-- Initial history values are never used until their corresponding slot has started. -/
def emptyParts (C : Committee) (attempts : ℕ) : PartsHistory C attempts :=
  fun _ _ => ⟨0, fun _ => 0, fun _ => 0⟩

theorem initial_not_started (attempts : ℕ) (D : C.Coalition) (slot : Slot attempts) :
    ¬ Started slot (initialSlot (E := E) D).1 := by
  unfold Started
  cases ht : slotTree slot <;> simp [LifetimeProof.runsAt, initialSlot]

theorem initial_inv (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (keys : C.Party → Keys C) (cache : HashCache C) :
    SlotKeyInv attempts k D keys (emptyParts C attempts) none
      ((initialSlot (E := E) D, (∅, cache, [])), Ghost.empty D) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
  · intro x hx
    simp at hx
  · intro x hx
    simp [Ghost.empty] at hx
  · intro name hn
    simp [Ghost.empty] at hn
  · change false = decide (Started _ (initialSlot (E := E) D).1)
    simp [initial_not_started]
  · intro tree fuel steps hr
    simp [initialSlot] at hr

section History
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (k : Fin (lifetimeRuns attempts))
variable (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives) (cache : HashCache C)

/-- A finite actual marked-kernel path with the sampled-history certificate of each request. -/
inductive History : PartsHistory C attempts → Option (Slot attempts) → Marked D E → Prop
  | initial : History (emptyParts C attempts) none ((initialSlot D, (∅, cache, [])), Ghost.empty D)
  | step {parts parts' : PartsHistory C attempts} {last last' : Option (Slot attempts)} {s : Marked D E}
      (before : History parts last s) (q : (TailSpec C E).Domain) (r : TailSpec C E q × Marked D E)
      (supported : r ∈ support ((markedKernel K circuits settings attempts k D keys h prims q).run s))
      (sampled : NewParts K circuits settings attempts D k keys h prims q s r.2 parts parts' last last') :
      History parts' last' r.2

/-- A started slot has a supported sampling on an actual prefix of the marked kernel path. -/
def SampledOccurrence (slot : Slot attempts) (parts : C.Party → Parts C) : Prop :=
  ∃ (beforeParts : PartsHistory C attempts) (beforeLast : Option (Slot attempts))
    (before : Marked D E) (tree : ThresholdLeanXmss.Tree)
    (answer : TailSpec C E (.inl (.inr (.start tree))) × Marked D E)
    (src : ((C.Party → Step C E RealSpec TreeOutput) × Option (Option TreeOutput)) × HashCache C),
    History K circuits settings attempts D k keys h prims cache beforeParts beforeLast before ∧
    answer ∈ support ((markedKernel K circuits settings attempts k D keys h prims
      (.inl (.inr (.start tree)))).run before) ∧
    LifetimeProof.canStart attempts D before.1.1.1 tree ∧
    startSlot attempts before.1.1.1 tree = some slot ∧
    src ∈ support ((simulateQ (worldAnswer prims)
      (startCore K circuits settings D keys h (worldMode attempts k true slot) before.1.1.1 tree)).run before.1.2.2.1) ∧
    SampledStart K circuits settings D keys h prims (worldMode attempts k true slot)
      before.1.1.1 tree before.1.2.2.1 src parts ∧
    answer.2.1 = ((startLife D before.1.1.1 tree (ceremonyFuel circuits settings) src.1,
      startAux (worldMode attempts k true slot) src.1.2), (before.1.2.1, src.2, before.1.2.2.2))

theorem history_started {parts : PartsHistory C attempts} {last : Option (Slot attempts)}
    {s : Marked D E} (hist : History K circuits settings attempts D k keys h prims cache parts last s)
    (slot : Slot attempts) (started : Started slot s.1.1.1) :
    SampledOccurrence K circuits settings attempts D k keys h prims cache slot (parts slot) := by
  induction hist with
  | initial => exact (initial_not_started attempts D slot started).elim
  | @step parts parts' last last' before hist q answer supported sampled ih =>
    rcases sampled with ⟨tree, current, src, fresh, heq, can, hs, hsrc, hsample, after, hp, hl⟩ |
      ⟨nostart, hp, hl, counts⟩
    · by_cases same : current = slot
      · subst current
        rw [hp, Function.update_self]
        subst q
        exact ⟨parts, last, before, tree, answer, src, hist, supported, can, hs, hsrc, hsample, after⟩
      · have old : Started slot before.1.1.1 := by
          rw [after] at started
          change slotAttempt slot < LifetimeProof.runsAt (startLife D before.1.1.1 tree _ src.1) (slotTree slot) at started
          rw [startLife_counts] at started
          have passed := Bool.eq_iff_iff.mp (started_after attempts slot current before.1.1.1 tree hs)
          simp only [decide_eq_true_eq, Bool.or_eq_true] at passed
          exact (passed.1 started).resolve_right same
        rw [hp, Function.update_of_ne (Ne.symm same)]
        exact ih old
    · rw [hp]
      apply ih
      unfold Started at started ⊢
      rwa [counts] at started

/-- The exact request induction composes through every adaptive program, preserving its source path. -/
theorem loop_inv {α : Type} (p : OracleComp (TailSpec C E) α)
    (s : Marked D E) (parts : PartsHistory C attempts) (last : Option (Slot attempts))
    (inv : SlotKeyInv attempts k D keys parts last s)
    (hist : History K circuits settings attempts D k keys h prims cache parts last s)
    (r : α × Marked D E)
    (hr : r ∈ support ((simulateQ (markedKernel K circuits settings attempts k D keys h prims) p).run s)) :
    ∃ parts' last', SlotKeyInv attempts k D keys parts' last' r.2 ∧
      History K circuits settings attempts D k keys h prims cache parts' last' r.2 := by
  induction p using OracleComp.inductionOn generalizing s parts last with
  | pure a =>
    have he : r = (a, s) := by simpa using hr
    subst r
    exact ⟨parts, last, inv, hist⟩
  | query_bind q f ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨u, hu, hr⟩ := hr
    obtain ⟨parts', last', inv', sampled⟩ := step_inv K circuits settings attempts D k keys h prims q s parts last inv u hu
    exact ih u.1 u.2 parts' last' inv' (History.step hist q u hu sampled) hr

variable (A : LifetimeAdversary C E)

/-- Every actual marked-game outcome retains its keygen prefix and sampled ceremony history. -/
theorem markedGame_keyLink (r : Bool × Marked D E)
    (hr : r ∈ support (markedGame K circuits settings attempts k D A prims)) :
    ∃ pre ∈ support (keygenPrefix D A prims), ∃ (h : C.Party) (parts : PartsHistory C attempts)
      (last : Option (Slot attempts)),
      SlotKeyInv attempts k D (fun i => (pre.1.2 i).getD default) parts last r.2 ∧
      History K circuits settings attempts D k (fun i => (pre.1.2 i).getD default) h prims pre.2 parts last r.2 := by
  unfold markedGame at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨pre, hpre, hr⟩ := hr
  refine ⟨pre, hpre, ?_⟩
  cases hh : C.parties.find? (· ∉ D.1) with
  | none =>
    simp only [hh, support_pure, Set.mem_singleton_iff] at hr
    subst r
    obtain ⟨h, _⟩ := exists_honest D
    exact ⟨h, emptyParts C attempts, none, initial_inv attempts k D _ pre.2, History.initial⟩
  | some h =>
    simp only [hh] at hr
    by_cases ready : ∀ i, i ∉ D.1 → (pre.1.2 i).isSome
    · rw [if_neg (not_not.mpr ready)] at hr
      obtain ⟨parts, last, inv, hist⟩ := loop_inv K circuits settings attempts D k
        (fun i => (pre.1.2 i).getD default) h prims pre.2 _ _ _ _
        (initial_inv attempts k D _ pre.2) History.initial r hr
      exact ⟨h, parts, last, inv, hist⟩
    · rw [if_pos ready] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst r
      exact ⟨h, emptyParts C attempts, none, initial_inv attempts k D _ pre.2, History.initial⟩

/-- An overlap has two distinct actually started slots, their sampled parts, and a common
cached derivation answer in the final actual marked-game cache. -/
theorem markedGame_overlap (r : Bool × Marked D E)
    (hr : r ∈ support (markedGame K circuits settings attempts k D A prims))
    (name : {name : KeyName C // Hidden D name}) (hn : name ∈ r.2.2.overlaps) :
    ∃ pre ∈ support (keygenPrefix D A prims), ∃ (h : C.Party) (shared : Slot attempts)
      (sharedParts selectedParts : C.Party → Parts C) (key : HashOutput),
      shared ≠ selectedSlot attempts k ∧ worldMode attempts k true shared = .shared ∧
      Started shared r.2.1.1.1 ∧ Started (selectedSlot attempts k) r.2.1.1.1 ∧
      SampledOccurrence K circuits settings attempts D k (fun i => (pre.1.2 i).getD default) h prims pre.2 shared sharedParts ∧
      SampledOccurrence K circuits settings attempts D k (fun i => (pre.1.2 i).getD default) h prims pre.2 (selectedSlot attempts k) selectedParts ∧
      r.2.1.2.2.1 (LifetimeIdealKeyLink.hiddenInput sharedParts name.1) = some key ∧
      r.2.1.2.2.1 (LifetimeIdealKeyLink.hiddenInput selectedParts name.1) = some key := by
  obtain ⟨pre, hpre, h, parts, last, inv, hist⟩ := markedGame_keyLink K circuits settings attempts D k prims A r hr
  obtain ⟨shared, key, mode, distinct, started, selected, sharedCache, selectedCache⟩ :=
    overlap_of_inv attempts k D _ parts last r.2 inv name hn
  exact ⟨pre, hpre, h, shared, parts shared, parts (selectedSlot attempts k), key, distinct, mode,
    started, selected, history_started K circuits settings attempts D k _ h prims pre.2 hist shared started,
    history_started K circuits settings attempts D k _ h prims pre.2 hist _ selected, sharedCache, selectedCache⟩

end History

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotKeyLink.step_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_inv

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotKeyLink.markedGame_keyLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms markedGame_keyLink

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotKeyLink.markedGame_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms markedGame_overlap

end ThresholdLeanXmssSecurity.LifetimeSlotKeyLink











