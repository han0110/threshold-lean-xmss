import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Phase
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutCheck.Budget
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutCheck.Tuples
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Records.Keys
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ledger.Parts
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Draws.OneKey
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Draws.Interval
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Draws.Fresh
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Schedule.Coupling
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Schedule.Joint
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Schedule.Rounds

/-!
# One ceremony with the record of a pass

`passCeremony` is the program of one ceremony with the record of a pass (`passRun` with
`plainShares`), and `passGhost` is its run on the ghost executor.

* `PassLaw` states that from a ready start there is a joint law of the cut at check `k` and of
  `passGhost` whose support has `CutLinkFree`, the link of `CutLink` with no premise on an honest output.
  `passLaw` proves it. The program of a pass is `recCeremonyAt` of the library at
  `early = true` (`ghostCeremonyAt_true`), so `PassLaw` is `couplingLawWith` at `early = true`.
  `passCoupling_of_law` gives from it the coupling of a bad check of the records to a bad check of
  the cut.
* `passFresh` proves `PassFresh`, the bound of one old key on `passGhost`. With the events
  `.opened` dropped by `filterOpened`, the program of a pass is `recCeremony` of the library
  (`passCeremony_records`). A map of the records commutes with the ghost executor
  (`executePhaseR_mapSteps`), and `UsesKey` reads only the starts, so `passFresh` is `freshOne` of
  the library.
* `passCeremonyBad` bounds a bad check of some batch or a reused key of `passGhost` from a ready
  start. Its premises are `PassLaw` and `PassFresh`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

section Ceremony

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## One ceremony with the record of a pass -/

/-- The program of operator `i` in one ceremony with the record of a pass, as `recCeremony`. -/
def passCeremony (i : C.Party) {σ : Type} (c : CeremonyStart C σ) : RecM C E CeremonyResult :=
  match c.keys i with
  | some keys => (passRun K circuits settings plainShares i keys c.jobs).run c.counters >>= fun p =>
      p.1.elim failure fun outputs => pure (outputs, p.2)
  | none => failure

/-- One ceremony with the record of a pass on the ghost executor, as `ghostCeremony`. -/
def passGhost (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) : StateT (StreamState C) ProbComp (net.State × CeremonySteps C E) :=
  simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality ([] : Record C E) rounds
    c.adversary fun i => (passCeremony K circuits settings i c).run.run)

/-- The joint law of the cut and of one ceremony with the record of a pass, as a statement. From a
ready start in a phase with the rounds of the ceremony, there is a law `J` of pairs whose first part
has the law of `ceremonyCheckAt k`, whose second part has the law of the ghost run with the record of
a pass, and whose support has `CutLinkFree`. It is `CouplingLaw` of the library for the record of a
pass, with no honest output in the link. The start is each ready start, so also the start of the
second ceremony of a bottom tree and the start of a retry. -/
def PassLaw : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    CheckTiming.ceremonyRounds circuits settings (gameParameter D c.keys) c.jobs ≤ rounds →
    ∀ k < (chunks settings.batchSize c.jobs).length,
    ∃ J : ProbComp ((Option (CheckStart C net.State) ×
        Option ((net.State × (C.Party → Option Unit)) × StreamState C)) ×
        ((net.State × CeremonySteps C E) × StreamState C)),
      (Prod.fst <$> J) =ᵈ ceremonyCheckAt prims K circuits settings D net rounds k c world ∧
      (Prod.snd <$> J) =ᵈ (passGhost prims K circuits settings D net rounds c).run world ∧
      ∀ x ∈ support J, CutLinkFree K D k x.1 x.2

omit [DecidableEq E] in
/-- The coupling of a record of a pass to its cut, with no premise on an honest output. From a ready
start, a bad check `k` in the records with no reused key and no global event at the end is at most
as likely as a bad check of `ceremonyCheckAt k`. -/
theorem passCoupling_of_law (law : PassLaw prims K circuits settings)
    (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C) (hready : CeremonyReady D ℓ c world)
    (hfuel : CheckTiming.ceremonyRounds circuits settings (gameParameter D c.keys) c.jobs ≤ rounds)
    (k : ℕ) (hk : k < (chunks settings.batchSize c.jobs).length) :
    (Pr{let ω ← (passGhost prims K circuits settings D net rounds c).run world}[
        BadCheckAt K D k ω.1.2 ∧ ¬ ReusedKey D world.2 ω.1.2 ∧ ¬ GlobalEvent ω.2]).toReal ≤
      (Pr{let r ← ceremonyCheckAt prims K circuits settings D net rounds k c world}[CheckBad D r]).toReal := by
  obtain ⟨J, hfst, hsnd, hlink⟩ := law D net rounds ℓ c world hready hfuel k hk
  rw [← hsnd.prEvent_eq, ← hfst.prEvent_eq, prEvent_map, prEvent_map]
  refine ENNReal.toReal_mono (prEvent_ne_top _) (prEvent_mono_of_support _ _ _ fun x hx hE => ?_)
  have hr : x.1 ∈ support (ceremonyCheckAt prims K circuits settings D net rounds k c world) := by
    rw [← support_eq_of_evalDistEq hfst, support_map]
    exact ⟨x, hx, rfl⟩
  exact checkBad_of_linkFree prims K circuits settings (ceremonyInterval prims K circuits settings) D net rounds ℓ
    c world hready k hk x.1 hr x.2 (hlink x hx) hE

/-- The fresh part for one old key, on the ghost run with the record of a pass. It is `FreshOne` of
the library. The starts of the two ghost runs are the same events, because the two recorded programs
differ only in the place of the record of an opening. -/
def PassFresh : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (name : KeyName C) (key : HashOutput),
    Hidden D name → (∃ kind parts, world.1 (.derive .prss kind parts) = some key) →
    Pr{let ω ← (passGhost prims K circuits settings D net rounds c).run world}[
        UsesKey D name key ω.1.2 ∧ ¬ GlobalEvent ω.2] ≤ ((2 : ℝ≥0∞) ^ 256)⁻¹

omit [Fintype E] [DecidableEq E] in
/-- The bound of a reused key on the ghost run with the record of a pass, as `reusedKey_le`. -/
theorem passReused_le (fresh : PassFresh prims K circuits settings)
    (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C) (hready : CeremonyReady D ℓ c world) :
    (Pr{let ω ← (passGhost prims K circuits settings D net rounds c).run world}[
        ReusedKey D world.2 ω.1.2 ∧ ¬ GlobalEvent ω.2]).toReal ≤ ceremonyFresh C ℓ.hiddenKeys := by
  obtain ⟨hidden, hcard, hmem⟩ := hiddenNames (C := C) D
  have hbound : HiddenKeyBound world.2 ℓ.hiddenKeys := hready.2.1.2.2.2
  have hprov : HiddenProvenance D world := hready.2.2
  choose keysOf hkeysCard hkeysMem using hbound
  let S : Finset (KeyName C × HashOutput) :=
    (hidden.biUnion fun name => (keysOf name).image fun key => (name, key)).filter fun p =>
      Hidden D p.1 ∧ ∃ ρ idx position, world.2 ((p.1, p.2), ρ, idx, position) ≠ none
  have hS : S.card ≤ prssKeyCount C * ℓ.hiddenKeys := by
    refine (Finset.card_filter_le _ _).trans (Finset.card_biUnion_le.trans ?_)
    refine (Finset.sum_le_card_nsmul _ _ ℓ.hiddenKeys fun name _ =>
      Finset.card_image_le.trans (hkeysCard name)).trans ?_
    rw [smul_eq_mul]
    exact Nat.mul_le_mul_right _ hcard
  have hone : ∀ p ∈ S, Pr{let ω ← (passGhost prims K circuits settings D net rounds c).run world}[
      UsesKey D p.1 p.2 ω.1.2 ∧ ¬ GlobalEvent ω.2] ≤ ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
    intro p hp
    obtain ⟨-, hhidden, ρ, idx, position, hcell⟩ := Finset.mem_filter.1 hp
    exact fresh D net rounds c world p.1 p.2 hhidden (hprov p.1 p.2 ρ idx position hhidden hcell)
  have hunion := prEvent_exists_finset_le_card_mul S
    ((passGhost prims K circuits settings D net rounds c).run world)
    (fun p ω => UsesKey D p.1 p.2 ω.1.2 ∧ ¬ GlobalEvent ω.2) hone
  have hcover : Pr{let ω ← (passGhost prims K circuits settings D net rounds c).run world}[
      ReusedKey D world.2 ω.1.2 ∧ ¬ GlobalEvent ω.2] ≤
      Pr{let ω ← (passGhost prims K circuits settings D net rounds c).run world}[
        ∃ p ∈ S, UsesKey D p.1 p.2 ω.1.2 ∧ ¬ GlobalEvent ω.2] := by
    refine prEvent_mono_of_support _ _ _ ?_
    rintro ω - ⟨⟨name, key, hhidden, huses, ρ, idx, position, hcell⟩, hglobal⟩
    refine ⟨(name, key), Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨name, hmem name hhidden,
      Finset.mem_image.2 ⟨key, hkeysMem name key ρ idx position hcell, rfl⟩⟩, hhidden, ρ, idx, position, hcell⟩,
      huses, hglobal⟩
  have htop : (S.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.2 (by positivity))
  have hreal := ENNReal.toReal_mono htop (hcover.trans hunion)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] at hreal
  refine hreal.trans ?_
  unfold ceremonyFresh
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hS) (by positivity)

omit [DecidableEq E] in
/-- The bound of one ceremony with the record of a pass. From a ready start with a ledger that has
room for this ceremony, in a phase with the rounds of the ceremony, a bad check of some batch or a
reused key, with no global event at the end, has probability at most the batches times
`checkErrorMax` plus the fresh part. No premise is on an output of an honest operator. The premises
are `PassLaw` and `PassFresh`, and each other fact is a theorem of the library. -/
theorem passCeremonyBad (law : PassLaw prims K circuits settings) (fresh : PassFresh prims K circuits settings)
    (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (q step rounds : ℕ)
    (hstep : ∀ st sent, IsQueryBoundP (net.round st sent) Counted step)
    (ℓ : StartBudget) (c : CeremonyStart C net.State) (world : StreamState C)
    (hjobs : AdmissibleJobs circuits settings c.jobs) (hready : CeremonyReady D ℓ c world)
    (hroom : LedgerRoom circuits settings runLimit C q step
      (ledgerStep circuits settings C step rounds (chunks settings.batchSize c.jobs).length ℓ))
    (hpad : (rounds + 2) * step ≤ q)
    (hfuel : CheckTiming.ceremonyRounds circuits settings (gameParameter D c.keys) c.jobs ≤ rounds) :
    (Pr{let ω ← (passGhost prims K circuits settings D net rounds c).run world}[
        ((∃ k ∈ Finset.range (chunks settings.batchSize c.jobs).length, BadCheckAt K D k ω.1.2) ∨
          ReusedKey D world.2 ω.1.2) ∧ ¬ GlobalEvent ω.2]).toReal ≤
      (chunks settings.batchSize c.jobs).length * checkErrorMax (E := E) circuits settings runLimit C q +
        ceremonyFresh C ℓ.hiddenKeys := by
  have hfresh := passReused_le prims K circuits settings fresh D net rounds ℓ c world hready
  obtain ⟨mx, hmx⟩ : ∃ mx, (passGhost prims K circuits settings D net rounds c).run world = mx := ⟨_, rfl⟩
  rw [hmx] at hfresh ⊢
  have hcover := prReal_mono mx
    (fun ω => ((∃ k ∈ Finset.range (chunks settings.batchSize c.jobs).length, BadCheckAt K D k ω.1.2) ∨
      ReusedKey D world.2 ω.1.2) ∧ ¬ GlobalEvent ω.2)
    (fun ω => (ReusedKey D world.2 ω.1.2 ∧ ¬ GlobalEvent ω.2) ∨
      ∃ k ∈ Finset.range (chunks settings.batchSize c.jobs).length, BadCheckAt K D k ω.1.2 ∧
        ¬ ReusedKey D world.2 ω.1.2 ∧ ¬ GlobalEvent ω.2) (by
    rintro ω - ⟨h, hglobal⟩
    by_cases hreused : ReusedKey D world.2 ω.1.2
    · exact Or.inl ⟨hreused, hglobal⟩
    · rcases h with ⟨k, hk, hbad⟩ | h
      · exact Or.inr ⟨k, hk, hbad, hreused, hglobal⟩
      · exact absurd h hreused)
  have hunion := prReal_or_le mx (fun ω => ReusedKey D world.2 ω.1.2 ∧ ¬ GlobalEvent ω.2)
    (fun ω => ∃ k ∈ Finset.range (chunks settings.batchSize c.jobs).length, BadCheckAt K D k ω.1.2 ∧
      ¬ ReusedKey D world.2 ω.1.2 ∧ ¬ GlobalEvent ω.2)
  have hsum := prReal_exists_finset_le mx (Finset.range (chunks settings.batchSize c.jobs).length) fun k ω =>
    BadCheckAt K D k ω.1.2 ∧ ¬ ReusedKey D world.2 ω.1.2 ∧ ¬ GlobalEvent ω.2
  have hcheck : ∑ k ∈ Finset.range (chunks settings.batchSize c.jobs).length,
      (Pr{let ω ← mx}[BadCheckAt K D k ω.1.2 ∧ ¬ ReusedKey D world.2 ω.1.2 ∧ ¬ GlobalEvent ω.2]).toReal ≤
      ∑ _k ∈ Finset.range (chunks settings.batchSize c.jobs).length,
        checkErrorMax (E := E) circuits settings runLimit C q :=
    Finset.sum_le_sum fun k hk => by
      rw [← hmx]
      exact (passCoupling_of_law prims K circuits settings law D net rounds ℓ c world hready hfuel k
          (Finset.mem_range.1 hk)).trans
        (ceremonyCheckBad_le prims K circuits settings runLimit
          (CutBudget.ceremonyBudget prims K circuits settings runLimit) (zeroCheck (C := C) (E := E))
          (EchoRound.ceremonyKeysAgree prims K circuits settings)
          (CutBudget.ceremonyTupleInputs prims K circuits settings) D net q step rounds hstep
          ℓ c world hjobs hready hroom hpad hfuel k (Finset.mem_range.1 hk))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hcheck
  exact hcover.trans (hunion.trans (by linarith))

end Ceremony

/-! ## A map of the record of a recorded program -/

section MapRec

variable {C : Committee} {E : Type} (f : Record C E → Record C E) (hnil : f [] = [])
  (happ : ∀ a b, f (a ++ b) = f a ++ f b)

/-- A recorded program with its record mapped by `f`. It is a monad map when `f` keeps `[]` and
`++`. -/
def mapRec : RecM C E →ᵐ RecM C E where
  toFun _ x := OptionT.mk (WriterT.mk (Prod.map id f <$> x.run.run))
  toFun_pure' a := OptionT.ext (by
    change Prod.map id f <$> (pure (some a, ∅) : OracleComp (PartySpec C E RealSpec) _) = pure (some a, ∅)
    simp [hnil])
  toFun_bind' x g := by
    apply OptionT.ext
    show WriterT.run (OptionT.run _) = WriterT.run (OptionT.run _)
    simp only [OptionT.run_mk, WriterT.run_mk, OptionT.run_bind, Option.elimM, WriterT.run_bind, map_bind,
      bind_map_left]
    refine bind_congr fun z => ?_
    rcases z with ⟨_ | a, w⟩
    · simp
    · simp [happ, Functor.map_map]

theorem mapRec_lift {α : Type} (p : PartyM C E RealSpec α) : mapRec f hnil happ (RecM.lift p) = RecM.lift p :=
  OptionT.ext (by
    change Prod.map id f <$> ((fun a => (a, ∅)) <$> p.run : OracleComp (PartySpec C E RealSpec) _) =
      (fun a => (a, ∅)) <$> p.run
    simp [Functor.map_map, hnil])

theorem mapRec_record (events : Record C E) :
    mapRec f hnil happ (RecM.record events) = RecM.record (f events) :=
  OptionT.ext (by
    change Prod.map id f <$> (RecM.record events).run.run = (RecM.record (f events)).run.run
    simp [RecM.record, OptionT.run_lift, WriterT.run_tell])

/-- A recorded program on a state with its record mapped by `f`. -/
def mapRecS {S : Type} : StateT S (RecM C E) →ᵐ StateT S (RecM C E) where
  toFun _ x := StateT.mk fun s => mapRec f hnil happ (x.run s)
  toFun_pure' a := StateT.ext fun s => by
    simp only [StateT.run_mk, StateT.run_pure, MonadHom.mmap_pure]
  toFun_bind' x g := StateT.ext fun s => by
    simp only [StateT.run_mk, StateT.run_bind, MonadHom.mmap_bind]

theorem mapRecS_liftS {S α : Type} (x : StateT S (PartyM C E RealSpec) α) :
    mapRecS f hnil happ (RecM.liftS x) = RecM.liftS x :=
  StateT.ext fun s => mapRec_lift f hnil happ (x.run s)

theorem mapRecS_record {S : Type} (events : Record C E) :
    mapRecS f hnil happ (StateT.lift (RecM.record events) : StateT S (RecM C E) PUnit) =
      StateT.lift (RecM.record (f events)) :=
  StateT.ext fun s => by
    change mapRec f hnil happ (RecM.record events >>= fun a => pure (a, s)) = RecM.record (f events) >>= _
    rw [MonadHom.mmap_bind, mapRec_record]
    simp only [MonadHom.mmap_pure]

theorem mapRecS_set {S : Type} (t : S) : mapRecS f hnil happ (set t : StateT S (RecM C E) PUnit) = set t :=
  StateT.ext fun _ => by
    change mapRec f hnil happ (pure (PUnit.unit, t)) = pure (PUnit.unit, t)
    exact MonadHom.mmap_pure _ _

end MapRec

/-! ## The record with no opening -/

section Opened

variable {C : Committee} {E : Type}

/-- The record with the events `.opened` dropped. -/
def filterOpened (record : Record C E) : Record C E :=
  record.filter fun e => match e with
    | .opened _ _ => false
    | _ => true

theorem filterOpened_append (a b : Record C E) : filterOpened (a ++ b) = filterOpened a ++ filterOpened b :=
  List.filter_append ..

theorem filterOpened_opened (v' : Shares C Bit) (inbox : Mail C E) :
    filterOpened [RecEvent.opened v' inbox] = [] := rfl

theorem startsOf_filterOpened (record : Record C E) : startsOf (filterOpened record) = startsOf record := by
  induction record with
  | nil => rfl
  | cons e record ih =>
    cases e <;> simp [filterOpened, startsOf] at ih ⊢ <;> exact ih

end Opened

/-! ## The program of a pass with no opening record -/

section Program

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits)
  (settings : Settings)

/-- A recorded program with the events `.opened` dropped from its record. -/
abbrev dropOpened : RecM C E →ᵐ RecM C E := mapRec filterOpened rfl filterOpened_append

/-- A recorded program on a state with the events `.opened` dropped from its record. -/
abbrev dropOpenedS {S : Type} : StateT S (RecM C E) →ᵐ StateT S (RecM C E) :=
  mapRecS filterOpened rfl filterOpened_append

omit [Field E] [Algebra Bit E] in
theorem dropOpenedS_liftS {S α : Type} (x : StateT S (PartyM C E RealSpec) α) :
    dropOpenedS (RecM.liftS x) = RecM.liftS x :=
  mapRecS_liftS _ _ _ x

omit [Field E] [Algebra Bit E] in
theorem dropOpenedS_record {S : Type} (events : Record C E) :
    dropOpenedS (StateT.lift (RecM.record events) : StateT S (RecM C E) PUnit) =
      StateT.lift (RecM.record (filterOpened events)) :=
  mapRecS_record _ _ _ events

omit [Field E] [Algebra Bit E] in
theorem dropOpenedS_set {S : Type} (t : S) : dropOpenedS (set t : StateT S (RecM C E) PUnit) = set t :=
  mapRecS_set _ _ _ t

omit [Field E] [Algebra Bit E] in
theorem liftS_lift_pure {S α : Type} (a : α) :
    RecM.liftS (StateT.lift (pure a : PartyM C E RealSpec α) : StateT S (PartyM C E RealSpec) α) = pure a :=
  StateT.ext fun s => by
    simp only [RecM.liftS, StateT.run_mk, StateT.run_lift, pure_bind, StateT.run_pure]
    rfl

omit [Field E] [Algebra Bit E] in
theorem lift_record_nil {S : Type} : (StateT.lift (RecM.record []) : StateT S (RecM C E) PUnit) = pure PUnit.unit :=
  StateT.ext fun s => OptionT.ext (by
    change (RecM.record ([] : Record C E) >>= fun a => pure (a, s)).run.run = (pure (PUnit.unit, s) : RecM C E _).run.run
    simp [RecM.record, OptionT.run_lift, WriterT.run_tell])

/-- With no opening record, the check of a pass is the check of the library. -/
theorem dropOpenedS_passCheckOpen (b : BatchStart C) (k : ℕ) :
    dropOpenedS (passCheckOpen K plainShares b k) = dropOpenedS (recCheckOpen K b k) := by
  unfold passCheckOpen recCheckOpen plainShares
  simp only [MonadHom.mmap_bind]
  refine bind_congr fun _ => bind_congr fun a => ?_
  simp only [dropOpenedS_liftS, dropOpenedS_record, dropOpenedS_set, MonadHom.mmap_pure, filterOpened_opened,
    lift_record_nil, liftS_lift_pure, pure_bind]

/-- A batch with the record of a pass is the head of the library and the check of a pass. -/
theorem passBatch_eq_head [Fintype E] [DecidableEq E] (ctx : Context C) (parameter : PublicParameter)
    (jobs : List Job) :
    passBatch K circuits settings plainShares ctx parameter jobs =
      recHead K circuits settings ctx parameter jobs >>= fun h => passCheckOpen K plainShares h.1 h.2 := by
  unfold passBatch recHead
  simp only [bind_assoc, pure_bind]

theorem dropOpenedS_passBatch [Fintype E] [DecidableEq E] (ctx : Context C) (parameter : PublicParameter)
    (jobs : List Job) :
    dropOpenedS (passBatch K circuits settings plainShares ctx parameter jobs) =
      dropOpenedS (recBatch K circuits settings ctx parameter jobs) := by
  rw [passBatch_eq_head, recBatch_eq_head, MonadHom.mmap_bind, MonadHom.mmap_bind]
  exact bind_congr fun h => dropOpenedS_passCheckOpen K h.1 h.2

theorem dropOpenedS_passRun [Fintype E] [DecidableEq E] (i : C.Party) (keys : Keys C) (jobs : List Job) :
    dropOpenedS (passRun K circuits settings plainShares i keys jobs) =
      dropOpenedS (recRun K circuits settings i keys jobs) := by
  unfold passRun recRun
  simp only [MonadHom.mmap_bind, dropOpenedS_liftS, monadHom_batched, dropOpenedS_passBatch]

/-- The check of a pass is `recCheckOpenWith` of the library at `early = true`. -/
theorem recCheckOpenWith_true (b : BatchStart C) (k : ℕ) :
    recCheckOpenWith K true b k = passCheckOpen K plainShares b k := by
  simp only [recCheckOpenWith, passCheckOpen, plainShares, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
    liftS_lift_pure, pure_bind]

theorem recBatchAt_true (ctx : Context C) (parameter : PublicParameter) :
    recBatchAt K circuits settings true ctx parameter = passBatch K circuits settings plainShares ctx parameter := by
  funext jobs
  unfold recBatchAt passBatch
  simp only [recCheckOpenWith_true]

theorem recRunAt_true (i : C.Party) (keys : Keys C) :
    recRunAt K circuits settings true i keys = passRun K circuits settings plainShares i keys := by
  funext jobs
  unfold recRunAt passRun
  simp only [recBatchAt_true]

end Program

/-! ## The fresh part by the erasure of the opening records -/

section Erasure

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- With no opening record, the program of a pass in one ceremony is `recCeremony`. -/
theorem passCeremony_records (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    Prod.map id filterOpened <$> (passCeremony K circuits settings i c).run.run =
      Prod.map id filterOpened <$> (recCeremony K circuits settings i c).run.run := by
  have h : dropOpened (passCeremony K circuits settings i c) = dropOpened (recCeremony K circuits settings i c) := by
    unfold passCeremony recCeremony
    rcases c.keys i with _ | keys
    · rfl
    · rw [MonadHom.mmap_bind, MonadHom.mmap_bind]
      have hrun := congrArg (fun x => StateT.run x c.counters)
        (dropOpenedS_passRun K circuits settings i keys c.jobs)
      exact congrArg (· >>= _) hrun
  exact congrArg (fun x => x.run.run) h

/-- The map of the last steps of a ghost run that drops the opening records of the honest
operators. -/
def eraseOpened (D : C.Coalition) {σ : Type} (ω : (σ × CeremonySteps C E) × StreamState C) :
    (σ × CeremonySteps C E) × StreamState C :=
  ((ω.1.1, mapSteps D (fun _ => filterOpened) ω.1.2), ω.2)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem usesKey_eraseOpened (D : C.Coalition) (name : KeyName C) (key : HashOutput) (steps : CeremonySteps C E) :
    UsesKey D name key (mapSteps D (fun _ => filterOpened) steps) ↔ UsesKey D name key steps := by
  have h : ∀ i, i ∉ D.1 →
      ceremonyRecord (mapSteps D (fun _ => filterOpened) steps) i = filterOpened (ceremonyRecord steps i) :=
    fun i hi => by
      unfold ceremonyRecord mapSteps
      rw [ite_eq_right hi]
      cases steps i <;> rfl
  unfold UsesKey
  refine exists_congr fun i => and_congr_right fun hi => ?_
  rw [h i hi, startsOf_filterOpened]

/-- With the opening records dropped, the ghost run with the record of a pass has the law of
`ghostCeremony`. -/
theorem passGhost_eraseOpened (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) :
    eraseOpened D <$> (passGhost prims K circuits settings D net rounds c).run world =
      eraseOpened D <$> (ghostCeremony prims K circuits settings D net rounds c).run world := by
  have hphase := fun (program : C.Party → OracleComp (PartySpec C E RealSpec) (Option CeremonyResult × Record C E)) =>
    executePhaseR_mapSteps D net noFunctionality ([] : Record C E) (fun _ => filterOpened) rounds c.adversary
      program (fun i => Prod.map id filterOpened <$> program i) fun _ _ => rfl
  have heq : (fun r => (r.1, mapSteps D (fun _ => filterOpened) r.2)) <$>
      executePhaseR worldRoles D net noFunctionality ([] : Record C E) rounds c.adversary
        (fun i => (passCeremony K circuits settings i c).run.run) =
      (fun r => (r.1, mapSteps D (fun _ => filterOpened) r.2)) <$>
      executePhaseR worldRoles D net noFunctionality ([] : Record C E) rounds c.adversary
        (fun i => (recCeremony K circuits settings i c).run.run) := by
    rw [← hphase, ← hphase]
    simp only [passCeremony_records]
  unfold passGhost ghostCeremony
  have e := congrArg (fun x => (simulateQ (streamWorld prims D) x).run world) heq
  simp only [simulateQ_map, StateT.run_map] at e
  exact e

/-- `PassFresh` holds. It is `freshOne` of the library by the erasure of the opening records. -/
theorem passFresh : PassFresh prims K circuits settings := by
  intro D net rounds c world name key hhidden hcell
  have hevent : ∀ ω : (net.State × CeremonySteps C E) × StreamState C,
      (UsesKey D name key (eraseOpened D ω).1.2 ∧ ¬ GlobalEvent (eraseOpened D ω).2) ↔
        (UsesKey D name key ω.1.2 ∧ ¬ GlobalEvent ω.2) := fun ω => by
    unfold eraseOpened
    rw [usesKey_eraseOpened]
  have hpass := prEvent_map ((passGhost prims K circuits settings D net rounds c).run world) (eraseOpened D)
    fun ω => UsesKey D name key ω.1.2 ∧ ¬ GlobalEvent ω.2
  have hrec := prEvent_map ((ghostCeremony prims K circuits settings D net rounds c).run world) (eraseOpened D)
    fun ω => UsesKey D name key ω.1.2 ∧ ¬ GlobalEvent ω.2
  simp only [hevent] at hpass hrec
  rw [← hpass, passGhost_eraseOpened, hrec]
  exact freshOne prims K circuits settings D net rounds c world name key hhidden hcell

end Erasure

/-! ## The joint law of a pass -/

section Law

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
theorem recCeremonyAt_true (i : C.Party) {σ : Type} (c : CeremonyStart C σ) :
    recCeremonyAt K circuits settings true i c = passCeremony K circuits settings i c := by
  unfold recCeremonyAt passCeremony
  cases c.keys i <;> simp only [recRunAt_true]

omit [Fintype E] [DecidableEq E] in
/-- The ghost run with the record of a pass is `ghostCeremonyAt` of the library at `early = true`. -/
theorem ghostCeremonyAt_true (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ)
    (c : CeremonyStart C net.State) :
    Joint.ghostCeremonyAt prims K circuits settings D net true rounds c =
      passGhost prims K circuits settings D net rounds c := by
  unfold Joint.ghostCeremonyAt passGhost
  simp only [recCeremonyAt_true]

/-- `PassLaw` holds. It is `couplingLawWith` of the library at `early = true`. -/
theorem passLaw : PassLaw prims K circuits settings := by
  intro D net rounds ℓ c world hready hfuel k hk
  obtain ⟨J, h1, h2, h3⟩ :=
    Joint.couplingLawWith prims K circuits settings true D net rounds ℓ c world hready hfuel k hk
  rw [ghostCeremonyAt_true] at h2
  exact ⟨J, h1, h2, h3⟩

end Law

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passFresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passFresh

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passLaw

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passCeremonyBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passCeremonyBad
