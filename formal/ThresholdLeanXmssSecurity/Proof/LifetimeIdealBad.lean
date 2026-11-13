import ThresholdLeanXmssSecurity.Proof.LifetimePrfTransportProof
import ThresholdLeanXmssSecurity.Proof.LifetimeLegacy

/-!
# The ideal lifetime stream tables

The free honest interface is used only by key generation and signing. Its
programs sample coins and query hashes; the PRSS streams of ceremonies use
their chronological run interfaces.

The pinned and current leanVM sources have no threshold network or lifetime
stream tables. The zero-query rules below reuse VCV's query-bound semantics.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeIdealBad

open LifetimePrfTransportProof
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- PRG queries on a local interface. -/
def PrgCall : (LocalSpec C).Domain → Prop
  | .inr (.inr _) => True
  | _ => False

def RoPrgCall : (RoSpec C).Domain → Prop
  | .inr _ => True
  | _ => False

/-- PRG queries in an honest party program. -/
def PartyPrgCall : (PartySpec C E RealSpec).Domain → Prop
  | .inl (.inl t) => PrgCall t
  | _ => False

/-- The free honest PRG copy in the four-copy lifetime program. -/
def FreePrgCall : (Spec4 C).Domain → Prop
  | .inl (.inr t) => PrgCall t
  | _ => False

section ZeroQueries

variable {ι α β : Type} {spec : OracleSpec ι} (P : ι → Prop)

theorem zero_bind {p : OracleComp spec α} {k : α → OracleComp spec β}
    (hp : IsQueryBoundP p P 0) (hk : ∀ a ∈ support p, IsQueryBoundP (k a) P 0) :
    IsQueryBoundP (p >>= k) P 0 := by
  simpa using isQueryBoundP_bind (m := 0) hp hk

theorem zero_sequenceFin {n : ℕ} (f : Fin n → OracleComp spec α)
    (hf : ∀ i, IsQueryBoundP (f i) P 0) :
    IsQueryBoundP (Concrete.sequenceFin f) P 0 := by
  induction n with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ n ih =>
    rw [Concrete.sequenceFin]
    exact zero_bind P (hf 0) fun _ _ => zero_bind P (ih _ fun i => hf i.succ)
      fun _ _ => isQueryBoundP_pure _ _ _

theorem zero_mapM (xs : List α) (f : α → OracleComp spec β)
    (hf : ∀ a, IsQueryBoundP (f a) P 0) : IsQueryBoundP (xs.mapM f) P 0 := by
  induction xs with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons a xs ih =>
    rw [List.mapM_cons]
    exact zero_bind P (hf a) fun _ _ => zero_bind P ih fun _ _ => isQueryBoundP_pure _ _ _

end ZeroQueries

theorem copy_quiet {α : Type} (p : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (advCopy4 p) FreePrgCall 0 ∧
    IsQueryBoundP (emulCopy4 p) FreePrgCall 0 ∧
    IsQueryBoundP (targetCopy4 p) FreePrgCall 0 := by
  constructor
  · apply LifetimeKeygenPrograms.qb0_simulateQ
    intro t
    exact (isQueryBoundP_query_iff _ _ _).2 (by simp [FreePrgCall])
  constructor <;> apply LifetimeKeygenPrograms.qb0_simulateQ <;> intro t <;>
    exact (isQueryBoundP_query_iff _ _ _).2 (by simp [FreePrgCall])

set_option backward.isDefEq.respectTransparency false in
theorem free_quiet {α : Type} (p : OracleComp (LocalSpec C) α)
    (hp : IsQueryBoundP p PrgCall 0) : IsQueryBoundP (freeCopy4 p) FreePrgCall 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have ht : ¬ PrgCall t := hp.1.resolve_right (by omega)
    rw [freeCopy4, simulateQ_bind, simulateQ_spec_query]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl ht, fun u => ?_⟩
    simpa only [freeCopy4, FreePrgCall, if_neg ht] using
      ih u (by simpa [ht] using hp.2 u)

theorem ro_local_quiet {α : Type} (p : OracleComp (RoSpec C) α)
    (hp : IsQueryBoundP p RoPrgCall 0) :
    IsQueryBoundP (liftComp p (LocalSpec C)) PrgCall 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have ht : ¬ RoPrgCall t := hp.1.resolve_right (by omega)
    rw [liftComp_bind]
    rcases t with t | t
    · change IsQueryBoundP ((OracleComp.lift (OracleSpec.query (Sum.inr (Sum.inl t))) :
        OracleComp (LocalSpec C) _) >>= _) PrgCall 0
      exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp [PrgCall]),
        fun u => by simpa only [PrgCall, if_false] using ih u (by simpa [ht] using hp.2 u)⟩
    · exact (ht trivial).elim

theorem sample_local_quiet {α : Type} (p : ProbComp α) :
    IsQueryBoundP (liftComp p (LocalSpec C)) PrgCall 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [liftComp_bind]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [PrgCall]), fun u => by simpa [PrgCall] using ih u⟩

theorem local_party_quiet {α : Type} (p : OracleComp (LocalSpec C) α)
    (hp : IsQueryBoundP p PrgCall 0) :
    IsQueryBoundP (liftComp p (PartySpec C E RealSpec)) PartyPrgCall 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    rw [liftComp_bind, liftComp_query]
    have he : ((OracleSpec.query t).cont <$> liftM (OracleSpec.query (OracleSpec.query t).input) :
        OracleComp (PartySpec C E RealSpec) _) =
        OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl t))) := by
      rw [← liftM_query_local]
      rfl
    rw [he]
    change IsQueryBoundP ((OracleComp.lift (OracleSpec.query (.inl (.inl t))) :
      OracleComp (PartySpec C E RealSpec) _) >>= _) PartyPrgCall 0
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨hp.1, fun u => by
      simpa only [Nat.zero_sub, ite_self] using ih u (by simpa only [Nat.zero_sub, ite_self] using hp.2 u)⟩

theorem party_bind {α β : Type} (p : PartyM C E RealSpec α) (k : α → PartyM C E RealSpec β)
    (hp : IsQueryBoundP p.run PartyPrgCall 0)
    (hk : ∀ a, IsQueryBoundP (k a).run PartyPrgCall 0) :
    IsQueryBoundP (p >>= k).run PartyPrgCall 0 := by
  rw [OptionT.run_bind]
  apply zero_bind PartyPrgCall hp
  rintro (_ | a) _
  · exact isQueryBoundP_pure _ _ _
  · exact hk a

theorem localStep_quiet {α : Type} (p : OracleComp (LocalSpec C) α)
    (hp : IsQueryBoundP p PrgCall 0) :
    IsQueryBoundP (localStep p : PartyM C E RealSpec α).run PartyPrgCall 0 := by
  change IsQueryBoundP (some <$> liftComp p (PartySpec C E RealSpec)) PartyPrgCall 0
  exact (isQueryBoundP_map_iff _ _ _).2 (local_party_quiet p hp)

theorem exchange_quiet (outbox : Mail C E) :
    IsQueryBoundP (exchange outbox : PartyM C E RealSpec _).run PartyPrgCall 0 := by
  simp only [exchange, OptionT.run_bind, OptionT.run_lift, Option.elimM, bind_assoc, pure_bind]
  apply zero_bind PartyPrgCall ((isQueryBoundP_query_iff _ _ _).2 (by simp [PartyPrgCall]))
  intro inbox _
  simp only [Option.elim]
  split <;> exact isQueryBoundP_pure _ _ _

theorem require_quiet (condition : Prop) :
    IsQueryBoundP (require condition : PartyM C E RealSpec Unit).run PartyPrgCall 0 := by
  unfold require
  split <;> exact isQueryBoundP_pure _ _ _

theorem hash_quiet (q : Query C) : IsQueryBoundP (hashQuery q) RoPrgCall 0 :=
  (isQueryBoundP_query_iff _ _ _).2 (by simp [RoPrgCall])

theorem oracleStep_quiet {α : Type} (p : OracleComp (RoSpec C) α)
    (hp : IsQueryBoundP p RoPrgCall 0) :
    IsQueryBoundP (oracleStep p : PartyM C E RealSpec α).run PartyPrgCall 0 :=
  localStep_quiet _ (ro_local_quiet p hp)

theorem deriveKeys_quiet (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    IsQueryBoundP (deriveKeys phase i view) RoPrgCall 0 := by
  unfold deriveKeys
  split <;> refine zero_bind RoPrgCall ?_ (fun _ _ => ?_)
  all_goals try first | exact hash_quiet _ | exact isQueryBoundP_pure _ _ _
  all_goals
    refine zero_bind RoPrgCall (zero_mapM _ _ _ fun T => ?_) (fun _ _ => ?_)
    · split
      · exact hash_quiet _
      · exact isQueryBoundP_pure _ _ _
    · refine zero_bind RoPrgCall (zero_mapM _ _ _ fun j => ?_) fun _ _ => isQueryBoundP_pure _ _ _
      split
      · exact isQueryBoundP_pure _ _ _
      · exact hash_quiet _

/-- The concrete setup uses private sampling, hashes and exchanges only. -/
theorem commitRevealEcho_quiet (phase : Phase) (i : C.Party) (own : Parts C) :
    IsQueryBoundP (commitRevealEcho phase i own : PartyM C E RealSpec _).run PartyPrgCall 0 := by
  rw [commitRevealEcho_eq]
  apply party_bind _ _ (oracleStep_quiet _ (zero_mapM _ _ _ fun _ => hash_quiet _))
  intro commitments
  apply party_bind _ _ (exchange_quiet _)
  intro committed
  apply party_bind _ _ (exchange_quiet _)
  intro revealed
  apply party_bind _ _ (oracleStep_quiet _ (zero_mapM _ _ _ fun _ => hash_quiet _))
  intro opens
  apply party_bind _ _ (require_quiet _)
  intro _
  apply party_bind _ _ (oracleStep_quiet _ (deriveKeys_quiet _ _ _))
  intro keys
  apply party_bind _ _ (oracleStep_quiet _ (zero_mapM _ _ _ fun _ => hash_quiet _))
  intro shared
  apply party_bind _ _ (exchange_quiet _)
  intro received
  apply party_bind _ _ (require_quiet _)
  intro _
  exact isQueryBoundP_pure _ _ _

theorem keygen_quiet (i : C.Party) :
    IsQueryBoundP (keygen i : PartyM C E RealSpec (Keys C)).run PartyPrgCall 0 := by
  unfold keygen keygenWith
  apply party_bind _ _ (localStep_quiet _ (sample_local_quiet _))
  intro own
  exact party_bind _ _ (commitRevealEcho_quiet _ _ _) fun _ => isQueryBoundP_pure _ _ _

/-- Suspended honest programs retain the absence of PRG calls. -/
def StepQuiet {α : Type} : Step C E RealSpec α → Prop
  | .done _ => True
  | .wait _ resume => ∀ inbox, IsQueryBoundP (resume inbox) PartyPrgCall 0
  | .call input _ => input.elim

theorem advance_quiet {α : Type} (p : OracleComp (PartySpec C E RealSpec) (Option α))
    (hp : IsQueryBoundP p PartyPrgCall 0) :
    IsQueryBoundP (advance p) PrgCall 0 ∧ ∀ s ∈ support (advance p), StepQuiet s := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    exact ⟨isQueryBoundP_pure _ _ _, fun s hs => by simpa [advance, StepQuiet] using hs ▸ True.intro⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have ht : ¬ PartyPrgCall t := hp.1.resolve_right (by omega)
    have hk : ∀ u, IsQueryBoundP (k u) PartyPrgCall 0 := fun u => by simpa [ht] using hp.2 u
    rcases t with (t | inbox) | input
    · change IsQueryBoundP ((OracleComp.lift (OracleSpec.query t) : OracleComp (LocalSpec C) _) >>=
        fun u => advance (k u)) PrgCall 0 ∧ _
      constructor
      · rw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl ht, fun u => by simpa [show ¬ PrgCall t from ht] using (ih u (hk u)).1⟩
      · intro s hs
        obtain ⟨u, _, hs⟩ := (mem_support_bind_iff _ _ _).mp hs
        exact (ih u (hk u)).2 s hs
    · exact ⟨isQueryBoundP_pure _ _ _, fun s hs => by
        change s ∈ support (pure (.wait inbox k) : OracleComp (LocalSpec C) _) at hs
        have he : s = .wait inbox k := by simpa using hs
        subst s
        exact hk⟩
    · exact input.elim

theorem free_support {α : Type} (p : OracleComp (LocalSpec C) α) :
    support (freeCopy4 p) ⊆ support p := by
  induction p using OracleComp.inductionOn with
  | pure a => exact Set.Subset.refl _
  | query_bind t k ih =>
    intro a ha
    change a ∈ support ((OracleComp.lift (OracleSpec.query (spec := Spec4 C) (.inl (.inr t))))
      >>= fun u => freeCopy4 (k u)) at ha
    obtain ⟨u, _, hu⟩ := (mem_support_bind_iff _ _ _).mp ha
    exact (mem_support_bind_iff _ _ _).mpr ⟨u, mem_support_query t u, ih u hu⟩

theorem start_base_quiet {α : Type} (D : C.Coalition) (program : C.Party → PartyM C E RealSpec α)
    (hp : ∀ i, IsQueryBoundP (program i).run PartyPrgCall 0) :
    IsQueryBoundP (startSteps base4 D program) FreePrgCall 0 ∧
      ∀ steps ∈ support (startSteps base4 D program), ∀ i, StepQuiet (steps i) := by
  constructor
  · apply zero_sequenceFin
    intro i
    by_cases hi : i ∈ D.1
    · simp only [hi, if_pos]; exact isQueryBoundP_pure _ _ _
    · simp only [hi]
      exact free_quiet _ (advance_quiet _ (hp i)).1
  · intro steps hs i
    have h := mem_support_sequenceFin_oc _ steps hs i
    by_cases hi : i ∈ D.1
    · simp only [hi, if_pos, mem_support_pure_iff] at h
      rw [h]
      trivial
    · simp only [hi] at h
      exact (advance_quiet _ (hp i)).2 _ (free_support _ h)

theorem round_base_quiet {α I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (hs : ∀ i, StepQuiet (steps i)) :
    IsQueryBoundP (stepRound base4 D A noFunctionality state steps) FreePrgCall 0 ∧
      ∀ r ∈ support (stepRound base4 D A noFunctionality state steps), ∀ i, StepQuiet (r.2.1 i) := by
  let local_ (sent : C.Party → C.Party → Option (Msg E)) (j : C.Party) :
      OracleComp (Spec4 C) (Step C E RealSpec α) :=
    match steps j with
    | .done out => pure (.done out)
    | .wait _ resume => if j ∈ D.1 then pure (.done none) else
        freeCopy4 (advance (resume (roundInbox D sent steps j)))
    | .call input _ => input.elim
  have hl (sent) (j) : IsQueryBoundP (local_ sent j) FreePrgCall 0 ∧
      ∀ s ∈ support (local_ sent j), StepQuiet s := by
    dsimp only [local_]
    cases hj : steps j with
    | done out =>
      simp only
      exact ⟨isQueryBoundP_pure _ _ _, fun s h => by
        have he : s = .done out := by simpa using h
        subst s
        trivial⟩
    | wait out resume =>
      simp only
      by_cases hc : j ∈ D.1
      · simp only [if_pos hc]
        exact ⟨isQueryBoundP_pure _ _ _, fun s h => by
          have he : s = .done none := by simpa using h
          subst s
          trivial⟩
      · simp only [if_neg hc]
        have hp : IsQueryBoundP (resume (roundInbox D sent steps j)) PartyPrgCall 0 := by
          have h := hs j
          rw [hj] at h
          exact h _
        exact ⟨free_quiet _ (advance_quiet _ hp).1,
          fun s h => (advance_quiet _ hp).2 s (free_support _ h)⟩
    | call input _ => exact input.elim
  have eqn : stepRound base4 D A noFunctionality state steps =
      (do
        let r ← advCopy4 (A.round state fun c i =>
          if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none)
        let next ← Concrete.sequenceFin (local_ r.2)
        pure (r.1, next, r.2)) := by
    unfold stepRound
    rw [if_neg (by simp [callInput_real])]
    apply bind_congr
    rintro ⟨state', sent⟩
    dsimp only
    congr 1
    congr 1
    funext j
    cases h : steps j with
    | done out => simp [local_, h]
    | wait out resume => simp only [local_, h, base4]; rfl
    | call input _ => exact input.elim
  rw [eqn]
  constructor
  · exact zero_bind FreePrgCall (copy_quiet _).1 fun r _ =>
      zero_bind FreePrgCall (zero_sequenceFin _ _ fun j => (hl r.2 j).1)
        fun _ _ => isQueryBoundP_pure _ _ _
  · intro r hr i
    simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨r', _, next, hn, rfl⟩ := hr
    exact (hl r'.2 i).2 _ (mem_support_sequenceFin_oc _ next hn i)

theorem rounds_base_quiet {α I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (hs : ∀ i, StepQuiet (steps i)) :
    IsQueryBoundP (executeRounds base4 D A noFunctionality fuel state steps) FreePrgCall 0 := by
  induction fuel generalizing state steps with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ fuel ih =>
    rw [executeRounds]
    split
    · exact isQueryBoundP_pure _ _ _
    · exact zero_bind FreePrgCall (round_base_quiet D A state steps hs).1 fun r hr =>
        ih r.1 r.2.1 ((round_base_quiet D A state steps hs).2 r hr)

/-- The full real keygen phase makes no free-copy PRG call, for every oracle answer. -/
theorem keygen_phase_quiet {I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (state : A.State) (fuel : ℕ) :
    IsQueryBoundP (executePhase base4 D A noFunctionality fuel state
      fun i => (keygen i : PartyM C E RealSpec (Keys C))) FreePrgCall 0 := by
  exact zero_bind FreePrgCall (start_base_quiet D _ keygen_quiet).1 fun steps hs =>
    rounds_base_quiet D A fuel state steps ((start_base_quiet D _ keygen_quiet).2 steps hs)

theorem tweakable_quiet {α : Type} (p : OracleComp HashSpec α) :
    IsQueryBoundP (tweakable (C := C) p) RoPrgCall 0 :=
  LifetimeKeygenPrograms.qb0_simulateQ _ (fun _ => hash_quiet _) p

theorem prfValue_quiet (seeds : C.Term → HashOutput) (x : Point) :
    IsQueryBoundP (prfValue seeds x) RoPrgCall 0 := by
  unfold prfValue
  apply zero_bind RoPrgCall (zero_mapM _ _ _ fun _ => ?_) fun _ _ => isQueryBoundP_pure _ _ _
  exact (isQueryBoundP_map_iff _ _ _).2 (hash_quiet _)

theorem eval_quiet (keys : Keys C) (i : C.Party) (J : C.Quorum) (x : Point) (message : Message) :
    IsQueryBoundP (eval keys i J x message) RoPrgCall 0 := by
  unfold eval
  refine zero_bind RoPrgCall (zero_mapM _ _ _ fun _ => ?_) fun _ _ => ?_
  · exact (isQueryBoundP_map_iff _ _ _).2 (hash_quiet _)
  exact zero_bind RoPrgCall (zero_mapM _ _ _ fun _ =>
    (isQueryBoundP_map_iff _ _ _).2 (hash_quiet _)) fun _ _ => isQueryBoundP_pure _ _ _

/-- From `SigningSelection.lean`, `SigningSelectionProof.run_liftM`. -/
theorem run_liftM {ι σ α : Type} {spec : OracleSpec ι} (p : OracleComp spec α) (st : σ) :
    (liftM p : StateT σ (OracleComp spec) α).run st = (fun a => (a, st)) <$> p := rfl

section Signing

variable {ι : Type} {spec : OracleSpec ι} (P : ι → Prop)
variable (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → OracleComp spec α)
variable (hlift : ∀ {α : Type} (p : OracleComp (RoSpec C) α),
  IsQueryBoundP p RoPrgCall 0 → IsQueryBoundP (lift p) P 0)

structure DealtQuiet (dealt : Dealt C (OracleComp spec)) : Prop where
  value : ∀ x, IsQueryBoundP (dealt.value x) P 0
  part : ∀ i J x message, IsQueryBoundP (dealt.part i J x message) P 0
  bottom : ∀ b, IsQueryBoundP (dealt.bottom b) P 0

include hlift

theorem signRound2With_quiet (part : Point → OracleComp spec Digest)
    (hp : ∀ x, IsQueryBoundP (part x) P 0) (parameter : PublicParameter) (J : C.Quorum)
    (commitment : Digest) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    IsQueryBoundP (signRound2With lift part parameter J commitment e message parts) P 0 := by
  unfold signRound2With
  apply zero_bind P (hlift _ (tweakable_quiet _))
  rintro (_ | ⟨randomness, encoding⟩) _
  · exact isQueryBoundP_pure _ _ _
  apply zero_bind P (zero_sequenceFin _ _ fun l => ?_) fun _ _ => isQueryBoundP_pure _ _ _
  split
  · exact (isQueryBoundP_map_iff _ _ _).2 (hp _)
  · exact isQueryBoundP_pure _ _ _

theorem referenceJob_quiet (value : Point → OracleComp spec Digest)
    (hv : ∀ x, IsQueryBoundP (value x) P 0) (parameter : PublicParameter) (job : Job) :
    IsQueryBoundP (referenceJob (fun p => lift (tweakable p)) value parameter job) P 0 := by
  unfold referenceJob
  apply zero_bind P (zero_mapM _ _ _ hv)
  intro values _
  cases job.kind with
  | chainEnd key l => exact (isQueryBoundP_map_iff _ _ _).2 (hlift _ (tweakable_quiet _))
  | chainRow key l =>
    exact zero_bind P (hlift _ (tweakable_quiet _)) fun _ _ =>
      zero_bind P (hlift _ (tweakable_quiet _)) fun _ _ =>
        zero_bind P (hlift _ (tweakable_quiet _)) fun _ _ => isQueryBoundP_pure _ _ _
  | chainValue key l p => exact (isQueryBoundP_map_iff _ _ _).2 (hlift _ (tweakable_quiet _))
  | commitment key => exact (isQueryBoundP_map_iff _ _ _).2 (hlift _ (tweakable_quiet _))
  | randomizer => exact isQueryBoundP_pure _ _ _

omit hlift in
/-- The tree assembler preserves any zero-query property of its two interfaces. -/
theorem ceremonyOutput_quiet
    (hashLift : ∀ {α : Type}, OracleComp HashSpec α → OracleComp spec α)
    (hhash : ∀ {α : Type} (p : OracleComp HashSpec α), IsQueryBoundP (hashLift p) P 0)
    (run : List Job → OracleComp spec (Option (List (List Bit))))
    (hrun : ∀ jobs, IsQueryBoundP (run jobs) P 0)
    (parameter : PublicParameter) (top : TopTree) (tree : Tree) :
    IsQueryBoundP (ceremonyOutput hashLift parameter run top tree) P 0 := by
  unfold ceremonyOutput
  cases tree with
  | top =>
    apply zero_bind P (hrun topJobs)
    rintro (_ | outputs) _
    · exact isQueryBoundP_pure _ _ _
    exact zero_bind P (hhash _) fun _ _ => isQueryBoundP_pure _ _ _
  | bottom b =>
    apply zero_bind P (hrun (bottomJobs b))
    rintro (_ | outputs) _
    · exact isQueryBoundP_pure _ _ _
    apply zero_bind P (hhash _)
    intro root _
    apply zero_bind P (hhash _)
    intro base _
    apply zero_bind P (hhash _)
    rintro (_ | ⟨randomness, encoding⟩) _
    · exact isQueryBoundP_pure _ _ _
    apply zero_bind P (hrun _)
    rintro (_ | values) _
    · exact isQueryBoundP_pure _ _ _
    apply zero_bind P (hhash _)
    intro path _
    apply zero_bind P (hhash _)
    intro topRoot _
    split <;> exact isQueryBoundP_pure _ _ _

theorem referenceTree_quiet (value : Point → OracleComp spec Digest)
    (hv : ∀ x, IsQueryBoundP (value x) P 0) (parameter : PublicParameter) (top : TopTree) (tree : Tree) :
    IsQueryBoundP (referenceTree (fun p => lift (tweakable p)) value parameter top tree) P 0 :=
  ceremonyOutput_quiet P _ (fun p => hlift _ (tweakable_quiet p)) _
    (fun _js => (isQueryBoundP_map_iff _ _ _).2
      (zero_mapM _ _ _ fun job => referenceJob_quiet P lift hlift value hv parameter job))
    parameter top tree

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
theorem dealtWith_quiet (parameter : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (value : Point → OracleComp spec Digest) (hv : ∀ x, IsQueryBoundP (value x) P 0) :
    DealtQuiet P (dealtWith lift parameter keys top value) := by
  refine ⟨hv, fun i J x message => hlift _ (eval_quiet _ _ _ _ _), fun b => ?_⟩
  change IsQueryBoundP (_ <$> referenceTree (fun p => lift (tweakable p)) value parameter top (.bottom b)) P 0
  with_reducible exact ((isQueryBoundP_map_iff _ _ _).2
    (referenceTree_quiet P lift hlift value hv parameter top (.bottom b)))

theorem honestSignature_quiet (dealt : Dealt C (OracleComp spec)) (hd : DealtQuiet P dealt)
    (e : KeyIndex) (message : Message) : IsQueryBoundP (honestSignature lift dealt e message) P 0 := by
  unfold honestSignature
  apply zero_bind P (hd.bottom _)
  rintro (_ | tree) _
  · exact isQueryBoundP_pure _ _ _
  apply zero_bind P (hd.value _)
  intro rho _
  apply zero_bind P (hlift _ (tweakable_quiet _))
  rintro (_ | ⟨randomness, encoding⟩) _
  · exact isQueryBoundP_pure _ _ _
  refine zero_bind P (zero_sequenceFin _ _ fun l => ?_) (fun values _ => ?_)
  · split
    · exact hd.value _
    · exact isQueryBoundP_pure _ _ _
    · exact zero_bind P (hd.value _) fun _ _ => isQueryBoundP_pure _ _ _
  · exact zero_bind P (hlift _ (tweakable_quiet _)) fun _ _ => isQueryBoundP_pure _ _ _

theorem forgeryWins_quiet (dealt : Dealt C (OracleComp spec)) (hd : DealtQuiet P dealt)
    (st : TsigState C) (forgery : Forgery) : IsQueryBoundP (forgeryWins lift dealt st forgery) P 0 := by
  unfold forgeryWins
  apply zero_bind P (hlift _ (tweakable_quiet _))
  intro verified _
  split
  · exact isQueryBoundP_pure _ _ _
  · exact zero_bind P (honestSignature_quiet P lift hlift dealt hd _ _) fun _ _ =>
      isQueryBoundP_pure _ _ _

omit hlift in
theorem bottomOnce_quiet (dealt : Dealt C (OracleComp spec)) (hd : DealtQuiet P dealt)
    (b : Fin (2 ^ layerHeight)) (st : TsigState C) :
    IsQueryBoundP ((bottomOnce dealt b).run st) P 0 := by
  simp only [bottomOnce, StateT.run_bind, StateT.run_get, pure_bind]
  cases ht : st.trees b with
  | some stored => exact isQueryBoundP_pure _ _ _
  | none =>
    simp only [StateT.run_bind, run_liftM, bind_map_left, StateT.run_modify,
      StateT.run_pure, pure_bind]
    exact zero_bind P (hd.bottom b) fun _ _ => isQueryBoundP_pure _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem tsig_quiet (dealt : Dealt C (OracleComp spec)) (hd : DealtQuiet P dealt)
    (q : (TsigSpec C).Domain) (st : TsigState C) :
    IsQueryBoundP ((tsigOracles lift dealt q).run st) P 0 := by
  cases q with
  | corrupt i =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact isQueryBoundP_pure _ _ _
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure]
      exact isQueryBoundP_pure _ _ _
  | tree b =>
    simp only [tsigOracles, StateT.run_bind]
    apply zero_bind P (bottomOnce_quiet P dealt hd _ st)
    rintro ⟨_ | tree, st'⟩ _
    · exact isQueryBoundP_pure _ _ _
    · simp only [StateT.run_bind, run_liftM, bind_map_left, StateT.run_pure]
      exact zero_bind P (hd.value _) fun _ _ => isQueryBoundP_pure _ _ _
  | round1 i J e message =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact isQueryBoundP_pure _ _ _
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_map, run_liftM, Functor.map_map]
      exact (isQueryBoundP_map_iff _ _ _).2 (hd.part _ _ _ _)
  | round2 i J e message parts =>
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · exact isQueryBoundP_pure _ _ _
    · apply zero_bind P (bottomOnce_quiet P dealt hd _ st)
      rintro ⟨_ | tree, st'⟩ _
      · exact isQueryBoundP_pure _ _ _
      · change IsQueryBoundP (StateT.run _ st') P 0
        simp only [StateT.run_bind, run_liftM, bind_map_left]
        apply zero_bind P (hd.part _ _ _ _)
        intro own _
        apply zero_bind P (signRound2With_quiet P lift hlift _ (hd.part i J · message) _ _ _ _ _ _)
        rintro (_ | values) _
        · exact isQueryBoundP_pure _ _ _
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact isQueryBoundP_pure _ _ _

end Signing

/-- Every ceremony interface avoids the free copy, including later real runs. -/
theorem roles4_quiet (n r : ℕ) {α : Type} (p : OracleComp (LocalSpec C) α) :
    IsQueryBoundP ((roles4 n r).adversary p) FreePrgCall 0 ∧
      IsQueryBoundP ((roles4 n r).honest p) FreePrgCall 0 := by
  unfold roles4
  split
  · exact ⟨(copy_quiet p).1, (copy_quiet p).2.1⟩
  · split
    · exact ⟨(copy_quiet p).1, (copy_quiet p).2.2⟩
    · exact ⟨(copy_quiet p).1, (copy_quiet p).1⟩

theorem start_roles_quiet {α : Type} (n r : ℕ) (D : C.Coalition)
    (program : C.Party → PartyM C E RealSpec α) :
    IsQueryBoundP (startSteps (roles4 n r) D program) FreePrgCall 0 := by
  apply zero_sequenceFin
  intro i
  split
  · exact isQueryBoundP_pure _ _ _
  · exact (roles4_quiet n r _).2

theorem round_roles_quiet {α I : Type} (n r : ℕ) (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    IsQueryBoundP (stepRound (roles4 n r) D A noFunctionality state steps) FreePrgCall 0 := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real])]
  apply zero_bind FreePrgCall (roles4_quiet n r _).1
  intro result _
  apply zero_bind FreePrgCall (zero_sequenceFin _ _ fun j => ?_)
    (fun _ _ => isQueryBoundP_pure _ _ _)
  cases steps j with
  | done out => exact isQueryBoundP_pure _ _ _
  | wait out resume =>
    simp only
    split
    · exact isQueryBoundP_pure _ _ _
    · exact (roles4_quiet n r _).2
  | call input _ => exact input.elim

/-- Pointwise zero bounds are preserved by stateful oracle simulation. -/
theorem simulate_run_quiet {ι κ α σ : Type} {spec : OracleSpec ι} {spec' : OracleSpec κ}
    (P : κ → Prop) (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (h : ∀ t st, IsQueryBoundP ((impl t).run st) P 0) (p : OracleComp spec α) (st : σ) :
    IsQueryBoundP ((simulateQ impl p).run st) P 0 := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact zero_bind P (h t st) fun r _ => ih r.1 r.2

def roFree {α : Type} (p : OracleComp (RoSpec C) α) : OracleComp (Spec4 C) α :=
  freeCopy4 (liftComp p _)

theorem roFree_quiet {α : Type} (p : OracleComp (RoSpec C) α)
    (hp : IsQueryBoundP p RoPrgCall 0) : IsQueryBoundP (roFree p) FreePrgCall 0 :=
  free_quiet _ (ro_local_quiet p hp)

theorem signerDealt_quiet (keys : C.Party → Keys C)
    (value : Point → OracleComp (Spec4 C) Digest)
    (hv : ∀ x, IsQueryBoundP (value x) FreePrgCall 0) (st : LifetimeState C E) (i : C.Party) :
    DealtQuiet FreePrgCall (ThresholdLeanXmss.signerDealt roFree keys value st i) :=
  ⟨hv, fun _ _ _ _ => roFree_quiet _ (eval_quiet _ _ _ _ _),
    fun _ => isQueryBoundP_pure _ _ _⟩

section Lifetime
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts n : ℕ)
variable (D : C.Coalition)

omit [Fintype E] [DecidableEq E] in
set_option maxRecDepth 2000 in
theorem lifetimeOracles_quiet (keys : C.Party → Keys C)
    (value : Point → OracleComp (Spec4 C) Digest)
    (hv : ∀ x, IsQueryBoundP (value x) FreePrgCall 0) (h : C.Party)
    (q : (LifetimeSpec C E).Domain) (st : LifetimeState C E) :
    IsQueryBoundP ((lifetimeOraclesWith K circuits settings attempts (roles4 n) base4 D
      keys value h q).run st) FreePrgCall 0 := by
  have sign (i : C.Party) (q : (TsigSpec C).Domain) (st : LifetimeState C E) :
      IsQueryBoundP ((tsigOracles roFree (ThresholdLeanXmss.signerDealt roFree keys value st i) q).run st.sign)
        FreePrgCall 0 :=
    tsig_quiet FreePrgCall roFree (fun p hp => roFree_quiet p hp) _
      (signerDealt_quiet keys value hv st i) q st.sign
  cases q with
  | sign q =>
    cases q with
    | corrupt i => exact isQueryBoundP_pure _ _ _
    | tree b =>
      change IsQueryBoundP ((_ >>= _) : OracleComp (Spec4 C) _) FreePrgCall 0
      exact zero_bind FreePrgCall (sign h (.tree b) st) fun _ _ => isQueryBoundP_pure _ _ _
    | round1 i J e message =>
      simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind]
      split
      · exact isQueryBoundP_pure _ _ _
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        exact zero_bind FreePrgCall (sign i (.round1 i J e message) _) fun _ _ =>
          isQueryBoundP_pure _ _ _
    | round2 i J e message parts =>
      simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind]
      split
      · exact isQueryBoundP_pure _ _ _
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        exact zero_bind FreePrgCall (sign i (.round2 i J e message parts) _) fun _ _ =>
          isQueryBoundP_pure _ _ _
  | publicKey => exact isQueryBoundP_pure _ _ _
  | start tree =>
    cases tree <;>
      simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind] <;>
      split
    · exact isQueryBoundP_pure _ _ _
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, StateT.run_set,
        StateT.run_pure, pure_bind]
      exact zero_bind FreePrgCall (start_roles_quiet n st.runCount D _) fun _ _ =>
        isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_pure _ _ _
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, StateT.run_set,
        StateT.run_pure, pure_bind]
      exact zero_bind FreePrgCall (start_roles_quiet n st.runCount D _) fun _ _ =>
        isQueryBoundP_pure _ _ _
  | round sent =>
    simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind]
    cases hr : st.running with
    | none => exact isQueryBoundP_pure _ _ _
    | some r =>
      rcases r with ⟨tree, fuel, steps⟩
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, StateT.run_set,
        StateT.run_pure, pure_bind]
      exact zero_bind FreePrgCall (round_roles_quiet n (st.runCount - 1) D (roundAdversary (I := PEmpty) sent) () steps)
        fun _ _ => isQueryBoundP_pure _ _ _

omit [Fintype E] [DecidableEq E] in
set_option maxRecDepth 3000 in
/-- The actual four-copy lifetime program never asks a free-copy PRG query,
for every sequence of oracle answers. -/
theorem program4_quiet (A : LifetimeAdversary C E) :
    IsQueryBoundP (program4 D K circuits settings attempts A n) FreePrgCall 0 := by
  unfold program4 lifetimeGameWith
  apply zero_bind FreePrgCall (copy_quiet _).1
  intro state _
  apply zero_bind FreePrgCall (keygen_phase_quiet D A.keygen state setupRounds)
  rintro ⟨state', outputs⟩ _
  cases hh : C.parties.find? (· ∉ D.1) with
  | none => exact isQueryBoundP_pure _ _ _
  | some h =>
    simp only
    split
    · exact isQueryBoundP_pure _ _ _
    · apply zero_bind FreePrgCall (simulate_run_quiet FreePrgCall _ (fun q st => ?_) _ _)
      · rintro ⟨forgery, st⟩ _
        split
        · exact isQueryBoundP_pure _ _ _
        · cases hp : st.publicKey ((outputs h).getD default).parameter h with
          | none => exact isQueryBoundP_pure _ _ _
          | some pk =>
            exact forgeryWins_quiet FreePrgCall roFree (fun p hp => roFree_quiet p hp) _
              (dealtWith_quiet FreePrgCall roFree (fun p hp => roFree_quiet p hp) _ _ _ _
                (fun x => roFree_quiet _ (prfValue_quiet _ x))) st.sign forgery
      · rcases q with t | q
        · simp only [QueryImpl.add_apply_inl]
          exact zero_bind FreePrgCall (copy_quiet _).1 fun _ _ => isQueryBoundP_pure _ _ _
        · exact lifetimeOracles_quiet K circuits settings attempts n D _ _
            (fun x => roFree_quiet _ (prfValue_quiet _ x)) h q st

end Lifetime

/-- The unflagged ideal world has entries only at hidden names. -/
def Clean (D : C.Coalition) (s : IdealState C) : Prop :=
  s.2.2.2 = false ∧ ∀ x, (s.2.1 x).isSome → Hidden D x.1.1

theorem clean_onCache (D : C.Coalition) {α : Type} (p : StateT (HashCache C) ProbComp α)
    (s : IdealState C) (hs : Clean D s) (r : α × IdealState C)
    (hr : r ∈ support ((onCache p).run s)) : Clean D r.2 := by
  simp only [onCache, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, _, rfl⟩ := hr
  exact hs

theorem clean_secondTable (D : C.Coalition) (x : Address C)
    (s : IdealState C) (hs : Clean D s) (r : Bit × IdealState C)
    (hr : r ∈ support ((secondTable x).run s)) : Clean D r.2 := by
  simp only [secondTable, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, _, rfl⟩ := hr
  exact hs

theorem clean_firstTable (D : C.Coalition) (x : Address C) (hx : Hidden D x.1.1)
    (s : IdealState C) (hs : Clean D s) (r : Bit × IdealState C)
    (hr : r ∈ support ((firstTable x).run s)) : Clean D r.2 := by
  simp only [firstTable, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  unfold tableDraw at hu
  cases hc : s.2.1 x with
  | some v =>
    simp only [hc, mem_support_pure_iff] at hu
    subst u
    exact hs
  | none =>
    simp only [hc, support_map, Set.mem_image] at hu
    obtain ⟨b, _, rfl⟩ := hu
    refine ⟨hs.1, fun y hy => ?_⟩
    by_cases he : y = x
    · simpa [he] using hx
    · exact hs.2 y (by simpa [QueryCache.cacheQuery_of_ne _ _ he] using hy)

/-- A query outside the free PRG interface preserves the unflagged hidden-table invariant. -/
theorem leftImpl_clean (prims : Primitives) (D : C.Coalition)
    (t : (Spec4 C).Domain) (ht : ¬ FreePrgCall t) (s : IdealState C) (hs : Clean D s)
    (r : Spec4 C t × IdealState C) (hr : r ∈ support ((leftImpl prims D t).run s)) :
    Clean D r.2 := by
  rcases t with (t | t) | t
  · rcases t with t | t
    · exact clean_onCache D _ s hs r hr
    · rcases t with t | (t | x)
      · exact clean_onCache D _ s hs r hr
      · exact clean_onCache D _ s hs r hr
      · change r ∈ support ((if Hidden D x.1 then firstTable (address x) else
          onCache (localAnswer prims (.inr (.inr x)))).run s) at hr
        split at hr
        · exact clean_firstTable D _ (by assumption) s hs r hr
        · exact clean_onCache D _ s hs r hr
  · rcases t with t | (t | x)
    · exact clean_onCache D _ s hs r hr
    · exact clean_onCache D _ s hs r hr
    · exact (ht trivial).elim
  · rcases t with t | (t | x)
    · exact clean_onCache D _ s hs r hr
    · exact clean_onCache D _ s hs r hr
    · change r ∈ support ((if Hidden D x.1 then secondTable (address x) else
        onCache (localAnswer prims (.inr (.inr x)))).run s) at hr
      split at hr
      · exact clean_secondTable D _ s hs r hr
      · exact clean_onCache D _ s hs r hr

theorem simulate_clean (prims : Primitives) (D : C.Coalition) {α : Type}
    (p : OracleComp (Spec4 C) α) (hp : IsQueryBoundP p FreePrgCall 0)
    (s : IdealState C) (hs : Clean D s) (r : α × IdealState C)
    (hr : r ∈ support ((simulateQ (leftImpl prims D) p).run s)) : Clean D r.2 := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure a =>
    have he : r = (a, s) := by simpa using hr
    rw [he]
    exact hs
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have ht : ¬ FreePrgCall t := hp.1.resolve_right (by omega)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨u, hu, hr⟩ := hr
    exact ih u.1 (by simpa [ht] using hp.2 u.1) u.2
      (leftImpl_clean prims D t ht s hs u hu) hr

/-- A hidden stream key occurs in both tables. The stream positions may differ. -/
def KeyOverlap (name : KeyName C) (s : IdealState C) : Prop :=
  ∃ key a b, (s.2.1 ((name, key), a)).isSome ∧ (s.2.2.1 ((name, key), b)).isSome

theorem idealBad_covered (D : C.Coalition) (s : IdealState C) (hs : Clean D s)
    (hb : IdealBad s) : ∃ name : {name : KeyName C // Hidden D name}, KeyOverlap name.1 s := by
  rcases hb with hb | ⟨x, hfirst, hsecond⟩
  · simp [hs.1] at hb
  · exact ⟨⟨x.1.1, hs.2 x hfirst⟩, x.1.2, x.2, x.2, hfirst, hsecond⟩

section Bound
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (prims : Primitives) (D : C.Coalition) (A : LifetimeAdversary C E)

omit [Fintype E] [DecidableEq E] in
/-- Every supported output of the actual left lifetime world has a false free-step flag. -/
theorem program4_clean (n : ℕ) (r : Bool × IdealState C)
    (hr : r ∈ support ((simulateQ (leftImpl prims D)
      (program4 D K circuits settings attempts A n)).run idealStart)) : Clean D r.2 :=
  simulate_clean prims D _ (program4_quiet K circuits settings attempts n D A) idealStart
    (by simp [Clean, idealStart]) r hr

omit [Fintype E] [DecidableEq E] in
theorem program4_flag_false (n : ℕ) (r : Bool × IdealState C)
    (hr : r ∈ support ((simulateQ (leftImpl prims D)
      (program4 D K circuits settings attempts A n)).run idealStart)) : r.2.2.2.2 = false :=
  (program4_clean K circuits settings attempts prims D A n r hr).1

omit [Fintype E] [DecidableEq E] in
/-- The free-step disjunct of the original bad event has probability zero. -/
theorem program4_flag_probability_zero (n : ℕ) :
    Pr[fun r => r.2.2.2.2 = true | (simulateQ (leftImpl prims D)
      (program4 D K circuits settings attempts A n)).run idealStart] = 0 := by
  apply probEvent_eq_zero_iff.2
  intro r hr
  simp [program4_flag_false K circuits settings attempts prims D A n r hr]

omit [Fintype E] [DecidableEq E] in
/-- The ideal bad event is covered by a finite union of actual hidden-key overlaps. -/
theorem idealBad_le_keyOverlap_sum (n : ℕ) :
    Pr[IdealBad ∘ Prod.snd | (simulateQ (leftImpl prims D)
      (program4 D K circuits settings attempts A n)).run idealStart] ≤
      ∑ name : {name : KeyName C // Hidden D name},
        Pr[KeyOverlap name.1 ∘ Prod.snd | (simulateQ (leftImpl prims D)
          (program4 D K circuits settings attempts A n)).run idealStart] := by
  let p := (simulateQ (leftImpl prims D)
    (program4 D K circuits settings attempts A n)).run idealStart
  have cover : Pr[IdealBad ∘ Prod.snd | p] ≤
      Pr[fun r => ∃ name : {name : KeyName C // Hidden D name}, KeyOverlap name.1 r.2 | p] :=
    probEvent_mono fun r hr hb => idealBad_covered D r.2
      (program4_clean K circuits settings attempts prims D A n r hr) hb
  refine cover.trans ?_
  simpa only [Finset.mem_univ, true_and, Function.comp_def] using
    probEvent_exists_finset_le_sum Finset.univ p
      (fun (name : {name : KeyName C // Hidden D name}) r => KeyOverlap name.1 r.2)

variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)

/-- The U4 estimate at one fixed hidden name in the actual left lifetime world.
The two tables retain their actual shared hash cache and adaptive execution.
The allowance counts input equality and output equality with earlier runs,
plus the original all-answer query budget. -/
def HiddenKeyOverlapBound (Q : ℕ) : Prop :=
  let F := ceremonyFuel (circuitsOf fun _ => 0) settings
  HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q →
  keySplit C (Q + lifetimeOverhead C attempts Q + (F + 2) * Q) < 2 →
  ∀ (n : Fin (lifetimeRuns attempts)) (values : MpcDomain → HashOutput)
      (name : {name : KeyName C // Hidden D name}),
    Pr[KeyOverlap name.1 ∘ Prod.snd | (simulateQ (leftImpl ⟨thOf values, aes⟩ D)
      (program4 D K (circuitsOf (thOf values)) settings attempts A n)).run idealStart] ≤
        ((2 * (lifetimeRuns attempts - 1) + Q : ℕ) : ℝ≥0∞) / 2 ^ 256

omit [Fintype E] [DecidableEq E] in
/-- Pointwise U4 estimates pay the original ideal share without a free-step error. -/
theorem idealBadBound_of_hiddenKeyOverlap (Q : ℕ)
    (bound : HiddenKeyOverlapBound K settings attempts D A aes circuitsOf Q) :
    IdealBadBound K settings attempts aes circuitsOf D A Q := by
  intro hQ hsplit n values
  have hattempts : 1 ≤ attempts := by
    have hn := n.isLt
    unfold lifetimeRuns at hn
    by_contra h
    have : attempts = 0 := by omega
    simp [this] at hn
  let count := 2 * (lifetimeRuns attempts - 1) + Q
  have hs := idealBad_le_keyOverlap_sum K (circuitsOf (thOf values)) settings attempts
    ⟨thOf values, aes⟩ D A n
  have hpoint := bound hQ hsplit n values
  have hsum :
      (∑ name : {name : KeyName C // Hidden D name},
        Pr[KeyOverlap name.1 ∘ Prod.snd | (simulateQ (leftImpl ⟨thOf values, aes⟩ D)
          (program4 D K (circuitsOf (thOf values)) settings attempts A n)).run idealStart]) ≤
      (prssKeyCount C : ℝ≥0∞) * (count : ℝ≥0∞) / 2 ^ 256 := by
    calc _ ≤ ∑ _name : {name : KeyName C // Hidden D name}, (count : ℝ≥0∞) / 2 ^ 256 :=
        Finset.sum_le_sum fun name _ => hpoint name
      _ = (Fintype.card {name : KeyName C // Hidden D name} : ℝ≥0∞) * count / 2 ^ 256 := by
        simp [nsmul_eq_mul, mul_div_assoc]
      _ ≤ _ := by
        gcongr
        exact_mod_cast aimed_hidden_card D
  have harith := (designCounts_le (C := C) attempts Q
    (ceremonyFuel (circuitsOf fun _ => 0) settings) _ hsplit hattempts).2
  have hcount : prssKeyCount C * count ≤ idealShare C attempts Q := by
    dsimp [count]
    nlinarith [harith]
  have htotal :
      Pr[IdealBad ∘ Prod.snd | (simulateQ (leftImpl ⟨thOf values, aes⟩ D)
        (program4 D K (circuitsOf (thOf values)) settings attempts A n)).run idealStart] ≤
      (idealShare C attempts Q : ℝ≥0∞) / 2 ^ 256 := by
    refine (hs.trans hsum).trans ?_
    apply ENNReal.div_le_div_right
    exact_mod_cast hcount
  have hreal := ENNReal.toReal_mono (by finiteness) htotal
  simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] using hreal

end Bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealBad.program4_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms program4_quiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealBad.program4_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms program4_clean

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealBad.program4_flag_probability_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms program4_flag_probability_zero

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealBad.idealBad_le_keyOverlap_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealBad_le_keyOverlap_sum

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealBad.idealBadBound_of_hiddenKeyOverlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealBadBound_of_hiddenKeyOverlap

end ThresholdLeanXmssSecurity.LifetimeIdealBad
