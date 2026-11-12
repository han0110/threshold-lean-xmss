import ThresholdLeanXmssSecurity.Proof.LifetimeRunBoundary

/-!
# No free stream-key hash in the four-copy lifetime program

Only the answer of a PRG query hashes a `.streamKey` input. The honest programs of keygen and
signing hash other inputs only. So the free copy of `program4` never asks a `.streamKey` hash.

The lemmas follow the walk of `LifetimeIdealBad.program4_quiet`, with the predicate `FreeStreamKey`
in place of `FreePrgCall`.

* `LocalKey`, `RoKey` and `PartyKey` are the stream-key hashes on the local, the random-oracle and
  the party interfaces.
* `keygen_phase_keyQuiet` states that the keygen phase on `base4` asks no free stream-key hash.
* `tsig_keyQuiet` states the same for one signing oracle step.
* `freeStreamKeyQuiet` is `LifetimeRunBoundary.FreeStreamKeyQuiet`.
* `reductionGame_bad` is the cover of `LifetimeRunBoundary.reductionGame_bad` with no premise.

The pinned and current leanVM sources have no threshold network or lifetime stream tables.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace ThresholdLeanXmssSecurity.LifetimeStreamKeyQuiet

open LifetimePrfTransportProof LifetimeIdealBad LifetimeRunBoundary

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- A stream-key hash on a local interface. -/
def LocalKey (t : (LocalSpec C).Domain) : Prop := FreeStreamKey (.inl (.inr t))

/-- A stream-key hash on a random-oracle interface. -/
def RoKey (t : (RoSpec C).Domain) : Prop := LocalKey (.inr t)

/-- A stream-key hash in an honest party program. -/
def PartyKey : (PartySpec C E RealSpec).Domain → Prop
  | .inl (.inl t) => LocalKey t
  | _ => False

section Local

set_option backward.isDefEq.respectTransparency false in
theorem free_keyQuiet {α : Type} (p : OracleComp (LocalSpec C) α)
    (hp : IsQueryBoundP p LocalKey 0) : IsQueryBoundP (freeCopy4 p) FreeStreamKey 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have ht : ¬ LocalKey t := hp.1.resolve_right (by omega)
    rw [freeCopy4, simulateQ_bind, simulateQ_spec_query]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl ht, fun u => ?_⟩
    have h := ih u (by simpa [ht] using hp.2 u)
    have ht' : ¬ FreeStreamKey (C := C) (.inl (.inr t)) := ht
    simpa only [freeCopy4, if_neg ht'] using h

theorem ro_local_keyQuiet {α : Type} (p : OracleComp (RoSpec C) α)
    (hp : IsQueryBoundP p RoKey 0) :
    IsQueryBoundP (liftComp p (LocalSpec C)) LocalKey 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have ht : ¬ RoKey t := hp.1.resolve_right (by omega)
    have ht' : ¬ LocalKey (.inr t) := ht
    rw [liftComp_bind]
    change IsQueryBoundP ((OracleComp.lift (OracleSpec.query (Sum.inr t)) :
      OracleComp (LocalSpec C) _) >>= _) LocalKey 0
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl ht',
      fun u => by simpa only [ht', if_false] using ih u (by simpa [ht] using hp.2 u)⟩

theorem sample_local_keyQuiet {α : Type} (p : ProbComp α) :
    IsQueryBoundP (liftComp p (LocalSpec C)) LocalKey 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [liftComp_bind]
    erw [isQueryBoundP_query_bind_iff]
    have ht : ¬ LocalKey (C := C) (.inl t) := fun h => h
    exact ⟨Or.inl ht, fun u => by simpa [ht] using ih u⟩

theorem local_party_keyQuiet {α : Type} (p : OracleComp (LocalSpec C) α)
    (hp : IsQueryBoundP p LocalKey 0) :
    IsQueryBoundP (liftComp p (PartySpec C E RealSpec)) PartyKey 0 := by
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
      OracleComp (PartySpec C E RealSpec) _) >>= _) PartyKey 0
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨hp.1, fun u => by
      simpa only [Nat.zero_sub, ite_self] using ih u (by simpa only [Nat.zero_sub, ite_self] using hp.2 u)⟩

theorem party_bind_key {α β : Type} (p : PartyM C E RealSpec α) (k : α → PartyM C E RealSpec β)
    (hp : IsQueryBoundP p.run PartyKey 0)
    (hk : ∀ a, IsQueryBoundP (k a).run PartyKey 0) :
    IsQueryBoundP (p >>= k).run PartyKey 0 := by
  rw [OptionT.run_bind]
  apply zero_bind PartyKey hp
  rintro (_ | a) _
  · exact isQueryBoundP_pure _ _ _
  · exact hk a

theorem localStep_keyQuiet {α : Type} (p : OracleComp (LocalSpec C) α)
    (hp : IsQueryBoundP p LocalKey 0) :
    IsQueryBoundP (localStep p : PartyM C E RealSpec α).run PartyKey 0 := by
  change IsQueryBoundP (some <$> liftComp p (PartySpec C E RealSpec)) PartyKey 0
  exact (isQueryBoundP_map_iff _ _ _).2 (local_party_keyQuiet p hp)

theorem exchange_keyQuiet (outbox : Mail C E) :
    IsQueryBoundP (exchange outbox : PartyM C E RealSpec _).run PartyKey 0 := by
  simp only [exchange, OptionT.run_bind, OptionT.run_lift, Option.elimM, bind_assoc, pure_bind]
  apply zero_bind PartyKey ((isQueryBoundP_query_iff _ _ _).2 (by simp [PartyKey]))
  intro inbox _
  simp only [Option.elim]
  split <;> exact isQueryBoundP_pure _ _ _

theorem require_keyQuiet (condition : Prop) :
    IsQueryBoundP (require condition : PartyM C E RealSpec Unit).run PartyKey 0 := by
  unfold require
  split <;> exact isQueryBoundP_pure _ _ _

theorem hash_keyQuiet (q : Query C) (hq : ¬ RoKey (.inl q)) : IsQueryBoundP (hashQuery q) RoKey 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h hq

theorem oracleStep_keyQuiet {α : Type} (p : OracleComp (RoSpec C) α)
    (hp : IsQueryBoundP p RoKey 0) :
    IsQueryBoundP (oracleStep p : PartyM C E RealSpec α).run PartyKey 0 :=
  localStep_keyQuiet _ (ro_local_keyQuiet p hp)

end Local

section Keygen

theorem deriveKeys_keyQuiet (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    IsQueryBoundP (deriveKeys phase i view) RoKey 0 := by
  unfold deriveKeys
  split <;> refine zero_bind RoKey ?_ (fun _ _ => ?_)
  all_goals try first | exact hash_keyQuiet _ id | exact isQueryBoundP_pure _ _ _
  all_goals
    refine zero_bind RoKey (zero_mapM _ _ _ fun T => ?_) (fun _ _ => ?_)
    · split
      · exact hash_keyQuiet _ id
      · exact isQueryBoundP_pure _ _ _
    · refine zero_bind RoKey (zero_mapM _ _ _ fun j => ?_) fun _ _ => isQueryBoundP_pure _ _ _
      split
      · exact isQueryBoundP_pure _ _ _
      · exact hash_keyQuiet _ id

theorem commitRevealEcho_keyQuiet (phase : Phase) (i : C.Party) (own : Parts C) :
    IsQueryBoundP (commitRevealEcho phase i own : PartyM C E RealSpec _).run PartyKey 0 := by
  rw [commitRevealEcho_eq]
  apply party_bind_key _ _ (oracleStep_keyQuiet _ (zero_mapM _ _ _ fun _ => hash_keyQuiet _ id))
  intro commitments
  apply party_bind_key _ _ (exchange_keyQuiet _)
  intro committed
  apply party_bind_key _ _ (exchange_keyQuiet _)
  intro revealed
  apply party_bind_key _ _ (oracleStep_keyQuiet _ (zero_mapM _ _ _ fun _ => hash_keyQuiet _ id))
  intro opens
  apply party_bind_key _ _ (require_keyQuiet _)
  intro _
  apply party_bind_key _ _ (oracleStep_keyQuiet _ (deriveKeys_keyQuiet _ _ _))
  intro keys
  apply party_bind_key _ _ (oracleStep_keyQuiet _ (zero_mapM _ _ _ fun _ => hash_keyQuiet _ id))
  intro shared
  apply party_bind_key _ _ (exchange_keyQuiet _)
  intro received
  apply party_bind_key _ _ (require_keyQuiet _)
  intro _
  exact isQueryBoundP_pure _ _ _

theorem keygen_keyQuiet (i : C.Party) :
    IsQueryBoundP (keygen i : PartyM C E RealSpec (Keys C)).run PartyKey 0 := by
  unfold keygen keygenWith
  apply party_bind_key _ _ (localStep_keyQuiet _ (sample_local_keyQuiet _))
  intro own
  exact party_bind_key _ _ (commitRevealEcho_keyQuiet _ _ _) fun _ => isQueryBoundP_pure _ _ _

/-- A suspended honest program that asks no stream-key hash. -/
def StepKeyQuiet {α : Type} : Step C E RealSpec α → Prop
  | .done _ => True
  | .wait _ resume => ∀ inbox, IsQueryBoundP (resume inbox) PartyKey 0
  | .call input _ => input.elim

theorem advance_keyQuiet {α : Type} (p : OracleComp (PartySpec C E RealSpec) (Option α))
    (hp : IsQueryBoundP p PartyKey 0) :
    IsQueryBoundP (advance p) LocalKey 0 ∧ ∀ s ∈ support (advance p), StepKeyQuiet s := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    exact ⟨isQueryBoundP_pure _ _ _, fun s hs => by simpa [advance, StepKeyQuiet] using hs ▸ True.intro⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hp
    have ht : ¬ PartyKey t := hp.1.resolve_right (by omega)
    have hk : ∀ u, IsQueryBoundP (k u) PartyKey 0 := fun u => by simpa [ht] using hp.2 u
    rcases t with (t | inbox) | input
    · change IsQueryBoundP ((OracleComp.lift (OracleSpec.query t) : OracleComp (LocalSpec C) _) >>=
        fun u => advance (k u)) LocalKey 0 ∧ _
      constructor
      · rw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl ht, fun u => by simpa [show ¬ LocalKey t from ht] using (ih u (hk u)).1⟩
      · intro s hs
        obtain ⟨u, _, hs⟩ := (mem_support_bind_iff _ _ _).mp hs
        exact (ih u (hk u)).2 s hs
    · exact ⟨isQueryBoundP_pure _ _ _, fun s hs => by
        change s ∈ support (pure (.wait inbox k) : OracleComp (LocalSpec C) _) at hs
        have he : s = .wait inbox k := by simpa using hs
        subst s
        exact hk⟩
    · exact input.elim

theorem start_base_keyQuiet {α : Type} (D : C.Coalition) (program : C.Party → PartyM C E RealSpec α)
    (hp : ∀ i, IsQueryBoundP (program i).run PartyKey 0) :
    IsQueryBoundP (startSteps base4 D program) FreeStreamKey 0 ∧
      ∀ steps ∈ support (startSteps base4 D program), ∀ i, StepKeyQuiet (steps i) := by
  constructor
  · apply zero_sequenceFin
    intro i
    by_cases hi : i ∈ D.1
    · simp only [hi, if_pos]; exact isQueryBoundP_pure _ _ _
    · simp only [hi]
      exact free_keyQuiet _ (advance_keyQuiet _ (hp i)).1
  · intro steps hs i
    have h := mem_support_sequenceFin_oc _ steps hs i
    by_cases hi : i ∈ D.1
    · simp only [hi, if_pos, mem_support_pure_iff] at h
      rw [h]
      trivial
    · simp only [hi] at h
      exact (advance_keyQuiet _ (hp i)).2 _ (free_support _ h)

theorem round_base_keyQuiet {α I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (hs : ∀ i, StepKeyQuiet (steps i)) :
    IsQueryBoundP (stepRound base4 D A noFunctionality state steps) FreeStreamKey 0 ∧
      ∀ r ∈ support (stepRound base4 D A noFunctionality state steps), ∀ i, StepKeyQuiet (r.2.1 i) := by
  let local_ (sent : C.Party → C.Party → Option (Msg E)) (j : C.Party) :
      OracleComp (Spec4 C) (Step C E RealSpec α) :=
    match steps j with
    | .done out => pure (.done out)
    | .wait _ resume => if j ∈ D.1 then pure (.done none) else
        freeCopy4 (advance (resume (roundInbox D sent steps j)))
    | .call input _ => input.elim
  have hl (sent) (j) : IsQueryBoundP (local_ sent j) FreeStreamKey 0 ∧
      ∀ s ∈ support (local_ sent j), StepKeyQuiet s := by
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
        have hp : IsQueryBoundP (resume (roundInbox D sent steps j)) PartyKey 0 := by
          have h := hs j
          rw [hj] at h
          exact h _
        exact ⟨free_keyQuiet _ (advance_keyQuiet _ hp).1,
          fun s h => (advance_keyQuiet _ hp).2 s (free_support _ h)⟩
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
  · exact zero_bind FreeStreamKey (advCopy4_quietP _ fun _ h => h) fun r _ =>
      zero_bind FreeStreamKey (zero_sequenceFin _ _ fun j => (hl r.2 j).1)
        fun _ _ => isQueryBoundP_pure _ _ _
  · intro r hr i
    simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨r', _, next, hn, rfl⟩ := hr
    exact (hl r'.2 i).2 _ (mem_support_sequenceFin_oc _ next hn i)

theorem rounds_base_keyQuiet {α I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (hs : ∀ i, StepKeyQuiet (steps i)) :
    IsQueryBoundP (executeRounds base4 D A noFunctionality fuel state steps) FreeStreamKey 0 := by
  induction fuel generalizing state steps with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ fuel ih =>
    rw [executeRounds]
    split
    · exact isQueryBoundP_pure _ _ _
    · exact zero_bind FreeStreamKey (round_base_keyQuiet D A state steps hs).1 fun r hr =>
        ih r.1 r.2.1 ((round_base_keyQuiet D A state steps hs).2 r hr)

/-- The real keygen phase on `base4` asks no free stream-key hash, for every oracle answer. -/
theorem keygen_phase_keyQuiet {I : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (state : A.State) (fuel : ℕ) :
    IsQueryBoundP (executePhase base4 D A noFunctionality fuel state
      fun i => (keygen i : PartyM C E RealSpec (Keys C))) FreeStreamKey 0 := by
  exact zero_bind FreeStreamKey (start_base_keyQuiet D _ keygen_keyQuiet).1 fun steps hs =>
    rounds_base_keyQuiet D A fuel state steps ((start_base_keyQuiet D _ keygen_keyQuiet).2 steps hs)

end Keygen

theorem tweakable_keyQuiet {α : Type} (p : OracleComp HashSpec α) :
    IsQueryBoundP (tweakable (C := C) p) RoKey 0 :=
  LifetimeKeygenPrograms.qb0_simulateQ _ (fun _ => hash_keyQuiet _ id) p

theorem prfValue_keyQuiet (seeds : C.Term → HashOutput) (x : Point) :
    IsQueryBoundP (prfValue seeds x) RoKey 0 := by
  unfold prfValue
  apply zero_bind RoKey (zero_mapM _ _ _ fun _ => ?_) fun _ _ => isQueryBoundP_pure _ _ _
  exact (isQueryBoundP_map_iff _ _ _).2 (hash_keyQuiet _ id)

theorem eval_keyQuiet (keys : Keys C) (i : C.Party) (J : C.Quorum) (x : Point) (message : Message) :
    IsQueryBoundP (eval keys i J x message) RoKey 0 := by
  unfold eval
  refine zero_bind RoKey (zero_mapM _ _ _ fun _ => ?_) fun _ _ => ?_
  · exact (isQueryBoundP_map_iff _ _ _).2 (hash_keyQuiet _ id)
  exact zero_bind RoKey (zero_mapM _ _ _ fun _ =>
    (isQueryBoundP_map_iff _ _ _).2 (hash_keyQuiet _ id)) fun _ _ => isQueryBoundP_pure _ _ _

section Signing

variable {ι : Type} {spec : OracleSpec ι} (P : ι → Prop)
variable (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → OracleComp spec α)
variable (hlift : ∀ {α : Type} (p : OracleComp (RoSpec C) α),
  IsQueryBoundP p RoKey 0 → IsQueryBoundP (lift p) P 0)

include hlift

theorem signRound2With_keyQuiet (part : Point → OracleComp spec Digest)
    (hp : ∀ x, IsQueryBoundP (part x) P 0) (parameter : PublicParameter) (J : C.Quorum)
    (commitment : Digest) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    IsQueryBoundP (signRound2With lift part parameter J commitment e message parts) P 0 := by
  unfold signRound2With
  apply zero_bind P (hlift _ (tweakable_keyQuiet _))
  rintro (_ | ⟨randomness, encoding⟩) _
  · exact isQueryBoundP_pure _ _ _
  apply zero_bind P (zero_sequenceFin _ _ fun l => ?_) fun _ _ => isQueryBoundP_pure _ _ _
  split
  · exact (isQueryBoundP_map_iff _ _ _).2 (hp _)
  · exact isQueryBoundP_pure _ _ _

theorem referenceJob_keyQuiet (value : Point → OracleComp spec Digest)
    (hv : ∀ x, IsQueryBoundP (value x) P 0) (parameter : PublicParameter) (job : Job) :
    IsQueryBoundP (referenceJob (fun p => lift (tweakable p)) value parameter job) P 0 := by
  unfold referenceJob
  apply zero_bind P (zero_mapM _ _ _ hv)
  intro values _
  cases job.kind with
  | chainEnd key l => exact (isQueryBoundP_map_iff _ _ _).2 (hlift _ (tweakable_keyQuiet _))
  | chainRow key l =>
    exact zero_bind P (hlift _ (tweakable_keyQuiet _)) fun _ _ =>
      zero_bind P (hlift _ (tweakable_keyQuiet _)) fun _ _ =>
        zero_bind P (hlift _ (tweakable_keyQuiet _)) fun _ _ => isQueryBoundP_pure _ _ _
  | chainValue key l p => exact (isQueryBoundP_map_iff _ _ _).2 (hlift _ (tweakable_keyQuiet _))
  | commitment key => exact (isQueryBoundP_map_iff _ _ _).2 (hlift _ (tweakable_keyQuiet _))
  | randomizer => exact isQueryBoundP_pure _ _ _

theorem referenceTree_keyQuiet (value : Point → OracleComp spec Digest)
    (hv : ∀ x, IsQueryBoundP (value x) P 0) (parameter : PublicParameter) (top : TopTree) (tree : Tree) :
    IsQueryBoundP (referenceTree (fun p => lift (tweakable p)) value parameter top tree) P 0 :=
  ceremonyOutput_quiet P _ (fun p => hlift _ (tweakable_keyQuiet p)) _
    (fun _js => (isQueryBoundP_map_iff _ _ _).2
      (zero_mapM _ _ _ fun job => referenceJob_keyQuiet P lift hlift value hv parameter job))
    parameter top tree

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
theorem dealtWith_keyQuiet (parameter : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (value : Point → OracleComp spec Digest) (hv : ∀ x, IsQueryBoundP (value x) P 0) :
    DealtQuiet P (dealtWith lift parameter keys top value) := by
  refine ⟨hv, fun i J x message => hlift _ (eval_keyQuiet _ _ _ _ _), fun b => ?_⟩
  change IsQueryBoundP (_ <$> referenceTree (fun p => lift (tweakable p)) value parameter top (.bottom b)) P 0
  with_reducible exact ((isQueryBoundP_map_iff _ _ _).2
    (referenceTree_keyQuiet P lift hlift value hv parameter top (.bottom b)))

theorem honestSignature_keyQuiet (dealt : Dealt C (OracleComp spec)) (hd : DealtQuiet P dealt)
    (e : KeyIndex) (message : Message) : IsQueryBoundP (honestSignature lift dealt e message) P 0 := by
  unfold honestSignature
  apply zero_bind P (hd.bottom _)
  rintro (_ | tree) _
  · exact isQueryBoundP_pure _ _ _
  apply zero_bind P (hd.value _)
  intro rho _
  apply zero_bind P (hlift _ (tweakable_keyQuiet _))
  rintro (_ | ⟨randomness, encoding⟩) _
  · exact isQueryBoundP_pure _ _ _
  refine zero_bind P (zero_sequenceFin _ _ fun l => ?_) (fun values _ => ?_)
  · split
    · exact hd.value _
    · exact isQueryBoundP_pure _ _ _
    · exact zero_bind P (hd.value _) fun _ _ => isQueryBoundP_pure _ _ _
  · exact zero_bind P (hlift _ (tweakable_keyQuiet _)) fun _ _ => isQueryBoundP_pure _ _ _

theorem forgeryWins_keyQuiet (dealt : Dealt C (OracleComp spec)) (hd : DealtQuiet P dealt)
    (st : TsigState C) (forgery : Forgery) : IsQueryBoundP (forgeryWins lift dealt st forgery) P 0 := by
  unfold forgeryWins
  apply zero_bind P (hlift _ (tweakable_keyQuiet _))
  intro verified _
  split
  · exact isQueryBoundP_pure _ _ _
  · exact zero_bind P (honestSignature_keyQuiet P lift hlift dealt hd _ _) fun _ _ =>
      isQueryBoundP_pure _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- One signing oracle step asks no `P` query, when the dealt values and `lift` ask none. -/
theorem tsig_keyQuiet (dealt : Dealt C (OracleComp spec)) (hd : DealtQuiet P dealt)
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
        apply zero_bind P (signRound2With_keyQuiet P lift hlift _ (hd.part i J · message) _ _ _ _ _ _)
        rintro (_ | values) _
        · exact isQueryBoundP_pure _ _ _
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
          exact isQueryBoundP_pure _ _ _

end Signing

/-- Every run interface of `program4` avoids the free copy. -/
theorem roles4_keyQuiet (n r : ℕ) : RolesQuiet FreeStreamKey (roles4 (C := C) n r) := by
  unfold roles4
  split
  · exact fun p => ⟨advCopy4_quietP p fun _ h => h, emulCopy4_quietP p fun _ h => h⟩
  · split
    · exact fun p => ⟨advCopy4_quietP p fun _ h => h, targetCopy4_quietP p fun _ h => h⟩
    · exact fun p => ⟨advCopy4_quietP p fun _ h => h, advCopy4_quietP p fun _ h => h⟩

theorem roFree_keyQuiet {α : Type} (p : OracleComp (RoSpec C) α)
    (hp : IsQueryBoundP p RoKey 0) : IsQueryBoundP (roFree p) FreeStreamKey 0 :=
  free_keyQuiet _ (ro_local_keyQuiet p hp)

theorem signerDealt_keyQuiet (keys : C.Party → Keys C)
    (value : Point → OracleComp (Spec4 C) Digest)
    (hv : ∀ x, IsQueryBoundP (value x) FreeStreamKey 0) (st : LifetimeState C E) (i : C.Party) :
    DealtQuiet FreeStreamKey (ThresholdLeanXmss.signerDealt roFree keys value st i) :=
  ⟨hv, fun _ _ _ _ => roFree_keyQuiet _ (eval_keyQuiet _ _ _ _ _),
    fun _ => isQueryBoundP_pure _ _ _⟩

section Lifetime

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts n : ℕ)
variable (D : C.Coalition)

omit [Fintype E] [DecidableEq E] in
set_option maxRecDepth 2000 in
theorem lifetimeOracles_keyQuiet (keys : C.Party → Keys C)
    (value : Point → OracleComp (Spec4 C) Digest)
    (hv : ∀ x, IsQueryBoundP (value x) FreeStreamKey 0) (h : C.Party)
    (q : (LifetimeSpec C E).Domain) (st : LifetimeState C E) :
    IsQueryBoundP ((lifetimeOraclesWith K circuits settings attempts (roles4 n) base4 D
      keys value h q).run st) FreeStreamKey 0 := by
  have sign (i : C.Party) (q : (TsigSpec C).Domain) (st : LifetimeState C E) :
      IsQueryBoundP ((tsigOracles roFree (ThresholdLeanXmss.signerDealt roFree keys value st i) q).run st.sign)
        FreeStreamKey 0 :=
    tsig_keyQuiet FreeStreamKey roFree (fun p hp => roFree_keyQuiet p hp) _
      (signerDealt_keyQuiet keys value hv st i) q st.sign
  cases q with
  | sign q =>
    cases q with
    | corrupt i => exact isQueryBoundP_pure _ _ _
    | tree b =>
      change IsQueryBoundP ((_ >>= _) : OracleComp (Spec4 C) _) FreeStreamKey 0
      exact zero_bind FreeStreamKey (sign h (.tree b) st) fun _ _ => isQueryBoundP_pure _ _ _
    | round1 i J e message =>
      simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind]
      split
      · exact isQueryBoundP_pure _ _ _
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        exact zero_bind FreeStreamKey (sign i (.round1 i J e message) _) fun _ _ =>
          isQueryBoundP_pure _ _ _
    | round2 i J e message parts =>
      simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind]
      split
      · exact isQueryBoundP_pure _ _ _
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        exact zero_bind FreeStreamKey (sign i (.round2 i J e message parts) _) fun _ _ =>
          isQueryBoundP_pure _ _ _
  | publicKey => exact isQueryBoundP_pure _ _ _
  | start tree =>
    cases tree <;>
      simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind] <;>
      split
    · exact isQueryBoundP_pure _ _ _
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, StateT.run_set,
        StateT.run_pure, pure_bind]
      exact zero_bind FreeStreamKey (startSteps_quietP (roles4_keyQuiet n st.runCount) D _) fun _ _ =>
        isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_pure _ _ _
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, StateT.run_set,
        StateT.run_pure, pure_bind]
      exact zero_bind FreeStreamKey (startSteps_quietP (roles4_keyQuiet n st.runCount) D _) fun _ _ =>
        isQueryBoundP_pure _ _ _
  | round sent =>
    simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind]
    cases hr : st.running with
    | none => exact isQueryBoundP_pure _ _ _
    | some r =>
      rcases r with ⟨tree, fuel, steps⟩
      simp only [StateT.run_bind, StateT.run_lift, bind_assoc, StateT.run_set,
        StateT.run_pure, pure_bind]
      exact zero_bind FreeStreamKey (stepRound_quietP (roles4_keyQuiet n (st.runCount - 1)) D
        (roundAdversary (I := PEmpty) sent) () steps) fun _ _ => isQueryBoundP_pure _ _ _

omit [Fintype E] [DecidableEq E] in
set_option maxRecDepth 3000 in
/-- The keygen and the signing of `program4` hash no stream key on the free copy. -/
theorem freeStreamKeyQuiet (A : LifetimeAdversary C E) :
    FreeStreamKeyQuiet K circuits settings attempts D n A := by
  unfold FreeStreamKeyQuiet program4 lifetimeGameWith
  apply zero_bind FreeStreamKey (advCopy4_quietP _ fun _ h => h)
  intro state _
  apply zero_bind FreeStreamKey (keygen_phase_keyQuiet D A.keygen state setupRounds)
  rintro ⟨state', outputs⟩ _
  cases hh : C.parties.find? (· ∉ D.1) with
  | none => exact isQueryBoundP_pure _ _ _
  | some h =>
    simp only
    split
    · exact isQueryBoundP_pure _ _ _
    · apply zero_bind FreeStreamKey (simulate_run_quiet FreeStreamKey _ (fun q st => ?_) _ _)
      · rintro ⟨forgery, st⟩ _
        split
        · exact isQueryBoundP_pure _ _ _
        · cases hp : st.publicKey ((outputs h).getD default).parameter h with
          | none => exact isQueryBoundP_pure _ _ _
          | some pk =>
            exact forgeryWins_keyQuiet FreeStreamKey roFree (fun p hp => roFree_keyQuiet p hp) _
              (dealtWith_keyQuiet FreeStreamKey roFree (fun p hp => roFree_keyQuiet p hp) _ _ _ _
                (fun x => roFree_keyQuiet _ (prfValue_keyQuiet _ x))) st.sign forgery
      · rcases q with t | q
        · simp only [QueryImpl.add_apply_inl]
          exact zero_bind FreeStreamKey (advCopy4_quietP _ fun _ h => h) fun _ _ =>
            isQueryBoundP_pure _ _ _
        · exact lifetimeOracles_keyQuiet K circuits settings attempts n D _ _
            (fun x => roFree_keyQuiet _ (prfValue_keyQuiet _ x)) h q st

end Lifetime

section Reduction

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ) (aes : Aes)
variable (circuitsOf : (HashInput → HashOutput) → Circuits) (D : C.Coalition) (A : LifetimeAdversary C E)
variable (values : MpcDomain → HashOutput) (n : ℕ)

/-- The cover of the stream-key bad event of hybrid `n` for one `Th`. -/
theorem reductionGame_bad :
    ∀ y ∈ support (runBoundary K (circuitsOf (thOf values)) settings attempts D n A ⟨thOf values, aes⟩),
      y.2.2.bad = true →
        ¬ KeysApart D (rowsAt y.1.1) ∨
          (KeysApart D (rowsAt y.1.1) ∧ KeyHit D (rowsAt y.1.1) y.2.2.hash) :=
  LifetimeRunBoundary.reductionGame_bad K settings attempts aes circuitsOf D A values n
    (freeStreamKeyQuiet K _ settings attempts n D A)

end Reduction

/-- info: 'ThresholdLeanXmssSecurity.LifetimeStreamKeyQuiet.freeStreamKeyQuiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freeStreamKeyQuiet

/-- info: 'ThresholdLeanXmssSecurity.LifetimeStreamKeyQuiet.reductionGame_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reductionGame_bad

end ThresholdLeanXmssSecurity.LifetimeStreamKeyQuiet
