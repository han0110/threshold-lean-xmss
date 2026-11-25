import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Collision.SetupBudgets
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Partition

/-!
# The cost of the reduction of a top slot

`slotHandler_bound` states that the handler of a slot reduction turns each call of the class
`prssSetup` on either copy into one counted call and makes no other counted call. `simulateQ_pot`
bounds a simulation on a state with a potential. The other lemmas bound the calls of the class of
the parts of the hybrid game, and `topSlotPartCosts` proves `TopSlotPartCosts`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

/-! ## The handler of a slot reduction -/

section Handler

variable {C : Committee} (prims : Primitives)

/-- Private coins make no counted call. -/
theorem liftComp_uncounted {α : Type} (pc : ProbComp α) :
    IsQueryBoundP (liftComp pc (LocalSpec C)) Counted 0 := by
  induction pc using OracleComp.inductionOn with
  | pure x => simp
  | query_bind n k ih =>
    have e : liftComp (liftM (unifSpec.query n) : ProbComp _) (LocalSpec C) =
        (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inl n)) : OracleComp _ _) := rfl
    rw [liftComp_bind, e]
    refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl fun h => h, fun u => ?_⟩
    have hn : ¬ Counted (C := C) (.inl n) := fun h => h
    simpa [hn] using ih u

/-- A forwarded call of the class `prssSetup` is one counted call. -/
theorem forward_counted (q : Query C) (hq : queryClass q = .prssSetup) {σ : Type} (s : σ) :
    IsQueryBoundP ((liftM (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q)))) :
      StateT σ (OracleComp (LocalSpec C)) _).run s) Counted 1 := by
  have hc : Counted (C := C) (.inr (.inl q)) := by
    cases q <;> simp_all [Counted, queryClass]
  refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr Nat.one_pos, fun u => ?_⟩
  simp [hc]

/-- A call of `H` is in the class `prssSetup` when its input is. -/
theorem inClass_prssSetup_iff (q : Query C) :
    InClass (C := C) .prssSetup (.inr (.inl q)) ↔ queryClass q = .prssSetup := by
  cases q <;> simp [InClass, queryClass]

/-- One step of `slotHandler` makes one counted call for a call of `Adds .prssSetup` and none for
another call. -/
theorem slotHandler_step (D : C.Coalition) (t : (WorldSpec C).Domain) (s : KeyJointState C) :
    IsQueryBoundP ((slotHandler prims D t).run s) Counted
      (if FirstCounts.Adds .prssSetup t then 1 else 0) := by
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals first
    | (by_cases hq : queryClass q = .prssSetup
       · simp only [slotHandler, hq, ite_true]
         exact (forward_counted q hq s).mono (by simp [FirstCounts.Adds, inClass_prssSetup_iff, hq])
       · simp only [slotHandler, hq, ite_false, StateT.run_mk]
         exact (liftComp_uncounted _).mono (Nat.zero_le _))
    | (simp only [slotHandler, StateT.run_mk]; exact (liftComp_uncounted _).mono (Nat.zero_le _))

/-- A computation with at most `n` calls of `Adds .prssSetup` gives, under `slotHandler`, a
computation with at most `n` counted calls, from each private state. -/
theorem slotHandler_bound (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α) (n : ℕ)
    (h : IsQueryBoundP oa (FirstCounts.Adds .prssSetup) n) (s : KeyJointState C) :
    IsQueryBoundP ((simulateQ (slotHandler prims D) oa).run s) Counted n :=
  h.simulateQ_run_StateT_of_step (slotHandler_step prims D) s

end Handler

/-! ## A simulation on two states with a potential -/

/-- A simulation on two states with a potential `Φ` of the inner state. Each step of the handler from
the states `st` and `s` makes at most `d` calls of `P`, and each inner state at its end has a potential
of at most `Φ s` plus `c` for a call of `Q`, less `d`. Then a source with at most `n` calls of `Q`
makes at most `n c + Φ s` calls of `P` from `st` and `s`. -/
theorem simulateQ_pot {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {τ σ α : Type}
    (impl : QueryImpl spec (StateT τ (StateT σ (OracleComp spec')))) (Q : ι → Prop) (P : ι' → Prop)
    (Φ : σ → ℕ) (c : ℕ)
    (hstep : ∀ t st s, ∃ d, d ≤ Φ s + (if Q t then c else 0) ∧ IsQueryBoundP (((impl t).run st).run s) P d ∧
      ∀ r ∈ support (((impl t).run st).run s), Φ r.2 + d ≤ Φ s + if Q t then c else 0)
    (oa : OracleComp spec α) :
    ∀ n, IsQueryBoundP oa Q n → ∀ st s, IsQueryBoundP (((simulateQ impl oa).run st).run s) P (n * c + Φ s) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n _ st s; simp
  | query_bind t k ih =>
    intro n h st s
    rw [isQueryBoundP_query_bind_iff] at h
    obtain ⟨d, hd, hb, hsupp⟩ := hstep t st s
    rw [simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    change IsQueryBoundP ((((impl t).run st).run s) >>= fun p =>
      ((simulateQ impl (k p.1.1)).run p.1.2).run p.2) P _
    refine (isQueryBoundP_bind hb (m := (if Q t then n - 1 else n) * c + (Φ s + (if Q t then c else 0) - d))
      fun r hr => (ih r.1.1 _ (h.2 r.1.1) r.1.2 r.2).mono ?_).mono ?_
    · have := hsupp r hr
      omega
    · by_cases hq : Q t
      · have hn := h.1.resolve_left (not_not.2 hq)
        simp only [hq, ↓reduceIte] at hd ⊢
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel, Nat.succ_mul]
        omega
      · simp only [hq, ↓reduceIte] at hd ⊢
        omega

/-! ## The calls of the class of one operator -/

section Operator

open SetupBudgets DigestBudgets

variable {C : Committee} {E : Type}

theorem parties_length_eq : C.parties.length = C.n := by
  simp [Committee.parties]

theorem PBound.map {p : (LocalSpec C).Domain → Prop} {α β : Type} {prog : PartyM C E RealSpec α} {n : ℕ}
    (f : α → β) (h : PBound p prog n) : PBound p (f <$> prog) n := by
  unfold PBound at h ⊢
  simpa [OptionT.run_map] using h

/-- The setup with commit, reveal and echo of the PRSS of one operator makes at most
`4 n + termCount C` calls of the class `prssSetup`. -/
theorem commitRevealEcho_classBound (i : C.Party) (own : Parts C) :
    PBound (InClass (C := C) .prssSetup) (commitRevealEcho .prss i own : PartyM C E RealSpec _)
      (4 * C.n + termCount C) := by
  have hp : ∀ t, InClass (C := C) .prssSetup t → InClass .prssSetup t := fun _ h => h
  have h1 : ∀ x : Query C, IsQueryBoundP (hashQuery x) (fun t => InClass (C := C) .prssSetup (.inr t)) 1 :=
    fun x => (hashQuery_queryBound x).of_imp fun _ _ => trivial
  have hex : ∀ outbox : Mail C E, PBound (InClass (C := C) .prssSetup) (exchange outbox : PartyM C E RealSpec _) 0 :=
    fun outbox => PBound.of_class hp (ClassBound.exchange outbox)
  have hreq : ∀ q : Prop, PBound (InClass (C := C) .prssSetup) (require q : PartyM C E RealSpec Unit) 0 :=
    fun q => PBound.of_class hp (ClassBound.require q)
  have hmap : ∀ f : C.Party → Query C, IsQueryBoundP (C.parties.mapM fun j => hashQuery (f j))
      (fun t => InClass (C := C) .prssSetup (.inr t)) C.n := fun f => by
    simpa [parties_length_eq] using queryBound_mapM _ (fun j => hashQuery (f j)) 1 C.parties fun j _ => h1 (f j)
  unfold commitRevealEcho
  refine (PBound.bind (PBound.oracleStep (hmap _)) fun _ =>
    PBound.bind (n := 0) (hex _) fun _ => PBound.bind (n := 0) (hex _) fun _ =>
    PBound.bind (PBound.oracleStep (hmap _)) fun _ =>
    PBound.bind (n := 0) (hreq _) fun _ => PBound.bind (PBound.oracleStep (deriveKeys_count _ i _)) fun _ =>
    PBound.bind (PBound.oracleStep (hmap _)) fun _ =>
    PBound.bind (n := 0) (hex _) fun _ => PBound.bind (n := 0) (hreq _) fun _ => PBound.pure _).mono ?_
  rw [parties_length_eq, check_terms_length, termCount]
  omega

/-- One PRSS setup of one operator makes at most `4 n + termCount C` calls of the class `prssSetup`. -/
theorem prssSetup_classBound (i : C.Party) :
    PBound (InClass (C := C) .prssSetup) (prssSetup i : PartyM C E RealSpec _) (4 * C.n + termCount C) := by
  unfold prssSetup prssSetupWith
  exact (PBound.bind (n := 0) (PBound.localStep ((liftComp_prob_bound .prssSetup _).of_imp fun _ h => h))
    fun own => PBound.bind (m := 0) (commitRevealEcho_classBound i own) fun _ => PBound.pure _).mono (by omega)

/-- A program on a state over the counter of the ceremonies makes at most `n` local calls of `p` from
each state and each counter. -/
def PState2 (p : (LocalSpec C).Domain → Prop) {σ α : Type}
    (prog : StateT σ (StateT ℕ (PartyM C E RealSpec)) α) (n : ℕ) : Prop :=
  ∀ s, PState p (prog.run s) n

variable {p : (LocalSpec C).Domain → Prop}

theorem PState2.mono {σ α : Type} {prog : StateT σ (StateT ℕ (PartyM C E RealSpec)) α} {n m : ℕ}
    (h : PState2 p prog n) (hnm : n ≤ m) : PState2 p prog m := fun s => (h s).mono hnm

theorem PState2.pure {σ α : Type} (a : α) : PState2 p (pure a : StateT σ (StateT ℕ (PartyM C E RealSpec)) α) 0 :=
  fun _ => PState.pure _

theorem PState2.bind {σ α β : Type} {prog : StateT σ (StateT ℕ (PartyM C E RealSpec)) α}
    {f : α → StateT σ (StateT ℕ (PartyM C E RealSpec)) β} {n m : ℕ} (h : PState2 p prog n)
    (hf : ∀ a, PState2 p (f a) m) : PState2 p (prog >>= f) (n + m) := fun s =>
  PState.bind (h s) fun a => hf a.1 a.2

theorem PState2.bind_le {σ α β : Type} {prog : StateT σ (StateT ℕ (PartyM C E RealSpec)) α}
    {f : α → StateT σ (StateT ℕ (PartyM C E RealSpec)) β} {n m k : ℕ} (h : PState2 p prog n)
    (hf : ∀ a, PState2 p (f a) m) (hk : n + m ≤ k) : PState2 p (prog >>= f) k :=
  (PState2.bind h hf).mono hk

theorem PState2.lift {σ α : Type} {prog : StateT ℕ (PartyM C E RealSpec) α} {n : ℕ} (h : PState p prog n) :
    PState2 p (StateT.lift prog : StateT σ (StateT ℕ (PartyM C E RealSpec)) α) n := fun s => by
  change PState p (prog >>= fun a => Pure.pure (a, s)) n
  simpa using PState.bind h fun a => PState.pure (p := p) (a, s)

theorem PState2.get {σ : Type} : PState2 p (get : StateT σ (StateT ℕ (PartyM C E RealSpec)) σ) 0 :=
  fun _ => PState.pure _

theorem PState2.set {σ : Type} (s : σ) : PState2 p (set s : StateT σ (StateT ℕ (PartyM C E RealSpec)) PUnit) 0 :=
  fun _ => PState.pure _

theorem PState2.mapM {σ α β : Type} (f : α → StateT σ (StateT ℕ (PartyM C E RealSpec)) β) (n : ℕ)
    (hf : ∀ a, PState2 p (f a) n) : ∀ xs : List α, PState2 p (xs.mapM f) (xs.length * n)
  | [] => by simpa using PState2.pure (p := p) (σ := σ) ([] : List β)
  | a :: xs => by
    rw [List.mapM_cons]
    simpa [Nat.succ_mul, Nat.add_comm] using
      (hf a).bind fun b => (PState2.mapM f n hf xs).bind fun bs => PState2.pure (p := p) (b :: bs)

/-- The ceremonies of a tree on the counter of the ceremonies make the calls of `p` of
`treeSetups tree` runs. -/
theorem ceremonyOutput_pbound2
    (lift : ∀ {α : Type}, OracleComp HashSpec α → StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α)
    (hlift : ∀ {α : Type} (oa : OracleComp HashSpec α), PState2 p (lift oa) 0) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) (Option (List (List Bit)))) (R : ℕ)
    (hrun : ∀ jobs, PState2 p (run jobs) R) (top : TopTree) (tree : Tree) :
    PState2 p (ceremonyOutput lift parameter run top tree) (treeSetups tree * R) := by
  cases tree with
  | top =>
    unfold ceremonyOutput
    refine PState2.bind_le (hrun topJobs) (m := 0) (fun out => ?_) (by simp [treeSetups])
    rcases out with _ | outputs
    · exact PState2.pure _
    · exact PState2.bind_le (hlift _) (fun _ => PState2.pure _) le_rfl
  | bottom b =>
    unfold ceremonyOutput
    refine PState2.bind_le (hrun (bottomJobs b)) (m := R) (fun out => ?_) (by simp [treeSetups]; omega)
    rcases out with _ | outputs
    · exact (PState2.pure _).mono (Nat.zero_le _)
    refine PState2.bind_le (hlift _) (m := R) (fun root => ?_) (by omega)
    refine PState2.bind_le (hlift _) (m := R) (fun base => ?_) (by omega)
    refine PState2.bind_le (hlift _) (m := R) (fun found => ?_) (by omega)
    rcases found with _ | ⟨randomness, encoding⟩
    · exact (PState2.pure _).mono (Nat.zero_le _)
    refine PState2.bind_le (hrun _) (m := 0) (fun out => ?_) (by omega)
    rcases out with _ | values
    · exact PState2.pure _
    refine PState2.bind_le (hlift _) (m := 0) (fun path => ?_) (by omega)
    refine PState2.bind_le (hlift _) (m := 0) (fun topRoot => ?_) (by omega)
    split_ifs
    · exact PState2.pure _
    · exact PState2.pure _

variable [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- One ceremony of a slot makes the calls of the class `prssSetup` of its PRSS setup, for each
choice of fresh keys. -/
theorem slotCeremony_classBound (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (i : C.Party)
    (keys : Keys C) (jobs : List Job) :
    PState2 (InClass (C := C) .prssSetup) (slotCeremony K circuits settings D fresh i keys jobs)
      (4 * C.n + termCount C) := by
  have hp : ∀ t, InClass (C := C) .prssSetup t → InClass .prssSetup t := fun _ h => h
  unfold slotCeremony
  refine PState2.bind_le (n := 0) (PState2.lift (PState.of_class hp StateBound.get)) (fun c => ?_) (Nat.zero_add _).le
  refine PState2.bind_le (n := 0) (PState2.lift (PState.of_class hp (StateBound.set _))) (fun _ => ?_) (Nat.zero_add _).le
  refine PState2.bind_le (PState2.lift (PState.lift (prssSetup_classBound i))) (m := 0) (fun prss => ?_)
    (by omega)
  unfold batched
  refine PState2.bind_le (m := 0) ((PState2.mapM _ 0 (fun batch => ?_) _).mono (by simp))
    (fun _ => PState2.pure _) (Nat.add_zero _).le
  refine PState2.bind_le (n := 0) PState2.get (fun lk => ?_) (Nat.zero_add _).le
  rcases lk with ⟨label, k⟩
  refine PState2.bind_le (n := 0) (PState2.lift (PState.lift (PBound.of_class hp
    ((ClassBound.mapM _ 0 (fun job => inputShares_bound _ (by decide) job) _).mono (by simp)))))
    (fun inputs => ?_) (Nat.zero_add _).le
  refine PState2.bind_le (n := 0) (PState2.lift (PState.lift (PBound.of_class hp
    ((runJobs_bound (c := .prssSetup) K _ (by decide) (by decide) _ _ _ _).mono (by simp [digestCost, copyCost])))))
    (fun r => ?_) (Nat.zero_add _).le
  rcases r with ⟨outputs, state⟩
  exact PState2.bind_le (n := 0) (PState2.set _) (fun _ => PState2.pure _) (Nat.zero_add _).le

/-- The ceremonies of a tree at one operator make the calls of the class `prssSetup` of
`treeSetups tree` PRSS setups, for each choice of fresh keys. -/
theorem slotTree_classBound (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (i : C.Party)
    (keys : Keys C) (top : TopTree) (tree : Tree) :
    PBound (InClass (C := C) .prssSetup) (slotTree K circuits settings D fresh i keys top tree)
      (treeSetups tree * (4 * C.n + termCount C)) := by
  have hp : ∀ t, InClass (C := C) .prssSetup t → InClass .prssSetup t := fun _ h => h
  have hrun := ceremonyOutput_pbound2 (p := InClass (C := C) .prssSetup)
    (fun oa => StateT.lift (StateT.lift (oracleStep (tweakable oa))))
    (fun oa => PState2.lift (PState.lift (PBound.of_class hp
      (ClassBound.oracleStep_zero (noCall_of_onlySign (by decide) (GameCount.onlySign_tweakable oa))))))
    keys.parameter (slotCeremony K circuits settings D fresh i keys) _
    (fun jobs => slotCeremony_classBound K circuits settings D fresh i keys jobs) top tree (0, 0) 0
  unfold slotTree
  refine (PBound.bind (m := 0) ?_ fun out => ?_).mono (Nat.add_zero _).le
  · simp only [StateT.run'_eq, StateT.run_map]
    exact PBound.map _ (PBound.map _ hrun)
  · rcases out with _ | output
    · exact isQueryBoundP_pure _ _ _
    · exact PBound.pure _

/-- The program of an operator in a run of `tree` makes the calls of the class `prssSetup` of
`treeSetups tree` PRSS setups, for each choice of fresh keys. -/
theorem slotProgram_classBound (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (i : C.Party)
    (operator : OperatorState C) (tree : Tree) :
    PBound (InClass (C := C) .prssSetup) (slotProgram K circuits settings D fresh i operator tree)
      (treeSetups tree * (4 * C.n + termCount C)) := by
  cases tree with
  | top =>
    rcases hk : operator.keys with _ | keys
    · simp only [slotProgram, hk]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [slotProgram, hk]
      exact slotTree_classBound K circuits settings D fresh i keys _ _
  | bottom b =>
    rcases hk : operator.keys with _ | keys <;> rcases ht : operator.top with _ | top
    · simp only [slotProgram, hk]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [slotProgram, hk]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [slotProgram, hk, ht]
      exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
    · simp only [slotProgram, hk, ht]
      exact slotTree_classBound K circuits settings D fresh i keys _ _

/-- The program of an operator in a top run after its PRSS setup makes no call of the class
`prssSetup`. -/
theorem topAfterSetup_classBound (i : C.Party) (keys : Keys C) (prss : PrssKeys C) :
    PBound (InClass (C := C) .prssSetup) (topAfterSetup K circuits settings i keys prss) 0 := by
  have hp : ∀ t, InClass (C := C) .prssSetup t → InClass .prssSetup t := fun _ h => h
  unfold topAfterSetup
  refine (PBound.bind (m := 0) ?_ fun out => ?_).mono le_rfl
  · simp only [StateT.run'_eq]
    refine PBound.map _ ?_
    refine (ceremonyOutput_pbound (p := InClass (C := C) .prssSetup) _
      (fun oa => PState.of_class hp (lift_tweakable_bound (by decide) oa)) keys.parameter _ 0
      (fun jobs => PState.of_class hp ?_) emptyTop .top (0, 0)).mono (by simp [treeSetups])
    unfold batched
    refine StateBound.bind_zero' ((StateBound.mapM _ 0 (fun batch => ?_) _).mono (by simp))
      fun _ => StateBound.pure _
    refine StateBound.zero_bind StateBound.get fun lk => ?_
    rcases lk with ⟨label, k⟩
    refine StateBound.zero_bind (StateBound.lift_zero ((ClassBound.mapM _ 0
      (fun job => inputShares_bound _ (by decide) job) _).mono (by simp))) fun inputs => ?_
    refine StateBound.bind_zero' (StateBound.lift ((runJobs_bound (c := .prssSetup) K _ (by decide) (by decide)
      _ _ _ _).mono (by simp [digestCost, copyCost]))) fun r => ?_
    rcases r with ⟨outputs, state⟩
    exact StateBound.bind_zero (StateBound.set _) fun _ => StateBound.pure _
  · rcases out with _ | output
    · exact isQueryBoundP_pure _ _ _
    · exact PBound.pure _

end Operator

/-! ## The calls of the class in the parts of the hybrid game -/

section Game

open SetupBudgets DigestBudgets FirstCounts
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)

variable {C : Committee} {E : Type}

/-- Private coins on the free copy add no cell of a class. -/
theorem free_prob_adds (c : HashClass) {α : Type} (pc : ProbComp α) :
    IsQueryBoundP (free (liftComp pc (LocalSpec C))) (Adds c) 0 := by
  induction pc using OracleComp.inductionOn with
  | pure x => simp
  | query_bind n k ih =>
    have e : free (liftComp (liftM (unifSpec.query n) >>= k) (LocalSpec C)) =
        (liftM ((WorldSpec C).query (.inr (.inl n))) : OracleComp (WorldSpec C) _) >>= fun u =>
          free (liftComp (k u) (LocalSpec C)) := by
      rw [liftComp_bind, ThresholdLeanXmssSecurity.free_bind]
      rfl
    rw [e]
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl fun h => h, fun u => by simpa using ih u⟩

/-- A computation of the adversary with `n` calls of the class makes `n` calls of `Adds`. -/
theorem adversary_adds {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ)
    (h : IsQueryBoundP oa (InClass .prssSetup) n) :
    IsQueryBoundP (worldRoles.adversary oa) (Adds .prssSetup) n :=
  (isQueryBoundP_add (fun _ => adds_or .prssSetup) _ _ _ (ownAdds_adversary _ _ _ h)
    (honestIn_adversary .prssSetup oa)).mono (by omega)

/-- A phase on the network with an adversary of `step` calls of the class in each round and honest
programs of `R` calls each makes at most `fuel step + n R` calls of `Adds`. -/
theorem phase_adds {α : Type} (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) (InClass .prssSetup) step) (fuel : ℕ)
    (st : net.State) (program : C.Party → PartyM C E RealSpec α) (R : ℕ)
    (hp : ∀ i, PBound (InClass (C := C) .prssSetup) (program i) R) :
    IsQueryBoundP (executePhase worldRoles D net noFunctionality fuel st program) (Adds .prssSetup)
      (fuel * step + C.n * R) := by
  have honest := executePhase_boundP (InClass (C := C) .prssSetup) D net fuel st program (fun _ => R)
    fun j _ => hp j
  have honest' : IsQueryBoundP (executePhase worldRoles D net noFunctionality fuel st program)
      (HonestIn .prssSetup) (C.n * R) := by
    refine ((isQueryBoundP_congr_pred fun t => ?_).1 honest).mono (le_of_eq ?_)
    · rcases t with _ | _ <;> exact Iff.rfl
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact isQueryBoundP_add (fun _ => adds_or .prssSetup) _ _ _
    (ownAdds_executePhase _ D net step hround fuel st program) honest'

/-- The monitor adds no cell of the class. -/
theorem wrongOutput_adds (D : C.Coalition) (keys : C.Party → Option (Keys C)) (tree : Tree)
    (outputs : C.Party → Option TreeOutput) :
    GameCount.Bound (Adds .prssSetup) (wrongOutput D keys tree outputs) 0 :=
  bound_of_noCall (GameCount.wrongOutput_noCall D (Adds .prssSetup)
    (fun _ ht => monitorCall_not_adds (by decide) ht) keys tree outputs)

variable [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- One run of `tree` in hybrid `j` from each state, with its vote, makes at most
`(treeFuel + 1) step + treeSetups tree setupClassCalls` calls of `Adds`. -/
theorem fixedTreeRun_adds (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) (InClass .prssSetup) step) (tree : Tree)
    (s : RealState C net.State) :
    IsQueryBoundP ((fixedTreeRun K circuits settings runLimit j (wrongOutput D) D net tree).run s)
      (Adds .prssSetup) ((treeFuel circuits settings + 1) * step + treeSetups tree * setupClassCalls C) := by
  unfold fixedTreeRun
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc]
  refine (isQueryBoundP_bind (n := 0) (free_prob_adds _ _) fun fresh _ => ?_).mono (Nat.zero_add _).le
  refine (isQueryBoundP_bind (phase_adds D net step hround _ _ _ _
    fun i => slotProgram_classBound K circuits settings D _ i _ tree) (m := step) fun r _ => ?_).mono ?_
  · rw [← GameCount.bound_iff]
    refine GameCount.bound_mono (GameCount.bound_bind (n := 0) (m := step)
      (wrongOutput_adds D (fun i => (s.operators i).keys) tree r.2) fun b => ?_) (Nat.zero_add _).le
    rw [GameCount.bound_iff]
    exact (isQueryBoundP_bind (n := step) (m := 0) (FirstCounts.voteRound_adds .prssSetup (by decide) D net step
      hround _ _ fun j q hq => by
        obtain ⟨o, -, rfl⟩ := Option.map_eq_some_iff.1 hq
        exact FirstCounts.queryClass_treeVote tree o) fun _ _ => isQueryBoundP_pure _ _ _).mono le_rfl
  · simp only [setupClassCalls]
    nlinarith

/-- At most `count` runs of `tree` make at most `count` times the cost of one run. -/
theorem fixedTreeRuns_adds (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) (InClass .prssSetup) step) (tree : Tree) :
    ∀ count (s : RealState C net.State),
      IsQueryBoundP ((fixedTreeRuns K circuits settings runLimit j (wrongOutput D) D net tree count).run s)
        (Adds .prssSetup) (count * ((treeFuel circuits settings + 1) * step + treeSetups tree * setupClassCalls C))
  | 0, s => isQueryBoundP_pure _ _ _
  | count + 1, s => by
    unfold fixedTreeRuns
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rw [StateT.run_bind]
      exact (isQueryBoundP_bind (fixedTreeRun_adds K circuits settings runLimit j D net step hround tree s)
        fun r _ => fixedTreeRuns_adds j D net step hround tree count r.2).mono (by rw [Nat.succ_mul count]; omega)
    · exact isQueryBoundP_pure _ _ _

/-- The first `count` top runs of the prefix make at most `count` times the cost of one top run. -/
theorem topLoop_adds (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) (InClass .prssSetup) step) :
    ∀ count (s : RealState C net.State),
      IsQueryBoundP ((topLoop K circuits settings runLimit j D net count).run s)
        (Adds .prssSetup) (count * ((treeFuel circuits settings + 1) * step + setupClassCalls C))
  | 0, s => isQueryBoundP_pure _ _ _
  | count + 1, s => by
    unfold topLoop
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rw [StateT.run_bind]
      have h := fixedTreeRun_adds K circuits settings runLimit j D net step hround .top s
      simp only [treeSetups, one_mul] at h
      exact (isQueryBoundP_bind h fun r _ => topLoop_adds j D net step hround count r.2).mono
        (by rw [Nat.succ_mul count]; omega)
    · exact isQueryBoundP_pure _ _ _

/-- A local computation on `.hash` and `.prf` of the honest operators adds no cell of the class and
keeps the state. -/
theorem realLift_adds {σ α : Type} {oa : OracleComp (RoSpec C) α} (h : GameCount.OnlySign oa)
    (s : RealState C σ) :
    IsQueryBoundP ((realLift oa : RealM C σ α).run s) (Adds .prssSetup) 0 ∧
      ∀ r ∈ support ((realLift oa : RealM C σ α).run s), r.2 = s := by
  unfold realLift
  rw [StateT.run_lift]
  refine ⟨isQueryBoundP_bind (n := 0) (m := 0) (free_noAdds (by decide) h) fun _ _ => isQueryBoundP_pure _ _ _,
    fun r hr => ?_⟩
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, rfl⟩ := hr
  rfl

/-- The answer of an honest operator to a signing request adds no cell of the class and keeps the
state of the game. -/
theorem operatorAnswer_adds {σ : Type} (D : C.Coalition) (operators : C.Party → OperatorState C)
    (operator : OperatorState C) (e : KeyIndex) (q : TsigQuery C) (st : TsigState C) (s : RealState C σ) :
    IsQueryBoundP (((operatorAnswer (m := RealM C σ) realLift (gameValue D operators) operator e q).run st).run s)
      (Adds .prssSetup) 0 ∧
      ∀ r ∈ support (((operatorAnswer (m := RealM C σ) realLift (gameValue D operators) operator e q).run st).run s), r.2 = s := by
  have hX : NoCall (DigestBudgets.RoIn .prssSetup) ((operatorAnswer (fun oa => oa)
      (prfValue (gameSeeds D fun i => (operators i).keys)) operator e q).run st) := by
    unfold operatorAnswer
    split
    · rw [ownAnswer_run]
      exact DigestBudgets.noCall_tsigOracles (by decide) _ _ _ q _
    · exact SigningSelectionProof.noCall_pure _ _
  rw [operatorAnswer_eq_free, StateT.run_lift]
  refine ⟨isQueryBoundP_bind (n := 0) (m := 0) (DigestBudgets.free_liftComp_bound .prssSetup _ (fun _ => Iff.rfl) _ 0
    ((noCall_iff _ _).1 hX)) fun _ _ => isQueryBoundP_pure _ _ _, fun r hr => ?_⟩
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, rfl⟩ := hr
  rfl

theorem onlySign_sequenceFin {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp (RoSpec C) α), (∀ i, GameCount.OnlySign (f i)) →
      GameCount.OnlySign (OverPermutation.sequenceFin f) := by
  intro n
  induction n with
  | zero => intro f _; exact GameCount.onlySign_pure _
  | succ n ih =>
    intro f hf
    rw [OverPermutation.sequenceFin]
    exact GameCount.onlySign_bind (hf 0) fun _ => GameCount.onlySign_bind (ih _ fun i => hf i.succ) fun _ =>
      GameCount.onlySign_pure _

/-- The win test on the dealt keys of `prfValue seeds` with held bottom trees, as a computation of
`H` and `PRG`, calls `H` only on `.hash` and `.prf`. -/
theorem onlySign_forgeryWins (keys : C.Party → Keys C) (parameter : PublicParameter) (top : TopTree)
    (seeds : C.Term → HashOutput) (held : Fin (2 ^ layerHeight) → Option BottomTree) (st : TsigState C)
    (forgery : Forgery) :
    GameCount.OnlySign (forgeryWins (fun oa => oa)
      { dealtWith (fun oa => oa) parameter keys top (prfValue seeds) with bottom := fun b => pure (held b) }
      st forgery) := by
  unfold forgeryWins
  refine GameCount.onlySign_bind (GameCount.onlySign_tweakable _) fun verified => ?_
  dsimp only
  split_ifs
  · simp only [pure_bind]
    exact GameCount.onlySign_pure _
  refine GameCount.onlySign_bind ?_ fun _ => by simp only [pure_bind]; exact GameCount.onlySign_pure _
  unfold honestSignature
  refine GameCount.onlySign_bind (GameCount.onlySign_pure _) fun tree => ?_
  rcases tree with _ | tree
  · exact GameCount.onlySign_pure _
  refine GameCount.onlySign_bind (GameCount.onlySign_prfValue _ _) fun ρ => ?_
  refine GameCount.onlySign_bind (by unfold signCodeword; exact GameCount.onlySign_tweakable _) fun r => ?_
  rcases r with _ | ⟨randomness, encoding⟩
  · exact GameCount.onlySign_pure _
  refine GameCount.onlySign_bind (onlySign_sequenceFin _ fun l => ?_) fun _ =>
    GameCount.onlySign_bind (GameCount.onlySign_tweakable _) fun _ => GameCount.onlySign_pure _
  split
  · exact GameCount.onlySign_prfValue _ _
  · exact GameCount.onlySign_pure _
  · exact GameCount.onlySign_bind (GameCount.onlySign_prfValue _ _) fun _ => GameCount.onlySign_pure _

/-- The win test adds no cell of the class. -/
theorem forgeryWins_adds {σ : Type} (D : C.Coalition) (operators : C.Party → OperatorState C)
    (parameter : PublicParameter) (top : TopTree) (st : TsigState C) (forgery : Forgery) (s : RealState C σ) :
    IsQueryBoundP ((forgeryWins (m := RealM C σ) realLift (canonicalDealt D operators parameter top) st
      forgery).run s) (Adds .prssSetup) 0 := by
  rw [forgeryWins_eq_free, StateT.run_lift]
  exact isQueryBoundP_bind (n := 0) (m := 0) (free_noAdds (by decide) (onlySign_forgeryWins _ _ _ _ _ _ _))
    fun _ _ => isQueryBoundP_pure _ _ _

/-- The cost of one run of each tree in the signing phase. The signing phase runs no top tree. -/
def bottomCost (step : ℕ) : Tree → ℕ
  | .top => 0
  | .bottom _ => (treeFuel circuits settings + 1) * step + 2 * setupClassCalls C

/-- The rest of a request of bottom tree `b` after its run adds no cell of the class and keeps the
state. -/
theorem requestRest_adds {σ : Type} (D : C.Coalition) (b : Fin (2 ^ layerHeight)) (s : RealState C σ) :
    IsQueryBoundP ((match heldBottom D s.operators b with
        | some tree => do
          let v ← gameValue D s.operators (.randomizer topLayer (topKey b))
          pure (some (tree, v))
        | none => pure none : RealM C σ (Option (BottomTree × Digest))).run s) (Adds .prssSetup) 0 ∧
      ∀ r ∈ support ((match heldBottom D s.operators b with
        | some tree => do
          let v ← gameValue D s.operators (.randomizer topLayer (topKey b))
          pure (some (tree, v))
        | none => pure none : RealM C σ (Option (BottomTree × Digest))).run s), r.2 = s := by
  split
  · obtain ⟨hb, hs⟩ := realLift_adds (σ := σ) (GameCount.onlySign_prfValue
      (gameSeeds D fun i => (s.operators i).keys) (.randomizer topLayer (topKey b))) s
    unfold gameValue
    rw [StateT.run_bind]
    refine ⟨isQueryBoundP_bind (n := 0) (m := 0) hb fun _ _ => isQueryBoundP_pure _ _ _, fun r hr => ?_⟩
    simp only [mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    exact hs x hx
  · refine ⟨isQueryBoundP_pure _ _ _, fun r hr => ?_⟩
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]

/-- A request of bottom tree `b` from a state `s` makes at most `d` calls of `Adds` and takes `d` from
the budget of the runs that remain. -/
theorem fixedTreeRequest_step (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) (InClass .prssSetup) step) (b : Fin (2 ^ layerHeight))
    (s : RealState C net.State) :
    ∃ d, d ≤ FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step) s.runs ∧
      IsQueryBoundP ((fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D net b).run s)
        (Adds .prssSetup) d ∧
      ∀ r ∈ support ((fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D net b).run s),
        FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step) r.2.runs + d ≤
          FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step) s.runs := by
  unfold fixedTreeRequest
  rw [StateT.run_bind]
  by_cases hm : mayRun runLimit D s (.bottom b)
  · have hupdate := remaining_update runLimit (bottomCost (C := C) circuits settings step) s.runs (.bottom b)
      (mayRun_lt runLimit hm)
    refine ⟨bottomCost circuits settings step (.bottom b), by omega, ?_, ?_⟩
    · have hrun := fixedTreeRun_adds K circuits settings runLimit j D net step hround (.bottom b) s
      simp only [treeSetups] at hrun
      simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind, hm, ↓reduceIte]
      rw [bind_assoc]
      refine (isQueryBoundP_bind hrun (m := 0) fun r _ => ?_).mono (by simp [bottomCost])
      simp only [StateT.run_pure, pure_bind]
      exact (requestRest_adds D b r.2).1
    · intro r hr
      simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind, hm, ↓reduceIte, bind_assoc,
        StateT.run_pure, mem_support_bind_iff] at hr
      obtain ⟨x, hx, hy⟩ := hr
      rw [(requestRest_adds D b x.2).2 r hy, fixedTreeRun_runs K circuits settings runLimit j D net _ s x hx]
      omega
  · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind, hm, ↓reduceIte, StateT.run_pure]
      exact (requestRest_adds D b s).1
    · intro r hr
      simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind, hm, ↓reduceIte, StateT.run_pure]
        at hr
      rw [(requestRest_adds D b s).2 r hr]
      omega

theorem run_lift_tsig {σ α : Type} (x : RealM C σ α) (st : TsigState C) (s : RealState C σ) :
    ((StateT.lift x : StateT (TsigState C) (RealM C σ) α).run st).run s =
      (fun p => ((p.1, st), p.2)) <$> x.run s := by
  simp [StateT.run_lift, map_eq_bind_pure_comp]

/-- A program of the game, lifted to the signing state, as a step of `simulateQ_pot`. -/
theorem lift_step {σ α : Type} (Φ : (Tree → ℕ) → ℕ) (e : ℕ) (x : RealM C σ α) (st : TsigState C)
    (s : RealState C σ) (d : ℕ) (hd : d ≤ Φ s.runs + e) (hb : IsQueryBoundP (x.run s) (Adds .prssSetup) d)
    (hs : ∀ r ∈ support (x.run s), Φ r.2.runs + d ≤ Φ s.runs + e) :
    ∃ d, d ≤ Φ s.runs + e ∧
      IsQueryBoundP (((StateT.lift x : StateT (TsigState C) (RealM C σ) α).run st).run s) (Adds .prssSetup) d ∧
      ∀ r ∈ support (((StateT.lift x : StateT (TsigState C) (RealM C σ) α).run st).run s), Φ r.2.runs + d ≤ Φ s.runs + e := by
  refine ⟨d, hd, ?_, fun r hr => ?_⟩
  · rw [run_lift_tsig]
    exact (isQueryBoundP_map_iff _ _ _).2 hb
  · rw [run_lift_tsig, support_map] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    exact hs p hp

/-- A signing request adds no cell of the class and keeps the runs. -/
theorem signRequest_quiet {σ : Type} (D : C.Coalition) (i : C.Party) (e : KeyIndex) (q : TsigQuery C)
    (st : TsigState C) (s : RealState C σ) :
    IsQueryBoundP (((signRequest D i e q).run st).run s) (Adds .prssSetup) 0 ∧
      ∀ r ∈ support (((signRequest D i e q).run st).run s), r.2.runs = s.runs := by
  unfold signRequest
  simp only [StateT.run_bind, run_lift_tsig, StateT.run_modify, StateT.run_get, map_pure, pure_bind]
  obtain ⟨hb, hs⟩ := operatorAnswer_adds D _ _ e q st
    { s with closed := Function.update s.closed (treeOf e) true }
  refine ⟨hb, fun r hr => ?_⟩
  rw [hs r hr]

/-- A call of `forge` to the local oracles costs one call of `Adds` when it is in the class. -/
theorem forger_step {σ : Type} (Φ : (Tree → ℕ) → ℕ) (t : (LocalSpec C).Domain) (st : TsigState C)
    (s : RealState C σ) :
    ∃ d, d ≤ Φ s.runs + (if InClass .prssSetup t then 1 else 0) ∧
      IsQueryBoundP (((StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))) :
        StateT (TsigState C) (RealM C σ) _).run st).run s) (Adds .prssSetup) d ∧
      ∀ r ∈ support (((StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))) :
        StateT (TsigState C) (RealM C σ) _).run st).run s),
        Φ r.2.runs + d ≤ Φ s.runs + (if InClass .prssSetup t then 1 else 0) := by
  have hq : IsQueryBoundP (OracleComp.lift (OracleSpec.query t) : OracleComp (LocalSpec C) _) (InClass .prssSetup)
      (if InClass .prssSetup t then 1 else 0) := by
    refine (isQueryBoundP_query_iff _ _ _).2 fun h => ?_
    simp only [h, ↓reduceIte, Nat.one_pos]
  refine lift_step _ _ _ st s (if InClass .prssSetup t then 1 else 0) (by omega) ?_ fun r hr => ?_
  · rw [StateT.run_lift]
    exact isQueryBoundP_bind (m := 0) (adversary_adds _ _ hq) fun _ _ => isQueryBoundP_pure _ _ _
  · rw [StateT.run_lift] at hr
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨_, _, rfl⟩ := hr
    dsimp only
    omega

/-- A read of the state cell of `forge` adds no cell of the class and keeps the state. -/
theorem cellRead_step {σ : Type} (Φ : (Tree → ℕ) → ℕ) (st : TsigState C) (s : RealState C σ) :
    ∃ d, d ≤ Φ s.runs + 0 ∧
      IsQueryBoundP (((StateT.lift ((·.adversary) <$> (get : RealM C σ _)) :
        StateT (TsigState C) (RealM C σ) σ).run st).run s) (Adds .prssSetup) d ∧
      ∀ r ∈ support (((StateT.lift ((·.adversary) <$> (get : RealM C σ _)) :
        StateT (TsigState C) (RealM C σ) σ).run st).run s), Φ r.2.runs + d ≤ Φ s.runs + 0 := by
  refine lift_step Φ _ _ st s 0 (Nat.zero_le _) ?_ fun r hr => ?_
  · change IsQueryBoundP (pure (s.adversary, s) : OracleComp (WorldSpec C) _) (Adds .prssSetup) 0
    exact isQueryBoundP_pure _ _ _
  · change r ∈ support (pure (s.adversary, s) : OracleComp (WorldSpec C) _) at hr
    obtain rfl : r = (s.adversary, s) := hr
    exact le_rfl

/-- A write of the state cell of `forge` adds no cell of the class and keeps the runs. -/
theorem cellWrite_step {σ : Type} (Φ : (Tree → ℕ) → ℕ) (state : σ) (st : TsigState C) (s : RealState C σ) :
    ∃ d, d ≤ Φ s.runs + 0 ∧
      IsQueryBoundP (((StateT.lift (modify fun s : RealState C σ => { s with adversary := state }) :
        StateT (TsigState C) (RealM C σ) PUnit).run st).run s) (Adds .prssSetup) d ∧
      ∀ r ∈ support (((StateT.lift (modify fun s : RealState C σ => { s with adversary := state }) :
        StateT (TsigState C) (RealM C σ) PUnit).run st).run s), Φ r.2.runs + d ≤ Φ s.runs + 0 := by
  refine lift_step Φ _ _ st s 0 (Nat.zero_le _) ?_ fun r hr => ?_
  · change IsQueryBoundP (pure (PUnit.unit, { s with adversary := state }) : OracleComp (WorldSpec C) _)
      (Adds .prssSetup) 0
    exact isQueryBoundP_pure _ _ _
  · change r ∈ support (pure (PUnit.unit, { s with adversary := state }) : OracleComp (WorldSpec C) _) at hr
    obtain rfl : r = (PUnit.unit, { s with adversary := state }) := hr
    exact le_rfl

/-- A call of `forge` to the signing oracles of hybrid `j` from a state `s` makes at most `d` calls of
`Adds` and takes `d` from the budget of the runs that remain. -/
theorem fixedOracles_step (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (step : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step) (q : TsigQuery C)
    (st : TsigState C) (s : RealState C A.net.State) :
    ∃ d, d ≤ FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step) s.runs + 0 ∧
      IsQueryBoundP (((fixedOracles K circuits settings runLimit j (wrongOutput D) D A q).run st).run s)
        (Adds .prssSetup) d ∧
      ∀ r ∈ support (((fixedOracles K circuits settings runLimit j (wrongOutput D) D A q).run st).run s),
        FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step) r.2.runs + d ≤
          FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step) s.runs + 0 := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · refine ⟨0, Nat.zero_le _, isQueryBoundP_pure _ _ _, fun r hr => ?_⟩
    simp only [fixedOracles, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
  · obtain ⟨d, hd, hb, hs⟩ := fixedTreeRequest_step K circuits settings runLimit j D A.net step hround b s
    have e : fixedOracles K circuits settings runLimit j (wrongOutput D) D A (.tree b) =
        StateT.lift (fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D A.net b) := rfl
    rw [e]
    refine lift_step (FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step)) 0
      (fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D A.net b) st s d (le_trans hd (Nat.le_add_right _ 0)) hb
      fun r hr => le_trans (hs r hr) (Nat.le_add_right _ 0)
  · obtain ⟨hb, hs⟩ := signRequest_quiet D i e (.round1 i J e message) st s
    have eq : fixedOracles K circuits settings runLimit j (wrongOutput D) D A (.round1 i J e message) =
        signRequest D i e (.round1 i J e message) := rfl
    rw [eq]
    exact ⟨0, Nat.zero_le _, hb, fun r hr => by simp only [hs r hr]; omega⟩
  · obtain ⟨hb, hs⟩ := signRequest_quiet D i e (.round2 i J e message parts) st s
    have eq : fixedOracles K circuits settings runLimit j (wrongOutput D) D A (.round2 i J e message parts) =
        signRequest D i e (.round2 i J e message parts) := rfl
    rw [eq]
    exact ⟨0, Nat.zero_le _, hb, fun r hr => by simp only [hs r hr]; omega⟩

/-- The signing phase in hybrid `j` from a state `s` makes at most `forge` calls of `Adds` for the
calls of `forge` and the budget of the runs of the bottom trees that remain. -/
theorem fixedSigning_adds (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (step forge : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step)
    (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge)
    (s : RealState C A.net.State) :
    IsQueryBoundP ((fixedSigning K circuits settings runLimit j (wrongOutput D) D A).run s) (Adds .prssSetup)
      (forge + FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step) s.runs) := by
  unfold fixedSigning
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rw [StateT.run_bind]
    refine (isQueryBoundP_bind (m := 0) ((simulateQ_pot _ (ForgeInClass .prssSetup) (Adds .prssSetup)
      (fun s : RealState C A.net.State => FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step)
        s.runs) 1 ?_ _ forge (hforge _ _) _ s)) fun p _ => ?_).mono (by omega)
    · intro t st s'
      rcases t with t | q | q
      · simp only [QueryImpl.add_apply_inl, ForgeInClass]
        exact forger_step (FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step)) t st s'
      · simp only [QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, ForgeInClass, ↓reduceIte]
        exact fixedOracles_step K circuits settings runLimit j D A step hround q st s'
      · simp only [QueryImpl.add_apply_inr, ForgeInClass, ↓reduceIte]
        rcases q with _ | state
        · exact cellRead_step (FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step)) st s'
        · exact cellWrite_step (FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step))
            state st s'
    · simp only [StateT.run_bind, StateT.run_get, pure_bind]
      exact forgeryWins_adds D _ _ _ _ _ _
  · exact isQueryBoundP_pure _ _ _

/-- The budget of the runs of the bottom trees that remain is at most `runLimit` runs of each bottom
tree. -/
theorem remaining_bottom_le (step : ℕ) (runs : Tree → ℕ) :
    FirstCounts.remaining runLimit (bottomCost (C := C) circuits settings step) runs ≤
      runLimit * 2 ^ layerHeight * ((treeFuel circuits settings + 1) * step + 2 * setupClassCalls C) := by
  unfold FirstCounts.remaining
  simp only [bottomCost, Nat.mul_zero, Nat.zero_add]
  calc ∑ b : Fin (2 ^ layerHeight), (runLimit - runs (.bottom b)) *
        ((treeFuel circuits settings + 1) * step + 2 * setupClassCalls C)
      ≤ ∑ _b : Fin (2 ^ layerHeight), runLimit * ((treeFuel circuits settings + 1) * step + 2 * setupClassCalls C) :=
        Finset.sum_le_sum fun b _ => Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = runLimit * 2 ^ layerHeight * ((treeFuel circuits settings + 1) * step + 2 * setupClassCalls C) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        ring

/-- The game after top run `j` makes at most the cost of the later top runs, the calls of `forge` and
`runLimit` runs of each bottom tree. -/
theorem topRest_adds (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (step forge : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step)
    (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge)
    (s : RealState C A.net.State) :
    IsQueryBoundP (topRest K circuits settings runLimit j D A s) (Adds .prssSetup)
      ((runLimit - (j + 1)) * ((treeFuel circuits settings + 1) * step + setupClassCalls C) +
        (forge + runLimit * 2 ^ layerHeight * ((treeFuel circuits settings + 1) * step + 2 * setupClassCalls C))) := by
  unfold topRest
  rw [isQueryBoundP_map_iff, StateT.run_bind]
  have hruns := fixedTreeRuns_adds K circuits settings runLimit (j + 1) D A.net step hround .top
    (runLimit - (j + 1)) s
  simp only [treeSetups, one_mul] at hruns
  exact isQueryBoundP_bind hruns fun p _ =>
    (fixedSigning_adds K circuits settings runLimit (j + 1) D A step forge hround hforge p.2).mono
      (Nat.add_le_add_left (remaining_bottom_le circuits settings runLimit step _) _)

/-- The rest of a live top run `j` after its setup, with its vote, and the game after it. -/
theorem topLiveRest_adds (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (step forge : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step)
    (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge)
    (s : RealState C A.net.State) (r : A.net.State × (C.Party → Option (Keys C))) :
    IsQueryBoundP (topLiveRest K circuits settings runLimit j D A s r) (Adds .prssSetup)
      ((treeFuel circuits settings - setupRounds) * step + C.n * 0 + step +
        ((runLimit - (j + 1)) * ((treeFuel circuits settings + 1) * step + setupClassCalls C) +
          (forge + runLimit * 2 ^ layerHeight * ((treeFuel circuits settings + 1) * step + 2 * setupClassCalls C)))) := by
  unfold topLiveRest
  refine (isQueryBoundP_bind (phase_adds D A.net step hround _ _ _ 0 fun i => ?_) fun p _ => ?_).mono
    (Nat.add_assoc _ _ _).ge
  · split
    · exact topAfterSetup_classBound K circuits settings _ _ _
    · exact isQueryBoundP_pure _ _ _
  · obtain ⟨state, outputs⟩ := p
    rw [← GameCount.bound_iff]
    refine GameCount.bound_mono (GameCount.bound_bind (n := 0)
      (wrongOutput_adds D (fun i => (s.operators i).keys) .top outputs) fun b => ?_) (Nat.zero_add _).le
    rw [GameCount.bound_iff]
    exact isQueryBoundP_bind (FirstCounts.voteRound_adds .prssSetup (by decide) D A.net step hround _ _
      fun j q hq => by
        obtain ⟨o, -, rfl⟩ := Option.map_eq_some_iff.1 hq
        exact FirstCounts.queryClass_treeVote .top o) fun _ _ =>
      topRest_adds K circuits settings runLimit j D A step forge hround hforge _

/-- The rest of the game at a dead or an absent top slot `j`. -/
theorem topSkipRest_adds (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (step forge : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step)
    (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge)
    (s : RealState C A.net.State) (runJ : Bool) :
    IsQueryBoundP (topSkipRest K circuits settings runLimit j D A s runJ) (Adds .prssSetup)
      (((treeFuel circuits settings + 1) * step + setupClassCalls C) +
        ((runLimit - (j + 1)) * ((treeFuel circuits settings + 1) * step + setupClassCalls C) +
          (forge + runLimit * 2 ^ layerHeight * ((treeFuel circuits settings + 1) * step + 2 * setupClassCalls C)))) := by
  unfold topSkipRest
  split
  · have hrun := fixedTreeRun_adds K circuits settings runLimit (j + 1) D A.net step hround .top s
    simp only [treeSetups, one_mul] at hrun
    exact isQueryBoundP_bind hrun fun p _ => topRest_adds K circuits settings runLimit j D A step forge hround hforge _
  · rw [isQueryBoundP_map_iff]
    exact (fixedSigning_adds K circuits settings runLimit (j + 1) D A step forge hround hforge s).mono
      ((Nat.add_le_add_left (remaining_bottom_le (C := C) circuits settings runLimit step s.runs) forge).trans
        (by omega))

/-- The prefix of hybrid `j` up to top slot `j`. -/
theorem topPrefix_adds (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (start step : ℕ)
    (hstart : ∀ x z, IsQueryBoundP (A.net.start x z) (InClass .prssSetup) start)
    (hround : ∀ st sent, IsQueryBoundP (A.net.round st sent) (InClass .prssSetup) step) :
    IsQueryBoundP (topPrefix K circuits settings runLimit j D A) (Adds .prssSetup)
      ((start + setupRounds * step + 0) + (step + (j * ((treeFuel circuits settings + 1) * step + setupClassCalls C) + 0))) := by
  unfold topPrefix
  refine isQueryBoundP_bind ((GameCount.bound_iff _ _ _).1
    (seedBlock_bound .prssSetup D A.net start step 0 hstart hround (seedHonest (by decide)))) fun p _ => ?_
  obtain ⟨state, keys⟩ := p
  refine isQueryBoundP_bind (FirstCounts.voteRound_adds .prssSetup (by decide) D A.net step hround _ _
    fun j q hq => by
      obtain ⟨o, -, rfl⟩ := Option.map_eq_some_iff.1 hq
      rfl) fun v _ => ?_
  obtain ⟨state, ok⟩ := v
  refine isQueryBoundP_bind (topLoop_adds K circuits settings runLimit j D A.net step hround j _) fun q _ => ?_
  obtain ⟨ran, s⟩ := q
  dsimp only
  split_ifs <;> exact isQueryBoundP_pure _ _ _

end Game

/-! ## The leaf -/

section Leaf

open FirstCounts

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (prims : Primitives)

/-- The arithmetic of the distinguisher at a live and at a skipped slot. -/
theorem topDistinguisher_arith (j a h F step forge X : ℕ) (hj : j < runLimit) (ha : a ≤ F * step + h) :
    a + ((runLimit - (j + 1)) * (F * step + h) + (forge + X)) ≤ (runLimit - j) * (F * step + h) + forge + X := by
  obtain ⟨m, rfl⟩ : ∃ m, runLimit = j + 1 + m := ⟨runLimit - (j + 1), by omega⟩
  have e1 : j + 1 + m - (j + 1) = m := by omega
  have e2 : j + 1 + m - j = m + 1 := by omega
  rw [e1, e2]
  nlinarith

/-- `TopSlotPartCosts`. The start, each round and the distinguisher of the reduction of a top slot
stay within their budgets in the class `prssSetup`. -/
theorem topSlotPartCosts : TopSlotPartCosts K circuits settings runLimit prims := by
  intro D A start step forge hs hr hf j hj
  refine ⟨fun x z => ?_, fun st sent => ?_, fun r => ?_⟩
  · simp only [topReduction]
    rw [isQueryBoundP_map_iff]
    refine slotHandler_bound prims D _ _ ((topPrefix_adds K circuits settings runLimit j D A start step hs hr).mono
      (le_of_eq ?_)) _
    simp only [setupRounds]
    ring
  · rcases st with ⟨priv, place⟩
    cases place with
    | live s =>
      simp only [topReduction]
      rw [isQueryBoundP_map_iff]
      exact slotHandler_bound prims D _ _ (adversary_adds _ _ (hr _ _)) _
    | skip s runJ => exact isQueryBoundP_pure _ _ _
  · rcases r with ⟨⟨priv, place⟩, out⟩
    unfold topDistinguisher
    rw [isQueryBoundP_map_iff]
    refine slotHandler_bound prims D _ _ ?_ _
    cases place with
    | live s =>
      exact (topLiveRest_adds K circuits settings runLimit j D A step forge hr hf s _).mono
        (topDistinguisher_arith runLimit j _ (setupClassCalls C) (treeFuel circuits settings + 1) step forge _ hj (by
          rw [Nat.mul_zero, Nat.add_zero, Nat.add_one_mul]
          exact Nat.le_add_right_of_le (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _)))
    | skip s runJ =>
      exact (topSkipRest_adds K circuits settings runLimit j D A step forge hr hf s runJ).mono
        (topDistinguisher_arith runLimit j _ _ _ _ _ _ hj le_rfl)

end Leaf

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.topSlotPartCosts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.topSlotPartCosts
