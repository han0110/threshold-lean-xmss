import ThresholdLeanXmssSecurity.Proof.LifetimeKeygenHopProof
import ThresholdLeanXmssSecurity.Proof.LifetimeEmulatedBudget

/-!
# Lifetime keygen program facts

The emulation monad is the image, under `simulateQ (impl3 D)`, of an oracle
computation with three copies of the local interface: the observed adversary,
the emulated honest operator and the free honest operator. The scheduler
transport `hom_lifetimeGameWith` and its step lemmas (`LifetimeEmulatedBudget`)
carry the lifetime along this map and along log erasure.

* `tailProgramFree`: the post-keygen tail makes no programming query, for every
  keygen output. A three-copy computation never programs, because its three
  interfaces only reach the counted and free copies (`simulate3_quiet`).
* `chronologicalRoles`: the chronological endpoint is the all-emulated
  lifetime. For `lifetimeRuns attempts > 0` the run roles agree below the run
  budget (`lifetimeGame_roles_congr` on the three-copy computation). For
  `attempts = 0` the endpoint is the literal `lifetimeGame`: no ceremony
  starts, and erasing the call log and the stream table of the all-emulated
  lifetime gives it.

The pinned and current leanVM sources have no threshold scheduler or emulation
monad; `hom_tailWith` repeats the tail part of `hom_lifetimeGameWith`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace ThresholdLeanXmssSecurity.LifetimeKeygenPrograms

open LifetimeHybridOrder LifetimeJointLink LifetimeKeygenHopProof LifetimeEmulatedBudget

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-! ## Programming-free computations -/

section Quiet

theorem qb0_simulateQ {ι κ α : Type} {spec : OracleSpec ι} {spec' : OracleSpec κ}
    {p : κ → Prop} [DecidablePred p] (impl : QueryImpl spec (OracleComp spec'))
    (h : ∀ t, IsQueryBoundP (impl t) p 0) (oa : OracleComp spec α) :
    IsQueryBoundP (simulateQ impl oa) p 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    simpa using isQueryBoundP_bind (m := 0) (h t) fun a _ => ih a

theorem qb0_bind' {ι α β : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p]
    {oa : OracleComp spec α} {f : α → OracleComp spec β} (h : IsQueryBoundP oa p 0)
    (hf : ∀ a, IsQueryBoundP (f a) p 0) : IsQueryBoundP (oa >>= f) p 0 := by
  simpa using isQueryBoundP_bind (m := 0) h fun a _ => hf a

theorem free_quiet {α : Type} (oa : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (free oa) Programming 0 := by
  apply qb0_simulateQ
  intro t
  apply (isQueryBoundP_query_iff _ _ _).2
  intro h
  exact absurd h (by simp [Programming])

theorem counted_quiet {α : Type} (oa : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (worldRoles.adversary oa) Programming 0 := by
  change IsQueryBoundP (counted (liftComp oa _)) Programming 0
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [liftComp_bind, counted_bind]
    have e : counted (liftComp (liftM ((LocalSpec C).query t) : OracleComp (LocalSpec C) _)
        (SimulatorSpec C)) =
        (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _) := by
      rcases t with t | (q | x) <;> rfl
    rw [e]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [Programming]), fun u => by simpa [Programming] using ih u⟩

/-- No programming query, from every stream table. -/
def Quiet {α : Type} (x : EmulationM C α) : Prop :=
  ∀ cache, IsQueryBoundP ((x.run cache).run) Programming 0

theorem quiet_pure {α : Type} (a : α) : Quiet (pure a : EmulationM C α) := fun _ =>
  isQueryBoundP_pure _ _ _

theorem quiet_bind {α β : Type} {x : EmulationM C α} {f : α → EmulationM C β}
    (hx : Quiet x) (hf : ∀ a, Quiet (f a)) : Quiet (x >>= f) := by
  intro cache
  simp only [StateT.run_bind, WriterT.run_bind']
  exact qb0_bind' (hx cache) fun r => (isQueryBoundP_map_iff _ _ _).2 (hf r.1.1 r.1.2)

theorem quiet_simulate {ι α : Type} {spec : OracleSpec ι} (impl : QueryImpl spec (EmulationM C))
    (h : ∀ t, Quiet (impl t)) (oa : OracleComp spec α) : Quiet (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact quiet_pure a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact quiet_bind (h t) ih

theorem quiet_lift {α : Type} {y : OracleComp (WorldSpec C) α}
    (hy : IsQueryBoundP y Programming 0) : Quiet (StateT.lift (liftM y) : EmulationM C α) := by
  intro cache
  simp only [StateT.run_lift, WriterT.run_bind', WriterT.run_monadLift', liftM]
  exact qb0_bind' ((isQueryBoundP_map_iff _ _ _).2 hy) fun _ => isQueryBoundP_map_iff _ _ _ |>.2 (isQueryBoundP_pure _ _ _)

theorem observe_quiet {α : Type} (p : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (observe p) Programming 0 := by
  unfold observe
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind']
    refine qb0_bind' ?_ fun r => (isQueryBoundP_map_iff _ _ _).2 (ih r.1)
    rcases t with u | q | x
    · simp only [WriterT.run_monadLift', liftM]
      exact (isQueryBoundP_map_iff _ _ _).2 (counted_quiet _)
    · simp only [WriterT.run_bind', WriterT.run_monadLift', liftM]
      refine qb0_bind' ((isQueryBoundP_map_iff _ _ _).2 (counted_quiet _)) fun r => ?_
      rw [isQueryBoundP_map_iff]
      exact qb0_bind' (isQueryBoundP_pure _ _ _) fun _ => (isQueryBoundP_map_iff _ _ _).2
        (isQueryBoundP_pure _ _ _)
    · simp only [WriterT.run_monadLift', liftM]
      exact (isQueryBoundP_map_iff _ _ _).2 (counted_quiet _)

theorem adversary_quiet (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α) :
    Quiet ((emulatedRoles D).adversary p) := by
  intro cache
  simp only [emulatedRoles, StateT.run_lift, WriterT.run_bind']
  exact qb0_bind' (observe_quiet p) fun _ => (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_pure _ _ _)

theorem honest_quiet (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α) :
    Quiet ((emulatedRoles D).honest p) := by
  apply quiet_simulate
  intro t
  rcases t with u | q | x
  · exact quiet_lift (free_quiet _)
  · exact quiet_lift (free_quiet _)
  · dsimp only
    split
    · intro cache
      simp only [StateT.run_mk, WriterT.run_monadLift', liftM]
      exact (isQueryBoundP_map_iff _ _ _).2 (free_quiet _)
    · exact quiet_lift (free_quiet _)

theorem base_honest_quiet (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α) :
    Quiet ((lifetimeHybridRoles D 0 0).honest p) := by
  simpa [lifetimeHybridRoles] using quiet_lift (C := C) (free_quiet p)

end Quiet

/-! ## The emulation monad as a three-copy oracle computation -/

section Copies

variable (D : C.Coalition)

/-- Observed adversary, emulated honest operator and free honest operator. -/
abbrev Spec3 (C : Committee) := (LocalSpec C + LocalSpec C) + LocalSpec C

/-- The three local interfaces of the emulation. -/
def impl3 : QueryImpl (Spec3 C) (EmulationM C) :=
  ((fun t => (emulatedRoles D).adversary (OracleComp.lift (OracleSpec.query t))) +
    (fun t => (emulatedRoles D).honest (OracleComp.lift (OracleSpec.query t)))) +
  (fun t => (lifetimeHybridRoles D 0 0).honest (OracleComp.lift (OracleSpec.query t)))

theorem impl3_quiet (t : (Spec3 C).Domain) : Quiet (impl3 D t) := by
  rcases t with (t | t) | t
  · exact adversary_quiet D _
  · exact honest_quiet D _
  · exact base_honest_quiet D _

theorem simulate3_quiet {α : Type} (x : OracleComp (Spec3 C) α) :
    Quiet (simulateQ (impl3 D) x) :=
  quiet_simulate _ (impl3_quiet D) x

theorem adversary_bind {α β : Type} (x : OracleComp (LocalSpec C) α)
    (f : α → OracleComp (LocalSpec C) β) :
    (emulatedRoles D).adversary (x >>= f) =
      (emulatedRoles D).adversary x >>= fun a => (emulatedRoles D).adversary (f a) := by
  apply StateT.ext
  intro cache
  simp only [emulatedRoles, StateT.run_lift, StateT.run_bind, observe, simulateQ_bind]
  simp only [WriterT.mk, WriterT.run, bind_assoc, pure_bind]

theorem writer_ext {ω : Type} {M : Type → Type} {α : Type} {x y : WriterT ω M α}
    (h : x.run = y.run) : x = y := h

/-- A pure- and bind-preserving map is the simulation of its query images. -/
theorem map_eq_simulate {M : Type → Type} [Monad M] [LawfulMonad M]
    (F : ∀ {α : Type}, OracleComp (LocalSpec C) α → M α)
    (hpure : ∀ {α : Type} (a : α), F (pure a) = pure a)
    (hbind : ∀ {α β : Type} (x : OracleComp (LocalSpec C) α) (f : α → OracleComp (LocalSpec C) β),
      F (x >>= f) = F x >>= fun a => F (f a))
    {α : Type} (p : OracleComp (LocalSpec C) α) :
    F p = simulateQ (fun t => F (OracleComp.lift (OracleSpec.query t))) p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [hpure]
  | query_bind t k ih =>
    rw [hbind, simulateQ_bind, simulateQ_spec_query]
    exact bind_congr fun u => ih u

theorem adversary_eq {α : Type} (p : OracleComp (LocalSpec C) α) :
    (emulatedRoles D).adversary p =
      simulateQ (fun t => (emulatedRoles D).adversary (OracleComp.lift (OracleSpec.query t))) p :=
  map_eq_simulate (fun p => (emulatedRoles D).adversary p) (fun a => by
    apply StateT.ext; intro cache; rfl) (adversary_bind D) p

theorem baseHonest_eq {α : Type} (p : OracleComp (LocalSpec C) α) :
    (lifetimeHybridRoles D 0 0).honest p =
      simulateQ (fun t => (lifetimeHybridRoles D 0 0).honest
        (OracleComp.lift (OracleSpec.query t))) p := by
  apply map_eq_simulate (fun p => (lifetimeHybridRoles D 0 0).honest p)
  · intro α a
    apply StateT.ext
    intro cache
    have hf : free (pure a : OracleComp (LocalSpec C) α) = pure a := rfl
    simp only [lifetimeHybridRoles, hf, StateT.run_lift, StateT.run_pure, liftM, Nat.lt_irrefl,
      if_false, if_true]
    apply writer_ext
    simp
  · intro α β x f
    apply StateT.ext
    intro cache
    simp only [lifetimeHybridRoles, free_bind, StateT.run_lift, StateT.run_bind, liftM,
      Nat.lt_irrefl, if_false, if_true, bind_assoc, pure_bind]
    apply writer_ext
    simp

theorem honest_eq {α : Type} (p : OracleComp (LocalSpec C) α) :
    (emulatedRoles D).honest p =
      simulateQ (fun t => (emulatedRoles D).honest (OracleComp.lift (OracleSpec.query t))) p := by
  apply map_eq_simulate (fun p => (emulatedRoles D).honest p)
  · intro α a
    simp [emulatedRoles]
  · intro α β x f
    simp [emulatedRoles, simulateQ_bind]

/-- The adversary copy. -/
def advCopy {α : Type} (p : OracleComp (LocalSpec C) α) : OracleComp (Spec3 C) α :=
  simulateQ (fun t => OracleComp.lift (OracleSpec.query (spec := Spec3 C) (.inl (.inl t)))) p

/-- The emulated honest copy. -/
def emulCopy {α : Type} (p : OracleComp (LocalSpec C) α) : OracleComp (Spec3 C) α :=
  simulateQ (fun t => OracleComp.lift (OracleSpec.query (spec := Spec3 C) (.inl (.inr t)))) p

/-- The free honest copy. -/
def freeCopy {α : Type} (p : OracleComp (LocalSpec C) α) : OracleComp (Spec3 C) α :=
  simulateQ (fun t => OracleComp.lift (OracleSpec.query (spec := Spec3 C) (.inr t))) p

theorem impl3_advCopy {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (impl3 D) (advCopy p) = (emulatedRoles D).adversary p := by
  rw [adversary_eq, advCopy, LifetimeEmulatedBudget.simulateQ_comp]
  congr 1
  funext t
  exact simulateQ_spec_query _ _

theorem impl3_emulCopy {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (impl3 D) (emulCopy p) = (emulatedRoles D).honest p := by
  rw [honest_eq, emulCopy, LifetimeEmulatedBudget.simulateQ_comp]
  congr 1
  funext t
  exact simulateQ_spec_query _ _

theorem impl3_freeCopy {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (impl3 D) (freeCopy p) = (lifetimeHybridRoles D 0 0).honest p := by
  rw [baseHonest_eq, freeCopy, LifetimeEmulatedBudget.simulateQ_comp]
  congr 1

/-- The emulation is the simulation of a three-copy computation. -/
def H3 : OracleComp (Spec3 C) →ᵐ EmulationM C where
  toFun _ x := simulateQ (impl3 D) x
  toFun_pure' _ := simulateQ_pure _ _
  toFun_bind' _ _ := simulateQ_bind _ _ _

/-- The all-emulated run roles on the copies. -/
def emulRoles3 : Roles C (OracleComp (Spec3 C)) := ⟨advCopy, emulCopy⟩

/-- The keygen, signing and adversary roles of `lifetimeHybridRoles D 0 0` on the copies. -/
def baseRoles3 : Roles C (OracleComp (Spec3 C)) := ⟨advCopy, freeCopy⟩

end Copies

/-! ## The post-keygen tail -/

section Tail

variable (K : Constants C E) (settings : Settings) (attempts : ℕ) (circuits : Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The literal post-keygen scheduler tail of `lifetimeGameWith`, for any roles. -/
def tailWith {m : Type → Type} [Monad m] (Ro : ℕ → Roles C m) (base : Roles C m)
    (state : A.keygen.State) (outputs : C.Party → Option (Keys C)) : m Bool := do
  let some h := C.parties.find? (· ∉ D.1) | pure false
  if ¬ ∀ i, i ∉ D.1 → (outputs i).isSome then pure false else do
  let keys := fun i => (outputs i).getD default
  let lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β := fun oa => base.honest (liftComp oa _)
  let value := fun x => lift (prfValue (honestSeeds D keys) x)
  let forger : QueryImpl (LocalSpec C) (StateT (LifetimeState C E) m) :=
    fun t => StateT.lift (base.adversary (OracleComp.lift (OracleSpec.query t)))
  let (forgery, st) ← (simulateQ
    (forger + lifetimeOraclesWith K circuits settings attempts Ro base D keys value h)
      (A.run state (keys h).parameter)).run
    ⟨⟨D.1, fun _ => none, [], fun _ => none⟩, fun _ => none, fun _ _ => none,
      0, fun _ => 0, ∅, none⟩
  if ¬ ∀ i, i ∉ D.1 → (st.top i).isSome then pure false else do
  let some (_, top) := st.publicKey (keys h).parameter h | pure false
  forgeryWins lift (dealtWith lift (keys h).parameter keys top value) st.sign forgery

theorem afterKeygen_eq (state : A.keygen.State) (outputs : C.Party → Option (Keys C)) :
    afterKeygen K settings attempts D A circuits state outputs =
      tailWith K settings attempts circuits D A (fun _ => emulatedRoles D)
        (lifetimeHybridRoles D 0 0) state outputs := rfl

/-- The fixed three-copy tail maps onto the actual tail. This is one instance of
transporting the scheduler tail along `H3 D`, with `emulRoles3` and `baseRoles3`
mapped to `emulatedRoles D` and `lifetimeHybridRoles D 0 0` by `impl3_advCopy`,
`impl3_emulCopy` and `impl3_freeCopy`. -/
def TailTransport : Prop :=
  ∀ r : A.keygen.State × (C.Party → Option (Keys C)),
    simulateQ (impl3 D) (tailWith K settings attempts circuits D A (fun _ => emulRoles3)
      baseRoles3 r.1 r.2) = afterKeygen K settings attempts D A circuits r.1 r.2

theorem emulationGame_quiet {p : EmulationM C Bool} (hp : Quiet p) :
    IsQueryBoundP (emulationGame p) Programming 0 :=
  (isQueryBoundP_map_iff _ _ _).2 (hp ∅)

/-- `TailProgramFree` from the fixed tail transport. -/
theorem tailProgramFree_of_transport (htail : TailTransport K settings attempts circuits D A) :
    TailProgramFree K settings attempts D A circuits := by
  intro r
  rw [← htail r]
  exact emulationGame_quiet (simulate3_quiet D _)

theorem rolesHom_emul : RolesHom (H3 D) (emulRoles3 (C := C)) (emulatedRoles D) :=
  ⟨fun p => impl3_advCopy D p, fun p => impl3_emulCopy D p⟩

theorem rolesHom_base : RolesHom (H3 D) (baseRoles3 (C := C)) (lifetimeHybridRoles D 0 0) :=
  ⟨fun p => impl3_advCopy D p, fun p => impl3_freeCopy D p⟩

/-- The tail part of `hom_lifetimeGameWith`, from the exported scheduler step transports. -/
theorem hom_tailWith {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    (φ : m →ᵐ n) (Ro : ℕ → Roles C m) (base : Roles C m)
    (Ro' : ℕ → Roles C n) (base' : Roles C n)
    (hRo : ∀ r, RolesHom φ (Ro r) (Ro' r)) (hbase : RolesHom φ base base')
    (state : A.keygen.State) (outputs : C.Party → Option (Keys C)) :
    φ (tailWith K settings attempts circuits D A Ro base state outputs) =
      tailWith K settings attempts circuits D A Ro' base' state outputs := by
  have hlift : ∀ {β : Type} (oa : OracleComp (RoSpec C) β),
      φ (base.honest (liftComp oa _)) = base'.honest (liftComp oa _) := fun oa => hbase.honest _
  unfold tailWith
  split
  · rename_i h _
    split
    · exact MonadHom.mmap_pure φ _
    · refine (MonadHom.mmap_bind φ _ _).trans ?_
      let keys := fun i => (outputs i).getD default
      let impl' : QueryImpl (LocalSpec C + LifetimeSpec C E) (StateT (LifetimeState C E) n) :=
        (fun t => StateT.lift (base'.adversary (OracleComp.lift (OracleSpec.query t)))) +
          lifetimeOraclesWith K circuits settings attempts Ro' base' D keys
            (fun x => base'.honest (liftComp (prfValue (honestSeeds D keys) x) _)) h
      erw [hom_run_simulate φ _ impl' (fun t s => by
        rcases t with t | q
        · change φ ((StateT.lift (base.adversary _)).run s) = (StateT.lift (base'.adversary _)).run s
          simp only [StateT.run_lift, MonadHom.mmap_bind, MonadHom.mmap_pure, hbase.adversary]
        · exact hom_lifetimeOracles φ K circuits settings attempts Ro base Ro' base' hRo hbase D _ _ _
            (fun x => hbase.honest _) h q s)]
      refine bind_congr fun r => ?_
      rcases r with ⟨forgery, st⟩
      dsimp only
      split
      · exact MonadHom.mmap_pure φ _
      · split
        · refine (hom_forgeryWins φ _ _ _ _).trans ?_
          rw [hom_dealtWith φ _ _ hlift _ _ _ _ _ (fun x => hbase.honest _)]
          simp only [hlift]
        · exact MonadHom.mmap_pure φ _
  · exact MonadHom.mmap_pure φ _

theorem tailTransport : TailTransport K settings attempts circuits D A := by
  intro r
  exact hom_tailWith K settings attempts circuits D A (H3 D) _ _ _ _
    (fun _ => rolesHom_emul D) (rolesHom_base D) r.1 r.2

/-- The post-keygen tail makes no programming query, for every keygen output. -/
theorem tailProgramFree : TailProgramFree K settings attempts D A circuits :=
  tailProgramFree_of_transport K settings attempts circuits D A
    (tailTransport K settings attempts circuits D A)

end Tail

/-! ## Chronological roles -/

section Chronological

variable (K : Constants C E) (settings : Settings) (attempts : ℕ) (circuits : Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- `lifetimeHybridRoles D L` on the copies. -/
def hyb3 (L r : ℕ) : Roles C (OracleComp (Spec3 C)) :=
  if r < L then emulRoles3 else if r = L then baseRoles3 else ⟨advCopy, advCopy⟩

theorem rolesHom_hyb (L r : ℕ) : RolesHom (H3 D) (hyb3 L r) (lifetimeHybridRoles D L r) := by
  unfold hyb3 lifetimeHybridRoles
  split_ifs
  · exact rolesHom_emul D
  · refine ⟨fun p => impl3_advCopy D p, fun p => ?_⟩
    exact impl3_freeCopy D p
  · exact ⟨fun p => impl3_advCopy D p, fun p => impl3_advCopy D p⟩

theorem rolesHom_erase :
    RolesHom (LifetimeEmulatedBudget.eraseHom (C := C)) (lifetimeHybridRoles D 0 0) plainRoles :=
  ⟨fun p => erase_base_adversary D p, fun p => erase_base_honest D p⟩

theorem rolesHom_lift : RolesHom (LifetimeEmulatedBudget.liftHom (C := C)) worldRoles plainRoles :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- The chronological endpoint is the all-emulated lifetime. -/
theorem chronologicalRoles : ChronologicalRoles K settings attempts D A circuits := by
  unfold ChronologicalRoles
  have hall := (hom_lifetimeGameWith (H3 D) K circuits settings attempts _ _ _ _
    (fun _ => rolesHom_emul D) (rolesHom_base D) D A).symm
  rw [hall]
  by_cases hL : lifetimeRuns attempts = 0
  · rw [chronologicalGame, if_pos hL]
    rw [LifetimeProof.lifetimeGame_roles_congr K circuits settings attempts (fun _ => emulRoles3)
      (fun _ => baseRoles3) baseRoles3 D A (fun n hn => absurd hn (by omega))]
    rw [hom_lifetimeGameWith (H3 D) K circuits settings attempts _ _ _ _
      (fun _ => rolesHom_base D) (rolesHom_base D) D A]
    rw [emulationGame_erased]
    change _ = (LifetimeEmulatedBudget.eraseHom (lifetimeGameWith K circuits settings attempts
      (fun _ => lifetimeHybridRoles D 0 0) (lifetimeHybridRoles D 0 0) D A)).run' ∅
    rw [hom_lifetimeGameWith LifetimeEmulatedBudget.eraseHom K circuits settings attempts _ _ _ _
      (fun _ => rolesHom_erase D) (rolesHom_erase D) D A]
    rw [← hom_lifetimeGameWith LifetimeEmulatedBudget.liftHom K circuits settings attempts _ _ _ _
      (fun _ => rolesHom_lift) rolesHom_lift D A]
    change _ = (StateT.lift (lifetimeGame K circuits settings attempts D A)).run' ∅
    simp [StateT.run'_eq, StateT.run_lift]
  · rw [chronologicalGame, if_neg hL]
    congr 1
    rw [← hom_lifetimeGameWith (H3 D) K circuits settings attempts (hyb3 (lifetimeRuns attempts))
      baseRoles3 _ _ (fun r => rolesHom_hyb D _ r) _ D A]
    · rw [LifetimeProof.lifetimeGame_roles_congr K circuits settings attempts (hyb3 (lifetimeRuns attempts))
        (fun _ => emulRoles3) baseRoles3 D A (fun n hn => by simp [hyb3, hn])]
    · simpa [hyb3] using rolesHom_hyb D (lifetimeRuns attempts) (lifetimeRuns attempts)

end Chronological

end ThresholdLeanXmssSecurity.LifetimeKeygenPrograms

/--
info: 'ThresholdLeanXmssSecurity.LifetimeKeygenPrograms.tailProgramFree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeKeygenPrograms.tailProgramFree

/--
info: 'ThresholdLeanXmssSecurity.LifetimeKeygenPrograms.chronologicalRoles' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeKeygenPrograms.chronologicalRoles

/--
info: 'ThresholdLeanXmssSecurity.LifetimeKeygenPrograms.tailTransport' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeKeygenPrograms.tailTransport

/--
info: 'ThresholdLeanXmssSecurity.LifetimeKeygenPrograms.simulate3_quiet' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.LifetimeKeygenPrograms.simulate3_quiet
