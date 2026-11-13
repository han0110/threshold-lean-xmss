import ThresholdLeanXmssSecurity.Proof.LifetimeKeygenHopProof
import ThresholdLeanXmssSecurity.Proof.LifetimeLegacy

/-!
# The all-emulated lifetime budget

`hom_lifetimeGameWith` maps the whole lifetime scheduler `lifetimeGameWith` through a
monad map, given maps of the base roles and of the roles of every ceremony run. It
reuses `treeSim_hom_phase` for keygen and `SeedHitProof.hom_tsigOracles` for signing.

The budget transport runs one tagged lifetime in which the honest operators of the
ceremony runs use a third copy of the local oracles. Collapsing that copy into the free
copy gives the real `lifetimeGame`. Interpreting it by the emulated roles, with the log
erased, gives the all-emulated lifetime of `realTailBound_of_sourceBound`. Each tagged
query costs the emulation at most its real `LifetimeCounted` charge: a hidden stream is
answered from the private table or by a free-copy uniform draw. `HasLifetimeQueryBoundAll`
bounds every answer path, so it bounds the tagged lifetime and then the emulation.
No support restriction and no probability enters this transport.

`realTailBound_of_hasLifetimeQueryBound` combines this budget with the real half of
`KeygenCapQuiet` (`RealKeygenCapQuiet`), the only half that the argument of
`realTailBound_of_sourceBound` reads.

The pinned and current leanVM proof sources were searched for scheduler monad maps and
query-bound transport; `IsQueryBoundP.simulateQ_run_StateT_of_step` of VCVio is used.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace ThresholdLeanXmssSecurity.LifetimeEmulatedBudget

open LifetimeHybridOrder LifetimeJointLink LifetimeKeygenHopProof

attribute [local instance] Classical.propDecidable

/-! ## The whole lifetime scheduler under a monad map -/

section Hom

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : m →ᵐ n)

/-- A monad map transports the adversary and honest steps of `Ro` to those of `Ro'`. -/
structure RolesHom (Ro : Roles C m) (Ro' : Roles C n) : Prop where
  adversary : ∀ {α : Type} (p : OracleComp (LocalSpec C) α), φ (Ro.adversary p) = Ro'.adversary p
  honest : ∀ {α : Type} (p : OracleComp (LocalSpec C) α), φ (Ro.honest p) = Ro'.honest p

theorem hom_run_simulate {ι α σ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ m)) (impl' : QueryImpl spec (StateT σ n))
    (himpl : ∀ t s, φ ((impl t).run s) = (impl' t).run s) (p : OracleComp spec α) (s : σ) :
    φ ((simulateQ impl p).run s) = (simulateQ impl' p).run s := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, MonadHom.mmap_bind, himpl]
    exact bind_congr fun r => ih r.1 r.2

theorem hom_startSteps {I α : Type} (Ro : Roles C m) (Ro' : Roles C n) (hR : RolesHom φ Ro Ro')
    (D : C.Coalition) (program : C.Party → PartyM C E (CallSpec I PEmpty) α) :
    φ (startSteps Ro D program) = startSteps Ro' D program := by
  unfold startSteps
  rw [SeedHitProof.hom_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1 <;> simp [hi, hR.honest]

theorem hom_stepRound {I α : Type} (Ro : Roles C m) (Ro' : Roles C n) (hR : RolesHom φ Ro Ro')
    (D : C.Coalition) (A : Adversary C E I PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    φ (stepRound Ro D A noFunctionality state steps) =
      stepRound Ro' D A noFunctionality state steps := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real]), if_neg (by simp [callInput_real])]
  simp only [MonadHom.mmap_bind, MonadHom.mmap_pure, hR.adversary, SeedHitProof.hom_sequenceFin]
  apply bind_congr
  intro r
  congr 1
  congr 1
  funext j
  cases hs : steps j with
  | done out => exact MonadHom.mmap_pure _ _
  | wait outbox resume =>
    by_cases hj : j ∈ D.1
    · simp [hj]
    · simp [hj, hR.honest]
  | call input resume => exact input.elim


theorem hom_dealtWith (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β)
    (lift' : ∀ {β : Type}, OracleComp (RoSpec C) β → n β)
    (hlift : ∀ {β : Type} (oa : OracleComp (RoSpec C) β), φ (lift oa) = lift' oa)
    (P : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (value : Point → m Digest) (value' : Point → n Digest) (hvalue : ∀ x, φ (value x) = value' x) :
    SeedHitProof.Dealt.hmap φ (dealtWith lift P keys top value) =
      dealtWith lift' P keys top value' := by
  simp only [SeedHitProof.Dealt.hmap, dealtWith, SeedHitProof.hom_map,
    SeedHitProof.hom_referenceTree, hlift, hvalue]

theorem hom_signerDealt (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β)
    (lift' : ∀ {β : Type}, OracleComp (RoSpec C) β → n β)
    (hlift : ∀ {β : Type} (oa : OracleComp (RoSpec C) β), φ (lift oa) = lift' oa)
    (keys : C.Party → Keys C)
    (value : Point → m Digest) (value' : Point → n Digest) (hvalue : ∀ x, φ (value x) = value' x)
    (st : LifetimeState C E) (i : C.Party) :
    SeedHitProof.Dealt.hmap φ (ThresholdLeanXmss.signerDealt lift keys value st i) =
      ThresholdLeanXmss.signerDealt lift' keys value' st i := by
  simp only [SeedHitProof.Dealt.hmap, ThresholdLeanXmss.signerDealt, dealtWith, hlift, hvalue, MonadHom.mmap_pure]

theorem hom_honestSignature (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β)
    (dealt : Dealt C m) (e : KeyIndex) (message : Message) :
    φ (honestSignature lift dealt e message) =
      honestSignature (fun oa => φ (lift oa)) (SeedHitProof.Dealt.hmap φ dealt) e message := by
  unfold honestSignature
  rw [MonadHom.mmap_bind]
  congr 1; funext tree
  rcases tree with _ | tree
  · exact MonadHom.mmap_pure _ _
  simp only [MonadHom.mmap_bind]
  congr 1; funext ρ
  congr 1; funext r
  rcases r with _ | ⟨randomness, encoding⟩
  · exact MonadHom.mmap_pure _ _
  simp only [MonadHom.mmap_bind, SeedHitProof.hom_sequenceFin]
  congr 1
  · congr 1
    funext l
    split
    · rfl
    · exact MonadHom.mmap_pure _ _
    · simp only [MonadHom.mmap_bind, MonadHom.mmap_pure]
      rfl
  · funext values
    simp only [MonadHom.mmap_pure]
    rfl

theorem hom_forgeryWins (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β)
    (dealt : Dealt C m) (st : TsigState C) (forgery : Forgery) :
    φ (forgeryWins lift dealt st forgery) =
      forgeryWins (fun oa => φ (lift oa)) (SeedHitProof.Dealt.hmap φ dealt) st forgery := by
  unfold forgeryWins
  rw [MonadHom.mmap_bind]
  congr 1; funext verified
  split
  · simp only [pure_bind, MonadHom.mmap_pure]
  · simp only [pure_bind, MonadHom.mmap_bind, MonadHom.mmap_pure, hom_honestSignature]

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)

theorem hom_lifetimeOracles (Ro : ℕ → Roles C m) (base : Roles C m)
    (Ro' : ℕ → Roles C n) (base' : Roles C n)
    (hRo : ∀ r, RolesHom φ (Ro r) (Ro' r)) (hbase : RolesHom φ base base')
    (D : C.Coalition) (keys : C.Party → Keys C) (value : Point → m Digest)
    (value' : Point → n Digest) (hvalue : ∀ x, φ (value x) = value' x) (h : C.Party)
    (q : (LifetimeSpec C E).Domain) (st : LifetimeState C E) :
    φ ((lifetimeOraclesWith K circuits settings attempts Ro base D keys value h q).run st) =
      (lifetimeOraclesWith K circuits settings attempts Ro' base' D keys value' h q).run st := by
  have hlift : ∀ {β : Type} (oa : OracleComp (RoSpec C) β),
      φ (base.honest (liftComp oa _)) = base'.honest (liftComp oa _) := fun oa => hbase.honest _
  have hsign : ∀ (i : C.Party) (q : TsigQuery C) (st : LifetimeState C E),
      φ ((tsigOracles (fun oa => base.honest (liftComp oa _))
        (ThresholdLeanXmss.signerDealt (fun oa => base.honest (liftComp oa _)) keys value st i) q).run
          st.sign) =
      (tsigOracles (fun oa => base'.honest (liftComp oa _))
        (ThresholdLeanXmss.signerDealt (fun oa => base'.honest (liftComp oa _)) keys value' st i) q).run
          st.sign := by
    intro i q st
    rw [SeedHitProof.hom_tsigOracles, hom_signerDealt φ _ _ hlift keys value value' hvalue]
    simp only [hlift]
  cases q with
  | sign q =>
    cases q with
    | corrupt i => exact MonadHom.mmap_pure _ _
    | tree b =>
      simp only [lifetimeOraclesWith]
      refine (MonadHom.mmap_bind φ _ _).trans ?_
      erw [hsign]
      refine bind_congr fun r => ?_
      exact MonadHom.mmap_pure _ _
    | round1 i J e message =>
      simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure, pure_bind, Bool.false_eq_true, if_false, MonadHom.mmap_pure]
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, if_true]
        refine (MonadHom.mmap_bind φ _ _).trans ?_
        erw [hsign]
        refine bind_congr fun r => ?_
        exact MonadHom.mmap_pure _ _
    | round2 i J e message parts =>
      simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind]
      split
      · simp only [StateT.run_pure, pure_bind, Bool.false_eq_true, if_false, MonadHom.mmap_pure]
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, if_true]
        refine (MonadHom.mmap_bind φ _ _).trans ?_
        erw [hsign]
        refine bind_congr fun r => ?_
        exact MonadHom.mmap_pure _ _
  | publicKey =>
    simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure,
      MonadHom.mmap_pure]
  | start tree =>
    cases tree <;>
      simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind] <;>
      split <;>
      simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, StateT.run_set, pure_bind,
        bind_assoc, MonadHom.mmap_bind, MonadHom.mmap_pure, hom_startSteps φ _ _ (hRo _)]
  | round sent =>
    cases hr : st.running with
    | none =>
      simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind, hr,
        StateT.run_pure, MonadHom.mmap_pure]
    | some r =>
      rcases r with ⟨tree, fuel, steps⟩
      simp only [lifetimeOraclesWith, StateT.run_bind, StateT.run_get, pure_bind, hr,
        StateT.run_lift, StateT.run_set, StateT.run_pure, bind_assoc, MonadHom.mmap_bind,
        MonadHom.mmap_pure, hom_stepRound φ _ _ (hRo _)]

/-- A monad map transports the entire lifetime scheduler, given role maps for the
base roles and for every ceremony run. -/
theorem hom_lifetimeGameWith (Ro : ℕ → Roles C m) (base : Roles C m)
    (Ro' : ℕ → Roles C n) (base' : Roles C n)
    (hRo : ∀ r, RolesHom φ (Ro r) (Ro' r)) (hbase : RolesHom φ base base')
    (D : C.Coalition) (A : LifetimeAdversary C E) :
    φ (lifetimeGameWith K circuits settings attempts Ro base D A) =
      lifetimeGameWith K circuits settings attempts Ro' base' D A := by
  have hlift : ∀ {β : Type} (oa : OracleComp (RoSpec C) β),
      φ (base.honest (liftComp oa _)) = base'.honest (liftComp oa _) := fun oa => hbase.honest _
  unfold lifetimeGameWith
  rw [MonadHom.mmap_bind, hbase.adversary]
  refine bind_congr fun state => ?_
  rw [MonadHom.mmap_bind, treeSim_hom_phase (fun p => φ p) (fun a => MonadHom.mmap_pure φ a)
    (fun p k => MonadHom.mmap_bind φ p k) base base' (fun p => hbase.adversary p)
    (fun p => hbase.honest p)]
  refine bind_congr fun r => ?_
  rcases r with ⟨state, outputs⟩
  dsimp only
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
      split
      · exact MonadHom.mmap_pure φ _
      · split
        · rw [hom_forgeryWins, hom_dealtWith φ _ _ hlift _ _ _ _ _ (fun x => hbase.honest _)]
          simp only [hlift]
        · exact MonadHom.mmap_pure φ _
  · exact MonadHom.mmap_pure φ _

end Hom

/-! ## The tagged lifetime -/

section Tagged

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- A monad map out of oracle computations is the simulation of its single queries. -/
theorem hom_simulateQ {ι α : Type} {spec : OracleSpec ι} {n : Type → Type} [Monad n]
    [LawfulMonad n] {r : Type → Type} [Monad r] [LawfulMonad r] (ψ : n →ᵐ r)
    (impl : QueryImpl spec n) (p : OracleComp spec α) :
    ψ (simulateQ impl p) = simulateQ (fun t => ψ (impl t)) p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, MonadHom.mmap_bind, ih]

theorem simulateQ_comp {ι κ α : Type} {spec : OracleSpec ι} {spec' : OracleSpec κ}
    {r : Type → Type} [Monad r] [LawfulMonad r] (outer : QueryImpl spec' r)
    (inner : QueryImpl spec (OracleComp spec')) (p : OracleComp spec α) :
    simulateQ outer (simulateQ inner p) = simulateQ (fun t => simulateQ outer (inner t)) p :=
  hom_simulateQ (simulateQ' outer) inner p

/-- The world oracles with a third copy of the local oracles, used by the honest
operators of the ceremony runs. -/
abbrev TaggedSpec (C : Committee) := WorldSpec C + LocalSpec C

/-- Move a world computation to the first two copies of the tagged oracles. -/
def toTagged {α : Type} (p : OracleComp (WorldSpec C) α) : OracleComp (TaggedSpec C) α :=
  simulateQ (fun t => (liftM ((TaggedSpec C).query (.inl t)) : OracleComp (TaggedSpec C) _)) p

/-- The keygen, the signing and the adversary, exactly as `worldRoles`. -/
def taggedBase : Roles C (OracleComp (TaggedSpec C)) where
  adversary p := toTagged (worldRoles.adversary p)
  honest p := toTagged (worldRoles.honest p)

/-- The ceremony runs: the honest operators on the third copy. -/
def taggedRun : Roles C (OracleComp (TaggedSpec C)) where
  adversary p := taggedBase.adversary p
  honest p := simulateQ (fun t => (liftM ((TaggedSpec C).query (.inr t)) : OracleComp (TaggedSpec C) _)) p

/-- The tagged lifetime. -/
def taggedGame (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
    (D : C.Coalition) (A : LifetimeAdversary C E) : OracleComp (TaggedSpec C) Bool :=
  lifetimeGameWith K circuits settings attempts (fun _ => taggedRun) taggedBase D A

/-- Merge the third copy into the free copy. -/
def collapseImpl : QueryImpl (TaggedSpec C) (OracleComp (WorldSpec C))
  | .inl t => (liftM ((WorldSpec C).query t) : OracleComp (WorldSpec C) _)
  | .inr t => (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _)

/-- The tagged charge: the real lifetime charge after merging the copies. -/
def TaggedCounted : (TaggedSpec C).Domain → Prop
  | .inl t => LifetimeCounted t
  | .inr t => LifetimeCounted (C := C) (.inr t)

theorem simulateQ_query_self {ι α : Type} {spec : OracleSpec ι} (p : OracleComp spec α) :
    simulateQ (fun t => (liftM (spec.query t) : OracleComp spec _)) p = p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih => simp only [simulateQ_bind, simulateQ_spec_query, ih]

theorem collapse_toTagged {α : Type} (p : OracleComp (WorldSpec C) α) :
    simulateQ collapseImpl (toTagged p) = p := by
  rw [toTagged, simulateQ_comp]
  refine (congrArg (fun f : QueryImpl (WorldSpec C) (OracleComp (WorldSpec C)) =>
    simulateQ f p) ?_).trans (simulateQ_query_self p)
  funext t
  exact simulateQ_spec_query collapseImpl (Sum.inl t)

/-- Merging the copies gives the real lifetime. -/
theorem collapse_taggedGame (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (attempts : ℕ) (D : C.Coalition) (A : LifetimeAdversary C E) :
    simulateQ collapseImpl (taggedGame K circuits settings attempts D A) =
      lifetimeGame K circuits settings attempts D A := by
  have hbase : RolesHom (simulateQ' (collapseImpl (C := C))) taggedBase worldRoles :=
    ⟨fun p => collapse_toTagged _, fun p => collapse_toTagged _⟩
  have hrun : RolesHom (simulateQ' (collapseImpl (C := C))) taggedRun worldRoles := by
    refine ⟨fun p => collapse_toTagged _, fun p => ?_⟩
    change simulateQ collapseImpl (simulateQ _ p) = free p
    rw [simulateQ_comp]
    exact congrArg (fun f : QueryImpl (LocalSpec C) (OracleComp (WorldSpec C)) => simulateQ f p)
      (funext fun t => simulateQ_spec_query collapseImpl (Sum.inr t))
  exact hom_lifetimeGameWith (simulateQ' collapseImpl) K circuits settings attempts
    (fun _ => taggedRun) taggedBase (fun _ => worldRoles) worldRoles (fun _ => hrun) hbase D A

/-! ## The emulated interpretation -/

/-- The emulation after erasing the observation log. -/
abbrev ErasedM (C : Committee) := StateT (StreamCache C) (OracleComp (WorldSpec C))

/-- Lift a world computation without touching the stream table. -/
def liftHom : OracleComp (WorldSpec C) →ᵐ ErasedM C where
  toFun _ p := StateT.lift p
  toFun_pure' a := by
    apply StateT.ext
    intro s
    simp [StateT.run_lift]
  toFun_bind' p k := by
    apply StateT.ext
    intro s
    simp [StateT.run_lift, StateT.run_bind]

/-- Erase the observation log, as `treeSimErase`. -/
def eraseHom : EmulationM C →ᵐ ErasedM C where
  toFun _ p := treeSimErase p
  toFun_pure' a := treeSimErase_pure a
  toFun_bind' p k := treeSimErase_bind p k

/-- The first two copies are the world itself; the third copy runs the emulated honest
operators of `emulatedRoles`, with the log erased. -/
def emuImpl (D : C.Coalition) : QueryImpl (TaggedSpec C) (ErasedM C)
  | .inl t => StateT.lift (liftM ((WorldSpec C).query t) : OracleComp (WorldSpec C) _)
  | .inr t => treeSimErase ((emulatedRoles D).honest
      (liftM ((LocalSpec C).query t) : OracleComp (LocalSpec C) _))

theorem emu_toTagged (D : C.Coalition) {α : Type} (p : OracleComp (WorldSpec C) α) :
    simulateQ (emuImpl D) (toTagged p) = StateT.lift p := by
  rw [toTagged, simulateQ_comp]
  have h := hom_simulateQ (liftHom (C := C))
    (fun t => (liftM ((WorldSpec C).query t) : OracleComp (WorldSpec C) _)) p
  rw [simulateQ_query_self] at h
  refine (congrArg (fun f : QueryImpl (WorldSpec C) (ErasedM C) => simulateQ f p) ?_).trans h.symm
  funext t
  exact simulateQ_spec_query (emuImpl D) (Sum.inl t)

theorem emulatedHonest_eq (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α) :
    (emulatedRoles D).honest p = simulateQ (fun t => (emulatedRoles D).honest
      (liftM ((LocalSpec C).query t) : OracleComp (LocalSpec C) _)) p := by
  unfold emulatedRoles
  dsimp only
  exact congrArg (fun f => simulateQ f p) (funext fun t => by rw [simulateQ_spec_query])

theorem emu_runHonest (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (emuImpl D) (taggedRun.honest p) = treeSimErase ((emulatedRoles D).honest p) := by
  change simulateQ (emuImpl D) (simulateQ _ p) = _
  rw [simulateQ_comp, emulatedHonest_eq D p]
  have h := hom_simulateQ (eraseHom (C := C)) (fun t => (emulatedRoles D).honest
      (liftM ((LocalSpec C).query t) : OracleComp (LocalSpec C) _)) p
  refine (congrArg (fun f : QueryImpl (LocalSpec C) (ErasedM C) => simulateQ f p) ?_).trans h.symm
  funext t
  exact simulateQ_spec_query (emuImpl D) (Sum.inr t)

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)

/-- The tagged lifetime under the emulated interpretation is the all-emulated lifetime of
`realTailBound_of_sourceBound`, after erasing its log. -/
theorem emulationGame_eq_tagged (D : C.Coalition) (A : LifetimeAdversary C E) :
    emulationGame (lifetimeGameWith K circuits settings attempts (fun _ => emulatedRoles D)
        (lifetimeHybridRoles D 0 0) D A) =
      (simulateQ (emuImpl D) (taggedGame K circuits settings attempts D A)).run' ∅ := by
  have herase : treeSimErase (lifetimeGameWith K circuits settings attempts
      (fun _ => emulatedRoles D) (lifetimeHybridRoles D 0 0) D A) =
      lifetimeGameWith K circuits settings attempts (fun _ => treeSimErasedRoles D) plainRoles D A :=
    hom_lifetimeGameWith (eraseHom (C := C)) K circuits settings attempts _ _ _ _
      (fun _ => ⟨fun _ => rfl, fun _ => rfl⟩)
      ⟨fun p => erase_base_adversary D p, fun p => erase_base_honest D p⟩ D A
  have hemu : simulateQ (emuImpl D) (taggedGame K circuits settings attempts D A) =
      lifetimeGameWith K circuits settings attempts (fun _ => treeSimErasedRoles D) plainRoles D A :=
    hom_lifetimeGameWith (simulateQ' (emuImpl D)) K circuits settings attempts _ _ _ _
      (fun _ => ⟨fun p => (emu_toTagged D _).trans (treeSimErase_adversary D p).symm,
        fun p => emu_runHonest D p⟩)
      ⟨fun p => emu_toTagged D _, fun p => emu_toTagged D _⟩ D A
  rw [emulationGame_erased, herase, hemu]

/-! ## The charge transport -/

/-- Merging the copies charges each tagged query its real lifetime charge. -/
theorem tagged_bound_of_collapse {α : Type} (p : OracleComp (TaggedSpec C) α) (Q : ℕ)
    (h : IsQueryBoundP (simulateQ collapseImpl p) LifetimeCounted Q) :
    IsQueryBoundP p TaggedCounted Q := by
  induction p using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query] at h
    rw [isQueryBoundP_query_bind_iff]
    rcases t with t | t
    · change IsQueryBoundP ((liftM ((WorldSpec C).query t) : OracleComp (WorldSpec C) _) >>= _)
        LifetimeCounted Q at h
      rw [isQueryBoundP_query_bind_iff] at h
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩
    · change IsQueryBoundP ((liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= _)
        LifetimeCounted Q at h
      rw [isQueryBoundP_query_bind_iff] at h
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

/-- A free-copy computation is charged as its local queries. -/
theorem isQueryBoundP_free_lifetime {β : Type} (oa : OracleComp (LocalSpec C) β) (n : ℕ)
    (h : IsQueryBoundP oa (fun t => LifetimeCounted (C := C) (.inr t)) n) :
    IsQueryBoundP (free oa) LifetimeCounted n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have e : free (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= fun u => free (k u) := by
      rw [free_bind]
      rfl
    rw [e]
    exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨h.1, fun u => ih u _ (h.2 u)⟩

/-- Private sampling is free. -/
theorem isQueryBoundP_liftComp_lifetime {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftComp oa (LocalSpec C)) (fun t => LifetimeCounted (C := C) (.inr t)) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t f ih =>
    rw [liftComp_bind]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [LifetimeCounted]), fun u => by simpa only [Nat.zero_sub, ite_self] using ih u⟩

/-- The single-query steps of `emulatedRoles D` for the honest operators, as in
`Reductions.lean`. -/
def emuHonestImpl (D : C.Coalition) : QueryImpl (LocalSpec C) (EmulationM C) := fun t =>
  match t with
  | .inr (.inr x) => if Hidden D x.1 then
      StateT.mk fun cache => liftM (free (liftComp (((PrgInput C →ₒ Bit).randomOracle x).run cache) (LocalSpec C)))
    else StateT.lift (liftM (free (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inr x))))))
  | t => StateT.lift (liftM (free (OracleComp.lift (OracleSpec.query t))))

theorem emulatedHonest_query (D : C.Coalition) (t : (LocalSpec C).Domain) :
    (emulatedRoles D).honest (liftM ((LocalSpec C).query t) : OracleComp (LocalSpec C) _) =
      emuHonestImpl D t :=
  simulateQ_spec_query (emuHonestImpl D) t

theorem stateLift_bound {α : Type} (w : OracleComp (WorldSpec C) α) (s : StreamCache C) (n : ℕ)
    (h : IsQueryBoundP w LifetimeCounted n) :
    IsQueryBoundP ((StateT.lift (liftM w) : EmulationM C α).run s).run LifetimeCounted n := by
  simpa [StateT.run_lift, WriterT.run_bind, WriterT.run_liftM] using h

theorem stateMk_bound {α : Type} (f : StreamCache C → OracleComp (WorldSpec C) (α × StreamCache C))
    (s : StreamCache C) (n : ℕ) (h : IsQueryBoundP (f s) LifetimeCounted n) :
    IsQueryBoundP ((StateT.mk fun c => liftM (f c) : EmulationM C α).run s).run LifetimeCounted n := by
  simpa [StateT.run_mk, WriterT.run_liftM] using h

theorem free_query_bound (t : (LocalSpec C).Domain) :
    IsQueryBoundP (free (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) t))) LifetimeCounted
      (if LifetimeCounted (C := C) (.inr t) then 1 else 0) := by
  apply isQueryBoundP_free_lifetime
  change IsQueryBoundP (liftM ((LocalSpec C).query t) : OracleComp (LocalSpec C) _) _ _
  rw [isQueryBoundP_query_iff]
  intro ht
  simp [ht]

/-- Each emulated step costs at most the real charge of its tagged query. A hidden stream
is a table hit or a free-copy uniform draw. -/
theorem emu_step (D : C.Coalition) (t : (TaggedSpec C).Domain) (s : StreamCache C) :
    IsQueryBoundP ((emuImpl D t).run s) LifetimeCounted (if TaggedCounted t then 1 else 0) := by
  rcases t with t | t
  · change IsQueryBoundP ((liftM ((WorldSpec C).query t) : OracleComp (WorldSpec C) _) >>=
      fun a => pure (a, s)) LifetimeCounted _
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨?_, fun _ => trivial⟩
    by_cases ht : LifetimeCounted t
    · exact Or.inr (by simp [TaggedCounted, ht])
    · exact Or.inl ht
  · change IsQueryBoundP ((treeSimErase ((emulatedRoles D).honest
      (liftM ((LocalSpec C).query t) : OracleComp (LocalSpec C) _))).run s) LifetimeCounted
      (if LifetimeCounted (C := C) (.inr t) then 1 else 0)
    rw [emulatedHonest_query]
    simp only [treeSimErase, StateT.run_mk, keygenEraseLog, isQueryBoundP_map_iff]
    rcases t with u | q | x
    · exact stateLift_bound _ s _ (free_query_bound _)
    · exact stateLift_bound _ s _ (free_query_bound _)
    · simp only [emuHonestImpl]
      split
      · refine stateMk_bound _ s _ ((isQueryBoundP_free_lifetime _ 0
          (isQueryBoundP_liftComp_lifetime _)).mono (Nat.zero_le _))
      · exact stateLift_bound _ s _ (free_query_bound _)

/-- The all-answer budget of the all-emulated lifetime, from the all-answer budget of the
real lifetime at the same circuits. -/
theorem emulatedBudget_of_real (D : C.Coalition) (A : LifetimeAdversary C E) (Q : ℕ)
    (hQ : IsQueryBoundP (lifetimeGame K circuits settings attempts D A) LifetimeCounted Q) :
    IsQueryBoundP
      (emulationGame (lifetimeGameWith K circuits settings attempts (fun _ => emulatedRoles D)
        (lifetimeHybridRoles D 0 0) D A)) LifetimeCounted Q := by
  rw [emulationGame_eq_tagged, StateT.run'_eq, isQueryBoundP_map_iff]
  rw [← collapse_taggedGame] at hQ
  exact IsQueryBoundP.simulateQ_run_StateT_of_step (tagged_bound_of_collapse _ Q hQ)
    (emu_step D) ∅

end Tagged

section Source

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The source budget of `realTailBound_of_sourceBound`, for every `values`, from the
original `HasLifetimeQueryBoundAll`. -/
theorem sourceBound_of_hasLifetimeQueryBound (Q : ℕ)
    (hQ : HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q)
    (values : MpcDomain → HashOutput) :
    IsQueryBoundP
      (emulationGame (lifetimeGameWith K (circuitsOf (thOf values)) settings attempts
        (fun _ => emulatedRoles D) (lifetimeHybridRoles D 0 0) D A)) LifetimeCounted Q :=
  emulatedBudget_of_real K (circuitsOf (thOf values)) settings attempts D A Q (hQ values)

/-- The real half of `KeygenCapQuiet`: capping the keygen adversary preserves the joint
output and cache law of the real keygen prefix. -/
def RealKeygenCapQuiet (prims : Primitives) (Q : ℕ) : Prop :=
  (simulateQ (worldAnswer prims) (phase D (capAdversary Q A.keygen) false)).run ∅ =
    (simulateQ (worldAnswer prims) (phase D A.keygen false)).run ∅

/-- The argument of `realTailBound_of_sourceBound`, with only the real half of the cap. -/
theorem realTailBound_of_realCap (prims : Primitives) (circuits : Circuits) (Q : ℕ)
    (hcap : RealKeygenCapQuiet D A prims Q)
    (hbudget : IsQueryBoundP
      (emulationGame (lifetimeGameWith K circuits settings attempts (fun _ => emulatedRoles D)
        (lifetimeHybridRoles D 0 0) D A)) LifetimeCounted Q) :
    RealTailBound K settings attempts D A prims circuits Q := by
  rw [allEmulated_real_factor] at hbudget
  intro r hr
  rw [hcap] at hr
  have hs : r.1 ∈ support (phase D A.keygen false) := by
    apply support_simulateQ_run'_subset (worldAnswer prims) (phase D A.keygen false) ∅
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ hr
  exact continuationOracle_bound _ Q
    (continuation_bound_of_support _ _ LifetimeCounted Q hbudget r.1 hs)

/-- With the real half of the keygen cap quiet, the original budget gives `RealTailBound`. -/
theorem realTailBound_of_hasLifetimeQueryBound (Q : ℕ)
    (hQ : HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q)
    (hcap : ∀ values : MpcDomain → HashOutput, RealKeygenCapQuiet D A ⟨thOf values, aes⟩ Q)
    (values : MpcDomain → HashOutput) :
    RealTailBound K settings attempts D A ⟨thOf values, aes⟩ (circuitsOf (thOf values)) Q :=
  realTailBound_of_realCap K settings attempts D A ⟨thOf values, aes⟩ (circuitsOf (thOf values)) Q
    (hcap values) (sourceBound_of_hasLifetimeQueryBound K settings attempts circuitsOf D A Q hQ values)

end Source

/-- info: 'ThresholdLeanXmssSecurity.LifetimeEmulatedBudget.hom_lifetimeOracles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hom_lifetimeOracles

/-- info: 'ThresholdLeanXmssSecurity.LifetimeEmulatedBudget.hom_lifetimeGameWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hom_lifetimeGameWith

/-- info: 'ThresholdLeanXmssSecurity.LifetimeEmulatedBudget.collapse_taggedGame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collapse_taggedGame

/-- info: 'ThresholdLeanXmssSecurity.LifetimeEmulatedBudget.emulationGame_eq_tagged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms emulationGame_eq_tagged

/-- info: 'ThresholdLeanXmssSecurity.LifetimeEmulatedBudget.tagged_bound_of_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tagged_bound_of_collapse

/-- info: 'ThresholdLeanXmssSecurity.LifetimeEmulatedBudget.emu_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms emu_step

/-- info: 'ThresholdLeanXmssSecurity.LifetimeEmulatedBudget.emulatedBudget_of_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms emulatedBudget_of_real

/-- info: 'ThresholdLeanXmssSecurity.LifetimeEmulatedBudget.sourceBound_of_hasLifetimeQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceBound_of_hasLifetimeQueryBound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeEmulatedBudget.realTailBound_of_realCap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realTailBound_of_realCap

/-- info: 'ThresholdLeanXmssSecurity.LifetimeEmulatedBudget.realTailBound_of_hasLifetimeQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realTailBound_of_hasLifetimeQueryBound

end ThresholdLeanXmssSecurity.LifetimeEmulatedBudget
