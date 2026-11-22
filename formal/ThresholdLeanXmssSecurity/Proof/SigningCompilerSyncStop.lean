import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareTables
import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareCap

/-! # Persistent stopping events for the fixed signing tables -/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncStop
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag
open SigningCompilerShareTables SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerUntil
variable {C : Committee}
attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support
set_option backward.isDefEq.respectTransparency false

abbrev CompState (C : Committee) := FullState C (Bool × Bool)
abbrev RealState (C : Committee) := SigningLaneUnionProof.TraceState C × HashCache C

def NullBad (sh : ShareStateT C (Bool × Bool)) : Prop :=
  ∃ c k l, sh.bad = some ((false, c), k, l)

def Stuck (st : CompState C) : Prop :=
  st.1.1.2.2 = true ∧ (st.2.bad = none ∨ ∃ m k l, st.2.bad = some ((m, true), k, l))

def Stop (st : CompState C) : Prop := NullBad st.2 ∨ Stuck st

def RealStop (q : ℕ) (st : RealState C) : Prop :=
  st.1.2.1.2 = true ∨ q < st.1.1.1.1.1.1.2

/-- The stopping decision depends only on the first tag and kind. -/
def BadStop (cap : Bool) (bad : Option (SigningShareLazy.FrozenBad (Bool × Bool))) : Prop :=
  (∃ c k, bad = some ((false, c), k)) ∨
    (cap = true ∧ (bad = none ∨ ∃ m k, bad = some ((m, true), k)))

theorem stop_iff (st : CompState C) :
    Stop st ↔ BadStop st.1.1.2.2 (SigningShareLazy.erase st.2).bad := by
  cases hb : st.2.bad with
  | none => simp [Stop, NullBad, Stuck, BadStop, SigningShareLazy.erase, hb]
  | some b =>
      rcases b with ⟨⟨m, c⟩, k, l⟩
      cases m <;> cases c <;> simp [Stop, NullBad, Stuck, BadStop, SigningShareLazy.erase, hb]

theorem BadStop.mono {c c' : Bool} {bad : Option (SigningShareLazy.FrozenBad (Bool × Bool))}
    (h : BadStop c bad) (hc : c ≤ c') : BadStop c' bad := by
  rcases h with h | ⟨hcap, h⟩
  · exact Or.inl h
  · have he : c' = true := (Bool.le_iff_imp.mp hc) hcap
    exact Or.inr ⟨he, h⟩

theorem badStop_update {c c' : Bool} {old next : Option (SigningShareLazy.FrozenBad (Bool × Bool))}
    (h : BadStop c old) (hc : c ≤ c')
    (hn : ∀ tag k, next = some (tag, k) → tag.2 = c) : BadStop c' (old <|> next) := by
  cases ho : old with
  | some b => simpa [ho] using h.mono hc
  | none =>
      have hcap : c = true := by simpa [BadStop, ho] using h
      have hcap' : c' = true := (Bool.le_iff_imp.mp hc) hcap
      cases hn' : next with
      | none => simp [BadStop, hcap']
      | some b =>
          rcases b with ⟨⟨m, cap⟩, k⟩
          have he := hn (m, cap) k hn'
          simp only at he
          simp [BadStop, hcap', he, hcap]



def QueryCap (cap : Bool) : SigningShareLazy.ShareQuery C.Term CPoint (Bool × Bool) → Prop
  | .read _ _ tag => tag.2 = cap
  | .complete _ _ tag => tag.2 = cap
  | .view => True

theorem setsBad_cap (τ : CPoint → Digest) (cap : Bool)
    (t : SigningShareLazy.ShareQuery C.Term CPoint (Bool × Bool))
    (st : ShareStateT C (Bool × Bool)) (ht : QueryCap cap t)
    (tag : Bool × Bool) (k : SigningShareLazy.Kind)
    (h : SigningShareLazy.setsBad C.terms τ t st = some (tag, k)) : tag.2 = cap := by
  cases t with
  | read T p m =>
      simp only [SigningShareLazy.setsBad] at h
      split_ifs at h
      cases h
      exact ht
  | complete p value m =>
      simp only [SigningShareLazy.setsBad] at h
      split_ifs at h
      cases h
      exact ht
  | view => cases h

theorem eager_badStop (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (cap : Bool) (t : SigningShareLazy.ShareQuery C.Term CPoint (Bool × Bool))
    (st : ShareStateT C (Bool × Bool)) (ht : QueryCap cap t)
    (h : BadStop cap (SigningShareLazy.erase st).bad)
    (r : SigningShareLazy.ShareSpec C.Term CPoint (Bool × Bool) t × ShareStateT C (Bool × Bool))
    (hr : r ∈ support ((SigningShareLazy.eagerImpl C.terms τ g t).run st)) :
    BadStop cap (SigningShareLazy.erase r.2).bad := by
  rw [SigningShareLazy.impl_bad_next C.terms τ (fun x => pure (g x))
    (fun T p _ _ => pure (g (T, p))) t st r hr]
  exact badStop_update h le_rfl (setsBad_cap τ cap t st ht)

-- Port of SigningCompilerShareCap.ordinary_cap; every ordinary query is covered.
theorem ordinary_cap (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support ((ordinary P seeds q s pads t).run st)) : st.2.2 ≤ r.2.2.2 := by
  have sticky (h : st.2.2 = true) : r.2.2.2 = true := by
    cases t with
    | inr k => exact cappedCompiler_flag_sticky P seeds q s (.inr k) st h r hr
    | inl t =>
      cases t with
      | pad p =>
        simp only [ordinary, StateT.run, mem_support_pure_iff] at hr
        subst r
        cases hp : st.1.1.data.pads p <;> simpa only [padStep, hp] using h
      | _ => exact cappedCompiler_flag_sticky P seeds q s _ st h r hr
  cases h : st.2.2 with
  | false => simp
  | true => simp [sticky h]

-- Port of current VCVio OracleComp/SimSemantics/StateT/Basic:324;
-- the pinned package uses lawful SetM lifts for support.
theorem support_simulateQ_subset {ι α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec ProbComp) (oa : OracleComp spec α) :
    support (simulateQ impl oa) ⊆ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
      intro x hx
      simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at hx
      obtain ⟨u, _, hx⟩ := hx
      exact (mem_support_bind_iff _ _ _).2 ⟨u, mem_support_query t u, ih u hx⟩

set_option linter.constructorNameAsVariable false in
theorem hashTail_cap (P : PublicParameter) (seeds : C.Term → HashOutput)
    (input : Query C) (st : CappedCompilerState C) (value : HashOutput) (cache : HashCache C)
    (r : HashOutput × CappedCompilerState C)
    (hr : r ∈ support (hashTail P seeds input st value cache)) : r.2.2.2 = st.2.2 :=
  congrArg Prod.snd (hashTail_support P seeds input st value cache r hr).2.2.2

attribute [local irreducible] hashTail

theorem freshPending_cap (edge : ChainNoiseIndex) (st : CappedCompilerState C)
    (r : DeferredOutput × CappedCompilerState C)
    (hr : r ∈ support (freshPending edge st)) : r.2.2.2 = st.2.2 := by
  unfold freshPending at hr
  cases hp : st.1.1.data.pending (chainPending edge) <;>
    simp only [hp, mem_support_bind_iff, mem_support_pure_iff] at hr
  · obtain ⟨_, _, rfl⟩ := hr; rfl
  · subst r; rfl

private theorem freshRest_of_tail (input : Query C) (z : RestSlot C) (st : CappedCompilerState C)
    (tail : HashOutput → HashCache C → ProbComp (HashOutput × CappedCompilerState C))
    (h : ∀ v c r, r ∈ support (tail v c) → r.2.2.2 = st.2.2) :
    ∀ r ∈ support (do
      let read ← match st.1.1.data.cache input with
        | some v => pure (v, st.1.1.data.cache)
        | none => do
          let v ← query (spec := PrivateSpec C) (.inr (.inr z))
          pure (v, st.1.1.data.cache.cacheQuery input v)
      liftM (tail read.1 read.2) : OracleComp (PrivateSpec C) _), r.2.2.2 = st.2.2 := by
  cases hc : st.1.1.data.cache input with
  | some value =>
    simp only [pure_bind]
    intro r hr
    exact h value _ r (mem_support_of_mem_support_liftComp (PrivateSpec C) _ _ hr)
  | none =>
    simp only [pure_bind]
    intro r hr
    obtain ⟨v, _, hr⟩ := mem_support_bind_peel _ _ hr
    exact h v _ r (mem_support_of_mem_support_liftComp (PrivateSpec C) _ _ hr)

theorem freshRest_cap (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (z : RestSlot C) (st : CappedCompilerState C)
    (r : HashOutput × CappedCompilerState C)
    (hr : r ∈ support (freshRest P seeds pairs z st)) : r.2.2.2 = st.2.2 := by
  let input := restInput seeds pairs z
  exact freshRest_of_tail input z st (hashTail P seeds input st) (hashTail_cap P seeds input st) r hr

theorem ordinaryRaw_cap (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CappedCompilerState C)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
    (hr : r ∈ support (ordinaryRaw P seeds pairs q s pads t st)) : st.2.2 ≤ r.2.2.2 := by
  have ho (t : DeferredQuery C ⊕ HiddenKey)
      (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CappedCompilerState C)
      (hr : r ∈ support (liftM (ordinary P seeds q s pads t st) :
        OracleComp (PrivateSpec C) _)) : st.2.2 ≤ r.2.2.2 :=
    ordinary_cap P seeds q s pads t st r
      (mem_support_of_mem_support_liftComp (PrivateSpec C) _ _ hr)
  cases t with
  | inr k => exact ho _ _ hr
  | inl t =>
      cases t with
      | pending p =>
          cases p with
          | bottom e l p => exact le_of_eq (freshPending_cap (l, .inl e, p) st r hr).symm
          | top b l p => exact le_of_eq (freshPending_cap (l, .inr b, p) st r hr).symm
          | _ => exact ho _ _ hr
      | hash input =>
          cases hz : restRoute seeds pairs input with
          | none => exact ho _ _ (by unfold ordinaryRaw at hr; simpa only [hz] using hr)
          | some z => exact le_of_eq (freshRest_cap P seeds pairs z st r
              (by unfold ordinaryRaw at hr; simpa only [hz] using hr)).symm
      | _ => exact ho _ _ hr

attribute [local irreducible] ordinaryStepTag readStepTag eagerHandlerTag SigningShareLazy.eagerImpl ordinary

theorem eagerBackend_stop (P : PublicParameter) (seeds : C.Term → HashOutput)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (t : (SpecX C).Domain) (st : CompState C) (h : Stop st)
    (r : (SpecX C t) × CompState C)
    (hr : r ∈ support (eagerBackend capTag P seeds q s pads τ g t st)) : Stop r.2 := by
  have hbad := (stop_iff st).mp h
  have hord (t : DeferredQuery C ⊕ HiddenKey)
      (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CompState C)
      (hr : r ∈ support ((fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (eagerHandlerTag τ g) (ordinaryStepTag P seeds q s pads t st.1)).run st.2)) :
      Stop r.2 := by
    rw [eager_ordinary] at hr
    simp only [support_map] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    apply (stop_iff _).mpr
    exact hbad.mono (ordinary_cap P seeds q s pads t (merged seeds st.1.1 st.2.cache) a ha)
  have hread (T : C.Term) (p : CPoint)
      (r : HashOutput × CompState C)
      (hr : r ∈ support ((fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (eagerHandlerTag τ g) (readStepTag capTag P seeds T p st.1)).run st.2)) :
      Stop r.2 := by
    refine eager_read_of_run seeds st _ _ _ (eager_read capTag P seeds τ g T p st) (fun r => Stop r.2) ?_ r hr
    intro a ha b hb
    apply (stop_iff _).mpr
    have he := hashTail_cap P seeds _ _ a.1 _ b hb
    change BadStop b.2.2.2 (SigningShareLazy.erase a.2).bad
    rw [he]
    exact eager_badStop τ g st.1.1.2.2 (.read T p (capTag st.1)) st.2 rfl hbad a ha
  rcases t with ((t | k) | mark) | ⟨p, target⟩
  · cases t with
    | hash input =>
        cases hrout : route seeds input with
        | none => exact hord (.inl (.hash input)) r (by
            simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag, hrout] at hr; exact hr)
        | some z => exact hread z.1 z.2 r (by
            simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag, hrout] at hr; exact hr)
    | pending p => exact hord (.inl (.pending p)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr; exact hr)
    | virtual T p => exact hord (.inl (.virtual T p)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr; exact hr)
    | pad p => exact hord (.inl (.pad p)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr; exact hr)
    | inspect p => exact hord (.inl (.inspect p)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr; exact hr)
    | plant p v => exact hord (.inl (.plant p v)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr; exact hr)
    | snapshot => exact hord (.inl .snapshot) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr; exact hr)
    | sample => exact hord (.inl .sample) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr; exact hr)
    | record p v => exact hord (.inl (.record p v)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr; exact hr)
    | uniform n => exact hord (.inl (.uniform n)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr; exact hr)
    | bindKey e m => exact hord (.inl (.bindKey e m)) r (by
        simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr; exact hr)
  · exact hord (.inr k) r (by
      simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag] at hr; exact hr)
  · simp only [eagerBackend, SigningCompilerUntil.fuse, StateT.run, shareBackendTag, simulateQ_pure,
    MonadAttach.mem_support] at hr
    subst r
    exact h
  · by_cases hp : Constrained p
    · simp only [eagerBackend, SigningCompilerUntil.fuse, shareBackendTag, hp, dite_eq_left] at hr
      change r ∈ support ((fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (eagerHandlerTag τ g) (do
          let value ← shareQueryTag (.complete ⟨p, hp⟩ target (capTag st.1))
          pure (value, st.1))).run st.2) at hr
      simp only [simulateQ_bind, StateT.run_bind, eager_share, simulateQ_pure,
        StateT.run_pure, map_bind, map_pure, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      apply (stop_iff _).mpr
      exact eager_badStop τ g st.1.1.2.2 (.complete ⟨p, hp⟩ target (capTag st.1))
        st.2 rfl hbad a ha
    · simp only [eagerBackend, SigningCompilerUntil.fuse, StateT.run, shareBackendTag, hp,
        MonadAttach.mem_support] at hr
      subst r
      exact h

theorem ordinaryFullRaw_stop (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (t : DeferredQuery C ⊕ HiddenKey) (st : CompState C) (h : Stop st)
    (r : (DeferredSpec C + RevealSpec HiddenKey Digest) t × CompState C)
    (hr : r ∈ support (ordinaryFullRaw P seeds pairs q s pads t st)) : Stop r.2 := by
  simp only [ordinaryFullRaw, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  apply (stop_iff _).mpr
  exact ((stop_iff st).mp h).mono
    (ordinaryRaw_cap P seeds pairs q s pads t (merged seeds st.1.1 st.2.cache) a ha)

attribute [local irreducible] ordinaryFullRaw eagerBackend

theorem backendRaw_stop (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (t : (SpecX C).Domain) (st : CompState C) (h : Stop st)
    (r : (SpecX C t) × CompState C)
    (hr : r ∈ support (backendRaw capTag P seeds pairs q s pads τ g t st)) : Stop r.2 := by
  have he (t : (SpecX C).Domain) (r : (SpecX C t) × CompState C)
      (hr : r ∈ support (liftM (eagerBackend capTag P seeds q s pads τ g t st) :
        OracleComp (PrivateSpec C) _)) : Stop r.2 :=
    eagerBackend_stop P seeds q s pads τ g t st h r
      (mem_support_of_mem_support_liftComp (PrivateSpec C) _ _ hr)
  rcases t with ((t | k) | mark) | complete
  · cases t with
    | hash input =>
        cases hout : route seeds input with
        | some z =>
            simp only [backendRaw, hout] at hr
            exact he (.inl (.inl (.inl (.hash input)))) r hr
        | none =>
            simp only [backendRaw, hout] at hr
            exact ordinaryFullRaw_stop P seeds pairs q s pads (.inl (.hash input)) st h r hr
    | pending p => exact ordinaryFullRaw_stop P seeds pairs q s pads (.inl (.pending p)) st h r hr
    | virtual T p => exact ordinaryFullRaw_stop P seeds pairs q s pads (.inl (.virtual T p)) st h r hr
    | pad p => exact ordinaryFullRaw_stop P seeds pairs q s pads (.inl (.pad p)) st h r hr
    | inspect p => exact ordinaryFullRaw_stop P seeds pairs q s pads (.inl (.inspect p)) st h r hr
    | plant p v => exact ordinaryFullRaw_stop P seeds pairs q s pads (.inl (.plant p v)) st h r hr
    | snapshot => exact ordinaryFullRaw_stop P seeds pairs q s pads (.inl .snapshot) st h r hr
    | sample => exact ordinaryFullRaw_stop P seeds pairs q s pads (.inl .sample) st h r hr
    | record p v => exact ordinaryFullRaw_stop P seeds pairs q s pads (.inl (.record p v)) st h r hr
    | uniform n => exact ordinaryFullRaw_stop P seeds pairs q s pads (.inl (.uniform n)) st h r hr
    | bindKey e m => exact ordinaryFullRaw_stop P seeds pairs q s pads (.inl (.bindKey e m)) st h r hr
  · exact ordinaryFullRaw_stop P seeds pairs q s pads (.inr k) st h r hr
  · exact he (.inl (.inr mark)) r hr
  · exact he (.inr complete) r hr

/-- Both components of the stopping event persist under every fixed-table query. -/
theorem backendT_stop (P : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (t : (SpecX C).Domain) (st : CompState C) (h : Stop st)
    (r : (SpecX C t) × CompState C)
    (hr : r ∈ support ((shareBackendTagT capTag P seeds pairs q s pads τ g noise rest t).run st)) :
    Stop r.2 := by
  exact backendRaw_stop P seeds pairs q s pads τ g t st h r
    (support_simulateQ_subset _ _ hr)

/-- A stopping outer state is retained through any inner handler. -/
theorem fuse_stop {ι κ σ : Type} {spec : OracleSpec ι} {mid : OracleSpec κ}
    (inner : QueryImpl spec (StateT σ (OracleComp mid)))
    (outer : QueryImpl mid (StateT (CompState C) ProbComp))
    (hs : ∀ t st, Stop st → ∀ r ∈ support ((outer t).run st), Stop r.2)
    (t : ι) (st : σ × CompState C) (h : Stop st.2)
    (r : spec t × (σ × CompState C))
    (hr : r ∈ support ((SigningCompilerUntil.fuse inner outer t).run st)) : Stop r.2.2 := by
  simp only [SigningCompilerUntil.fuse, StateT.run, ← bind_pure_comp] at hr
  obtain ⟨a, ha, hr⟩ := mem_support_bind_peel _ _ hr
  obtain rfl := eq_of_mem_support_pure _ hr
  exact simulateQ_sticky outer Stop hs ((inner t).run st.1) st.2 h a ha

abbrev TraceCount (st : SigningLaneUnionProof.TraceState C) : ℕ := st.1.1.1.1.1.2
abbrev TraceFlag (st : SigningLaneUnionProof.TraceState C) : Bool := st.2.1.2

private theorem rawCarriedLogged_control (prims : Primitives) (t : (WorldSpec C).Domain)
    (st : SigningFlatProof.FlatJointState C) (r : WorldSpec C t × SigningFlatProof.FlatJointState C)
    (hr : r ∈ support ((rawCarriedLogged prims t).run st)) :
    r.2.2 = st.2 ∧ st.1.1.2 ≤ r.2.1.1.2 := by
  obtain ⟨b, _, rfl⟩ := mem_support_map_peel _ _ hr
  exact ⟨rfl, Nat.le_add_right _ _⟩

private theorem bind_map_all {ι α β γ : Type} {spec : OracleSpec ι} (first : OracleComp spec α)
    (next : α → OracleComp spec β) (finish : α → β → γ) (I : γ → Prop)
    (ok : ∀ a ∈ support first, ∀ b, I (finish a b)) (r : γ)
    (hr : r ∈ support (first >>= fun a => finish a <$> next a)) : I r := by
  obtain ⟨a, ha, hr⟩ := mem_support_bind_peel _ _ hr
  obtain ⟨b, _, rfl⟩ := mem_support_map_peel _ _ hr
  exact ok a ha b

private theorem rawKeyedSplitWorld_control (prims : Primitives) (x : Keys3 C) (t : (WorldSpec C).Domain)
    (st : RawSplitState C) (r : WorldSpec C t × RawSplitState C)
    (hr : r ∈ support ((rawKeyedSplitWorld prims x t).run st)) :
    r.2.2 = st.2 ∧ st.1.1.1.1.2 ≤ r.2.1.1.1.1.2 := by
  unfold rawKeyedSplitWorld at hr
  let first := (rawCarriedLogged prims t).run (st.1.1.1, st.2)
  generalize hc : rawKeyedSplitOracle (XmssSecurity.encodingInputLeafIndex? x.1) = impl at hr
  refine bind_map_all first _ _ (fun r => r.2.2 = st.2 ∧ st.1.1.1.1.2 ≤ r.2.1.1.1.1.2) ?_ r hr
  intro z hz _
  exact rawCarriedLogged_control prims t _ z hz

/-- A raw world call retains the entire opening state and adds its nonnegative cost. -/
theorem rawTraceWorld_control (prims : Primitives) (x : Keys3 C)
    (t : (WorldSpec C).Domain) (st : SigningLaneUnionProof.TraceState C)
    (r : WorldSpec C t × SigningLaneUnionProof.TraceState C)
    (hr : r ∈ support ((rawTraceWorld prims x t).run st)) :
    r.2.2 = st.2 ∧ TraceCount st ≤ TraceCount r.2 := by
  obtain ⟨a, ha, rfl⟩ := mem_support_map_peel _ _ hr
  exact rawKeyedSplitWorld_control prims x t _ a ha

theorem rawTraceWorld_run_control {α : Type} (prims : Primitives) (x : Keys3 C)
    (oa : OracleComp (WorldSpec C) α) (st : SigningLaneUnionProof.TraceState C)
    (r : α × SigningLaneUnionProof.TraceState C)
    (hr : r ∈ support ((simulateQ (rawTraceWorld prims x) oa).run st)) :
    r.2.2 = st.2 ∧ TraceCount st ≤ TraceCount r.2 := by
  induction oa using OracleComp.inductionOn generalizing st r with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      subst r
      exact ⟨rfl, le_rfl⟩
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨a, ha, hr⟩ := hr
      have h₁ := rawTraceWorld_control prims x t st a ha
      have h₂ := ih a.1 a.2 r hr
      exact ⟨h₂.1.trans h₁.1, h₁.2.trans h₂.2⟩

theorem openingOracles_flag (x : Keys3 C) (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C + TsigSpec C).Domain) (st : SigningJointEagerProof.OpeningState C)
    (r : (LocalSpec C + TsigSpec C) t × SigningJointEagerProof.OpeningState C)
    (hr : r ∈ support ((openingOracles x dealt t).run st)) : st.1.2 ≤ r.2.1.2 := by
  cases t <;>
    simp only [openingOracles, SigningCoreProof.flaggedOracles, StateT.run_mk,
      Functor.map_map, support_map] at hr
  · obtain ⟨_, _, rfl⟩ := hr
    cases st.1.2 <;> simp
  · obtain ⟨_, _, rfl⟩ := hr
    exact le_rfl

theorem rawTraceAdv_control (prims : Primitives) (x : Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C + TsigSpec C).Domain) (st : SigningLaneUnionProof.TraceState C)
    (r : (LocalSpec C + TsigSpec C) t × SigningLaneUnionProof.TraceState C)
    (hr : r ∈ support ((rawTraceFlatWith prims x (openingOracles x dealt) t).run st)) :
    TraceFlag st ≤ TraceFlag r.2 ∧ TraceCount st ≤ TraceCount r.2 := by
  simp only [rawTraceFlatWith, StateT.run_mk, support_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  have hc := rawTraceWorld_run_control prims x ((openingOracles x dealt t).run st.2) st a ha
  have hs := Marks.mem_support_of_simulate_run
    (rawTraceWorld prims x) ((openingOracles x dealt t).run st.2) st ha
  exact ⟨openingOracles_flag x dealt t st.2 a.1 hs, hc.2⟩

/-- A raw handler's flag/count monotonicity survives every private interpreter. -/
theorem realStop_fuse {ι : Type} {spec : OracleSpec ι}
    (inner : QueryImpl spec (StateT (SigningLaneUnionProof.TraceState C)
      (OracleComp (SigningGuessProof.SigningRawSpec C))))
    (outer : QueryImpl (SigningGuessProof.SigningRawSpec C) (StateT (HashCache C) ProbComp))
    (hc : ∀ t st, ∀ r ∈ support ((inner t).run st),
      TraceFlag st ≤ TraceFlag r.2 ∧ TraceCount st ≤ TraceCount r.2)
    (q : ℕ) (t : ι) (st : RealState C) (h : RealStop q st)
    (r : spec t × RealState C)
    (hr : r ∈ support ((SigningCompilerUntil.fuse inner outer t).run st)) : RealStop q r.2 := by
  simp only [SigningCompilerUntil.fuse, StateT.run, support_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  have hs := Marks.mem_support_of_simulate_run outer ((inner t).run st.1) st.2 ha
  have hm := hc t st.1 a.1 hs
  rcases h with hf | hn
  · exact Or.inl ((Bool.le_iff_imp.mp hm.1) hf)
  · exact Or.inr (hn.trans_le hm.2)

theorem realStop_world (prims : Primitives) (x : Keys3 C)
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (q : ℕ) (t : (WorldSpec C).Domain) (st : RealState C) (h : RealStop q st)
    (r : WorldSpec C t × RealState C)
    (hr : r ∈ support ((SigningCompilerUntil.fuse (rawTraceWorld prims x)
      (SigningGuessProof.privateRoImpl ∘ₛ resolveSlots x.2.1 x.2.2 (realTable g rest)) t).run st)) :
    RealStop q r.2 := by
  apply realStop_fuse (rawTraceWorld prims x) _ ?_ q t st h r hr
  intro t st r hr
  have hc := rawTraceWorld_control prims x t st r hr
  exact ⟨le_of_eq (congrArg (fun x => x.1.2) hc.1).symm, hc.2⟩

theorem realStop_adv (prims : Primitives) (x : Keys3 C)
    (dealt : Dealt C (OracleComp (WorldSpec C)))
    (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput)
    (q : ℕ) (t : (LocalSpec C + TsigSpec C).Domain) (st : RealState C) (h : RealStop q st)
    (r : (LocalSpec C + TsigSpec C) t × RealState C)
    (hr : r ∈ support ((SigningCompilerUntil.fuse (rawTraceFlatWith prims x (openingOracles x dealt))
      (SigningGuessProof.privateRoImpl ∘ₛ resolveSlots x.2.1 x.2.2 (realTable g rest)) t).run st)) :
    RealStop q r.2 :=
  realStop_fuse _ _ (rawTraceAdv_control prims x dealt) q t st h r hr

end ThresholdLeanXmssSecurity.SigningCompilerSyncStop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncStop.backendT_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncStop.backendT_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncStop.fuse_stop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncStop.fuse_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncStop.rawTraceWorld_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncStop.rawTraceWorld_control

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncStop.realStop_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncStop.realStop_world

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncStop.realStop_adv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncStop.realStop_adv
