import ThresholdLeanXmssSecurity.Proof.SigningGuessLink

/-!
# Support facts of the uncharged lane

* `StateGrows st st'` says that `bound` is write-once, and that the corrupt set and the release list
  grow. `gameOracles_stateGrows` gives it for one call of the signing oracles.
  `SigningLane2TraceLink` and `SigningReleasedAlign` use it.
* `releasedAt st e` is `HonestKey.released` read at the state `st`. `honestKey_released` shows that
  the final key uses the final state. `SigningCompilerO1Canonical` uses it.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningSupportProof

open HashSig LeanXmss ThresholdLeanXmss SigningOpeningProof

variable {C : Committee}

section Grows

/-- The state of the signing oracles grows from `st` to `st'`. `bound` is write-once, and the
corrupt set and the release list grow. -/
def StateGrows (st st' : TsigState C) : Prop :=
  SigningGuessProof.BoundExtends st st' ∧ st.corrupt ⊆ st'.corrupt ∧ st.released <+: st'.released

theorem stateGrows_refl (st : TsigState C) : StateGrows st st :=
  ⟨SigningGuessProof.boundExtends_refl st, Finset.Subset.refl _, List.prefix_refl _⟩

theorem gameOracles_stateGrows (dealt : Dealt C (OracleComp (WorldSpec C)))
    (t : (LocalSpec C + TsigSpec C).Domain) (st : TsigState C)
    (r : (LocalSpec C + TsigSpec C).Range t × TsigState C)
    (hr : r ∈ support ((SigningCoreProof.gameOracles dealt t).run st)) : StateGrows st r.2 := by
  cases t with
  | inl t =>
    change r ∈ support ((fun a => (a, st)) <$>
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) at hr
    simp only [support_map] at hr
    obtain ⟨value, _, rfl⟩ := hr
    exact stateGrows_refl st
  | inr t =>
    refine ⟨SigningGuessProof.tsigOracles_boundExtends _ dealt t st r hr,
      SigningGuessProof.tsigOracles_corrupt_mono _ dealt t st r hr, ?_⟩
    rw [SigningGuessProof.tsigOracles_releaseStep _ dealt t st r hr, SigningGuessProof.releaseStep_append]
    exact List.prefix_append _ _

end Grows

section CallTime

/-- `HonestKey.released` read at the state `st`. At least `t` operators can give the chain parts at
`e` for the bound message. -/
def releasedAt (st : TsigState C) (e : KeyIndex) : Bool :=
  match st.bound e with
  | some message => decide (C.t ≤ (signersAt st e message).card)
  | none => false

theorem honestKey_released (prims : Primitives) (z : SigningDescentProof.FinalState C) :
    (z.honestKey prims).released = releasedAt z.state z.key := rfl

end CallTime

end SigningSupportProof

end ThresholdLeanXmssSecurity
