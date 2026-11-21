import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutBounds

/-!
# The coupling of the ghost run to the cut at a check

`CeremonyCoupling` compares the ghost run of one ceremony, which keeps the records, with
`ceremonyCheckAt`, which is the plain prefix of the ceremony and then the real check from the joint
start. `CutLink` is the link of one outcome of each run at check `k`, and `CutLinkFree` is the same
link with no premise on an honest output. `CouplingLaw` states a joint law
of the two runs with the link on its support. `ceremonyCoupling_of_law` proves `CeremonyCoupling` from
`CouplingLaw`. The pointwise step `checkBad_of_link` gives `CheckBad` from the link, with the fresh
streams of `CeremonyInterval`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-! ## The link at a check -/

/-- The link of an outcome `r` of the cut at check `k` and an outcome `ω` of the ghost run. With the
start of check `k` recorded at each honest operator, an honest output and no global event at the
end of `ω`, the cut reaches a joint start `start` and ends its check with `out`. The tuples of `start`
are the recorded tuples of check `k` and its PRSS keys are those of the recorded start, at each
honest operator. Each honest operator that recorded opening `k` accepts in `out`. The hash caches of
`start` and `out` are below the end cache of `ω`. -/
def CutLink (D : C.Coalition) (k : ℕ) {σ : Type}
    (r : Option (CheckStart C σ) × Option ((σ × (C.Party → Option Unit)) × StreamState C))
    (ω : (σ × CeremonySteps C E) × StreamState C) : Prop :=
  StartedAt D k ω.1.2 → HonestOutput D (ceremonyOutputs ω.1.2) → ¬ GlobalEvent ω.2 →
    ∃ start out, r = (some start, some out) ∧
      (∀ i, i ∉ D.1 → start.x i = ceremonyTuplesAt K k ω.1.2 i ∧
        ∀ b, (startsOf (ceremonyRecord ω.1.2 i))[k]? = some b → b.ctx.prss = start.prss i) ∧
      (∀ i, i ∉ D.1 → k < (openingsOf (ceremonyRecord ω.1.2 i)).length → out.1.2 i = some ()) ∧
      start.world.1 ≤ ω.2.1 ∧ out.2.1 ≤ ω.2.1

/-- `CutLink` with no premise on an honest output. -/
def CutLinkFree (D : C.Coalition) (k : ℕ) {σ : Type}
    (r : Option (CheckStart C σ) × Option ((σ × (C.Party → Option Unit)) × StreamState C))
    (ω : (σ × CeremonySteps C E) × StreamState C) : Prop :=
  StartedAt D k ω.1.2 → ¬ GlobalEvent ω.2 →
    ∃ start out, r = (some start, some out) ∧
      (∀ i, i ∉ D.1 → start.x i = ceremonyTuplesAt K k ω.1.2 i ∧
        ∀ b, (startsOf (ceremonyRecord ω.1.2 i))[k]? = some b → b.ctx.prss = start.prss i) ∧
      (∀ i, i ∉ D.1 → k < (openingsOf (ceremonyRecord ω.1.2 i)).length → out.1.2 i = some ()) ∧
      start.world.1 ≤ ω.2.1 ∧ out.2.1 ≤ ω.2.1

/-- The joint law of the cut at check `k` and the ghost run. With the synchronization at the checks,
from a ready start in a phase with the rounds of the ceremony, there is a law `J` of pairs whose
first part has the law of `ceremonyCheckAt k`, whose second part has the law of the ghost run, and
whose support has `CutLink`. -/
def CouplingLaw : Prop :=
  CeremonySync prims K circuits settings →
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    CheckTiming.ceremonyRounds circuits settings (gameParameter D c.keys) c.jobs ≤ rounds →
    ∀ k < (chunks settings.batchSize c.jobs).length,
    ∃ J : ProbComp ((Option (CheckStart C net.State) ×
        Option ((net.State × (C.Party → Option Unit)) × StreamState C)) ×
        ((net.State × CeremonySteps C E) × StreamState C)),
      (Prod.fst <$> J) =ᵈ ceremonyCheckAt prims K circuits settings D net rounds k c world ∧
      (Prod.snd <$> J) =ᵈ (ghostCeremony prims K circuits settings D net rounds c).run world ∧
      ∀ x ∈ support J, CutLink K D k x.1 x.2

/-! ## The bad check from the link -/

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem honestView_congr (D : C.Coalition) {x y : C.Party → List (Tuple C)} (h : ∀ i, i ∉ D.1 → x i = y i) :
    (fun i => if i ∈ D.1 then none else some (x i)) = fun i => if i ∈ D.1 then none else some (y i) := by
  funext i
  split_ifs with hi
  · rfl
  · rw [h i hi]

omit [Fintype E] [DecidableEq E] in
/-- A bad check `k` in the records with no reused key, an honest output and no global event at the
end, linked to an outcome `r` of the cut, gives a bad check of the cut. The streams are fresh at the
joint start by `CeremonyInterval`, because the PRSS keys of the start are those of the recorded starts
and no recorded key is reused. -/
theorem checkBad_of_link (interval : CeremonyInterval prims K circuits settings) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget) (c : CeremonyStart C net.State)
    (world : StreamState C) (hready : CeremonyReady D ℓ c world) (k : ℕ)
    (hk : k < (chunks settings.batchSize c.jobs).length)
    (r : Option (CheckStart C net.State) × Option ((net.State × (C.Party → Option Unit)) × StreamState C))
    (hr : r ∈ support (ceremonyCheckAt prims K circuits settings D net rounds k c world))
    (ω : (net.State × CeremonySteps C E) × StreamState C) (hlink : CutLink K D k r ω)
    (hE : BadCheckAt K D k ω.1.2 ∧ ¬ ReusedKey D world.2 ω.1.2 ∧ HonestOutput D (ceremonyOutputs ω.1.2) ∧
      ¬ GlobalEvent ω.2) : CheckBad D r := by
  obtain ⟨⟨hstart, hcase, i₀, hi₀, hopen⟩, hreused, hhonest, hglobal⟩ := hE
  obtain ⟨start, out, rfl, hx, hacc, hle₁, hle₂⟩ := hlink hstart hhonest hglobal
  unfold ceremonyCheckAt at hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨z, hz, hr⟩ := hr
  cases hj : jointStop D z.1 z.2 with
  | none =>
    rw [hj] at hr
    simp at hr
  | some start' =>
    rw [hj] at hr
    simp only [support_map, Set.mem_image, Prod.mk.injEq, Option.some.injEq] at hr
    obtain ⟨out', -, hstart', hout'⟩ := hr
    subst hstart' hout'
    obtain ⟨hworld, -⟩ := jointStop_eq hj
    have hgz : ¬ GlobalEvent z.2 := fun h => hglobal (globalEvent_mono (hworld ▸ hle₁) h)
    have hfresh : KeysFresh D world.2 start' := by
      intro i hi name key hname hhidden ρ idx position
      by_contra hcell
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hstart i hi)
      refine hreused ⟨name, key, hhidden, ⟨i, hi, b, List.mem_of_getElem? hb, ?_⟩, ρ, idx, position, hcell⟩
      rw [(hx i hi).2 b hb]
      exact hname
    have hview := honestView_congr D fun i hi => (hx i hi).1
    refine ⟨start', out', rfl, ⟨i₀, hi₀, hacc i₀ hi₀ hopen⟩, ?_,
      interval D net rounds ℓ c world hready k hk z hz start' hj hgz hfresh, by rw [hworld]; exact hgz,
      fun h => hglobal (Or.inr (Or.inr (Or.inr (SetupAgree.domainCollision_mono hle₂ h))))⟩
    unfold WrongTuple honestTuples
    unfold WrongTuple honestTuples at hcase
    rw [hview]
    exact hcase

/-! ## `CeremonyCoupling` from the joint law -/

omit [Fintype E] [DecidableEq E] in
/-- `CeremonyCoupling` from `CouplingLaw`. The event of the ghost run has the probability of its
pull to the second part of `J`, the link moves it to the event `CheckBad` of the first part on the
support of `J`, and that event has the probability of `CheckBad` of `ceremonyCheckAt`. -/
theorem ceremonyCoupling_of_law (law : CouplingLaw prims K circuits settings) :
    CeremonyCoupling prims K circuits settings := by
  intro sync interval D net rounds ℓ c world hready hfuel k hk
  obtain ⟨J, hfst, hsnd, hlink⟩ := law sync D net rounds ℓ c world hready hfuel k hk
  rw [← hsnd.prEvent_eq, ← hfst.prEvent_eq, prEvent_map, prEvent_map]
  refine ENNReal.toReal_mono (prEvent_ne_top _) (prEvent_mono_of_support _ _ _ fun x hx hE => ?_)
  have hr : x.1 ∈ support (ceremonyCheckAt prims K circuits settings D net rounds k c world) := by
    rw [← support_eq_of_evalDistEq hfst, support_map]
    exact ⟨x, hx, rfl⟩
  exact checkBad_of_link prims K circuits settings interval D net rounds ℓ c world hready k hk x.1 hr x.2
    (hlink x hx) hE

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyCoupling_of_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.ceremonyCoupling_of_law
