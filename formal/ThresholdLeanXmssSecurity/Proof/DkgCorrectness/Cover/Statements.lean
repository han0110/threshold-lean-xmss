import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Statements
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.MonitorReplay
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.SharesAgree

/-!
# The lock step of one ceremony and the PRF cells at its end, the statements

`CeremonyStarted` states that each honest operator records the start of each check of a ceremony
that an honest operator ends. `CeremonyCells` states that the hash cache at the end of such a
ceremony holds the PRF cells of its jobs.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The statements -/

section Statements

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The PRF cells of the jobs of one ceremony are in the cache at its end. On each outcome of a
ceremony of a positive batch size from a start with no MPC cell in the hash cache, where each honest
operator has keys and the keys are consistent, with an honest result and no global event at the end,
each cell `.prf (gameSeeds T) x` of each point `x` of each job and each term `T` is in the hash cache. -/
def CeremonyCells : Prop :=
  0 < settings.batchSize →
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (c : CeremonyStart C net.State)
    (world : StreamState C), NoMpc world.1 → seedsDiffer D c.keys = false → (∀ i, i ∉ D.1 → (c.keys i).isSome) →
    ∀ r ∈ support ((ceremonyPhase prims K circuits settings D net rounds c).run world), ¬ GlobalEvent r.2 →
      (∃ i, i ∉ D.1 ∧ (r.1.2 i).isSome) → ∀ job ∈ c.jobs, ∀ T, PrfCached r.2.1 (gameSeeds D c.keys T) job.points

/-- The lock step of the honest operators in one ceremony. On each outcome of the ghost run of a
ceremony of a positive batch size from a start with no MPC cell in the hash cache, where each honest
operator has keys and the keys are consistent, with an honest output and no global event at the end,
each honest operator recorded the start of each check. It is `CeremonyAbort` with no ledger and no
provenance of the hidden keys at the start. -/
def CeremonyStarted : Prop :=
  0 < settings.batchSize →
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (c : CeremonyStart C net.State)
    (world : StreamState C), NoMpc world.1 → seedsDiffer D c.keys = false → (∀ i, i ∉ D.1 → (c.keys i).isSome) →
    ∀ ω ∈ support ((ghostCeremony prims K circuits settings D net rounds c).run world), ¬ GlobalEvent ω.2 →
      (∃ i, i ∉ D.1 ∧ (ω.1.2 i).output.isSome) →
      ∀ k < (chunks settings.batchSize c.jobs).length, StartedAt D k ω.1.2

end Statements

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end
