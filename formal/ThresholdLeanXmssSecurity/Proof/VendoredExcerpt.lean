/-
This file holds copies from https://github.com/leanEthereum/leanVM at commit
1acdff19dffcaaf1642e88a9e9b522b415425168, folder `formal/lean_xmss/XmssSecurity/Proof/`.
Each declaration is a verbatim copy with its upstream name.

leanVM at commit f5f3672f2b72d3f89dbbaeff18a53a73c975d620 has the two source files of the three
declarations, but it does not have the declarations.

* `DeterministicSigning.Resolves.map` is lines 85 to 88 of `Bridge/Basic.lean`.
* `DeterministicSigning.Resolves.of_map` is lines 90 to 94 of `Bridge/Basic.lean`.
* `DeterministicSigning.Resolves.run_eq_pure` is lines 72 to 80 of `Deterministic/Replay.lean`.
-/
import XmssSecurity.Proof.IdealStatement
import XmssSecurity.Proof.Bridge.Basic
import VCVio.OracleComp.QueryTracking.SubSpec
import VCVio.OracleComp.QueryTracking.QueryBound

open OracleComp OracleSpec
open scoped BigOperators

namespace DeterministicSigning

variable {D R : Type}

theorem Resolves.map {α β : Type} {cache : QueryCache (D →ₒ R)} {c : OracleComp (D →ₒ R) α}
    {v : α} (h : Resolves cache c v) (g : α → β) : Resolves cache (g <$> c) (g v) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind (.pure _)

theorem Resolves.of_map {α β : Type} {cache : QueryCache (D →ₒ R)} {c : OracleComp (D →ₒ R) α}
    {g : α → β} {w : β} (h : Resolves cache (g <$> c) w) : ∃ v, Resolves cache c v ∧ g v = w := by
  rw [map_eq_bind_pure_comp] at h
  obtain ⟨v, hv, hw⟩ := h.of_bind
  exact ⟨v, hv, hw.pure_inv⟩

variable [DecidableEq D] [SampleableType R]

theorem Resolves.run_eq_pure {α : Type} {cache : QueryCache (D →ₒ R)}
    {computation : OracleComp (D →ₒ R) α} {value : α}
    (h : Resolves cache computation value) :
    (simulateQ randomOracle computation).run cache = Pure.pure (value, cache) := by
  induction h with
  | pure value => rfl
  | query input answer hanswer next value _ ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        QueryImpl.withCaching_run_some _ hanswer, pure_bind, ih]

end DeterministicSigning

/-- info: 'DeterministicSigning.Resolves.map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeterministicSigning.Resolves.map

/-- info: 'DeterministicSigning.Resolves.of_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeterministicSigning.Resolves.of_map

/-- info: 'DeterministicSigning.Resolves.run_eq_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeterministicSigning.Resolves.run_eq_pure
