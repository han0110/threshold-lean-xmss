/-
This file holds copies from https://github.com/leanEthereum/leanVM at commit
1acdff19dffcaaf1642e88a9e9b522b415425168, folder `formal/lean_xmss/XmssSecurity/Proof/`.
leanVM deleted the three source files in commit b6167fe4. Each declaration is a verbatim copy with
its upstream name.

* `XmssSecurity.OracleComp.IsQueryBoundP.bind_right_of_mem_support` is lines 7 to 25 of
  `EncodingQueryAccounting.lean`.
* `OracleComp.IsQueryBoundP.of_bind_left` is lines 7 to 18 of `QueryBoundSupport.lean`.
* `OracleComp.IsQueryBoundP.continuation_mono_of_mem_support` is lines 20 to 39 of
  `QueryBoundSupport.lean`.
* `XmssSecurity.ExactPredicateQueryCount` is lines 15 to 24 of `ExactQueryCount.lean`.
* `XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind` is lines 103 to 117 of
  `ExactQueryCount.lean`.
-/
import XmssSecurity.Proof.IdealStatement
import VCVio.OracleComp.QueryTracking.SubSpec
import VCVio.OracleComp.QueryTracking.QueryBound

open OracleComp OracleSpec
open scoped BigOperators

namespace XmssSecurity

theorem OracleComp.IsQueryBoundP.bind_right_of_mem_support
    {index : Type} {spec : OracleSpec index} {α β : Type}
    {predicate : spec.Domain → Prop} [DecidablePred predicate]
    {head : OracleComp spec α} {next : α → OracleComp spec β}
    {fuel : Nat}
    (hbound : (head >>= next).IsQueryBoundP predicate fuel)
    (result : α) (hresult : result ∈ support head) :
    (next result).IsQueryBoundP predicate fuel := by
  induction head using OracleComp.inductionOn generalizing fuel result with
  | pure value =>
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simpa only [pure_bind] using hbound
  | query_bind input rest ih =>
      rw [bind_assoc, OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [mem_support_bind_iff] at hresult
      obtain ⟨response, _hquery, hrest⟩ := hresult
      exact (ih response (hbound.2 response) result hrest).mono (by
        split <;> omega)

end XmssSecurity

namespace OracleComp

theorem IsQueryBoundP.of_bind_left
    {ι : Type} {spec : OracleSpec ι} {α β : Type}
    {p : ι → Prop} [DecidablePred p]
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {q : Nat}
    (hbound : IsQueryBoundP (oa >>= ob) p q) :
    IsQueryBoundP oa p q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure value => simp
  | query_bind input next ih =>
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at hbound
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨hbound.1, fun output => ih output (hbound.2 output)⟩

theorem IsQueryBoundP.continuation_mono_of_mem_support
    {ι : Type} {spec : OracleSpec ι} {α β : Type}
    (p : ι → Prop) [DecidablePred p]
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) (q : Nat)
    (hbound : IsQueryBoundP (oa >>= ob) p q)
    (x : α) (hx : x ∈ support oa) :
    IsQueryBoundP (ob x) p q := by
  induction oa using OracleComp.inductionOn generalizing q x with
  | pure value =>
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst x
      simpa using hbound
  | query_bind input next ih =>
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at hbound
      rw [mem_support_bind_iff] at hx
      obtain ⟨output, _houtput, hx⟩ := hx
      have hrest := ih output (if p input then q - 1 else q)
        (hbound.2 output) x hx
      apply hrest.mono
      split <;> omega

end OracleComp

namespace XmssSecurity

inductive ExactPredicateQueryCount {index : Type} {spec : OracleSpec index}
    (predicate : spec.Domain → Prop) [DecidablePred predicate] :
    OracleComp spec α → Nat → Prop where
  | pure (value : α) : ExactPredicateQueryCount predicate (pure value) 0
  | query (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
      (count : Nat)
      (hnext : ∀ output, ExactPredicateQueryCount predicate (next output) count) :
      ExactPredicateQueryCount predicate
        (liftM (spec.query input) >>= next)
        (count + if predicate input then 1 else 0)
namespace ExactQueryCount

namespace ExactPredicateQueryCount

variable {index : Type} {spec : OracleSpec index}
variable {predicate : spec.Domain → Prop} [DecidablePred predicate]

theorem bind {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactPredicateQueryCount predicate computation count)
    (next : α → OracleComp spec β) (nextCount : Nat)
    (hnext : ∀ value, ExactPredicateQueryCount predicate (next value) nextCount) :
    ExactPredicateQueryCount predicate (computation >>= next) (count + nextCount) := by
  induction hcomputation with
  | pure value => simpa using hnext value
  | query input rest restCount hrest ih =>
      rw [bind_assoc]
      convert ExactPredicateQueryCount.query input
        (fun output => rest output >>= next) (restCount + nextCount) ih using 1
      by_cases hinput : predicate input
      · simp [hinput]
        omega
      · simp [hinput]
end ExactPredicateQueryCount

end ExactQueryCount
end XmssSecurity

/-- info: 'XmssSecurity.OracleComp.IsQueryBoundP.bind_right_of_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms XmssSecurity.OracleComp.IsQueryBoundP.bind_right_of_mem_support

/-- info: 'OracleComp.IsQueryBoundP.of_bind_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OracleComp.IsQueryBoundP.of_bind_left

/-- info: 'OracleComp.IsQueryBoundP.continuation_mono_of_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OracleComp.IsQueryBoundP.continuation_mono_of_mem_support

/-- info: 'XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms XmssSecurity.ExactQueryCount.ExactPredicateQueryCount.bind
