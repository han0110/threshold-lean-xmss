import XmssSecurity.Proof.RandomOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Constrained share tables

A visible cache carries full hash outputs. Completion constrains the XOR of the low
halves, choosing the first currently absent share as slack. The private full table
extends this cache. Original handlers retain a sticky lucky bit; frozen handlers
retain only the first bad tag and query kind.

The hash splitting equivalence and uniform truncation law are those of the pinned
`XmssSecurity.Proof.RandomOracle`. Table marginalization uses VCV-io's `EagerTable`.
-/

open OracleComp OracleSpec
open scoped Classical

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace ThresholdLeanXmssSecurity.SigningShareLazy

abbrev Digest := XmssSecurity.Digest
abbrev HashOutput := XmssSecurity.HashOutput
abbrev pair := XmssSecurity.Rom.hashOutputEquivDigestPair
abbrev lowHash := XmssSecurity.truncateHash

inductive Kind
  | read
  | complete
  deriving DecidableEq

abbrev ImplBad (Tag : Type) := Tag × Kind × Bool
abbrev FrozenBad (Tag : Type) := Tag × Kind

structure ShareState (κ ι B : Type) where
  cache : κ × ι → Option HashOutput
  done : Finset ι
  bad : Option B

variable {κ ι Tag B : Type} [DecidableEq κ] [DecidableEq ι]

/-- Only the lucky bit is forgotten. -/
def erase (st : ShareState κ ι (ImplBad Tag)) : ShareState κ ι (FrozenBad Tag) :=
  ⟨st.cache, st.done, st.bad.map (fun b => (b.1, b.2.1))⟩

def init (bad : Option B := none) : ShareState κ ι B := ⟨fun _ => none, ∅, bad⟩

def xorSum (order : List κ) (f : κ → Digest) : Digest :=
  order.foldr (fun b acc => f b ^^^ acc) 0

def low (st : ShareState κ ι B) (b : κ) (p : ι) : Digest :=
  lowHash ((st.cache (b, p)).getD 0)

def sum (order : List κ) (st : ShareState κ ι B) (p : ι) : Digest :=
  xorSum order (fun b => low st b p)

def others (order : List κ) (st : ShareState κ ι B) (p : ι) (b : κ) : Digest :=
  xorSum (order.filter (· ≠ b)) (fun t => low st t p)

def slack (order : List κ) (st : ShareState κ ι B) (p : ι) : Option κ :=
  order.find? (fun b => (st.cache (b, p)).isNone)

inductive ShareQuery (κ ι Tag : Type)
  | read (b : κ) (p : ι) (tag : Tag)
  | complete (p : ι) (target : Digest) (tag : Tag)
  | view

def ShareSpec (κ ι Tag : Type) : OracleSpec (ShareQuery κ ι Tag)
  | .read .. => HashOutput
  | .complete .. => Bool
  | .view => (κ × ι → Option HashOutput) × Finset ι

/-- The first-bad decision uses only the state before the query. -/
def setsBad (order : List κ) (τ : ι → Digest) (q : ShareQuery κ ι Tag)
    (st : ShareState κ ι B) : Option (FrozenBad Tag) := by
  classical
  exact match q with
  | .read b p tag =>
      if st.cache (b, p) = none ∧ p ∉ st.done ∧
          ∀ t ∈ order, t ≠ b → st.cache (t, p) ≠ none then
        some (tag, .read) else none
  | .complete p target tag =>
      if p ∉ st.done ∧ (slack order st p = none ∨ target ≠ τ p) then
        some (tag, .complete) else none
  | .view => none

def put (st : ShareState κ ι B) (b : κ) (p : ι) (v : HashOutput) :
    ShareState κ ι B := { st with cache := Function.update st.cache (b, p) (some v) }

/-- Sampling takes place only at an absent visible cache entry. -/
def fillTerm (draw : κ × ι → ProbComp HashOutput) (p : ι) (b : κ)
    (st : ShareState κ ι B) : ProbComp (ShareState κ ι B) :=
  match st.cache (b, p) with
  | some _ => pure st
  | none => (fun v => put st b p v) <$> draw (b, p)

def fillTerms (draw : κ × ι → ProbComp HashOutput) (p : ι)
    (order : List κ) (st : ShareState κ ι B) : ProbComp (ShareState κ ι B) :=
  order.foldlM (fun s b => fillTerm draw p b s) st

/-- Original implementation, parameterized by fresh reads and the slack answer. -/
def impl (order : List κ) (τ : ι → Digest)
    (draw : κ × ι → ProbComp HashOutput)
    (finish : κ → ι → Digest → ShareState κ ι (ImplBad Tag) → ProbComp HashOutput) :
    QueryImpl (ShareSpec κ ι Tag) (StateT (ShareState κ ι (ImplBad Tag)) ProbComp)
  | .read b p tag => fun st => match st.cache (b, p) with
    | some v => pure (v, st)
    | none => do
        let v ← draw (b, p)
        let st' := put st b p v
        let new := (setsBad order τ (.read b p tag) st).map
          (fun r => (r.1, r.2, decide (sum order st' p = τ p)))
        pure (v, { st' with bad := st.bad <|> new })
  | .complete p target tag => fun st => do
      if p ∈ st.done then
        pure (decide (sum order st p = target), st)
      else match slack order st p with
      | none => pure (decide (sum order st p = target),
          { st with bad := st.bad <|> some (tag, .complete, false) })
      | some b =>
          let st' ← fillTerms draw p (order.filter (· ≠ b)) st
          let v ← finish b p target st'
          let st'' := put st' b p v
          pure (true, { st'' with
            done := insert p st''.done
            bad := st.bad <|> (if target = τ p then none else some (tag, .complete, false)) })
  | .view => fun st => pure ((st.cache, st.done), st)

def lazyImpl (order : List κ) (τ : ι → Digest) :
    QueryImpl (ShareSpec κ ι Tag) (StateT (ShareState κ ι (ImplBad Tag)) ProbComp) :=
  impl order τ (fun _ => $ᵗ HashOutput) (fun b p target st =>
    (fun h => pair.symm (lowHash h, target ^^^ others order st p b)) <$> ($ᵗ HashOutput))

def eagerImpl (order : List κ) (τ : ι → Digest) (g : κ × ι → HashOutput) :
    QueryImpl (ShareSpec κ ι Tag) (StateT (ShareState κ ι (ImplBad Tag)) ProbComp) :=
  impl order τ (fun x => pure (g x)) (fun b p _ _ => pure (g (b, p)))

/-- Reintroducing a false lucky bit is used only to run a nonbad original step. -/
private def unerase (st : ShareState κ ι (FrozenBad Tag)) : ShareState κ ι (ImplBad Tag) :=
  ⟨st.cache, st.done, st.bad.map (fun b => (b.1, b.2, false))⟩

def frozen (order : List κ) (τ : ι → Digest)
    (original : QueryImpl (ShareSpec κ ι Tag)
      (StateT (ShareState κ ι (ImplBad Tag)) ProbComp)) :
    QueryImpl (ShareSpec κ ι Tag) (StateT (ShareState κ ι (FrozenBad Tag)) ProbComp) :=
  fun q st =>
    let bad := st.bad <|> setsBad order τ q st
    match bad with
    | some r => match q with
      | .read .. => pure ((0 : HashOutput), { st with bad := some r })
      | .complete .. => pure (false, { st with bad := some r })
      | .view => pure ((st.cache, st.done), { st with bad := some r })
    | none => (fun z => (z.1, erase z.2)) <$> (original q).run (unerase st)

def lazyFrozen (order : List κ) (τ : ι → Digest) :=
  frozen (Tag := Tag) order τ (lazyImpl order τ)

def eagerFrozen (order : List κ) (τ : ι → Digest) (g : κ × ι → HashOutput) :=
  frozen (Tag := Tag) order τ (eagerImpl order τ g)

/-- Completed points satisfy their constraint; unfinished points retain slack. -/
def Good (order : List κ) (τ : ι → Digest) (st : ShareState κ ι B) : Prop :=
  (∀ p ∈ st.done, (∀ b, st.cache (b, p) ≠ none) ∧ sum order st p = τ p) ∧
  (∀ p, p ∉ st.done → ∃ b, st.cache (b, p) = none)

/-- The sampled table remains private. Cached outputs take priority. -/
def fiberTable (order : List κ) (τ : ι → Digest) (st : ShareState κ ι B)
    (u : κ × ι → HashOutput) : κ × ι → HashOutput := fun (b, p) =>
  match st.cache (b, p) with
  | some v => v
  | none => if p ∉ st.done ∧ slack order st p = some b then
      pair.symm ((pair (u (b, p))).1,
        τ p ^^^ xorSum (order.filter (· ≠ b))
          (fun t => lowHash ((st.cache (t, p)).getD (u (t, p)))))
    else u (b, p)

/-- An empty cache has slack whenever there is a term, or no point needs slack. -/
theorem good_init (order : List κ) (τ : ι → Digest)
    (h : order ≠ [] ∨ IsEmpty ι) : Good order τ (init (κ := κ) (B := B)) := by
  refine ⟨by simp [init], ?_⟩
  intro p _
  rcases h with h | h
  · obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil order h
    exact ⟨b, rfl⟩
  · exact (h.false p).elim

/-- The empty-cache slack is the head of the chosen order. -/
theorem slack_init (order : List κ) (p : ι) (x : Option B) :
    slack order (init x) p = order.head? := by
  cases order <;> simp [slack, init]

/-- With a head term, only that term is constrained in the empty cache. -/
theorem fiberTable_init_cons (b₀ : κ) (rest : List κ) (τ : ι → Digest)
    (x : Option B) (u : κ × ι → HashOutput) (b : κ) (p : ι) :
    fiberTable (b₀ :: rest) τ (init x) u (b, p) =
      if b = b₀ then pair.symm ((pair (u (b₀, p))).1,
        τ p ^^^ xorSum ((b₀ :: rest).filter (· ≠ b₀)) (fun t => lowHash (u (t, p))))
      else u (b, p) := by
  by_cases h : b = b₀
  · subst b
    simp [fiberTable, slack, init]
  · simp [fiberTable, slack, init, h, Ne.symm h]

/-- With an empty order, the private table is just the visible-cache overlay. -/
theorem fiberTable_nil (τ : ι → Digest) (st : ShareState κ ι B)
    (u : κ × ι → HashOutput) :
    fiberTable [] τ st u = fun y => (st.cache y).getD (u y) := by
  funext y
  rcases y with ⟨b, p⟩
  cases h : st.cache (b, p) <;> simp [fiberTable, slack, h]


/-- The two-cell change of low halves used when reading the current slack. -/
def slackMove (target rest : Digest) : (HashOutput × HashOutput) ≃
    (HashOutput × HashOutput) where
  toFun w :=
    (pair.symm ((pair w.1).1, target ^^^ (pair w.2).2 ^^^ rest),
     pair.symm ((pair w.2).1, (pair w.1).2))
  invFun w :=
    (pair.symm ((pair w.1).1, (pair w.2).2),
     pair.symm ((pair w.2).1, target ^^^ (pair w.1).2 ^^^ rest))
  left_inv w := by
    apply Prod.ext <;> apply pair.injective <;>
      simp only [Equiv.apply_symm_apply] <;> apply Prod.ext <;>
      simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] <;>
      simp [BitVec.xor_assoc]
  right_inv w := by
    apply Prod.ext <;> apply pair.injective <;>
      simp only [Equiv.apply_symm_apply] <;> apply Prod.ext <;>
      simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] <;>
      simp [BitVec.xor_assoc]

/-- The adaptive two-cell change preserves uniform full hash outputs, including high halves. -/
theorem evalDist_slackMove (target rest : Digest) :
    𝒟[slackMove target rest <$> ($ᵗ (HashOutput × HashOutput))] =
      𝒟[$ᵗ (HashOutput × HashOutput)] :=
  evalDist_map_bijective_uniform_cross (HashOutput × HashOutput) _ (slackMove target rest).bijective

section UntilBad

variable {σ₁ σ₂ R α J : Type} {spec : OracleSpec J}

/-- Full output/state before bad, only the immutable first-bad record afterwards. -/
def observe (proj : σ₁ → σ₂) (bad : σ₂ → Option R) (z : α × σ₁) :
    (α × σ₂) ⊕ R :=
  match bad (proj z.2) with
  | none => .inl (z.1, proj z.2)
  | some r => .inr r

/-- Port of VCV-io `Relational/SimulateQ.lean:2965`, with the sticky record as predicate. -/
private theorem sticky_run
    (I : QueryImpl spec (StateT σ₁ ProbComp)) (bad : σ₁ → Option R)
    (sticky : ∀ q s r, bad s = some r →
      ∀ z ∈ support ((I q).run s), bad z.2 = some r)
    (oa : OracleComp spec α) (s : σ₁) (r : R) (h : bad s = some r) :
    ∀ z ∈ support ((simulateQ I oa).run s), bad z.2 = some r := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
      intro z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact h
  | query_bind q k ih =>
      intro z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, support_bind, Set.mem_iUnion,
        exists_prop] at hz
      obtain ⟨⟨a, s'⟩, hs', hz⟩ := hz
      exact ih a s' (sticky q s r h (a, s') hs') z hz

private theorem map_const_of_support {A D : Type} (oa : ProbComp A)
    (f : A → D) (d : D) (h : ∀ a ∈ support oa, f a = d) :
    𝒟[f <$> oa] = 𝒟[(pure d : ProbComp D)] := by
  rw [map_eq_bind_pure_comp]
  trans 𝒟[oa >>= fun _ => pure d]
  · exact evalDist_bind_congr fun a ha => by simp [Function.comp, h a ha]
  · exact DeferredSampling.evalDist_bind_const_neverFails oa (by simp) _

private theorem observe_sticky_run
    (I : QueryImpl spec (StateT σ₁ ProbComp)) (proj : σ₁ → σ₂)
    (bad : σ₂ → Option R)
    (sticky : ∀ q s r, bad (proj s) = some r →
      ∀ z ∈ support ((I q).run s), bad (proj z.2) = some r)
    (oa : OracleComp spec α) (s : σ₁) (r : R) (h : bad (proj s) = some r) :
    𝒟[observe proj bad <$> (simulateQ I oa).run s] =
      𝒟[(pure (.inr r) : ProbComp ((α × σ₂) ⊕ R))] := by
  apply map_const_of_support
  intro z hz
  have hz' : bad (proj z.2) = some r :=
    sticky_run I (bad ∘ proj) sticky oa s r h z hz
  simp [observe, hz']

/-- Projected identical-until-bad induction. Its one-step law retains all nonbad
observations and the first bad record. This ports the induction of VCV-io
`Relational/SimulateQ.lean:534–559,1140–1193` to two state types and Option-valued bad. -/
theorem untilBad_proj
    (I₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (I₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (proj : σ₁ → σ₂) (bad : σ₂ → Option R)
    (step : ∀ q s, bad (proj s) = none →
      𝒟[observe proj bad <$> (I₁ q).run s] =
        𝒟[observe id bad <$> (I₂ q).run (proj s)])
    (sticky₁ : ∀ q s r, bad (proj s) = some r →
      ∀ z ∈ support ((I₁ q).run s), bad (proj z.2) = some r)
    (sticky₂ : ∀ q s r, bad s = some r →
      ∀ z ∈ support ((I₂ q).run s), bad z.2 = some r)
    (oa : OracleComp spec α) (s : σ₁) :
    𝒟[observe proj bad <$> (simulateQ I₁ oa).run s] =
      𝒟[observe id bad <$> (simulateQ I₂ oa).run (proj s)] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp [observe]
  | query_bind q k ih =>
      cases hb : bad (proj s) with
      | some r =>
          rw [observe_sticky_run I₁ proj bad sticky₁ _ s r hb,
            observe_sticky_run I₂ id bad sticky₂ _ (proj s) r hb]
      | none =>
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
          let cont : (spec.Range q × σ₂) ⊕ R → ProbComp ((α × σ₂) ⊕ R) :=
            fun z => match z with
            | .inl (a, s') => observe id bad <$> (simulateQ I₂ (k a)).run s'
            | .inr r => pure (.inr r)
          have h₁ : ∀ z : spec.Range q × σ₁,
              𝒟[observe proj bad <$> (simulateQ I₁ (k z.1)).run z.2] =
                𝒟[cont (observe proj bad z)] := by
            intro z
            cases hz : bad (proj z.2) with
            | none => simpa [observe, hz, cont] using ih z.1 z.2
            | some r => simpa [observe, hz, cont] using
                observe_sticky_run I₁ proj bad sticky₁ (k z.1) z.2 r hz
          have h₂ : ∀ z : spec.Range q × σ₂,
              𝒟[observe id bad <$> (simulateQ I₂ (k z.1)).run z.2] =
                𝒟[cont (observe id bad z)] := by
            intro z
            cases hz : bad z.2 with
            | none => simp [observe, hz, cont]
            | some r => simpa [observe, hz, cont] using
                observe_sticky_run I₂ id bad sticky₂ (k z.1) z.2 r hz
          rw [evalDist_bind_congr' _ h₁, evalDist_bind_congr' _ h₂]
          calc
            _ = 𝒟[(observe proj bad <$> (I₁ q).run s) >>= cont] := by
              simp only [bind_map_left]
            _ = 𝒟[(observe id bad <$> (I₂ q).run (proj s)) >>= cont] := by
              rw [evalDist_bind, evalDist_bind, step q s hb]
            _ = _ := by simp only [bind_map_left]


end UntilBad


@[simp] theorem setsBad_erase (order : List κ) (τ : ι → Digest)
    (q : ShareQuery κ ι Tag) (st : ShareState κ ι (ImplBad Tag)) :
    setsBad order τ q (erase st) = setsBad order τ q st := by
  cases q <;> rfl

@[simp] theorem erase_bad_none (st : ShareState κ ι (ImplBad Tag)) :
    (erase st).bad = none ↔ st.bad = none := by simp [erase]

private theorem unerase_erase (st : ShareState κ ι (ImplBad Tag))
    (h : st.bad = none) : unerase (erase st) = st := by
  cases st
  simp_all [unerase, erase]

/-- The projection of the original record changes exactly according to the pre-state test. -/
theorem impl_bad_next (order : List κ) (τ : ι → Digest)
    (draw : κ × ι → ProbComp HashOutput)
    (finish : κ → ι → Digest → ShareState κ ι (ImplBad Tag) → ProbComp HashOutput)
    (q : ShareQuery κ ι Tag) (st : ShareState κ ι (ImplBad Tag)) :
    ∀ z ∈ support (((impl order τ draw finish) q).run st),
      (erase z.2).bad = ((erase st).bad <|> setsBad order τ q st) := by
  classical
  cases q with
  | read b p tag =>
      cases hc : st.cache (b, p) with
      | some v =>
          intro z hz
          simp only [impl, hc, StateT.run, support_pure, Set.mem_singleton_iff] at hz
          subst z
          simp [setsBad, hc]
      | none =>
          intro z hz
          simp only [impl, StateT.run, hc, support_bind, Set.mem_iUnion,
            exists_prop, support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨v, _, rfl⟩ := hz
          simp only [erase]
          cases st.bad <;> cases setsBad order τ (.read b p tag) st <;> rfl
  | complete p target tag =>
      by_cases hd : p ∈ st.done
      · intro z hz
        simp only [impl, StateT.run, hd, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
        subst z
        simp [setsBad, hd]
      · cases hs : slack order st p with
        | none =>
            intro z hz
            simp only [impl, StateT.run, hd, ↓reduceIte, hs, support_pure,
              Set.mem_singleton_iff] at hz
            subst z
            simp only [erase, setsBad, hd, hs, true_or, not_false_eq_true,
              and_self, ↓reduceIte]
            cases st.bad <;> rfl
        | some b =>
            intro z hz
            simp only [impl, StateT.run, hd, ↓reduceIte, hs, support_bind,
              Set.mem_iUnion, exists_prop, support_pure, Set.mem_singleton_iff] at hz
            obtain ⟨st', _, v, _, rfl⟩ := hz
            simp only [erase, setsBad, hd, hs, Option.some_ne_none, false_or,
              not_false_eq_true, true_and]
            by_cases ht : target = τ p <;> simp [ht] <;> cases st.bad <;> rfl
  | view =>
      intro z hz
      simp only [impl, StateT.run, support_pure, Set.mem_singleton_iff] at hz
      subst z
      simp [setsBad]

private theorem frozen_sticky (order : List κ) (τ : ι → Digest)
    (original : QueryImpl (ShareSpec κ ι Tag)
      (StateT (ShareState κ ι (ImplBad Tag)) ProbComp))
    (q : ShareQuery κ ι Tag) (st : ShareState κ ι (FrozenBad Tag)) (r : FrozenBad Tag)
    (h : st.bad = some r) :
    ∀ z ∈ support (((frozen order τ original) q).run st), z.2.bad = some r := by
  intro z hz
  cases q <;> simp [frozen, StateT.run, h] at hz <;> subst z <;> rfl

private theorem impl_frozen_step (order : List κ) (τ : ι → Digest)
    (draw : κ × ι → ProbComp HashOutput)
    (finish : κ → ι → Digest → ShareState κ ι (ImplBad Tag) → ProbComp HashOutput)
    (q : ShareQuery κ ι Tag) (st : ShareState κ ι (ImplBad Tag))
    (h : (erase st).bad = none) :
    𝒟[observe erase ShareState.bad <$> (impl order τ draw finish q).run st] =
      𝒟[observe id ShareState.bad <$>
        (frozen order τ (impl order τ draw finish) q).run (erase st)] := by
  have hb := (erase_bad_none st).mp h
  cases hs : setsBad order τ q st with
  | none =>
      simp only [frozen, StateT.run, h, setsBad_erase, hs, Option.orElse_eq_orElse, Option.orElse,
        unerase_erase st hb, Functor.map_map]
      rfl
  | some r =>
      have hl : 𝒟[observe erase ShareState.bad <$> (impl order τ draw finish q).run st] =
          𝒟[(pure (.inr r) : ProbComp (((ShareSpec κ ι Tag).Range q ×
            ShareState κ ι (FrozenBad Tag)) ⊕ FrozenBad Tag))] := by
        apply map_const_of_support
        intro z hz
        have hz' := impl_bad_next order τ draw finish q st z hz
        simp only [h, hs, Option.orElse] at hz'
        simp [observe, hz']
      rw [hl]
      cases q <;> simp [frozen, StateT.run, h, setsBad_erase, hs, observe]

/-- Full stopped-observation equality for the original and frozen handlers. -/
theorem impl_frozen_observe (order : List κ) (τ : ι → Digest)
    (draw : κ × ι → ProbComp HashOutput)
    (finish : κ → ι → Digest → ShareState κ ι (ImplBad Tag) → ProbComp HashOutput)
    {α : Type} (oa : OracleComp (ShareSpec κ ι Tag) α)
    (st : ShareState κ ι (ImplBad Tag)) :
    𝒟[observe erase ShareState.bad <$> (simulateQ (impl order τ draw finish) oa).run st] =
      𝒟[observe id ShareState.bad <$>
        (simulateQ (frozen order τ (impl order τ draw finish)) oa).run (erase st)] := by
  apply untilBad_proj _ _ erase ShareState.bad
  · exact impl_frozen_step order τ draw finish
  · intro q s r hr z hz
    rw [impl_bad_next order τ draw finish q s z hz, hr]
    rfl
  · exact frozen_sticky order τ (impl order τ draw finish)


/-- Uniform queries preserve the visible share state. -/
def unifImpl (σ : Type) : QueryImpl unifSpec (StateT σ ProbComp) :=
  fun n st => (fun a => (a, st)) <$> ($[0..n])

/-- The stopped law includes independent uniform queries in the caller. -/
theorem impl_frozen_observe_uniform (order : List κ) (τ : ι → Digest)
    (draw : κ × ι → ProbComp HashOutput)
    (finish : κ → ι → Digest → ShareState κ ι (ImplBad Tag) → ProbComp HashOutput)
    {α : Type} (oa : OracleComp (unifSpec + ShareSpec κ ι Tag) α)
    (st : ShareState κ ι (ImplBad Tag)) :
    𝒟[observe erase ShareState.bad <$>
      (simulateQ (unifImpl (ShareState κ ι (ImplBad Tag)) + impl order τ draw finish) oa).run st] =
      𝒟[observe id ShareState.bad <$>
        (simulateQ (unifImpl (ShareState κ ι (FrozenBad Tag)) + frozen order τ (impl order τ draw finish)) oa).run (erase st)] := by
  apply untilBad_proj _ _ erase ShareState.bad
  · intro q s hs
    cases q with
    | inl n => simp [unifImpl, StateT.run, Functor.map_map, observe]
    | inr q => exact impl_frozen_step order τ draw finish q s hs
  · intro q s r hr z hz
    cases q with
    | inl n =>
        obtain ⟨a, _, rfl⟩ := mem_support_map_peel (fun a : Fin (n + 1) => (a, s))
          ($[0..n]) hz
        exact hr
    | inr q =>
        rw [impl_bad_next order τ draw finish q s z hz, hr]
        rfl
  · intro q s r hr z hz
    cases q with
    | inl n =>
        obtain ⟨a, _, rfl⟩ := mem_support_map_peel (fun a : Fin (n + 1) => (a, s))
          ($[0..n]) hz
        exact hr
    | inr q => exact frozen_sticky order τ _ q s r hr z hz

private theorem probEvent_of_observe_eq {σ₁ σ₂ R α : Type}
    (proj : σ₁ → σ₂) (bad : σ₂ → Option R)
    (oa : ProbComp (α × σ₁)) (ob : ProbComp (α × σ₂))
    (h : 𝒟[observe proj bad <$> oa] = 𝒟[observe id bad <$> ob])
    (P : ((α × σ₂) ⊕ R) → Prop) :
    Pr[P ∘ observe proj bad | oa] = Pr[P ∘ observe id bad | ob] := by
  rw [← probEvent_map, ← probEvent_map, probEvent_def, probEvent_def, h]

/-- Nonbad observations retain the complete result and projected final state. -/
theorem impl_frozen_nonbad (order : List κ) (τ : ι → Digest)
    (draw : κ × ι → ProbComp HashOutput)
    (finish : κ → ι → Digest → ShareState κ ι (ImplBad Tag) → ProbComp HashOutput)
    {α : Type} (oa : OracleComp (unifSpec + ShareSpec κ ι Tag) α)
    (st : ShareState κ ι (ImplBad Tag)) (G : α × ShareState κ ι (FrozenBad Tag) → Prop) :
    Pr[fun z => G (z.1, erase z.2) ∧ z.2.bad = none |
      (simulateQ (unifImpl (ShareState κ ι (ImplBad Tag)) + impl order τ draw finish) oa).run st] =
      Pr[fun z => G z ∧ z.2.bad = none |
        (simulateQ (unifImpl (ShareState κ ι (FrozenBad Tag)) + frozen order τ (impl order τ draw finish)) oa).run (erase st)] := by
  let P : ((α × ShareState κ ι (FrozenBad Tag)) ⊕ FrozenBad Tag) → Prop :=
    fun z => match z with | .inl y => G y | .inr _ => False
  have h := probEvent_of_observe_eq erase ShareState.bad _ _
    (impl_frozen_observe_uniform order τ draw finish oa st) P
  have h₁ : P ∘ observe erase ShareState.bad =
      (fun z : α × ShareState κ ι (ImplBad Tag) => G (z.1, erase z.2) ∧ z.2.bad = none) := by
    funext z
    cases hb : z.2.bad <;> simp [Function.comp_def, observe, erase, hb, P]
  have h₂ : P ∘ observe id ShareState.bad =
      (fun z : α × ShareState κ ι (FrozenBad Tag) => G z ∧ z.2.bad = none) := by
    funext z
    cases hb : z.2.bad <;> simp [Function.comp_def, observe, hb, P]
  rwa [h₁, h₂] at h

/-- First-bad tag and kind have the same law, without transporting lucky. -/
theorem impl_frozen_firstbad (order : List κ) (τ : ι → Digest)
    (draw : κ × ι → ProbComp HashOutput)
    (finish : κ → ι → Digest → ShareState κ ι (ImplBad Tag) → ProbComp HashOutput)
    {α : Type} (oa : OracleComp (unifSpec + ShareSpec κ ι Tag) α)
    (st : ShareState κ ι (ImplBad Tag)) (r : FrozenBad Tag) :
    Pr[fun z => (erase z.2).bad = some r |
      (simulateQ (unifImpl (ShareState κ ι (ImplBad Tag)) + impl order τ draw finish) oa).run st] =
      Pr[fun z => z.2.bad = some r |
        (simulateQ (unifImpl (ShareState κ ι (FrozenBad Tag)) + frozen order τ (impl order τ draw finish)) oa).run (erase st)] := by
  let P : ((α × ShareState κ ι (FrozenBad Tag)) ⊕ FrozenBad Tag) → Prop :=
    fun z => match z with | .inl _ => False | .inr r' => r' = r
  have h := probEvent_of_observe_eq erase ShareState.bad _ _
    (impl_frozen_observe_uniform order τ draw finish oa st) P
  have h₁ : P ∘ observe erase ShareState.bad =
      (fun z : α × ShareState κ ι (ImplBad Tag) => (erase z.2).bad = some r) := by
    funext z
    cases hb : (erase z.2).bad <;> simp [Function.comp_def, observe, hb, P]
  have h₂ : P ∘ observe id ShareState.bad =
      (fun z : α × ShareState κ ι (FrozenBad Tag) => z.2.bad = some r) := by
    funext z
    cases hb : z.2.bad <;> simp [Function.comp_def, observe, hb, P]
  rwa [h₁, h₂] at h


private theorem xor_left_comm (a b c : Digest) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

private theorem xorSum_congr (order : List κ) (f g : κ → Digest)
    (h : ∀ b ∈ order, f b = g b) : xorSum order f = xorSum order g := by
  induction order with
  | nil => rfl
  | cons b rest ih =>
      change f b ^^^ xorSum rest f = g b ^^^ xorSum rest g
      rw [h b (by simp), ih (fun t ht => h t (by simp [ht]))]

private theorem xorSum_filter_of_not_mem (order : List κ) (f : κ → Digest) (b : κ)
    (h : b ∉ order) : xorSum (order.filter (· ≠ b)) f = xorSum order f := by
  congr 1
  apply List.filter_eq_self.mpr
  intro t ht
  simp only [decide_eq_true_eq]
  intro he
  subst t
  exact h ht

/-- Splitting a distinct ordered XOR at one term. -/
theorem xorSum_split (order : List κ) (hn : order.Nodup) (f : κ → Digest)
    (b : κ) (hb : b ∈ order) :
    xorSum order f = f b ^^^ xorSum (order.filter (· ≠ b)) f := by
  induction order with
  | nil => simp at hb
  | cons a rest ih =>
      obtain ⟨ha, hn⟩ := List.nodup_cons.mp hn
      by_cases hab : a = b
      · subst a
        simpa only [xorSum, List.foldr_cons, List.filter_cons, ne_eq,
          not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] using
            congrArg (fun x => f b ^^^ x) (xorSum_filter_of_not_mem rest f b ha).symm
      · have hb' : b ∈ rest := (List.mem_cons.mp hb).resolve_left (Ne.symm hab)
        simp only [xorSum, List.foldr_cons]
        change f a ^^^ xorSum rest f = _
        rw [ih hn hb']
        simp only [List.filter_cons, hab, ne_eq, not_false_eq_true, decide_true,
          ↓reduceIte, xorSum, List.foldr_cons]
        exact xor_left_comm _ _ _

/-- Replacing one full output changes the aggregate by its low half only. -/
theorem sum_put (order : List κ) (hn : order.Nodup) (b : κ) (hb : b ∈ order)
    (st : ShareState κ ι B) (p : ι) (v : HashOutput) :
    sum order (put st b p v) p = lowHash v ^^^ others order st p b := by
  rw [sum, xorSum_split order hn _ b hb]
  simp only [low, put, Function.update_self, Option.getD_some]
  congr 1
  apply xorSum_congr
  intro t ht
  have ht' : t ≠ b := by simpa using (List.mem_filter.mp ht).2
  simp [Function.update, ht', low]

/-- A fresh output has a uniform aggregate after every fixed set of other shares. -/
theorem evalDist_sum_put (order : List κ) (hn : order.Nodup) (b : κ) (hb : b ∈ order)
    (st : ShareState κ ι B) (p : ι) :
    𝒟[(fun v => sum order (put st b p v) p) <$> ($ᵗ HashOutput)] = 𝒟[$ᵗ Digest] := by
  simp_rw [sum_put order hn b hb]
  calc
    _ = 𝒟[(fun d => d ^^^ others order st p b) <$> (lowHash <$> ($ᵗ HashOutput))] := by
      rw [Functor.map_map]
    _ = 𝒟[(fun d => d ^^^ others order st p b) <$> ($ᵗ Digest)] := by
      rw [evalDist_map, XmssSecurity.Rom.evalDist_truncate_uniformHashOutput, ← evalDist_map]
    _ = _ := by

      apply evalDist_map_bijective_uniform_cross Digest
      refine ⟨fun a b h => (BitVec.xor_left_inj _).mp h, fun a => ?_⟩
      exact ⟨a ^^^ others order st p b, by simp [BitVec.xor_assoc]⟩

/-- Original records, including lucky, are sticky. -/
private theorem impl_sticky (order : List κ) (τ : ι → Digest)
    (draw : κ × ι → ProbComp HashOutput)
    (finish : κ → ι → Digest → ShareState κ ι (ImplBad Tag) → ProbComp HashOutput)
    (q : ShareQuery κ ι Tag) (st : ShareState κ ι (ImplBad Tag)) (r : ImplBad Tag)
    (h : st.bad = some r) :
    ∀ z ∈ support (((impl order τ draw finish) q).run st), z.2.bad = some r := by
  cases q with
  | read b p tag =>
      cases hc : st.cache (b, p) with
      | some v =>
          intro z hz
          simp only [impl, hc, StateT.run, support_pure, Set.mem_singleton_iff] at hz
          subst z
          exact h
      | none =>
          intro z hz
          simp only [impl, StateT.run, hc, support_bind, Set.mem_iUnion,
            exists_prop, support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨v, _, rfl⟩ := hz
          simp [h]
  | complete p target tag =>
      by_cases hd : p ∈ st.done
      · intro z hz
        simp only [impl, StateT.run, hd, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
        subst z
        exact h
      · cases hs : slack order st p with
        | none =>
            intro z hz
            simp only [impl, StateT.run, hd, ↓reduceIte, hs, support_pure,
              Set.mem_singleton_iff] at hz
            subst z
            simp [h]
        | some b =>
            intro z hz
            simp only [impl, StateT.run, hd, ↓reduceIte, hs, support_bind,
              Set.mem_iUnion, exists_prop, support_pure, Set.mem_singleton_iff] at hz
            obtain ⟨st', _, v, _, rfl⟩ := hz
            simp [h]
  | view =>
      intro z hz
      simp only [impl, StateT.run, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact h


section Ratio

variable {σ R J α : Type} {spec : OracleSpec J}

private theorem sticky_prob
    (I : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Option R)
    (sticky : ∀ q s r, bad s = some r → ∀ z ∈ support ((I q).run s), bad z.2 = some r)
    (oa : OracleComp spec α) (s : σ) (r r' : R) (h : bad s = some r') :
    Pr[fun z => bad z.2 = some r | (simulateQ I oa).run s] =
      if r' = r then 1 else 0 := by
  classical
  have hm : 𝒟[(fun z => bad z.2) <$> (simulateQ I oa).run s] =
      𝒟[(pure (some r') : ProbComp (Option R))] :=
    map_const_of_support _ _ _ (sticky_run I bad sticky oa s r' h)
  calc
    _ = Pr[fun x => x = some r | (fun z => bad z.2) <$> (simulateQ I oa).run s] := by
      rw [probEvent_map]; rfl
    _ = Pr[fun x => x = some r | (pure (some r') : ProbComp (Option R))] := by
      rw [probEvent_def, probEvent_def, hm]
    _ = _ := by simp [eq_comm]

/-- Splitting the next step into its first-bad mass and its nonbad continuation mass. -/
private theorem sticky_split
    (I : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Option R)
    (sticky : ∀ q s r, bad s = some r → ∀ z ∈ support ((I q).run s), bad z.2 = some r)
    (q : spec.Domain) (k : spec.Range q → OracleComp spec α) (s : σ) (r : R) :
    Pr[fun z => bad z.2 = some r |
      (I q).run s >>= fun y => (simulateQ I (k y.1)).run y.2] =
      Pr[fun z => bad z.2 = some r | (I q).run s] +
      ∑' y, Pr[= y | (I q).run s] *
        (if bad y.2 = none then
          Pr[fun z => bad z.2 = some r | (simulateQ I (k y.1)).run y.2] else 0) := by
  classical
  letI : DecidableEq R := Classical.decEq R
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro y
  cases hb : bad y.2 with
  | none => simp [hb]
  | some r' =>
      rw [sticky_prob (ι := Unit) I bad sticky (k y.1) y.2 r r' hb]
      simp only [hb, Option.some.injEq, Option.some_ne_none, ↓reduceIte,
        mul_zero, add_zero]
      split <;> simp_all only [mul_one, mul_zero, ↓reduceIte]

/-- A local ratio for a sticky first-bad record persists through adaptive calls. -/
theorem sticky_ratio
    (I : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Option R)
    (sticky : ∀ q s r, bad s = some r → ∀ z ∈ support ((I q).run s), bad z.2 = some r)
    (r₀ r₁ : R) (c : ENNReal)
    (step : ∀ q s, bad s = none →
      Pr[fun z => bad z.2 = some r₀ | (I q).run s] =
        c * Pr[fun z => bad z.2 = some r₁ | (I q).run s])
    (oa : OracleComp spec α) (s : σ) (hs : bad s = none) :
    Pr[fun z => bad z.2 = some r₀ | (simulateQ I oa).run s] =
      c * Pr[fun z => bad z.2 = some r₁ | (simulateQ I oa).run s] := by
  classical
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp [hs]
  | query_bind q k ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      rw [sticky_split I bad sticky q k s r₀, sticky_split I bad sticky q k s r₁,
        step q s hs, mul_add, ← ENNReal.tsum_mul_left]
      congr 1
      apply tsum_congr
      intro y
      by_cases hy : bad y.2 = none
      · simp only [hy, ↓reduceIte, ih y.1 y.2 hy]
        ac_rfl
      · simp [hy]

end Ratio


private theorem uniform_digest_ratio (target : Digest) :
    Pr[fun d => d ≠ target | $ᵗ Digest] =
      (Fintype.card Digest - 1 : ℕ) * Pr[fun d => d = target | $ᵗ Digest] := by
  rw [probEvent_uniformSample, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, probEvent_eq_eq_probOutput, probOutput_uniformSample, div_eq_mul_inv]

private theorem lazy_step_ratio (order : List κ) (hn : order.Nodup)
    (hcover : ∀ b, b ∈ order) (τ : ι → Digest)
    (q : ShareQuery κ ι Tag) (st : ShareState κ ι (ImplBad Tag))
    (hs : st.bad = none) (t : Tag) :
    Pr[fun z => z.2.bad = some (t, Kind.read, false) | (lazyImpl order τ q).run st] =
      (Fintype.card Digest - 1 : ℕ) *
        Pr[fun z => z.2.bad = some (t, Kind.read, true) | (lazyImpl order τ q).run st] := by
  classical
  cases q with
  | read b p tag =>
      cases hc : st.cache (b, p) with
      | some v => simp [lazyImpl, impl, StateT.run, hc, hs]
      | none =>
          by_cases hbad : p ∉ st.done ∧ ∀ a ∈ order, a ≠ b → st.cache (a, p) ≠ none
          · by_cases htag : tag = t
            · subst tag
              simp only [lazyImpl, impl, StateT.run, hc, setsBad, hbad.1, hbad.2,
                true_and, and_true, not_false_eq_true, ↓reduceIte, Option.map_some,
                hs, Option.orElse_eq_orElse, Option.orElse, probEvent_bind_eq_tsum,
                probEvent_pure, Option.some.injEq, Prod.mk.injEq, true_and,
                decide_eq_false_iff_not, decide_eq_true_eq]
              simp only [if_pos hbad.2, Option.map_some, Option.some.injEq,
                Prod.mk.injEq, true_and, decide_eq_false_iff_not, decide_eq_true_eq]
              have he := evalDist_sum_put order hn b (hcover b) st p
              have hp (P : Digest → Prop) :
                  Pr[P ∘ (fun v => sum order (put st b p v) p) | $ᵗ HashOutput] =
                    Pr[P | $ᵗ Digest] := by
                rw [← probEvent_map, probEvent_def, probEvent_def, he]
              have hf := hp (fun d => d ≠ τ p)
              have ht := hp (fun d => d = τ p)
              rw [probEvent_eq_tsum_ite] at hf ht
              simpa only [Function.comp_def, mul_ite, mul_one, mul_zero, ne_eq] using
                hf.trans ((uniform_digest_ratio (τ p)).trans (congrArg _ ht.symm))
            · simp [lazyImpl, impl, StateT.run, hc, setsBad, hs, hbad, htag]
          · have htest : setsBad order τ (.read b p tag) st = none := by
              simp [setsBad, hc, hbad]
            simp [lazyImpl, impl, StateT.run, hc, hs, htest]
  | complete p target tag =>
      have hzero (luck : Bool) :
          Pr[fun z => z.2.bad = some (t, Kind.read, luck) |
            (lazyImpl order τ (.complete p target tag)).run st] = 0 := by
        apply probEvent_eq_zero_iff.mpr
        intro z hz he
        have hz' := impl_bad_next order τ (fun _ => $ᵗ HashOutput)
          (fun b p target st =>
            (fun h => pair.symm (lowHash h, target ^^^ others order st p b)) <$> ($ᵗ HashOutput))
          (.complete p target tag) st z hz
        simp only [erase, hs, he, Option.map_none, Option.map_some,
          Option.orElse_eq_orElse, Option.orElse] at hz'
        simp only [setsBad] at hz'
        split at hz' <;> simp_all
      rw [hzero false, hzero true, mul_zero]
  | view => simp [lazyImpl, impl, StateT.run, hs]

/-- The lucky ratio belongs only to the original lazy implementation. -/
theorem lazy_lucky_ratio (order : List κ) (hn : order.Nodup)
    (hcover : ∀ b, b ∈ order) (τ : ι → Digest)
    {α : Type} (oa : OracleComp (unifSpec + ShareSpec κ ι Tag) α)
    (st : ShareState κ ι (ImplBad Tag)) (hs : st.bad = none) (t : Tag) :
    Pr[fun z => z.2.bad = some (t, Kind.read, false) |
      (simulateQ (unifImpl (ShareState κ ι (ImplBad Tag)) + lazyImpl (Tag := Tag) order τ) oa).run st] =
      (Fintype.card Digest - 1 : ℕ) *
        Pr[fun z => z.2.bad = some (t, Kind.read, true) |
          (simulateQ (unifImpl (ShareState κ ι (ImplBad Tag)) + lazyImpl (Tag := Tag) order τ) oa).run st] := by
  apply sticky_ratio _ ShareState.bad _ _ _ _ _ oa st hs
  · intro q s r hr z hz
    cases q with
    | inl n =>
        obtain ⟨a, _, rfl⟩ := mem_support_map_peel (fun a : Fin (n + 1) => (a, s)) ($[0..n]) hz
        exact hr
    | inr q =>
        exact impl_sticky order τ (fun _ => $ᵗ HashOutput)
          (fun b p target st =>
            (fun h => pair.symm (lowHash h, target ^^^ others order st p b)) <$> ($ᵗ HashOutput))
          q s r hr z hz
  · intro q s hs
    cases q with
    | inl n => simp [unifImpl, StateT.run, probEvent_map, Function.comp_def, hs]
    | inr q => exact lazy_step_ratio order hn hcover τ q s hs t


@[simp] theorem lowHash_pair (hi lo : Digest) : lowHash (pair.symm (hi, lo)) = lo :=
  congrArg Prod.snd (pair.apply_symm_apply (hi, lo))

/-- The visible cache is always the first case of the private table. -/
theorem fiberTable_cached (order : List κ) (τ : ι → Digest)
    (st : ShareState κ ι B) (u : κ × ι → HashOutput) (b : κ) (p : ι) (v : HashOutput)
    (h : st.cache (b, p) = some v) : fiberTable order τ st u (b, p) = v := by
  simp [fiberTable, h]

private theorem slack_some (order : List κ) (st : ShareState κ ι B) (p : ι) (b : κ)
    (h : slack order st p = some b) : b ∈ order ∧ st.cache (b, p) = none := by
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

private theorem slack_none (order : List κ) (st : ShareState κ ι B) (p : ι) :
    slack order st p = none ↔ ∀ b ∈ order, st.cache (b, p) ≠ none := by
  simp [slack, List.find?_eq_none]

private theorem good_slack (order : List κ) (hcover : ∀ b, b ∈ order) (τ : ι → Digest)
    (st : ShareState κ ι B) (hgood : Good order τ st) (p : ι) (hp : p ∉ st.done) :
    ∃ b, slack order st p = some b := by
  obtain ⟨b, hb⟩ := hgood.2 p hp
  cases h : slack order st p with
  | none => exact ((slack_none order st p).mp h b (hcover b) hb).elim
  | some b => exact ⟨b, rfl⟩

private theorem slack_put_other (order : List κ) (st : ShareState κ ι B)
    (b : κ) (p p' : ι) (v : HashOutput) (h : p' ≠ p) :
    slack order (put st b p v) p' = slack order st p' := by
  unfold slack
  congr 1
  funext a
  simp [put, Function.update, h]

/-- Materializing a different share leaves the current slack unchanged. -/
private theorem slack_put_ne (order : List κ) (st : ShareState κ ι B)
    (a b : κ) (p : ι) (v : HashOutput) (hab : a ≠ b)
    (hs : slack order st p = some b) : slack order (put st a p v) p = some b := by
  obtain ⟨hb, left, right, horder, hleft⟩ := List.find?_eq_some_iff_append.mp hs
  apply List.find?_eq_some_iff_append.mpr
  refine ⟨?_, left, right, horder, ?_⟩
  · simpa [put, Function.update, Ne.symm hab] using hb
  · intro c hc
    by_cases he : c = a
    · simp [put, Function.update, he]
    · simpa [put, Function.update, he] using hleft c hc

/-- With no first-bad read, a fresh read leaves another uncached share. -/
private theorem good_put (order : List κ) (hcover : ∀ b, b ∈ order) (τ : ι → Digest)
    (st : ShareState κ ι B) (hg : Good order τ st) (b : κ) (p : ι) (v : HashOutput)
    (hc : st.cache (b, p) = none) (tag : Tag)
    (hs : setsBad order τ (.read b p tag) st = none) : Good order τ (put st b p v) := by
  have hp : p ∉ st.done := fun h => (hg.1 p h).1 b hc
  have ho : ∃ a ∈ order, a ≠ b ∧ st.cache (a, p) = none := by
    have hn : ¬∀ a ∈ order, a ≠ b → st.cache (a, p) ≠ none := by
      intro ha
      have hbad : st.cache (b, p) = none ∧ p ∉ st.done ∧
          ∀ a ∈ order, a ≠ b → st.cache (a, p) ≠ none := ⟨hc, hp, ha⟩
      simp only [setsBad, if_pos hbad, Option.some_ne_none] at hs
    push Not at hn
    exact hn
  refine ⟨?_, ?_⟩
  · intro p' hp'
    have hpp : p' ≠ p := by intro he; subst p'; exact hp hp'
    refine ⟨?_, ?_⟩
    · intro a
      simpa [put, Function.update, hpp] using (hg.1 p' hp').1 a
    · rw [sum]
      have he : (fun a => low (put st b p v) a p') = fun a => low st a p' := by
        funext a
        simp [low, put, Function.update, hpp]
      rw [he]
      exact (hg.1 p' hp').2
  · intro p' hp'
    by_cases hpp : p' = p
    · subst p'
      obtain ⟨a, _, hab, ha⟩ := ho
      exact ⟨a, by simp [put, Function.update, hab, ha]⟩
    · obtain ⟨a, ha⟩ := hg.2 p' hp'
      exact ⟨a, by simp [put, Function.update, hpp, ha]⟩

/-- Programming the low half at one absent slack enforces the row constraint. -/
theorem fiberTable_sum (order : List κ) (hn : order.Nodup) (hcover : ∀ b, b ∈ order)
    (τ : ι → Digest) (st : ShareState κ ι B) (hg : Good order τ st)
    (u : κ × ι → HashOutput) (p : ι) :
    xorSum order (fun b => lowHash (fiberTable order τ st u (b, p))) = τ p := by
  by_cases hp : p ∈ st.done
  · have hf : ∀ b ∈ order, lowHash (fiberTable order τ st u (b, p)) = low st b p := by
      intro b _
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((hg.1 p hp).1 b)
      simp [fiberTable, low, hv]
    rw [xorSum_congr order _ _ hf]
    exact (hg.1 p hp).2
  · obtain ⟨b, hb⟩ := good_slack order hcover τ st hg p hp
    obtain ⟨hbm, hbc⟩ := slack_some order st p b hb
    rw [xorSum_split order hn _ b hbm]
    have hrest : xorSum (order.filter (· ≠ b))
        (fun a => lowHash (fiberTable order τ st u (a, p))) =
        xorSum (order.filter (· ≠ b)) (fun a => lowHash ((st.cache (a, p)).getD (u (a, p)))) := by
      apply xorSum_congr
      intro a ha
      have hab : a ≠ b := by simpa using (List.mem_filter.mp ha).2
      cases hc : st.cache (a, p) <;> simp [fiberTable, hc, hp, hb, Ne.symm hab]
    rw [hrest]
    simp [fiberTable, hbc, hp, hb, BitVec.xor_assoc]


def extend (st : ShareState κ ι B) (u : κ × ι → HashOutput) : κ × ι → HashOutput :=
  fun y => (st.cache y).getD (u y)

/-- The first-absent test already excludes all cached coordinates. -/
private theorem fiberTable_eq (order : List κ) (τ : ι → Digest)
    (st : ShareState κ ι B) (u : κ × ι → HashOutput) (b : κ) (p : ι) :
    fiberTable order τ st u (b, p) =
      if p ∉ st.done ∧ slack order st p = some b then
        pair.symm ((pair (u (b, p))).1,
          τ p ^^^ xorSum (order.filter (· ≠ b)) (fun t => lowHash (extend st u (t, p))))
      else extend st u (b, p) := by
  cases hc : st.cache (b, p) with
  | none => simp [fiberTable, extend, hc]
  | some v =>
      have hs : slack order st p ≠ some b := by
        intro h
        have hh := (slack_some order st p b h).2
        simp [hc] at hh
      simp [fiberTable, extend, hc, hs]

private theorem extend_put (st : ShareState κ ι B) (u : κ × ι → HashOutput)
    (a : κ) (p : ι) (v : HashOutput) (hc : st.cache (a, p) = none) :
    extend (put st a p v) u = extend st (Function.update u (a, p) v) := by
  funext y
  by_cases hy : y = (a, p)
  · subst y
    simp [extend, put, hc]
  · simp [extend, put, Function.update, hy]

/-- One-cell absorption when the fresh read is not the current slack. -/
private theorem fiberTable_put_ne (order : List κ) (τ : ι → Digest)
    (st : ShareState κ ι B) (u : κ × ι → HashOutput) (a b : κ) (p : ι) (v : HashOutput)
    (hc : st.cache (a, p) = none) (hab : a ≠ b) (hs : slack order st p = some b) :
    fiberTable order τ (put st a p v) u = fiberTable order τ st (Function.update u (a, p) v) := by
  have hsl : ∀ p', slack order (put st a p v) p' = slack order st p' := by
    intro p'
    by_cases hpp : p' = p
    · subst p'
      rw [slack_put_ne order st a b p v hab hs, hs]
    · exact slack_put_other order st a p p' v hpp
  funext y
  rcases y with ⟨t, p'⟩
  rw [fiberTable_eq, fiberTable_eq, extend_put st u a p v hc]
  rw [hsl p']
  simp only [put]
  by_cases hy : (t, p') = (a, p)
  · rcases Prod.mk.inj hy with ⟨rfl, rfl⟩
    simp [hs, Ne.symm hab]
  · simp [Function.update, hy]

/-- The unsampled non-slack coordinate is an ordinary independent table entry. -/
private theorem fiberTable_fresh_ne (order : List κ) (τ : ι → Digest)
    (st : ShareState κ ι B) (u : κ × ι → HashOutput) (a b : κ) (p : ι)
    (hc : st.cache (a, p) = none) (hab : a ≠ b) (hs : slack order st p = some b) :
    fiberTable order τ st u (a, p) = u (a, p) := by
  simp [fiberTable, hc, hs, Ne.symm hab]

/-- Distributional read absorption at a non-slack coordinate, retaining the whole private table. -/
private theorem read_table_ne [Finite κ] [Finite ι] [SampleableType (κ × ι → HashOutput)]
    (order : List κ) (τ : ι → Digest) (st : ShareState κ ι B)
    (a b : κ) (p : ι) (hc : st.cache (a, p) = none)
    (hab : a ≠ b) (hs : slack order st p = some b) :
    𝒟[do let v ← $ᵗ HashOutput
         let u ← $ᵗ (κ × ι → HashOutput)
         pure (v, fiberTable order τ (put st a p v) u)] =
      𝒟[do let u ← $ᵗ (κ × ι → HashOutput)
           pure (fiberTable order τ st u (a, p), fiberTable order τ st u)] := by
  let ψ : (κ × ι → HashOutput) → HashOutput × (κ × ι → HashOutput) :=
    fun u => (u (a, p), fiberTable order τ st u)
  have hm := evalDist_uniformSample_bind_update_map (a, p) ψ
  simpa only [ψ, Function.update_self, fiberTable_put_ne order τ st _ a b p _ hc hab hs,
    fiberTable_fresh_ne order τ st _ a b p hc hab hs] using hm


/-- Characterization of a constrained table relative to its unused randomness. -/
def TableCompatible (order : List κ) (τ : ι → Digest) (st : ShareState κ ι B)
    (u g : κ × ι → HashOutput) : Prop :=
  (∀ b p v, st.cache (b, p) = some v → g (b, p) = v) ∧
  (∀ p, xorSum order (fun b => lowHash (g (b, p))) = τ p) ∧
  (∀ b p, st.cache (b, p) = none → (pair (g (b, p))).1 = (pair (u (b, p))).1) ∧
  (∀ b p, st.cache (b, p) = none → slack order st p ≠ some b → g (b, p) = u (b, p))

private theorem fiberTable_compatible (order : List κ) (hn : order.Nodup)
    (hcover : ∀ b, b ∈ order) (τ : ι → Digest) (st : ShareState κ ι B)
    (hg : Good order τ st) (u : κ × ι → HashOutput) :
    TableCompatible order τ st u (fiberTable order τ st u) := by
  refine ⟨fiberTable_cached order τ st u, fiberTable_sum order hn hcover τ st hg u, ?_, ?_⟩
  · intro b p hc
    simp only [fiberTable, hc]
    split <;> simp
  · intro b p hc hs
    simp [fiberTable, hc, hs]

/-- Cache agreement, the row constraint and unused coordinates uniquely determine the fiber. -/
private theorem fiberTable_unique (order : List κ) (hn : order.Nodup)
    (τ : ι → Digest) (st : ShareState κ ι B) (hg : Good order τ st)
    (u g : κ × ι → HashOutput) (h : TableCompatible order τ st u g) :
    fiberTable order τ st u = g := by
  funext y
  rcases y with ⟨b, p⟩
  cases hc : st.cache (b, p) with
  | some v => rw [fiberTable_cached order τ st u b p v hc, h.1 b p v hc]
  | none =>
      have hp : p ∉ st.done := fun hp => (hg.1 p hp).1 b hc
      by_cases hs : slack order st p = some b
      · have hbm := (slack_some order st p b hs).1
        have ho : xorSum (order.filter (· ≠ b)) (fun t => lowHash (extend st u (t, p))) =
            xorSum (order.filter (· ≠ b)) (fun t => lowHash (g (t, p))) := by
          apply xorSum_congr
          intro t ht
          have htb : t ≠ b := by simpa using (List.mem_filter.mp ht).2
          cases htcache : st.cache (t, p) with
          | some v => simp [extend, htcache, h.1 t p v htcache]
          | none =>
              have hts : slack order st p ≠ some t := by simpa [hs] using Ne.symm htb
              simp [extend, htcache, h.2.2.2 t p htcache hts]
        rw [fiberTable_eq, if_pos ⟨hp, hs⟩, ho]
        apply pair.injective
        rw [pair.apply_symm_apply]
        apply Prod.ext
        · exact (h.2.2.1 b p hc).symm
        · have hsum := h.2.1 p
          rw [xorSum_split order hn _ b hbm] at hsum
          change τ p ^^^ xorSum (order.filter (· ≠ b)) (fun t => lowHash (g (t, p))) =
            lowHash (g (b, p))
          rw [← hsum]
          simp [BitVec.xor_assoc]
      · simp [fiberTable, hc, hs, h.2.2.2 b p hc hs]

/-- Eager reads preserve the private table even when its adaptive slack moves. -/
theorem fiberTable_put_eager (order : List κ) (hn : order.Nodup)
    (hcover : ∀ b, b ∈ order) (τ : ι → Digest) (st : ShareState κ ι B)
    (hg : Good order τ st) (u : κ × ι → HashOutput) (a : κ) (p : ι)
    (hc : st.cache (a, p) = none) (tag : Tag)
    (hbad : setsBad order τ (.read a p tag) st = none) :
    fiberTable order τ (put st a p (fiberTable order τ st u (a, p))) u =
      fiberTable order τ st u := by
  let g := fiberTable order τ st u
  have ht := fiberTable_compatible order hn hcover τ st hg u
  apply fiberTable_unique order hn τ _ (good_put order hcover τ st hg a p (g (a, p)) hc tag hbad)
  refine ⟨?_, ht.2.1, ?_, ?_⟩
  · intro b p' v hv
    by_cases hy : (b, p') = (a, p)
    · rcases Prod.mk.inj hy with ⟨rfl, rfl⟩
      simpa [put] using hv
    · have hv' : st.cache (b, p') = some v := by simpa [put, Function.update, hy] using hv
      exact ht.1 b p' v hv'
  · intro b p' hv
    have hy : (b, p') ≠ (a, p) := by intro he; cases he; simp [put] at hv
    have hv' : st.cache (b, p') = none := by simpa [put, Function.update, hy] using hv
    exact ht.2.2.1 b p' hv'
  · intro b p' hv hs
    have hy : (b, p') ≠ (a, p) := by intro he; cases he; simp [put] at hv
    have hv' : st.cache (b, p') = none := by simpa [put, Function.update, hy] using hv
    apply ht.2.2.2 b p' hv'
    intro hsb
    by_cases hpp : p' = p
    · subst p'
      have hba : b ≠ a := fun he => hy (by simp [he])
      exact hs (slack_put_ne order st a b p (g (a, p)) (Ne.symm hba) hsb)
    · exact hs ((slack_put_other order st a p p' (g (a, p)) hpp).trans hsb)


private theorem fiberTable_raw_congr (order : List κ) (τ : ι → Digest)
    (st : ShareState κ ι B) (u u' : κ × ι → HashOutput)
    (h : ∀ b p, st.cache (b, p) = none → u (b, p) = u' (b, p)) :
    fiberTable order τ st u = fiberTable order τ st u' := by
  have he : extend st u = extend st u' := by
    funext y
    rcases y with ⟨b, p⟩
    cases hc : st.cache (b, p) with
    | none => simp [extend, hc, h b p hc]
    | some v => simp [extend, hc]
  funext y
  rcases y with ⟨b, p⟩
  rw [fiberTable_eq, fiberTable_eq, he]
  split
  · rename_i hb
    rw [h b p (slack_some order st p b hb.2).2]
  · rfl

private theorem slack_put_value (order : List κ) (st : ShareState κ ι B)
    (a : κ) (p p' : ι) (v w : HashOutput) :
    slack order (put st a p v) p' = slack order (put st a p w) p' := by
  unfold slack
  congr 1
  funext b
  by_cases h : (b, p') = (a, p) <;> simp [put, Function.update, h]

private def rowRest (order : List κ) (st : ShareState κ ι B)
    (u : κ × ι → HashOutput) (a b : κ) (p : ι) : Digest :=
  xorSum ((order.filter (· ≠ a)).filter (· ≠ b)) (fun t => lowHash (extend st u (t, p)))

private def rawTwo (u : κ × ι → HashOutput) (a b : κ) (p : ι)
    (v w : HashOutput) : κ × ι → HashOutput :=
  Function.update (Function.update u (a, p) v) (b, p) w

private theorem rowRest_other (order : List κ) (hn : order.Nodup)
    (st : ShareState κ ι B) (u : κ × ι → HashOutput) (a b : κ) (p : ι)
    (ha : a ≠ b) (hb : b ∈ order) (hc : st.cache (b, p) = none) (v w : HashOutput) :
    xorSum (order.filter (· ≠ a))
      (fun t => lowHash (extend st (rawTwo u a b p v w) (t, p))) =
      lowHash w ^^^ rowRest order st u a b p := by
  rw [xorSum_split _ (hn.filter _) _ b (by simp [hb, Ne.symm ha])]
  simp only [extend, rawTwo, Function.update_self, hc, Option.getD_none]
  congr 1
  apply xorSum_congr
  intro t ht
  have hta : t ≠ a := by simpa using (List.mem_filter.mp (List.mem_filter.mp ht).1).2
  have htb : t ≠ b := by simpa using (List.mem_filter.mp ht).2
  simp [extend, rawTwo, Function.update, hta, htb]

/-- Inverting the two-cell shuffle makes the eager slack answer the fresh lazy value. -/
private theorem slack_read_answer (order : List κ) (hn : order.Nodup)
    (τ : ι → Digest) (st : ShareState κ ι B) (u : κ × ι → HashOutput)
    (a b : κ) (p : ι) (ha : a ≠ b) (hb : b ∈ order)
    (hca : st.cache (a, p) = none) (hcb : st.cache (b, p) = none)
    (hp : p ∉ st.done) (hs : slack order st p = some a) (v w : HashOutput) :
    let moved := (slackMove (τ p) (rowRest order st u a b p)).symm (v, w)
    fiberTable order τ st (rawTwo u a b p moved.1 moved.2) (a, p) = v := by
  dsimp only
  rw [fiberTable_eq, if_pos ⟨hp, hs⟩,
    rowRest_other order hn st u a b p ha hb hcb]
  apply pair.injective
  simp only [rawTwo, Function.update_of_ne (show (a, p) ≠ (b, p) by simp [ha]),
    Function.update_self, slackMove, Equiv.coe_fn_symm_mk, Equiv.apply_symm_apply,
    lowHash_pair]
  apply Prod.ext
  · rfl
  · change τ p ^^^ (τ p ^^^ (pair v).2 ^^^ rowRest order st u a b p ^^^
      rowRest order st u a b p) = (pair v).2
    simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    simp [BitVec.xor_assoc]

/-- Deterministic table identity behind the adaptive-slack read coupling. -/
private theorem slack_read_tables (order : List κ) (hn : order.Nodup)
    (hcover : ∀ b, b ∈ order) (τ : ι → Digest) (st : ShareState κ ι B)
    (hg : Good order τ st) (u : κ × ι → HashOutput) (a b : κ) (p : ι)
    (ha : a ≠ b) (hca : st.cache (a, p) = none) (hcb : st.cache (b, p) = none)
    (hp : p ∉ st.done) (hs : slack order st p = some a)
    (v w : HashOutput) (hg' : Good order τ (put st a p v))
    (hs' : slack order (put st a p v) p = some b) :
    let moved := (slackMove (τ p) (rowRest order st u a b p)).symm (v, w)
    fiberTable order τ (put st a p v) (rawTwo u a b p v w) =
      fiberTable order τ st (rawTwo u a b p moved.1 moved.2) := by
  dsimp only
  let moved := (slackMove (τ p) (rowRest order st u a b p)).symm (v, w)
  let right := rawTwo u a b p moved.1 moved.2
  let g := fiberTable order τ st right
  have ht := fiberTable_compatible order hn hcover τ st hg right
  have hanswer : g (a, p) = v := slack_read_answer order hn τ st u a b p ha (hcover b)
    hca hcb hp hs v w
  apply fiberTable_unique order hn τ _ hg'
  refine ⟨?_, ht.2.1, ?_, ?_⟩
  · intro t p' x hx
    by_cases hy : (t, p') = (a, p)
    · rcases Prod.mk.inj hy with ⟨rfl, rfl⟩
      have hvx : v = x := by simpa [put] using hx
      exact hanswer.trans hvx
    · exact ht.1 t p' x (by simpa [put, Function.update, hy] using hx)
  · intro t p' hc
    have hne : (t, p') ≠ (a, p) := by intro he; cases he; simp [put] at hc
    have hc' : st.cache (t, p') = none := by simpa [put, Function.update, hne] using hc
    rw [ht.2.2.1 t p' hc']
    by_cases htb : (t, p') = (b, p)
    · rcases Prod.mk.inj htb with ⟨rfl, rfl⟩
      simp [right, rawTwo, moved, slackMove]
    · simp [right, rawTwo, Function.update, hne, htb]
  · intro t p' hc hsl
    have hne : (t, p') ≠ (a, p) := by intro he; cases he; simp [put] at hc
    have hc' : st.cache (t, p') = none := by simpa [put, Function.update, hne] using hc
    have htb : (t, p') ≠ (b, p) := by
      intro he
      rcases Prod.mk.inj he with ⟨rfl, rfl⟩
      exact hsl hs'
    have hsl' : slack order st p' ≠ some t := by
      by_cases hpp : p' = p
      · subst p'
        simpa [hs] using (show a ≠ t from fun he => hne (by simp [he]))
      · rw [← slack_put_other order st a p p' v hpp]
        exact hsl
    rw [ht.2.2.2 t p' hc' hsl']
    simp [right, rawTwo, Function.update, hne, htb]


private theorem evalDist_pair_equiv {A R : Type} [Finite R] [SampleableType R]
    (e : (R × R) ≃ (R × R)) (K : R × R → A) :
    𝒟[do let v ← $ᵗ R; let w ← $ᵗ R; pure (K (e (v, w)))] =
      𝒟[do let v ← $ᵗ R; let w ← $ᵗ R; pure (K (v, w))] := by
  have hpair : ($ᵗ (R × R)) = (do let v ← $ᵗ R; let w ← $ᵗ R; pure (v, w)) := by
    change (Prod.mk <$> ($ᵗ R) <*> ($ᵗ R)) = _
    simp [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]
  have hmap (f : R × R → A) : f <$> ($ᵗ (R × R)) =
      (do let v ← $ᵗ R; let w ← $ᵗ R; pure (f (v, w))) := by
    rw [hpair]
    simp [map_bind]
  rw [← hmap (fun z => K (e z)), ← hmap K]
  calc
    _ = 𝒟[K <$> (e <$> ($ᵗ (R × R)))] := by rw [Functor.map_map]
    _ = _ := by
      rw [evalDist_map, evalDist_map_bijective_uniform_cross (R × R) e e.bijective,
        ← evalDist_map]

private theorem evalDist_two_draws_comm {R U A : Type} (dr : ProbComp R) (du : ProbComp U)
    (K : R → R → U → ProbComp A) :
    𝒟[do let v ← dr; let w ← dr; let u ← du; K v w u] =
      𝒟[do let u ← du; let v ← dr; let w ← dr; K v w u] := by
  calc
    _ = 𝒟[do let v ← dr; let u ← du; let w ← dr; K v w u] := by
      apply evalDist_bind_congr'
      intro v
      exact DeferredSampling.evalDist_bind_comm dr du (fun w u => K v w u)
    _ = _ := DeferredSampling.evalDist_bind_comm dr du (fun v u => do let w ← dr; K v w u)

/-- The adaptive-slack read is absorbed by the invertible two-cell shift. -/
private theorem read_table_slack [Finite κ] [Finite ι] [SampleableType (κ × ι → HashOutput)]
    (order : List κ) (hn : order.Nodup) (hcover : ∀ b, b ∈ order) (τ : ι → Digest)
    (st : ShareState κ ι B) (hg : Good order τ st) (a : κ) (p : ι)
    (hc : st.cache (a, p) = none) (hs : slack order st p = some a) (tag : Tag)
    (hbad : setsBad order τ (.read a p tag) st = none) :
    𝒟[do let v ← $ᵗ HashOutput
         let u ← $ᵗ (κ × ι → HashOutput)
         pure (v, fiberTable order τ (put st a p v) u)] =
      𝒟[do let u ← $ᵗ (κ × ι → HashOutput)
           pure (fiberTable order τ st u (a, p), fiberTable order τ st u)] := by
  have hp : p ∉ st.done := fun hp => (hg.1 p hp).1 a hc
  have hgood (v : HashOutput) := good_put order hcover τ st hg a p v hc tag hbad
  obtain ⟨b, hb⟩ := good_slack order hcover τ (put st a p 0) (hgood 0) p hp
  have hbc := (slack_some order (put st a p 0) p b hb).2
  have hba : b ≠ a := by intro he; subst b; simp [put] at hbc
  have hcb : st.cache (b, p) = none := by simpa [put, Function.update, hba] using hbc
  have hb' (v : HashOutput) : slack order (put st a p v) p = some b :=
    (slack_put_value order st a p p v 0).trans hb
  let L := fun v u => (v, fiberTable order τ (put st a p v) u)
  let K := fun u => (fiberTable order τ st u (a, p), fiberTable order τ st u)
  have hraw (v w : HashOutput) (u : κ × ι → HashOutput) :
      L v (Function.update u (b, p) w) = L v (rawTwo u a b p v w) := by
    apply Prod.ext
    · rfl
    apply fiberTable_raw_congr
    intro t p' ht
    have htne : (t, p') ≠ (a, p) := by intro he; cases he; simp [put] at ht
    simp [rawTwo, Function.update, htne]
  have hshift (v w : HashOutput) (u : κ × ι → HashOutput) :
      L v (rawTwo u a b p v w) =
        let moved := (slackMove (τ p) (rowRest order st u a b p)).symm (v, w)
        K (rawTwo u a b p moved.1 moved.2) := by
    apply Prod.ext
    · exact (slack_read_answer order hn τ st u a b p (Ne.symm hba) (hcover b)
        hc hcb hp hs v w).symm
    · exact slack_read_tables order hn hcover τ st hg u a b p (Ne.symm hba)
        hc hcb hp hs v w (hgood v) (hb' v)
  calc
    _ = 𝒟[do let v ← $ᵗ HashOutput; let w ← $ᵗ HashOutput
             let u ← $ᵗ (κ × ι → HashOutput); pure (L v (Function.update u (b, p) w))] := by
      apply evalDist_bind_congr'
      intro v
      exact (evalDist_uniformSample_bind_update_map (b, p) (L v)).symm
    _ = 𝒟[do let v ← $ᵗ HashOutput; let w ← $ᵗ HashOutput
             let u ← $ᵗ (κ × ι → HashOutput); pure (L v (rawTwo u a b p v w))] := by
      simp_rw [hraw]
    _ = 𝒟[do let u ← $ᵗ (κ × ι → HashOutput)
             let v ← $ᵗ HashOutput; let w ← $ᵗ HashOutput
             pure (L v (rawTwo u a b p v w))] :=
      evalDist_two_draws_comm _ _ _
    _ = 𝒟[do let u ← $ᵗ (κ × ι → HashOutput)
             let v ← $ᵗ HashOutput; let w ← $ᵗ HashOutput
             pure (K (rawTwo u a b p v w))] := by
      apply evalDist_bind_congr'
      intro u
      simp_rw [hshift]
      exact evalDist_pair_equiv (slackMove (τ p) (rowRest order st u a b p)).symm
        (fun z => K (rawTwo u a b p z.1 z.2))
    _ = 𝒟[do let v ← $ᵗ HashOutput; let w ← $ᵗ HashOutput
             let u ← $ᵗ (κ × ι → HashOutput); pure (K (rawTwo u a b p v w))] :=
      (evalDist_two_draws_comm _ _ _).symm
    _ = _ := evalDist_uniformSample_bind_update_two_map (by simp [Ne.symm hba]) K


private theorem read_cont_ne [Finite κ] [Finite ι] [SampleableType (κ × ι → HashOutput)]
    {A : Type} (order : List κ) (τ : ι → Digest) (st : ShareState κ ι B)
    (a b : κ) (p : ι) (hc : st.cache (a, p) = none)
    (hab : a ≠ b) (hs : slack order st p = some b)
    (Φ : ShareState κ ι B → (κ × ι → HashOutput) → ProbComp A) :
    𝒟[do let v ← $ᵗ HashOutput; let u ← $ᵗ (κ × ι → HashOutput)
         Φ (put st a p v) (fiberTable order τ (put st a p v) u)] =
      𝒟[do let u ← $ᵗ (κ × ι → HashOutput)
           let g := fiberTable order τ st u
           Φ (put st a p (g (a, p))) g] := by
  have h := read_table_ne order τ st a b p hc hab hs
  have h' := congrArg (fun d => d >>= fun z => 𝒟[Φ (put st a p z.1) z.2]) h
  simpa only [← evalDist_bind, bind_assoc, pure_bind] using h'

/-- Non-slack completion draws are absorbed one cell at a time. -/
private theorem fill_table [Finite κ] [Finite ι] [SampleableType (κ × ι → HashOutput)]
    {A : Type} (order : List κ) (τ : ι → Digest) (p : ι) (b : κ)
    (todo : List κ) (hlist : ∀ a ∈ todo, a ≠ b) (st : ShareState κ ι B)
    (hs : slack order st p = some b)
    (Φ : ShareState κ ι B → (κ × ι → HashOutput) → ProbComp A) :
    𝒟[do let st' ← fillTerms (fun _ => $ᵗ HashOutput) p todo st
         let u ← $ᵗ (κ × ι → HashOutput)
         Φ st' (fiberTable order τ st' u)] =
      𝒟[do let u ← $ᵗ (κ × ι → HashOutput)
           let g := fiberTable order τ st u
           let st' ← fillTerms (fun x => pure (g x)) p todo st
           Φ st' g] := by
  induction todo generalizing st with
  | nil => simp [fillTerms]
  | cons a todo ih =>
      have hab := hlist a (by simp)
      have htail : ∀ a ∈ todo, a ≠ b := fun a ha => hlist a (by simp [ha])
      cases hc : st.cache (a, p) with
      | some v =>
          simpa only [fillTerms, List.foldlM_cons, fillTerm, hc, pure_bind] using
            ih htail st hs
      | none =>
          simp only [fillTerms, List.foldlM_cons, fillTerm, hc, map_bind, bind_assoc,
            map_pure, pure_bind]
          change 𝒟[do let v ← $ᵗ HashOutput
                      let st' ← fillTerms (fun _ => $ᵗ HashOutput) p todo (put st a p v)
                      let u ← $ᵗ (κ × ι → HashOutput)
                      Φ st' (fiberTable order τ st' u)] = _
          calc
            _ = 𝒟[do let v ← $ᵗ HashOutput; let u ← $ᵗ (κ × ι → HashOutput)
                     let g := fiberTable order τ (put st a p v) u
                     let st' ← fillTerms (fun x => pure (g x)) p todo (put st a p v)
                     Φ st' g] := by
              apply evalDist_bind_congr'
              intro v
              exact ih htail (put st a p v) (slack_put_ne order st a b p v hab hs)
            _ = _ := read_cont_ne order τ st a b p hc hab hs
              (fun s g => do let st' ← fillTerms (fun x => pure (g x)) p todo s; Φ st' g)

/-- Every completion fill preserves prior cache entries and the two non-cache fields. -/
private theorem fillTerms_frame (draw : κ × ι → ProbComp HashOutput) (p : ι)
    (todo : List κ) (st : ShareState κ ι B) :
    ∀ st' ∈ support (fillTerms draw p todo st),
      st'.done = st.done ∧ st'.bad = st.bad ∧
      (∀ y v, st.cache y = some v → st'.cache y = some v) ∧
      (∀ y, y.2 ≠ p ∨ y.1 ∉ todo → st'.cache y = st.cache y) ∧
      (∀ a ∈ todo, st'.cache (a, p) ≠ none) := by
  induction todo generalizing st with
  | nil =>
      intro st' h
      have he : st' = st := by simpa [fillTerms] using h
      subst st'
      simp
  | cons a todo ih =>
      intro st' h
      change st' ∈ support (fillTerm draw p a st >>= fillTerms draw p todo) at h
      obtain ⟨mid, hm, hrest⟩ := mem_support_bind_peel _ _ h
      obtain ⟨hd, hb, hkeep, hout, hfilled⟩ := ih mid st' hrest
      cases hc : st.cache (a, p) with
      | some v =>
          have he : mid = st := by simpa [fillTerm, hc] using hm
          subst mid
          refine ⟨hd, hb, hkeep, ?_, ?_⟩
          · intro y hy
            apply hout y
            rcases hy with hy | hy
            · exact Or.inl hy
            · exact Or.inr (fun h => hy (by simp [h]))
          · intro x hx
            rcases List.mem_cons.mp hx with he | he
            · subst x
              rw [hkeep (a, p) v hc]
              exact Option.some_ne_none _
            · exact hfilled x he
      | none =>
          obtain ⟨v, _, rfl⟩ := mem_support_map_peel (fun v => put st a p v) (draw (a, p))
            (by simpa only [fillTerm, hc] using hm)
          refine ⟨hd, hb, ?_, ?_, ?_⟩
          · intro y w hy
            apply hkeep y w
            by_cases he : y = (a, p)
            · subst y
              simp [hc] at hy
            · simp [put, Function.update, he, hy]
          · intro y hy
            have hy' : y.2 ≠ p ∨ y.1 ∉ todo := by
              rcases hy with h | h
              · exact Or.inl h
              · exact Or.inr (fun he => h (by simp [he]))
            rw [hout y hy']
            have hyne : y ≠ (a, p) := by
              intro he
              subst y
              simp at hy
            simp [put, Function.update, hyne]
          · intro x hx
            rcases List.mem_cons.mp hx with he | he
            · subst x
              rw [hkeep (a, p) v (by simp [put])]
              exact Option.some_ne_none _
            · exact hfilled x he


private theorem fillTerms_good (order : List κ) (τ : ι → Digest)
    (draw : κ × ι → ProbComp HashOutput) (p : ι) (b : κ)
    (todo : List κ) (hn : b ∉ todo) (st : ShareState κ ι B)
    (hg : Good order τ st) (hc : st.cache (b, p) = none) :
    ∀ st' ∈ support (fillTerms draw p todo st), Good order τ st' := by
  intro st' hs
  obtain ⟨hd, _, hkeep, hout, _⟩ := fillTerms_frame draw p todo st st' hs
  refine ⟨?_, ?_⟩
  · intro p' hp'
    rw [hd] at hp'
    have hrow : ∀ a, st'.cache (a, p') = st.cache (a, p') := by
      intro a
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((hg.1 p' hp').1 a)
      rw [hv, hkeep (a, p') v hv]
    refine ⟨fun a => by rw [hrow a]; exact (hg.1 p' hp').1 a, ?_⟩
    have he : sum order st' p' = sum order st p' := by
      unfold sum low
      simp_rw [hrow]
    rw [he]
    exact (hg.1 p' hp').2
  · intro p' hp'
    rw [hd] at hp'
    by_cases hpp : p' = p
    · subst p'
      exact ⟨b, (hout (b, p) (Or.inr hn)).trans hc⟩
    · obtain ⟨a, ha⟩ := hg.2 p' hp'
      exact ⟨a, (hout (a, p') (Or.inl hpp)).trans ha⟩

private theorem fillTerms_slack (order : List κ) (draw : κ × ι → ProbComp HashOutput)
    (p : ι) (b : κ) (todo : List κ) (hn : b ∉ todo) (st : ShareState κ ι B)
    (hs : slack order st p = some b) :
    ∀ st' ∈ support (fillTerms draw p todo st), slack order st' p = some b := by
  intro st' hz
  obtain ⟨_, _, hkeep, hout, _⟩ := fillTerms_frame draw p todo st st' hz
  obtain ⟨hb, left, right, horder, hleft⟩ := List.find?_eq_some_iff_append.mp hs
  apply List.find?_eq_some_iff_append.mpr
  refine ⟨?_, left, right, horder, ?_⟩
  · rw [hout (b, p) (Or.inr hn)]
    exact hb
  · intro a ha
    have hc : st.cache (a, p) ≠ none := by simpa [Option.isSome_iff_ne_none] using hleft a ha
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hc
    simp [hkeep (a, p) v hv]

private theorem fillTerms_agree (g : κ × ι → HashOutput) (p : ι) (todo : List κ)
    (st : ShareState κ ι B) (h : ∀ y v, st.cache y = some v → g y = v) :
    ∀ st' ∈ support (fillTerms (fun y => pure (g y)) p todo st),
      ∀ y v, st'.cache y = some v → g y = v := by
  induction todo generalizing st with
  | nil =>
      intro st' hs
      have he : st' = st := by simpa [fillTerms] using hs
      subst st'
      exact h
  | cons a todo ih =>
      intro st' hs
      change st' ∈ support (fillTerm (fun y => pure (g y)) p a st >>=
        fillTerms (fun y => pure (g y)) p todo) at hs
      obtain ⟨mid, hm, hs⟩ := mem_support_bind_peel _ _ hs
      apply ih mid _ st' hs
      cases hc : st.cache (a, p) with
      | some v =>
          have he : mid = st := by simpa [fillTerm, hc] using hm
          subst mid
          exact h
      | none =>
          have he : mid = put st a p (g (a, p)) := by simpa [fillTerm, hc] using hm
          subst mid
          intro y v hv
          by_cases hy : y = (a, p)
          · subst y
            simpa [put] using hv
          · exact h y v (by simpa [put, Function.update, hy] using hv)

/-- Filling non-slack coordinates from the eager table preserves its reconstruction. -/
private theorem fillTerms_table_eager (order : List κ) (hn : order.Nodup)
    (hcover : ∀ b, b ∈ order) (τ : ι → Digest) (p : ι) (b : κ)
    (todo : List κ) (hlist : b ∉ todo) (st : ShareState κ ι B)
    (hg : Good order τ st) (hs : slack order st p = some b) (u : κ × ι → HashOutput) :
    ∀ st' ∈ support (fillTerms (fun y => pure (fiberTable order τ st u y)) p todo st),
      fiberTable order τ st' u = fiberTable order τ st u := by
  intro st' hz
  let g := fiberTable order τ st u
  have ht := fiberTable_compatible order hn hcover τ st hg u
  have hc := (slack_some order st p b hs).2
  have hg' := fillTerms_good order τ (fun y => pure (g y)) p b todo hlist st hg hc st' hz
  obtain ⟨_, _, hkeep, hout, _⟩ := fillTerms_frame (fun y => pure (g y)) p todo st st' hz
  have hs' := fillTerms_slack order (fun y => pure (g y)) p b todo hlist st hs st' hz
  have hnone (a : κ) (p' : ι) (h : st'.cache (a, p') = none) : st.cache (a, p') = none := by
    cases he : st.cache (a, p') with
    | none => rfl
    | some v => simp [hkeep (a, p') v he] at h
  apply fiberTable_unique order hn τ st' hg'
  refine ⟨?_, ht.2.1, ?_, ?_⟩
  · intro a p' v hv
    exact fillTerms_agree g p todo st (fun y v hv => ht.1 y.1 y.2 v hv) st' hz (a, p') v hv
  · intro a p' ha
    exact ht.2.2.1 a p' (hnone a p' ha)
  · intro a p' ha hsl
    apply ht.2.2.2 a p' (hnone a p' ha)
    intro hsa
    by_cases hpp : p' = p
    · subst p'
      have hab : b = a := Option.some.inj (hs.symm.trans hsa)
      exact hsl (by simpa [hab] using hs')
    · have he : slack order st' p' = slack order st p' := by
        unfold slack
        congr 1
        funext t
        rw [hout (t, p') (Or.inl hpp)]
      exact hsl (he.trans hsa)

private def finishState (st : ShareState κ ι B) (p : ι) (b : κ) (v : HashOutput) :
    ShareState κ ι B := { put st b p v with done := insert p st.done }

private theorem finish_good (order : List κ) (hn : order.Nodup)
    (τ : ι → Digest) (st : ShareState κ ι B) (hg : Good order τ st)
    (p : ι) (b : κ) (hb : b ∈ order) (hc : st.cache (b, p) = none)
    (hall : ∀ a, a ≠ b → st.cache (a, p) ≠ none) (hi : Digest) :
    Good order τ (finishState st p b (pair.symm (hi, τ p ^^^ others order st p b))) := by
  have hp : p ∉ st.done := fun h => (hg.1 p h).1 b hc
  refine ⟨?_, ?_⟩
  · intro p' hp'
    have hp' : p' = p ∨ p' ∈ st.done := by simpa [finishState, put] using hp'
    rcases hp' with he | hp'
    · subst p'
      refine ⟨?_, ?_⟩
      · intro a
        by_cases ha : a = b
        · simp [finishState, put, ha]
        · simpa [finishState, put, Function.update, ha] using hall a ha
      · change sum order (put st b p (pair.symm (hi, τ p ^^^ others order st p b))) p = τ p
        rw [sum_put order hn b hb, lowHash_pair]
        simp [BitVec.xor_assoc]
    · have hpp : p' ≠ p := by intro he; subst p'; exact hp hp'
      refine ⟨?_, ?_⟩
      · intro a
        simpa [finishState, put, Function.update, hpp] using (hg.1 p' hp').1 a
      · have he : sum order (finishState st p b (pair.symm (hi, τ p ^^^ others order st p b))) p' =
            sum order st p' := by
          unfold sum low
          simp [finishState, put, Function.update, hpp]
        rw [he]
        exact (hg.1 p' hp').2
  · intro p' hp'
    have hpp : p' ≠ p := by intro he; subst p'; simp [finishState, put] at hp'
    have hpd : p' ∉ st.done := by simpa [finishState, put, hpp] using hp'
    obtain ⟨a, ha⟩ := hg.2 p' hpd
    exact ⟨a, by simp [finishState, put, Function.update, hpp, ha]⟩


private theorem fiberTable_last (order : List κ) (τ : ι → Digest)
    (st : ShareState κ ι B) (p : ι) (b : κ) (u : κ × ι → HashOutput)
    (hp : p ∉ st.done) (hs : slack order st p = some b)
    (hall : ∀ a, a ≠ b → st.cache (a, p) ≠ none) :
    fiberTable order τ st u (b, p) =
      pair.symm ((pair (u (b, p))).1, τ p ^^^ others order st p b) := by
  rw [fiberTable_eq, if_pos ⟨hp, hs⟩]
  congr 2
  congr 1
  apply xorSum_congr
  intro a ha
  have hab : a ≠ b := by simpa using (List.mem_filter.mp ha).2
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hall a hab)
  simp [extend, low, hv]

private theorem finish_table_eager (order : List κ) (hn : order.Nodup)
    (hcover : ∀ b, b ∈ order) (τ : ι → Digest) (st : ShareState κ ι B)
    (hg : Good order τ st) (p : ι) (b : κ) (u : κ × ι → HashOutput)
    (hp : p ∉ st.done) (hs : slack order st p = some b)
    (hall : ∀ a, a ≠ b → st.cache (a, p) ≠ none) :
    fiberTable order τ (finishState st p b (fiberTable order τ st u (b, p))) u =
      fiberTable order τ st u := by
  let g := fiberTable order τ st u
  have hc := (slack_some order st p b hs).2
  have ht := fiberTable_compatible order hn hcover τ st hg u
  have hg' : Good order τ (finishState st p b (g (b, p))) := by
    rw [show g (b, p) = _ from fiberTable_last order τ st p b u hp hs hall]
    exact finish_good order hn τ st hg p b (hcover b) hc hall _
  apply fiberTable_unique order hn τ _ hg'
  refine ⟨?_, ht.2.1, ?_, ?_⟩
  · intro a p' v hv
    by_cases hy : (a, p') = (b, p)
    · rcases Prod.mk.inj hy with ⟨rfl, rfl⟩
      simpa [finishState, put] using hv
    · exact ht.1 a p' v (by simpa [finishState, put, Function.update, hy] using hv)
  · intro a p' ha
    have hy : (a, p') ≠ (b, p) := by intro he; cases he; simp [finishState, put] at ha
    have hc' : st.cache (a, p') = none := by simpa [finishState, put, Function.update, hy] using ha
    exact ht.2.2.1 a p' hc'
  · intro a p' ha hsl
    have hy : (a, p') ≠ (b, p) := by intro he; cases he; simp [finishState, put] at ha
    have hc' : st.cache (a, p') = none := by simpa [finishState, put, Function.update, hy] using ha
    have hpp : p' ≠ p := by
      intro he
      subst p'
      exact hall a (fun he => hy (by simp [he])) hc'
    apply ht.2.2.2 a p' hc'
    have he : slack order (finishState st p b (g (b, p))) p' = slack order st p' :=
      slack_put_other order st b p p' _ hpp
    exact fun h => hsl (he.trans h)

private theorem evalDist_high_uniform :
    𝒟[(fun v : HashOutput => (pair v).1) <$> ($ᵗ HashOutput)] = 𝒟[$ᵗ Digest] := by
  calc
    _ = 𝒟[Prod.fst <$> (pair <$> ($ᵗ HashOutput))] := by rw [Functor.map_map]
    _ = 𝒟[Prod.fst <$> ($ᵗ (Digest × Digest))] := by
      rw [evalDist_map, evalDist_map_bijective_uniform_cross HashOutput pair pair.bijective,
        ← evalDist_map]
    _ = _ := evalDist_map_fst_uniformSample_prod

/-- The final low half is constrained, while its high half remains a fresh uniform digest. -/
private theorem finish_table [Finite κ] [Finite ι] [SampleableType (κ × ι → HashOutput)]
    {A : Type} (order : List κ) (hn : order.Nodup) (hcover : ∀ b, b ∈ order)
    (τ : ι → Digest) (st : ShareState κ ι B) (hg : Good order τ st) (p : ι) (b : κ)
    (hp : p ∉ st.done) (hs : slack order st p = some b)
    (hall : ∀ a, a ≠ b → st.cache (a, p) ≠ none)
    (Φ : ShareState κ ι B → (κ × ι → HashOutput) → ProbComp A) :
    𝒟[do let h ← $ᵗ HashOutput
         let st' := finishState st p b (pair.symm (lowHash h, τ p ^^^ others order st p b))
         let u ← $ᵗ (κ × ι → HashOutput)
         Φ st' (fiberTable order τ st' u)] =
      𝒟[do let u ← $ᵗ (κ × ι → HashOutput)
           let g := fiberTable order τ st u
           Φ (finishState st p b (g (b, p))) g] := by
  let K : Digest → ProbComp A := fun hi => do
    let st' := finishState st p b (pair.symm (hi, τ p ^^^ others order st p b))
    let u ← $ᵗ (κ × ι → HashOutput)
    Φ st' (fiberTable order τ st' u)
  have hhigh : 𝒟[do let h ← $ᵗ HashOutput; K (lowHash h)] =
      𝒟[do let h ← $ᵗ HashOutput; K (pair h).1] := by
    calc
      _ = 𝒟[(lowHash <$> ($ᵗ HashOutput)) >>= K] := by simp only [bind_map_left]
      _ = 𝒟[((fun h : HashOutput => (pair h).1) <$> ($ᵗ HashOutput)) >>= K] := by
        rw [evalDist_bind, evalDist_bind, XmssSecurity.Rom.evalDist_truncate_uniformHashOutput,
          evalDist_high_uniform]
      _ = _ := by simp only [bind_map_left]
  rw [show (do let h ← $ᵗ HashOutput
               let st' := finishState st p b (pair.symm (lowHash h, τ p ^^^ others order st p b))
               let u ← $ᵗ (κ × ι → HashOutput)
               Φ st' (fiberTable order τ st' u)) =
      ($ᵗ HashOutput >>= fun h => K (lowHash h)) from rfl, hhigh]
  let ψ : (κ × ι → HashOutput) → ShareState κ ι B × (κ × ι → HashOutput) :=
    fun u => (finishState st p b (fiberTable order τ st u (b, p)), fiberTable order τ st u)
  have hm := evalDist_uniformSample_bind_update_map (b, p) ψ
  have hm' := congrArg (fun d => d >>= fun z => 𝒟[Φ z.1 z.2]) hm
  simp only [← evalDist_bind, bind_assoc, pure_bind] at hm'
  have hid (v : HashOutput) (u : κ × ι → HashOutput) :
      ψ (Function.update u (b, p) v) =
        let st' := finishState st p b (pair.symm ((pair v).1, τ p ^^^ others order st p b))
        (st', fiberTable order τ st' u) := by
    dsimp [ψ]
    rw [fiberTable_last order τ st p b _ hp hs hall, Function.update_self]
    apply Prod.ext
    · rfl
    symm
    rw [← finish_table_eager order hn hcover τ st hg p b (Function.update u (b, p) v) hp hs hall]
    rw [fiberTable_last order τ st p b _ hp hs hall, Function.update_self]
    apply fiberTable_raw_congr
    intro a p' ha
    have hy : (a, p') ≠ (b, p) := by intro he; cases he; simp [finishState, put] at ha
    simp [Function.update, hy]
  simp_rw [hid] at hm'
  exact hm'


private def completeLazy (order : List κ) (τ : ι → Digest) (st : ShareState κ ι B)
    (p : ι) (b : κ) : ProbComp (ShareState κ ι B) := do
  let st' ← fillTerms (fun _ => $ᵗ HashOutput) p (order.filter (· ≠ b)) st
  let h ← $ᵗ HashOutput
  pure (finishState st' p b (pair.symm (lowHash h, τ p ^^^ others order st' p b)))

private def completeEager (order : List κ) (g : κ × ι → HashOutput)
    (st : ShareState κ ι B) (p : ι) (b : κ) : ProbComp (ShareState κ ι B) := do
  let st' ← fillTerms (fun y => pure (g y)) p (order.filter (· ≠ b)) st
  pure (finishState st' p b (g (b, p)))

private theorem completion_table [Finite κ] [Finite ι] [SampleableType (κ × ι → HashOutput)]
    {A : Type} (order : List κ) (hn : order.Nodup) (hcover : ∀ b, b ∈ order)
    (τ : ι → Digest) (st : ShareState κ ι B) (hg : Good order τ st) (p : ι) (b : κ)
    (hp : p ∉ st.done) (hs : slack order st p = some b)
    (Φ : ShareState κ ι B → (κ × ι → HashOutput) → ProbComp A) :
    𝒟[do let st' ← completeLazy order τ st p b
         let u ← $ᵗ (κ × ι → HashOutput)
         Φ st' (fiberTable order τ st' u)] =
      𝒟[do let u ← $ᵗ (κ × ι → HashOutput)
           let g := fiberTable order τ st u
           let st' ← completeEager order g st p b
           Φ st' g] := by
  have hbn : b ∉ order.filter (· ≠ b) := by simp
  have hc := (slack_some order st p b hs).2
  unfold completeLazy completeEager
  simp only [bind_assoc, pure_bind]
  calc
    _ = 𝒟[do let st' ← fillTerms (fun _ => $ᵗ HashOutput) p (order.filter (· ≠ b)) st
             let u ← $ᵗ (κ × ι → HashOutput)
             let g := fiberTable order τ st' u
             Φ (finishState st' p b (g (b, p))) g] := by
      apply evalDist_bind_congr
      intro st' hz
      obtain ⟨hd, _, _, _, hfill⟩ := fillTerms_frame (fun _ => $ᵗ HashOutput) p
        (order.filter (· ≠ b)) st st' hz
      exact finish_table order hn hcover τ st'
        (fillTerms_good order τ _ p b _ hbn st hg hc st' hz) p b (by rwa [hd])
        (fillTerms_slack order _ p b _ hbn st hs st' hz)
        (fun a ha => hfill a (by simp [hcover a, ha])) Φ
    _ = _ := fill_table order τ p b (order.filter (· ≠ b))
      (fun a ha => by simpa using (List.mem_filter.mp ha).2) st hs
      (fun st' g => Φ (finishState st' p b (g (b, p))) g)

private theorem completeLazy_good (order : List κ) (hn : order.Nodup)
    (hcover : ∀ b, b ∈ order) (τ : ι → Digest) (st : ShareState κ ι B)
    (hg : Good order τ st) (p : ι) (b : κ) (hs : slack order st p = some b) :
    ∀ st' ∈ support (completeLazy order τ st p b), Good order τ st' := by
  intro st' hz
  obtain ⟨mid, hm, hz⟩ := mem_support_bind_peel _ _ hz
  obtain ⟨h, _, hz⟩ := mem_support_bind_peel ($ᵗ HashOutput) _ hz
  have he := eq_of_mem_support_pure _ hz
  subst st'
  have hbn : b ∉ order.filter (· ≠ b) := by simp
  obtain ⟨_, _, _, hout, hfilled⟩ := fillTerms_frame (fun _ => $ᵗ HashOutput) p
    (order.filter (· ≠ b)) st mid hm
  have hc := (slack_some order st p b hs).2
  exact finish_good order hn τ mid
    (fillTerms_good order τ _ p b _ hbn st hg hc mid hm) p b (hcover b)
    ((hout (b, p) (Or.inr hbn)).trans hc)
    (fun a ha => hfilled a (by simp [hcover a, ha])) _

private theorem completeEager_good_table (order : List κ) (hn : order.Nodup)
    (hcover : ∀ b, b ∈ order) (τ : ι → Digest) (st : ShareState κ ι B)
    (hg : Good order τ st) (p : ι) (b : κ) (hp : p ∉ st.done)
    (hs : slack order st p = some b) (u : κ × ι → HashOutput) :
    ∀ st' ∈ support (completeEager order (fiberTable order τ st u) st p b),
      Good order τ st' ∧ fiberTable order τ st' u = fiberTable order τ st u := by
  intro st' hz
  let g := fiberTable order τ st u
  obtain ⟨mid, hm, hz⟩ := mem_support_bind_peel _ _ hz
  have he := eq_of_mem_support_pure _ hz
  subst st'
  have hbn : b ∉ order.filter (· ≠ b) := by simp
  have hc := (slack_some order st p b hs).2
  obtain ⟨hd, _, _, hout, hfilled⟩ := fillTerms_frame (fun y => pure (g y)) p
    (order.filter (· ≠ b)) st mid hm
  have hgm := fillTerms_good order τ (fun y => pure (g y)) p b _ hbn st hg hc mid hm
  have hsm := fillTerms_slack order (fun y => pure (g y)) p b _ hbn st hs mid hm
  have hfm := fillTerms_table_eager order hn hcover τ p b _ hbn st hg hs u mid hm
  have hall : ∀ a, a ≠ b → mid.cache (a, p) ≠ none :=
    fun a ha => hfilled a (by simp [hcover a, ha])
  have hpm : p ∉ mid.done := by rwa [hd]
  have hlast : g (b, p) = pair.symm ((pair (u (b, p))).1, τ p ^^^ others order mid p b) := by
    change fiberTable order τ st u (b, p) = _
    rw [← hfm]
    exact fiberTable_last order τ mid p b u hpm hsm hall
  refine ⟨?_, ?_⟩
  · change Good order τ (finishState mid p b (g (b, p)))
    rw [hlast]
    exact finish_good order hn τ mid hgm p b (hcover b)
      ((hout (b, p) (Or.inr hbn)).trans hc) hall _
  · change fiberTable order τ (finishState mid p b (g (b, p))) u = g
    rw [show g = fiberTable order τ mid u from hfm.symm]
    exact finish_table_eager order hn hcover τ mid hgm p b u hpm hsm hall

@[simp] private theorem erase_unerase (st : ShareState κ ι (FrozenBad Tag)) :
    erase (unerase st) = st := by
  rcases st with ⟨cache, done, bad⟩
  cases bad <;> rfl

@[simp] private theorem erase_put (st : ShareState κ ι (ImplBad Tag)) (a : κ) (p : ι)
    (v : HashOutput) : erase (put st a p v) = put (erase st) a p v := rfl

@[simp] private theorem erase_fillTerms (draw : κ × ι → ProbComp HashOutput) (p : ι)
    (todo : List κ) (st : ShareState κ ι (ImplBad Tag)) :
    erase <$> fillTerms draw p todo st = fillTerms draw p todo (erase st) := by
  induction todo generalizing st with
  | nil => simp [fillTerms]
  | cons a todo ih =>
      change erase <$> (fillTerm draw p a st >>= fun s => fillTerms draw p todo s) =
        (fillTerm draw p a (erase st) >>= fun s => fillTerms draw p todo s)
      cases hc : st.cache (a, p) with
      | some v =>
          have hc' : (erase st).cache (a, p) = some v := hc
          simp only [fillTerm, hc, hc', pure_bind, ih]
      | none =>
          have hc' : (erase st).cache (a, p) = none := hc
          simp only [fillTerm, hc, hc', bind_map_left, map_bind, ih, erase_put]


private theorem frozen_complete_map (order : List κ) (τ : ι → Digest)
    (draw : κ × ι → ProbComp HashOutput)
    (finish : κ → ι → Digest → ShareState κ ι (ImplBad Tag) → ProbComp HashOutput)
    (finish' : κ → ι → Digest → ShareState κ ι (FrozenBad Tag) → ProbComp HashOutput)
    (hf : ∀ b p target s, finish b p target s = finish' b p target (erase s))
    (st : ShareState κ ι (FrozenBad Tag)) (hbad : st.bad = none)
    (p : ι) (b : κ) (tag : Tag) (hp : p ∉ st.done) (hs : slack order st p = some b) :
    𝒟[(frozen order τ (impl order τ draw finish) (.complete p (τ p) tag)).run st] =
      𝒟[do let mid ← fillTerms draw p (order.filter (· ≠ b)) st
           let v ← finish' b p (τ p) mid
           pure (true, finishState mid p b v)] := by
  have hset : setsBad order τ (.complete p (τ p) tag) st = none := by simp [setsBad, hp, hs]
  have hp0 : p ∉ (unerase st).done := hp
  have hs0 : slack order (unerase st) p = some b := hs
  have hb0 : (unerase st).bad = none := by simp [unerase, hbad]
  simp only [frozen, StateT.run, hbad, hset, Option.orElse_eq_orElse, Option.orElse,
    impl, hp0, ↓reduceIte, hs0, hb0, map_bind, map_pure]
  calc
    _ = 𝒟[do let mid ← fillTerms draw p (order.filter (· ≠ b)) (unerase st)
             let v ← finish' b p (τ p) (erase mid)
             pure (true, finishState (erase mid) p b v)] := by
      apply evalDist_bind_congr
      intro mid hm
      have hb := (fillTerms_frame draw p (order.filter (· ≠ b)) (unerase st) mid hm).2.1
      rw [hf]
      apply evalDist_bind_congr'
      intro v
      congr 1
      simp [finishState, erase, put, hb, hb0]
    _ = _ := by
      rw [show (do let mid ← fillTerms draw p (order.filter (· ≠ b)) (unerase st)
                    let v ← finish' b p (τ p) (erase mid)
                    pure (true, finishState (erase mid) p b v)) =
        (erase <$> fillTerms draw p (order.filter (· ≠ b)) (unerase st)) >>=
          (fun mid => do let v ← finish' b p (τ p) mid; pure (true, finishState mid p b v))
        from by simp only [bind_map_left]]
      rw [erase_fillTerms, erase_unerase]

private theorem lazyFrozen_complete (order : List κ) (τ : ι → Digest)
    (st : ShareState κ ι (FrozenBad Tag)) (hbad : st.bad = none)
    (p : ι) (b : κ) (tag : Tag) (hp : p ∉ st.done) (hs : slack order st p = some b) :
    𝒟[(lazyFrozen order τ (.complete p (τ p) tag)).run st] =
      𝒟[(fun st' => (true, st')) <$> completeLazy order τ st p b] := by
  simpa only [lazyFrozen, lazyImpl, completeLazy, map_bind, map_pure, bind_map_left] using
    frozen_complete_map order τ (fun _ => $ᵗ HashOutput)
      (fun b p target s => (fun h => pair.symm (lowHash h, target ^^^ others order s p b)) <$>
        ($ᵗ HashOutput))
      (fun b p target s => (fun h => pair.symm (lowHash h, target ^^^ others order s p b)) <$>
        ($ᵗ HashOutput))
      (fun _ _ _ _ => rfl) st hbad p b tag hp hs

private theorem eagerFrozen_complete (order : List κ) (τ : ι → Digest)
    (g : κ × ι → HashOutput) (st : ShareState κ ι (FrozenBad Tag)) (hbad : st.bad = none)
    (p : ι) (b : κ) (tag : Tag) (hp : p ∉ st.done) (hs : slack order st p = some b) :
    𝒟[(eagerFrozen order τ g (.complete p (τ p) tag)).run st] =
      𝒟[(fun st' => (true, st')) <$> completeEager order g st p b] := by
  simpa only [eagerFrozen, eagerImpl, completeEager, map_bind, map_pure, pure_bind] using
    frozen_complete_map order τ (fun y => pure (g y))
      (fun b p _ _ => pure (g (b, p))) (fun b p _ _ => pure (g (b, p)))
      (fun _ _ _ _ => rfl) st hbad p b tag hp hs


private theorem frozen_read_miss (order : List κ) (τ : ι → Digest)
    (draw : κ × ι → ProbComp HashOutput)
    (finish : κ → ι → Digest → ShareState κ ι (ImplBad Tag) → ProbComp HashOutput)
    (st : ShareState κ ι (FrozenBad Tag)) (hbad : st.bad = none)
    (a : κ) (p : ι) (tag : Tag) (hc : st.cache (a, p) = none)
    (hs : setsBad order τ (.read a p tag) st = none) :
    (frozen order τ (impl order τ draw finish) (.read a p tag)).run st =
      (fun v => (v, put st a p v)) <$> draw (a, p) := by
  have hs0 : setsBad order τ (.read a p tag) (unerase st) = none := hs
  have hc0 : (unerase st).cache (a, p) = none := hc
  simp only [frozen, StateT.run, hbad, hs, Option.orElse_eq_orElse, Option.orElse,
    impl, hc0, map_bind, map_pure, hs0, Option.map_none]
  rw [map_eq_bind_pure_comp]
  congr 1
  funext v
  congr 1
  rcases st with ⟨cache, done, bad⟩
  simp_all [unerase, erase, put]

private theorem pure_table_step [SampleableType (κ × ι → HashOutput)] {X A : Type}
    (order : List κ) (τ : ι → Digest) (st : ShareState κ ι B)
    (L : ProbComp (X × ShareState κ ι B))
    (E : (κ × ι → HashOutput) → ProbComp (X × ShareState κ ι B))
    (y : X × ShareState κ ι B) (hy : Good order τ y.2)
    (hF : ∀ u, fiberTable order τ y.2 u = fiberTable order τ st u)
    (hl : 𝒟[L] = 𝒟[(pure y : ProbComp _)])
    (he : ∀ u, 𝒟[E (fiberTable order τ st u)] = 𝒟[(pure y : ProbComp _)])
    (Φ : (X × ShareState κ ι B) → (κ × ι → HashOutput) → ProbComp A) :
    (∀ z ∈ support L, Good order τ z.2) ∧
    (∀ u, ∀ z ∈ support (E (fiberTable order τ st u)),
      Good order τ z.2 ∧ fiberTable order τ z.2 u = fiberTable order τ st u) ∧
    𝒟[do let z ← L; let u ← $ᵗ (κ × ι → HashOutput); Φ z (fiberTable order τ z.2 u)] =
      𝒟[do let u ← $ᵗ (κ × ι → HashOutput)
           let z ← E (fiberTable order τ st u); Φ z (fiberTable order τ st u)] := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have heq := eq_of_mem_support_pure y ((mem_support_iff_of_evalDist_eq hl z).mp hz)
    subst z
    exact hy
  · intro u z hz
    have heq := eq_of_mem_support_pure y ((mem_support_iff_of_evalDist_eq (he u) z).mp hz)
    subst z
    exact ⟨hy, hF u⟩
  · rw [evalDist_bind, hl, evalDist_pure, pure_bind]
    apply evalDist_bind_congr'
    intro u
    rw [evalDist_bind, he u, evalDist_pure, pure_bind, hF u]

/-- Per-query reconstruction and coupling for the frozen oracle. -/
private theorem frozen_step [Finite κ] [Finite ι] [SampleableType (κ × ι → HashOutput)]
    {A : Type} (order : List κ) (hn : order.Nodup) (hcover : ∀ b, b ∈ order)
    (τ : ι → Digest) (q : ShareQuery κ ι Tag) (st : ShareState κ ι (FrozenBad Tag))
    (hg : Good order τ st)
    (Φ : ((ShareSpec κ ι Tag).Range q × ShareState κ ι (FrozenBad Tag)) →
      (κ × ι → HashOutput) → ProbComp A) :
    (∀ z ∈ support ((lazyFrozen order τ q).run st), Good order τ z.2) ∧
    (∀ u, ∀ z ∈ support ((eagerFrozen order τ (fiberTable order τ st u) q).run st),
      Good order τ z.2 ∧ fiberTable order τ z.2 u = fiberTable order τ st u) ∧
    𝒟[do let z ← (lazyFrozen order τ q).run st
         let u ← $ᵗ (κ × ι → HashOutput); Φ z (fiberTable order τ z.2 u)] =
      𝒟[do let u ← $ᵗ (κ × ι → HashOutput)
           let z ← (eagerFrozen order τ (fiberTable order τ st u) q).run st
           Φ z (fiberTable order τ st u)] := by
  cases hb : st.bad with
  | some r =>
      have hreset : { st with bad := some r } = st := by rw [← hb]
      let y : (ShareSpec κ ι Tag).Range q × ShareState κ ι (FrozenBad Tag) :=
        match q with
        | .read .. => ((0 : HashOutput), st)
        | .complete .. => (false, st)
        | .view => ((st.cache, st.done), st)
      apply pure_table_step order τ st ((lazyFrozen order τ q).run st)
        (fun g => (eagerFrozen order τ g q).run st) y (Φ := Φ)
      · cases q <;> exact hg
      · intro u; cases q <;> rfl
      · cases q <;> simp [y, lazyFrozen, frozen, StateT.run, hb, hreset]
      · intro u; cases q <;> simp [y, eagerFrozen, frozen, StateT.run, hb, hreset]
  | none =>
      have hreset : { st with bad := none } = st := by rw [← hb]
      cases hs : setsBad order τ q st with
      | some r =>
          let st' : ShareState κ ι (FrozenBad Tag) := { st with bad := some r }
          let y : (ShareSpec κ ι Tag).Range q × ShareState κ ι (FrozenBad Tag) :=
            match q with
            | .read .. => ((0 : HashOutput), st')
            | .complete .. => (false, st')
            | .view => ((st.cache, st.done), st')
          apply pure_table_step order τ st ((lazyFrozen order τ q).run st)
            (fun g => (eagerFrozen order τ g q).run st) y (Φ := Φ)
          · cases q <;> exact hg
          · intro u; cases q <;> rfl
          · cases q <;> simp [y, st', lazyFrozen, frozen, StateT.run, hb, hs, unerase, erase, hreset]
          · intro u; cases q <;> simp [y, st', eagerFrozen, frozen, StateT.run, hb, hs, unerase, erase, hreset]
      | none =>
          cases q with
          | view =>
              apply pure_table_step order τ st ((lazyFrozen order τ .view).run st)
                (fun g => (eagerFrozen order τ g .view).run st) ((st.cache, st.done), st) hg (fun _ => rfl) (Φ := Φ)
              · simp [lazyFrozen, frozen, lazyImpl, impl, StateT.run, hb, hs, unerase, erase, hreset]
              · intro u; simp [eagerFrozen, frozen, eagerImpl, impl, StateT.run, hb, hs, unerase, erase, hreset]
          | read a p tag =>
              cases hc : st.cache (a, p) with
              | some v =>
                  apply pure_table_step order τ st ((lazyFrozen order τ (.read a p tag)).run st)
                    (fun g => (eagerFrozen order τ g (.read a p tag)).run st) (v, st) hg (fun _ => rfl) (Φ := Φ)
                  · simp [lazyFrozen, frozen, lazyImpl, impl, StateT.run, hb, hs, unerase, hc, erase, hreset]
                  · intro u; simp [eagerFrozen, frozen, eagerImpl, impl, StateT.run, hb, hs, unerase, hc, erase, hreset]
              | none =>
                  have hl := frozen_read_miss order τ (fun _ => $ᵗ HashOutput)
                    (fun b p target s =>
                      (fun h => pair.symm (lowHash h, target ^^^ others order s p b)) <$> ($ᵗ HashOutput))
                    st hb a p tag hc hs
                  have he (g : κ × ι → HashOutput) := frozen_read_miss order τ (fun y => pure (g y))
                    (fun b p _ _ => pure (g (b, p))) st hb a p tag hc hs
                  change (∀ z ∈ support _, _) ∧ (∀ u, ∀ z ∈ support _, _) ∧ _
                  simp only [lazyFrozen, lazyImpl, eagerFrozen, eagerImpl, hl, he, map_pure,
                    support_pure, Set.mem_singleton_iff]
                  refine ⟨?_, ?_, ?_⟩
                  · intro z hz
                    obtain ⟨v, _, rfl⟩ := mem_support_map_peel _ _ hz
                    exact good_put order hcover τ st hg a p v hc tag hs
                  · intro u z hz
                    subst z
                    exact ⟨good_put order hcover τ st hg a p _ hc tag hs,
                      fiberTable_put_eager order hn hcover τ st hg u a p hc tag hs⟩
                  · simp only [bind_map_left, pure_bind]
                    have hp : p ∉ st.done := fun hp => (hg.1 p hp).1 a hc
                    obtain ⟨b, hsb⟩ := good_slack order hcover τ st hg p hp
                    have hr : 𝒟[$ᵗ HashOutput >>= fun v => $ᵗ (κ × ι → HashOutput) >>= fun u =>
                        pure (v, fiberTable order τ (put st a p v) u)] =
                        𝒟[$ᵗ (κ × ι → HashOutput) >>= fun u =>
                            pure (fiberTable order τ st u (a, p), fiberTable order τ st u)] := by
                      by_cases hab : a = b
                      · subst b; exact read_table_slack order hn hcover τ st hg a p hc hsb tag hs
                      · exact read_table_ne order τ st a b p hc hab hsb
                    have hr' := congrArg (fun d => d >>= fun z => 𝒟[Φ (z.1, put st a p z.1) z.2]) hr
                    simpa only [← evalDist_bind, bind_assoc, pure_bind] using hr'
          | complete p target tag =>
              by_cases hp : p ∈ st.done
              · apply pure_table_step order τ st ((lazyFrozen order τ (.complete p target tag)).run st)
                  (fun g => (eagerFrozen order τ g (.complete p target tag)).run st)
                  (decide (sum order st p = target), st) hg (fun _ => rfl) (Φ := Φ)
                · simp [lazyFrozen, frozen, lazyImpl, impl, StateT.run, hb, hs, unerase, hp, erase, sum, low, hreset]
                · intro u; simp [eagerFrozen, frozen, eagerImpl, impl, StateT.run, hb, hs, unerase, hp, erase, sum, low, hreset]
              · have ht : target = τ p := by
                  by_contra ht
                  simp [setsBad, hp, ht] at hs
                subst target
                obtain ⟨b, hsb⟩ := good_slack order hcover τ st hg p hp
                have hl := lazyFrozen_complete order τ st hb p b tag hp hsb
                have he (u : κ × ι → HashOutput) := eagerFrozen_complete order τ
                  (fiberTable order τ st u) st hb p b tag hp hsb
                refine ⟨?_, ?_, ?_⟩
                · intro z hz
                  have hz' := (mem_support_iff_of_evalDist_eq hl z).mp hz
                  obtain ⟨s, hs', rfl⟩ := mem_support_map_peel _ _ hz'
                  exact completeLazy_good order hn hcover τ st hg p b hsb s hs'
                · intro u z hz
                  have hz' := (mem_support_iff_of_evalDist_eq (he u) z).mp hz
                  obtain ⟨s, hs', rfl⟩ := mem_support_map_peel _ _ hz'
                  exact completeEager_good_table order hn hcover τ st hg p b hp hsb u s hs'
                · rw [evalDist_bind, hl, ← evalDist_bind, bind_map_left]
                  calc
                    _ = 𝒟[do let u ← $ᵗ (κ × ι → HashOutput)
                             let g := fiberTable order τ st u
                             let s ← completeEager order g st p b
                             Φ (true, s) g] :=
                      completion_table order hn hcover τ st hg p b hp hsb (fun s g => Φ (true, s) g)
                    _ = _ := by
                      apply evalDist_bind_congr'
                      intro u
                      symm
                      rw [evalDist_bind, he u, ← evalDist_bind, bind_map_left]


/-- Full frozen lazy/eager law from every Good state, including states already carrying bad. -/
theorem lazyFrozen_eq_eagerFrozen [Fintype κ] [Fintype ι]
    [SampleableType (κ × ι → HashOutput)]
    (order : List κ) (hn : order.Nodup) (hcover : ∀ b, b ∈ order) (τ : ι → Digest)
    {α : Type} (oa : OracleComp (unifSpec + ShareSpec κ ι Tag) α)
    (st : ShareState κ ι (FrozenBad Tag)) (hg : Good order τ st) :
    𝒟[(simulateQ (unifImpl (ShareState κ ι (FrozenBad Tag)) + lazyFrozen (Tag := Tag) order τ) oa).run st] =
      𝒟[do let u ← $ᵗ (κ × ι → HashOutput)
           (simulateQ (unifImpl (ShareState κ ι (FrozenBad Tag)) +
             eagerFrozen (Tag := Tag) order τ (fiberTable order τ st u)) oa).run st] := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure]
      exact (DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _).symm
  | query_bind q k ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      cases q with
      | inl n =>
          simp only [QueryImpl.add_apply_inl, unifImpl, StateT.run, bind_map_left]
          calc
            _ = 𝒟[do let a ← $[0..n]; let u ← $ᵗ (κ × ι → HashOutput)
                     (simulateQ (unifImpl (ShareState κ ι (FrozenBad Tag)) +
                       eagerFrozen (Tag := Tag) order τ (fiberTable order τ st u)) (k a)).run st] := by
              apply evalDist_bind_congr'
              intro a
              exact ih a st hg
            _ = _ := DeferredSampling.evalDist_bind_comm _ _ _
      | inr q =>
          simp only [QueryImpl.add_apply_inr]
          let Φ := fun (z : (ShareSpec κ ι Tag).Range q × ShareState κ ι (FrozenBad Tag))
              (g : κ × ι → HashOutput) =>
            (simulateQ (unifImpl (ShareState κ ι (FrozenBad Tag)) +
              eagerFrozen (Tag := Tag) order τ g) (k z.1)).run z.2
          have hstep := frozen_step order hn hcover τ q st hg Φ
          calc
            _ = 𝒟[do let z ← (lazyFrozen order τ q).run st
                     let u ← $ᵗ (κ × ι → HashOutput)
                     Φ z (fiberTable order τ z.2 u)] := by
              apply evalDist_bind_congr
              intro z hz
              exact ih z.1 z.2 (hstep.1 z hz)
            _ = _ := hstep.2.2

/-- T2(a), specialized to the original lazy implementation. -/
theorem lazyImpl_frozen_nonbad (order : List κ) (τ : ι → Digest)
    {α : Type} (oa : OracleComp (unifSpec + ShareSpec κ ι Tag) α)
    (st : ShareState κ ι (ImplBad Tag)) (G : α × ShareState κ ι (FrozenBad Tag) → Prop) :
    Pr[fun z => G (z.1, erase z.2) ∧ z.2.bad = none |
      (simulateQ (unifImpl (ShareState κ ι (ImplBad Tag)) + lazyImpl (Tag := Tag) order τ) oa).run st] =
      Pr[fun z => G z ∧ z.2.bad = none |
        (simulateQ (unifImpl (ShareState κ ι (FrozenBad Tag)) + lazyFrozen (Tag := Tag) order τ) oa).run (erase st)] :=
  impl_frozen_nonbad order τ _ _ oa st G

/-- T2(b), retaining the lazy first-bad tag and kind through erasure. -/
theorem lazyImpl_frozen_firstbad (order : List κ) (τ : ι → Digest)
    {α : Type} (oa : OracleComp (unifSpec + ShareSpec κ ι Tag) α)
    (st : ShareState κ ι (ImplBad Tag)) (r : FrozenBad Tag) :
    Pr[fun z => (erase z.2).bad = some r |
      (simulateQ (unifImpl (ShareState κ ι (ImplBad Tag)) + lazyImpl (Tag := Tag) order τ) oa).run st] =
      Pr[fun z => z.2.bad = some r |
        (simulateQ (unifImpl (ShareState κ ι (FrozenBad Tag)) + lazyFrozen (Tag := Tag) order τ) oa).run (erase st)] :=
  impl_frozen_firstbad order τ _ _ oa st r

/-- T2(a) holds for every eager answer table, without a fiber assumption. -/
theorem eagerImpl_frozen_nonbad (order : List κ) (τ : ι → Digest) (g : κ × ι → HashOutput)
    {α : Type} (oa : OracleComp (unifSpec + ShareSpec κ ι Tag) α)
    (st : ShareState κ ι (ImplBad Tag)) (G : α × ShareState κ ι (FrozenBad Tag) → Prop) :
    Pr[fun z => G (z.1, erase z.2) ∧ z.2.bad = none |
      (simulateQ (unifImpl (ShareState κ ι (ImplBad Tag)) + eagerImpl (Tag := Tag) order τ g) oa).run st] =
      Pr[fun z => G z ∧ z.2.bad = none |
        (simulateQ (unifImpl (ShareState κ ι (FrozenBad Tag)) + eagerFrozen (Tag := Tag) order τ g) oa).run (erase st)] :=
  impl_frozen_nonbad order τ _ _ oa st G

/-- T2(b) holds for every eager answer table and transports no lucky bit. -/
theorem eagerImpl_frozen_firstbad (order : List κ) (τ : ι → Digest) (g : κ × ι → HashOutput)
    {α : Type} (oa : OracleComp (unifSpec + ShareSpec κ ι Tag) α)
    (st : ShareState κ ι (ImplBad Tag)) (r : FrozenBad Tag) :
    Pr[fun z => (erase z.2).bad = some r |
      (simulateQ (unifImpl (ShareState κ ι (ImplBad Tag)) + eagerImpl (Tag := Tag) order τ g) oa).run st] =
      Pr[fun z => z.2.bad = some r |
        (simulateQ (unifImpl (ShareState κ ι (FrozenBad Tag)) + eagerFrozen (Tag := Tag) order τ g) oa).run (erase st)] :=
  impl_frozen_firstbad order τ _ _ oa st r

end ThresholdLeanXmssSecurity.SigningShareLazy

/-- info: 'ThresholdLeanXmssSecurity.SigningShareLazy.good_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningShareLazy.good_init

/-- info: 'ThresholdLeanXmssSecurity.SigningShareLazy.lazyFrozen_eq_eagerFrozen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningShareLazy.lazyFrozen_eq_eagerFrozen

/-- info: 'ThresholdLeanXmssSecurity.SigningShareLazy.untilBad_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningShareLazy.untilBad_proj

/-- info: 'ThresholdLeanXmssSecurity.SigningShareLazy.lazyImpl_frozen_nonbad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningShareLazy.lazyImpl_frozen_nonbad

/-- info: 'ThresholdLeanXmssSecurity.SigningShareLazy.lazyImpl_frozen_firstbad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningShareLazy.lazyImpl_frozen_firstbad

/-- info: 'ThresholdLeanXmssSecurity.SigningShareLazy.eagerImpl_frozen_nonbad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningShareLazy.eagerImpl_frozen_nonbad

/-- info: 'ThresholdLeanXmssSecurity.SigningShareLazy.eagerImpl_frozen_firstbad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningShareLazy.eagerImpl_frozen_firstbad

/-- info: 'ThresholdLeanXmssSecurity.SigningShareLazy.lazy_lucky_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningShareLazy.lazy_lucky_ratio

/-- info: 'ThresholdLeanXmssSecurity.SigningShareLazy.fiberTable_init_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningShareLazy.fiberTable_init_cons

/-- info: 'ThresholdLeanXmssSecurity.SigningShareLazy.fiberTable_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningShareLazy.fiberTable_nil

/-- info: 'ThresholdLeanXmssSecurity.SigningShareLazy.evalDist_slackMove' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningShareLazy.evalDist_slackMove
