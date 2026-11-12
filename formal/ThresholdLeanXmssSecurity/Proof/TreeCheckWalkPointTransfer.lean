import LeanXmss.Bytes
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkEncoding
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkEntry
import ThresholdLeanXmssSecurity.Proof.TreeKey
import XmssSecurity.Proof.QueryBoundSupport

/-!
# Successful local-prefix identification at signing

A distinguished query marks the start of a continuation. A canonical local
prefix makes no such query, and its entire continuation makes at most one.
Equality of the full programs therefore identifies every
successful alternative prefix at the same state and the same continuation.

The free-program head observations below generalize the constant-range
`headQuery` and `query_bind_inj` from pinned leanVM's
`XmssSecurity/Proof/Bridge/Basic.lean` to dependent oracle ranges. The concrete
query bound uses the pinned `LeanXmss.Bytes` address injectivity and structural
walks from `TreeSimHashCount`, `TreeCheckNoCommit` and `SigningSelection`.

`head_transfer` applies to arbitrary matching points, arbitrary initial world
states, and successful heads. It preserves the choice and the complete final
world state; it does not require the points' saved output lists to be equal.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section

namespace ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer

attribute [local instance] Classical.propDecidable

section Prefix

variable {ι α σ : Type} {spec : OracleSpec ι}

/-- The first query, together with its dependently typed continuation. -/
def headQuery : OracleComp spec α → Option (Σ t, spec.Range t → OracleComp spec α)
  | .pure _ => none
  | .roll t k => some ⟨t, k⟩

theorem query_bind_inj {t u : ι} {k : spec.Range t → OracleComp spec α}
    {l : spec.Range u → OracleComp spec α}
    (he : (OracleComp.lift (spec.query t) >>= k) = OracleComp.lift (spec.query u) >>= l) :
    (Sigma.mk t k : Σ t, spec.Range t → OracleComp spec α) = Sigma.mk u l := by
  exact Option.some.inj (congrArg headQuery he)

theorem query_bind_ne_pure (t : ι) (k : spec.Range t → OracleComp spec α) (a : α) :
    (OracleComp.lift (spec.query t) >>= k) ≠ pure a := by
  intro he
  exact Option.some_ne_none _ (congrArg headQuery he)

/-- A marked query is the first instruction of the continuation. -/
def StartsIn (marked : ι → Prop) (p : OracleComp spec α) : Prop :=
  ∃ t k, marked t ∧ p = OracleComp.lift (spec.query t) >>= k

theorem StartsIn.not_zero {marked : ι → Prop} {p : OracleComp spec α}
    (hp : StartsIn marked p) : ¬ IsQueryBoundP p marked 0 := by
  obtain ⟨t, k, ht, rfl⟩ := hp
  rw [isQueryBoundP_query_bind_iff]
  rintro ⟨h, -⟩
  exact h.elim (fun hn => hn ht) (by omega)

set_option backward.isDefEq.respectTransparency false in
/-- A zero marked-query budget excludes every successful gate branch that
would enter a marked continuation. -/
theorem no_success_of_zero (marked : ι → Prop) (aborted : α)
    (gate : OracleComp spec (Option Unit)) (rest : OracleComp spec α)
    (root : StartsIn marked rest)
    (budget : IsQueryBoundP (TreeCheckWalkRecipe.localContinue aborted gate (fun _ => rest)) marked 0) :
    some () ∉ support gate := by
  intro hs
  unfold TreeCheckWalkRecipe.localContinue at budget
  have h := OracleComp.IsQueryBoundP.continuation_mono_of_mem_support marked _ _ 0 budget (some ()) hs
  exact root.not_zero h

theorem simulated_support (impl : QueryImpl spec (StateT σ ProbComp))
    (p : OracleComp spec α) (s : σ) (r : α × σ)
    (hr : r ∈ support ((simulateQ impl p).run s)) : r.1 ∈ support p := by
  apply support_simulateQ_run'_subset impl p s
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ hr

set_option backward.isDefEq.respectTransparency false in
/-- Equality of full programs identifies successful prefixes before a unique
marked continuation. The conclusion retains the literal final state. -/
theorem prefix_transfer (marked : ι → Prop) (aborted : α)
    (rest rest₀ : OracleComp spec α) (root : StartsIn marked rest)
    (root₀ : StartsIn marked rest₀) (gate₀ : OracleComp spec (Option Unit))
    (quiet : IsQueryBoundP gate₀ marked 0) :
    ∀ (gate : OracleComp spec (Option Unit)),
      IsQueryBoundP (TreeCheckWalkRecipe.localContinue aborted gate (fun _ => rest)) marked 1 →
      TreeCheckWalkRecipe.localContinue aborted gate (fun _ => rest) =
        TreeCheckWalkRecipe.localContinue aborted gate₀ (fun _ => rest₀) →
      ∀ (impl : QueryImpl spec (StateT σ ProbComp)) (s final : σ),
        (some (), final) ∈ support ((simulateQ impl gate).run s) →
        (some (), final) ∈ support ((simulateQ impl gate₀).run s) ∧ rest = rest₀ := by
  induction gate₀ using OracleComp.inductionOn with
  | pure value =>
    intro gate budget same impl s final run
    induction gate using OracleComp.inductionOn with
    | pure out =>
      have ho : out = some () := by
        have he : (some (), final) = (out, s) := by simpa using run
        exact (congrArg Prod.fst he).symm
      subst out
      cases value with
      | none =>
        have he : rest = pure aborted := by simpa [TreeCheckWalkRecipe.localContinue] using same
        obtain ⟨t, k, _, hr⟩ := root
        exact (query_bind_ne_pure t k aborted (hr.symm.trans he)).elim
      | some u =>
        cases u
        exact ⟨run, by simpa [TreeCheckWalkRecipe.localContinue] using same⟩
    | query_bind t k _ =>
      cases value with
      | none =>
        simp [TreeCheckWalkRecipe.localContinue] at same
      | some u =>
        obtain ⟨q, l, hq, hr⟩ := root₀
        have eqh := query_bind_inj (show
          (OracleComp.lift (spec.query t) >>= fun a =>
            TreeCheckWalkRecipe.localContinue aborted (k a) (fun _ => rest)) =
              OracleComp.lift (spec.query q) >>= l from by
          simpa [TreeCheckWalkRecipe.localContinue, hr] using same)
        have ht : t = q := congrArg Sigma.fst eqh
        have counted : marked t := ht.symm ▸ hq
        change IsQueryBoundP (OracleComp.lift (spec.query t) >>= fun a =>
          TreeCheckWalkRecipe.localContinue aborted (k a) (fun _ => rest)) marked 1 at budget
        rw [isQueryBoundP_query_bind_iff] at budget
        have hs := simulated_support impl (.roll t k) s (some (), final) run
        change some () ∈ support (OracleComp.lift (spec.query t) >>= k) at hs
        rw [mem_support_bind_iff] at hs
        obtain ⟨a, _, hs⟩ := hs
        exact (no_success_of_zero marked aborted (k a) rest root
          (by simpa [counted] using budget.2 a) hs).elim
  | query_bind q l ih =>
    rw [isQueryBoundP_query_bind_iff] at quiet
    have unmarked : ¬ marked q := quiet.1.resolve_right (by omega)
    intro gate budget same impl s final run
    induction gate using OracleComp.inductionOn with
    | pure out =>
      cases out with
      | none =>
        simp [TreeCheckWalkRecipe.localContinue] at same
      | some u =>
        obtain ⟨t, k, ht, hr⟩ := root
        have eqh := query_bind_inj (show
          (OracleComp.lift (spec.query t) >>= k) = OracleComp.lift (spec.query q) >>=
            (fun a => TreeCheckWalkRecipe.localContinue aborted (l a) (fun _ => rest₀)) from by
          simpa [TreeCheckWalkRecipe.localContinue, hr] using same)
        have he : t = q := congrArg Sigma.fst eqh
        exact (unmarked (he ▸ ht)).elim
    | query_bind t k _ =>
      have eqh := query_bind_inj (show
        (OracleComp.lift (spec.query t) >>= fun a =>
          TreeCheckWalkRecipe.localContinue aborted (k a) (fun _ => rest)) =
        OracleComp.lift (spec.query q) >>= fun a =>
          TreeCheckWalkRecipe.localContinue aborted (l a) (fun _ => rest₀) from by
        simpa [TreeCheckWalkRecipe.localContinue] using same)
      have ht : t = q := congrArg Sigma.fst eqh
      subst t
      have tails : (fun a => TreeCheckWalkRecipe.localContinue aborted (k a) (fun _ => rest)) =
          (fun a => TreeCheckWalkRecipe.localContinue aborted (l a) (fun _ => rest₀)) := by
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using eqh
      change IsQueryBoundP (OracleComp.lift (spec.query q) >>= fun a =>
        TreeCheckWalkRecipe.localContinue aborted (k a) (fun _ => rest)) marked 1 at budget
      rw [isQueryBoundP_query_bind_iff] at budget
      change (some (), final) ∈ support ((impl q >>= fun a => simulateQ impl (k a)).run s) at run
      rw [StateT.run_bind, mem_support_bind_iff] at run
      obtain ⟨r, hr, run⟩ := run
      obtain ⟨run₀, sameRest⟩ := ih r.1 (by simpa [unmarked] using quiet.2 r.1)
        (k r.1) (by simpa [unmarked] using budget.2 r.1) (congrFun tails r.1)
        impl r.2 final run
      refine ⟨?_, sameRest⟩
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      exact ⟨r, hr, run₀⟩

end Prefix

section FirstLeaf

/-- The leftmost leaf index of a Merkle subtree, reduced as in `merkleNode`. -/
def leftmostKey (height idx : ℕ) : KeyIndex :=
  ⟨(2 ^ height * idx) % lifetime, Nat.mod_lt _ (by decide)⟩

theorem leftmostKey_zero (idx : ℕ) :
    leftmostKey 0 idx = ⟨idx % lifetime, Nat.mod_lt _ (by decide)⟩ := by
  apply Fin.ext
  simp [leftmostKey]

theorem leftmostKey_succ (height idx : ℕ) :
    leftmostKey (height + 1) idx = leftmostKey height (2 * idx) := by
  apply Fin.ext
  simp only [leftmostKey, Nat.pow_succ, Nat.mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Every Merkle computation starts with the hash of its leftmost leaf. -/
theorem merkleNode_head (parameter : PublicParameter) (lay : Layer)
    (ends : KeyIndex → ChainIndex → Digest) (height idx : ℕ) :
    ∃ next : HashOutput → OracleComp HashSpec Digest,
      merkleNode parameter lay ends height idx =
        OracleComp.lift (HashSpec.query (tweakableHashInput parameter
          (.leaf lay (leftmostKey height idx)) (Concrete.leafPayload (ends (leftmostKey height idx))))) >>=
            next := by
  induction height generalizing idx with
  | zero =>
    refine ⟨fun x => pure (truncateHash x), ?_⟩
    rw [leftmostKey_zero]
    rfl
  | succ height ih =>
    obtain ⟨next, hn⟩ := ih (2 * idx)
    rw [merkleNode, hn, bind_assoc, leftmostKey_succ]
    exact ⟨_, rfl⟩

/-- The distinguished public query domain, independently of its payload. -/
def LeafQuery (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (input : HashInput) : Prop :=
  ∃ payload, input = tweakableHashInput parameter (.leaf lay key) payload

theorem merkleNode_starts (parameter : PublicParameter) (lay : Layer)
    (ends : KeyIndex → ChainIndex → Digest) (height idx : ℕ) :
    StartsIn (LeafQuery parameter lay (leftmostKey height idx))
      (merkleNode parameter lay ends height idx) := by
  obtain ⟨next, he⟩ := merkleNode_head parameter lay ends height idx
  exact ⟨_, next, ⟨_, rfl⟩, he⟩

end FirstLeaf

section PublicCancellation

variable {C : Committee} {E α : Type}

/-- A public hash as a literal local query of a party program. -/
def publicQ (input : HashInput) : OracleComp (PartySpec C E RealSpec) HashOutput :=
  OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
    (.inl (.inl (.inr (.inl (.hash input))))))

def publicComp (p : OracleComp HashSpec α) : OracleComp (PartySpec C E RealSpec) α :=
  simulateQ publicQ p

set_option backward.isDefEq.respectTransparency false in
theorem publicQ_bind_inj (q q' : HashInput)
    (k k' : HashOutput → OracleComp (PartySpec C E RealSpec) α)
    (he : publicQ q >>= k = publicQ q' >>= k') : q = q' ∧ k = k' := by
  have h := query_bind_inj he
  have hq : q = q' := by
    simpa only [Sum.inl.injEq, Sum.inr.injEq, Query.hash.injEq] using congrArg Sigma.fst h
  subst q'
  refine ⟨rfl, ?_⟩
  simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h

set_option backward.isDefEq.respectTransparency false in
/-- A tweakable hash exposes its input and has every digest as a possible
answer. Therefore an equality of suffixed computations cancels the suffix. -/
theorem public_hash_cancel (parameter : PublicParameter) (domain : HashDomain)
    (payload payload' : HashInput) (k k' : Digest → OracleComp (PartySpec C E RealSpec) α)
    (he : publicComp (Concrete.tweakableHash parameter domain payload) >>= k =
      publicComp (Concrete.tweakableHash parameter domain payload') >>= k') :
    (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest) =
      Concrete.tweakableHash parameter domain payload' ∧ k = k' := by
  have he' : publicQ (tweakableHashInput parameter domain payload) >>=
      (fun h => k (truncateHash h)) = publicQ (tweakableHashInput parameter domain payload') >>=
      (fun h => k' (truncateHash h)) := by
    simpa [publicComp, Concrete.tweakableHash, Concrete.oracleHash] using he
  obtain ⟨hq, hk⟩ := publicQ_bind_inj _ _ _ _ he'
  constructor
  · exact congrArg (fun q => (truncateHash <$> OracleComp.lift (HashSpec.query q))) hq
  · funext d
    have hd := congrFun hk (keygenFullParameter 0 d)
    simpa only [truncate_keygenFullParameter] using hd

/-- Merkle prefixes of the same shape can be cancelled before arbitrary
party continuations. Their full oracle programs, and their suffixes, agree. -/
theorem merkle_cancel (parameter : PublicParameter) (lay : Layer)
    (ends ends' : KeyIndex → ChainIndex → Digest) (height idx : ℕ) :
    ∀ (k k' : Digest → OracleComp (PartySpec C E RealSpec) α),
      (publicComp (merkleNode parameter lay ends height idx) >>= k) =
        publicComp (merkleNode parameter lay ends' height idx) >>= k' →
      merkleNode parameter lay ends height idx = merkleNode parameter lay ends' height idx ∧
        k = k' := by
  induction height generalizing idx with
  | zero =>
    intro k k' he
    exact public_hash_cancel parameter _ _ _ k k' he
  | succ height ih =>
    intro k k' he
    simp only [merkleNode, publicComp, simulateQ_bind, bind_assoc] at he
    obtain ⟨left, tails⟩ := ih (2 * idx) _ _ he
    have tail := congrFun tails 0
    obtain ⟨right, nodes⟩ := ih (2 * idx + 1) _ _ tail
    obtain ⟨_, next⟩ := public_hash_cancel parameter _ _ _ k k' (congrFun nodes 0)
    refine ⟨?_, next⟩
    simp only [merkleNode, left, right]

set_option backward.isDefEq.respectTransparency false in
/-- Equality of arbitrary suffixed signing programs determines the complete
public-choice program, including its Merkle and randomizer inputs. -/
theorem publicChoice_cancel (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (outputs outputs' : List (List Bit))
    (k k' : Option TreeCheckWalkRecipe.PublicChoice → OracleComp (PartySpec C E RealSpec) α)
    (he : publicComp (treeLockstepPublicChoiceCode parameter b outputs) >>= k =
      publicComp (treeLockstepPublicChoiceCode parameter b outputs') >>= k') :
    treeLockstepPublicChoiceCode parameter b outputs =
      treeLockstepPublicChoiceCode parameter b outputs' := by
  unfold treeLockstepPublicChoiceCode at he ⊢
  dsimp only at he ⊢
  simp only [publicComp, simulateQ_bind, bind_assoc] at he
  obtain ⟨merkle, tails⟩ := merkle_cancel parameter bottomLayer _ _ layerHeight b.val _ _ he
  rw [merkle]
  refine bind_congr fun root => ?_
  have ht := congrFun tails root
  simp only [simulateQ_map, bind_map_left, Concrete.oracleHash] at ht
  obtain ⟨input, _⟩ := publicQ_bind_inj _ _ _ _ ht
  dsimp at input
  simp only [Concrete.oracleHash]
  rw [input]

end PublicCancellation

section SigningRest

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local irreducible] treeLockstepPublicChoiceCode

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
set_option backward.isDefEq.respectTransparency false in
theorem publicComp_lift {α : Type} (p : OracleComp HashSpec α) :
    publicComp (C := C) (E := E) p =
      liftComp (liftComp (tweakable (C := C) p) (LocalSpec C)) (PartySpec C E RealSpec) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [publicComp, tweakable]
  | query_bind q k ih =>
    simp only [publicComp, simulateQ_bind, simulateQ_spec_query, tweakable,
      liftComp_bind] at ih ⊢
    simp_rw [← ih]
    rfl

omit [Fintype E] [DecidableEq E] in
set_option backward.isDefEq.respectTransparency false in
theorem firstRest_run (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) (records : List (TreeSimCheckBatchRecord C)) (initial : ℕ × ℕ) :
    (treeLockstepFirstRest K circuits settings ctx top (.bottom b) ((some outputs, records), initial)).run =
      publicComp (treeLockstepPublicChoiceCode ctx.keys.parameter b outputs) >>= fun c =>
        match c with
        | none => pure none
        | some c => (TreeCheckWalkRecipe.signingCont K circuits settings ctx top b outputs records
            initial c).run := by
  rw [publicComp_lift]
  simp only [treeLockstepFirstRest, oracleStep, OptionT.run_bind,
    TreeCheckWalkRecipe.signingCont, localStep, OptionT.lift, OptionT.run_mk,
    Option.elimM, bind_assoc, pure_bind]
  apply bind_congr
  intro c
  rcases c with _ | ⟨root, randomness, enc⟩
  · rfl
  · simp only [Option.elim, OptionT.run_bind, Option.elimM]

omit [Fintype E] [DecidableEq E] in
/-- Equal actual continuations have the same public-choice code, without
assuming equality of their saved output lists or records. -/
theorem publicChoice_of_rest (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (outputs outputs' : List (List Bit)) (records records' : List (TreeSimCheckBatchRecord C))
    (initial : ℕ × ℕ)
    (he : (treeLockstepFirstRest K circuits settings ctx top (.bottom b)
        ((some outputs, records), initial)).run =
      (treeLockstepFirstRest K circuits settings ctx top (.bottom b)
        ((some outputs', records'), initial)).run) :
    treeLockstepPublicChoiceCode ctx.keys.parameter b outputs =
      treeLockstepPublicChoiceCode ctx.keys.parameter b outputs' := by
  rw [firstRest_run, firstRest_run] at he
  exact publicChoice_cancel _ _ _ _ _ _ he

end SigningRest

section MarkedRest

variable {C : Committee} {E : Type}

def LocalLeaf (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) :
    (LocalSpec C).Domain → Prop
  | .inr (.inl (.hash input)) => LeafQuery parameter bottomLayer (leftmostKey layerHeight b.val) input
  | _ => False

def LocalHash : (LocalSpec C).Domain → Prop
  | .inr (.inl (.hash _)) => True
  | _ => False

abbrev PartyLeaf (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) :
    (PartySpec C E RealSpec).Domain → Prop := TreeSimHashCount.PartyQuery (LocalLeaf parameter b)

set_option backward.isDefEq.respectTransparency false in
theorem publicChoice_head (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) :
    StartsIn (LeafQuery parameter bottomLayer (leftmostKey layerHeight b.val))
      (treeLockstepPublicChoiceCode parameter b outputs) := by
  unfold treeLockstepPublicChoiceCode
  dsimp only
  obtain ⟨t, next, ht, he⟩ := merkleNode_starts parameter bottomLayer _ layerHeight b.val
  rw [he, bind_assoc]
  exact ⟨t, _, ht, rfl⟩

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

omit [Fintype E] [DecidableEq E] in
set_option backward.isDefEq.respectTransparency false in
theorem firstRest_starts (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) (records : List (TreeSimCheckBatchRecord C)) (initial : ℕ × ℕ) :
    StartsIn (PartyLeaf ctx.keys.parameter b)
      (treeLockstepFirstRest K circuits settings ctx top (.bottom b) ((some outputs, records), initial)).run := by
  rw [firstRest_run]
  obtain ⟨q, next, hq, he⟩ := publicChoice_head ctx.keys.parameter b outputs
  rw [he]
  simp only [publicComp, simulateQ_bind, simulateQ_spec_query, bind_assoc]
  exact ⟨.inl (.inl (.inr (.inl (.hash q)))), _, hq, rfl⟩

end MarkedRest

section LocalTransfer

variable {C : Committee} {E α σ : Type}

/-- An arbitrary local handler extends to party queries. Only its local
branch is used when interpreting a lifted local prefix. -/
def extendLocal (impl : QueryImpl (LocalSpec C) (StateT σ ProbComp)) :
    QueryImpl (PartySpec C E RealSpec) (StateT σ ProbComp)
  | .inl (.inl q) => impl q
  | .inl (.inr _) => pure (fun _ => none)
  | .inr impossible => nomatch impossible

set_option backward.isDefEq.respectTransparency false in
theorem simulateQ_extendLocal (impl : QueryImpl (LocalSpec C) (StateT σ ProbComp))
    (p : OracleComp (LocalSpec C) α) :
    simulateQ (extendLocal (E := E) impl) (liftComp p (PartySpec C E RealSpec)) = simulateQ impl p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [liftComp_bind, simulateQ_bind, simulateQ_spec_query]
    simp_rw [ih]
    simp only [OracleComp.liftComp, simulateQ_spec_query]
    rw [simulateQ_liftM_query]
    have hl : (liftM (OracleSpec.query (spec := LocalSpec C) t) :
        OracleQuery (PartySpec C E RealSpec) ((LocalSpec C).Range t)) =
        OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl t)) := by
      rcases t with u | q | x <;> rfl
    rw [hl]
    simp [QueryImpl.mapQuery, extendLocal]

set_option backward.isDefEq.respectTransparency false in
theorem noHash_lift_leaf (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (p : OracleComp (LocalSpec C) α) (hp : IsQueryBoundP p LocalHash 0) :
    IsQueryBoundP (liftComp p (PartySpec C E RealSpec)) (PartyLeaf parameter b) 0 := by
  apply qb0_liftComp p hp
  intro t ht
  rcases t with u | q | x
  all_goals erw [isQueryBoundP_query_iff]
  all_goals try { simp [PartyLeaf, TreeSimHashCount.PartyQuery, LocalLeaf]; done }
  cases q <;> simp_all [PartyLeaf, TreeSimHashCount.PartyQuery, LocalLeaf, LocalHash]

/-- The successful-prefix theorem specialized to actual local computations
inside party programs, with the canonical continuation's one-leaf bound. -/
theorem local_prefix_transfer (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (aborted : α) (rest rest₀ : OracleComp (PartySpec C E RealSpec) α)
    (root : StartsIn (PartyLeaf parameter b) rest) (root₀ : StartsIn (PartyLeaf parameter b) rest₀)
    (gate gate₀ : OracleComp (LocalSpec C) (Option Unit))
    (quiet : IsQueryBoundP gate₀ LocalHash 0)
    (once : IsQueryBoundP rest₀ (PartyLeaf parameter b) 1)
    (same : TreeCheckWalkRecipe.localContinue aborted (liftComp gate (PartySpec C E RealSpec))
        (fun _ => rest) = TreeCheckWalkRecipe.localContinue aborted
          (liftComp gate₀ (PartySpec C E RealSpec)) (fun _ => rest₀))
    (impl : QueryImpl (LocalSpec C) (StateT σ ProbComp)) (s final : σ)
    (run : (some (), final) ∈ support ((simulateQ impl gate).run s)) :
    (some (), final) ∈ support ((simulateQ impl gate₀).run s) ∧ rest = rest₀ := by
  have hq := noHash_lift_leaf (E := E) parameter b gate₀ quiet
  have hb : IsQueryBoundP (TreeCheckWalkRecipe.localContinue aborted
      (liftComp gate (PartySpec C E RealSpec)) (fun _ => rest)) (PartyLeaf parameter b) 1 := by
    rw [same]
    unfold TreeCheckWalkRecipe.localContinue
    apply isQueryBoundP_bind (n := 0) (m := 1) hq
    intro a _
    cases a
    · exact isQueryBoundP_pure _ _ _
    · exact once
  have h := prefix_transfer (PartyLeaf parameter b) aborted rest rest₀ root root₀
    _ hq _ hb same (extendLocal impl) s final (by simpa only [simulateQ_extendLocal] using run)
  simpa only [simulateQ_extendLocal] using h

end LocalTransfer

section HeadTransfer

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local irreducible] treeLockstepPublicChoiceCode

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
set_option backward.isDefEq.respectTransparency false in
theorem prelude_run {α : Type} (gate : OracleComp (LocalSpec C) (Option Unit))
    (rest : PartyM C E RealSpec α) :
    (treeLockstepLocalPrelude gate >>= fun _ => rest).run =
      TreeCheckWalkRecipe.localContinue none (liftComp gate (PartySpec C E RealSpec))
        (fun _ => rest.run) := by
  simp only [treeLockstepLocalPrelude, bind_assoc, localStep, OptionT.run_bind,
    OptionT.lift, OptionT.run_mk, Option.elimM, pure_bind, TreeCheckWalkRecipe.localContinue]
  apply bind_congr
  intro out
  rcases out with _ | ⟨⟩ <;> simp [failure, OptionT.fail]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
def localWorld (prims : Primitives) (D : C.Coalition) :
    QueryImpl (LocalSpec C) (StateT (TreeSimState C) ProbComp) :=
  fun t => simulateQ (treeSimLoggedWorld prims D) (free (OracleComp.lift (OracleSpec.query t)))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem localWorld_run (prims : Primitives) (D : C.Coalition) {α : Type}
    (p : OracleComp (LocalSpec C) α) :
    simulateQ (localWorld prims D) p = simulateQ (treeSimLoggedWorld prims D) (free p) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [free_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, free_bind]
    simp_rw [ih]
    rfl

omit [Fintype E] [DecidableEq E] in
/-- Successful signing heads transfer across matching full programs once
the canonical continuation's unique first-leaf query is certified. -/
theorem signingHead_transfer_of_bound (prims : Primitives) (D : C.Coalition)
    (K : Constants C E) (circuits : Circuits) (settings : Settings) (ctx : Context C)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (outputs outputs₀ : List (List Bit))
    (records records₀ : List (TreeSimCheckBatchRecord C)) (initial : ℕ × ℕ)
    (gate gate₀ : OracleComp (LocalSpec C) (Option Unit))
    (quiet : IsQueryBoundP gate₀ LocalHash 0)
    (once : IsQueryBoundP (treeLockstepFirstRest K circuits settings ctx top (.bottom b)
      ((some outputs₀, records₀), initial)).run (PartyLeaf ctx.keys.parameter b) 1)
    (same : (treeLockstepLocalPrelude gate >>= fun _ => treeLockstepFirstRest K circuits settings
      ctx top (.bottom b) ((some outputs, records), initial)) =
      (treeLockstepLocalPrelude gate₀ >>= fun _ => treeLockstepFirstRest K circuits settings
        ctx top (.bottom b) ((some outputs₀, records₀), initial)))
    (s final : TreeSimState C) (choice : TreeCheckWalkRecipe.PublicChoice)
    (run : (some choice, final) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (TreeCheckWalkRecipe.signingHead ctx.keys.parameter b outputs gate))).run s)) :
    (some choice, final) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (TreeCheckWalkRecipe.signingHead ctx.keys.parameter b outputs₀ gate₀))).run s) := by
  obtain ⟨middle, tail, head⟩ := TreeCheckWalkEncoding.head_split prims D _ _ _ _ _ _ _ run
  have sameRun := congrArg OptionT.run same
  rw [prelude_run, prelude_run] at sameRun
  have transferred := local_prefix_transfer ctx.keys.parameter b none _ _
    (firstRest_starts K circuits settings ctx top b outputs records initial)
    (firstRest_starts K circuits settings ctx top b outputs₀ records₀ initial)
    gate gate₀ quiet once sameRun (localWorld prims D) s middle
    (by simpa only [localWorld_run] using tail)
  have code := publicChoice_of_rest K circuits settings ctx top b outputs outputs₀ records records₀
    initial transferred.2
  rw [code] at head
  unfold TreeCheckWalkRecipe.signingHead
  simp only [free_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  refine ⟨(some (), middle), ?_, ?_⟩
  · simpa only [localWorld_run] using transferred.1
  · exact head

end HeadTransfer

namespace HashQuiet

open TreeSimHashCount

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]
variable {ι α : Type} {G : OracleSpec ι}

omit [Field E] [Algebra Bit E] in
theorem party_of_all {p : PartyM C E G α} {n : ℕ} (h : PartyBound p n) :
    PartyBudget LocalHash p n := by
  apply IsQueryBoundP.of_imp _ h
  rintro ((q | out) | input) ht
  · rcases q with noise | query
    · exact ht.elim
    · trivial
  · exact ht.elim
  · exact ht.elim

omit [Field E] [Algebra Bit E] in
theorem run_of_zero {p : RunM C E G α} (h : RunBound p 0) :
    RunBudget LocalHash p 0 := fun s => party_of_all (h s)

variable (K : Constants C E)

/-- The structural bounds of `TreeSimHashCount` and `TreeCheckNoCommit`,
with the predicate selecting exactly public `.hash` queries. -/
theorem prg_zero (name : KeyName C) (key : HashOutput) (label idx count : ℕ) :
    IsQueryBoundP (prgBits name key label idx count)
      (fun t => LocalHash (C := C) (.inr t)) 0 := by
  unfold prgBits
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
  have h := queryBound_mapM (fun t => LocalHash (C := C) (.inr t))
    (fun position => (query (spec := RoSpec C) (.inr (name, key, label, idx, position)) :
      OracleComp (RoSpec C) Bit)) 0 (List.range count) (fun position _ => ?_)
  · simpa using h
  · change IsQueryBoundP (OracleComp.lift (OracleSpec.query
      (spec := RoSpec C) (.inr (name, key, label, idx, position)))) _ 0
    rw [isQueryBoundP_query_iff]
    simp [LocalHash]

theorem prss_zero {R : Type} [Zero R] (ctx : Context C)
    (codec : Codec C E R)
    (hd : ∀ name key label idx count, IsQueryBoundP (codec.draw name key label idx count)
      (fun t => LocalHash (C := C) (.inr t)) 0) (idx count : ℕ) :
    RunBudget LocalHash (prssRandomness ctx codec idx count : RunM C E G _) 0 := by
  unfold prssRandomness
  refine (run_of_zero
    (RunBound.freshLabel (C := C) (E := E) (G := G))).bind (m := 0) (fun label => ?_)
  refine (RunBudget.lift (oracle_bound (n := 0) ?_)).bind
    (m := 0) (fun r => ?_)
  · simpa using queryBound_mapM (fun t => LocalHash (C := C) (.inr t))
      (fun T => if ctx.self ∈ C.holders T then codec.draw (.term T) (ctx.prss.term T) label idx count
        else pure fun _ => 0) 0 C.terms (fun T _ => by
          split_ifs
          · exact hd _ _ _ _ _
          · exact isQueryBoundP_pure _ _ _)
  · refine (RunBudget.lift (oracle_bound (n := 0) ?_)).bind
      (m := 0) (fun Z => .pure _ 0)
    simpa using queryBound_mapM (fun t => LocalHash (C := C) (.inr t))
      (fun j => if h : j = ctx.self then pure fun _ => 0
        else codec.draw (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) label idx count)
      0 C.parties (fun j _ => by
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · exact hd _ _ _ _ _)

theorem reshare_zero {R : Type} [Field R] (ctx : Context C)
    (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R) (count : ℕ) :
    RunBudget LocalHash (reshare K ctx codec randomness v count : RunM C E G _) 0 := by
  apply run_of_zero
  unfold reshare
  exact (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun inbox =>
    (RunBound.record K ctx codec .peer _ count).bind (m := 0) (fun _ => RunBound.pure _))

structure GadgetBounds (gadgets : CheckGadgets C E G) : Prop where
  coin : ∀ count, RunBudget LocalHash (gadgets.coin count) 0
  mult : ∀ products, RunBudget LocalHash (gadgets.extendMult products) 0
  elements : ∀ count, RunBudget LocalHash (gadgets.randElements count) 0
  bits : ∀ count, RunBudget LocalHash (gadgets.randBits count) 0

theorem gadgets_zero (ctx : Context C) :
    GadgetBounds (realCheckGadgets K ctx : CheckGadgets C E G) := by
  have hd : ∀ name key label idx count, IsQueryBoundP
      ((elementCodec K).draw name key label idx count)
      (fun t => LocalHash (C := C) (.inr t)) 0 := by
    intro name key label idx count
    unfold elementCodec
    exact isQueryBoundP_bind (prg_zero name key label idx _)
      (fun _ _ => isQueryBoundP_pure _ _ 0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro count
    change RunBudget LocalHash
      (prssRandomness ctx (elementCodec K) 1 count >>= fun r => coinWith K ctx r count) 0
    refine (prss_zero ctx (elementCodec K) hd 1 count).bind (m := 0) (fun r => ?_)
    unfold coinWith
    exact (RunBudget.lift (party_of_all (RunBound.openSh K ctx _ count))).bind
      (m := 0) (fun _ => .pure _ 0)
  · intro products
    change RunBudget LocalHash
      (prssRandomness ctx (elementCodec K) 0 products.length >>= fun r =>
        reshare K ctx (elementCodec K) r _ products.length) 0
    exact (prss_zero ctx (elementCodec K) hd 0 products.length).bind
      (m := 0) (fun r => reshare_zero K ctx _ r _ _)
  · intro count
    exact prss_zero ctx (elementCodec K) hd 1 count
  · intro count
    exact prss_zero ctx bitCodec prg_zero 2 count

theorem hash_zero (q : Query C) (hq : ¬ LocalHash (.inr (.inl q))) :
    IsQueryBoundP (hashQuery q) (fun t => LocalHash (C := C) (.inr t)) 0 := by
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl q))) _ 0
  rw [isQueryBoundP_query_iff]
  exact fun h => (hq h).elim

theorem findChallenge_zero (key : HashOutput) (tries index : ℕ) :
    IsQueryBoundP (findChallenge K key tries index)
      (fun t => LocalHash (C := C) (.inr t)) 0 := by
  induction tries generalizing index with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ tries ih =>
    unfold findChallenge
    refine isQueryBoundP_bind (n := 0) (m := 0)
      (hash_zero _ (by simp [LocalHash])) (fun h _ => ?_)
    dsimp only
    split
    · exact isQueryBoundP_pure _ _ _
    · exact ih _

theorem expand_zero (key : HashOutput) (count : ℕ) :
    RunBudget LocalHash (expand K key count : RunM C E G _) 0 := by
  unfold expand
  apply RunBudget.lift
  apply oracle_bound
  simpa using queryBound_mapM (fun t => LocalHash (C := C) (.inr t))
    (fun k => elementOfHash K <$> hashQuery (.expand key k)) 0 (List.range count)
    (fun k _ => (isQueryBoundP_map_iff _ _ _).mpr
      (hash_zero _ (by simp [LocalHash])))

theorem collector_zero (ctx : Context C) (r : PrssOutput C Bit)
    (v : ℕ → Bit) (count : ℕ) :
    RunBudget LocalHash (reshareCollector K ctx r v count : RunM C E G _) 0 := by
  apply run_of_zero
  unfold reshareCollector
  exact (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun inbox =>
    (RunBound.lift (PartyBound.exchange _)).bind (m := 0) (fun forward =>
      (RunBound.record K ctx bitCodec .collector _ count).bind (m := 0) (fun _ => RunBound.pure _)))

theorem reshareWith_zero (ctx : Context C) (mode : ReshareMode)
    (r : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    RunBudget LocalHash (reshareWith K ctx mode r v count : RunM C E G _) 0 := by
  cases mode with
  | peer => exact reshare_zero K ctx _ r v count
  | collector => exact collector_zero K ctx r v count

theorem inputShares_zero (ctx : Context C) (job : Job) :
    PartyBudget LocalHash (inputShares ctx job : PartyM C E G _) 0 := by
  have hp (seed : HashOutput) (xs : List Point) :
      IsQueryBoundP (xs.flatMapM fun x => bitsOfDigest <$> prf (C := C) seed x)
        (fun t => LocalHash (C := C) (.inr t)) 0 := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.flatMapM_cons]
      refine isQueryBoundP_bind (n := 0) (m := 0) ?_
        (fun ys _ => isQueryBoundP_bind ih (fun zs _ => isQueryBoundP_pure _ _ 0))
      simp only [prf, Functor.map_map, isQueryBoundP_map_iff]
      exact hash_zero _ (by simp [LocalHash])
  unfold inputShares
  refine (oracle_bound (n := 0) ?_).bind (m := 0) (fun terms => PartyBudget.pure _)
  simpa using queryBound_mapM (fun t => LocalHash (C := C) (.inr t))
    (fun T => if ctx.self ∈ C.holders T then job.points.flatMapM fun x => bitsOfDigest <$> prf (ctx.keys.seed T) x
      else pure []) 0 C.terms (fun T _ => by
        split_ifs
        · exact hp _ _
        · exact isQueryBoundP_pure _ _ _)

theorem compare_quiet (ctx : Context C) (salts : Shares C Bit) :
    RunBudget LocalHash (compareDigests ctx salts : RunM C E G _) 0 := by
  unfold compareDigests
  refine RunBudget.bind_zero (RunBudget.get) (fun s => ?_)
  refine RunBudget.bind_zero (RunBudget.lift (oracle_bound ?_)) (fun ds => ?_)
  · simpa using queryBound_mapM (fun t => LocalHash (C := C) (.inr t)) _ 0 C.terms
      (fun T _ => by
        split_ifs
        · exact isQueryBoundP_bind (n := 0) (m := 0)
            (hash_zero _ (by simp [LocalHash])) (fun _ _ => hash_zero _ (by simp [LocalHash]))
        · exact isQueryBoundP_pure _ _ _)
  · exact RunBudget.bind_zero (RunBudget.lift ((party_of_all
      (PartyBound.exchange _)))) (fun inbox =>
        RunBudget.lift ((party_of_all (PartyBound.require _))))

theorem coinKey_quiet (gadgets : CheckGadgets C E G) (hg : GadgetBounds gadgets) :
    RunBudget LocalHash (coinKey K gadgets) 0 := by
  unfold coinKey
  exact RunBudget.bind_zero RunBudget.get (fun s => RunBudget.bind_zero ((hg.coin 1))
    (fun values => RunBudget.lift (oracle_bound (hash_zero _ (by simp [LocalHash])))))

theorem challenge_quiet (gadgets : CheckGadgets C E G) (hg : GadgetBounds gadgets) :
    RunBudget LocalHash (challenge K gadgets) 0 := by
  unfold challenge
  refine RunBudget.bind_zero (coinKey_quiet K gadgets hg) (fun key => ?_)
  refine RunBudget.bind_zero
    (RunBudget.lift (oracle_bound ((findChallenge_zero K key _ _)))) (fun out => ?_)
  cases out with
  | none => exact .lift ((party_of_all PartyBound.failure))
  | some r => exact .pure _ 0

theorem slice_quiet (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : GadgetBounds gadgets) (τ : List E) (count : ℕ)
    (v : Shares C E × Shares C E × E) (j : ℕ) :
    RunBudget LocalHash (sliceStep K ctx gadgets τ count v j) 0 := by
  rcases v with ⟨xs, ys, d⟩
  unfold sliceStep
  exact ((hg.mult _)).bind_zero (fun _ =>
    (challenge_quiet K gadgets hg).bind_zero (fun _ => .pure _ 0))

theorem halving_quiet (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : GadgetBounds gadgets) (width : ℕ)
    (v : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    RunBudget LocalHash (halvingStep K ctx gadgets width v j) 0 := by
  rcases v with ⟨a, b, d⟩
  unfold halvingStep
  exact ((hg.mult _)).bind_zero (fun _ =>
    (challenge_quiet K gadgets hg).bind_zero (fun _ => .pure _ 0))

theorem final_quiet (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : GadgetBounds gadgets) (v : (ℕ → E) × (ℕ → E) × E) :
    RunBudget LocalHash (finalStep K ctx gadgets v) 0 := by
  rcases v with ⟨a, b, d⟩
  unfold finalStep
  exact ((hg.elements 2)).bind_zero (fun w =>
    ((hg.mult _)).bind_zero (fun q =>
      ((hg.bits 256)).bind_zero (fun salts =>
        (compare_quiet ctx salts.1).bind_zero (fun _ =>
          (challenge_quiet K gadgets hg).bind_zero (fun r =>
            (RunBudget.lift ((party_of_all (RunBound.openSh K ctx _ 3)))).bind_zero
              (fun opened => RunBudget.lift (
                (party_of_all (PartyBound.require _)))))))))

theorem check_quiet (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : GadgetBounds gadgets) (tuples : List (Tuple C)) :
    RunBudget LocalHash (check K ctx gadgets tuples) 0 := by
  by_cases hz : (tuples.map (·.count)).sum = 0
  · simp only [check, hz, ↓reduceIte]
    exact .pure _ _
  · rw [check_eq K ctx gadgets tuples hz]
    exact (coinKey_quiet K gadgets hg).bind_zero (fun key =>
      ((expand_zero K key _)).bind_zero (fun τ =>
        (RunBudget.lift ((party_of_all (PartyBound.require _)))).bind_zero
          (fun _ => ((RunBudget.foldlM _ 0 (slice_quiet K ctx gadgets hg τ _) _ _).mono (by simp)).bind_zero (fun v =>
            ((RunBudget.foldlM _ 0 (halving_quiet K ctx gadgets hg _) _ _).mono (by simp)).bind_zero (fun v' => final_quiet K ctx gadgets hg v')))))

theorem openRep_quiet (ctx : Context C) (v : Shares C Bit) (count : ℕ) :
    PartyBudget LocalHash (openRep K ctx v count : PartyM C E G _) 0 := by
  have hc (f : C.Term → List Bit) : PartyBudget LocalHash
      (oracleStep (C.terms.mapM fun T => hashQuery (.copy (f T))) : PartyM C E G _) 0 :=
    oracle_bound (by
      simpa using (queryBound_mapM (fun t => LocalHash (C := C) (.inr t))
        (fun T => hashQuery (.copy (f T))) 0 C.terms
        (fun _ _ => hash_zero _ (by simp [LocalHash]))))
  unfold openRep
  simpa using (hc _).bind (fun ds =>
    ((party_of_all (PartyBound.exchange _))).bind (fun inbox =>
      (hc _).bind (fun copies =>
        ((party_of_all (PartyBound.require _))).bind
          (fun _ => PartyBudget.pure _))))

theorem runJobs_quiet (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    RunBudget LocalHash
      (runJobs K (realRunGadgets K ctx mode : RunGadgets C E G) jobs inputs) 0 := by
  have hm : ∀ x y count, RunBudget LocalHash
      ((realRunGadgets K ctx mode : RunGadgets C E G).mult x y count) 0 := by
    intro x y count
    change RunBudget _ (prssRandomness ctx bitCodec 0 count >>= _) 0
    exact ((prss_zero ctx bitCodec prg_zero 0 count).bind (m := 0)
      (fun r => reshareWith_zero K ctx mode r _ count))
  have hr : ∀ v count, RunBudget LocalHash
      ((realRunGadgets K ctx mode : RunGadgets C E G).rerand v count) 0 := by
    intro v count
    change RunBudget _ (prssRandomness ctx bitCodec 0 count >>= _) 0
    exact ((prss_zero ctx bitCodec prg_zero 0 count).bind (m := 0)
      (fun r => reshare_zero K ctx _ r _ count))
  rw [runJobs_eq]
  refine RunBudget.bind_zero ((RunBudget.foldlM _ 0 (fun p l => ?_) _ _).mono (by simp)) (fun p => ?_)
  · unfold layerBody
    exact (hm _ _ _).bind_zero (fun z => .pure _ 0)
  · unfold tailBody
    exact (hr _ _).bind_zero (fun v =>
      (check_quiet (G := G) K ctx _ (gadgets_zero K ctx) _).bind_zero (fun _ =>
        (RunBudget.lift (openRep_quiet K ctx v _)).bind_zero (fun out => .pure _ 0)))

variable (circuits : Circuits) (settings : Settings)

theorem batch_quiet (ctx : Context C) (jobs : List Job) :
    RunBudget LocalHash (ceremonyBatch (G := G) K circuits settings ctx jobs) 0 := by
  have hi : PartyBudget LocalHash (jobs.mapM (inputShares ctx) : PartyM C E G _) 0 :=
    (by simpa using party_mapM (inputShares ctx) 0 (inputShares_zero ctx) jobs)
  unfold ceremonyBatch
  exact RunBudget.bind_zero RunBudget.get (fun s => (RunBudget.lift hi).bind_zero (fun inputs =>
    (RunBudget.lift (runJobs_quiet K ctx settings.mode _ inputs ⟨fun _ => [], s.1, s.2⟩)).bind_zero
      (fun result => (RunBudget.set _).bind_zero (fun _ => RunBudget.pure _ 0))))

theorem batched_quiet (ctx : Context C) (jobs : List Job) :
    RunBudget LocalHash
      (batched settings.batchSize (ceremonyBatch (G := G) K circuits settings ctx) jobs) 0 := by
  unfold batched
  exact ((RunBudget.mapM _ 0 (batch_quiet K circuits settings ctx) _).mono (by simp)).bind_zero
    (fun outputs => .pure _ 0)

theorem batched_audit_quiet [Fintype E] [DecidableEq E] (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    PartyBudget LocalHash
      ((batched settings.batchSize (treeSimCheckBatchAudit (G := G) K circuits settings ctx)
        jobs).run.run initial) 0 := by
  classical
  have he := congrArg (fun p => p.run initial)
    (show treeSimCheckWriterErase
      (batched settings.batchSize (treeSimCheckBatchAudit (G := G) K circuits settings ctx) jobs) =
        batched settings.batchSize (ceremonyBatch K circuits settings ctx) jobs by
      rw [monadHom_batched]
      simp only [treeSimCheckBatchAudit_erase])
  have hb := batched_quiet (G := G) K circuits settings ctx jobs initial
  rw [← he] at hb
  simpa only [treeSimCheckWriterErase, StateT.run_map, PartyBudget,
    OptionT.run_map, isQueryBoundP_map_iff] using hb

end HashQuiet

section MerkleBudget

variable (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)

theorem leafQuery_leaf (lay' : Layer) (key' : KeyIndex) (payload : HashInput) :
    LeafQuery parameter lay key (tweakableHashInput parameter (.leaf lay' key') payload) ↔
      lay' = lay ∧ key' = key := by
  constructor
  · rintro ⟨_, he⟩
    have hd := hashDomainFields_injective (d := .leaf lay' key') (d' := .leaf lay key)
      trivial trivial (tweakableInput_injective he).1
    exact HashDomain.leaf.inj hd
  · rintro ⟨rfl, rfl⟩
    exact ⟨payload, rfl⟩

theorem leafQuery_not_tag (domain : HashDomain) (payload : HashInput)
    (tag : (hashDomainFields domain).tag ≠ 2) :
    ¬LeafQuery parameter lay key (tweakableHashInput parameter domain payload) := by
  rintro ⟨_, he⟩
  apply tag
  exact congrArg TweakFields.tag (tweakableInput_injective he).1

theorem leafQuery_not_randomizer (lay' : Layer) (key' : KeyIndex)
    (randomness : Randomness) (message : HashInput) :
    ¬LeafQuery parameter lay key (randomizerInput parameter lay' key' randomness message) := by
  rintro ⟨payload, he⟩
  simp only [randomizerInput, tweakableHashInput, tweakBytes, List.append_assoc] at he
  have hf := congrArg TweakFields.tag (fieldInput_injective (by simpa only [List.append_assoc] using he)).1
  exact (by decide : (7 : BitVec 5) ≠ 2) hf

theorem tweakableHash_leaf_bound (domain : HashDomain) (payload : HashInput) (n : ℕ)
    (h : LeafQuery parameter lay key (tweakableHashInput parameter domain payload) → 0 < n) :
    IsQueryBoundP (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest)
      (LeafQuery parameter lay key) n := by
  unfold Concrete.tweakableHash
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query _) >>= _) _ n
  simpa only [Nat.add_zero] using isQueryBoundP_bind (n := n) (m := 0)
    ((isQueryBoundP_query_iff _ _ _).mpr h) (fun _ _ => isQueryBoundP_pure _ _ _)

/-- One leaf is visited once exactly when its index lies in the subtree interval. -/
def leafIn (height idx : ℕ) (key : KeyIndex) : ℕ :=
  if 2 ^ height * idx ≤ key.val ∧ key.val < 2 ^ height * (idx + 1) then 1 else 0

theorem leafIn_children (height idx : ℕ) (key : KeyIndex) :
    leafIn height (2 * idx) key + leafIn height (2 * idx + 1) key =
      leafIn (height + 1) idx key := by
  have ha : 2 ^ height * (2 * idx) = 2 ^ (height + 1) * idx := by ring
  have hb : 2 ^ height * (2 * idx + 1 + 1) = 2 ^ (height + 1) * (idx + 1) := by ring
  have hmid : 2 ^ height * (2 * idx) ≤ 2 ^ height * (2 * idx + 1) := Nat.mul_le_mul_left _ (by omega)
  have hmid' : 2 ^ height * (2 * idx + 1) ≤ 2 ^ height * (2 * idx + 1 + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [ha] at hmid
  rw [hb] at hmid'
  unfold leafIn
  rw [ha, hb]
  split_ifs <;> omega

theorem merkle_leaf_bound (ends : KeyIndex → ChainIndex → Digest) (height idx : ℕ)
    (range : 2 ^ height * (idx + 1) ≤ lifetime) :
    IsQueryBoundP (merkleNode parameter lay ends height idx)
      (LeafQuery parameter lay key) (leafIn height idx key) := by
  induction height generalizing idx with
  | zero =>
    have hi : idx < lifetime := by
      simp only [pow_zero, one_mul] at range
      omega
    apply tweakableHash_leaf_bound
    rw [leafQuery_leaf]
    rintro ⟨_, hk⟩
    have hv := congrArg Fin.val hk
    simp only [Nat.mod_eq_of_lt hi] at hv
    simp [leafIn, ← hv]
  | succ height ih =>
    have left : 2 ^ height * (2 * idx + 1) ≤ lifetime := by
      have hpow : 2 ^ height * (2 * idx + 1) ≤ 2 ^ (height + 1) * (idx + 1) := by
        rw [Nat.pow_succ]
        nlinarith [Nat.zero_le (2 ^ height)]
      exact hpow.trans range
    have right : 2 ^ height * (2 * idx + 1 + 1) ≤ lifetime := by
      convert range using 1; ring
    rw [merkleNode, ← leafIn_children]
    apply isQueryBoundP_bind (ih _ left)
    intro lhs _
    simpa only [Nat.add_zero] using isQueryBoundP_bind (ih _ right) (fun rhs _ =>
      tweakableHash_leaf_bound parameter lay key _ _ 0
        (fun h => (leafQuery_not_tag parameter lay key _ _
          (by change (3 : BitVec 5) ≠ 2; decide) h).elim))

end MerkleBudget

section TopQuiet

variable (parameter : PublicParameter) (key : KeyIndex)

/-- Hashes with a non-leaf tag never visit the selected leaf. -/
theorem tag_quiet (domain : HashDomain) (payload : HashInput)
    (tag : (hashDomainFields domain).tag ≠ 2) :
    IsQueryBoundP (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest)
      (LeafQuery parameter bottomLayer key) 0 :=
  tweakableHash_leaf_bound _ _ _ _ _ 0
    (fun h => (leafQuery_not_tag _ _ _ _ _ tag h).elim)

theorem topLeaf_quiet (e : KeyIndex) (payload : HashInput) :
    IsQueryBoundP (Concrete.tweakableHash parameter (.leaf topLayer e) payload : OracleComp HashSpec Digest)
      (LeafQuery parameter bottomLayer key) 0 := by
  apply tweakableHash_leaf_bound
  rw [leafQuery_leaf]
  rintro ⟨h, _⟩
  exact (by decide : topLayer ≠ bottomLayer) h |>.elim

/-- The structural walk of `SigningSelection` specialized to bottom leaf queries. -/
theorem topMerkle_quiet (ends : KeyIndex → ChainIndex → Digest) (height idx : ℕ) :
    IsQueryBoundP (merkleNode parameter topLayer ends height idx)
      (LeafQuery parameter bottomLayer key) 0 := by
  induction height generalizing idx with
  | zero => exact topLeaf_quiet _ _ _ _
  | succ height ih =>
    rw [merkleNode]
    exact isQueryBoundP_bind (n := 0) (m := 0) (ih _) (fun _ _ =>
      isQueryBoundP_bind (n := 0) (m := 0) (ih _) (fun _ _ =>
        tag_quiet _ _ _ _ (by change (3 : BitVec 5) ≠ 2; decide)))

theorem topPath_quiet (ends : KeyIndex → ChainIndex → Digest) (e : KeyIndex) :
    IsQueryBoundP (merklePath parameter topLayer ends e) (LeafQuery parameter bottomLayer key) 0 :=
  isQueryBoundP_sequenceFin _ (fun _ => topMerkle_quiet _ _ _ _ _)

theorem chain_quiet (lay : Layer) (e : KeyIndex) (l : ChainIndex)
    (start steps : ℕ) (value : Digest) :
    IsQueryBoundP (Concrete.chainWalk parameter lay e l start steps value : OracleComp HashSpec Digest)
      (LeafQuery parameter bottomLayer key) 0 := by
  induction steps with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ steps ih =>
    rw [Concrete.chainWalk]
    refine isQueryBoundP_bind (n := 0) (m := 0) ih (fun _ _ => ?_)
    split
    · exact tag_quiet _ _ _ _ (by change (1 : BitVec 5) ≠ 2; decide)
    · exact isQueryBoundP_pure _ _ _

theorem fold_quiet (lay : Layer) (e : KeyIndex) (path : Fin layerHeight → Digest)
    (levels : ℕ) (value : Digest) :
    IsQueryBoundP (Concrete.treeFold parameter lay e path levels value : OracleComp HashSpec Digest)
      (LeafQuery parameter bottomLayer key) 0 := by
  induction levels with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ levels ih =>
    rw [Concrete.treeFold]
    refine isQueryBoundP_bind (n := 0) (m := 0) ih (fun _ _ => ?_)
    split_ifs <;> exact tag_quiet parameter key (.node lay (levels + 1) _) _
      (by change (3 : BitVec 5) ≠ 2; decide)

theorem topOts_quiet (e : KeyIndex) (message : HashInput) (randomness : Randomness)
    (values : ChainIndex → Digest) :
    IsQueryBoundP (Concrete.otsLeaf parameter topLayer e message randomness values : OracleComp HashSpec _)
      (LeafQuery parameter bottomLayer key) 0 := by
  unfold Concrete.otsLeaf Concrete.messageDigest
  refine isQueryBoundP_bind (n := 0) (m := 0)
    (tag_quiet _ _ _ _ (by change (12 : BitVec 5) ≠ 2; decide)) (fun digest _ => ?_)
  split
  · refine isQueryBoundP_bind (n := 0) (m := 0)
      (isQueryBoundP_sequenceFin _ (fun l => chain_quiet _ _ _ _ _ _ _ _)) (fun endpoints _ => ?_)
    exact isQueryBoundP_bind (n := 0) (m := 0) (topLeaf_quiet _ _ _ _)
      (fun _ _ => isQueryBoundP_pure _ _ _)
  · exact isQueryBoundP_pure _ _ _

attribute [local irreducible] Concrete.treeFold Concrete.otsLeaf

theorem topRoot_quiet (e : KeyIndex) (message : HashInput) (part : LayerSignature) :
    IsQueryBoundP (Concrete.layerRoot parameter topLayer e message part : OracleComp HashSpec _)
      (LeafQuery parameter bottomLayer key) 0 := by
  unfold Concrete.layerRoot
  refine isQueryBoundP_bind (n := 0) (m := 0) (topOts_quiet parameter key e message part.randomness part.chainValues) (fun leaf _ => ?_)
  cases leaf
  · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_bind (n := 0) (m := 0) (fold_quiet parameter key topLayer e part.path layerHeight _)
      (fun _ _ => isQueryBoundP_pure _ _ _)

theorem grind_quiet (lay : Layer) (e : KeyIndex) (message : HashInput)
    (base : Randomness) (attempts trial : ℕ) :
    IsQueryBoundP (grind parameter lay e message base attempts trial)
      (LeafQuery parameter bottomLayer key) 0 := by
  induction attempts generalizing trial with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ attempts ih =>
    rw [grind]
    refine isQueryBoundP_bind (n := 0) (m := 0)
      (tag_quiet _ _ _ _ (by change (12 : BitVec 5) ≠ 2; decide)) (fun digest _ => ?_)
    split
    · exact isQueryBoundP_pure _ _ _
    · exact ih _

end TopQuiet

section RestBudget

open TreeSimHashCount

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local irreducible] treeLockstepPublicChoiceCode merkleNode merklePath Concrete.layerRoot

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem publicComp_leaf_bound {α : Type} (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (p : OracleComp HashSpec α) (n : ℕ)
    (bound : IsQueryBoundP p (LeafQuery parameter bottomLayer (leftmostKey layerHeight b.val)) n) :
    IsQueryBoundP (publicComp (C := C) (E := E) p) (PartyLeaf parameter b) n := by
  induction p using OracleComp.inductionOn generalizing n with
  | pure a => simp [publicComp]
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at bound
    simp only [publicComp, simulateQ_bind, simulateQ_spec_query]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query _) >>= _) _ n
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨bound.1, fun u => ih u _ (bound.2 u)⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem oracle_leaf_bound {α : Type} (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (p : OracleComp HashSpec α) (n : ℕ)
    (bound : IsQueryBoundP p (LeafQuery parameter bottomLayer (leftmostKey layerHeight b.val)) n) :
    PartyBudget (LocalLeaf parameter b) (oracleStep (tweakable p) : PartyM C E RealSpec α) n := by
  unfold PartyBudget oracleStep localStep
  change IsQueryBoundP (some <$> liftComp
    (liftComp (tweakable p) (LocalSpec C)) (PartySpec C E RealSpec)) _ n
  rw [← publicComp_lift, isQueryBoundP_map_iff]
  exact publicComp_leaf_bound _ _ _ _ bound

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem party_noHash_leaf {α : Type} (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (p : PartyM C E RealSpec α) (bound : PartyBudget LocalHash p 0) :
    PartyBudget (LocalLeaf parameter b) p 0 := by
  apply IsQueryBoundP.of_imp _ bound
  rintro ((q | _) | _) h
  · rcases q with _ | (_ | _) | _ <;> simp_all [PartyQuery, LocalLeaf, LocalHash]
  · exact h.elim
  · exact h.elim

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem publicChoice_once (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) :
    IsQueryBoundP (treeLockstepPublicChoiceCode parameter b outputs)
      (LeafQuery parameter bottomLayer (leftmostKey layerHeight b.val)) 1 := by
  have range : 2 ^ layerHeight * (b.val + 1) ≤ lifetime := by
    have hb := b.isLt
    simp only [layerHeight, lifetime, numLayers] at *
    omega
  have merkle (ends : KeyIndex → ChainIndex → Digest) :
      IsQueryBoundP (merkleNode parameter bottomLayer ends layerHeight b.val)
        (LeafQuery parameter bottomLayer (leftmostKey layerHeight b.val)) 1 :=
    (merkle_leaf_bound _ _ _ _ _ _ range).mono (by unfold leafIn; split <;> omega)
  unfold treeLockstepPublicChoiceCode
  refine isQueryBoundP_bind (n := 1) (m := 0) (merkle _) (fun root _ => ?_)
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun base _ => ?_)
  · rw [isQueryBoundP_map_iff]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query _)) _ 0
    rw [isQueryBoundP_query_iff]
    exact fun h => (leafQuery_not_randomizer _ _ _ _ _ _ _ h).elim
  · exact isQueryBoundP_bind (n := 0) (m := 0) (grind_quiet _ _ _ _ _ _ _ _)
      (fun _ _ => isQueryBoundP_pure _ _ _)

omit [Fintype E] [DecidableEq E] in
theorem bottomFinish_quiet (parameter : PublicParameter) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) (root : Digest)
    (randomness : Randomness) (values : Option (List (List Bit)))
    (records : List (TreeSimCheckBatchRecord C)) :
    PartyBudget (LocalLeaf parameter b)
      (treeLockstepBottomFinish (E := E) parameter top b outputs root randomness values records) 0 := by
  cases values with
  | none => exact isQueryBoundP_pure _ _ _
  | some values =>
    unfold treeLockstepBottomFinish
    refine (oracle_leaf_bound parameter b _ 0 (topPath_quiet _ _ _ _)).bind (m := 0) (fun path => ?_)
    refine (oracle_leaf_bound parameter b _ 0 (topRoot_quiet _ _ _ _ _)).bind (m := 0) (fun topRoot => ?_)
    split <;> exact isQueryBoundP_pure _ _ _

theorem signingCont_quiet (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (top : TopTree) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit))
    (records : List (TreeSimCheckBatchRecord C)) (initial : ℕ × ℕ)
    (choice : TreeCheckWalkRecipe.PublicChoice) :
    PartyBudget (LocalLeaf ctx.keys.parameter b)
      (TreeCheckWalkRecipe.signingCont K circuits settings ctx top b outputs records initial choice) 0 := by
  unfold TreeCheckWalkRecipe.signingCont
  refine (party_noHash_leaf _ _ _ (HashQuiet.batched_audit_quiet K circuits settings ctx _ initial)).bind
    (m := 0) (fun result => ?_)
  exact bottomFinish_quiet _ _ _ _ _ _ _ _

theorem firstRest_once (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (top : TopTree) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit))
    (records : List (TreeSimCheckBatchRecord C)) (initial : ℕ × ℕ) :
    IsQueryBoundP (treeLockstepFirstRest K circuits settings ctx top (.bottom b)
      ((some outputs, records), initial)).run (PartyLeaf ctx.keys.parameter b) 1 := by
  rw [firstRest_run]
  refine isQueryBoundP_bind (n := 1) (m := 0)
    (publicComp_leaf_bound _ _ _ _ (publicChoice_once _ _ _)) (fun choice _ => ?_)
  cases choice with
  | none => exact isQueryBoundP_pure _ _ _
  | some choice => exact signingCont_quiet K circuits settings ctx top b outputs records initial choice

end RestBudget

section MatchingPoints

attribute [local irreducible] treeLockstepFirstRest treeLockstepPublicChoiceCode

open TreeCheckWalkRecipe

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- Every successful head of a matching point transfers to any matching point
whose honest local tail makes no public hash query, with the same final state. -/
theorem head_transfer (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C)) (j : ℕ)
    (b : Fin (2 ^ layerHeight)) (q : TreeCheckWalkDef.Pending A) (point point₀ : SigningPoint C)
    (hm : SigningMatches K D A circuits settings top x setup j b q point)
    (hm₀ : SigningMatches K D A circuits settings top x setup j b q point₀)
    (i : C.Party) (honest : i ∉ D.1) (quiet : IsQueryBoundP (point₀.tail i) LocalHash 0)
    (s final : TreeSimState C) (choice : PublicChoice)
    (run : (some choice, final) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (signingHead (x i).parameter b (point.outputs i) (point.tail i)))).run s)) :
    (some choice, final) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (signingHead (x i).parameter b (point₀.outputs i) (point₀.tail i)))).run s) := by
  exact signingHead_transfer_of_bound prims D K circuits settings ⟨i, x i, setupKeys setup i⟩ top b
    (point.outputs i) (point₀.outputs i) (point.records i) (point₀.records i)
    (signingInitial K D circuits settings (.bottom b) x) (point.tail i) (point₀.tail i) quiet
    (firstRest_once K circuits settings ⟨i, x i, setupKeys setup i⟩ top b
      (point₀.outputs i) (point₀.records i) (signingInitial K D circuits settings (.bottom b) x))
    ((hm.2 i honest).symm.trans (hm₀.2 i honest))
    s final choice run

end MatchingPoints

end ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer.prefix_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer.prefix_transfer

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer.publicChoice_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer.publicChoice_cancel

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer.signingHead_transfer_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer.signingHead_transfer_of_bound

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer.HashQuiet.batched_audit_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer.HashQuiet.batched_audit_quiet

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer.merkle_leaf_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer.merkle_leaf_bound

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer.firstRest_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer.firstRest_once

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer.head_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkPointTransfer.head_transfer

