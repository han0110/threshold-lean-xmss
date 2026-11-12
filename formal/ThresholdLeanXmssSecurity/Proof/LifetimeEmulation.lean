import ThresholdLeanXmssSecurity.Proof.LifetimeLemmas
import ThresholdLeanXmssSecurity.Proof.SeedHit

/-!
# Signing emulation

This is Stage A2 item 2 of `FIX.md`. During a ceremony of one tree, the ceremony adversary answers the
signing requests on the other trees by itself.

* `requestPoint_not_ceremonyPoint` shows Stage A0 item 1. A signing request on another tree reads no
  point of the ceremony, at which the ceremony queries `prf (seed T) x` (`inputShares`). A ceremony
  queries no mask.
* `emulatedOracles` is `tsigOracles` on tables (`emulatedDealt`). It runs on the oracles of the
  adversary and holds no honest key.
* `emulatedOracles_run` shows that it gives the same output, the same state and the same cache as the
  signing service of the lifetime (`signerDealt`). The cache must already hold every PRF term and
  mask that the request reads (`Covers`). Only the costs differ, because the calls of the adversary
  count.
* `Covers.mono` keeps the hypothesis on a larger cache, so the emulation runs request after request.
* The tables (`SigningTables`) are countable. `encodeAux` puts them in the auxiliary input, and
  `decodeAux_encodeAux` gets them back.

The hypothesis `Covers` is necessary. From the empty cache, `.round1` writes `H16(seed_T ‖ x)` into
the cache of the real service, and the emulation writes nothing. So each hidden value that the real
service reads during the ceremony must be in the start cache.

The tables are not the full state of the hop adversary. `SimulatedBy` fixes the adversary and its
state type before `z`, and the state of the lifetime adversary is an arbitrary type. So the hop
adversary replays the lifetime prefix from `z` (D13), and the tables go into `z` next to the
transcript of the prefix.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open SigningCoreProof SeedHitProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The points of a request and of a ceremony -/

/-- The points `x` at which a signing request queries `prf (seed T) x` or a mask at `x`. -/
def RequestPoint : TsigQuery C → Point → Prop
  | .corrupt _, _ => False
  | .tree b, x => x = .randomizer topLayer (topKey b)
  | .round1 _ _ e _, x => x = .randomizer bottomLayer e
  | .round2 _ _ e _ _, x => x = .randomizer bottomLayer e ∨
      ∃ l, ∃ p : Digit, p.val < chainLength - 1 ∧ x = .chain bottomLayer e l p

/-- The bottom tree of a signing request. -/
def requestTree : TsigQuery C → Option (Fin (2 ^ layerHeight))
  | .corrupt _ => none
  | .tree b => some b
  | .round1 _ _ e _ => some (treeOf e)
  | .round2 _ _ e _ _ => some (treeOf e)

/-- The points of the jobs of a ceremony, at which its holders query `prf (seed T) x`
(`inputShares`). -/
def CeremonyPoint : Tree → Point → Prop
  | .top, x => ∃ job ∈ topJobs, x ∈ job.points
  | .bottom b, x => (∃ job ∈ bottomJobs b, x ∈ job.points) ∨ ∃ encoding, ∃ job ∈ signJobs b encoding, x ∈ job.points

theorem ceremonyPoint_cases {tree : Tree} {x : Point} (h : CeremonyPoint tree x) :
    (∃ b l, x = .chain topLayer (topKey b) l (digit 0)) ∨
      ∃ b, tree = .bottom b ∧ ((∃ k l d, x = .chain bottomLayer (bottomKey b k) l d) ∨
        (∃ k, x = .randomizer bottomLayer (bottomKey b k)) ∨ x = .randomizer topLayer (topKey b)) := by
  cases tree with
  | top =>
    obtain ⟨job, hjob, hx⟩ := h
    simp only [topJobs, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hjob
    obtain ⟨b, l, rfl⟩ := hjob
    simp only [List.mem_singleton] at hx
    exact .inl ⟨b, l, hx⟩
  | bottom b =>
    rcases h with ⟨job, hjob, hx⟩ | ⟨encoding, job, hjob, hx⟩
    · refine .inr ⟨b, rfl, ?_⟩
      simp only [bottomJobs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and,
        List.mem_singleton] at hjob
      rcases hjob with (⟨k, l, rfl⟩ | ⟨k, rfl⟩) | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> exact .inl ⟨k, l, _, rfl⟩
      · simp only [List.mem_singleton] at hx
        exact .inr (.inl ⟨k, hx⟩)
      · simp only [List.mem_singleton] at hx
        exact .inr (.inr hx)
    · simp only [signJobs, List.mem_map, List.mem_finRange, true_and] at hjob
      obtain ⟨l, rfl⟩ := hjob
      simp only [List.mem_singleton] at hx
      exact .inl ⟨b, l, hx⟩

theorem treeOf_bottomKey (b k : Fin (2 ^ layerHeight)) : treeOf (bottomKey b k) = b := by
  ext
  simp only [treeOf, bottomKey]
  have := k.isLt
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt this, zero_add]

theorem topKey_injective : Function.Injective topKey := fun b b' h => Fin.ext (by simpa [topKey] using congrArg Fin.val h)

/-- Stage A0 item 1. A signing request on a tree other than the tree of a ceremony queries no
point of that ceremony. The ceremony queries `prf (seed T) x` only at its points (`inputShares`) and
no mask, so the two share no random-oracle input with `.prf` or `.mask`. -/
theorem requestPoint_not_ceremonyPoint {q : TsigQuery C} {tree : Tree}
    (hq : ∀ b, tree = .bottom b → requestTree q ≠ some b) {x : Point} (hx : RequestPoint q x) :
    ¬ CeremonyPoint tree x := fun hc => by
  rcases ceremonyPoint_cases hc with ⟨b, l, rfl⟩ | ⟨b, rfl, hb⟩
  · cases q with
    | corrupt => exact hx
    | tree b' => cases hx
    | round1 i J e m => cases hx
    | round2 i J e m parts =>
      rcases hx with h | ⟨l', p, -, h⟩
      · cases h
      · cases h
  · have hne := hq b rfl
    cases q with
    | corrupt => exact hx
    | tree b' =>
      cases hx
      rcases hb with ⟨k, l, d, h⟩ | ⟨k, h⟩ | h
      · cases h
      · cases h
      · exact hne (by rw [requestTree, topKey_injective (Point.randomizer.inj h).2])
    | round1 i J e m =>
      cases hx
      rcases hb with ⟨k, l, d, h⟩ | ⟨k, h⟩ | h
      · cases h
      · exact hne (by rw [requestTree, (Point.randomizer.inj h).2, treeOf_bottomKey])
      · cases h
    | round2 i J e m parts =>
      rcases hx with rfl | ⟨l', p, -, rfl⟩
      · rcases hb with ⟨k, l, d, h⟩ | ⟨k, h⟩ | h
        · cases h
        · exact hne (by rw [requestTree, (Point.randomizer.inj h).2, treeOf_bottomKey])
        · cases h
      · rcases hb with ⟨k, l, d, h⟩ | ⟨k, h⟩ | h
        · exact hne (by rw [requestTree, (Point.chain.inj h).2.1, treeOf_bottomKey])
        · cases h
        · cases h

/-! ## The emulated signing service -/

/-- `KeyGen` as the ceremony adversary holds it. The PRF values `value`, the parts `part` and the
trees are tables. The keys are zero, because the adversary has no honest key. -/
def emulatedDealt (parameter : PublicParameter) (top : TopTree) (trees : Fin (2 ^ layerHeight) → Option BottomTree)
    (value : Point → Digest) (part : C.Party → C.Quorum → Point → Message → Digest) :
    Dealt C (OracleComp (LocalSpec C)) :=
  ⟨fun _ => ⟨parameter, fun _ => 0, fun _ => 0⟩, parameter, top, fun x => pure (value x),
    fun i J x message => pure (part i J x message), fun b => pure (trees b)⟩

/-- The signing service that the ceremony adversary runs by itself on its own oracles. It is
`tsigOracles` on the tables of `emulatedDealt`. -/
def emulatedOracles (parameter : PublicParameter) (top : TopTree) (trees : Fin (2 ^ layerHeight) → Option BottomTree)
    (value : Point → Digest) (part : C.Party → C.Quorum → Point → Message → Digest) :
    QueryImpl (TsigSpec C) (StateT (TsigState C) (OracleComp (LocalSpec C))) :=
  tsigOracles (fun oa => liftComp oa (LocalSpec C)) (emulatedDealt parameter top trees value part)

/-- `KeyGen` as an honest signer of the lifetime holds it, as `signerDealt` of the Stage A1 draft. It
signs with its keys and its stored trees, and it evaluates `F` on `seeds`. -/
def signerDealt (parameter : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (trees : Fin (2 ^ layerHeight) → Option BottomTree) (seeds : C.Term → HashOutput) :
    Dealt C (OracleComp (WorldSpec C)) :=
  { dealtWith honestLift parameter keys top (fun x => honestLift (prfValue seeds x)) with
    bottom := fun b => pure (trees b) }

/-! ## Steps that read only the cache -/

section Cache

variable (prims : Primitives)

/-- `m` gives `a` and keeps the cache, from every cache that extends `s`. -/
def Steady {α : Type} (s : HashCache C) (m : StateT (HashCache C) ProbComp α) (a : α) : Prop :=
  ∀ s', s ≤ s' → m.run s' = pure (a, s')

variable {prims}

theorem steady_pure {α : Type} (s : HashCache C) (a : α) : Steady s (pure a) a := fun _ _ => rfl

theorem Steady.map {α β : Type} {s : HashCache C} {m : StateT (HashCache C) ProbComp α} {a : α} (h : Steady s m a)
    (f : α → β) : Steady s (f <$> m) (f a) := fun s' hs' => by
  rw [StateT.run_map, h s' hs']; rfl

theorem Steady.bind {α β : Type} {s : HashCache C} {m : StateT (HashCache C) ProbComp α} {a : α}
    {k : α → StateT (HashCache C) ProbComp β} {b : β} (h : Steady s m a) (hk : Steady s (k a) b) :
    Steady s (m >>= k) b := fun s' hs' => by
  rw [StateT.run_bind, h s' hs', pure_bind, hk s' hs']

theorem steady_mapM {α β : Type} {s : HashCache C} (f : α → StateT (HashCache C) ProbComp β) (g : α → β) :
    ∀ (xs : List α), (∀ a ∈ xs, Steady s (f a) (g a)) → Steady s (xs.mapM f) (xs.map g)
  | [], _ => steady_pure s _
  | a :: xs, h => by
    rw [List.mapM_cons, List.map_cons]
    exact (h a (by simp)).bind ((steady_mapM f g xs fun b hb => h b (by simp [hb])).bind (steady_pure s _))

theorem steady_sequenceFin {α : Type} {s : HashCache C} :
    ∀ {n : ℕ} (f : Fin n → StateT (HashCache C) ProbComp α) (v : Fin n → α), (∀ l, Steady s (f l) (v l)) →
      Steady s (Concrete.sequenceFin f) v
  | 0, f, v, _ => by
    have : v = Fin.elim0 := funext fun i => i.elim0
    subst this; exact steady_pure s _
  | n + 1, f, v, h => by
    have hv : v = Fin.cases (v 0) fun i : Fin n => v i.succ := funext fun i => by cases i using Fin.cases <;> rfl
    rw [hv]
    exact (h 0).bind ((steady_sequenceFin _ _ fun l => h l.succ).bind (steady_pure s _))

/-- Two steps that are steady with one value agree from every extension of `s`. -/
theorem Steady.run_eq {α : Type} {s s' : HashCache C} {m m' : StateT (HashCache C) ProbComp α} {a : α}
    (h : Steady s m a) (h' : Steady s m' a) (hs' : s ≤ s') : m.run s' = m'.run s' := by
  rw [h s' hs', h' s' hs']

/-- A cached call of `H` outside the domain of `Th` reads the cache. -/
theorem steady_randomOracle {s : HashCache C} {q : Query C} {v : HashOutput} (hq : s q = some v) :
    Steady s ((Query C →ₒ HashOutput).randomOracle q) v := fun s' hs' => by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ (hs' hq)]

/-- `H16(seed ‖ x)` as the cache holds it. -/
def cachedPrf (s : HashCache C) (seed : HashOutput) (x : Point) : Digest := truncateHash ((s (.prf seed x)).getD 0)

/-- `F(x)` on `seeds` as the cache holds it. -/
def cachedPrfValue (s : HashCache C) (seeds : C.Term → HashOutput) (x : Point) : Digest :=
  (C.terms.map fun T => cachedPrf s (seeds T) x).foldl (· ^^^ ·) 0

/-- `Eval'(sk'_i, J, x, m)` as the cache holds it. -/
def cachedEval (s : HashCache C) (keys : Keys C) (i : C.Party) (J : C.Quorum) (x : Point) (message : Message) : Digest :=
  ((C.terms.filter (· ∈ L J i)).map (fun T => cachedPrf s (keys.seed T) x) ++
    (C.parties.filter fun j => j ∈ J.1 ∧ j ≠ i).map fun j =>
      truncateHash ((s (.mask (keys.pairKey j) x message J)).getD 0)).foldl (· ^^^ ·) 0

/-- The cache holds every `H16(seed_T ‖ x)` of `F(x)` on `seeds`. -/
def PrfValueCached (s : HashCache C) (seeds : C.Term → HashOutput) (x : Point) : Prop :=
  ∀ T ∈ C.terms, (s (.prf (seeds T) x)).isSome

/-- The cache holds every term and every mask of `Eval'(sk'_i, J, x, m)`. -/
def EvalCached (s : HashCache C) (keys : Keys C) (i : C.Party) (J : C.Quorum) (x : Point) (message : Message) : Prop :=
  (∀ T ∈ C.terms.filter (· ∈ L J i), (s (.prf (keys.seed T) x)).isSome) ∧
    ∀ j ∈ C.parties.filter (fun j => j ∈ J.1 ∧ j ≠ i), (s (.mask (keys.pairKey j) x message J)).isSome

theorem steady_hashQuery {s : HashCache C} {q : Query C} (hq : ∀ input, q ≠ .hash input) (hs : (s q).isSome) :
    Steady s (simulateQ (roImpl prims) (hashQuery q)) ((s q).getD 0) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  rw [hv]
  have : simulateQ (roImpl prims) (hashQuery q) = (Query C →ₒ HashOutput).randomOracle q := by
    cases q with
    | hash input => exact (hq input rfl).elim
    | _ => simp [hashQuery, roImpl, hashAnswer]
  rw [this]
  exact steady_randomOracle hv

theorem steady_prf {s : HashCache C} {seed : HashOutput} {x : Point} (hs : (s (.prf seed x)).isSome) :
    Steady s (simulateQ (roImpl prims) (prf seed x)) (cachedPrf s seed x) := by
  rw [prf, simulateQ_map]
  exact (steady_hashQuery (q := .prf seed x) (fun _ h => by cases h) hs).map _

theorem steady_prfValue {s : HashCache C} {seeds : C.Term → HashOutput} {x : Point} (hs : PrfValueCached s seeds x) :
    Steady s (simulateQ (roImpl prims) (prfValue seeds x)) (cachedPrfValue s seeds x) := by
  rw [prfValue, simulateQ_bind, simulateQ_list_mapM]
  exact (steady_mapM _ _ _ fun T hT => steady_prf (hs T hT)).bind (steady_pure s _)

theorem steady_eval {s : HashCache C} {keys : Keys C} {i : C.Party} {J : C.Quorum} {x : Point} {message : Message}
    (hs : EvalCached s keys i J x message) :
    Steady s (simulateQ (roImpl prims) (eval keys i J x message)) (cachedEval s keys i J x message) := by
  rw [eval, simulateQ_bind, simulateQ_list_mapM]
  refine (steady_mapM _ _ _ fun T hT => steady_prf (hs.1 T hT)).bind ?_
  rw [simulateQ_bind, simulateQ_list_mapM]
  refine (steady_mapM _ (fun j => truncateHash ((s (.mask (keys.pairKey j) x message J)).getD 0)) _
    fun j hj => ?_).bind ?_
  · rw [simulateQ_map]
    exact (steady_hashQuery (q := .mask (keys.pairKey j) x message J) (fun _ h => by cases h) (hs.2 j hj)).map _
  · exact steady_pure s _

end Cache

/-! ## The emulation gives the view of the signing service -/

section Emulation

variable (prims : Primitives)

theorem simulateQ_worldAnswer_honestLift {β : Type} (oa : OracleComp (RoSpec C) β) :
    simulateQ (worldAnswer prims) (honestLift oa) = simulateQ (roImpl prims) oa := by
  rw [honestLift, worldRoles, worldAnswer, simulateQ_free, simulateQ_localAnswer_liftComp]; rfl

theorem simulateQ_adversaryAnswer_liftComp {β : Type} (oa : OracleComp (RoSpec C) β) :
    simulateQ ((fun t => worldAnswer prims (.inl (.inl t))) : QueryImpl (LocalSpec C) (StateT (HashCache C) ProbComp))
      (liftComp oa (LocalSpec C)) = simulateQ (roImpl prims) oa :=
  simulateQ_localAnswer_liftComp prims oa

/-- The steps of `D₁` and `D₂` that request `q` reads give the same values and keep every cache that
extends `s`. -/
def SteadyOn (s : HashCache C) (D₁ D₂ : Dealt C (StateT (HashCache C) ProbComp)) : TsigQuery C → Prop
  | .corrupt _ => False
  | .tree b => ∃ v, Steady s (D₁.value (.randomizer topLayer (topKey b))) v ∧
      Steady s (D₂.value (.randomizer topLayer (topKey b))) v
  | q@(.round1 i J _ message) | q@(.round2 i J _ message _) => ∀ x, RequestPoint q x →
      ∃ v, Steady s (D₁.part i J x message) v ∧ Steady s (D₂.part i J x message) v

/-- Round 2 with two part steps that agree at the chain points of key `e` gives the same run. -/
theorem signRound2With_run_eq (part₁ part₂ : Point → StateT (HashCache C) ProbComp Digest)
    (parameter : PublicParameter) (J : C.Quorum) (commitment : Digest) (e : KeyIndex) (message : Message)
    (parts : C.Party → Digest) (s : HashCache C)
    (h : ∀ l (p : Digit), p.val < chainLength - 1 →
      ∃ w, Steady s (part₁ (.chain bottomLayer e l p)) w ∧ Steady s (part₂ (.chain bottomLayer e l p)) w) :
    (signRound2With (fun oa => simulateQ (roImpl prims) oa) part₁ parameter J commitment e message parts).run s =
      (signRound2With (fun oa => simulateQ (roImpl prims) oa) part₂ parameter J commitment e message parts).run s := by
  unfold signRound2With
  rw [StateT.run_bind, StateT.run_bind]
  refine bind_congr_of_forall_mem_support _ fun r hr => ?_
  have hle : s ≤ r.2 := (roRun_support prims _ s r hr).1
  rcases r with ⟨_ | ⟨_, encoding⟩, s'⟩
  · rfl
  · simp only [StateT.run_bind]
    have hl : ∀ l, ∃ v, Steady s (if (encoding l).val < chainLength - 1 then
        some <$> part₁ (.chain bottomLayer e l (encoding l)) else pure none) v ∧
        Steady s (if (encoding l).val < chainLength - 1 then
        some <$> part₂ (.chain bottomLayer e l (encoding l)) else pure none) v := fun l => by
      split_ifs with hp
      · obtain ⟨w, h₁, h₂⟩ := h l _ hp
        exact ⟨some w, h₁.map some, h₂.map some⟩
      · exact ⟨none, steady_pure s _, steady_pure s _⟩
    choose v hv using hl
    rw [(steady_sequenceFin _ v fun l => (hv l).1).run_eq (steady_sequenceFin _ v fun l => (hv l).2)
      (s' := s') hle]

/-- `bottomOnce` on a bottom tree that the dealer gives without a call. -/
theorem bottomOnce_run_of_pure (D : Dealt C (StateT (HashCache C) ProbComp)) (b : Fin (2 ^ layerHeight))
    (tree : Option BottomTree) (h : D.bottom b = pure tree) (st : TsigState C) :
    (bottomOnce D b).run st = pure (match st.trees b with
      | some stored => (stored, st)
      | none => (tree, { st with trees := Function.update st.trees b (some tree) })) := by
  unfold bottomOnce
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases st.trees b <;>
    simp [h, liftM, monadLift, MonadLift.monadLift, StateT.run_bind, StateT.run_lift, StateT.run_modify,
      StateT.run_pure]

/-- The signing service on two `Dealt` that agree on the steps of a request gives the same run. -/
theorem tsigOracles_run_eq (D₁ D₂ : Dealt C (StateT (HashCache C) ProbComp)) (hparameter : D₁.parameter = D₂.parameter)
    (htrees : ∀ b, ∃ tree, D₁.bottom b = pure tree ∧ D₂.bottom b = pure tree) (q : TsigQuery C)
    (st : TsigState C) (s : HashCache C) (hq : SteadyOn s D₁ D₂ q) :
    ((tsigOracles (fun oa => simulateQ (roImpl prims) oa) D₁ q).run st).run s =
      ((tsigOracles (fun oa => simulateQ (roImpl prims) oa) D₂ q).run st).run s := by
  cases q with
  | corrupt i => exact hq.elim
  | tree b =>
    obtain ⟨v, h₁, h₂⟩ := hq
    obtain ⟨tree, ht₁, ht₂⟩ := htrees b
    simp only [tsigOracles, StateT.run_bind, bottomOnce_run_of_pure D₁ b tree ht₁,
      bottomOnce_run_of_pure D₂ b tree ht₂, pure_bind]
    generalize (match st.trees b with
      | some stored => (stored, st)
      | none => (tree, { st with trees := Function.update st.trees b (some tree) })) = found
    rcases found with ⟨_ | tree, st'⟩
    · rfl
    · simp only [liftM, monadLift, MonadLift.monadLift, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        bind_assoc, pure_bind]
      rw [h₁ s le_rfl, h₂ s le_rfl]
  | round1 i J e message =>
    obtain ⟨v, h₁, h₂⟩ := hq _ rfl
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · simp only [liftM, monadLift, MonadLift.monadLift, StateT.run_bind, StateT.run_lift, StateT.run_pure,
        StateT.run_set, StateT.run_map, pure_bind]
      rw [h₁ s le_rfl, h₂ s le_rfl]
  | round2 i J e message parts =>
    obtain ⟨v, h₁, h₂⟩ := hq _ (.inl rfl)
    simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · rfl
    · obtain ⟨tree, ht₁, ht₂⟩ := htrees (treeOf e)
      simp only [StateT.run_bind, bottomOnce_run_of_pure D₁ _ tree ht₁, bottomOnce_run_of_pure D₂ _ tree ht₂,
        hparameter, pure_bind]
      generalize (match st.trees (treeOf e) with
        | some stored => (stored, st)
        | none => (tree, { st with trees := Function.update st.trees (treeOf e) (some tree) })) = found
      rcases found with ⟨_ | tree, st'⟩
      · rfl
      · simp only [liftM, monadLift, MonadLift.monadLift, StateT.run_bind, StateT.run_lift]
        simp only [bind_assoc, pure_bind]
        rw [h₁ s le_rfl, h₂ s le_rfl, pure_bind, pure_bind]
        simp only [StateT.run_pure, pure_bind]
        rw [signRound2With_run_eq prims (fun x => D₁.part i J x message) (fun x => D₂.part i J x message) _ _ _ _ _ _
            s (fun l p hp => hq _ (.inr ⟨l, p, hp, rfl⟩))]

/-- The cache already holds every hidden value that request `q` reads, and the tables hold them. -/
def Covers (s : HashCache C) (keys : C.Party → Keys C) (seeds : C.Term → HashOutput) (value : Point → Digest)
    (part : C.Party → C.Quorum → Point → Message → Digest) : TsigQuery C → Prop
  | .corrupt _ => False
  | .tree b => PrfValueCached s seeds (.randomizer topLayer (topKey b)) ∧
      value (.randomizer topLayer (topKey b)) = cachedPrfValue s seeds (.randomizer topLayer (topKey b))
  | q@(.round1 i J _ message) | q@(.round2 i J _ message _) => ∀ x, RequestPoint q x →
      EvalCached s (keys i) i J x message ∧ part i J x message = cachedEval s (keys i) i J x message

theorem getD_of_le {s s' : HashCache C} (hle : s ≤ s') {q : Query C} (hq : (s q).isSome) :
    (s' q).isSome ∧ (s' q).getD 0 = (s q).getD 0 := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hq
  rw [hv, hle hv]
  exact ⟨rfl, rfl⟩

/-- A larger cache still covers a request, with the same tables. So the emulation runs request after
request, while the signing service only adds entries to the cache. -/
theorem Covers.mono {s s' : HashCache C} (hle : s ≤ s') {keys : C.Party → Keys C} {seeds : C.Term → HashOutput}
    {value : Point → Digest} {part : C.Party → C.Quorum → Point → Message → Digest} {q : TsigQuery C}
    (hq : Covers s keys seeds value part q) : Covers s' keys seeds value part q := by
  have hprf : ∀ x, PrfValueCached s seeds x →
      PrfValueCached s' seeds x ∧ cachedPrfValue s' seeds x = cachedPrfValue s seeds x := fun x h => by
    refine ⟨fun T hT => (getD_of_le hle (h T hT)).1, ?_⟩
    unfold cachedPrfValue cachedPrf
    congr 1
    exact List.map_congr_left fun T hT => by rw [(getD_of_le hle (h T hT)).2]
  have heval : ∀ i J x message, EvalCached s (keys i) i J x message →
      EvalCached s' (keys i) i J x message ∧
        cachedEval s' (keys i) i J x message = cachedEval s (keys i) i J x message := fun i J x message h => by
    refine ⟨⟨fun T hT => (getD_of_le hle (h.1 T hT)).1, fun j hj => (getD_of_le hle (h.2 j hj)).1⟩, ?_⟩
    unfold cachedEval cachedPrf
    congr 2
    · exact List.map_congr_left fun T hT => by rw [(getD_of_le hle (h.1 T hT)).2]
    · exact List.map_congr_left fun j hj => by rw [(getD_of_le hle (h.2 j hj)).2]
  cases q with
  | corrupt i => exact hq
  | tree b => exact ⟨(hprf _ hq.1).1, hq.2.trans (hprf _ hq.1).2.symm⟩
  | round1 i J e message | round2 i J e message parts =>
    exact fun x hx => ⟨(heval i J x message (hq x hx).1).1,
      (hq x hx).2.trans (heval i J x message (hq x hx).1).2.symm⟩

/-- The signing emulation. From a cache that holds the hidden values of request `q`, the service
that the ceremony adversary runs on its own oracles gives the same output, the same state and the
same cache as the signing service of the lifetime. -/
theorem emulatedOracles_run (parameter : PublicParameter) (keys : C.Party → Keys C) (top : TopTree)
    (trees : Fin (2 ^ layerHeight) → Option BottomTree) (seeds : C.Term → HashOutput) (value : Point → Digest)
    (part : C.Party → C.Quorum → Point → Message → Digest) (q : TsigQuery C) (st : TsigState C)
    (s : HashCache C) (hq : Covers s keys seeds value part q) :
    (simulateQ (worldAnswer prims) ((tsigOracles honestLift (signerDealt parameter keys top trees seeds) q).run st)).run s =
      (simulateQ (worldAnswer prims)
        (worldRoles.adversary ((emulatedOracles parameter top trees value part q).run st))).run s := by
  rw [simulateQ_adversary_split, emulatedOracles]
  have h₁ := hom_tsigOracles (simulateQ' (worldAnswer prims)) honestLift (signerDealt parameter keys top trees seeds) q st
  have h₂ := hom_tsigOracles (simulateQ' ((fun t => worldAnswer prims (.inl (.inl t))) :
    QueryImpl (LocalSpec C) (StateT (HashCache C) ProbComp))) (fun oa => liftComp oa (LocalSpec C))
    (emulatedDealt parameter top trees value part) q st
  simp only [simulateQ'] at h₁ h₂
  rw [h₁, h₂]
  simp only [simulateQ_worldAnswer_honestLift, simulateQ_adversaryAnswer_liftComp]
  refine tsigOracles_run_eq prims _ _ ?_ ?_ q st s ?_
  · rfl
  · exact fun b => ⟨trees b, by simp [Dealt.hmap, signerDealt], by simp [Dealt.hmap, emulatedDealt]⟩
  cases q with
  | corrupt i => exact hq.elim
  | tree b =>
    refine ⟨cachedPrfValue s seeds (.randomizer topLayer (topKey b)), ?_, ?_⟩
    · simp only [Dealt.hmap, signerDealt, dealtWith, simulateQ_worldAnswer_honestLift]
      exact steady_prfValue hq.1
    · simp only [Dealt.hmap, emulatedDealt, simulateQ_pure, hq.2]
      exact steady_pure s _
  | round1 i J e message | round2 i J e message parts =>
    intro x hx
    refine ⟨cachedEval s (keys i) i J x message, ?_, ?_⟩
    · simp only [Dealt.hmap, signerDealt, dealtWith, simulateQ_worldAnswer_honestLift]
      exact steady_eval (hq x hx).1
    · simp only [Dealt.hmap, emulatedDealt, simulateQ_pure, (hq x hx).2]
      exact steady_pure s _

end Emulation

/-! ## The tables in the auxiliary input -/

section Encoding

/-- The data of `emulatedOracles`, namely the parameter, the top tree, the bottom trees, the PRF values
and the parts. -/
abbrev SigningTables (C : Committee) :=
  PublicParameter × TopTree × (Fin (2 ^ layerHeight) → Option BottomTree) × (Point → Digest) ×
    (C.Party → C.Quorum → Point → Message → Digest)

instance : Finite Point :=
  Finite.of_injective (β := (Layer × KeyIndex × ChainIndex × Digit) ⊕ (Layer × KeyIndex))
    (fun | .chain lay e l p => .inl (lay, e, l, p) | .randomizer lay e => .inr (lay, e))
    (fun x y h => by cases x <;> cases y <;> simp_all)

instance : Countable TopTree :=
  Function.Injective.countable (f := fun t : TopTree => (t.chainEnd, t.root))
    (fun x y h => by cases x; cases y; simp_all)

instance : Countable LayerSignature :=
  Function.Injective.countable (f := fun t : LayerSignature => (t.randomness, t.chainValues, t.path))
    (fun x y h => by cases x; cases y; simp_all)

instance : Countable BottomTree :=
  Function.Injective.countable (f := fun t : BottomTree => (t.cpk, t.commitment, t.root, t.topSignature))
    (fun x y h => by cases x; cases y; simp_all)

instance : Countable (SigningTables C) := by
  have : Countable (Message → Digest) := inferInstance
  have : Countable (Point → Message → Digest) := inferInstance
  have : Countable (C.Quorum → Point → Message → Digest) := inferInstance
  have : Countable (C.Party → C.Quorum → Point → Message → Digest) := inferInstance
  have : Countable (Fin (2 ^ layerHeight) → Option BottomTree) := inferInstance
  unfold SigningTables; infer_instance

/-- A countable value as an auxiliary input, in unary. -/
def encodeAux {α : Type} [Countable α] (a : α) : Aux :=
  List.replicate (@Encodable.encode α (Encodable.ofCountable α) a) true

/-- The value of an auxiliary input that `encodeAux` gives. -/
def decodeAux {α : Type} [Countable α] (z : Aux) : Option α :=
  @Encodable.decode α (Encodable.ofCountable α) z.length

theorem decodeAux_encodeAux {α : Type} [Countable α] (a : α) : decodeAux (encodeAux a) = some a := by
  rw [decodeAux, encodeAux, List.length_replicate]
  exact @Encodable.encodek α (Encodable.ofCountable α) a

end Encoding

/-- info: 'ThresholdLeanXmssSecurity.requestPoint_not_ceremonyPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms requestPoint_not_ceremonyPoint

/-- info: 'ThresholdLeanXmssSecurity.emulatedOracles_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms emulatedOracles_run

/-- info: 'ThresholdLeanXmssSecurity.Covers.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Covers.mono

/-- info: 'ThresholdLeanXmssSecurity.decodeAux_encodeAux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decodeAux_encodeAux

end ThresholdLeanXmssSecurity
