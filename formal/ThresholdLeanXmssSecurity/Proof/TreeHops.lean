import ThresholdLeanXmssSecurity.Proof.TreeSecurity
import ThresholdLeanXmssSecurity.Proof.Coupling

/-!
# The two hops of a ceremony

`TreeHopsRemaining` is the stream-key bound `TreeStreamKeyBound` and the simulation hop
`TreeSimulationHop` with the split `keySplit`. `treeSecurityFull` gives `TreeSecurityStatement`
from the two open stages below by `treeSecurityProof`.

## The key hop up to the derivation boundary (proved)

1. `treeRealGame_eq_split`: the real game is `setupPrefix` (the start of the adversary, the first two
   setup rounds and the opening checks, derivations and echo hashes of the reveal round) followed by
   `afterDerivation` (the echo round, the batches and the distinguisher).
2. `qb0_setupPrefix`: the prefix makes no stream call. So in the ideal joint world no private key is
   in use and no flag rises before the boundary (`jointKeyWorld_false_simulate_eq`).
3. `probBad_streamKey_eq_afterDerivation`: the bad event of the whole game is the bad event of the
   ideal joint world started at the boundary from the cache of the world (`boundaryState`).

## Open stage 1: `TreeStreamKeyAfterDerivation`

A plan, in the ideal joint world from the boundary.
1. Discipline. Every honest free call after the boundary is a hash other than `.streamKey`, a
   sampling, or a stream under the key that the boundary rows give its own context. This is a walk of
   `ceremonyAfterSetup`, as the rename walk `rename_ceremonyAfterSetup` of `Tree.lean`.
2. With 1, a flag rises only on (a) a boundary collision: a hidden derived key with a cached
   `.streamKey` entry, or equal to the key of another name in some row; or (b) a hit: a counted call
   after the boundary on `.streamKey k` or on a stream under `k`, for a hidden derived key `k`.
3. (a) is a predicate of `worldRun prims (setupPrefix ..)`. Its derivation inputs are fresh with
   probability `prob_prssEarlyCachedInput_le` (to be moved from the logged local table to the world),
   and fresh derived keys collide with probability at most the birthday term in `streamKeyError`.
4. (b) needs the secrecy of the hidden parts and keys after the boundary: the swap of a derived key
   value in the cache entry and in the honest consumption (`PrssEchoRelabeling` and
   `evalDist_lazyKey_ceremony_swap` of `Tree.lean`, carried to `KeyJointState`), then
   `probEvent_hit_realExecution_le`. It costs `2 q m / 2 ^ 256` of `keySplit`.

## Open stage 2: `TreeSimulationHop`

GS20, Theorem 2, over the whole ceremony with the real gadgets, by `abs_accepts_lockstep_sub_le`
with the uniform shift of the hidden streams at each reshare, `Rerand` and `openRep` (the `T₀`
shift), as `MainStages.lean` does for one batch in the hybrid model. The dealer of `F_tree` queries
`H` before the emulation, so the hash order differs from the real run; the eager oracle of
`evalDist_prssLocal_eager` removes the order. The undetected-attack case uses the check soundness.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section JointNoStream

variable {C : Committee}

/-! ## The joint key world without honest streams -/

/-- An honest stream call, the only call that records a private stream key. -/
def FreeStream : (WorldSpec C).Domain → Prop
  | .inr (.inr (.inr _)) => True
  | _ => False

theorem onJointHash_frame {α : Type} (m : StateT (HashCache C) ProbComp α) (s : KeyJointState C) :
    ∀ r ∈ support ((onJointHash m).run s), r.2.used = s.used ∧ r.2.keys = s.keys ∧ r.2.bad = s.bad := by
  intro r hr
  simp only [onJointHash, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, _, rfl⟩ := hr
  exact ⟨rfl, rfl, rfl⟩

theorem jointHash_frame (prims : Primitives) (real : Bool) (q : Query C) (s : KeyJointState C) :
    ∀ r ∈ support ((jointHash prims real q).run s), r.2.used = s.used ∧ r.2.keys = s.keys ∧ r.2.bad = s.bad := by
  intro r hr
  cases q with
  | streamKey k =>
    simp only [jointHash, StateT.run_mk] at hr
    split_ifs at hr
    · split at hr
      · simp only [support_pure, Set.mem_singleton_iff] at hr
        subst hr
        exact ⟨rfl, rfl, rfl⟩
      · exact onJointHash_frame _ s r hr
    · exact onJointHash_frame _ s r hr
  | _ => exact onJointHash_frame _ s r hr

theorem jointProgram_frame (real : Bool) (x : Query C × HashOutput) (s : KeyJointState C) :
    ∀ r ∈ support ((jointProgram real x).run s), r.2.used = s.used ∧ r.2.keys = s.keys ∧ r.2.bad = s.bad := by
  intro r hr
  rcases x with ⟨q, v⟩
  cases q with
  | streamKey k =>
    simp only [jointProgram, StateT.run_mk] at hr
    split_ifs at hr
    · simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨rfl, rfl, rfl⟩
    · exact onJointHash_frame _ s r hr
  | _ => exact onJointHash_frame _ s r hr

theorem jointLocal_frame (prims : Primitives) (real : Bool) (t : (LocalSpec C).Domain) (s : KeyJointState C) :
    ∀ r ∈ support ((jointLocal prims real t).run s), r.2.used = s.used ∧ r.2.keys = s.keys ∧ r.2.bad = s.bad := by
  intro r hr
  rcases t with u | q | x
  · exact onJointHash_frame _ s r hr
  · exact jointHash_frame prims real q s r hr
  · simp only [jointLocal, StateT.run_bind, StateT.run_pure, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    exact jointHash_frame prims real _ s p hp

/-- Without a private key in use, a call other than an honest stream keeps the private state and
raises no flag. -/
theorem jointKeyWorld_frame (prims : Primitives) (D : C.Coalition) (real : Bool)
    (q : (WorldSpec C).Domain) (hq : ¬ FreeStream q) (s : KeyJointState C) (hs : ∀ k, s.used k = none) :
    ∀ r ∈ support ((jointKeyWorld prims D real q).run s), r.2.used = s.used ∧ r.2.keys = s.keys ∧ r.2.bad = s.bad := by
  intro r hr
  simp only [jointKeyWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  have hrisk : keyJointRisk D q s = false := by
    rcases q with ((u | q | x) | ⟨q, v⟩) | (u | q | x)
    all_goals first
      | exact absurd trivial hq
      | rfl
      | (cases q <;> simp [keyJointRisk, hs])
      | simp [keyJointRisk, hs]
  have hcore : p.2.used = s.used ∧ p.2.keys = s.keys ∧ p.2.bad = s.bad := by
    rcases q with ((u | q | x) | x) | (u | q | x)
    · exact jointLocal_frame prims real (.inl u) s p hp
    · exact jointLocal_frame prims real (.inr (.inl q)) s p hp
    · exact jointLocal_frame prims real (.inr (.inr x)) s p hp
    · exact jointProgram_frame real x s p hp
    · exact jointLocal_frame prims real (.inl u) s p hp
    · exact jointLocal_frame prims real (.inr (.inl q)) s p hp
    · exact absurd trivial hq
  refine ⟨hcore.1, hcore.2.1, ?_⟩
  simp [hrisk]

/-- A computation without honest streams, run from a state with no private key in use, keeps the
private state and raises no flag. -/
theorem jointKeyWorld_run_frame (prims : Primitives) (D : C.Coalition) (real : Bool) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (hoa : IsQueryBoundP oa FreeStream 0)
    (s : KeyJointState C) (hs : ∀ k, s.used k = none) :
    ∀ r ∈ support ((simulateQ (jointKeyWorld prims D real) oa).run s),
      r.2.used = s.used ∧ r.2.keys = s.keys ∧ r.2.bad = s.bad := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨rfl, rfl, rfl⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have ht : ¬ FreeStream t := by
      rcases hoa.1 with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    intro r hr
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hr
    obtain ⟨p, hp, hr⟩ := hr
    have h₁ := jointKeyWorld_frame prims D real t ht s hs p hp
    have hk : IsQueryBoundP (k p.1) FreeStream 0 := by
      have := hoa.2 p.1
      rwa [if_neg ht] at this
    have h₂ := ih p.1 hk p.2 (fun k => h₁.1 ▸ hs k) r hr
    exact ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

/-- Without a private key in use, the ideal joint world answers a call other than an honest stream
as the world does on the public cache. -/
theorem jointKeyWorld_false_run_eq (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (hq : ¬ FreeStream q) (s : KeyJointState C) (hs : ∀ k, s.used k = none) :
    (jointKeyWorld prims D false q).run s =
      (fun r => (r.1, { s with hash := r.2 })) <$> (worldAnswer prims q).run s.hash := by
  have hrisk : keyJointRisk D q s = false := by
    rcases q with ((u | q | x) | ⟨q, v⟩) | (u | q | x)
    all_goals first
      | exact absurd trivial hq
      | rfl
      | (cases q <;> simp [keyJointRisk, hs])
      | simp [keyJointRisk, hs]
  have hcore : (jointKeyWorldCore prims D false q).run s =
      (fun r => (r.1, { s with hash := r.2 })) <$> (worldAnswer prims q).run s.hash := by
    rcases q with ((u | q | x) | x) | (u | q | x)
    · simp only [jointKeyWorldCore, jointLocal_false, onJointHash]; rfl
    · simp only [jointKeyWorldCore, jointLocal_false, onJointHash]; rfl
    · simp only [jointKeyWorldCore, jointLocal_false, onJointHash]; rfl
    · simp only [jointKeyWorldCore, jointProgram_false, onJointHash]; rfl
    · simp only [jointKeyWorldCore, jointLocal_false, onJointHash]; rfl
    · simp only [jointKeyWorldCore, jointLocal_false, onJointHash]; rfl
    · exact absurd trivial hq
  simp only [jointKeyWorld, StateT.run_mk, hcore, hrisk, Bool.or_false, Functor.map_map]

/-- A computation without honest streams runs in the ideal joint world as in the world, from a state
with no private key in use. -/
theorem jointKeyWorld_false_simulate_eq (prims : Primitives) (D : C.Coalition) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (hoa : IsQueryBoundP oa FreeStream 0)
    (s : KeyJointState C) (hs : ∀ k, s.used k = none) :
    (simulateQ (jointKeyWorld prims D false) oa).run s =
      (fun r => (r.1, { s with hash := r.2 })) <$> (simulateQ (worldAnswer prims) oa).run s.hash := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa
    have ht : ¬ FreeStream t := by
      rcases hoa.1 with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    have hk : ∀ u, IsQueryBoundP (k u) FreeStream 0 := fun u => by
      have := hoa.2 u
      rwa [if_neg ht] at this
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, map_bind]
    rw [jointKeyWorld_false_run_eq prims D t ht s hs, bind_map_left]
    refine bind_congr fun r => ?_
    exact ih r.1 (hk r.1) { s with hash := r.2 } hs

/-! ## Computations without streams -/

/-- A stream call of a party. -/
def LocalStream : (LocalSpec C).Domain → Prop
  | .inr (.inr _) => True
  | _ => False

/-- A stream call of `H` and `PRG`. -/
def RoStream : (RoSpec C).Domain → Prop
  | .inr _ => True
  | _ => False

theorem qb0_bind {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p] {α β : Type}
    {oa : OracleComp spec α} {f : α → OracleComp spec β} (h : IsQueryBoundP oa p 0)
    (hf : ∀ a, IsQueryBoundP (f a) p 0) : IsQueryBoundP (oa >>= f) p 0 := by
  simpa using isQueryBoundP_bind (m := 0) h fun a _ => hf a

theorem qb0_mapM {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p] {α β : Type}
    (f : α → OracleComp spec β) (hf : ∀ a, IsQueryBoundP (f a) p 0) :
    ∀ xs : List α, IsQueryBoundP (xs.mapM f) p 0
  | [] => by simp
  | x :: xs => by
    rw [List.mapM_cons]
    exact qb0_bind (hf x) fun _ => qb0_bind (qb0_mapM f hf xs) fun _ => by simp

theorem qb0_hashQuery (q : Query C) : IsQueryBoundP (hashQuery q) (RoStream (C := C)) 0 := by
  unfold hashQuery
  erw [isQueryBoundP_query_iff]
  intro h
  exact absurd h (by simp [RoStream])

theorem qb0_liftComp_ro {α : Type} (oa : OracleComp (RoSpec C) α) (h : IsQueryBoundP oa RoStream 0) :
    IsQueryBoundP (liftComp oa (LocalSpec C)) (LocalStream (C := C)) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t f ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ RoStream t := by
      rcases h.1 with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    rw [liftComp_bind]
    erw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl ?_, fun u => ?_⟩
    · rcases t with q | x
      · simp [LocalStream]
      · exact absurd trivial ht
    · have := h.2 u
      rw [if_neg ht] at this
      simpa only [Nat.zero_sub, ite_self] using ih u this

theorem qb0_liftComp_prob {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftComp oa (LocalSpec C)) (LocalStream (C := C)) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t f ih =>
    rw [liftComp_bind]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [LocalStream]), fun u => by simpa only [Nat.zero_sub, ite_self] using ih u⟩

theorem qb0_free {α : Type} (oa : OracleComp (LocalSpec C) α) (h : IsQueryBoundP oa LocalStream 0) :
    IsQueryBoundP (free oa) (FreeStream (C := C)) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [free]; exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ LocalStream t := by
      rcases h.1 with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    have e : free (liftM (OracleSpec.query t) >>= k) =
        (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _) >>= fun u => free (k u) := by
      rw [free_bind]
      rfl
    rw [e, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl ?_, fun u => ?_⟩
    · rcases t with u | q | x
      · simp [FreeStream]
      · simp [FreeStream]
      · exact absurd trivial ht
    · have := h.2 u
      rw [if_neg ht] at this
      simpa only [Nat.zero_sub, ite_self] using ih u this

theorem qb0_adversary {α : Type} (oa : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (worldRoles.adversary oa) (FreeStream (C := C)) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [worldRoles, counted, liftComp_pure]; exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (k u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, adversary_query]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [FreeStream]), fun u => by simpa only [Nat.zero_sub, ite_self] using ih u⟩

theorem qb0_hashes {β : Type} (xs : List β) (f : β → Query C) :
    IsQueryBoundP (xs.mapM fun x => hashQuery (f x)) (RoStream (C := C)) 0 :=
  qb0_mapM _ (fun x => qb0_hashQuery (f x)) xs

theorem qb0_deriveKeys (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    IsQueryBoundP (deriveKeys phase i view) (RoStream (C := C)) 0 := by
  unfold deriveKeys
  dsimp only
  split_ifs
  all_goals first | refine qb0_bind (qb0_hashQuery _) fun _ => ?_ | simp only [pure_bind]
  all_goals refine qb0_bind (qb0_mapM _ (fun T => ?_) _) fun _ =>
    qb0_bind (qb0_mapM _ (fun j => ?_) _) fun _ => by simp
  all_goals split_ifs
  all_goals first | exact qb0_hashQuery _ | simp

theorem qb0_prssInitialData (D : C.Coalition) :
    IsQueryBoundP (prssInitialData (C := C) D) (LocalStream (C := C)) 0 := by
  unfold prssInitialData
  refine isQueryBoundP_sequenceFin _ fun i => ?_
  split_ifs
  · simp
  · exact qb0_bind (qb0_liftComp_prob _) fun _ =>
      qb0_bind (qb0_liftComp_ro _ (qb0_hashes _ _)) fun _ => by simp

theorem qb0_prssRevealRows (D : C.Coalition) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) :
    IsQueryBoundP (prssRevealRows D active parts committed sent) (LocalStream (C := C)) 0 := by
  unfold prssRevealRows
  refine isQueryBoundP_sequenceFin _ fun i => ?_
  split_ifs
  · simp
  · unfold prssRevealData
    split_ifs
    · simp
    · unfold prssPostRevealData
      refine qb0_bind (qb0_liftComp_ro _ (qb0_hashes _ _)) fun _ => ?_
      split_ifs
      · exact qb0_bind (qb0_liftComp_ro _ (qb0_deriveKeys _ _ _)) fun _ =>
          qb0_bind (qb0_liftComp_ro _ (qb0_hashes _ _)) fun _ => by simp
      · simp
  · simp

end JointNoStream

/-! ## The real game at the derivation boundary -/

section SetupSplit

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The rows of the reveal round, namely the derived PRSS keys and the echo hashes of each operator. -/
abbrev RevealRows (C : Committee) := C.Party → Option (PrssKeys C × List HashOutput)

/-- The real game up to the derivation of the PRSS keys: the start of the adversary, the commitments,
the first two setup rounds, and the opening checks, derivations and echo hashes of the reveal round. -/
def setupPrefix (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (z : Aux) : OracleComp (WorldSpec C) (A.State × Option (RevealRows C)) := do
  let state ← worldRoles.adversary (A.start (corruptInputs D x) z)
  let data ← free (prssInitialData D)
  let (state', sent, revealed) ← worldRoles.adversary (prssEarlyDataRounds D A state data)
  match revealed with
  | none => pure (state', none)
  | some sent' => do
    let rows ← free (prssRevealRows D (prssCommitActive D sent) (fun i => (data i).1)
      (prssCommitInbox D data sent) sent')
    pure (state', some rows)

/-- The rest of the real game after the derivation of the PRSS keys: the echo round, the batches and
the distinguisher. -/
def afterDerivation (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (Z : Distinguisher C A.State TreeOutput) :
    A.State × Option (RevealRows C) → OracleComp (WorldSpec C) Bool
  | (state', none) => worldRoles.adversary (Z (state', fun _ => none))
  | (state', some rows) => do
    let r ← executeRounds worldRoles D A noFunctionality (ceremonyFuel circuits settings - 2) state'
      (fun i => suspendStep (fun prss => (ceremonyAfterSetup K circuits settings ⟨i, x i, prss⟩ top tree :
        PartyM C E RealSpec TreeOutput)) (prssFinishStep i (rows i)))
    worldRoles.adversary (Z r)

theorem treeRealGame_eq_split (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    treeRealGame K circuits settings top tree D A x z Z =
      setupPrefix D A x z >>= afterDerivation K circuits settings top tree D A x Z := by
  have hf : ceremonyFuel circuits settings = (ceremonyFuel circuits settings - 2) + 2 := by
    unfold ceremonyFuel setupRounds; omega
  unfold treeRealGame distinguish realExecution
  rw [hf]
  simp only [ceremony_eq_prssSetup_bind]
  unfold setupPrefix
  simp only [bind_assoc]
  refine bind_congr fun state => ?_
  rw [executePhase_prssSetup_early D A state _
    (fun i prss => ceremonyAfterSetup K circuits settings ⟨i, x i, prss⟩ top tree)]
  simp only [bind_assoc]
  refine bind_congr fun data => ?_
  refine bind_congr fun r => ?_
  rcases r with ⟨state', sent, revealed⟩
  cases revealed with
  | none => simp [afterDerivation]
  | some sent' => simp [afterDerivation]

omit [Field E] [Algebra Bit E] in
/-- The setup prefix makes no stream call. -/
theorem qb0_setupPrefix (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (z : Aux) : IsQueryBoundP (setupPrefix D A x z) (FreeStream (C := C)) 0 := by
  unfold setupPrefix
  refine qb0_bind (qb0_adversary _) fun state => ?_
  refine qb0_bind (qb0_free _ (qb0_prssInitialData D)) fun data => ?_
  refine qb0_bind (qb0_adversary _) fun r => ?_
  rcases r with ⟨state', sent, revealed⟩
  cases revealed with
  | none => simp
  | some sent' =>
    exact qb0_bind (qb0_free _ (qb0_prssRevealRows D _ _ _ _)) fun _ => by simp

end SetupSplit

/-! ## The stream-key bound from the derivation boundary -/

section KeyBoundary

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The joint state at the derivation boundary: the public cache of the world, no private key yet. -/
def boundaryState (hash : HashCache C) : KeyJointState C := ⟨hash, ∅, fun _ => none, false⟩

/-- The stream-key bad event of the ideal joint world, run from the derivation boundary that the
world reaches. No flag can rise before it (`setupPrefix` makes no stream call). -/
def TreeStreamKeyAfterDerivation : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    (Pr[fun r => r.2.bad = true | worldRun prims (setupPrefix D A x z) >>= fun r =>
      (simulateQ (jointKeyWorld prims D false) (afterDerivation K circuits settings top tree D A x Z r.1)).run
        (boundaryState r.2)]).toReal ≤ streamKeyError C + keySplit C q

omit [Fintype E] [DecidableEq E] in
/-- The bad event of the whole real game is the one after the derivation boundary. -/
theorem probBad_streamKey_eq_afterDerivation (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    probBad_streamKey prims D (treeRealGame K circuits settings top tree D A x z Z) =
      (Pr[fun r => r.2.bad = true | worldRun prims (setupPrefix D A x z) >>= fun r =>
        (simulateQ (jointKeyWorld prims D false) (afterDerivation K circuits settings top tree D A x Z r.1)).run
          (boundaryState r.2)]).toReal := by
  rw [probBad_streamKey_eq_ideal, treeRealGame_eq_split, simulateQ_bind, StateT.run_bind,
    jointKeyWorld_false_simulate_eq prims D _ (qb0_setupPrefix D A x z) keyJointInitial (fun _ => rfl),
    bind_map_left]
  rfl

omit [Fintype E] [DecidableEq E] in
theorem treeStreamKeyBound_of_afterDerivation (h : TreeStreamKeyAfterDerivation prims K circuits settings) :
    TreeStreamKeyBound prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq
  rw [probBad_streamKey_eq_afterDerivation]
  exact h hb top tree D A x z Z q hx hq

end KeyBoundary

section TreeHopsAssembly

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- `TreeSecurityStatement` from the two open stages: the stream-key bound after the derivation
boundary and the simulation hop. -/
theorem treeSecurityFull (hKey : TreeStreamKeyAfterDerivation prims K circuits settings)
    (hSim : TreeSimulationHop prims K circuits settings (keySplit C)) :
    TreeSecurityStatement prims K circuits settings :=
  treeSecurityProof prims K circuits settings
    ⟨treeStreamKeyBound_of_afterDerivation prims K circuits settings hKey, hSim⟩

end TreeHopsAssembly

/-- info: 'ThresholdLeanXmssSecurity.treeSecurityFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSecurityFull

end ThresholdLeanXmssSecurity
