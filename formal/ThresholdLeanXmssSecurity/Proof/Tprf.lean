import ThresholdLeanXmssSecurity.Proof.Execution
import ThresholdLeanXmssSecurity.Proof.Lemmas
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# The threshold PRF

PRAWNS, Definition 2.1 (`tprfCorrectness`), and PRAWNS, Definition 2.2 with Theorem 5.1
(`tprfSecurity`), in the random-oracle model of `ThresholdLeanXmss/Scheme.lean`.

The security proof follows PRAWNS, Theorem 5.1, without the guess of Lemma 5.2.

* The real game splits the cache of `H` into the slots of the keys and the other inputs.
* The symbolic game lets the honest operators read the slots, and the adversary reads only the
  slots of revealed keys. The two games agree until the adversary queries an unrevealed key.
* On a full table of the slots, the hidden term value and the private masks shift the challenge
  answers without a change of the view, so the symbolic game does not depend on `b`.
* Each key is hidden until its reveal, so a query hits it with probability `2^-256`.
* A collision of two seeds or two pair keys counts once.
-/

open OracleComp OracleSpec LeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

/-! ## Correctness -/

namespace TprfCorrectnessProof

variable {C : Committee}

/-- `Digest` with `^^^` as the addition, so that a fold of `^^^` is a sum. -/
def XorDigest := Digest

instance : Zero XorDigest := ⟨(0 : Digest)⟩

instance : Add XorDigest := ⟨fun a b => BitVec.xor a b⟩

instance : Neg XorDigest := ⟨id⟩

instance : AddCommGroup XorDigest where
  add_assoc a b c := BitVec.xor_assoc a b c
  zero_add a := BitVec.zero_xor (x := a)
  add_zero a := BitVec.xor_zero (x := a)
  add_comm a b := BitVec.xor_comm a b
  neg_add_cancel a := BitVec.xor_self (x := a)
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- A digest as an element of `XorDigest`. -/
def toXor (d : Digest) : XorDigest := d

theorem toXor_foldl {α : Type} [DecidableEq α] (f : α → Digest) (a : Digest) (l : List α) (hl : l.Nodup) :
    toXor (l.foldl (fun acc x => acc ^^^ f x) a) = toXor a + ∑ x ∈ l.toFinset, toXor (f x) := by
  rw [List.sum_toFinset _ hl]
  clear hl
  induction l generalizing a with
  | nil => exact (add_zero _).symm
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    exact add_assoc (toXor a) (toXor (f x)) _

theorem toXor_zero : toXor 0#digestBits = 0 := rfl

theorem mapM_id {α β : Type} (g : α → Id β) (l : List α) : List.mapM g l = (l.map g : List β) :=
  List.mapM_pure (m := Id) (f := g)

/-- The answers of `H` and `PRG` that a table of `H` fixes, as `hashAnswer` and `prgAnswer` give them. -/
def tableAnswer (prims : Primitives) (f : Query C → HashOutput) : QueryImpl (RoSpec C) Id := fun t =>
  open Classical in
  match t with
  | .inl (.hash input) => if MpcInput input then prims.Th input else f (.hash input)
  | .inl q => f q
  | .inr x => prims.aes.eval (truncateHash (f (.streamKey x.2.1))) x.2.2

theorem simulateQ_sequenceFin {ι : Type} {spec : OracleSpec ι} {α : Type} (impl : QueryImpl spec Id) {k : ℕ}
    (g : Fin k → OracleComp spec α) :
    simulateQ impl (Concrete.sequenceFin g) = fun i => simulateQ impl (g i) := by
  induction k with
  | zero => funext i; exact i.elim0
  | succ k ih =>
    rw [Concrete.sequenceFin]
    simp only [simulateQ_bind, ih, simulateQ_pure]
    funext i
    cases i using Fin.cases <;> rfl

variable (prims : Primitives) (f : Query C → HashOutput)

theorem toXor_combine (J : C.Quorum) (parts : C.Party → Digest) :
    toXor (combine J parts) = ∑ i ∈ J.1, toXor (parts i) := by
  have hp : C.parties.Nodup := List.nodup_finRange _
  rw [combine, toXor_foldl _ _ _ (hp.filter _)]
  simp [Committee.parties, toXor_zero]

theorem tableAnswer_prf (seed : HashOutput) (x : Point) :
    simulateQ (tableAnswer prims f) (hashQuery (.prf seed x)) = f (.prf seed x) := by
  simp [hashQuery, tableAnswer]

theorem tableAnswer_mask (key : HashOutput) (x : Point) (message : Message) (J : C.Quorum) :
    simulateQ (tableAnswer prims f) (hashQuery (.mask key x message J)) = f (.mask key x message J) := by
  simp [hashQuery, tableAnswer]

theorem toXor_prfValue (seeds : C.Term → HashOutput) (x : Point) :
    toXor (simulateQ (tableAnswer prims f) (prfValue seeds x)) =
      ∑ T, toXor (truncateHash (f (.prf (seeds T) x))) := by
  have ht : C.terms.Nodup := Finset.nodup_toList _
  simp only [prfValue, prf, simulateQ_list_mapM, simulateQ_bind, simulateQ_pure, simulateQ_map,
    tableAnswer_prf, mapM_id]
  change toXor ((C.terms.map fun T => truncateHash (f (.prf (seeds T) x))).foldl (fun acc d => acc ^^^ id d) 0) = _
  rw [List.foldl_map, toXor_foldl _ _ _ ht]
  simp [Committee.terms, toXor_zero]

theorem toXor_eval (keys : Keys C) (i : C.Party) (J : C.Quorum) (x : Point) (message : Message) :
    toXor (simulateQ (tableAnswer prims f) (eval keys i J x message)) =
      ∑ T ∈ L J i, toXor (truncateHash (f (.prf (keys.seed T) x))) +
        ∑ j ∈ univ.filter (fun j => j ∈ J.1 ∧ j ≠ i), toXor (truncateHash (f (.mask (keys.pairKey j) x message J))) := by
  have ht : C.terms.Nodup := Finset.nodup_toList _
  have hp : C.parties.Nodup := List.nodup_finRange _
  simp only [eval, prf, simulateQ_list_mapM, simulateQ_bind, simulateQ_pure, simulateQ_map,
    tableAnswer_prf, tableAnswer_mask, mapM_id]
  change toXor ((((C.terms.filter (· ∈ L J i)).map fun T => truncateHash (f (.prf (keys.seed T) x))) ++
    (C.parties.filter fun j => j ∈ J.1 ∧ j ≠ i).map fun j => truncateHash (f (.mask (keys.pairKey j) x message J))).foldl
      (fun acc d => acc ^^^ id d) 0) = _
  rw [List.foldl_append, List.foldl_map, List.foldl_map, toXor_foldl _ _ _ (hp.filter _),
    toXor_foldl _ _ _ (ht.filter _)]
  simp [L, Committee.terms, Committee.parties, toXor_zero]

/-- A symmetric value summed over the ordered pairs of distinct members cancels. -/
theorem sum_pairs_symm_eq_zero (s : Finset C.Party) (N : C.Party → C.Party → XorDigest)
    (hN : ∀ i j, N i j = N j i) :
    ∑ i ∈ s, ∑ j ∈ univ.filter (fun j => j ∈ s ∧ j ≠ i), N i j = 0 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) (fun p _ => by rw [hN]; exact BitVec.xor_self (x := N p.2 p.1))
    (fun p hp _ => ?_) (fun p hp => ?_) (fun p _ => rfl)
  · simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    intro hswap
    exact hp.2.2.2 (congrArg Sigma.fst hswap)
  · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.2.1, hp.1, Ne.symm hp.2.2⟩

theorem mem_holders_of_mem_L {J : C.Quorum} {i : C.Party} {T : C.Term} (h : T ∈ L J i) : i ∈ C.holders T := by
  simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at h
  have := Finset.mem_of_min h
  simp only [Finset.mem_sdiff] at this
  simpa [Committee.holders] using this.2

/-- The sets `L_i` of a quorum partition the terms, since `J \ T` is never empty. -/
theorem sum_L (J : C.Quorum) (g : C.Term → XorDigest) : ∑ i ∈ J.1, ∑ T ∈ L J i, g T = ∑ T, g T := by
  simp only [L, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hne : (J.1 \ T.1).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.le_card_sdiff T.1 J.1
    have := C.one_le_t
    omega
  rw [← Finset.coe_min' hne]
  simp only [WithTop.coe_eq_coe]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_sdiff.mp (Finset.min'_mem _ hne)).1]

/-- The parts of a quorum combine to `F(x)` for every table of `H`, since each mask appears twice. -/
theorem combine_eq_prfValue (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) (J : C.Quorum) (x : Point) (message : Message) :
    combine J (fun i => simulateQ (tableAnswer prims f) (eval (dealtKeys parameter seeds pairKeys i) i J x message)) =
      simulateQ (tableAnswer prims f) (prfValue seeds x) := by
  suffices h : toXor (combine J _) = toXor (simulateQ (tableAnswer prims f) (prfValue seeds x)) from h
  rw [toXor_combine, toXor_prfValue]
  simp only [toXor_eval, Finset.sum_add_distrib]
  have hseed : ∀ i ∈ J.1, ∑ T ∈ L J i, toXor (truncateHash (f (.prf ((dealtKeys parameter seeds pairKeys i).seed T) x))) =
      ∑ T ∈ L J i, toXor (truncateHash (f (.prf (seeds T) x))) :=
    fun i _ => Finset.sum_congr rfl fun T hT => by simp [dealtKeys, mem_holders_of_mem_L hT]
  rw [Finset.sum_congr rfl hseed, sum_L, sum_pairs_symm_eq_zero, add_zero]
  intro i j
  by_cases hij : i = j
  · rw [hij]
  · simp only [dealtKeys, dif_neg hij, dif_neg (Ne.symm hij), pairOf_comm i j hij]

/-- `H` and `PRG`, as the world answers them. -/
abbrev roAnswer : QueryImpl (RoSpec C) (StateT (HashCache C) ProbComp) :=
  hashAnswer (C := C) prims + prgAnswer (C := C) prims

/-- A table of `H` agrees with a cache. -/
def Agrees (cache : HashCache C) (f : Query C → HashOutput) : Prop := ∀ q v, cache q = some v → f q = v

theorem randomOracle_run {q : Query C} {cache : HashCache C} {z : HashOutput × HashCache C}
    (hz : z ∈ support (((Query C →ₒ HashOutput).randomOracle q).run cache)) :
    cache ≤ z.2 ∧ z.2 q = some z.1 := by
  cases hq : cache q with
  | some u =>
    rw [QueryImpl.withCaching_run_some _ hq, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, hq⟩
  | none =>
    rw [QueryImpl.withCaching_run_none _ hq, support_map] at hz
    obtain ⟨v, _, rfl⟩ := hz
    exact ⟨QueryCache.le_cacheQuery cache hq, QueryCache.cacheQuery_self _ _ _⟩

theorem hashAnswer_run (q : Query C) {cache : HashCache C} {z : HashOutput × HashCache C}
    (hz : z ∈ support ((hashAnswer prims q).run cache)) :
    cache ≤ z.2 ∧ ∀ f, Agrees z.2 f → z.1 = (tableAnswer prims f (.inl q)).run := by
  have hro : hashAnswer prims q = (Query C →ₒ HashOutput).randomOracle q →
      cache ≤ z.2 ∧ ∀ f, Agrees z.2 f → z.1 = f q := fun h => by
    rw [h] at hz
    obtain ⟨hle, hq⟩ := randomOracle_run hz
    exact ⟨hle, fun f hf => (hf q z.1 hq).symm⟩
  cases q
  case hash input =>
    by_cases hmpc : MpcInput input
    · simp only [hashAnswer, if_pos hmpc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨le_rfl, fun f _ => by simp [tableAnswer, hmpc]; rfl⟩
    · obtain ⟨hle, hans⟩ := hro (by simp [hashAnswer, hmpc])
      exact ⟨hle, fun f hf => by rw [hans f hf]; simp [tableAnswer, hmpc]; rfl⟩
  all_goals exact hro rfl

theorem localAnswer_run (t : (RoSpec C).Domain) {cache : HashCache C} {z : (RoSpec C).Range t × HashCache C}
    (hz : z ∈ support ((roAnswer prims t).run cache)) :
    cache ≤ z.2 ∧ ∀ f, Agrees z.2 f → z.1 = (tableAnswer prims f t).run := by
  rcases t with q | x
  · exact hashAnswer_run prims q hz
  · obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Bit × HashCache C, z₀ = z := ⟨z, rfl⟩
    subst hz₀
    change z₀ ∈ support ((hashAnswer prims (.streamKey x.2.1) >>= fun derived =>
      (pure (prims.aes.eval (truncateHash derived) x.2.2) : StateT (HashCache C) ProbComp Bit)).run cache) at hz
    rw [StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨z₁, hz₁, hz⟩ := hz
    rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    obtain ⟨hle, hans⟩ := hashAnswer_run prims _ hz₁
    exact ⟨hle, fun f hf => by rw [hans f hf]; rfl⟩

/-- A run of the lazy oracle only extends the cache, and its output is the evaluation against every
table that agrees with the final cache. -/
theorem simulateQ_run {α : Type} (oa : OracleComp (RoSpec C) α) {cache : HashCache C} {z : α × HashCache C}
    (hz : z ∈ support ((simulateQ (roAnswer prims) oa).run cache)) :
    cache ≤ z.2 ∧ ∀ f, Agrees z.2 f → z.1 = (simulateQ (tableAnswer prims f) oa).run := by
  induction oa using OracleComp.inductionOn generalizing cache z with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, fun _ _ => rfl⟩
  | query_bind t k ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨z₁, hz₁, hz⟩ := hz
    obtain ⟨hle₁, hans⟩ := localAnswer_run prims t hz₁
    obtain ⟨hle, hrest⟩ := ih _ hz
    refine ⟨hle₁.trans hle, fun f hf => ?_⟩
    rw [hrest f hf, hans f fun q v h => hf q v (hle h)]
    simp

/-- The free copy runs the local oracles of the world with no cost. -/
theorem runWorld_free {α : Type} (oa : OracleComp (LocalSpec C) α) :
    Prod.fst <$> runWorld prims (free oa) = (simulateQ (localAnswer prims) oa).run' ∅ := by
  have hmap : ∀ {β ω : Type} (W : StateT (HashCache C) ProbComp (β × ω)),
      Prod.fst <$> W.run' ∅ = (Prod.fst <$> W).run' ∅ := fun W => by
    simp [StateT.run'_eq, StateT.run_map]
  rw [runWorld, world, QueryImpl.withAddCost, free]
  refine (hmap _).trans ?_
  erw [QueryImpl.fst_map_run_withCost (ω := Multiplicative ℕ)]
  rw [← QueryImpl.simulateQ_compose]
  congr 2
  funext t
  exact simulateQ_spec_query _ _

end TprfCorrectnessProof

open TprfCorrectnessProof in
theorem tprfCorrectness (prims : Primitives) (C : Committee) : TprfCorrectnessStatement prims C := by
  intro J x ec r hr
  have h : r.1 ∈ support (Prod.fst <$> runWorld prims (tprfCorrectnessRun J x ec)) := by
    rw [support_map]; exact ⟨r, hr, rfl⟩
  rw [tprfCorrectnessRun, TprfCorrectnessProof.runWorld_free] at h
  simp only [localAnswer, simulateQ_bind, QueryImpl.simulateQ_add_liftComp_left, QueryImpl.simulateQ_add_liftComp_right, StateT.run'_eq,
    StateT.run_bind, unifFwdImpl.simulateQ_run, simulateQ_pure] at h
  simp only [support_map, Set.mem_image, mem_support_bind_iff, bind_map_left, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at h
  obtain ⟨_, ⟨k, hk, z₁, hz₁, z₂, hz₂, rfl⟩, hr⟩ := h
  rw [← hr]
  simp only [prawnsKeyGen, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hk
  obtain ⟨parameter, -, seeds, -, pairKeys, -, rfl⟩ := hk
  obtain ⟨-, hparts⟩ := simulateQ_run prims _ hz₁
  obtain ⟨hle, hvalue⟩ := simulateQ_run prims _ hz₂
  have hf : TprfCorrectnessProof.Agrees z₂.2 fun q => (z₂.2 q).getD 0 := fun q v h => by simp [h]
  rw [hparts _ fun q v h => hf q v (hle h), hvalue _ hf]
  simp only [Id.run, TprfCorrectnessProof.simulateQ_sequenceFin]
  exact decide_eq_true (combine_eq_prfValue prims _ parameter seeds pairKeys J x ec)

namespace TprfSecurityProof

open TprfCorrectnessProof

variable {C : Committee}

/-! ## Basic facts -/

instance : Fintype Point :=
  Fintype.ofEquiv ((Layer × KeyIndex × ChainIndex × Digit) ⊕ (Layer × KeyIndex))
    ⟨fun | .inl (lay, e, l, p) => .chain lay e l p | .inr (lay, e) => .randomizer lay e,
     fun | .chain lay e l p => .inl (lay, e, l, p) | .randomizer lay e => .inr (lay, e),
     fun x => by rcases x with ⟨_, _, _, _⟩ | ⟨_, _⟩ <;> rfl, fun x => by cases x <;> rfl⟩

theorem toXor_xor (a b : Digest) : toXor (a ^^^ b) = toXor a + toXor b := rfl

theorem XorDigest.add_self (a : XorDigest) : a + a = 0 := BitVec.xor_self (x := a)

theorem toXor_foldl_map {α : Type} (f : α → Digest) (a : Digest) (l : List α) :
    toXor (l.foldl (fun acc x => acc ^^^ f x) a) = toXor a + (l.map (toXor ∘ f)).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, toXor_xor, add_assoc]

/-! ## The world without the cost -/

variable (prims : Primitives)

theorem simulateQ_liftComp_local {α : Type} (impl : QueryImpl (LocalSpec C) (StateT (HashCache C) ProbComp))
    (oa : OracleComp (LocalSpec C) α) :
    simulateQ (impl + programAnswer (C := C)) (liftComp oa (SimulatorSpec C)) = simulateQ impl oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [liftComp_bind, simulateQ_bind, simulateQ_bind]
    simp only [ih]
    congr 1
    rw [liftComp_query]
    rcases t with t | t | t <;>
    exact ((simulateQ_query _ _).trans (id_map _)).trans ((simulateQ_query _ _).trans (id_map _)).symm

theorem simulateQ_adversary {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ (worldAnswer prims) (worldRoles.adversary oa) = simulateQ (localAnswer prims) oa := by
  simp only [worldAnswer, worldRoles, simulateQ_counted]
  exact simulateQ_liftComp_local _ oa

/-! ## The game with the world -/

/-- The state of `tprfGame` after `Eval` of operator `i` at `(x, ec)`. -/
def addQuery (st : TprfState C) (i : C.Party) (x : Point) (ec : Message) : TprfState C :=
  { st with queried := Function.update st.queried x (Function.update (st.queried x) ec (insert i (st.queried x ec))) }

/-- The state of `tprfGame` after the challenge `x` with the answer `y`. -/
def addChallenge (st : TprfState C) (x : Point) (y : Digest) : TprfState C :=
  { st with challenged := insert x st.challenged, random := Function.update st.random x (some y) }

/-- The initial state of `tprfGame`. -/
def tprfInit : TprfState C := ⟨∅, fun _ _ => ∅, ∅, fun _ => none⟩

/-- `corrupt i` is refused. -/
def CorruptRefused (st : TprfState C) (i : C.Party) : Prop :=
  ∃ x ∈ st.challenged, ∃ ec, C.t ≤ (st.corrupt ∪ st.queried x ec ∪ {i}).card

/-- `eval i J x ec` is refused. -/
def EvalRefused (st : TprfState C) (i : C.Party) (J : C.Quorum) (x : Point) (ec : Message) : Prop :=
  i ∉ J.1 ∨ (C.t ≤ (st.corrupt ∪ st.queried x ec ∪ {i}).card ∧ x ∈ st.challenged)

/-- `challenge x` is refused. -/
def ChallengeRefused (st : TprfState C) (x : Point) : Prop := ∃ ec, C.t ≤ (st.corrupt ∪ st.queried x ec).card

open Classical in
/-- The oracles of `tprfGame` with the world fused in. The adversary queries `adversary D` for the
corrupt operators `D`, an honest `Eval` runs `evalH`, and a challenge runs `prfH` or `sampleH`. -/
def gameImplWith {σ : Type} (adversary : Finset C.Party → QueryImpl (LocalSpec C) (StateT σ ProbComp))
    (evalH : C.Party → C.Quorum → Point → Message → StateT σ ProbComp Digest)
    (prfH : Point → StateT σ ProbComp Digest) (sampleH : StateT σ ProbComp Digest) (b : Bool)
    (keys : C.Party → Keys C) : QueryImpl (LocalSpec C + TprfSpec C) (StateT (TprfState C × σ) ProbComp)
  | .inl t => StateT.mk fun p => (fun z => (z.1, (p.1, z.2))) <$> (adversary p.1.corrupt t).run p.2
  | .inr (.corrupt i) => StateT.mk fun p =>
      if ∃ x ∈ p.1.challenged, ∃ ec, C.t ≤ (p.1.corrupt ∪ p.1.queried x ec ∪ {i}).card then pure (none, p)
      else pure (some (keys i), ({ p.1 with corrupt := insert i p.1.corrupt }, p.2))
  | .inr (.eval i J x ec) => StateT.mk fun p =>
      if i ∉ J.1 ∨ (C.t ≤ (p.1.corrupt ∪ p.1.queried x ec ∪ {i}).card ∧ x ∈ p.1.challenged) then pure (none, p)
      else (fun z => (some z.1, (addQuery p.1 i x ec, z.2))) <$> (evalH i J x ec).run p.2
  | .inr (.challenge x) => StateT.mk fun p =>
      if ∃ ec, C.t ≤ (p.1.corrupt ∪ p.1.queried x ec).card then pure (none, p)
      else (fun z => (some z.1, (addChallenge p.1 x z.1, z.2))) <$>
        (if b then (match p.1.random x with
            | some y => pure y
            | none => sampleH : StateT σ ProbComp Digest).run p.2
          else (prfH x).run p.2)

/-- `gameImplWith` with every query on the local oracles `W`. -/
abbrev gameImpl {σ : Type} (W : QueryImpl (LocalSpec C) (StateT σ ProbComp)) (b : Bool)
    (seeds : C.Term → HashOutput) (keys : C.Party → Keys C) :
    QueryImpl (LocalSpec C + TprfSpec C) (StateT (TprfState C × σ) ProbComp) :=
  gameImplWith (fun _ => W) (fun i J x ec => simulateQ W (liftComp (eval (keys i) i J x ec) _))
    (fun x => simulateQ W (liftComp (prfValue seeds x) _)) (simulateQ W (liftComp ($ᵗ Digest) _)) b keys

/-- The oracles of `tprfGame`. -/
def gameOracles (b : Bool) (seeds : C.Term → HashOutput) (keys : C.Party → Keys C) :
    QueryImpl (LocalSpec C + TprfSpec C) (StateT (TprfState C) (OracleComp (WorldSpec C))) :=
  let forward : QueryImpl (LocalSpec C) (StateT (TprfState C) (OracleComp (WorldSpec C))) :=
    fun t => StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))
  forward + tprfOracles keys seeds b

theorem gameOracles_step (b : Bool) (seeds : C.Term → HashOutput) (keys : C.Party → Keys C)
    (t : (LocalSpec C + TprfSpec C).Domain) (s : TprfState C) (c : HashCache C) :
    (simulateQ (worldAnswer prims) ((gameOracles b seeds keys t).run s)).run c =
      (fun z => ((z.1, z.2.1), z.2.2)) <$> (gameImpl (localAnswer prims) b seeds keys t).run (s, c) := by
  rcases t with t | q
  · change (simulateQ (worldAnswer prims) (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
      fun a => pure (a, s))).run c = _
    rw [simulateQ_bind, simulateQ_adversary, simulateQ_query]
    simp [gameImplWith, Functor.map_map]
  · cases q with
    | corrupt i =>
      change (simulateQ (worldAnswer prims) ((tprfOracles keys seeds b (.corrupt i)).run s)).run c = _
      simp only [tprfOracles, gameImplWith, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_mk]
      split_ifs <;> simp
    | eval i J x ec =>
      change (simulateQ (worldAnswer prims) ((tprfOracles keys seeds b (.eval i J x ec)).run s)).run c = _
      simp only [tprfOracles, gameImplWith, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_mk]
      split_ifs
      · simp
      · rw [worldAnswer]
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_map, StateT.run_lift, simulateQ_map,
          simulateQ_free, Functor.map_map, StateT.run_map, bind_pure_comp]
        rfl
    | challenge x =>
      change (simulateQ (worldAnswer prims) ((tprfOracles keys seeds b (.challenge x)).run s)).run c = _
      rw [worldAnswer]
      cases b
      · simp only [tprfOracles, gameImplWith, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_mk,
          if_false, Bool.false_eq_true]
        split_ifs
        · simp
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_map, StateT.run_lift, simulateQ_map,
            simulateQ_free, Functor.map_map, StateT.run_map, bind_pure_comp,
            map_pure]
          rfl
      · simp only [tprfOracles, gameImplWith, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_mk, if_true]
        split_ifs
        · simp
        · cases s.random x
          · simp only [StateT.run_bind, StateT.run_set, StateT.run_map, StateT.run_lift, simulateQ_map,
              simulateQ_free, Functor.map_map, StateT.run_map, bind_pure_comp,
              map_pure]
            rfl
          · simp [addChallenge]

/-- A fused run of `tprfGame`. -/
theorem simulateQ_fused {S σ α : Type} {ι : Type} {spec : OracleSpec ι}
    (W : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (I : QueryImpl spec (StateT S (OracleComp (WorldSpec C)))) (G : QueryImpl spec (StateT (S × σ) ProbComp))
    (h : ∀ t s c, (simulateQ W ((I t).run s)).run c = (fun z => ((z.1, z.2.1), z.2.2)) <$> (G t).run (s, c))
    (oa : OracleComp spec α) (s : S) (c : σ) :
    (simulateQ W ((simulateQ I oa).run s)).run c =
      (fun z => ((z.1, z.2.1), z.2.2)) <$> (simulateQ G oa).run (s, c) := by
  induction oa using OracleComp.inductionOn generalizing s c with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, h, bind_map_left, map_bind]
    exact bind_congr fun z => ih _ _ _

/-- A run of an implementation through a map of its state. -/
theorem simulateQ_run_map {σ₁ σ₂ α : Type} {ι : Type} {spec : OracleSpec ι} (φ : σ₁ → σ₂)
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (h : ∀ t s, (impl₂ t).run (φ s) = Prod.map id φ <$> (impl₁ t).run s) (oa : OracleComp spec α) (s : σ₁) :
    (simulateQ impl₂ oa).run (φ s) = Prod.map id φ <$> (simulateQ impl₁ oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, h, bind_map_left, map_bind]
    exact bind_congr fun z => ih _ _

theorem runWorld_tprfGame (A : TprfAdversary C) (b : Bool) :
    (simulateQ (worldAnswer prims) (tprfGame A b)).run' ∅ = (do
      let parameter ← $ᵗ PublicParameter
      let seeds ← $ᵗ (C.Term → HashOutput)
      let pairKeys ← $ᵗ (C.Pair → HashOutput)
      (simulateQ (gameImpl (localAnswer prims) b seeds (dealtKeys parameter seeds pairKeys)) A).run'
        (tprfInit, ∅)) := by
  rw [tprfGame, simulateQ_bind, StateT.run'_eq, StateT.run_bind, worldAnswer, simulateQ_free, localAnswer,
    QueryImpl.simulateQ_add_liftComp_left, unifFwdImpl.simulateQ_run, bind_map_left]
  simp only [prawnsKeyGen, bind_assoc, pure_bind, map_bind]
  refine bind_congr fun parameter => bind_congr fun seeds => bind_congr fun pairKeys => ?_
  have h := simulateQ_fused (worldAnswer prims) (gameOracles b seeds (dealtKeys parameter seeds pairKeys))
    (gameImpl (localAnswer prims) b seeds (dealtKeys parameter seeds pairKeys))
    (gameOracles_step prims b seeds _) A tprfInit ∅
  simp only [StateT.run'_eq, StateT.run_map, simulateQ_map]
  refine (congrArg (fun m => (fun x => x.1) <$> (fun p => (p.1.1, p.2)) <$> m) h).trans ?_
  simp only [Functor.map_map]
  rfl

/-! ## Slots -/

/-- A key of `prawnsKeyGen`, the seed of a term or the key of a pair. -/
abbrev KeySlot (C : Committee) := C.Term ⊕ C.Pair

/-- A hidden value of `H`, the PRF value of a term at a point or a mask. -/
abbrev Slot (C : Committee) := (C.Term × Point) ⊕ (C.Pair × Point × Message × C.Quorum)

instance : DecidableEq (Slot C) := Classical.decEq _

/-- The key of a slot. -/
def slotKey : Slot C → KeySlot C
  | .inl (T, _) => .inl T
  | .inr (p, _) => .inr p

/-- The input of `H` of a slot. -/
def slotInput (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput) : Slot C → Query C
  | .inl (T, x) => .prf (seeds T) x
  | .inr (p, x, m, J) => .mask (pairKeys p) x m J

/-- The cache of the slots. -/
abbrev SlotCache (C : Committee) := (Slot C →ₒ HashOutput).QueryCache

/-- A key that the corrupt operators `D` hold. -/
def Revealed (D : Finset C.Party) : KeySlot C → Prop
  | .inl T => ∃ i ∈ D, i ∈ C.holders T
  | .inr p => p.1.1 ∈ D ∨ p.1.2 ∈ D

/-- A step on the cache of `H`. -/
def onCache {α : Type} (m : StateT (HashCache C) ProbComp α) : StateT (HashCache C × SlotCache C) ProbComp α :=
  StateT.mk fun p => (fun z => (z.1, (z.2, p.2))) <$> m.run p.1

/-- A step on the cache of the slots. -/
def onTable {α : Type} (m : StateT (SlotCache C) ProbComp α) : StateT (HashCache C × SlotCache C) ProbComp α :=
  StateT.mk fun p => (fun z => (z.1, (p.1, z.2))) <$> m.run p.2

/-- The lazy random oracle at a slot. -/
abbrev slotOracle (s : Slot C) : StateT (SlotCache C) ProbComp HashOutput := (Slot C →ₒ HashOutput).randomOracle s

variable (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)

open Classical in
/-- The local oracles with the slots in their own cache. -/
def routedAnswer : QueryImpl (LocalSpec C) (StateT (HashCache C × SlotCache C) ProbComp)
  | .inr (.inl u) => if h : ∃ s, slotInput seeds pairKeys s = u then onTable (slotOracle h.choose)
      else onCache (hashAnswer prims u)
  | t => onCache (localAnswer prims t)

open Classical in
/-- The cache of `H` as the cache off the slots and the cache of the slots. -/
def splitCache (g : HashCache C) : HashCache C × SlotCache C :=
  (fun u => if ∃ s, slotInput seeds pairKeys s = u then none else g u, fun s => g (slotInput seeds pairKeys s))

open Classical in
/-- The adversary of the symbolic game. It reads the slots of the revealed keys, and every other input
in the cache of `H`. -/
def symAdversary (D : Finset C.Party) : QueryImpl (LocalSpec C) (StateT (HashCache C × SlotCache C) ProbComp)
  | .inr (.inl u) => if h : ∃ s, Revealed D (slotKey s) ∧ slotInput seeds pairKeys s = u then
        onTable (slotOracle h.choose)
      else onCache (hashAnswer prims u)
  | t => onCache (localAnswer prims t)

/-- `Eval` on the slots. -/
def evalSlots (i : C.Party) (J : C.Quorum) (x : Point) (ec : Message) :
    StateT (HashCache C × SlotCache C) ProbComp Digest := onTable (do
  let terms ← (C.terms.filter (· ∈ L J i)).mapM fun T => truncateHash <$> slotOracle (.inl (T, x))
  let masks ← (C.parties.filter fun j => j ∈ J.1 ∧ j ≠ i).mapM fun j =>
    if h : j = i then pure 0 else truncateHash <$> slotOracle (.inr (C.pairOf i j (Ne.symm h), x, ec, J))
  pure ((terms ++ masks).foldl (· ^^^ ·) 0))

/-- `F(x)` on the slots. -/
def prfSlots (x : Point) : StateT (HashCache C × SlotCache C) ProbComp Digest := onTable (do
  let terms ← C.terms.mapM fun T => truncateHash <$> slotOracle (.inl (T, x))
  pure (terms.foldl (· ^^^ ·) 0))

/-- The state of the hop, namely the game state, the two caches, and the keys that the adversary hit. -/
abbrev SymState (C : Committee) := (TprfState C × HashCache C × SlotCache C) × Finset (KeySlot C)

open Classical in
/-- The keys that a query of the adversary hits while they are not revealed. -/
def firedBy (D : Finset C.Party) : (LocalSpec C + TprfSpec C).Domain → Finset (KeySlot C)
  | .inl (.inr (.inl u)) => Finset.univ.filter fun σ =>
      ¬Revealed D σ ∧ ∃ s, slotKey s = σ ∧ slotInput seeds pairKeys s = u
  | _ => ∅

/-- A query of the adversary hits a key that is not revealed. -/
def hitFlag (D : Finset C.Party) (t : (LocalSpec C + TprfSpec C).Domain) : Bool :=
  decide (firedBy seeds pairKeys D t).Nonempty

/-- An implementation that records the hit keys and sets the flag at a hit. -/
def withFired (I : QueryImpl (LocalSpec C + TprfSpec C) (StateT (TprfState C × HashCache C × SlotCache C) ProbComp)) :
    QueryImpl (LocalSpec C + TprfSpec C) (StateT (SymState C × Bool) ProbComp) := fun t =>
  StateT.mk fun p => (fun z => (z.1, ((z.2, p.1.2 ∪ firedBy seeds pairKeys p.1.1.1.corrupt t),
    p.2 || hitFlag seeds pairKeys p.1.1.1.corrupt t))) <$> (I t).run p.1.1

/-- The real game on split caches. -/
def realImpl (b : Bool) (parameter : PublicParameter) :
    QueryImpl (LocalSpec C + TprfSpec C) (StateT (SymState C × Bool) ProbComp) :=
  withFired seeds pairKeys (gameImpl (routedAnswer prims seeds pairKeys) b seeds (dealtKeys parameter seeds pairKeys))

/-- The symbolic game. The honest operators use the slots, and the adversary reads the slots of the
revealed keys only. -/
def symImpl (b : Bool) (parameter : PublicParameter) :
    QueryImpl (LocalSpec C + TprfSpec C) (StateT (SymState C × Bool) ProbComp) :=
  withFired seeds pairKeys (gameImplWith (symAdversary prims seeds pairKeys) evalSlots prfSlots
    (simulateQ (routedAnswer prims seeds pairKeys) (liftComp ($ᵗ Digest) _)) b (dealtKeys parameter seeds pairKeys))

/-! ## The real game on split caches -/

/-- `m₂` runs as `m₁` through the map `φ` of the state. -/
def StateMap {σ₁ σ₂ α : Type} (φ : σ₁ → σ₂) (m₁ : StateT σ₁ ProbComp α) (m₂ : StateT σ₂ ProbComp α) : Prop :=
  ∀ s, m₂.run (φ s) = Prod.map id φ <$> m₁.run s

theorem StateMap.pure {σ₁ σ₂ α : Type} (φ : σ₁ → σ₂) (a : α) :
    StateMap φ (pure a : StateT σ₁ ProbComp α) (pure a) := fun s => by simp

theorem StateMap.bind {σ₁ σ₂ α β : Type} {φ : σ₁ → σ₂} {m₁ : StateT σ₁ ProbComp α} {m₂ : StateT σ₂ ProbComp α}
    {f₁ : α → StateT σ₁ ProbComp β} {f₂ : α → StateT σ₂ ProbComp β} (h : StateMap φ m₁ m₂)
    (hf : ∀ a, StateMap φ (f₁ a) (f₂ a)) : StateMap φ (m₁ >>= f₁) (m₂ >>= f₂) := fun s => by
  simp only [StateT.run_bind, h s, bind_map_left, map_bind, Prod.map_fst, id, Prod.map_snd]
  exact bind_congr fun z => hf z.1 z.2

theorem StateMap.map {σ₁ σ₂ α β : Type} {φ : σ₁ → σ₂} {m₁ : StateT σ₁ ProbComp α} {m₂ : StateT σ₂ ProbComp α}
    (f : α → β) (h : StateMap φ m₁ m₂) : StateMap φ (f <$> m₁) (f <$> m₂) := by
  simp only [map_eq_bind_pure_comp]
  exact h.bind fun a => StateMap.pure φ _

theorem StateMap.simulateQ {σ₁ σ₂ α : Type} {ι : Type} {spec : OracleSpec ι} {φ : σ₁ → σ₂}
    {impl₁ : QueryImpl spec (StateT σ₁ ProbComp)} {impl₂ : QueryImpl spec (StateT σ₂ ProbComp)}
    (h : ∀ t, StateMap φ (impl₁ t) (impl₂ t)) (oa : OracleComp spec α) :
    StateMap φ (simulateQ impl₁ oa) (simulateQ impl₂ oa) := fun s => simulateQ_run_map φ impl₁ impl₂ (fun t => h t) oa s

theorem onCache_run {α : Type} (m : StateT (HashCache C) ProbComp α) (c : HashCache C) (τ : SlotCache C) :
    (onCache m).run (c, τ) = (fun z => (z.1, (z.2, τ))) <$> m.run c := rfl

theorem onTable_run {α : Type} (m : StateT (SlotCache C) ProbComp α) (c : HashCache C) (τ : SlotCache C) :
    (onTable m).run (c, τ) = (fun z => (z.1, (c, z.2))) <$> m.run τ := rfl

theorem onCache_pure {α : Type} (a : α) : onCache (pure a : StateT (HashCache C) ProbComp α) = pure a := by
  ext p
  simp [onCache]

theorem onCache_bind {α β : Type} (m : StateT (HashCache C) ProbComp α) (f : α → StateT (HashCache C) ProbComp β) :
    onCache (m >>= f) = onCache m >>= fun a => onCache (f a) := by
  ext p
  simp [onCache, StateT.run_bind, map_bind, bind_map_left]

theorem onTable_bind {α β : Type} (m : StateT (SlotCache C) ProbComp α) (f : α → StateT (SlotCache C) ProbComp β) :
    onTable (m >>= f) = onTable m >>= fun a => onTable (f a) := by
  ext p
  simp [onTable, StateT.run_bind, map_bind, bind_map_left]

theorem hashAnswer_eq_randomOracle {u : Query C} (hu : ∀ input, u = .hash input → ¬MpcInput input) :
    hashAnswer prims u = (Query C →ₒ HashOutput).randomOracle u := by
  cases u with
  | hash input => simp only [hashAnswer, if_neg (hu input rfl)]
  | _ => rfl

theorem slotInput_ne_hash (s : Slot C) (input : HashInput) : slotInput seeds pairKeys s ≠ .hash input := by
  rcases s with ⟨T, x⟩ | ⟨p, x, m, J⟩ <;> simp [slotInput]

theorem splitCache_fst_of_not_slot {u : Query C} (hu : ∀ s, slotInput seeds pairKeys s ≠ u) (g : HashCache C) :
    (splitCache seeds pairKeys g).1 u = g u := by
  simp only [splitCache]
  rw [if_neg (fun ⟨s, h⟩ => hu s h)]

theorem splitCache_cacheQuery_of_not_slot {u : Query C} (hu : ∀ s, slotInput seeds pairKeys s ≠ u) (g : HashCache C)
    (v : HashOutput) : splitCache seeds pairKeys (g.cacheQuery u v) =
      ((splitCache seeds pairKeys g).1.cacheQuery u v, (splitCache seeds pairKeys g).2) := by
  refine Prod.ext (funext fun w => ?_) (funext fun s => ?_)
  · simp only [splitCache]
    by_cases hw : w = u
    · subst hw
      rw [if_neg (fun ⟨s, h⟩ => hu s h), QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ hw, QueryCache.cacheQuery_of_ne _ _ hw]
  · simp only [splitCache]
    rw [QueryCache.cacheQuery_of_ne _ _ (hu s)]

theorem splitCache_cacheQuery_slot (hinj : Function.Injective (slotInput seeds pairKeys)) (s₀ : Slot C)
    (g : HashCache C) (v : HashOutput) : splitCache seeds pairKeys (g.cacheQuery (slotInput seeds pairKeys s₀) v) =
      ((splitCache seeds pairKeys g).1, (splitCache seeds pairKeys g).2.cacheQuery s₀ v) := by
  refine Prod.ext (funext fun w => ?_) (funext fun s => ?_)
  · simp only [splitCache]
    by_cases h : ∃ s, slotInput seeds pairKeys s = w
    · rw [if_pos h, if_pos h]
    · have hw : w ≠ slotInput seeds pairKeys s₀ := fun hw => h ⟨s₀, hw.symm⟩
      rw [if_neg h, if_neg h, QueryCache.cacheQuery_of_ne _ _ hw]
  · by_cases hs : s = s₀
    · subst hs; simp [splitCache]
    · simp [splitCache, QueryCache.cacheQuery_of_ne _ _ hs,
        QueryCache.cacheQuery_of_ne _ _ (fun h => hs (hinj h))]

theorem stateMap_hash_of_not_slot {u : Query C} (hu : ∀ s, slotInput seeds pairKeys s ≠ u) :
    StateMap (splitCache seeds pairKeys) (hashAnswer prims u) (onCache (hashAnswer prims u)) := by
  intro g
  rw [show splitCache seeds pairKeys g = ((splitCache seeds pairKeys g).1, (splitCache seeds pairKeys g).2) from rfl,
    onCache_run]
  by_cases hm : ∃ input, u = .hash input ∧ MpcInput input
  · obtain ⟨input, rfl, hmpc⟩ := hm
    simp [hashAnswer, hmpc]
  · have hu' : ∀ input, u = .hash input → ¬MpcInput input := fun input h hmpc => hm ⟨input, h, hmpc⟩
    rw [hashAnswer_eq_randomOracle prims hu']
    have hc := splitCache_fst_of_not_slot seeds pairKeys hu g
    cases hg : g u with
    | some v =>
      simp only [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hg,
        QueryImpl.withCaching_run_some _ (hc.trans hg), map_pure, Prod.map_apply, id, Prod.mk.eta]
    | none =>
      simp only [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hg,
        QueryImpl.withCaching_run_none _ (hc.trans hg), Functor.map_map, Prod.map_apply, id,
        splitCache_cacheQuery_of_not_slot seeds pairKeys hu]

theorem stateMap_hash_slot (hinj : Function.Injective (slotInput seeds pairKeys)) (s₀ : Slot C) :
    StateMap (splitCache seeds pairKeys) (hashAnswer prims (slotInput seeds pairKeys s₀))
      (onTable (slotOracle s₀)) := by
  intro g
  rw [show splitCache seeds pairKeys g = ((splitCache seeds pairKeys g).1, (splitCache seeds pairKeys g).2) from rfl,
    onTable_run, hashAnswer_eq_randomOracle prims fun input h => absurd h (slotInput_ne_hash seeds pairKeys s₀ input)]
  have he : (splitCache seeds pairKeys g).2 s₀ = g (slotInput seeds pairKeys s₀) := rfl
  cases hg : g (slotInput seeds pairKeys s₀) with
  | some v =>
    simp only [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hg,
      QueryImpl.withCaching_run_some _ (he.trans hg), map_pure, Prod.map_apply, id, Prod.mk.eta]
  | none =>
    simp only [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hg,
      QueryImpl.withCaching_run_none _ (he.trans hg), Functor.map_map, Prod.map_apply, id,
      splitCache_cacheQuery_slot seeds pairKeys hinj]
    rfl

theorem localAnswer_unif_run (n : ℕ) (c : HashCache C) :
    (localAnswer prims (.inl n)).run c = (fun x => (x, c)) <$> (liftM (unifSpec.query n) : ProbComp ((LocalSpec C).Range (.inl n))) := by
  simp [localAnswer, unifFwdImpl]

theorem stateMap_routedAnswer (hinj : Function.Injective (slotInput seeds pairKeys)) (t : (LocalSpec C).Domain) :
    StateMap (splitCache seeds pairKeys) (localAnswer prims t) (routedAnswer prims seeds pairKeys t) := by
  rcases t with n | u | x
  · intro g
    rw [show splitCache seeds pairKeys g = ((splitCache seeds pairKeys g).1, (splitCache seeds pairKeys g).2) from rfl]
    simp only [routedAnswer, onCache_run, localAnswer_unif_run]
    rw [Functor.map_map, Functor.map_map]
    simp only [Prod.map_apply, id, Prod.mk.eta]
  · by_cases h : ∃ s, slotInput seeds pairKeys s = u
    · obtain ⟨s₀, rfl⟩ := h
      have hc : (⟨s₀, rfl⟩ : ∃ s, slotInput seeds pairKeys s = slotInput seeds pairKeys s₀).choose = s₀ :=
        hinj (Exists.choose_spec (⟨s₀, rfl⟩ : ∃ s, slotInput seeds pairKeys s = slotInput seeds pairKeys s₀))
      have e : routedAnswer prims seeds pairKeys (.inr (.inl (slotInput seeds pairKeys s₀))) =
          onTable (slotOracle s₀) := by
        simp only [routedAnswer, dif_pos (⟨s₀, rfl⟩ : ∃ s, slotInput seeds pairKeys s = slotInput seeds pairKeys s₀), hc]
        rfl
      rw [e]
      exact stateMap_hash_slot prims seeds pairKeys hinj s₀
    · have e : routedAnswer prims seeds pairKeys (.inr (.inl u)) = onCache (hashAnswer prims u) := by
        simp only [routedAnswer, dif_neg h]
        rfl
      rw [e]
      exact stateMap_hash_of_not_slot prims seeds pairKeys fun s hs => h ⟨s, hs⟩
  · change StateMap _ (prgAnswer prims x) (onCache (prgAnswer prims x))
    simp only [prgAnswer, onCache_bind]
    refine (stateMap_hash_of_not_slot prims seeds pairKeys fun s hs => ?_).bind fun d => ?_
    · rcases s with ⟨T, y⟩ | ⟨p, y, m, J⟩ <;> simp [slotInput] at hs
    · rw [onCache_pure]
      exact StateMap.pure _ _

theorem stateMap_gameImpl {σ₁ σ₂ : Type} (φ : σ₁ → σ₂) (W₁ : QueryImpl (LocalSpec C) (StateT σ₁ ProbComp))
    (W₂ : QueryImpl (LocalSpec C) (StateT σ₂ ProbComp)) (h : ∀ t, StateMap φ (W₁ t) (W₂ t)) (b : Bool)
    (keys : C.Party → Keys C) (t : (LocalSpec C + TprfSpec C).Domain) :
    StateMap (Prod.map id φ) (gameImpl W₁ b seeds keys t) (gameImpl W₂ b seeds keys t) := by
  rintro ⟨st, c⟩
  have hs := fun {α : Type} (oa : OracleComp (LocalSpec C) α) => StateMap.simulateQ h oa c
  rcases t with t | (i | ⟨i, J, x, ec⟩ | x)
  · simp only [gameImplWith, StateT.run_mk, Prod.map_apply, id, h t c, Functor.map_map]
    rfl
  · simp only [gameImplWith, StateT.run_mk, Prod.map_apply, id]
    split_ifs <;> simp
  · simp only [gameImplWith, StateT.run_mk, Prod.map_apply, id]
    split_ifs
    · simp
    · simp only [hs, Functor.map_map]
      rfl
  · cases b
    · simp only [gameImplWith, StateT.run_mk, Prod.map_apply, id, if_false, Bool.false_eq_true]
      split_ifs
      · simp
      · simp only [hs, Functor.map_map]
        rfl
    · simp only [gameImplWith, StateT.run_mk, Prod.map_apply, id, if_true]
      split_ifs
      · simp
      · cases st.random x
        · simp only [hs, Functor.map_map]
          rfl
        · simp

/-- The oracles `H` and `PRG` of local oracles. -/
def roPart {σ : Type} (W : QueryImpl (LocalSpec C) (StateT σ ProbComp)) : QueryImpl (RoSpec C) (StateT σ ProbComp) :=
  fun q => W (.inr q)

theorem simulateQ_liftComp_ro {σ α : Type} (W : QueryImpl (LocalSpec C) (StateT σ ProbComp))
    (oa : OracleComp (RoSpec C) α) :
    simulateQ W (liftComp oa (LocalSpec C)) = simulateQ (roPart W) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rw [liftComp_pure, simulateQ_pure, simulateQ_pure]
  | query_bind t k ih =>
    rw [liftComp_bind, simulateQ_bind, simulateQ_bind]
    simp only [ih]
    congr 1

theorem routedAnswer_slot (hinj : Function.Injective (slotInput seeds pairKeys)) (s₀ : Slot C) :
    routedAnswer prims seeds pairKeys (.inr (.inl (slotInput seeds pairKeys s₀))) = onTable (slotOracle s₀) := by
  have hc : (⟨s₀, rfl⟩ : ∃ s, slotInput seeds pairKeys s = slotInput seeds pairKeys s₀).choose = s₀ :=
    hinj (Exists.choose_spec (⟨s₀, rfl⟩ : ∃ s, slotInput seeds pairKeys s = slotInput seeds pairKeys s₀))
  simp only [routedAnswer, dif_pos (⟨s₀, rfl⟩ : ∃ s, slotInput seeds pairKeys s = slotInput seeds pairKeys s₀), hc]
  rfl

theorem onTable_map {α β : Type} (f : α → β) (m : StateT (SlotCache C) ProbComp α) :
    onTable (f <$> m) = f <$> onTable m := by
  ext p
  simp [onTable, Functor.map_map]

theorem onTable_pure {α : Type} (a : α) : onTable (pure a : StateT (SlotCache C) ProbComp α) = pure a := by
  ext p
  simp [onTable]

theorem onTable_mapM {α β : Type} (f : α → StateT (SlotCache C) ProbComp β) (l : List α) :
    onTable (l.mapM f) = l.mapM fun a => onTable (f a) := by
  induction l with
  | nil => simp [onTable_pure]
  | cons a l ih => simp [List.mapM_cons, onTable_bind, onTable_map, ih]

theorem mapM_congr_mem {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} {f g : α → m β} {l : List α}
    (h : ∀ a ∈ l, f a = g a) : l.mapM f = l.mapM g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.mapM_cons, List.mapM_cons, h a (List.mem_cons_self ..), ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem routed_hashQuery (hinj : Function.Injective (slotInput seeds pairKeys)) (s₀ : Slot C) :
    simulateQ (roPart (routedAnswer prims seeds pairKeys)) (hashQuery (slotInput seeds pairKeys s₀)) =
      onTable (slotOracle s₀) :=
  ((simulateQ_query _ _).trans (id_map _)).trans (routedAnswer_slot prims seeds pairKeys hinj s₀)

theorem routed_eval (hinj : Function.Injective (slotInput seeds pairKeys)) (parameter : PublicParameter)
    (i : C.Party) (J : C.Quorum) (x : Point) (ec : Message) :
    simulateQ (routedAnswer prims seeds pairKeys)
      (liftComp (eval (dealtKeys parameter seeds pairKeys i) i J x ec) (LocalSpec C)) = evalSlots i J x ec := by
  rw [simulateQ_liftComp_ro]
  have hterms : ∀ T ∈ C.terms.filter (· ∈ L J i),
      simulateQ (roPart (routedAnswer prims seeds pairKeys))
        (prf ((dealtKeys parameter seeds pairKeys i).seed T) x) =
      truncateHash <$> onTable (slotOracle (.inl (T, x))) := fun T hT => by
    rw [List.mem_filter] at hT
    simp only [prf, simulateQ_map, dealtKeys, if_pos (mem_holders_of_mem_L (of_decide_eq_true hT.2))]
    exact congrArg _ (routed_hashQuery prims seeds pairKeys hinj (.inl (T, x)))
  have hmasks : ∀ j ∈ C.parties.filter (fun j => j ∈ J.1 ∧ j ≠ i),
      simulateQ (roPart (routedAnswer prims seeds pairKeys))
        (truncateHash <$> hashQuery (.mask ((dealtKeys parameter seeds pairKeys i).pairKey j) x ec J)) =
      onTable (if h : j = i then pure 0 else truncateHash <$> slotOracle (.inr (C.pairOf i j (Ne.symm h), x, ec, J))) :=
    fun j hj => by
    rw [List.mem_filter] at hj
    have hji : j ≠ i := (of_decide_eq_true hj.2).2
    rw [dif_neg hji, onTable_map, simulateQ_map]
    simp only [dealtKeys, dif_neg hji]
    exact congrArg _ (routed_hashQuery prims seeds pairKeys hinj (.inr (C.pairOf i j (Ne.symm hji), x, ec, J)))
  simp only [eval, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure, evalSlots, onTable_bind, onTable_mapM,
    onTable_pure]
  rw [mapM_congr_mem hterms, mapM_congr_mem hmasks]
  simp only [onTable_map]

theorem routed_prfValue (hinj : Function.Injective (slotInput seeds pairKeys)) (x : Point) :
    simulateQ (routedAnswer prims seeds pairKeys) (liftComp (prfValue seeds x) (LocalSpec C)) = prfSlots x := by
  rw [simulateQ_liftComp_ro]
  have hterms : ∀ T ∈ C.terms, simulateQ (roPart (routedAnswer prims seeds pairKeys)) (prf (seeds T) x) =
      truncateHash <$> onTable (slotOracle (.inl (T, x))) := fun T _ => by
    simp only [prf, simulateQ_map]
    exact congrArg _ (routed_hashQuery prims seeds pairKeys hinj (.inl (T, x)))
  simp only [prfValue, simulateQ_bind, simulateQ_list_mapM, simulateQ_pure, prfSlots, onTable_bind, onTable_mapM,
    onTable_pure]
  rw [mapM_congr_mem hterms]
  simp only [onTable_map]

theorem withFired_forget (I : QueryImpl (LocalSpec C + TprfSpec C) (StateT (TprfState C × HashCache C × SlotCache C) ProbComp))
    {α : Type} (oa : OracleComp (LocalSpec C + TprfSpec C) α) (x : TprfState C × HashCache C × SlotCache C)
    (F : Finset (KeySlot C)) (f : Bool) :
    (fun z => (z.1, z.2.1.1)) <$> (simulateQ (withFired seeds pairKeys I) oa).run ((x, F), f) =
      (simulateQ I oa).run x := by
  induction oa using OracleComp.inductionOn generalizing x F f with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, withFired, StateT.run_mk, bind_map_left, map_bind]
    exact bind_congr fun z => ih _ _ _ _

theorem splitCache_empty : splitCache seeds pairKeys (∅ : HashCache C) = (∅, ∅) := by
  refine Prod.ext (funext fun u => ?_) (funext fun s => rfl)
  simp only [splitCache]
  split_ifs <;> rfl

/-- The initial state of the hop. -/
def symInit : SymState C × Bool := (((tprfInit, ∅, ∅), ∅), false)

theorem game_eq_real (hinj : Function.Injective (slotInput seeds pairKeys)) (b : Bool) (parameter : PublicParameter)
    (A : TprfAdversary C) :
    Prod.fst <$> (simulateQ (gameImpl (localAnswer prims) b seeds (dealtKeys parameter seeds pairKeys)) A).run (tprfInit, ∅) =
      Prod.fst <$> (simulateQ (realImpl prims seeds pairKeys b parameter) A).run symInit := by
  have h1 := withFired_forget seeds pairKeys
    (gameImpl (routedAnswer prims seeds pairKeys) b seeds (dealtKeys parameter seeds pairKeys)) A (tprfInit, ∅, ∅) ∅ false
  have h2 := simulateQ_run_map (Prod.map id (splitCache seeds pairKeys))
    (gameImpl (localAnswer prims) b seeds (dealtKeys parameter seeds pairKeys))
    (gameImpl (routedAnswer prims seeds pairKeys) b seeds (dealtKeys parameter seeds pairKeys))
    (fun t => stateMap_gameImpl seeds _ _ _ (stateMap_routedAnswer prims seeds pairKeys hinj) b _ t) A (tprfInit, ∅)
  simp only [Prod.map_apply, id, splitCache_empty] at h2
  have h3 := congrArg (Prod.fst <$> ·) h1
  simp only [Functor.map_map] at h3
  rw [realImpl, symInit]
  refine Eq.trans ?_ h3.symm
  rw [h2, Functor.map_map]
  rfl

theorem symAdversary_eq_routed (hinj : Function.Injective (slotInput seeds pairKeys)) (D : Finset C.Party)
    (t : (LocalSpec C).Domain) (hF : firedBy seeds pairKeys D (.inl t) = ∅) :
    symAdversary prims seeds pairKeys D t = routedAnswer prims seeds pairKeys t := by
  rcases t with n | u | y
  · rfl
  · by_cases h : ∃ s, slotInput seeds pairKeys s = u
    · obtain ⟨s₀, rfl⟩ := h
      have hrev : Revealed D (slotKey s₀) := by
        by_contra hr
        have : slotKey s₀ ∈ firedBy seeds pairKeys D (.inl (.inr (.inl (slotInput seeds pairKeys s₀)))) := by
          simp only [firedBy, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hr, s₀, rfl, rfl⟩
        rw [hF] at this
        exact Finset.notMem_empty _ this
      have hex : ∃ s, Revealed D (slotKey s) ∧ slotInput seeds pairKeys s = slotInput seeds pairKeys s₀ :=
        ⟨s₀, hrev, rfl⟩
      have hc : hex.choose = s₀ := hinj hex.choose_spec.2
      rw [routedAnswer_slot prims seeds pairKeys hinj]
      simp only [symAdversary, dif_pos hex, hc]
      rfl
    · have h' : ¬∃ s, Revealed D (slotKey s) ∧ slotInput seeds pairKeys s = u := fun ⟨s, _, hs⟩ => h ⟨s, hs⟩
      simp only [symAdversary, routedAnswer, dif_neg h, dif_neg h']
  · rfl

/-- The core of `realImpl`. -/
abbrev realCore (b : Bool) (parameter : PublicParameter) :=
  gameImpl (routedAnswer prims seeds pairKeys) b seeds (dealtKeys parameter seeds pairKeys)

/-- The core of `symImpl`. -/
abbrev symCore (b : Bool) (parameter : PublicParameter) :=
  gameImplWith (symAdversary prims seeds pairKeys) evalSlots prfSlots
    (simulateQ (routedAnswer prims seeds pairKeys) (liftComp ($ᵗ Digest) _)) b (dealtKeys parameter seeds pairKeys)

theorem realCore_eq_symCore (hinj : Function.Injective (slotInput seeds pairKeys)) (b : Bool)
    (parameter : PublicParameter) (t : (LocalSpec C + TprfSpec C).Domain) (x : TprfState C × HashCache C × SlotCache C)
    (hF : firedBy seeds pairKeys x.1.corrupt t = ∅) :
    (realCore prims seeds pairKeys b parameter t).run x = (symCore prims seeds pairKeys b parameter t).run x := by
  rcases t with t | (i | ⟨i, J, y, ec⟩ | y)
  · simp only [gameImplWith, StateT.run_mk, symAdversary_eq_routed prims seeds pairKeys hinj _ t hF]
  · simp only [gameImplWith, StateT.run_mk]
  · simp only [gameImplWith, StateT.run_mk, routed_eval prims seeds pairKeys hinj]
  · cases b
    · simp only [gameImplWith, StateT.run_mk, routed_prfValue prims seeds pairKeys hinj]
    · simp only [gameImplWith, StateT.run_mk, if_true]

theorem withFired_mono (I : QueryImpl (LocalSpec C + TprfSpec C) (StateT (TprfState C × HashCache C × SlotCache C) ProbComp))
    (t : (LocalSpec C + TprfSpec C).Domain) (p : SymState C × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((withFired seeds pairKeys I t).run p), z.2.2 = true := by
  intro z hz
  simp only [withFired, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨w, -, rfl⟩ := hz
  simp [hp]

theorem real_sym_agree (hinj : Function.Injective (slotInput seeds pairKeys)) (b : Bool) (parameter : PublicParameter)
    (t : (LocalSpec C + TprfSpec C).Domain) (s : SymState C) (u : (LocalSpec C + TprfSpec C).Range t)
    (s' : SymState C) :
    Pr[= (u, (s', false)) | (symImpl prims seeds pairKeys b parameter t).run (s, false)] =
      Pr[= (u, (s', false)) | (realImpl prims seeds pairKeys b parameter t).run (s, false)] := by
  by_cases hF : firedBy seeds pairKeys s.1.1.corrupt t = ∅
  · simp only [symImpl, realImpl, withFired, StateT.run_mk]
    rw [← realCore_eq_symCore prims seeds pairKeys hinj b parameter t s.1 hF]
  · have hz : ∀ I : QueryImpl (LocalSpec C + TprfSpec C) (StateT (TprfState C × HashCache C × SlotCache C) ProbComp),
        Pr[= (u, (s', false)) | (withFired seeds pairKeys I t).run (s, false)] = 0 := fun I => by
      refine probOutput_eq_zero_of_not_mem_support fun h => ?_
      simp only [withFired, StateT.run_mk, support_map, Set.mem_image] at h
      obtain ⟨w, -, hw⟩ := h
      have := congrArg (fun z => z.2.2) hw
      simp [hitFlag, Finset.nonempty_iff_ne_empty.mpr hF] at this
    rw [symImpl, realImpl, hz, hz]

/-- The hop from the real game to the symbolic game, for keys without a collision. -/
theorem real_sym_hop (hinj : Function.Injective (slotInput seeds pairKeys)) (b : Bool) (parameter : PublicParameter)
    (A : TprfAdversary C) :
    |(Pr[= true | Prod.fst <$> (simulateQ (realImpl prims seeds pairKeys b parameter) A).run symInit]).toReal -
      (Pr[= true | Prod.fst <$> (simulateQ (symImpl prims seeds pairKeys b parameter) A).run symInit]).toReal| ≤
      (Pr[fun z => z.2.2 = true | (simulateQ (symImpl prims seeds pairKeys b parameter) A).run symInit]).toReal := by
  have h := OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
    (symImpl prims seeds pairKeys b parameter) (realImpl prims seeds pairKeys b parameter) A symInit.1
    (real_sym_agree prims seeds pairKeys hinj b parameter)
    (withFired_mono seeds pairKeys _) (withFired_mono seeds pairKeys _)
  rw [abs_sub_comm]
  exact (abs_probOutput_toReal_sub_le_tvDist _ _).trans ((tvDist_map_le _ _ _).trans h)

/-! ## Presampling the slots -/

section Presample

variable {σ : Type} (getC : σ → SlotCache C) (setC : σ → SlotCache C → σ)

/-- A step keeps its distribution if the slot `x`, fresh in the state, is sampled before it. The
continuation must have the same property. -/
def Presampled (x : Slot C) {α : Type} (m : StateT σ ProbComp α) : Prop :=
  ∀ p, getC p x = none → ∀ {β : Type} (k : α × σ → ProbComp β),
    (∀ a p', getC p' x = none →
      𝒟[($ᵗ HashOutput) >>= fun v => k (a, setC p' ((getC p').cacheQuery x v))] = 𝒟[k (a, p')]) →
    𝒟[($ᵗ HashOutput) >>= fun v => m.run (setC p ((getC p).cacheQuery x v)) >>= k] = 𝒟[m.run p >>= k]

variable {getC setC}

theorem presampled_pure (x : Slot C) {α : Type} (a : α) :
    Presampled getC setC x (pure a : StateT σ ProbComp α) := by
  intro p hp β k hk
  simpa using hk a p hp

theorem presampled_bind (x : Slot C) {α γ : Type} {m : StateT σ ProbComp α}
    {f : α → StateT σ ProbComp γ} (hm : Presampled getC setC x m) (hf : ∀ a, Presampled getC setC x (f a)) :
    Presampled getC setC x (m >>= f) := by
  intro p hp β k hk
  simp only [StateT.run_bind, bind_assoc]
  exact hm p hp (fun z => (f z.1).run z.2 >>= k) fun a p' hp' => hf a p' hp' k hk

theorem presampled_map (x : Slot C) {α γ : Type} {m : StateT σ ProbComp α} (f : α → γ)
    (hm : Presampled getC setC x m) : Presampled getC setC x (f <$> m) := by
  rw [map_eq_bind_pure_comp]
  exact presampled_bind x hm fun a => presampled_pure x _

theorem presampled_mapM (x : Slot C) {α γ : Type} {f : α → StateT σ ProbComp γ}
    (hf : ∀ a, Presampled getC setC x (f a)) (l : List α) : Presampled getC setC x (l.mapM f) := by
  induction l with
  | nil => exact presampled_pure x _
  | cons a l ih =>
    rw [List.mapM_cons]
    exact presampled_bind x (hf a) fun b => presampled_bind x ih fun bs => presampled_pure x _

/-- A step through a map of the state, which reads and writes the slots only through `m`. -/
theorem presampled_transport {σ' : Type} {getC' : σ' → SlotCache C} {setC' : σ' → SlotCache C → σ'}
    (x : Slot C) {α β' : Type} (π : σ' → σ) (m : σ' → StateT σ ProbComp α) (out : σ' → α × σ → β' × σ')
    (hget : ∀ p, getC' p = getC (π p)) (hπ : ∀ p c, π (setC' p c) = setC (π p) c)
    (hm' : ∀ p c, m (setC' p c) = m p) (hout : ∀ p c, out (setC' p c) = out p)
    (hset : ∀ p a s c, out p (a, setC s c) = ((out p (a, s)).1, setC' (out p (a, s)).2 c))
    (hget' : ∀ p a s, getC' (out p (a, s)).2 = getC s)
    (hm : ∀ p, Presampled getC setC x (m p)) :
    Presampled getC' setC' x (StateT.mk fun p => out p <$> (m p).run (π p)) := by
  intro p hp γ k hk
  simp only [StateT.run_mk, hm', hout, hπ, hget, bind_map_left]
  rw [hget] at hp
  refine hm p (π p) hp (fun z => k (out p z)) fun a s hs => ?_
  simp only [hset]
  have h := hk (out p (a, s)).1 (out p (a, s)).2 (by rw [hget']; exact hs)
  rw [hget'] at h
  exact h

theorem presampled_ite (x : Slot C) {α : Type} (c : σ → Prop) [DecidablePred c] (m₁ m₂ : σ → StateT σ ProbComp α)
    (hc : ∀ p v, c (setC p v) ↔ c p) (h₁ : ∀ p, Presampled getC setC x (m₁ p)) (h₂ : ∀ p, Presampled getC setC x (m₂ p))
    (hm₁ : ∀ p v, m₁ (setC p v) = m₁ p) (hm₂ : ∀ p v, m₂ (setC p v) = m₂ p) :
    Presampled getC setC x (StateT.mk fun p => if c p then (m₁ p).run p else (m₂ p).run p) := by
  intro p hp β k hk
  simp only [StateT.run_mk, hc]
  split_ifs
  · simp only [hm₁]
    exact h₁ p p hp k hk
  · simp only [hm₂]
    exact h₂ p p hp k hk

end Presample

theorem slotCache_cacheQuery_comm (c : SlotCache C) {s x : Slot C} (h : s ≠ x) (u v : HashOutput) :
    (c.cacheQuery x v).cacheQuery s u = (c.cacheQuery s u).cacheQuery x v :=
  (Function.update_comm h _ _ _).symm

theorem presampled_slotOracle (x s : Slot C) : Presampled id (fun _ c => c) x (slotOracle s) := by
  intro c hc β k hk
  simp only [id] at hc hk ⊢
  by_cases hsx : s = x
  · subst hsx
    simp only [QueryImpl.withCaching_run_none _ hc,
      QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self c s _), pure_bind, bind_map_left]
    rfl
  · cases hcs : c s with
    | some w =>
      have hcs' : ∀ v, (c.cacheQuery x v) s = some w := fun v => by
        rw [QueryCache.cacheQuery_of_ne _ _ hsx]; exact hcs
      simp only [QueryImpl.withCaching_run_some _ (hcs' _),
        QueryImpl.withCaching_run_some _ hcs, pure_bind]
      exact hk _ c hc
    | none =>
      have hcs' : ∀ v, (c.cacheQuery x v) s = none := fun v => by
        rw [QueryCache.cacheQuery_of_ne _ _ hsx]; exact hcs
      simp only [QueryImpl.withCaching_run_none _ (hcs' _),
        QueryImpl.withCaching_run_none _ hcs, bind_map_left]
      rw [evalDist_bind_bind_swap]
      refine evalDist_bind_congr' _ fun w => ?_
      rw [← hk w (c.cacheQuery s w) (by rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hsx)]; exact hc)]
      refine congrArg _ (bind_congr fun v => ?_)
      rw [slotCache_cacheQuery_comm c hsx]

/-- `Presampled` on the two caches. -/
abbrev Presampled₁ (x : Slot C) {α : Type} (m : StateT (HashCache C × SlotCache C) ProbComp α) : Prop :=
  Presampled Prod.snd (fun p c => (p.1, c)) x m

theorem presampled_onTable (x : Slot C) {α : Type} {m : StateT (SlotCache C) ProbComp α}
    (hm : Presampled id (fun _ c => c) x m) : Presampled₁ x (onTable m) :=
  presampled_transport x Prod.snd (fun _ => m) (fun p z => (z.1, (p.1, z.2))) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) fun _ => hm

theorem presampled_onCache (x : Slot C) {α : Type} (m : StateT (HashCache C) ProbComp α) :
    Presampled₁ x (onCache m) := by
  intro p hp β k hk
  simp only [onCache, StateT.run_mk, bind_map_left]
  rw [evalDist_bind_bind_swap]
  exact evalDist_bind_congr' _ fun z => hk z.1 (z.2, p.2) hp

theorem presampled_routedAnswer (x : Slot C) (t : (LocalSpec C).Domain) :
    Presampled₁ x (routedAnswer prims seeds pairKeys t) := by
  rcases t with n | u | y
  · exact presampled_onCache x _
  · show Presampled₁ x (if h : ∃ s, slotInput seeds pairKeys s = u then _ else _)
    split_ifs
    · exact presampled_onTable x (presampled_slotOracle x _)
    · exact presampled_onCache x _
  · exact presampled_onCache x _

theorem presampled_simulateQ_routed (x : Slot C) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    Presampled₁ x (simulateQ (routedAnswer prims seeds pairKeys) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using presampled_pure x a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact presampled_bind x (presampled_routedAnswer prims seeds pairKeys x t) ih

theorem presampled_symAdversary (x : Slot C) (D : Finset C.Party) (t : (LocalSpec C).Domain) :
    Presampled₁ x (symAdversary prims seeds pairKeys D t) := by
  rcases t with n | u | y
  · exact presampled_onCache x _
  · classical
    show Presampled₁ x (if h : ∃ s, Revealed D (slotKey s) ∧ slotInput seeds pairKeys s = u then _ else _)
    split_ifs
    · exact presampled_onTable x (presampled_slotOracle x _)
    · exact presampled_onCache x _
  · exact presampled_onCache x _

theorem presampled_evalSlots (x : Slot C) (i : C.Party) (J : C.Quorum) (y : Point) (ec : Message) :
    Presampled₁ x (evalSlots (C := C) i J y ec) := by
  refine presampled_onTable x (presampled_bind x (presampled_mapM x (fun T => presampled_map x _
    (presampled_slotOracle x _)) _) fun _ => presampled_bind x (presampled_mapM x (fun j => ?_) _) fun _ =>
      presampled_pure x _)
  split_ifs
  · exact presampled_pure x _
  · exact presampled_map x _ (presampled_slotOracle x _)

theorem presampled_prfSlots (x : Slot C) (y : Point) : Presampled₁ x (prfSlots (C := C) y) :=
  presampled_onTable x (presampled_bind x (presampled_mapM x (fun _ => presampled_map x _
    (presampled_slotOracle x _)) _) fun _ => presampled_pure x _)

/-- `Presampled` on the game state and the two caches. -/
abbrev Presampled₂ (x : Slot C) {α : Type} (m : StateT (TprfState C × HashCache C × SlotCache C) ProbComp α) : Prop :=
  Presampled (fun p => p.2.2) (fun p c => (p.1, (p.2.1, c))) x m

theorem presampled_lift₂ (x : Slot C) {α β : Type} (m : TprfState C → StateT (HashCache C × SlotCache C) ProbComp α)
    (out : TprfState C → α → β × TprfState C) (hm : ∀ st, Presampled₁ x (m st)) :
    Presampled₂ x (StateT.mk fun p => (fun z => ((out p.1 z.1).1, ((out p.1 z.1).2, z.2))) <$> (m p.1).run p.2) :=
  presampled_transport x Prod.snd (fun p => m p.1) (fun p z => ((out p.1 z.1).1, ((out p.1 z.1).2, z.2)))
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    fun p => hm p.1

theorem presampled_ite₂ (x : Slot C) {α : Type} (c : TprfState C → Prop) [DecidablePred c]
    (A B : TprfState C × HashCache C × SlotCache C → ProbComp (α × (TprfState C × HashCache C × SlotCache C)))
    (hA : Presampled₂ x (StateT.mk A)) (hB : Presampled₂ x (StateT.mk B)) :
    Presampled₂ x (StateT.mk fun p => if c p.1 then A p else B p) := by
  intro p hp β k hk
  simp only [StateT.run_mk]
  split_ifs
  · exact hA p hp k hk
  · exact hB p hp k hk

set_option maxRecDepth 10000 in
theorem presampled_gameImplWith (x : Slot C)
    (adversary : Finset C.Party → QueryImpl (LocalSpec C) (StateT (HashCache C × SlotCache C) ProbComp))
    (evalH : C.Party → C.Quorum → Point → Message → StateT (HashCache C × SlotCache C) ProbComp Digest)
    (prfH : Point → StateT (HashCache C × SlotCache C) ProbComp Digest)
    (sampleH : StateT (HashCache C × SlotCache C) ProbComp Digest) (b : Bool) (keys : C.Party → Keys C)
    (hadv : ∀ D t, Presampled₁ x (adversary D t)) (heval : ∀ i J y ec, Presampled₁ x (evalH i J y ec))
    (hprf : ∀ y, Presampled₁ x (prfH y)) (hsample : Presampled₁ x sampleH) (t : (LocalSpec C + TprfSpec C).Domain) :
    Presampled₂ x (gameImplWith adversary evalH prfH sampleH b keys t) := by
  have hpure : ∀ {α : Type} (f : TprfState C → α) (g : TprfState C → TprfState C),
      Presampled₂ x (StateT.mk fun p => pure (f p.1, (g p.1, p.2))) := fun f g p hp β k hk => by
    simpa using hk (f p.1) (g p.1, p.2) hp
  rcases t with t | (i | ⟨i, J, y, ec⟩ | y)
  · exact presampled_lift₂ x (fun st => adversary st.corrupt t) (fun st a => (a, st)) fun st => hadv _ t
  · exact presampled_ite₂ x (fun st => ∃ x ∈ st.challenged, ∃ ec, C.t ≤ (st.corrupt ∪ st.queried x ec ∪ {i}).card)
      (fun p => pure (none, p)) (fun p => pure (some (keys i), ({ p.1 with corrupt := insert i p.1.corrupt }, p.2)))
      (hpure (fun _ => none) id) (hpure (fun _ => some (keys i)) fun st => { st with corrupt := insert i st.corrupt })
  · have hB := presampled_lift₂ (β := (LocalSpec C + TprfSpec C).Range (.inr (.eval i J y ec))) x (fun _ => evalH i J y ec)
        (fun st d => (some d, addQuery st i y ec)) fun _ => heval i J y ec
    have hA := hpure (α := (LocalSpec C + TprfSpec C).Range (.inr (.eval i J y ec))) (fun _ => none) id
    have := presampled_ite₂ x (fun st => i ∉ J.1 ∨ (C.t ≤ (st.corrupt ∪ st.queried y ec ∪ {i}).card ∧ y ∈ st.challenged)) _ _ hA hB
    convert this using 1
    ext p : 1
    simp only [gameImplWith, StateT.run_mk, id]
  · cases b
    · have hB := presampled_lift₂ (β := (LocalSpec C + TprfSpec C).Range (.inr (.challenge y))) x (fun _ => prfH y)
        (fun st d => (some d, addChallenge st y d)) fun _ => hprf y
      have hA := hpure (α := (LocalSpec C + TprfSpec C).Range (.inr (.challenge y))) (fun _ => none) id
      have := presampled_ite₂ x (fun st => ∃ ec, C.t ≤ (st.corrupt ∪ st.queried y ec).card) _ _ hA hB
      convert this using 1
      ext p : 1
      simp only [gameImplWith, StateT.run_mk, id, if_false, Bool.false_eq_true]
    · have hB := presampled_lift₂ (β := (LocalSpec C + TprfSpec C).Range (.inr (.challenge y))) x
        (fun st => match st.random y with | some d => pure d | none => sampleH)
        (fun st d => (some d, addChallenge st y d)) fun st => by
          cases st.random y
          · exact hsample
          · exact presampled_pure x _
      have hA := hpure (α := (LocalSpec C + TprfSpec C).Range (.inr (.challenge y))) (fun _ => none) id
      have := presampled_ite₂ x (fun st => ∃ ec, C.t ≤ (st.corrupt ∪ st.queried y ec).card) _ _ hA hB
      convert this using 1
      ext p : 1
      simp only [gameImplWith, StateT.run_mk, id, if_true]

/-- The slots of the state of the hop. -/
def getTable (p : SymState C × Bool) : SlotCache C := p.1.1.2.2

/-- The state of the hop with the slot cache `c`. -/
def setTable (p : SymState C × Bool) (c : SlotCache C) : SymState C × Bool := (((p.1.1.1, p.1.1.2.1, c), p.1.2), p.2)

theorem setTable_getTable (p : SymState C × Bool) : setTable p (getTable p) = p := rfl

/-- `Presampled` on the state of the hop. -/
abbrev Presampled₃ (x : Slot C) {α : Type} (m : StateT (SymState C × Bool) ProbComp α) : Prop :=
  Presampled getTable setTable x m

theorem presampled_withFired (x : Slot C)
    (I : QueryImpl (LocalSpec C + TprfSpec C) (StateT (TprfState C × HashCache C × SlotCache C) ProbComp))
    (t : (LocalSpec C + TprfSpec C).Domain) (h : Presampled₂ x (I t)) :
    Presampled₃ x (withFired seeds pairKeys I t) := by
  intro p hp β k hk
  simp only [withFired, StateT.run_mk, bind_map_left, setTable, getTable]
  exact h p.1.1 hp (fun z => k (z.1, ((z.2, p.1.2 ∪ firedBy seeds pairKeys p.1.1.1.corrupt t),
    p.2 || hitFlag seeds pairKeys p.1.1.1.corrupt t))) (fun a s hs => hk a ((s, p.1.2 ∪ firedBy seeds pairKeys
      p.1.1.1.corrupt t), p.2 || hitFlag seeds pairKeys p.1.1.1.corrupt t) hs)

set_option maxRecDepth 100000 in
theorem presampled_symImpl (x : Slot C) (b : Bool) (parameter : PublicParameter)
    (t : (LocalSpec C + TprfSpec C).Domain) : Presampled₃ x (symImpl prims seeds pairKeys b parameter t) := by
  have h := presampled_gameImplWith x (symAdversary prims seeds pairKeys) evalSlots prfSlots
    (simulateQ (routedAnswer prims seeds pairKeys) (liftComp ($ᵗ Digest) _)) b (dealtKeys parameter seeds pairKeys)
    (presampled_symAdversary prims seeds pairKeys x) (presampled_evalSlots x) (presampled_prfSlots x)
    (presampled_simulateQ_routed prims seeds pairKeys x _) t
  unfold symImpl
  exact presampled_withFired seeds pairKeys x _ t h

theorem presampled_simulateQ_symImpl (x : Slot C) (b : Bool) (parameter : PublicParameter) {α : Type}
    (oa : OracleComp (LocalSpec C + TprfSpec C) α) :
    Presampled₃ x (simulateQ (symImpl prims seeds pairKeys b parameter) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using presampled_pure x a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact presampled_bind x (presampled_symImpl prims seeds pairKeys x b parameter t) ih

/-- The slot cache `c` with the values of `ω` at the slots `l`. -/
def fillSlots (ω : Slot C → HashOutput) : List (Slot C) → SlotCache C → SlotCache C
  | [], c => c
  | s :: l, c => (fillSlots ω l c).cacheQuery s (ω s)

theorem fillSlots_of_not_mem (ω : Slot C → HashOutput) (l : List (Slot C)) (c : SlotCache C) {x : Slot C}
    (hx : x ∉ l) : fillSlots ω l c x = c x := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    simp only [fillSlots]
    rw [QueryCache.cacheQuery_of_ne _ _ (by rintro rfl; exact hx (List.mem_cons_self ..))]
    exact ih fun h => hx (List.mem_cons_of_mem _ h)

theorem fillSlots_update (ω : Slot C → HashOutput) (l : List (Slot C)) (c : SlotCache C) {x : Slot C} (hx : x ∉ l)
    (u : HashOutput) : fillSlots (Function.update ω x u) l c = fillSlots ω l c := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [fillSlots]
    rw [ih (fun h => hx (List.mem_cons_of_mem _ h)),
      Function.update_of_ne (by rintro rfl; exact hx (List.mem_cons_self ..))]

theorem evalDist_uniform_bind_const {α : Type} [SampleableType α] {β : Type} (my : ProbComp β) :
    𝒟[($ᵗ α) >>= fun _ => my] = 𝒟[my] :=
  evalDist_ext fun y => by simp

/-- Sampling the slots `l`, fresh in the state, before a run of the symbolic game leaves the result
unchanged. -/
theorem presample_symImpl (b : Bool) (parameter : PublicParameter) {α : Type}
    (oa : OracleComp (LocalSpec C + TprfSpec C) α) (l : List (Slot C)) (hl : l.Nodup) (p : SymState C × Bool)
    (hp : ∀ s ∈ l, getTable p s = none) :
    𝒟[($ᵗ (Slot C → HashOutput)) >>= fun ω =>
        (simulateQ (symImpl prims seeds pairKeys b parameter) oa).run' (setTable p (fillSlots ω l (getTable p)))] =
      𝒟[(simulateQ (symImpl prims seeds pairKeys b parameter) oa).run' p] := by
  induction l with
  | nil =>
    simp only [fillSlots, setTable_getTable]
    exact evalDist_uniform_bind_const (α := Slot C → HashOutput) _
  | cons s l ih =>
    have hs : s ∉ l := (List.nodup_cons.mp hl).1
    rw [evalDist_bind, ← evalDist_uniformSample_bind_update (D := Slot C) (R := HashOutput) s, ← evalDist_bind]
    simp only [bind_assoc, pure_bind, fillSlots, fillSlots_update _ l _ hs, Function.update_self]
    rw [evalDist_bind_bind_swap]
    rw [← ih (List.nodup_cons.mp hl).2 (fun a ha => hp a (List.mem_cons_of_mem _ ha))]
    refine evalDist_bind_congr' _ fun g => ?_
    have hfresh : getTable (setTable p (fillSlots g l (getTable p))) s = none := by
      show fillSlots g l (getTable p) s = none
      rw [fillSlots_of_not_mem g l _ hs]
      exact hp s (List.mem_cons_self ..)
    have h := presampled_simulateQ_symImpl prims seeds pairKeys s b parameter oa
      (setTable p (fillSlots g l (getTable p))) hfresh (fun z => (pure z.1 : ProbComp α)) fun a p' _ =>
        evalDist_uniform_bind_const (α := HashOutput) (pure a)
    simp only [StateT.run'_eq, map_eq_bind_pure_comp]
    exact h

/-! ## The fiber balance of the symbolic game

A view fixes the `Eval` answers, the values that the adversary reads at revealed slots, and the
challenge answers. Each challenge answer splits the consistent tables into fibers of equal size. -/

section Fiber

/-- An `Eval` answer of the view. -/
structure EvalRecord (C : Committee) where
  i : C.Party
  J : C.Quorum
  x : Point
  ec : Message
  answer : XorDigest

/-- The answer of `Eval` for the table `ω`. -/
def evalSum (ω : Slot C → HashOutput) (i : C.Party) (J : C.Quorum) (x : Point) (ec : Message) : XorDigest :=
  ∑ T ∈ L J i, toXor (truncateHash (ω (.inl (T, x)))) +
    ∑ j ∈ univ.filter (fun j => j ∈ J.1 ∧ j ≠ i),
      if h : j = i then 0 else toXor (truncateHash (ω (.inr (C.pairOf i j (Ne.symm h), x, ec, J))))

/-- The PRF value at `x` for the table `ω`. -/
def prfSum (ω : Slot C → HashOutput) (x : Point) : XorDigest :=
  ∑ T, toXor (truncateHash (ω (.inl (T, x))))

/-- The table `ω` gives the view. -/
def Consistent (records : List (EvalRecord C)) (reads : List (Slot C × HashOutput))
    (challenged : Finset Point) (c : Point → XorDigest) (ω : Slot C → HashOutput) : Prop :=
  (∀ e ∈ records, evalSum ω e.i e.J e.x e.ec = e.answer) ∧ (∀ r ∈ reads, ω r.1 = r.2) ∧
    ∀ x ∈ challenged, prfSum ω x = c x

/-- The operators with an `Eval` answer at `(x, ec)` in the view. -/
def recordQueriers (records : List (EvalRecord C)) (x : Point) (ec : Message) : Finset C.Party :=
  ((records.filter fun e => e.x = x ∧ e.ec = ec).map (·.i)).toFinset

theorem truncateHash_xor_setWidth (v : HashOutput) (d : Digest) :
    truncateHash (v ^^^ d.setWidth hashOutputBits) = truncateHash v ^^^ d := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [truncateHash, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]
  have : k < hashOutputBits := by simp [hashOutputBits, digestBits] at hk ⊢; omega
  simp [hk, this]

theorem pairOf_eq_iff {i j i' j' : C.Party} (h : i ≠ j) (h' : i' ≠ j') :
    C.pairOf i j h = C.pairOf i' j' h' ↔ (i = i' ∧ j = j') ∨ (i = j' ∧ j = i') := by
  constructor
  · intro heq
    unfold Committee.pairOf at heq
    split_ifs at heq <;> simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq <;>
      obtain ⟨rfl, rfl⟩ := heq <;> simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact pairOf_comm _ _ h

theorem pairOf_fst_mem {i j : C.Party} (h : i ≠ j) : (C.pairOf i j h).1.1 = i ∨ (C.pairOf i j h).1.1 = j := by
  unfold Committee.pairOf; split_ifs <;> simp

theorem pairOf_snd_mem {i j : C.Party} (h : i ≠ j) : (C.pairOf i j h).1.2 = i ∨ (C.pairOf i j h).1.2 = j := by
  unfold Committee.pairOf; split_ifs <;> simp

section Balance

open Classical

variable (records : List (EvalRecord C)) (D : Finset C.Party) (challenged : Finset Point) (Tstar : C.Term)

/-- An honest operator of the quorum, other than `i`, without an `Eval` answer at `(x, ec)`. -/
def IsPad (x : Point) (ec : Message) (J : C.Quorum) (i j : C.Party) : Prop :=
  j ∈ J.1 ∧ j ≠ i ∧ j ∉ D ∧ j ∉ recordQueriers records x ec

/-- The private pad of the answers of `i` at `(J, x, ec)`. -/
def pad (i : C.Party) (J : C.Quorum) (x : Point) (ec : Message) : C.Party :=
  if h : ∃ j, IsPad records D x ec J i j then Classical.choose h else i

/-- The answers of `i` at `(J, x, ec)` hold the hidden term `Tstar` at a challenged point. -/
def Shifted (i : C.Party) (J : C.Quorum) (x : Point) (ec : Message) : Prop :=
  i ∉ D ∧ Tstar ∈ L J i ∧ x ∈ challenged ∧ i ∈ recordQueriers records x ec

variable {records D challenged Tstar}

theorem pad_isPad (hinv : ∀ x ∈ challenged, ∀ ec, (D ∪ recordQueriers records x ec).card ≤ C.t - 1)
    {i : C.Party} {J : C.Quorum} {x : Point} {ec : Message} (h : Shifted records D challenged Tstar i J x ec) :
    IsPad records D x ec J i (pad records D i J x ec) := by
  have hex : ∃ j, IsPad records D x ec J i j := by
    have hcard := hinv x h.2.2.1 ec
    have hJ := J.2
    have := C.one_le_t
    obtain ⟨j, hj, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := D ∪ recordQueriers records x ec) (t := J.1) (by omega)
    simp only [Finset.mem_union, not_or] at hnot
    exact ⟨j, hj, fun hji => hnot.2 (hji ▸ h.2.2.2), hnot.1, hnot.2⟩
  rw [pad, dif_pos hex]
  exact Classical.choose_spec hex

/-- The shift of each slot. -/
def shiftOf (δ : Point → XorDigest) : Slot C → Digest
  | .inl (T, x) => if T = Tstar ∧ x ∈ challenged then δ x else 0#digestBits
  | .inr (p, x, ec, J) => if ∃ i, Shifted records D challenged Tstar i J x ec ∧
      ∃ h : i ≠ pad records D i J x ec, p = C.pairOf i (pad records D i J x ec) h then δ x else 0#digestBits

variable (records D challenged Tstar) in
/-- The bijection of the tables. -/
def shiftTable (δ : Point → XorDigest) (ω : Slot C → HashOutput) : Slot C → HashOutput :=
  fun s => ω s ^^^ (shiftOf (records := records) (D := D) (challenged := challenged) (Tstar := Tstar) δ s).setWidth
    hashOutputBits

theorem shiftTable_shiftTable (δ : Point → XorDigest) (ω : Slot C → HashOutput) :
    shiftTable records D challenged Tstar δ (shiftTable records D challenged Tstar δ ω) = ω := by
  funext s
  simp [shiftTable, BitVec.xor_assoc]

theorem toXor_truncateHash_shiftTable (δ : Point → XorDigest) (ω : Slot C → HashOutput) (s : Slot C) :
    toXor (truncateHash (shiftTable records D challenged Tstar δ ω s)) =
      toXor (truncateHash (ω s)) + toXor (shiftOf (records := records) (D := D) (challenged := challenged)
        (Tstar := Tstar) δ s) := by
  rw [shiftTable, truncateHash_xor_setWidth, toXor_xor]

variable (hT : D ⊆ Tstar.1)
  (hinv : ∀ x ∈ challenged, ∀ ec, (D ∪ recordQueriers records x ec).card ≤ C.t - 1)
include hT hinv

omit hT in
theorem shiftOf_mask (δ : Point → XorDigest) {i j : C.Party} (hij : i ≠ j) {J : C.Quorum} {x : Point}
    {ec : Message} (hi : i ∈ recordQueriers records x ec) :
    shiftOf (records := records) (D := D) (challenged := challenged) (Tstar := Tstar) δ
        (.inr (C.pairOf i j hij, x, ec, J)) =
      if Shifted records D challenged Tstar i J x ec ∧ j = pad records D i J x ec then δ x else 0#digestBits := by
  simp only [shiftOf]
  by_cases hs : Shifted records D challenged Tstar i J x ec ∧ j = pad records D i J x ec
  · rw [if_pos hs, if_pos ⟨i, hs.1, hs.2 ▸ hij, by simp [← hs.2]⟩]
  · rw [if_neg hs, if_neg]
    rintro ⟨i', hs', hne, heq⟩
    rcases (pairOf_eq_iff hij hne).mp heq with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
    · exact hs ⟨hs', rfl⟩
    · exact (pad_isPad hinv hs').2.2.2 hi

omit hinv in
theorem mem_L_not_mem {i : C.Party} {J : C.Quorum} (h : Tstar ∈ L J i) : i ∉ D := fun hi => by
  have := mem_holders_of_mem_L h
  simp only [Committee.holders, Finset.mem_compl] at this
  exact this (hT hi)

theorem evalSum_shiftTable (δ : Point → XorDigest) (ω : Slot C → HashOutput) {i : C.Party} {J : C.Quorum}
    {x : Point} {ec : Message} (hi : i ∈ recordQueriers records x ec) :
    evalSum (shiftTable records D challenged Tstar δ ω) i J x ec = evalSum ω i J x ec := by
  have hterm : ∑ T ∈ L J i, toXor (shiftOf (records := records) (D := D) (challenged := challenged)
      (Tstar := Tstar) δ (.inl (T, x))) = if Tstar ∈ L J i ∧ x ∈ challenged then δ x else 0 := by
    simp only [shiftOf, apply_ite toXor, toXor_zero]
    by_cases hx : x ∈ challenged
    · simp only [hx, and_true]
      rw [Finset.sum_ite_eq' (L J i) Tstar]
      rfl
    · simp only [hx, and_false, if_false]
      exact Finset.sum_eq_zero fun _ _ => rfl
  have hmask : ∑ j ∈ univ.filter (fun j => j ∈ J.1 ∧ j ≠ i), (if h : j = i then (0 : XorDigest) else
      toXor (shiftOf (records := records) (D := D) (challenged := challenged) (Tstar := Tstar) δ
        (.inr (C.pairOf i j (Ne.symm h), x, ec, J)))) =
      if Shifted records D challenged Tstar i J x ec then δ x else 0 := by
    have hstep : ∀ j ∈ univ.filter (fun j => j ∈ J.1 ∧ j ≠ i), (if h : j = i then (0 : XorDigest) else
        toXor (shiftOf (records := records) (D := D) (challenged := challenged) (Tstar := Tstar) δ
          (.inr (C.pairOf i j (Ne.symm h), x, ec, J)))) =
        if Shifted records D challenged Tstar i J x ec ∧ j = pad records D i J x ec then δ x else 0 := by
      intro j hj
      have hji : j ≠ i := (Finset.mem_filter.mp hj).2.2
      rw [dif_neg hji, shiftOf_mask hinv δ (Ne.symm hji) hi]
      split_ifs <;> rfl
    rw [Finset.sum_congr rfl hstep]
    by_cases hs : Shifted records D challenged Tstar i J x ec
    · simp only [hs, true_and]
      have hpad := pad_isPad hinv hs
      have hmem : pad records D i J x ec ∈ univ.filter (fun j => j ∈ J.1 ∧ j ≠ i) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpad.1, hpad.2.1⟩
      rw [Finset.sum_ite_eq' _ (pad records D i J x ec), if_pos hmem, if_pos trivial]
    · simp only [hs, false_and, if_false]
      exact Finset.sum_eq_zero fun _ _ => rfl
  have hiff : (Tstar ∈ L J i ∧ x ∈ challenged) ↔ Shifted records D challenged Tstar i J x ec :=
    ⟨fun h => ⟨mem_L_not_mem hT h.1, h.1, h.2, hi⟩, fun h => ⟨h.2.1, h.2.2.1⟩⟩
  have hsplit : evalSum (shiftTable records D challenged Tstar δ ω) i J x ec = evalSum ω i J x ec +
      ((if Tstar ∈ L J i ∧ x ∈ challenged then δ x else 0) +
        if Shifted records D challenged Tstar i J x ec then δ x else 0) := by
    rw [← hterm, ← hmask]
    simp only [evalSum, toXor_truncateHash_shiftTable, Finset.sum_add_distrib]
    have hd : ∀ (a b : ∀ j : C.Party, ¬j = i → XorDigest), ∑ j ∈ univ.filter (fun j => j ∈ J.1 ∧ j ≠ i),
        (if h : j = i then (0 : XorDigest) else a j h + b j h) =
        ∑ j ∈ univ.filter (fun j => j ∈ J.1 ∧ j ≠ i), (if h : j = i then (0 : XorDigest) else a j h) +
          ∑ j ∈ univ.filter (fun j => j ∈ J.1 ∧ j ≠ i), (if h : j = i then (0 : XorDigest) else b j h) := by
      intro a b
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [hd (fun j h => toXor (truncateHash (ω (.inr (C.pairOf i j (Ne.symm h), x, ec, J)))))
      (fun j h => toXor (shiftOf (records := records) (D := D) (challenged := challenged) (Tstar := Tstar) δ
        (.inr (C.pairOf i j (Ne.symm h), x, ec, J))))]
    abel
  rw [hsplit]
  by_cases hs : Shifted records D challenged Tstar i J x ec
  · rw [if_pos (hiff.mpr hs), if_pos hs, XorDigest.add_self, add_zero]
  · rw [if_neg (fun h => hs (hiff.mp h)), if_neg hs, add_zero, add_zero]

omit hT hinv in
/-- The PRF value at a challenged point moves by `δ x`. -/
theorem prfSum_shiftTable (δ : Point → XorDigest) (ω : Slot C → HashOutput) {x : Point} (hx : x ∈ challenged) :
    prfSum (shiftTable records D challenged Tstar δ ω) x = prfSum ω x + δ x := by
  simp only [prfSum, toXor_truncateHash_shiftTable, Finset.sum_add_distrib]
  congr 1
  simp only [shiftOf, hx, and_true, apply_ite toXor, toXor_zero]
  rw [Finset.sum_ite_eq' Finset.univ Tstar, if_pos (Finset.mem_univ _)]
  rfl

/-- A revealed slot stays. -/
theorem shiftTable_revealed (δ : Point → XorDigest) (ω : Slot C → HashOutput) {s : Slot C}
    (hs : Revealed D (slotKey s)) : shiftTable records D challenged Tstar δ ω s = ω s := by
  have hzero : shiftOf (records := records) (D := D) (challenged := challenged) (Tstar := Tstar) δ s =
      0#digestBits := by
    rcases s with ⟨T, x⟩ | ⟨p, x, ec, J⟩
    · simp only [shiftOf]
      rw [if_neg]
      rintro ⟨rfl, -⟩
      obtain ⟨i, hi, hhold⟩ := hs
      simp only [Committee.holders, Finset.mem_compl] at hhold
      exact hhold (hT hi)
    · simp only [shiftOf]
      rw [if_neg]
      rintro ⟨i, hsh, hne, rfl⟩
      have hpad := pad_isPad hinv hsh
      have hout : ∀ k, k = i ∨ k = pad records D i J x ec → k ∉ D := by
        rintro k (rfl | rfl)
        · exact hsh.1
        · exact hpad.2.2.1
      rcases hs with h | h
      · exact hout _ (pairOf_fst_mem hne) h
      · exact hout _ (pairOf_snd_mem hne) h
  simp [shiftTable, hzero]

variable (reads : List (Slot C × HashOutput)) (hreads : ∀ r ∈ reads, Revealed D (slotKey r.1))
include hreads

theorem consistent_shiftTable {c c' : Point → XorDigest} {ω : Slot C → HashOutput}
    (h : Consistent records reads challenged c ω) :
    Consistent records reads challenged c' (shiftTable records D challenged Tstar (fun x => c x + c' x) ω) := by
  refine ⟨fun e he => ?_, fun r hr => ?_, fun x hx => ?_⟩
  · have hi : e.i ∈ recordQueriers records e.x e.ec := by
      simp only [recordQueriers, List.mem_toFinset, List.mem_map, List.mem_filter]
      exact ⟨e, ⟨he, by simp⟩, rfl⟩
    rw [evalSum_shiftTable hT hinv _ _ hi, h.1 e he]
  · rw [shiftTable_revealed hT hinv _ _ (hreads r hr), h.2.1 r hr]
  · rw [prfSum_shiftTable _ _ hx, h.2.2 x hx, ← add_assoc, XorDigest.add_self, zero_add]

/-- The fiber balance. The tables that give the view and the challenge answers `c` are as many as
those for `c'`. -/
theorem card_consistent_eq (c c' : Point → XorDigest) :
    (univ.filter (Consistent records reads challenged c)).card =
      (univ.filter (Consistent records reads challenged c')).card := by
  refine Finset.card_nbij' (shiftTable records D challenged Tstar (fun x => c x + c' x))
    (shiftTable records D challenged Tstar (fun x => c x + c' x)) (fun ω hω => ?_) (fun ω hω => ?_)
    (fun ω _ => shiftTable_shiftTable _ _) (fun ω _ => shiftTable_shiftTable _ _)
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
    exact consistent_shiftTable hT hinv reads hreads hω
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
    have h := consistent_shiftTable hT hinv reads hreads (c' := c) hω
    have hδ : (fun x => c' x + c x) = fun x => c x + c' x := funext fun x => add_comm _ _
    rwa [hδ] at h

/-- Each challenge answer divides the tables that give the other answers by `2 ^ 128`. -/
theorem card_consistent_mul (c : Point → XorDigest) :
    (univ.filter (Consistent records reads challenged c)).card * (2 ^ digestBits) ^ challenged.card =
      (univ.filter (Consistent records reads ∅ c)).card := by
  letI : Fintype XorDigest := inferInstanceAs (Fintype Digest)
  letI : DecidableEq XorDigest := inferInstanceAs (DecidableEq Digest)
  let f : (Slot C → HashOutput) → (challenged → XorDigest) := fun ω x => prfSum ω x.1
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (s := univ.filter (Consistent records reads ∅ c))
    (t := univ) (fun _ _ => Finset.mem_univ _)]
  have hfiber : ∀ d : challenged → XorDigest,
      ((univ.filter (Consistent records reads ∅ c)).filter fun ω => f ω = d).card =
        (univ.filter (Consistent records reads challenged c)).card := by
    intro d
    rw [card_consistent_eq hT hinv reads hreads c (fun x => if h : x ∈ challenged then d ⟨x, h⟩ else 0),
      Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr fun ω _ => ?_)
    simp only [Consistent, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, and_true, and_assoc, f]
    refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h x hx => ?_, fun h => ?_⟩
    · rw [dif_pos hx, ← h]
    · funext x
      have := h x.1 x.2
      rwa [dif_pos x.2] at this
  have hcard : Fintype.card XorDigest = 2 ^ digestBits := by
    change Fintype.card Digest = _
    simp
  rw [Finset.sum_congr rfl fun d _ => hfiber d, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Fintype.card_fun, Fintype.card_coe, hcard, mul_comm]

end Balance

end Fiber

/-! ## The symbolic game on a full table is the same for both `b` -/

section Balanced

open Classical

variable (parameter : PublicParameter)

/-- The state `v` with the full table `ω`. -/
def conc (v : SymState C × Bool) (ω : Slot C → HashOutput) : SymState C × Bool := setTable v fun s => some (ω s)

/-- The probability that the symbolic game outputs `true` from the state `p`. -/
def symP (b : Bool) (oa : OracleComp (LocalSpec C + TprfSpec C) Bool) (p : SymState C × Bool) : ℝ≥0∞ :=
  Pr[fun z => z.1 = true | (simulateQ (symImpl prims seeds pairKeys b parameter) oa).run p]

/-- The challenged points. -/
def chalSet (v : SymState C × Bool) : Finset Point := v.1.1.1.challenged

/-- The challenge answer at a point. -/
def chalValue (v : SymState C × Bool) (x : Point) : XorDigest := toXor ((v.1.1.1.random x).getD 0)

/-- The invariant of a state with the `Eval` answers `records` and the reads `reads` of the view. -/
def ViewInv (v : SymState C × Bool) (records : List (EvalRecord C)) (reads : List (Slot C × HashOutput)) : Prop :=
  (∀ x ∈ v.1.1.1.challenged, ∀ ec, (v.1.1.1.corrupt ∪ v.1.1.1.queried x ec).card ≤ C.t - 1) ∧
    (∀ x ec, v.1.1.1.queried x ec = recordQueriers records x ec) ∧
    (∀ rd ∈ reads, Revealed v.1.1.1.corrupt (slotKey rd.1)) ∧ ∀ x, x ∈ v.1.1.1.challenged ↔ (v.1.1.1.random x).isSome

/-- The weights of `b = false` and `b = true` from the state `v` with the view `records` and
`reads` agree. -/
def BalancedAt (oa : OracleComp (LocalSpec C + TprfSpec C) Bool) (v : SymState C × Bool)
    (records : List (EvalRecord C)) (reads : List (Slot C × HashOutput)) : Prop :=
  (∑ ω ∈ univ.filter (Consistent records reads (chalSet v) (chalValue v)),
      symP prims seeds pairKeys parameter false oa (conc v ω)) * (2 ^ digestBits : ℝ≥0∞) ^ (chalSet v).card =
    ∑ ω ∈ univ.filter (Consistent records reads ∅ (chalValue v)), symP prims seeds pairKeys parameter true oa (conc v ω)

/-- The weights agree from every state that satisfies the invariant. -/
def Balanced (oa : OracleComp (LocalSpec C + TprfSpec C) Bool) : Prop :=
  ∀ v records reads, ViewInv v records reads → BalancedAt prims seeds pairKeys parameter oa v records reads

/-- The PRF value at `x` for the table `ω`, as a digest. -/
def prfDigest (ω : Slot C → HashOutput) (x : Point) : Digest := prfSum ω x

theorem ennreal_mul_cancel (S a K : ℝ≥0∞) (h0 : K ≠ 0) (ht : K ≠ ⊤) : S * a = K⁻¹ * (S * (a * K)) := by
  rw [show K⁻¹ * (S * (a * K)) = S * a * (K⁻¹ * K) by ring, ENNReal.inv_mul_cancel h0 ht, mul_one]

theorem sum_tsum_mul {Ω β : Type} (S : Finset Ω) (q : β → ℝ≥0∞) (F : β → Ω → ℝ≥0∞) :
    ∑ ω ∈ S, ∑' w, q w * F w ω = ∑' w, q w * ∑ ω ∈ S, F w ω := by
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  exact tsum_congr fun w => (Finset.mul_sum _ _ _).symm

theorem consistent_empty_iff (records : List (EvalRecord C)) (reads : List (Slot C × HashOutput))
    (c c' : Point → XorDigest) (ω : Slot C → HashOutput) :
    Consistent records reads ∅ c ω ↔ Consistent records reads ∅ c' ω := by
  simp [Consistent]

/-- A step that reads no slot and keeps the view. -/
theorem balancedAt_indep {R : Type} {oa : OracleComp (LocalSpec C + TprfSpec C) Bool}
    {step : Bool → StateT (SymState C × Bool) ProbComp R} {cont : R → OracleComp (LocalSpec C + TprfSpec C) Bool}
    (hoa : ∀ b p, symP prims seeds pairKeys parameter b oa p = Pr[fun z => z.1 = true | (step b).run p >>= fun z =>
      (simulateQ (symImpl prims seeds pairKeys b parameter) (cont z.1)).run z.2])
    (IH : ∀ u, Balanced prims seeds pairKeys parameter (cont u)) {v : SymState C × Bool} {records reads}
    (m : ProbComp (R × SymState C × Bool))
    (hstep : ∀ b ω, (step b).run (conc v ω) = (fun w => (w.1, conc w.2 ω)) <$> m)
    (hm : ∀ w ∈ support m, ViewInv w.2 records reads ∧ chalSet w.2 = chalSet v ∧
      chalValue w.2 = chalValue v) :
    BalancedAt prims seeds pairKeys parameter oa v records reads := by
  have hP : ∀ b ω, symP prims seeds pairKeys parameter b oa (conc v ω) =
      ∑' w, Pr[= w | m] * symP prims seeds pairKeys parameter b (cont w.1) (conc w.2 ω) := fun b ω => by
    rw [hoa, hstep, bind_map_left, probEvent_bind_eq_tsum]
    rfl
  unfold BalancedAt
  simp only [hP, sum_tsum_mul, ← ENNReal.tsum_mul_right, mul_assoc]
  refine tsum_congr fun w => ?_
  by_cases hw : w ∈ support m
  · obtain ⟨hinv, hs, hc⟩ := hm w hw
    have h := IH w.1 w.2 records reads hinv
    unfold BalancedAt at h
    rw [hs, hc] at h
    rw [h]
  · simp [probOutput_eq_zero_of_not_mem_support hw]

/-- A step that reads one deterministic value `g ω` of the table and logs it in the view. -/
theorem balancedAt_observe {R A : Type} [Fintype A] [DecidableEq A] {oa : OracleComp (LocalSpec C + TprfSpec C) Bool}
    {step : Bool → StateT (SymState C × Bool) ProbComp R} {cont : R → OracleComp (LocalSpec C + TprfSpec C) Bool}
    (hoa : ∀ b p, symP prims seeds pairKeys parameter b oa p = Pr[fun z => z.1 = true | (step b).run p >>= fun z =>
      (simulateQ (symImpl prims seeds pairKeys b parameter) (cont z.1)).run z.2])
    (IH : ∀ u, Balanced prims seeds pairKeys parameter (cont u)) {v : SymState C × Bool} {records reads}
    (g : (Slot C → HashOutput) → A) (u : A → R) (v' : A → SymState C × Bool)
    (records' : A → List (EvalRecord C)) (reads' : A → List (Slot C × HashOutput))
    (hstep : ∀ b ω, (step b).run (conc v ω) = pure (u (g ω), conc (v' (g ω)) ω))
    (hinv : ∀ a, ViewInv (v' a) (records' a) (reads' a))
    (hchal : ∀ a, chalSet (v' a) = chalSet v ∧ chalValue (v' a) = chalValue v)
    (hcons : ∀ a ch c ω, Consistent (records' a) (reads' a) ch c ω ↔ Consistent records reads ch c ω ∧ g ω = a) :
    BalancedAt prims seeds pairKeys parameter oa v records reads := by
  have hP : ∀ b ω, symP prims seeds pairKeys parameter b oa (conc v ω) =
      symP prims seeds pairKeys parameter b (cont (u (g ω))) (conc (v' (g ω)) ω) := fun b ω => by
    rw [hoa, hstep, pure_bind]
    rfl
  have hsplit : ∀ b ch, ∑ ω ∈ univ.filter (Consistent records reads ch (chalValue v)),
      symP prims seeds pairKeys parameter b oa (conc v ω) = ∑ a, ∑ ω ∈ univ.filter (Consistent (records' a) (reads' a) ch
        (chalValue (v' a))), symP prims seeds pairKeys parameter b (cont (u a)) (conc (v' a) ω) := fun b ch => by
    rw [← Finset.sum_fiberwise (univ.filter (Consistent records reads ch (chalValue v))) g]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun ω _ => by rw [hcons, (hchal a).2]) fun ω hω => ?_
    have hg := ((hcons a _ _ ω).mp (Finset.mem_filter.mp hω).2).2
    rw [hP, hg]
  unfold BalancedAt
  rw [hsplit, hsplit, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := IH (u a) (v' a) (records' a) (reads' a) (hinv a)
  unfold BalancedAt at h
  rw [(hchal a).1] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- A challenge at a new point. For `b = false` it reads `prfSum ω x`, and for `b = true` it
samples a uniform value. Each answer adds the point to the challenged points. -/
theorem balancedAt_challenge_new {R : Type} {oa : OracleComp (LocalSpec C + TprfSpec C) Bool}
    {step : Bool → StateT (SymState C × Bool) ProbComp R} {cont : R → OracleComp (LocalSpec C + TprfSpec C) Bool}
    (hoa : ∀ b p, symP prims seeds pairKeys parameter b oa p = Pr[fun z => z.1 = true | (step b).run p >>= fun z =>
      (simulateQ (symImpl prims seeds pairKeys b parameter) (cont z.1)).run z.2])
    (IH : ∀ u, Balanced prims seeds pairKeys parameter (cont u)) {v : SymState C × Bool} {records reads}
    (x : Point) (hx : x ∉ chalSet v) (u : Digest → R) (v' : Digest → SymState C × Bool)
    (hstepF : ∀ ω, (step false).run (conc v ω) = pure (u (prfDigest ω x), conc (v' (prfDigest ω x)) ω))
    (mq : ProbComp Digest) (hmq : ∀ d, Pr[= d | mq] = ((2 : ℝ≥0∞) ^ digestBits)⁻¹)
    (hstepT : ∀ ω, (step true).run (conc v ω) = (fun d => (u d, conc (v' d) ω)) <$> mq)
    (hinv : ∀ d, ViewInv (v' d) records reads)
    (hchal : ∀ d, chalSet (v' d) = insert x (chalSet v) ∧
      chalValue (v' d) = Function.update (chalValue v) x (toXor d)) :
    BalancedAt prims seeds pairKeys parameter oa v records reads := by
  have hK0 : (2 : ℝ≥0∞) ^ digestBits ≠ 0 := by simp
  have hKt : (2 : ℝ≥0∞) ^ digestBits ≠ ⊤ := by simp
  have hPF : ∀ ω, symP prims seeds pairKeys parameter false oa (conc v ω) =
      symP prims seeds pairKeys parameter false (cont (u (prfDigest ω x))) (conc (v' (prfDigest ω x)) ω) := fun ω => by
    rw [hoa, hstepF, pure_bind]
    rfl
  have hPT : ∀ ω, symP prims seeds pairKeys parameter true oa (conc v ω) =
      ∑ d : Digest, ((2 : ℝ≥0∞) ^ digestBits)⁻¹ * symP prims seeds pairKeys parameter true (cont (u d)) (conc (v' d) ω) := fun ω => by
    rw [hoa, hstepT, bind_map_left, probEvent_bind_eq_tsum, tsum_fintype]
    exact Finset.sum_congr rfl fun d _ => by rw [hmq]; rfl
  have hcons : ∀ (d : Digest) ω, Consistent records reads (chalSet (v' d)) (chalValue (v' d)) ω ↔
      Consistent records reads (chalSet v) (chalValue v) ω ∧ prfDigest ω x = d := fun d ω => by
    rw [(hchal d).1, (hchal d).2]
    simp only [Consistent, Finset.mem_insert, forall_eq_or_imp, Function.update_self]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨⟨h1, h2, fun y hy => ?_⟩, h3⟩
      rw [h4 y hy, Function.update_of_ne (by rintro rfl; exact hx hy)]
    · rintro ⟨⟨h1, h2, h4⟩, h3⟩
      refine ⟨h1, h2, h3, fun y hy => ?_⟩
      rw [h4 y hy, Function.update_of_ne (by rintro rfl; exact hx hy)]
  unfold BalancedAt
  simp only [hPF, hPT]
  rw [← Finset.sum_fiberwise (κ := Digest) (univ.filter (Consistent records reads (chalSet v) (chalValue v)))
    (fun ω => prfDigest ω x), Finset.sum_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h := IH (u d) (v' d) records reads (hinv d)
  unfold BalancedAt at h
  rw [(hchal d).1, Finset.card_insert_of_notMem hx, pow_succ] at h
  rw [← Finset.mul_sum]
  have hfilter : (univ.filter (Consistent records reads (chalSet v) (chalValue v))).filter
      (fun ω => prfDigest ω x = d) =
      univ.filter (Consistent records reads (chalSet (v' d)) (chalValue (v' d))) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun ω _ => (hcons d ω).symm
  have hempty : univ.filter (Consistent records reads ∅ (chalValue (v' d))) =
      univ.filter (Consistent records reads ∅ (chalValue v)) :=
    Finset.filter_congr fun ω _ => consistent_empty_iff _ _ _ _ _
  rw [hempty] at h
  rw [hfilter, (hchal d).1]
  refine Eq.trans ?_ (congrArg (((2 : ℝ≥0∞) ^ digestBits)⁻¹ * ·) h)
  have hsum : ∀ ω ∈ univ.filter (Consistent records reads (insert x (chalSet v)) (chalValue (v' d))),
      symP prims seeds pairKeys parameter false (cont (u (prfDigest ω x))) (conc (v' (prfDigest ω x)) ω) =
        symP prims seeds pairKeys parameter false (cont (u d)) (conc (v' d) ω) := fun ω hω => by
    rw [← (hchal d).1] at hω
    rw [((hcons d ω).mp (Finset.mem_filter.mp hω).2).2]
  rw [Finset.sum_congr rfl hsum]
  exact ennreal_mul_cancel _ _ _ hK0 hKt

/-- A challenge at a point that is already challenged repeats the answer. -/
theorem balancedAt_challenge_old {R : Type} {oa : OracleComp (LocalSpec C + TprfSpec C) Bool}
    {step : Bool → StateT (SymState C × Bool) ProbComp R} {cont : R → OracleComp (LocalSpec C + TprfSpec C) Bool}
    (hoa : ∀ b p, symP prims seeds pairKeys parameter b oa p = Pr[fun z => z.1 = true | (step b).run p >>= fun z =>
      (simulateQ (symImpl prims seeds pairKeys b parameter) (cont z.1)).run z.2])
    (IH : ∀ u, Balanced prims seeds pairKeys parameter (cont u)) {v : SymState C × Bool} {records reads}
    (x : Point) (hx : x ∈ chalSet v) (u : Digest → R) (v' : Digest → SymState C × Bool)
    (hstepF : ∀ ω, (step false).run (conc v ω) = pure (u (prfDigest ω x), conc (v' (prfDigest ω x)) ω))
    (hstepT : ∀ ω, (step true).run (conc v ω) = pure (u (chalValue v x), conc (v' (chalValue v x)) ω))
    (hinv : ViewInv (v' (chalValue v x)) records reads)
    (hchal : chalSet (v' (chalValue v x)) = chalSet v ∧ chalValue (v' (chalValue v x)) = chalValue v) :
    BalancedAt prims seeds pairKeys parameter oa v records reads := by
  have h := IH (u (chalValue v x)) (v' (chalValue v x)) records reads hinv
  unfold BalancedAt at h ⊢
  rw [hchal.1, hchal.2] at h
  have hF : ∀ ω ∈ univ.filter (Consistent records reads (chalSet v) (chalValue v)),
      symP prims seeds pairKeys parameter false oa (conc v ω) =
        symP prims seeds pairKeys parameter false (cont (u (chalValue v x))) (conc (v' (chalValue v x)) ω) := fun ω hω => by
    rw [hoa, hstepF, pure_bind, show prfDigest ω x = chalValue v x from (Finset.mem_filter.mp hω).2.2.2 x hx]
    rfl
  have hT : ∀ ω, symP prims seeds pairKeys parameter true oa (conc v ω) =
      symP prims seeds pairKeys parameter true (cont (u (chalValue v x))) (conc (v' (chalValue v x)) ω) := fun ω => by
    rw [hoa, hstepT, pure_bind]
    rfl
  rw [Finset.sum_congr rfl hF, Finset.sum_congr rfl fun ω _ => hT ω]
  exact h

theorem balanced_pure (a : Bool) : Balanced prims seeds pairKeys parameter (pure a) := by
  intro v records reads hv
  unfold BalancedAt
  have hP : ∀ b p, symP prims seeds pairKeys parameter b (pure a) p = if a = true then 1 else 0 := fun b p => by
    simp [symP]
  simp only [hP, Finset.sum_const, nsmul_eq_mul]
  by_cases hc : chalSet v = ∅
  · have hf : univ.filter (Consistent records reads (chalSet v) (chalValue v)) =
        univ.filter (Consistent records reads ∅ (chalValue v)) := by rw [hc]
    rw [hf, hc, Finset.card_empty, pow_zero, mul_one]
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hc
  have hD : v.1.1.1.corrupt.card ≤ C.t - 1 :=
    (Finset.card_le_card Finset.subset_union_left).trans (hv.1 x₀ hx₀ 0)
  obtain ⟨T, hDT, hT⟩ := Finset.exists_superset_card_eq hD (by simp [Committee.n]; omega)
  have hinv : ∀ x ∈ chalSet v, ∀ ec, (v.1.1.1.corrupt ∪ recordQueriers records x ec).card ≤ C.t - 1 :=
    fun x hx ec => by rw [← hv.2.1]; exact hv.1 x hx ec
  have h := card_consistent_mul (Tstar := ⟨T, hT⟩) hDT hinv reads hv.2.2.1 (chalValue v)
  rw [mul_comm, ← mul_assoc, mul_comm _ (_ : ℝ≥0∞), ← h]
  push_cast
  ring

/-- The full slot cache of the table `ω`. -/
def fullTable (ω : Slot C → HashOutput) : SlotCache C := fun s => some (ω s)

theorem toXor_foldl_id (a : Digest) (l : List Digest) :
    toXor (l.foldl (· ^^^ ·) a) = toXor a + (l.map toXor).sum :=
  toXor_foldl_map id a l

theorem slotOracle_run_full (ω : Slot C → HashOutput) (s : Slot C) :
    (slotOracle s).run (fullTable ω) = pure (ω s, fullTable ω) :=
  QueryImpl.withCaching_run_some _ rfl

theorem mapM_run_of_pure {σ α β : Type} (l : List α) (f : α → StateT σ ProbComp β) (g : α → β) (c : σ)
    (h : ∀ a ∈ l, (f a).run c = pure (g a, c)) : (l.mapM f).run c = pure (l.map g, c) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.mapM_cons, StateT.run_bind, h a (List.mem_cons_self ..), pure_bind,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb), StateT.run_pure, List.map_cons]

theorem sum_terms_filter (S : Finset C.Term) (f : C.Term → XorDigest) :
    ((C.terms.filter (· ∈ S)).map f).sum = ∑ T ∈ S, f T := by
  have hl : (C.terms.filter (· ∈ S)).Nodup := (Finset.nodup_toList _).filter _
  rw [← List.sum_toFinset f hl]
  congr 1
  ext T
  simp [Committee.terms]

theorem sum_parties_filter (P : C.Party → Prop) [DecidablePred P] (f : C.Party → XorDigest) :
    ((C.parties.filter fun j => decide (P j)).map f).sum = ∑ j ∈ univ.filter P, f j := by
  have hl : (C.parties.filter fun j => decide (P j)).Nodup := (List.nodup_finRange _).filter _
  rw [← List.sum_toFinset f hl]
  congr 1
  ext j
  simp [Committee.parties]

theorem evalSlots_run_full (ω : Slot C → HashOutput) (c : HashCache C) (i : C.Party) (J : C.Quorum) (x : Point)
    (ec : Message) : (evalSlots i J x ec).run (c, fullTable ω) =
      pure ((evalSum ω i J x ec : XorDigest), (c, fullTable ω)) := by
  simp only [evalSlots, onTable_run, StateT.run_bind]
  rw [mapM_run_of_pure _ _ (fun T => truncateHash (ω (.inl (T, x)))) _ fun T _ => by
    rw [StateT.run_map, slotOracle_run_full, map_pure]]
  simp only [pure_bind]
  rw [mapM_run_of_pure _ _ (fun j => if h : j = i then 0 else truncateHash (ω (.inr (C.pairOf i j (Ne.symm h),
    x, ec, J)))) _ fun j _ => by
      split_ifs
      · rfl
      · rw [StateT.run_map, slotOracle_run_full, map_pure]]
  simp only [pure_bind, StateT.run_pure, map_pure]
  congr 2
  change toXor _ = _
  rw [toXor_foldl_id, List.map_append, List.sum_append, List.map_map, List.map_map,
    show toXor (0 : Digest) = 0 from rfl, zero_add, evalSum]
  rw [← sum_terms_filter (L J i), ← sum_parties_filter (fun j => j ∈ J.1 ∧ j ≠ i)]
  congr 3

theorem prfSlots_run_full (ω : Slot C → HashOutput) (c : HashCache C) (x : Point) :
    (prfSlots x).run (c, fullTable ω) = pure ((prfSum ω x : XorDigest), (c, fullTable ω)) := by
  simp only [prfSlots, onTable_run, StateT.run_bind]
  rw [mapM_run_of_pure _ _ (fun T => truncateHash (ω (.inl (T, x)))) _ fun T _ => by
    rw [StateT.run_map, slotOracle_run_full, map_pure]]
  simp only [pure_bind, StateT.run_pure, map_pure]
  congr 2
  change toXor _ = _
  rw [toXor_foldl_id, List.map_map, show toXor (0 : Digest) = 0 from rfl, zero_add, prfSum]
  have h := sum_terms_filter (C := C) Finset.univ fun T => toXor (truncateHash (ω (.inl (T, x))))
  rw [List.filter_eq_self.mpr (fun T _ => by simp)] at h
  exact h

theorem routed_liftComp_run {α : Type} (p : ProbComp α) (y : HashCache C × SlotCache C) :
    (simulateQ (routedAnswer prims seeds pairKeys) (liftComp p (LocalSpec C))).run y = (fun a => (a, y)) <$> p := by
  induction p using OracleComp.inductionOn generalizing y with
  | pure a => simp
  | query_bind t k ih =>
    have hq : simulateQ (routedAnswer prims seeds pairKeys) (liftComp (liftM (unifSpec.query t) : ProbComp _) (LocalSpec C)) =
        routedAnswer prims seeds pairKeys (.inl t) := by
      rw [liftComp_query]
      exact (simulateQ_query _ _).trans (id_map _)
    have hr : (routedAnswer prims seeds pairKeys (.inl t)).run y =
        (fun a => (a, y)) <$> (liftM (unifSpec.query t) : ProbComp ((LocalSpec C).Range (.inl t))) := by
      obtain ⟨c, τ⟩ := y
      change (onCache (localAnswer prims (.inl t))).run (c, τ) = _
      rw [onCache_run, localAnswer_unif_run, Functor.map_map]
    rw [liftComp_bind, simulateQ_bind, StateT.run_bind, hq]
    erw [hr]
    simp only [map_bind, ih]
    erw [bind_map_left]

/-- The state `v` after a step to the game state `st` and the cache `c`. -/
def afterStep (v : SymState C × Bool) (t : (LocalSpec C + TprfSpec C).Domain) (st : TprfState C) (c : HashCache C) :
    SymState C × Bool :=
  (((st, c, getTable v), v.1.2 ∪ firedBy seeds pairKeys v.1.1.1.corrupt t), v.2 || hitFlag seeds pairKeys v.1.1.1.corrupt t)

theorem revealed_mono {D D' : Finset C.Party} (hD : D ⊆ D') {σ : KeySlot C} (h : Revealed D σ) : Revealed D' σ := by
  rcases σ with T | p
  · obtain ⟨i, hi, hT⟩ := h
    exact ⟨i, hD hi, hT⟩
  · rcases h with h | h
    · exact Or.inl (hD h)
    · exact Or.inr (hD h)

theorem addQuery_queried (st : TprfState C) (i : C.Party) (x : Point) (ec : Message) (x' : Point) (ec' : Message) :
    (addQuery st i x ec).queried x' ec' = if x' = x ∧ ec' = ec then insert i (st.queried x ec) else st.queried x' ec' := by
  simp only [addQuery]
  by_cases hx : x' = x
  · subst hx
    by_cases he : ec' = ec
    · subst he; simp
    · simp [he]
  · simp [hx]

theorem recordQueriers_append (records : List (EvalRecord C)) (e : EvalRecord C) (x : Point) (ec : Message) :
    recordQueriers (records ++ [e]) x ec =
      if e.x = x ∧ e.ec = ec then insert e.i (recordQueriers records x ec) else recordQueriers records x ec := by
  unfold recordQueriers
  split_ifs with h
  · ext j
    simp only [List.filter_append, List.map_append, List.toFinset_append, Finset.mem_union, Finset.mem_insert]
    simp [h, or_comm]
  · simp [List.filter_append, h]

theorem map_map_map_eq {α β γ δ ε : Type} (f : γ → δ) (g : β → γ) (h : α → β) (k : ε → δ) (l : α → ε)
    (X : ProbComp α) (hx : ∀ a, f (g (h a)) = k (l a)) : f <$> g <$> h <$> X = k <$> l <$> X := by
  simp only [Functor.map_map]
  exact congrArg (· <$> X) (funext hx)

theorem symImpl_run_eq (b : Bool) (t : (LocalSpec C + TprfSpec C).Domain) (v : SymState C × Bool)
    (ω : Slot C → HashOutput) : (symImpl prims seeds pairKeys b parameter t).run (conc v ω) =
      (fun z => (z.1, ((z.2, v.1.2 ∪ firedBy seeds pairKeys v.1.1.1.corrupt t),
        v.2 || hitFlag seeds pairKeys v.1.1.1.corrupt t))) <$>
        (symCore prims seeds pairKeys b parameter t).run (v.1.1.1, v.1.1.2.1, fullTable ω) := rfl

set_option maxRecDepth 10000 in
theorem symCore_challenge_run (b : Bool) (x : Point) (p : TprfState C × HashCache C × SlotCache C) :
    (symCore prims seeds pairKeys b parameter (.inr (.challenge x))).run p =
      if ∃ ec, C.t ≤ (p.1.corrupt ∪ p.1.queried x ec).card then pure (none, p)
      else (fun z => (some z.1, (addChallenge p.1 x z.1, z.2))) <$>
        (if b then (match p.1.random x with
            | some y => pure y
            | none => simulateQ (routedAnswer prims seeds pairKeys) (liftComp ($ᵗ Digest) _) :
              StateT (HashCache C × SlotCache C) ProbComp Digest).run p.2
          else (prfSlots x).run p.2) := by
  simp only [gameImplWith, StateT.run_mk]
  split_ifs <;> rfl

theorem viewInv_afterStep {v : SymState C × Bool} {records reads} (hv : ViewInv v records reads)
    (t : (LocalSpec C + TprfSpec C).Domain) (c : HashCache C) :
    ViewInv (afterStep seeds pairKeys v t v.1.1.1 c) records reads := hv

set_option maxRecDepth 10000 in
/-- The symbolic game on a full table gives the same weights for both `b`. -/
theorem balanced_simulateQ (oa : OracleComp (LocalSpec C + TprfSpec C) Bool) :
    Balanced prims seeds pairKeys parameter oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact balanced_pure prims seeds pairKeys parameter a
  | query_bind t cont ih =>
    intro v records reads hv
    have hoa : ∀ b p, symP prims seeds pairKeys parameter b
        ((liftM ((LocalSpec C + TprfSpec C).query t) : OracleComp (LocalSpec C + TprfSpec C) _) >>= cont) p =
        Pr[fun z => z.1 = true | (symImpl prims seeds pairKeys b parameter t).run p >>= fun z =>
          (simulateQ (symImpl prims seeds pairKeys b parameter) (cont z.1)).run z.2] := fun b p => by
      rw [symP, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with (n | u | y) | (i | ⟨i, J, x, ec⟩ | x)
    · refine balancedAt_indep prims seeds pairKeys parameter hoa ih
        ((fun a => (a, afterStep seeds pairKeys v (.inl (.inl n)) v.1.1.1 v.1.1.2.1)) <$>
          (liftM (unifSpec.query n) : ProbComp ((LocalSpec C).Range (.inl n)))) (fun b ω => ?_) fun w hw => ?_
      · rw [symImpl_run_eq]
        show (fun z => _) <$> ((fun z => (z.1, (v.1.1.1, z.2))) <$>
          (onCache (localAnswer prims (.inl n))).run (v.1.1.2.1, fullTable ω)) = _
        rw [onCache_run, localAnswer_unif_run]
        simp only [Functor.map_map]
        rfl
      · rw [support_map] at hw
        obtain ⟨a, -, rfl⟩ := hw
        exact ⟨hv, rfl, rfl⟩
    · by_cases hrev : ∃ s, Revealed v.1.1.1.corrupt (slotKey s) ∧ slotInput seeds pairKeys s = u
      · have hadv : symAdversary prims seeds pairKeys v.1.1.1.corrupt (.inr (.inl u)) =
            onTable (slotOracle hrev.choose) := by
          simp only [symAdversary, dif_pos hrev]
          rfl
        refine balancedAt_observe prims seeds pairKeys parameter hoa ih (A := HashOutput) (fun ω => ω hrev.choose) id
          (fun _ => afterStep seeds pairKeys v (.inl (.inr (.inl u))) v.1.1.1 v.1.1.2.1) (fun _ => records)
          (fun a => reads ++ [(hrev.choose, a)]) (fun b ω => ?_) (fun a => ?_) (fun a => ⟨rfl, rfl⟩)
          (fun a ch c ω => ?_)
        · rw [symImpl_run_eq]
          show (fun z => _) <$> ((fun z => (z.1, (v.1.1.1, z.2))) <$>
            (symAdversary prims seeds pairKeys v.1.1.1.corrupt (.inr (.inl u))).run (v.1.1.2.1, fullTable ω)) = _
          rw [hadv]
          erw [onTable_run, slotOracle_run_full]
          rfl
        · refine ⟨hv.1, hv.2.1, fun rd hrd => ?_, hv.2.2.2⟩
          rcases List.mem_append.mp hrd with hrd | hrd
          · exact hv.2.2.1 rd hrd
          · rw [List.mem_singleton.mp hrd]
            exact hrev.choose_spec.1
        · simp only [Consistent, List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
          tauto
      · have hadv : symAdversary prims seeds pairKeys v.1.1.1.corrupt (.inr (.inl u)) =
            onCache (hashAnswer prims u) := by
          simp only [symAdversary, dif_neg hrev]
          rfl
        refine balancedAt_indep prims seeds pairKeys parameter hoa ih
          ((fun z => (z.1, afterStep seeds pairKeys v (.inl (.inr (.inl u))) v.1.1.1 z.2)) <$>
            (hashAnswer prims u).run v.1.1.2.1) (fun b ω => ?_) fun w hw => ?_
        · rw [symImpl_run_eq]
          show (fun z => _) <$> ((fun z => (z.1, (v.1.1.1, z.2))) <$>
            (symAdversary prims seeds pairKeys v.1.1.1.corrupt (.inr (.inl u))).run (v.1.1.2.1, fullTable ω)) = _
          rw [hadv]
          erw [onCache_run]
          exact map_map_map_eq _ _ _ _ _ _ fun _ => rfl
        · rw [support_map] at hw
          obtain ⟨a, -, rfl⟩ := hw
          exact ⟨hv, rfl, rfl⟩
    · refine balancedAt_indep prims seeds pairKeys parameter hoa ih
        ((fun z => (z.1, afterStep seeds pairKeys v (.inl (.inr (.inr y))) v.1.1.1 z.2)) <$>
          (localAnswer prims (.inr (.inr y))).run v.1.1.2.1) (fun b ω => ?_) fun w hw => ?_
      · rw [symImpl_run_eq]
        show (fun z => _) <$> ((fun z => (z.1, (v.1.1.1, z.2))) <$>
          (onCache (localAnswer prims (.inr (.inr y)))).run (v.1.1.2.1, fullTable ω)) = _
        erw [onCache_run]
        exact map_map_map_eq _ _ _ _ _ _ fun _ => rfl
      · rw [support_map] at hw
        obtain ⟨a, -, rfl⟩ := hw
        exact ⟨hv, rfl, rfl⟩
    · by_cases hc : ∃ x ∈ v.1.1.1.challenged, ∃ ec, C.t ≤ (v.1.1.1.corrupt ∪ v.1.1.1.queried x ec ∪ {i}).card
      · refine balancedAt_indep prims seeds pairKeys parameter hoa ih
          (pure (none, afterStep seeds pairKeys v (.inr (.corrupt i)) v.1.1.1 v.1.1.2.1)) (fun b ω => ?_) fun w hw => ?_
        · rw [symImpl_run_eq]
          show (fun z => _) <$> (if ∃ x ∈ v.1.1.1.challenged, ∃ ec, C.t ≤
            (v.1.1.1.corrupt ∪ v.1.1.1.queried x ec ∪ {i}).card then _ else _) = _
          rw [if_pos hc]
          rfl
        · obtain rfl := (mem_support_pure_iff _ _).mp hw
          exact ⟨hv, rfl, rfl⟩
      · refine balancedAt_indep prims seeds pairKeys parameter hoa ih
          (pure (some (dealtKeys parameter seeds pairKeys i), afterStep seeds pairKeys v (.inr (.corrupt i))
            { v.1.1.1 with corrupt := insert i v.1.1.1.corrupt } v.1.1.2.1)) (fun b ω => ?_) fun w hw => ?_
        · rw [symImpl_run_eq]
          show (fun z => _) <$> (if ∃ x ∈ v.1.1.1.challenged, ∃ ec, C.t ≤
            (v.1.1.1.corrupt ∪ v.1.1.1.queried x ec ∪ {i}).card then _ else _) = _
          rw [if_neg hc]
          rfl
        · obtain rfl := (mem_support_pure_iff _ _).mp hw
          push Not at hc
          refine ⟨⟨fun x hx ec => ?_, hv.2.1, fun rd hrd => revealed_mono (Finset.subset_insert _ _)
            (hv.2.2.1 rd hrd), hv.2.2.2⟩, rfl, rfl⟩
          have h1 := hc x hx ec
          have e : v.1.1.1.corrupt ∪ v.1.1.1.queried x ec ∪ {i} = insert i v.1.1.1.corrupt ∪ v.1.1.1.queried x ec := by
            ext j; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
          rw [e] at h1
          show (insert i v.1.1.1.corrupt ∪ v.1.1.1.queried x ec).card ≤ C.t - 1
          omega
    · by_cases hc : i ∉ J.1 ∨ (C.t ≤ (v.1.1.1.corrupt ∪ v.1.1.1.queried x ec ∪ {i}).card ∧ x ∈ v.1.1.1.challenged)
      · refine balancedAt_indep prims seeds pairKeys parameter hoa ih
          (pure (none, afterStep seeds pairKeys v (.inr (.eval i J x ec)) v.1.1.1 v.1.1.2.1)) (fun b ω => ?_) fun w hw => ?_
        · rw [symImpl_run_eq]
          show (fun z => _) <$> (if i ∉ J.1 ∨ (C.t ≤ (v.1.1.1.corrupt ∪ v.1.1.1.queried x ec ∪ {i}).card ∧
            x ∈ v.1.1.1.challenged) then _ else _) = _
          rw [if_pos hc]
          rfl
        · obtain rfl := (mem_support_pure_iff _ _).mp hw
          exact ⟨hv, rfl, rfl⟩
      · refine balancedAt_observe prims seeds pairKeys parameter hoa ih (A := Digest)
          (fun ω => (evalSum ω i J x ec : XorDigest)) some
          (fun _ => afterStep seeds pairKeys v (.inr (.eval i J x ec)) (addQuery v.1.1.1 i x ec) v.1.1.2.1)
          (fun a => records ++ [⟨i, J, x, ec, toXor a⟩]) (fun _ => reads) (fun b ω => ?_) (fun a => ?_)
          (fun a => ⟨rfl, rfl⟩) (fun a ch c ω => ?_)
        · rw [symImpl_run_eq]
          show (fun z => _) <$> (if i ∉ J.1 ∨ (C.t ≤ (v.1.1.1.corrupt ∪ v.1.1.1.queried x ec ∪ {i}).card ∧
            x ∈ v.1.1.1.challenged) then _ else _) = _
          rw [if_neg hc]
          erw [evalSlots_run_full]
          rfl
        · refine ⟨fun x' hx' ec' => ?_, fun x' ec' => ?_, hv.2.2.1, hv.2.2.2⟩
          · show (v.1.1.1.corrupt ∪ (addQuery v.1.1.1 i x ec).queried x' ec').card ≤ C.t - 1
            rw [addQuery_queried]
            split_ifs with h
            · obtain ⟨rfl, rfl⟩ := h
              have h3 : ¬(C.t ≤ (v.1.1.1.corrupt ∪ v.1.1.1.queried x' ec' ∪ {i}).card ∧ x' ∈ v.1.1.1.challenged) :=
                fun h => hc (Or.inr h)
              have := Nat.lt_of_not_le fun h => h3 ⟨h, hx'⟩
              have e : v.1.1.1.corrupt ∪ v.1.1.1.queried x' ec' ∪ {i} =
                  v.1.1.1.corrupt ∪ insert i (v.1.1.1.queried x' ec') := by
                ext j; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
              rw [e] at this
              omega
            · exact hv.1 x' hx' ec'
          · show (addQuery v.1.1.1 i x ec).queried x' ec' = _
            rw [addQuery_queried, recordQueriers_append]
            simp only [eq_comm (a := x), eq_comm (a := ec)]
            split_ifs with h
            · obtain ⟨rfl, rfl⟩ := h
              rw [hv.2.1]
            · exact hv.2.1 x' ec'
        · simp only [Consistent, List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3, h4⟩
            exact ⟨⟨h1, h3, h4⟩, h2⟩
          · rintro ⟨⟨h1, h3, h4⟩, h2⟩
            exact ⟨⟨h1, h2⟩, h3, h4⟩
    · by_cases hc : ∃ ec, C.t ≤ (v.1.1.1.corrupt ∪ v.1.1.1.queried x ec).card
      · refine balancedAt_indep prims seeds pairKeys parameter hoa ih
          (pure (none, afterStep seeds pairKeys v (.inr (.challenge x)) v.1.1.1 v.1.1.2.1)) (fun b ω => ?_) fun w hw => ?_
        · rw [symImpl_run_eq]
          show (fun z => _) <$> (if ∃ ec, C.t ≤ (v.1.1.1.corrupt ∪ v.1.1.1.queried x ec).card then _ else _) = _
          rw [if_pos hc]
          rfl
        · obtain rfl := (mem_support_pure_iff _ _).mp hw
          exact ⟨hv, rfl, rfl⟩
      have hxq : ∀ ec, (v.1.1.1.corrupt ∪ v.1.1.1.queried x ec).card ≤ C.t - 1 := fun ec => by
        have := Nat.lt_of_not_le fun h => hc ⟨ec, h⟩
        omega
      have hinv : ∀ d, ViewInv (afterStep seeds pairKeys v (.inr (.challenge x)) (addChallenge v.1.1.1 x d) v.1.1.2.1)
          records reads := fun d => by
        refine ⟨fun x' hx' ec => ?_, hv.2.1, hv.2.2.1, fun x' => ?_⟩
        · show (v.1.1.1.corrupt ∪ v.1.1.1.queried x' ec).card ≤ C.t - 1
          rcases Finset.mem_insert.mp hx' with rfl | hx'
          · exact hxq ec
          · exact hv.1 x' hx' ec
        · show x' ∈ insert x v.1.1.1.challenged ↔ (Function.update v.1.1.1.random x (some d) x').isSome
          by_cases hx : x' = x
          · subst hx; simp
          · rw [Finset.mem_insert, Function.update_of_ne hx, hv.2.2.2]
            simp [hx]
      have hstepF : ∀ ω, (symImpl prims seeds pairKeys false parameter (.inr (.challenge x))).run (conc v ω) =
          pure (some (prfDigest ω x), conc (afterStep seeds pairKeys v (.inr (.challenge x))
            (addChallenge v.1.1.1 x (prfDigest ω x)) v.1.1.2.1) ω) := fun ω => by
        rw [symImpl_run_eq]
        show (fun z => _) <$> (if ∃ ec, C.t ≤ (v.1.1.1.corrupt ∪ v.1.1.1.queried x ec).card then _ else _) = _
        rw [if_neg hc]
        erw [prfSlots_run_full]
        rfl
      by_cases hx : x ∈ chalSet v
      · obtain ⟨y₀, hy₀⟩ := Option.isSome_iff_exists.mp ((hv.2.2.2 x).mp hx)
        have hcv : chalValue v x = toXor y₀ := by simp [chalValue, hy₀]
        refine balancedAt_challenge_old prims seeds pairKeys parameter hoa ih x hx some
          (fun d => afterStep seeds pairKeys v (.inr (.challenge x)) (addChallenge v.1.1.1 x d) v.1.1.2.1) hstepF
          (fun ω => ?_) (hinv _) ⟨?_, ?_⟩
        · rw [symImpl_run_eq, symCore_challenge_run]
          simp only [if_neg hc, if_true, hy₀, hcv]
          rfl
        · exact Finset.insert_eq_of_mem hx
        · funext z
          by_cases hz : z = x
          · subst hz
            simp [chalValue, addChallenge, afterStep, hy₀]
            rfl
          · simp [chalValue, addChallenge, afterStep, Function.update_of_ne hz]
      · have hnone : v.1.1.1.random x = none := by
          by_contra h
          exact hx ((hv.2.2.2 x).mpr (Option.ne_none_iff_isSome.mp h))
        refine balancedAt_challenge_new prims seeds pairKeys parameter hoa ih x hx some
          (fun d => afterStep seeds pairKeys v (.inr (.challenge x)) (addChallenge v.1.1.1 x d) v.1.1.2.1) hstepF
          ($ᵗ Digest) (fun d => ?_) (fun ω => ?_) hinv fun d => ⟨rfl, ?_⟩
        · rw [probOutput_uniformSample]
          simp
        · rw [symImpl_run_eq, symCore_challenge_run]
          simp only [if_neg hc, if_true, hnone]
          erw [routed_liftComp_run]
          exact map_map_map_eq _ _ _ _ _ _ fun _ => rfl
        · funext z
          by_cases hz : z = x
          · subst hz
            simp [chalValue, addChallenge, afterStep]
          · simp [chalValue, addChallenge, afterStep, Function.update_of_ne hz]

theorem fillSlots_of_mem (ω : Slot C → HashOutput) (l : List (Slot C)) (c : SlotCache C) {s : Slot C} (hs : s ∈ l) :
    fillSlots ω l c s = some (ω s) := by
  induction l with
  | nil => simp at hs
  | cons a l ih =>
    simp only [fillSlots]
    by_cases hsa : s = a
    · subst hsa; rw [QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ hsa]
      exact ih ((List.mem_cons.mp hs).resolve_left hsa)

/-- The symbolic game is the average of the symbolic game on a full table. -/
theorem symbolic_eq_average (b : Bool) (A : OracleComp (LocalSpec C + TprfSpec C) Bool) :
    Pr[fun z => z.1 = true | (simulateQ (symImpl prims seeds pairKeys b parameter) A).run symInit] =
      ∑ ω : Slot C → HashOutput, (Fintype.card (Slot C → HashOutput) : ℝ≥0∞)⁻¹ *
        symP prims seeds pairKeys parameter b A (conc symInit ω) := by
  have h := presample_symImpl prims seeds pairKeys b parameter A (Finset.univ : Finset (Slot C)).toList
    (Finset.nodup_toList _) symInit fun _ _ => rfl
  have hfill : ∀ ω, setTable symInit (fillSlots ω (Finset.univ : Finset (Slot C)).toList (getTable symInit)) =
      conc symInit ω := fun ω => by
    simp only [conc]
    congr 1
    funext s
    exact fillSlots_of_mem ω _ _ (Finset.mem_toList.mpr (Finset.mem_univ s))
  simp only [hfill] at h
  have e1 : ∀ p, Pr[fun z => z.1 = true | (simulateQ (symImpl prims seeds pairKeys b parameter) A).run p] =
      Pr[= true | (simulateQ (symImpl prims seeds pairKeys b parameter) A).run' p] := fun p => by
    rw [StateT.run'_eq, ← probEvent_eq_eq_probOutput, probEvent_map]
    rfl
  rw [e1, ← evalDist_ext_iff.mp h true, probOutput_bind_eq_tsum, tsum_fintype]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [probOutput_uniformSample, symP, e1]

theorem viewInv_init : ViewInv (C := C) symInit [] [] :=
  ⟨fun x hx => by simp [symInit, tprfInit] at hx, fun x ec => rfl, by simp, fun x => by simp [symInit, tprfInit]⟩

set_option maxRecDepth 10000 in
/-- `hsymbolic`. The symbolic game does not depend on `b`. -/
theorem symbolic_balanced (A : OracleComp (LocalSpec C + TprfSpec C) Bool) :
    Pr[fun z => z.1 = true | (simulateQ (symImpl prims seeds pairKeys true parameter) A).run symInit] =
      Pr[fun z => z.1 = true | (simulateQ (symImpl prims seeds pairKeys false parameter) A).run symInit] := by
  rw [symbolic_eq_average, symbolic_eq_average, ← Finset.mul_sum, ← Finset.mul_sum]
  refine congrArg _ ?_
  have h : BalancedAt prims seeds pairKeys parameter A symInit [] [] :=
    balanced_simulateQ prims seeds pairKeys parameter A symInit [] [] viewInv_init
  unfold BalancedAt at h
  have hc : chalSet (C := C) symInit = ∅ := rfl
  have huniv : ∀ c : Point → XorDigest, univ.filter (Consistent (C := C) [] [] ∅ c) = univ := fun c =>
    Finset.filter_true_of_mem fun ω _ => by simp [Consistent]
  simp only [hc, Finset.card_empty, pow_zero, mul_one, huniv] at h
  exact h.symm

end Balanced

/-! ## The bad event of the symbolic game -/

section Bad

/-- The seeds with the key `σ` set to `k`. -/
def updSeeds (σ : KeySlot C) (k : HashOutput) (seeds : C.Term → HashOutput) : C.Term → HashOutput :=
  match σ with
  | .inl T => Function.update seeds T k
  | .inr _ => seeds

/-- The pair keys with the key `σ` set to `k`. -/
def updPairs (σ : KeySlot C) (k : HashOutput) (pairKeys : C.Pair → HashOutput) : C.Pair → HashOutput :=
  match σ with
  | .inl _ => pairKeys
  | .inr p => Function.update pairKeys p k

/-- A query of `H` with the key `k` in the domain of the key `σ`. -/
def HitQuery (σ : KeySlot C) (u : Query C) (k : HashOutput) : Prop :=
  match σ with
  | .inl _ => ∃ x, u = .prf k x
  | .inr _ => ∃ x m J, u = .mask k x m J

theorem slotInput_upd_of_ne {σ : KeySlot C} {s : Slot C} (h : slotKey s ≠ σ) (k : HashOutput) :
    slotInput (updSeeds σ k seeds) (updPairs σ k pairKeys) s = slotInput seeds pairKeys s := by
  rcases s with ⟨T, x⟩ | ⟨p, x, m, J⟩ <;> rcases σ with T' | p' <;>
    simp_all [slotInput, slotKey, updSeeds, updPairs, Function.update_of_ne]

theorem exists_slot_iff_hitQuery (σ : KeySlot C) (u : Query C) (k : HashOutput) :
    (∃ s, slotKey s = σ ∧ slotInput (updSeeds σ k seeds) (updPairs σ k pairKeys) s = u) ↔ HitQuery σ u k := by
  rcases σ with T | p
  · constructor
    · rintro ⟨⟨T', x⟩ | ⟨p, x, m, J⟩, hs, rfl⟩
      · simp only [slotKey, Sum.inl.injEq] at hs
        subst hs
        exact ⟨x, by simp [slotInput, updSeeds]⟩
      · simp [slotKey] at hs
    · rintro ⟨x, rfl⟩
      exact ⟨.inl (T, x), rfl, by simp [slotInput, updSeeds]⟩
  · constructor
    · rintro ⟨⟨T, x⟩ | ⟨p', x, m, J⟩, hs, rfl⟩
      · simp [slotKey] at hs
      · simp only [slotKey, Sum.inr.injEq] at hs
        subst hs
        exact ⟨x, m, J, by simp [slotInput, updPairs]⟩
    · rintro ⟨x, m, J, rfl⟩
      exact ⟨.inr (p, x, m, J), rfl, by simp [slotInput, updPairs]⟩

theorem hitQuery_unique {σ : KeySlot C} {u : Query C} {k k' : HashOutput} (h : HitQuery σ u k)
    (h' : HitQuery σ u k') : k = k' := by
  rcases σ with T | p
  · obtain ⟨x, rfl⟩ := h
    obtain ⟨x', h'⟩ := h'
    simp only [Query.prf.injEq] at h'
    exact h'.1
  · obtain ⟨x, m, J, rfl⟩ := h
    obtain ⟨x', m', J', h'⟩ := h'
    simp only [Query.mask.injEq] at h'
    exact h'.1

set_option maxRecDepth 10000 in
theorem gameImplWith_corrupt_mono {σ' : Type}
    (adversary : Finset C.Party → QueryImpl (LocalSpec C) (StateT σ' ProbComp))
    (evalH : C.Party → C.Quorum → Point → Message → StateT σ' ProbComp Digest)
    (prfH : Point → StateT σ' ProbComp Digest) (sampleH : StateT σ' ProbComp Digest) (b : Bool)
    (keys : C.Party → Keys C) (t : (LocalSpec C + TprfSpec C).Domain) (p : TprfState C × σ') :
    ∀ z ∈ support ((gameImplWith adversary evalH prfH sampleH b keys t).run p), p.1.corrupt ⊆ z.2.1.corrupt := by
  intro z hz
  rcases t with t | (i | ⟨i, J, y, ec⟩ | y)
  · simp only [gameImplWith, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact subset_rfl
  · simp only [gameImplWith, StateT.run_mk] at hz
    split_ifs at hz <;> simp only [support_pure, Set.mem_singleton_iff] at hz <;> subst hz
    · exact subset_rfl
    · exact Finset.subset_insert _ _
  · simp only [gameImplWith, StateT.run_mk] at hz
    split_ifs at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact subset_rfl
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, -, rfl⟩ := hz
      exact subset_rfl
  · simp only [gameImplWith, StateT.run_mk] at hz
    split_ifs at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact subset_rfl
    all_goals simp only [support_map, Set.mem_image] at hz; obtain ⟨w, -, rfl⟩ := hz; exact subset_rfl

/-- A key that is revealed and not hit stays so. -/
theorem symImpl_revealed_stays (b : Bool) (parameter : PublicParameter) (σ : KeySlot C)
    (t : (LocalSpec C + TprfSpec C).Domain) (p : SymState C × Bool) (hr : Revealed p.1.1.1.corrupt σ)
    (hσ : σ ∉ p.1.2) : ∀ z ∈ support ((symImpl prims seeds pairKeys b parameter t).run p),
      Revealed z.2.1.1.1.corrupt σ ∧ σ ∉ z.2.1.2 := by
  intro z hz
  simp only [symImpl, withFired, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  refine ⟨revealed_mono (gameImplWith_corrupt_mono _ _ _ _ b _ t _ w hw) hr, ?_⟩
  simp only [Finset.mem_union, not_or]
  refine ⟨hσ, fun h => ?_⟩
  rcases t with ((n | u | y) | q)
  · simp [firedBy] at h
  · simp only [firedBy, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h.1 hr
  · simp [firedBy] at h
  · simp [firedBy] at h

theorem probEvent_revealed_stays (b : Bool) (parameter : PublicParameter) (σ : KeySlot C) {α : Type}
    (oa : OracleComp (LocalSpec C + TprfSpec C) α) (p : SymState C × Bool) (hr : Revealed p.1.1.1.corrupt σ)
    (hσ : σ ∉ p.1.2) : Pr[fun z => σ ∈ z.2.1.2 | (simulateQ (symImpl prims seeds pairKeys b parameter) oa).run p] = 0 := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure a => simp [hσ]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind]
    rw [probEvent_bind_eq_tsum]
    refine ENNReal.tsum_eq_zero.mpr fun z => ?_
    by_cases hz : z ∈ support ((symImpl prims seeds pairKeys b parameter t).run p)
    · obtain ⟨h1, h2⟩ := symImpl_revealed_stays prims seeds pairKeys b parameter σ t p hr hσ z hz
      rw [ih z.1 z.2 h1 h2, mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul]

theorem choose_congr {α : Type} {P Q : α → Prop} (h : P = Q) (h₁ : ∃ a, P a) (h₂ : ∃ a, Q a) :
    h₁.choose = h₂.choose := by
  subst h; rfl

theorem pairOf_self_mem {i j : C.Party} (h : i ≠ j) : (C.pairOf i j h).1.1 = i ∨ (C.pairOf i j h).1.2 = i := by
  unfold Committee.pairOf; split_ifs <;> simp

/-- The adversary hits the key `σ` with the value `k`. -/
def Hit (σ : KeySlot C) (t : (LocalSpec C + TprfSpec C).Domain) (k : HashOutput) : Prop :=
  ∃ u, t = .inl (.inr (.inl u)) ∧ HitQuery σ u k

/-- `corrupt i` is accepted and reveals the key `σ`. -/
def RevealsAt (σ : KeySlot C) (st : TprfState C) (t : (LocalSpec C + TprfSpec C).Domain) : Prop :=
  ∃ i, t = .inr (.corrupt i) ∧ ¬(∃ x ∈ st.challenged, ∃ ec, C.t ≤ (st.corrupt ∪ st.queried x ec ∪ {i}).card) ∧
    Revealed (insert i st.corrupt) σ

theorem firedBy_upd (σ : KeySlot C) (D : Finset C.Party) (t : (LocalSpec C + TprfSpec C).Domain) {k k' : HashOutput}
    (hk : ¬Hit σ t k) (hk' : ¬Hit σ t k') :
    firedBy (updSeeds σ k seeds) (updPairs σ k pairKeys) D t = firedBy (updSeeds σ k' seeds) (updPairs σ k' pairKeys) D t := by
  rcases t with ((n | u | y) | q)
  · rfl
  · ext σ'
    simp only [firedBy, Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr_right fun _ => ?_
    by_cases hσ : σ' = σ
    · subst hσ
      rw [exists_slot_iff_hitQuery, exists_slot_iff_hitQuery]
      exact ⟨fun h => absurd ⟨u, rfl, h⟩ hk, fun h => absurd ⟨u, rfl, h⟩ hk'⟩
    · refine exists_congr fun s => and_congr_right fun hs => ?_
      rw [slotInput_upd_of_ne seeds pairKeys (hs ▸ hσ : slotKey s ≠ σ),
        slotInput_upd_of_ne seeds pairKeys (hs ▸ hσ : slotKey s ≠ σ)]
  · rfl
  · rfl

theorem symAdversary_upd (σ : KeySlot C) (D : Finset C.Party) (hD : ¬Revealed D σ) (k : HashOutput)
    (t : (LocalSpec C).Domain) :
    symAdversary prims (updSeeds σ k seeds) (updPairs σ k pairKeys) D t = symAdversary prims seeds pairKeys D t := by
  rcases t with n | u | y
  · rfl
  · have e : ∀ s, (Revealed D (slotKey s) ∧ slotInput (updSeeds σ k seeds) (updPairs σ k pairKeys) s = u) ↔
        (Revealed D (slotKey s) ∧ slotInput seeds pairKeys s = u) := fun s => by
      refine and_congr_right fun hs => ?_
      rw [slotInput_upd_of_ne seeds pairKeys (σ := σ) (s := s) (fun h => hD (h ▸ hs)) k]
    simp only [symAdversary]
    split_ifs with h₁ h₂ h₂
    · rw [choose_congr (P := fun s => Revealed D (slotKey s) ∧ slotInput (updSeeds σ k seeds) (updPairs σ k pairKeys) s = u)
        (Q := fun s => Revealed D (slotKey s) ∧ slotInput seeds pairKeys s = u) (funext fun s => propext (e s)) h₁ h₂]
    · exact absurd ((exists_congr e).mp h₁) h₂
    · exact absurd ((exists_congr e).mpr h₂) h₁
    · rfl
  · rfl

theorem dealtKeys_upd (σ : KeySlot C) (parameter : PublicParameter) (i : C.Party) (hi : ¬Revealed {i} σ)
    (k : HashOutput) : dealtKeys parameter (updSeeds σ k seeds) (updPairs σ k pairKeys) i = dealtKeys parameter seeds pairKeys i := by
  rcases σ with T | p
  · simp only [dealtKeys, updSeeds, updPairs, Keys.mk.injEq, true_and, and_true]
    funext T'
    by_cases hT : T' = T
    · subst hT
      have : i ∉ C.holders T' := fun h => hi ⟨i, Finset.mem_singleton_self _, h⟩
      simp [this]
    · simp [Function.update_of_ne hT]
  · simp only [dealtKeys, updSeeds, updPairs, Keys.mk.injEq, true_and]
    funext j
    split_ifs with hj
    · rfl
    · refine Function.update_of_ne (fun hp => hi ?_) _ _
      subst hp
      rcases pairOf_self_mem (Ne.symm hj) with h | h
      · exact Or.inl (by rw [h]; exact Finset.mem_singleton_self _)
      · exact Or.inr (by rw [h]; exact Finset.mem_singleton_self _)

theorem sample_upd (σ : KeySlot C) (k : HashOutput) :
    simulateQ (routedAnswer prims (updSeeds σ k seeds) (updPairs σ k pairKeys)) (liftComp ($ᵗ Digest) (LocalSpec C)) =
      simulateQ (routedAnswer prims seeds pairKeys) (liftComp ($ᵗ Digest) (LocalSpec C)) := by
  ext y : 1
  rw [routed_liftComp_run, routed_liftComp_run]

set_option maxRecDepth 10000 in
theorem symCore_upd (σ : KeySlot C) (b : Bool) (parameter : PublicParameter) (t : (LocalSpec C + TprfSpec C).Domain)
    (x : TprfState C × HashCache C × SlotCache C) (hD : ¬Revealed x.1.corrupt σ) (hrev : ¬RevealsAt σ x.1 t)
    (k : HashOutput) :
    (symCore prims (updSeeds σ k seeds) (updPairs σ k pairKeys) b parameter t).run x =
      (symCore prims seeds pairKeys b parameter t).run x := by
  rcases t with t | (i | ⟨i, J, y, ec⟩ | y)
  · simp only [gameImplWith, StateT.run_mk, symAdversary_upd prims seeds pairKeys σ _ hD]
  · simp only [gameImplWith, StateT.run_mk]
    split_ifs with h
    · rfl
    · have hi : ¬Revealed {i} σ := fun hi => hrev ⟨i, rfl, h, revealed_mono (by simp) hi⟩
      rw [dealtKeys_upd seeds pairKeys σ parameter i hi]
  · simp only [gameImplWith, StateT.run_mk]
  · simp only [gameImplWith, StateT.run_mk, sample_upd]

theorem symImpl_upd_eq (σ : KeySlot C) (b : Bool) (parameter : PublicParameter) (t : (LocalSpec C + TprfSpec C).Domain)
    (p : SymState C × Bool) (hD : ¬Revealed p.1.1.1.corrupt σ) (hrev : ¬RevealsAt σ p.1.1.1 t) {k k' : HashOutput}
    (hk : ¬Hit σ t k) (hk' : ¬Hit σ t k') :
    (symImpl prims (updSeeds σ k seeds) (updPairs σ k pairKeys) b parameter t).run p =
      (symImpl prims (updSeeds σ k' seeds) (updPairs σ k' pairKeys) b parameter t).run p := by
  simp only [symImpl, withFired, StateT.run_mk, hitFlag, firedBy_upd seeds pairKeys σ _ t hk hk']
  rw [show (symCore prims (updSeeds σ k seeds) (updPairs σ k pairKeys) b parameter t).run p.1.1 = _ from
      symCore_upd prims seeds pairKeys σ b parameter t p.1.1 hD hrev k,
    show (symCore prims (updSeeds σ k' seeds) (updPairs σ k' pairKeys) b parameter t).run p.1.1 = _ from
      symCore_upd prims seeds pairKeys σ b parameter t p.1.1 hD hrev k']

set_option maxRecDepth 10000 in
theorem gameImplWith_corrupt_cases {σ' : Type}
    (adversary : Finset C.Party → QueryImpl (LocalSpec C) (StateT σ' ProbComp))
    (evalH : C.Party → C.Quorum → Point → Message → StateT σ' ProbComp Digest)
    (prfH : Point → StateT σ' ProbComp Digest) (sampleH : StateT σ' ProbComp Digest) (b : Bool)
    (keys : C.Party → Keys C) (t : (LocalSpec C + TprfSpec C).Domain) (p : TprfState C × σ') :
    ∀ z ∈ support ((gameImplWith adversary evalH prfH sampleH b keys t).run p), z.2.1.corrupt = p.1.corrupt ∨
      ∃ i, t = .inr (.corrupt i) ∧ ¬(∃ x ∈ p.1.challenged, ∃ ec, C.t ≤ (p.1.corrupt ∪ p.1.queried x ec ∪ {i}).card) ∧
        z.2.1.corrupt = insert i p.1.corrupt := by
  intro z hz
  rcases t with t | (i | ⟨i, J, y, ec⟩ | y)
  · simp only [gameImplWith, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact Or.inl rfl
  · simp only [gameImplWith, StateT.run_mk] at hz
    split_ifs at hz with h <;> simp only [support_pure, Set.mem_singleton_iff] at hz <;> subst hz
    · exact Or.inl rfl
    · exact Or.inr ⟨i, rfl, h, rfl⟩
  · simp only [gameImplWith, StateT.run_mk] at hz
    split_ifs at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact Or.inl rfl
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, -, rfl⟩ := hz
      exact Or.inl rfl
  · simp only [gameImplWith, StateT.run_mk] at hz
    split_ifs at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact Or.inl rfl
    all_goals simp only [support_map, Set.mem_image] at hz; obtain ⟨w, -, rfl⟩ := hz; exact Or.inl rfl

theorem symImpl_hit (σ : KeySlot C) (b : Bool) (parameter : PublicParameter) (t : (LocalSpec C + TprfSpec C).Domain)
    (p : SymState C × Bool) (hD : ¬Revealed p.1.1.1.corrupt σ) {k : HashOutput} (hk : Hit σ t k) :
    ∀ z ∈ support ((symImpl prims (updSeeds σ k seeds) (updPairs σ k pairKeys) b parameter t).run p),
      σ ∈ z.2.1.2 := by
  intro z hz
  obtain ⟨u, rfl, hu⟩ := hk
  simp only [symImpl, withFired, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨w, -, rfl⟩ := hz
  simp only [Finset.mem_union, firedBy, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr ⟨hD, (exists_slot_iff_hitQuery seeds pairKeys σ u k).mpr hu⟩

theorem symImpl_miss (σ : KeySlot C) (b : Bool) (parameter : PublicParameter) (t : (LocalSpec C + TprfSpec C).Domain)
    (p : SymState C × Bool) (hD : ¬Revealed p.1.1.1.corrupt σ) (hσ : σ ∉ p.1.2) (hrev : ¬RevealsAt σ p.1.1.1 t)
    {k : HashOutput} (hk : ¬Hit σ t k) :
    ∀ z ∈ support ((symImpl prims (updSeeds σ k seeds) (updPairs σ k pairKeys) b parameter t).run p),
      ¬Revealed z.2.1.1.1.corrupt σ ∧ σ ∉ z.2.1.2 := by
  intro z hz
  simp only [symImpl, withFired, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  refine ⟨?_, ?_⟩
  · rcases gameImplWith_corrupt_cases _ _ _ _ b _ t _ w hw with h | ⟨i, rfl, hr, h⟩
    · exact h ▸ hD
    · exact h ▸ fun hi => hrev ⟨i, rfl, hr, hi⟩
  · simp only [Finset.mem_union, not_or]
    refine ⟨hσ, fun h => ?_⟩
    rcases t with ((n | u | y) | q)
    · simp [firedBy] at h
    · simp only [firedBy, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact hk ⟨u, rfl, (exists_slot_iff_hitQuery seeds pairKeys σ u k).mp h.2⟩
    · simp [firedBy] at h
    · simp [firedBy] at h

theorem symImpl_reveals (σ : KeySlot C) (b : Bool) (parameter : PublicParameter)
    (t : (LocalSpec C + TprfSpec C).Domain) (p : SymState C × Bool) (hσ : σ ∉ p.1.2) (hrev : RevealsAt σ p.1.1.1 t)
    (k : HashOutput) :
    ∀ z ∈ support ((symImpl prims (updSeeds σ k seeds) (updPairs σ k pairKeys) b parameter t).run p),
      Revealed z.2.1.1.1.corrupt σ ∧ σ ∉ z.2.1.2 := by
  intro z hz
  obtain ⟨i, rfl, hr, hi⟩ := hrev
  simp only [symImpl, withFired, StateT.run_mk, gameImplWith, if_neg hr, support_map, support_pure,
    Set.image_singleton, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨hi, by simp [firedBy, hσ]⟩

theorem exists_not_hit (σ : KeySlot C) (t : (LocalSpec C + TprfSpec C).Domain) : ∃ k, ¬Hit σ t k := by
  by_contra h
  push Not at h
  obtain ⟨u, rfl, h0⟩ := h 0
  obtain ⟨u', hu', h1⟩ := h 1
  cases hu'
  exact absurd (hitQuery_unique h0 h1) (by decide)

open Classical in
/-- The weight of the hits of the key `σ` over all its values is at most the budget. -/
theorem sum_hit_le (σ : KeySlot C) (b : Bool) (parameter : PublicParameter) {α : Type}
    (oa : OracleComp (LocalSpec C + TprfSpec C) α) (n : ℕ)
    (hq : IsQueryBoundP oa (fun t => Sum.elim Counted (fun _ => False) t) n) (p : SymState C × Bool)
    (hD : ¬Revealed p.1.1.1.corrupt σ) (hσ : σ ∉ p.1.2) :
    ∑ k : HashOutput, Pr[fun z => σ ∈ z.2.1.2 |
      (simulateQ (symImpl prims (updSeeds σ k seeds) (updPairs σ k pairKeys) b parameter) oa).run p] ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n p with
  | pure a => simp [hσ]
  | query_bind t cont ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, probEvent_bind_eq_tsum]
    by_cases hrev : RevealsAt σ p.1.1.1 t
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun k _ => ENNReal.tsum_eq_zero.mpr fun z => ?_) bot_le
      by_cases hz : z ∈ support ((symImpl prims (updSeeds σ k seeds) (updPairs σ k pairKeys) b parameter t).run p)
      · obtain ⟨h1, h2⟩ := symImpl_reveals prims seeds pairKeys σ b parameter t p hσ hrev k z hz
        rw [probEvent_revealed_stays _ _ _ b parameter σ _ z.2 h1 h2, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul]
    obtain ⟨k₁, hk₁⟩ := exists_not_hit σ t
    set M := (symImpl prims (updSeeds σ k₁ seeds) (updPairs σ k₁ pairKeys) b parameter t).run p
    set n' := if Sum.elim Counted (fun _ => False) t then n - 1 else n
    have hstep : ∀ k, ¬Hit σ t k →
        (symImpl prims (updSeeds σ k seeds) (updPairs σ k pairKeys) b parameter t).run p = M :=
      fun k hk => symImpl_upd_eq prims seeds pairKeys σ b parameter t p hD hrev hk hk₁
    have hk : ∀ k, (∑' z, Pr[= z | (symImpl prims (updSeeds σ k seeds) (updPairs σ k pairKeys) b parameter t).run p] *
        Pr[fun z' => σ ∈ z'.2.1.2 | (simulateQ (symImpl prims (updSeeds σ k seeds) (updPairs σ k pairKeys) b parameter)
          (cont z.1)).run z.2]) ≤ (if Hit σ t k then 1 else 0) + ∑' z, Pr[= z | M] *
        Pr[fun z' => σ ∈ z'.2.1.2 | (simulateQ (symImpl prims (updSeeds σ k seeds) (updPairs σ k pairKeys) b parameter)
          (cont z.1)).run z.2] := fun k => by
      split_ifs with h
      · refine le_add_right ?_
        rw [← probEvent_bind_eq_tsum]
        exact probEvent_le_one
      · rw [hstep k h, zero_add]
    refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
    rw [Finset.sum_add_distrib, ← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
    have hM : ∀ z, Pr[= z | M] * ∑ k : HashOutput, Pr[fun z' => σ ∈ z'.2.1.2 |
        (simulateQ (symImpl prims (updSeeds σ k seeds) (updPairs σ k pairKeys) b parameter) (cont z.1)).run z.2] ≤
          Pr[= z | M] * n' := fun z => by
      by_cases hz : z ∈ support M
      · obtain ⟨h1, h2⟩ := symImpl_miss prims seeds pairKeys σ b parameter t p hD hσ hrev hk₁ z hz
        exact mul_le_mul_right (ih z.1 n' (hq.2 z.1) z.2 h1 h2) _
      · simp [probOutput_eq_zero_of_not_mem_support hz]
    have hsum : ∑' z, ∑ k : HashOutput, Pr[= z | M] * Pr[fun z' => σ ∈ z'.2.1.2 |
        (simulateQ (symImpl prims (updSeeds σ k seeds) (updPairs σ k pairKeys) b parameter) (cont z.1)).run z.2] ≤ n' := by
      refine (ENNReal.tsum_le_tsum fun z => (Finset.mul_sum _ _ _).symm.le.trans (hM z)).trans ?_
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
    by_cases hh : ∃ k₀, Hit σ t k₀
    · obtain ⟨k₀, u, rfl, hu⟩ := hh
      have hc : Sum.elim Counted (fun _ => False) (Sum.inl (Sum.inr (Sum.inl u)) : (LocalSpec C + TprfSpec C).Domain) := by
        rcases σ with T | p'
        · obtain ⟨x, rfl⟩ := hu; trivial
        · obtain ⟨x, m, J, rfl⟩ := hu; trivial
      have hn : 0 < n := hq.1.resolve_left (not_not.mpr hc)
      have h1 : ∑ k : HashOutput, (if Hit σ (.inl (.inr (.inl u))) k then (1 : ℝ≥0∞) else 0) ≤ 1 := by
        rw [Finset.sum_eq_single k₀ (fun k _ hk => if_neg fun h => hk (hitQuery_unique (by
          obtain ⟨u', hu', h'⟩ := h; cases hu'; exact h') hu)) (by simp)]
        split_ifs <;> simp
      have hn' : n' = n - 1 := if_pos hc
      refine (add_le_add h1 hsum).trans (le_of_eq ?_)
      rw [hn', ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_cancel' hn]
    · have h0 : ∑ k : HashOutput, (if Hit σ t k then (1 : ℝ≥0∞) else 0) = 0 :=
        Finset.sum_eq_zero fun k _ => if_neg fun h => hh ⟨k, h⟩
      rw [h0, zero_add]
      refine hsum.trans ?_
      simp only [n']
      split_ifs
      · exact_mod_cast Nat.sub_le n 1
      · exact le_rfl

theorem flag_fired (b : Bool) (parameter : PublicParameter) {α : Type} (oa : OracleComp (LocalSpec C + TprfSpec C) α)
    (p : SymState C × Bool) (hp : p.2 = true → p.1.2.Nonempty) :
    ∀ z ∈ support ((simulateQ (symImpl prims seeds pairKeys b parameter) oa).run p), z.2.2 = true → z.2.1.2.Nonempty := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hp
  | query_bind t k ih =>
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    refine ih w.1 w.2 (fun hf => ?_) z hz
    simp only [symImpl, withFired, StateT.run_mk, support_map, Set.mem_image] at hw
    obtain ⟨y, -, rfl⟩ := hw
    simp only [Bool.or_eq_true] at hf
    rcases hf with hf | hf
    · exact (hp hf).mono Finset.subset_union_left
    · simp only [hitFlag, decide_eq_true_eq] at hf
      exact hf.mono Finset.subset_union_right

theorem probEvent_resample {D R β : Type} [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R] [SampleableType R]
    [SampleableType (D → R)] (d : D) (X : (D → R) → ProbComp β) (E : β → Prop) (c : ℝ≥0∞)
    (h : ∀ g, ∑ u : R, Pr[E | X (Function.update g d u)] ≤ c) :
    Pr[E | $ᵗ (D → R) >>= X] ≤ c / Fintype.card R := by
  have he : Pr[E | $ᵗ (D → R) >>= X] =
      Pr[E | ($ᵗ (D → R)) >>= fun g => ($ᵗ R) >>= fun u => X (Function.update g d u)] := by
    rw [probEvent_def, probEvent_def, evalDist_bind, ← evalDist_uniformSample_bind_update (D := D) (R := R) d,
      ← evalDist_bind, evalDist_bind_bind_swap]
    simp only [bind_assoc, pure_bind]
  rw [he]
  refine probEvent_bind_le_of_forall_le fun g _ => ?_
  rw [probEvent_bind_eq_tsum, tsum_fintype]
  simp only [probOutput_uniformSample]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]
  exact mul_le_mul_left (h g) _

theorem symInit_unrevealed (σ : KeySlot C) : ¬Revealed (symInit (C := C)).1.1.1.corrupt σ := by
  rcases σ with T | p <;> simp [Revealed, symInit, tprfInit]

theorem sum_tsum_bind_le {β γ : Type} [SampleableType γ] (F : HashOutput → γ → ProbComp β) (E : β → Prop) (c : ℝ≥0∞)
    (h : ∀ y, ∑ u : HashOutput, Pr[E | F u y] ≤ c) : ∑ u : HashOutput, Pr[E | $ᵗ γ >>= F u] ≤ c := by
  simp only [probEvent_bind_eq_tsum]
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  calc ∑' y, ∑ u : HashOutput, Pr[= y | $ᵗ γ] * Pr[E | F u y]
      = ∑' y, Pr[= y | $ᵗ γ] * ∑ u : HashOutput, Pr[E | F u y] := tsum_congr fun y => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑' y, Pr[= y | $ᵗ γ] * c := ENNReal.tsum_le_tsum fun y => mul_le_mul_right (h y) _
    _ ≤ c := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one

open Classical in
/-- The key `σ` is hit with probability at most `q / 2^256`. -/
theorem symbolic_hit_le (b : Bool) (A : TprfAdversary C) (q : ℕ)
    (hq : IsQueryBoundP A (fun t => Sum.elim Counted (fun _ => False) t) q) (σ : KeySlot C) :
    Pr[fun z => σ ∈ z.2.1.2 | do
      let parameter ← $ᵗ PublicParameter
      let seeds ← $ᵗ (C.Term → HashOutput)
      let pairKeys ← $ᵗ (C.Pair → HashOutput)
      (simulateQ (symImpl prims seeds pairKeys b parameter) A).run symInit] ≤ (q : ℝ≥0∞) / 2 ^ 256 := by
  have hcard : (Fintype.card HashOutput : ℝ≥0∞) = 2 ^ 256 := by
    simp [hashOutputBits]
    norm_num
  refine probEvent_bind_le_of_forall_le fun parameter _ => ?_
  rcases σ with T | p
  · rw [← hcard]
    refine probEvent_resample T _ _ q fun g => sum_tsum_bind_le _ _ _ fun pairKeys => ?_
    exact sum_hit_le prims g pairKeys (.inl T) b parameter A q hq symInit (symInit_unrevealed _) (by simp [symInit])
  · refine probEvent_bind_le_of_forall_le fun seeds _ => ?_
    rw [← hcard]
    refine probEvent_resample p _ _ q fun g => ?_
    exact sum_hit_le prims seeds g (.inr p) b parameter A q hq symInit (symInit_unrevealed _) (by simp [symInit])

open Classical in
/-- `hbad`. The symbolic game hits a key with probability at most `(C(n, t - 1) + C(n, 2)) q / 2^256`. -/
theorem symbolic_bad (b : Bool) (A : TprfAdversary C) (q : ℕ)
    (hq : IsQueryBoundP A (fun t => Sum.elim Counted (fun _ => False) t) q) :
    Pr[fun z => z.2.2 = true | do
      let parameter ← $ᵗ PublicParameter
      let seeds ← $ᵗ (C.Term → HashOutput)
      let pairKeys ← $ᵗ (C.Pair → HashOutput)
      (simulateQ (symImpl prims seeds pairKeys b parameter) A).run symInit] ≤
      (Fintype.card (KeySlot C) * q : ℝ≥0∞) / 2 ^ 256 := by
  refine (probEvent_mono fun z hz hf => ?_).trans ((probEvent_exists_finset_le_sum Finset.univ _
    (fun σ z => σ ∈ z.2.1.2)).trans ?_)
  · simp only [mem_support_bind_iff] at hz
    obtain ⟨parameter, -, seeds, -, pairKeys, -, hz⟩ := hz
    obtain ⟨σ, hσ⟩ := flag_fired prims seeds pairKeys b parameter A symInit (by simp [symInit]) z hz hf
    exact ⟨σ, Finset.mem_univ _, hσ⟩
  · refine (Finset.sum_le_sum fun σ _ => symbolic_hit_le prims b A q hq σ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc]

end Bad

/-! ## Collisions of the keys -/

section Collision

theorem card_hashOutput : (Fintype.card HashOutput : ℝ≥0∞) = 2 ^ 256 := by
  simp [hashOutputBits]
  norm_num

/-- The pairs are the 2-subsets of the operators. -/
theorem card_pair : Fintype.card C.Pair = C.n.choose 2 := by
  classical
  have hcard : Fintype.card (Finset.powersetCard 2 (Finset.univ : Finset C.Party)) = C.n.choose 2 := by
    rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  refine Fintype.card_congr ⟨fun p => ⟨{p.1.1, p.1.2}, by
      simp [Finset.mem_powersetCard, Finset.card_pair (ne_of_lt p.2)]⟩,
    fun s => ⟨((s.1.min' (Finset.card_pos.mp (by have := (Finset.mem_powersetCard.mp s.2).2; omega))),
      (s.1.max' (Finset.card_pos.mp (by have := (Finset.mem_powersetCard.mp s.2).2; omega)))),
      Finset.min'_lt_max'_of_card _ (by have := (Finset.mem_powersetCard.mp s.2).2; omega)⟩, ?_, ?_⟩
  · intro p
    obtain ⟨⟨a, b⟩, hab⟩ := p
    apply Subtype.ext
    simp only
    ext
    · simp [Finset.min'_insert, min_eq_left hab.le]
    · simpa [Finset.max'_insert] using hab.le
  · intro s
    obtain ⟨s, hs⟩ := s
    apply Subtype.ext
    simp only
    have h2 := (Finset.mem_powersetCard.mp hs).2
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
    rcases lt_or_gt_of_ne hab with h | h
    · simp [Finset.min'_insert, Finset.max'_insert, min_eq_left h.le, max_eq_right h.le]
    · simp [Finset.min'_insert, Finset.max'_insert, min_eq_left h.le, max_eq_right h.le,
        Finset.pair_comm]

theorem card_term : Fintype.card C.Term = C.n.choose (C.t - 1) := by
  simp [Committee.Term, Fintype.card_finset_len]

theorem probEvent_bind_le_of_ite {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (p : α → Prop)
    (q : β → Prop) (h : ∀ a, ¬p a → Pr[q | f a] = 0) : Pr[q | mx >>= f] ≤ Pr[p | mx] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : p a
  · rw [if_pos ha]; exact mul_le_of_le_one_right' probEvent_le_one
  · rw [if_neg ha, h a ha, mul_zero]

theorem probEvent_update_le {Ω : Type} [Fintype Ω] [DecidableEq Ω] [SampleableType (Ω → HashOutput)]
    (E : (Ω → HashOutput) → Prop) (d : Ω)
    (h : ∀ g x y, E (Function.update g d x) → E (Function.update g d y) → x = y) :
    Pr[E | $ᵗ (Ω → HashOutput)] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  classical
  rw [probEvent_def, ← evalDist_uniformSample_bind_update (D := Ω) (R := HashOutput) d,
    ← probEvent_def, probEvent_bind_bind_swap]
  refine probEvent_bind_le_of_forall_le fun g _ => ?_
  rw [bind_pure_comp, probEvent_map, probEvent_uniformSample, card_hashOutput]
  have hcard : (Finset.univ.filter (E ∘ Function.update g d)).card ≤ 1 :=
    Finset.card_le_one.mpr fun x hx y hy => h g x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  rw [ENNReal.div_eq_inv_mul]
  calc ((2 : ℝ≥0∞) ^ 256 : ℝ≥0∞)⁻¹ * ((Finset.univ.filter (E ∘ Function.update g d)).card : ℝ≥0∞)
      ≤ ((2 : ℝ≥0∞) ^ 256)⁻¹ * 1 := by gcongr; exact_mod_cast hcard
    _ = _ := mul_one _

/-- A uniform table has a collision with probability at most `C(|Ω|, 2) / 2 ^ 256`. -/
theorem probEvent_not_injective {Ω : Type} [Fintype Ω] [DecidableEq Ω] [SampleableType (Ω → HashOutput)] :
    Pr[fun g => ¬Function.Injective g | $ᵗ (Ω → HashOutput)] ≤
      (Fintype.card Ω).choose 2 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  let E : Finset Ω → (Ω → HashOutput) → Prop := fun s g => ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ g a = g b
  calc Pr[fun g => ¬Function.Injective g | $ᵗ (Ω → HashOutput)]
      ≤ Pr[fun g => ∃ s ∈ powersetCard 2 (univ : Finset Ω), E s g | $ᵗ (Ω → HashOutput)] := by
        refine probEvent_mono fun g _ hg => ?_
        simp only [Function.Injective, not_forall] at hg
        obtain ⟨a, b, hab, hne⟩ := hg
        exact ⟨{a, b}, by simp [mem_powersetCard, Finset.card_pair hne], a, by simp, b, by simp, hne, hab⟩
    _ ≤ ∑ s ∈ powersetCard 2 (univ : Finset Ω), Pr[E s | $ᵗ (Ω → HashOutput)] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _s ∈ powersetCard 2 (univ : Finset Ω), (2 ^ 256 : ℝ≥0∞)⁻¹ := by
        refine sum_le_sum fun s hs => ?_
        obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp (mem_powersetCard.mp hs).2
        refine (probEvent_mono fun g _ (hg : E {a, b} g) => (?_ : g a = g b)).trans
          (probEvent_update_le (fun g => g a = g b) a fun g x y hx hy => ?_)
        · obtain ⟨c, hc, d, hd, hcd, h⟩ := hg
          simp only [mem_insert, mem_singleton] at hc hd
          rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
          · exact absurd rfl hcd
          · exact h
          · exact h.symm
          · exact absurd rfl hcd
        · simp only [Function.update_self, Function.update_of_ne hab.symm] at hx hy
          rw [hx, hy]
    _ = (Fintype.card Ω).choose 2 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
        rw [sum_const, card_powersetCard, card_univ, nsmul_eq_mul]

theorem slotInput_injective {seeds : C.Term → HashOutput} {pairKeys : C.Pair → HashOutput}
    (hs : Function.Injective seeds) (hp : Function.Injective pairKeys) : Function.Injective (slotInput seeds pairKeys) := by
  rintro (⟨T, x⟩ | ⟨p, x, m, J⟩) (⟨T', x'⟩ | ⟨p', x', m', J'⟩) h <;> simp only [slotInput, Query.prf.injEq,
    Query.mask.injEq, reduceCtorEq] at h
  · rw [hs h.1, h.2]
  · rw [hp h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- Two seeds or two pair keys collide. -/
def KeyCollision (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput) : Prop :=
  ¬Function.Injective seeds ∨ ¬Function.Injective pairKeys

theorem probEvent_keyCollision :
    Pr[fun k => KeyCollision k.2.1 k.2.2 | do
      let parameter ← $ᵗ PublicParameter
      let seeds ← $ᵗ (C.Term → HashOutput)
      let pairKeys ← $ᵗ (C.Pair → HashOutput)
      pure (parameter, seeds, pairKeys)] ≤
      ((C.n.choose (C.t - 1)).choose 2 + (C.n.choose 2).choose 2 : ℕ) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  refine (probEvent_or_le _ _ _).trans ?_
  rw [Nat.cast_add, add_mul]
  refine add_le_add ?_ ?_
  · refine probEvent_bind_le_of_forall_le fun _ _ => ?_
    refine (probEvent_bind_le_of_ite _ _ (fun g => ¬Function.Injective g) _ fun g hg => ?_).trans ?_
    · simp [hg]
    · have h := probEvent_not_injective (Ω := C.Term)
      rwa [card_term] at h
  · refine probEvent_bind_le_of_forall_le fun _ _ => probEvent_bind_le_of_forall_le fun _ _ => ?_
    refine (probEvent_bind_le_of_ite _ _ (fun g => ¬Function.Injective g) _ fun g hg => ?_).trans ?_
    · simp [hg]
    · have h := probEvent_not_injective (Ω := C.Pair)
      rwa [card_pair] at h

end Collision

/-! ## Assembly -/

section Assembly

/-- The keys of `prawnsKeyGen` before the dealing. -/
def keyGen3 : ProbComp (PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput)) := do
  let parameter ← $ᵗ PublicParameter
  let seeds ← $ᵗ (C.Term → HashOutput)
  let pairKeys ← $ᵗ (C.Pair → HashOutput)
  pure (parameter, seeds, pairKeys)

theorem bind_keyGen3 {β : Type} (X : PublicParameter → (C.Term → HashOutput) → (C.Pair → HashOutput) → ProbComp β) :
    (do
      let parameter ← $ᵗ PublicParameter
      let seeds ← $ᵗ (C.Term → HashOutput)
      let pairKeys ← $ᵗ (C.Pair → HashOutput)
      X parameter seeds pairKeys) = keyGen3 >>= fun x => X x.1 x.2.1 x.2.2 := by
  simp [keyGen3, bind_assoc]

theorem le_add_of_abs_toReal {a b c : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (h : |a.toReal - b.toReal| ≤ c.toReal) : a ≤ b + c := by
  rw [← ENNReal.toReal_le_toReal ha (ENNReal.add_ne_top.mpr ⟨hb, hc⟩), ENNReal.toReal_add hb hc]
  linarith [(abs_le.mp h).2]

/-- The game for the keys `x`. -/
abbrev gameP (A : TprfAdversary C) (b : Bool) (x : PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput)) :
    ℝ≥0∞ :=
  Pr[= true | (simulateQ (gameImpl (localAnswer prims) b x.2.1 (dealtKeys x.1 x.2.1 x.2.2)) A).run' (tprfInit, ∅)]

/-- The symbolic game for the keys `x`. -/
abbrev symRun (A : TprfAdversary C) (b : Bool) (x : PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput)) :=
  (simulateQ (symImpl prims x.2.1 x.2.2 b x.1) A).run symInit

open Classical in
theorem gameP_le (A : TprfAdversary C) (b : Bool) (x : PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput)) :
    gameP prims A b x ≤ gameP prims A (!b) x + (Pr[fun z => z.2.2 = true | symRun prims A b x] +
      Pr[fun z => z.2.2 = true | symRun prims A (!b) x] + if KeyCollision x.2.1 x.2.2 then 1 else 0) := by
  obtain ⟨parameter, seeds, pairKeys⟩ := x
  split_ifs with hc
  · exact le_add_left (le_add_left probOutput_le_one)
  · simp only [KeyCollision, not_or, not_not] at hc
    have hinj := slotInput_injective hc.1 hc.2
    have hreal : ∀ b, gameP prims A b (parameter, seeds, pairKeys) =
        Pr[= true | Prod.fst <$> (simulateQ (realImpl prims seeds pairKeys b parameter) A).run symInit] := fun b => by
      rw [gameP, StateT.run'_eq, game_eq_real prims seeds pairKeys hinj]
    have hsym : ∀ b, Pr[= true | Prod.fst <$> symRun prims A b (parameter, seeds, pairKeys)] =
        Pr[fun z => z.1 = true | symRun prims A b (parameter, seeds, pairKeys)] := fun b => by
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      rfl
    have hbal : Pr[fun z => z.1 = true | symRun prims A b (parameter, seeds, pairKeys)] =
        Pr[fun z => z.1 = true | symRun prims A (!b) (parameter, seeds, pairKeys)] := by
      cases b
      · exact (symbolic_balanced prims seeds pairKeys parameter A).symm
      · exact symbolic_balanced prims seeds pairKeys parameter A
    have h1 := le_add_of_abs_toReal (probOutput_ne_top) (probOutput_ne_top) (probEvent_ne_top)
      (real_sym_hop prims seeds pairKeys hinj b parameter A)
    have h2 := le_add_of_abs_toReal (probOutput_ne_top) (probOutput_ne_top) (probEvent_ne_top)
      ((abs_sub_comm _ _).trans_le (real_sym_hop prims seeds pairKeys hinj (!b) parameter A))
    rw [hreal, hreal, add_zero]
    calc _ ≤ _ := h1
      _ = Pr[= true | Prod.fst <$> symRun prims A (!b) (parameter, seeds, pairKeys)] +
          Pr[fun z => z.2.2 = true | symRun prims A b (parameter, seeds, pairKeys)] := by
        rw [hsym, hsym, hbal]
      _ ≤ _ := by
        refine (add_le_add h2 le_rfl).trans (le_of_eq ?_)
        ring

end Assembly

section Final

theorem two_mul_choose_two_le (n : ℕ) : 2 * n.choose 2 ≤ n ^ 2 := by
  rw [Nat.choose_two_right]
  have h1 : 2 * (n * (n - 1) / 2) ≤ n * (n - 1) := Nat.mul_div_le _ 2
  have h2 : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
  nlinarith

theorem choose_two_le_sq (n : ℕ) : n.choose 2 ≤ n ^ 2 := by
  have := two_mul_choose_two_le n
  omega

/-- The error of the hops is at most `tprfError`. -/
theorem error_le (q : ℕ) :
    2 * (C.n.choose (C.t - 1) + C.n.choose 2) * q + ((C.n.choose (C.t - 1)).choose 2 + (C.n.choose 2).choose 2) ≤
      (2 * C.n.choose (C.t - 1) + C.n ^ 2) * q + (C.n.choose (C.t - 1) + C.n ^ 2) ^ 2 := by
  set T := C.n.choose (C.t - 1)
  set P := C.n.choose 2
  have hP : 2 * P ≤ C.n ^ 2 := two_mul_choose_two_le _
  have hT2 : T.choose 2 ≤ T ^ 2 := choose_two_le_sq T
  have hP2 : P.choose 2 ≤ P ^ 2 := choose_two_le_sq P
  have hPn : P ≤ C.n ^ 2 := by omega
  have hPP : P ^ 2 ≤ (C.n ^ 2) ^ 2 := Nat.pow_le_pow_left hPn 2
  have hq : 2 * P * q ≤ C.n ^ 2 * q := Nat.mul_le_mul_right q hP
  nlinarith

theorem toReal_le_div {e : ℝ≥0∞} {x : ℕ} (h : e ≤ (x : ℝ≥0∞) / 2 ^ 256) : e.toReal ≤ (x : ℝ) / 2 ^ 256 := by
  have := ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top x) (by simp)) h
  simpa [ENNReal.toReal_div] using this

open Classical in
theorem accepts_tprfGame (A : TprfAdversary C) (b : Bool) :
    accepts prims (tprfGame A b) = (Pr[= true | keyGen3 >>= fun x =>
      (simulateQ (gameImpl (localAnswer prims) b x.2.1 (dealtKeys x.1 x.2.1 x.2.2)) A).run' (tprfInit, ∅)]).toReal := by
  have h1 : Pr[fun r => r.1 = true | runWorld prims (tprfGame A b)] =
      Pr[= true | (simulateQ (worldAnswer prims) (tprfGame A b)).run' ∅] := by
    rw [← fst_map_runWorld, ← probEvent_eq_eq_probOutput, probEvent_map]
    rfl
  rw [accepts, h1, runWorld_tprfGame, bind_keyGen3]

end Final

end TprfSecurityProof

open TprfSecurityProof in
/-- The threshold PRF is adaptively secure (PRAWNS, Definition 2.2 and Theorem 5.1). -/
theorem tprfSecurity (prims : Primitives) (C : Committee) : TprfSecurityStatement prims C := by
  classical
  intro A q hq
  set w := fun x => Pr[= x | keyGen3 (C := C)]
  set c : PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput) → ℝ≥0∞ := fun x =>
    Pr[fun z => z.2.2 = true | symRun prims A false x] + Pr[fun z => z.2.2 = true | symRun prims A true x] +
      if KeyCollision x.2.1 x.2.2 then 1 else 0
  have hstep : ∀ b, Pr[= true | keyGen3 >>= fun x => (simulateQ (gameImpl (localAnswer prims) b x.2.1
      (dealtKeys x.1 x.2.1 x.2.2)) A).run' (tprfInit, ∅)] ≤
      Pr[= true | keyGen3 >>= fun x => (simulateQ (gameImpl (localAnswer prims) (!b) x.2.1
        (dealtKeys x.1 x.2.1 x.2.2)) A).run' (tprfInit, ∅)] + ∑' x, w x * c x := fun b => by
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun x => ?_
    rw [← mul_add]
    refine mul_le_mul_right ((gameP_le prims A b x).trans (le_of_eq ?_)) _
    cases b
    · simp only [c, Bool.not_false]
    · simp only [c, Bool.not_true]
      ring
  have hc : ∑' x, w x * c x ≤ ((2 * (C.n.choose (C.t - 1) + C.n.choose 2) * q +
      ((C.n.choose (C.t - 1)).choose 2 + (C.n.choose 2).choose 2) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    simp only [c, mul_add, ENNReal.tsum_add]
    have hbad : ∀ b, ∑' x, w x * Pr[fun z => z.2.2 = true | symRun prims A b x] ≤
        (Fintype.card (KeySlot C) * q : ℝ≥0∞) / 2 ^ 256 := fun b => by
      have h := symbolic_bad prims b A q hq
      rw [bind_keyGen3 (fun parameter seeds pairKeys => (simulateQ (symImpl prims seeds pairKeys b parameter) A).run symInit),
        probEvent_bind_eq_tsum] at h
      exact h
    have hcoll : ∑' x, w x * (if KeyCollision x.2.1 x.2.2 then 1 else 0) ≤
        ((C.n.choose (C.t - 1)).choose 2 + (C.n.choose 2).choose 2 : ℕ) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
      have h := probEvent_keyCollision (C := C)
      rw [probEvent_eq_tsum_ite] at h
      refine le_of_eq_of_le (tsum_congr fun x => ?_) h
      split_ifs <;> simp [w, keyGen3]
    have hcard : (Fintype.card (KeySlot C) : ℝ≥0∞) = C.n.choose (C.t - 1) + C.n.choose 2 := by
      rw [Fintype.card_sum, card_term, TprfSecurityProof.card_pair]; push_cast; rfl
    refine (add_le_add (add_le_add (hbad false) (hbad true)) hcoll).trans (le_of_eq ?_)
    rw [hcard]
    simp only [ENNReal.div_eq_inv_mul]
    push_cast
    ring
  have hfin : ∑' x, w x * c x ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)) hc
  have h0 := hstep false
  have h1 := hstep true
  simp only [Bool.not_false, Bool.not_true] at h0 h1
  rw [tprfAdvantage, accepts_tprfGame, accepts_tprfGame]
  refine le_trans ?_ ((toReal_le_div hc).trans ?_)
  · rw [abs_le]
    constructor
    · have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probOutput_ne_top, hfin⟩) h1
      rw [ENNReal.toReal_add probOutput_ne_top hfin] at this
      linarith
    · have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probOutput_ne_top, hfin⟩) h0
      rw [ENNReal.toReal_add probOutput_ne_top hfin] at this
      linarith
  · rw [tprfError]
    exact div_le_div_of_nonneg_right (by exact_mod_cast error_le (C := C) q) (by positivity)

end ThresholdLeanXmssSecurity
