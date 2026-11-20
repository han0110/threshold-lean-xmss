import ThresholdLeanXmssSecurity.Proof.BatchCheck.ExtendBlock
import ThresholdLeanXmssSecurity.Proof.BatchCheck.Tails

/-!
# The tails of the wrapper do not change the outputs of the check

`c1Wrapper` runs a tail after a partial reply to `F_coin` or `F_extendMult`, and a round tail after a
partial digest round. This file shows that the outputs of the check are the same without these tails.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.TailErasure

open RealNetworkV3 RealNetworkC1s RealNetworkC1r RealNetworkC1v RealNetworkC1x

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-! ## The outputs of a run -/

section Outputs

variable (prims : Primitives)

/-- Two runs give the same distribution of the outputs of the honest operators, from each cache. -/
def OutEq {S S' α : Type} (oa : OracleComp (LocalSpec C) (S × (C.Party → Option α)))
    (ob : OracleComp (LocalSpec C) (S' × (C.Party → Option α))) : Prop :=
  ∀ cache : HashCache C, (simulateQ (localAnswer prims) (Prod.snd <$> oa)).run' cache =ᵈ
    (simulateQ (localAnswer prims) (Prod.snd <$> ob)).run' cache

/-- A run gives no output, from each cache. -/
def OutNone {S α : Type} (oa : OracleComp (LocalSpec C) (S × (C.Party → Option α))) : Prop :=
  ∀ cache : HashCache C, (simulateQ (localAnswer prims) (Prod.snd <$> oa)).run' cache =ᵈ
    (pure fun _ => none : ProbComp (C.Party → Option α))

/-- Each honest operator has an output. -/
def Full {β : Type} (D : C.Coalition) (o : C.Party → Option β) : Prop := ∀ i, i ∉ D.1 → (o i).isSome

variable {prims}

theorem OutEq.symm {S S' α : Type} {oa : OracleComp (LocalSpec C) (S × (C.Party → Option α))}
    {ob : OracleComp (LocalSpec C) (S' × (C.Party → Option α))} (h : OutEq prims oa ob) : OutEq prims ob oa :=
  fun cache => (h cache).symm

theorem OutEq.trans {S S' S'' α : Type} {oa : OracleComp (LocalSpec C) (S × (C.Party → Option α))}
    {ob : OracleComp (LocalSpec C) (S' × (C.Party → Option α))}
    {oc : OracleComp (LocalSpec C) (S'' × (C.Party → Option α))} (h : OutEq prims oa ob) (h' : OutEq prims ob oc) :
    OutEq prims oa oc :=
  fun cache => (h cache).trans (h' cache)

theorem OutEq.of_outNone {S S' α : Type} {oa : OracleComp (LocalSpec C) (S × (C.Party → Option α))}
    {ob : OracleComp (LocalSpec C) (S' × (C.Party → Option α))} (ha : OutNone prims oa) (hb : OutNone prims ob) :
    OutEq prims oa ob :=
  fun cache => (ha cache).trans (hb cache).symm

theorem OutEq.of_sameRun {S α : Type} {oa ob : OracleComp (LocalSpec C) (S × (C.Party → Option α))}
    (h : SameRun prims oa ob) : OutEq prims oa ob := fun cache => by
  have := ((h.map Prod.snd) cache).map Prod.fst
  simpa only [StateT.run'_eq] using this

theorem OutNone.of_sameRun {S α : Type} {oa ob : OracleComp (LocalSpec C) (S × (C.Party → Option α))}
    (h : SameRun prims oa ob) (hb : OutNone prims ob) : OutNone prims oa :=
  fun cache => ((OutEq.of_sameRun h) cache).trans (hb cache)

theorem OutEq.bind_right {γ S S' α : Type} (oa : OracleComp (LocalSpec C) γ)
    {f : γ → OracleComp (LocalSpec C) (S × (C.Party → Option α))}
    {g : γ → OracleComp (LocalSpec C) (S' × (C.Party → Option α))} (h : ∀ a, OutEq prims (f a) (g a)) :
    OutEq prims (oa >>= f) (oa >>= g) := fun cache => by
  simp only [map_bind, simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  refine EvalDistEq.bind_right _ fun p => ?_
  have := h p.1 p.2
  simpa only [StateT.run'_eq] using this

theorem OutNone.bind {γ S α : Type} (oa : OracleComp (LocalSpec C) γ)
    {f : γ → OracleComp (LocalSpec C) (S × (C.Party → Option α))} (h : ∀ a, OutNone prims (f a)) :
    OutNone prims (oa >>= f) := fun cache => by
  simp only [map_bind, simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  refine (EvalDistEq.bind_right _ fun p => ?_).trans (OracleComp.EvalDistEq.bind_const _ _)
  have := h p.1 p.2
  simpa only [StateT.run'_eq] using this

theorem outNone_pure {S α : Type} (s : S) : OutNone prims (pure (s, fun _ => none) :
    OracleComp (LocalSpec C) (S × (C.Party → Option α))) := fun cache => by
  simp only [map_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure]
  rfl

theorem outEq_pure {S S' α : Type} (s : S) (s' : S') (o : C.Party → Option α) :
    OutEq prims (pure (s, o) : OracleComp (LocalSpec C) (S × (C.Party → Option α)))
      (pure (s', o) : OracleComp (LocalSpec C) (S' × (C.Party → Option α))) := fun cache => by
  simp only [map_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure]
  rfl

theorem not_full_none {β : Type} (D : C.Coalition) : ¬ Full D (fun _ : C.Party => (none : Option β)) := by
  obtain ⟨i, hi⟩ := exists_honest D
  exact fun h => by simpa using h i hi

/-- One reply of a wrapper with a tail, and the rest of the run, on both sides. After a reply where `P`
holds both sides give no output, whatever the tail. After another reply both sides reach the same
state. The goals close with `refine` on this form, because the state types of the two wrappers unify
only up to the unfolding of their definitions. -/
theorem outEq_reply {Sst R S S' α : Type} (x : OracleComp (LocalSpec C) (Sst × R)) (P : Sst × R → Prop)
    (tT tN : Sst × R → OracleComp (LocalSpec C) Sst) (c : ℕ)
    (GT : (Sst × ℕ) × R → OracleComp (LocalSpec C) (S × (C.Party → Option α)))
    (GN : (Sst × ℕ) × R → OracleComp (LocalSpec C) (S' × (C.Party → Option α)))
    (hdead : ∀ a, P a → ∀ st, OutNone prims (GT ((st, c), a.2)) ∧ OutNone prims (GN ((st, c), a.2)))
    (hsame : ∀ a, ¬ P a → OutEq prims (GT ((a.1, c), a.2)) (GN ((a.1, c), a.2))) :
    OutEq prims
      ((x >>= fun a => if P a then (fun st' => ((st', c), a.2)) <$> tT a else pure ((a.1, c), a.2)) >>= GT)
      ((x >>= fun a => if P a then (fun st' => ((st', c), a.2)) <$> tN a else pure ((a.1, c), a.2)) >>= GN) := by
  rw [bind_assoc, bind_assoc]
  refine OutEq.bind_right _ fun a => ?_
  by_cases hP : P a
  · simp only [hP, ↓reduceIte, bind_map_left]
    exact OutEq.of_outNone (OutNone.bind _ fun st => (hdead a hP st).1) (OutNone.bind _ fun st => (hdead a hP st).2)
  · simp only [hP, ↓reduceIte, pure_bind]
    exact hsame a hP

/-- One reply where both tails are the identity, and the rest of the run. -/
theorem outEq_reply_pure {Sst R S S' α : Type} (x : OracleComp (LocalSpec C) (Sst × R)) (P : Sst × R → Prop)
    (tT tN : Sst × R → OracleComp (LocalSpec C) Sst) (c : ℕ)
    (GT : (Sst × ℕ) × R → OracleComp (LocalSpec C) (S × (C.Party → Option α)))
    (GN : (Sst × ℕ) × R → OracleComp (LocalSpec C) (S' × (C.Party → Option α)))
    (hT : ∀ a : Sst × R, P a → tT a = pure a.1) (hN : ∀ a : Sst × R, P a → tN a = pure a.1)
    (hsame : ∀ a : Sst × R, OutEq prims (GT ((a.1, c), a.2)) (GN ((a.1, c), a.2))) :
    OutEq prims
      ((x >>= fun a => if P a then (fun st' => ((st', c), a.2)) <$> tT a else pure ((a.1, c), a.2)) >>= GT)
      ((x >>= fun a => if P a then (fun st' => ((st', c), a.2)) <$> tN a else pure ((a.1, c), a.2)) >>= GN) := by
  rw [bind_assoc, bind_assoc]
  refine OutEq.bind_right _ fun a => ?_
  by_cases hP : P a
  · simp only [hP, ↓reduceIte, hT a hP, hN a hP, map_pure, pure_bind]
    exact hsame a
  · simp only [hP, ↓reduceIte, pure_bind]
    exact hsame a

/-- One round of a wrapper with a round tail, against the same round with no tail. After a round where
`P` holds both sides give no output. After another round both sides reach the same state. -/
theorem outEq_round {Ws Sst Sst' R O S S' α : Type} (x : OracleComp (LocalSpec C) (Ws × R)) (P : Ws × R → Prop)
    (t : Ws × R → OracleComp (LocalSpec C) Ws) (gT : Ws → Sst) (gN : Ws → Sst') (out : R → O)
    (GT : Sst × O → OracleComp (LocalSpec C) (S × (C.Party → Option α)))
    (GN : Sst' × O → OracleComp (LocalSpec C) (S' × (C.Party → Option α)))
    (hdead : ∀ a, P a → (∀ w, OutNone prims (GT (gT w, out a.2))) ∧ OutNone prims (GN (gN a.1, out a.2)))
    (hsame : ∀ a, ¬ P a → OutEq prims (GT (gT a.1, out a.2)) (GN (gN a.1, out a.2))) :
    OutEq prims
      (((x >>= fun r => if P r then (fun w => (gT w, r.2)) <$> t r else pure (gT r.1, r.2)) >>= fun b =>
        pure (b.1, out b.2)) >>= GT)
      ((((fun r => (gN r.1, r.2)) <$> x) >>= fun b => pure (b.1, out b.2)) >>= GN) := by
  simp only [bind_map_left, bind_assoc]
  refine OutEq.bind_right _ fun a => ?_
  by_cases hP : P a
  · simp only [hP, ↓reduceIte, bind_map_left, pure_bind]
    exact OutEq.of_outNone (OutNone.bind _ fun w => (hdead a hP).1 w) (hdead a hP).2
  · simp only [hP, ↓reduceIte, pure_bind]
    exact hsame a hP

end Outputs

/-! ## The two wrappers and the claim of the head -/

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

section Claim

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
  (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
  (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg : ℕ)
  (hist : C.Party → C.Term → List Bit)

/-- `c1Wrapper` with each tail of a reply and each tail of a round replaced by the identity. -/
@[reducible] def c1Erased : Adversary C E Ia (CheckLeak C E) (CheckAnswer C E) :=
  roundScheduled D (relabel (withMemory W (C1Memory C E) ⟨hist, []⟩) (checkReply (C := C) (E := E)))
    (c1Sims K D W knownE knownB) c1Names RealNetworkGP.noTails (fun _ => digestSurv D) RealNetworkGP.noTails

/-- The claim for the head from position `n` with `f` steps of fuel. Each continuation that is the same
on a full output at the counter `n + f`, and that gives no output after a missing output, gives the
same outputs after the run under `c1Wrapper` and after the run under `c1Erased`. -/
def ErasedAt {β : Type} (f n : ℕ) (prog : C.Party → PartyM C E (CheckSpec C E) β) : Prop :=
  ∀ (s : W.State × C1Memory C E) {S S' : Type}
    (kT : (c1Wrapper K D W knownE knownB count L tg hist).State × (C.Party → Option β) →
      OracleComp (LocalSpec C) (S × (C.Party → Option Unit)))
    (kN : (c1Erased K D W knownE knownB hist).State × (C.Party → Option β) →
      OracleComp (LocalSpec C) (S' × (C.Party → Option Unit))),
    (∀ r, Full D r.2 → r.1.2 = n + f → OutEq prims (kT r) (kN r)) →
    (∀ r, ¬ Full D r.2 → OutNone prims (kT r) ∧ OutNone prims (kN r)) →
    OutEq prims
      (executePhase localRoles D (c1Wrapper K D W knownE knownB count L tg hist) (checkFunctionalities K) f
        (s, n) prog >>= kT)
      (executePhase localRoles D (c1Erased K D W knownE knownB hist) (checkFunctionalities K) f (s, n) prog >>= kN)

/-- A phase that gives no output on each adversary, before each continuation that gives no output
after a missing output. -/
def DeadAt {β : Type} (f : ℕ) (prog : C.Party → PartyM C E (CheckSpec C E) β) : Prop :=
  ∀ (A : CheckAdversary C E Ia) (st : A.State) {S : Type}
    (k : A.State × (C.Party → Option β) → OracleComp (LocalSpec C) (S × (C.Party → Option Unit))),
    (∀ r, ¬ Full D r.2 → OutNone prims (k r)) →
    OutNone prims (executePhase localRoles D A (checkFunctionalities K) f st prog >>= k)

omit [Fintype E] in
theorem erasedAt_congr {β : Type} (f n : ℕ) (p p' : C.Party → PartyM C E (CheckSpec C E) β)
    (hp : ∀ i, i ∉ D.1 → p i = p' i) (h : ErasedAt prims K D W knownE knownB count L tg hist f n p') :
    ErasedAt prims K D W knownE knownB count L tg hist f n p := by
  intro s S S' kT kN hf hn
  rw [executePhase_congr_honest D _ _ f _ p p' hp, executePhase_congr_honest D _ _ f _ p p' hp]
  exact h s kT kN hf hn

omit [Fintype E] in
/-- Programs that make no step on each adversary. -/
theorem erasedAt_dead {β : Type} (f n : ℕ) (prog : C.Party → PartyM C E (CheckSpec C E) β)
    (h : ∀ (A : CheckAdversary C E Ia) (st : A.State),
      executePhase localRoles D A (checkFunctionalities K) f st prog = pure (st, fun _ => none)) :
    ErasedAt prims K D W knownE knownB count L tg hist f n prog := by
  intro s S S' kT kN _ hn
  rw [h, h, pure_bind, pure_bind]
  exact OutEq.of_outNone (hn _ (not_full_none D)).1 (hn _ (not_full_none D)).2

omit [Fintype E] in
/-- The split of an output. A full output uses the claim of the next block. Another output makes the
next block dead on both sides. -/
theorem erasedAt_elim {β γ : Type} (f n : ℕ) (o : C.Party → Option γ)
    (k : C.Party → γ → PartyM C E (CheckSpec C E) β)
    (hdead : (∃ i, i ∉ D.1 ∧ o i = none) → ∀ (A : CheckAdversary C E Ia) (st : A.State),
      executePhase localRoles D A (checkFunctionalities K) f st (fun i => (o i).elim failure (k i)) =
        pure (st, fun _ => none))
    (hfull : ∀ b : C.Party → γ, (∀ i, i ∉ D.1 → o i = some (b i)) →
      ErasedAt prims K D W knownE knownB count L tg hist f n (fun i => k i (b i))) :
    ErasedAt prims K D W knownE knownB count L tg hist f n (fun i => (o i).elim failure (k i)) := by
  by_cases hn : ∃ i, i ∉ D.1 ∧ o i = none
  · exact erasedAt_dead prims K D W knownE knownB count L tg hist f n _ (hdead hn)
  push Not at hn
  obtain ⟨i₀, hi₀⟩ := exists_honest D
  obtain ⟨b₀, -⟩ := Option.ne_none_iff_exists'.1 (hn i₀ hi₀)
  let b : C.Party → γ := fun i => (o i).getD b₀
  have hb : ∀ i, i ∉ D.1 → o i = some (b i) := fun i hi => by
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (hn i hi)
    simp only [b, hx, Option.getD_some]
  refine erasedAt_congr prims K D W knownE knownB count L tg hist f n _ _ (fun i hi => ?_) (hfull b hb)
  rw [hb i hi, Option.elim_some]

omit [Fintype E] in
/-- The values of `H` of the honest operators move to the front. -/
theorem erasedAt_oracle {β γ : Type} (f n : ℕ) (d : γ) (q : C.Party → OracleComp (RoSpec C) γ)
    (g : C.Party → γ → PartyM C E (CheckSpec C E) β)
    (h : ∀ w : C.Party → γ, ErasedAt prims K D W knownE knownB count L tg hist f n (fun i => g i (w i))) :
    ErasedAt prims K D W knownE knownB count L tg hist f n (fun i => oracleStep (q i) >>= g i) := by
  intro s S S' kT kN hf hn
  have h₁ := (executePhase_oracleStep_bind prims D (c1Wrapper K D W knownE knownB count L tg hist)
    (checkFunctionalities K) d f (s, n) q g).bind fun r => SameRun.refl prims (kT r)
  have h₂ := (executePhase_oracleStep_bind prims D (c1Erased K D W knownE knownB hist)
    (checkFunctionalities K) d f (s, n) q g).bind fun r => SameRun.refl prims (kN r)
  rw [bind_assoc] at h₁ h₂
  exact (OutEq.of_sameRun h₁).trans ((OutEq.bind_right _ fun w => h w s kT kN hf hn).trans
    (OutEq.of_sameRun h₂).symm)

omit [Fintype E] [DecidableEq E] in
/-- A phase that is `pure` with no output on each adversary is dead. -/
theorem deadAt_of_eq {β : Type} (f : ℕ) (prog : C.Party → PartyM C E (CheckSpec C E) β)
    (h : ∀ (A : CheckAdversary C E Ia) (st : A.State),
      executePhase localRoles D A (checkFunctionalities K) f st prog = pure (st, fun _ => none)) :
    DeadAt prims K D (Ia := Ia) f prog := by
  intro A st S k hk
  rw [h, pure_bind]
  exact hk _ (not_full_none D)

omit [Fintype E] [DecidableEq E] in
/-- The values of `H` of the honest operators move to the front of a dead phase. -/
theorem deadAt_oracle {β γ : Type} (f : ℕ) (d : γ) (q : C.Party → OracleComp (RoSpec C) γ)
    (g : C.Party → γ → PartyM C E (CheckSpec C E) β)
    (h : ∀ w : C.Party → γ, DeadAt prims K D (Ia := Ia) f (fun i => g i (w i))) :
    DeadAt prims K D (Ia := Ia) f (fun i => oracleStep (q i) >>= g i) := by
  intro A st S k hk
  have h₁ := (executePhase_oracleStep_bind prims D A (checkFunctionalities K) d f st q g).bind
    fun r => SameRun.refl prims (k r)
  rw [bind_assoc] at h₁
  exact OutNone.of_sameRun h₁ (OutNone.bind _ fun w => h w A st k hk)

omit [Fintype E] [DecidableEq E] in
/-- The reply of `c1Erased` to `F_rand` for elements runs no tail. -/
theorem erased_frandElements_answer (s : W.State × C1Memory C E) (k : ℕ) :
    (leftAdversary (rightAdversary (c1Erased K D W knownE knownB hist))).answer (s, k) () =
      (pure (((s, k + 1) : (c1Erased K D W knownE knownB hist).State), knownE k) :
        OracleComp (LocalSpec C) _) := by
  simp only [leftAdversary, rightAdversary, c1Sims,
    RealNetworkC1u.frand_not_partial_names D c1Names (c1Names_receivers D), ite_false]
  rfl

omit [Fintype E] in
/-- A call at position `k`. The tail of the reply runs only after a partial reply, and then the next
phase is dead on both sides. On each other reply both wrappers reach the same state. -/
theorem erasedAt_call {β P X : Type} (k fuel : ℕ) (input : C.Party → (ℕ ⊕ List (Product C E)) ⊕ (ℕ ⊕ ℕ))
    (f : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) →
      PartyM C E (CheckSpec C E) β)
    (pre : OracleComp (LocalSpec C) P) (lk : P → CheckLeak C E)
    (samp : P → CheckAnswer C E → OracleComp (LocalSpec C) X)
    (outF : P → CheckAnswer C E → X → C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)))
    (hF : ∀ (A : CheckAdversary C E Ia) (st : A.State),
      runFunctionality localRoles D A (checkFunctionalities K) st (fun i => if i ∈ D.1 then none else some (input i)) =
        pre >>= fun p => A.answer st (lk p) >>= fun a => samp p a.2 >>= fun x => pure (a.1, outF p a.2 x))
    (hdead : ∀ p r x, PartialOut D (receivers D c1Names (lk p) r) →
      DeadAt prims K D (Ia := Ia) fuel (fun i => f i (outF p r x i)))
    (hrest : ∀ out : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)),
      ErasedAt prims K D W knownE knownB count L tg hist fuel (k + 1) (fun i => f i (out i))) :
    ErasedAt prims K D W knownE knownB count L tg hist (fuel + 1) k (fun i => call (input i) >>= f i) := by
  intro s S S' kT kN hf hn
  rw [executePhase_call, executePhase_call, hF, hF]
  simp only [bind_assoc, pure_bind]
  refine OutEq.bind_right _ fun p => ?_
  refine outEq_reply _ _ _ _ (k + 1) _ _ (fun a hP st => ⟨OutNone.bind _ fun x => hdead p a.2 x hP _ _ kT
    fun r hr => (hn r hr).1, OutNone.bind _ fun x => hdead p a.2 x hP _ _ kN fun r hr => (hn r hr).2⟩)
    fun a _ => OutEq.bind_right _ fun x => hrest _ a.1 kT kN (fun r hr hc => hf r hr (by omega)) hn

/-- A call of `F_rand` for two elements. Its reply runs no tail under both wrappers. -/
theorem erasedAt_rand {β : Type} (k fuel : ℕ)
    (f : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) →
      PartyM C E (CheckSpec C E) β)
    (hrest : ∀ out : C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)),
      ErasedAt prims K D W knownE knownB count L tg hist fuel (k + 1) (fun i => f i (out i))) :
    ErasedAt prims K D W knownE knownB count L tg hist (fuel + 1) k
      (fun i => call (Sum.inr (Sum.inl 2)) >>= f i) := by
  intro s S S' kT kN hf hn
  rw [executePhase_call, executePhase_call, runCheck_randElements K D _ _ (fun _ => 2),
    runCheck_randElements K D _ _ (fun _ => 2), bind_map_left, bind_map_left,
    runFunctionality_rand_local D _ _ _ (by intro i hi; simp [hi]),
    runFunctionality_rand_local D _ _ _ (by intro i hi; simp [hi]),
    RealNetworkC1u.frandElements_answer K D W knownE knownB count hist c1Names (c1Names_receivers D) _ s k,
    erased_frandElements_answer K D W knownE knownB hist s k, pure_bind]
  simp only [bind_assoc, pure_bind]
  exact OutEq.bind_right _ fun a => OutEq.bind_right _ fun b =>
    hrest _ s kT kN (fun r hr hc => hf r hr (by omega)) hn

omit [Fintype E] in
/-- The last call of the head. The outputs of the phase follow at once. After a partial reply the
outputs are not full on both sides. -/
theorem erasedAt_lastCall {α P X : Type} (k : ℕ) (input : C.Party → (ℕ ⊕ List (Product C E)) ⊕ (ℕ ⊕ ℕ))
    (extract : C.Party → ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) → Option α)
    (pre : OracleComp (LocalSpec C) P) (lk : P → CheckLeak C E)
    (samp : P → CheckAnswer C E → OracleComp (LocalSpec C) X)
    (outF : P → CheckAnswer C E → X → C.Party → Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)))
    (hF : ∀ (A : CheckAdversary C E Ia) (st : A.State),
      runFunctionality localRoles D A (checkFunctionalities K) st (fun i => if i ∈ D.1 then none else some (input i)) =
        pre >>= fun p => A.answer st (lk p) >>= fun a => samp p a.2 >>= fun x => pure (a.1, outF p a.2 x))
    (hlink : ∀ p r x, PartialOut D (receivers D c1Names (lk p) r) → ∃ i, i ∉ D.1 ∧ outF p r x i = none) :
    ErasedAt prims K D W knownE knownB count L tg hist (0 + 1) k
      (fun i => RealNetworkGP.callProg (input i) (extract i)) := by
  intro s S S' kT kN hf hn
  have e := fun (A : CheckAdversary C E Ia) =>
    RealNetworkGP.callPhase_eq D (checkFunctionalities K) input extract pre lk samp outF A (hF A) 0
  unfold RealNetworkGP.callPhase at e
  rw [e, e]
  simp only [bind_assoc, pure_bind]
  refine OutEq.bind_right _ fun p => ?_
  refine outEq_reply _ _ _ _ (k + 1) _ _ (fun a hP st => ?_) fun a _ => OutEq.bind_right _ fun x => ?_
  · have hnf : ∀ x, ¬ Full D (fun j => if j ∈ D.1 then none else (outF p a.2 x j).bind (extract j)) := by
      intro x hfull
      obtain ⟨i, hi, hnone⟩ := hlink p a.2 x hP
      have := hfull i hi
      simp only [hi, ↓reduceIte, hnone, Option.bind_none, Option.isSome_none, Bool.false_eq_true] at this
    exact ⟨OutNone.bind _ fun x => (hn _ (hnf x)).1, OutNone.bind _ fun x => (hn _ (hnf x)).2⟩
  · by_cases hfull : Full D (fun j => if j ∈ D.1 then none else (outF p a.2 x j).bind (extract j))
    · exact hf _ hfull rfl
    · exact OutEq.of_outNone (hn _ hfull).1 (hn _ hfull).2

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
theorem coin_link (D : C.Coalition) (l : List E) (v : CoinValues D E) (r : CheckAnswer C E)
    (hP : PartialOut D (receivers D c1Names (Sum.inl (Sum.inl l) : CheckLeak C E) r)) :
    ∃ i, i ∉ D.1 ∧ coinOutputs D v r i = none := by
  obtain ⟨⟨i, hi, hnone⟩, -⟩ := hP
  refine ⟨i, hi, ?_⟩
  simp only [receivers, c1Names, hi, not_false_eq_true, true_and, ite_eq_right_iff, reduceCtorEq, imp_false] at hnone
  simp only [coinOutputs, hi, hnone, not_false_eq_true, and_false, ↓reduceIte]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem extend_link (D : C.Coalition) (products : C.Party → List (Product C E))
    (l : C.Party → List (Product C E)) (r : CheckAnswer C E)
    (fresh : C.Term → Fin (firstInput (fullInputs D products)).length → E)
    (hP : PartialOut D (receivers D c1Names (Sum.inl (Sum.inr l) : CheckLeak C E) r)) :
    ∃ i, i ∉ D.1 ∧ extendOutputs K D products r fresh i = none := by
  obtain ⟨⟨i, hi, hnone⟩, -⟩ := hP
  refine ⟨i, hi, ?_⟩
  simp only [receivers, c1Names, hi, not_false_eq_true, true_and, ite_eq_right_iff, reduceCtorEq, imp_false] at hnone
  simp [extendOutputs, multFinish, hi, hnone]

end Claim

/-! ## The blocks of the head -/

section Blocks

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
  (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
  (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg : ℕ)
  (hist : C.Party → C.Term → List Bit)

/-- The claim before the `extendMult` of step `j`, with `d` steps to run. -/
def PlanErased (j d : ℕ) : Prop :=
  ∀ (p : C.Party → Plan C E) (hs : C.Party → RunState C), (∀ i, i ∉ D.1 → PlanOK (p i) d) →
    ErasedAt prims K D W knownE knownB count L tg hist (2 * d + 2) (2 * j + 1)
      (fun i => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) (p i)).run (hs i))

/-- The claim before the coin of step `j`, with `d` steps after it. -/
def CoinErased (j d : ℕ) : Prop :=
  ∀ (next : C.Party → E → Plan C E) (hs : C.Party → RunState C), (∀ i, i ∉ D.1 → ∀ r, PlanOK (next i r) d) →
    ErasedAt prims K D W knownE knownB count L tg hist (2 * d + 3) (2 * j + 2)
      (fun i => (hybridCoin K i (next i)).run (hs i))

/-- The claim before the first coin. -/
def StartErased : Prop :=
  ∀ (next : C.Party → List E → Plan C E) (hs : C.Party → RunState C),
    (∀ i, i ∉ D.1 → ∀ τ, PlanOK (next i τ) (halvings count)) →
    ErasedAt prims K D W knownE knownB count L tg hist (2 * halvings count + 3) 0
      (fun i => (hybridStart K count i (next i)).run (hs i))

/-- The masked multiplication, the call of `F_rand` and the last `F_extendMult` of the head. -/
theorem maskErased (j : ℕ) : PlanErased prims K D W knownE knownB count L tg hist j 0 := by
  intro p hs hRel
  let maskA : C.Party → ℕ → E := fun i => match p i with
    | .mask A _ _ => A
    | .step _ _ => fun _ => 0
  let maskB : C.Party → ℕ → E := fun i => match p i with
    | .mask _ B _ => B
    | .step _ _ => fun _ => 0
  let maskV : C.Party → E := fun i => match p i with
    | .mask _ _ V => V
    | .step _ _ => 0
  have hp : ∀ i, i ∉ D.1 → p i = .mask (maskA i) (maskB i) (maskV i) := by
    intro i hi
    have h := hRel i hi
    simp only [maskA, maskB, maskV]
    cases hpi : p i with
    | mask A B V => rfl
    | step ps nx =>
      rw [hpi] at h
      obtain ⟨-, d', hd, -⟩ := h
      omega
  rw [show 2 * 0 + 2 = 1 + 1 by rfl]
  refine erasedAt_congr prims K D W knownE knownB count L tg hist _ _ _
    (fun i => call (Sum.inr (Sum.inl 2)) >>= fun o => (o.bind randOutput).elim failure fun w =>
      call (Sum.inl (Sum.inr (maskProducts K i (maskA i) (maskB i) w))) >>= fun o' =>
        (o'.bind extendOutput).elim failure fun z => pure (maskOut K i (hs i) (maskA i) (maskB i) (maskV i) w z))
    (fun i hi => by rw [hp i hi, mask_run]) ?_
  refine erasedAt_rand prims K D W knownE knownB count L tg hist (2 * j + 1) 1 _ fun out => ?_
  refine erasedAt_elim prims K D W knownE knownB count L tg hist _ _ (fun i => (out i).bind randOutput)
    (fun i w => call (Sum.inl (Sum.inr (maskProducts K i (maskA i) (maskB i) w))) >>= fun o' =>
      (o'.bind extendOutput).elim failure fun z => pure (maskOut K i (hs i) (maskA i) (maskB i) (maskV i) w z))
    (fun hdead A st => ?_) (fun b _ => ?_)
  · refine executePhase_dead D A _ 1 st _ (fun i _ => ?_) (hdead.imp fun i h => ⟨h.1, by rw [h.2]; rfl⟩)
    cases (out i).bind randOutput with
    | none => exact Or.inl rfl
    | some w => exact Or.inr ⟨_, _, rfl, rfl⟩
  · let products : C.Party → List (Product C E) := fun i => maskProducts K i (maskA i) (maskB i) (b i)
    refine erasedAt_congr prims K D W knownE knownB count L tg hist _ _ _
      (fun i => RealNetworkGP.callProg (Sum.inl (Sum.inr (products i)))
        (fun o => (extendOutput o).map (maskOut K i (hs i) (maskA i) (maskB i) (maskV i) (b i))))
      (fun i _ => ?_) ?_
    · unfold RealNetworkGP.callProg
      refine bind_congr fun r => ?_
      rcases r with _ | o
      · rfl
      · simp only [Option.bind_some]
        cases extendOutput o <;> rfl
    · exact erasedAt_lastCall prims K D W knownE knownB count L tg hist (2 * j + 1 + 1) _ _
        (pure () : OracleComp (LocalSpec C) Unit)
        (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
        (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
        (fun _ r fresh => extendOutputs K D products r fresh) (fun A st => extendRun_form K D A st products)
        (fun _ r fresh hP => extend_link K D products _ r fresh hP)

/-- The `extendMult` of step `j`. -/
theorem extendErased (j d : ℕ) (hIH : CoinErased prims K D W knownE knownB count L tg hist j d) :
    PlanErased prims K D W knownE knownB count L tg hist j (d + 1) := by
  intro p hs hRel
  let products : C.Party → List (Product C E) := fun i => match p i with
    | .step ps _ => ps
    | .mask _ _ _ => []
  let next : C.Party → Shares C E → E → Plan C E := fun i => match p i with
    | .step _ nx => nx
    | .mask _ _ _ => fun _ _ => p i
  have hp : ∀ i, i ∉ D.1 → p i = .step (products i) (next i) ∧ (products i).length = 2 ∧
      ∀ z r, PlanOK (next i z r) d := by
    intro i hi
    have h := hRel i hi
    simp only [products, next]
    cases hpi : p i with
    | mask A B V =>
      rw [hpi] at h
      simp only [PlanOK] at h
      omega
    | step ps nx =>
      rw [hpi] at h
      obtain ⟨hl, d', hd, hnx⟩ := h
      obtain rfl : d' = d := by omega
      exact ⟨rfl, hl, hnx⟩
  let st' : C.Party → Shares C E → RunState C := fun i z =>
    ⟨recordHistory K i (hs i).history z (products i).length, (hs i).label + 1, (hs i).tag⟩
  rw [show 2 * (d + 1) + 2 = 2 * d + 3 + 1 by omega]
  refine erasedAt_congr prims K D W knownE knownB count L tg hist _ _ _
    (fun i => call (Sum.inl (Sum.inr (products i))) >>= fun o => (o.bind extendOutput).elim failure fun z =>
      (hybridCoin K i (next i z)).run (st' i z)) (fun i hi => by rw [(hp i hi).1, step_run]) ?_
  refine erasedAt_call prims K D W knownE knownB count L tg hist (2 * j + 1) (2 * d + 3)
    (fun i => Sum.inl (Sum.inr (products i))) _ (pure () : OracleComp (LocalSpec C) Unit)
    (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
    (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
    (fun _ r fresh => extendOutputs K D products r fresh) (fun A st => extendRun_form K D A st products)
    (fun _ r fresh hP => ?_) fun out => ?_
  · obtain ⟨i, hi, hnone⟩ := extend_link K D products _ r fresh hP
    refine deadAt_of_eq prims K D _ _ fun A st => ?_
    have h := coinDead K D A (2 * d + 3) st
      (fun i => ((extendOutputs K D products r fresh i).bind extendOutput).map fun z => (next i z, st' i z))
      ⟨i, hi, by rw [hnone]; rfl⟩
    rw [← h]
    congr 1
    funext i
    cases (extendOutputs K D products r fresh i).bind extendOutput <;> rfl
  refine erasedAt_elim prims K D W knownE knownB count L tg hist _ _ (fun i => (out i).bind extendOutput)
    (fun i z => (hybridCoin K i (next i z)).run (st' i z)) (fun hdead A st => ?_) (fun b hb => ?_)
  · have h := coinDead K D A (2 * d + 3) st (fun i => ((out i).bind extendOutput).map fun z => (next i z, st' i z))
      (hdead.imp fun i h => ⟨h.1, by rw [h.2]; rfl⟩)
    rw [← h]
    congr 1
    funext i
    cases (out i).bind extendOutput <;> rfl
  · rw [show 2 * j + 1 + 1 = 2 * j + 2 by omega]
    exact hIH (fun i => next i (b i)) (fun i => st' i (b i)) fun i hi r => (hp i hi).2.2 (b i) r

/-- The coin of a challenge of step `j`. -/
theorem coinErased (j d : ℕ) (hIH : PlanErased prims K D W knownE knownB count L tg hist (j + 1) d) :
    CoinErased prims K D W knownE knownB count L tg hist j d := by
  intro next hs hRel
  refine erasedAt_congr prims K D W knownE knownB count L tg hist _ _ _
    (fun i => call (Sum.inl (Sum.inl 2)) >>= fun o => oracleStep (coinSearch K (hs i) o) >>= fun w =>
      (RealNetworkC1x.coinNext (hs i) (next i) o w).elim failure fun p =>
        (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p.1).run p.2)
    (fun i _ => coin_run K i (hs i) (next i)) ?_
  refine erasedAt_call prims K D W knownE knownB count L tg hist (2 * j + 2) (2 * d + 2)
    (fun _ => Sum.inl (Sum.inl 2)) _ (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C))
    (fun v => Sum.inl (Sum.inl (List.ofFn v))) (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit))
    (fun v r _ => coinOutputs D v r) (fun A st => coinRun_form K D A st) (fun v r _ hP => ?_) fun out => ?_
  · obtain ⟨i, hi, hnone⟩ := coin_link D _ v r hP
    refine deadAt_oracle prims K D _ none (fun i => coinSearch K (hs i) (coinOutputs D v r i)) _ fun w => ?_
    exact deadAt_of_eq prims K D _ _ fun A st => planDead K D A _ st _
      ⟨i, hi, by simp only [RealNetworkC1x.coinNext, hnone, Option.bind_none]⟩
  refine erasedAt_oracle prims K D W knownE knownB count L tg hist _ _ none
    (fun i => coinSearch K (hs i) (out i)) _ fun w => ?_
  refine erasedAt_elim prims K D W knownE knownB count L tg hist _ _
    (fun i => RealNetworkC1x.coinNext (hs i) (next i) (out i) (w i))
    (fun i p => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p.1).run p.2)
    (fun hdead A st => planDead K D A _ st _ hdead) (fun b hb => ?_)
  rw [show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by omega]
  refine hIH (fun i => (b i).1) (fun i => (b i).2) fun i hi => ?_
  have h := hb i hi
  simp only [RealNetworkC1x.coinNext, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨-, -, r, -, hr⟩ := h
  rw [← hr]
  exact hRel i hi r

/-- The first coin. -/
theorem startErased (hIH : PlanErased prims K D W knownE knownB count L tg hist 0 (halvings count)) :
    StartErased prims K D W knownE knownB count L tg hist := by
  intro next hs hRel
  refine erasedAt_congr prims K D W knownE knownB count L tg hist _ _ _
    (fun i => call (Sum.inl (Sum.inl 2)) >>= fun o => oracleStep (startSearch K count (hs i) o) >>= fun τ =>
      (startNext (hs i) (next i) o τ).elim failure fun p =>
        (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p.1).run p.2)
    (fun i _ => start_run K count i (hs i) (next i)) ?_
  refine erasedAt_call prims K D W knownE knownB count L tg hist 0 (2 * halvings count + 2)
    (fun _ => Sum.inl (Sum.inl 2)) _ (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C))
    (fun v => Sum.inl (Sum.inl (List.ofFn v))) (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit))
    (fun v r _ => coinOutputs D v r) (fun A st => coinRun_form K D A st) (fun v r _ hP => ?_) fun out => ?_
  · obtain ⟨i, hi, hnone⟩ := coin_link D _ v r hP
    refine deadAt_oracle prims K D _ [] (fun i => startSearch K count (hs i) (coinOutputs D v r i)) _ fun τ => ?_
    exact deadAt_of_eq prims K D _ _ fun A st => planDead K D A _ st _
      ⟨i, hi, by simp only [startNext, hnone, Option.bind_none]⟩
  refine erasedAt_oracle prims K D W knownE knownB count L tg hist _ _ []
    (fun i => startSearch K count (hs i) (out i)) _ fun τ => ?_
  refine erasedAt_elim prims K D W knownE knownB count L tg hist _ _
    (fun i => startNext (hs i) (next i) (out i) (τ i))
    (fun i p => (runPlan K (localContext i) (hybridCheckBuildingBlocks K i) p.1).run p.2)
    (fun hdead A st => planDead K D A _ st _ hdead) (fun b hb => ?_)
  rw [show 0 + 1 = 2 * 0 + 1 by omega]
  refine hIH (fun i => (b i).1) (fun i => (b i).2) fun i hi => ?_
  have h := hb i hi
  simp only [startNext, Option.bind_eq_some_iff] at h
  obtain ⟨-, -, h⟩ := h
  split_ifs at h
  rw [← Option.some_inj.1 h]
  exact hRel i hi (τ i)

/-- The claim for the whole head. -/
theorem headErased : StartErased prims K D W knownE knownB count L tg hist := by
  have hall : ∀ d j, j + d = halvings count → PlanErased prims K D W knownE knownB count L tg hist j d := by
    intro d
    induction d with
    | zero => exact fun j _ => maskErased prims K D W knownE knownB count L tg hist j
    | succ d ih =>
      intro j h
      exact extendErased prims K D W knownE knownB count L tg hist j d
        (coinErased prims K D W knownE knownB count L tg hist j d (ih (j + 1) (by omega)))
  exact startErased prims K D W knownE knownB count L tg hist (hall _ 0 (by omega))

end Blocks

/-! ## The check -/

section Check

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
  (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
  (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg : ℕ)
  (hist : C.Party → C.Term → List Bit)

/-- The claim for the rest of the check after a full head. In the rest only the round tail of the
digest round differs between the two wrappers. -/
def RestErased : Prop :=
  ∀ (s : W.State × C1Memory C E) (b : C.Party → HeadOut C E × RunState C),
    OutEq prims
      (executePhase localRoles D (c1Wrapper K D W knownE knownB count L tg hist) (checkFunctionalities K) 5
        (s, 2 * halvings count + 3) (fun i => restAt K i (b i)))
      (executePhase localRoles D (c1Erased K D W knownE knownB hist) (checkFunctionalities K) 5
        (s, 2 * halvings count + 3) (fun i => restAt K i (b i)))

omit [Fintype E] [DecidableEq E] in
/-- The rest after an output of the head with a missing honest output gives no output. -/
theorem rest_dead (A : CheckAdversary C E Ia) (st : A.State) (o : C.Party → Option (HeadOut C E × RunState C))
    (ho : ¬ Full D o) :
    executePhase localRoles D A (checkFunctionalities K) 5 st (fun i => (o i).elim failure (restAt K i)) =
      pure (st, fun _ => none) := by
  by_cases hp : PartialOut D o
  · exact restAbort K D A st o hp
  · have hnone : ∀ i, i ∉ D.1 → o i = none := by
      intro i hi
      by_contra hne
      refine hp ⟨?_, i, hi, Option.isSome_iff_ne_none.2 hne⟩
      by_contra hall
      push Not at hall
      exact ho fun j hj => Option.isSome_iff_ne_none.2 (hall j hj)
    obtain ⟨i₀, hi₀⟩ := exists_honest D
    refine executePhase_dead D A _ 5 st _ (fun i hi => Or.inl (by rw [hnone i hi]; rfl))
      ⟨i₀, hi₀, by rw [hnone i₀ hi₀]; rfl⟩

/-- The tails of the replies and of the rounds of `c1Wrapper` do not change the distribution of the
outputs of the check, from each cache, when the rest of the check has the same property. -/
theorem tailErasure_of_rest (counts : List ℕ) (x : C.Party → List (Tuple C)) (st : W.State)
    (hx : ∀ i, i ∉ D.1 → (x i).map (·.count) = counts)
    (hrest : RestErased prims K D W knownE knownB counts.sum L tg (knownHist K D x)) :
    OutEq prims
      (executePhase localRoles D (c1Wrapper K D W knownE knownB counts.sum L tg (knownHist K D x))
        (checkFunctionalities K) (checkRounds counts.sum) ((st, ⟨knownHist K D x, []⟩), 0) (checkAt K L tg x))
      (executePhase localRoles D (c1Erased K D W knownE knownB (knownHist K D x))
        (checkFunctionalities K) (checkRounds counts.sum) ((st, ⟨knownHist K D x, []⟩), 0) (checkAt K L tg x)) := by
  by_cases hsum : counts.sum = 0
  · have hz : ∀ (A : CheckAdversary C E Ia) (s : A.State),
        executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) s (checkAt K L tg x) =
          pure (s, fun i => if i ∈ D.1 then none else some ()) := by
      intro A s
      rw [← executePhase_pure D A _ (checkRounds counts.sum) s ()]
      refine executePhase_congr D A _ _ s _ _ fun i hi => ?_
      unfold checkAt
      rw [check_of_count_eq_zero K _ _ (x i) (by rw [hx i hi]; exact hsum)]
      simp only [StateT.run'_eq, StateT.run_pure, map_pure]
    rw [hz, hz]
    exact outEq_pure _ _ _
  refine (OutEq.of_sameRun (RealNetworkC1p.hybridCut prims K D _ counts L tg x _ hsum hx)).trans
    (OutEq.trans ?_ (OutEq.of_sameRun (RealNetworkC1p.hybridCut prims K D _ counts L tg x _ hsum hx)).symm)
  rw [executePhase_congr D _ (checkFunctionalities K) _ _ (headAt K L tg x) _ (headAt_eq K D counts L tg x hx),
    executePhase_congr D _ (checkFunctionalities K) _ _ (headAt K L tg x) _ (headAt_eq K D counts L tg x hx)]
  refine headErased prims K D W knownE knownB counts.sum L tg (knownHist K D x)
    (fun i τ => headPlan K (localContext i) τ (x i)) (fun i => ⟨filledHistory K i (x i), L, tg⟩)
    (fun i hi τ => by
      have h := planOK_headPlan K (localContext i) τ (x i)
      rwa [hx i hi] at h) (st, ⟨knownHist K D x, []⟩) _ _ (fun r hr hc => ?_) (fun r hr => ?_)
  · obtain ⟨⟨s', n'⟩, o⟩ := r
    simp only at hr hc
    subst hc
    obtain ⟨i₀, hi₀⟩ := exists_honest D
    obtain ⟨b₀, -⟩ := Option.isSome_iff_exists.1 (hr i₀ hi₀)
    let b : C.Party → HeadOut C E × RunState C := fun i => (o i).getD b₀
    have hb : ∀ i, i ∉ D.1 → (o i).elim failure (restAt K i) = restAt K i (b i) := fun i hi => by
      obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (hr i hi)
      simp only [b, hz, Option.getD_some, Option.elim_some]
    simp only
    rw [executePhase_congr_honest D _ _ 5 _ _ _ hb, executePhase_congr_honest D _ _ 5 _ _ _ hb]
    rw [show 0 + (2 * halvings counts.sum + 3) = 2 * halvings counts.sum + 3 by omega]
    exact hrest s' b
  · constructor
    · rw [rest_dead K D _ _ _ hr]
      exact outNone_pure _
    · rw [rest_dead K D _ _ _ hr]
      exact outNone_pure _

omit [Fintype E] [DecidableEq E] in
/-- A reply of `c1Erased` makes the counted calls of one round of `W`. -/
theorem c1Erased_answer_counted (step : ℕ) (hr : ∀ st m, IsQueryBoundP (W.round st m) Counted step)
    (s : (c1Erased K D W knownE knownB hist).State) (l : CheckLeak C E) :
    IsQueryBoundP ((c1Erased K D W knownE knownB hist).answer s l) Counted step := by
  simpa using roundScheduled_answer_counted D
    (relabel (withMemory W (C1Memory C E) ⟨hist, []⟩) (checkReply (C := C) (E := E)))
    (c1Sims K D W knownE knownB) c1Names RealNetworkGP.noTails (fun _ => digestSurv D) RealNetworkGP.noTails step 0
    (RealNetworkC1p.c1SimsCounted K D W knownE knownB step hr) (fun _ _ _ => isQueryBoundP_pure _ _ _) s l

omit [Fintype E] [DecidableEq E] in
/-- A round of `c1Erased` makes the counted calls of one round of `W`. -/
theorem c1Erased_round_counted (step : ℕ) (hr : ∀ st m, IsQueryBoundP (W.round st m) Counted step)
    (s : (c1Erased K D W knownE knownB hist).State) (m : C.Party → C.Party → Option (Msg E)) :
    IsQueryBoundP ((c1Erased K D W knownE knownB hist).round s m) Counted step := by
  simpa using roundScheduled_round_counted D
    (relabel (withMemory W (C1Memory C E) ⟨hist, []⟩) (checkReply (C := C) (E := E)))
    (c1Sims K D W knownE knownB) c1Names RealNetworkGP.noTails (fun _ => digestSurv D) RealNetworkGP.noTails step 0
    (fun st m => (isQueryBoundP_map_iff (p := Counted) _ _ _).2 (hr st.1 m))
    (fun _ _ _ => isQueryBoundP_pure _ _ _) s m

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- Two runs with the same distribution of the outputs give each event on the outputs with the same
probability. -/
theorem OutEq.prob_eq {S S' α : Type} {oa : OracleComp (LocalSpec C) (S × (C.Party → Option α))}
    {ob : OracleComp (LocalSpec C) (S' × (C.Party → Option α))} (h : OutEq prims oa ob) (cache : HashCache C)
    (P : (C.Party → Option α) → Prop) :
    Pr{let out ← (simulateQ (localAnswer prims) oa).run' cache}[P out.2] =
      Pr{let out ← (simulateQ (localAnswer prims) ob).run' cache}[P out.2] := by
  have := (h cache).prEvent_eq P
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] at this
  simpa only [StateT.run'_eq, prEvent_map, Function.comp_def] using this

end Check

/-! ## The rest of the check -/

section Rest

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
  (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
  (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg : ℕ)
  (hist : C.Party → C.Term → List Bit)

omit [Fintype E] [DecidableEq E] in
/-- A round of `c1Erased` is a round of `W`. -/
theorem c1Erased_round (st : W.State) (mem : C1Memory C E) (k : ℕ) (m : C.Party → C.Party → Option (Msg E)) :
    (c1Erased K D W knownE knownB hist).round ((st, mem), k) m =
      (fun r => ((((r.1, mem), k) : (c1Erased K D W knownE knownB hist).State), r.2)) <$> W.round st m := by
  simp only [c1Erased, relabel, withMemory, RealNetworkGP.noTails, map_pure, bind_map_left, ite_self]
  rw [map_eq_bind_pure_comp]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- The reply of `c1Erased` to `F_rand` for bits runs no tail. -/
theorem erased_frandBits_answer (s : W.State × C1Memory C E) (k : ℕ) :
    (rightAdversary (rightAdversary (c1Erased K D W knownE knownB hist))).answer (s, k) () =
      (pure (((s, k + 1) : (c1Erased K D W knownE knownB hist).State), knownB) :
        OracleComp (LocalSpec C) _) := by
  simp only [rightAdversary, c1Sims,
    RealNetworkC1u.frand_not_partial_names D c1Names (c1Names_receivers D), ite_false]
  rfl

omit [Fintype E] in
/-- The round of `OpenSh` at the end of the check, at a position other than the digest round. The
cases follow `openRound`. -/
theorem openEq (st : W.State) (mem : C1Memory C E) (k : ℕ) (hk : k ≠ 2 * halvings count + 4)
    (o : C.Party → Option (HeadOut C E × E × RunState C)) :
    OutEq prims
      (executePhase localRoles D (c1Wrapper K D W knownE knownB count L tg hist) (checkFunctionalities K) 2
        ((st, mem), k) (fun i => (o i).elim failure fun z => (openTailOf K (localContext i) z.1 z.2.1).run' z.2.2))
      (executePhase localRoles D (c1Erased K D W knownE knownB hist) (checkFunctionalities K) 2
        ((st, mem), k) (fun i => (o i).elim failure fun z => (openTailOf K (localContext i) z.1 z.2.1).run' z.2.2)) := by
  by_cases hnone : ∀ i ∉ D.1, o i = none
  · rw [executePhase_congr_honest D _ _ 2 _ _ (fun _ => failure) (fun i hi => by simp only [hnone i hi, Option.elim_none]),
      executePhase_failure, executePhase_congr_honest D _ _ 2 _ _ (fun _ => failure)
        (fun i hi => by simp only [hnone i hi, Option.elim_none]), executePhase_failure]
    exact outEq_pure _ _ _
  by_cases hfull : ∀ i ∉ D.1, (o i).isSome
  · have hprog {I O : Type} : ∀ i, i ∉ D.1 →
        ((o i).elim failure fun z => (openTailOf (G := CallSpec I O) K (localContext i) z.1 z.2.1).run' z.2.2) =
          exchange ((o i).elim (fun _ => none) fun z => RealNetworkC1t.openTailOut K (localContext i) z.1 z.2.1) >>= fun inbox =>
            OptionT.mk (pure ((o i).elim none fun z => RealNetworkC1t.openTailRes K (localContext i) z.1 z.2.1 inbox)) := by
      intro i hi
      obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (hfull i hi)
      simp only [hz, Option.elim_some]
      exact RealNetworkC1t.openTailOf_run' K (localContext i) z.1 z.2.1 z.2.2
    rw [RealNetworkC1q.roundPhase_full D _ _ _ _ _ hprog 1, RealNetworkC1q.roundPhase_full D _ _ _ _ _ hprog 1,
      RealNetworkC1t.c1Wrapper_round K D W knownE knownB count hist c1Names _ st mem k hk, c1Erased_round]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    exact OutEq.bind_right _ fun r => outEq_pure _ _ _
  · have hp : RealNetworkRC.PartialOut D o := by
      refine ⟨?_, ?_⟩
      · push Not at hfull
        obtain ⟨i, hi, h⟩ := hfull
        exact ⟨i, hi, Option.not_isSome_iff_eq_none.1 h⟩
      · push Not at hnone
        obtain ⟨i, hi, h⟩ := hnone
        exact ⟨i, hi, Option.isSome_iff_ne_none.2 h⟩
    have h := fun (A : CheckAdversary C E Ia) (s : A.State) => RealNetworkRC.roundPhase_partial D A
      (checkFunctionalities K)
      (fun i (z : HeadOut C E × E × RunState C) => (openTailOf K (localContext i) z.1 z.2.1).run' z.2.2)
      (fun i z => RealNetworkC1t.openTailOut K (localContext i) z.1 z.2.1)
      (fun i z inbox => OptionT.mk (pure (RealNetworkC1t.openTailRes K (localContext i) z.1 z.2.1 inbox)))
      (fun i z => by rw [RealNetworkC1t.openTailOf_run', advance_exchange_bind]) 1 s o hp
    rw [h, h]
    exact OutEq.of_outNone (OutNone.bind _ fun _ => outNone_pure _) (OutNone.bind _ fun _ => outNone_pure _)

omit [Fintype E] [DecidableEq E] in
/-- After a partial digest round the call of `F_coin` does not run, on each adversary. -/
theorem digest_abort (A : CheckAdversary C E Ia) (s : A.State) (o : C.Party → Option Unit) (hpO : PartialOut D o)
    (v : C.Party → HeadOut C E) (hs : C.Party → RunState C) :
    executePhase localRoles D A (checkFunctionalities K) 3 s (fun i => (o i).elim failure fun _ =>
      (challenge K (hybridCheckBuildingBlocks K i) >>= fun r => openTailOf K (localContext i) (v i) r).run' (hs i)) =
      pure (s, fun _ => none) := by
  have hg := fun i => RealNetworkC1t.hybridChallenge_call K i (hs i) (v i)
  choose g hgn hgeq using hg
  have hprog : (fun i => (o i).elim failure fun _ =>
      (challenge K (hybridCheckBuildingBlocks K i) >>= fun r => openTailOf K (localContext i) (v i) r).run' (hs i)) =
      fun i => optionalCall ((o i).map fun _ => Sum.inl (Sum.inl 2)) (fun c => (o i).elim failure fun _ => g i c) := by
    funext i
    cases o i with
    | none => rfl
    | some u => exact hgeq i
  rw [hprog]
  refine executePhase_partialCall_abort D _ _ 2 s _ _ (fun i _ => ?_) ?_
  · cases o i with
    | none => rfl
    | some u => exact hgn i
  · obtain ⟨⟨i, hi, h⟩, -⟩ := hpO
    exact ⟨i, hi, by simp only [h, Option.map_none]⟩

omit [Fintype E] in
/-- The search of the last challenge and the round of `OpenSh`, after the last coin. -/
theorem searchEq (st : W.State) (mem : C1Memory C E) (v : C.Party → HeadOut C E) (hs : C.Party → RunState C)
    (O : C.Party → Option (List E)) :
    OutEq prims
      (executePhase localRoles D (c1Wrapper K D W knownE knownB count L tg hist) (checkFunctionalities K) 2
        ((st, mem), 2 * halvings count + 4 + 1) (fun i => (O i).elim failure (RealNetworkC1t.restC K i (hs i) (v i))))
      (executePhase localRoles D (c1Erased K D W knownE knownB hist) (checkFunctionalities K) 2
        ((st, mem), 2 * halvings count + 4 + 1)
        (fun i => (O i).elim failure (RealNetworkC1t.restC K i (hs i) (v i)))) := by
  let q : C.Party → OracleComp (RoSpec C) (Option E) := fun i => match O i with
    | some vals => challengeQuery K (hs i).tag (hs i).label vals
    | none => pure none
  let g : C.Party → Option E → PartyM C E (CheckSpec C E) Unit := fun i c => (O i).elim failure fun _ =>
    match c with
    | some r => (openTailOf K (localContext i) (v i) r).run' ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩
    | none => failure
  have hprog : ∀ i, i ∉ D.1 → (O i).elim failure (RealNetworkC1t.restC K i (hs i) (v i)) =
      oracleStep (q i) >>= g i := by
    intro i _
    cases hO : O i with
    | none => simp only [q, g, hO, Option.elim_none, oracleStep_pure, pure_bind]
    | some vals =>
      simp only [q, g, hO, Option.elim_some, RealNetworkC1t.restC]
      rfl
  rw [executePhase_congr_honest D _ _ 2 _ _ _ hprog, executePhase_congr_honest D _ _ 2 _ _ _ hprog]
  refine (OutEq.of_sameRun (executePhase_oracleStep_bind prims D _ (checkFunctionalities K) none 2 _ q g)).trans
    (OutEq.trans (OutEq.bind_right _ fun w => ?_)
      (OutEq.of_sameRun (executePhase_oracleStep_bind prims D _ (checkFunctionalities K) none 2 _ q g)).symm)
  let o' : C.Party → Option (HeadOut C E × E × RunState C) := fun i =>
    (O i).bind fun _ => (w i).map fun r => (v i, r, ⟨(hs i).history, (hs i).label + 1, (hs i).tag⟩)
  have hw : ∀ i, i ∉ D.1 → g i (w i) =
      (o' i).elim failure fun z => (openTailOf K (localContext i) z.1 z.2.1).run' z.2.2 := by
    intro i _
    cases hO : O i with
    | none => simp only [g, o', hO, Option.elim_none, Option.bind_none]
    | some vals =>
      cases hwi : w i with
      | none => simp only [g, o', hO, hwi, Option.elim_some, Option.bind_some, Option.map_none, Option.elim_none]
      | some r => simp only [g, o', hO, hwi, Option.elim_some, Option.bind_some, Option.map_some]
  rw [executePhase_congr_honest D _ _ 2 _ _ _ hw, executePhase_congr_honest D _ _ 2 _ _ _ hw]
  exact openEq prims K D W knownE knownB count L tg hist st mem _ (by omega) o'

/-- The last coin at `2 R + 4`. Its tail is the identity in both wrappers. -/
theorem coinEq (st : W.State) (mem : C1Memory C E) (v : C.Party → HeadOut C E) (hs : C.Party → RunState C) :
    OutEq prims
      (executePhase localRoles D (c1Wrapper K D W knownE knownB count L tg hist) (checkFunctionalities K) 3
        ((st, mem), 2 * halvings count + 4)
        (fun i => (challenge K (hybridCheckBuildingBlocks K i) >>= fun r =>
          openTailOf K (localContext i) (v i) r).run' (hs i)))
      (executePhase localRoles D (c1Erased K D W knownE knownB hist) (checkFunctionalities K) 3
        ((st, mem), 2 * halvings count + 4)
        (fun i => (challenge K (hybridCheckBuildingBlocks K i) >>= fun r =>
          openTailOf K (localContext i) (v i) r).run' (hs i))) := by
  have hct : ∀ (live : Finset C.Party) (s : W.State × C1Memory C E),
      c1Tails K D W knownE knownB count L tg (2 * halvings count + 4) live s = pure s := fun live s => by
    simp only [c1Tails, show 2 * halvings count + 4 ≠ 0 by omega,
      show 2 * halvings count + 4 ≠ 2 * halvings count + 2 by omega,
      show 2 * halvings count < 2 * halvings count + 4 by omega, ↓reduceIte]
  rw [show 3 = 1 + 2 by rfl,
    executePhase_congr_honest D _ _ _ _ _
      (fun i => RealNetworkGP.callProg (Sum.inl (Sum.inl 2)) coinOutput >>= RealNetworkC1t.restC K i (hs i) (v i))
      (fun i _ => RealNetworkC1t.hybridChallenge_split K i (hs i) (v i)),
    executePhase_congr_honest D _ _ _ _ _
      (fun i => RealNetworkGP.callProg (Sum.inl (Sum.inl 2)) coinOutput >>= RealNetworkC1t.restC K i (hs i) (v i))
      (fun i _ => RealNetworkC1t.hybridChallenge_split K i (hs i) (v i))]
  refine (OutEq.of_sameRun (executePhase_bind prims D _ _ 1 2 _ _ _
    fun i _ => RealNetworkC1t.timed_callProg _ _)).trans (OutEq.trans ?_
      (OutEq.of_sameRun (executePhase_bind prims D _ _ 1 2 _ _ _
        fun i _ => RealNetworkC1t.timed_callProg _ _)).symm)
  have e := fun (A : CheckAdversary C E Ia) => RealNetworkGP.callPhase_eq D (checkFunctionalities K)
    (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput) (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C))
    (fun v => Sum.inl (Sum.inl (List.ofFn v))) (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit))
    (fun v r _ => coinOutputs D v r) A (fun st => coinRun_form K D A st) 0
  unfold RealNetworkGP.callPhase at e
  simp only [Nat.zero_add] at e
  rw [e, e]
  simp only [bind_assoc, pure_bind]
  refine OutEq.bind_right _ fun cv => ?_
  exact outEq_reply_pure _ _ _ _ _ _ _ (fun a _ => hct _ _) (fun a _ => rfl) fun a =>
    searchEq prims K D W knownE knownB count L tg hist a.1.1 a.1.2 v hs _

/-- The digest round at `2 R + 4`. Its round tail runs only after a partial round, and then the call of
`F_coin` does not run under both wrappers. After each other round both wrappers reach the same state. -/
theorem digestEq (st : W.State) (mem : C1Memory C E) (salts : C.Party → Shares C Bit) (v : C.Party → HeadOut C E)
    (hs : C.Party → RunState C) :
    OutEq prims
      (executePhase localRoles D (c1Wrapper K D W knownE knownB count L tg hist) (checkFunctionalities K) 4
        ((st, mem), 2 * halvings count + 4)
        (fun i => (compareDigests (localContext i) (salts i) >>= fun _ =>
          challenge K (hybridCheckBuildingBlocks K i) >>= fun r => openTailOf K (localContext i) (v i) r).run' (hs i)))
      (executePhase localRoles D (c1Erased K D W knownE knownB hist) (checkFunctionalities K) 4
        ((st, mem), 2 * halvings count + 4)
        (fun i => (compareDigests (localContext i) (salts i) >>= fun _ =>
          challenge K (hybridCheckBuildingBlocks K i) >>= fun r => openTailOf K (localContext i) (v i) r).run' (hs i))) := by
  let restH : C.Party → PartyM C E (CheckSpec C E) Unit := fun i =>
    (challenge K (hybridCheckBuildingBlocks K i) >>= fun r => openTailOf K (localContext i) (v i) r).run' (hs i)
  let oa : C.Party → OracleComp (LocalSpec C) (List HashOutput) := fun i =>
    liftComp (digestQuery i (salts i) (hs i).history) (LocalSpec C)
  have hblk : ∀ i, i ∉ D.1 → (compareDigests (localContext i) (salts i) >>= fun _ =>
      challenge K (hybridCheckBuildingBlocks K i) >>= fun r => openTailOf K (localContext i) (v i) r).run' (hs i) =
      localStep (oa i) >>= fun ds => RealNetworkC1t.digestBlk i ds >>= fun _ => restH i :=
    fun i _ => RealNetworkC1t.compareDigests_blk (E := E) i (salts i) _ (hs i)
  rw [executePhase_congr_honest D _ _ 4 _ _ _ hblk, executePhase_congr_honest D _ _ 4 _ _ _ hblk]
  refine (OutEq.of_sameRun (executePhase_local_fallback prims D _ _ 4 _ oa (fun _ => [])
    (fun i ds => RealNetworkC1t.digestBlk i ds >>= fun _ => restH i))).trans (OutEq.trans
      (OutEq.bind_right _ fun w => ?_) (OutEq.of_sameRun (executePhase_local_fallback prims D _ _ 4 _ oa
        (fun _ => []) (fun i ds => RealNetworkC1t.digestBlk i ds >>= fun _ => restH i))).symm)
  refine (OutEq.of_sameRun (executePhase_bind prims D _ _ 1 3 _ _ _
    fun i _ => RealNetworkC1t.timed_digestBlk i (w i))).trans (OutEq.trans ?_
      (OutEq.of_sameRun (executePhase_bind prims D _ _ 1 3 _ _ _
        fun i _ => RealNetworkC1t.timed_digestBlk i (w i))).symm)
  rw [RealNetworkC1t.digestPhase_full, RealNetworkC1t.digestPhase_full,
    RealNetworkC1t.c1Wrapper_round_digest, c1Erased_round]
  have hagree := RealNetworkC1t.digestOuts_surv (E := E) D w
  refine outEq_round (W.round st (RealNetworkC1t.digestView D w))
    (fun r => PartialOut D (survivors D (digestSurv D (RealNetworkC1t.digestView D w) r.2)))
    (fun r => RealNetworkC1s.coinTail K D W (knownE (2 * halvings count + 4)).1 (knownE (2 * halvings count + 4)).2 2
      (liveSet D (survivors D (digestSurv D (RealNetworkC1t.digestView D w) r.2))) r.1)
    (fun st' => (((st', mem), 2 * halvings count + 4) : (c1Wrapper K D W knownE knownB count L tg hist).State))
    (fun st' => (((st', mem), 2 * halvings count + 4) : (c1Erased K D W knownE knownB hist).State))
    (RealNetworkC1t.digestOuts D w) _ _ (fun a hP => ?_) (fun a hP => ?_)
  · have hpO : PartialOut D (RealNetworkC1t.digestOuts D w a.2) := by
      have hag := hagree a.2 (Or.inr hP)
      obtain ⟨⟨i, hi, h⟩, i', hi', h'⟩ := hP
      refine ⟨⟨i, hi, ?_⟩, i', hi', by rw [hag i' hi']; exact h'⟩
      have := hag i hi
      rw [h, Option.isSome_none] at this
      exact Option.not_isSome_iff_eq_none.1 (by rw [this]; decide)
    exact ⟨fun st' => by
      dsimp only
      rw [digest_abort K D _ _ _ hpO v hs]
      exact outNone_pure _, by
      dsimp only
      rw [digest_abort K D _ _ _ hpO v hs]
      exact outNone_pure _⟩
  · have hnp : ¬ PartialOut D (RealNetworkC1t.digestOuts D w a.2) := fun h => by
      have hag := hagree a.2 (Or.inl h)
      obtain ⟨⟨i, hi, hn⟩, i', hi', hs'⟩ := h
      refine hP ⟨⟨i, hi, ?_⟩, i', hi', by rw [← hag i' hi']; exact hs'⟩
      have := hag i hi
      rw [hn, Option.isSome_none] at this
      exact Option.not_isSome_iff_eq_none.1 (by rw [← this]; decide)
    dsimp only
    by_cases hnone : ∀ i, i ∉ D.1 → RealNetworkC1t.digestOuts D w a.2 i = none
    · rw [executePhase_congr_honest D _ _ 3 _ _ (fun _ => failure)
          (fun i hi => by simp only [hnone i hi, Option.elim_none]), executePhase_failure,
        executePhase_congr_honest D _ _ 3 _ _ (fun _ => failure)
          (fun i hi => by simp only [hnone i hi, Option.elim_none]), executePhase_failure]
      exact outEq_pure _ _ _
    have hfull : ∀ i, i ∉ D.1 → (RealNetworkC1t.digestOuts D w a.2 i).isSome := by
      intro i hi
      by_contra hni
      push Not at hnone
      obtain ⟨j, hj, hjs⟩ := hnone
      exact hnp ⟨⟨i, hi, Option.not_isSome_iff_eq_none.1 hni⟩, j, hj, Option.isSome_iff_ne_none.2 hjs⟩
    have hp : ∀ i, i ∉ D.1 → (RealNetworkC1t.digestOuts D w a.2 i).elim failure (fun _ => restH i) = restH i := by
      intro i hi
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hfull i hi)
      rw [hu]
      rfl
    rw [executePhase_congr_honest D _ _ 3 _ _ _ hp, executePhase_congr_honest D _ _ 3 _ _ _ hp]
    exact coinEq prims K D W knownE knownB count L tg hist a.1 mem v hs

omit [DecidableEq E] in
/-- The rest of the check starts with the call of `F_rand` for the salts. Its reply is `knownB` in both
wrappers. -/
theorem rest_salts (A : CheckAdversary C E Ia) (s s' : A.State)
    (hans : (rightAdversary (rightAdversary A)).answer s () = pure (s', knownB))
    (b : C.Party → HeadOut C E × RunState C) :
    executePhase localRoles D A (checkFunctionalities K) 5 s (fun i => restAt K i (b i)) = (do
      let sa ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
      let sb ← liftComp ($ᵗ (C.Pair → Fin 256 → Bit)) (LocalSpec C)
      executePhase localRoles D A (checkFunctionalities K) 4 s' fun i =>
        (compareDigests (localContext i) (frandShare D 256 knownB.1 knownB.2 sa sb i).1 >>= fun _ =>
          challenge K (hybridCheckBuildingBlocks K i) >>= fun r => openTailOf K (localContext i) (b i).1 r).run'
          ⟨(b i).2.history, (b i).2.label + 1, (b i).2.tag⟩) := by
  unfold restAt
  simp only [RealNetworkC1u.checkRest_eq]
  rw [executePhase_randBits K D _ 4 _ (fun _ => 256) (fun i => (b i).2) (fun i salts =>
      compareDigests (localContext i) salts.1 >>= fun _ => challenge K (hybridCheckBuildingBlocks K i) >>= fun r =>
        openTailOf K (localContext i) (b i).1 r),
    runFunctionality_rand_local D _ _ _ (by intro i hi; simp [hi]), firstInput_honest_const, hans, pure_bind]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun sa => bind_congr fun sb => ?_
  refine executePhase_congr_honest D _ _ 4 _ _ _ fun i hi => ?_
  simp only [randFinish, hi, ite_false]
  rfl

/-- `RestErased` holds. -/
theorem restErased : RestErased prims K D W knownE knownB count L tg hist := by
  intro s b
  rw [rest_salts K D knownB _ _ _ (RealNetworkC1u.frandBits_answer K D W knownE knownB count hist c1Names
      (c1Names_receivers D) _ s _) b,
    rest_salts K D knownB _ _ _ (erased_frandBits_answer K D W knownE knownB hist s _) b]
  refine OutEq.bind_right _ fun sa => OutEq.bind_right _ fun sb => ?_
  exact digestEq prims K D W knownE knownB count L tg hist s.1 s.2 _ (fun i => (b i).1) _

end Rest

/-! ## The result -/

section Result

variable (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
  (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
  (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (L tg : ℕ)

/-- The tails of the replies and of the rounds of `c1Wrapper` do not change the distribution of the
outputs of the check, from each cache. -/
theorem tailErasure (counts : List ℕ) (x : C.Party → List (Tuple C)) (st : W.State)
    (hx : ∀ i, i ∉ D.1 → (x i).map (·.count) = counts) :
    OutEq prims
      (executePhase localRoles D (c1Wrapper K D W knownE knownB counts.sum L tg (knownHist K D x))
        (checkFunctionalities K) (checkRounds counts.sum) ((st, ⟨knownHist K D x, []⟩), 0) (checkAt K L tg x))
      (executePhase localRoles D (c1Erased K D W knownE knownB (knownHist K D x))
        (checkFunctionalities K) (checkRounds counts.sum) ((st, ⟨knownHist K D x, []⟩), 0) (checkAt K L tg x)) :=
  tailErasure_of_rest prims K D W knownE knownB L tg counts x st hx
    (restErased prims K D W knownE knownB counts.sum L tg (knownHist K D x))

/-- The event of `checkSoundFrom`, that an honest operator accepts, together with any proposition `Q`
that does not read the run (for example `WrongTuple D x`), has the same probability under `c1Wrapper`
and under `c1Erased`, from each cache. -/
theorem accept_eq (counts : List ℕ) (x : C.Party → List (Tuple C)) (st : W.State)
    (hx : ∀ i, i ∉ D.1 → (x i).map (·.count) = counts) (cache : HashCache C) (Q : Prop) :
    Pr{let out ← (simulateQ (localAnswer prims)
        (executePhase localRoles D (c1Wrapper K D W knownE knownB counts.sum L tg (knownHist K D x))
          (checkFunctionalities K) (checkRounds counts.sum) ((st, ⟨knownHist K D x, []⟩), 0)
          (checkAt K L tg x))).run' cache}[(∃ i, i ∉ D.1 ∧ out.2 i = some ()) ∧ Q] =
      Pr{let out ← (simulateQ (localAnswer prims)
        (executePhase localRoles D (c1Erased K D W knownE knownB (knownHist K D x))
          (checkFunctionalities K) (checkRounds counts.sum) ((st, ⟨knownHist K D x, []⟩), 0)
          (checkAt K L tg x))).run' cache}[(∃ i, i ∉ D.1 ∧ out.2 i = some ()) ∧ Q] :=
  OutEq.prob_eq prims (tailErasure prims K D W knownE knownB L tg counts x st hx) cache
    fun o => (∃ i, i ∉ D.1 ∧ o i = some ()) ∧ Q

end Result

end ThresholdLeanXmssSecurity.TailErasure

end

end

/-- info: 'ThresholdLeanXmssSecurity.TailErasure.tailErasure_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TailErasure.tailErasure_of_rest

/-- info: 'ThresholdLeanXmssSecurity.TailErasure.headErased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TailErasure.headErased

/-- info: 'ThresholdLeanXmssSecurity.TailErasure.tailErasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TailErasure.tailErasure

/-- info: 'ThresholdLeanXmssSecurity.TailErasure.accept_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TailErasure.accept_eq
