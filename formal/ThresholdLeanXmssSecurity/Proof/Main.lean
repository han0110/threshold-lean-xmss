import ThresholdLeanXmssSecurity.Proof.Execution
import ThresholdLeanXmssSecurity.Proof.Lemmas
import VCVio.OracleComp.QueryTracking.Birthday

/-!
# A batch

`MainCompletenessStatement` follows from the honest run of a batch. `MainStatement` (GS20, Theorem 2)
reduces to its distance half `MainSecurityDistance`, which is open. `mainSimulator_queryBound` gives
the query half.
-/

open OracleComp OracleSpec LeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-! ## The reduction to the honest real run -/

section Honest

variable {κ : Type} {S : OracleSpec κ} {I L R : Type} (reply : L → R)

@[simp] theorem honestSimulator_start (x : C.Party → Option I) (z : Aux) :
    (honestSimulator (C := C) (S := S) (I := I) reply).start x z = pure () := rfl

@[simp] theorem honestSimulator_answer (st : (honestSimulator (C := C) (S := S) (I := I) reply).State) (l : L) :
    (honestSimulator (C := C) (S := S) (I := I) reply).answer st l = pure (st, reply l) := rfl

@[simp] theorem honestSimulator_output (st : (honestSimulator (C := C) (S := S) (I := I) reply).State) :
    (honestSimulator (C := C) (S := S) (I := I) reply).output st = pure () := rfl

end Honest

/-- The outputs of `F_main` on the inputs of a run with no coalition. -/
def mainOutputs (jobs : List Circuit) (x : C.Party → List (C.Term → List Bit)) : List (List Bit) :=
  jobs.zipIdx.map fun p => p.1.eval (inputValue (reconstruct fun i => (x i)[p.2]?))

/-- The ideal run of `F_main` with no coalition gives `mainOutputs` to every operator. -/
theorem fmain_honest_support (prims : Primitives) (jobs : List Circuit) (x : C.Party → List (C.Term → List Bit)) :
    ∀ r ∈ support (runWorld prims (idealExecution (fun oa => oa) noCoalition (Fmain jobs)
      (honestSimulator (S := WorldSpec C) fun _ => Finset.univ) x [])), r.1.2 = fun _ => some (mainOutputs jobs x) := by
  intro r hr
  simp only [runWorld, idealExecution, Fmain, leak, OracleComp.lift, simulateQ_bind, simulateQ_query,
    simulateQ_pure] at hr
  simp only [OracleQuery.input_query, OracleQuery.cont_query] at hr
  dsimp only [HAdd.hAdd, QueryImpl.add] at hr
  simp [noCoalition] at hr
  obtain ⟨_, _, rfl⟩ := hr
  rfl

/-- The honest real run of a batch, as `MainCompletenessStatement` runs it. -/
abbrev mainHonestRun (prims : Primitives) (K : Constants C E) (mode : ReshareMode) (jobs : List Circuit)
    (x : C.Party → List (C.Term → List Bit)) :=
  runWorld prims (realExecution noCoalition (honestAdversary mainReply) (mainFunctionalities K mode)
    (depth jobs + 3) (mainProtocol K mode jobs) x [])

omit [Fintype E] [DecidableEq E] in
/-- `MainCompletenessStatement` follows from the support of the honest real run. -/
theorem mainCompleteness_of_real (prims : Primitives) (K : Constants C E)
    (hreal : ∀ mode jobs x, MainInputs jobs noCoalition x →
      ∀ r ∈ support (mainHonestRun prims K mode jobs x), r.1.2 = fun _ => some (mainOutputs jobs x)) :
    MainCompletenessStatement prims K := by
  intro mode jobs x hx
  refine le_of_eq ((tvDist_eq_zero_iff _ _).2 ?_)
  refine (evalDist_eq_pure_of_support _ (fun _ => some (mainOutputs jobs x)) ?_).trans
    (evalDist_eq_pure_of_support _ (fun _ => some (mainOutputs jobs x)) ?_).symm
  · intro y hy
    rw [support_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    exact hreal mode jobs x hx r hr
  · intro y hy
    rw [support_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    exact fmain_honest_support prims jobs x r hr

/-! ## Value-level facts of the honest run -/

omit [Fintype E] [DecidableEq E] in
/-- The `MulRep` shares of views that agree with one sharing on the held terms sum to the product of
the shared values (CDI05, Section 4). -/
theorem mulRep_views_sum {R : Type} [CommRing R] (K : Constants C E) (xv yv : C.Party → Shares C R)
    (x y : Shares C R) (g : ℕ) (hx : ∀ i T, i ∈ C.holders T → xv i T g = x T g)
    (hy : ∀ i T, i ∈ C.holders T → yv i T g = y T g) :
    ∑ i, mulRep K (localContext i) (xv i) (yv i) g = shareValue x g * shareValue y g := by
  have h : ∀ i, mulRep K (localContext i) (xv i) (yv i) g = ∑ AB ∈ K.pairs i, x AB.1 g * y AB.2 g := by
    intro i
    refine Finset.sum_congr rfl fun AB hAB => ?_
    obtain ⟨h1, h2⟩ := K.pairs_held i AB hAB
    rw [hx i AB.1 h1, hy i AB.2 h2]
  simp_rw [h]
  rw [sum_sum_pairs K (fun AB => x AB.1 g * y AB.2 g), shareValue, shareValue, Finset.sum_mul_sum,
    ← Finset.sum_product', Finset.univ_product_univ]

/-- The empty coalition lacks a term, so `F_mult` puts the product in it. -/
theorem lackedTerm_empty_isSome : (lackedTerm (∅ : Finset C.Party)).isSome := by
  classical
  obtain ⟨T⟩ : Nonempty C.Term := by
    obtain ⟨T, -, hT⟩ := Finset.exists_superset_card_eq (s := (∅ : Finset C.Party))
      (n := C.t - 1) (by simp) (by simp [Committee.n]; omega)
    exact ⟨⟨T, hT⟩⟩
  rw [lackedTerm, List.find?_isSome]
  exact ⟨T, Finset.mem_toList.2 (Finset.mem_univ T), by simp [KnownTo]⟩

/-- The terms of an `F_mult` output sum to the target, as one term `T₀` takes the rest of the sum. -/
theorem sum_lacked {R : Type} [AddCommGroup R] (T₀ : C.Term) (base : Shares C R) (target : ℕ → R) (g : ℕ) :
    ∑ T, (if T₀ = T then target g - ∑ T' ∈ Finset.univ.erase T, base T' g else base T g) = target g := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ T₀), if_pos rfl]
  have : ∑ T ∈ Finset.univ.erase T₀, (if T₀ = T then target g - ∑ T' ∈ Finset.univ.erase T, base T' g
      else base T g) = ∑ T ∈ Finset.univ.erase T₀, base T g :=
    Finset.sum_congr rfl fun T hT => if_neg fun h => (Finset.ne_of_mem_erase hT) h.symm
  rw [this, sub_add_cancel]

/-- The sum of the shares of an affine function is its value on the shared wires, since only
`publicTerm` adds the constant. -/
theorem sum_affine_share (a : Affine) (w : C.Term → List Bit) (publicTerm : C.Term) (plain : List Bit)
    (hplain : ∀ k, plain.getD k 0 = ∑ T, (w T).getD k 0) :
    ∑ T, a.share w publicTerm T = a.eval plain := by
  simp only [Affine.share, Affine.eval, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, hplain]
  congr 1
  induction a.wires with
  | nil => simp
  | cons k ks ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- A copy at its place in the bundle of an owner (MPClan, App. B). -/
theorem getD_flatMap_vector (owned : List C.Term) (v : Shares C Bit) (count : ℕ) (T : C.Term)
    (hT : T ∈ owned) (hnodup : owned.Nodup) (g : ℕ) (hg : g < count) :
    (owned.flatMap fun T' => vector count (v T')).getD (count * owned.idxOf T + g) 0 = v T g := by
  induction owned with
  | nil => simp at hT
  | cons T' rest ih =>
    rw [List.flatMap_cons]
    by_cases h : T' = T
    · subst h
      simp [vector, List.getD_eq_getElem?_getD, List.getElem?_append_left, hg]
    · have hT : T ∈ rest := (List.mem_cons.1 hT).resolve_left (Ne.symm h)
      rw [List.idxOf_cons_ne _ h, List.getD_eq_getElem?_getD, List.getElem?_append_right
        (by simp [vector]; nlinarith), ← List.getD_eq_getElem?_getD]
      have := ih hT (List.nodup_cons.1 hnodup).2
      simp only [vector, List.length_map, List.length_range, Nat.mul_succ] at this ⊢
      rw [show count * List.idxOf T rest + count + g - count = count * List.idxOf T rest + g by omega]
      exact this

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

section Cache

variable {C : Committee} (prims : Primitives)

theorem support_withCost_run {α : Type} (c : (WorldSpec C).Domain → Multiplicative ℕ)
    (oa : OracleComp (WorldSpec C) α) (a : α) (w : Multiplicative ℕ) (s s₀ : HashCache C)
    (hmem : ((a, w), s) ∈ support ((simulateQ ((worldAnswer prims).withCost c) oa).run.run s₀)) :
    (a, s) ∈ support ((simulateQ (worldAnswer prims) oa).run s₀) := by
  rw [← QueryImpl.fst_map_run_withCost (worldAnswer prims) c oa, StateT.run_map, support_map]
  exact ⟨((a, w), s), hmem, rfl⟩

theorem support_runWorld {α : Type} (oa : OracleComp (WorldSpec C) α) (r : α × ℕ)
    (hr : r ∈ support (runWorld prims oa)) :
    ∃ s, (r.1, s) ∈ support ((simulateQ (worldAnswer prims) oa).run ∅) := by
  have hr' : r ∈ support (Prod.fst <$> ((simulateQ (world prims) oa).run.run ∅)) := hr
  rw [support_map] at hr'
  obtain ⟨⟨⟨a, w⟩, s⟩, hmem, hrr⟩ := hr'
  subst hrr
  exact ⟨s, support_withCost_run prims _ oa a w s ∅ hmem⟩

/-- The cache `s'` keeps every entry of `s`. -/
def Extends (s s' : HashCache C) : Prop := ∀ q v, s q = some v → s' q = some v

theorem Extends.refl (s : HashCache C) : Extends s s := fun _ _ h => h

theorem Extends.trans {s₁ s₂ s₃ : HashCache C} (h₁ : Extends s₁ s₂) (h₂ : Extends s₂ s₃) : Extends s₁ s₃ :=
  fun q v h => h₂ q v (h₁ q v h)

/-- A lazy random-oracle answer returns the cached value, or caches a fresh one. -/
theorem support_randomOracle (q : Query C) (σ : HashCache C) (z : HashOutput × HashCache C)
    (hz : z ∈ support (((Query C →ₒ HashOutput).randomOracle q).run σ)) :
    Extends σ z.2 ∧ z.2 q = some z.1 := by
  rw [randomOracle.apply_eq] at hz
  rcases hσ : σ q with _ | v
  · simp [StateT.run_bind, hσ, modifyGet, MonadStateOf.modifyGet] at hz
    obtain ⟨i, hi⟩ := hz
    have : z = (i, σ.cacheQuery q i) := by simpa [StateT.modifyGet, StateT.run] using hi
    subst this
    refine ⟨fun q' v hv => ?_, QueryCache.cacheQuery_self _ _ _⟩
    have hne : q' ≠ q := fun h => by subst h; rw [hσ] at hv; cases hv
    simpa [QueryCache.cacheQuery, Function.update_of_ne hne] using hv
  · simp [StateT.run_bind, hσ] at hz
    subst hz
    exact ⟨Extends.refl σ, hσ⟩

theorem support_hashAnswer (q : Query C) (σ : HashCache C) (z : HashOutput × HashCache C)
    (hz : z ∈ support ((hashAnswer prims q).run σ)) :
    Extends σ z.2 ∧ ((∀ input, q = .hash input → ¬ MpcInput input) → z.2 q = some z.1) := by
  cases q
  case hash input =>
    by_cases hm : MpcInput input
    · simp only [hashAnswer, hm, if_true] at hz
      simp at hz
      subst hz
      exact ⟨Extends.refl σ, fun h => absurd hm (h input rfl)⟩
    · simp only [hashAnswer, hm, if_false] at hz
      exact ⟨(support_randomOracle _ σ z hz).1, fun _ => (support_randomOracle _ σ z hz).2⟩
  all_goals exact ⟨(support_randomOracle _ σ z hz).1, fun _ => (support_randomOracle _ σ z hz).2⟩

theorem support_prgAnswer (x : PrgInput C) (σ : HashCache C) (z : Bit × HashCache C)
    (hz : z ∈ support ((prgAnswer prims x).run σ)) : Extends σ z.2 := by
  simp only [prgAnswer] at hz
  rw [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  simp at hz
  subst hz
  exact (support_hashAnswer prims _ σ y hy).1

theorem support_localAnswer_extends (t : (LocalSpec C).Domain) (σ : HashCache C) (z)
    (hz : z ∈ support ((localAnswer prims t).run σ)) : Extends σ z.2 := by
  rcases t with n | q | x
  · simp [localAnswer, unifFwdImpl] at hz
    obtain ⟨a, rfl⟩ := hz
    exact Extends.refl σ
  · exact (support_hashAnswer prims q σ z hz).1
  · exact support_prgAnswer prims x σ z hz

theorem support_programAnswer (x : Query C × HashOutput) (σ : HashCache C) (z : Bool × HashCache C)
    (hz : z ∈ support ((programAnswer x).run σ)) : Extends σ z.2 := by
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind] at hz
  split_ifs at hz with h
  · simp at hz
    subst hz
    exact Extends.refl σ
  · simp [StateT.run_bind] at hz
    subst hz
    intro q v hv
    have hne : q ≠ x.1 := fun hq => by subst hq; simp [hv] at h
    simpa [QueryCache.cacheQuery, Function.update_of_ne hne] using hv

theorem support_baseWorld_extends (t : (WorldSpec C).Domain) (σ : HashCache C) (z)
    (hz : z ∈ support ((worldAnswer prims t).run σ)) : Extends σ z.2 := by
  rcases t with (t | x) | t
  · exact support_localAnswer_extends prims t σ z hz
  · exact support_programAnswer x σ z hz
  · exact support_localAnswer_extends prims t σ z hz

/-- The cache of the world only grows. -/
theorem baseWorld_extends {α : Type} (oa : OracleComp (WorldSpec C) α) (σ : HashCache C) (z)
    (hz : z ∈ support ((simulateQ (worldAnswer prims) oa).run σ)) : Extends σ z.2 :=
  OracleComp.simulateQ_run_preservesInv (worldAnswer prims) (Extends σ)
    (fun t σ₀ h₀ z hz => h₀.trans (support_baseWorld_extends prims t σ₀ z hz)) oa σ (Extends.refl σ) z hz

end Cache

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

/-! ## The program of one operator -/

section Program

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}

def gatesAt (jobs : List Circuit) (layer : ℕ) : List (ℕ × Affine × Affine) :=
  jobs.zipIdx.flatMap fun (job, k) => (job.layers.getD layer []).map fun ab => (k, ab)

def layerX (K : Constants C E) (jobs : List Circuit) (layer : ℕ) (wires : List (C.Term → List Bit)) : Shares C Bit :=
  fun T g => match (gatesAt jobs layer)[g]? with
    | some (k, ab) => ab.1.share (wires.getD k fun _ => []) K.publicTerm T | none => 0

def layerY (K : Constants C E) (jobs : List Circuit) (layer : ℕ) (wires : List (C.Term → List Bit)) : Shares C Bit :=
  fun T g => match (gatesAt jobs layer)[g]? with
    | some (k, ab) => ab.2.share (wires.getD k fun _ => []) K.publicTerm T | none => 0

def appendLayer (jobs : List Circuit) (layer : ℕ) (wires : List (C.Term → List Bit)) (z : Shares C Bit) :
    List (C.Term → List Bit) :=
  wires.zipIdx.map fun (w, k) T => w T ++ (((gatesAt jobs layer).zipIdx.filter (·.1.1 = k)).map fun (_, g) => z T g)

def layerBody (K : Constants C E) (gadgets : RunGadgets C E G) (jobs : List Circuit) :
    List (C.Term → List Bit) × List (Tuple C) → ℕ → RunM C E G (List (C.Term → List Bit) × List (Tuple C)) :=
  fun p layer => do
    let z ← gadgets.mult (layerX K jobs layer p.1) (layerY K jobs layer p.1) (gatesAt jobs layer).length
    pure (appendLayer jobs layer p.1 z,
      p.2 ++ [⟨layerX K jobs layer p.1, layerY K jobs layer p.1, z, (gatesAt jobs layer).length, gadgets.mode⟩])

def outputsOf (jobs : List Circuit) : List (ℕ × Affine) := jobs.zipIdx.flatMap fun (job, k) => job.outputs.map fun a => (k, a)

def outputShares (K : Constants C E) (jobs : List Circuit) (wires : List (C.Term → List Bit)) : Shares C Bit :=
  fun T g => match (outputsOf jobs)[g]? with
    | some (k, a) => a.share (wires.getD k fun _ => []) K.publicTerm T | none => 0

def assemble (jobs : List Circuit) (opened : ℕ → Bit) : List (List Bit) :=
  (jobs.map (·.outputs.length)).zipIdx.map fun (width, k) =>
    vector width fun g => opened (((jobs.map (·.outputs.length)).take k).sum + g)

def tailBody (K : Constants C E) (gadgets : RunGadgets C E G) (jobs : List Circuit) :
    List (C.Term → List Bit) × List (Tuple C) → RunM C E G (List (List Bit)) := fun p => do
  let v' ← gadgets.rerand (outputShares K jobs p.1) (outputsOf jobs).length
  gadgets.verify (p.2 ++ [⟨outputShares K jobs p.1, one K, v', (outputsOf jobs).length, .peer⟩])
  let opened ← gadgets.output v' (outputsOf jobs).length
  pure (assemble jobs opened)

theorem runJobs_eq (K : Constants C E) (gadgets : RunGadgets C E G) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    runJobs K gadgets jobs inputs =
      (List.range (depth jobs)).foldlM (layerBody K gadgets jobs) (inputs, []) >>= tailBody K gadgets jobs := by
  rfl

variable (K : Constants C E) (mode : ReshareMode) (jobs : List Circuit) (i : C.Party)

/-- The rest of the program of operator `i` before the layers `ls`. -/
def progAt (ls : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C)) (st : RunState C) :
    PartyM C E (MainSpec C) (List (List Bit)) :=
  (ls.foldlM (layerBody K (hybridRunGadgets K mode i) jobs) p >>= tailBody K (hybridRunGadgets K mode i) jobs).run' st

theorem layerBody_apply (gadgets : RunGadgets C E G) (p : List (C.Term → List Bit) × List (Tuple C)) (l : ℕ) :
    layerBody K gadgets jobs p l = (do
      let z ← gadgets.mult (layerX K jobs l p.1) (layerY K jobs l p.1) (gatesAt jobs l).length
      pure (appendLayer jobs l p.1 z,
        p.2 ++ [⟨layerX K jobs l p.1, layerY K jobs l p.1, z, (gatesAt jobs l).length, gadgets.mode⟩])) := rfl

theorem hybrid_mult (x y : Shares C Bit) (n : ℕ) :
    (hybridRunGadgets (E := E) K mode i).mult x y n = (do
      let some (.inl (.inl z)) ← StateT.lift (call (.inl (.inl (x, y, n)))) | StateT.lift failure
      pure z) := rfl

theorem progAt_cons (l : ℕ) (ls : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C)) (st : RunState C) :
    progAt K mode jobs i (l :: ls) p st =
      call (Sum.inl (Sum.inl (layerX K jobs l p.1, layerY K jobs l p.1, (gatesAt jobs l).length))) >>= fun r =>
        match r with
        | some (.inl (.inl z)) => progAt K mode jobs i ls (appendLayer jobs l p.1 z,
            p.2 ++ [⟨layerX K jobs l p.1, layerY K jobs l p.1, z, (gatesAt jobs l).length, mode⟩]) st
        | _ => failure := by
  rw [progAt, List.foldlM_cons, bind_assoc, layerBody_apply, hybrid_mult]
  simp only [bind_assoc]
  rw [run'_lift_bind]
  congr 1
  funext r
  rcases r with _ | ((z | z) | u) <;> simp [progAt, StateT.run'_eq, StateT.run_bind]
  all_goals rfl

theorem tailBody_apply (gadgets : RunGadgets C E G) (p : List (C.Term → List Bit) × List (Tuple C)) :
    tailBody K gadgets jobs p = (do
      let v' ← gadgets.rerand (outputShares K jobs p.1) (outputsOf jobs).length
      gadgets.verify (p.2 ++ [⟨outputShares K jobs p.1, one K, v', (outputsOf jobs).length, .peer⟩])
      let opened ← gadgets.output v' (outputsOf jobs).length
      pure (assemble jobs opened)) := rfl

theorem hybrid_rerand (v : Shares C Bit) (n : ℕ) :
    (hybridRunGadgets (E := E) K mode i).rerand v n = (do
      let some (.inl (.inr z)) ← StateT.lift (call (.inl (.inr (v, one K, n)))) | StateT.lift failure
      pure z) := rfl

theorem hybrid_verify (tuples : List (Tuple C)) :
    (hybridRunGadgets (E := E) K mode i).verify tuples = (do
      let some (.inr ()) ← StateT.lift (call (.inr tuples)) | StateT.lift failure) := rfl

theorem hybrid_output (v : Shares C Bit) (n : ℕ) :
    (hybridRunGadgets (E := E) K mode i).output v n = StateT.lift (openRep K (localContext i) v n) := rfl

theorem progAt_nil (p : List (C.Term → List Bit) × List (Tuple C)) (st : RunState C) :
    progAt K mode jobs i [] p st =
      call (Sum.inl (Sum.inr (outputShares K jobs p.1, one K, (outputsOf jobs).length))) >>= fun r =>
        match r with
        | some (.inl (.inr v')) =>
          call (Sum.inr (p.2 ++ [⟨outputShares K jobs p.1, one K, v', (outputsOf jobs).length, .peer⟩])) >>= fun r' =>
            match r' with
            | some (.inr ()) => (fun opened => assemble jobs opened) <$> openRep K (localContext i) v' (outputsOf jobs).length
            | _ => failure
        | _ => failure := by
  rw [progAt, List.foldlM_nil, pure_bind, tailBody_apply, hybrid_rerand]
  simp only [bind_assoc]
  rw [run'_lift_bind]
  congr 1
  funext r
  rcases r with _ | ((z | z) | u)
  · simp [StateT.run'_eq, StateT.run_bind]
  · simp [StateT.run'_eq, StateT.run_bind]
  · simp only [pure_bind]
    rw [hybrid_verify]
    simp only [bind_assoc]
    rw [run'_lift_bind]
    congr 1
    funext r'
    rcases r' with _ | ((w | w) | u)
    · simp [StateT.run'_eq, StateT.run_bind]
    · simp [StateT.run'_eq, StateT.run_bind]
    · simp [StateT.run'_eq, StateT.run_bind]
    · simp only [pure_bind, hybrid_output]
      simp [StateT.run'_eq, StateT.run_bind, StateT.run_lift]
  · simp [StateT.run'_eq, StateT.run_bind]

section Honest
variable {I L R : Type} (reply : L → R)

@[simp] theorem honestAdversary_start (x : C.Party → Option I) (z : Aux) :
    (honestAdversary (C := C) (E := E) (I := I) reply).start x z = pure () := rfl

@[simp] theorem honestAdversary_answer (st : (honestAdversary (C := C) (E := E) (I := I) reply).State) (l : L) :
    (honestAdversary (C := C) (E := E) (I := I) reply).answer st l = pure (st, reply l) := rfl

end Honest

end Program

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

/-! ## The functionalities of the honest run -/

section Functionalities

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

def replyImpl' {L R : Type} (reply : L → R) : QueryImpl (LocalSpec C + (L →ₒ R)) (OracleComp (LocalSpec C)) :=
  (fun (t : (LocalSpec C).Domain) => OracleComp.lift (OracleSpec.query t)) + fun (l : L) => (pure (reply l) : OracleComp (LocalSpec C) R)

theorem firstInput_some_pos {I : Type} [Inhabited I] (f : C.Party → I) :
    firstInput (C := C) (fun i => some (f i)) = f ⟨0, by simp [Committee.n]; have := C.one_le_t; omega⟩ := by
  have hpos : 0 < C.n := by have := C.one_le_t; unfold Committee.n; omega
  simp only [firstInput, Committee.parties]
  rw [List.headD_eq_head?_getD]
  have : List.filterMap (fun i => some (f i)) (List.finRange C.n) = List.ofFn f := by
    rw [show (fun i => some (f i)) = some ∘ f from rfl, ← List.filterMap_map]
    simp [List.ofFn_eq_map]
  rw [this, List.head?_eq_getElem?, List.getElem?_ofFn]
  simp [hpos]

/-- `F_mult` in an honest run gives each operator its held terms of one sharing of the product. -/
theorem honest_mult_support (K : Constants C E) (mode : ReshareMode) (X Y : C.Party → Shares C Bit) (n : ℕ) o
    (ho : o ∈ support (simulateQ (replyImpl' mainReply) ((mainFunctionalities K mode).run noCoalition
      (fun i => some (Sum.inl (Sum.inl (X i, Y i, n))))))) :
    ∃ z : Shares C Bit, (∀ g, ∑ T, z T g = ∑ i, mulRep K (localContext i) (X i) (Y i) g) ∧
      o = fun i => some (.inl (.inl fun T g => if i ∈ C.holders T ∧ g < n then z T g else 0)) := by
  simp only [mainFunctionalities, Functionality.sum, FmultBit, Fmult, leak, sample, OracleComp.lift] at ho
  simp [noCoalition, simulateQ_bind, simulateQ_query, replyImpl', mainReply] at ho
  dsimp only [HAdd.hAdd, QueryImpl.add] at ho
  simp at ho
  simp only [QueryImpl.add] at ho
  simp [simulateQ_bind, simulateQ_query, QueryImpl.add, OracleComp.lift] at ho
  have hfi : (firstInput fun i => some (X i, Y i, n)).2.2 = n := by rw [firstInput_some_pos]
  set m := (firstInput fun i => some (X i, Y i, n)).2.2 with hm
  rw [← hfi]
  obtain ⟨fresh, -, rfl⟩ := ho
  obtain ⟨T₀, hT₀⟩ := Option.isSome_iff_exists.1 (lackedTerm_empty_isSome (C := C))
  let base : Shares C Bit := fun T g => if h : g < m then fresh T ⟨g, h⟩ else 0
  refine ⟨fun T g => if lackedTerm ∅ = some T then
      (∑ x, mulRep K (localContext x) (X x) (Y x) g) - ∑ T' ∈ Finset.univ.erase T, base T' g
      else base T g, fun g => ?_, ?_⟩
  · have := sum_lacked (C := C) T₀ base (fun g => ∑ x, mulRep K (localContext x) (X x) (Y x) g) g
    simp only [hT₀, Option.some.injEq]
    exact this
  · funext i
    simp only [KnownTo, Finset.notMem_empty, false_and, exists_false, if_false]
    congr 3
    funext T g
    have h0 : ∀ a : Bit, Add.add a 0 = a := fun a => add_zero a
    split_ifs <;> simp_all [base, m, Finset.sum_erase_eq_sub, h0]

end Functionalities

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open ThresholdLeanXmss

section FunctionalitiesHonest

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- `reconstruct` returns a value on which every holder agrees. -/
theorem reconstruct_of_agree {α : Type} [Inhabited α] (views : C.Party → Option (C.Term → α)) (T : C.Term) (V : α)
    (h : ∀ i, i ∈ C.holders T → ∃ f, views i = some f ∧ f T = V) : reconstruct views T = V := by
  obtain ⟨i₀, hi₀⟩ := exists_holder T
  unfold reconstruct
  rcases hl : (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) with _ | ⟨f, rest⟩
  · exfalso
    obtain ⟨f, hf, -⟩ := h i₀ hi₀
    have : f ∈ (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) :=
      List.mem_filterMap.2 ⟨i₀, List.mem_finRange i₀, by simp [hi₀, hf]⟩
    rw [hl] at this
    simp at this
  · have hmem : f ∈ (C.parties.filterMap fun i => if i ∈ C.holders T then views i else none) := by
      rw [hl]; exact List.mem_cons_self
    obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hmem
    split_ifs at hi with hiT
    obtain ⟨f', hf', hV⟩ := h i hiT
    rw [hf'] at hi
    cases hi
    simp [hV]

set_option linter.constructorNameAsVariable false in
/-- Tuple `τ` agrees with `τ'` on the terms that operator `i` holds. -/
def TupleAgrees (i : C.Party) (τ τ' : Tuple C) : Prop :=
  (∀ T, i ∈ C.holders T → τ.x T = τ'.x T ∧ τ.y T = τ'.y T ∧ τ.z T = τ'.z T) ∧ τ.count = τ'.count ∧ τ.mode = τ'.mode

/-- A tuple whose shared values multiply. -/
def IsProduct (τ : Tuple C) : Prop := ∀ g < τ.count, shareValue τ.z g = shareValue τ.x g * shareValue τ.y g

theorem tupleAt_of_agree (views : C.Party → List (Tuple C)) (Ts : List (Tuple C))
    (hlen : ∀ i, (views i).length = Ts.length)
    (hag : ∀ i m (hm : m < Ts.length), TupleAgrees i ((views i)[m]'(by rw [hlen]; exact hm)) Ts[m])
    (k : ℕ) (hk : k < Ts.length) : tupleAt (fun i => some (views i)) k = Ts[k] := by
  have hat : ∀ i, (some (views i)).bind (·[k]?) = some ((views i)[k]'(by rw [hlen]; exact hk)) := by
    intro i
    simp [List.getElem?_eq_getElem (by rw [hlen]; exact hk : k < (views i).length)]
  have hfirst := firstInput_some_pos (C := C) views
  rcases hTs : Ts[k] with ⟨x, y, z, count, mode⟩
  have hx : ∀ i T, i ∈ C.holders T → ((views i)[k]'(by rw [hlen]; exact hk)).x T = x T := fun i T h => by
    have := ((hag i k hk).1 T h).1; rw [hTs] at this; exact this
  have hy : ∀ i T, i ∈ C.holders T → ((views i)[k]'(by rw [hlen]; exact hk)).y T = y T := fun i T h => by
    have := ((hag i k hk).1 T h).2.1; rw [hTs] at this; exact this
  have hz : ∀ i T, i ∈ C.holders T → ((views i)[k]'(by rw [hlen]; exact hk)).z T = z T := fun i T h => by
    have := ((hag i k hk).1 T h).2.2; rw [hTs] at this; exact this
  have hc : ∀ i, ((views i)[k]'(by rw [hlen]; exact hk)).count = count := fun i => by
    have := (hag i k hk).2.1; rw [hTs] at this; exact this
  have hmo : ∀ i, ((views i)[k]'(by rw [hlen]; exact hk)).mode = mode := fun i => by
    have := (hag i k hk).2.2; rw [hTs] at this; exact this
  unfold tupleAt
  simp only [hat, Option.map_some, hfirst]
  congr 1
  · funext T; exact reconstruct_of_agree _ T _ fun i h => ⟨_, rfl, hx i T h⟩
  · funext T; exact reconstruct_of_agree _ T _ fun i h => ⟨_, rfl, hy i T h⟩
  · funext T; exact reconstruct_of_agree _ T _ fun i h => ⟨_, rfl, hz i T h⟩
  · rw [List.getElem?_eq_getElem (by rw [hlen]; exact hk)]; simp [hc]
  · rw [List.getElem?_eq_getElem (by rw [hlen]; exact hk)]; simp [hmo]

end FunctionalitiesHonest

section Lists

variable {β : Type}

/-- The entries of some lists, each with the index of its list from `s`. -/
def flatIdx (L : List (List β)) (s : ℕ) : List (ℕ × β) := (L.zipIdx s).flatMap fun p => p.1.map fun b => (p.2, b)

theorem flatIdx_cons (xs : List β) (L : List (List β)) (s : ℕ) :
    flatIdx (xs :: L) s = xs.map (fun b => (s, b)) ++ flatIdx L (s + 1) := by
  simp [flatIdx]

theorem length_flatIdx (L : List (List β)) (s : ℕ) : (flatIdx L s).length = (L.map List.length).sum := by
  induction L generalizing s with
  | nil => simp [flatIdx]
  | cons xs L ih => simp [flatIdx_cons, ih]

theorem getElem?_flatIdx (L : List (List β)) (s k j : ℕ) (hk : k < L.length) (hj : j < (L[k]).length) :
    (flatIdx L s)[((L.take k).map List.length).sum + j]? = some (s + k, L[k][j]) := by
  induction L generalizing s k with
  | nil => simp at hk
  | cons xs L ih =>
    rw [flatIdx_cons]
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at hj
      rw [List.getElem?_append_left (by simpa using hj)]
      simp [hj]
    | succ k =>
      have hk' : k < L.length := by simpa using hk
      rw [List.getElem?_append_right (by simp; omega)]
      have := ih (s + 1) k hk' (by simpa using hj)
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.length_map] at this ⊢
      rw [show xs.length + (List.map List.length (List.take k L)).sum + j - xs.length =
        (List.map List.length (List.take k L)).sum + j by omega, this]
      simp [Nat.add_assoc, Nat.add_comm 1 k]
      rfl

theorem filter_zipIdx_flatIdx (L : List (List β)) (s t k : ℕ) :
    ((flatIdx L s).zipIdx t).filter (fun p => decide (p.1.1 = k)) =
      if s ≤ k then ((L.getD (k - s) []).zipIdx).map
        (fun p => ((k, p.1), t + ((L.take (k - s)).map List.length).sum + p.2)) else [] := by
  induction L generalizing s t with
  | nil => simp [flatIdx]
  | cons xs L ih =>
    rw [flatIdx_cons, List.zipIdx_append, List.filter_append, ih, List.zipIdx_map]
    by_cases hsk : s = k
    · subst hsk
      have h1 : List.filter (fun p => decide (p.1.1 = s)) (List.map (Prod.map (fun b => (s, b)) id) (xs.zipIdx t)) =
          List.map (Prod.map (fun b => (s, b)) id) (xs.zipIdx t) := List.filter_eq_self.2 (by simp; intros; simp_all)
      rw [h1, if_neg (by omega), if_pos le_rfl, List.zipIdx_eq_map_add]
      simp [Function.comp_def]
    · have h1 : List.filter (fun p => decide (p.1.1 = k)) (List.map (Prod.map (fun b => (s, b)) id) (xs.zipIdx t)) =
          [] := List.filter_eq_nil_iff.2 (by simp; omega)
      rw [h1, List.nil_append]
      by_cases hle : s ≤ k
      · rw [if_pos (by omega), if_pos hle]
        obtain ⟨d, hd⟩ : ∃ d, k - s = d + 1 := ⟨k - s - 1, by omega⟩
        rw [hd, show k - (s + 1) = d by omega]
        simp [Nat.add_assoc]
      · rw [if_neg (by omega), if_neg hle]

theorem filterMap_zip_idxOf {α : Type} [BEq α] [LawfulBEq α] (L : List α) (hL : L.Nodup) (P : α → Prop) [DecidablePred P]
    (ds : List β) (hds : ds.length = L.length) (T : α) (hT : T ∈ L) (hP : P T) :
    ((L.zip ds).filterMap fun p => if P p.1 then some p.2 else none)[(L.filter P).idxOf T]? = ds[L.idxOf T]? := by
  induction L generalizing ds with
  | nil => simp at hT
  | cons a L ih =>
    obtain _ | ⟨d, ds⟩ := ds
    · simp at hds
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hds
    rw [List.zip_cons_cons, List.filterMap_cons]
    rcases Classical.em (a = T) with ha | ha
    · subst ha
      simp [hP]
    · have hT' : T ∈ L := (List.mem_cons.1 hT).resolve_left (Ne.symm ha)
      have := ih (List.nodup_cons.1 hL).2 ds hds hT'
      rw [List.idxOf_cons_ne _ ha]
      by_cases hPa : P a
      · rw [List.filter_cons_of_pos (by simpa using hPa), List.idxOf_cons_ne _ ha]
        simpa [hPa] using this
      · rw [List.filter_cons_of_neg (by simpa using hPa)]
        simpa [hPa] using this

theorem lookup_zip_idxOf {α : Type} [BEq α] [LawfulBEq α] (L : List α) (ds : List β) (hds : ds.length = L.length)
    (T : α) (hT : T ∈ L) : (L.zip ds).lookup T = ds[L.idxOf T]? := by
  induction L generalizing ds with
  | nil => simp at hT
  | cons a L ih =>
    obtain _ | ⟨d, ds⟩ := ds
    · simp at hds
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hds
    rw [List.zip_cons_cons, List.lookup_cons]
    rcases Classical.em (a = T) with ha | ha
    · subst ha
      simp
    · have hT' : T ∈ L := (List.mem_cons.1 hT).resolve_left (Ne.symm ha)
      rw [List.idxOf_cons_ne _ ha]
      have : (T == a) = false := by simpa using Ne.symm ha
      simp [this, ih ds hds hT']

theorem getD_append_of_lt (l l' : List β) (d : β) (n : ℕ) (h : n < l.length) : (l ++ l').getD n d = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_of_le (l l' : List β) (d : β) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

end Lists

section Hashes

variable {C : Committee} (prims : Primitives)

/-- After the queries of `H` at `q T` for the terms of `L`, the cache holds every answer. -/
theorem support_hashes (L : List C.Term) (q : C.Term → Query C) (hq : ∀ T, ¬ IsFixed (q T)) (s : HashCache C) z
    (hz : z ∈ support ((simulateQ (localAnswer prims)
      (liftComp (L.mapM fun T => hashQuery (q T)) (LocalSpec C))).run s)) :
    ∃ h : z.1.length = L.length, s ≤ z.2 ∧ ∀ m (hm : m < L.length), z.2 (q L[m]) = some (z.1[m]'(h ▸ hm)) := by
  induction L generalizing s z with
  | nil =>
    simp at hz
    subst hz
    exact ⟨rfl, le_rfl, fun m hm => absurd hm (by simp)⟩
  | cons T L ih =>
    rw [List.mapM_cons, liftComp_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨a, s₁⟩, h₁, hz⟩ := hz
    rw [simulateQ_localAnswer_hash] at h₁
    have hc₁ := hashAnswer_cached prims (hq T) s _ h₁
    have hg₁ := grows_hashAnswer prims (q T) s _ h₁
    rw [liftComp_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨as, s₂⟩, h₂, hz⟩ := hz
    obtain ⟨hlen, hg₂, hc₂⟩ := ih s₁ _ h₂
    simp only [liftComp_pure, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨by simp [hlen], hg₁.trans hg₂, fun m hm => ?_⟩
    cases m with
    | zero => exact hg₂ hc₁
    | succ m => exact hc₂ m (by simpa using hm)

/-- The queries of `H` at cached inputs return the cached answers and keep the cache. -/
theorem support_hashes_cached (L : List C.Term) (q : C.Term → Query C) (hq : ∀ T, ¬ IsFixed (q T)) (s : HashCache C)
    (val : C.Term → HashOutput) (hs : ∀ T ∈ L, s (q T) = some (val T)) z
    (hz : z ∈ support ((simulateQ (localAnswer prims)
      (liftComp (L.mapM fun T => hashQuery (q T)) (LocalSpec C))).run s)) :
    z = (L.map val, s) := by
  induction L generalizing z with
  | nil =>
    simp at hz
    exact hz
  | cons T L ih =>
    rw [List.mapM_cons, liftComp_bind, simulateQ_bind, StateT.run_bind, simulateQ_localAnswer_hash,
      hashAnswer_run_cached prims (hq T) (hs T List.mem_cons_self), pure_bind] at hz
    rw [liftComp_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨as, s₂⟩, h₂, hz⟩ := hz
    have := ih (fun T' h => hs T' (List.mem_cons_of_mem _ h)) _ h₂
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    simp only [liftComp_pure, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    simp [hz]

end Hashes

/-! ## Sequences with a state -/

section StateSeq

variable {σ α : Type}

/-- The steps of a sequence that keep a monotone property give it to the whole sequence. -/
theorem support_sequenceFin_state [Preorder σ] (s₀ : σ) :
    ∀ {n : ℕ} (f : Fin n → StateT σ ProbComp α) (P : Fin n → α → σ → Prop)
      (hf : ∀ i s, s₀ ≤ s → ∀ z ∈ support ((f i).run s), s ≤ z.2 ∧ P i z.1 z.2)
      (hP : ∀ i a s s', P i a s → s ≤ s' → P i a s') (s : σ), s₀ ≤ s →
      ∀ z ∈ support ((Concrete.sequenceFin f).run s), s ≤ z.2 ∧ ∀ i, P i (z.1 i) z.2
  | 0, f, P, hf, hP, s, _ => by
    intro z hz
    simp [Concrete.sequenceFin] at hz
    subst hz
    exact ⟨le_rfl, fun i => i.elim0⟩
  | n + 1, f, P, hf, hP, s, hs => by
    intro z hz
    simp only [Concrete.sequenceFin, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨a, s₁⟩, h₁, hz⟩ := hz
    obtain ⟨⟨as, s₂⟩, h₂, hz⟩ := hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    obtain ⟨hs₁, hP₁⟩ := hf 0 s hs _ h₁
    obtain ⟨hs₂, hP₂⟩ := support_sequenceFin_state s₀ (fun i : Fin n => f i.succ) (fun i => P i.succ)
      (fun i => hf i.succ) (fun i => hP i.succ) s₁ (hs.trans hs₁) _ h₂
    refine ⟨hs₁.trans hs₂, fun i => ?_⟩
    cases i using Fin.cases with
    | zero => exact hP 0 a s₁ s₂ hP₁ hs₂
    | succ i => exact hP₂ i

end StateSeq

/-! ## The steps of an honest batch -/

section Steps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]
variable (K : Constants C E) (mode : ReshareMode) (jobs : List Circuit) (i : C.Party)

/-- The call that operator `i` makes before the layers `ls`. -/
def callStep (ls : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C)) :
    Step C E (MainSpec C) (List (List Bit)) :=
  match ls with
  | l :: ls => .call (Sum.inl (Sum.inl (layerX K jobs l p.1, layerY K jobs l p.1, (gatesAt jobs l).length)))
      fun (r : Option ((Shares C Bit ⊕ Shares C Bit) ⊕ Unit)) =>
      (match r with
        | some (.inl (.inl z)) => progAt K mode jobs i ls (appendLayer jobs l p.1 z,
            p.2 ++ [(⟨layerX K jobs l p.1, layerY K jobs l p.1, z, (gatesAt jobs l).length, mode⟩ : Tuple C)]) startRun
        | _ => failure).run
  | [] => .call (Sum.inl (Sum.inr (outputShares K jobs p.1, one K, (outputsOf jobs).length)))
      fun (r : Option ((Shares C Bit ⊕ Shares C Bit) ⊕ Unit)) =>
      (match r with
        | some (.inl (.inr v')) =>
          call (G := MainSpec C) (Sum.inr (p.2 ++ [(⟨outputShares K jobs p.1, one K, v', (outputsOf jobs).length, .peer⟩ : Tuple C)])) >>=
            fun (r' : Option ((Shares C Bit ⊕ Shares C Bit) ⊕ Unit)) =>
            match r' with
            | some (.inr ()) => (fun opened => assemble jobs opened) <$> openRep K (localContext i) v' (outputsOf jobs).length
            | _ => failure
        | _ => failure).run

theorem advance_progAt (ls : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C)) :
    advance (progAt K mode jobs i ls p startRun).run = pure (callStep K mode jobs i ls p) := by
  cases ls with
  | cons l ls =>
    rw [progAt_cons, advance_call_bind]
    simp only [callStep]
    congr 2
    funext r
    rcases r with _ | ((z | z) | u) <;> rfl
  | nil =>
    rw [progAt_nil, advance_call_bind]
    simp only [callStep]
    congr 2
    funext r
    rcases r with _ | ((z | z) | u)
    · rfl
    · rfl
    · dsimp only
      refine bind_congr fun r' => ?_
      rcases r' with _ | ((w | w) | u) <;> rfl
    · rfl

theorem mainProtocol_eq (inputs : List (C.Term → List Bit)) :
    mainProtocol K mode jobs i inputs = progAt K mode jobs i (List.range (depth jobs)) (inputs, []) startRun := by
  rw [progAt, mainProtocol, runJobs_eq]

end Steps

/-! ## The steps of `OpenRep` -/

section OpenRep

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) {ι : Type} {G : OracleSpec ι}
  (i : C.Party) (v : Shares C Bit) (count : ℕ)

/-- The message of operator `i` in `OpenRep`. -/
def repOutbox (digests : List HashOutput) : Mail C E := fun j => if j = i then none else some (.bundle [
    .bits ((C.terms.filter fun T => j ∉ C.holders T ∧ K.owner T = i).flatMap fun T => vector count (v T)),
    .hashes ((C.terms.zip digests).filterMap fun (T, d) =>
      if j ∉ C.holders T ∧ i ∈ C.holders T ∧ K.owner T ≠ i then some d else none)])

/-- The copy of each term at operator `i` after `OpenRep`. -/
def repCopy (inbox : Mail C E) : Shares C Bit := fun T g =>
  if i ∈ C.holders T then v T g else
    let owned := C.terms.filter fun T' => i ∉ C.holders T' ∧ K.owner T' = K.owner T
    Msg.bitAt (Msg.part (inbox (K.owner T)) 0) (count * owned.idxOf T + g)

/-- The hash check of `OpenRep` at operator `i`. -/
def repCheck (inbox : Mail C E) (copyDigests : List HashOutput) : Prop :=
  ∀ T : C.Term, i ∉ C.holders T → ∀ h ∈ C.holders T, h ≠ K.owner T →
    let sent := C.terms.filter fun T' => i ∉ C.holders T' ∧ h ∈ C.holders T' ∧ K.owner T' ≠ h
    (Msg.hashesOf (Msg.part (inbox h) 1))[sent.idxOf T]? = (C.terms.zip copyDigests).lookup T

open Classical in
theorem openRep_eq : openRep (G := G) K (localContext i) v count = (do
    let digests ← oracleStep (C.terms.mapM fun T => hashQuery (.copy (vector count (v T))))
    let inbox ← exchange (repOutbox (E := E) K i v count digests)
    let copyDigests ← oracleStep (C.terms.mapM fun T => hashQuery (.copy (vector count (repCopy K i v count inbox T))))
    require (repCheck K i inbox copyDigests)
    pure fun g => ∑ T, repCopy K i v count inbox T g) := rfl

open Classical in
/-- The steps of `OpenRep` after the round. -/
def repRest (inbox : Mail C E) : PartyM C E G (ℕ → Bit) := do
  let copyDigests ← oracleStep (C.terms.mapM fun T => hashQuery (.copy (vector count (repCopy K i v count inbox T))))
  require (repCheck K i inbox copyDigests)
  pure fun g => ∑ T, repCopy K i v count inbox T g

theorem advance_openRep {β : Type} (f : (ℕ → Bit) → β) :
    advance (f <$> openRep (G := G) K (localContext i) v count).run =
      liftComp (C.terms.mapM fun T => hashQuery (C := C) (.copy (vector count (v T)))) (LocalSpec C) >>= fun digests =>
        pure (.wait (repOutbox K i v count digests) (exchangeResume fun inbox =>
          f <$> repRest (G := G) K i v count inbox)) := by
  rw [openRep_eq, map_bind, advance_oracleStep_bind]
  refine bind_congr fun digests => ?_
  rw [map_bind, advance_exchange_bind]
  rfl

open Classical in
theorem advance_openRest {β : Type} (f : (ℕ → Bit) → β) (inbox : Mail C E) :
    advance (f <$> repRest (G := G) K i v count inbox).run =
      liftComp (C.terms.mapM fun T => hashQuery (C := C) (.copy (vector count (repCopy K i v count inbox T)))) (LocalSpec C) >>=
        fun copyDigests => if repCheck K i inbox copyDigests then
          pure (.done (some (f fun g => ∑ T, repCopy K i v count inbox T g))) else pure (.done none) := by
  rw [repRest, map_bind, advance_oracleStep_bind]
  refine bind_congr fun copyDigests => ?_
  rw [map_bind, advance_require_bind]
  split_ifs
  · rfl
  · rfl

theorem mem_terms (T : C.Term) : T ∈ C.terms := Finset.mem_toList.2 (Finset.mem_univ T)

/-- In an honest `OpenRep`, each copy is the shared value. -/
theorem openCopy_eq (w : Shares C Bit) (vr : C.Party → Shares C Bit)
    (hvr : ∀ i T g, i ∈ C.holders T → g < count → vr i T g = w T g) (ds : C.Party → List HashOutput)
    (T : C.Term) (g : ℕ) (hg : g < count) :
    repCopy K i (vr i) count (fun k => repOutbox (E := E) K k (vr k) count (ds k) i) T g = w T g := by
  unfold repCopy
  split_ifs with hi
  · exact hvr i T g hi hg
  · have hne : i ≠ K.owner T := fun h => hi (h ▸ K.owner_held T)
    simp only [repOutbox, if_neg hne, Msg.part, List.getElem?_cons_zero, Msg.bitAt]
    rw [getD_flatMap_vector _ _ _ T (List.mem_filter.2 ⟨mem_terms T, by simp [hi]⟩)
      (terms_nodup.filter _) g hg]
    exact hvr _ T g (K.owner_held T) hg

/-- In an honest `OpenRep`, the hash check passes. -/
theorem repCheck_honest (vr : C.Party → Shares C Bit) (ds : C.Party → List HashOutput) (val : C.Term → HashOutput)
    (hlen : ∀ h, (ds h).length = C.terms.length)
    (hds : ∀ h T, h ∈ C.holders T → (ds h)[C.terms.idxOf T]? = some (val T)) :
    repCheck K i (fun k => repOutbox (E := E) K k (vr k) count (ds k) i) (C.terms.map val) := by
  intro T hiT h hh hown
  have hne : i ≠ h := fun e => hiT (e ▸ hh)
  simp only [repOutbox, if_neg hne, Msg.part, List.getElem?_cons_succ, List.getElem?_cons_zero, Msg.hashesOf]
  have h1 := filterMap_zip_idxOf C.terms terms_nodup
    (fun T' => i ∉ C.holders T' ∧ h ∈ C.holders T' ∧ K.owner T' ≠ h) (ds h) (hlen h) T (mem_terms T) ⟨hiT, hh, Ne.symm hown⟩
  rw [lookup_zip_idxOf C.terms (C.terms.map val) (by simp) T (mem_terms T)]
  rw [List.getElem?_map,
    List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem (mem_terms T))]
  simp only [Option.map_some, List.getElem_idxOf]
  rw [← hds h T hh, ← h1]

end OpenRep

/-! ## The values of the layers -/

section Values

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (jobs : List Circuit)

/-- One layer of a circuit on its plain wires. -/
def plainLayer (job : Circuit) (w : List Bit) (layer : ℕ) : List Bit :=
  w ++ (job.layers.getD layer []).map fun ab => ab.1.eval w * ab.2.eval w

/-- The plain wires of a circuit after `l` layers. -/
def plainAt (job : Circuit) (input : List Bit) (l : ℕ) : List Bit := (List.range l).foldl (plainLayer job) input

/-- The plain input wires of job `k`. -/
def plainInput (x : C.Party → List (C.Term → List Bit)) (k : ℕ) : List Bit := inputValue (reconstruct fun i => (x i)[k]?)

theorem plainAt_succ (job : Circuit) (input : List Bit) (l : ℕ) :
    plainAt job input (l + 1) = plainLayer job (plainAt job input l) l := by
  simp [plainAt, List.range_succ, List.foldl_append]

theorem gatesAt_eq (l : ℕ) : gatesAt jobs l = flatIdx (jobs.map fun job => job.layers.getD l []) 0 := by
  simp only [gatesAt, flatIdx, List.zipIdx_map, List.flatMap_map]
  rfl

theorem outputsOf_eq : outputsOf jobs = flatIdx (jobs.map (·.outputs)) 0 := by
  simp only [outputsOf, flatIdx, List.zipIdx_map, List.flatMap_map]
  rfl

/-- The wires that layer `l` appends to job `k`. -/
def newWires (l k : ℕ) (z : Shares C Bit) (T : C.Term) : List Bit :=
  ((gatesAt jobs l).zipIdx.filter (·.1.1 = k)).map fun (_, g) => z T g

/-- The first gate of job `k` in layer `l`. -/
def gateOffset (l k : ℕ) : ℕ := (((jobs.map fun job => job.layers.getD l []).take k).map List.length).sum

theorem newWires_eq (l k : ℕ) (hk : k < jobs.length) (z : Shares C Bit) (T : C.Term) :
    newWires jobs l k z T = (List.range (jobs[k].layers.getD l []).length).map fun j => z T (gateOffset jobs l k + j) := by
  unfold newWires
  rw [gatesAt_eq, filter_zipIdx_flatIdx, if_pos (Nat.zero_le k)]
  simp only [Nat.sub_zero, List.map_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
  simp only [Option.map_some, Option.getD_some]
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp [gateOffset]

theorem getD_appendLayer (l : ℕ) (wires : List (C.Term → List Bit)) (z : Shares C Bit) (k : ℕ) :
    (appendLayer jobs l wires z).getD k (fun _ => []) =
      if k < wires.length then fun T => (wires.getD k fun _ => []) T ++ newWires jobs l k z T else fun _ => [] := by
  unfold appendLayer newWires
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx]
  split_ifs with hk
  · rw [List.getElem?_eq_getElem hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    simp
  · rw [List.getElem?_eq_none (by omega)]
    rfl

theorem length_appendLayer (l : ℕ) (wires : List (C.Term → List Bit)) (z : Shares C Bit) :
    (appendLayer jobs l wires z).length = wires.length := by
  simp [appendLayer]

/-- `layerX` reads only the held wires. -/
theorem layerX_congr (l : ℕ) (w w' : List (C.Term → List Bit)) (T : C.Term)
    (h : ∀ k, (w.getD k fun _ => []) T = (w'.getD k fun _ => []) T) :
    layerX K jobs l w T = layerX K jobs l w' T := by
  funext g
  unfold layerX
  split
  · simp only [Affine.share, h]
  · rfl

theorem layerY_congr (l : ℕ) (w w' : List (C.Term → List Bit)) (T : C.Term)
    (h : ∀ k, (w.getD k fun _ => []) T = (w'.getD k fun _ => []) T) :
    layerY K jobs l w T = layerY K jobs l w' T := by
  funext g
  unfold layerY
  split
  · simp only [Affine.share, h]
  · rfl

theorem outputShares_congr (w w' : List (C.Term → List Bit)) (T : C.Term)
    (h : ∀ k, (w.getD k fun _ => []) T = (w'.getD k fun _ => []) T) :
    outputShares K jobs w T = outputShares K jobs w' T := by
  funext g
  unfold outputShares
  split
  · simp only [Affine.share, h]
  · rfl

theorem gatesAt_offset (l k j : ℕ) (hk : k < jobs.length) (hj : j < (jobs[k].layers.getD l []).length) :
    (gatesAt jobs l)[gateOffset jobs l k + j]? = some (k, (jobs[k].layers.getD l [])[j]) := by
  rw [gatesAt_eq, gateOffset]
  have := getElem?_flatIdx (jobs.map fun job => job.layers.getD l []) 0 k j (by simpa using hk) (by simpa using hj)
  simpa using this

theorem gateOffset_lt (l k j : ℕ) (hk : k < jobs.length) (hj : j < (jobs[k].layers.getD l []).length) :
    gateOffset jobs l k + j < (gatesAt jobs l).length := by
  have h := gatesAt_offset jobs l k j hk hj
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

variable (x : C.Party → List (C.Term → List Bit))

/-- The state of the operators after `l` layers. Each operator agrees with the common wires `W` and
the common tuples `Ts` on its held terms, `W` shares the plain wires, and each tuple of `Ts` is a product. -/
structure LayerInv (l : ℕ) (p : C.Party → List (C.Term → List Bit) × List (Tuple C)) (W : List (C.Term → List Bit))
    (Ts : List (Tuple C)) : Prop where
  length_wires : ∀ i, (p i).1.length = jobs.length
  length_W : W.length = jobs.length
  agree : ∀ i T, i ∈ C.holders T → ∀ k, ((p i).1.getD k fun _ => []) T = (W.getD k fun _ => []) T
  length_plain : ∀ k (hk : k < jobs.length) T,
    ((W.getD k fun _ => []) T).length = (plainAt jobs[k] (plainInput x k) l).length
  sum_plain : ∀ k (hk : k < jobs.length) g,
    (plainAt jobs[k] (plainInput x k) l).getD g 0 = ∑ T, ((W.getD k fun _ => []) T).getD g 0
  length_tuples : ∀ i, (p i).2.length = Ts.length
  agree_tuples : ∀ i m (hm : m < Ts.length), TupleAgrees i ((p i).2[m]'(by rw [length_tuples]; exact hm)) Ts[m]
  product : ∀ τ ∈ Ts, IsProduct τ

theorem tupleAgrees_append (i : C.Party) (vs Ts : List (Tuple C)) (v τ : Tuple C) (hlen : vs.length = Ts.length)
    (hag : ∀ m (hm : m < Ts.length), TupleAgrees i (vs[m]'(by rw [hlen]; exact hm)) Ts[m]) (hv : TupleAgrees i v τ) :
    ∀ m (hm : m < (Ts ++ [τ]).length), TupleAgrees i ((vs ++ [v])[m]'(by simp [hlen] at hm ⊢; exact hm)) (Ts ++ [τ])[m] := by
  intro m hm
  simp only [List.length_append, List.length_singleton] at hm
  rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
  · rw [List.getElem_append_left (by omega), List.getElem_append_left hm]
    exact hag m hm
  · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    simpa [hlen] using hv

/-- One layer keeps the invariant, with the output of `F_mult` from `honest_mult_support`. -/
theorem layerInv_step (mode : ReshareMode) (l : ℕ) (p : C.Party → List (C.Term → List Bit) × List (Tuple C))
    (W : List (C.Term → List Bit)) (Ts : List (Tuple C)) (hinv : LayerInv jobs x l p W Ts) (z : Shares C Bit)
    (hz : ∀ g, ∑ T, z T g = ∑ i, mulRep K (localContext i) (layerX K jobs l (p i).1) (layerY K jobs l (p i).1) g) :
    LayerInv jobs x (l + 1)
      (fun i => (appendLayer jobs l (p i).1 fun T g => if i ∈ C.holders T ∧ g < (gatesAt jobs l).length then z T g else 0,
        (p i).2 ++ [⟨layerX K jobs l (p i).1, layerY K jobs l (p i).1,
          fun T g => if i ∈ C.holders T ∧ g < (gatesAt jobs l).length then z T g else 0, (gatesAt jobs l).length, mode⟩]))
      (appendLayer jobs l W fun T g => if g < (gatesAt jobs l).length then z T g else 0)
      (Ts ++ [⟨layerX K jobs l W, layerY K jobs l W, fun T g => if g < (gatesAt jobs l).length then z T g else 0,
        (gatesAt jobs l).length, mode⟩]) := by
  set n := (gatesAt jobs l).length with hn
  have hX : ∀ i T, i ∈ C.holders T → layerX K jobs l (p i).1 T = layerX K jobs l W T :=
    fun i T h => layerX_congr K jobs l _ _ T (hinv.agree i T h)
  have hY : ∀ i T, i ∈ C.holders T → layerY K jobs l (p i).1 T = layerY K jobs l W T :=
    fun i T h => layerY_congr K jobs l _ _ T (hinv.agree i T h)
  have hprod : ∀ g, ∑ T, z T g = shareValue (layerX K jobs l W) g * shareValue (layerY K jobs l W) g := fun g => by
    rw [hz g]
    exact mulRep_views_sum K _ _ _ _ g (fun i T h => by rw [hX i T h]) (fun i T h => by rw [hY i T h])
  have hplain : ∀ k (hk : k < jobs.length), ∀ g, (plainAt jobs[k] (plainInput x k) l).getD g 0 =
      ∑ T, ((W.getD k fun _ => []) T).getD g 0 := hinv.sum_plain
  refine ⟨fun i => ?_, ?_, fun i T hi k => ?_, fun k hk T => ?_, fun k hk g => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · simp [length_appendLayer, hinv.length_wires]
  · simp [length_appendLayer, hinv.length_W]
  · rw [getD_appendLayer, getD_appendLayer, hinv.length_wires, hinv.length_W]
    split_ifs with hk
    · simp only [hinv.agree i T hi k, newWires, hi, true_and]
    · rfl
  · rw [getD_appendLayer, hinv.length_W, if_pos hk, plainAt_succ, plainLayer]
    have := hinv.length_plain k hk T
    rw [List.getD_eq_getElem?_getD] at this
    simp [this, newWires_eq jobs l k hk]
  · rw [getD_appendLayer, hinv.length_W, if_pos hk, plainAt_succ, plainLayer]
    simp only [newWires_eq jobs l k hk]
    set w := plainAt jobs[k] (plainInput x k) l with hw
    by_cases hg : g < w.length
    · rw [getD_append_of_lt _ _ _ _ hg, hplain k hk g]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [getD_append_of_lt _ _ _ _ (by rw [hinv.length_plain k hk T]; exact hg)]
    · push_neg at hg
      obtain ⟨j, rfl⟩ : ∃ j, g = w.length + j := ⟨g - w.length, by omega⟩
      rw [getD_append_of_le _ _ _ _ (by omega)]
      have hT : ∀ T, ((W.getD k fun _ => []) T ++ (List.range (jobs[k].layers.getD l []).length).map
          fun j => (if gateOffset jobs l k + j < n then z T (gateOffset jobs l k + j) else 0)).getD (w.length + j) 0 =
          ((List.range (jobs[k].layers.getD l []).length).map
            fun j => (if gateOffset jobs l k + j < n then z T (gateOffset jobs l k + j) else 0)).getD j 0 := fun T => by
        rw [getD_append_of_le _ _ _ _ (by rw [hinv.length_plain k hk T]; omega), hinv.length_plain k hk T, ← hw,
          Nat.add_sub_cancel_left]
      simp only [hT, Nat.add_sub_cancel_left]
      by_cases hj : j < (jobs[k].layers.getD l []).length
      · have e1 : ((jobs[k].layers.getD l []).map fun ab => ab.1.eval w * ab.2.eval w).getD j 0 =
            ((jobs[k].layers.getD l [])[j]).1.eval w * ((jobs[k].layers.getD l [])[j]).2.eval w := by
          generalize jobs[k].layers.getD l [] = L at hj ⊢
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        have e2 : ∀ T, ((List.range (jobs[k].layers.getD l []).length).map
            fun j => (if gateOffset jobs l k + j < n then z T (gateOffset jobs l k + j) else 0)).getD j 0 =
            z T (gateOffset jobs l k + j) := fun T => by
          have hlt := gateOffset_lt jobs l k j hk hj
          generalize jobs[k].layers.getD l [] = L at hj ⊢
          simp [List.getD_eq_getElem?_getD, List.getElem?_range hj, hn ▸ hlt]
        rw [e1]
        simp only [e2]
        rw [hprod, shareValue, shareValue]
        simp only [layerX, layerY, gatesAt_offset jobs l k j hk hj]
        rw [sum_affine_share _ _ _ _ (hplain k hk), sum_affine_share _ _ _ _ (hplain k hk)]
      · have e1 : ((jobs[k].layers.getD l []).map fun ab => ab.1.eval w * ab.2.eval w).getD j 0 = 0 := by
          generalize jobs[k].layers.getD l [] = L at hj ⊢
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hj)]
        have e2 : ∀ T, ((List.range (jobs[k].layers.getD l []).length).map
            fun j => (if gateOffset jobs l k + j < n then z T (gateOffset jobs l k + j) else 0)).getD j 0 = 0 :=
          fun T => by
            generalize jobs[k].layers.getD l [] = L at hj ⊢
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega : (List.range L.length).length ≤ j)]
        rw [e1]
        simp only [e2, Finset.sum_const_zero]
  · simp [hinv.length_tuples]
  · refine tupleAgrees_append i _ _ _ _ (hinv.length_tuples i) (hinv.agree_tuples i) ⟨fun T hT => ?_, rfl, rfl⟩
    refine ⟨hX i T hT, hY i T hT, ?_⟩
    funext g
    simp [hT]
  · intro τ hτ
    rcases List.mem_append.1 hτ with hτ | hτ
    · exact hinv.product τ hτ
    · simp only [List.mem_singleton] at hτ
      subst hτ
      intro g hg
      simp only [shareValue, if_pos hg]
      exact hprod g

theorem le_foldl_max (l : List ℕ) : ∀ init, init ≤ l.foldl max init ∧ ∀ a ∈ l, a ≤ l.foldl max init := by
  induction l with
  | nil => simp
  | cons b l ih =>
    intro init
    obtain ⟨h1, h2⟩ := ih (max init b)
    refine ⟨(le_max_left _ _).trans h1, fun a ha => ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · exact (le_max_right _ _).trans h1
    · exact h2 a ha

theorem foldl_max_const (l : List ℕ) (w : ℕ) (hl : l ≠ []) (h : ∀ a ∈ l, a = w) : l.foldl max 0 = w := by
  have key : ∀ (l : List ℕ) init, (∀ a ∈ l, a = w) → l.foldl max init = if l = [] then init else max init w := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih =>
      intro init h
      have hb := h b List.mem_cons_self
      subst hb
      rw [List.foldl_cons, ih _ fun a ha => h a (List.mem_cons_of_mem _ ha)]
      split_ifs <;> simp_all
  rw [key l 0 h, if_neg hl]
  simp

theorem plainAt_of_le (job : Circuit) (w : List Bit) : ∀ d, job.layers.length ≤ d →
    plainAt job w d = plainAt job w job.layers.length := by
  intro d hd
  induction d with
  | zero => rw [Nat.le_zero.1 hd]
  | succ d ih =>
    rcases Nat.lt_or_ge job.layers.length (d + 1) with h | h
    · rw [plainAt_succ, plainLayer, ih (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show job.layers.length ≤ d by omega)]
    · rw [show d + 1 = job.layers.length by omega]

theorem plainAt_length (job : Circuit) (w : List Bit) :
    plainAt job w job.layers.length =
      job.layers.foldl (fun w layer => w ++ layer.map fun ab => ab.1.eval w * ab.2.eval w) w := by
  have hl : (List.range job.layers.length).map (fun l => job.layers.getD l []) = job.layers :=
    List.ext_getElem (by simp) fun k h₁ h₂ => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
  conv_rhs => rw [← hl]
  rw [List.foldl_map]
  rfl

theorem layers_le_depth (k : ℕ) (hk : k < jobs.length) : jobs[k].layers.length ≤ depth jobs :=
  (le_foldl_max _ 0).2 _ (List.mem_map.2 ⟨jobs[k], List.getElem_mem hk, rfl⟩)

theorem shareValue_one (g : ℕ) : shareValue (one (R := Bit) K) g = 1 := by
  simp [shareValue, one]

/-- The opened outputs of a batch are the outputs of `F_main`. -/
theorem assemble_eq (p : C.Party → List (C.Term → List Bit) × List (Tuple C)) (W : List (C.Term → List Bit))
    (Ts : List (Tuple C)) (hinv : LayerInv jobs x (depth jobs) p W Ts) (V : ℕ → Bit)
    (hV : ∀ g < (outputsOf jobs).length, V g = shareValue (outputShares K jobs W) g) :
    assemble jobs V = mainOutputs jobs x := by
  unfold assemble mainOutputs
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  simp only [List.length_zipIdx, List.length_map] at h₁ h₂
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  rw [Circuit.eval, ← plainAt_length, ← plainAt_of_le _ _ _ (layers_le_depth jobs k h₂)]
  refine List.ext_getElem (by simp [vector]) fun g hg₁ hg₂ => ?_
  simp only [vector, List.getElem_map, List.getElem_range, List.length_map] at hg₁ ⊢
  have hoff : ((jobs.map (·.outputs)).take k).map List.length = (jobs.map (·.outputs.length)).take k := by
    simp [List.map_take]
    rfl
  have hget := getElem?_flatIdx (jobs.map (·.outputs)) 0 k g (by simpa using h₂) (by simpa using hg₁)
  rw [hoff, ← outputsOf_eq] at hget
  have hlt : ((jobs.map (·.outputs.length)).take k).sum + g < (outputsOf jobs).length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  rw [hV _ hlt, shareValue]
  simp only [outputShares, hget]
  simp only [Nat.zero_add, List.getElem_map]
  exact sum_affine_share _ _ _ _ (hinv.sum_plain k h₂)

/-- The inputs of a batch give the invariant before the layers. -/
theorem layerInv_zero (hx : MainInputs jobs noCoalition x) :
    LayerInv jobs x 0 (fun i => (x i, [])) ((List.range jobs.length).map fun k => reconstruct fun i => (x i)[k]?) [] := by
  obtain ⟨widths, -, hwidth, hcons⟩ := hx
  have hlen : ∀ i, (x i).length = jobs.length := fun i => (hwidth i (by simp [noCoalition])).1
  have hW : ∀ k (hk : k < jobs.length),
      ((List.range jobs.length).map fun k => reconstruct fun i => (x i)[k]?).getD k (fun _ => []) =
        reconstruct fun i => (x i)[k]? := fun k hk => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_range hk]
  have hrec : ∀ k (hk : k < jobs.length) i T, i ∈ C.holders T →
      (reconstruct fun i => (x i)[k]?) T = ((x i)[k]'(by rw [hlen]; exact hk)) T := fun k hk i T hi =>
    reconstruct_of_agree _ T _ fun j hj => ⟨(x j)[k]'(by rw [hlen]; exact hk),
      List.getElem?_eq_getElem _, by
        have := hcons k T j hj i hi (by simp [noCoalition]) (by simp [noCoalition])
        simpa [List.getElem?_eq_getElem (by rw [hlen]; exact hk : k < (x j).length),
          List.getElem?_eq_getElem (by rw [hlen]; exact hk : k < (x i).length)] using this⟩
  have hlenT : ∀ k (hk : k < jobs.length) T, ((reconstruct fun i => (x i)[k]?) T).length = widths.getD k 0 := by
    intro k hk T
    obtain ⟨h, hh⟩ := exists_holder T
    rw [hrec k hk h T hh]
    have := (hwidth h (by simp [noCoalition])).2 k hk T
    simpa [List.getElem?_eq_getElem (by rw [hlen]; exact hk : k < (x h).length), hh] using this
  have hinput : ∀ k (hk : k < jobs.length), (plainInput x k).length = widths.getD k 0 := by
    intro k hk
    unfold plainInput inputValue
    rw [List.length_map, List.length_range]
    refine foldl_max_const _ _ ?_ fun a ha => ?_
    · obtain ⟨T₀, -⟩ := Option.isSome_iff_exists.1 (lackedTerm_empty_isSome (C := C))
      exact List.ne_nil_of_mem (List.mem_map_of_mem (mem_terms T₀))
    · obtain ⟨T, -, rfl⟩ := List.mem_map.1 ha
      exact hlenT k hk T
  refine ⟨fun i => hlen i, by simp, fun i T hi k => ?_, fun k hk T => ?_, fun k hk g => ?_, fun i => rfl,
    fun i m hm => absurd hm (by simp), fun τ hτ => absurd hτ (by simp)⟩
  · rcases Nat.lt_or_ge k jobs.length with hk | hk
    · rw [hW k hk, hrec k hk i T hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hk)]
      rfl
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen i]; exact hk),
        List.getElem?_eq_none (by simpa using hk)]
  · rw [hW k hk, hlenT k hk T, plainAt, List.range_zero, List.foldl_nil, hinput k hk]
  · rw [hW k hk, plainAt, List.range_zero, List.foldl_nil]
    unfold plainInput inputValue
    rcases Nat.lt_or_ge g ((C.terms.map fun T => ((reconstruct fun i => (x i)[k]?) T).length).foldl max 0) with hg | hg
    · simp [List.getD_eq_getElem?_getD, List.getElem?_range hg]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hg)]
      symm
      refine Finset.sum_eq_zero fun T _ => ?_
      have := hinput k hk
      unfold plainInput inputValue at this
      rw [List.length_map, List.length_range] at this
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlenT k hk T, ← this]; exact hg)]
      rfl

end Values

/-! ## The rounds of an honest batch -/

section Rounds

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) (K : Constants C E)
  (mode : ReshareMode) (jobs : List Circuit)

theorem callStep_not_done (ls : List ℕ) (p : C.Party → List (C.Term → List Bit) × List (Tuple C)) :
    ¬ ∀ i, (callStep K mode jobs i ls (p i)).isDone := by
  have hpos : 0 < C.n := by have := C.one_le_t; unfold Committee.n; omega
  intro h
  have := h ⟨0, hpos⟩
  cases ls <;> exact this

/-- The step of a layer gives the next calls, with one sharing of the products. -/
theorem honestStep_layer (l : ℕ) (ls : List ℕ) (p : C.Party → List (C.Term → List Bit) × List (Tuple C))
    (s : HashCache C) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (honestStep (mainFunctionalities K mode) mainReply
      fun i => callStep K mode jobs i (l :: ls) (p i))).run s)) :
    ∃ zz : Shares C Bit, (∀ g, ∑ T, zz T g =
        ∑ i, mulRep K (localContext i) (layerX K jobs l (p i).1) (layerY K jobs l (p i).1) g) ∧
      z.1 = fun i => callStep K mode jobs i ls
        (appendLayer jobs l (p i).1 (fun T g => if i ∈ C.holders T ∧ g < (gatesAt jobs l).length then zz T g else 0),
          (p i).2 ++ [⟨layerX K jobs l (p i).1, layerY K jobs l (p i).1,
            fun T g => if i ∈ C.holders T ∧ g < (gatesAt jobs l).length then zz T g else 0,
            (gatesAt jobs l).length, mode⟩]) := by
  have hpos : 0 < C.n := by have := C.one_le_t; unfold Committee.n; omega
  unfold honestStep at hz
  rw [if_pos ⟨⟨⟨0, hpos⟩, rfl⟩, fun i => Or.inl rfl⟩] at hz
  unfold honestFunctionality at hz
  rw [if_neg (by simp [callStep, Step.callInput])] at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨outs, s₁⟩, h₁, hz⟩ := hz
  have h₁' : outs ∈ support (simulateQ (replyImpl mainReply) ((mainFunctionalities K mode).run noCoalition
      fun i => (callStep K mode jobs i (l :: ls) (p i)).callInput)) := by
    refine support_simulateQ_run'_subset (localAnswer prims) _ s ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨_, h₁, rfl⟩
  obtain ⟨zz, hzz, rfl⟩ := honest_mult_support K mode (fun i => layerX K jobs l (p i).1)
    (fun i => layerY K jobs l (p i).1) (gatesAt jobs l).length outs h₁'
  refine ⟨zz, hzz, ?_⟩
  simp only [callStep] at hz
  simp only [advance_progAt, sequenceFin_pure, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  rw [hz]

set_option linter.constructorNameAsVariable false in
/-- `F_mult` of `Rerand` in an honest run gives each operator its held terms of one sharing of the product. -/
theorem honest_rerand_support (X Y : C.Party → Shares C Bit) (n : ℕ) o
    (ho : o ∈ support (simulateQ (replyImpl mainReply) ((mainFunctionalities K mode).run noCoalition
      fun i => some (Sum.inl (Sum.inr (X i, Y i, n)))))) :
    ∃ z : Shares C Bit, (∀ g, ∑ T, z T g = ∑ i, mulRep K (localContext i) (X i) (Y i) g) ∧
      o = fun i => some (.inl (.inr fun T g => if i ∈ C.holders T ∧ g < n then z T g else 0)) := by
  have hpos : 0 < C.n := by have := C.one_le_t; unfold Committee.n; omega
  haveI : Nonempty C.Party := ⟨⟨0, hpos⟩⟩
  simp only [mainFunctionalities, Functionality.sum, FmultBit, Fmult, leak, sample, OracleComp.lift] at ho
  simp [noCoalition, simulateQ_bind, simulateQ_query, replyImpl, mainReply] at ho
  dsimp only [HAdd.hAdd, QueryImpl.add] at ho
  simp at ho
  simp [simulateQ_bind, simulateQ_query, QueryImpl.add, OracleComp.lift] at ho
  have hfi : (firstInput fun i => some (X i, Y i, n)).2.2 = n := by rw [firstInput_some_pos]
  set m := (firstInput fun i => some (X i, Y i, n)).2.2 with hm
  rw [← hfi]
  obtain ⟨fresh, -, rfl⟩ := ho
  obtain ⟨T₀, hT₀⟩ := Option.isSome_iff_exists.1 (lackedTerm_empty_isSome (C := C))
  let base : Shares C Bit := fun T g => if h : g < m then fresh T ⟨g, h⟩ else 0
  refine ⟨fun T g => if lackedTerm ∅ = some T then
      (∑ x, mulRep K (localContext x) (X x) (Y x) g) - ∑ T' ∈ Finset.univ.erase T, base T' g
      else base T g, fun g => ?_, ?_⟩
  · have := sum_lacked (C := C) T₀ base (fun g => ∑ x, mulRep K (localContext x) (X x) (Y x) g) g
    simp only [hT₀, Option.some.injEq]
    exact this
  · funext i
    simp only [KnownTo, Finset.notMem_empty, false_and, exists_false, if_false]
    congr 3
    funext T g
    have h0 : ∀ a : Bit, Add.add a 0 = a := fun a => add_zero a
    split_ifs <;> simp_all [base, m, Finset.sum_erase_eq_sub, h0]

set_option linter.constructorNameAsVariable false in
/-- `F_multVerify` in an honest run accepts tuples that agree and multiply. -/
theorem honest_verify_support (views : C.Party → List (Tuple C)) (Ts : List (Tuple C))
    (hlen : ∀ i, (views i).length = Ts.length)
    (hag : ∀ i m (hm : m < Ts.length), TupleAgrees i ((views i)[m]'(by rw [hlen]; exact hm)) Ts[m])
    (hprod : ∀ τ ∈ Ts, IsProduct τ) o
    (ho : o ∈ support (simulateQ (replyImpl mainReply) ((mainFunctionalities K mode).run noCoalition
      fun i => some (Sum.inr (views i))))) :
    o = fun _ => some (.inr ()) := by
  have hpos : 0 < C.n := by have := C.one_le_t; unfold Committee.n; omega
  haveI : Nonempty C.Party := ⟨⟨0, hpos⟩⟩
  have hfirst := firstInput_some_pos (C := C) views
  simp only [mainFunctionalities, Functionality.sum, FmultVerify, leak, OracleComp.lift] at ho
  simp [noCoalition, simulateQ_bind, simulateQ_query, replyImpl, mainReply] at ho
  dsimp only [HAdd.hAdd, QueryImpl.add] at ho
  simp at ho
  simp [QueryImpl.add] at ho
  have hL : (firstInput fun i => some (views i)).length = Ts.length := by rw [hfirst, hlen]
  have htup : (List.range Ts.length).map (tupleAt fun i => some (views i)) = Ts := by
    refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
    simp only [List.getElem_map, List.getElem_range]
    exact tupleAt_of_agree views Ts hlen hag k h₂
  rw [← ho]
  funext i
  rw [if_pos]
  refine ⟨by simp, ?_, by simp⟩
  simp only [decide_eq_true_eq]
  refine ⟨fun k hk T i hi j hj _ _ g _ => ?_, fun τ hτ => ?_⟩
  · rw [hL] at hk
    rw [List.getElem?_eq_getElem (by rw [hlen]; exact hk), List.getElem?_eq_getElem (by rw [hlen]; exact hk)]
    obtain ⟨hxi, hyi, hzi⟩ := (hag i k hk).1 T hi
    obtain ⟨hxj, hyj, hzj⟩ := (hag j k hk).1 T hj
    simp [hxi, hyi, hzi, hxj, hyj, hzj]
  · rw [hL, htup] at hτ
    exact hprod τ hτ

set_option linter.constructorNameAsVariable false in
/-- The step of `Rerand` gives the calls of `F_multVerify`, with one sharing of the outputs. -/
theorem honestStep_rerand (p : C.Party → List (C.Term → List Bit) × List (Tuple C)) (s : HashCache C) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (honestStep (mainFunctionalities K mode) mainReply
      fun i => callStep K mode jobs i [] (p i))).run s)) :
    ∃ v : Shares C Bit, (∀ g, ∑ T, v T g = ∑ i, mulRep K (localContext i) (outputShares K jobs (p i).1) (one K) g) ∧
      ∃ resume : C.Party → Option ((Shares C Bit ⊕ Shares C Bit) ⊕ Unit) →
          OracleComp (PartySpec C E (MainSpec C)) (Option (List (List Bit))),
        (∀ i, resume i (some (.inr ())) = ((fun opened => assemble jobs opened) <$> openRep K (localContext i)
          (fun T g => if i ∈ C.holders T ∧ g < (outputsOf jobs).length then v T g else 0) (outputsOf jobs).length).run) ∧
        z.1 = fun i => .call (Sum.inr ((p i).2 ++ [⟨outputShares K jobs (p i).1, one K,
          fun T g => if i ∈ C.holders T ∧ g < (outputsOf jobs).length then v T g else 0,
          (outputsOf jobs).length, .peer⟩])) (resume i) := by
  have hpos : 0 < C.n := by have := C.one_le_t; unfold Committee.n; omega
  unfold honestStep at hz
  rw [if_pos ⟨⟨⟨0, hpos⟩, rfl⟩, fun i => Or.inl rfl⟩] at hz
  unfold honestFunctionality at hz
  rw [if_neg (by simp [callStep, Step.callInput])] at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨outs, s₁⟩, h₁, hz⟩ := hz
  have h₁' : outs ∈ support (simulateQ (replyImpl mainReply) ((mainFunctionalities K mode).run noCoalition
      fun i => some (Sum.inl (Sum.inr (outputShares K jobs (p i).1, one K, (outputsOf jobs).length))))) := by
    refine support_simulateQ_run'_subset (localAnswer prims) _ s ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨_, h₁, rfl⟩
  obtain ⟨v, hv, rfl⟩ := honest_rerand_support K mode (fun i => outputShares K jobs (p i).1) (fun _ => one K)
    (outputsOf jobs).length outs h₁'
  refine ⟨v, hv, ?_⟩
  simp only [callStep] at hz
  simp only [Option.map_some, advance_call_bind, sequenceFin_pure, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  exact ⟨_, fun i => rfl, by rw [hz]⟩

/-- The step of `F_multVerify` gives the round of `OpenRep`, with the digests of every operator in the cache. -/
theorem honestStep_verify (views : C.Party → List (Tuple C)) (Ts : List (Tuple C))
    (hlen : ∀ i, (views i).length = Ts.length)
    (hag : ∀ i m (hm : m < Ts.length), TupleAgrees i ((views i)[m]'(by rw [hlen]; exact hm)) Ts[m])
    (hprod : ∀ τ ∈ Ts, IsProduct τ) (v' : C.Party → Shares C Bit) (count : ℕ)
    (resume : C.Party → Option ((Shares C Bit ⊕ Shares C Bit) ⊕ Unit) →
      OracleComp (PartySpec C E (MainSpec C)) (Option (List (List Bit))))
    (hres : ∀ i, resume i (some (.inr ())) =
      ((fun opened => assemble jobs opened) <$> openRep K (localContext i) (v' i) count).run)
    (s : HashCache C) (steps : C.Party → Step C E (MainSpec C) (List (List Bit)))
    (hsteps : ∀ i, steps i = .call (Sum.inr (views i)) (resume i)) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (honestStep (mainFunctionalities K mode) mainReply
      steps)).run s)) :
    ∃ ds : C.Party → List HashOutput,
      z.1 = (fun i => .wait (repOutbox K i (v' i) count (ds i)) (exchangeResume fun inbox =>
        (fun opened => assemble jobs opened) <$> repRest K i (v' i) count inbox)) ∧ s ≤ z.2 ∧
      ∀ i, ∃ h : (ds i).length = C.terms.length, ∀ k (hk : k < C.terms.length),
        z.2 (.copy (vector count (v' i C.terms[k]))) = some ((ds i)[k]'(h ▸ hk)) := by
  obtain rfl : steps = _ := funext hsteps
  have hpos : 0 < C.n := by have := C.one_le_t; unfold Committee.n; omega
  unfold honestStep at hz
  rw [if_pos ⟨⟨⟨0, hpos⟩, rfl⟩, fun i => Or.inl rfl⟩] at hz
  unfold honestFunctionality at hz
  rw [if_neg (by simp [Step.callInput])] at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨outs, s₁⟩, h₁, hz⟩ := hz
  have hs₁ : s ≤ s₁ := Grows.simulateQ (grows_localAnswer prims) _ s _ h₁
  have h₁' : outs ∈ support (simulateQ (replyImpl mainReply) ((mainFunctionalities K mode).run noCoalition
      fun i => some (Sum.inr (views i)))) := by
    refine support_simulateQ_run'_subset (localAnswer prims) _ s ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨_, h₁, rfl⟩
  have houts := honest_verify_support K mode views Ts hlen hag hprod outs h₁'
  subst houts
  simp only [hres, advance_openRep] at hz
  rw [sequenceFin_bind_pure, simulateQ_bind, simulateQ_sequenceFin, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨dss, s₂⟩, h₂, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨hs₂, hP⟩ := support_sequenceFin_state s₁ _
    (fun i (ds : List HashOutput) (σ : HashCache C) => ∃ h : ds.length = C.terms.length, ∀ k (hk : k < C.terms.length),
      σ (.copy (vector count (v' i C.terms[k]))) = some (ds[k]'(h ▸ hk)))
    (fun i σ _ w hw => by
      obtain ⟨h, hle, hc⟩ := support_hashes prims C.terms (fun T => .copy (vector count (v' i T)))
        (fun T ⟨_, hT, _⟩ => by cases hT) σ w hw
      exact ⟨hle, h, hc⟩)
    (fun i ds σ σ' ⟨h, hc⟩ hle => ⟨h, fun k hk => hle (hc k hk)⟩) s₁ le_rfl _ h₂
  exact ⟨dss, rfl, hs₁.trans hs₂, hP⟩

theorem vector_congr {R : Type} (count : ℕ) (a b : ℕ → R) (h : ∀ g < count, a g = b g) :
    vector count a = vector count b := by
  unfold vector
  exact List.map_congr_left fun g hg => h g (List.mem_range.1 hg)

/-- The round of `OpenRep` ends every operator with the sum of the shared terms. -/
theorem honestStep_open {I O L R : Type} (F : Functionality C I O L R) (reply : L → R) {β : Type}
    (w : Shares C Bit) (count : ℕ) (vr : C.Party → Shares C Bit)
    (hvr : ∀ i T g, i ∈ C.holders T → g < count → vr i T g = w T g) (ds : C.Party → List HashOutput)
    (hlen : ∀ i, (ds i).length = C.terms.length) (s : HashCache C)
    (hcache : ∀ i k (hk : k < C.terms.length),
      s (.copy (vector count (vr i C.terms[k]))) = some ((ds i)[k]'(by rw [hlen]; exact hk)))
    (f : (ℕ → Bit) → β) (steps : C.Party → Step C E (CallSpec I O) β)
    (hsteps : ∀ i, steps i = .wait (repOutbox (E := E) K i (vr i) count (ds i))
        (exchangeResume fun inbox => f <$> repRest (G := CallSpec I O) K i (vr i) count inbox)) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (honestStep F reply steps)).run s)) :
    ∃ V : C.Party → ℕ → Bit, (∀ i g, g < count → V i g = ∑ T, w T g) ∧ z.1 = fun i => .done (some (f (V i))) := by
  obtain rfl : steps = _ := funext hsteps
  have hidx : ∀ T : C.Term, C.terms.idxOf T < C.terms.length := fun T => List.idxOf_lt_length_of_mem (mem_terms T)
  let val : C.Term → HashOutput := fun T => (ds (K.owner T))[C.terms.idxOf T]'(by rw [hlen]; exact hidx T)
  have hvec : ∀ h T, h ∈ C.holders T → vector count (vr h T) = vector count (vr (K.owner T) T) := fun h T hh =>
    vector_congr count _ _ fun g hg => by rw [hvr h T g hh hg, hvr _ T g (K.owner_held T) hg]
  have hval : ∀ T, s (.copy (vector count (vr (K.owner T) T))) = some (val T) := fun T => by
    have := hcache (K.owner T) (C.terms.idxOf T) (hidx T)
    rw [show C.terms[C.terms.idxOf T]'(hidx T) = T from List.getElem_idxOf _] at this
    exact this
  have hds : ∀ h T, h ∈ C.holders T → (ds h)[C.terms.idxOf T]? = some (val T) := fun h T hh => by
    have h1 := hcache h (C.terms.idxOf T) (hidx T)
    rw [show C.terms[C.terms.idxOf T]'(hidx T) = T from List.getElem_idxOf _, hvec h T hh, hval T] at h1
    simp only [Option.some.injEq] at h1
    rw [List.getElem?_eq_getElem (by rw [hlen]; exact hidx T), h1]
  rw [honestStep_exchange] at hz
  have hnoabort : ∀ j k, Msg.isAbort (repOutbox (E := E) K k (vr k) count (ds k) j) = false := fun j k => by
    unfold repOutbox
    split_ifs <;> rfl
  simp only [exchangeResume_of_no_abort _ _ (hnoabort _), advance_openRest] at hz
  rw [simulateQ_sequenceFin] at hz
  obtain ⟨-, hP⟩ := support_sequenceFin_state s _
    (fun j (step : Step C E (CallSpec I O) β) (_ : HashCache C) => step = .done (some (f fun g =>
      ∑ T, repCopy K j (vr j) count (fun k => repOutbox (E := E) K k (vr k) count (ds k) j) T g)))
    (fun j σ hσ y hy => by
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hy
      obtain ⟨⟨cds, σ'⟩, h₁, hy⟩ := hy
      have hq : ∀ T ∈ C.terms, σ (.copy (vector count (repCopy K j (vr j) count
          (fun k => repOutbox (E := E) K k (vr k) count (ds k) j) T))) = some (val T) := fun T _ => by
        rw [vector_congr count _ (vr (K.owner T) T) fun g hg => by
          rw [openCopy_eq K j count w vr hvr ds T g hg, hvr _ T g (K.owner_held T) hg]]
        exact hσ (hval T)
      have := support_hashes_cached prims C.terms _ (fun T ⟨_, hT, _⟩ => by cases hT) σ val hq _ h₁
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rw [if_pos (repCheck_honest K j count vr ds val hlen hds)] at hy
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨le_rfl, rfl⟩)
    (fun _ _ _ _ h _ => h) s le_rfl z hz
  refine ⟨fun j g => ∑ T, repCopy K j (vr j) count (fun k => repOutbox (E := E) K k (vr k) count (ds k) j) T g,
    fun j g hg => Finset.sum_congr rfl fun T _ => openCopy_eq K j count w vr hvr ds T g hg, funext hP⟩

variable (x : C.Party → List (C.Term → List Bit))

/-- After the layers, `Rerand`, `F_multVerify` and `OpenRep` give every operator the outputs of `F_main`. -/
theorem tail_support (p : C.Party → List (C.Term → List Bit) × List (Tuple C)) (W : List (C.Term → List Bit))
    (Ts : List (Tuple C)) (hinv : LayerInv jobs x (depth jobs) p W Ts) (s : HashCache C) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (honestRounds (mainFunctionalities K mode) mainReply 3
      fun i => callStep K mode jobs i [] (p i))).run s)) :
    z.1 = fun _ => some (mainOutputs jobs x) := by
  have hpos : 0 < C.n := by have := C.one_le_t; unfold Committee.n; omega
  rw [show (3 : ℕ) = 2 + 1 from rfl, honestRounds_succ _ _ _ _ (callStep_not_done K mode jobs [] p),
    simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨st₁, s₁⟩, h₁, hz⟩ := hz
  obtain ⟨v, hv, resume, hres, hst₁⟩ := honestStep_rerand prims K mode jobs p s _ h₁
  dsimp only at hst₁ hz
  subst hst₁
  have hO : ∀ i T, i ∈ C.holders T → outputShares K jobs (p i).1 T = outputShares K jobs W T :=
    fun i T h => outputShares_congr K jobs _ _ T (hinv.agree i T h)
  have hsum : ∀ g, ∑ T, v T g = shareValue (outputShares K jobs W) g := fun g => by
    rw [hv g, mulRep_views_sum K _ _ _ (one K) g (fun i T h => by rw [hO i T h]) (fun _ _ _ => rfl),
      shareValue_one, mul_one]
  rw [honestRounds_succ _ _ _ _ ?nd₁, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  case nd₁ => exact fun h => h ⟨0, hpos⟩
  obtain ⟨⟨st₂, s₂⟩, h₂, hz⟩ := hz
  obtain ⟨ds, hst₂, -, hcache⟩ := honestStep_verify prims K mode jobs
    (fun i => (p i).2 ++ [⟨outputShares K jobs (p i).1, one K,
      fun T g => if i ∈ C.holders T ∧ g < (outputsOf jobs).length then v T g else 0, (outputsOf jobs).length, .peer⟩])
    (Ts ++ [⟨outputShares K jobs W, one K, fun T g => if g < (outputsOf jobs).length then v T g else 0,
      (outputsOf jobs).length, .peer⟩]) (by intro i; simp [hinv.length_tuples])
    (by
      intro i
      refine tupleAgrees_append i _ _ _ _ (hinv.length_tuples i) (hinv.agree_tuples i)
        ⟨fun T hT => ⟨hO i T hT, rfl, funext fun g => by simp [hT]⟩, rfl, rfl⟩)

    (by
      intro τ hτ
      rcases List.mem_append.1 hτ with hτ | hτ
      · exact hinv.product τ hτ
      · simp only [List.mem_singleton] at hτ
        subst hτ
        intro g hg
        rw [shareValue_one, mul_one, ← hsum g]
        simp only [shareValue, if_pos hg])
    (fun i T g => if i ∈ C.holders T ∧ g < (outputsOf jobs).length then v T g else 0) (outputsOf jobs).length
    resume hres s₁ _ (by intro i; rfl) _ h₂
  dsimp only at hst₂ hz
  subst hst₂
  rw [honestRounds_succ _ _ _ _ ?nd₂, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  case nd₂ => exact fun h => h ⟨0, hpos⟩
  obtain ⟨⟨st₃, s₃⟩, h₃, hz⟩ := hz
  obtain ⟨V, hV, hst₃⟩ := honestStep_open prims K (mainFunctionalities K mode) mainReply v (outputsOf jobs).length
    (fun i T g => if i ∈ C.holders T ∧ g < (outputsOf jobs).length then v T g else 0)
    (fun i T g hi hg => by simp [hi, hg]) ds (fun i => (hcache i).1) s₂
    (fun i k hk => (hcache i).2 k hk) _ _ (fun i => rfl) _ h₃
  dsimp only at hst₃ hz
  subst hst₃
  simp only [honestRounds, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  funext i
  simp only [Step.output]
  rw [assemble_eq K jobs x p W Ts hinv (V i) fun g hg => by rw [hV i g hg, hsum g]]

/-- The layers keep the invariant and end in `tail_support`. -/
theorem rounds_support : ∀ (k l : ℕ) (p : C.Party → List (C.Term → List Bit) × List (Tuple C))
    (W : List (C.Term → List Bit)) (Ts : List (Tuple C)), l + k = depth jobs → LayerInv jobs x l p W Ts →
    ∀ (s : HashCache C) z, z ∈ support ((simulateQ (localAnswer prims) (honestRounds (mainFunctionalities K mode)
      mainReply (k + 3) fun i => callStep K mode jobs i (List.range' l k) (p i))).run s) →
    z.1 = fun _ => some (mainOutputs jobs x)
  | 0, l, p, W, Ts, hkl, hinv, s, z, hz => by
    simp only [Nat.add_zero] at hkl
    subst hkl
    exact tail_support prims K mode jobs x p W Ts hinv s z hz
  | k + 1, l, p, W, Ts, hkl, hinv, s, z, hz => by
    rw [List.range'_succ, show k + 1 + 3 = (k + 3) + 1 from rfl,
      honestRounds_succ _ _ _ _ (callStep_not_done K mode jobs _ p), simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨⟨st₁, s₁⟩, h₁, hz⟩ := hz
    obtain ⟨zz, hzz, hst₁⟩ := honestStep_layer prims K mode jobs l _ p s _ h₁
    dsimp only at hst₁
    subst hst₁
    exact rounds_support k (l + 1) _ _ _ (by omega) (layerInv_step K jobs x mode l p W Ts hinv zz hzz) s₁ z hz

theorem support_map_free {β γ : Type} (f : β → γ) (oa : OracleComp (LocalSpec C) β) (s₀ : HashCache C) a s
    (h : (a, s) ∈ support ((simulateQ (worldAnswer prims) (f <$> free oa)).run s₀)) :
    ∃ b t, (b, t) ∈ support ((simulateQ (localAnswer prims) oa).run s₀) ∧ a = f b := by
  rw [simulateQ_map, simulateQ_free, StateT.run_map, support_map] at h
  obtain ⟨⟨b, t⟩, hb, hbt⟩ := h
  simp only [Prod.mk.injEq] at hbt
  exact ⟨b, t, hb, hbt.1.symm⟩

/-- Every honest run of a batch gives the outputs of `F_main`. -/
theorem main_honest_support (hx : MainInputs jobs noCoalition x) :
    ∀ r ∈ support (mainHonestRun prims K mode jobs x), r.1.2 = fun _ => some (mainOutputs jobs x) := by
  intro r hr
  rw [mainHonestRun, realExecution_honest] at hr
  obtain ⟨s', hs'⟩ := support_runWorld prims _ r hr
  obtain ⟨o, so, ho, hob⟩ := support_map_free prims _ _ ∅ _ _ hs'
  rw [hob]
  simp only [honestStart, mainProtocol_eq, advance_progAt, sequenceFin_pure, pure_bind] at ho
  rw [List.range_eq_range'] at ho
  exact rounds_support prims K mode jobs x (depth jobs) 0 _ _ _ (by omega) (layerInv_zero jobs x hx) ∅ _ ho

end Rounds

/-- An honest batch gives the outputs of `F_main`. -/
theorem mainCompleteness {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
    (prims : Primitives) (K : Constants C E) : MainCompletenessStatement prims K :=
  mainCompleteness_of_real prims K fun mode jobs x hx => main_honest_support prims K mode jobs x hx

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- A corrupt operator's additive product share uses only known terms. -/
theorem main_mulRep_known (K : Constants C E) (D : C.Coalition)
    (i : C.Party) (hi : i ∈ D.1) (x y : Shares C Bit) (count g : ℕ)
    (hg : g < count) :
    mulRep K (localContext i) (knownView D.1 count x) (knownView D.1 count y) g =
      mulRep K (localContext i) x y g := by
  unfold mulRep
  refine Finset.sum_congr rfl fun AB hAB => ?_
  obtain ⟨ha, hb⟩ := K.pairs_held i AB hAB
  have hka : KnownTo D.1 AB.1 := ⟨i, hi, ha⟩
  have hkb : KnownTo D.1 AB.2 := ⟨i, hi, hb⟩
  simp only [knownView, hka, hkb, hg, and_self, if_true]

/-- Splitting the additive shares into honest and corrupt contributions. -/
theorem main_mulRep_honest_add_corrupt (K : Constants C E) (D : C.Coalition)
    (x y : Shares C Bit) (g : ℕ) :
    (∑ i ∈ Finset.univ.filter (fun i => i ∉ D.1), mulRep K (localContext i) x y g) +
      (∑ i ∈ Finset.univ.filter (fun i => i ∈ D.1), mulRep K (localContext i) x y g) =
      shareValue x g * shareValue y g := by
  rw [Finset.sum_filter_not_add_sum_filter]
  exact mulRep_views_sum K (fun _ => x) (fun _ => y) x y g
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)

/-- The multiplication difference is computable from the attack and the known terms. -/
theorem main_mulRep_difference (K : Constants C E) (D : C.Coalition)
    (x y : Shares C Bit) (count g : ℕ) (hg : g < count) (d : Bit) :
    ((∑ i ∈ Finset.univ.filter (fun i => i ∉ D.1),
        mulRep K (localContext i) x y g) + d) - shareValue x g * shareValue y g =
      d - ∑ i ∈ Finset.univ.filter (fun i => i ∈ D.1),
        mulRep K (localContext i) (knownView D.1 count x) (knownView D.1 count y) g := by
  have hknown : (∑ i ∈ Finset.univ.filter (fun i => i ∈ D.1),
      mulRep K (localContext i) (knownView D.1 count x) (knownView D.1 count y) g) =
      ∑ i ∈ Finset.univ.filter (fun i => i ∈ D.1), mulRep K (localContext i) x y g := by
    refine Finset.sum_congr rfl fun i hi => ?_
    exact main_mulRep_known K D i (Finset.mem_filter.mp hi).2 x y count g hg
  rw [hknown, ← main_mulRep_honest_add_corrupt K D x y g]
  ring

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- Each replicated term has an honest holder. -/
theorem main_exists_honest_holder (D : C.Coalition) (T : C.Term) :
    ∃ i, i ∈ C.holders T ∧ i ∉ D.1 := by
  have hcard : D.1.card < (C.holders T).card := by
    rw [Committee.holders, Finset.card_compl, T.2, Fintype.card_fin]
    have := D.2
    have := C.one_le_t
    simp only [Committee.n]
    omega
  obtain ⟨i, hi, hiD⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨i, hi, hiD⟩

/-- A collision between distinct inputs in the copy domain. -/
def MainCopyCollision (s : HashCache C) : Prop :=
  ∃ (a b : List Bit) (u : HashOutput), a ≠ b ∧
    s (.copy a) = some u ∧ s (.copy b) = some u

theorem main_copy_eq_of_not_collision (s : HashCache C) (hs : ¬ MainCopyCollision s)
    (a b : List Bit) (u : HashOutput)
    (ha : s (.copy a) = some u) (hb : s (.copy b) = some u) : a = b := by
  by_contra hab
  exact hs ⟨a, b, u, hab, ha, hb⟩

/-- The honest hash sent for one term has its original index in the digest list. -/
theorem main_open_hash_sent (K : Constants C E) (i h : C.Party) (v : Shares C Bit)
    (count : ℕ) (ds : List HashOutput) (hlen : ds.length = C.terms.length)
    (T : C.Term) (hiT : i ∉ C.holders T) (hhT : h ∈ C.holders T) (hown : h ≠ K.owner T) :
    (Msg.hashesOf (Msg.part (repOutbox K h v count ds i) 1))[
      (C.terms.filter fun T' => i ∉ C.holders T' ∧ h ∈ C.holders T' ∧ K.owner T' ≠ h).idxOf T]? =
      ds[C.terms.idxOf T]? := by
  have hne : i ≠ h := fun e => hiT (e ▸ hhT)
  simp only [repOutbox, if_neg hne, Msg.part, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Msg.hashesOf]
  exact filterMap_zip_idxOf C.terms terms_nodup
    (fun T' => i ∉ C.holders T' ∧ h ∈ C.holders T' ∧ K.owner T' ≠ h)
    ds hlen T (mem_terms T) ⟨hiT, hhT, Ne.symm hown⟩

/-- Passing the copy check gives the correct opening outside a copy-domain collision. -/
theorem main_openCopy_sound (K : Constants C E) (D : C.Coalition)
    (w : Shares C Bit) (vr : C.Party → Shares C Bit) (count : ℕ)
    (hvr : ∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < count → vr i T g = w T g)
    (ds : C.Party → List HashOutput) (hlen : ∀ h, (ds h).length = C.terms.length)
    (i : C.Party) (hiD : i ∉ D.1) (inbox : Mail C E)
    (hinbox : ∀ h, h ∉ D.1 → inbox h = repOutbox K h (vr h) count (ds h) i)
    (cds : List HashOutput) (hcdlen : cds.length = C.terms.length)
    (s : HashCache C) (hs : ¬ MainCopyCollision s)
    (hds : ∀ h T, h ∉ D.1 → ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
      s (.copy (vector count (vr h T))) = some u)
    (hcds : ∀ T, ∃ u, cds[C.terms.idxOf T]? = some u ∧
      s (.copy (vector count (repCopy K i (vr i) count inbox T))) = some u)
    (hcheck : repCheck K i inbox cds) (T : C.Term) (g : ℕ) (hg : g < count) :
    repCopy K i (vr i) count inbox T g = w T g := by
  by_cases hiT : i ∈ C.holders T
  · simpa only [repCopy, if_pos hiT] using hvr i T g hiD hiT hg
  by_cases hown : K.owner T ∉ D.1
  · have hne : i ≠ K.owner T := fun h => hiT (h ▸ K.owner_held T)
    simp only [repCopy, if_neg hiT, hinbox _ hown, repOutbox, if_neg hne,
      Msg.part, List.getElem?_cons_zero, Msg.bitAt]
    rw [getD_flatMap_vector _ _ _ T (List.mem_filter.2 ⟨mem_terms T, by simp [hiT]⟩)
      (terms_nodup.filter _) g hg]
    exact hvr _ T g hown (K.owner_held T) hg
  · obtain ⟨h, hhT, hhD⟩ := main_exists_honest_holder D T
    have hne : h ≠ K.owner T := fun e => hown (e ▸ hhD)
    have hc := hcheck T hiT h hhT hne
    dsimp only at hc
    rw [hinbox h hhD, main_open_hash_sent K i h (vr h) count (ds h) (hlen h) T hiT hhT hne,
      lookup_zip_idxOf C.terms cds hcdlen T (mem_terms T)] at hc
    obtain ⟨u, hu, hsU⟩ := hds h T hhD
    obtain ⟨v, hv, hsV⟩ := hcds T
    rw [hu, hv] at hc
    have huv : u = v := Option.some.inj hc
    subst v
    have heq := main_copy_eq_of_not_collision s hs
      (vector count (vr h T)) (vector count (repCopy K i (vr i) count inbox T)) u hsU hsV
    have heqg := congrArg (fun l : List Bit => l.getD g 0) heq
    have hvec : ∀ f : ℕ → Bit, (vector count f).getD g 0 = f g := by
      intro f
      simp [vector, List.getD_eq_getElem?_getD, List.getElem?_range hg]
    rw [hvec, hvec] at heqg
    exact heqg.symm.trans (hvr h T g hhD hhT hg)

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- The pivot of `F_mult` is unknown to the coalition. -/
theorem main_lacked_unknown (D : C.Coalition) (T : C.Term)
    (h : lackedTerm D.1 = some T) : ¬ KnownTo D.1 T := by
  simpa [lackedTerm] using List.find?_some h

/-- A corrupted filler can only change a term known to the coalition. -/
theorem main_filler_known (K : Constants C E) (D : C.Coalition) (mode : ReshareMode)
    (T : C.Term) (g : ℕ) (h : ∃ j ∈ D.1, filler K mode T g = some j) : KnownTo D.1 T := by
  obtain ⟨j, hj, hf⟩ := h
  refine ⟨j, hj, ?_⟩
  cases mode with
  | peer =>
    have heq : K.filled j = T := by simpa [filler] using List.find?_some hf
    rw [← heq]
    exact K.filled_held j
  | collector =>
    simp only [filler] at hf
    split_ifs at hf with hT
    · have hj' := Option.some.inj hf
      rw [← hj', ← hT]
      exact K.collector_held g

/-- The visible part of `F_mult` is independent of its secret product. -/
def mainMultBase (D : C.Coalition) (count : ℕ) (known : Shares C Bit)
    (fresh : C.Term → Fin count → Bit) : Shares C Bit := fun T g =>
  if KnownTo D.1 T then known T g else if h : g < count then fresh T ⟨g, h⟩ else 0

def mainMultSharing (D : C.Coalition) (base : Shares C Bit) (target : ℕ → Bit) : Shares C Bit :=
  fun T g => if lackedTerm D.1 = some T then
    target g - ∑ T' ∈ Finset.univ.erase T, base T' g else base T g

theorem mainMultSharing_known (D : C.Coalition) (base : Shares C Bit) (target : ℕ → Bit)
    (T : C.Term) (hT : KnownTo D.1 T) : mainMultSharing D base target T = base T := by
  funext g
  have hne : lackedTerm D.1 ≠ some T := fun h => main_lacked_unknown D T h hT
  simp only [mainMultSharing, if_neg hne]

theorem mainMultSharing_sum (D : C.Coalition) (base : Shares C Bit) (target : ℕ → Bit)
    (T₀ : C.Term) (hT₀ : lackedTerm D.1 = some T₀) (g : ℕ) :
    shareValue (mainMultSharing D base target) g = target g := by
  simpa only [shareValue, mainMultSharing, hT₀, Option.some.injEq] using
    sum_lacked T₀ base target g

/-- A product share only reads terms held by the operator. -/
theorem main_mulRep_views (K : Constants C E) (D : C.Coalition)
    (xv yv : C.Party → Shares C Bit) (x y : Shares C Bit)
    (hx : ∀ i T, i ∉ D.1 → i ∈ C.holders T → xv i T = x T)
    (hy : ∀ i T, i ∉ D.1 → i ∈ C.holders T → yv i T = y T)
    (i : C.Party) (hi : i ∉ D.1) :
    mulRep K (localContext i) (xv i) (yv i) = mulRep K (localContext i) x y := by
  funext g
  unfold mulRep
  refine Finset.sum_congr rfl fun AB hAB => ?_
  obtain ⟨hA, hB⟩ := K.pairs_held i AB hAB
  rw [hx i AB.1 hi hA, hy i AB.2 hi hB]

/-- Agreement can be checked on known terms when every unknown term already agrees. -/
theorem main_consistent_iff_known {α : Type} [Zero α] (D : C.Coalition)
    (views : C.Party → C.Term → α)
    (hidden : ∀ T, ¬ KnownTo D.1 T → ConsistentAt D views T) :
    Consistent D views ↔ Consistent D (fun i T => if KnownTo D.1 T then views i T else 0) := by
  constructor
  · intro h T i hi j hj hiD hjD
    dsimp only
    split_ifs with hT
    · exact h T i hi j hj hiD hjD
    · rfl
  · intro h T
    by_cases hT : KnownTo D.1 T
    · intro i hi j hj hiD hjD
      simpa only [hT, if_true] using h T i hi j hj hiD hjD
    · exact hidden T hT

/-- Computing an affine gate commutes with hiding the unknown terms. -/
theorem main_affine_known (D : C.Coalition) (a : Affine)
    (w w' : C.Term → List Bit) (publicTerm : C.Term)
    (h : ∀ T, KnownTo D.1 T → w T = w' T) (T : C.Term) (hT : KnownTo D.1 T) :
    a.share w publicTerm T = a.share w' publicTerm T := by
  simp only [Affine.share, h T hT]

/-- One layer preserves equality of the known wire lists. -/
theorem main_appendLayer_known (D : C.Coalition) (jobs : List Circuit) (l : ℕ)
    (w w' : List (C.Term → List Bit)) (z z' : Shares C Bit)
    (hlen : w.length = w'.length)
    (hw : ∀ T, KnownTo D.1 T → ∀ k, (w.getD k fun _ => []) T = (w'.getD k fun _ => []) T)
    (hz : ∀ T, KnownTo D.1 T → z T = z' T) :
    ∀ T, KnownTo D.1 T → ∀ k,
      ((appendLayer jobs l w z).getD k fun _ => []) T =
        ((appendLayer jobs l w' z').getD k fun _ => []) T := by
  intro T hT k
  rw [getD_appendLayer, getD_appendLayer, hlen]
  split_ifs
  · simp only [hw T hT k, newWires, hz T hT]
  · rfl

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

abbrev MainInput (C : Committee) := List (C.Term → List Bit)
abbrev MainMultLeak (C : Committee) := ℕ × (C.Party → Option (Shares C Bit × Shares C Bit))
abbrev MainMultReply (C : Committee) :=
  (ℕ → Bit) × Shares C Bit × (C.Party → Shares C Bit) × Finset C.Party
abbrev MainHybridLeak (C : Committee) :=
  (MainMultLeak C ⊕ MainMultLeak C) ⊕ ((C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool)
abbrev MainHybridReply (C : Committee) := (MainMultReply C ⊕ MainMultReply C) ⊕ Finset C.Party
abbrev MainAdversary (C : Committee) (E : Type) :=
  Adversary C E (MainInput C) (MainHybridLeak C) (MainHybridReply C)
abbrev MainIdealLeak (C : Committee) := (C.Party → Option (MainInput C)) × List (List Bit)

/-- The known wire lists, known tuples and errors accumulated by the simulator. -/
structure MainSimData (C : Committee) where
  wires : C.Party → MainInput C
  tuples : C.Party → List (Tuple C)
  differences : List (ℕ → Bit)

def mainRefHolder (D : C.Coalition) (T : C.Term) : C.Party :=
  Classical.choose (main_exists_honest_holder D T)

theorem mainRefHolder_spec (D : C.Coalition) (T : C.Term) :
    mainRefHolder D T ∈ C.holders T ∧ mainRefHolder D T ∉ D.1 :=
  Classical.choose_spec (main_exists_honest_holder D T)

def mainMultLeak (D : C.Coalition) (count : ℕ) (X Y : C.Party → Shares C Bit) : MainMultLeak C :=
  (count, fun i => if i ∈ D.1 then none else some (knownView D.1 count (X i), knownView D.1 count (Y i)))

/-- The terms of a multiplication that the simulator knows, including the split-copy offsets. -/
def mainKnownMult (K : Constants C E) (D : C.Coalition) (mode : ReshareMode)
    (count : ℕ) (r : MainMultReply C) : C.Party → Shares C Bit := fun i T g =>
  if KnownTo D.1 T ∧ i ∈ C.holders T ∧ g < count then
    r.2.1 T g + (if ∃ j ∈ D.1, filler K mode T g = some j then r.2.2.1 i T g else 0)
  else 0

/-- The difference is the additive attack, minus the corrupt product shares, plus the copy offsets. -/
def mainDifference (K : Constants C E) (D : C.Coalition) (mode : ReshareMode)
    (count : ℕ) (X Y : C.Party → Shares C Bit) (r : MainMultReply C) : ℕ → Bit := fun g =>
  if g < count then
    r.1 g - (∑ i ∈ Finset.univ.filter (· ∈ D.1), mulRep K (localContext i)
      (fun T => X (mainRefHolder D T) T) (fun T => Y (mainRefHolder D T) T) g) +
      ∑ T, if ∃ j ∈ D.1, filler K mode T g = some j then r.2.2.1 (mainRefHolder D T) T g else 0
  else 0

def mainAllReceive (D : C.Coalition) (receivers : Finset C.Party) : Prop :=
  ∀ i, i ∉ D.1 → i ∈ receivers

/-- One simulated multiplication layer. A partial abort prevents the next functionality call. -/
def mainSimLayer (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (l : ℕ) (st : A.State) (data : MainSimData C) :
    OracleComp (LocalSpec C) (A.State × Option (MainSimData C)) := do
  let X := fun i => layerX K jobs l (data.wires i)
  let Y := fun i => layerY K jobs l (data.wires i)
  let n := (gatesAt jobs l).length
  let (st, reply) ← A.answer st (.inl (.inl (mainMultLeak D n X Y)))
  let r := match reply with | .inl (.inl r) => r | _ => default
  if ¬ mainAllReceive D r.2.2.2 then return (st, none)
  let Z := mainKnownMult K D mode n r
  pure (st, some {
    wires := fun i => appendLayer jobs l (data.wires i) (Z i)
    tuples := fun i => data.tuples i ++ [⟨knownView D.1 n (X i), knownView D.1 n (Y i), Z i, n, mode⟩]
    differences := data.differences ++ [mainDifference K D mode n X Y r] })

def mainSimLayers (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) :
    List ℕ → A.State → MainSimData C → OracleComp (LocalSpec C) (A.State × Option (MainSimData C))
  | [], st, data => pure (st, some data)
  | l :: ls, st, data => do
    let (st, out) ← mainSimLayer K D A mode jobs l st data
    match out with
    | none => pure (st, none)
    | some data => mainSimLayers K D A mode jobs ls st data

/-- Agreement of the visible copies of the tuples. All hidden copies agree automatically. -/
def mainKnownAgree (D : C.Coalition) (views : C.Party → List (Tuple C)) : Prop :=
  ∀ (k : ℕ) (T : C.Term) (i : C.Party), i ∈ C.holders T → ∀ (j : C.Party), j ∈ C.holders T → i ∉ D.1 → j ∉ D.1 →
    ((views i)[k]?).map (fun (τ : Tuple C) => (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T))) =
      ((views j)[k]?).map (fun (τ : Tuple C) => (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T)))

/-- The common sharing of the public outputs, with a fresh mask in each non-pivot hidden term. -/
def mainRebuild (D : C.Coalition) (count : ℕ) (known : C.Party → Shares C Bit)
    (outputs : List (List Bit)) (fresh : C.Term → Fin count → Bit) : Shares C Bit :=
  mainMultSharing D
    (mainMultBase D count (fun T => known (mainRefHolder D T) T) fresh)
    (fun g => outputs.flatten.getD g 0)

/-- One list of copy hashes on the simulator's counted interface. -/
def mainCopyHashes (v : Shares C Bit) (n : ℕ) : OracleComp (LocalSpec C) (List HashOutput) :=
  C.terms.mapM fun T => liftComp (hashQuery (C := C) (.copy (vector n (v T)))) (LocalSpec C)

/-- The last network round, with the same opening and abort semantics as the real execution. -/
def mainSimOpen (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (_mode : ReshareMode) (jobs : List Circuit) (st : A.State) (receivers : Finset C.Party)
    (known : C.Party → Shares C Bit) (outputs : List (List Bit)) :
    OracleComp (LocalSpec C) (A.State × Finset C.Party) := do
  let n := (outputsOf jobs).length
  let fresh ← liftComp ($ᵗ (C.Term → Fin n → Bit)) (LocalSpec C)
  let V := mainRebuild D n known outputs fresh
  let vr := fun i T g => if i ∈ C.holders T ∧ g < n then V T g else 0
  let ds ← Concrete.sequenceFin fun i =>
    if i ∉ D.1 ∧ i ∈ receivers then mainCopyHashes (vr i) n else pure []
  if ¬ ∃ i, i ∉ D.1 ∧ i ∈ receivers then return (st, ∅)
  let (st, sent) ← A.round st fun c i =>
    if c ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers then repOutbox K i (vr i) n (ds i) c else none
  let accepts ← Concrete.sequenceFin fun i => do
    if ¬ (i ∉ D.1 ∧ i ∈ receivers) then return false
    let inbox := fun k => if k ∈ D.1 then sent k i else
      if k ∈ receivers then repOutbox K k (vr k) n (ds k) i else some .abort
    if C.parties.any (fun k => Msg.isAbort (inbox k)) then return false
    let cds ← mainCopyHashes (repCopy K i (vr i) n inbox) n
    pure (decide (repCheck K i inbox cds))
  pure (st, Finset.univ.filter fun i => accepts i)

/-- The simulator of `Rerand`, verification, and opening. -/
def mainSimTail (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (st : A.State) (data : MainSimData C)
    (outputs : List (List Bit)) : OracleComp (LocalSpec C) (A.State × Finset C.Party) := do
  let X := fun i => outputShares K jobs (data.wires i)
  let Y := fun _ : C.Party => one K
  let n := (outputsOf jobs).length
  let (st, reply) ← A.answer st (.inl (.inr (mainMultLeak D n X Y)))
  let r := match reply with | .inl (.inr r) => r | _ => default
  if ¬ mainAllReceive D r.2.2.2 then return (st, ∅)
  let Z := mainKnownMult K D .peer n r
  let tuples := fun i => data.tuples i ++ [⟨knownView D.1 n (X i), knownView D.1 n (Y i), Z i, n, .peer⟩]
  let differences := data.differences ++ [mainDifference K D .peer n X Y r]
  let agree := mainKnownAgree D tuples
  let accept := decide (agree ∧ ∀ d ∈ differences, ∀ g, d g = 0)
  let (st, reply) ← A.answer st (.inr (fun i => if i ∈ D.1 then none else some (tuples i),
    if agree then differences else [], accept))
  let receivers := match reply with | .inr rs => rs | _ => ∅
  if ¬ accept then return (st, ∅)
  mainSimOpen K D A mode jobs st receivers Z outputs

/-- GS20's simulator from the initial known terms and the public outputs. -/
def mainSimulator (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) :
    Simulator (C := C) (LocalSpec C) (MainInput C) (MainIdealLeak C) (Finset C.Party) A.State where
  State := A.State
  start := A.start
  answer st l := do
    let data : MainSimData C := ⟨fun i => (l.1 i).getD [], fun _ => [], []⟩
    let (st, out) ← mainSimLayers K D A mode jobs (List.range (depth jobs)) st data
    match out with
    | none => pure (st, ∅)
    | some data => mainSimTail K D A mode jobs st data l.2
  output := pure

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

section Bounds
variable {α β : Type}

/-- Uniform samples cost no counted queries. -/
theorem main_bound_sample (oa : ProbComp α) :
    IsQueryBoundP (liftComp oa (LocalSpec C)) Counted 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t f ih =>
    rw [liftComp_bind]
    erw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [Counted]), fun u => by simpa only [Nat.zero_sub, ite_self] using ih u⟩

theorem main_bound_bind {oa : OracleComp (LocalSpec C) α} {k : α → OracleComp (LocalSpec C) β}
    {n m : ℕ} (ha : IsQueryBoundP oa Counted n) (hk : ∀ a, IsQueryBoundP (k a) Counted m) :
    IsQueryBoundP (oa >>= k) Counted (n + m) :=
  isQueryBoundP_bind ha fun a _ => hk a

theorem main_bound_ite (p : Prop) [Decidable p] {oa ob : OracleComp (LocalSpec C) α} {n : ℕ}
    (ha : IsQueryBoundP oa Counted n) (hb : IsQueryBoundP ob Counted n) :
    IsQueryBoundP (if p then oa else ob) Counted n := by
  split <;> assumption

theorem main_bound_mapM (f : α → OracleComp (LocalSpec C) β) (n : ℕ)
    (h : ∀ a, IsQueryBoundP (f a) Counted n) :
    ∀ (xs : List α), IsQueryBoundP (xs.mapM f) Counted (xs.length * n)
  | [] => by simp
  | a :: xs => by
    simp only [List.mapM_cons, List.length_cons]
    simpa only [Nat.succ_mul, Nat.add_comm, Nat.add_zero] using
      main_bound_bind (h a) (fun b => main_bound_bind (main_bound_mapM f n h xs)
        (fun bs => isQueryBoundP_pure Counted (b :: bs) 0))

theorem main_bound_sequenceFin (k : ℕ) : ∀ {n : ℕ} (f : Fin n → OracleComp (LocalSpec C) α),
    (∀ i, IsQueryBoundP (f i) Counted k) → IsQueryBoundP (Concrete.sequenceFin f) Counted (n * k)
  | 0, f, _ => by simp [Concrete.sequenceFin]
  | n + 1, f, h => by
    simp only [Concrete.sequenceFin]
    apply IsQueryBoundP.mono (n := k + (n * k + 0)) _ (by simp [Nat.succ_mul, Nat.add_comm])
    refine main_bound_bind (h 0) fun a => ?_
    refine main_bound_bind
      (main_bound_sequenceFin k (fun i : Fin n => f i.succ) (fun i => h i.succ)) fun as => ?_
    exact isQueryBoundP_pure Counted _ 0

theorem mainCopyHashes_bound (v : Shares C Bit) (n : ℕ) :
    IsQueryBoundP (mainCopyHashes v n) Counted C.terms.length := by
  unfold mainCopyHashes
  simpa using main_bound_mapM (fun T => liftComp (hashQuery (C := C) (.copy (vector n (v T)))) (LocalSpec C))
    1 (fun T => by
      change IsQueryBoundP (query (spec := LocalSpec C) (.inr (.inl (.copy (vector n (v T)))))) Counted 1
      erw [isQueryBoundP_query_iff]
      exact fun _ => by omega) C.terms

variable (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E) (step : ℕ)
  (hanswer : ∀ st l, IsQueryBoundP (A.answer st l) Counted step)
  (hround : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step)

include hanswer in
theorem mainSimLayer_bound (mode : ReshareMode) (jobs : List Circuit) (l : ℕ) (st : A.State) (data : MainSimData C) :
    IsQueryBoundP (mainSimLayer K D A mode jobs l st data) Counted step := by
  unfold mainSimLayer
  apply IsQueryBoundP.mono (n := step + 0) _ (Nat.add_zero _).le
  refine main_bound_bind (hanswer _ _) fun r => ?_
  try dsimp only
  try simp only [pure_bind]
  exact main_bound_ite _ (isQueryBoundP_pure Counted _ 0) (isQueryBoundP_pure Counted _ 0)

include hanswer in
theorem mainSimLayers_bound (mode : ReshareMode) (jobs : List Circuit) :
    ∀ ls st data, IsQueryBoundP (mainSimLayers K D A mode jobs ls st data) Counted (ls.length * step)
  | [], st, data => by simp [mainSimLayers]
  | l :: ls, st, data => by
    unfold mainSimLayers
    apply IsQueryBoundP.mono (n := step + ls.length * step) _ (by simp [Nat.succ_mul, Nat.add_comm])
    refine main_bound_bind (mainSimLayer_bound K D A step hanswer mode jobs l st data) fun r => ?_
    rcases r with ⟨st, data | data⟩
    · exact isQueryBoundP_pure Counted _ _
    · exact mainSimLayers_bound mode jobs ls st data

set_option maxHeartbeats 2000000 in
include hround in
theorem mainSimOpen_bound (mode : ReshareMode) (jobs : List Circuit) (st : A.State)
    (receivers : Finset C.Party) (known : C.Party → Shares C Bit) (outputs : List (List Bit)) :
    IsQueryBoundP (mainSimOpen K D A mode jobs st receivers known outputs)
      Counted (step + 2 * C.n * C.terms.length) := by
  unfold mainSimOpen
  apply IsQueryBoundP.mono (n := 0 + (C.n * C.terms.length + (step + C.n * C.terms.length))) _
    (Nat.le_of_eq (by ring))
  refine main_bound_bind (n := 0) (by exact main_bound_sample _) fun fresh => ?_
  try dsimp only
  refine main_bound_bind (n := C.n * C.terms.length) (by
    refine main_bound_sequenceFin C.terms.length _ (fun i => ?_)
    exact main_bound_ite _ (mainCopyHashes_bound _ _) (isQueryBoundP_pure Counted _ _)) fun ds => ?_
  try dsimp only
  try simp only [pure_bind]
  refine main_bound_ite _ (isQueryBoundP_pure Counted _ _) ?_
  refine main_bound_bind (hround _ _) fun r => ?_
  try dsimp only
  apply IsQueryBoundP.mono (n := C.n * C.terms.length + 0) _ (Nat.add_zero _).le
  refine main_bound_bind (n := C.n * C.terms.length) (by
    refine main_bound_sequenceFin C.terms.length _ (fun i => ?_)
    try simp only [pure_bind]
    refine main_bound_ite _ (isQueryBoundP_pure Counted _ _) ?_
    refine main_bound_ite _ (isQueryBoundP_pure Counted _ _) ?_
    apply IsQueryBoundP.mono (n := C.terms.length + 0) _ (Nat.add_zero _).le
    exact main_bound_bind (mainCopyHashes_bound _ _) (fun _ => isQueryBoundP_pure Counted _ 0))
    (fun accepts => isQueryBoundP_pure Counted _ 0)

set_option maxHeartbeats 2000000 in
include hanswer hround in
theorem mainSimTail_bound (mode : ReshareMode) (jobs : List Circuit) (st : A.State)
    (data : MainSimData C) (outputs : List (List Bit)) :
    IsQueryBoundP (mainSimTail K D A mode jobs st data outputs)
      Counted (3 * step + 2 * C.n * C.terms.length) := by
  unfold mainSimTail
  apply IsQueryBoundP.mono (n := step + (step + (step + 2 * C.n * C.terms.length))) _ (by omega)
  refine main_bound_bind (hanswer _ _) fun r => ?_
  try dsimp only
  try simp only [pure_bind]
  refine main_bound_ite _ (isQueryBoundP_pure Counted _ _) ?_
  refine main_bound_bind (hanswer _ _) fun r' => ?_
  try dsimp only
  try simp only [pure_bind]
  exact main_bound_ite _ (isQueryBoundP_pure Counted _ _)
    (mainSimOpen_bound K D A step hround mode jobs _ _ _ _)

include hanswer hround in
theorem mainSimulator_answer_bound (mode : ReshareMode) (jobs : List Circuit)
    (st : A.State) (l : MainIdealLeak C) :
    IsQueryBoundP ((mainSimulator K D A mode jobs).answer st l)
      Counted ((depth jobs + 3) * step + 2 * C.n * C.n.choose (C.t - 1)) := by
  have hterms : C.terms.length = C.n.choose (C.t - 1) := by
    simp only [Committee.terms, Finset.length_toList, Finset.card_univ]
    simpa using Fintype.card_finset_len (α := C.Party) (C.t - 1)
  unfold mainSimulator
  apply IsQueryBoundP.mono (n := (List.range (depth jobs)).length * step +
    (3 * step + 2 * C.n * C.terms.length)) _ (by rw [hterms]; simp [Nat.add_mul, Nat.add_assoc])
  refine main_bound_bind (mainSimLayers_bound K D A step hanswer mode jobs _ _ _) fun r => ?_
  rcases r with ⟨st, data | data⟩
  · exact isQueryBoundP_pure Counted _ _
  · exact mainSimTail_bound K D A step hanswer hround mode jobs _ data l.2

end Bounds
end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

theorem main_hasHashQueryBound (prims : Primitives) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (n : ℕ) (h : IsQueryBoundP oa Counted n) :
    HasHashQueryBound (runWorld prims (worldRoles.adversary oa)) n := by
  intro r hr
  unfold runWorld at hr
  rw [StateT.run'_eq] at hr
  erw [support_map] at hr
  obtain ⟨r', hr', rfl⟩ := hr
  exact cost_counted prims oa n h ∅ r' hr'

/-- The unique leak made by `F_main` on the supplied inputs. -/
def mainIdealLeak (D : C.Coalition) (jobs : List Circuit) (x : C.Party → MainInput C) : MainIdealLeak C :=
  let inputs := fun i => if i ∈ D.1 then none else some (x i)
  let input := fun k => reconstruct fun i => (inputs i).bind (·[k]?)
  (fun i => if i ∈ D.1 then none else
      (inputs i).map fun views => views.map fun v T => if KnownTo D.1 T then v T else [],
    jobs.zipIdx.map fun (job, k) => job.eval (inputValue (input k)))

def mainIdealLocal (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (x : C.Party → MainInput C) (z : Aux) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (List (List Bit)))) := do
  let st ← A.start (corruptInputs D x) z
  let ans ← (mainSimulator K D A mode jobs).answer st (mainIdealLeak D jobs x)
  pure (ans.1, fun i => if i ∉ D.1 ∧ i ∈ ans.2 then some (mainIdealLeak D jobs x).2 else none)

theorem main_worldRoles_bind {α β : Type} (oa : OracleComp (LocalSpec C) α)
    (f : α → OracleComp (LocalSpec C) β) :
    worldRoles.adversary (oa >>= f) = worldRoles.adversary oa >>= fun a => worldRoles.adversary (f a) := by
  simp only [worldRoles, liftComp_bind, counted_bind]

theorem main_worldRoles_pure {α : Type} (a : α) :
    worldRoles.adversary (C := C) (pure a : OracleComp (LocalSpec C) α) = pure a := rfl

theorem mainIdealLocal_eq (K : Constants C E) (D : C.Coalition) (A : MainAdversary C E)
    (mode : ReshareMode) (jobs : List Circuit) (x : C.Party → MainInput C) (z : Aux) :
    idealExecution worldRoles.adversary D (Fmain jobs) (mainSimulator K D A mode jobs) x z =
      worldRoles.adversary (mainIdealLocal K D A mode jobs x z) := by
  have hs : (mainSimulator K D A mode jobs).start = A.start := rfl
  have ho : (mainSimulator K D A mode jobs).output = pure := rfl
  simp only [idealExecution, Fmain, leak, simulateQ_bind, simulateQ_query, simulateQ_pure,
    OracleQuery.input_query, OracleQuery.cont_query, mainIdealLocal, main_worldRoles_bind]
  dsimp only [HAdd.hAdd, QueryImpl.add]
  simp only [StateT.run_map, StateT.run_bind, StateT.run_pure, StateT.run_mk,
    bind_assoc, pure_bind, hs, ho, main_worldRoles_pure, id_map]
  simp only [StateT.run, StateT.mk, bind_map_left, bind_assoc, pure_bind, main_worldRoles_pure]
  refine bind_congr fun st => ?_
  change ((worldRoles.adversary ((mainSimulator K D A mode jobs).answer st (mainIdealLeak D jobs x)) >>=
      fun a => pure (a.2, a.1)) >>= fun a => (do
        let b ← worldRoles.adversary (pure a.2 : OracleComp (LocalSpec C) A.State)
        pure (b, fun i => if i ∉ D.1 ∧ i ∈ a.1 then some (mainIdealLeak D jobs x).2 else none))) = _
  rw [bind_assoc]
  refine bind_congr fun a => ?_
  simp only [pure_bind, main_worldRoles_pure]

/-- The concrete simulator meets the exact overhead in `MainStatement`. -/
theorem mainSimulator_queryBound (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : MainAdversary C E) (mode : ReshareMode) (jobs : List Circuit)
    (x : C.Party → MainInput C) (z : Aux) (Z : Distinguisher C A.State (List (List Bit)))
    (q : ℕ) (hq : IsQueryBounded A Z (depth jobs + 3) q) :
    HasHashQueryBound (runWorld prims (distinguish
      (idealExecution worldRoles.adversary D (Fmain jobs) (mainSimulator K D A mode jobs) x z) Z))
      (q + 2 * C.n * C.n.choose (C.t - 1)) := by
  obtain ⟨start, step, final, hq, hstart, hround, hanswer, hZ⟩ := hq
  rw [mainIdealLocal_eq, distinguish, ← main_worldRoles_bind]
  apply main_hasHashQueryBound
  apply IsQueryBoundP.mono (n := (start + ((depth jobs + 3) * step +
      2 * C.n * C.n.choose (C.t - 1))) + final) _ (by omega)
  refine main_bound_bind (n := start + ((depth jobs + 3) * step +
      2 * C.n * C.n.choose (C.t - 1))) (by
    unfold mainIdealLocal
    refine main_bound_bind (hstart _ _) fun st => ?_
    apply IsQueryBoundP.mono (n := ((depth jobs + 3) * step +
      2 * C.n * C.n.choose (C.t - 1)) + 0) _ (Nat.add_zero _).le
    exact main_bound_bind
      (mainSimulator_answer_bound K D A step hanswer hround mode jobs st _)
      (fun ans => isQueryBoundP_pure Counted _ 0)) hZ

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- The pivot exists for every allowed coalition. -/
theorem main_lacked_exists (D : C.Coalition) : ∃ T : C.Term, lackedTerm D.1 = some T := by
  obtain ⟨T, hDT, hT⟩ := Finset.exists_superset_card_eq D.2
    (by simp [Committee.n]; have := C.one_le_t; omega)
  have hunknown : ¬ KnownTo D.1 (⟨T, hT⟩ : C.Term) := by
    rintro ⟨j, hj, hh⟩
    have hmem := hDT hj
    simpa [Committee.holders, hmem] using hh
  have hsome : (lackedTerm D.1).isSome := by
    rw [lackedTerm, List.find?_isSome]
    exact ⟨⟨T, hT⟩, mem_terms _, by simpa using hunknown⟩
  exact Option.isSome_iff_exists.mp hsome

/-- Taking the known part of a multiplication output gives the simulator's copy. -/
theorem mainKnownMult_matches (K : Constants C E) (D : C.Coalition) (mode : ReshareMode)
    (count : ℕ) (r : MainMultReply C) (fresh : C.Term → Fin count → Bit) (target : ℕ → Bit)
    (i : C.Party) :
    knownView D.1 count (fun T g =>
      if i ∈ C.holders T ∧ g < count then
        mainMultSharing D (mainMultBase D count r.2.1 fresh) target T g +
          (if ∃ j ∈ D.1, filler K mode T g = some j then r.2.2.1 i T g else 0)
      else 0) = mainKnownMult K D mode count r i := by
  funext T g
  by_cases hT : KnownTo D.1 T
  · simp only [knownView, hT, true_and]
    rw [mainMultSharing_known D _ target T hT]
    simp only [knownView, mainMultBase, mainKnownMult, hT, true_and, if_true]
    split_ifs <;> simp_all
  · simp [knownView, mainKnownMult, hT]

/-- Unknown copies cannot be split by an offset. -/
theorem main_unknown_offset_zero (K : Constants C E) (D : C.Coalition) (mode : ReshareMode)
    (T : C.Term) (hT : ¬ KnownTo D.1 T) (g : ℕ) (offset : C.Party → Shares C Bit) (i : C.Party) :
    (if ∃ j ∈ D.1, filler K mode T g = some j then offset i T g else 0) = 0 := by
  exact if_neg (fun h => hT (main_filler_known K D mode T g h))

/-- When the copies agree, the simulator computes exactly the difference leaked by verification. -/
theorem mainDifference_correct (K : Constants C E) (D : C.Coalition) (mode : ReshareMode)
    (count : ℕ) (X Y Xs Ys : C.Party → Shares C Bit) (x y : Shares C Bit)
    (hx : ∀ i T, i ∉ D.1 → i ∈ C.holders T → X i T = x T)
    (hy : ∀ i T, i ∉ D.1 → i ∈ C.holders T → Y i T = y T)
    (hxs : ∀ i T, i ∉ D.1 → KnownTo D.1 T → i ∈ C.holders T →
      ∀ g < count, Xs i T g = X i T g)
    (hys : ∀ i T, i ∉ D.1 → KnownTo D.1 T → i ∈ C.holders T →
      ∀ g < count, Ys i T g = Y i T g)
    (r : MainMultReply C) (base : Shares C Bit) (g : ℕ) (hg : g < count) :
    shareValue (fun T g =>
      mainMultSharing D base
          (fun g => (∑ i ∈ Finset.univ.filter (· ∉ D.1), mulRep K (localContext i) (X i) (Y i) g) + r.1 g) T g +
        (if ∃ j ∈ D.1, filler K mode T g = some j then r.2.2.1 (mainRefHolder D T) T g else 0)) g -
        shareValue x g * shareValue y g = mainDifference K D mode count Xs Ys r g := by
  obtain ⟨T₀, hT₀⟩ := main_lacked_exists D
  have hhonest : (∑ i ∈ Finset.univ.filter (· ∉ D.1), mulRep K (localContext i) (X i) (Y i) g) =
      ∑ i ∈ Finset.univ.filter (· ∉ D.1), mulRep K (localContext i) x y g := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [main_mulRep_views K D X Y x y hx hy i (Finset.mem_filter.mp hi).2]
  have hcorrupt : (∑ i ∈ Finset.univ.filter (· ∈ D.1), mulRep K (localContext i)
      (fun T => Xs (mainRefHolder D T) T) (fun T => Ys (mainRefHolder D T) T) g) =
      ∑ i ∈ Finset.univ.filter (· ∈ D.1), mulRep K (localContext i) x y g := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiD := (Finset.mem_filter.mp hi).2
    unfold mulRep
    refine Finset.sum_congr rfl fun AB hAB => ?_
    obtain ⟨hA, hB⟩ := K.pairs_held i AB hAB
    have hknownA : KnownTo D.1 AB.1 := ⟨i, hiD, hA⟩
    have hknownB : KnownTo D.1 AB.2 := ⟨i, hiD, hB⟩
    have ha := mainRefHolder_spec D AB.1
    have hb := mainRefHolder_spec D AB.2
    dsimp only
    rw [hxs _ _ ha.2 hknownA ha.1 g hg, hys _ _ hb.2 hknownB hb.1 g hg,
      hx _ _ ha.2 ha.1, hy _ _ hb.2 hb.1]
  rw [mainDifference, if_pos hg, hcorrupt]
  simp only [shareValue, Finset.sum_add_distrib]
  rw [show (∑ T, mainMultSharing D base
      (fun g => (∑ i ∈ Finset.univ.filter (· ∉ D.1), mulRep K (localContext i) (X i) (Y i) g) + r.1 g) T g) =
        (∑ i ∈ Finset.univ.filter (· ∉ D.1), mulRep K (localContext i) (X i) (Y i) g) + r.1 g from
      mainMultSharing_sum D _ _ T₀ hT₀ g, hhonest]
  have hsum := main_mulRep_honest_add_corrupt K D x y g
  simp only [shareValue] at hsum
  rw [← hsum]
  ring

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- The copy-domain event is included in the usual ROM cache-collision event. -/
theorem mainCopyCollision_implies_cacheCollision (s : HashCache C) :
    MainCopyCollision s → CacheHasCollision s := by
  rintro ⟨a, b, u, hab, ha, hb⟩
  exact ⟨.copy a, .copy b, u, u, fun h => hab (Query.copy.inj h), ha, hb, HEq.rfl⟩

/-- A finite set of queried inputs covers a cache. -/
def MainCacheBound (s : HashCache C) (k : ℕ) : Prop :=
  ∃ S : Finset (Query C), S.card ≤ k ∧ ∀ q, s q ≠ none → q ∈ S

theorem mainCacheBound_mono {s : HashCache C} {k k' : ℕ} (h : MainCacheBound s k) (hk : k ≤ k') :
    MainCacheBound s k' := by
  obtain ⟨S, hS, hm⟩ := h
  exact ⟨S, hS.trans hk, hm⟩

theorem mainCacheBound_insert {s : HashCache C} {k : ℕ} (h : MainCacheBound s k) (q : Query C) (u : HashOutput) :
    MainCacheBound (s.cacheQuery q u) (k + 1) := by
  obtain ⟨S, hS, hm⟩ := h
  refine ⟨insert q S, (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hS 1), fun q' hq' => ?_⟩
  by_cases hq : q' = q
  · simpa only [hq] using Finset.mem_insert_self q S
  · rw [QueryCache.cacheQuery_of_ne s _ hq] at hq'
    exact Finset.mem_insert_of_mem (hm q' hq')

/-- A collision caused by one new answer matches an answer already in the cache. -/
theorem main_cache_collision_insert (s : HashCache C) (hs : ¬ CacheHasCollision s)
    (q : Query C) (u : HashOutput) (h : CacheHasCollision (s.cacheQuery q u)) :
    ∃ q', q' ≠ q ∧ s q' = some u := by
  obtain ⟨q₁, q₂, u₁, u₂, hne, h₁, h₂, heq⟩ := h
  have huu : u₁ = u₂ := eq_of_heq heq
  subst u₂
  by_cases hq₁ : q₁ = q
  · subst q₁
    rw [QueryCache.cacheQuery_self, Option.some.injEq] at h₁
    subst u₁
    exact ⟨q₂, hne.symm, by rwa [QueryCache.cacheQuery_of_ne s _ hne.symm] at h₂⟩
  · by_cases hq₂ : q₂ = q
    · subst q₂
      rw [QueryCache.cacheQuery_self, Option.some.injEq] at h₂
      subst u₁
      exact ⟨q₁, hne, by rwa [QueryCache.cacheQuery_of_ne s _ hq₁] at h₁⟩
    · exact (hs ⟨q₁, q₂, u₁, u₁, hne,
        by rwa [QueryCache.cacheQuery_of_ne s _ hq₁] at h₁,
        by rwa [QueryCache.cacheQuery_of_ne s _ hq₂] at h₂, HEq.rfl⟩).elim

/-- The standard per-query birthday charge, specialized to the model's 256-bit cache. -/
theorem main_cache_fresh_collision_bound (s : HashCache C) (hs : ¬ CacheHasCollision s)
    (k : ℕ) (hb : MainCacheBound s k) (q : Query C) :
    Pr[fun u => CacheHasCollision (s.cacheQuery q u) | $ᵗ HashOutput] ≤
      (k : ℝ≥0∞) / Fintype.card HashOutput := by
  obtain ⟨S, hS, hm⟩ := hb
  have hbad : (Finset.univ.filter fun u : HashOutput => CacheHasCollision (s.cacheQuery q u)).card ≤ S.card := by
    let f : HashOutput → Query C := fun u =>
      if h : CacheHasCollision (s.cacheQuery q u) then (main_cache_collision_insert s hs q u h).choose else q
    refine Finset.card_le_card_of_injOn f (fun u hu => ?_) (fun u hu v hv heq => ?_)
    · have hc := (Finset.mem_filter.mp hu).2
      rw [show f u = _ from dif_pos hc]
      apply hm
      rw [(main_cache_collision_insert s hs q u hc).choose_spec.2]
      exact Option.some_ne_none u
    · have hc := (Finset.mem_filter.mp hu).2
      have hd := (Finset.mem_filter.mp hv).2
      rw [show f u = _ from dif_pos hc, show f v = _ from dif_pos hd] at heq
      have h₁ := (main_cache_collision_insert s hs q u hc).choose_spec.2
      have h₂ := (main_cache_collision_insert s hs q v hd).choose_spec.2
      rw [heq, h₂] at h₁
      exact (Option.some.inj h₁).symm
  rw [probEvent_uniformSample]
  exact ENNReal.div_le_div_right (by exact_mod_cast hbad.trans hS) _

/-- One ROM lookup followed by a continuation; cached lookups are harmless. -/
theorem main_birthday_hash_step {α : Type} (s : HashCache C) (hs : ¬ CacheHasCollision s)
    (k : ℕ) (hb : MainCacheBound s k) (q : Query C)
    (f : HashOutput → HashCache C → ProbComp (α × HashCache C)) (ε : ℝ≥0∞)
    (hf : ∀ u s', ¬ CacheHasCollision s' → MainCacheBound s' (k + 1) →
      Pr[fun z => CacheHasCollision z.2 | f u s'] ≤ ε) :
    Pr[fun z => CacheHasCollision z.2 |
      ((Query C →ₒ HashOutput).randomOracle q).run s >>= fun r => f r.1 r.2] ≤
        (k : ℝ≥0∞) / Fintype.card HashOutput + ε := by
  cases hsq : s q with
  | some u =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hsq, pure_bind]
    exact (hf u s hs (mainCacheBound_mono hb (Nat.le_succ k))).trans (le_add_self)
  | none =>
    have heq : ((Query C →ₒ HashOutput).randomOracle q).run s =
        (fun u => (u, s.cacheQuery q u)) <$> ($ᵗ HashOutput) := by
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hsq]
      rfl
    rw [heq, bind_map_left]
    have h := probEvent_bind_le_add
      (mx := ($ᵗ HashOutput)) (my := fun u => f u (s.cacheQuery q u))
      (p := fun u => ¬ CacheHasCollision (s.cacheQuery q u)) (q := fun z => ¬ CacheHasCollision z.2)
      (ε₁ := (k : ℝ≥0∞) / Fintype.card HashOutput) (ε₂ := ε)
      (by simpa only [not_not] using main_cache_fresh_collision_bound s hs k hb q)
      (by intro u _ hu; simpa only [not_not] using hf u _ hu (mainCacheBound_insert hb q u))
    simpa only [not_not] using h

private theorem main_birthday_arith (n k : ℕ) (hn : 0 < n) (M : ℝ≥0∞) :
    (k : ℝ≥0∞) / M + (((n - 1) * (k + 1 + (n - 1)) : ℕ) : ℝ≥0∞) / M ≤
      ((n * (k + n) : ℕ) : ℝ≥0∞) / M := by
  rw [← ENNReal.add_div]
  apply ENNReal.div_le_div_right
  norm_cast
  have hn' : n - 1 + 1 = n := by omega
  have he : k + 1 + (n - 1) = k + n := by omega
  rw [he]
  nlinarith

/-- A counted local computation has the usual birthday bound, with private samples free. -/
theorem main_local_birthday (prims : Primitives) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (n k : ℕ) (h : IsQueryBoundP oa Counted n)
    (s : HashCache C) (hs : ¬ CacheHasCollision s) (hb : MainCacheBound s k) :
    Pr[fun z => CacheHasCollision z.2 | (simulateQ (localAnswer prims) oa).run s] ≤
      ((n * (k + n) : ℕ) : ℝ≥0∞) / Fintype.card HashOutput := by
  induction oa using OracleComp.inductionOn generalizing n k s with
  | pure a => simp [hs]
  | query_bind t f ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rcases t with t | (q | x)
    · have heq : (localAnswer (C := C) prims (.inl t)).run s =
          (fun u => (u, s)) <$> (OracleComp.lift (OracleSpec.query (spec := unifSpec) t)) := by
        simp [localAnswer, unifFwdImpl]
      change Pr[fun z => CacheHasCollision z.2 |
        (localAnswer prims (.inl t)).run s >>= fun r => (simulateQ (localAnswer prims) (f r.1)).run r.2] ≤ _
      rw [heq]
      erw [bind_map_left]
      refine probEvent_bind_le_of_forall_le fun u _ => ?_
      exact ih u n k (by simpa [Counted] using h.2 u) s hs hb
    · change Pr[fun z => CacheHasCollision z.2 |
        (hashAnswer prims q).run s >>= fun r => (simulateQ (localAnswer prims) (f r.1)).run r.2] ≤ _
      by_cases hfixed : IsFixed q
      · obtain ⟨input, rfl, hinput⟩ := hfixed
        rw [hashAnswer_of_isFixed prims hinput, StateT.run_pure, pure_bind]
        exact ih _ n k (by simpa [Counted, hinput] using h.2 (prims.Th input)) s hs hb
      · have hc : Counted (C := C) (.inr (.inl q)) := by
          cases q <;> simp_all [Counted, IsFixed]
        have hn : 0 < n := h.1.resolve_left (not_not.mpr hc)
        rw [hashAnswer_of_not_isFixed prims hfixed]
        refine (main_birthday_hash_step s hs k hb q _ _ (fun u s' hs' hb' =>
          ih u (n - 1) (k + 1) (by simpa only [if_pos hc] using h.2 u) s' hs' hb')).trans ?_
        exact main_birthday_arith n k hn _
    · change Pr[fun z => CacheHasCollision z.2 |
        (prgAnswer prims x).run s >>= fun r => (simulateQ (localAnswer prims) (f r.1)).run r.2] ≤ _
      simp only [prgAnswer, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, hashAnswer]
      have hc : Counted (C := C) (.inr (.inr x)) := trivial
      have hn : 0 < n := h.1.resolve_left (not_not.mpr hc)
      refine (main_birthday_hash_step s hs k hb (.streamKey x.2.1)
        (fun u s' => (simulateQ (localAnswer prims) (f (prims.aes.eval (truncateHash u) x.2.2))).run s')
        _ (fun u s' hs' hb' => ih _ (n - 1) (k + 1)
          (by simpa only [if_pos hc] using h.2 (prims.aes.eval (truncateHash u) x.2.2)) s' hs' hb')).trans ?_
      exact main_birthday_arith n k hn _

/-- The exact copy-collision error used in `MainStatement`. -/
theorem main_copy_birthday (prims : Primitives) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (n : ℕ) (h : IsQueryBoundP oa Counted n) :
    (Pr[fun z => MainCopyCollision z.2 | (simulateQ (localAnswer prims) oa).run ∅]).toReal ≤
      ((n ^ 2 : ℕ) : ℝ) / 2 ^ 256 := by
  have h0 : ¬ CacheHasCollision (∅ : HashCache C) := by
    rintro ⟨q₁, q₂, u₁, u₂, hne, h₁, h₂, heq⟩
    simpa using h₁
  have hb : MainCacheBound (∅ : HashCache C) 0 := ⟨∅, by simp, by simp⟩
  have hh := (probEvent_mono (fun z _ hz => mainCopyCollision_implies_cacheCollision z.2 hz)).trans
    (main_local_birthday prims oa n 0 h ∅ h0 hb)
  have hcard : Fintype.card HashOutput = 2 ^ 256 := by
    exact card_bitVec 256
  simp only [zero_add, ← pow_two, hcard] at hh
  have ht : (((n ^ 2 : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞)) ≠ ⊤ := by
    exact ENNReal.div_ne_top (by simp) (by
      exact_mod_cast (pow_ne_zero 256 (by decide : (2 : ℕ) ≠ 0)))
  have hr := ENNReal.toReal_mono ht hh
  norm_num at hr ⊢
  exact hr

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- The distance half of `MainStatement` for `mainSimulator`. -/
def MainSecurityDistance (prims : Primitives) (K : Constants C E) : Prop :=
  ∀ (mode : ReshareMode) (jobs : List Circuit) (D : C.Coalition) (A : MainAdversary C E)
    (x : C.Party → MainInput C) (z : Aux) (Z : Distinguisher C A.State (List (List Bit))) (q : ℕ),
    MainInputs jobs D x → IsQueryBounded A Z (mainRounds jobs) q →
    |accepts prims (distinguish (realExecution D A (mainFunctionalities K mode)
        (mainRounds jobs) (mainProtocol K mode jobs) x z) Z) -
      accepts prims (distinguish (idealExecution worldRoles.adversary D (Fmain jobs)
        (mainSimulator K D A mode jobs) x z) Z)| ≤ copyHashError C q

/-- `MainStatement` from its distance half. The query half is `mainSimulator_queryBound`. -/
theorem mainStatement_of_simulator_distance (prims : Primitives) (K : Constants C E)
    (h : MainSecurityDistance prims K) : MainStatement prims K := by
  intro mode jobs D A
  refine ⟨mainSimulator K D A mode jobs, ?_⟩
  intro x z Z q hx hq
  exact ⟨mainSimulator_queryBound prims K D A mode jobs x z Z q hq,
    h mode jobs D A x z Z q hx hq⟩

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

end ThresholdLeanXmssSecurity
