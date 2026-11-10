import ThresholdLeanXmssSecurity.Proof.Tree
import ThresholdLeanXmssSecurity.Proof.Signing

/-!
# The dealer of `F_tree`

`DealerTreeStatement` and `TreeSuccessStatement`. When the circuits compute `Th`, the dealer of
`F_tree` evaluates each job as `referenceJob` does, because the inputs of `Th` that the MPC
evaluates are fixed and never cached. The batches keep the order of the jobs. So the dealer and
`referenceTree` give the same tree and the same cache, and the success bound follows from the
randomizer search of the bottom tree.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section DealerProof

variable {C : Committee} (prims : Primitives) (circuits : Circuits) (settings : Settings)

/-! ## The log of the dealer -/

/-- Forgetting the log of a `WriterT` is a monad map. -/
def dropLog {ω : Type} {n : Type → Type} [Monad n] [LawfulMonad n] [EmptyCollection ω] [Append ω] :
    WriterT ω n →ᵐ n where
  toFun _ x := Prod.fst <$> x.run
  toFun_pure' x := WriterT.fst_map_run_pure' x
  toFun_bind' x f := WriterT.fst_map_run_bind' x f

theorem dropLog_liftM {ω : Type} {n : Type → Type} [Monad n] [LawfulMonad n] [EmptyCollection ω] [Append ω]
    {α : Type} (x : n α) : (dropLog (ω := ω)).toFun α (liftM x) = x := by
  change Prod.fst <$> ((fun a => (a, (∅ : ω))) <$> x) = x
  simp

theorem dropLog_tell {n : Type → Type} [Monad n] [LawfulMonad n] {β : Type} (w : List β) :
    (dropLog (ω := List β) (n := n)).toFun PUnit (tell w) = pure PUnit.unit := by
  change Prod.fst <$> (pure (PUnit.unit, w) : n (PUnit × List β)) = _
  simp

/-! ## The batches keep the order of the jobs -/

theorem mapM_map_out {n : Type → Type} [Monad n] [LawfulMonad n] {α β γ : Type} (g : β → γ)
    (f : α → n β) : ∀ l : List α, l.mapM (fun a => g <$> f a) = List.map g <$> l.mapM f
  | [] => by simp
  | a :: l => by simp [List.mapM_cons, mapM_map_out g f l]

theorem mapM_flatten {n : Type → Type} [Monad n] [LawfulMonad n] {α β : Type} (f : α → n β) :
    ∀ L : List (List α), L.flatten.mapM f = List.flatten <$> L.mapM (fun c => c.mapM f)
  | [] => by simp
  | c :: L => by
    rw [List.flatten_cons, List.mapM_append, mapM_flatten f L, List.mapM_cons]
    simp [map_bind]

/-- A run in batches of a positive size is the run of all jobs. -/
theorem batched_some {n : Type → Type} [Monad n] [LawfulMonad n] (size : ℕ) (hsize : 0 < size)
    (f : Job → n (List Bit)) (jobs : List Job) :
    batched size (fun js => some <$> js.mapM f) jobs = some <$> jobs.mapM f := by
  unfold batched
  rw [mapM_map_out, ← chunks_flatten size hsize jobs, mapM_flatten, chunks_flatten size hsize jobs]
  simp only [bind_map_left, Functor.map_map]
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun a => ?_
  have := foldlM_some_append a []
  rw [List.nil_append] at this
  exact congrArg pure this

/-- With its log dropped, the dealer runs `ceremonyOutput` with all jobs of a run at once. -/
theorem fst_dealerCeremony (hsize : 0 < settings.batchSize) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree) :
    Prod.fst <$> dealerCeremony circuits settings parameter seeds top tree =
      ceremonyOutput tweakable parameter (fun js => some <$> js.mapM (evalJob circuits parameter seeds)) top tree := by
  unfold dealerCeremony
  change dropLog _ = _
  rw [monadHom_ceremonyOutput]
  congr 1
  · funext β oa
    show Prod.fst <$> (liftM (tweakable oa) : WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) β).run = _
    exact dropLog_liftM _
  · funext js
    rw [monadHom_batched, ← batched_some settings.batchSize hsize]
    congr 1
    funext js'
    simp only [MonadHom.toFun_bind', MonadHom.toFun_pure', dropLog_liftM, dropLog_tell, pure_bind]
    rw [map_eq_bind_pure_comp]
    rfl

/-! ## The inputs of `Th` that the MPC evaluates are not cached -/

/-- A run that leaves the cache as it is and gives `a`. -/
def FixedR {α : Type} (ob : OracleComp (RoSpec C) α) (a : α) : Prop :=
  ∀ s, roRun prims ob s = pure (a, s)

variable {prims}

theorem FixedR.pure {α : Type} (a : α) : FixedR prims (pure a : OracleComp (RoSpec C) α) a :=
  fun s => roRun_pure prims a s

theorem FixedR.bind {α β : Type} {ob : OracleComp (RoSpec C) α} {f : α → OracleComp (RoSpec C) β} {a : α}
    {b : β} (h1 : FixedR prims ob a) (h2 : FixedR prims (f a) b) : FixedR prims (ob >>= f) b := fun s => by
  rw [roRun_bind, h1, pure_bind, h2]

theorem FixedR.map {α β : Type} {ob : OracleComp (RoSpec C) α} {a : α} (g : α → β) (h : FixedR prims ob a) :
    FixedR prims (g <$> ob) (g a) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind (FixedR.pure _)

theorem FixedR.oracleHash {x : HashInput} (hx : MpcInput x) :
    FixedR prims (tweakable (C := C) (Concrete.oracleHash x)) (prims.Th x) := fun s => by
  rw [tweakable_oracleHash, roRun_hashQuery]
  simp [hashAnswer, hx]

theorem evalTh_bind {α β : Type} (Th : HashInput → HashOutput) (oa : OracleComp HashSpec α)
    (f : α → OracleComp HashSpec β) : evalTh Th (oa >>= f) = evalTh Th (f (evalTh Th oa)) := by
  simp [evalTh, simulateQ_bind]
  rfl

theorem evalTh_pure {α : Type} (Th : HashInput → HashOutput) (a : α) :
    evalTh Th (pure a : OracleComp HashSpec α) = a := by
  simp [evalTh]
  rfl

/-- A leanVM computation that makes only calls of `Th` that the MPC evaluates. -/
def FixedTh {α : Type} (prims : Primitives) (oa : OracleComp HashSpec α) : Prop :=
  FixedR prims (tweakable (C := C) oa) (evalTh prims.Th oa)

theorem FixedTh.pure {α : Type} (a : α) : FixedTh (C := C) prims (pure a : OracleComp HashSpec α) := by
  unfold FixedTh
  rw [tweakable_pure, evalTh_pure]
  exact FixedR.pure a

theorem FixedTh.bind {α β : Type} {oa : OracleComp HashSpec α} {f : α → OracleComp HashSpec β}
    (h1 : FixedTh (C := C) prims oa) (h2 : ∀ a, FixedTh (C := C) prims (f a)) :
    FixedTh (C := C) prims (oa >>= f) := by
  unfold FixedTh
  rw [tweakable_bind, evalTh_bind]
  exact FixedR.bind h1 (h2 _)

theorem FixedTh.oracleHash {x : HashInput} (hx : MpcInput x) :
    FixedTh (C := C) prims (Concrete.oracleHash x : OracleComp HashSpec HashOutput) := by
  unfold FixedTh
  have : evalTh prims.Th (Concrete.oracleHash x : OracleComp HashSpec HashOutput) = prims.Th x := by
    simp [evalTh, Concrete.oracleHash]
    rfl
  rw [this]
  exact FixedR.oracleHash hx

theorem FixedTh.chainWalk (P : PublicParameter) (lay : Layer) (key : KeyIndex) (l : ChainIndex) (s : ℕ) :
    ∀ n v, FixedTh (C := C) prims (Concrete.chainWalk P lay key l s n v : OracleComp HashSpec Digest)
  | 0, v => by rw [Concrete.chainWalk]; exact FixedTh.pure v
  | n + 1, v => by
    rw [Concrete.chainWalk]
    refine FixedTh.bind (FixedTh.chainWalk P lay key l s n v) fun w => ?_
    split
    · unfold Concrete.tweakableHash
      exact FixedTh.bind (FixedTh.oracleHash (Or.inl ⟨_, _, _, _, _, _, rfl⟩)) fun _ => FixedTh.pure _
    · exact FixedTh.pure _

theorem FixedTh.commitment (P : PublicParameter) (e : KeyIndex) (ρ : Digest) :
    FixedTh (C := C) prims (Concrete.oracleHash (commitmentInput P e ρ) : OracleComp HashSpec HashOutput) :=
  FixedTh.oracleHash (Or.inr ⟨_, _, _, rfl⟩)

/-! ## One job -/

/-- `referenceJob` after the PRF values of its points. -/
def refCore {m : Type → Type} [Monad m] (lift : ∀ {α : Type}, OracleComp HashSpec α → m α)
    (parameter : PublicParameter) (kind : JobKind) (values : List Digest) : m (List Bit) :=
  let value := fun k => values.getD k 0
  match kind with
  | .chainEnd e l => bitsOfDigest <$> lift (Concrete.chainWalk parameter topLayer e l 0 3 (value 0))
  | .chainRow e l => do
      let y₁ ← lift (Concrete.chainWalk parameter bottomLayer e l 0 1 (value 0))
      let y₂ ← lift (Concrete.chainWalk parameter bottomLayer e l 0 2 (value 0))
      let y₃ ← lift (Concrete.chainWalk parameter bottomLayer e l 0 3 (value 0))
      pure (bitsOfDigest (y₁ ^^^ value 1) ++ bitsOfDigest (y₂ ^^^ value 2) ++ bitsOfDigest y₃)
  | .chainValue e l p => bitsOfDigest <$> lift (Concrete.chainWalk parameter topLayer e l 0 p.val (value 0))
  | .commitment e => (bitsOfDigest ∘ truncateHash) <$> lift (Concrete.oracleHash (commitmentInput parameter e (value 0)))
  | .randomizer => pure (bitsOfDigest (value 0))

theorem referenceJob_eq {m : Type → Type} [Monad m] (lift : ∀ {α : Type}, OracleComp HashSpec α → m α)
    (F : Point → m Digest) (parameter : PublicParameter) (job : Job) :
    referenceJob lift F parameter job = job.points.mapM F >>= refCore lift parameter job.kind := by
  unfold referenceJob refCore
  rfl

theorem referenceJob_id (Th : HashInput → HashOutput) (F : Point → Digest) (parameter : PublicParameter) (job : Job) :
    referenceJob (m := Id) (fun oa => evalTh Th oa) F parameter job =
      refCore (m := Id) (fun oa => evalTh Th oa) parameter job.kind (job.points.map F) := by
  rw [referenceJob_eq, id_mapM]
  rfl

/-- The calls of `Th` of a job are fixed, so the job leaves the cache as it is. -/
theorem fixedR_refCore (parameter : PublicParameter) (kind : JobKind) (values : List Digest) :
    FixedR prims (refCore (fun oa => tweakable (C := C) oa) parameter kind values)
      (refCore (m := Id) (fun oa => evalTh prims.Th oa) parameter kind values) := by
  cases kind with
  | chainEnd e l => exact (FixedTh.chainWalk _ _ _ _ _ _ _).map _
  | chainRow e l =>
    exact FixedR.bind (FixedTh.chainWalk _ _ _ _ _ _ _) <| FixedR.bind (FixedTh.chainWalk _ _ _ _ _ _ _) <|
      FixedR.bind (FixedTh.chainWalk _ _ _ _ _ _ _) (FixedR.pure _)
  | chainValue e l p => exact (FixedTh.chainWalk _ _ _ _ _ _ _).map _
  | commitment e => exact (FixedTh.commitment _ _ _).map _
  | randomizer => exact FixedR.pure _

/-- The values of a list of points, padded to the length of the list. -/
def pad (k : ℕ) (v : List Digest) : List Digest := List.ofFn fun i : Fin k => v.getD i 0

theorem pad_cons (k : ℕ) (a : Digest) (v : List Digest) : pad (k + 1) (a :: v) = a :: pad k v := by
  simp [pad, List.ofFn_succ]

theorem length_pad (k : ℕ) (v : List Digest) : (pad k v).length = k := by simp [pad]

theorem mapM_pad {n : Type → Type} [Monad n] [LawfulMonad n] {α : Type} (F : α → n Digest) :
    ∀ xs : List α, xs.mapM F = pad xs.length <$> xs.mapM F
  | [] => by simp [pad]
  | x :: xs => by
    conv_lhs => rw [List.mapM_cons, mapM_pad F xs]
    simp [List.mapM_cons, pad_cons]

variable (prims) in
/-- When the circuits compute `Th`, a circuit gives `referenceJob` on values of its arity. -/
theorem eval_eq_refCore (hc : CircuitsCompute circuits prims.Th) (parameter : PublicParameter) (kind : JobKind)
    (v : List Digest) (hv : v.length = kind.arity) :
    (circuits parameter kind).eval (v.flatMap bitsOfDigest) =
      refCore (m := Id) (fun oa => evalTh prims.Th oa) parameter kind v := by
  have hlen : v.length ≤ 3 := by rw [hv]; cases kind <;> simp [JobKind.arity]
  let pts : List Point := (List.range v.length).map fun i =>
    Point.randomizer topLayer ⟨i % lifetime, Nat.mod_lt _ (by decide)⟩
  let F : Point → Digest := fun x => match x with
    | .randomizer _ e => v.getD e.val 0
    | _ => 0
  have hpts : pts.map F = v := by
    refine List.ext_getElem (by simp [pts]) fun i h1 h2 => ?_
    have hi : i < v.length := h2
    have hmod : i % lifetime = i := Nat.mod_eq_of_lt (lt_of_lt_of_le hi (hlen.trans (by decide)))
    simp [pts, F, hmod, hi]
  have := hc parameter ⟨kind, pts⟩ F (by simp [pts, hv])
  rw [referenceJob_id] at this
  simpa only [hpts] using this

variable (prims) in
/-- When the circuits compute `Th`, the dealer evaluates a job as `referenceJob` with the PRF values
of the seeds, with the same cache. -/
theorem roRun_evalJob (hc : CircuitsCompute circuits prims.Th) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (job : Job) (harity : job.points.length = job.kind.arity) (s : HashCache C) :
    roRun prims (evalJob circuits parameter seeds job) s =
      roRun prims (referenceJob tweakable (prfValue seeds) parameter job) s := by
  rw [referenceJob_eq]
  unfold evalJob
  rw [mapM_pad (prfValue seeds) job.points]
  simp only [bind_map_left]
  rw [roRun_bind, roRun_bind]
  refine bind_congr fun p => ?_
  rw [fixedR_refCore, roRun_pure,
    eval_eq_refCore prims circuits hc parameter job.kind _ (by rw [length_pad, harity])]

variable (prims) in
theorem roRun_mapM_congr {α β : Type} (f g : α → OracleComp (RoSpec C) β) :
    ∀ l : List α, (∀ a ∈ l, ∀ s, roRun prims (f a) s = roRun prims (g a) s) →
      ∀ s, roRun prims (l.mapM f) s = roRun prims (l.mapM g) s
  | [], _, s => rfl
  | a :: l, h, s => by
    simp only [List.mapM_cons, roRun_bind]
    rw [h a (by simp) s]
    refine bind_congr fun p => ?_
    rw [roRun_mapM_congr f g l (fun a' ha' => h a' (by simp [ha'])) p.2]

/-! ## The jobs of each run have their arity -/

/-- Every job of a list has the number of points that its kind takes. -/
def AllArity (jobs : List Job) : Prop := ∀ job ∈ jobs, job.points.length = job.kind.arity

theorem allArity_topJobs : AllArity topJobs := by
  intro job hjob
  simp only [topJobs, List.mem_flatMap, List.mem_map] at hjob
  obtain ⟨b, -, l, -, rfl⟩ := hjob
  rfl

theorem allArity_bottomJobs (b : Fin (2 ^ layerHeight)) : AllArity (bottomJobs b) := by
  intro job hjob
  simp only [bottomJobs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_singleton] at hjob
  rcases hjob with (⟨k, -, l, -, rfl⟩ | ⟨k, -, rfl⟩) | rfl <;> rfl

theorem allArity_signJobs (b : Fin (2 ^ layerHeight)) (encoding : Encoding) : AllArity (signJobs b encoding) := by
  intro job hjob
  simp only [signJobs, List.mem_map] at hjob
  obtain ⟨l, -, rfl⟩ := hjob
  rfl

/-- `ceremonyOutput` runs only the jobs of its runs. -/
theorem ceremonyOutput_congr {m : Type → Type} [Monad m] (lift : ∀ {α : Type}, OracleComp HashSpec α → m α)
    (parameter : PublicParameter) (run₁ run₂ : List Job → m (Option (List (List Bit))))
    (h : ∀ js, AllArity js → run₁ js = run₂ js) (top : TopTree) (tree : Tree) :
    ceremonyOutput lift parameter run₁ top tree = ceremonyOutput lift parameter run₂ top tree := by
  cases tree with
  | top =>
    dsimp only [ceremonyOutput]
    rw [h _ allArity_topJobs]
  | bottom b =>
    have hs : ∀ enc, run₁ (signJobs b enc) = run₂ (signJobs b enc) := fun enc => h _ (allArity_signJobs b enc)
    dsimp only [ceremonyOutput]
    rw [h _ (allArity_bottomJobs b)]
    simp only [hs]

/-! ## The dealer is `referenceTree` -/

variable (prims) in
/-- `simulateQ` of the oracles of `H` and `PRG`, as a monad map. -/
def roHom : OracleComp (RoSpec C) →ᵐ StateT (HashCache C) ProbComp where
  toFun _ oa := simulateQ (roImpl prims) oa
  toFun_pure' _ := simulateQ_pure _ _
  toFun_bind' _ _ := simulateQ_bind _ _ _

variable (prims) in
theorem roRun_dealer (hc : CircuitsCompute circuits prims.Th) (hsize : 0 < settings.batchSize)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree) (s : HashCache C) :
    roRun prims (Prod.fst <$> dealerCeremony circuits settings parameter seeds top tree) s =
      roRun prims (referenceTree tweakable (prfValue seeds) parameter top tree) s := by
  rw [fst_dealerCeremony circuits settings hsize]
  unfold referenceTree
  have e1 : simulateQ (roImpl prims) (ceremonyOutput (fun oa => tweakable oa) parameter
      (fun js => some <$> js.mapM (evalJob circuits parameter seeds)) top tree) = _ :=
    monadHom_ceremonyOutput (roHom prims) (fun oa => tweakable oa) parameter
      (fun js => some <$> js.mapM (evalJob circuits parameter seeds)) top tree
  have e2 : simulateQ (roImpl prims) (ceremonyOutput (fun oa => tweakable oa) parameter
      (fun jobs => some <$> jobs.mapM (referenceJob tweakable (prfValue seeds) parameter)) top tree) = _ :=
    monadHom_ceremonyOutput (roHom prims) (fun oa => tweakable oa) parameter
      (fun jobs => some <$> jobs.mapM (referenceJob tweakable (prfValue seeds) parameter)) top tree
  unfold roRun
  rw [e1, e2]
  refine congrArg (fun x => StateT.run x s) (ceremonyOutput_congr _ _ _ _ (fun js hjs => ?_) top tree)
  apply StateT.ext
  intro s'
  change roRun prims (some <$> _) s' = roRun prims (some <$> _) s'
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, roRun_bind, roRun_bind,
    roRun_mapM_congr prims _ _ js (fun job hjob s'' => roRun_evalJob prims circuits hc parameter seeds job
      (hjs job hjob) s'') s']

variable (prims) in
theorem localRun_liftComp {α : Type} (oa : OracleComp (RoSpec C) α) (s : HashCache C) :
    (simulateQ (localAnswer prims) (liftComp oa (LocalSpec C))).run s = roRun prims oa s := by
  unfold roRun
  exact congrArg (fun x => StateT.run x s)
    (QueryImpl.simulateQ_add_liftComp_right (unifFwdImpl (Query C →ₒ HashOutput)) (roImpl (C := C) prims) oa)

end DealerProof

/-- When the circuits compute `Th`, the dealer of `F_tree` gives `referenceTree` with the PRF values
of the seeds, with the same distribution of the tree and of the next cache. -/
theorem dealerTreeProof (prims : Primitives) (circuits : Circuits) (settings : Settings) (C : Committee) :
    DealerTreeStatement prims circuits settings C := by
  intro hc hsize parameter seeds top tree cache
  rw [localRun_liftComp, localRun_liftComp, roRun_dealer prims circuits settings hc hsize]

/-! ## The dealer succeeds except for the randomizer search -/

section Success

variable {C : Committee} (prims : Primitives) (circuits : Circuits) (settings : Settings)

/-- The top tree and then bottom tree `b` by `referenceTree`. -/
def refSuccessRun (parameter : PublicParameter) (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight)) :
    OracleComp (RoSpec C) (Option TreeOutput) := do
  let output ← referenceTree tweakable (prfValue seeds) parameter emptyTop .top
  let some top := TreeOutput.topTree output | pure none
  referenceTree tweakable (prfValue seeds) parameter top (.bottom b)

/-- The top tree never fails, and bottom tree `b` fails only when its randomizer search fails. -/
theorem refSuccess_fail (parameter : PublicParameter) (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight)) :
    Pr[fun z => z.1 = none | roRun prims (refSuccessRun parameter seeds b) ∅] ≤
      (1 - codewordP) ^ randomizerAttemptLimit := by
  unfold refSuccessRun
  refine step prims _ _ _ ∅ _ noMpc_empty fun r1 s1 hle1 hn1 hd1 hp1 => ?_
  have hm1 := hp1 IsMsg (Pres_refTop prims IsMsg (fun _ h => h) seeds parameter emptyTop) (noB_empty _)
  obtain ⟨h0, hg0, ha0⟩ := exists_good prims s1 hn1
  obtain ⟨top, htop, -, -⟩ := D_refTop (prims := prims) (h := h0) parameter seeds emptyTop
  have hr1 : r1 = some (.top top) := (hd1 h0 hg0 ha0).trans htop
  have htopf : ∀ h, Good prims h → Agrees h s1 → TopFacts prims h seeds parameter top := by
    intro h hg ha
    obtain ⟨top', htop', hc', hr'⟩ := D_refTop (prims := prims) (h := h) parameter seeds emptyTop
    have : some (TreeOutput.top top') = some (.top top) := htop'.symm.trans ((hd1 h hg ha).symm.trans hr1)
    cases this
    exact ⟨hc', hr'⟩
  subst hr1
  exact refBottom_fail prims seeds parameter top b s1 hn1 hm1 htopf

theorem roRun_map {α β : Type} (f : α → β) (oa : OracleComp (RoSpec C) α) (s : HashCache C) :
    roRun prims (f <$> oa) s = (fun p => (f p.1, p.2)) <$> roRun prims oa s := by
  rw [map_eq_bind_pure_comp, roRun_bind, map_eq_bind_pure_comp]
  refine bind_congr fun p => ?_
  rw [Function.comp, roRun_pure]
  rfl

/-- The run of the dealer in `TreeSuccessStatement` is `refSuccessRun`. -/
theorem roRun_dealerSuccess (hc : CircuitsCompute circuits prims.Th) (hsize : 0 < settings.batchSize)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight)) :
    roRun prims (do
        let (output, _) ← dealerCeremony circuits settings parameter seeds emptyTop .top
        let some top := TreeOutput.topTree output | pure none
        Prod.fst <$> dealerCeremony circuits settings parameter seeds top (.bottom b)) ∅ =
      roRun prims (refSuccessRun parameter seeds b) ∅ := by
  unfold refSuccessRun
  rw [roRun_bind, roRun_bind, ← roRun_dealer prims circuits settings hc hsize, roRun_map, bind_map_left]
  refine bind_congr fun p => ?_
  rcases p with ⟨⟨output, log⟩, s'⟩
  dsimp only
  cases TreeOutput.topTree output with
  | none => rfl
  | some top => exact roRun_dealer prims circuits settings hc hsize _ _ _ _ _

theorem pr_runWorld_free {α : Type} (oa : OracleComp (RoSpec C) α) (p : α → Prop) :
    Pr[fun r => p r.1 | runWorld prims (free (liftComp oa (LocalSpec C)))] = Pr[fun z => p z.1 | roRun prims oa ∅] := by
  rw [runWorld, StateT.run'_eq, world_lift_run, Functor.map_map]
  erw [probEvent_map]
  rfl

end Success

/-- When the circuits compute `Th`, the dealer of `F_tree` gives the top tree and then bottom tree
`b`, except when the randomizer search of its top signature fails. -/
theorem treeSuccessProof (prims : Primitives) (circuits : Circuits) (settings : Settings) (C : Committee) :
    TreeSuccessStatement prims circuits settings C := by
  intro hc hsize parameter seeds b
  have hfin : (1 - codewordP) ^ randomizerAttemptLimit ≠ ⊤ :=
    ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  rw [← toReal_failure]
  refine ENNReal.toReal_mono hfin ?_
  rw [pr_runWorld_free prims _ (fun r => r = none)]
  erw [roRun_dealerSuccess prims circuits settings hc hsize]
  exact refSuccess_fail prims parameter seeds b

/-- info: 'ThresholdLeanXmssSecurity.dealerTreeProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dealerTreeProof

/-- info: 'ThresholdLeanXmssSecurity.treeSuccessProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSuccessProof

end ThresholdLeanXmssSecurity
