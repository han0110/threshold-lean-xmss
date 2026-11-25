import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Game
import ThresholdLeanXmssSecurity.Proof.SeedGenAlias
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.VoteSupport

/-!
# The hops of the flag and of the seeds

`flagFirstHop` proves `FlagFirstHopW`. When the flag of `dkgTreeGame` is set, `firstRunWith` has a
first bad record (`FlagRecorded`), for each readiness test. The converse does not hold, because a start
that is not ready makes a record while the flag stays false. `seedsHop` proves `SeedsHopW`. The seeds
differ after the seed generation with probability at most `seedGenHashError C q`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity SeedHitProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## The relation of the two games -/

/-- The record of the first bad event is set when the flag is set. -/
def FlagRecorded {σ : Type} (s : FirstState C σ) : Prop := s.real.flag = true → s.first ≠ none

/-- `y` is `x` with the record, from the state `s`. The real state of `y` has the law of the state
of `x` under `streamWorld`, and `y` keeps `FlagRecorded`. -/
def TracksAt (D : C.Coalition) {σ α : Type} (x : RealM C σ α) (y : FirstM C σ α) (s : FirstState C σ) : Prop :=
  simulateQ (streamWorld prims D) (x.run s.real) = (fun r => (r.1, r.2.real)) <$> y.run s ∧
    ∀ w, FlagRecorded s → ∀ z ∈ support ((y.run s).run w), FlagRecorded z.1.2

/-- `y` is `x` with the record, from each state. -/
def Tracks (D : C.Coalition) {σ α : Type} (x : RealM C σ α) (y : FirstM C σ α) : Prop :=
  ∀ s, TracksAt prims D x y s

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem tracks_pure (D : C.Coalition) {σ α : Type} (a : α) :
    Tracks (C := C) prims D (pure a : RealM C σ α) (pure a) := by
  intro s
  refine ⟨by simp, fun w hs z hz => ?_⟩
  simp at hz
  rw [hz]
  exact hs

theorem tracks_bind (D : C.Coalition) {σ α β : Type} {x : RealM C σ α} {y : FirstM C σ α}
    {f : α → RealM C σ β} {g : α → FirstM C σ β} (hxy : Tracks prims D x y)
    (hfg : ∀ a, Tracks prims D (f a) (g a)) : Tracks prims D (x >>= f) (y >>= g) := by
  intro s
  constructor
  · simp only [StateT.run_bind, simulateQ_bind, (hxy s).1, bind_map_left, map_bind]
    congr 1
    funext r
    exact (hfg r.1 r.2).1
  · intro w hs z hz
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨u, hu, hz⟩ := hz
    exact (hfg u.1.1 u.1.2).2 u.2 ((hxy s).2 w hs u hu) z hz

theorem tracks_lift (D : C.Coalition) {σ α : Type} (oa : OracleComp (WorldSpec C) α) :
    Tracks prims D (StateT.lift oa : RealM C σ α) (inStream prims D oa) := by
  intro s
  refine ⟨by simp [inStream], fun w hs z hz => ?_⟩
  simp only [inStream, StateT.run_lift, StateT.run_bind, StateT.run_pure, support_bind, support_pure,
    Set.mem_iUnion, Set.mem_singleton_iff] at hz
  obtain ⟨u, -, rfl⟩ := hz
  exact hs

theorem tracks_get_bind (D : C.Coalition) {σ α : Type} {f : RealState C σ → RealM C σ α}
    {g : FirstState C σ → FirstM C σ α} (h : ∀ s, TracksAt prims D (f s.real) (g s) s) :
    Tracks prims D (get >>= f) (get >>= g) := by
  intro s
  simpa [TracksAt] using h s

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem tracks_map_get (D : C.Coalition) {σ α : Type} (f : RealState C σ → α) :
    Tracks prims D (f <$> (get : RealM C σ _)) ((fun s => f s.real) <$> (get : FirstM C σ _)) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact tracks_get_bind prims D fun s => tracks_pure prims D _ s

/-! ## The runs of a tree -/

omit [Fintype E] [DecidableEq E] in
theorem tracks_treeRun (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (ready : RealState C net.State → StreamState C → Prop) (tree : Tree) :
    Tracks prims D (treeRun K circuits settings (wrongOutput D) D net tree)
      (firstTreeRunWith prims K circuits settings D net ready tree) := by
  intro s
  constructor
  · simp [treeRun, firstTreeRunWith, firstTreeRunOf, streamTreeRun, inStream]
  · intro w hs z hz
    simp only [firstTreeRunWith, firstTreeRunOf, inStream, StateT.run_bind, StateT.run_get, pure_bind,
      StateT.run_lift, bind_assoc, StateT.run_set, StateT.run_pure, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨x, -, y, hy, rfl⟩ := hz
    have hsplit := Vote.voteRound_split_run worldRoles D net x.1.1.1 x.1.1.2 (treeVote tree) (streamWorld prims D)
      x.2 y hy
    intro hflag
    simp only [hsplit, Bool.or_false, Bool.or_eq_true] at hflag
    rcases hflag with hflag | hbad
    · cases hfirst : s.first with
      | none => exact absurd hfirst (hs hflag)
      | some _ => simp
    · simp [hbad]

omit [Fintype E] [DecidableEq E] in
theorem tracks_treeRuns (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (ready : RealState C net.State → StreamState C → Prop) (tree : Tree) (count : ℕ) :
    Tracks prims D (treeRuns K circuits settings runLimit (wrongOutput D) D net tree count)
      (firstTreeRunsWith prims K circuits settings runLimit D net ready tree count) := by
  induction count with
  | zero => exact tracks_pure prims D ()
  | succ count ih =>
    refine tracks_get_bind prims D fun s => ?_
    by_cases h : mayRun runLimit D s.real tree
    · simp only [h, ↓reduceIte]
      exact tracks_bind prims D (tracks_treeRun prims K circuits settings D net ready tree) (fun _ => ih) s
    · simp only [h, ↓reduceIte]
      exact tracks_pure prims D () s

/-! ## The computations of the world as monad maps -/

/-- A computation of the world on the real state. It keeps the state. -/
def realHom (σ : Type) : OracleComp (WorldSpec C) →ᵐ RealM C σ where
  toFun _ oa := StateT.lift oa
  toFun_pure' a := by ext; simp
  toFun_bind' _ _ := by ext; simp

/-- A computation of the world on the state of `firstRunWith`, answered by `streamWorld`. -/
def firstHom (D : C.Coalition) (σ : Type) : OracleComp (WorldSpec C) →ᵐ FirstM C σ where
  toFun _ oa := inStream prims D oa
  toFun_pure' a := by ext; simp [inStream]
  toFun_bind' _ _ := by ext; simp [inStream]

theorem hmap_dealtWith_hom {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    (h : m →ᵐ n) (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) (parameter : PublicParameter)
    (keys : C.Party → Keys C) (top : TopTree) (value : Point → m Digest) :
    Dealt.hmap h (dealtWith lift parameter keys top value) =
      dealtWith (fun oa => h (lift oa)) parameter keys top (fun x => h (value x)) := by
  unfold Dealt.hmap dealtWith
  congr 1
  funext b
  rw [hom_map, hom_referenceTree]

theorem hom_operatorAnswer {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    (h : m →ᵐ n) (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) (value : Point → m Digest)
    (operator : OperatorState C) (e : KeyIndex) (q : TsigQuery C) (st : TsigState C) :
    h ((operatorAnswer lift value operator e q).run st) =
      (operatorAnswer (fun oa => h (lift oa)) (fun x => h (value x)) operator e q).run st := by
  unfold operatorAnswer
  split
  · rw [ownAnswer_run, ownAnswer_run, hom_tsigOracles, hmap_dealtWith_hom]
  · simp

theorem hom_honestSignature {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    (h : m →ᵐ n) (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) (dealt : Dealt C m) (e : KeyIndex)
    (message : Message) :
    h (honestSignature lift dealt e message) =
      honestSignature (fun oa => h (lift oa)) (Dealt.hmap h dealt) e message := by
  unfold honestSignature
  rw [MonadHom.mmap_bind]
  congr 1
  funext tree
  rcases tree with _ | tree
  · exact h.toFun_pure' _
  · simp only [MonadHom.mmap_bind]
    congr 1
    funext ρ
    congr 1
    funext r
    rcases r with _ | ⟨randomness, encoding⟩
    · exact h.toFun_pure' _
    · simp only [MonadHom.mmap_bind, hom_sequenceFin, MonadHom.mmap_pure]
      congr 2
      funext l
      split <;> simp [Dealt.hmap]

theorem hom_forgeryWins {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    (h : m →ᵐ n) (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) (dealt : Dealt C m) (st : TsigState C)
    (forgery : Forgery) :
    h (forgeryWins lift dealt st forgery) = forgeryWins (fun oa => h (lift oa)) (Dealt.hmap h dealt) st forgery := by
  unfold forgeryWins
  simp only [MonadHom.mmap_bind]
  congr 1
  funext verified
  split_ifs
  · simp
  · simp [hom_honestSignature]

/-- `canonicalDealt` in the world. -/
def worldDealt (D : C.Coalition) (operators : C.Party → OperatorState C) (parameter : PublicParameter)
    (top : TopTree) : Dealt C (OracleComp (WorldSpec C)) :=
  { dealtWith (m := OracleComp (WorldSpec C)) (fun oa => free (liftComp oa _)) parameter
      (fun i => ((operators i).keys).getD noKeys) top
      (fun x => free (liftComp (prfValue (gameSeeds D fun i => (operators i).keys) x) _)) with
    bottom := fun b => pure (heldBottom D operators b) }

/-- The win test on the real state is a computation of the world. It keeps the real state. -/
theorem forgeryWins_canonicalDealt (D : C.Coalition) {σ : Type} (operators : C.Party → OperatorState C)
    (parameter : PublicParameter) (top : TopTree) (st : TsigState C) (forgery : Forgery) :
    forgeryWins (m := RealM C σ) realLift (canonicalDealt D operators parameter top) st forgery =
      realHom σ (forgeryWins (fun oa => free (liftComp oa _)) (worldDealt D operators parameter top) st forgery) := by
  rw [hom_forgeryWins]
  have : Dealt.hmap (realHom σ) (worldDealt D operators parameter top) = canonicalDealt D operators parameter top := by
    unfold Dealt.hmap worldDealt canonicalDealt
    congr 1
  rw [this]
  rfl

/-! ## The signing phase -/

theorem tracks_modify (D : C.Coalition) {σ : Type} (f : RealState C σ → RealState C σ)
    (g : FirstState C σ → FirstState C σ) (real : ∀ s, (g s).real = f s.real)
    (recorded : ∀ s, FlagRecorded s → FlagRecorded (g s)) :
    Tracks prims D (modify f : RealM C σ Unit) (modify g) := by
  intro s
  refine ⟨by simp [real], fun w hs z hz => ?_⟩
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  rw [hz]
  exact recorded s hs

/-- `y` is `x` with the record, from each state of the signing game. -/
def TracksSign (D : C.Coalition) {σ α : Type} (x : StateT (TsigState C) (RealM C σ) α)
    (y : StateT (TsigState C) (FirstM C σ) α) : Prop :=
  ∀ st, Tracks prims D (x.run st) (y.run st)

theorem tracksSign_pure (D : C.Coalition) {σ α : Type} (a : α) :
    TracksSign (C := C) prims D (pure a : StateT (TsigState C) (RealM C σ) α) (pure a) :=
  fun _ => tracks_pure prims D _

theorem tracksSign_bind (D : C.Coalition) {σ α β : Type} {x : StateT (TsigState C) (RealM C σ) α}
    {y : StateT (TsigState C) (FirstM C σ) α} {f : α → StateT (TsigState C) (RealM C σ) β}
    {g : α → StateT (TsigState C) (FirstM C σ) β} (hxy : TracksSign prims D x y)
    (hfg : ∀ a, TracksSign prims D (f a) (g a)) : TracksSign prims D (x >>= f) (y >>= g) := fun st =>
  tracks_bind prims D (hxy st) fun r => hfg r.1 r.2

theorem tracksSign_lift (D : C.Coalition) {σ α : Type} {x : RealM C σ α} {y : FirstM C σ α}
    (hxy : Tracks prims D x y) :
    TracksSign prims D (StateT.lift x : StateT (TsigState C) (RealM C σ) α) (StateT.lift y) := fun _ =>
  tracks_bind prims D hxy fun _ => tracks_pure prims D _

theorem tracksSign_get_bind (D : C.Coalition) {σ α : Type}
    {f : RealState C σ → StateT (TsigState C) (RealM C σ) α}
    {g : FirstState C σ → StateT (TsigState C) (FirstM C σ) α}
    (h : ∀ s st, TracksAt prims D ((f s.real).run st) ((g s).run st) s) :
    TracksSign prims D (StateT.lift get >>= f) (StateT.lift get >>= g) := by
  intro st s
  simpa [TracksAt] using h s st

/-- A run of an oracle program keeps `TracksSign` when each oracle keeps it. -/
theorem tracksSign_simulateQ (D : C.Coalition) {σ ι α : Type} {spec : OracleSpec ι}
    (implx : QueryImpl spec (StateT (TsigState C) (RealM C σ)))
    (imply : QueryImpl spec (StateT (TsigState C) (FirstM C σ)))
    (h : ∀ t, TracksSign prims D (implx t) (imply t)) (oa : OracleComp spec α) :
    TracksSign prims D (simulateQ implx oa) (simulateQ imply oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using tracksSign_pure prims D a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query]
    exact tracksSign_bind prims D (by simpa using h t) ih

omit [Fintype E] [DecidableEq E] in
theorem tracks_treeRequest (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (ready : RealState C net.State → StreamState C → Prop) (b : Fin (2 ^ layerHeight)) :
    Tracks prims D (treeRequest K circuits settings runLimit (wrongOutput D) D net b)
      (firstTreeRequestWith prims K circuits settings runLimit D net ready b) := by
  refine tracks_bind prims D (tracks_treeRuns prims K circuits settings runLimit D net ready _ 1) fun _ => ?_
  refine tracks_get_bind prims D fun s => ?_
  rcases heldBottom D s.real.operators b with _ | tree
  · exact tracks_pure prims D _ s
  · exact tracks_bind prims D (tracks_lift prims D _) (fun _ => tracks_pure prims D _) s

theorem tracksSign_signRequest (D : C.Coalition) {σ : Type} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    TracksSign prims D (signRequest D (σ := σ) i e q) (firstSignRequest prims D i e q) := by
  refine tracksSign_bind prims D (tracksSign_lift prims D (tracks_modify prims D _ _ (fun _ => rfl)
    fun s hs => hs)) fun _ => ?_
  refine tracksSign_get_bind prims D fun s st => ?_
  have key := tracks_lift prims D (σ := σ) ((operatorAnswer (m := OracleComp (WorldSpec C))
    (fun oa => free (liftComp oa _)) (fun x => free (liftComp (prfValue (gameSeeds D fun j =>
      (s.real.operators j).keys) x) _)) (s.real.operators i) e q).run st) s
  rw [show StateT.lift _ = realHom σ _ from rfl, show inStream prims D _ = firstHom prims D σ _ from rfl,
    hom_operatorAnswer, hom_operatorAnswer] at key
  exact key

omit [Fintype E] [DecidableEq E] in
theorem tracksSign_oracles (D : C.Coalition) (A : DkgTsigAdversary C E)
    (ready : RealState C A.net.State → StreamState C → Prop) (q : TsigQuery C) :
    TracksSign prims D (realOracles K circuits settings runLimit (wrongOutput D) D A q)
      (firstOraclesWith prims K circuits settings runLimit D A ready q) := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact tracksSign_pure prims D _
  · exact tracksSign_lift prims D (tracks_treeRequest prims K circuits settings runLimit D A.net ready b)
  · exact tracksSign_signRequest prims D i e _
  · exact tracksSign_signRequest prims D i e _

omit [Fintype E] [DecidableEq E] in
/-- The run of `A.forge` in `dkgSigning` and in `firstSigningWith`. -/
theorem tracksSign_forge (D : C.Coalition) (A : DkgTsigAdversary C E)
    (ready : RealState C A.net.State → StreamState C → Prop) (pk : PublicKey) (top : TopTree) :
    TracksSign prims D
      (simulateQ ((fun t => StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
          : QueryImpl (LocalSpec C) (StateT (TsigState C) (RealM C A.net.State))) +
        (realOracles K circuits settings runLimit (wrongOutput D) D A +
          (fun q => match q with
            | .read => StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _))
            | .write state => StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state })
            : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (RealM C A.net.State)))))
        (A.forge pk top))
      (simulateQ ((fun t => StateT.lift (inStream prims D (worldRoles.adversary (OracleComp.lift (OracleSpec.query t))))
          : QueryImpl (LocalSpec C) (StateT (TsigState C) (FirstM C A.net.State))) +
        (firstOraclesWith prims K circuits settings runLimit D A ready +
          (fun q => match q with
            | .read => StateT.lift ((·.real.adversary) <$> (get : FirstM C A.net.State _))
            | .write state => StateT.lift (modify fun s : FirstState C A.net.State =>
                { s with real := { s.real with adversary := state } })
            : QueryImpl (StateSpec A.net.State) (StateT (TsigState C) (FirstM C A.net.State)))))
        (A.forge pk top)) := by
  refine tracksSign_simulateQ prims D _ _ (fun t => ?_) _
  rcases t with t | q | q
  · exact tracksSign_lift prims D (tracks_lift prims D _)
  · exact tracksSign_oracles prims K circuits settings runLimit D A ready q
  · rcases q with _ | state
    · exact tracksSign_lift prims D (tracks_map_get prims D (·.adversary))
    · exact tracksSign_lift prims D (tracks_modify prims D _ _ (fun _ => rfl) fun s hs => hs)

/-- A computation that ends with a computation of the world on the real state has the law of the flag
of the computation without that end. -/
theorem drop_winTest (D : C.Coalition) {σ β : Type} (fs : FirstState C σ) (w : StreamState C) {X : RealM C σ β}
    {Y : FirstM C σ β} (h : simulateQ (streamWorld prims D) (X.run fs.real) = (fun r => (r.1, r.2.real)) <$> Y.run fs)
    (W : β → RealState C σ → OracleComp (WorldSpec C) Bool) :
    (fun r => r.1.2.real.flag) <$> ((Y >>= fun _ => pure ()).run fs).run w =ᵈ
      (fun r => r.1.2.flag) <$> (simulateQ (streamWorld prims D)
        ((X >>= fun p => get >>= fun s => realHom σ (W p s)).run fs.real)).run w := by
  simp only [StateT.run_bind]
  rw [simulateQ_bind, h]
  simp only [bind_map_left, map_bind, StateT.run_bind]
  refine EvalDistEq.bind_right _ fun a => ?_
  simp only [realHom]
  simp
  rw [evalDistEq_iff_evalDist_eq]
  simp

omit [Fintype E] [DecidableEq E] in
/-- The signing phase without the win test keeps the law of the flag. The win test only reads the
real state. -/
theorem signing_flag (D : C.Coalition) (A : DkgTsigAdversary C E)
    (ready : RealState C A.net.State → StreamState C → Prop) (fs : FirstState C A.net.State)
    (w : StreamState C) :
    (fun r => r.1.2.real.flag) <$> ((firstSigningWith prims K circuits settings runLimit D A ready).run fs).run w =ᵈ
      (fun r => r.1.2.flag) <$> (simulateQ (streamWorld prims D)
        ((dkgSigning K circuits settings runLimit (wrongOutput D) D A).run fs.real)).run w := by
  unfold firstSigningWith firstSigningOf dkgSigning
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases topHolder D fs.real.operators with _ | ⟨keys, top⟩
  · simp
  · simp only [forgeryWins_canonicalDealt]
    exact drop_winTest prims D fs w (tracksSign_forge prims K circuits settings runLimit D A ready
      ⟨top.root, keys.parameter⟩ top ⟨D.1, fun _ => none, [], fun _ => none⟩ fs).1 _

omit [Fintype E] [DecidableEq E] in
/-- The signing phase without the win test keeps `FlagRecorded`. -/
theorem signing_recorded (D : C.Coalition) (A : DkgTsigAdversary C E)
    (ready : RealState C A.net.State → StreamState C → Prop) (fs : FirstState C A.net.State)
    (w : StreamState C) (hs : FlagRecorded fs) :
    ∀ z ∈ support (((firstSigningWith prims K circuits settings runLimit D A ready).run fs).run w),
      FlagRecorded z.1.2 := by
  unfold firstSigningWith firstSigningOf
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases topHolder D fs.real.operators with _ | ⟨keys, top⟩
  · intro z hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hs
  · intro z hz
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨u, hu, hz⟩ := hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact (tracksSign_forge prims K circuits settings runLimit D A ready ⟨top.root, keys.parameter⟩ top
      ⟨D.1, fun _ => none, [], fun _ => none⟩ fs).2 w hs u hu

omit [Fintype E] [DecidableEq E] in
/-- The runs of the top tree and the signing phase keep the law of the flag. -/
theorem afterSetup_flag (D : C.Coalition) (A : DkgTsigAdversary C E)
    (ready : RealState C A.net.State → StreamState C → Prop) (fs : FirstState C A.net.State)
    (w : StreamState C) :
    (do
      let x ← ((firstTreeRunsWith prims K circuits settings runLimit D A.net ready .top runLimit).run fs).run w
      let a ← ((firstSigningWith prims K circuits settings runLimit D A ready).run x.1.2).run x.2
      pure a.1.2.real.flag) =ᵈ
    (do
      let x ← (simulateQ (streamWorld prims D)
        ((treeRuns K circuits settings runLimit (wrongOutput D) D A.net .top runLimit).run fs.real)).run w
      let a ← (simulateQ (streamWorld prims D)
        ((dkgSigning K circuits settings runLimit (wrongOutput D) D A).run x.1.2)).run x.2
      pure a.1.2.flag) := by
  rw [(tracks_treeRuns prims K circuits settings runLimit D A.net ready .top runLimit fs).1]
  simp only [StateT.run_map, bind_map_left, bind_pure_comp]
  exact EvalDistEq.bind_right _ fun a =>
    signing_flag prims K circuits settings runLimit D A ready a.1.2 a.2

/-! ## The hop -/

omit [Fintype E] [DecidableEq E] in
/-- The flag of `dkgTreeGame` in `streamWorld` comes with a first bad record of `firstRunWith`. -/
theorem flagFirstHop : FlagFirstHopW prims K circuits settings runLimit (C := C) (E := E) := by
  intro D A ready
  have law : Pr{let r ← (simulateQ (streamWorld prims D) (dkgTreeGame K circuits settings runLimit D A)).run (∅, ∅)}[
      r.1 = true] = Pr{let r ← firstRunWith prims K circuits settings runLimit D A ready}[r.1.real.flag = true] := by
    have hd : (fun r => r.1.real.flag) <$> firstRunWith prims K circuits settings runLimit D A ready =ᵈ
        (fun r => r.1) <$>
          (simulateQ (streamWorld prims D) (dkgTreeGame K circuits settings runLimit D A)).run (∅, ∅) := by
      unfold firstRunWith firstRunOf dkgTreeGame dkgTsigRun
      simp only [simulateQ_map, simulateQ_bind, StateT.run_bind, StateT.run_map, map_bind]
      refine EvalDistEq.bind_right _ fun u => ?_
      simp only [StateT.run_get, pure_bind, StateT.run_pure, map_pure, simulateQ_pure, bind_assoc]
      exact EvalDistEq.bind_right _ fun t => afterSetup_flag prims K circuits settings runLimit D A ready _ t.2
    have h := hd.prEvent_eq (· = true)
    rw [prEvent_map, prEvent_map] at h
    exact h.symm
  have mono : Pr{let r ← firstRunWith prims K circuits settings runLimit D A ready}[r.1.real.flag = true] ≤
      Pr{let r ← firstRunWith prims K circuits settings runLimit D A ready}[r.1.first ≠ none] := by
    refine prEvent_mono_of_support _ _ _ fun r hr hflag => ?_
    unfold firstRunWith firstRunOf at hr
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at hr
    obtain ⟨u, -, v, hv, t, -, x, ⟨y, hy, hx⟩, hr⟩ := hr
    simp only [StateT.run_get, support_pure, Set.mem_singleton_iff] at hv
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hv hr
    refine signing_recorded prims K circuits settings runLimit D A ready y.1.2 y.2
      ((tracks_treeRuns prims K circuits settings runLimit D A.net ready .top runLimit _).2 _ ?_ y hy) x hx hflag
    intro hstart
    simp only at hstart
    simp [hstart]
  unfold firstProbWith
  rw [law]
  exact ENNReal.toReal_mono (prEvent_ne_top _) mono

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

/-! ## The seed generation in the stream world -/

section NoStream

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

theorem hashQuery_noStreamKey (phase : Phase) (q : Query C) (hq : SetupCell phase q) :
    IsQueryBoundP (hashQuery q) (fun t => FreeStreamKey (C := C) (.inr (.inr t))) 0 := by
  show IsQueryBoundP (liftM ((RoSpec C).query (.inl q)) : OracleComp (RoSpec C) _) _ 0
  rw [isQueryBoundP_query_iff]
  intro h
  cases q <;> first | exact h.elim | exact hq.elim

theorem deriveKeys_noStreamKey (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    IsQueryBoundP (deriveKeys phase i view) (fun t => FreeStreamKey (C := C) (.inr (.inr t))) 0 := by
  have rest : ∀ parameter : HashOutput, IsQueryBoundP (do
      let term ← C.terms.mapM fun T => if i ∈ C.holders T then
        hashQuery (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T))
        else pure 0
      let pair ← C.parties.mapM fun j => if h : j = i then pure 0 else
        let p := C.pairOf i j (Ne.symm h)
        hashQuery (.derive phase .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1])
      pure (parameter, fun T : C.Term => term.getD (C.terms.idxOf T) 0, fun j : C.Party => pair.getD j.val 0) :
        OracleComp (RoSpec C) (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))) (fun t => FreeStreamKey (C := C) (.inr (.inr t))) 0 := fun parameter => by
    refine isQueryBoundP_bind_zero _ _ ?_ fun _ => isQueryBoundP_bind_zero _ _ ?_ fun _ =>
      isQueryBoundP_pure _ _ _
    · refine isQueryBoundP_mapM_zero _ _ _ fun T _ => ?_
      split_ifs
      · exact hashQuery_noStreamKey phase _ rfl
      · exact isQueryBoundP_pure _ _ _
    · refine isQueryBoundP_mapM_zero _ _ _ fun j _ => ?_
      split_ifs
      · exact isQueryBoundP_pure _ _ _
      · exact hashQuery_noStreamKey phase _ rfl
  unfold deriveKeys
  split_ifs
  · exact isQueryBoundP_bind_zero _ _ (hashQuery_noStreamKey phase _ rfl) rest
  · exact isQueryBoundP_bind_zero _ _ (isQueryBoundP_pure _ _ _) rest

theorem oracleStep_noStreamKey {β : Type} (oa : OracleComp (RoSpec C) β)
    (h : IsQueryBoundP oa (fun t => FreeStreamKey (C := C) (.inr (.inr t))) 0) :
    IsQueryBoundP (oracleStep oa : PartyM C E G β).run (PartyFree (E := E) (G := G) (FreeStreamKey (C := C))) 0 :=
  isQueryBoundP_localStep _ _ (isQueryBoundP_liftComp_ro _ oa h)

theorem commitRevealEcho_noStreamKey (phase : Phase) (i : C.Party) (own : Parts C) :
    IsQueryBoundP (commitRevealEcho phase i own : PartyM C E G _).run
      (PartyFree (E := E) (G := G) (FreeStreamKey (C := C))) 0 := by
  have hx : ∀ outbox : Mail C E, ¬ PartyFree (E := E) (G := G) (FreeStreamKey (C := C)) (.inl (.inr outbox)) :=
    fun _ h => h
  unfold commitRevealEcho
  refine isQueryBoundP_partyBind _ _ _ (oracleStep_noStreamKey _
    (isQueryBoundP_mapM_zero _ _ _ fun j _ => hashQuery_noStreamKey phase _ rfl)) fun commitments => ?_
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_exchange _ hx _) fun committed => ?_
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_exchange _ hx _) fun revealed => ?_
  refine isQueryBoundP_partyBind _ _ _ (oracleStep_noStreamKey _
    (isQueryBoundP_mapM_zero _ _ _ fun j _ => hashQuery_noStreamKey phase _ rfl)) fun opens => ?_
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_require _ _) fun _ => ?_
  refine isQueryBoundP_partyBind _ _ _ (oracleStep_noStreamKey _ (deriveKeys_noStreamKey phase i _)) fun keys => ?_
  refine isQueryBoundP_partyBind _ _ _ (oracleStep_noStreamKey _
    (isQueryBoundP_mapM_zero _ _ _ fun j _ => hashQuery_noStreamKey phase _ rfl)) fun shared => ?_
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_exchange _ hx _) fun received => ?_
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_require _ _) fun _ => ?_
  exact isQueryBoundP_partyPure _ _

/-- An operator of the seed generation makes no `PRG` call and hashes no stream key. -/
theorem seedGen_noStreamKey (i : C.Party) :
    IsQueryBoundP (seedGen i : PartyM C E RealSpec (Keys C)).run
      (PartyFree (E := E) (G := RealSpec) (FreeStreamKey (C := C))) 0 := by
  unfold seedGen seedGenWith
  refine isQueryBoundP_partyBind _ _ _ (isQueryBoundP_localStep _ _
    (isQueryBoundP_liftComp_prob_of_sample _ (fun _ h => h) _)) fun own => ?_
  exact isQueryBoundP_partyBind _ _ _ (commitRevealEcho_noStreamKey .seedGen i own) fun _ =>
    isQueryBoundP_partyPure _ _

/-- The real seed generation makes no free stream call under a hidden name. -/
theorem seedGen_noHidden (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit)
    (z : Aux) :
    IsQueryBoundP (realExecution D A noFunctionality setupRounds
      (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z) (FreeHiddenStream D) 0 :=
  (isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_adversary_noStreamKey _ 0) fun st _ =>
    executePhase_free _ (fun _ h => h) D A noFunctionality setupRounds st _ fun i _ =>
      seedGen_noStreamKey i).of_imp (freeStreamKey_of_freeHiddenStream D)

/-- The real seed generation in the stream world is its run in the ordinary world, and the hidden
table does not change. -/
theorem streamWorld_seedGen (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (cache : HashCache C) (table : HiddenCache C) :
    (simulateQ (streamWorld prims D) (realExecution D A noFunctionality setupRounds
      (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z)).run (cache, table) =
      (fun r => (r.1, (r.2, table))) <$> (simulateQ (worldAnswer prims) (realExecution D A noFunctionality
        setupRounds (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z)).run cache :=
  streamWorld_run_of_noHidden prims D _ (seedGen_noHidden D A x z) cache table

end NoStream

/-! ## The seeds of the real seed generation -/

section Consistent

variable {C : Committee} {E : Type}

/-- Outputs that are dealt keys of one dealing never differ. -/
theorem seedsDiffer_of_dealt (D : C.Coalition) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (out : C.Party → Option (Keys C))
    (hout : ∀ i, ∀ k ∈ out i, k = dealtKeys parameter seeds pairs i) : seedsDiffer D out = false := by
  obtain ⟨hseeds, hpairs⟩ := keysAgree_of_dealt D parameter seeds pairs out hout
  rw [seedsDiffer, decide_eq_false_iff_not]
  rintro ⟨i, j, ki, kj, hi, hj, hki, hkj, hdiff⟩
  rcases hdiff with hpar | ⟨T, hiT, hjT, hT⟩ | ⟨hij, hpair⟩
  · rw [hout i ki hki, hout j kj hkj] at hpar
    exact hpar rfl
  · exact hT (hseeds i j T hi hj hiT hjT ki hki kj hkj)
  · exact hpair (hpairs i j hi hj hij ki hki kj hkj)

/-- The seeds differ after the real seed generation with probability at most `seedGenHashError`.
The proof uses the distance claim of the setup at the distinguisher that reads only the outputs. -/
theorem seedGenConsistent (prims : Primitives) (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (q : ℕ)
    (hq : IsQueryBounded A (fun _ => pure true : Distinguisher C A.State (Keys C)) setupRounds q) :
    (Pr{let r ← runWorld prims (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z)}[
      seedsDiffer D r.1.2 = true]).toReal ≤ seedGenHashError C q := by
  let f : A.State × (C.Party → Option (Keys C)) → Bool := fun r => seedsDiffer D r.2
  have hq' : IsQueryBounded A (fun r => pure (f r) : Distinguisher C A.State (Keys C)) setupRounds q := by
    obtain ⟨start, step, final, hsum, hs, hr, ha, -⟩ := hq
    exact ⟨start, step, final, hsum, hs, hr, ha, fun _ => isQueryBoundP_pure _ _ _⟩
  have hd := setupSecurityDistance (C := C) (E := E) prims .seedGen D A x z (fun r => pure (f r)) q hq'
  have hideal : f <$> (seedGenIdealProjection D <$> setupCommonGame .seedGen D A x z) =
      (fun _ => false) <$> setupCommonGame .seedGen D A x z := by
    unfold setupCommonGame
    simp only [map_bind, map_pure]
    refine bind_congr fun st => bind_congr fun s => ?_
    rcases s with ⟨p, s, pr⟩
    refine bind_congr fun e => ?_
    rcases e with ⟨st', em⟩
    congr 1
    refine seedsDiffer_of_dealt D p s pr _ fun i k hk => ?_
    simp only [seedGenIdealProjection] at hk
    split_ifs at hk
    · simp only [Option.mem_def, Option.some.injEq] at hk
      rw [← hk]
    · simp only [Option.mem_def, reduceCtorEq] at hk
  rw [distinguish_pure, distinguish_pure, hideal, accepts_map, accepts_map, setupHashError_seedGen] at hd
  simp only [Bool.false_eq_true, prEvent_false, ENNReal.toReal_zero, sub_zero] at hd
  exact (le_abs_self _).trans hd

end Consistent

/-! ## The first bad event after the seed generation -/

section Keep

variable {C : Committee} {σ : Type}

/-- The record of a first bad event is not the seeds. -/
def SeedsFree (first : Option (Stage × StreamState C)) : Prop := ∀ world, first ≠ some (.seeds, world)

theorem seedsFree_none : SeedsFree (C := C) none := fun _ h => by cases h

theorem seedsFree_orElse {a b : Option (Stage × StreamState C)} (ha : SeedsFree a) (hb : SeedsFree b) :
    SeedsFree (a <|> b) := by
  cases a with
  | none => exact hb
  | some _ => exact ha

/-- A computation of the game that keeps `SeedsFree` on the record of the first bad event. -/
def KeepsFree {α : Type} (m : FirstM C σ α) : Prop :=
  ∀ s world, SeedsFree s.first → ∀ z ∈ support ((m.run s).run world), SeedsFree z.1.2.first

theorem keepsFree_pure {α : Type} (a : α) : KeepsFree (C := C) (σ := σ) (pure a) := by
  intro s world hs z hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact hs

theorem keepsFree_bind {α β : Type} {m : FirstM C σ α} {f : α → FirstM C σ β} (hm : KeepsFree m)
    (hf : ∀ a, KeepsFree (f a)) : KeepsFree (m >>= f) := by
  intro s world hs z hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  exact hf y.1.1 y.1.2 y.2 (hm s world hs y hy) z hz

theorem keepsFree_get_bind {β : Type} {f : FirstState C σ → FirstM C σ β}
    (hf : ∀ s, SeedsFree s.first → KeepsFree (f s)) : KeepsFree (get >>= f) := by
  intro s world hs z hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  exact hf s hs s world hs z hz

theorem keepsFree_lift {α : Type} (x : StateT (StreamState C) ProbComp α) :
    KeepsFree (C := C) (σ := σ) (StateT.lift x) := by
  intro s world hs z hz
  simp only [StateT.run_lift, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨y, -, rfl⟩ := hz
  exact hs

theorem keepsFree_get : KeepsFree (C := C) (σ := σ) get := by
  intro s world hs z hz
  simp only [StateT.run_get] at hz
  subst hz
  exact hs

theorem keepsFree_set (s' : FirstState C σ) (h : SeedsFree s'.first) : KeepsFree (set s' : FirstM C σ Unit) := by
  intro s world hs z hz
  simp only [StateT.run_set] at hz
  subst hz
  exact h

theorem keepsFree_modify (f : FirstState C σ → FirstState C σ) (h : ∀ s, SeedsFree s.first → SeedsFree (f s).first) :
    KeepsFree (modify f : FirstM C σ Unit) := by
  intro s world hs z hz
  simp only [StateT.run_modify] at hz
  subst hz
  exact h s hs

/-- A computation of the signing phase that keeps `SeedsFree` from each state of the signing game. -/
def KeepsFreeT {α : Type} (m : StateT (TsigState C) (FirstM C σ) α) : Prop := ∀ t, KeepsFree (m.run t)

theorem keepsFreeT_lift {α : Type} {m : FirstM C σ α} (hm : KeepsFree m) :
    KeepsFreeT (StateT.lift m : StateT (TsigState C) (FirstM C σ) α) := fun t => by
  rw [StateT.run_lift]
  exact keepsFree_bind hm fun _ => keepsFree_pure _

theorem keepsFreeT_bind {α β : Type} {m : StateT (TsigState C) (FirstM C σ) α}
    {f : α → StateT (TsigState C) (FirstM C σ) β} (hm : KeepsFreeT m) (hf : ∀ a, KeepsFreeT (f a)) :
    KeepsFreeT (m >>= f) := fun t => by
  rw [StateT.run_bind]
  exact keepsFree_bind (hm t) fun y => hf y.1 y.2

theorem keepsFreeT_simulateQ {ι : Type} {spec : OracleSpec ι} (impl : QueryImpl spec (StateT (TsigState C) (FirstM C σ)))
    (h : ∀ q, KeepsFreeT (impl q)) {α : Type} (oa : OracleComp spec α) : KeepsFreeT (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun t => by rw [simulateQ_pure, StateT.run_pure]; exact keepsFree_pure _
  | query_bind q k ih =>
    intro t
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind]
    exact keepsFree_bind (h q t) fun y => ih y.1 y.2

end Keep

section Game

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Field E] [Algebra Bit E] in
theorem firstTreeRunOf_keepsFree (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (run : RunOf C net.State)
    (ready : RealState C net.State → StreamState C → Prop) (tree : Tree) :
    KeepsFree (firstTreeRunOf prims D net run ready tree) := by
  unfold firstTreeRunOf
  refine keepsFree_get_bind fun s hs => keepsFree_bind (keepsFree_lift _) fun before =>
    keepsFree_bind (keepsFree_lift _) fun r => ?_
  rcases r with ⟨⟨state, outputs⟩, bad⟩
  refine keepsFree_bind (keepsFree_lift _) fun after => keepsFree_bind (keepsFree_lift _) fun v => ?_
  rcases v with ⟨state, ok⟩
  refine keepsFree_set _ ?_
  refine seedsFree_orElse (seedsFree_orElse hs ?_) ?_
  · split_ifs
    · exact seedsFree_none
    · intro w h
      cases h
  · split_ifs
    · intro w h
      cases h
    · exact seedsFree_none

omit [Field E] [Algebra Bit E] in
theorem firstTreeRunsOf_keepsFree (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (run : RunOf C net.State) (ready : RealState C net.State → StreamState C → Prop) (tree : Tree) :
    ∀ count, KeepsFree (firstTreeRunsOf prims runLimit D net run ready tree count)
  | 0 => keepsFree_pure _
  | count + 1 => by
    unfold firstTreeRunsOf
    refine keepsFree_get_bind fun s _ => ?_
    split_ifs
    · exact keepsFree_bind (firstTreeRunOf_keepsFree prims D net run ready tree) fun _ =>
        firstTreeRunsOf_keepsFree D net run ready tree count
    · exact keepsFree_pure _

omit [Field E] [Algebra Bit E] in
theorem firstTreeRequestOf_keepsFree (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (run : RunOf C net.State) (ready : RealState C net.State → StreamState C → Prop) (b : Fin (2 ^ layerHeight)) :
    KeepsFree (firstTreeRequestOf prims runLimit D net run ready b) := by
  unfold firstTreeRequestOf
  refine keepsFree_bind (firstTreeRunsOf_keepsFree prims runLimit D net run ready _ 1) fun _ =>
    keepsFree_get_bind fun s _ => ?_
  split
  · exact keepsFree_bind (keepsFree_lift _) fun _ => keepsFree_pure _
  · exact keepsFree_pure _

/-- `StateT.lift` from the stream world into the game, as a monad map. -/
def streamLift (C : Committee) (σ : Type) : StateT (StreamState C) ProbComp →ᵐ FirstM C σ where
  toFun _ x := StateT.lift x
  toFun_pure' a := StateT.ext fun s => by simp
  toFun_bind' x f := StateT.ext fun s => by simp

/-- The local oracles of the honest operators in the stream world. -/
def streamLocal (D : C.Coalition) {β : Type} (oa : OracleComp (RoSpec C) β) : StateT (StreamState C) ProbComp β :=
  simulateQ (streamWorld prims D) (free (liftComp oa _))

/-- The answer of an honest operator keeps the state of the game. It is `tsigOracles` under the map
`streamLift`. -/
theorem operatorAnswer_keepsFree {σ : Type} (D : C.Coalition) (operators : C.Party → OperatorState C)
    (operator : OperatorState C) (e : KeyIndex) (q : TsigQuery C) :
    KeepsFreeT (operatorAnswer (m := FirstM C σ) (firstLift prims D) (firstValue prims D operators) operator e q) := by
  intro t
  unfold operatorAnswer
  split
  · rename_i keys top _ _ _ _
    rw [ownAnswer_run]
    let value : Point → StateT (StreamState C) ProbComp Digest :=
      fun x => streamLocal prims D (prfValue (gameSeeds D fun i => (operators i).keys) x)
    let dealt := dealtWith (fun oa => streamLocal prims D oa) keys.parameter (fun _ => keys) top value
    have hdealt : SeedHitProof.Dealt.hmap (streamLift C σ) dealt =
        dealtWith (m := FirstM C σ) (fun oa => firstLift prims D oa) keys.parameter (fun _ => keys) top
          (firstValue prims D operators) := by
      simp only [SeedHitProof.Dealt.hmap, dealt, dealtWith, SeedHitProof.hom_map, SeedHitProof.hom_referenceTree]
      rfl
    rw [← hdealt]
    have hom := SeedHitProof.hom_tsigOracles (streamLift C σ) (fun oa => streamLocal prims D oa) dealt q
      { t with trees := fun b => some (operator.bottom b) }
    change KeepsFree ((tsigOracles (fun oa => streamLift C σ (streamLocal prims D oa))
      (SeedHitProof.Dealt.hmap (streamLift C σ) dealt) q).run _)
    rw [← hom]
    exact keepsFree_lift _
  · exact keepsFree_pure _

theorem firstSignRequest_keepsFree (D : C.Coalition) {σ : Type} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    KeepsFreeT (firstSignRequest (σ := σ) prims D i e q) := by
  unfold firstSignRequest
  refine keepsFreeT_bind (keepsFreeT_lift (keepsFree_modify _ fun s hs => hs)) fun _ =>
    keepsFreeT_bind (keepsFreeT_lift keepsFree_get) fun s => ?_
  exact operatorAnswer_keepsFree prims D _ _ e q

omit [Field E] [Algebra Bit E] in
theorem firstOraclesOf_keepsFree (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (run : RunOf C net.State) (ready : RealState C net.State → StreamState C → Prop) (q : TsigQuery C) :
    KeepsFreeT (firstOraclesOf prims runLimit D net run ready q) := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact fun t => keepsFree_pure _
  · exact keepsFreeT_lift (firstTreeRequestOf_keepsFree prims runLimit D net run ready b)
  · exact firstSignRequest_keepsFree prims D i e _
  · exact firstSignRequest_keepsFree prims D i e _

omit [Field E] [Algebra Bit E] in
theorem firstSigningOf_keepsFree (D : C.Coalition) (A : DkgTsigAdversary C E) (run : RunOf C A.net.State)
    (ready : RealState C A.net.State → StreamState C → Prop) :
    KeepsFree (firstSigningOf prims runLimit D A run ready) := by
  unfold firstSigningOf
  refine keepsFree_get_bind fun s _ => ?_
  split
  · refine keepsFree_bind (keepsFreeT_simulateQ _ (fun q => ?_) _ _) fun _ => keepsFree_pure _
    rcases q with t | q | q
    · exact keepsFreeT_lift (keepsFree_lift _)
    · exact firstOraclesOf_keepsFree prims runLimit D A.net run ready q
    · rcases q with _ | state
      · exact keepsFreeT_lift (keepsFree_bind keepsFree_get fun _ => keepsFree_pure _)
      · exact keepsFreeT_lift (keepsFree_modify _ fun s hs => hs)
  · exact keepsFree_pure _

end Game

/-! ## The hop -/

section Hop

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- An event after a continuation that needs the event `q` of the first draw has probability at most
that of `q`. -/
theorem prEvent_bind_le_of_imp {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (p : β → Prop) (q : α → Prop)
    (h : ∀ a, ¬ q a → ∀ z ∈ support (f a), ¬ p z) : Pr{let z ← mx >>= f}[p z] ≤ Pr{let a ← mx}[q a] := by
  refine (prEvent_bind_mono_of_forall_le mx f pure p q fun a => ?_).trans (le_of_eq (by rw [bind_pure]))
  by_cases ha : q a
  · exact (prEvent_le_one _).trans (le_of_eq (by simp [ha]))
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ (h a ha)]
    exact bot_le

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The first record of `firstRunOf` is the seeds with probability at most `seedGenHashError`, for
each run and each readiness test. The record of the seeds comes before each run, so no run is read. -/
theorem seedsHopOf (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ) (run : RunOf C A.net.State)
    (ready : RealState C A.net.State → StreamState C → Prop) (bounded : DkgTsigBounded circuits settings runLimit A q) :
    (Pr{let r ← firstRunOf prims runLimit D A run ready}[∃ world, r.1.first = some (.seeds, world)]).toReal ≤
      seedGenHashError C q := by
  obtain ⟨start, step, forge, hsum, hstart, hround, -⟩ := bounded
  have hrounds : setupRounds * step ≤ dkgTsigRounds circuits settings runLimit * step :=
    Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hq : IsQueryBounded A.net (fun _ => pure true : Distinguisher C A.net.State (Keys C)) setupRounds q :=
    ⟨start, step, 0, by omega,
      fun x z => isQueryBoundP_of_queryCostAtMost (hstart x z) fun _ ht =>
        one_le_ownCost (exists_inClass ht).choose_spec,
      fun st sent => isQueryBoundP_of_queryCostAtMost (hround st sent) fun _ ht =>
        one_le_ownCost (exists_inClass ht).choose_spec,
      fun _ l => l.elim, fun _ => isQueryBoundP_pure _ _ _⟩
  have hc := seedGenConsistent (E := E) prims D A.net (fun _ => ()) [] q hq
  rw [probEvent_runWorld_fst prims _ (fun r : A.net.State × (C.Party → Option (Keys C)) =>
    seedsDiffer D r.2 = true), StateT.run'_eq, prEvent_map] at hc
  unfold firstRunOf
  rw [StateT.run_bind]
  refine (ENNReal.toReal_mono (prEvent_ne_top _) (prEvent_bind_le_of_imp _ _ _
    (fun a => seedsDiffer D a.1.2 = true) ?_)).trans ?_
  · rintro ⟨⟨state, keys⟩, world⟩ hdiffer z hz
    simp only [StateT.run_bind, StateT.run_get, pure_bind, mem_support_bind_iff] at hz
    obtain ⟨t, ht, hz⟩ := hz
    have hsplit := Vote.voteRound_split_run worldRoles D A.net state keys seedVote (streamWorld prims D) world t ht
    have hflag : (seedState D t.1.1 keys t.1.2).flag = false := by
      simpa [seedState, startState, hsplit] using hdiffer
    simp only [hflag, Bool.false_eq_true, ite_false] at hz
    obtain ⟨y, hy, hz⟩ := hz
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    obtain ⟨x, hx, hy⟩ := hy
    have hruns := firstTreeRunsOf_keepsFree prims runLimit D A.net run ready .top runLimit _ _ seedsFree_none x hx
    exact fun ⟨w, hw⟩ => firstSigningOf_keepsFree prims runLimit D A run ready _ _ hruns y hy w hw
  · rw [streamWorld_seedGen, prEvent_map]
    exact hc

omit [Fintype E] [DecidableEq E] in
/-- The first bad event of `firstRunWith` is the seeds with probability at most `seedGenHashError`. -/
theorem seedsHop : SeedsHopW prims K circuits settings runLimit (C := C) (E := E) := by
  intro D A q ready bounded
  unfold firstProbWith firstRunWith
  exact seedsHopOf prims circuits settings runLimit D A q _ ready bounded

end Hop

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.flagFirstHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.flagFirstHop

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.seedsHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.seedsHop
