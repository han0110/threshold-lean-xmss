import ThresholdLeanXmss.Scheme
import LeanXmss.Statement

/-!
# The functionalities and the games

The functionalities of GS20 for replicated sharing, the trusted dealer `F_KeyGen`, and the games of
PRAWNS and of the primitives, which the claims of `Statement.lean` use.
-/

open OracleComp OracleSpec LeanXmss

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- `0` as the default element of the check field. -/
@[reducible] def inhabitedField : Inhabited E := ⟨0⟩

attribute [local instance] inhabitedField

/-! ## Functionalities of GS20 for replicated sharing -/

section Functionalities

variable {I O L R : Type}

/-- A leak to the adversary and its reply. -/
def leak (l : L) : OracleComp (LocalSpec C + (L →ₒ R)) R :=
  OracleComp.lift (OracleSpec.query (spec := LocalSpec C + (L →ₒ R)) (Sum.inr l))

/-- A uniform sample. -/
def sample (β : Type) [SampleableType β] : OracleComp (LocalSpec C + (L →ₒ R)) β := liftComp ($ᵗ β) _

/-- A term that some operator of `D` holds. -/
def KnownTo (D : Finset C.Party) (T : C.Term) : Prop := ∃ j ∈ D, j ∈ C.holders T

/-- The first term that no operator of `D` holds. It exists when `D` is a coalition. -/
def lackedTerm (D : Finset C.Party) : Option C.Term := C.terms.find? fun T => ¬ KnownTo D T

/-- Each term from its first honest holder. -/
def reconstruct {α : Type} [Inhabited α] (views : C.Party → Option (C.Term → α)) : C.Term → α := fun T =>
  ((C.parties.filterMap fun i => if i ∈ C.holders T then views i else none).head?.map (· T)).getD default

/-- The value of a replicated sharing at position `g`. -/
def shareValue {R : Type} [AddCommMonoid R] (v : Shares C R) (g : ℕ) : R := ∑ T, v T g

/-- The honest holders of term `T` agree on it. -/
def ConsistentAt {α : Type} (D : C.Coalition) (views : C.Party → C.Term → α) (T : C.Term) : Prop :=
  ∀ i ∈ C.holders T, ∀ j ∈ C.holders T, i ∉ D.1 → j ∉ D.1 → views i T = views j T

/-- The honest holders of each term agree on it. -/
def Consistent {α : Type} (D : C.Coalition) (views : C.Party → C.Term → α) : Prop :=
  ∀ T, ConsistentAt D views T

/-- The first honest input. -/
def firstInput [Inhabited I] (inputs : C.Party → Option I) : I := (C.parties.filterMap inputs).headD default

/-- The terms of a replicated sharing of `count` positions that the corrupt operators know, and zero
elsewhere. -/
def knownView {R : Type} [Zero R] (D : Finset C.Party) (count : ℕ) (v : Shares C R) : Shares C R :=
  fun T g => if KnownTo D T ∧ g < count then v T g else 0

/-- `F_rand` (GS20, Functionality 1) for `count` positions, with the pair streams of a zero sharing
(CDI05). The adversary chooses the terms and the pair streams that a corrupt operator knows. -/
def Frand (R : Type) [AddCommGroup R] [SampleableType R] :
    Functionality C ℕ (PrssOutput C R) Unit (Shares C R × (C.Party → C.Party → ℕ → R)) where
  run coalition inputs := do
    let D := coalition.1
    let count := firstInput inputs
    let (known, knownPairs) ← leak ()
    let fresh ← sample (C.Term → Fin count → R)
    let freshPair ← sample (C.Pair → Fin count → R)
    let extend := fun (v : Fin count → R) (g : ℕ) => if h : g < count then v ⟨g, h⟩ else 0
    let r : Shares C R := fun T => if KnownTo D T then known T else extend (fresh T)
    let Z : C.Party → C.Party → ℕ → R := fun i j =>
      if h : i = j then fun _ => 0 else if j ∈ D then knownPairs j i else extend (freshPair (C.pairOf i j h))
    pure fun i => if i ∈ D then none else some (fun T => if i ∈ C.holders T then r T else fun _ => 0, Z i)

/-- `F_coin` (GS20, Functionality 5) for `count` values, with selective abort. -/
def Fcoin [SampleableType E] : Functionality C ℕ (List E) (List E) (Finset C.Party) where
  run coalition inputs := do
    let D := coalition.1
    let count := firstInput inputs
    let values ← sample (Fin count → E)
    let receivers ← leak (List.ofFn values)
    pure fun i => if i ∉ D ∧ i ∈ receivers then some (List.ofFn values) else none

/-- `F_mult` (GS20, Functionalities 7 and 9) with a replicated output. The product is the sum of the
additive shares `share i` of the honest operators from their own views, plus the additive attack
`d`, which also absorbs the shares of the corrupt operators (KPPS23, CGH+18). The adversary chooses
the terms that a corrupt operator holds. A corrupt operator that fills a term at a position gives
each honest holder its own copy by `offset`. Each honest operator gets only its held terms at the
`count` positions, and zero elsewhere. The adversary names the honest receivers, and the others abort
(GL05). -/
def Fmult {In Lk : Type} [Inhabited In] [Field R] [SampleableType R] (count : In → ℕ)
    (filled : In → C.Term → ℕ → Option C.Party) (share : C.Party → In → ℕ → R)
    (view : Finset C.Party → (C.Party → Option In) → Lk) :
    Functionality C In (Shares C R) Lk ((ℕ → R) × Shares C R × (C.Party → Shares C R) × Finset C.Party) where
  run coalition inputs := do
    let D := coalition.1
    let input := firstInput inputs
    let width := count input
    let (d, known, offset, receivers) ← leak (view D inputs)
    let fresh ← sample (C.Term → Fin width → R)
    let base : Shares C R := fun T g =>
      if KnownTo D T then known T g else if h : g < width then fresh T ⟨g, h⟩ else 0
    let product := fun g => ∑ i ∈ Finset.univ.filter (· ∉ D), ((inputs i).map fun x => share i x g).getD 0
    let z : Shares C R := fun T g => if lackedTerm D = some T then
      product g + d g - ∑ T' ∈ Finset.univ.erase T, base T' g else base T g
    pure fun i => if i ∈ D ∨ i ∉ receivers then none else
      some fun T g => if i ∈ C.holders T ∧ g < width then
        z T g + (if ∃ j ∈ D, filled input T g = some j then offset i T g else 0) else 0

/-- `F_mult` for the AND gates in `mode`, on `([[x]], [[y]], count)`. It leaks the count, which the
lengths of the real messages show, and the view of each honest operator of the terms that the
corrupt operators know. -/
def FmultBit (K : Constants C E) (mode : ReshareMode) :
    Functionality C (Shares C Bit × Shares C Bit × ℕ) (Shares C Bit)
      (ℕ × (C.Party → Option (Shares C Bit × Shares C Bit))) ((ℕ → Bit) × Shares C Bit × (C.Party → Shares C Bit) × Finset C.Party) :=
  Fmult (·.2.2) (fun _ => filler K mode) (fun i x => mulRep K (localContext i) x.1 x.2.1)
    (fun D inputs => ((firstInput inputs).2.2, fun i => if i ∈ D then none else
      (inputs i).map fun x => (knownView D x.2.2 x.1, knownView D x.2.2 x.2.1)))

/-- The kind and the length of an inner product. -/
def Product.shape : Product C E → Bool × ℕ
  | .replicated _ _ count => (true, count)
  | .shamir _ _ count => (false, count)

def Product.replicatedParts : Product C E → Shares C E × Shares C E
  | .replicated x y _ => (x, y)
  | .shamir .. => (fun _ _ => 0, fun _ _ => 0)

def Product.shamirParts : Product C E → (ℕ → E) × (ℕ → E)
  | .shamir x y _ => (x, y)
  | .replicated .. => (fun _ => 0, fun _ => 0)

/-- The Lagrange weight of `α_l` at `x` among the points of `S`. -/
def lagrangeAt (K : Constants C E) (S : Finset C.Party) (x : E) (l : C.Party) : E :=
  ∏ k ∈ S.erase l, (x - K.point k) / (K.point l - K.point k)

/-- The value at `x` of the polynomial through the shares of the first `t` honest operators. -/
def interpolate (K : Constants C E) (D : Finset C.Party) (share : C.Party → E) (x : E) : E :=
  let S := ((C.parties.filter (· ∉ D)).take C.t).toFinset
  ∑ l ∈ S, lagrangeAt K S x l * share l

/-- `F_extendMult` (GS20, Functionality 9) for inner products. It leaks to each corrupt operator only
its own shares, namely its Shamir shares and its known terms. -/
def FextendMult [SampleableType E] (K : Constants C E) : Functionality C (List (Product C E)) (Shares C E)
    (C.Party → List (Product C E)) ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party) :=
  Fmult List.length (fun _ => filler K .peer)
    (fun i products g => match products[g]? with | some p => productShare K (localContext i) p | none => 0)
    (fun D inputs c =>
      if c ∉ D then [] else (firstInput inputs).zipIdx.map fun (p, g) =>
        let entry := fun i => (inputs i).bind (·[g]?)
        match p with
        | .replicated _ _ count =>
            .replicated (knownView D count (reconstruct fun i => (entry i).map (·.replicatedParts.1)))
              (knownView D count (reconstruct fun i => (entry i).map (·.replicatedParts.2))) count
        | .shamir _ _ count =>
            .shamir (fun k => if k < count then
                interpolate K D (fun i => (((entry i).map (·.shamirParts.1)).getD fun _ => 0) k) (K.point c) else 0)
              (fun k => if k < count then
                interpolate K D (fun i => (((entry i).map (·.shamirParts.2)).getD fun _ => 0) k) (K.point c) else 0)
              count)

/-- Tuple `k` of the honest views, each term from its first honest holder. -/
def tupleAt (views : C.Party → Option (List (Tuple C))) (k : ℕ) : Tuple C :=
  let at_ := fun i => (views i).bind (·[k]?)
  ⟨reconstruct fun i => (at_ i).map (·.x), reconstruct fun i => (at_ i).map (·.y),
    reconstruct fun i => (at_ i).map (·.z), (((firstInput views)[k]?).map (·.count)).getD 0,
    (((firstInput views)[k]?).map (·.mode)).getD .peer⟩

/-- `F_multVerify` (GS20, Functionality 16) with selective abort. It accepts when the honest holders
agree on every copy (KPPS23, `Π_agree`, and CGH+18, Protocol 3.3) and every tuple is a product. It
leaks the view of each honest operator of the terms that the corrupt operators know. It leaks the
differences `z - x y` only when the copies agree, because reconstructed values of split copies can
depend on secrets. -/
def FmultVerify : Functionality C (List (Tuple C)) Unit
    ((C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool) (Finset C.Party) where
  run coalition inputs := do
    let D := coalition.1
    let count := (firstInput inputs).length
    let tuples := (List.range count).map (tupleAt inputs)
    let differences := tuples.map fun τ g =>
      if g < τ.count then shareValue τ.z g - shareValue τ.x g * shareValue τ.y g else 0
    let agree := ∀ k < count, ∀ T, ∀ i ∈ C.holders T, ∀ j ∈ C.holders T, i ∉ D → j ∉ D →
      ∀ g < (tuples.getD k ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, 0, .peer⟩).count,
        ((inputs i).bind (·[k]?)).map (fun τ => (τ.x T g, τ.y T g, τ.z T g)) =
          ((inputs j).bind (·[k]?)).map fun τ => (τ.x T g, τ.y T g, τ.z T g)
    let accept := decide (agree ∧ ∀ τ ∈ tuples, ∀ g < τ.count, shareValue τ.z g = shareValue τ.x g * shareValue τ.y g)
    let known := fun i => if i ∈ D then none else (inputs i).map fun views =>
      views.map fun τ => (⟨knownView D τ.count τ.x, knownView D τ.count τ.y, knownView D τ.count τ.z, τ.count, τ.mode⟩ : Tuple C)
    let receivers ← leak (known, (if agree then differences else []), accept)
    pure fun i => if i ∉ D ∧ accept ∧ i ∈ receivers then some () else none

/-- The value of the input wires of a job, from the honest views. -/
def inputValue (input : C.Term → List Bit) : List Bit :=
  (List.range ((C.terms.map fun T => (input T).length).foldl max 0)).map fun g => ∑ T, (input T).getD g 0

/-- `F_main` (GS20, Functionality 18) for the circuits of a run on replicated inputs, with selective
abort. It leaks the terms that the corrupt operators know in the view of each honest operator, and
every output. -/
def Fmain (jobs : List Circuit) : Functionality C (List (C.Term → List Bit)) (List (List Bit))
    ((C.Party → Option (List (C.Term → List Bit))) × List (List Bit)) (Finset C.Party) where
  run coalition inputs := do
    let D := coalition.1
    let input := fun k => reconstruct fun i => (inputs i).bind (·[k]?)
    let outputs := jobs.zipIdx.map fun (job, k) => job.eval (inputValue (input k))
    let known := fun i => if i ∈ D then none else
      (inputs i).map fun views => views.map fun v T => if KnownTo D T then v T else []
    let receivers ← leak (known, outputs)
    pure fun i => if i ∉ D ∧ i ∈ receivers then some outputs else none

/-- The sum of two functionalities. All honest operators call the same one. -/
def Functionality.sum {I₁ O₁ L₁ R₁ I₂ O₂ L₂ R₂ : Type} [Inhabited R₁] [Inhabited R₂]
    (F₁ : Functionality C I₁ O₁ L₁ R₁) (F₂ : Functionality C I₂ O₂ L₂ R₂) :
    Functionality C (I₁ ⊕ I₂) (O₁ ⊕ O₂) (L₁ ⊕ L₂) (R₁ ⊕ R₂) where
  run coalition inputs :=
    let left : QueryImpl (LocalSpec C + (L₁ →ₒ R₁)) (OracleComp (LocalSpec C + (L₁ ⊕ L₂ →ₒ R₁ ⊕ R₂))) :=
      (fun t => OracleComp.lift (OracleSpec.query (spec := LocalSpec C + (L₁ ⊕ L₂ →ₒ R₁ ⊕ R₂)) (Sum.inl t))) +
      (fun (l : L₁) => do
        match ← leak (C := C) (R := R₁ ⊕ R₂) (Sum.inl l : L₁ ⊕ L₂) with
        | .inl r => pure r
        | .inr _ => pure default)
    let right : QueryImpl (LocalSpec C + (L₂ →ₒ R₂)) (OracleComp (LocalSpec C + (L₁ ⊕ L₂ →ₒ R₁ ⊕ R₂))) :=
      (fun t => OracleComp.lift (OracleSpec.query (spec := LocalSpec C + (L₁ ⊕ L₂ →ₒ R₁ ⊕ R₂)) (Sum.inl t))) +
      (fun (l : L₂) => do
        match ← leak (C := C) (R := R₁ ⊕ R₂) (Sum.inr l : L₁ ⊕ L₂) with
        | .inr r => pure r
        | .inl _ => pure default)
    if ∀ i, ∀ x ∈ inputs i, x.isLeft then
      (fun out i => (out i).map Sum.inl) <$> simulateQ left (F₁.run coalition fun i => (inputs i).bind Sum.getLeft?)
    else if ∀ i, ∀ x ∈ inputs i, x.isRight then
      (fun out i => (out i).map Sum.inr) <$> simulateQ right (F₂.run coalition fun i => (inputs i).bind Sum.getRight?)
    else pure fun _ => none

end Functionalities

/-! ## The trusted dealer -/

instance : Inhabited (Keys C) := ⟨⟨0, fun _ => 0, fun _ => 0⟩⟩

/-- `F_keygen`, the trusted dealer of PRAWNS `KeyGen'` with selective abort. It leaks `P` and the
corrupt keys, and the adversary names the honest receivers. -/
def Fkeygen : Functionality C Unit (Keys C) (PublicParameter × (C.Party → Option (Keys C))) (Finset C.Party) where
  run coalition _ := do
    let D := coalition.1
    let (parameter, _, keys) ← liftComp prawnsKeyGen _
    let receivers ← leak (parameter, fun i => if i ∈ D then some (keys i) else none)
    pure fun i => if i ∉ D ∧ i ∈ receivers then some (keys i) else none

/-- The dealer computes a ceremony in the clear with the circuits, and logs the openings of each
batch. -/
def dealerCeremony (circuits : Circuits) (settings : Settings) (parameter : PublicParameter)
    (seed : C.Term → HashOutput) (top : TopTree) (tree : Tree) :
    OracleComp (RoSpec C) (Option TreeOutput × List (List (List Bit))) :=
  (ceremonyOutput (m := WriterT (List (List (List Bit))) (OracleComp (RoSpec C))) (fun oa => liftM (tweakable (C := C) oa))
    parameter (batched settings.batchSize fun jobs => do
      let outputs ← liftM (jobs.mapM (evalJob circuits parameter seed))
      tell [outputs]
      pure (some outputs)) top tree).run

/-- `F_tree`, one ceremony with selective abort. It takes the keys of the honest operators, computes
the tree in the clear with the circuits on the seeds of the honest holders, and leaks `P` and the
openings of each batch, as GS20, Functionality 18, opens every output. -/
def Ftree (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree) :
    Functionality C (Keys C) TreeOutput (PublicParameter × List (List (List Bit))) (Finset C.Party) where
  run coalition inputs := do
    let D := coalition.1
    let parameter := (firstInput inputs).parameter
    let seeds : C.Term → HashOutput := fun T => (C.parties.findSome? fun i =>
      if i ∈ C.holders T then (inputs i).map (·.seed T) else none).getD 0
    let (output, openings) ← liftComp (dealerCeremony circuits settings parameter seeds top tree) _
    let receivers ← leak (parameter, openings)
    pure fun i => if i ∉ D ∧ i ∈ receivers then output else none

/-! ## The functionalities of each claim -/

/-- The honest operators agree on the count. -/
def SameCount (D : C.Coalition) (x : C.Party → ℕ) : Prop := ∀ i j, i ∉ D.1 → j ∉ D.1 → x i = x j

/-- The reply of an honest adversary to `F_rand`. -/
def randReply (R : Type) [Zero R] : Unit → Shares C R × (C.Party → C.Party → ℕ → R) := fun _ => (0, 0)

/-- The functionalities of the check. -/
def checkFunctionalities [SampleableType E] (K : Constants C E) :
    Functionality C ((ℕ ⊕ List (Product C E)) ⊕ (ℕ ⊕ ℕ)) ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit))
      ((List E ⊕ (C.Party → List (Product C E))) ⊕ (Unit ⊕ Unit))
      ((Finset C.Party ⊕ ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)) ⊕
        ((Shares C E × (C.Party → C.Party → ℕ → E)) ⊕ (Shares C Bit × (C.Party → C.Party → ℕ → Bit)))) :=
  ((Fcoin (E := E)).sum (FextendMult K)).sum ((Frand E).sum (Frand Bit))

/-- The reply of an honest adversary to the functionalities of the check. -/
def checkReply : (List E ⊕ (C.Party → List (Product C E))) ⊕ (Unit ⊕ Unit) →
    (Finset C.Party ⊕ ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)) ⊕
      ((Shares C E × (C.Party → C.Party → ℕ → E)) ⊕ (Shares C Bit × (C.Party → C.Party → ℕ → Bit)))
  | .inl (.inl _) => .inl (.inl Finset.univ)
  | .inl (.inr _) => .inl (.inr (0, 0, 0, Finset.univ))
  | .inr (.inl _) => .inr (.inl (0, 0))
  | .inr (.inr _) => .inr (.inr (0, 0))

/-- The functionalities of a batch, namely `F_mult` of the AND gates in `mode`, `F_mult` in peer mode
for `Rerand`, and `F_multVerify`. -/
def mainFunctionalities (K : Constants C E) (mode : ReshareMode) :=
  ((FmultBit K mode).sum (FmultBit K .peer)).sum (FmultVerify (C := C))

/-- The reply of an honest adversary to the functionalities of a batch. -/
def mainReply : ((ℕ × (C.Party → Option (Shares C Bit × Shares C Bit))) ⊕
      (ℕ × (C.Party → Option (Shares C Bit × Shares C Bit)))) ⊕
      ((C.Party → Option (List (Tuple C))) × List (ℕ → Bit) × Bool) →
    (((ℕ → Bit) × Shares C Bit × (C.Party → Shares C Bit) × Finset C.Party) ⊕ ((ℕ → Bit) × Shares C Bit × (C.Party → Shares C Bit) × Finset C.Party)) ⊕
      Finset C.Party
  | .inl (.inl _) => .inl (.inl (0, 0, 0, Finset.univ))
  | .inl (.inr _) => .inl (.inr (0, 0, 0, Finset.univ))
  | .inr _ => .inr Finset.univ

/-! ## The PRF game of the streams -/

/-- A PRSS key that the coalition does not know, namely the key of a term with no corrupt holder or
of a pair of honest operators. -/
def Hidden (D : C.Coalition) : KeyName C → Prop
  | .parameter => False
  | .term T => ¬ KnownTo D.1 T
  | .pair p => p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1

instance : Fintype (KeyName C) :=
  Fintype.ofEquiv (Unit ⊕ C.Term ⊕ C.Pair)
    ⟨fun | .inl () => .parameter | .inr (.inl T) => .term T | .inr (.inr p) => .pair p,
     fun | .parameter => .inl () | .term T => .inr (.inl T) | .pair p => .inr (.inr p),
     fun x => by rcases x with u | T | p <;> rfl, fun x => by cases x <;> rfl⟩

/-- The streams under the hidden keys, with one independent AES-128 key for each named key. -/
def hiddenStreams (aes : Aes) :
    PRFScheme (KeyName C × HashOutput → Digest) ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) Bit where
  keygen := $ᵗ (KeyName C × HashOutput → Digest)
  eval keys input := aes.eval (keys input.1) input.2

/-! ## The threshold PRF game -/

variable (prims : Primitives)

/-- The oracles of PRAWNS, Figure 1, namely `OCorrupt`, `OEval` with the quorum, and `OChallenge`. -/
inductive TprfQuery (C : Committee)
  | corrupt (i : C.Party)
  | eval (i : C.Party) (J : C.Quorum) (x : Point) (ec : Message)
  | challenge (x : Point)

def TprfSpec (C : Committee) : OracleSpec (TprfQuery C)
  | .corrupt _ => Option (Keys C)
  | .eval .. => Option Digest
  | .challenge _ => Option Digest

/-- An adversary against the threshold PRF. -/
abbrev TprfAdversary (C : Committee) := OracleComp (LocalSpec C + TprfSpec C) Bool

structure TprfState (C : Committee) where
  corrupt : Finset C.Party
  /-- `Q[x, ec]`, the operators that gave a share of `x` under `ec`. -/
  queried : Point → Message → Finset C.Party
  challenged : Finset Point
  /-- The random function `f` on the challenged points. -/
  random : Point → Option Digest

/-- The oracles of PRAWNS, Figure 1. `b = false` answers a challenge with `F(msk, x)` and
`b = true` with a random function. -/
def tprfOracles (keys : C.Party → Keys C) (seeds : C.Term → HashOutput) (b : Bool) :
    QueryImpl (TprfSpec C) (StateT (TprfState C) (OracleComp (WorldSpec C))) := fun q =>
  match q with
  | .corrupt i => do
      let st ← get
      if ∃ x ∈ st.challenged, ∃ ec, C.t ≤ (st.corrupt ∪ st.queried x ec ∪ {i}).card then pure none else do
        set { st with corrupt := insert i st.corrupt }
        pure (some (keys i))
  | .eval i J x ec => do
      let st ← get
      if i ∉ J.1 ∨ (C.t ≤ (st.corrupt ∪ st.queried x ec ∪ {i}).card ∧ x ∈ st.challenged) then pure none else do
        set { st with queried := Function.update st.queried x (Function.update (st.queried x) ec (insert i (st.queried x ec))) }
        some <$> StateT.lift (free (C := C) (liftComp (eval (keys i) i J x ec) (LocalSpec C)))
  | .challenge x => do
      let st ← get
      if ∃ ec, C.t ≤ (st.corrupt ∪ st.queried x ec).card then pure none else do
        let y ← if b then match st.random x with
            | some y => pure y
            | none => StateT.lift (free (C := C) (liftComp ($ᵗ Digest) (LocalSpec C)))
          else StateT.lift (free (C := C) (liftComp (prfValue seeds x) (LocalSpec C)))
        set { st with challenged := insert x st.challenged, random := Function.update st.random x (some y) }
        pure (some y)

/-- The game `G^tprf` of PRAWNS, Figure 1, with `KeyGen'` of PRAWNS, Section 5.1. -/
def tprfGame (A : TprfAdversary C) (b : Bool) : OracleComp (WorldSpec C) Bool := do
  let (_, seeds, keys) ← free (liftComp (prawnsKeyGen (C := C)) _)
  let forward : QueryImpl (LocalSpec C) (StateT (TprfState C) (OracleComp (WorldSpec C))) :=
    fun t => StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))
  (simulateQ (forward + tprfOracles keys seeds b) A : StateT (TprfState C) (OracleComp (WorldSpec C)) Bool).run'
    ⟨∅, fun _ _ => ∅, ∅, fun _ => none⟩

/-- `Adv^tprf`, PRAWNS, Definition 2.2. -/
def tprfAdvantage (A : TprfAdversary C) : ℝ :=
  |accepts prims (tprfGame A false) - accepts prims (tprfGame A true)|

/-! ## The signing game -/

/-- The oracles of PRAWNS, Figure 3, namely `OCorrupt`, the public outputs of a bottom tree, and the
two rounds of `OSign` with the quorum. A tree also gives the opened randomizer value of its top key. -/
inductive TsigQuery (C : Committee)
  | corrupt (i : C.Party)
  | tree (b : Fin (2 ^ layerHeight))
  | round1 (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message)
  | round2 (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) (parts : C.Party → Digest)

def TsigSpec (C : Committee) : OracleSpec (TsigQuery C)
  | .corrupt _ => Option (Keys C)
  | .tree _ => Option (BottomTree × Digest)
  | .round1 .. => Option Digest
  | .round2 .. => Option (ChainIndex → Option Digest)

/-- A forger. It gets the public key and the top tree, the hash, and the oracles. -/
abbrev TsigAdversary (C : Committee) := PublicKey → TopTree → OracleComp (LocalSpec C + TsigSpec C) Forgery

structure TsigState (C : Committee) where
  corrupt : Finset C.Party
  /-- The one message that the honest operators sign at a key, over all quorums and aborts. -/
  bound : KeyIndex → Option Message
  /-- The honest operators that sent chain parts at a key for a message. -/
  released : List (KeyIndex × Message × C.Party)
  /-- The randomizer values that honest signers accepted. -/
  opened : List (KeyIndex × Digest)

/-- The operators that can give a chain part at key `e` for `message`, namely the corrupt operators
and the honest operators that released one. -/
def signersAt (st : TsigState C) (e : KeyIndex) (message : Message) : Finset C.Party :=
  st.corrupt ∪ ((st.released.filter fun r => r.1 = e ∧ r.2.1 = message).map (·.2.2)).toFinset

/-- The message at key `e` whose chain parts reached `t` operators, the `m'` of PRAWNS, Theorem 3.1,
Game 2. -/
def exposedMessage (st : TsigState C) (e : KeyIndex) : Option Message :=
  ((st.released.filter (·.1 = e)).map (·.2.1)).find? fun m => C.t ≤ (signersAt st e m).card

variable {m : Type → Type} [Monad m]

/-- The signing oracles. Corruption is adaptive and stops at `t - 1` operators. At each key, honest
operators sign one message only (`doc/sign.md`, Section 4, in place of line 8 of Figure 3). -/
def tsigOracles (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) (dealt : Dealt C m) :
    QueryImpl (TsigSpec C) (StateT (TsigState C) m) := fun q =>
  match q with
  | .corrupt i => do
      let st ← get
      if C.t - 1 < (insert i st.corrupt).card then pure none else do
        set { st with corrupt := insert i st.corrupt }
        pure (some (dealt.keys i))
  | .tree b => do
      let some tree ← liftM (dealt.bottom b) | pure none
      pure (some (tree, ← liftM (dealt.value (.randomizer topLayer (topKey b)))))
  | .round1 i J e message => do
      let st ← get
      if i ∈ st.corrupt ∨ i ∉ J.1 ∨ (st.bound e).any (· ≠ message) then pure none else do
        set { st with bound := Function.update st.bound e (some message) }
        some <$> liftM (dealt.part i J (.randomizer bottomLayer e) message)
  | .round2 i J e message parts => do
      let st ← get
      if i ∈ st.corrupt ∨ i ∉ J.1 ∨ st.bound e ≠ some message then pure none else do
        let some tree ← liftM (dealt.bottom (treeOf e)) | pure none
        let own ← liftM (dealt.part i J (.randomizer bottomLayer e) message)
        let parts := Function.update parts i own
        let some values ← liftM (signRound2With lift (fun x => dealt.part i J x message) dealt.parameter J
            (tree.commitment e) e message parts) | pure none
        set { st with released := st.released ++ [(e, message, i)], opened := st.opened ++ [(e, combine J parts)] }
        pure (some values)

/-- The game of PRAWNS, Figure 3, for strong unforgeability. A verified forgery wins if fewer than
`t` operators can give chain parts at its key for its message. It also wins if it differs from the
signature of `KeyGen` there. Strong unforgeability goes beyond PRAWNS and matches leanVM. -/
def tsigGameWith (Ro : Roles C m) (dealt : Dealt C m) (A : TsigAdversary C) :
    m (Bool × TsigState C × Forgery) := do
  let lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β := fun oa => Ro.honest (liftComp oa _)
  let forger : QueryImpl (LocalSpec C) (StateT (TsigState C) m) := fun t => liftM (Ro.adversary (OracleComp.lift (OracleSpec.query t)))
  let (forgery, st) ← (simulateQ (forger + tsigOracles lift dealt) (A ⟨dealt.top.root, dealt.parameter⟩ dealt.top)).run
    ⟨∅, fun _ => none, [], []⟩
  let verified ← lift (tweakable (Concrete.verify ⟨dealt.top.root, dealt.parameter⟩ forgery.message forgery.signature))
  let fresh ← if (signersAt st forgery.signature.leafIndex forgery.message).card < C.t then pure true else do
    let honest ← honestSignature lift dealt forgery.signature.leafIndex forgery.message
    pure (decide (honest ≠ some forgery.signature))
  pure (verified && fresh, st, forgery)

/-- The game `G^tsig` of PRAWNS, Figure 3. -/
def tsigGame (A : TsigAdversary C) : OracleComp (WorldSpec C) Bool := do
  let some dealt ← keyGen | pure false
  (·.1) <$> tsigGameWith worldRoles dealt A

/-- `Adv^tsig`, PRAWNS, Definition 3.2. -/
def tsigAdvantage (A : TsigAdversary C) : ℝ := accepts prims (tsigGame A)

/-! ## The games of the primitives -/

/-- The guesses of Game 2 of Theorem 3.1, namely a layer, a key, a chain and a position. -/
def guessCount : ℕ := numLayers * lifetime * numChains * (chainLength - 1)

/-- The position `j` of the target of Game 2, from `1` to `3`. -/
abbrev Guess := Layer × KeyIndex × ChainIndex × Fin (chainLength - 1)

instance : Nonempty Guess :=
  ⟨(⟨0, by decide⟩, ⟨0, by unfold lifetime; exact Nat.two_pow_pos _⟩, ⟨0, by decide⟩, ⟨0, by decide⟩)⟩

instance : SampleableType Guess := SampleableType.ofFintype Guess

/-- `Adv^spr`, PRAWNS, Definition 3.3, for the chains of leanXMSS. The task is to find `x'` at
position `j - 1` whose chain reaches `f^3(x)`, given `y = f^j(x)` on a uniform chain under a uniform
parameter. The tweak of the chain plays the key of the keyed hash of PRAWNS, Remark 1. -/
abbrev SprAdversary (C : Committee) := PublicParameter → Guess → Digest → OracleComp (LocalSpec C) Digest

def sprGame (B : SprAdversary C) : OracleComp (WorldSpec C) Bool := do
  let parameter ← free (liftComp ($ᵗ PublicParameter) _)
  let guess ← free (liftComp ($ᵗ Guess) _)
  let (lay, e, l, j) := guess
  let x ← free (liftComp ($ᵗ Digest) _)
  let walk := fun start steps value => free (liftComp (tweakable (C := C) (Concrete.chainWalk parameter lay e l start steps value)) _)
  let y ← walk 0 (j.val + 1) x
  let x' ← worldRoles.adversary (B parameter guess y)
  pure (decide ((← walk j.val (chainLength - 1 - j.val) x') = (← walk 0 (chainLength - 1) x)))

def sprAdvantage (B : SprAdversary C) : ℝ := accepts prims (sprGame B)

/-- `Adv` of collision resistance of the fixed `Th`, which gives two different inputs that the MPC
evaluates, namely chain steps or commitments, with one truncated output. -/
abbrev CollisionAdversary (C : Committee) := OracleComp (LocalSpec C) (HashInput × HashInput)

def collisionGame (B : CollisionAdversary C) : OracleComp (WorldSpec C) Bool := do
  let (a, b) ← worldRoles.adversary B
  let ha ← free (liftComp (hashQuery (C := C) (.hash a)) _)
  let hb ← free (liftComp (hashQuery (C := C) (.hash b)) _)
  pure (decide (a ≠ b ∧ MpcInput a ∧ MpcInput b ∧ truncateHash ha = truncateHash hb))

def collisionAdvantage (B : CollisionAdversary C) : ℝ := accepts prims (collisionGame B)

end ThresholdLeanXmss
