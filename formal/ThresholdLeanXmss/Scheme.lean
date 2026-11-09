import LeanXmss.Scheme
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.QueryTracking.WriterCost
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.EvalDist.TVDist

/-!
# Threshold leanXMSS

The key generation of `doc/dkg.md` and the signing of `doc/sign.md`, as programs of one operator, at
the level of GS20 and PRAWNS. The end of the file holds the execution model, the programs in the
hybrid models of GS20, and the honest runs that the claims compare.

* An operator program is an `OracleComp` with private sampling, the oracle `H` and one query
  `exchange` for each synchronous round. A program that returns `none` aborts.
* A program in a hybrid model also has a query `call` to the functionality (GS20, Section 3.1).
* Each use of `H` has its own domain. The implementation separates the uses by tags and lengths, so
  its inputs map to these domains one to one (BR93).
* The domain `hash` is the tweakable hash `Th` of leanXMSS. On the inputs that the MPC evaluates,
  namely a chain step and the commitment `c_e`, it is one fixed function. Every other input of `Th`,
  namely a leaf, a node and a message digest, and every other domain are a random oracle.
* `PRG(key, ρ, idx)` is AES-128 under `H(key)` truncated to 128 bits, as in the implementation.
* Messages carry values, not bytes. Every encoding of the implementation is injective, so it does
  not change a view.
* A run splits its jobs into batches of `batchSize` jobs. Each batch is one run of the protocol of
  GS20, Protocol 19, with its own check and fresh running digests.
* The AND gates reshare in peer mode or in collector mode. `Rerand` and the check use peer mode.
* The digests travel in their own round before the last coin. The implementation sends them with
  that coin, which saves one round and changes no message.
* The session nonces and the commitment of the PRSS setup in the nonce round are not modeled. Fresh
  PRSS parts in each ceremony separate the sessions.
-/

open OracleComp OracleSpec LeanXmss

noncomputable section

namespace ThresholdLeanXmss

abbrev Bit := ZMod 2

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ## Operators and terms -/

/-- `n = 2t - 1` operators. Any `t` of them sign, and at most `t - 1` are corrupt. -/
structure Committee where
  t : ℕ
  one_le_t : 1 ≤ t

namespace Committee

variable (C : Committee)

def n : ℕ := 2 * C.t - 1

abbrev Party := Fin C.n

/-- A term is a set of `t - 1` operators. The `t` operators outside it hold it. -/
abbrev Term := {T : Finset C.Party // T.card = C.t - 1}

def holders (T : C.Term) : Finset C.Party := T.1ᶜ

/-- At most `t - 1` corrupt operators. -/
abbrev Coalition := {D : Finset C.Party // D.card ≤ C.t - 1}

/-- `t` operators that sign together. -/
abbrev Quorum := {J : Finset C.Party // J.card = C.t}

/-- An unordered pair of distinct operators. It shares one key `K_ij`. -/
abbrev Pair := {p : C.Party × C.Party // p.1 < p.2}

/-- The pair of two distinct operators. -/
def pairOf (i j : C.Party) (h : i ≠ j) : C.Pair :=
  if hij : i < j then ⟨(i, j), hij⟩ else ⟨(j, i), lt_of_le_of_ne (not_lt.mp hij) h.symm⟩

/-- All terms, in one fixed order that every operator uses. -/
def terms : List C.Term := (Finset.univ : Finset C.Term).toList

/-- All operators, in operator order. -/
def parties : List C.Party := List.finRange C.n

end Committee

/-! ## Public constants -/

/-- The bits of an element of the check field. -/
def elementBits : ℕ := 192

/-- A word of the check holds `2 ^ wordBits` tuples. -/
def wordBits : ℕ := 6

/-- The check folds `2 ^ sliceBits` slices with the slice steps. -/
def sliceBits : ℕ := 7

/-- The public constants of a committee (`doc/dkg.md` 1.1.3). Every choice with these properties is
allowed. -/
structure Constants (C : Committee) (E : Type) [Field E] [Algebra Bit E] where
  /-- `α_i`, the Shamir point of operator `i`. -/
  point : C.Party ↪ E
  point_ne_zero : ∀ i, point i ≠ 0
  /-- `pairs_i`, the products of terms that operator `i` adds. Each pair goes to one holder. -/
  pairs : C.Party → Finset (C.Term × C.Term)
  pairs_unique : ∀ AB, ∃! i, AB ∈ pairs i
  pairs_held : ∀ i AB, AB ∈ pairs i → i ∈ C.holders AB.1 ∧ i ∈ C.holders AB.2
  /-- `T_i`, the term that operator `i` fills in a peer reshare. -/
  filled : C.Party ↪ C.Term
  filled_held : ∀ i, i ∈ C.holders (filled i)
  /-- `(T*, κ)` of gate `g` in a collector reshare. -/
  collector : ℕ → C.Term × C.Party
  collector_held : ∀ g, (collector g).2 ∈ C.holders (collector g).1
  /-- `owner(T)`, the holder that sends the copy of `T` and adds the mask of `T`. -/
  owner : C.Term → C.Party
  owner_held : ∀ T, owner T ∈ C.holders T
  /-- The term that holds the public part `c` of a replicated sharing. -/
  publicTerm : C.Term
  /-- `x^q`, the weight of bit `q` of a word in the check. -/
  weight : Fin (2 ^ wordBits) → E
  weight_independent : LinearIndependent Bit weight
  /-- The bits of an element of `E`. -/
  encode : E ≃ (Fin elementBits → Bit)

/-- The reshare of the AND gates. -/
inductive ReshareMode
  | peer
  | collector
deriving DecidableEq

/-- The rounds of one reshare. -/
def ReshareMode.rounds : ReshareMode → ℕ
  | .peer => 1
  | .collector => 2

/-- The settings of the ceremonies, which every operator uses. -/
structure Settings where
  mode : ReshareMode
  batchSize : ℕ

/-! ## The oracles -/

/-- A PRF point of PRAWNS, Section 3.1, as `doc/sign.md` adapts it. `A_prf(e, l, p)` is position `p`
on chain `l` of key `e`, and `A_rnd(e)` is the randomizer value of key `e`. -/
inductive Point
  | chain (lay : Layer) (e : KeyIndex) (l : ChainIndex) (p : Digit)
  | randomizer (lay : Layer) (e : KeyIndex)
deriving DecidableEq

/-- A setup with commit, reveal and echo, namely the keygen or the PRSS setup of a ceremony. -/
inductive Phase
  | keygen
  | prss
deriving DecidableEq

/-- The kind of a key that a setup derives. The derivation hashes only the tag of the phase and the
kind, and the parts. -/
inductive KeyKind
  | parameter
  | term
  | pair
deriving DecidableEq

/-- A key that a setup derives, namely `P`, the key of a term, or the key of a pair. The name only
keeps track of a key, and no hash takes it. -/
inductive KeyName (C : Committee)
  | parameter
  | term (T : C.Term)
  | pair (p : C.Pair)
deriving DecidableEq

/-- An input of `H`. Each constructor is one use of `H`, and the tag of the implementation separates
it (`doc/dkg.md` 1.1.4). -/
inductive Query (C : Committee)
  /-- The tweakable hash `Th` of leanXMSS, on the bytes of leanVM. -/
  | hash (input : HashInput)
  /-- `H16(seed_T ‖ x)`, the PRF of a term, which the note defines with no tag. -/
  | prf (seed : HashOutput) (x : Point)
  /-- `H16(K_ij ‖ x ‖ m ‖ J)`, a mask of `Eval`, which the note defines with no tag. -/
  | mask (key : HashOutput) (x : Point) (message : Message) (J : C.Quorum)
  /-- `com_{i → j}`, which names its sender and its receiver. The tag is `thlxmss-commit` in the
  keygen and `thlxmss-prss-commit` in the PRSS setup. -/
  | commit (phase : Phase) (sender receiver : C.Party) (reveal : List HashOutput)
  /-- A key from its parts. The tags are `thlxmss-keygen-parameter`, `thlxmss-keygen-term`,
  `thlxmss-keygen-pair`, `thlxmss-prss-term` and `thlxmss-prss-pair`. -/
  | derive (phase : Phase) (kind : KeyKind) (parts : List HashOutput)
  /-- The hash of the keys of the terms that two operators share, which the echo of a setup carries.
  The tag is `thlxmss-keygen-echo` or `thlxmss-prss-echo`. -/
  | sharedKeys (phase : Phase) (keys : List HashOutput)
  /-- The hash of a copy in `OpenRep`, with the tag `thlxmss-copy`. -/
  | copy (values : List Bit)
  /-- The running hash `h_T` of the values that a term records, with the tag `thlxmss-history`. -/
  | history (values : List Bit)
  /-- The salted digest `d_T = H(s_T ‖ h_T)`, with the tag `thlxmss-digest`. -/
  | digest (salt : List Bit) (history : HashOutput)
  /-- `H(key)`, whose first 128 bits key the AES-128 of a stream, with the label `rss-prss`. -/
  | streamKey (key : HashOutput)
  /-- `H` of the tag of the batch, the round label `ρ` of the `Rand(ρ, 1)` of a coin, and its opened
  value, the key of its expansion, with the tag `thlxmss-coin`. -/
  | coinKey (tag ρ : ℕ) (value : List Bit)
  /-- Value `index` of the expansion of a coin key, with the tag `thlxmss-expand`. -/
  | expand (key : HashOutput) (index : ℕ)
deriving DecidableEq

/-- An input `(name, key, ρ, idx, position)` of `PRG`. The name of the key is not an input of AES.
It only marks the key for the AES term of the claims. -/
abbrev PrgInput (C : Committee) := KeyName C × HashOutput × ℕ × ℕ × ℕ

/-- `H` gives 32 bytes, and `PRG` gives one bit. -/
abbrev RoSpec (C : Committee) := (Query C →ₒ HashOutput) + (PrgInput C →ₒ Bit)

/-- Private sampling, `H` and `PRG`. -/
abbrev LocalSpec (C : Committee) := unifSpec + RoSpec C

variable {C : Committee}

/-- One query of `H`. -/
def hashQuery (q : Query C) : OracleComp (RoSpec C) HashOutput :=
  query (spec := RoSpec C) (.inl q)

/-- Run a computation of leanVM on the domain `Th` of `H`. -/
def tweakable {α : Type} (oa : OracleComp HashSpec α) : OracleComp (RoSpec C) α :=
  simulateQ (fun input => hashQuery (.hash input)) oa

/-- A computation of leanVM with the fixed function `Th`. -/
def evalTh {α : Type} (Th : HashInput → HashOutput) (oa : OracleComp HashSpec α) : α :=
  let impl : QueryImpl HashSpec Id := fun input => pure (Th input)
  simulateQ impl oa

/-- `F(seed, x) = H16(seed ‖ x)`, the PRF of one term. -/
def prf (seed : HashOutput) (x : Point) : OracleComp (RoSpec C) Digest :=
  truncateHash <$> hashQuery (.prf seed x)

/-! ## Messages and programs -/

/-- A message of one round from one operator to another. An operator that aborts sends `abort` to
every operator in each later round (`src/net.rs`). -/
inductive Msg (E : Type) where
  | bits (values : List Bit)
  | elements (values : List E)
  | hashes (values : List HashOutput)
  | bundle (parts : List (Msg E))
  | abort

namespace Msg

variable {E : Type} [Zero E]

def bitAt : Option (Msg E) → ℕ → Bit
  | some (.bits values), k => values.getD k 0
  | _, _ => 0

def elementAt : Option (Msg E) → ℕ → E
  | some (.elements values), k => values.getD k 0
  | _, _ => 0

def hashesOf : Option (Msg E) → List HashOutput
  | some (.hashes values) => values
  | _ => []

def part : Option (Msg E) → ℕ → Option (Msg E)
  | some (.bundle parts), k => parts[k]?
  | _, _ => none

def isAbort : Option (Msg E) → Bool
  | some .abort => true
  | _ => false

end Msg

/-- The messages that one operator sends to, or receives from, each operator. -/
abbrev Mail (C : Committee) (E : Type) := C.Party → Option (Msg E)

/-- One synchronous round sends the outbox and receives the inbox. -/
abbrev RoundSpec (C : Committee) (E : Type) := Mail C E →ₒ Mail C E

/-- The oracles of an operator in the `G`-hybrid model. The real network has `G = []ₒ`. -/
abbrev PartySpec (C : Committee) (E : Type) {ι : Type} (G : OracleSpec ι) :=
  LocalSpec C + RoundSpec C E + G

/-- The program of one operator. `none` is an abort. -/
abbrev PartyM (C : Committee) (E : Type) {ι : Type} (G : OracleSpec ι) :=
  OptionT (OracleComp (PartySpec C E G))

/-- A program stopped at its output, at its next round, or at its next call. -/
inductive Step (C : Committee) (E : Type) {ι : Type} (G : OracleSpec ι) (α : Type) where
  | done (out : Option α)
  | wait (outbox : Mail C E) (resume : Mail C E → OracleComp (PartySpec C E G) (Option α))
  | call (input : ι) (resume : G input → OracleComp (PartySpec C E G) (Option α))

variable {E : Type} {ι : Type} {G : OracleSpec ι}

/-- Run the local steps of a program up to its output, its next round or its next call. -/
def advance {α : Type} : OracleComp (PartySpec C E G) (Option α) → OracleComp (LocalSpec C) (Step C E G α)
  | .pure out => pure (.done out)
  | .roll (Sum.inl (Sum.inl q)) k => do
      let r ← OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q)
      advance (k r)
  | .roll (Sum.inl (Sum.inr outbox)) k => pure (.wait outbox k)
  | .roll (Sum.inr input) k => pure (.call input k)

/-- One round. The operator aborts if it receives an abort frame from any operator. A missing message
from an operator that sends nothing by design reads as empty. -/
def exchange (outbox : Mail C E) : PartyM C E G (Mail C E) := do
  let inbox : Mail C E ← OptionT.lift (OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inr outbox))))
  if C.parties.any fun j => Msg.isAbort (inbox j) then failure else pure inbox

/-- A call to the functionality of the hybrid model. -/
def call (input : ι) : PartyM C E G (G input) :=
  OptionT.lift (OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (Sum.inr input)))

def localStep {α : Type} (oa : OracleComp (LocalSpec C) α) : PartyM C E G α :=
  OptionT.lift (liftComp oa _)

def oracleStep {α : Type} (oa : OracleComp (RoSpec C) α) : PartyM C E G α :=
  localStep (liftComp oa _)

def require (condition : Prop) : PartyM C E G Unit :=
  open Classical in if condition then pure () else failure

/-! ## Keys -/

/-- The keys of one operator after the keygen. -/
structure Keys (C : Committee) where
  parameter : PublicParameter
  /-- `seed_T` for each held term. -/
  seed : C.Term → HashOutput
  /-- `K_ij` for each other operator `j`. -/
  pairKey : C.Party → HashOutput

/-- The PRSS keys of one operator in one ceremony (CDI05). Only the streams of the ceremony use them,
and the operator erases them at its end. -/
structure PrssKeys (C : Committee) where
  term : C.Term → HashOutput
  pair : C.Party → HashOutput

/-- Operator `i` in one ceremony. -/
structure Context (C : Committee) where
  self : C.Party
  keys : Keys C
  prss : PrssKeys C

/-- Operator `i` with no keys, for the gadgets that read only `self`. -/
def localContext (i : C.Party) : Context C := ⟨i, ⟨0, fun _ => 0, fun _ => 0⟩, ⟨fun _ => 0, fun _ => 0⟩⟩

/-! ## Sharings -/

/-- A replicated sharing of a vector at one operator, meaningful at its held terms (CDI05). The
public part joins the term `publicTerm`. -/
abbrev Shares (C : Committee) (R : Type) := C.Term → ℕ → R

/-- The state of a run, namely the running value `h_T` of each term, the next round label, and the
tag of the batch. -/
structure RunState (C : Committee) where
  history : C.Term → List Bit
  label : ℕ
  tag : ℕ

/-- A program of one run. -/
abbrev RunM (C : Committee) (E : Type) {ι : Type} (G : OracleSpec ι) := StateT (RunState C) (PartyM C E G)

def vector {R : Type} (count : ℕ) (v : ℕ → R) : List R := (List.range count).map v

def bitsOfDigest (d : Digest) : List Bit := List.ofFn fun k : Fin digestBits => if d.getLsbD k then 1 else 0

def digestOfBits (bits : List Bit) : Digest :=
  BitVec.ofNat digestBits (∑ k ∈ Finset.range digestBits, (bits.getD k 0).val * 2 ^ k)

/-- How the values of a sharing travel and how a stream gives them, as bits of the circuit or as
elements of the check. -/
structure Codec (C : Committee) (E R : Type) where
  pack : List R → Msg E
  unpack : Option (Msg E) → ℕ → R
  draw : KeyName C → HashOutput → ℕ → ℕ → ℕ → OracleComp (RoSpec C) (ℕ → R)
  toBits : R → List Bit

/-- The PRSS outputs of one round, namely the terms `r_T` of `Rand` and the pair streams `Z_ij`. -/
abbrev PrssOutput (C : Committee) (R : Type) := Shares C R × (C.Party → ℕ → R)

/-- An inner product that the check reshares. -/
inductive Product (C : Committee) (E : Type)
  /-- Of two replicated vectors, which `MulRep` shares in the slice steps. -/
  | replicated (x y : Shares C E) (count : ℕ)
  /-- Of two Shamir vectors, which `MulSh` shares. -/
  | shamir (x y : ℕ → E) (count : ℕ)

section Gadgets

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C)

/-- `count` bits of `PRG(key, ρ, idx)`. -/
def prgBits (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) : OracleComp (RoSpec C) (ℕ → Bit) := do
  let bits ← (List.range count).mapM fun position =>
    (query (spec := RoSpec C) (.inr (name, key, ρ, idx, position)) : OracleComp (RoSpec C) Bit)
  pure fun g => bits.getD g 0

def bitCodec : Codec C E Bit where
  pack := .bits
  unpack := Msg.bitAt
  draw := prgBits
  toBits b := [b]

def elementCodec : Codec C E E where
  pack := .elements
  unpack := Msg.elementAt
  draw name key ρ idx count := do
    let bits ← prgBits name key ρ idx (elementBits * count)
    pure fun g => K.encode.symm fun b => bits (elementBits * g + b)
  toBits x := List.ofFn (K.encode x)

/-- A fresh round label. -/
def freshLabel : RunM C E G ℕ := modifyGet fun s => (s.label, { s with label := s.label + 1 })

/-- `Rand(ρ, idx)` and the pair streams of round `ρ`, from the PRSS keys (CDI05). -/
def prssRandomness {R : Type} [Zero R] (codec : Codec C E R) (idx count : ℕ) :
    RunM C E G (PrssOutput C R) := do
  let ρ ← freshLabel
  let r ← StateT.lift (oracleStep (C.terms.mapM fun T =>
    if ctx.self ∈ C.holders T then codec.draw (.term T) (ctx.prss.term T) ρ idx count else pure fun _ => 0))
  let Z ← StateT.lift (oracleStep (C.parties.mapM fun j =>
    if h : j = ctx.self then pure fun _ => 0
    else codec.draw (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) ρ idx count))
  pure (fun T => r.getD (C.terms.idxOf T) fun _ => 0, fun j => Z.getD j.val fun _ => 0)

/-- `MulRep`, the additive share of the products of two replicated sharings. -/
def mulRep {R : Type} [CommRing R] (x y : Shares C R) : ℕ → R := fun g =>
  ∑ AB ∈ K.pairs ctx.self, x AB.1 g * y AB.2 g

/-- `ψ_T(α_i)`, the weight of term `T` at operator `i` in `Conv`. -/
def psi (T : C.Term) (i : C.Party) : E :=
  ∏ j ∈ T.1, (K.point i + K.point j) / K.point j

/-- `Conv`, the Shamir share of a replicated sharing over `E`. -/
def conv (x : Shares C E) : ℕ → E := fun g =>
  ∑ T ∈ Finset.univ.filter (ctx.self ∈ C.holders ·), psi K T ctx.self * x T g

/-- `λ_i`, the Lagrange weight of `α_i` at `0` among all `n` points. -/
def lagrangeAll (i : C.Party) : E :=
  ∏ j ∈ Finset.univ.erase i, K.point j / (K.point j + K.point i)

/-- `MulSh`, the additive share of the inner product of two Shamir vectors of length `count`. -/
def mulSh (x y : ℕ → E) (count : ℕ) : E :=
  lagrangeAll K ctx.self * ∑ g ∈ Finset.range count, x g * y g

/-- The additive share of an inner product. -/
def productShare : Product C E → E
  | .replicated x y count => ∑ g ∈ Finset.range count, mulRep K ctx x y g
  | .shamir x y count => mulSh K ctx x y count

/-- The Lagrange weight of the point of operator `l` at `x`, among the first `t` operators. -/
def lagrangeFirst (x : E) (l : C.Party) : E :=
  ∏ k ∈ (Finset.univ.filter fun k : C.Party => k.val < C.t).erase l,
    (x - K.point k) / (K.point l - K.point k)

/-- The filled terms `C` of a peer reshare. -/
def filledTerms : Finset C.Term := Finset.univ.map K.filled

/-- The operator that fills term `T` at position `g` of a reshare. In peer mode operator `i` fills
`T_i`. In collector mode the collector `κ` of gate `g` fills `T*`. -/
def filler : ReshareMode → C.Term → ℕ → Option C.Party
  | .peer, T, _ => C.parties.find? (K.filled · = T)
  | .collector, T, g => if (K.collector g).1 = T then some (K.collector g).2 else none

/-- Each holder of a term appends the values that a reshare fills in it to `h_T` (`doc/dkg.md`
1.6). -/
def record {R : Type} (codec : Codec C E R) (mode : ReshareMode) (z : Shares C R) (count : ℕ) :
    RunM C E G Unit :=
  modify fun s => ⟨fun T => if ctx.self ∈ C.holders T then
    s.history T ++ ((List.range count).filter fun g => (filler K mode T g).isSome).flatMap
      (codec.toBits ∘ z T) else s.history T, s.label, s.tag⟩

/-- `Reshare` of an additive sharing in one round, with the PRSS outputs `randomness`. Operator `i`
sends `u_i` to the other holders of `T_i`, and each holder of a filled term records it in `h_T`. The
output is zero outside the held terms and the `count` positions. -/
def reshare {R : Type} [Field R] (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R)
    (count : ℕ) : RunM C E G (Shares C R) := do
  let i := ctx.self
  let (r, Z) := randomness
  let u : ℕ → R := fun g => v g + ∑ j ∈ Finset.univ.erase i, Z j g +
    ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T = i), r T g
  let inbox ← StateT.lift (exchange fun j =>
    if j ≠ i ∧ j ∈ C.holders (K.filled i) then some (codec.pack (vector count u)) else none)
  let z : Shares C R := fun T g =>
    if i ∉ C.holders T ∨ count ≤ g then 0
    else if T ∈ filledTerms K then
      ∑ j ∈ Finset.univ.filter (K.filled · = T), if j = i then u g else codec.unpack (inbox j) g
    else r T g
  record K ctx codec .peer z count
  pure z

/-- `Reshare` of the AND gates in collector mode, in two rounds. Operator `i` sends `u_i` of gate `g`
to the collector `κ` of `T*`, and `κ` sends the sum to the other holders of `T*`. -/
def reshareCollector (randomness : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    RunM C E G (Shares C Bit) := do
  let i := ctx.self
  let (r, Z) := randomness
  let star := fun g => (K.collector g).1
  let kappa := fun g => (K.collector g).2
  let collectedBy := fun j => (List.range count).filter (kappa · = j)
  let u : ℕ → Bit := fun g => v g + ∑ j ∈ Finset.univ.erase i, Z j g +
    ∑ T ∈ Finset.univ.filter (fun T => T ≠ star g ∧ K.owner T = i), r T g
  let inbox ← StateT.lift (exchange fun j =>
    if j ≠ i then some (.bits ((collectedBy j).map u)) else none)
  let sum : ℕ → Bit := fun g => u g + ∑ j ∈ Finset.univ.erase i,
    Msg.bitAt (inbox j) ((collectedBy i).idxOf g)
  let forwardedTo := fun (κ h : C.Party) => (collectedBy κ).filter fun g => h ∈ C.holders (star g)
  let forward ← StateT.lift (exchange fun h =>
    if h ≠ i then some (.bits ((forwardedTo i h).map sum)) else none)
  let z : Shares C Bit := fun T g =>
    if i ∉ C.holders T ∨ count ≤ g then 0
    else if T = star g then
      if kappa g = i then sum g else Msg.bitAt (forward (kappa g)) ((forwardedTo (kappa g) i).idxOf g)
    else r T g
  record K ctx bitCodec .collector z count
  pure z

/-- `Reshare` of the AND gates in a mode. -/
def reshareWith (mode : ReshareMode) (randomness : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    RunM C E G (Shares C Bit) :=
  match mode with
  | .peer => reshare K ctx bitCodec randomness v count
  | .collector => reshareCollector K ctx randomness v count

/-- The additive share `Σ_{owner(T) = i} v_T` of a replicated sharing, which `Rerand` reshares. -/
def ownerSum {R : Type} [AddCommMonoid R] (v : Shares C R) : ℕ → R := fun g =>
  ∑ T ∈ Finset.univ.filter (K.owner · = ctx.self), v T g

/-- `[[1]]`, the public constant `1` in the term `publicTerm`. -/
def one {R : Type} [Zero R] [One R] : Shares C R := fun T _ => if T = K.publicTerm then 1 else 0

/-- `OpenRep` of a replicated bit vector. For each term, the owner sends its copy and every other
holder sends the hash of its copy to each operator that lacks the term (MPClan, App. B). -/
def openRep (v : Shares C Bit) (count : ℕ) : PartyM C E G (ℕ → Bit) := do
  let i := ctx.self
  let digests ← oracleStep (C.terms.mapM fun T => hashQuery (.copy (vector count (v T))))
  let inbox ← exchange fun j => if j = i then none else some (.bundle [
    .bits ((C.terms.filter fun T => j ∉ C.holders T ∧ K.owner T = i).flatMap fun T => vector count (v T)),
    .hashes ((C.terms.zip digests).filterMap fun (T, d) =>
      if j ∉ C.holders T ∧ i ∈ C.holders T ∧ K.owner T ≠ i then some d else none)])
  let copies := fun j => Msg.part (inbox j) 0
  let hashes := fun j => Msg.part (inbox j) 1
  let copy : Shares C Bit := fun T g =>
    if i ∈ C.holders T then v T g else
      let owned := C.terms.filter fun T' => i ∉ C.holders T' ∧ K.owner T' = K.owner T
      Msg.bitAt (copies (K.owner T)) (count * owned.idxOf T + g)
  let copyDigests ← oracleStep (C.terms.mapM fun T => hashQuery (.copy (vector count (copy T))))
  require (∀ T : C.Term, i ∉ C.holders T → ∀ h ∈ C.holders T, h ≠ K.owner T →
    let sent := C.terms.filter fun T' => i ∉ C.holders T' ∧ h ∈ C.holders T' ∧ K.owner T' ≠ h
    (Msg.hashesOf (hashes h))[sent.idxOf T]? = (C.terms.zip copyDigests).lookup T)
  pure fun g => ∑ T, copy T g

/-- `OpenSh` of a Shamir vector. Each operator interpolates the shares of the first `t` operators
and aborts unless all `n` shares lie on that polynomial. -/
def openSh (v : ℕ → E) (count : ℕ) : PartyM C E G (ℕ → E) := do
  let i := ctx.self
  let inbox ← exchange fun j => if j = i then none else some (.elements (vector count v))
  let share : C.Party → ℕ → E := fun j g => if j = i then v g else Msg.elementAt (inbox j) g
  let first := Finset.univ.filter fun l : C.Party => l.val < C.t
  require (∀ j : C.Party, ∀ g < count,
    share j g = ∑ l ∈ first, lagrangeFirst K (K.point j) l * share l g)
  pure fun g => ∑ l ∈ first, lagrangeFirst K 0 l * share l g

/-- `Coin`, `count` public values `OpenSh(Conv(Rand))` (GS20, Protocol 6). -/
def coinWith (randomness : PrssOutput C E) (count : ℕ) : RunM C E G (List E) := do
  let opened ← StateT.lift (openSh K ctx (conv K ctx randomness.1) count)
  pure (vector count opened)

/-- The salted digests `d_T` of the held terms go to every operator. Each operator aborts unless all
holders of each term sent the same digest (CGH+18, Protocol 3.3). -/
def compareDigests (salts : Shares C Bit) : RunM C E G Unit := do
  let i := ctx.self
  let h := (← get).history
  let digests ← StateT.lift (oracleStep (C.terms.mapM fun T =>
    if i ∈ C.holders T then do hashQuery (.digest (vector 256 (salts T)) (← hashQuery (.history (h T))))
    else pure 0))
  let inbox ← StateT.lift (exchange fun j => if j = i then none else some (.hashes digests))
  let digestOf := fun j => if j = i then digests else Msg.hashesOf (inbox j)
  StateT.lift (require (∀ T : C.Term, ∀ j ∈ C.holders T, ∀ j' ∈ C.holders T,
    (digestOf j)[C.terms.idxOf T]? = (digestOf j')[C.terms.idxOf T]? ∧
      (digestOf j)[C.terms.idxOf T]?.isSome))

end Gadgets

/-! ## The check

The check of GS20, Section 5, with compression parameter `k = 2`, in the layout of the
implementation (`src/check.rs`). Tuple `k` is bit `q` of word `w` of slice `h`. -/

/-- A multiplication tuple `([[x]], [[y]], [[z]])` of bit vectors of length `count`, from a reshare
in `mode`. -/
structure Tuple (C : Committee) where
  x : Shares C Bit
  y : Shares C Bit
  z : Shares C Bit
  count : ℕ
  mode : ReshareMode

/-- The words of a slice of `count` tuples, a multiple of 8 (`slice_length` of the implementation). -/
def sliceLength (count : ℕ) : ℕ :=
  (((count + 2 ^ wordBits - 1) / 2 ^ wordBits + 2 ^ sliceBits - 1) / 2 ^ sliceBits + 7) / 8 * 8

/-- The tuples of a slice, which is also the length of the vectors after the slice steps. -/
def sliceWidth (count : ℕ) : ℕ := 2 ^ wordBits * sliceLength count

/-- The length after one halving step. The step pads a vector of more than 16 elements to a multiple
of 16, and a shorter vector to an even length. -/
def halvedLength (length : ℕ) : ℕ :=
  (if 16 < length then (length + 15) / 16 * 16 else (length + 1) / 2 * 2) / 2

/-- The halving steps from `length` elements down to one element. -/
def halvingSteps (length : ℕ) : ℕ := if 1 < length then halvingSteps (halvedLength length) + 1 else 0
termination_by length
decreasing_by unfold halvedLength; split_ifs <;> omega

/-- The number `R` of halving steps of a check of `count` tuples, the slice steps included. -/
def halvings (count : ℕ) : ℕ := sliceBits + halvingSteps (sliceWidth count)

/-- The number `d` of coins of the weights, `log2` of the padded words rounded up. -/
def coins (count : ℕ) : ℕ := Nat.clog 2 (2 ^ sliceBits * sliceLength count)

def sliceOf (count k : ℕ) : ℕ := k / sliceWidth count

def wordOf (count k : ℕ) : ℕ := k / 2 ^ wordBits % sliceLength count

def bitOf (k : ℕ) : Fin (2 ^ wordBits) := ⟨k % 2 ^ wordBits, Nat.mod_lt _ (by positivity)⟩

/-- The tries of a challenge. -/
def challengeTries : ℕ := 2 ^ 64

/-- The gadgets that the check calls, namely the values of `F_coin`, the inner products of
`F_extendMult` as a replicated sharing, and the PRSS outputs of `F_rand`. -/
structure CheckGadgets (C : Committee) (E : Type) {ι : Type} (G : OracleSpec ι) where
  coin : ℕ → RunM C E G (List E)
  extendMult : List (Product C E) → RunM C E G (Shares C E)
  randElements : ℕ → RunM C E G (PrssOutput C E)
  randBits : ℕ → RunM C E G (PrssOutput C Bit)

section Check

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C) (gadgets : CheckGadgets C E G)

/-- `τ^a`, the product of the coins `τ[offset + b]` at the set bits `b < width` of `a`. -/
def coinProduct (τ : List E) (offset width a : ℕ) : E :=
  ∏ b ∈ Finset.range width, if a.testBit b then τ.getD (offset + b) 0 else 1

/-- An element of `E` from the first bits of a hash output. -/
def elementOfHash (h : HashOutput) : E := K.encode.symm fun b => if h.getLsbD b.val then 1 else 0

/-- The key of a coin, `H` of the tag of the batch, the label `ρ` of its `Rand(ρ, 1)`, which is the
label before the coin, and its opened value (`doc/dkg.md` 1.9). The model counts the labels over a
ceremony, and the implementation counts the rounds of each batch. -/
def coinKey : RunM C E G HashOutput := do
  let state ← get
  let values ← gadgets.coin 1
  StateT.lift (oracleStep (hashQuery (.coinKey state.tag state.label
    (values.flatMap fun v => List.ofFn (K.encode v)))))

/-- `count` expanded values of a coin key. -/
def expand (key : HashOutput) (count : ℕ) : RunM C E G (List E) :=
  StateT.lift (oracleStep ((List.range count).mapM fun k => elementOfHash K <$> hashQuery (.expand key k)))

/-- The first expanded value outside `{0, 1}` from position `index`, within `tries` positions. -/
def findChallenge (key : HashOutput) : ℕ → ℕ → OracleComp (RoSpec C) (Option E)
  | 0, _ => pure none
  | tries + 1, index => do
      let r := elementOfHash K (← hashQuery (.expand key index))
      match Classical.propDecidable (r ≠ 0 ∧ r ≠ 1) with
      | isTrue _ => pure (some r)
      | isFalse _ => findChallenge key tries (index + 1)

/-- A challenge, the first expanded value of a fresh coin outside `{0, 1}`. -/
def challenge : RunM C E G E := do
  let key ← coinKey K gadgets
  let some r ← StateT.lift (oracleStep (findChallenge K key challengeTries 0)) | StateT.lift failure
  pure r

/-- The check of the tuples (GS20, Protocols 13 to 15, in the layout of `src/check.rs`). A check of
no tuple accepts at once. -/
def check (tuples : List (Tuple C)) : RunM C E G Unit := do
  let lift := fun (part : Tuple C → Shares C Bit) (T : C.Term) =>
    tuples.flatMap fun τ => vector τ.count fun g => algebraMap Bit E (part τ T g)
  let X : Shares C E := fun T k => (lift (·.x) T).getD k 0
  let Y : Shares C E := fun T k => (lift (·.y) T).getD k 0
  let Z : Shares C E := fun T k => (lift (·.z) T).getD k 0
  let count := (tuples.map (·.count)).sum
  if count = 0 then return
  let m := halvings count
  let d := coins count
  let s := sliceBits
  let width := sliceWidth count
  -- De-linearization with the coins `τ` and the word weights `x^q`. The claim weighs tuple `k` by
  -- `τ^h τ^w x^q`, and `x` keeps `τ^w x^q`.
  let τ ← expand K (← coinKey K gadgets) d
  StateT.lift (require (∀ b < s, τ.getD b 0 ≠ 0))
  let wordWeight := fun k => coinProduct τ s (d - s) (wordOf count k) * K.weight (bitOf k)
  let claim : Shares C E := fun T _ => ∑ k ∈ Finset.range (2 ^ s * width),
    coinProduct τ 0 s (sliceOf count k) * wordWeight k * Z T k
  -- The slice steps fold the top bit of the slice with the coin `c_j` kept out of `x`.
  let (xs, ys, D) ← (List.range s).foldlM (init := ((fun T k => wordWeight k * X T k : Shares C E), Y,
      conv K ctx claim 0)) fun (xs, ys, D) j => do
    let half := width * 2 ^ (s - 1 - j)
    let rest := fun k => coinProduct τ 0 (s - 1 - j) (k / width)
    let t ← gadgets.extendMult [.replicated (fun T k => rest k * xs T k) ys half,
      .replicated (fun T k => rest k * (xs T k + xs T (k + half))) (fun T k => ys T k + ys T (k + half)) half]
    let r ← challenge K gadgets
    let t₀ := conv K ctx t 0
    let tInf := conv K ctx t 1
    let t₁ := (D + t₀) / τ.getD (s - 1 - j) 0
    let fold := fun (v : Shares C E) T k => v T k + r * (v T k + v T (k + half))
    pure (fold xs, fold ys, (1 + r) * t₀ + r * t₁ + r * (1 + r) * tInf)
  -- Dimension-Reduction with `k = 2` (GS20, Protocol 14). The high half reads the padding as zeros.
  let (A, B, D) ← (List.range (m - s)).foldlM (init := (conv K ctx xs, conv K ctx ys, D))
    fun (A, B, D) j => do
      let length := halvedLength^[j] width
      let half := halvedLength length
      let hi := fun (v : ℕ → E) k => if k + half < length then v (k + half) else 0
      let sum := fun (v : ℕ → E) k => v k + hi v k
      let p ← gadgets.extendMult [.shamir A B half, .shamir (sum A) (sum B) half]
      let r ← challenge K gadgets
      let fold := fun (v : ℕ → E) k => v k + r * (v k + hi v k)
      pure (fold A, fold B, conv K ctx p 0 + (D + conv K ctx p 1) * r + conv K ctx p 1 * r ^ 2)
  -- Randomization (GS20, Protocol 15), with the digests before its coin.
  let w ← gadgets.randElements 2
  let wa := conv K ctx w.1 0
  let wb := conv K ctx w.1 1
  let q ← gadgets.extendMult [.shamir (fun _ => wa) (fun _ => wb) 1,
    .shamir (fun _ => wa + A 0) (fun _ => wb + B 0) 1]
  let q₀ := conv K ctx q 0
  let q₂ := conv K ctx q 1
  let salts ← gadgets.randBits 256
  compareDigests ctx salts.1
  let r ← challenge K gadgets
  let opened ← StateT.lift (openSh K ctx (fun k => match k with
    | 0 => wa + r * (wa + A 0)
    | 1 => wb + r * (wb + B 0)
    | _ => q₀ + (D + q₀ + q₂) * r + q₂ * r ^ 2) 3)
  StateT.lift (require (opened 0 * opened 1 = opened 2))

/-- The gadgets of the real check, from the PRSS keys of the ceremony. -/
def realCheckGadgets : CheckGadgets C E G where
  coin count := do coinWith K ctx (← prssRandomness ctx (elementCodec K) 1 count) count
  extendMult products := do
    let randomness ← prssRandomness ctx (elementCodec K) 0 products.length
    reshare K ctx (elementCodec K) randomness
      (fun g => match products[g]? with | some p => productShare K ctx p | none => 0) products.length
  randElements count := prssRandomness ctx (elementCodec K) 1 count
  randBits count := prssRandomness ctx bitCodec 2 count

end Check

/-! ## Circuits -/

/-- The sum of some wires and a public constant. -/
structure Affine where
  wires : List ℕ
  const : Bit

/-- A layered Boolean circuit. Each layer appends the products of its pairs to the wires. -/
structure Circuit where
  layers : List (List (Affine × Affine))
  outputs : List Affine

def Affine.eval (a : Affine) (w : List Bit) : Bit := (a.wires.map fun k => w.getD k 0).sum + a.const

def Circuit.eval (c : Circuit) (x : List Bit) : List Bit :=
  let w := c.layers.foldl (fun w layer => w ++ layer.map fun ab => ab.1.eval w * ab.2.eval w) x
  c.outputs.map (·.eval w)

/-- The identity on `width` input bits. -/
def Circuit.identity (width : ℕ) : Circuit := ⟨[], (List.range width).map fun k => ⟨[k], 0⟩⟩

/-- What a job computes from the threshold PRF values of its points (`doc/dkg.md` 3.1). -/
inductive JobKind
  /-- `y_3` from `F(x_0)` on chain `l` of top key `e`. -/
  | chainEnd (e : KeyIndex) (l : ChainIndex)
  /-- `y_1 ⊕ F(x_1)`, `y_2 ⊕ F(x_2)` and `y_3` from `F(x_0), F(x_1), F(x_2)` on bottom key `e`. -/
  | chainRow (e : KeyIndex) (l : ChainIndex)
  /-- `y_p` from `F(x_0)` on chain `l` of top key `e`. -/
  | chainValue (e : KeyIndex) (l : ChainIndex) (p : Digit)
  /-- `c_e` from `F(A_rnd(e))` on bottom key `e`. -/
  | commitment (e : KeyIndex)
  /-- `F(A_rnd(e))` itself. -/
  | randomizer

/-- The PRF values that a job of each kind takes. -/
def JobKind.arity : JobKind → ℕ
  | .chainRow .. => 3
  | _ => 1

/-- A job on the threshold PRF values `F(x)` of some points `x`. -/
structure Job where
  kind : JobKind
  points : List Point

/-- The Boolean circuit of each job kind under each public parameter, which the MPC evaluates. -/
abbrev Circuits := PublicParameter → JobKind → Circuit

/-- The gadgets that a run calls, namely `F_mult` for the AND gates in `mode` and for `Rerand`, and
`F_multVerify` for the check (GS20, Protocol 19). -/
structure RunGadgets (C : Committee) (E : Type) {ι : Type} (G : OracleSpec ι) where
  mode : ReshareMode
  mult : Shares C Bit → Shares C Bit → ℕ → RunM C E G (Shares C Bit)
  rerand : Shares C Bit → ℕ → RunM C E G (Shares C Bit)
  verify : List (Tuple C) → RunM C E G Unit
  /-- `OpenRep` of the outputs. -/
  output : Shares C Bit → ℕ → RunM C E G (ℕ → Bit)

/-- The most AND layers of the circuits of a run. -/
def depth (jobs : List Circuit) : ℕ := (jobs.map (·.layers.length)).foldl max 0

/-- The tuple bits that the check of a run covers, namely the AND gates and the outputs. -/
def tupleCount (jobs : List Circuit) : ℕ :=
  ((List.range (depth jobs)).map fun layer => (jobs.map fun job => (job.layers.getD layer []).length).sum).sum +
    (jobs.map (·.outputs.length)).sum

/-- The rounds of a run of `jobs`. Each AND layer takes one reshare, `Rerand` one round and each coin
one round. Each halving step takes two rounds, the randomization with its digests four, and
`OpenRep` one. -/
def runRounds (mode : ReshareMode) (jobs : List Circuit) : ℕ :=
  depth jobs * mode.rounds + 1 + 1 + 2 * halvings (tupleCount jobs) + 4 + 1

section Run

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C)

/-- An affine function of the wires of a replicated sharing, with the constant in `publicTerm`. -/
def Affine.share (a : Affine) (w : C.Term → List Bit) (publicTerm T : C.Term) : Bit :=
  (a.wires.map fun k => (w T).getD k 0).sum + if T = publicTerm then a.const else 0

/-- The sharing of the PRF values of the points of a job, as its input wires. Each holder of `T`
computes term `T` as `H16(seed_T ‖ x)`, a `Rand` with chosen input (`doc/dkg.md` 3.1). -/
def inputShares (job : Job) : PartyM C E G (C.Term → List Bit) := do
  let terms ← oracleStep (C.terms.mapM fun T =>
    if ctx.self ∈ C.holders T then job.points.flatMapM fun x => bitsOfDigest <$> prf (ctx.keys.seed T) x
    else pure [])
  pure fun T => terms.getD (C.terms.idxOf T) []

/-- A run of the circuits of some jobs on their input sharings (GS20, Protocol 19). The AND gates of
one layer of all jobs take one call of `mult`. Then `rerand` re-randomizes the outputs, `verify`
checks every tuple, and `output` opens the outputs (BBY23, Section 4.3, and MPClan, App. B). -/
def runJobs (gadgets : RunGadgets C E G) (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    RunM C E G (List (List Bit)) := do
  let (wires, tuples) ← (List.range (depth jobs)).foldlM (init := (inputs, ([] : List (Tuple C))))
    fun (wires, tuples) layer => do
      let gates := jobs.zipIdx.flatMap fun (job, k) =>
        (job.layers.getD layer []).map fun ab => (k, ab)
      let x : Shares C Bit := fun T g => match gates[g]? with
        | some (k, ab) => ab.1.share (wires.getD k fun _ => []) K.publicTerm T | none => 0
      let y : Shares C Bit := fun T g => match gates[g]? with
        | some (k, ab) => ab.2.share (wires.getD k fun _ => []) K.publicTerm T | none => 0
      let z ← gadgets.mult x y gates.length
      let wires := wires.zipIdx.map fun (w, k) T =>
        w T ++ ((gates.zipIdx.filter (·.1.1 = k)).map fun (_, g) => z T g)
      pure (wires, tuples ++ [⟨x, y, z, gates.length, gadgets.mode⟩])
  let outputs := jobs.zipIdx.flatMap fun (job, k) => job.outputs.map fun a => (k, a)
  let v : Shares C Bit := fun T g => match outputs[g]? with
    | some (k, a) => a.share (wires.getD k fun _ => []) K.publicTerm T | none => 0
  let v' ← gadgets.rerand v outputs.length
  gadgets.verify (tuples ++ [⟨v, one K, v', outputs.length, .peer⟩])
  let opened ← gadgets.output v' outputs.length
  let widths := jobs.map (·.outputs.length)
  pure (widths.zipIdx.map fun (width, k) =>
    vector width fun g => opened ((widths.take k).sum + g))

/-- The gadgets of the real run in `mode`, from the PRSS keys of the ceremony. -/
def realRunGadgets (mode : ReshareMode) : RunGadgets C E G where
  mode := mode
  mult x y count := do
    reshareWith K ctx mode (← prssRandomness ctx bitCodec 0 count) (mulRep K ctx x y) count
  rerand v count := do
    reshare K ctx bitCodec (← prssRandomness ctx bitCodec 0 count) (ownerSum K ctx v) count
  verify := check K ctx (realCheckGadgets K ctx)
  output v count := StateT.lift (openRep K ctx v count)

end Run

/-! ## Setup -/

/-- The parts that one operator samples in a setup, namely its part of `P`, one part for each term
and one part for each other operator. -/
structure Parts (C : Committee) where
  parameter : HashOutput
  term : C.Term → HashOutput
  pair : C.Party → HashOutput

def sampleParts : ProbComp (Parts C) := do
  let parameter ← $ᵗ HashOutput
  let term ← $ᵗ (C.Term → HashOutput)
  let pair ← $ᵗ (C.Party → HashOutput)
  pure ⟨parameter, term, pair⟩

/-- The terms that operators `i` and `j` both hold. -/
def sharedTerms (i j : C.Party) : List C.Term := C.terms.filter fun T => i ∈ C.holders T ∧ j ∈ C.holders T

/-- The reveal from `i` to `j`, namely the part of `P` in the keygen, the parts of the shared terms
and the part for `j`. -/
def revealTo (phase : Phase) (c : Parts C) (i j : C.Party) : List HashOutput :=
  (if phase = .keygen then [c.parameter] else []) ++ (sharedTerms i j).map c.term ++ [c.pair j]

/-- The parts that `j` revealed to `i`. -/
def readReveal (phase : Phase) (reveal : List HashOutput) (i j : C.Party) : Parts C :=
  let offset := if phase = .keygen then 1 else 0
  { parameter := reveal.getD 0 0
    term := fun T => reveal.getD (offset + (sharedTerms j i).idxOf T) 0
    pair := fun _ => reveal.getD (offset + (sharedTerms j i).length) 0 }

/-- The keys that operator `i` derives from the parts `view j` of each operator `j`. Holders and
pair members are in increasing order. Only the keygen derives `P`. -/
def deriveKeys (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    OracleComp (RoSpec C) (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) := do
  let parameter ← if phase = .keygen then
    hashQuery (.derive phase .parameter (C.parties.map fun j => (view j).parameter)) else pure 0
  let term ← C.terms.mapM fun T => if i ∈ C.holders T then
    hashQuery (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T))
    else pure 0
  let pair ← C.parties.mapM fun j => if h : j = i then pure 0 else
    let p := C.pairOf i j (Ne.symm h)
    hashQuery (.derive phase .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1])
  pure (parameter, fun T => term.getD (C.terms.idxOf T) 0, fun j => pair.getD j.val 0)

/-- A setup with commit, reveal and echo (the note, Section 2.1). Operator `i` commits to each reveal
with a commitment that names its sender and its receiver (CF01). The keygen echo carries the hash of
all parts of `P`, which is `P` before truncation, and the hash of the shared seeds. The PRSS echo
carries only the hash of the shared keys. Each operator aborts unless each reveal opens its
commitment and each hash of each echo matches. -/
def commitRevealEcho (phase : Phase) (i : C.Party) (own : Parts C) :
    PartyM C E G (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) := do
  let commitments ← oracleStep (C.parties.mapM fun j => hashQuery (.commit phase i j (revealTo phase own i j)))
  let committed ← exchange fun j => if j = i then none else some (.hashes [commitments.getD j.val 0])
  let revealed ← exchange fun j => if j = i then none else some (.hashes (revealTo phase own i j))
  let opens ← oracleStep (C.parties.mapM fun j => hashQuery (.commit phase j i (Msg.hashesOf (revealed j))))
  require (∀ j, j ≠ i → (Msg.hashesOf (revealed j)).length = (revealTo phase own j i).length ∧
    [opens.getD j.val 0] = Msg.hashesOf (committed j))
  let view := fun j => if j = i then own else readReveal phase (Msg.hashesOf (revealed j)) i j
  let keys ← oracleStep (deriveKeys phase i view)
  let shared ← oracleStep (C.parties.mapM fun j => hashQuery (.sharedKeys phase ((sharedTerms i j).map keys.2.1)))
  let echo := fun j => (if phase = .keygen then [keys.1] else []) ++ [shared.getD j.val 0]
  let received ← exchange fun j => if j = i then none else some (.hashes (echo j))
  require (∀ j, j ≠ i → Msg.hashesOf (received j) = echo j)
  pure keys

/-- The keygen of operator `i` gives `P`, its seeds and its pair keys. -/
def keygenWith (i : C.Party) (own : Parts C) : PartyM C E G (Keys C) := do
  let (parameter, seed, pairKey) ← commitRevealEcho .keygen i own
  pure ⟨truncateHash parameter, seed, pairKey⟩

def keygen (i : C.Party) : PartyM C E G (Keys C) := do
  keygenWith i (← localStep (liftComp sampleParts _))

/-- The PRSS setup of a ceremony gives fresh PRSS keys (`doc/dkg.md` 3.1). -/
def prssSetup (i : C.Party) : PartyM C E G (PrssKeys C) := do
  let (_, term, pair) ← commitRevealEcho .prss i (← localStep (liftComp sampleParts _))
  pure ⟨term, pair⟩

/-- The rounds of a setup. -/
def setupRounds : ℕ := 3

/-! ## Trees -/

/-- `Th(P, A_rnd(e) at step 1, ρ ‖ 0)`, the input of the commitment `c_e`. -/
def commitmentInput (parameter : PublicParameter) (e : KeyIndex) (ρ : Digest) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (tweakFields 7 1 (layerHi bottomLayer 0) e.val) ++
    bytesLE 16 ρ ++ bytesLE 16 0

/-- `Th(P, A_rnd(e), ρ ‖ M)`, the input of the start `R_0` of the randomizer search. -/
def randomizerInput (parameter : PublicParameter) (lay : Layer) (e : KeyIndex) (ρ : Digest)
    (message : HashInput) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (tweakFields 7 0 (layerHi lay 0) e.val) ++ bytesLE 16 ρ ++ message

/-- Position `p < 4` of a chain. -/
def digit (p : ℕ) (h : p < chainLength := by decide) : Digit := ⟨p, h⟩

/-- A top key `b < 2 ^ 16` as a key index. -/
def topKey (b : Fin (2 ^ layerHeight)) : KeyIndex :=
  ⟨b.val, lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by decide))⟩

/-- Bottom key `k` of bottom tree `b`. -/
def bottomKey (b k : Fin (2 ^ layerHeight)) : KeyIndex :=
  ⟨2 ^ layerHeight * b.val + k.val, by
    have hb := b.isLt; have hk := k.isLt
    show _ < 2 ^ (numLayers * layerHeight)
    simp only [numLayers, layerHeight] at *
    omega⟩

/-- The public outputs of the top tree ceremony. -/
structure TopTree where
  chainEnd : KeyIndex → ChainIndex → Digest
  root : Digest

/-- The public outputs of the ceremony of a bottom tree, namely `cpk_e`, `c_e`, the root, and the
signature of the root by its top key. -/
structure BottomTree where
  cpk : KeyIndex → ChainIndex → Digest × Digest × Digest
  commitment : KeyIndex → Digest
  root : Digest
  topSignature : LayerSignature

/-- A ceremony, namely the top tree or bottom tree `b`. -/
inductive Tree
  | top
  | bottom (b : Fin (2 ^ layerHeight))

/-- The output of a ceremony. -/
inductive TreeOutput
  | top (tree : TopTree)
  | bottom (tree : BottomTree)

section Trees

/-- Node `idx` at `level` of a layer, from the chain ends of its keys. Indices are global. leanVM
builds a tree only from a seed, so this is the one tree routine of the model. -/
def merkleNode (parameter : PublicParameter) (lay : Layer) (chainEnd : KeyIndex → ChainIndex → Digest) :
    ℕ → ℕ → OracleComp HashSpec Digest
  | 0, idx => do
      let key : KeyIndex := ⟨idx % lifetime, Nat.mod_lt _ (by decide)⟩
      Concrete.leafHash parameter lay key (chainEnd key)
  | level + 1, idx => do
      let left ← merkleNode parameter lay chainEnd level (2 * idx)
      let right ← merkleNode parameter lay chainEnd level (2 * idx + 1)
      Concrete.tweakableHash parameter (.node lay (level + 1) idx) (Concrete.nodePayload left right)

/-- The authentication path of a key. -/
def merklePath (parameter : PublicParameter) (lay : Layer) (chainEnd : KeyIndex → ChainIndex → Digest)
    (key : KeyIndex) : OracleComp HashSpec (Fin layerHeight → Digest) :=
  Concrete.sequenceFin fun level =>
    merkleNode parameter lay chainEnd level.val (Nat.xor (key.val / 2 ^ level.val) 1)

/-- The leanXMSS randomizer search from `R_0` finds the first trial whose digest is a codeword. -/
def grind (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (base : Randomness) : ℕ → ℕ → OracleComp HashSpec (Option (Randomness × Encoding))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := base + BitVec.ofNat digestBits trial
      let digest ← Concrete.messageDigest parameter lay key message randomness
      match Codeword.decode digest with
      | some encoding => pure (some (randomness, encoding))
      | none => grind parameter lay key message base attempts (trial + 1)

/-- The digest of the `k`-th 128 bits of an output. -/
def digestAt (bits : List Bit) (k : ℕ) : Digest := digestOfBits (bits.drop (digestBits * k))

/-- The jobs of the top tree, the chain ends of all top keys. -/
def topJobs : List Job :=
  (List.finRange (2 ^ layerHeight)).flatMap fun b => (List.finRange numChains).map fun l =>
    ⟨.chainEnd (topKey b) l, [.chain topLayer (topKey b) l (digit 0)]⟩

/-- The jobs of the first run of bottom tree `b`, namely `cpk` of each key, its commitment `c_e`,
and the randomizer value of top key `b`. -/
def bottomJobs (b : Fin (2 ^ layerHeight)) : List Job :=
  ((List.finRange (2 ^ layerHeight)).flatMap fun k => (List.finRange numChains).map fun l =>
    let e := bottomKey b k
    ⟨.chainRow e l,
      [.chain bottomLayer e l (digit 0), .chain bottomLayer e l (digit 1), .chain bottomLayer e l (digit 2)]⟩) ++
  ((List.finRange (2 ^ layerHeight)).map fun k =>
    ⟨.commitment (bottomKey b k), [.randomizer bottomLayer (bottomKey b k)]⟩) ++
  [⟨.randomizer, [.randomizer topLayer (topKey b)]⟩]

/-- The jobs of the second run of bottom tree `b`. They give the chain values at the positions of
`encoding` for the signature of its root by top key `b`. -/
def signJobs (b : Fin (2 ^ layerHeight)) (encoding : Encoding) : List Job :=
  (List.finRange numChains).map fun l => ⟨.chainValue (topKey b) l (encoding l), [.chain topLayer (topKey b) l (digit 0)]⟩

/-- Split a list in chunks of `size`. -/
def chunks {α : Type} (size : ℕ) (items : List α) : List (List α) :=
  (List.range ((items.length + size - 1) / size)).map fun k => (items.drop (size * k)).take size

/-- A run as its batches of `size` jobs. `run` evaluates one batch. -/
def batched {m : Type → Type} [Monad m] (size : ℕ) (run : List Job → m (Option (List (List Bit))))
    (jobs : List Job) : m (Option (List (List Bit))) := do
  let outputs ← (chunks size jobs).mapM run
  pure (outputs.foldlM (fun acc batch => batch.map (acc ++ ·)) [])

variable {m : Type → Type} [Monad m] (lift : ∀ {α : Type}, OracleComp HashSpec α → m α)

/-- The public outputs of a ceremony. `run` evaluates the jobs of a run, by MPC for the operators or
in the clear for the dealer. A bottom tree has two runs. The first gives `cpk`, the commitments and
the randomizer value of its top key. The second gives the chain values of the top signature, which
must lead to the root of the top tree (`src/dkg.rs`). -/
def ceremonyOutput (parameter : PublicParameter) (run : List Job → m (Option (List (List Bit))))
    (top : TopTree) : Tree → m (Option TreeOutput)
  | .top => do
      let keys := (List.finRange (2 ^ layerHeight)).flatMap fun b =>
        (List.finRange numChains).map fun l => (topKey b, l)
      let some outputs ← run topJobs | pure none
      let chainEnd := fun (e : KeyIndex) (l : ChainIndex) => digestAt (outputs.getD (keys.idxOf (e, l)) []) 0
      let root ← lift (merkleNode parameter topLayer chainEnd layerHeight 0)
      pure (some (.top ⟨chainEnd, root⟩))
  | .bottom b => do
      let keys := (List.finRange (2 ^ layerHeight)).flatMap fun k =>
        (List.finRange numChains).map fun l => (bottomKey b k, l)
      let some outputs ← run (bottomJobs b) | pure none
      let cpk := fun (e : KeyIndex) (l : ChainIndex) =>
        let bits := outputs.getD (keys.idxOf (e, l)) []
        (digestAt bits 0, digestAt bits 1, digestAt bits 2)
      let commitment := fun (e : KeyIndex) => digestAt (outputs.getD (keys.length + e.val % 2 ^ layerHeight) []) 0
      let ρ := digestAt (outputs.getD (keys.length + 2 ^ layerHeight) []) 0
      let root ← lift (merkleNode parameter bottomLayer (fun e l => (cpk e l).2.2) layerHeight b.val)
      let message := bytesLE 16 root
      let base ← lift (truncateHash <$> Concrete.oracleHash (randomizerInput parameter topLayer (topKey b) ρ message))
      let some (randomness, encoding) ← lift (grind parameter topLayer (topKey b) message base
          randomizerAttemptLimit 0) | pure none
      let some values ← run (signJobs b encoding) | pure none
      let path ← lift (merklePath parameter topLayer top.chainEnd (topKey b))
      let signature : LayerSignature := ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩
      let topRoot ← lift (Concrete.layerRoot parameter topLayer (topKey b) message signature)
      if topRoot ≠ some top.root then pure none else
      pure (some (.bottom ⟨cpk, commitment, root, signature⟩))

end Trees

/-- `F(x) = ⊕_T H16(seed_T ‖ x)`, the threshold PRF of PRAWNS, Section 5, on all seeds. -/
def prfValue (seed : C.Term → HashOutput) (x : Point) : OracleComp (RoSpec C) Digest := do
  let terms ← C.terms.mapM fun T => prf (seed T) x
  pure (terms.foldl (· ^^^ ·) 0)

/-- A job in the clear on all seeds, by its circuit. -/
def evalJob (circuits : Circuits) (parameter : PublicParameter) (seed : C.Term → HashOutput) (job : Job) :
    OracleComp (RoSpec C) (List Bit) := do
  let values ← job.points.mapM (prfValue seed)
  pure ((circuits parameter job.kind).eval (values.flatMap bitsOfDigest))

/-- A job in the clear by leanXMSS, with the PRF values from `F`. -/
def referenceJob {m : Type → Type} [Monad m] (lift : ∀ {α : Type}, OracleComp HashSpec α → m α)
    (F : Point → m Digest) (parameter : PublicParameter) (job : Job) : m (List Bit) := do
  let values ← job.points.mapM F
  let value := fun k => values.getD k 0
  match job.kind with
  | .chainEnd e l => bitsOfDigest <$> lift (Concrete.chainWalk parameter topLayer e l 0 3 (value 0))
  | .chainRow e l => do
      let y₁ ← lift (Concrete.chainWalk parameter bottomLayer e l 0 1 (value 0))
      let y₂ ← lift (Concrete.chainWalk parameter bottomLayer e l 0 2 (value 0))
      let y₃ ← lift (Concrete.chainWalk parameter bottomLayer e l 0 3 (value 0))
      pure (bitsOfDigest (y₁ ^^^ value 1) ++ bitsOfDigest (y₂ ^^^ value 2) ++ bitsOfDigest y₃)
  | .chainValue e l p => bitsOfDigest <$> lift (Concrete.chainWalk parameter topLayer e l 0 p.val (value 0))
  | .commitment e => (bitsOfDigest ∘ truncateHash) <$> lift (Concrete.oracleHash (commitmentInput parameter e (value 0)))
  | .randomizer => pure (bitsOfDigest (value 0))

section Ceremony

variable [Field E] [Algebra Bit E] (K : Constants C E)

/-- The ceremony of a tree at operator `i`. It runs the PRSS setup, then each batch of each run with
the gadgets `gadgets ctx k jobs` of batch `k`. Each batch starts with empty running digests and
continues the round labels. The real protocol uses `realRunGadgets`. -/
def ceremonyWith (circuits : Circuits) (settings : Settings)
    (gadgets : Context C → ℕ → List Job → RunGadgets C E G) (i : C.Party) (keys : Keys C) (top : TopTree)
    (tree : Tree) : PartyM C E G TreeOutput := do
  let prss ← prssSetup i
  let ctx : Context C := ⟨i, keys, prss⟩
  let some output ← (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E G))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter
      (batched settings.batchSize fun jobs => do
        let (label, k) ← get
        let inputs ← StateT.lift (jobs.mapM (inputShares ctx))
        let (outputs, state) ← StateT.lift ((runJobs K (gadgets ctx k jobs)
          (jobs.map (circuits keys.parameter ·.kind)) inputs).run ⟨fun _ => [], label, k⟩)
        set (state.label, k + 1)
        pure (some outputs)) top tree).run' (0, 0) | failure
  pure output

/-- The real ceremony. -/
def ceremony (circuits : Circuits) (settings : Settings) (i : C.Party) (keys : Keys C) (top : TopTree)
    (tree : Tree) : PartyM C E G TreeOutput :=
  ceremonyWith K circuits settings (fun ctx _ _ => realRunGadgets K ctx settings.mode) i keys top tree

end Ceremony

/-! ## The trusted dealer -/

/-- The keys of operator `i` from a parameter, the seeds and the pair keys. -/
def dealtKeys (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (i : C.Party) : Keys C :=
  ⟨parameter, fun T => if i ∈ C.holders T then seeds T else 0,
    fun j => if h : j = i then 0 else pairKeys (C.pairOf i j (Ne.symm h))⟩

/-- PRAWNS `KeyGen'` (Section 5.1) for leanXMSS. It samples a uniform parameter, uniform term seeds
and uniform pair keys, and gives each operator the seeds of its held terms and its pair keys. -/
def prawnsKeyGen : ProbComp (PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C)) := do
  let parameter ← $ᵗ PublicParameter
  let seeds ← $ᵗ (C.Term → HashOutput)
  let pairKeys ← $ᵗ (C.Pair → HashOutput)
  pure (parameter, seeds, dealtKeys parameter seeds pairKeys)

/-- The outputs of a ceremony in the clear by leanXMSS, with the PRF values from `F`. This is the
key generation of PRAWNS, Section 3.1, for the trees of leanXMSS. -/
def referenceTree {m : Type → Type} [Monad m] (lift : ∀ {α : Type}, OracleComp HashSpec α → m α)
    (F : Point → m Digest) (parameter : PublicParameter) (top : TopTree) (tree : Tree) : m (Option TreeOutput) :=
  ceremonyOutput lift parameter (fun jobs => some <$> jobs.mapM (referenceJob lift F parameter)) top tree

/-! ## Signing -/

/-- `L_i`, the terms whose first holder in `J` is operator `i` (PRAWNS, Section 5). -/
def L (J : C.Quorum) (i : C.Party) : Finset C.Term :=
  Finset.univ.filter fun T => (J.1 \ T.1).min = i

/-- `Eval'(sk'_i, J, x, ec)` of PRAWNS, Section 5.1, with the message as the evaluation context. It
gives the terms of `L_i` and one mask `H16(K_ij ‖ x ‖ m ‖ J)` for each other signer `j`. -/
def eval (keys : Keys C) (i : C.Party) (J : C.Quorum) (x : Point) (message : Message) :
    OracleComp (RoSpec C) Digest := do
  let terms ← (C.terms.filter (· ∈ L J i)).mapM fun T => prf (keys.seed T) x
  let masks ← (C.parties.filter fun j => j ∈ J.1 ∧ j ≠ i).mapM fun j =>
    truncateHash <$> hashQuery (.mask (keys.pairKey j) x message J)
  pure ((terms ++ masks).foldl (· ^^^ ·) 0)

/-- `Combine'`, the sum of the parts of the quorum. -/
def combine (J : C.Quorum) (parts : C.Party → Digest) : Digest :=
  (C.parties.filter (· ∈ J.1)).foldl (fun acc j => acc ^^^ parts j) 0

/-- Round 1 of signer `i` computes its part of `F(A_rnd(e))`. -/
def signRound1 (keys : Keys C) (i : C.Party) (J : C.Quorum) (e : KeyIndex) (message : Message) :
    OracleComp (RoSpec C) Digest :=
  eval keys i J (.randomizer bottomLayer e) message

/-- The codeword of a signature at key `e` from the opened randomizer value, or `none` if it does
not match the commitment `c_e` or the search fails. -/
def signCodeword (parameter : PublicParameter) (commitment : Digest) (e : KeyIndex) (message : Message)
    (ρ : Digest) : OracleComp (RoSpec C) (Option (Randomness × Encoding)) := tweakable do
  let opened := truncateHash (← Concrete.oracleHash (commitmentInput parameter e ρ))
  if opened ≠ commitment then pure none else
  let base := truncateHash (← Concrete.oracleHash
    (randomizerInput parameter bottomLayer e ρ (bytesLE 32 message)))
  grind parameter bottomLayer e (bytesLE 32 message) base randomizerAttemptLimit 0

/-- Round 2 of a signer checks `c_e` from the parts of round 1 and finds the codeword. Then it sends
its parts `part x` of `F(x_{l, p_l})` for each chain with `p_l < 3`. -/
def signRound2With {m : Type → Type} [Monad m] (lift : ∀ {α : Type}, OracleComp (RoSpec C) α → m α)
    (part : Point → m Digest) (parameter : PublicParameter) (J : C.Quorum) (commitment : Digest)
    (e : KeyIndex) (message : Message) (parts : C.Party → Digest) : m (Option (ChainIndex → Option Digest)) := do
  let some (_, encoding) ← lift (signCodeword parameter commitment e message (combine J parts))
    | pure none
  let values ← Concrete.sequenceFin fun l =>
    if (encoding l).val < chainLength - 1 then some <$> part (.chain bottomLayer e l (encoding l))
    else pure none
  pure (some values)

/-- Round 2 of signer `i` with its keys. -/
def signRound2 (keys : Keys C) (i : C.Party) (J : C.Quorum) (commitment : Digest) (e : KeyIndex)
    (message : Message) (parts : C.Party → Digest) : OracleComp (RoSpec C) (Option (ChainIndex → Option Digest)) :=
  signRound2With (fun oa => oa) (fun x => eval keys i J x message) keys.parameter J commitment e message parts

/-- The leanXMSS signature of a quorum at bottom key `e`, from the parts of both rounds. Each signer
checks that every chain value leads to its chain end. -/
def assemble (parameter : PublicParameter) (tree : BottomTree) (e : KeyIndex) (message : Message)
    (J : C.Quorum) (parts : C.Party → Digest) (chainParts : C.Party → ChainIndex → Digest) :
    OracleComp (RoSpec C) (Option Signature) := do
  let some (randomness, encoding) ← signCodeword parameter (tree.commitment e) e message
      (combine J parts) | pure none
  tweakable do
  let value := fun l => match (encoding l).val with
    | 0 => combine J (chainParts · l)
    | 3 => (tree.cpk e l).2.2
    | p => (if p = 1 then (tree.cpk e l).1 else (tree.cpk e l).2.1) ^^^ combine J (chainParts · l)
  let ends ← Concrete.sequenceFin fun l => Concrete.recoverChain parameter bottomLayer e l (encoding l) (value l)
  if ∃ l, ends l ≠ (tree.cpk e l).2.2 then pure none else
  let path ← merklePath parameter bottomLayer (fun e l => (tree.cpk e l).2.2) e
  pure (some ⟨e, fun lay => if lay = bottomLayer then ⟨randomness, value, path⟩ else tree.topSignature⟩)

/-! ## The oracle world -/

attribute [local instance] Classical.propDecidable

/-- The inputs of `Th` that the MPC evaluates as a circuit, namely a chain step and the commitment
`c_e`. -/
def MpcInput (input : HashInput) : Prop :=
  (∃ parameter lay key step l value, input = tweakableHashInput parameter (.chain lay key step)
    (Concrete.chainPayload l value)) ∨
  ∃ parameter e ρ, input = commitmentInput parameter e ρ

instance : SampleableType Bit := SampleableType.ofFintype Bit

/-- AES-128 as a PRF from a 128-bit key and a stream position `(ρ, idx, position)` to one bit. -/
abbrev Aes := PRFScheme Digest (ℕ × ℕ × ℕ) Bit

/-- The fixed functions of the claims, namely `Th` on the inputs that the MPC evaluates and AES-128. -/
structure Primitives where
  Th : HashInput → HashOutput
  aes : Aes

/-- A programming query asks to set `H` at one input to one output. -/
abbrev ProgramSpec (C : Committee) := (Query C × HashOutput) →ₒ Bool

/-- The oracles of the explicit simulator, namely the local oracles and the programming of `H`. -/
abbrev SimulatorSpec (C : Committee) := LocalSpec C + ProgramSpec C

/-- The oracles of a run, namely a counted copy of the oracles of the simulator and a free copy of
the local oracles. -/
abbrev WorldSpec (C : Committee) := SimulatorSpec C + LocalSpec C

/-- The cache of the random-oracle domains of `H`. -/
abbrev HashCache (C : Committee) := (Query C →ₒ HashOutput).QueryCache

/-- A computation on the counted copy. -/
def counted {α : Type} (oa : OracleComp (SimulatorSpec C) α) : OracleComp (WorldSpec C) α :=
  simulateQ (fun t => query (spec := WorldSpec C) (.inl t)) oa

/-- A computation on the free copy. -/
def free {α : Type} (oa : OracleComp (LocalSpec C) α) : OracleComp (WorldSpec C) α :=
  simulateQ (fun t => query (spec := WorldSpec C) (.inr t)) oa

variable (prims : Primitives)

/-- `H` answers an input that the MPC evaluates with `Th`, and every other input as a lazy random
oracle. -/
def hashAnswer : QueryImpl (Query C →ₒ HashOutput) (StateT (HashCache C) ProbComp) := fun q =>
  match q with
  | .hash input => if MpcInput input then pure (prims.Th input) else (Query C →ₒ HashOutput).randomOracle q
  | q => (Query C →ₒ HashOutput).randomOracle q

/-- `PRG(key, ρ, idx)` at one position, AES-128 under the first 128 bits of `H(key)`. -/
def prgAnswer : QueryImpl (PrgInput C →ₒ Bit) (StateT (HashCache C) ProbComp) := fun x => do
  let derived ← hashAnswer prims (.streamKey x.2.1)
  pure (prims.aes.eval (truncateHash derived) x.2.2)

/-- Private sampling, `H` and `PRG`. -/
def localAnswer : QueryImpl (LocalSpec C) (StateT (HashCache C) ProbComp) :=
  unifFwdImpl (Query C →ₒ HashOutput) + (hashAnswer (C := C) prims + prgAnswer (C := C) prims)

/-- The programmable random oracle sets `H` only at a random-oracle input that no one queried, and
tells whether it did (CDG+18). -/
def programAnswer (x : Query C × HashOutput) : StateT (HashCache C) ProbComp Bool := do
  let cache ← get
  if (∃ input, x.1 = .hash input ∧ MpcInput input) ∨ (cache x.1).isSome then pure false else do
    set (cache.cacheQuery x.1 x.2)
    pure true

/-- The world. Both copies share one cache. Each call of a random-oracle domain of `H`, each call of
`PRG` and each programming query on the counted copy costs one query. The fixed part of `Th` costs
nothing. -/
def world : QueryImpl (WorldSpec C) (AddWriterT ℕ (StateT (HashCache C) ProbComp)) :=
  QueryImpl.withAddCost (localAnswer (C := C) prims + programAnswer (C := C) + localAnswer (C := C) prims :
      QueryImpl (WorldSpec C) (StateT (HashCache C) ProbComp))
    fun | .inl (.inl (.inl _)) => 0 | .inl (.inl (.inr (.inl (.hash input)))) => if MpcInput input then 0 else 1
        | .inl _ => 1 | .inr _ => 0

/-- The world that counts every call of `Th` on a leaf, a node or a message digest, on both copies. -/
def treeWorld : QueryImpl (WorldSpec C) (AddWriterT ℕ (StateT (HashCache C) ProbComp)) :=
  QueryImpl.withAddCost (localAnswer (C := C) prims + programAnswer (C := C) + localAnswer (C := C) prims :
      QueryImpl (WorldSpec C) (StateT (HashCache C) ProbComp))
    fun | .inl (.inl (.inr (.inl (.hash input)))) => if MpcInput input then 0 else 1
        | .inr (.inr (.inl (.hash input))) => if MpcInput input then 0 else 1
        | _ => 0

/-- Run a computation in the world from an empty cache, with its number of counted queries. -/
def runWorld {α : Type} (oa : OracleComp (WorldSpec C) α) : ProbComp (α × ℕ) :=
  (simulateQ (world prims) oa).run.run' ∅

/-- Every execution makes at most `q` counted queries. In an ideal run these are the calls of the
simulator, which runs the adversary, its programming queries, and the calls of the distinguisher. -/
def HasHashQueryBound {α : Type} (run : ProbComp (α × ℕ)) (q : ℕ) : Prop :=
  ∀ r ∈ support run, r.2 ≤ q

/-- Every execution makes at most `N` calls of `Th` on a leaf, a node or a message digest, by every
party. -/
def HasTreeCallBound {α : Type} (oa : OracleComp (WorldSpec C) α) (N : ℕ) : Prop :=
  ∀ r ∈ support ((simulateQ (treeWorld prims) oa).run.run' ∅), r.2 ≤ N

/-- The probability that a computation outputs `true`. -/
def accepts (oa : OracleComp (WorldSpec C) Bool) : ℝ := (Pr[fun r => r.1 = true | runWorld prims oa]).toReal

/-! ## The network -/

/-- An ideal functionality. It knows the fixed coalition, reads the input of each honest operator,
talks to the adversary by leak and reply, and gives each honest operator an output or an abort. The
execution runs it only when every honest operator has an input. -/
structure Functionality (C : Committee) (I O L R : Type) where
  run : C.Coalition → (C.Party → Option I) → OracleComp (LocalSpec C + (L →ₒ R)) (C.Party → Option O)

/-- A call to a functionality gives an output or an abort. -/
abbrev CallSpec (I O : Type) := I →ₒ Option O

/-- The real network has no functionality. -/
abbrev RealSpec := CallSpec PEmpty PEmpty

def noFunctionality : Functionality C PEmpty PEmpty PEmpty PEmpty := ⟨fun _ _ => pure fun _ => none⟩

/-- The auxiliary input `z` of the adversary and of the simulator (Canetti 2000). -/
abbrev Aux := List Bool

/-- A rushing adversary. It starts from the inputs of the corrupt operators and the auxiliary input.
Each round it reads the messages to the corrupt operators, then it sends the messages of the corrupt
operators. It also answers the functionality of the hybrid model. -/
structure Adversary (C : Committee) (E I L R : Type) where
  State : Type
  start : (C.Party → Option I) → Aux → OracleComp (LocalSpec C) State
  round : State → (C.Party → C.Party → Option (Msg E)) →
    OracleComp (LocalSpec C) (State × (C.Party → C.Party → Option (Msg E)))
  answer : State → L → OracleComp (LocalSpec C) (State × R)

/-- The inputs of the corrupt operators. -/
def corruptInputs {I : Type} (D : C.Coalition) (x : C.Party → I) : C.Party → Option I :=
  fun i => if i ∈ D.1 then some (x i) else none

/-- Where the steps of the adversary and the local steps of the honest operators run. -/
structure Roles (C : Committee) (m : Type → Type) where
  adversary : ∀ {β : Type}, OracleComp (LocalSpec C) β → m β
  honest : ∀ {β : Type}, OracleComp (LocalSpec C) β → m β

/-- The adversary runs on the counted copy and the honest operators on the free copy. -/
def worldRoles : Roles C (OracleComp (WorldSpec C)) := ⟨fun oa => counted (liftComp oa _), free⟩

section Network

variable {α : Type}

def Step.outbox : Step C E G α → Mail C E
  | .wait outbox _ => outbox
  | _ => fun _ => none

/-- The message to `j` in a round, with the abort frame of an operator that aborted. -/
def Step.delivered : Step C E G α → Mail C E
  | .wait outbox _ => outbox
  | .done none => fun _ => some .abort
  | _ => fun _ => none

def Step.output : Step C E G α → Option α
  | .done out => out
  | _ => none

def Step.isDone : Step C E G α → Prop
  | .done _ => True
  | _ => False

def Step.callInput : Step C E G α → Option ι
  | .call input _ => some input
  | _ => none

end Network

section Execution

variable {m : Type → Type} [Monad m] {I O L R α Ia : Type}

/-- The functionality of the hybrid model on the inputs of the honest operators, with the adversary
on its interface. If an honest operator has no input, because it aborted, every honest operator
aborts and nothing leaks. -/
def runFunctionality (Ro : Roles C m) (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (state : A.State) (inputs : C.Party → Option I) : m (A.State × (C.Party → Option O)) := do
  if ¬ ∀ i, i ∉ D.1 → (inputs i).isSome then return (state, fun _ => none)
  let impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT A.State m) :=
    (fun t => StateT.lift (Ro.honest (OracleComp.lift (OracleSpec.query t)))) +
    (fun (l : L) => (StateT.mk fun st => do
      let (st, r) ← Ro.adversary (A.answer st l)
      pure (r, st) : StateT A.State m R))
  let (outputs, state) ← (simulateQ impl (F.run D inputs)).run state
  pure (state, outputs)

/-- One synchronous step. When every running honest operator calls the functionality, it runs.
Otherwise one round runs, and an honest operator that calls out of turn aborts. -/
def stepRound (Ro : Roles C m) (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α) :
    m (A.State × (C.Party → Step C E (CallSpec I O) α) × (C.Party → C.Party → Option (Msg E))) := do
  if (∃ i, i ∉ D.1 ∧ (steps i).callInput.isSome) ∧ ∀ i, i ∉ D.1 → (steps i).callInput.isSome ∨ (steps i).isDone then
    let (state, outputs) ← runFunctionality Ro D A F state fun i => if i ∈ D.1 then none else (steps i).callInput
    let steps' ← Concrete.sequenceFin fun j => match steps j with
      | .call _ resume => if j ∈ D.1 then pure (Step.done none) else Ro.honest (advance (resume (outputs j)))
      | step => pure step
    pure (state, steps', fun _ _ => none)
  else
    let (state, sent) ← Ro.adversary (A.round state fun c i =>
      if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none)
    let steps' ← Concrete.sequenceFin fun j => match steps j with
      | .done out => pure (Step.done out)
      | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
          Ro.honest (advance (resume fun k => if k ∈ D.1 then sent k j else (steps k).delivered j))
      | .call _ _ => pure (Step.done none)
    pure (state, steps', sent)

/-- Run the honest programs for at most `fuel` steps. A program that is still running then aborts. -/
def executeRounds (Ro : Roles C m) (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R) :
    ℕ → A.State → (C.Party → Step C E (CallSpec I O) α) → m (A.State × (C.Party → Option α))
  | 0, state, steps => pure (state, fun i => (steps i).output)
  | fuel + 1, state, steps =>
    if ∀ i, i ∉ D.1 → (steps i).isDone then pure (state, fun i => (steps i).output) else do
    let (state, steps, _) ← stepRound Ro D A F state steps
    executeRounds Ro D A F fuel state steps

/-- The first steps of the honest programs. -/
def startSteps (Ro : Roles C m) (D : C.Coalition) (program : C.Party → PartyM C E (CallSpec I O) α) :
    m (C.Party → Step C E (CallSpec I O) α) :=
  Concrete.sequenceFin fun i => if i ∈ D.1 then pure (Step.done none) else Ro.honest (advance (program i).run)

/-- One phase of at most `fuel` steps. -/
def executePhase (Ro : Roles C m) (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E (CallSpec I O) α) :
    m (A.State × (C.Party → Option α)) := do
  executeRounds Ro D A F fuel state (← startSteps Ro D program)

end Execution

/-! ## Secure computation -/

/-- A simulator with the oracles `S`. It starts from the inputs of the corrupt operators and the
auxiliary input, answers the leaks of a functionality, and ends with an output of the type of the
state of the adversary. -/
structure Simulator {κ : Type} (S : OracleSpec κ) (I L R σ : Type) where
  State : Type
  start : (C.Party → Option I) → Aux → OracleComp S State
  answer : State → L → OracleComp S (State × R)
  output : State → OracleComp S σ

/-- The calls of a local computation that the budget counts, namely the random-oracle inputs of `H`
and `PRG`. -/
def Counted : (LocalSpec C).Domain → Prop
  | .inr (.inl (.hash input)) => ¬ MpcInput input
  | .inr _ => True
  | .inl _ => False

/-- A distinguisher reads the joint output of the adversary and the honest operators, with oracle
access (GL05 and Canetti 2000). -/
abbrev Distinguisher (C : Committee) (σ O : Type) := σ × (C.Party → Option O) → OracleComp (LocalSpec C) Bool

/-- A `q`-query adversary with its distinguisher, in the sense of BR93. For every answer of the
oracles, the start makes at most `start` counted calls, each round and each reply at most `step`, and
the distinguisher at most `final`, and a run of `fuel` steps stays within `q`. A step runs one round
or one functionality, and each functionality of the model leaks once. -/
def IsQueryBounded {I L R O : Type} (A : Adversary C E I L R) (Z : Distinguisher C A.State O) (fuel q : ℕ) : Prop :=
  ∃ start step final : ℕ, start + fuel * step + final ≤ q ∧
    (∀ x z, IsQueryBoundP (A.start x z) Counted start) ∧
    (∀ state sent, IsQueryBoundP (A.round state sent) Counted step) ∧
    (∀ state l, IsQueryBoundP (A.answer state l) Counted step) ∧
    (∀ r, IsQueryBoundP (Z r) Counted final)

/-- The real execution of a protocol in the hybrid model of `Fh`, on the inputs `x` and the auxiliary
input `z`. -/
def realExecution {I O Ih Oh Lh Rh : Type} (D : C.Coalition) (A : Adversary C E I Lh Rh)
    (Fh : Functionality C Ih Oh Lh Rh) (fuel : ℕ) (program : C.Party → I → PartyM C E (CallSpec Ih Oh) O)
    (x : C.Party → I) (z : Aux) : OracleComp (WorldSpec C) (A.State × (C.Party → Option O)) := do
  let state ← worldRoles.adversary (A.start (corruptInputs D x) z)
  executePhase worldRoles D A Fh fuel state fun i => program i (x i)

/-- The ideal execution of `F` with the simulator `Sim`. The functionality runs on the free copy. -/
def idealExecution {κ : Type} {S : OracleSpec κ} {I O L R σ : Type}
    (lift : ∀ {β : Type}, OracleComp S β → OracleComp (WorldSpec C) β) (D : C.Coalition)
    (F : Functionality C I O L R) (Sim : Simulator (C := C) S I L R σ) (x : C.Party → I) (z : Aux) :
    OracleComp (WorldSpec C) (σ × (C.Party → Option O)) := do
  let state ← lift (Sim.start (corruptInputs D x) z)
  let impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT Sim.State (OracleComp (WorldSpec C))) :=
    (fun (t : (LocalSpec C).Domain) =>
      (StateT.lift (free (C := C) (OracleComp.lift (OracleSpec.query t))) : StateT Sim.State _ _)) +
    (fun (l : L) => (StateT.mk fun st => do
      let (st, r) ← lift (Sim.answer st l)
      pure (r, st) : StateT Sim.State (OracleComp (WorldSpec C)) R))
  let (outputs, state) ← (simulateQ impl (F.run D fun i => if i ∈ D.1 then none else some (x i))).run state
  pure (← lift (Sim.output state), outputs)

/-- An execution followed by the distinguisher on the counted copy. -/
def distinguish {σ O : Type} (oa : OracleComp (WorldSpec C) (σ × (C.Party → Option O)))
    (Z : Distinguisher C σ O) : OracleComp (WorldSpec C) Bool :=
  oa >>= fun r => worldRoles.adversary (Z r)

/-- The protocol `program` in the `Fh`-hybrid model securely computes `F` on the valid inputs
(Canetti 2000, GS20). For each coalition and adversary there is a simulator without programming, and
all its calls are counted. It is fixed before the inputs, the auxiliary input, the distinguisher and
the budget, and it sees only the corrupt inputs, the auxiliary input and the leaks of `F`. For a
`q`-query adversary and distinguisher, the ideal run makes at most `q + overhead` counted queries,
and the error is `ε q`. -/
def SecurelyComputes {I O L R Ih Oh Lh Rh : Type} (program : C.Party → I → PartyM C E (CallSpec Ih Oh) O)
    (fuel : ℕ) (Fh : Functionality C Ih Oh Lh Rh) (F : Functionality C I O L R)
    (valid : C.Coalition → (C.Party → I) → Prop) (overhead : ℕ) (ε : ℕ → ℝ) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E I Lh Rh), ∃ S : Simulator (C := C) (LocalSpec C) I L R A.State,
    ∀ (x : C.Party → I) (z : Aux) (Z : Distinguisher C A.State O) (q : ℕ), valid D x →
      IsQueryBounded A Z fuel q →
      HasHashQueryBound (runWorld prims (distinguish (idealExecution worldRoles.adversary D F S x z) Z))
          (q + overhead) ∧
        |accepts prims (distinguish (realExecution D A Fh fuel program x z) Z) -
          accepts prims (distinguish (idealExecution worldRoles.adversary D F S x z) Z)| ≤ ε q

/-- The protocol `program` on the real network securely computes `F` on the valid inputs with the
explicit simulator `Sim D A`. It is fixed code that runs the adversary on the counted copy, emulates
the honest operators on the free copy as the real operators do, and may program `H`. For a `q`-query adversary and distinguisher, the
ideal run makes at most `q + overhead` counted queries, and the error is `ε D A x z Z q`. -/
def SimulatedBy {I O L R : Type} (program : C.Party → I → PartyM C E RealSpec O) (fuel : ℕ)
    (F : Functionality C I O L R) (valid : C.Coalition → (C.Party → I) → Prop)
    (Sim : (D : C.Coalition) → (A : Adversary C E I PEmpty PEmpty) → Simulator (C := C) (WorldSpec C) I L R A.State)
    (overhead : ℕ)
    (ε : (D : C.Coalition) → (A : Adversary C E I PEmpty PEmpty) → (C.Party → I) → Aux →
      Distinguisher C A.State O → ℕ → ℝ) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E I PEmpty PEmpty) (x : C.Party → I) (z : Aux)
    (Z : Distinguisher C A.State O) (q : ℕ), valid D x →
    IsQueryBounded A Z fuel q →
    HasHashQueryBound (runWorld prims (distinguish (idealExecution (fun oa => oa) D F (Sim D A) x z) Z))
        (q + overhead) ∧
      |accepts prims (distinguish (realExecution D A noFunctionality fuel program x z) Z) -
        accepts prims (distinguish (idealExecution (fun oa => oa) D F (Sim D A) x z) Z)| ≤ ε D A x z Z q

def noCoalition : C.Coalition := ⟨∅, by simp⟩

/-- The adversary of an honest run. It controls no operator and replies `reply` to each leak. -/
def honestAdversary {I L R : Type} (reply : L → R) : Adversary C E I L R :=
  ⟨Unit, fun _ _ => pure (), fun _ _ => pure ((), fun _ _ => none), fun _ l => pure ((), reply l)⟩

/-- The simulator of an honest run, which replies `reply` to each leak. -/
def honestSimulator {κ : Type} {S : OracleSpec κ} {I L R : Type} (reply : L → R) :
    Simulator (C := C) S I L R Unit :=
  ⟨Unit, fun _ _ => pure (), fun _ l => pure ((), reply l), fun _ => pure ()⟩

/-- An honest run of `program` in the `Fh`-hybrid model gives the outputs of `F` on the valid inputs,
up to `ε` in statistical distance. Each functionality gets the reply of an honest adversary. -/
def Completes {I O L R Ih Oh Lh Rh : Type} (program : C.Party → I → PartyM C E (CallSpec Ih Oh) O)
    (fuel : ℕ) (Fh : Functionality C Ih Oh Lh Rh) (replyH : Lh → Rh) (F : Functionality C I O L R)
    (reply : L → R) (valid : C.Coalition → (C.Party → I) → Prop) (ε : ℝ) : Prop :=
  ∀ x : C.Party → I, valid noCoalition x →
    tvDist ((fun r => r.1.2) <$> runWorld prims
        (realExecution noCoalition (honestAdversary replyH) Fh fuel program x []))
      ((fun r => r.1.2) <$> runWorld prims
        (idealExecution (fun oa => oa) noCoalition F (honestSimulator reply) x [])) ≤ ε

/-! ## Programs in the hybrid models of GS20 -/

section Hybrid

variable [Field E] [Algebra Bit E] (K : Constants C E)

def startRun : RunState C := ⟨fun _ => [], 0, 0⟩

/-- `Coin` in the `F_rand`-hybrid model (GS20, Protocol 6). -/
def coinProtocol (i : C.Party) (count : ℕ) : PartyM C E (CallSpec ℕ (PrssOutput C E)) (List E) := do
  let some randomness ← call count | failure
  (coinWith K (localContext i) randomness count).run' startRun

/-- `MulRep` and `Reshare` in `mode` in the `F_rand`-hybrid model (GS20, Protocol 8). -/
def multProtocol (mode : ReshareMode) (i : C.Party) (input : Shares C Bit × Shares C Bit × ℕ) :
    PartyM C E (CallSpec ℕ (PrssOutput C Bit)) (Shares C Bit) := do
  let (x, y, count) := input
  let some randomness ← call count | failure
  (reshareWith K (localContext i) mode randomness (mulRep K (localContext i) x y) count).run' startRun

/-- `MulRep` or `MulSh` and `Reshare` in the `F_rand`-hybrid model (GS20, Protocol 10). -/
def extendMultProtocol (i : C.Party) (products : List (Product C E)) :
    PartyM C E (CallSpec ℕ (PrssOutput C E)) (Shares C E) := do
  let some randomness ← call products.length | failure
  let ctx := localContext i
  (reshare K ctx (elementCodec K) randomness
    (fun g => match products[g]? with | some p => productShare K ctx p | none => 0)
    products.length).run' startRun

/-- The functionalities of the check, namely `F_coin`, `F_extendMult`, and `F_rand` over `E` and over
bits. -/
abbrev CheckSpec (C : Committee) (E : Type) :=
  CallSpec ((ℕ ⊕ List (Product C E)) ⊕ (ℕ ⊕ ℕ)) ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit))

/-- The gadgets of the check as calls. Each call takes one round label, as each real gadget does. -/
def hybridCheckGadgets (i : C.Party) : CheckGadgets C E (CheckSpec C E) where
  coin count := do
    let _ ← freshLabel
    let some (.inl (.inl values)) ← StateT.lift (call (.inl (.inl count))) | StateT.lift failure
    pure values
  extendMult products := do
    let _ ← freshLabel
    let some (.inl (.inr z)) ← StateT.lift (call (.inl (.inr products))) | StateT.lift failure
    record K (localContext i) (elementCodec K) .peer z products.length
    pure z
  randElements count := do
    let _ ← freshLabel
    let some (.inr (.inl randomness)) ← StateT.lift (call (.inr (.inl count))) | StateT.lift failure
    pure randomness
  randBits count := do
    let _ ← freshLabel
    let some (.inr (.inr randomness)) ← StateT.lift (call (.inr (.inr count))) | StateT.lift failure
    pure randomness

/-- The values that the reshares of the tuples fill, which start the running values of the check. -/
def filledHistory (i : C.Party) (tuples : List (Tuple C)) (T : C.Term) : List Bit :=
  if i ∈ C.holders T then tuples.flatMap fun τ =>
    ((List.range τ.count).filter fun g => (filler K τ.mode T g).isSome).map (τ.z T)
  else []

/-- The check in the `{F_coin, F_extendMult, F_rand}`-hybrid model (GS20, Protocol 17). -/
def checkProtocol (i : C.Party) (tuples : List (Tuple C)) : PartyM C E (CheckSpec C E) Unit :=
  (check K (localContext i) (hybridCheckGadgets K i) tuples).run' ⟨filledHistory K i tuples, 0, 0⟩

/-- The functionalities of a run, namely `F_mult` of the AND gates, `F_mult` in peer mode for
`Rerand`, and `F_multVerify`. -/
abbrev MainSpec (C : Committee) :=
  CallSpec (((Shares C Bit × Shares C Bit × ℕ) ⊕ (Shares C Bit × Shares C Bit × ℕ)) ⊕ List (Tuple C))
    ((Shares C Bit ⊕ Shares C Bit) ⊕ Unit)

/-- The gadgets of a run as calls, with `Rerand` as a product with `[[1]]` (GS20, Protocol 19). -/
def hybridRunGadgets (mode : ReshareMode) (i : C.Party) : RunGadgets C E (MainSpec C) where
  mode := mode
  mult x y count := do
    let some (.inl (.inl z)) ← StateT.lift (call (.inl (.inl (x, y, count)))) | StateT.lift failure
    pure z
  rerand v count := do
    let some (.inl (.inr z)) ← StateT.lift (call (.inl (.inr (v, one K, count)))) | StateT.lift failure
    pure z
  verify tuples := do
    let some (.inr ()) ← StateT.lift (call (.inr tuples)) | StateT.lift failure
  output v count := StateT.lift (openRep K (localContext i) v count)

/-- A run in the `{F_mult, F_multVerify}`-hybrid model (GS20, Protocol 19). -/
def mainProtocol (mode : ReshareMode) (jobs : List Circuit) (i : C.Party) (inputs : List (C.Term → List Bit)) :
    PartyM C E (MainSpec C) (List (List Bit)) :=
  (runJobs K (hybridRunGadgets K mode i) jobs inputs).run' startRun

end Hybrid

/-! ## Honest runs -/

/-- The empty top tree, which the top ceremony takes. -/
def emptyTop : TopTree := ⟨fun _ _ => 0, 0⟩

/-- The tree of an output, if it is a top tree. -/
def TreeOutput.topTree : Option TreeOutput → Option TopTree
  | some (.top tree) => some tree
  | _ => none

/-- The batches of a ceremony, at most. -/
def ceremonyBatches (settings : Settings) : ℕ :=
  (chunks settings.batchSize topJobs).length ⊔
    ((chunks settings.batchSize (bottomJobs 0)).length + (chunks settings.batchSize (signJobs 0 fun _ => digit 0)).length)

/-- The circuits of the jobs of a run. -/
def runCircuits (circuits : Circuits) (parameter : PublicParameter) (jobs : List Job) : List Circuit :=
  jobs.map (circuits parameter ·.kind)

/-- The most of a measure over all batches of all runs of all ceremonies. -/
def maxBatch (circuits : Circuits) (settings : Settings) (measure : List Circuit → ℕ) : ℕ :=
  Finset.univ.sup fun x : PublicParameter × Fin (2 ^ layerHeight) × Encoding =>
    (([topJobs, bottomJobs x.2.1, signJobs x.2.1 x.2.2].flatMap (chunks settings.batchSize)).map
      fun jobs => measure (runCircuits circuits x.1 jobs)).foldl max 0

/-- A ceremony runs the PRSS setup and its batches. -/
def ceremonyFuel (circuits : Circuits) (settings : Settings) : ℕ :=
  setupRounds + ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode)


/-- `KeyGen` of PRAWNS, Section 3.1, for leanXMSS, as the signing game needs it. `part` gives the
part of operator `i` of `F(x)` for quorum `J` and message `m`, and `value` gives `F(x)`. -/
structure Dealt (C : Committee) (m : Type → Type) where
  keys : C.Party → Keys C
  parameter : PublicParameter
  top : TopTree
  value : Point → m Digest
  part : C.Party → C.Quorum → Point → Message → m Digest
  bottom : Fin (2 ^ layerHeight) → m (Option BottomTree)

/-- The bottom tree of a bottom key. -/
def treeOf (e : KeyIndex) : Fin (2 ^ layerHeight) :=
  ⟨e.val / 2 ^ layerHeight, by
    have := e.isLt; simp only [lifetime, numLayers, layerHeight] at *; omega⟩

section Dealer

variable {m : Type → Type} [Monad m]

/-- `KeyGen` of PRAWNS with `KeyGen'` and the trees of leanXMSS, with the PRF values from `value`. -/
def dealtWith (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) (parameter : PublicParameter)
    (keys : C.Party → Keys C) (top : TopTree) (value : Point → m Digest) : Dealt C m where
  keys := keys
  parameter := parameter
  top := top
  value := value
  part i J x message := lift (eval (keys i) i J x message)
  bottom b := (fun | some (.bottom tree) => some tree | _ => none) <$>
    referenceTree (fun oa => lift (tweakable oa)) value parameter top (.bottom b)

/-- `KeyGen` with the local oracles in `m`. It is `none` if a randomizer search of a top signature
fails. -/
def keyGenWith (sample : ∀ {β : Type}, ProbComp β → m β) (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) :
    m (Option (Dealt C m)) := do
  let (parameter, seeds, keys) ← sample prawnsKeyGen
  let value := fun x => lift (prfValue seeds x)
  let some (.top top) ← referenceTree (fun oa => lift (tweakable oa)) value parameter emptyTop .top | pure none
  pure (some (dealtWith lift parameter keys top value))

/-- The signature of `KeyGen` at bottom key `e` for `m`, which every honest quorum outputs. -/
def honestSignature (lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β) (dealt : Dealt C m) (e : KeyIndex)
    (message : Message) : m (Option Signature) := do
  let some tree ← dealt.bottom (treeOf e) | pure none
  let ρ ← dealt.value (.randomizer bottomLayer e)
  let some (randomness, encoding) ← lift (signCodeword dealt.parameter (tree.commitment e) e message ρ)
    | pure none
  let values ← Concrete.sequenceFin fun l => match (encoding l).val with
    | 0 => dealt.value (.chain bottomLayer e l (encoding l))
    | 3 => pure (tree.cpk e l).2.2
    | p => do
        let f ← dealt.value (.chain bottomLayer e l (encoding l))
        pure ((if p = 1 then (tree.cpk e l).1 else (tree.cpk e l).2.1) ^^^ f)
  let path ← lift (tweakable (merklePath dealt.parameter bottomLayer (fun e l => (tree.cpk e l).2.2) e))
  pure (some ⟨e, fun lay => if lay = bottomLayer then ⟨randomness, values, path⟩ else tree.topSignature⟩)

end Dealer

/-- `KeyGen` on the free copy. -/
def keyGen : OracleComp (WorldSpec C) (Option (Dealt C (OracleComp (WorldSpec C)))) :=
  keyGenWith (fun oa => free (liftComp oa _)) (fun oa => free (liftComp oa _))

/-- `Combine'` of the parts of a quorum and `F(msk, x)` under `KeyGen'`. -/
def tprfCorrectnessRun (J : C.Quorum) (x : Point) (ec : Message) : OracleComp (WorldSpec C) Bool := free do
  let (_, seeds, keys) ← liftComp prawnsKeyGen _
  let parts ← liftComp (Concrete.sequenceFin fun i => eval (keys i) i J x ec) _
  let value ← liftComp (prfValue seeds x) _
  pure (decide (combine J parts = value))

/-- An honest quorum signs `m` at key `e` with `KeyGen`. The result is `none` if `KeyGen` or a
randomizer search fails, and otherwise tells whether the signature verifies. -/
def honestSigning (J : C.Quorum) (e : KeyIndex) (message : Message) : OracleComp (WorldSpec C) (Option Bool) := do
  let some dealt ← keyGen | pure none
  let lift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β := fun oa => free (liftComp oa _)
  let some tree ← dealt.bottom (treeOf e) | pure none
  let parts ← Concrete.sequenceFin fun i => if i ∈ J.1 then dealt.part i J (.randomizer bottomLayer e) message else pure 0
  let some _ ← lift (signCodeword dealt.parameter (tree.commitment e) e message (combine J parts)) | pure none
  let chainParts ← Concrete.sequenceFin fun i => do
    let values ← signRound2With lift (fun x => dealt.part i J x message) dealt.parameter J (tree.commitment e) e message parts
    pure fun l => ((values.bind (· l)).getD 0)
  let some signature ← lift (assemble dealt.parameter tree e message J parts chainParts) | pure (some false)
  some <$> lift (tweakable (Concrete.verify ⟨dealt.top.root, dealt.parameter⟩ message signature))

end ThresholdLeanXmss
