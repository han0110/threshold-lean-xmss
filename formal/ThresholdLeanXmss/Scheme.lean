import LeanXmss.Scheme
import VCVio.CryptoFoundations.PRF
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Threshold leanXMSS, the protocol

The key generation of `doc/dkg.md` and the signing of `doc/sign.md`, as programs of one operator.

* An operator program is an `OracleComp` with private sampling, the hash `H`, the stream `PRG`
  and one query `exchange` for each synchronous round. A program that returns `none` aborts.
* A receiver reads a missing or short message as zeros, as the implementation pads short messages.
* The model keeps single bits. The check groups the tuple bits in words of `2 ^ wordBits` bits only
  for the fixed weights `x^q`, so lanes, padding and batch sizes do not change a statement.
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

/-- The bits of a gate form words of `2 ^ wordBits` bits. -/
def wordBits : ℕ := 6

/-- The check folds `2 ^ sliceBits` slices with the small-value steps. -/
def sliceBits : ℕ := 7

/-- The bits of an element of the check field. -/
def elementBits : ℕ := 192

/-- The public constants of a committee. Every choice with these properties is allowed, so the
statements hold for the balanced choice of the implementation. -/
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
  /-- `owner(T)`, the holder that sends the copy of `T` and adds the mask of `T`. -/
  owner : C.Term → C.Party
  owner_held : ∀ T, owner T ∈ C.holders T
  /-- `(T*, κ)` of gate `g` in a collector reshare. -/
  collector : ℕ → C.Term × C.Party
  collector_held : ∀ g, (collector g).2 ∈ C.holders (collector g).1
  /-- The term that a public constant joins. -/
  publicTerm : C.Term
  /-- `x^q`, the weight of bit `q` of a word. -/
  weight : Fin (2 ^ wordBits) → E
  weight_independent : LinearIndependent Bit weight
  /-- The bits of an element of `E`. -/
  encode : E ≃ (Fin elementBits → Bit)

/-- The reshare of the AND gates. The check always uses the peer reshare. -/
inductive ReshareMode
  | peer
  | collector
deriving DecidableEq

/-! ## Messages and programs -/

/-- A message of one round from one operator to another. -/
inductive Msg (E : Type) where
  | bits (values : List Bit)
  | elements (values : List E)
  | bytes (values : List UInt8)
  | bundle (parts : List (Option (Msg E)))

namespace Msg

variable {E : Type} [Zero E]

def bitAt : Option (Msg E) → ℕ → Bit
  | some (.bits values), k => values.getD k 0
  | _, _ => 0

def elementAt : Option (Msg E) → ℕ → E
  | some (.elements values), k => values.getD k 0
  | _, _ => 0

def bytesOf : Option (Msg E) → List UInt8
  | some (.bytes values) => values
  | _ => []

def part : Option (Msg E) → ℕ → Option (Msg E)
  | some (.bundle parts), k => (parts.getD k none)
  | _, _ => none

end Msg

/-- The name of a `PRG` key. The key of a term or a pair stays secret, the key of a coin is
public. -/
inductive KeyName (C : Committee)
  | term (T : C.Term)
  | pair (p : C.Pair)
  | coin
deriving DecidableEq

/-- A batch stream, given by the batch tag, the step and the index `idx` of `doc/dkg.md` 1.1.4. -/
abbrev StreamId := ℕ × ℕ × ℕ

/-- One bit of `PRG(key, session, stream)` at a position. -/
abbrev PrgSpec (C : Committee) :=
  (KeyName C × HashOutput × HashOutput × StreamId × ℕ) →ₒ Bit

/-- Private sampling, the shared hash `H` and the stream `PRG`. -/
abbrev LocalSpec (C : Committee) := unifSpec + HashSpec + PrgSpec C

/-- The messages that one operator sends to, or receives from, each operator. -/
abbrev Mail (C : Committee) (E : Type) := C.Party → Option (Msg E)

/-- One synchronous round sends the outbox and receives the inbox. -/
abbrev RoundSpec (C : Committee) (E : Type) := Mail C E →ₒ Mail C E

abbrev PartySpec (C : Committee) (E : Type) := LocalSpec C + RoundSpec C E

/-- The program of one operator. `none` is an abort. -/
abbrev PartyM (C : Committee) (E : Type) := OptionT (OracleComp (PartySpec C E))

/-- A program stopped at its output or at its next round. -/
inductive Step (C : Committee) (E α : Type) where
  | done (out : Option α)
  | wait (outbox : Mail C E) (resume : Mail C E → OracleComp (PartySpec C E) (Option α))

variable {C : Committee} {E : Type}

/-- Run the local steps of a program up to its output or its next round. -/
def advance {α : Type} : OracleComp (PartySpec C E) (Option α) → OracleComp (LocalSpec C) (Step C E α)
  | .pure out => pure (.done out)
  | .roll (Sum.inl q) k => do
      let r ← OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q)
      advance (k r)
  | .roll (Sum.inr outbox) k => pure (.wait outbox k)

def exchange (outbox : Mail C E) : PartyM C E (Mail C E) :=
  OptionT.lift (OracleComp.lift (OracleSpec.query (spec := PartySpec C E) (Sum.inr outbox)))

def localStep {α : Type} (oa : OracleComp (LocalSpec C) α) : PartyM C E α :=
  OptionT.lift (liftComp oa _)

def require (condition : Prop) : PartyM C E Unit :=
  open Classical in if condition then pure () else failure

/-- Run programs side by side, one round of each per round, as the batches of a ceremony run on
their own channels. The operator aborts all of them when one aborts. -/
def parallel {α : Type} : ℕ → List (OracleComp (PartySpec C E) (Option α)) → PartyM C E (List α)
  | 0, _ => failure
  | fuel + 1, programs => do
      let steps ← localStep (programs.mapM advance)
      if steps.any (fun | .done none => true | _ => false) then failure
      else if steps.all (fun | .done _ => true | _ => false) then
        pure (steps.filterMap fun | .done out => out | _ => none)
      else
        let outbox : Mail C E := fun j => some (.bundle (steps.map fun
          | .wait box _ => box j
          | .done _ => none))
        let inbox ← exchange outbox
        parallel fuel (steps.mapIdx fun k step => match step with
          | .done out => pure out
          | .wait _ resume => resume fun j => Msg.part (inbox j) k)

/-! ## Keys -/

/-- The keys of one operator after the setup. -/
structure Keys (C : Committee) where
  parameter : PublicParameter
  /-- `seed_T` for each held term. -/
  seed : C.Term → HashOutput
  /-- `K_ij` for each other operator `j`. -/
  pairKey : C.Party → HashOutput

/-- A program of operator `i` in a session of a ceremony. -/
structure Context (C : Committee) where
  self : C.Party
  keys : Keys C
  session : HashOutput

/-! ## Streams -/

section Streams

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C)

/-- `count` bits of `PRG(key, session, stream)`. -/
def stream (name : KeyName C) (key : HashOutput) (s : StreamId) (count : ℕ) : PartyM C E (List Bit) :=
  localStep ((List.range count).mapM fun position =>
    query (spec := PrgSpec C) (name, key, ctx.session, s, position))

/-- `count` elements of `E` from `PRG(key, session, stream)`. -/
def streamElements (name : KeyName C) (key : HashOutput) (s : StreamId) (count : ℕ) :
    PartyM C E (List E) := do
  let bits ← stream ctx name key s (elementBits * count)
  pure ((List.range count).map fun k =>
    K.encode.symm fun b => bits.getD (elementBits * k + b) 0)

/-- `Rand(ρ, idx)`, the terms `PRG(seed_T, ρ, idx)` of each held term. -/
def randBits (s : StreamId) (count : ℕ) : PartyM C E (C.Term → List Bit) := do
  let streams ← C.terms.mapM fun T =>
    if ctx.self ∈ C.holders T then stream ctx (.term T) (ctx.keys.seed T) s count else pure []
  pure fun T => streams.getD (C.terms.idxOf T) []

def randElements (s : StreamId) (count : ℕ) : PartyM C E (C.Term → List E) := do
  let streams ← C.terms.mapM fun T =>
    if ctx.self ∈ C.holders T then streamElements K ctx (.term T) (ctx.keys.seed T) s count
    else pure []
  pure fun T => streams.getD (C.terms.idxOf T) []

end Streams


attribute [local instance] Classical.propDecidable

/-! ## Sharings and gadgets

At operator `i`, a replicated sharing is a vector for each term, meaningful at the held terms. A
vector is a function on `ℕ`, and a message carries its first `count` entries. -/

/-- The terms of a replicated sharing at one operator. -/
abbrev Shares (C : Committee) (R : Type) := C.Term → ℕ → R

/-- The running hash `h_T` of each term, of the values that the reshares give it, as bits. -/
abbrev History (C : Committee) := C.Term → List Bit

/-- A program of one batch, which keeps the running hashes. -/
abbrev BatchM (C : Committee) (E : Type) := StateT (History C) (PartyM C E)

/-- How the values of a sharing travel, as bits of the circuit or as elements of the check. -/
structure Codec (C : Committee) (E R : Type) where
  pack : List R → Msg E
  unpack : Option (Msg E) → ℕ → R
  draw : KeyName C → HashOutput → StreamId → ℕ → PartyM C E (ℕ → R)
  toBits : R → List Bit

def vector {R : Type} (count : ℕ) (v : ℕ → R) : List R := (List.range count).map v

def bytesOfBits (bits : List Bit) : List UInt8 := bits.map fun b => if b = 0 then 0 else 1

def bitsOfDigest (d : Digest) : List Bit := List.ofFn fun k : Fin digestBits => if d.getLsbD k then 1 else 0

def digestOfBits (bits : List Bit) : Digest :=
  BitVec.ofNat digestBits (∑ k ∈ Finset.range digestBits, (bits.getD k 0).val * 2 ^ k)

section Gadgets

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C)

def bitCodec : Codec C E Bit where
  pack := .bits
  unpack := Msg.bitAt
  draw name key s count := do
    let bits ← stream ctx name key s count
    pure fun g => bits.getD g 0
  toBits b := [b]

def elementCodec : Codec C E E where
  pack := .elements
  unpack := Msg.elementAt
  draw name key s count := do
    let values ← streamElements K ctx name key s count
    pure fun g => values.getD g 0
  toBits x := List.ofFn (K.encode x)

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

/-- The Lagrange weight of the point of operator `l` at `x`, among the first `t` operators. -/
def lagrangeFirst (x : E) (l : C.Party) : E :=
  ∏ k ∈ (Finset.univ.filter fun k : C.Party => k.val < C.t).erase l,
    (x - K.point k) / (K.point l - K.point k)

/-- The filled terms `C` of the peer reshare. -/
def filledTerms : Finset C.Term := Finset.univ.map K.filled

/-- Append the new values of the terms in `terms` to their running hashes. -/
def record {R : Type} (codec : Codec C E R) (terms : Finset C.Term) (z : Shares C R) (count : ℕ) :
    BatchM C E Unit :=
  modify fun h T =>
    if ctx.self ∈ C.holders T ∧ T ∈ terms then h T ++ (vector count (z T)).flatMap codec.toBits else h T

/-- The pair masks `ζ_i`, which sum to zero over all operators. -/
def pairMasks {R : Type} [AddCommMonoid R] (codec : Codec C E R) (s : StreamId) (count : ℕ) :
    PartyM C E (ℕ → R) := do
  let masks ← C.parties.mapM fun j =>
    if h : j = ctx.self then pure (fun _ => 0)
    else codec.draw (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.keys.pairKey j) s count
  pure fun g => (masks.map (· g)).sum

/-- The masks `r_T` of the held terms. -/
def termMasks {R : Type} [Zero R] (codec : Codec C E R) (s : StreamId) (count : ℕ) :
    PartyM C E (Shares C R) := do
  let masks ← C.terms.mapM fun T =>
    if ctx.self ∈ C.holders T then codec.draw (.term T) (ctx.keys.seed T) s count else pure (fun _ => 0)
  pure fun T => masks.getD (C.terms.idxOf T) (fun _ => 0)

/-- `Reshare` in peer mode, one round. Operator `i` sends `u_i` to the other holders of `T_i`. -/
def resharePeer {R : Type} [Field R] (codec : Codec C E R) (v : ℕ → R) (count : ℕ) (s : StreamId) :
    BatchM C E (Shares C R) := do
  let i := ctx.self
  let r ← termMasks ctx codec s count
  let ζ ← pairMasks ctx codec s count
  let u : ℕ → R := fun g => v g + ζ g +
    ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T = i), r T g
  let inbox ← exchange fun j =>
    if j ≠ i ∧ j ∈ C.holders (K.filled i) then some (codec.pack (vector count u)) else none
  let z : Shares C R := fun T g =>
    if T ∈ filledTerms K then
      ∑ j ∈ Finset.univ.filter (K.filled · = T), if j = i then u g else codec.unpack (inbox j) g
    else r T g
  record ctx codec (filledTerms K) z count
  pure z

/-- The gates `g < count` of a collector reshare, numbered from `offset`, whose collector is `j`. -/
def collectedBy (offset count : ℕ) (j : C.Party) : List ℕ :=
  (List.range count).filter fun g => (K.collector (offset + g)).2 = j

/-- `Reshare` in collector mode, two rounds. Gate `g` sends every `u_i` to its collector `κ`,
which sends the sum to the other holders of `T*`. -/
def reshareCollector (v : ℕ → Bit) (count offset : ℕ) (s : StreamId) : BatchM C E (Shares C Bit) := do
  let i := ctx.self
  let star := fun g => (K.collector (offset + g)).1
  let kappa := fun g => (K.collector (offset + g)).2
  let r ← termMasks ctx (bitCodec (E := E) ctx) s count
  let ζ ← pairMasks ctx (bitCodec (E := E) ctx) s count
  let u : ℕ → Bit := fun g => v g + ζ g +
    ∑ T ∈ Finset.univ.filter (fun T => T ≠ star g ∧ K.owner T = i), r T g
  let inbox ← exchange (E := E) fun j =>
    if j ≠ i then some (.bits ((collectedBy K offset count j).map u)) else none
  let sum : ℕ → Bit := fun g => u g + ∑ j ∈ Finset.univ.erase i,
    Msg.bitAt (inbox j) ((collectedBy K offset count i).idxOf g)
  let forward ← exchange (E := E) fun h =>
    if h ≠ i then some (.bits (((collectedBy K offset count i).filter fun g =>
      h ∈ C.holders (star g)).map sum)) else none
  let z : Shares C Bit := fun T g =>
    if T = star g then
      (if kappa g = i then sum g
       else Msg.bitAt (forward (kappa g))
         (((collectedBy K offset count (kappa g)).filter fun g' => i ∈ C.holders (star g')).idxOf g))
    else r T g
  modify fun h T => if i ∈ C.holders T then
    h T ++ ((List.range count).filter (star · = T)).map (z T) else h T
  pure z

/-- `OpenRep` of a replicated bit vector. For each term, the owner sends its copy and every other
holder sends the hash of its copy to each operator that lacks the term (MPClan, App. B). -/
def openRep (v : Shares C Bit) (count : ℕ) : PartyM C E (ℕ → Bit) := do
  let i := ctx.self
  let digests ← localStep (C.terms.mapM fun T =>
    query (spec := HashSpec) (bytesOfBits (vector count (v T))))
  let inbox ← exchange fun j => some (.bundle (C.terms.mapIdx fun k T =>
    if j ∉ C.holders T ∧ i ∈ C.holders T then
      if K.owner T = i then some (.bits (vector count (v T)))
      else some (.bytes (bytesLE 32 (digests.getD k 0)))
    else none))
  let copy : Shares C Bit := fun T g =>
    if i ∈ C.holders T then v T g else Msg.bitAt (Msg.part (inbox (K.owner T)) (C.terms.idxOf T)) g
  let copyDigests ← localStep (C.terms.mapM fun T =>
    query (spec := HashSpec) (bytesOfBits (vector count (copy T))))
  require (∀ T : C.Term, i ∉ C.holders T → ∀ h : C.Party, h ∈ C.holders T → h ≠ K.owner T →
    Msg.bytesOf (Msg.part (inbox h) (C.terms.idxOf T)) =
      bytesLE 32 (copyDigests.getD (C.terms.idxOf T) 0))
  pure fun g => ∑ T, copy T g

/-- `OpenSh` of a Shamir vector with a payload. Each operator interpolates the shares of the first
`t` operators and aborts unless all `n` shares lie on that polynomial. -/
def openSh (v : ℕ → E) (count : ℕ) (payload : Msg E) :
    PartyM C E ((ℕ → E) × (C.Party → Option (Msg E))) := do
  let i := ctx.self
  let inbox ← exchange fun j =>
    if j = i then none else some (.bundle [some (.elements (vector count v)), some payload])
  let share : C.Party → ℕ → E := fun j g =>
    if j = i then v g else Msg.elementAt (Msg.part (inbox j) 0) g
  let first := Finset.univ.filter fun l : C.Party => l.val < C.t
  require (∀ j : C.Party, ∀ g < count,
    share j g = ∑ l ∈ first, lagrangeFirst K (K.point j) l * share l g)
  pure (fun g => ∑ l ∈ first, lagrangeFirst K 0 l * share l g,
    fun j => if j = i then some payload else Msg.part (inbox j) 1)

/-- `Coin`, the hash of `OpenSh(Conv(Rand(ρ, 1)))`. It also carries a payload from each operator. -/
def coin (s : StreamId) (payload : Msg E) : PartyM C E (HashOutput × (C.Party → Option (Msg E))) := do
  let r ← randElements K ctx s 1
  let (opened, payloads) ← openSh K ctx (conv K ctx fun T g => (r T).getD g 0) 1 payload
  let key ← localStep (query (spec := HashSpec) (bytesOfBits ((elementCodec K ctx).toBits (opened 0))))
  pure (key, payloads)

/-- `count` values of a coin. -/
def coinValues (key : HashOutput) (index count : ℕ) : PartyM C E (List E) :=
  streamElements K ctx .coin key (0, index, 0) count

/-- The challenge of a coin is its first value outside `{0, 1}`. -/
def challenge (key : HashOutput) : ℕ → ℕ → PartyM C E E
  | 0, _ => failure
  | tries + 1, index => do
      let r := (← coinValues K ctx key index 1).getD 0 0
      match Classical.propDecidable (r ∉ ({0, 1} : Set E)) with
      | .isTrue _ => pure r
      | .isFalse _ => challenge key tries (index + 1)

/-- The search for a challenge stops after `2 ^ 64` candidates. -/
def challengeTries : ℕ := 2 ^ 64

/-- The salted digest `d_T = H(s_T ‖ h_T)` of each held term, as a payload to every operator. -/
def digests (h : History C) (s : StreamId) : PartyM C E (Msg E) := do
  let salts ← randBits ctx s 256
  let values ← localStep (C.terms.mapM fun T => do
    let running ← query (spec := HashSpec) (bytesOfBits (h T))
    query (spec := HashSpec) (bytesOfBits (salts T) ++ bytesLE 32 running))
  pure (.bundle (C.terms.mapIdx fun k T =>
    if ctx.self ∈ C.holders T then some (.bytes (bytesLE 32 (values.getD k 0))) else none))

/-- Each operator aborts unless all holders of each term send the same digest. -/
def compareDigests (payloads : C.Party → Option (Msg E)) : PartyM C E Unit :=
  require (∀ T : C.Term, ∀ h h' : C.Party, h ∈ C.holders T → h' ∈ C.holders T →
    Msg.part (payloads h) (C.terms.idxOf T) = Msg.part (payloads h') (C.terms.idxOf T) ∧
      Msg.part (payloads h) (C.terms.idxOf T) ≠ none)

end Gadgets

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

/-- The circuit that outputs its first `width` inputs. -/
def Circuit.identity (width : ℕ) : Circuit := ⟨[], (List.range width).map fun k => ⟨[k], 0⟩⟩

/-- A circuit on the threshold PRF values `F(X)` of some points `X`. -/
structure Job where
  circuit : Circuit
  points : List HashInput

/-- `seed ‖ X`, the input of term `T` of `F(X)`. -/
def prfInput (seed : HashOutput) (point : HashInput) : HashInput := bytesLE 32 seed ++ point

/-- The number `m` of halving steps of a check of `count` tuples (`doc/dkg.md` 3.3). -/
def halvings (count : ℕ) : ℕ := max (sliceBits + wordBits) (Nat.clog 2 count)

/-- The number `d` of coins of the weights (`doc/dkg.md` 3.3). -/
def coins (count : ℕ) : ℕ := halvings count - wordBits

/-- The tuple index `k` of bit `q` of word `w` in slice `h`. -/
def sliceOf (m k : ℕ) : ℕ := k / 2 ^ (m - sliceBits)
def wordOf (m k : ℕ) : ℕ := (k / 2 ^ wordBits) % 2 ^ (m - sliceBits - wordBits)
def bitOf (k : ℕ) : Fin (2 ^ wordBits) := ⟨k % 2 ^ wordBits, Nat.mod_lt _ (by positivity)⟩

section Batch

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C)

/-- `τ^a`, the product of the coins `τ[offset + b]` at the set bits `b < width` of `a`. -/
def coinProduct (τ : List E) (offset width a : ℕ) : E :=
  ∏ b ∈ Finset.range width, if a.testBit b then τ.getD (offset + b) 0 else 1

def liftShares (x : C.Term → List Bit) : Shares C E := fun T k => algebraMap Bit E ((x T).getD k 0)

/-- The check of `doc/dkg.md` 2.2 with the slice steps of `doc/dkg.md` 3.3. It aborts unless every
tuple `(x, y, z)` has `z = x y`, except with a small probability (GS20, Protocol 17). -/
def check (tag base : ℕ) (x y z : C.Term → List Bit) (count : ℕ) : BatchM C E Unit := do
  let i := ctx.self
  let m := halvings count
  let d := coins count
  let s := sliceBits
  -- After de-linearization the claim is `D = ∑ β_k z_k` with `β = τ^h τ^w x^q`, and `x` keeps
  -- `τ^w x^q`.
  let (key, _) ← coin K ctx (tag, base, 1) (.bundle [])
  let τ ← coinValues K ctx key 0 d
  require (C := C) (E := E) (∀ b < s, τ.getD b 0 ≠ 0)
  let wordWeight := fun k => coinProduct τ s (d - s) (wordOf m k) * K.weight (bitOf k)
  let xHat : Shares C E := fun T k => wordWeight k * liftShares x T k
  let claim : Shares C E := fun T _ => ∑ k ∈ Finset.range (2 ^ m),
    coinProduct τ 0 s (sliceOf m k) * wordWeight k * liftShares z T k
  -- The slice steps fold the top bit of the slice with the coin `c_j` kept out of `x` (Gruen).
  let (xHat, yFold, D) ← (List.range s).foldlM (init := (xHat, liftShares y, conv K ctx claim 0))
    fun (xs, ys, D) j => do
      let half := 2 ^ (m - j - 1)
      let rest := fun k => ∏ b ∈ Finset.range (s - 1 - j),
        if k.testBit (m - s + b) then τ.getD b 0 else 1
      let t0 : E := ∑ AB ∈ K.pairs i, ∑ k ∈ Finset.range half, rest k * xs AB.1 k * ys AB.2 k
      let tInf : E := ∑ AB ∈ K.pairs i, ∑ k ∈ Finset.range half,
        rest k * (xs AB.1 k + xs AB.1 (k + half)) * (ys AB.2 k + ys AB.2 (k + half))
      let t ← resharePeer K ctx (elementCodec K ctx) (fun g => if g = 0 then t0 else tInf) 2
        (tag, base + 1 + j, 0)
      let (key, _) ← coin K ctx (tag, base + 1 + j, 1) (.bundle [])
      let r ← challenge K ctx key challengeTries 0
      let c := τ.getD (s - 1 - j) 0
      let t0Share := conv K ctx t 0
      let tInfShare := conv K ctx t 1
      let t1Share := (D + t0Share) / c
      let fold := fun (v : Shares C E) T k => v T k + r * (v T k + v T (k + half))
      pure (fold xs, fold ys, (1 + r) * t0Share + r * t1Share + r * (1 + r) * tInfShare)
  -- Halving steps on Shamir vectors (GS20, Protocol 14 with `k = 2`).
  let (A, B, D) ← (List.range (m - s)).foldlM
    (init := (conv K ctx xHat, conv K ctx yFold, D)) fun (A, B, D) j => do
      let half := 2 ^ (m - s - j - 1)
      let lo := fun (v : ℕ → E) k => v k
      let sum := fun (v : ℕ → E) k => v k + v (k + half)
      let c1 := mulSh K ctx (lo A) (lo B) half
      let p2 := mulSh K ctx (sum A) (sum B) half
      let t ← resharePeer K ctx (elementCodec K ctx) (fun g => if g = 0 then c1 else p2) 2
        (tag, base + 1 + s + j, 0)
      let (key, _) ← coin K ctx (tag, base + 1 + s + j, 1) (.bundle [])
      let r ← challenge K ctx key challengeTries 0
      let fold := fun (v : ℕ → E) k => v k + r * (v k + v (k + half))
      pure (fold A, fold B, conv K ctx t 0 + (D + conv K ctx t 1) * r + conv K ctx t 1 * r ^ 2)
  -- The final step (GS20, Protocol 15) uses random masks, digests to all operators and a robust
  -- opening.
  let final := base + 1 + m
  let masks ← randElements K ctx (tag, final, 1) 2
  let a0 := conv K ctx (fun T g => (masks T).getD (2 * g) 0) 0
  let b0 := conv K ctx (fun T g => (masks T).getD (2 * g + 1) 0) 0
  let c0 := mulSh K ctx (fun _ => a0) (fun _ => b0) 1
  let q2 := mulSh K ctx (fun _ => a0 + A 0) (fun _ => b0 + B 0) 1
  let q ← resharePeer K ctx (elementCodec K ctx) (fun g => if g = 0 then c0 else q2) 2 (tag, final, 0)
  let payload ← digests (E := E) ctx (← get) (tag, final + 1, 2)
  let (key, payloads) ← coin K ctx (tag, final + 1, 1) payload
  compareDigests payloads
  let r ← challenge K ctx key challengeTries 0
  let c0Share := conv K ctx q 0
  let q2Share := conv K ctx q 1
  let opened ← openSh K ctx (fun g =>
      if g = 0 then a0 + r * (a0 + A 0)
      else if g = 1 then b0 + r * (b0 + B 0)
      else c0Share + (D + c0Share + q2Share) * r + q2Share * r ^ 2) 3 (.bundle [])
  require (C := C) (E := E) (opened.1 0 * opened.1 1 = opened.1 2)

/-- The term of an affine wire at one operator. The public constant joins one term. -/
def affineTerm (a : Affine) (w : C.Term → List Bit) (T : C.Term) : Bit :=
  (a.wires.map fun k => (w T).getD k 0).sum + if T = K.publicTerm then a.const else 0

/-- One batch runs the AND layers of its jobs, the check, then `OpenRep` of the outputs. -/
def batch (mode : ReshareMode) (tag : ℕ) (jobs : List Job) : BatchM C E (List (List Bit)) := do
  let i := ctx.self
  let inputs : List (List (List Bit)) ← jobs.mapM fun job => localStep (C := C) (E := E) (C.terms.mapM fun T =>
    if i ∈ C.holders T then job.points.flatMapM fun X => do
      pure (bitsOfDigest (truncateHash (← query (spec := HashSpec) (prfInput (ctx.keys.seed T) X))))
    else pure [])
  let wires₀ : List (C.Term → List Bit) :=
    inputs.map fun terms T => terms.getD (C.terms.idxOf T) []
  let depth := (jobs.map (·.circuit.layers.length)).foldl max 0
  let empty : C.Term → List Bit := fun _ => []
  let (wires, x, y, z, _) ← (List.range depth).foldlM
    (init := (wires₀, empty, empty, empty, (0 : ℕ)))
    fun (wires, xs, ys, zs, offset) layer => do
      let gates := (jobs.zip wires).zipIdx.flatMap fun ((job, w), j) =>
        (job.circuit.layers.getD layer []).map fun ab => (j, ab, w)
      let a : Shares C Bit := fun T g => (gates.getD g (0, (⟨[], 0⟩, ⟨[], 0⟩), fun _ => [])).2.2
        |> fun w => affineTerm K (gates.getD g (0, (⟨[], 0⟩, ⟨[], 0⟩), fun _ => [])).2.1.1 w T
      let b : Shares C Bit := fun T g => affineTerm K
        (gates.getD g (0, (⟨[], 0⟩, ⟨[], 0⟩), fun _ => [])).2.1.2
        (gates.getD g (0, (⟨[], 0⟩, ⟨[], 0⟩), fun _ => [])).2.2 T
      let v := mulRep K ctx a b
      let count := gates.length
      let products ← match mode with
        | .peer => resharePeer K ctx (bitCodec ctx) v count (tag, layer, 0)
        | .collector => reshareCollector K ctx v count offset (tag, layer, 0)
      let wires' := wires.zipIdx.map fun (w, j) T =>
        w T ++ ((List.range count).filter fun g => (gates.getD g (0, (⟨[], 0⟩, ⟨[], 0⟩),
          fun _ => [])).1 = j).map (products T)
      pure (wires', fun T => xs T ++ vector count (a T), fun T => ys T ++ vector count (b T),
        fun T => zs T ++ vector count (products T), offset + count)
  let count := (x K.publicTerm).length
  if count ≠ 0 then check K ctx tag depth x y z count
  (jobs.zip wires).mapM fun (job, w) => do
    let opened ← openRep K ctx (fun T g => affineTerm K (job.circuit.outputs.getD g ⟨[], 0⟩) w T)
      job.circuit.outputs.length
    pure (vector job.circuit.outputs.length opened)

end Batch

/-! ## Setup -/

/-- The random contribution of one operator to the setup, namely a part of `P`, a part of each held
term seed, and a part of each pair key. -/
structure Contribution (C : Committee) where
  parameter : List UInt8
  termPart : C.Term → List UInt8
  pairPart : C.Party → List UInt8

/-- The bytes that operator `i` reveals to operator `j`. -/
def revealTo (c : Contribution C) (i j : C.Party) : List UInt8 :=
  c.parameter ++ (C.terms.filter fun T => i ∈ C.holders T ∧ j ∈ C.holders T).flatMap c.termPart ++
    c.pairPart j

/-- The contribution of `j` as operator `i` reads it from the reveal of `j`. -/
def readReveal (bytes : List UInt8) (i j : C.Party) : Contribution C where
  parameter := bytes.take 32
  termPart T := (bytes.drop (32 + 32 *
    (C.terms.filter fun U => i ∈ C.holders U ∧ j ∈ C.holders U).idxOf T)).take 32
  pairPart _ := (bytes.drop (32 + 32 *
    (C.terms.filter fun U => i ∈ C.holders U ∧ j ∈ C.holders U).length)).take 32

/-- The keys of operator `i`, namely `P = H16(parameter parts)`,
`seed_T = H(parts of the holders of T)` and
`K_ij = H(part of the lower operator ‖ part of the higher operator)`. -/
def deriveKeys {m : Type → Type} [Monad m] [HasQuery HashSpec m] (i : C.Party)
    (c : C.Party → Contribution C) : m (Keys C) := do
  let parameter ← query (spec := HashSpec) (C.parties.flatMap fun j => (c j).parameter)
  let seeds ← C.terms.mapM fun T =>
    if i ∈ C.holders T then
      query (spec := HashSpec) ((C.parties.filter (· ∈ C.holders T)).flatMap fun j => (c j).termPart T)
    else pure 0
  let pairKeys ← C.parties.mapM fun j =>
    if j = i then pure 0 else
    let (low, high) := if i < j then (i, j) else (j, i)
    query (spec := HashSpec) ((c low).pairPart high ++ (c high).pairPart low)
  pure ⟨truncateHash parameter, fun T => seeds.getD (C.terms.idxOf T) 0,
    fun j => pairKeys.getD j.val 0⟩

/-- The seeds of all terms from the contributions, as the holders derive them. -/
def deriveSeeds {m : Type → Type} [Monad m] [HasQuery HashSpec m] (c : C.Party → Contribution C) :
    m (C.Term → HashOutput) := do
  let seeds ← C.terms.mapM fun T =>
    query (spec := HashSpec) ((C.parties.filter (· ∈ C.holders T)).flatMap fun j => (c j).termPart T)
  pure fun T => seeds.getD (C.terms.idxOf T) 0

instance (w : ℕ) : SampleableType (BitVec w) := SampleableType.ofFintype _

instance : NeZero lifetime := ⟨by decide⟩

instance : NeZero numLayers := ⟨by decide⟩

instance : NeZero numChains := ⟨by decide⟩

def sampleKey : ProbComp HashOutput := $ᵗ HashOutput

/-- A fresh contribution of operator `i`. -/
def sampleContribution (i : C.Party) : ProbComp (Contribution C) := do
  let parameter ← sampleKey
  let termParts ← C.terms.mapM fun _ => sampleKey
  let pairParts ← C.parties.mapM fun _ => sampleKey
  pure ⟨bytesLE 32 parameter, fun T => bytesLE 32 (termParts.getD (C.terms.idxOf T) 0),
    fun j => if j = i then [] else bytesLE 32 (pairParts.getD j.val 0)⟩

/-- The setup in three rounds, namely commit, reveal and echo (the leanXMSS note, Section 2.1). -/
def setup (i : C.Party) : PartyM C E (Keys C) := do
  let c ← localStep (liftComp (sampleContribution i) _)
  let commitments ← localStep (C.parties.mapM fun j => query (spec := HashSpec) (revealTo c i j))
  let committed ← exchange fun j =>
    if j = i then none else some (.bytes (bytesLE 32 (commitments.getD j.val 0)))
  let revealed ← exchange fun j => if j = i then none else some (.bytes (revealTo c i j))
  let opened ← localStep (C.parties.mapM fun j => query (spec := HashSpec) (Msg.bytesOf (revealed j)))
  require (∀ j ≠ i, (Msg.bytesOf (revealed j)).length = (revealTo c i j).length ∧
    bytesLE 32 (opened.getD j.val 0) = Msg.bytesOf (committed j))
  let view : C.Party → Contribution C := fun j =>
    if j = i then c else readReveal (Msg.bytesOf (revealed j)) i j
  let keys ← localStep (deriveKeys i view)
  let echo ← localStep (C.parties.mapM fun j => do
    let all ← query (spec := HashSpec) (C.parties.flatMap fun k => (view k).parameter)
    let shared ← query (spec := HashSpec)
      ((C.terms.filter fun T => i ∈ C.holders T ∧ j ∈ C.holders T).flatMap fun T => bytesLE 32 (keys.seed T))
    pure (bytesLE 32 all ++ bytesLE 32 shared))
  let echoed ← exchange fun j => if j = i then none else some (.bytes (echo.getD j.val []))
  require (∀ j ≠ i, Msg.bytesOf (echoed j) = echo.getD j.val [])
  pure keys

/-! ## Ceremonies -/

/-- The settings that all operators of a ceremony check in `establish`. -/
structure Settings where
  mode : ReshareMode
  batchSize : ℕ

/-- `establish` runs one round of nonces, then the session value is the hash of all messages. -/
def establish (i : C.Party) (settings : Settings) : PartyM C E HashOutput := do
  let nonce ← localStep (liftComp sampleKey _)
  let message := (bytesLE 32 nonce).take 16 ++ [if settings.mode = .peer then 1 else 0] ++
    bytesLE 8 (BitVec.ofNat 64 settings.batchSize)
  let inbox ← exchange fun j => if j = i then none else some (.bytes message)
  let received := fun j => if j = i then message else Msg.bytesOf (inbox j)
  require (∀ j, (received j).length = message.length ∧ (received j).drop 16 = message.drop 16)
  localStep (query (spec := HashSpec) (C.parties.flatMap received))

/-- The circuits that the batches evaluate, for the chain values of the leanXMSS note. -/
structure Circuits where
  /-- `y_3` from `F(X_0)` on chain `l` of top key `e`. -/
  chainEnd : PublicParameter → KeyIndex → ChainIndex → Circuit
  /-- `y_1 ⊕ F(X_1)`, `y_2 ⊕ F(X_2)` and `y_3` from `F(X_0), F(X_1), F(X_2)` on bottom key `e`. -/
  chainRow : PublicParameter → KeyIndex → ChainIndex → Circuit
  /-- `y_p` from `F(X_0)` on chain `l` of top key `e`. -/
  chainValue : PublicParameter → KeyIndex → ChainIndex → Digit → Circuit
  /-- `c_e` from `F(A_rnd(e))` on bottom key `e`. -/
  commitment : PublicParameter → KeyIndex → Circuit

/-- `A_prf(e, l, p)`, the PRF point of position `p` on chain `l` of key `e`. -/
def prfPoint (lay : Layer) (e : KeyIndex) (l : ChainIndex) (p : ℕ) : HashInput :=
  fieldBytes (tweakFields 0 p (layerHi lay l.val) e.val)

/-- `A_rnd(e)`, the PRF point of the randomizer value of key `e`. -/
def randomizerPoint (lay : Layer) (e : KeyIndex) : HashInput :=
  fieldBytes (tweakFields 7 0 (layerHi lay 0) e.val)

/-- `Th(P, A_rnd(e) at step 1, ρ ‖ 0)`, the input of the commitment `c_e`. -/
def commitmentInput (parameter : PublicParameter) (e : KeyIndex) (ρ : Digest) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (tweakFields 7 1 (layerHi bottomLayer 0) e.val) ++
    bytesLE 16 ρ ++ bytesLE 16 0

/-- `Th(P, A_rnd(e), ρ ‖ M)`, the input of the start `R_0` of the randomizer search. -/
def randomizerInput (parameter : PublicParameter) (lay : Layer) (e : KeyIndex) (ρ : Digest)
    (message : HashInput) : HashInput :=
  bytesLE 16 parameter ++ randomizerPoint lay e ++ bytesLE 16 ρ ++ message

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

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- Node `idx` at `level` of a layer, from the chain ends of its keys. Indices are global. -/
def merkleNode (parameter : PublicParameter) (lay : Layer) (chainEnd : KeyIndex → ChainIndex → Digest) :
    ℕ → ℕ → m Digest
  | 0, idx => do
      let key : KeyIndex := ⟨idx % lifetime, Nat.mod_lt _ (by decide)⟩
      Concrete.leafHash parameter lay key (chainEnd key)
  | level + 1, idx => do
      let left ← merkleNode parameter lay chainEnd level (2 * idx)
      let right ← merkleNode parameter lay chainEnd level (2 * idx + 1)
      Concrete.tweakableHash parameter (.node lay (level + 1) idx) (Concrete.nodePayload left right)

/-- The authentication path of a key. -/
def merklePath (parameter : PublicParameter) (lay : Layer) (chainEnd : KeyIndex → ChainIndex → Digest)
    (key : KeyIndex) : m (Fin layerHeight → Digest) :=
  Concrete.sequenceFin fun level =>
    merkleNode parameter lay chainEnd level.val (Nat.xor (key.val / 2 ^ level.val) 1)

/-- The leanXMSS randomizer search from `R_0` finds the first trial whose digest is a codeword. -/
def grind (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (base : Randomness) : ℕ → ℕ → m (Option (Randomness × Encoding))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := base + BitVec.ofNat digestBits trial
      let digest ← Concrete.messageDigest parameter lay key message randomness
      match Codeword.decode digest with
      | some encoding => pure (some (randomness, encoding))
      | none => grind parameter lay key message base attempts (trial + 1)

/-- The digest of the `k`-th 128 bits of an output. -/
def digestAt (bits : List Bit) (k : ℕ) : Digest := digestOfBits (bits.drop (digestBits * k))

/-- The public outputs of a ceremony from the opened outputs of its jobs. `run` evaluates a list of
jobs, in the clear for the dealer or in batches of MPC for the operators. The call number separates
the batch tags of the three runs of a bottom tree. -/
def ceremonyOutput (circuits : Circuits) (parameter : PublicParameter)
    (run : ℕ → List Job → m (Option (List (List Bit)))) (top : TopTree) :
    Tree → m (Option TreeOutput)
  | .top => do
      let keys := (List.finRange (2 ^ layerHeight)).flatMap fun b =>
        (List.finRange numChains).map fun l => (topKey b, l)
      let some outputs ← run 0 (keys.map fun (e, l) =>
          ⟨circuits.chainEnd parameter e l, [prfPoint topLayer e l 0]⟩) | pure none
      let chainEnd := fun (e : KeyIndex) (l : ChainIndex) =>
        digestAt (outputs.getD (keys.idxOf (e, l)) []) 0
      let root ← merkleNode parameter topLayer chainEnd layerHeight 0
      pure (some (.top ⟨chainEnd, root⟩))
  | .bottom b => do
      let keys := (List.finRange (2 ^ layerHeight)).flatMap fun k =>
        (List.finRange numChains).map fun l => (bottomKey b k, l)
      let chainJobs := keys.map fun (e, l) => (⟨circuits.chainRow parameter e l,
        [prfPoint bottomLayer e l 0, prfPoint bottomLayer e l 1, prfPoint bottomLayer e l 2]⟩ : Job)
      let commitmentJobs := (List.finRange (2 ^ layerHeight)).map fun k =>
        (⟨circuits.commitment parameter (bottomKey b k), [randomizerPoint bottomLayer (bottomKey b k)]⟩ : Job)
      let some outputs ← run 0 (chainJobs ++ commitmentJobs) | pure none
      let cpk := fun (e : KeyIndex) (l : ChainIndex) =>
        let bits := outputs.getD (keys.idxOf (e, l)) []
        (digestAt bits 0, digestAt bits 1, digestAt bits 2)
      let commitment := fun (e : KeyIndex) =>
        digestAt (outputs.getD (keys.length + e.val % 2 ^ layerHeight) []) 0
      let root ← merkleNode parameter bottomLayer (fun e l => (cpk e l).2.2) layerHeight b.val
      let message := bytesLE 16 root
      let some opened ← run 1 [⟨Circuit.identity digestBits, [randomizerPoint topLayer (topKey b)]⟩]
        | pure none
      let ρ := digestAt (opened.getD 0 []) 0
      let base := truncateHash (← query (spec := HashSpec)
        (randomizerInput parameter topLayer (topKey b) ρ message))
      let some (randomness, encoding) ← grind parameter topLayer (topKey b) message base
          randomizerAttemptLimit 0 | pure none
      let some values ← run 2 ((List.finRange numChains).map fun l =>
          ⟨circuits.chainValue parameter (topKey b) l (encoding l), [prfPoint topLayer (topKey b) l 0]⟩)
        | pure none
      let path ← merklePath parameter topLayer top.chainEnd (topKey b)
      pure (some (.bottom ⟨cpk, commitment, root,
        ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩⟩))

end Trees

/-- `F(X) = ⊕_T H16(seed_T ‖ X)`, the threshold PRF of PRAWNS, Section 5, on all seeds. -/
def prfValue {m : Type → Type} [Monad m] [HasQuery HashSpec m] (seed : C.Term → HashOutput)
    (point : HashInput) : m Digest := do
  let terms ← C.terms.mapM fun T => query (spec := HashSpec) (prfInput (seed T) point)
  pure ((terms.map truncateHash).foldl (· ^^^ ·) 0)

/-- A job in the clear on all seeds. -/
def evalJob {m : Type → Type} [Monad m] [HasQuery HashSpec m] (seed : C.Term → HashOutput) (job : Job) :
    m (List Bit) := do
  let values ← job.points.mapM (prfValue seed)
  pure (job.circuit.eval (values.flatMap bitsOfDigest))

/-- Split a list in chunks of `size`. -/
def chunks {α : Type} (size : ℕ) (items : List α) : List (List α) :=
  (List.range ((items.length + size - 1) / size)).map fun k => (items.drop (size * k)).take size

/-- More rounds than any program of the protocol runs. -/
def roundLimit : ℕ := 2 ^ 64

section Ceremony

variable [Field E] [Algebra Bit E] (K : Constants C E)

/-- The jobs of a run in batches of `batchSize`, each batch an MPC on its own channel. -/
def runBatches (settings : Settings) (ctx : Context C) (call : ℕ) (jobs : List Job) :
    PartyM C E (List (List Bit)) := do
  let batches := chunks settings.batchSize jobs
  let outputs ← parallel roundLimit (batches.mapIdx fun k jobs =>
    ((batch K ctx settings.mode (2 ^ 32 * call + k) jobs).run' (fun _ => [])).run)
  pure outputs.flatten

/-- The ceremony of a tree at operator `i` runs `establish`, then the batches. -/
def ceremony (circuits : Circuits) (settings : Settings) (i : C.Party) (keys : Keys C)
    (top : TopTree) (tree : Tree) : PartyM C E TreeOutput := do
  let session ← establish i settings
  let ctx : Context C := ⟨i, keys, session⟩
  let some output ← ceremonyOutput circuits keys.parameter
      (fun call jobs => some <$> runBatches K settings ctx call jobs) top tree | failure
  pure output

end Ceremony

/-! ## The trusted dealer -/

/-- The keys of all operators from the contributions of all operators, as the setup derives them. -/
def dealerKeys {m : Type → Type} [Monad m] [HasQuery HashSpec m] (c : C.Party → Contribution C) :
    m (C.Party → Keys C) := do
  let keys ← C.parties.mapM fun i => deriveKeys i c
  pure fun i => keys.getD i.val ⟨0, fun _ => 0, fun _ => 0⟩

/-- The outputs of a ceremony in the clear. -/
def dealerTree {m : Type → Type} [Monad m] [HasQuery HashSpec m] (circuits : Circuits)
    (parameter : PublicParameter) (seed : C.Term → HashOutput) (top : TopTree) (tree : Tree) :
    m (Option TreeOutput) :=
  ceremonyOutput circuits parameter (fun _ jobs => some <$> jobs.mapM (evalJob seed)) top tree

/-! ## Signing -/

/-- `J` as 4 bytes, the sum of `2 ^ j` over its operators. -/
def quorumBytes (J : C.Quorum) : List UInt8 := bytesLE 4 (BitVec.ofNat 32 (∑ j ∈ J.1, 2 ^ j.val))

/-- `L_i`, the terms whose first holder in `J` is operator `i` (PRAWNS, Section 5). -/
def L (J : C.Quorum) (i : C.Party) : Finset C.Term :=
  Finset.univ.filter fun T => (J.1 \ T.1).min = i

/-- `Eval_i(x, m, J)` gives the terms of `L_i` and one mask `H16(K_ij ‖ x ‖ m ‖ J)` for each other
signer `j`. -/
def eval {m : Type → Type} [Monad m] [HasQuery HashSpec m] (keys : Keys C) (i : C.Party)
    (J : C.Quorum) (point : HashInput) (message : Message) : m Digest := do
  let terms ← (C.terms.filter (· ∈ L J i)).mapM fun T =>
    query (spec := HashSpec) (prfInput (keys.seed T) point)
  let masks ← (C.parties.filter fun j => j ∈ J.1 ∧ j ≠ i).mapM fun j =>
    query (spec := HashSpec)
      (bytesLE 32 (keys.pairKey j) ++ point ++ bytesLE 32 message ++ quorumBytes J)
  pure (((terms ++ masks).map truncateHash).foldl (· ^^^ ·) 0)

/-- `Combine`, the sum of the parts of the quorum. -/
def combine (J : C.Quorum) (parts : C.Party → Digest) : Digest :=
  (C.parties.filter (· ∈ J.1)).foldl (fun acc j => acc ^^^ parts j) 0

/-- Round 1 of signer `i` computes its part of `F(A_rnd(e))`. -/
def signRound1 {m : Type → Type} [Monad m] [HasQuery HashSpec m] (keys : Keys C) (i : C.Party)
    (J : C.Quorum) (e : KeyIndex) (message : Message) : m Digest :=
  eval keys i J (randomizerPoint bottomLayer e) message

/-- The codeword of a signature at key `e` from the opened randomizer value, or `none` if it does
not match the commitment `c_e` or the search fails. -/
def signCodeword {m : Type → Type} [Monad m] [HasQuery HashSpec m] (parameter : PublicParameter)
    (commitment : Digest) (e : KeyIndex) (message : Message) (ρ : Digest) :
    m (Option (Randomness × Encoding)) := do
  let opened := truncateHash (← query (spec := HashSpec) (commitmentInput parameter e ρ))
  if opened ≠ commitment then pure none else
  let base := truncateHash (← query (spec := HashSpec)
    (randomizerInput parameter bottomLayer e ρ (bytesLE 32 message)))
  grind parameter bottomLayer e (bytesLE 32 message) base randomizerAttemptLimit 0

/-- Round 2 of signer `i` checks `c_e` from the parts of round 1, finds the codeword, and sends its
parts of `F(X_{l, p_l})` for each chain with `p_l < 3`. -/
def signRound2 {m : Type → Type} [Monad m] [HasQuery HashSpec m] (keys : Keys C) (i : C.Party)
    (J : C.Quorum) (commitment : Digest) (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    m (Option (ChainIndex → Option Digest)) := do
  let some (_, encoding) ← signCodeword keys.parameter commitment e message (combine J parts)
    | pure none
  let values ← Concrete.sequenceFin fun l =>
    if (encoding l).val < chainLength - 1 then
      some <$> eval keys i J (prfPoint bottomLayer e l (encoding l).val) message
    else pure none
  pure (some values)

/-- The leanXMSS signature of an honest quorum at bottom key `e`, from the parts of both rounds.
Each signer checks that every chain value leads to its chain end. -/
def assemble {m : Type → Type} [Monad m] [HasQuery HashSpec m] (parameter : PublicParameter)
    (tree : BottomTree) (e : KeyIndex) (message : Message) (J : C.Quorum) (parts : C.Party → Digest)
    (chainParts : C.Party → ChainIndex → Digest) : m (Option Signature) := do
  let some (randomness, encoding) ← signCodeword parameter (tree.commitment e) e message
      (combine J parts) | pure none
  let value := fun l => match (encoding l).val with
    | 0 => combine J (chainParts · l)
    | 3 => (tree.cpk e l).2.2
    | p => (if p = 1 then (tree.cpk e l).1 else (tree.cpk e l).2.1) ^^^ combine J (chainParts · l)
  let ends ← Concrete.sequenceFin fun l => Concrete.recoverChain parameter bottomLayer e l (encoding l) (value l)
  if ∃ l, ends l ≠ (tree.cpk e l).2.2 then pure none else
  let path ← merklePath parameter bottomLayer (fun e l => (tree.cpk e l).2.2) e
  pure (some ⟨e, fun lay => if lay = bottomLayer then ⟨randomness, value, path⟩ else tree.topSignature⟩)

end ThresholdLeanXmss
