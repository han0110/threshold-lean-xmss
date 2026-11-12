import ThresholdLeanXmss.Statement

/-!
# Circuit facts for a signing forger of the final lifetime world

The ideal runs of the final world `S_N` of `LifetimeSlots` evaluate `circuitsOf Th` gate by gate in
`runJobs`. This module states two facts about that use of the circuits.

* `signingLocalAnswer_th` states that the signing world gives the same answers for every `Th`.
* `evalAttacked` is `Circuit.eval` with an error added to each AND gate output. `evalAttacked_zero`
  states that it is `Circuit.eval` when every error is zero.
* `gadget β` computes `a b c` twice and adds the two results. The first copy multiplies in the order
  `(a b) c` if `β = false` and `(b c) a` if `β = true`. The second copy uses `(a b) c`.
  `gadget_shape` states that the layer lengths and the output count do not depend on `β`.
  `gadget_eval` states that the output is `0` on every input. `gadget_attacked` states that an error
  `1` on the first gate output gives the output `c` if `β = false` and `a` if `β = true`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

namespace ThresholdLeanXmssSecurity.LifetimeForgerBound

variable {C : Committee}

/-- The signing world gives the same answers for every `Th`. -/
theorem signingLocalAnswer_th (Th Th' : HashInput → HashOutput) (aes : Aes) :
    signingLocalAnswer (C := C) ⟨Th, aes⟩ = signingLocalAnswer (C := C) ⟨Th', aes⟩ := rfl

/-- `Circuit.eval` with the error `δ k` added to the AND gate output at wire `k`. -/
def evalAttacked (c : Circuit) (x : List Bit) (δ : ℕ → Bit) : List Bit :=
  let w := c.layers.foldl (fun w layer =>
    w ++ layer.mapIdx fun j ab => ab.1.eval w * ab.2.eval w + δ (w.length + j)) x
  c.outputs.map (·.eval w)

theorem evalAttacked_zero (c : Circuit) (x : List Bit) : evalAttacked c x 0 = c.eval x := by
  have h : (fun (w : List Bit) (layer : List (Affine × Affine)) =>
      w ++ layer.mapIdx fun j ab => ab.1.eval w * ab.2.eval w + (0 : ℕ → Bit) (w.length + j)) =
      fun w layer => w ++ layer.map fun ab => ab.1.eval w * ab.2.eval w := by
    funext w layer
    simp only [List.mapIdx_eq_zipIdx_map, Pi.zero_apply, add_zero]
    rw [← List.zipIdx_map_fst 0 layer, List.map_map, List.zipIdx_map_fst]
    rfl
  simp only [evalAttacked, Circuit.eval, h]

/-- On the input wires `a, b, c`, wire `3` is `a b` or `b c`, wire `4` is `a b`, wire `5` is
`(a b) c` or `(b c) a`, wire `6` is `(a b) c`, and the output is wire `5` plus wire `6`. -/
def gadget (β : Bool) : Circuit :=
  ⟨[[(⟨[if β then 1 else 0], 0⟩, ⟨[if β then 2 else 1], 0⟩), (⟨[0], 0⟩, ⟨[1], 0⟩)],
    [(⟨[3], 0⟩, ⟨[if β then 0 else 2], 0⟩), (⟨[4], 0⟩, ⟨[2], 0⟩)]], [⟨[5, 6], 0⟩]⟩

theorem gadget_shape (β β' : Bool) :
    (gadget β).layers.map List.length = (gadget β').layers.map List.length ∧
      (gadget β).outputs.length = (gadget β').outputs.length := ⟨rfl, rfl⟩

theorem gadget_eval (β : Bool) (a b c : Bit) : (gadget β).eval [a, b, c] = [0] := by
  revert β a b c
  decide

/-- An error `1` on wire `3` gives the output `c` if `β = false` and `a` if `β = true`. -/
theorem gadget_attacked (a b c : Bit) :
    evalAttacked (gadget false) [a, b, c] (fun k => if k = 3 then 1 else 0) = [c] ∧
      evalAttacked (gadget true) [a, b, c] (fun k => if k = 3 then 1 else 0) = [a] := by
  revert a b c
  decide

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerBound.signingLocalAnswer_th' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signingLocalAnswer_th

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerBound.evalAttacked_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalAttacked_zero

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerBound.gadget_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gadget_shape

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerBound.gadget_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gadget_eval

/-- info: 'ThresholdLeanXmssSecurity.LifetimeForgerBound.gadget_attacked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gadget_attacked

end ThresholdLeanXmssSecurity.LifetimeForgerBound
