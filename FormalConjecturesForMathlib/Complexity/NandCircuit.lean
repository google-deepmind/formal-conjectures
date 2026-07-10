import Mathlib.Data.PNat.Defs
import FormalConjecturesForMathlib.Complexity.TrapezoidalBitArray

/- Copyright (c) 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace ComplexityTheory

/- An unbounded fan-in NAND gate circuit.
We represent the inputs to each gate as a bitmask.
A trapezoidal bit array represents the inputs and/or previous
gates which are fed into each gate.
-/
def NandCircuit (num_inputs : Nat) (num_gates : PNat) : Type :=
  TrapezoidalBitArray num_gates num_inputs

/- Evaluates a single gate.
Given a circuit, the inputs to gate g, and the index of g,
returns those inputs, with the output of gate g appended.
-/
def eval_gate (num_inputs : Nat) (num_gates : PNat)
    (circuit : NandCircuit num_inputs num_gates)
    (inputs : BitVec num_inputs) (gate : Fin num_gates) :
    BitVec (num_inputs + (gate.val + 1)) :=
  let previous_inputs : BitVec (num_inputs + gate.val) :=
    match gate with
    | ⟨0, _⟩ => inputs
    | ⟨g+1, h⟩ => eval_gate num_inputs num_gates circuit inputs ⟨g, Nat.lt_of_succ_lt h⟩
  let wires : BitVec (num_inputs + gate.val) :=
    Nat.add_comm gate.val num_inputs ▸ TrapezoidalBitArray.get_row circuit gate
  let output_bit : Bool := (previous_inputs &&& wires) != wires
  BitVec.cons output_bit previous_inputs

/- Evaluates the entire circuit. -/
def eval_circuit (num_inputs : Nat) (num_gates : PNat)
    (circuit : NandCircuit num_inputs num_gates)
    (inputs : BitVec num_inputs) : Bool :=
  have : 0 < num_gates.val := num_gates.property
  let last_gate_index : Fin num_gates := ⟨num_gates.val - 1, by omega⟩
  BitVec.msb <| eval_gate num_inputs num_gates circuit inputs last_gate_index

end ComplexityTheory
