/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesForMathlib.Computability.BooleanCircuit
public import FormalConjecturesForMathlib.Computability.SearchProblems

/-!
# Explicit multi-output Boolean circuits

Gates reuse the De Morgan basis from `BooleanCircuit`. Inputs and previously
computed gates have separate references. Programs are topologically ordered;
a syntactic validity predicate rejects forward and out-of-range references.
Outputs are an explicit list of references, with unrestricted sharing.

The input count is encoded in unary, so even unused input positions contribute
to instance length. Gate indices are binary. The reference evaluator is total
on malformed descriptions, but search promises require syntactic validity.

Reference: Johnson–Papadimitriou–Yannakakis, *How Easy Is Local Search?* (1988),
§3, pp.86–87, https://doi.org/10.1016/0022-0000(88)90046-3.
-/

@[expose] public section

namespace EncodedBooleanCircuit

/-- False denotes an input; true denotes a previously computed gate. -/
abbrev Ref := Bool × ℕ
abbrev Gate := BooleanCircuit.Gate Ref

namespace Gate

def code : Gate → ℕ × List Ref
  | .not a => (0, [a])
  | .and a b => (1, [a, b])
  | .or a b => (2, [a, b])

def decode : ℕ × List Ref → Option Gate
  | (0, [a]) => some (.not a)
  | (1, [a, b]) => some (.and a b)
  | (2, [a, b]) => some (.or a b)
  | _ => none

@[simp] theorem decode_code (g : Gate) : decode (code g) = some g := by cases g <;> rfl

instance : BitstringEncoding Gate := BitstringEncoding.ofLeftInverse code decode decode_code

def refs : Gate → List Ref
  | .not a => [a]
  | .and a b | .or a b => [a, b]

end Gate

/-- Unary input count, gate list, and output references. -/
abbrev Circuit := BooleanTruthTable.UnarySize × List Gate × List Ref

def arity (c : Circuit) : ℕ := c.1.value

theorem arity_le_encoded_length (c : Circuit) :
    arity c ≤ (BitstringEncoding.bitEncode c).length := by
  change arity c ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode c.1) ++
    BitstringEncoding.bitEncode c.2).length
  simp only [List.length_append, BitstringEncoding.length_delimit,
    BooleanTruthTable.UnarySize.length_bitEncode, arity]
  omega

def validRef (n k : ℕ) (r : Ref) : Prop := r.2 < if r.1 then k else n

instance (n k : ℕ) (r : Ref) : Decidable (validRef n k r) := inferInstanceAs
  (Decidable (r.2 < if r.1 then k else n))

def validFrom (n : ℕ) : ℕ → List Gate → Prop
  | _, [] => True
  | k, g :: gs => (∀ r ∈ Gate.refs g, validRef n k r) ∧ validFrom n (k + 1) gs

instance (n k : ℕ) (gs : List Gate) : Decidable (validFrom n k gs) := by
  induction gs generalizing k with
  | nil => exact isTrue trivial
  | cons g gs ih => unfold validFrom; infer_instance

def Valid (c : Circuit) : Prop :=
  validFrom (arity c) 0 c.2.1 ∧ ∀ r ∈ c.2.2, validRef (arity c) c.2.1.length r

instance (c : Circuit) : Decidable (Valid c) := by unfold Valid; infer_instance

def evalRef (input registers : List Bool) (r : Ref) : Bool :=
  if r.1 then registers[r.2]?.getD false else input[r.2]?.getD false

/-- A valid reference selects an existing bit, never the missing-reference default. -/
theorem evalRef_valid (input registers : List Bool) (r : Ref)
    (h : validRef input.length registers.length r) :
    (if r.1 then registers[r.2]? else input[r.2]?) = some (evalRef input registers r) := by
  rcases r with ⟨b, i⟩
  cases b <;> simp only [validRef, Bool.false_eq_true, ↓reduceIte] at h <;>
    simp [evalRef, List.getElem?_eq_getElem h]

def evalFrom (input : List Bool) : List Gate → List Bool → List Bool
  | [], registers => registers
  | g :: gs, registers =>
    evalFrom input gs (registers ++ [g.eval (evalRef input registers)])

def eval (c : Circuit) (input : List Bool) : List Bool :=
  c.2.2.map (evalRef input (evalFrom input c.2.1 []))

@[simp] theorem length_eval (c : Circuit) (input : List Bool) :
    (eval c input).length = c.2.2.length := List.length_map ..

theorem length_evalFrom (input : List Bool) (gs : List Gate) (registers : List Bool) :
    (evalFrom input gs registers).length = registers.length + gs.length := by
  induction gs generalizing registers with
  | nil => simp [evalFrom]
  | cons g gs ih => simp [evalFrom, ih]; omega

/-- All-zero source vertex, with exactly the specified number of input bits. -/
def zero (c : Circuit) : List Bool := List.replicate (arity c) false

end EncodedBooleanCircuit
