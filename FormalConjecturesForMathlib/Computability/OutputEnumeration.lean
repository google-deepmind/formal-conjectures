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

public import FormalConjecturesForMathlib.Computability.Complexity
public import Mathlib.Data.Finset.Sort

/-!
# Output-polynomial enumeration with an actual machine clock

The runtime bound depends on the encoded input and complete encoded output.
It is a total-time bound, not a delay or incremental-time guarantee. Output
lists contain each mathematical answer exactly once, preventing padding by
repeated answers. Finite-set outputs have sorted canonical encodings.

Reference: Mary, *Enumeration of minimal transversals of hypergraphs of bounded
VC-dimension*, §1, https://arxiv.org/html/2407.00694v3.
-/

@[expose] public section

namespace BitstringEncoding

instance {α : Type} [LinearOrder α] [BitstringEncoding α] : BitstringEncoding (Finset α) :=
  ofLeftInverse (fun s => s.sort (· ≤ ·)) (fun l => some l.toFinset) (by
    intro s
    simp)

end BitstringEncoding

namespace ComplexityTheory

variable {α β : Type} [BitstringEncoding α] [BitstringEncoding β]

/-- A single deterministic TM2 halts with the complete output within a global
polynomial in the sum of encoded input and output lengths. -/
def IsOutputPolyTime (f : α → β) : Prop :=
  ∃ m : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial ℕ, ∀ x,
    Nonempty (Turing.TM2OutputsInTime m.tm
      ((BitstringEncoding.bitEncode x).map m.inputAlphabet.invFun)
      (some ((BitstringEncoding.bitEncode (f x)).map m.outputAlphabet.invFun))
      (p.eval ((BitstringEncoding.bitEncode x).length +
        (BitstringEncoding.bitEncode (f x)).length)))

def HasOutputPolyEnumerator (relation : α → β → Prop) : Prop :=
  ∃ f : α → List β, IsOutputPolyTime f ∧
    ∀ x, (f x).Nodup ∧ ∀ y, y ∈ f x ↔ relation x y

theorem HasOutputPolyEnumerator.finite {r : α → β → Prop}
    (h : HasOutputPolyEnumerator r) (x : α) : Set.Finite {y | r x y} := by
  obtain ⟨f, _, hf⟩ := h
  have he : {y | r x y} = {y | y ∈ f x} := by
    ext y
    exact (hf x).2 y |>.symm
  rw [he]
  exact List.finite_toSet _

end ComplexityTheory
