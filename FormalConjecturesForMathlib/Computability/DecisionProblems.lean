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

/-!
# Polynomial-time deciders for predicates on encoded inputs

A decider is a Boolean-valued function with a correctness equivalence on every input.
Its running time uses the existing TM2-based `ComplexityTheory.IsPolyTime`, with the
domain's specified binary encoding. This separates a mathematical predicate from a
particular exhaustive reference implementation.

For the decision-problem and encoding conventions, see Karp, *Reducibility among
Combinatorial Problems* (1972), §4, https://doi.org/10.1007/978-1-4684-2001-2_9.
-/

@[expose] public section

namespace ComplexityTheory

variable {α : Type} [BitstringEncoding α]

/-- A total deterministic polynomial-time algorithm deciding the supplied predicate. -/
def HasPolyTimeDecider (p : α → Prop) : Prop :=
  ∃ f : α → Bool, IsPolyTime f ∧ ∀ x, f x = true ↔ p x

theorem hasPolyTimeDecider_congr {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
    HasPolyTimeDecider p ↔ HasPolyTimeDecider q := by
  simp only [HasPolyTimeDecider, h]

/-- An actual polynomial-time function supplies a decider for its true preimage. -/
theorem IsPolyTime.hasPolyTimeDecider {f : α → Bool} (h : IsPolyTime f) :
    HasPolyTimeDecider (fun x ↦ f x = true) :=
  ⟨f, h, fun _ ↦ Iff.rfl⟩

/-- For bitstring languages, the decider interface agrees with the repository's class P.
This uses the existing encoding on both sides; it is not a bridge for arbitrary encodings. -/
theorem hasPolyTimeDecider_iff_mem_P (L : DecisionProblem) :
    HasPolyTimeDecider (fun x ↦ L x = true) ↔ L ∈ P := by
  constructor
  · rintro ⟨f, hf, h⟩
    have heq : f = L := by
      funext x
      have hx := h x
      cases hf : f x <;> cases hL : L x <;> simp_all
    change IsPolyTime L
    simpa only [heq] using hf
  · exact IsPolyTime.hasPolyTimeDecider

end ComplexityTheory
