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

import FormalConjectures.Util.ProblemImports

/-!
# Green's Open Problem 27

References:
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.27)
-/

namespace Green27

/--
A set `A` has no unique representation in its sumset `A + A` if for every pair of elements
`a₁, a₂ ∈ A`, there exist another pair of elements `b₁, b₂ ∈ A` such that `a₁ + a₂ = b₁ + b₂`
and `{a₁, a₂} ≠ {b₁, b₂}`.
-/
def HasNoUniqueRepresentation {G : Type*} [AddCommMonoid G] (A : Finset G) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∃ b₁ ∈ A, ∃ b₂ ∈ A,
    a₁ + a₂ = b₁ + b₂ ∧ ¬((a₁ = b₁ ∧ a₂ = b₂) ∨ (a₁ = b₂ ∧ a₂ = b₁))

/--
The size of the smallest set $A \subset \mathbb{Z} / p\mathbb{Z}$ (with at least two elements)
for which no element in the sumset $A + A$ has a unique representation.
-/
noncomputable def minSizeNoUniqueRep (p : ℕ) [Fact p.Prime] : ℕ :=
  sInf { k | ∃ A : Finset (ZMod p), A.card = k ∧ 2 ≤ k ∧ HasNoUniqueRepresentation A }

/--
What is the size of the smallest set $A \subset \mathbb{Z} / p\mathbb{Z}$ (with at least two elements)
for which no element in the sumset $A + A$ has a unique representation?
-/
@[category research open, AMS 5 11]
theorem green_27 (p : ℕ) [Fact p.Prime] : minSizeNoUniqueRep p = answer(sorry) := by
  sorry

end Green27
