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
# Kourovka Problem 2.24

*Reference:* Kourovka Notebook, Problem 2.24.

Does every torsion-free Engel group admit a bi-invariant linear order? The question is intertwined
with Plotkin's conjecture on the local nilpotence of Engel groups: a positive answer to Plotkin's
conjecture would imply an affirmative answer here via Mal'cev's theorem that torsion-free locally
nilpotent groups are orderable.
-/

namespace KourovkaProblem2_24

variable (G : Type*) [Group G]

/-- The `n`-fold iterated commutator `[x,_n y]`. -/
def commutator_n (x y : G) : ℕ → G
  | 0 => x
  | n + 1 =>
      let z := commutator_n x y n
      z * y * z⁻¹ * y⁻¹

/-- An Engel group: every pair of elements has some iterated commutator equal to the identity. -/
def IsEngel : Prop :=
  ∀ x y : G, ∃ n : ℕ, commutator_n (G := G) x y n = 1

/-- A torsion-free group: no non-identity element has finite order. -/
def IsTorsionFree : Prop :=
  ∀ x : G, x ≠ 1 → ∀ n : ℕ, 0 < n → x ^ n ≠ 1

/-- A group is orderable if it admits a bi-invariant strict total order. -/
def IsOrderable : Prop :=
  ∃ r : G → G → Prop,
    IsStrictTotalOrder G r ∧
    (∀ a b g : G, r a b → r (g * a) (g * b)) ∧
    (∀ a b g : G, r a b → r (a * g) (b * g))

/--
*Kourovka Problem 2.24.*

Does every torsion-free Engel group admit a bi-invariant linear order?
-/
@[category research open, AMS 20]
theorem kourovka_problem_2_24 :
    answer(sorry) ↔ ∀ (H : Type*) [Group H], IsEngel H → IsTorsionFree H → IsOrderable H := by
  sorry

end KourovkaProblem2_24
