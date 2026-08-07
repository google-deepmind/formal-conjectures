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

open Nat Set

/-- The sum of the decimal digits of a natural number $m$. -/
private def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum

/--
A277223: $a(n)$ is the largest multiplier $k$ such that $m = k \cdot n$ is $n$ times the sum of its decimal digits.
This is equivalent to $a(n) = \max \{ k \in \mathbb{N} \mid k = \text{sum\_digits}_{10}(k \cdot n) \}$.
-/
noncomputable def A277223 (n : ℕ) : ℕ :=
  -- Define the set of all $k \in \mathbb{N}$ satisfying the property.
  -- This set is bounded and non-empty (contains 0), so its supremum is the maximum element.
  let valid_multipliers : Set ℕ := { k | k = sum_digits_10 (k * n) }

  -- sSup (supremum) in the complete lattice $\mathbb{N}$ gives the maximum element.
  sSup valid_multipliers

/--
Conjecture: if A277223(n) < 12 then A277223(n) = 0 or 9.
A277223 a(n) is never 1, 2, 3, 4, 5 or 6. Conjecture: if a(n) < 12 then a(n) = 0 or 9. - _Robert Israel_, Oct 06 2016
-/
theorem A277223_conjecture (n : ℕ) :
  n > 0 → (A277223 n < 12 → A277223 n = 0 ∨ A277223 n = 9) := by sorry
