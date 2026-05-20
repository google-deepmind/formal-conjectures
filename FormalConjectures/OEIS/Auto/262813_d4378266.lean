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

open Finset Nat

/-- The $z$-th triangular number $\frac{z(z+1)}{2}$. -/
def triangular (z : ℕ) : ℕ := z * (z + 1) / 2

/--
A262813: Number of ordered ways to write $n$ as $x^3 + y^2 + z(z+1)/2$ with $x \ge 0$, $y \ge 0$ and $z > 0$.
-/
def a (n : ℕ) : ℕ :=
  -- The summation range can be safely finite, as x^3, y^2, and triangular z must be <= n.
  (range (n + 1)).sum fun x =>
  (range (n + 1)).sum fun y =>
  (range (n + 1)).sum fun z =>
    -- Count only if z > 0 and the equation holds.
    if z > 0 ∧ x^3 + y^2 + triangular z = n then 1 else 0

-- The provided small examples are kept to follow the submission template but are using `sorry`.
theorem a_one : a 1 = 1 := by
  sorry

theorem a_two : a 2 = 2 := by
  sorry

theorem a_three : a 3 = 2 := by
  sorry

theorem a_four : a 4 = 2 := by
  sorry

/--
A262813 Conjecture: a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 9, 21, 35, 98, 152, 306.
-/
theorem oeis_262813_conjecture :
  -- Define the set of exceptional natural numbers where a(n) = 1.
  let S : Finset ℕ := {1, 9, 21, 35, 98, 152, 306}
  -- The conjecture is formally stated as a conjunction of two properties for all n > 0.
  ∀ n : ℕ, n > 0 → (a n > 0 ∧ (a n = 1 ↔ n ∈ S)) := by
  sorry
