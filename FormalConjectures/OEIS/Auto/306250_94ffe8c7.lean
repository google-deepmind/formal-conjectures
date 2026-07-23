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

open Nat Finset

/--
A306250: Number of ways to write $n$ as $x(3x+1) + y(3y-1) + z(3z+2) + w(3w-2)$,
where $x,y,z,w$ are nonnegative integers with $x \cdot y \cdot z = 0$.
-/
def A306250 (n : ℕ) : ℕ :=
  let T₁ (x : ℕ) : ℕ := x * (3 * x + 1)
  let T₂ (y : ℕ) : ℕ := y * (3 * y - 1)
  let T₃ (z : ℕ) : ℕ := z * (3 * z + 2)
  let T₄ (w : ℕ) : ℕ := w * (3 * w - 2)

  -- The search space for each variable is bounded by $n$.
  -- A more precise bound can be derived, but `n+1` is a safe upper limit for the range.
  -- For non-negative $x,y,z,w$, $T_i(v) \ge v$. If $T_i(v) \le n$, then $v \le n$.
  let R := range (n + 1)

  -- We compute the number of tuples $(x, y, z, w)$ satisfying the conditions using a sum of indicator functions.
  R.sum fun x =>
    R.sum fun y =>
      R.sum fun z =>
        R.sum fun w =>
          if (x = 0 ∨ y = 0 ∨ z = 0) ∧ T₁ x + T₂ y + T₃ z + T₄ w = n then
            1
          else
            0

/--
Conjecture: a(n) > 0 for any nonnegative integer n.
-/
theorem oeis_306250_conjecture_0 (n : ℕ) : A306250 n > 0 := by sorry
