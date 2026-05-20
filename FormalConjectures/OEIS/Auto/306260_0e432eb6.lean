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

/--
A306260: Number of ways to write $n$ as $w(4w+1) + x(4x-1) + y(4y-2) + z(4z-3)$ with $w,x,y,z$ nonnegative integers.
-/
def A306260 (n : ℕ) : ℕ :=
  let P₁ (w : ℕ) : ℕ := w * (4 * w + 1)
  let P₂ (x : ℕ) : ℕ := x * (4 * x - 1)
  let P₃ (y : ℕ) : ℕ := y * (4 * y - 2)
  let P₄ (z : ℕ) : ℕ := z * (4 * z - 3)

  -- The search space for $w, x, y, z$ is bounded by $n$.
  let B : ℕ := n.succ
  let R := range B -- Finset {0, 1, ..., n}

  R.sum fun w =>
    R.sum fun x =>
      R.sum fun y =>
        R.sum fun z =>
          if P₁ w + P₂ x + P₃ y + P₄ z = n then 1 else 0


theorem a_zero : A306260 0 = 1 := by
  sorry

theorem a_one : A306260 1 = 1 := by
  sorry

theorem a_two : A306260 2 = 1 := by
  sorry

theorem a_three : A306260 3 = 2 := by
  sorry

/--
Conjecture 1: a(n) > 0 for all n >= 0, and a(n) = 1 only for n = 0, 1, 2, 4, 7, 9, 11, 14, 23, 25, 28, 37.
-/
theorem oeis_306260_conjecture_1 :
  (∀ (n : ℕ), A306260 n > 0) ∧
  (∀ (n : ℕ), A306260 n = 1 ↔ n ∈ ({0, 1, 2, 4, 7, 9, 11, 14, 23, 25, 28, 37} : Finset ℕ)) :=
by
  sorry
