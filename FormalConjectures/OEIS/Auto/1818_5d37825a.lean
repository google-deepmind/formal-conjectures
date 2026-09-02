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

open Nat Finset Matrix

/--
A001818: Squares of double factorials: $(1 \cdot 3 \cdot 5 \cdot \dots \cdot (2n-1))^2 = ((2n-1)!!)^2$.
-/
def a (n : ℕ) : ℕ :=
  ((range n).prod (fun k => 2 * k + 1)) ^ 2


theorem a_zero : a 0 = 1 := by
  simp [a]

theorem a_one : a 1 = 1 := by
  simp [a]

theorem a_two : a 2 = 9 := by
  simp [a]; norm_num

theorem a_three : a 3 = 225 := by
  simp [a]; norm_num

/--
Conjecture 1: For any primitive 2n-th root zeta of unity, the permanent of the 2n X 2n matrix [m(j,k)]_{j,k=1..2n} coincides with a(n) = ((2n-1)!!)^2, where m(j,k) is (1+zeta^(j-k))/(1-zeta^(j-k)) if j is not equal to k, and 1 otherwise.
-/
theorem oeis_1818_conjecture_0 (n : ℕ) (h_n : 1 ≤ n) :
    ∀ (ζ : ℂ), IsPrimitiveRoot ζ (2 * n) →
      permanent (fun (i j : Fin (2 * n)) =>
        if i = j then
          (1 : ℂ)
        else
          (1 + ζ ^ (i.val - j.val : ℤ)) / (1 - ζ ^ (i.val - j.val : ℤ))
      ) = (a n : ℂ) := by
  sorry
