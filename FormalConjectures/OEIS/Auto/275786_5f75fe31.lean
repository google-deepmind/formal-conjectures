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

open Nat

/--
The $d$-th triangular number, $T(d) = d(d+1)/2$.
-/
def T_triangular (d : ℕ) : ℕ := d * (d + 1) / 2

/--
A275786: $a(n) = \prod_{d|n} T(d)$ where $T(x)$ is the $x$-th triangular number.
-/
def a (n : ℕ) : ℕ :=
  (Nat.divisors n).prod T_triangular


theorem a_one : a 1 = 1 := by
  simp [a, T_triangular, Nat.divisors]

theorem a_two : a 2 = 3 := by
  simp [a, T_triangular, Nat.divisors]
  sorry

theorem a_three : a 3 = 6 := by
  simp [a, T_triangular, Nat.divisors]
  sorry

theorem a_four : a 4 = 30 := by
  simp [a, T_triangular, Nat.divisors]
  sorry

/-- A275786 Conjecture: the sequence is injective (all terms of this sequence occur only once). -/
theorem oeis_A275786_conjecture :
  ∀ n m : ℕ, n > 0 → m > 0 → (a n = a m → n = m) :=
  by sorry
