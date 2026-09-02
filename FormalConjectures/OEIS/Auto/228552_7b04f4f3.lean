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

open Matrix Nat

/--
A228552: Square root of the absolute value of A069191(n).
A069191(n) is the determinant of the $n \times n$ matrix $M$ where $M_{i,j} = 1$ if $i+j$ is prime, and $0$ otherwise, for $1 \le i, j \le n$.
$$a(n) = \sqrt{\left|\det\left( \left( \indicator_{\mathbb{P}}(i+j) \right)_{1 \le i, j \le n} \right)\right|}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Matrix.det (Matrix.of (fun (i j : Fin n) =>
    if Nat.Prime (i.val + j.val + 2) then (1 : ℤ) else (0 : ℤ)))).natAbs.sqrt


theorem a_one : a 1 = 1 := by
  subsingleton

theorem a_two : a 2 = 1 := by
  delta a
  norm_num [(Matrix.det_fin_two)]

theorem a_three : a 3 = 1 := by
  delta a
  norm_num +decide [@Matrix.det_succ_row_zero]

theorem a_four : a 4 = 0 := by
  trivial

/-- oeis_228552_conjecture_0: We conjecture that a(n) > 0 for all n > 15. -/
theorem oeis_228552_conjecture_0 : ∀ n : ℕ, 15 < n → a n > 0 :=
  by sorry
