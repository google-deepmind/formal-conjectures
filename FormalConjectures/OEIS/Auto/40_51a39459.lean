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
A000040: The prime numbers.
The $n$-th prime number $p_n$, where $p_1 = 2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | (n' + 1) => nth Nat.Prime n'


theorem a_one : a 1 = 2 := by
  simp_all[a]

theorem a_two : a 2 = 3 := by
  borelize ℂ
  norm_num[a ·]

theorem a_three : a 3 = 5 := by
  norm_num[a]

theorem a_four : a 4 = 7 := by
  norm_num[a ·]


/--
A000040 Conjecture: log log a(n+1) - log log a(n) < 1/n. - _Thomas Ordowski_, Feb 17 2023
-/
theorem oeis_40_conjecture_5 (n : ℕ) (hn : 0 < n) :
  Real.log (Real.log ((a (n + 1)).cast : ℝ)) - Real.log (Real.log ((a n).cast : ℝ)) < 1 / (n.cast : ℝ) :=
by sorry
