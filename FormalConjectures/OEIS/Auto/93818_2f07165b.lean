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

open Nat Rat Int

/--
A093818: $a(n) = \gcd(\mathrm{A001008}(n), n!)$.
$\mathrm{A001008}(n)$ is the numerator of the $n$-th harmonic number $H_n = \sum_{i=1}^n \frac{1}{i}$.
-/
def a (n : ℕ) : ℕ :=
  Nat.gcd ((harmonic n).num.natAbs) (n.factorial)


-- The placeholder theorems from the prompt are included for completeness but are not the main task.
theorem a_one : a 1 = 1 := by
  simp_all [a,]

theorem a_two : a 2 = 1 := by
  delta a
  -- relies on harmonic 2 = 3/2
  norm_num

theorem a_three : a 3 = 1 := by
  delta a
  -- relies on harmonic 3 = 11/6
  norm_num

theorem a_four : a 4 = 1 := by
  delta a
  -- relies on harmonic 4 = 25/12
  norm_num


/-- Conjecture: every odd prime occurs as a term in the sequence. -/
theorem oeis_93818_conjecture_0 :
  ∀ (p : ℕ), Nat.Prime p → p ≠ 2 → ∃ (n : ℕ), 0 < n ∧ a n = p :=
by sorry
