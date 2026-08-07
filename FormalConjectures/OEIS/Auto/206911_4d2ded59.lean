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

open Real Nat Finset Filter

/--
A206911: Position of $n$-th partial sum of the harmonic series when all the partial sums are jointly ranked with the set $\{\log(k+1)\}$; complement of A206912.
The $n$-th term $a(n)$ is the rank of $S(n) = \sum_{i=1}^n 1/i$ in the sorted list.
This rank is computed as $n + \lfloor \exp(S(n)) - 1 \rfloor$.
-/
noncomputable def A206911 (n : ℕ) : ℕ :=
  -- Define $S_n = \sum_{k=1}^n \frac{1}{k}$
  let S_n_real : ℝ := (range n).sum fun k => 1 / ((k : ℝ) + 1)

  -- Count of log terms is $\lfloor e^{S_n} - 1 \rfloor$
  let count_log_terms : ℤ := floor (exp S_n_real - 1)

  -- Final rank: n + count.
  n + count_log_terms.toNat


theorem a_one : A206911 1 = 2 := by sorry

theorem a_two : A206911 2 = 5 := by sorry

theorem a_three : A206911 3 = 8 := by sorry

theorem a_four : A206911 4 = 11 := by sorry

/-- The difference sequence D(n) = A206911(n+1) - A206911(n), indexed starting at n=1. -/
noncomputable def A206911_diff (n : ℕ) : ℕ := A206911 (n + 1) - A206911 n

/-- The number of 3s in the first N terms of the difference sequence D(1), ..., D(N). -/
noncomputable def A206911_count_3s (N : ℕ) : ℕ :=
  (range N).sum fun n => if A206911_diff (n + 1) = 3 then 1 else 0

/-- The number of 2s in the first N terms of the difference sequence D(1), ..., D(N). -/
noncomputable def A206911_count_2s (N : ℕ) : ℕ :=
 (range N).sum fun n => if A206911_diff (n + 1) = 2 then 1 else 0

/--
Conjecture: the difference sequence of A206911 consists of 2s and 3s, and the ratio (number of 3s)/(number of 2s) tends to a number between 3.5 and 3.6.
-/
theorem oeis_206911_conjecture :
  -- Part 1: The difference sequence consists of 2s and 3s for n ≥ 1.
  (∀ n : ℕ, 1 ≤ n → A206911_diff n = 2 ∨ A206911_diff n = 3) ∧

  -- Part 2: The ratio of counts of 3s to 2s tends to a limit L in (3.5, 3.6).
  (∃ L : ℝ,
     (35/10 : ℝ) < L ∧ L < (36/10 : ℝ) ∧
     Tendsto (fun N : ℕ => (A206911_count_3s N : ℝ) / (A206911_count_2s N : ℝ)) atTop (nhds L))
:= by sorry
