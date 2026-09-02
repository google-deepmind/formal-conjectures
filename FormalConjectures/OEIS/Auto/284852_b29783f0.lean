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

open List Nat

/-- The substitution rule for A284851: $0 \mapsto [0, 1]$, $1 \mapsto [0, 1, 0, 0]$. -/
def A284851_subst_rule : ℕ → List ℕ
| 0 => [0, 1]
| 1 => [0, 1, 0, 0]
| _ => []

/--
The sequence of finite prefixes of A284851.
$L_0 = [0]$. $L_{n+1} = L_n$.flatMap $A284851\_subst\_rule$.
-/
def A284851_list_at_step : ℕ → List ℕ
| 0 => [0]
| (n + 1) => (A284851_list_at_step n).flatMap A284851_subst_rule

/--
A proxy for the infinite word A284851.
We take the value from a large-enough prefix (10th iteration).
-/
noncomputable def A284851_value (n : ℕ) : ℕ :=
  (A284851_list_at_step 10).getD n 1

/--
A284852: Positions of 0 in A284851; complement of A284853.
The $n$-th term $a(n)$ is the sequence of 1-indexed positions $k$ such that $A284851(k-1) = 0$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The sequence is 1-indexed, so we find the (n-1)-th 0-indexed position k, and add 1.
  (n - 1).nth (fun k => A284851_value k = 0) + 1


theorem a_one : a 1 = 1 := by
  simp_all[a]
  exact ( 0).nth_count ↑rfl

theorem a_two : a 2 = 3 := by
  delta a
  delta A284851_value
  exact (congr_arg) (. + 1) (( (congr_arg _) (by constructor)).trans ( (2).nth_count (↑rfl)))

theorem a_three : a 3 = 5 := by
  delta a
  exact (congr_arg) ( ·+1) ((congr_arg _ (by constructor)).trans (Nat.nth_count (↑rfl)))

theorem a_four : a 4 = 6 := by
  (inhabit Int)
  norm_num[a]
  exact (congr_arg) (.+1) ((congr_arg _ (by decide)).trans (Nat.nth_count rfl))

-- The constant r = (3 + sqrt(3)) / 3
noncomputable def r : ℝ := (3 + Real.sqrt 3) / 3

/--
Conjecture A284852: -2 < n*r - a(n) < 2 for n >= 1, where r = (3+sqrt(3))/3.
-/
theorem oeis_284852_conjecture : ∀ (n : ℕ), 0 < n →
  abs ((n : ℝ) * r - (a n : ℝ)) < 2 := by sorry
