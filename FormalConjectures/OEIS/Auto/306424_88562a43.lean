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

open List Finset Nat

/--
A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each $b = 3..k-1$ never contains more than two distinct digits.
-/
def A306424_condition (k : ℕ) : Prop :=
  -- The bases $b$ range over $3 \le b \le k-1$, expressed as $3 \le b$ and $b < k$.
  ∀ b : ℕ, 3 ≤ b ∧ b < k → ((Nat.digits b k).toFinset.card) ≤ 2

/--
The sequence A306424: Numbers $k$ such that the base $b$ expansion of $k$ for each $b = 3..k-1$ never contains more than two distinct digits.
-/
noncomputable def a (n : ℕ) : ℕ := n.nth A306424_condition


theorem a_one : a 1 = 1 := by
  sorry

theorem a_two : a 2 = 2 := by
  sorry

theorem a_three : a 3 = 3 := by
  sorry

theorem a_four : a 4 = 4 := by
  sorry


/--
A306424 Conjecture: The sequence is finite, with 43 being the last term.
-/
theorem oeis_306424_conjecture_0 : A306424_condition 43 ∧ ∀ k : ℕ, 43 < k → ¬ A306424_condition k := by
  sorry
