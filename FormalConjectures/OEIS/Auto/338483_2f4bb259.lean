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
open Finset Nat Set

/-- The number of divisors function $\tau(n)$. -/
noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card

/--
$A047983(m)$ is the number of positive integers $k < m$ such that $\tau(k) = \tau(m)$.
-/
noncomputable def A047983_count (m : ℕ) : ℕ :=
  let tau_m := tau m
  -- Finset.Ico 1 m is the set of positive integers $k$ such that $1 \le k < m$.
  Finset.card ((Finset.Ico 1 m).filter (fun k : ℕ => tau k = tau_m))

/--
A338483: $a(n)$ is the smallest number having $n$ smaller numbers with the same number of divisors.
$A338483(n)$ is the smallest $m$ such that $A047983(m) = n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- sInf requires Classical.choice and returns the smallest element of the set.
  sInf {m : ℕ | A047983_count m = n}


-- Example terms from the OEIS page (proofs omitted as they are not required for the submission)
theorem a_one : a 1 = 3 := by sorry
theorem a_two : a 2 = 5 := by sorry
theorem a_three : a 3 = 7 := by sorry
theorem a_four : a 4 = 11 := by sorry


/--
A338483: Are there prime terms greater than 31?
--/
theorem oeis_338483_conjecture_0 :
  ∃ n : ℕ, n > 0 ∧ Nat.Prime (a n) ∧ a n > 31 := by
  sorry
