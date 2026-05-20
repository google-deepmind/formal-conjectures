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
open Set

/--
A159829: $a(n)$ is the smallest natural number $m$ such that $n^3+m^3+1^3$ is prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | 1 ≤ m ∧ Nat.Prime (n ^ 3 + m ^ 3 + 1) }


theorem a_one : a 1 = 1 := by sorry

theorem a_two : a 2 = 2 := by sorry

theorem a_three : a 3 = 1 := by sorry

theorem a_four : a 4 = 2 := by sorry


/--
OEIS A159829 Exponent k>2: Are there infinitely many primes of the forms $n^k+m^k$ and $n^k+m^k+1^k$?
We formalize the claim for $n^k+m^k+1^k$, which generalizes the sequence A159829.
-/
theorem oeis_159829_conjecture_0 : ∀ (k : ℕ), k ≥ 3 →
    Set.Infinite { p : ℕ | ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ Nat.Prime p ∧ p = n ^ k + m ^ k + 1 } := by
  sorry
