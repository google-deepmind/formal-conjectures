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

open Nat Set

-- P i is the i-th prime, 1-indexed: p(i).
/-- P i is the i-th prime, 1-indexed: p(i). -/
noncomputable def P (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

-- S i is $p_i + p_{i+1}$.
/-- S i is $p_i + p_{i+1}$. -/
noncomputable def S (i : ℕ) : ℕ := P i + P (i + 1)

/--
A167918: $a(n)$ is smallest index $k > n$ of $k$-th prime with $f(n,k):=(p(k)+p(k+1))/(p(n)+p(n+1))$ an integer $\ge 2$ ($n=1,2,...$).
-/
noncomputable def A167918 (n : ℕ) : ℕ :=
  if n = 0 then 0 -- The sequence is 1-indexed.
  else
    let D_n := S n
    -- The set of indices $k$ that satisfy the condition.
    -- Since $k > n$, the ratio of the sums must be $\ge 2$ if divisibility holds.
    let k_set : Set ℕ := { k : ℕ | k > n ∧ D_n ∣ S k }

    -- sInf returns the smallest element of the set.
    sInf k_set


theorem a_one : A167918 1 = 6 := by sorry
theorem a_two : A167918 2 = 5 := by sorry
theorem a_three : A167918 3 = 5 := by sorry
theorem a_four : A167918 4 = 7 := by sorry


/--
Conjecture (2): It is conjectured that $f(n,k)=2$ for infinite many cases.
Where $f(n,k) = (p(k)+p(k+1))/(p(n)+p(n+1))$ and $k = \text{A167918}(n)$.
The value $f(n, k)$ is $S(\text{A167918}(n)) / S(n)$.
The conjecture is formalized as: for any bound $M$, there exists an index $n > M$ such that this ratio is 2.
-/
theorem oeis_A167918_conjecture_2 :
  (∀ M : ℕ, ∃ n : ℕ, n ≥ M ∧ n > 0 ∧ S (A167918 n) = 2 * S n) := by
  sorry
