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

open Nat Classical

/--
A366833: Number of times $n$ appears in A362965 (number of primes $\le$ the $n$-th prime power).
This is equivalent to: One less than the number of prime powers $q$ such that $\mathrm{prime}(n) \le q \le \mathrm{prime}(n+1)$, inclusive.
Where $\mathrm{prime}(n)$ is the $n$-th prime ($p_1=2$).
$$a(n) = \left|\left\{q \in \mathbb{N} : \text{IsPrimePow}(q) \land \mathrm{prime}(n) \le q \le \mathrm{prime}(n+1)\right\}\right| - 1$$
-/
noncomputable def A366833 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    -- p_n (1-indexed) is Nat.nth Nat.Prime (n-1) (0-indexed). Since n > 0, n-1 is safe.
    let p_n   : ℕ := Nat.nth Nat.Prime (n - 1)
    -- p_{n+1} is Nat.nth Nat.Prime n
    let p_np1 : ℕ := Nat.nth Nat.Prime n

    -- Count the number of prime powers in the inclusive interval [p_n, p_{n+1}]
    let count_prime_powers : ℕ :=
      Finset.card ((Finset.Icc p_n p_np1).filter IsPrimePow)

    -- Subtracting 1 is safe since both p_n and p_{n+1} are prime powers, giving a count >= 2.
    count_prime_powers - 1


theorem a_one : A366833 1 = 1 := by
  sorry

theorem a_two : A366833 2 = 2 := by
  sorry

theorem a_three : A366833 3 = 1 := by
  sorry

theorem a_four : A366833 4 = 3 := by
  sorry

/--
Conjecture: a(n) can be only 1, 2, or 3 (with the first occurrences of 3 appearing at n = 4, 9, 30, 327 and 3512).
-/
theorem oeis_366833_conjecture_0 : ∀ (n : ℕ), 1 ≤ n → A366833 n ∈ ({1, 2, 3} : Finset ℕ) := by
  sorry
