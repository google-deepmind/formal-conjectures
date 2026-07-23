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

open Nat Finset Classical

/--
A386888: Number of ways to write $n$ as $u + (1+(n \bmod 2)) \cdot v$ with $v \le n/2$,
where $u$ and $v$ are both sums of three consecutive primes.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define $p_k$ as the $k$-th prime, 0-indexed.
  let p (k : ℕ) : ℕ := Nat.nth Nat.Prime k

  -- Define $S(k)$ as the sum of three consecutive primes starting at $p_k$.
  let S (k : ℕ) : ℕ := p k + p (k + 1) + p (k + 2)

  -- $C$ is the coefficient $1 + n \bmod 2$.
  let C : ℕ := 1 + n % 2

  -- A safe upper bound for indices $j$ and $k$.
  let max_index_bound := n + 1

  -- We count the number of indices $j$ such that $v = S j$ satisfies all constraints,
  -- which is equivalent to counting the number of valid pairs $(u, v)$.
  Finset.card <| Finset.filter (λ j =>
    let v := S j

    -- Constraint 1: $v \le n/2$, represented as $2 \cdot v \le n$.
    v * 2 ≤ n ∧

    -- Constraint 2: Calculate $u = n - C \cdot v$. Ensure no underflow.
    C * v ≤ n ∧
    let u := n - C * v

    -- Constraint 3: $u$ must be a sum of three consecutive primes.
    -- Bounded search for an index $k$ such that $S k = u$.
    ∃ k ∈ range max_index_bound, S k = u

  ) (Finset.range max_index_bound)


theorem a_one : a 1 = 0 := by
  sorry

theorem a_two : a 2 = 0 := by
  sorry

theorem a_three : a 3 = 0 := by
  sorry

theorem a_four : a 4 = 0 := by
  sorry


/--
Conjecture 2:
If n is an odd number greater than 905, or an even number greater than 1466, then we have a(n) > 0.
Also, a(n) > 1 for all n > 2258.
(In the case k = m = 3 for the general conjecture by Sun.)
-/
theorem oeis_386888_conjecture_2 :
  (∀ n : ℕ,
    ((Odd n ∧ n > 905) ∨ (Even n ∧ n > 1466)) → a n > 0)
  ∧
  (∀ n : ℕ, n > 2258 → a n > 1) :=
by sorry
