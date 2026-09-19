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

import FormalConjecturesUtil

/-!
# Representations as sum of three consecutive primes with parity factor

$a(n)$ is the number of ways to write $n$ as $u + (1 + (n \bmod 2)) v$ with $v \le n/2$,
where $u$ and $v$ are both sums of three consecutive primes.

*References:*
- [A386888](https://oeis.org/A386888)
-/
open Nat Finset

namespace OeisA386888

/--
Number of ways to write $n$ as $u + (1+(n \bmod 2)) v$ with $v \le n/2$.
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

  ) (range max_index_bound)

@[category API, AMS 11]
lemma a_zero_for_small (n : ℕ) (hn : n ≤ 11) : a n = 0 := by
  unfold a
  apply Finset.card_eq_zero.mpr
  ext j
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨_, h1, _⟩
    have hp (x : ℕ) : 2 ≤ Nat.nth Nat.Prime x := by
      apply Nat.Prime.two_le
      apply Nat.nth_mem
      intro h
      exfalso
      exact Nat.infinite_setOf_prime h
    have h_S (k : ℕ) :
        6 ≤ Nat.nth Nat.Prime k + Nat.nth Nat.Prime (k + 1) + Nat.nth Nat.Prime (k + 2) := by
      have hk := hp k
      have hk1 := hp (k+1)
      have hk2 := hp (k+2)
      omega
    have hj := h_S j
    omega
  · intro h; exfalso; simp_all

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := a_zero_for_small 0 (by decide)

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := a_zero_for_small 1 (by decide)

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := a_zero_for_small 2 (by decide)

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := a_zero_for_small 3 (by decide)

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := a_zero_for_small 4 (by decide)

@[category test, AMS 11]
theorem a_5 : a 5 = 0 := a_zero_for_small 5 (by decide)

/--
If n is an odd number greater than 905, or an even number greater than 1466, then we have a(n) > 0.
Also, a(n) > 1 for all n > 2258.
(In the case k = m = 3 for the general conjecture by Sun.)
-/
@[category research open, AMS 11]
theorem eventually_positive :
  (∀ n : ℕ,
    ((Odd n ∧ n > 905) ∨ (Even n ∧ n > 1466)) → a n > 0)
  ∧
  (∀ n : ℕ, n > 2258 → a n > 1) :=
by sorry

end OeisA386888
