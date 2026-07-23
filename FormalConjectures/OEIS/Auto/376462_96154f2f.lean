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
open Nat Finset

/--
A helper function for the $A108625$ array:
$$A108625(n, k) = \sum_{i=0}^k \binom{n}{i}^2 \binom{n+k-i}{k-i}$$
-/
noncomputable def a108625_aux (n k : ℕ) : ℕ :=
  (range (k + 1)).sum fun i =>
    (n.choose i) ^ 2 * ((n + k - i).choose (k - i))

/--
A376462: $a(n) = \sum_{k = 0..n} \binom{n}{k}^2 \binom{n+k}{k} A108625(n, n-k)$.
-/
noncomputable def A376462 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    (n.choose k) ^ 2 * (n + k).choose k * (a108625_aux n (n - k))


theorem a_zero : A376462 0 = 1 := by
  constructor

theorem a_one : A376462 1 = 5 := by
  rfl

theorem a_two : A376462 2 = 109 := by
  subsingleton

theorem a_three : A376462 3 = 3317 := by
  econstructor

/--
We conjecture that the present sequence satisfies the same pair of supercongruences
as the Apéry numbers A005258. Specifically, for all primes $p \ge 5$ and all
positive integers $n$ and $r$:
1) $A(n p^r) \equiv A(n p^{r-1}) \pmod{p^{3r}}$
2) $A(n p^r - 1) \equiv A(n p^{r-1} - 1) \pmod{p^{3r}}$
-/
theorem oeis_376462_conjecture_0 :
  ∀ (p n r : ℕ),
    Nat.Prime p →
    5 ≤ p →
    0 < n →
    0 < r →
    (  -- Supercongruence 1
      (A376462 (n * p ^ r) : ℤ) ≡ (A376462 (n * p ^ (r - 1)) : ℤ) [ZMOD (p ^ (3 * r) : ℕ).cast]
    ∧
      -- Supercongruence 2
      let m_r := n * p ^ r - 1
      let m_r_minus_1 := n * p ^ (r - 1) - 1
      (A376462 m_r : ℤ) ≡ (A376462 m_r_minus_1 : ℤ) [ZMOD (p ^ (3 * r) : ℕ).cast]
    ) := by sorry
