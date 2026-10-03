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
# Sum involving Catalan-like triangle coefficients

The sequence is defined by
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} T(n, n-k)$$
where $T(n, k)$ is the array defined in A108625.

*References:*
- [A376462](https://oeis.org/A376462)
-/
open Nat Finset

namespace OeisA376462

/--
A helper function for the $A108625$ array:
$$A108625(n, k) = \sum_{i=0}^k \binom{n}{i}^2 \binom{n+k-i}{k-i}$$
-/
noncomputable def a108625_aux (n k : ℕ) : ℕ :=
  ∑ i ∈ range (k + 1),
    (n.choose i) ^ 2 * ((n + k - i).choose (k - i))

/--
The sequence $a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} T(n, n-k)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1),
    (n.choose k) ^ 2 * (n + k).choose k * (a108625_aux n (n - k))

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 5 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 109 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 3317 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 121501 := by rfl

/--
We conjecture that the present sequence satisfies the same pair of supercongruences
as the Apéry numbers A005258. Specifically, for all primes $p \ge 5$ and all
positive integers $n$ and $r$:
1) $A(n p^r) \equiv A(n p^{r-1}) \pmod{p^{3r}}$
2) $A(n p^r - 1) \equiv A(n p^{r-1} - 1) \pmod{p^{3r}}$
-/
@[category research open, AMS 11]
theorem supercongruences :
  ∀ (p n r : ℕ),
    p.Prime →
    5 ≤ p →
    0 < n →
    0 < r →
    (  -- Supercongruence 1
      (a (n * p ^ r) : ℤ) ≡ (a (n * p ^ (r - 1)) : ℤ) [ZMOD (p ^ (3 * r) : ℕ).cast]
    ∧
      -- Supercongruence 2
      let m_r := n * p ^ r - 1
      let m_r_minus_1 := n * p ^ (r - 1) - 1
      (a m_r : ℤ) ≡ (a m_r_minus_1 : ℤ) [ZMOD (p ^ (3 * r) : ℕ).cast]
    ) := by sorry

end OeisA376462
