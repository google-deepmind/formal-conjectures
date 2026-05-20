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
A003162: A binomial coefficient summation.
The sequence is $a(n) = S(3,n)/S(1,n)$, where
$S(r,n) = \sum_{k = 0}^{\lfloor n/2 \rfloor} (\binom{n}{k} - \binom{n}{k-1})^r$.
$$a(n) = \frac{\sum_{k = 0}^{\lfloor n/2 \rfloor} \left( \binom{n}{k} - \binom{n}{k-1} \right)^3}{\binom{n}{\lfloor n/2 \rfloor}}$$
where $\binom{n}{-1} = 0$.
-/
def A003162 (n : ℕ) : ℕ :=
  let numerator := (Finset.range (n / 2 + 1)).sum fun k =>
    let c_k := n.choose k
    let c_k_prev := if k = 0 then 0 else n.choose (k - 1)
    (c_k - c_k_prev) ^ 3

  let denominator := n.choose (n / 2)
  -- The OEIS entry implies this division is exact
  numerator / denominator

/--
Conjecture sequence $b(n) = a(2n-1)$.
Since $n$ is a positive integer in the context of the conjecture, $2n-1$ is always $\ge 1$.
-/
def A003162.b (n : ℕ) : ℕ :=
  A003162 (2 * n - 1)

/--
%C A003162 Conjecture: Let b(n) = a(2*n-1). Then the supercongruence b(n*p^k) == b(n*p^(k-1)) (mod p^(3*k))
holds for positive integers n and k and all primes p >= 5. See A183069.
-/
theorem oeis_3162_supercongruence_conjecture :
    ∀ (n k p : ℕ),
      n > 0 → k > 0 → Nat.Prime p → p ≥ 5
      → (A003162.b (n * p ^ k) : ℤ) ≡ (A003162.b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)] :=
  by sorry
