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

open Nat Int

/--
A003161: A binomial coefficient sum.
The number of triples of standard tableaux of the same shape of height less than or equal to 2.
$$a(n) = \sum_{k = 0}^{\lfloor n/2 \rfloor} \left( \binom{n}{k} - \binom{n}{k-1} \right)^3$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k =>
    -- Use Int for arithmetic robustness to model $\binom{n}{k-1} = 0$ when $k=0$.
    let choose_k_int : ℤ := (Nat.choose n k).cast
    let choose_km1_int : ℤ := if k = 0 then 0 else (Nat.choose n (k - 1)).cast
    let diff : ℤ := choose_k_int - choose_km1_int
    -- The difference is known to be non-negative in the summation range, so toNat is safe.
    (diff ^ 3).toNat

/--
Sequence b(n) is defined as a(2*n - 1) for $n \ge 1$.
We define it on ℕ and rely on the theorem statement to enforce $n \ge 1$.
When $n>0$, $2*n - 1$ is well-defined in ℕ.
-/
def b (n : ℕ) : ℕ :=
  a (2 * n - 1)

/--
A003161 Conjecture: Let b(n) = a(2*n-1). Then the supercongruence b(n*p^k) == b(n*p^(k-1)) (mod p^(3*k)) holds for positive integers n and k and all primes p >= 5.
-/
theorem oeis_3161_conjecture_1 (n k p : ℕ) (hn : n > 0) (hk : k > 0) (hp : Nat.Prime p) (hmod : p ≥ 5) :
    (b (n * p ^ k)).cast ≡ (b (n * p ^ (k - 1))).cast [ZMOD (p.cast ^ (3 * k) : ℤ)] := by
  sorry
