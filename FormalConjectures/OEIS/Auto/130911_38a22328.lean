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
A130911: $a(n)$ is the number of primes with odd binary weight among the first $n$ primes minus the number with an even binary weight.
Primes with odd binary weight are called odious primes (A027697); primes with even binary weight are called evil primes (A027699).
$$a(n) = \sum_{k=1}^n \left( \mathbf{1}_{\{\operatorname{popcount}(p_k) \text{ is odd}\}} - \mathbf{1}_{\{\operatorname{popcount}(p_k) \text{ is even}\}} \right)$$
where $p_k$ is the $k$-th prime number.
-/
noncomputable def A130911 (n : ℕ) : ℤ :=
  -- The binary weight (popcount) is the sum of digits in base 2.
  let binary_weight (k : ℕ) : ℕ := (Nat.digits 2 k).sum

  -- The function to be summed: +1 for odd weight, -1 for even weight.
  let weight_parity_sign (p : ℕ) : ℤ :=
    -- Nat.bodd returns true if the number is odd.
    if (binary_weight p).bodd then 1 else -1

  -- Sum over the indices i from 0 to n-1, corresponding to the first n primes.
  Finset.sum (Finset.range n) fun i =>
    let p_i := Nat.nth Nat.Prime i
    weight_parity_sign p_i

/-- Shevelev conjectures that a(n) >= 0 for n > 3. -/
theorem oeis_130911_conjecture_0 (n : ℕ) (h : n > 3) : A130911 n ≥ 0 := by
  sorry
