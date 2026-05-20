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

open Nat Rat Finset

/--
A263326: Denominator of the rational number $\sum_{d|n} \frac{1}{d+1}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if hn : n > 0 then
    (Finset.sum (Nat.divisors n) fun d : ℕ => (d.cast + 1 : ℚ)⁻¹).den
  else 0

-- Definition of the generalized sum from the conjecture
/--
The generalized sum $\sum_{d|n} \frac{1}{(d+k)^s}$ for $n, k, s \in \mathbb{N}$.
We require $n>0$ for the set of divisors to be non-empty, and $k, s > 0$ from the conjecture's context.
Since $d \ge 1$ for $d \in \mathrm{divisors}(n)$ when $n>0$, the denominator $d+k$ is non-zero.
-/
noncomputable def sum_divisors_inv_pow (n k s : ℕ) : ℚ :=
  Finset.sum (Nat.divisors n) fun d : ℕ => (d.cast + k.cast : ℚ)⁻¹ ^ s

/--
A263326 Conjecture: For any positive integers k and s, all the numbers
$\sum_{d|n} \frac{1}{(d+k)^s}$ (n = 1,2,3,...) have pairwise distinct fractional parts,
and none of them is an integer.
-/
theorem oeis_a263326_conjecture_1 :
  ∀ (k s : ℕ), k > 0 ∧ s > 0 →
  (∀ n : ℕ, n > 0 →
    -- The value is not an integer
    (Int.fract (sum_divisors_inv_pow n k s) ≠ 0))
  ∧
  -- The fractional parts are distinct for distinct n
  (∀ n₁ n₂ : ℕ, n₁ > 0 → n₂ > 0 → Int.fract (sum_divisors_inv_pow n₁ k s) = Int.fract (sum_divisors_inv_pow n₂ k s) → n₁ = n₂) := by
  sorry
