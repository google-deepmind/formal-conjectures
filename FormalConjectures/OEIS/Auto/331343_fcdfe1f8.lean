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
A331343: $a(n) = \mathrm{lcm}(1,2,\dots,n) \cdot \sum_{k=1}^n \frac{2^{k-1} - 1}{k}$.

The expression is calculated in $\mathbb{N}$ using exact integer division property of the LCM.
$$a(n) = \sum_{k=1}^n \left(\frac{\mathrm{lcm}(1, \dots, n)}{k}\right) \cdot (2^{k-1} - 1)$$
-/
def A331343 (n : ℕ) : ℕ :=
  let L : ℕ := (Ico 1 (n + 1)).lcm id
  (Ico 1 (n + 1)).sum fun k : ℕ ↦ (L / k) * (2 ^ (k - 1) - 1)

-- Use the provided definition name `a` for the sequence.
def a (n : ℕ) : ℕ := A331343 n

-- The example theorems are removed as they were placeholders and are not part of the request.

/--
oeis_331343_conjecture_0: Conjecture: for n > 3, if n^3 | a(n), then n is prime.
If so, there are no such pseudoprimes.
-/
theorem oeis_331343_conjecture_0 : ∀ n : ℕ, n > 3 → n ^ 3 ∣ (a n) → Nat.Prime n := by
  sorry
