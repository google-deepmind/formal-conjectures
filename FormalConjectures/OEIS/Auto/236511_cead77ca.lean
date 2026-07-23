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
A236511: $a(n) = |\{0 < k < n: p = 3\phi(k) + \phi(n-k) - 1, p + 2, p + 6 \text{ and } p + 8 \text{ are all prime}\}|$, where $\phi(\cdot)$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (Ioo 0 n).sum (fun k ↦
    let T := 3 * totient k + totient (n - k)
    -- p = T - 1. The four primes are p, p+2, p+6, p+8, which correspond to T-1, T+1, T+5, T+7.
    if (T - 1).Prime ∧ (T + 1).Prime ∧ (T + 5).Prime ∧ (T + 7).Prime then 1 else 0
  )

/-- Conjecture: a(n) > 0 for all n > 1075. -/
theorem oeis_236511_conjecture_0 : ∀ n : ℕ, n > 1075 → a n > 0 := by sorry
