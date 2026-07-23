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

-- We need to open scoped Nat.Prime for Nat.Prime. `Nat.Prime p` is just `p.Prime`.
open scoped Nat.Prime

/--
A236097: $a(n) = |\{0 < k < n-2: p = \phi(k) + \phi(n-k)/2 + 1, \text{prime}(p) - p - 1 \text{ and } \text{prime}(p) - p + 1 \text{ are all prime}\}|$, where $\phi(\cdot)$ is Euler's totient function.
-/
noncomputable def A236097 (n : ℕ) : ℕ :=
  -- The set of $k$ is $1 \le k \le n - 3$.
  -- Icc 1 (n - 3) is correct. If $n \le 3$, $n-3=0$ or less, Icc 1 0 is empty.
  (Icc 1 (n - 3)).sum fun k =>
    -- $p = \phi(k) + \phi(n-k)/2 + 1$.
    let p_val := k.totient + (n - k).totient / 2 + 1

    -- The $p$-th prime (1-indexed) is Nat.nth Nat.Prime (p_val - 1).
    -- Mathlib uses `Nat.prime` which is a bound variable style definition.
    -- The canonical way to get the $n$-th prime is `Nat.prime (n-1)` (using 1-indexing for $n$).
    -- In Mathlib, use `Nat.nth Nat.Prime (p_val - 1)` or simply `Nat.prime_aux` or similar.
    -- The common alias for the $n$-th prime is `Nat.prime (n-1)` in many older contexts,
    -- but after the search, `Nat.nth Nat.Prime` seems to be the right function.
    let p_prime := Nat.nth Nat.Prime (p_val - 1)

    -- Condition check. We assume the subtractions are safe because the prime sequence grows fast enough.
    -- For $p \ge 2$, $\pi_p \ge p+1$. The result of the subtraction must be in $\mathbb{N}$, and since they are primes, must be $\ge 2$.
    -- $p\_prime - p\_val - 1$ is interpreted as $p\_prime - (p\_val + 1)$.
    -- $p\_prime - p\_val + 1$ is straightforward.
    if p_val.Prime ∧ (p_prime - p_val - 1).Prime ∧ (p_prime - p_val + 1).Prime then 1
    else 0

/--
Conjecture: a(n) > 0 for all n > 31.
-/
theorem oeis_236097_conjecture_0 : ∀ (n : ℕ), n > 31 → A236097 n > 0 := by
  sorry
