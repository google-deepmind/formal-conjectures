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
open Rat Nat

/--
A046969: Denominators of coefficients in Stirling's expansion for $\log(\Gamma(z))$.
The $n$-th term is the denominator of the rational number
$$ \frac{B_{2n}}{2n(2n-1)} $$
where $B_{2n}$ is the $2n$-th Bernoulli number (Mathlib's `bernoulli`).
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    -- We use Rat.bernoulli (aliased as bernoulli) for B_{2n}.
    -- The denominator k is coerced to Rat for division.
    (bernoulli m / (k : ℚ)).den


theorem a_one : a 1 = 12 := by sorry

theorem a_two : a 2 = 360 := by sorry

theorem a_three : a 3 = 1260 := by sorry

theorem a_four : a 4 = 1680 := by sorry

/--
Conjecture II: if a(n)/12 is prime, then a(n-1)/12 - (n-1), a(n)/12 - n and a(n+2)/12 - (n+2) are multiples of 6.

The conjecture is formalized for $n \ge 2$ since $a(n-1)$ must be well-defined for $n-1 \ge 1$.
We assume $a(k)$ is a multiple of 12 for all relevant indices $k$, allowing for natural number division.
The differences are cast to $\mathbb{Z}$ to ensure well-defined subtraction.
-/
theorem oeis_a046969_conjecture_2 (n : ℕ) :
    2 ≤ n →
    (a n) % 12 = 0 →
    Nat.Prime ((a n) / 12) →
    (a (n - 1)) % 12 = 0 →
    (a (n + 2)) % 12 = 0 →
    6 ∣ (((a (n - 1)) / 12 : ℤ) - ((n - 1) : ℤ)) ∧
    6 ∣ (((a n) / 12 : ℤ) - (n : ℤ)) ∧
    6 ∣ (((a (n + 2)) / 12 : ℤ) - ((n + 2) : ℤ)) :=
by sorry
