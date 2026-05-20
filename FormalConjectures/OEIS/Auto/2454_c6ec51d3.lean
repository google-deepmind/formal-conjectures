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

open Nat

/--
A002454: Central factorial numbers: $a(n) = 4^n \cdot (n!)^2$.
-/
def a (n : ℕ) : ℕ := 4 ^ n * n.factorial ^ 2


theorem a_zero : a 0 = 1 := by
  rfl

theorem a_one : a 1 = 4 := by
  rfl

theorem a_two : a 2 = 64 := by
  rfl

theorem a_three : a 3 = 2304 := by
  rfl

open Matrix Complex

/--
Conjecture A002454: Let $\zeta$ be a primitive $(2n+1)$-th root of unity.
Then the permanent of the $2n \times 2n$ matrix $[m(j,k)]_{j,k=1..2n}$ is
$a(n)/(2n+1) = ((2n)!!)^2/(2n+1)$, where $m(j,k)$ is $1$ or $\frac{1+\zeta^{j-k}}{1-\zeta^{j-k}}$
according as $j = k$ or not.

Note: We use $0$-indexed matrices $j, k \in \operatorname{Fin}(2n)$ corresponding to $1$-based indices $j+1, k+1$.
The difference in exponent $j-k$ remains the same.
-/
theorem oeis_2454_conjecture_0 (n : ℕ) :
  let N : ℕ := 2 * n
  -- The order of the root of unity
  let K : ℕ := N + 1
  -- We work in the complex numbers ℂ.
  -- Assume a primitive K-th root of unity
  ∀ (ζ : ℂ), IsPrimitiveRoot ζ K →
  (
    let M : Matrix (Fin N) (Fin N) ℂ := of fun j k : Fin N =>
      if j = k
      then 1
      else
        -- j and k are Nat, coerced to ℤ for the power exponent
        let pow : ℤ := (j : ℤ) - (k : ℤ)
        (1 + ζ ^ pow) / (1 - ζ ^ pow)
    M.permanent = (a n : ℂ) / (K : ℂ)
  ) := by sorry
