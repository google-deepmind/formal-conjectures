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
# Central factorial numbers: $((2n)!!)^2$

Central factorial numbers: $a(n) = 4^n (n!)^2 = ((2n)!!)^2$.

*References:*
- [A002454](https://oeis.org/A002454)-/

namespace OeisA2454

/-- Central factorial numbers: $a(n) = 4^n (n!)^2$. -/
def a (n : ℕ) : ℕ :=
  4 ^ n * n.factorial ^ 2

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 64 := by rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2304 := by rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 147456 := by rfl

/--
Let $\zeta$ be a primitive $(2n+1)$-th root of unity. Then the permanent of the
$2n \times 2n$ matrix $[m(j,k)]_{j,k=1..2n}$ is $a(n)/(2n+1) = ((2n)!!)^2/(2n+1)$,
where $m(j,k)$ is $1$ or $(1+\zeta^{j-k})/(1-\zeta^{j-k})$ according as $j = k$ or not.
- Zhi-Wei Sun, Dec 21 2021-/
@[category research open, AMS 11 15]
theorem conjecture (n : ℕ) :
    let N : ℕ := 2 * n
    let K : ℕ := N + 1
    ∀ (ζ : ℂ), IsPrimitiveRoot ζ K →
      Matrix.permanent (fun (j k : Fin N) =>
        if j = k then
          (1 : ℂ)
        else
          let pow : ℤ := (j : ℤ) - (k : ℤ)
          (1 + ζ ^ pow) / (1 - ζ ^ pow)
      ) = (a n : ℂ) / (K : ℂ) := by
  sorry

end OeisA2454
