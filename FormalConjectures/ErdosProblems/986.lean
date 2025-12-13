/-
Copyright 2025 The Formal Conjectures Authors.

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

/-!
# Erdős Problem 986

For fixed `k ≥ 3`, is there a constant `c = c(k) > 0` such that
for all sufficiently large `n` one has
`R(k,n) ≫ n^(k-1) / (log n)^c`?

*Reference:* [erdosproblems.com/986](https://www.erdosproblems.com/986)

The Erdős Problems page notes this is known for `k = 3` (Spencer) and `k = 4`
(Mattheus–Verstraete), while the general case remains open.
-/

namespace Erdos986

open Filter

/-- A placeholder for the classical two-colour graph Ramsey number `R(k,n)`. -/
axiom  RamseyNumber : ℕ → ℕ → ℕ

/--
A bundled form of the asymptotic lower bound:
there exist constants `c > 0` and `C > 0` such that for all sufficiently large `n`,
`R(k,n) ≥ C * (n^(k-1) / (log n)^c)`.
We model the real exponent using `Real.rpow`.
-/
def RamseyLowerBound (k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (RamseyNumber k n : ℝ) ≥
          C * ((n : ℝ) ^ (k - 1) / Real.rpow (Real.log (n : ℝ)) c)

/--
**Erdős Problem 986.**
For any fixed `k ≥ 3`, does `R(k,n)` admit a lower bound of order
`n^(k-1) / (log n)^c` for some `c = c(k) > 0`?
-/
@[category research open, AMS 05]
theorem erdos_986 :
    (∀ k : ℕ, k ≥ 3 → RamseyLowerBound k) ↔ answer(sorry) := by
  sorry

/--
The Erdős Problems page reports the statement is known for `k = 3` (Spencer).
-/
@[category research solved, AMS 05]
theorem erdos_986.variants.three :
    RamseyLowerBound 3 ↔ answer(True) := by
  sorry

/--
The Erdős Problems page reports the statement is known for `k = 4`
(Mattheus–Verstraete).
-/
@[category research solved, AMS 05]
theorem erdos_986.variants.four :
    RamseyLowerBound 4 ↔ answer(True) := by
  sorry

end Erdos986

