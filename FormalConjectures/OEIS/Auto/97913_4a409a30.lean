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

open BigOperators Finset Nat

/--
A097913: G.f.: (1+x^18)/((1-x)*(1-x^8)*(1-x^12)*(1-x^24)).
The sequence $a(n)$ is the coefficient of $x^n$ in the generating function.
$a(n) = f(n) + f(n-18)$, where $f(m)$ is the number of partitions of $m$ into parts from $\{1, 8, 12, 24\}$.
-/
def A097913 (n : ℕ) : ℕ :=
  let f (m : ℕ) : ℕ :=
    -- f(m) is the number of non-negative integer solutions (b₁, b₈, b₁₂, b₂₄) to the equation
    -- b₁ + 8*b₈ + 12*b₁₂ + 24*b₂₄ = m, where b₁ is the remainder.
    (Finset.range (m / 24 + 1)).sum fun l =>
      (Finset.range ((m - 24 * l) / 12 + 1)).sum fun k =>
        (Finset.range ((m - 24 * l - 12 * k) / 8 + 1)).card

  f n + if 18 ≤ n then f (n - 18) else 0


theorem a_zero : A097913 0 = 1 := by
  rfl

theorem a_one : A097913 1 = 1 := by
  rfl

theorem a_two : A097913 2 = 1 := by
  rfl

theorem a_three : A097913 3 = 1 := by
  rfl

/-! ### Formalization of the Conjecture -/

noncomputable section

open PowerSeries
open scoped PowerSeries

-- We work with formal power series over ℚ.
private abbrev PQS := PowerSeries ℚ

/--
The generating function for A097913, viewed as a power series over ℚ.
Since the constant term of the denominator is 1, it is invertible in the power series ring.
-/
@[simp]
def A097913.generating_function : PQS :=
  let num : PQS := (1 + X ^ 18)
  let den : PQS := (1 - X) * (1 - X ^ 8) * (1 - X ^ 12) * (1 - X ^ 24)
  num * den⁻¹

/--
The mathematical object "Poincaré series for genus 2 Siegel theta series of odd unimodular lattices"
is not defined in Mathlib, so we introduce a symbolic placeholder for it.
This object is conjectured to be equal to the generating function A097913.
-/
axiom poincare_series_genus2_odd_unimodular_lattices : PQS

/--
oeis_97913_conjecture_0: Conjectured Poincaré series for genus 2 Siegel theta series of odd unimodular lattices.
The conjecture is that the generating function A097913.generating_function equals this Poincaré series.
-/
theorem poincare_series_conjecture :
  A097913.generating_function = poincare_series_genus2_odd_unimodular_lattices :=
by sorry

end noncomputable section
