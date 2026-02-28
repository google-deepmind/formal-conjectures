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

/-!
# Erdős Problem 100
*References:*
* [erdosproblems.com/100](https://www.erdosproblems.com/100)
* [Kanold](No references found)
* [GuKa15](Guth, Larry and Katz, Nets Hawk, On the Erd\H{o}s distinct distances problem in the plane. Ann. of Math. (2) (2015), 155-190.)
* [Piepmeyer](No references found)
-/

open Set Metric Filter Real
open scoped EuclideanGeometry

namespace Erdos100

/-- If two distances in A differ, they differ by at least 1. -/
def DistancesSeparated (A : Finset ℝ²) : Prop :=
  ∀ p₁ q₁ p₂ q₂, p₁ ∈ A → q₁ ∈ A → p₂ ∈ A → q₂ ∈ A →
    dist p₁ q₁ ≠ dist p₂ q₂ →
    |dist p₁ q₁ - dist p₂ q₂| ≥ 1

/-- Is the diameter of $A$ at least $Cn$ for some constant $C > 0$? -/
@[category research open, AMS 52]
theorem erdos_100 :
    answer(sorry) ↔ ∃ C > (0 : ℝ), ∀ᶠ n in atTop, ∀ A : Finset ℝ²,
      A.card = n →
      DistancesSeparated A →
      diam (A : Set ℝ²) > C * n := by
  sorry

/-- Stronger conjecture: diameter $\geq n - 1$ for sufficiently large $n$. -/
@[category research open, AMS 52]
theorem erdos_100_strong :
    ∀ᶠ n in atTop, ∀ A : Finset ℝ²,
      A.card = n →
      DistancesSeparated A →
      diam (A : Set ℝ²) ≥ n - 1 := by
  sorry

/-- From [Kanold]: diameter $\geq n^{3/4}$.
TODO: find reference -/
@[category research open, AMS 52]
theorem erdos_100_kanold :
    ∃ C > (0 : ℝ), ∀ᶠ n in atTop, ∀ A : Finset ℝ²,
      A.card = n →
      DistancesSeparated A →
      diam (A : Set ℝ²) ≥ (n : ℝ) ^ (3 / 4 : ℝ) := by
  sorry

/-- From [GuKa15]: diameter $\gg n / \log n$. -/
@[category research open, AMS 52]
theorem erdos_100_guth_katz :
    ∃ C > (0 : ℝ), ∀ᶠ n in atTop, ∀ A : Finset ℝ²,
      A.card = n →
      DistancesSeparated A →
      diam (A : Set ℝ²) ≥ C * n / log n := by
  sorry

/-- From [Piepmeyer]: 9 points with diameter $< 5$.
TODO: find reference -/
@[category research formally solved using formal_conjectures at "https://github.com/theaustinhatfield/formal-conjectures/blob/solve-erdos-100-piepmeyer/FormalConjectures/ErdosProblems/100.lean", AMS 52]
theorem erdos_100_piepmeyer :
    ∃ A : Finset ℝ², A.card = 9 ∧ DistancesSeparated A ∧
      diam (A : Set ℝ²) < 5 := by
  sorry

end Erdos100
