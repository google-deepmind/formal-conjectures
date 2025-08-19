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
# Erdős Problem 213

*Reference:* [erdosproblems.com/213](https://www.erdosproblems.com/213)
-/

open scoped EuclideanGeometry

/--
Let n ≥ 4. Are there n points in ℝ², no three on a line and no four on a circle,
such that all pairwise distances are integers?
-/
@[category research open, AMS 52]
theorem erdos_213 :
    (∃ S : Set ℝ², S.Finite ∧ S.ncard ≥ 4 ∧
                   (∀ T : Set ℝ², T ⊆ S ∧ T.ncard = 3 → ¬ Collinear ℝ T) ∧
                   (∀ Q : Set ℝ², Q ⊆ S ∧ Q.ncard = 4 → ¬ EuclideanGeometry.Cospherical Q) ∧
                   (S.Pairwise fun p₁ p₂ => dist p₁ p₂ ∈ Set.range Int.cast))
    ↔ answer(sorry) := by
  sorry
