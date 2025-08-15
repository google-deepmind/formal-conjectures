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
# Erdős Problem 352

*Reference:* [erdosproblems.com/352](https://www.erdosproblems.com/352)
-/

open scoped EuclideanGeometry
open scoped ProbabilityTheory

/--
Is there some c > 0 such that every measurable A ⊆ ℝ² of measure ≥ c
 contains the vertices of a triangle of area 1?
-/
@[category research open, AMS 51]
theorem erdos_352 :
    (∃ c > (0: ℝ), ∀ A : Set ℝ², MeasurableSet A → ℙ A ≥ c.toEReal
       → (∃ t : Affine.Triangle ℝ ℝ²,
           (∀ p : Fin 3, t.points p ∈ A) ∧
           EuclideanGeometry.triangle_area (t.points 0) (t.points 1) (t.points 2) = 1))
    ↔ answer(sorry) := by
  sorry
