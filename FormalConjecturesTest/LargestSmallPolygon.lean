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

import FormalConjectures.Paper.LargestSmallPolygon

/-!
# Boundary checks for maximum-area small polygons

These checks use complete proofs and do not use the unproved problem statements.
-/

open scoped EuclideanGeometry

namespace LargestSmallPolygonTest

open LargestSmallPolygon WithLp

/-- The domain restriction excludes every order below three. -/
theorem no_admissible_below_three {n : ℕ} (hn : n < 3) (p : Polygon ℝ² n) :
    ¬ IsAdmissible p := by
  intro hp
  exact (Nat.not_le_of_lt hn) hp.1.1

/-- A repeated vertex cannot be counted as a second genuine corner. -/
theorem no_repeated_vertex {n : ℕ} (p : Polygon ℝ² n) (i j : Fin n)
    (hij : i ≠ j) (hp : p i = p j) : ¬ IsAdmissible p := by
  intro h
  exact hij (h.1.2.1 hp)

/-- A unit diagonal has squared Euclidean length two, ruling out the sup-norm metric. -/
theorem diagonal_dist_sq :
    dist (toLp 2 ![(0 : ℝ), 0]) (toLp 2 ![(1 : ℝ), 1]) ^ 2 = 2 := by
  norm_num [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]

/-- Reversing a triangle's orientation preserves its unoriented area. -/
theorem triangle_area_both_orientations :
    let p : Polygon ℝ² 3 :=
      ⟨![toLp 2 ![0, 0], toLp 2 ![1 / 2, 0], toLp 2 ![0, 1 / 2]]⟩
    let q : Polygon ℝ² 3 :=
      ⟨![toLp 2 ![0, 0], toLp 2 ![0, 1 / 2], toLp 2 ![1 / 2, 0]]⟩
    p.area = 1 / 8 ∧ q.area = 1 / 8 := by
  norm_num [Polygon.area, Polygon.signedArea, Fin.sum_univ_succ, Fin.add_def]

/-- Distinct vertices alone do not define a simple polygon: changing the boundary
order of the square to a bow tie changes its shoelace area. -/
theorem square_and_crossed_order_areas :
    let p : Polygon ℝ² 4 :=
      ⟨![toLp 2 ![0, 0], toLp 2 ![1 / 2, 0],
        toLp 2 ![1 / 2, 1 / 2], toLp 2 ![0, 1 / 2]]⟩
    let q : Polygon ℝ² 4 :=
      ⟨![toLp 2 ![0, 0], toLp 2 ![1 / 2, 1 / 2],
        toLp 2 ![0, 1 / 2], toLp 2 ![1 / 2, 0]]⟩
    p.area = 1 / 4 ∧ q.area = 0 := by
  norm_num [Polygon.area, Polygon.signedArea, Fin.sum_univ_succ, Fin.add_def]

/-- A uniqueness assertion supplies an actual admissible maximizer. -/
theorem uniqueness_implies_existence {n : ℕ} (h : HasUniqueMaximizer n) :
    ∃ p : Polygon ℝ² n, IsAdmissible p := by
  obtain ⟨p, hp, _⟩ := h
  exact ⟨p, hp.1⟩

end LargestSmallPolygonTest
