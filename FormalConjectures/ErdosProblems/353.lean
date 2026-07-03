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
# Erdős Problem 353

*References:*
- [erdosproblems.com/353](https://www.erdosproblems.com/353)
- [Ko23] Kovač, V., *Coloring and density theorems for configurations of a given volume*.
  arXiv:2309.09973 (2023).
- [KoPr24] Kovač, V. and B. Predojević, *Polygons of unit area with vertices in sets of infinite
  planar measure*. arXiv:2412.11725 (2024).
- [Ko25] J. Koizumi, *Isosceles trapezoids of unit area with vertices in sets of infinite planar
  measure*. arXiv:2501.01914 (2025).
-/

open Affine EuclideanGeometry MeasureTheory

open scoped Real

namespace Erdos353

/--
`a b c d` are the vertices, in counter-clockwise order, of an isosceles trapezoid:
they are in strictly convex position, the side `ab` is parallel to the side `cd`
(the two bases), and the diagonals `ac` and `bd` have equal length. One pair of
parallel sides together with equal diagonals is the classical characterization of
an isosceles trapezoid; in particular it rules out non-rectangular parallelograms.
-/
def IsIsoscelesTrapezoid (a b c d : ℝ²) : Prop :=
  IsCcwConvexPolygon ![a, b, c, d] ∧
  line[ℝ, a, b] ∥ line[ℝ, c, d] ∧
  dist a c = dist b d

/--
Let $A\subseteq \mathbb{R}^2$ be a measurable set with infinite measure. Must $A$ contain the
vertices of an isosceles trapezoid of area $1$? What about an isosceles triangle, or a
right-angled triangle, or a cyclic quadrilateral, or a convex polygon with congruent sides?

Koizumi [Ko25] has resolved this question, proving that any set with infinite measure must
contain the vertices of an isosceles trapezoid, an isosceles triangle, and a right-angled
triangle, all of area $1$.

This statement formalizes the leading question, for isosceles trapezoids; the remaining
configurations are given as variants below. The area of a polygon is taken to be the Lebesgue
measure of the convex hull of its vertices.
-/
@[category research solved, AMS 28 51]
theorem erdos_353 : answer(True) ↔
    ∀ A : Set ℝ², MeasurableSet A → volume A = ⊤ →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ d ∈ A,
        IsIsoscelesTrapezoid a b c d ∧
        volume (convexHull ℝ {a, b, c, d}) = 1 := by
  sorry

/--
Every measurable $A\subseteq \mathbb{R}^2$ with infinite measure contains the vertices of an
isosceles triangle of area $1$.

Koizumi [Ko25] has resolved this question, proving that any set with infinite measure must
contain the vertices of an isosceles trapezoid, an isosceles triangle, and a right-angled
triangle, all of area $1$.

Note the area condition forces `a`, `b`, `c` to be affinely independent, so no separate
non-degeneracy hypothesis is needed.
-/
@[category research solved, AMS 28 51]
theorem erdos_353.variants.isosceles_triangle :
    ∀ A : Set ℝ², MeasurableSet A → volume A = ⊤ →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
        (dist a b = dist a c ∨ dist b a = dist b c ∨ dist c a = dist c b) ∧
        volume (convexHull ℝ {a, b, c}) = 1 := by
  sorry

/--
Every measurable $A\subseteq \mathbb{R}^2$ with infinite measure contains the vertices of a
right-angled triangle of area $1$.

Koizumi [Ko25] has resolved this question, proving that any set with infinite measure must
contain the vertices of an isosceles trapezoid, an isosceles triangle, and a right-angled
triangle, all of area $1$.

Note the area condition forces `a`, `b`, `c` to be affinely independent, so no separate
non-degeneracy hypothesis is needed.
-/
@[category research solved, AMS 28 51]
theorem erdos_353.variants.right_angled_triangle :
    ∀ A : Set ℝ², MeasurableSet A → volume A = ⊤ →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
        (∠ b a c = π / 2 ∨ ∠ a b c = π / 2 ∨ ∠ b c a = π / 2) ∧
        volume (convexHull ℝ {a, b, c}) = 1 := by
  sorry

/--
Every measurable $A\subseteq \mathbb{R}^2$ with infinite measure contains the vertices of a
cyclic quadrilateral of area $1$.

Kovač and Predojević [KoPr24] have proved that this is true for cyclic quadrilaterals - that
is, every set with infinite measure contains four distinct points on a circle such that the
quadrilateral determined by these four points has area $1$. The quadrilateral determined by
four distinct concyclic points is their convex hull.
-/
@[category research solved, AMS 28 51]
theorem erdos_353.variants.cyclic_quadrilateral :
    ∀ A : Set ℝ², MeasurableSet A → volume A = ⊤ →
      ∃ Q : Set ℝ², Q ⊆ A ∧ Q.ncard = 4 ∧ Cospherical Q ∧
        volume (convexHull ℝ Q) = 1 := by
  sorry

/--
The answer is negative for convex polygons with congruent sides: Kovač and Predojević
[KoPr24] prove that there exists a set of infinite measure such that every convex polygon
with congruent sides and all vertices in the set has area $<1$.
-/
@[category research solved, AMS 28 51]
theorem erdos_353.variants.congruent_sides :
    ∃ A : Set ℝ², MeasurableSet A ∧ volume A = ⊤ ∧
      ∀ (n : ℕ) (v : Fin (n + 3) → ℝ²),
        IsCcwConvexPolygon v → (∀ i, v i ∈ A) →
        (∀ i, dist (v i) (v (i + 1)) = dist (v 0) (v 1)) →
        volume (convexHull ℝ (Set.range v)) < 1 := by
  sorry

end Erdos353
