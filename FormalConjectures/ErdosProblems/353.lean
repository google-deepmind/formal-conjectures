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

*Reference:* [erdosproblems.com/353](https://www.erdosproblems.com/353)

Erdős asked whether every measurable subset of $\mathbb{R}^2$ with infinite Lebesgue measure
must contain the vertices of an isosceles trapezoid of area $1$, and similarly for isosceles
triangles, right-angled triangles, and cyclic quadrilaterals of area $1$.

[Er83d] Erdős, P., _Problems and results on combinatorial geometry_.

[Ko25] Koizumi, S., _On geometric configurations in measurable sets of infinite measure_.

[KoPr24] Kovač, V. and Predojević, B., _Cyclic quadrilaterals in measurable sets_.
-/

open MeasureTheory

namespace Erdos353

/-- Squared Euclidean distance between two points in $\mathbb{R}^2$. -/
noncomputable def sqDist (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Area of a triangle with vertices $p_1$, $p_2$, $p_3$ via the cross product formula. -/
noncomputable def triangleArea (p₁ p₂ p₃ : ℝ × ℝ) : ℝ :=
  |(p₂.1 - p₁.1) * (p₃.2 - p₁.2) - (p₃.1 - p₁.1) * (p₂.2 - p₁.2)| / 2

/-- Area of a quadrilateral with consecutive vertices $p_1$, $p_2$, $p_3$, $p_4$ via the
shoelace formula. -/
noncomputable def quadArea (p₁ p₂ p₃ p₄ : ℝ × ℝ) : ℝ :=
  |(p₁.1 * p₂.2 - p₂.1 * p₁.2 + p₂.1 * p₃.2 - p₃.1 * p₂.2 +
    p₃.1 * p₄.2 - p₄.1 * p₃.2 + p₄.1 * p₁.2 - p₁.1 * p₄.2)| / 2

/-- Two vectors in $\mathbb{R}^2$ are parallel (cross product is zero). -/
def Parallel (v w : ℝ × ℝ) : Prop :=
  v.1 * w.2 = v.2 * w.1

/-- Three points form an isosceles triangle: all distinct with at least two sides
of equal length. -/
def IsIsoscelesTriangle (p₁ p₂ p₃ : ℝ × ℝ) : Prop :=
  p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ ∧
  (sqDist p₁ p₂ = sqDist p₁ p₃ ∨
   sqDist p₁ p₂ = sqDist p₂ p₃ ∨
   sqDist p₁ p₃ = sqDist p₂ p₃)

/-- Three points form a right-angled triangle: all distinct with one angle equal
to $90°$ (dot product of adjacent edges is zero at some vertex). -/
def IsRightTriangle (p₁ p₂ p₃ : ℝ × ℝ) : Prop :=
  p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ ∧
  ((p₂.1 - p₁.1) * (p₃.1 - p₁.1) + (p₂.2 - p₁.2) * (p₃.2 - p₁.2) = 0 ∨
   (p₁.1 - p₂.1) * (p₃.1 - p₂.1) + (p₁.2 - p₂.2) * (p₃.2 - p₂.2) = 0 ∨
   (p₁.1 - p₃.1) * (p₂.1 - p₃.1) + (p₁.2 - p₃.2) * (p₂.2 - p₃.2) = 0)

/-- Four points (in order) form an isosceles trapezoid: exactly one pair of
parallel opposite sides, with the non-parallel sides (legs) of equal length.
Here $p_1 p_2 \parallel p_4 p_3$ are the parallel sides and $p_1 p_4$, $p_2 p_3$
are the equal legs. -/
def IsIsoscelesTrapezoid (p₁ p₂ p₃ p₄ : ℝ × ℝ) : Prop :=
  p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₁ ≠ p₄ ∧ p₂ ≠ p₃ ∧ p₂ ≠ p₄ ∧ p₃ ≠ p₄ ∧
  Parallel (p₂.1 - p₁.1, p₂.2 - p₁.2) (p₃.1 - p₄.1, p₃.2 - p₄.2) ∧
  sqDist p₁ p₄ = sqDist p₂ p₃ ∧
  ¬ Parallel (p₄.1 - p₁.1, p₄.2 - p₁.2) (p₃.1 - p₂.1, p₃.2 - p₂.2)

/-- Four distinct points lie on a common circle. -/
def IsCyclicQuadrilateral (p₁ p₂ p₃ p₄ : ℝ × ℝ) : Prop :=
  p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₁ ≠ p₄ ∧ p₂ ≠ p₃ ∧ p₂ ≠ p₄ ∧ p₃ ≠ p₄ ∧
  ∃ (c : ℝ × ℝ) (r_sq : ℝ), 0 < r_sq ∧
    sqDist c p₁ = r_sq ∧ sqDist c p₂ = r_sq ∧
    sqDist c p₃ = r_sq ∧ sqDist c p₄ = r_sq

/--
Erdős Problem 353, Part 1 [Er83d]:

Let $A \subseteq \mathbb{R}^2$ be a measurable set with infinite Lebesgue measure. Must $A$
contain the vertices of an isosceles trapezoid of area $1$?

Proved by Koizumi [Ko25].
-/
@[category research solved, AMS 28 52]
theorem erdos_353 : answer(True) ↔
    ∀ (A : Set (ℝ × ℝ)), MeasurableSet A → volume A = ⊤ →
    ∃ p₁ p₂ p₃ p₄ : ℝ × ℝ,
      p₁ ∈ A ∧ p₂ ∈ A ∧ p₃ ∈ A ∧ p₄ ∈ A ∧
      IsIsoscelesTrapezoid p₁ p₂ p₃ p₄ ∧
      quadArea p₁ p₂ p₃ p₄ = 1 := by
  sorry

/--
Erdős Problem 353, Part 2 [Er83d]:

Must a measurable set $A \subseteq \mathbb{R}^2$ with infinite measure contain the vertices of
an isosceles triangle of area $1$?

Proved by Koizumi [Ko25].
-/
@[category research solved, AMS 28 52]
theorem erdos_353.variants.isosceles_triangle : answer(True) ↔
    ∀ (A : Set (ℝ × ℝ)), MeasurableSet A → volume A = ⊤ →
    ∃ p₁ p₂ p₃ : ℝ × ℝ,
      p₁ ∈ A ∧ p₂ ∈ A ∧ p₃ ∈ A ∧
      IsIsoscelesTriangle p₁ p₂ p₃ ∧
      triangleArea p₁ p₂ p₃ = 1 := by
  sorry

/--
Erdős Problem 353, Part 3 [Er83d]:

Must a measurable set $A \subseteq \mathbb{R}^2$ with infinite measure contain the vertices of
a right-angled triangle of area $1$?

Proved by Koizumi [Ko25].
-/
@[category research solved, AMS 28 52]
theorem erdos_353.variants.right_triangle : answer(True) ↔
    ∀ (A : Set (ℝ × ℝ)), MeasurableSet A → volume A = ⊤ →
    ∃ p₁ p₂ p₃ : ℝ × ℝ,
      p₁ ∈ A ∧ p₂ ∈ A ∧ p₃ ∈ A ∧
      IsRightTriangle p₁ p₂ p₃ ∧
      triangleArea p₁ p₂ p₃ = 1 := by
  sorry

/--
Erdős Problem 353, Part 4 [Er83d]:

Must a measurable set $A \subseteq \mathbb{R}^2$ with infinite measure contain four distinct
points on a common circle forming a quadrilateral of area $1$?

Proved by Kovač and Predojević [KoPr24].
-/
@[category research solved, AMS 28 52]
theorem erdos_353.variants.cyclic_quadrilateral : answer(True) ↔
    ∀ (A : Set (ℝ × ℝ)), MeasurableSet A → volume A = ⊤ →
    ∃ p₁ p₂ p₃ p₄ : ℝ × ℝ,
      p₁ ∈ A ∧ p₂ ∈ A ∧ p₃ ∈ A ∧ p₄ ∈ A ∧
      IsCyclicQuadrilateral p₁ p₂ p₃ p₄ ∧
      quadArea p₁ p₂ p₃ p₄ = 1 := by
  sorry

end Erdos353
