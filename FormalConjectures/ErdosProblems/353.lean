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

[Ko23] Kovač, V., _Coloring and density theorems for configurations of a given volume_.
arXiv:2309.09973 (2023).

[Ko25] Koizumi, S., _Isosceles trapezoids of unit area with vertices in sets of infinite
planar measure_. arXiv:2501.01914 (2025).

[KoPr24] Kovač, V. and Predojević, B., _Polygons of unit area with vertices in sets of
infinite planar measure_. arXiv:2412.11725 (2024).
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
shoelace formula: $\frac{1}{2} |x_1 y_2 - x_2 y_1 + x_2 y_3 - x_3 y_2
+ x_3 y_4 - x_4 y_3 + x_4 y_1 - x_1 y_4|$. -/
noncomputable def quadArea (p₁ p₂ p₃ p₄ : ℝ × ℝ) : ℝ :=
  |(p₁.1 * p₂.2 - p₂.1 * p₁.2) + (p₂.1 * p₃.2 - p₃.1 * p₂.2) +
   (p₃.1 * p₄.2 - p₄.1 * p₃.2) + (p₄.1 * p₁.2 - p₁.1 * p₄.2)| / 2

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
The side from $p_1$ to $p_2$ is parallel to the side from $p_4$ to $p_3$, and
$p_1 p_4$, $p_2 p_3$ are the equal legs. -/
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

/-- Four points (in order) form a trapezoid: exactly one pair of parallel opposite sides.
The side from $p_1$ to $p_2$ is parallel to the side from $p_4$ to $p_3$, and the
legs $p_1 p_4$, $p_2 p_3$ are not parallel. -/
def IsTrapezoid (p₁ p₂ p₃ p₄ : ℝ × ℝ) : Prop :=
  p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₁ ≠ p₄ ∧ p₂ ≠ p₃ ∧ p₂ ≠ p₄ ∧ p₃ ≠ p₄ ∧
  Parallel (p₂.1 - p₁.1, p₂.2 - p₁.2) (p₃.1 - p₄.1, p₃.2 - p₄.2) ∧
  ¬ Parallel (p₄.1 - p₁.1, p₄.2 - p₁.2) (p₃.1 - p₂.1, p₃.2 - p₂.2)

/-- Four points form a parallelogram: both pairs of opposite sides are parallel. -/
def IsParallelogram (p₁ p₂ p₃ p₄ : ℝ × ℝ) : Prop :=
  p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₁ ≠ p₄ ∧ p₂ ≠ p₃ ∧ p₂ ≠ p₄ ∧ p₃ ≠ p₄ ∧
  Parallel (p₂.1 - p₁.1, p₂.2 - p₁.2) (p₃.1 - p₄.1, p₃.2 - p₄.2) ∧
  Parallel (p₄.1 - p₁.1, p₄.2 - p₁.2) (p₃.1 - p₂.1, p₃.2 - p₂.2)

/--
Erdős Problem 353, Variant (general trapezoid) [Er83d]:

Must a measurable set $A \subseteq \mathbb{R}^2$ with infinite measure contain the vertices of
a (not necessarily isosceles) trapezoid of area $1$?

Erdős and Mauldin claim the result holds for general trapezoids.
-/
@[category research solved, AMS 28 52]
theorem erdos_353.variants.trapezoid : answer(True) ↔
    ∀ (A : Set (ℝ × ℝ)), MeasurableSet A → volume A = ⊤ →
    ∃ p₁ p₂ p₃ p₄ : ℝ × ℝ,
      p₁ ∈ A ∧ p₂ ∈ A ∧ p₃ ∈ A ∧ p₄ ∈ A ∧
      IsTrapezoid p₁ p₂ p₃ p₄ ∧
      quadArea p₁ p₂ p₃ p₄ = 1 := by
  sorry

/--
Erdős Problem 353, Variant (parallelogram counterexample) [Ko23]:

There exists a measurable set $A \subseteq \mathbb{R}^2$ with infinite measure such that $A$
does not contain the vertices of any parallelogram of area $1$.

Kovač [Ko23] constructed such a counterexample, showing the result fails for parallelograms.
-/
@[category research solved, AMS 28 52]
theorem erdos_353.variants.parallelogram_counterexample : answer(True) ↔
    ∃ (A : Set (ℝ × ℝ)), MeasurableSet A ∧ volume A = ⊤ ∧
    ∀ p₁ p₂ p₃ p₄ : ℝ × ℝ,
      p₁ ∈ A → p₂ ∈ A → p₃ ∈ A → p₄ ∈ A →
      IsParallelogram p₁ p₂ p₃ p₄ →
      quadArea p₁ p₂ p₃ p₄ ≠ 1 := by
  sorry

/--
Erdős Problem 353, Variant (congruent-sided polygon counterexample) [KoPr24]:

There exists a measurable set $A \subseteq \mathbb{R}^2$ with infinite measure such that
every convex polygon with congruent sides and all vertices in $A$ has area less than $1$.

Proved by Kovač and Predojević [KoPr24].
-/
@[category research solved, AMS 28 52]
theorem erdos_353.variants.congruent_sided_polygon_counterexample : answer(True) ↔
    ∃ (A : Set (ℝ × ℝ)), MeasurableSet A ∧ volume A = ⊤ ∧
    ∀ (n : ℕ) (pts : Fin (n + 3) → ℝ × ℝ) (s : ℝ),
      (∀ i, pts i ∈ A) →
      (∀ i : Fin (n + 3), sqDist (pts i) (pts ⟨(i.val + 1) % (n + 3), Nat.mod_lt _ (by omega)⟩) = s) →
      Convex ℝ (Set.range pts) →
      ∑ i : Fin (n + 1),
        triangleArea (pts ⟨0, by omega⟩) (pts ⟨i.val + 1, by omega⟩)
          (pts ⟨i.val + 2, by omega⟩) < 1 := by
  sorry

end Erdos353
