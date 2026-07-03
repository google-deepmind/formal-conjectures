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
# Erdős Problem 209

*References:*
- [erdosproblems.com/209](https://www.erdosproblems.com/209)
- [FuPa84] Füredi, Z. and Palásti, I., *Arrangements of lines with a large number of triangles*.
  Proc. Amer. Math. Soc. (1984), 561-566.
- [Es16] Escudero, Juan García, *Gallai triangles in configurations of lines in the projective
  plane*. C. R. Math. Acad. Sci. Paris (2016), 551-554.
-/

open EuclideanGeometry Affine

namespace Erdos209

/-- A line in the plane: the affine span of two distinct points. -/
def IsLine (L : AffineSubspace ℝ ℝ²) : Prop :=
  ∃ p q : ℝ², p ≠ q ∧ L = affineSpan ℝ {p, q}

/-- The number of lines from `A` that pass through the point `p`. -/
noncomputable def pointMultiplicity (A : Finset (AffineSubspace ℝ ℝ²)) (p : ℝ²) : ℕ :=
  {L ∈ (A : Set (AffineSubspace ℝ ℝ²)) | p ∈ L}.ncard

/--
A *Gallai triangle* (or *ordinary triangle*) in a collection `A` of lines: three lines from `A`
which intersect in three points, and each of these intersection points only intersects two
lines from `A`.
-/
def HasGallaiTriangle (A : Finset (AffineSubspace ℝ ℝ²)) : Prop :=
  ∃ L₁ ∈ A, ∃ L₂ ∈ A, ∃ L₃ ∈ A, L₁ ≠ L₂ ∧ L₂ ≠ L₃ ∧ L₁ ≠ L₃ ∧
    ∃ p₁ p₂ p₃ : ℝ², p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ ∧
      p₁ ∈ L₁ ∧ p₁ ∈ L₂ ∧ p₂ ∈ L₂ ∧ p₂ ∈ L₃ ∧ p₃ ∈ L₃ ∧ p₃ ∈ L₁ ∧
      pointMultiplicity A p₁ = 2 ∧ pointMultiplicity A p₂ = 2 ∧ pointMultiplicity A p₃ = 2

/--
Let $A$ be a finite collection of $d\geq 4$ non-parallel lines in $\mathbb{R}^2$ such that
there are no points where at least four lines from $A$ meet. Must there exist a 'Gallai
triangle' (or 'ordinary triangle'): three lines from $A$ which intersect in three points, and
each of these intersection points only intersects two lines from $A$?

Füredi and Palásti [FuPa84] showed this is false when $d\geq 4$ is not divisible by $9$.
Escudero [Es16] showed this is false for all $d\geq 4$.
-/
@[category research solved, AMS 52]
theorem erdos_209 : answer(False) ↔
    ∀ d : ℕ, 4 ≤ d → ∀ A : Finset (AffineSubspace ℝ ℝ²), A.card = d →
      (∀ L ∈ A, IsLine L) →
      ((A : Set (AffineSubspace ℝ ℝ²)).Pairwise fun L₁ L₂ => ¬ L₁ ∥ L₂) →
      (∀ p : ℝ², pointMultiplicity A p ≤ 3) →
      HasGallaiTriangle A := by
  sorry

end Erdos209
