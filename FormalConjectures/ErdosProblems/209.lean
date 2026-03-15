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

Must every finite collection of $d \geq 4$ non-parallel lines in $\mathbb{R}^2$, with no point
having $4$ or more lines passing through it, contain a Gallai triangle (three lines whose three
pairwise intersection points are each ordinary)?

Disproved by Füredi–Palásti [FuPa84] for $d$ not divisible by $9$, and by Escudero [Es16] for
all $d \geq 4$. See also Problem 960.

*Reference:* [erdosproblems.com/209](https://www.erdosproblems.com/209)

[Er84] Erdős, P., _Some old and new problems on combinatorial geometry_, 1984.

[ErPu95b] Erdős, P. and Purdy, G., _Extremal problems in combinatorial geometry_.
Handbook of Combinatorics (1995).

[FuPa84] Füredi, Z. and Palásti, I., _Arrangements of lines with a large number of triangles_.
Proc. Amer. Math. Soc. **92** (1984), 561–566.

[Es16] Escudero, J. G., _Gallai triangles in configurations of lines in the projective plane_.
C. R. Math. Acad. Sci. Paris **354** (2016), 551–554.
-/

open Classical

namespace Erdos209

/-- Points in the Euclidean plane $\mathbb{R}^2$. -/
abbrev Point2 := EuclideanSpace ℝ (Fin 2)

/-- An affine subspace of $\mathbb{R}^2$ is a line if it has dimension $1$. -/
noncomputable def IsLine (L : AffineSubspace ℝ Point2) : Prop :=
  Module.finrank ℝ L.direction = 1

/-- Two affine subspaces are parallel if they have the same direction. -/
def AreParallel (L₁ L₂ : AffineSubspace ℝ Point2) : Prop :=
  L₁.direction = L₂.direction

/-- The number of lines from $A$ passing through a point $p$. -/
noncomputable def pointMultiplicity (A : Finset (AffineSubspace ℝ Point2)) (p : Point2) : ℕ :=
  (A.filter (fun L => p ∈ L)).card

/-- A point is ordinary if exactly $2$ lines from $A$ pass through it. -/
noncomputable def IsOrdinaryPoint (A : Finset (AffineSubspace ℝ Point2)) (p : Point2) : Prop :=
  pointMultiplicity A p = 2

/-- A Gallai (ordinary) triangle: three lines forming a triangle with
all three vertices being ordinary points. -/
noncomputable def HasGallaiTriangle (A : Finset (AffineSubspace ℝ Point2)) : Prop :=
  ∃ L₁ ∈ A, ∃ L₂ ∈ A, ∃ L₃ ∈ A,
    L₁ ≠ L₂ ∧ L₂ ≠ L₃ ∧ L₁ ≠ L₃ ∧
    ∃ p₁₂ p₂₃ p₁₃ : Point2,
      p₁₂ ∈ L₁ ∧ p₁₂ ∈ L₂ ∧
      p₂₃ ∈ L₂ ∧ p₂₃ ∈ L₃ ∧
      p₁₃ ∈ L₁ ∧ p₁₃ ∈ L₃ ∧
      p₁₂ ≠ p₂₃ ∧ p₂₃ ≠ p₁₃ ∧ p₁₂ ≠ p₁₃ ∧
      IsOrdinaryPoint A p₁₂ ∧ IsOrdinaryPoint A p₂₃ ∧ IsOrdinaryPoint A p₁₃

/--
Must every finite collection of $d \geq 4$ non-parallel lines in $\mathbb{R}^2$, with no point
having $4$ or more lines passing through it, contain a Gallai triangle (three lines whose three
pairwise intersection points are each ordinary)?

Disproved by Füredi–Palásti for $d$ not divisible by $9$, and by Escudero for all $d \geq 4$.
-/
@[category research solved, AMS 5 52]
theorem erdos_209 : answer(False) ↔
    ∀ d : ℕ, d ≥ 4 →
      ∀ A : Finset (AffineSubspace ℝ Point2),
        A.card = d →
        (∀ L ∈ A, IsLine L) →
        (∀ L₁ ∈ A, ∀ L₂ ∈ A, L₁ ≠ L₂ → ¬AreParallel L₁ L₂) →
        (∀ p : Point2, pointMultiplicity A p ≤ 3) →
        HasGallaiTriangle A := by
  sorry

/--
Stronger disproof due to Escudero [Es16]: for *every* $d \geq 4$, there exists a line
arrangement of $d$ non-parallel lines with no point of multiplicity $\geq 4$ and no Gallai
triangle. This is stronger than the main `erdos_209` statement, which only asserts the existence
of *some* such $d$.
-/
@[category research solved, AMS 5 52]
theorem erdos_209_strong : ∀ d : ℕ, d ≥ 4 →
    ∃ A : Finset (AffineSubspace ℝ Point2),
      A.card = d ∧
      (∀ L ∈ A, IsLine L) ∧
      (∀ L₁ ∈ A, ∀ L₂ ∈ A, L₁ ≠ L₂ → ¬AreParallel L₁ L₂) ∧
      (∀ p : Point2, pointMultiplicity A p ≤ 3) ∧
      ¬HasGallaiTriangle A := by
  sorry

/--
Füredi–Palásti partial result [FuPa84]: for $d \geq 4$ with $d$ not divisible by $9$, there
exists a line arrangement of $d$ non-parallel lines with no point of multiplicity $\geq 4$ and
no Gallai triangle.
-/
@[category research solved, AMS 5 52]
theorem erdos_209_furedi_palasti (d : ℕ) (hd : d ≥ 4) (h9 : ¬(9 ∣ d)) :
    ∃ A : Finset (AffineSubspace ℝ Point2),
      A.card = d ∧
      (∀ L ∈ A, IsLine L) ∧
      (∀ L₁ ∈ A, ∀ L₂ ∈ A, L₁ ≠ L₂ → ¬AreParallel L₁ L₂) ∧
      (∀ p : Point2, pointMultiplicity A p ≤ 3) ∧
      ¬HasGallaiTriangle A := by
  sorry

end Erdos209
