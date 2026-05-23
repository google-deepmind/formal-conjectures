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
# Erdős Problem 755

*References:*
- [erdosproblems.com/755](https://www.erdosproblems.com/755)
- [ErPu75] Erdős, Paul and Purdy, George, Some extremal problems in geometry. III.
  (1975), 291--308.
- [Er94b] Erdős, Paul, Some problems in number theory, combinatorics and
  combinatorial geometry. Math. Pannon. (1994), 261--269.
- [CDL25b] Clemen, Felix Christian, Dumitrescu, Adrian, and Liu, Dingyuan,
  The number of regular simplices in higher dimensions. arXiv:2507.19841 (2025).

### AI disclosure

Lean 4 code in this file was drafted with assistance from OpenAI Codex.
The mathematical content and references are the author's own work.
-/

open Filter Metric Classical
open scoped EuclideanGeometry Asymptotics

namespace Erdos755

/-- A three-point set whose pairwise distances are all equal to `side`. -/
def IsEquilateralTriangle {d : ℕ} (side : ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  T.card = 3 ∧ ∀ p ∈ T, ∀ q ∈ T, p ≠ q → dist p q = side

/-- A unit equilateral triangle in Euclidean `d`-space. -/
def IsUnitEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  IsEquilateralTriangle 1 T

/-- An equilateral triangle of any positive side length in Euclidean `d`-space. -/
def IsAnySizeEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ side : ℝ, 0 < side ∧ IsEquilateralTriangle side T

/-- Number of unit equilateral triangles spanned by a finite point set. -/
noncomputable def unitEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  ((P.powersetCard 3).filter fun T => IsUnitEquilateralTriangle T).card

/-- Number of equilateral triangles of any positive side length spanned by a finite point set. -/
noncomputable def anySizeEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  ((P.powersetCard 3).filter fun T => IsAnySizeEquilateralTriangle T).card

/-- Maximum number of unit equilateral triangles spanned by `n` points in `ℝ^d`. -/
noncomputable def TUnit (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ unitEquilateralTriangleCount d P = m}

/-- Maximum number of equilateral triangles of any size spanned by `n` points in `ℝ^d`. -/
noncomputable def TAnySize (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ anySizeEquilateralTriangleCount d P = m}

@[category test, AMS 52]
theorem erdos_755.test_dim_one :
    unitEquilateralTriangleCount 1 (∅ : Finset (EuclideanSpace ℝ (Fin 1))) = 0 := by
  simp [unitEquilateralTriangleCount]

/--
**Erdős Problem 755** (solved). Erdős asked whether every `n`-point set in
`ℝ^6` spans at most `(1 / 27 + o(1)) n^3` unit equilateral triangles.

Clemen, Dumitrescu, and Liu [CDL25b] proved the stronger any-size statement
`T_6(n) = (1 / 27 + o(1)) n^3`. The unit-triangle upper bound follows as a
corollary, since unit equilateral triangles are a subset of equilateral
triangles of any positive side length: `T_unit ≤ T_anysize`.
-/
@[category research solved, AMS 52]
theorem erdos_755 :
    answer(True) ↔ ∃ o : ℕ → ℝ,
      o =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
        ∀ᶠ n in atTop,
          (TUnit 6 n : ℝ) ≤ ((1 / 27 : ℝ) + o n) * (n : ℝ) ^ 3 := by
  sorry

/--
Clemen, Dumitrescu, and Liu [CDL25b] proved the stronger version where
equilateral triangles of all positive side lengths are counted.
-/
@[category research solved, AMS 52]
theorem erdos_755.variants.any_size_cdl :
    (fun n : ℕ => (TAnySize 6 n : ℝ)) ~[atTop]
      (fun n : ℕ => (1 / 27 : ℝ) * (n : ℝ) ^ 3) := by
  sorry

end Erdos755
