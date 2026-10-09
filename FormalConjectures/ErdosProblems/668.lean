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
module

public import FormalConjecturesUtil
public import FormalConjectures.ErdosProblems.«90»

/-!
# Erdős Problem 668

*References:*
- [erdosproblems.com/668](https://www.erdosproblems.com/668)
- [A385657](https://oeis.org/A385657)
- [AMP25] B. Alexeev, D. Mixon, and H. Parshall, *The Erdős unit distance problem for small point
  sets*. arXiv:2412.11914 (2025).
- [EHSVZ25] P. Engel, O. Hammond-Lee, Y. Su, D. Varga, and P. Zsámboki, *Diverse beam search to
  find densest-known planar unit distance graphs*. arXiv:2406.15317 (2025).
- [Er97f] Erdős, Paul, *Some unsolved problems*. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1-10.
-/

@[expose] public section

open Filter
open scoped EuclideanGeometry

namespace Erdos668

open Erdos90

/-- Two finite sets of points of the plane are *congruent* if an isometry of the plane maps one
onto the other. -/
def Congruent (A B : Finset ℝ²) : Prop :=
  ∃ f : ℝ² ≃ᵢ ℝ², f '' A = B

/--
Is it true that the number of incongruent sets of $n$ points in $\mathbb{R}^2$ which maximise the
number of unit distances tends to infinity as $n\to\infty$?

The actual maximal number of unit distances is the subject of
[Erdős Problem 90](https://www.erdosproblems.com/90).
-/
@[category research open, AMS 52]
theorem erdos_668.parts.i : answer(sorry) ↔
    ∀ m : ℕ, ∀ᶠ n in atTop, ∃ A : Fin m → Finset ℝ²,
      (∀ i, (A i).card = n ∧ unitDistNum (A i) = maxUnitDistances n) ∧
      ∀ i j, i ≠ j → ¬ Congruent (A i) (A j) := by
  sorry

/--
Is it always $>1$ for $n>3$?

In fact this is $=1$ also for $n=4$, the unique example given by two equilateral triangles joined
by an edge.

Computational evidence of Engel, Hammond-Lee, Su, Varga, and Zsámboki [EHSVZ25] and Alexeev,
Mixon, and Parshall [AMP25] suggests that this count is $=1$ for various other $5\leq n\leq 21$
(although these calculations were checking only up to graph isomorphism, rather than
congruency).
-/
@[category research solved, AMS 52]
theorem erdos_668.parts.ii : answer(False) ↔
    ∀ n : ℕ, 3 < n → ∃ A B : Finset ℝ², A.card = n ∧ B.card = n ∧
      unitDistNum A = maxUnitDistances n ∧ unitDistNum B = maxUnitDistances n ∧
      ¬ Congruent A B := by
  sorry

/--
For $n=4$ there is, up to congruence, exactly one set of points in $\mathbb{R}^2$ which maximises
the number of unit distances: two unit equilateral triangles $abc$ and $bcd$ joined by the edge
$bc$, with $a\neq d$.
-/
@[category research solved, AMS 52]
theorem erdos_668.variants.four_points :
    ∃ a b c d : ℝ², dist a b = 1 ∧ dist a c = 1 ∧ dist b c = 1 ∧ dist b d = 1 ∧ dist c d = 1 ∧
      ({a, b, c, d} : Finset ℝ²).card = 4 ∧
      ∀ B : Finset ℝ², B.card = 4 →
        (unitDistNum B = maxUnitDistances 4 ↔ Congruent {a, b, c, d} B) := by
  sorry

/-- `Erdos668.erdos_668.variants.four_points` settles `Erdos668.erdos_668.parts.ii` at
$n = 4$. -/
@[category test, AMS 52]
theorem erdos_668.variants.four_points_implies_parts_ii :
    type_of% erdos_668.variants.four_points → type_of% erdos_668.parts.ii := by
  rintro ⟨a, b, c, d, -, -, -, -, -, -, h⟩
  refine ⟨False.elim, fun H => ?_⟩
  obtain ⟨A, B, hA, hB, hAm, hBm, hAB⟩ := H 4 (by norm_num)
  obtain ⟨f, hf⟩ := (h A hA).1 hAm
  obtain ⟨g, hg⟩ := (h B hB).1 hBm
  exact hAB ⟨f.symm.trans g, by rw [← hf, ← hg, Set.image_image]; simp⟩

end Erdos668
