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
import FormalConjecturesForMathlib.Geometry.«2d»

/-!
# Erdős Problem 91

*Reference:*
- [Er87b] Erdős, P., Some combinatorial and metric problems in geometry.
  Intuitive geometry (Siófok, 1985) (1987), 167-177.
- [Ko24c] Z. Kovács, A note on Erdős's mysterious remark. arXiv:2412.05190 (2024).
- [erdosproblems.com/91](https://www.erdosproblems.com/91)
-/

open Finset EuclideanGeometry Filter

namespace Erdos91

/-- A set $A$ is 'optimal' if it has $n$ points and achieves the minimum distance count. -/
noncomputable def IsOptimal (A : Finset ℝ²) (n : ℕ) : Prop :=
  A.card = n ∧ distinctDistances A = minimalDistinctDistances n

/-- Two finite sets of points in $\mathbb{R}^2$ are similar if one can be mapped to the other by a
DilationEquiv. -/
def DilationEquivSimilar (A B : Finset ℝ²) : Prop :=
  ∃ f : ℝ² ≃ᵈ ℝ², (f '' A.toSet) = B.toSet

noncomputable def unitSquare : Finset ℝ² := {![0, 0], ![0, 1], ![1, 0], ![1, 1]}

/-- Regular 7-gon with unit side length, touching both axes in the first quadrant. -/
noncomputable def circleSeven : Finset ℝ² :=
  let r := 1 / (2 * Real.sin (Real.pi / 7))
  let cx := r * Real.cos (Real.pi / 7)
  let cy := r * Real.sin (4 * Real.pi / 7)
  (Finset.range 7).image fun k : ℕ =>
    ![r * Real.cos (2 * Real.pi * ↑k / 7) + cx, r * Real.sin (2 * Real.pi * ↑k / 7) + cy]

/-- Wheel graph on 7 vertices (center + regular hexagon) with unit side length,
touching both axes in the first quadrant. -/
noncomputable def wheelSeven : Finset ℝ² :=
  {![1, Real.sqrt 3 / 2],
   ![2, Real.sqrt 3 / 2],
   ![3 / 2, Real.sqrt 3],
   ![1 / 2, Real.sqrt 3],
   ![0, Real.sqrt 3 / 2],
   ![1 / 2, 0],
   ![3 / 2, 0]}

@[category test, AMS 52]
lemma erdos_91.test.unitSquare_optimal : IsOptimal unitSquare 4 := by
  sorry

@[category test, AMS 52]
lemma erdos_91.test.unitSquare_unique_optimal :
    ∀ A : Finset ℝ², IsOptimal A 4 → DilationEquivSimilar A unitSquare := by
  sorry

@[category test, AMS 52]
lemma erdos_91.test.circleSeven_optimal : IsOptimal circleSeven 7 := by
  sorry

@[category test, AMS 52]
lemma erdos_91.test.wheelSeven_optimal : IsOptimal wheelSeven 7 := by
  sorry

@[category test, AMS 52]
lemma erdos_91.test.dissimilar_circleSeven_wheelSeven :
    ¬DilationEquivSimilar circleSeven wheelSeven := by
  sorry

/--
The predicate on $n$ asserting all $A, B\subset \mathbb{R}^2$,
with $\lvert A\rvert=n = \lvert B\rvert$, which minimise the number of distinct points for all sets
with $n$ elements are similar.
-/
def UniqueMinimizer (n : ℕ) : Prop :=
  ∀ (A B : Finset ℝ²),  A.card = n → B.card = n →
  minimalDistinctDistances n = distinctDistances A →
  minimalDistinctDistances n = distinctDistances B → DilationEquivSimilar A B

/--
Suppose $A\subset \mathbb{R}^2$ has $\lvert A\rvert=n$ and minimises the number of distinct
distances between points in $A$. Prove that for large $n$ there are at least two
(and probably many) such $A$ which are non-similar.
-/
@[category research open, AMS 52]
theorem erdos_91 :
    (∀ᶠ n : ℕ in atTop, ¬ UniqueMinimizer n) ↔ answer(sorry) := by
  sorry


/--
For $n = 3$ the equilateral triangle is the only such set.
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.three : UniqueMinimizer 3 := by
  sorry


/--
For $n=4$ the square or two equilateral triangles sharing an edge give two
non-similar examples.
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.four : ¬ UniqueMinimizer 4 := by
  sorry


/--
For $n = 5$ the regular pentagon is the unique such set (which has two distinct distances).
Erdős mysteriously remarks in [Er90] this was proved by 'a colleague'. (In [Er87b] this is
described as 'a colleague from Zagreb (unfortunately I do not have his letter)'.)
A published proof of this fact is provided by Kovács [Ko24c].
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.five : UniqueMinimizer 5 := by
  sorry

/--
In [Er87b] on p.171 Erdős says that there are at least two non-similar examples for $n = 6$.
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.six: ¬ UniqueMinimizer 6 := by
  sorry


/--
In [Er87b] on p.171 Erdős says that there are at least two non-similar examples for $n = 7$.
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.seven: ¬ UniqueMinimizer 7 := by
  sorry


/--
In [Er87b] on p.171 Erdős says that there are at least two non-similar examples for $n = 8$.
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.eight: ¬ UniqueMinimizer 8 := by
  sorry


/--
In [Er87b] on p.171 Erdős says that there are at least two non-similar examples for $n = 9$.
-/
@[category research solved, AMS 52]
theorem erdos_91.variants.nine: ¬ UniqueMinimizer 9 := by
  sorry

end Erdos91
