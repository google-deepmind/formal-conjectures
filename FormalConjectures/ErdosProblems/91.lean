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
# Erdős Problem 91

*Reference:*
- [erdosproblems.com/91](https://www.erdosproblems.com/91)
-/

open Finset EuclideanGeometry

namespace Erdos91

notation "E²" => EuclideanSpace ℝ (Fin 2)

/-- The set of distinct pairwise distances in a finite point set. -/
noncomputable def distinctDistances (A : Finset E²) : ℕ :=
  (A.offDiag.image fun p => dist p.1 p.2).card

/-- The minimum number of distinct distances possible for any set of n points in $\mathbb R^2$. -/
noncomputable def minDistanceCount (n : ℕ) : ℕ :=
  sInf { k | ∃ (A : Finset E²), A.card = n ∧ distinctDistances A = k }

/-- A set $A$ is 'optimal' if it has $n$ points and achieves the minimum distance count. -/
noncomputable def IsOptimal (A : Finset E²) (n : ℕ) : Prop :=
  A.card = n ∧ distinctDistances A = minDistanceCount n

/-- Two sets are similar if one can be mapped to the other by scaling, rotation/reflection,
and translation. -/
def IsSimilar (A B : Finset E²) : Prop :=
  ∃ (c : ℝ) (f : E² ≃ₗᵢ[ℝ] E²) (v : E²), 0 < c ∧
    B = A.image (fun x => c • (f x) + v)

noncomputable def unitSquare : Finset E² := {!₂[0, 0], !₂[0, 1], !₂[1, 0], !₂[1, 1]}

/-- Regular 7-gon with unit side length, touching both axes in the first quadrant. -/
noncomputable def circleSeven : Finset E² :=
  let r := 1 / (2 * Real.sin (Real.pi / 7))
  let cx := r * Real.cos (Real.pi / 7)
  let cy := r * Real.sin (4 * Real.pi / 7)
  (Finset.range 7).image fun k : ℕ =>
    !₂[r * Real.cos (2 * Real.pi * ↑k / 7) + cx, r * Real.sin (2 * Real.pi * ↑k / 7) + cy]

/-- Wheel graph on 7 vertices (center + regular hexagon) with unit side length,
touching both axes in the first quadrant. -/
noncomputable def wheelSeven : Finset E² :=
  {!₂[1, Real.sqrt 3 / 2],
   !₂[2, Real.sqrt 3 / 2],
   !₂[3 / 2, Real.sqrt 3],
   !₂[1 / 2, Real.sqrt 3],
   !₂[0, Real.sqrt 3 / 2],
   !₂[1 / 2, 0],
   !₂[3 / 2, 0]}

@[category test, AMS 52]
lemma erdos_91.test.unitSquare_optimal : IsOptimal unitSquare 4 := by
  sorry

@[category test, AMS 52]
lemma erdos_91.test.unitSquare_unique_optimal :
    ∀ A : Finset E², IsOptimal A 4 → IsSimilar A unitSquare := by
  sorry

@[category test, AMS 52]
lemma erdos_91.test.circleSeven_optimal : IsOptimal circleSeven 7 := by
  sorry

@[category test, AMS 52]
lemma erdos_91.test.wheelSeven_optimal : IsOptimal wheelSeven 7 := by
  sorry

@[category test, AMS 52]
lemma erdos_91.test.dissimilar_circleSeven_wheelSeven :
    ¬IsSimilar circleSeven wheelSeven := by
  sorry

/-- Erdős Problem 91: For sufficiently large $n$, there are at least
    two non-similar sets that minimize the number of distinct distances. -/
@[category research open, AMS 52]
theorem erdos_91 :
  ∀ᶠ (n : ℕ) in Filter.atTop,
    ∃ (A B : Finset E²), IsOptimal A n ∧ IsOptimal B n ∧ ¬IsSimilar A B := by
  sorry


end Erdos91
