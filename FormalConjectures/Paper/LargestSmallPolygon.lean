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

import FormalConjecturesUtil

/-!
# Maximum-area small polygons

Determine the largest area of a simple planar polygon with exactly $n \geq 3$
genuine vertices and diameter at most $1$, and characterize the maximizing
polygons up to Euclidean congruence, including reflection.

The value problem, the reduction to convex hulls, and uniqueness of the
maximizing shape are stated separately. Quadrilaterals have infinitely many
noncongruent maximizers. The proposed even-order uniqueness statement starts
at $n = 8$.

References:
* C. Bingane and M. J. Mossinghoff, *Small polygons with large area*,
  Journal of Global Optimization 88 (2024), 1035–1050.
  https://doi.org/10.1007/s10898-023-01329-1
* D. Trela, *Maximum-Area Small Polygons of Even Order* (2026),
  Theorem 1.1 and Section 2. https://arxiv.org/abs/2608.15666
* https://github.com/google-deepmind/formal-conjectures/issues/5303
-/

open scoped EuclideanGeometry

namespace LargestSmallPolygon

/-- A simple small $n$-gon with exactly $n$ distinct genuine corners. -/
def IsAdmissible {n : ℕ} (p : Polygon ℝ² n) : Prop :=
  p.IsSimple ∧ p.diameter ≤ 1

/-- An admissible polygon whose vertices are in convex boundary order. -/
def IsConvexAdmissible {n : ℕ} (p : Polygon ℝ² n) : Prop :=
  IsAdmissible p ∧ EuclideanGeometry.IsConvexPolygon p.vertices

/-- The set of areas attained by simple small $n$-gons. -/
def feasibleAreas (n : ℕ) : Set ℝ :=
  {a | ∃ p : Polygon ℝ² n, IsAdmissible p ∧ p.area = a}

/-- The supremum of the areas of simple small $n$-gons. Statements use $n \geq 3$. -/
noncomputable def maximalArea (n : ℕ) : ℝ := sSup (feasibleAreas n)

/-- The supremum restricted to simple small polygons in convex boundary order. -/
noncomputable def convexMaximalArea (n : ℕ) : ℝ :=
  sSup {a | ∃ p : Polygon ℝ² n, IsConvexAdmissible p ∧ p.area = a}

/-- An $n$-tuple feasible for the convex-hull problem. Its entries need not be
distinct or extreme points; it is not required to trace a simple boundary. -/
def IsHullFeasible {n : ℕ} (p : Polygon ℝ² n) : Prop :=
  ∀ i j, dist (p i) (p j) ≤ 1

/-- The supremum of the convex-hull areas of feasible $n$-tuples. -/
noncomputable def hullMaximalArea (n : ℕ) : ℝ :=
  sSup {a | ∃ p : Polygon ℝ² n, IsHullFeasible p ∧ p.hullArea = a}

/-- A global maximizer among all simple small $n$-gons, including nonconvex competitors. -/
def IsMaximizer {n : ℕ} (p : Polygon ℝ² n) : Prop :=
  IsAdmissible p ∧ ∀ q : Polygon ℝ² n, IsAdmissible q → q.area ≤ p.area

/-- There exists a maximizer and all maximizers are congruent to it.
Existence is included, so this cannot hold vacuously. -/
def HasUniqueMaximizer (n : ℕ) : Prop :=
  ∃ p : Polygon ℝ² n, IsMaximizer p ∧
    ∀ q : Polygon ℝ² n, IsMaximizer q → p.Congruent q

/-- Admissibility implies the pairwise Euclidean distance bound. -/
@[category API, AMS 52]
theorem IsAdmissible.dist_le_one {n : ℕ} {p : Polygon ℝ² n} (hp : IsAdmissible p) :
    ∀ i j, dist (p i) (p j) ≤ 1 :=
  p.diameter_le_one_iff.mp hp.2

/-- For $n \geq 3$, the area set is nonempty and bounded above. -/
@[category textbook, AMS 52]
theorem feasibleAreas_nonempty_bddAbove (n : ℕ) (hn : 3 ≤ n) :
    (feasibleAreas n).Nonempty ∧ BddAbove (feasibleAreas n) := by
  sorry

/-- For $n \geq 3$, the maximum is attained by a polygon in convex boundary order. -/
@[category textbook, AMS 52]
theorem exists_convex_maximizer (n : ℕ) (hn : 3 ≤ n) :
    ∃ p : Polygon ℝ² n, IsConvexAdmissible p ∧ IsMaximizer p ∧
      p.area = maximalArea n := by
  sorry

/-- For $n \geq 3$, the simple-polygon, convex-polygon and finite-hull values agree.
The finite-hull problem allows repeated and nonextreme entries. -/
@[category textbook, AMS 52]
theorem maximalArea_eq_convex_eq_hull (n : ℕ) (hn : 3 ≤ n) :
    maximalArea n = convexMaximalArea n ∧ maximalArea n = hullMaximalArea n := by
  sorry

/-- At a hull maximum with $n \geq 3$, all $n$ entries are distinct extreme points
and the diameter is $1$; see Proposition 2.3 in Trela's preprint. -/
@[category textbook, AMS 52]
theorem hull_maximizer_has_genuine_vertices (n : ℕ) (hn : 3 ≤ n)
    (p : Polygon ℝ² n) (hp : IsHullFeasible p) (ha : p.hullArea = hullMaximalArea n) :
    Function.Injective p.vertices ∧ EuclideanGeometry.ConvexIndep (Set.range p.vertices) ∧
      p.diameter = 1 := by
  sorry

/-- For $n \geq 3$, global maximality is equivalent to attaining the area supremum. -/
@[category textbook, AMS 52]
theorem isMaximizer_iff_area_eq (n : ℕ) (hn : 3 ≤ n) (p : Polygon ℝ² n) :
    IsMaximizer p ↔ IsAdmissible p ∧ p.area = maximalArea n := by
  sorry

/-- Determine the maximal area $A_n$ for every $n \geq 3$.
The answer is a function of the order; its values below $3$ are unconstrained. -/
@[category research open, AMS 52 90]
theorem determine_maximalArea :
    let a : ℕ → ℝ := answer(sorry)
    ∀ n : ℕ, 3 ≤ n → maximalArea n = a n := by
  sorry

/-- For odd $n \geq 3$, Reinhardt's maximal area is
$n\sin(2\pi/n)/(8\cos^2(\pi/(2n)))$; see the review by Bingane and Mossinghoff. -/
@[category research solved, AMS 52]
theorem maximalArea_odd (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    maximalArea n = (n : ℝ) * Real.sin (2 * Real.pi / (n : ℝ)) /
      (8 * Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2) := by
  sorry

/-- The maximal area of a small quadrilateral is $1/2$. -/
@[category textbook, AMS 52]
theorem maximalArea_four : maximalArea 4 = 1 / 2 := by
  sorry

/-- There are infinitely many pairwise noncongruent maximum-area small quadrilaterals. -/
@[category textbook, AMS 52]
theorem quadrilateral_infinitely_many_maximizers :
    ∃ p : ℕ → Polygon ℝ² 4, (∀ i, IsMaximizer (p i)) ∧
      ∀ i j, i ≠ j → ¬ (p i).Congruent (p j) := by
  sorry

/-- The proposed even-order theorem in Trela's preprint: for every even
$n \geq 8$, there is exactly one congruence class of global maximizers. -/
@[category research open, AMS 52 90]
theorem unique_maximizer_even (n : ℕ) (hn : 8 ≤ n) (heven : Even n) :
    HasUniqueMaximizer n := by
  sorry

end LargestSmallPolygon
