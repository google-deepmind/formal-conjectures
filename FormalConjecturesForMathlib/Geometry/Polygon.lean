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

public import Mathlib.Geometry.Polygon.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Simple planar polygons and area

The area is the absolute value of the shoelace sum. For a simple polygon it is
the ordinary area of the bounded polygonal region. The convex-hull area is a
separate definition; no equality with the shoelace area is built into either one.

`IsSimple` requires genuine corners and excludes self-intersections.
`Congruent` compares boundaries under arbitrary Euclidean isometries, including
reflections, and does not depend on a choice of vertex labels.
-/

@[expose] public section

open Set
open scoped BigOperators

namespace Polygon

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

variable {n : ℕ}

/-- A simple polygon with at least three distinct genuine vertices.
Distinct edges meet only at endpoints that they share. Three consecutive
vertices are affinely independent, so straight angles are excluded. -/
def IsSimple (p : Polygon ℝ² n) : Prop :=
  3 ≤ n ∧ Function.Injective p.vertices ∧
    (∀ i, AffineIndependent ℝ
      ![p i, p (finRotate n i), p (finRotate n (finRotate n i))]) ∧
    ∀ i j, i ≠ j →
      p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
        ({p i, p (finRotate n i)} ∩ {p j, p (finRotate n j)})

/-- The oriented area given by the shoelace formula in standard orthonormal coordinates. -/
noncomputable def signedArea (p : Polygon ℝ² n) : ℝ :=
  (∑ i : Fin n, (p i 0 * p (finRotate n i) 1 - p i 1 * p (finRotate n i) 0)) / 2

/-- The unoriented shoelace area. It is the usual area when the polygon is simple. -/
noncomputable def area (p : Polygon ℝ² n) : ℝ := |p.signedArea|

/-- The diameter of the vertex set in the Euclidean metric. -/
noncomputable def diameter (p : Polygon ℝ² n) : ℝ :=
  Metric.diam (Set.range p.vertices)

/-- The convex hull of all vertices; repeated or nonextreme vertices are allowed. -/
def hull (p : Polygon ℝ² n) : Set ℝ² := convexHull ℝ (Set.range p.vertices)

/-- Lebesgue area of the convex hull. A finite planar hull is compact and has finite measure. -/
noncomputable def hullArea (p : Polygon ℝ² n) : ℝ :=
  (MeasureTheory.volume p.hull).toReal

/-- Congruence of polygonal boundaries, allowing translations, rotations and reflections. -/
def Congruent {m : ℕ} (p : Polygon ℝ² n) (q : Polygon ℝ² m) : Prop :=
  ∃ e : ℝ² ≃ᵢ ℝ², e '' p.boundary ℝ = q.boundary ℝ

theorem area_nonneg (p : Polygon ℝ² n) : 0 ≤ p.area := abs_nonneg _

/-- A finite hull has finite volume, so taking its real-valued area loses no information. -/
theorem hull_volume_lt_top (p : Polygon ℝ² n) : MeasureTheory.volume p.hull < ⊤ :=
  ((Set.finite_range p.vertices).isCompact_convexHull ℝ).measure_lt_top

/-- For a finite vertex set, the diameter bound is equivalent to the pairwise distance bound. -/
theorem diameter_le_one_iff (p : Polygon ℝ² n) :
    p.diameter ≤ 1 ↔ ∀ i j, dist (p i) (p j) ≤ 1 := by
  constructor
  · intro h i j
    exact (Metric.dist_le_diam_of_mem (Set.finite_range p.vertices).isBounded
      (Set.mem_range_self i) (Set.mem_range_self j)).trans h
  · intro h
    apply Metric.diam_le_of_forall_dist_le zero_le_one
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact h i j

theorem Congruent.refl (p : Polygon ℝ² n) : p.Congruent p := by
  exact ⟨IsometryEquiv.refl _, Set.image_id _⟩

end Polygon
