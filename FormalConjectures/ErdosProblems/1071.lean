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
# Erdős Problem 1071

*Reference:* [erdosproblems.com/1071](__https://www.erdosproblems.com/1071__)
-/

open Set Metric

namespace Erdos1071

/-- The unit square $[0,1]^2$ in $\mathbb{R}^2$. -/
def unitSquare : Set (ℝ × ℝ) := Icc (0, 0) (1, 1)

/-- A segment with endpoints $p$ and $q$ is a unit segment if the distance between them is 1. -/
def IsUnitSegment (p q : ℝ × ℝ) : Prop := dist p q = 1

/-- Two segments are disjoint if they only intersect at their endpoints (if at all). -/
def SegmentsDisjoint (p1 q1 p2 q2 : ℝ × ℝ) : Prop :=
  (segment ℝ p1 q1 ∩ segment ℝ p2 q2) ⊆ {p1, q1, p2, q2}

/-- A segment is contained in region $R$ if both its endpoints are in $R$. -/
def SegmentInRegion (p q : ℝ × ℝ) (R : Set (ℝ × ℝ)) : Prop :=
  p ∈ R ∧ q ∈ R

/-- A finite set $S$ of unit segments (represented as endpoint pairs) in region $R$ is maximal
    if it is pairwise disjoint and no additional unit segment in $R$ can be added while
    maintaining disjointness. -/
def IsMaximalDisjointUnitSegments (S : Finset ((ℝ × ℝ) × (ℝ × ℝ))) (R : Set (ℝ × ℝ)) : Prop :=
  (∀ seg ∈ S, IsUnitSegment seg.1 seg.2 ∧ SegmentInRegion seg.1 seg.2 R) ∧
  (∀ s1 s2, s1 ∈ S → s2 ∈ S → s1 ≠ s2 → SegmentsDisjoint s1.1 s1.2 s2.1 s2.2) ∧
  (∀ p q, IsUnitSegment p q → SegmentInRegion p q R →
    (∀ seg ∈ S, SegmentsDisjoint p q seg.1 seg.2) → (p, q) ∈ S)

/-- A countable set $S$ of unit segments (represented as endpoint pairs) in region $R$ is maximal
    if it is pairwise disjoint and no additional unit segment in $R$ can be added while
    maintaining disjointness. -/
def IsMaximalDisjointUnitSegmentsCountable (S : Set ((ℝ × ℝ) × (ℝ × ℝ))) (R : Set (ℝ × ℝ)) : Prop :=
  (∀ seg ∈ S, IsUnitSegment seg.1 seg.2 ∧ SegmentInRegion seg.1 seg.2 R) ∧
  (∀ s1 s2, s1 ∈ S → s2 ∈ S → s1 ≠ s2 → SegmentsDisjoint s1.1 s1.2 s2.1 s2.2) ∧
  (∀ p q, IsUnitSegment p q → SegmentInRegion p q R →
    (∀ seg ∈ S, SegmentsDisjoint p q seg.1 seg.2) → (p, q) ∈ S)

/-- Are there a finite set of unit line segments in the unit square, no two of which intersect,
    which are maximal with respect to this property?

    Solved affirmatively by Danzer, who gave an explicit construction.

    [Da85] Danzer, L., _Some combinatorial and metric problems in geometry_.
    Intuitive geometry (Siófok, 1985), 167-177. -/
@[category research solved, AMS 51]
theorem erdos_1071a :
    answer(True) ↔ ∃ S : Finset ((ℝ × ℝ) × (ℝ × ℝ)),
      IsMaximalDisjointUnitSegments S unitSquare := by
  sorry

/-- Is there a region $R$ with a maximal set of disjoint unit line segments
    that is countably infinite? -/
@[category research open, AMS 51]
theorem erdos_1071b :
    answer(sorry) ↔ ∃ (R : Set (ℝ × ℝ)) (S : Set ((ℝ × ℝ) × (ℝ × ℝ))),
      S.Countable ∧ S.Infinite ∧ IsMaximalDisjointUnitSegmentsCountable S R := by
  sorry

end Erdos1071
