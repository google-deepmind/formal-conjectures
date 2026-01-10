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

open Set Metric EuclideanGeometry Order

namespace Erdos1071

/-- Two segments are disjoint if they only intersect at their endpoints (if at all). -/
def SegmentsDisjoint (p1 q1 p2 q2 : ℝ²) : Prop :=
  (segment ℝ p1 q1 ∩ segment ℝ p2 q2) ⊆ {p1, q1, p2, q2}

/-- Are there a finite set of unit line segments in the unit square, no two of which intersect, which are maximal with respect to this property?
Solved affirmatively by Danzer, who gave an explicit construction.

[Da85] Danzer, L., _Some combinatorial and metric problems in geometry_.
Intuitive geometry (Siófok, 1985), 167-177. -/
@[category research solved, AMS 52]
theorem erdos_1071a :
    answer(True) ↔ ∃ S : Finset (ℝ² × ℝ²),
      (∀ seg ∈ S, dist seg.1 seg.2 = 1 ∧
        seg.1 0 ∈ Icc 0 1 ∧ seg.1 1 ∈ Icc 0 1 ∧
        seg.2 0 ∈ Icc 0 1 ∧ seg.2 1 ∈ Icc 0 1) ∧
      (∀ s1 s2, s1 ∈ S → s2 ∈ S → s1 ≠ s2 → SegmentsDisjoint s1.1 s1.2 s2.1 s2.2) ∧
      Maximal (fun T : Finset (ℝ² × ℝ²) =>
        (∀ seg ∈ T, dist seg.1 seg.2 = 1 ∧
          seg.1 0 ∈ Icc 0 1 ∧ seg.1 1 ∈ Icc 0 1 ∧
          seg.2 0 ∈ Icc 0 1 ∧ seg.2 1 ∈ Icc 0 1) ∧
        (∀ s1 s2, s1 ∈ T → s2 ∈ T → s1 ≠ s2 → SegmentsDisjoint s1.1 s1.2 s2.1 s2.2)) S := by
  sorry

/-- Is there a region $R$ with a maximal set of disjoint unit line segments that is countably infinite? -/
@[category research open, AMS 52]
theorem erdos_1071b :
    answer(sorry) ↔ ∃ (R : Set ℝ²) (S : Set (ℝ² × ℝ²)),
      S.Countable ∧ S.Infinite ∧
      (∀ seg ∈ S, dist seg.1 seg.2 = 1 ∧ seg.1 ∈ R ∧ seg.2 ∈ R) ∧
      (∀ s1 s2, s1 ∈ S → s2 ∈ S → s1 ≠ s2 → SegmentsDisjoint s1.1 s1.2 s2.1 s2.2) ∧
      Maximal (fun T : Set (ℝ² × ℝ²) =>
        (∀ seg ∈ T, dist seg.1 seg.2 = 1 ∧ seg.1 ∈ R ∧ seg.2 ∈ R) ∧
        (∀ s1 s2, s1 ∈ T → s2 ∈ T → s1 ≠ s2 → SegmentsDisjoint s1.1 s1.2 s2.1 s2.2)) S := by
  sorry

end Erdos1071
