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

*References:*
* [erdosproblems.com/1071](https://www.erdosproblems.com/1071)
* [Da85] Danzer, L., _Some combinatorial and metric problems in geometry_.
  Intuitive geometry (Siófok, 1985), 167-177.
-/

open Set Metric EuclideanGeometry Order

namespace Erdos1071

/-- Two segments are disjoint if they only intersect at their endpoints (if at all). -/
def SegmentsDisjoint (seg1 seg2 : ℝ² × ℝ²) : Prop :=
  segment ℝ seg1.1 seg1.2 ∩ segment ℝ seg2.1 seg2.2 ⊆ {seg1.1, seg1.2, seg2.1, seg2.2}

/-- Can a finite set of disjoint unit segments in a unit square be maximal?
Solved affirmatively by [Da85], who gave an explicit construction. -/
@[category research solved, AMS 52]
theorem erdos_1071a :
    answer(True) ↔ ∃ S : Finset (ℝ² × ℝ²),
      Maximal (fun T : Finset (ℝ² × ℝ²) =>
        (∀ seg ∈ T, dist seg.1 seg.2 = 1 ∧
          seg.1 0 ∈ Icc 0 1 ∧ seg.1 1 ∈ Icc 0 1 ∧
          seg.2 0 ∈ Icc 0 1 ∧ seg.2 1 ∈ Icc 0 1) ∧
          (T : Set (ℝ² × ℝ²)).Pairwise SegmentsDisjoint) S := by
  sorry

/-- Is there a region $R$ with a maximal set of disjoint unit line segments that is countably infinite? -/
@[category research open, AMS 52]
theorem erdos_1071b :
    answer(sorry) ↔ ∃ (R : Set ℝ²) (S : Set (ℝ² × ℝ²)),
      S.Countable ∧ S.Infinite ∧
      Maximal (fun T : Set (ℝ² × ℝ²) =>
        (∀ seg ∈ T, dist seg.1 seg.2 = 1 ∧ seg.1 ∈ R ∧ seg.2 ∈ R) ∧
        T.Pairwise SegmentsDisjoint) S := by
  sorry

end Erdos1071
