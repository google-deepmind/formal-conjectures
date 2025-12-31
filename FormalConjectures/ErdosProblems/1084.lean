/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 1084

*Reference:* [erdosproblems.com/1084](https://www.erdosproblems.com/1084)

Let `f_2(n)` be the maximum number of pairs of points at distance exactly `1`
among any set of `n` points in `ℝ²`, under the condition that all pairwise
distances are at least `1`.

Estimate the growth of `f_2(n)`.

Status: open.
-/

open Finset Real
open scoped EuclideanGeometry

namespace Erdos1084

/--
Erdős problem 1084.

There exists a constant `C` such that for any finite set `s` of points in `ℝ²`
with all pairwise distances at least `1`, the number of ordered pairs of distinct
points in `s` at distance exactly `1` is at most `C * n^{4/3}`, where `n = card s`.
-/
@[category research open, AMS 52]
theorem erdos_1084 :
    ∃ C : ℝ,
      ∀ s : Finset ℝ²,
        (s.toSet.Pairwise (fun x y => 1 ≤ dist x y)) →
        #{p ∈ s.offDiag | dist p.1 p.2 = 1} ≤ C * (#s : ℝ) ^ (4 / 3) := by
  sorry

end Erdos1084
