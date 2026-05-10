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
# Erdős Problem 101

*Reference:* [erdosproblems.com/101](https://www.erdosproblems.com/101)
-/



namespace Erdos101

open EuclideanGeometry Filter Asymptotics

/--
The set of lines in $\mathbb{R}^2$ containing exactly $k$ points from a given set $S$.
-/
private noncomputable def linesWithPointsFor (k : ℕ) (S : Set ℝ²) : Set (AffineSubspace ℝ ℝ²) :=
  let determined_lines := { affineSpan ℝ {p, q} | (p ∈ S) (q ∈ S) (_ : p ≠ q) }
  { L ∈ determined_lines | (↑L ∩ S).ncard = k }

/--
The maximum number of lines containing exactly $4$ points among all sets $S$ of $n$
points in $\mathbb{R}^2$ satisfying the condition that no five points are collinear.
-/
noncomputable def numLinesWithFourPointMax (n : ℕ) : ℕ :=
  sSup {((linesWithPointsFor 4 S).ncard)| (S : Set ℝ²)
    (_ : S.ncard = n) (_ : S.Finite) (_ : NonCollinearFor 5 S)}

/--
Given $n$ points in $\mathbb{R}^2$, no five of which are on a line, the number of
lines containing four points is $o(n^2)$.
-/
@[category research open, AMS 52]
theorem erdos_101 : (fun n => (numLinesWithFourPointMax n : ℝ)) =o[atTop] (fun n => (n : ℝ)^2) := by
  sorry

-- TODO(firsching): formalize other results from the additional material

end Erdos101
