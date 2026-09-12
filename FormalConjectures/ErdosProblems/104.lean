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
# Erdős Problem 104

*References:*
- [erdosproblems.com/104](https://www.erdosproblems.com/104)
- [El84] Elekes, G., *{$n$} points in the plane can determine $n^{3/2}$ unit circles*. Combinatorica
  (1984), 131.
- [Er75h] Erdős, P., *Some problems on elementary geometry*. Austral. Math. Soc. Gaz. (1975), 2-3.
- [Er81d] Erdős, P., *Some applications of graph theory and combinatorial methods to number theory
  and geometry*. Algebraic methods in graph theory, Vol. I, II (Szeged, 1978) (1981), 137-148.
- [Er92e] Erdős, Pál, *Some Unsolved problems in Geometry, Number Theory and Combinatorics*. Eureka
  (1992), 44-48.
- [HaMe86] Harborth, Heiko and Mengersen, Ingrid, *Point sets with many unit circles*. Discrete
  Math. (1986), 193--197.
-/

open Filter
open scoped EuclideanGeometry

namespace Erdos104

open EuclideanGeometry

/-- The number of distinct unit circles containing at least three points of `P`. -/
noncomputable def unitCircleCount (P : Finset ℝ²) : ℕ :=
  Set.ncard {s : Sphere ℝ² | s.radius = 1 ∧ 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard}

/-- The set of unit-circle counts attained by configurations of `n` points in the plane. -/
noncomputable def possibleUnitCircleCounts (n : ℕ) : Set ℕ :=
  {k | ∃ P : Finset ℝ², P.card = n ∧ unitCircleCount P = k}

/-- The maximum number of qualifying unit circles attained by a configuration of `n` points. -/
noncomputable def maxUnitCircleCount (n : ℕ) : ℕ :=
  sSup (possibleUnitCircleCounts n)

/--
Given $n$ points in $\mathbb{R}^2$ the number of distinct unit circles containing at least three points is $o(n^2)$.
-/
@[category research open, AMS 52]
theorem erdos_104 :
    (fun n : ℕ => (maxUnitCircleCount n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ 2) := by
  sorry

end Erdos104
