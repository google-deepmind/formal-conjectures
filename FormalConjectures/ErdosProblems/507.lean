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
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Erdős Problem 507

*Reference:* [erdosproblems.com/507](https://www.erdosproblems.com/507)
-/

open scoped EuclideanGeometry

namespace Erdos507

abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The unit disk in the plane. -/
def UnitDisk : Set Point := Metric.closedBall 0 1

/--
The minimum area of a triangle determined by three distinct points in a set `S`.
-/
noncomputable def minTriangleArea (S : Finset Point) : ℝ :=
  let triples := S ×ˢ S ×ˢ S
  let distinctTriples := triples.filter fun ⟨p, q, r⟩ => p ≠ q ∧ q ≠ r ∧ p ≠ r
  let areas := distinctTriples.image fun ⟨p, q, r⟩ => EuclideanGeometry.triangle_area p q r
  (areas.min).getD 0 -- Return the minimum, defaulting to 0 if the set is empty (n < 3)

/--
$\alpha(n)$ is the supremum of `minTriangleArea S` over all sets `S` of $n$ points in the unit disk.
-/
noncomputable def α (n : ℕ) : ℝ :=
  sSup (minTriangleArea '' { S : Finset Point | S.card = n ∧ ↑S ⊆ UnitDisk })

/--
Let $\alpha(n)$ be such that every set of $n$ points in the unit disk contains three points which
determine a triangle of area at most $\alpha(n)$. Estimate $\alpha(n)$.
-/
@[category research open, AMS 52]
theorem erdos_507 :
    α = answer(sorry) := by
  sorry

end Erdos507
