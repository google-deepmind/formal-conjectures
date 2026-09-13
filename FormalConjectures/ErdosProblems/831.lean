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
# Erdős Problem 831

The problem asks to estimate $h(n)$. This is interpreted as asking for $\Theta(h(n))$.

*References:*
- [erdosproblems.com/831](https://www.erdosproblems.com/831)
- [Er75h] Erdős, P., *Some problems on elementary geometry*. Austral. Math. Soc. Gaz. (1975), 2-3.
- [Er92e] Erdős, Pál, *Some Unsolved problems in Geometry, Number Theory and Combinatorics*. Eureka
  (1992), 44-48.
-/

open Filter Asymptotics EuclideanGeometry
open scoped EuclideanGeometry

namespace Erdos831

/-- The number of distinct radii of circles passing through at least three points of `P`. -/
noncomputable def distinctCircumradii (P : Finset ℝ²) : ℕ :=
  Set.ncard ((fun s : Sphere ℝ² ↦ s.radius) ''
    {s | 3 ≤ {p ∈ (P : Set ℝ²) | p ∈ s}.ncard})

/--
$h(n)$ is the minimum number of distinct circumradii determined by any $n$-point set in
$\mathbb{R}^2$ in general position (no three collinear, no four cocyclic).
-/
noncomputable def h (n : ℕ) : ℕ :=
  sInf {distinctCircumradii P | (P : Finset ℝ²) (_ : P.card = n)
    (_ : InGeneralPosition (P : Set ℝ²))}

/--
Let $h(n)$ be maximal such that in any $n$ points in $\mathbb{R}^2$ (with no three on a line and
no four on a circle) there are at least $h(n)$ many circles of different radii passing through
three points. Estimate $h(n)$.
-/
@[category research open, AMS 52]
theorem erdos_831 :
    (fun n ↦ (h n : ℝ)) =Θ[atTop] (answer(sorry) : ℕ → ℝ) := by
  sorry

end Erdos831
