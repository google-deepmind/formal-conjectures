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
# Erdős Problem 1121

If circles in the plane with radii $r_1, \ldots, r_n$ cannot be separated into two non-empty
groups by a line disjoint from all of them, then they can be covered by a single circle of radius
$r = \sum r_i$.

*Reference:* [erdosproblems.com/1121](https://www.erdosproblems.com/1121)

[GoGo45] Goodman, A. W. and Goodman, R. E., *A circle covering theorem*,
American Mathematical Monthly 52 (1945), 494-498.
-/

open scoped BigOperators

namespace Erdos1121

/--
Erdős Problem #1121 (proved by Goodman and Goodman [GoGo45]):

If $C_1, \ldots, C_n$ are circles in $\mathbb{R}^2$ with radii $r_1, \ldots, r_n$ such that no
line disjoint from all the circles divides them into two non-empty sets, then the circles can be
covered by a circle of radius $r = \sum r_i$.

A line in $\mathbb{R}^2$ is parameterized by a unit normal vector $v$ and offset $d$, defining
$\ell = \{x : \langle x, v \rangle = d\}$. The closed disk $\bar{B}(c_i, r_i)$ is disjoint from
$\ell$ when $|\langle c_i, v \rangle - d| > r_i$. The non-separability condition says that whenever
all disks are disjoint from a line, they all lie on the same side.
-/
@[category research solved, AMS 52]
theorem erdos_1121
    (n : ℕ)
    (center : Fin n → EuclideanSpace ℝ (Fin 2))
    (radius : Fin n → ℝ)
    (hr : ∀ i, 0 < radius i)
    (hns : ∀ (v : EuclideanSpace ℝ (Fin 2)) (d : ℝ),
      ‖v‖ = 1 →
      (∀ i, |@inner ℝ _ _ (center i) v - d| > radius i) →
      (∀ i j, @inner ℝ _ _ (center i) v > d ↔ @inner ℝ _ _ (center j) v > d)) :
    ∃ p : EuclideanSpace ℝ (Fin 2),
      ∀ i, dist (center i) p + radius i ≤ ∑ j : Fin n, radius j := by
  sorry

/--
Higher-dimensional generalization of Erdős Problem #1121:

The Goodman–Goodman result generalizes to $\mathbb{R}^d$: if $n$ closed balls in $\mathbb{R}^d$
with radii $r_1, \ldots, r_n$ cannot be separated into two non-empty groups by a hyperplane
disjoint from all of them, then they can be covered by a single ball of radius $\sum r_i$.

A hyperplane in $\mathbb{R}^d$ is parameterized by a unit normal vector $v$ and offset $d$,
defining $H = \{x : \langle x, v \rangle = d\}$. The non-separability condition is the same as
in the planar case.
-/
@[category research solved, AMS 52]
theorem erdos_1121_generalized
    (d : ℕ)
    (n : ℕ)
    (center : Fin n → EuclideanSpace ℝ (Fin d))
    (radius : Fin n → ℝ)
    (hr : ∀ i, 0 < radius i)
    (hns : ∀ (v : EuclideanSpace ℝ (Fin d)) (δ : ℝ),
      ‖v‖ = 1 →
      (∀ i, |@inner ℝ _ _ (center i) v - δ| > radius i) →
      (∀ i j, @inner ℝ _ _ (center i) v > δ ↔ @inner ℝ _ _ (center j) v > δ)) :
    ∃ p : EuclideanSpace ℝ (Fin d),
      ∀ i, dist (center i) p + radius i ≤ ∑ j : Fin n, radius j := by
  sorry

end Erdos1121
