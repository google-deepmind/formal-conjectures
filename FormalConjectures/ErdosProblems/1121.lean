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
# Erdős Problem 1121

*References:*
- [erdosproblems.com/1121](https://www.erdosproblems.com/1121)
- [BeLi16] Bezdek, Károly and Litvak, Alexander E., *Packing convex bodies by cylinders*.
  Discrete Comput. Geom. (2016), 725-738.
- [GoGo45] Goodman, A. W. and Goodman, R. E., *A circle covering theorem*. Amer. Math. Monthly
  (1945), 494-498.
- [Ha47] Hadwiger, H., *Nonseparable convex systems*. Amer. Math. Monthly (1947), 583-585.
-/

namespace Erdos1121

open scoped EuclideanGeometry

/--
If $C_1,\ldots,C_n$ are circles in $\mathbb{R}^2$ with radii $r_1,\ldots,r_n$ such that no line
disjoint from all the circles divides them into two non-empty sets then the circles can be
covered by a circle of radius $r=\sum r_i$.

This is true, and was proved by Goodman and Goodman [GoGo45] (whose proof also generalises to
higher dimensions). A generalisation to convex bodies was proved by Hadwiger [Ha47].

An alternative proof is given by Bezdek and Litvak [BeLi16].
-/
@[category research solved, AMS 52, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos1121.lean"]
theorem erdos_1121 {n : ℕ} (c : Fin n → ℝ²) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hsep : ∀ (v : ℝ²) (t : ℝ), v ≠ 0 →
      (∀ i, ∀ p ∈ Metric.closedBall (c i) (r i), inner ℝ v p ≠ t) →
      (∀ i, inner ℝ v (c i) < t) ∨ (∀ i, t < inner ℝ v (c i))) :
    ∃ z : ℝ², (⋃ i, Metric.closedBall (c i) (r i)) ⊆ Metric.closedBall z (∑ i, r i) := by
  sorry

/--
The proof of Goodman and Goodman [GoGo45] also generalises to higher dimensions: if
$B_1,\ldots,B_n$ are balls in $\mathbb{R}^d$ with radii $r_1,\ldots,r_n$ such that no hyperplane
disjoint from all the balls divides them into two non-empty sets then the balls can be covered by
a ball of radius $r=\sum r_i$.
-/
@[category research solved, AMS 52]
theorem erdos_1121.variants.higher_dimension {d n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin d))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hsep : ∀ (v : EuclideanSpace ℝ (Fin d)) (t : ℝ), v ≠ 0 →
      (∀ i, ∀ p ∈ Metric.closedBall (c i) (r i), inner ℝ v p ≠ t) →
      (∀ i, inner ℝ v (c i) < t) ∨ (∀ i, t < inner ℝ v (c i))) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      (⋃ i, Metric.closedBall (c i) (r i)) ⊆ Metric.closedBall z (∑ i, r i) := by
  sorry

end Erdos1121
