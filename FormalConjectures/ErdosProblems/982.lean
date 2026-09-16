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
import FormalConjecturesUtil

/-!
# Erdős Problem 982

*Reference:* [erdosproblems.com/982](https://www.erdosproblems.com/982)
-/

open EuclideanGeometry

namespace Erdos982

/--
If $n$ distinct points in $\mathbb{R}^2$ form a convex polygon then some vertex has at least
$\lfloor\frac{n}{2}\rfloor$ different distances to other vertices.
-/
@[category research open, AMS 52]
theorem erdos_982 (n : ℕ) (hn : 3 ≤ n) (p : Fin n → ℝ²) (hp : Function.Injective p)
    (hp' : EuclideanGeometry.IsConvexPolygon p) :
    ∃ (i : Fin n), { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ n / 2 := by
  sorry

/--
For distinct points on a common circle, every vertex has at least
$\lfloor\frac{n}{2}\rfloor$ different distances to the other vertices.
This does not require convexity or the assumption $3 \leq n$.
-/
@[category research solved, AMS 52,
  formal_proof using lean4 at "https://github.com/arex1337/formal-conjectures-proofs/blob/3b7d581c75fd00e482deabfb20675cf3ccfaf49f/Erdos982/GeneralCircle.lean"]
theorem erdos_982.variants.concyclic {n : ℕ} (p : Fin n → ℝ²) (hp : Function.Injective p)
    (c : ℝ²) (R : ℝ) (hR : ∀ j, dist (p j) c = R) (i : Fin n) :
    { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ n / 2 := by
  sorry

end Erdos982
