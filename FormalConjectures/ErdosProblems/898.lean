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
# Erdős Problem 898

*References:*
- [erdosproblems.com/898](https://www.erdosproblems.com/898)
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*.
  (1982), 59--79.
- [Wikipedia](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Mordell_inequality)
-/

open Affine EuclideanGeometry

namespace Erdos898

/--
If $A,B,C\in \mathbb{R}^2$ form a triangle and $P$ is a point in the interior then, if $N$ is
where the perpendicular from $P$ to $AB$ meets the triangle, and similarly for $M$ and $L$,
\[
\overline{PA}+\overline{PB}+\overline{PC}\geq 2(\overline{PM}+\overline{PN}+\overline{PL}).
\]

Conjectured by Erdős in 1932 (according to [Er82e]) and proved by Mordell soon afterwards, now
known as the Erdős-Mordell inequality.
-/
@[category research solved, AMS 51, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos898.lean"]
theorem erdos_898 (A B C P L M N : ℝ²) (hABC : AffineIndependent ℝ ![A, B, C])
    (hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²)))
    (hN : N ∈ line[ℝ, A, B]) (hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction)
    (hM : M ∈ line[ℝ, B, C]) (hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction)
    (hL : L ∈ line[ℝ, C, A]) (hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction) :
    dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L) := by
  sorry

end Erdos898
