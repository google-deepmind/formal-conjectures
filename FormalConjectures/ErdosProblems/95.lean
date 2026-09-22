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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 95

*References:*
- [erdosproblems.com/95](https://www.erdosproblems.com/95)
- [Er92e] Erdős, Pál, *Some Unsolved problems in Geometry, Number Theory and Combinatorics*.
  Eureka (1992), 44-48.
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [Er97c] Erdős, Paul, *Some of my favorite problems and results*. The mathematics of Paul
  Erdős, I (1997), 47-67.
- [Er97f] Erdős, Paul, *Some unsolved problems*. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1-10.
- [Al63] Altman, E., *On a problem of P. Erdős*. Amer. Math. Monthly (1963), 148-157.
- [GuKa15] Guth, Larry and Katz, Nets Hawk, *On the Erdős distinct distances problem in the
  plane*. Ann. of Math. (2) (2015), 155-190.
-/

@[expose] public section

open Filter EuclideanGeometry

namespace Erdos95

/--
Let $x_1,\ldots,x_n\in\mathbb{R}^2$ determine the set of distances $\{u_1,\ldots,u_t\}$. Suppose
$u_i$ appears as the distance between $f(u_i)$ many pairs of points. Then for all $\epsilon>0$
$$\sum_i f(u_i)^2 \ll_\epsilon n^{3+\epsilon}.$$

The case when the points determine a convex polygon was solved by Altman [Al63]. Note it is
trivial that $\sum f(u_i)=\binom{n}{2}$.

Solved by Guth and Katz [GuKa15] who proved the upper bound
$$\sum_i f(u_i)^2 \ll n^3\log n.$$

See also [94](https://www.erdosproblems.com/94).
-/
@[category research solved, AMS 5 52, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos95.lean#L1005"]
theorem erdos_95 : answer(True) ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ P : Finset ℝ²,
    ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤
      C * (P.card : ℝ) ^ (3 + ε) := by
  sorry

/-- Guth and Katz [GuKa15] proved the upper bound $\sum_i f(u_i)^2 \ll n^3\log n$. -/
@[category research solved, AMS 5 52]
theorem erdos_95.variants.guth_katz : ∃ C : ℝ, 0 < C ∧ ∀ P : Finset ℝ², 2 ≤ P.card →
    ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤
      C * (P.card : ℝ) ^ 3 * Real.log P.card := by
  sorry

end Erdos95
