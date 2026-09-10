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
# Erdős Problem 21

*References:*
- [erdosproblems.com/21](https://www.erdosproblems.com/21)
- [BaWa21] J. Barát and I. M. Wanless, Intersecting and 2-intersecting hypergraphs with maximal
  covering number: the Erdős-Lovász theme revisited. J. Combin. Des. (2021), 260-286.
- [ErLo75] Erdős, P. and Lovász, L., Problems and results on {$3$}-chromatic hypergraphs and some
  related questions. (1975), 609--627.
- [Ka92b] Kahn, Jeff, On a problem of Erdős and Lovász: random lines in a projective plane.
  Combinatorica (1992), 417-423.
- [Ka94] Kahn, Jeff, On a problem of Erdős and Lovász. II. {$n(r)=O(r)$}. J. Amer. Math. Soc.
  (1994), 125-143.
- [Tr14] A. Tripathi, A result on intersecting families with maximum transversal size.
  arXiv:1409.4610 (2014).
-/

namespace Erdos21

open Filter Asymptotics

/--
Let $f(n)$ be minimal such that there is an intersecting family $\mathcal{F}$ of sets of size $n$
(so $A\cap B\neq\emptyset$ for all $A,B\in \mathcal{F}$) with $\lvert \mathcal{F}\rvert=f(n)$ such
that any set $S$ with $\lvert S\rvert \leq n-1$ is disjoint from at least one $A\in \mathcal{F}$. Is
it true that
$$f(n) \ll n?$$

This problem was solved by Kahn [Ka94] who proved the upper bound $f(n) \ll n$.
-/
@[category research solved, AMS 5]
theorem erdos_21 :
    answer(True) ↔ ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r →
    (Hypergraph.minIntersectingEdges r : ENNReal) ≤ ENNReal.ofReal (C * r) := by
  sorry

end Erdos21
