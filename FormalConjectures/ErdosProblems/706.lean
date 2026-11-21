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
# Erdős Problem 706

*References:*
- [erdosproblems.com/706](https://www.erdosproblems.com/706)
- [Er81] Erdős, P., *On the combinatorial problems which I would most like to see solved*.
  Combinatorica (1981), 25-42.
-/

@[expose] public section

open Filter
open scoped EuclideanGeometry

namespace Erdos706

/--
Let $L(r)$ be such that if $G$ is a graph formed by taking a finite set of points $P$ in
$\mathbb{R}^2$ and some set $A\subset (0,\infty)$ of size $r$, where the vertex set is $P$ and
there is an edge between two points if and only if their distance is a member of $A$, then
$\chi(G)\leq L(r)$.

Estimate $L(r)$. In particular, is it true that $L(r)\leq r^{O(1)}$?

The case $r=1$ is the Hadwiger-Nelson problem, for which it is known that
$5\leq L(1)\leq 7$.

See also [508](https://www.erdosproblems.com/508), [704](https://www.erdosproblems.com/704),
and [705](https://www.erdosproblems.com/705).

Here $L(r)\leq r^{O(1)}$ is read as: there is $C$ with $\chi(G)\leq r^C$ for all large $r$. Small
$r$ must be excluded, since $L(1)\geq 5 > 1^C$.
-/
@[category research open, question, AMS 5 52]
theorem erdos_706 :
    ∃ C : ℕ, ∀ᶠ r : ℕ in atTop, ∀ (P : Finset ℝ²) (A : Finset ℝ), A.card = r →
      (∀ a ∈ A, 0 < a) →
      (SimpleGraph.DistancePlaneGraph (A : Set ℝ) (P : Set ℝ²)).chromaticNumber ≤
        (r ^ C : ℕ) := by
  sorry

end Erdos706
