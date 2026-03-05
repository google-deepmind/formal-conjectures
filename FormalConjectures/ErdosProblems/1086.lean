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
# Erdős Problem 1086

*Reference:* [erdosproblems.com/1086](https://www.erdosproblems.com/1086)

Let $g(n)$ be minimal such that any set of $n$ points in $\mathbb{R}^2$ contains the vertices
of at most $g(n)$ many triangles with the same area. Equivalently, how many triangles of area $1$
can a set of $n$ points in $\mathbb{R}^2$ determine? This question is attributed to Oppenheim.

Erdős and Purdy [ErPu71] proved $n^2 \log \log n \ll g(n) \ll n^{5/2}$ and believed the lower
bound to be closer to the truth. The best known upper bound is $g(n) \ll n^{20/9}$ by Raz and
Sharir [RaSh17].

[ErPu71] Erdős, P. and Purdy, G., _Some extremal problems in geometry_.

[RaSh17] Raz, O. E. and Sharir, M., _The number of unit-area triangles in the plane: theme
and variations_.
-/

namespace Erdos1086

/-- The area of a triangle in $\mathbb{R}^2$ with vertices $p$, $q$, $r$, computed as
half the absolute value of the cross product $(q - p) \times (r - p)$. -/
noncomputable def triangleArea (p q r : ℝ × ℝ) : ℝ :=
  |(q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)| / 2

/-- The number of ordered triples of distinct points from $S \subseteq \mathbb{R}^2$ that form
a triangle with area exactly $A$. Each unordered triangle is counted $6$ times
(once per ordering of its vertices). -/
noncomputable def countTrianglesWithArea (S : Finset (ℝ × ℝ)) (A : ℝ) : ℕ :=
  ((S ×ˢ (S ×ˢ S)).filter (fun (p, q, r) =>
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ triangleArea p q r = A)).card

/--
Erdős Problem 1086 (Erdős–Purdy conjecture on equal-area triangles) [ErPu71]:

For every $\varepsilon > 0$, there exists $C > 0$ such that for every finite set $S$ of
points in $\mathbb{R}^2$ and every area $A$, the number of triangles with area $A$
determined by $S$ is at most $C \cdot |S|^{2+\varepsilon}$.

This formalizes the belief of Erdős and Purdy that $g(n) \ll n^{2+\varepsilon}$,
where $g(n)$ is the maximum number of triangles of the same area in any
set of $n$ points. The statement uses ordered triples, so the constant $C$
absorbs the factor of $6$.
-/
@[category research open, AMS 5 52]
theorem erdos_1086 :
    ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
    ∀ (S : Finset (ℝ × ℝ)) (A : ℝ),
      (countTrianglesWithArea S A : ℝ) ≤ C * (S.card : ℝ) ^ (2 + ε) := by
  sorry

end Erdos1086
