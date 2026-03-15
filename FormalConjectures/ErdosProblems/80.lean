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
# Erdős Problem 80

*Reference:* [erdosproblems.com/80](https://www.erdosproblems.com/80)

Let $c > 0$ and let $f_c(n)$ be the maximal $m$ such that every graph $G$ with
$n$ vertices and at least $cn^2$ edges, where each edge is contained in at least
one triangle, must contain a book of size $m$, that is, an edge shared by at least
$m$ different triangles.

Estimate $f_c(n)$. In particular, is it true that $f_c(n) \gg \log n$?

A problem of Erdős and Rothschild. Alon and Trotter showed that, provided $c < 1/4$,
$f_c(n) \ll_c n^{1/2}$. Szemerédi observed that his regularity lemma implies
$f_c(n) \to \infty$. Fox and Loh [FoLo12] proved that
$f_c(n) \le n^{O(1/\log\log n)}$ for all $c < 1/4$, disproving the stronger
conjecture $f_c(n) > n^\varepsilon$. Edwards (unpublished) and Khadziivanov and
Nikiforov [KhNi79] showed that for $c > 1/4$, $f_c(n) \geq n/6$.

The weaker conjecture $f_c(n) \gg \log n$ remains open.

See also Problem 600.

[FoLo12] Fox, J., Loh, P.-S., _On a problem of Erdős and Rothschild on edges in
triangles_. Combinatorica (2012), 619–628.

[KhNi79] Hadžiivanov, N. G., Nikiforov, S. V., _Solution of a problem of P. Erdős
about the maximum number of triangles with a common edge in a graph_. C. R. Acad.
Bulgare Sci. (1979), 1315–1318.
-/

open SimpleGraph

namespace Erdos80

/-- The number of common neighbors of $u$ and $v$ in $G$. When $\{u, v\}$ is an edge,
    this equals the number of triangles containing that edge (i.e., the book size at
    that edge). -/
def bookSize {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ :=
  ((G.neighborFinset u) ∩ (G.neighborFinset v)).card

/-- Every edge of $G$ is contained in at least one triangle. -/
def EveryEdgeInTriangle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v : V, G.Adj u v → 0 < bookSize G u v

/-- **Erdős Problem 80**: For every $c > 0$, there exists $C > 0$ such that for all
    sufficiently large $n$, every graph on $n$ vertices with at least $cn^2$ edges,
    where every edge lies in a triangle, contains an edge that is in at least
    $C \log n$ triangles. -/
@[category research open, AMS 5]
theorem erdos_80 : answer(sorry) ↔
    ∀ c : ℝ, c > 0 →
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ (n : ℕ), n ≥ N₀ →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (G.edgeFinset.card : ℝ) ≥ c * (n : ℝ) ^ 2 →
      EveryEdgeInTriangle G →
      ∃ u v : Fin n, G.Adj u v ∧
        (bookSize G u v : ℝ) ≥ C * Real.log (n : ℝ) := by
  sorry

end Erdos80
