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
# Erdős Problem 1034

A conjecture of Erdős and Faudree, and a stronger version of Problem #905.
Erdős asked whether every dense graph (with more than $n^2/4$ edges) contains a triangle
whose vertices have many common neighbors — specifically, more than $(1/2 - \varepsilon)n$
vertices each adjacent to at least two of the triangle's vertices.

*Reference:* [erdosproblems.com/1034](https://www.erdosproblems.com/1034)

[Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
Quaestiones Mathematicae (1993), 333–350.
-/

open Classical SimpleGraph Finset

namespace Erdos1034

/-- The number of vertices in a graph adjacent to at least two of three
given vertices $u$, $v$, $w$. -/
noncomputable def adjToAtLeastTwoOfTriangle {n : ℕ} (G : SimpleGraph (Fin n))
    (u v w : Fin n) : ℕ :=
  (Finset.univ.filter fun x : Fin n =>
    (G.Adj x u ∧ G.Adj x v) ∨ (G.Adj x v ∧ G.Adj x w) ∨ (G.Adj x u ∧ G.Adj x w)).card

/--
**Erdős Problem 1034** (Disproved) [Er93, p. 344]:

For every $\varepsilon > 0$, does there exist $N_0$ such that for all $n \ge N_0$, every graph on
$n$ vertices with more than $n^2 / 4$ edges contains a triangle $\{u, v, w\}$ such that
more than $(1/2 - \varepsilon) \cdot n$ vertices are each adjacent to at least two of $u$, $v$, $w$?

Disproved by Ma and Tang, who construct a graph with $n$ vertices and
$> n^2 / 4$ edges in which every triangle has at most $(2 - \sqrt{5/2} + o(1))n$
vertices adjacent to at least two of its vertices ($2 - \sqrt{5/2} \approx 0.4189$).
-/
@[category research solved, AMS 5]
theorem erdos_1034 : answer(False) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      G.edgeFinset.card > n ^ 2 / 4 →
      ∃ u v w : Fin n, G.Adj u v ∧ G.Adj v w ∧ G.Adj u w ∧
        (adjToAtLeastTwoOfTriangle G u v w : ℝ) > (1 / 2 - ε) * (n : ℝ) := by
  sorry

end Erdos1034
