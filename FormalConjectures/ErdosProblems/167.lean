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
# Erdős Problem 167

*Reference:* [erdosproblems.com/167](https://www.erdosproblems.com/167)

Tuza's conjecture (1981): If $G$ is a finite simple graph whose maximum number
of pairwise edge-disjoint triangles (the triangle packing number $\nu(G)$) is at
most $k$, then $G$ can be made triangle-free by removing at most $2k$ edges (the
triangle covering number $\tau(G)$ is at most $2k$).

Equivalently: $\tau(G) \leq 2 \cdot \nu(G)$ for every finite graph $G$.

It is trivial that $\tau(G) \leq 3 \cdot \nu(G)$. The examples of $K_4$ and $K_5$ show that
$2k$ would be best possible. Haxell [Ha99] improved the trivial bound to
$(3 - 3/23 + o(1))k$. Kahn and Park [KaPa22] proved this for random graphs.

[Ha99] Haxell, P. E., _Packing and covering triangles in graphs_. Discrete Math. 195 (1999), 251–254.

[KaPa22] Kahn, J. and Park, J., _Tuza's conjecture for random graphs_. Random Structures & Algorithms 61 (2022), 235–249.

[Er88] Erdős, P., _Problems and results on chromatic numbers in finite and infinite graphs_. Graph theory with applications to algorithms and computer science (1985), 201–213.
-/

open SimpleGraph Finset

namespace Erdos167

/--
Erdős Conjecture (Problem 167) — Tuza's Conjecture [Er88]:

For any finite simple graph $G$, if the maximum number of pairwise edge-disjoint
triangles in $G$ is at most $k$, then $G$ can be made triangle-free by removing at
most $2k$ edges.

Two triangles (3-cliques) are edge-disjoint iff their vertex sets share at most
one vertex, since in a triangle every pair of vertices forms an edge.

The hypothesis states that every family of pairwise edge-disjoint triangles
has size at most $k$. The conclusion states that there exists a subgraph $H \leq G$
that is triangle-free, obtained by removing at most $2k$ edges from $G$.
-/
@[category research open, AMS 5]
theorem erdos_167 : answer(sorry) ↔
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
    (∀ (T : Finset (Finset V)),
      (∀ t ∈ T, G.IsNClique 3 t) →
      (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → (t₁ ∩ t₂).card ≤ 1) →
      T.card ≤ k) →
    ∃ (H : SimpleGraph V),
      H ≤ G ∧
      H.CliqueFree 3 ∧
      (G.edgeSet \ H.edgeSet).ncard ≤ 2 * k := by sorry

end Erdos167
