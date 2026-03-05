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
# Erdős Problem 636

*Reference:* [erdosproblems.com/636](https://www.erdosproblems.com/636)

Suppose $G$ is a graph on $n$ vertices which contains no complete graph or independent
set on $\gg \log n$ many vertices. Must $G$ contain $\gg n^{5/2}$ induced subgraphs which
pairwise differ in either the number of vertices or the number of edges?

A problem of Erdős, Faudree, and Sós [Er93, p.346], who proved there exist
$\gg n^{3/2}$ many such subgraphs, and note that $n^{5/2}$ would be best possible.

This was proved by Kwan and Sudakov [KwSu21].

[Er93] Erdős, P., _On some of my favourite theorems_ (1993), p.346.

[Er97d] Erdős, P., _Some of my new and almost new problems and results in
combinatorics and graph theory_ (1997).

[KwSu21] Kwan, M. and Sudakov, B., _Proof of a conjecture on induced subgraphs
of Ramsey graphs_ (2021).
-/

open SimpleGraph

namespace Erdos636

/-- The set of distinct (vertex count, edge count) signatures realized by induced
subgraphs of a graph $G$ on $\operatorname{Fin}(n)$. For each subset $S$ of vertices,
we record $(|S|, |E(G[S])|)$ where $G[S]$ is the induced subgraph on $S$. -/
noncomputable def inducedSubgraphSignatures {n : ℕ} (G : SimpleGraph (Fin n)) :
    Finset (ℕ × ℕ) :=
  Finset.univ.image fun S : Finset (Fin n) =>
    (S.card, (G.induce (↑S : Set (Fin n))).edgeSet.ncard)

/--
**Erdős Problem 636** [Er93, p.346][Er97d]:

For every $C > 0$, there exist $c > 0$ and $N_0$ such that for all $n \geq N_0$, if $G$ is a
graph on $n$ vertices with clique number at most $C \cdot \log_2(n)$ and independence number
at most $C \cdot \log_2(n)$, then $G$ has at least $c \cdot n^{5/2}$ distinct induced subgraph
signatures (pairs (vertex count, edge count) among all induced subgraphs of $G$).

Proved by Kwan and Sudakov [KwSu21].
-/
@[category research solved, AMS 5]
theorem erdos_636 :
    answer(True) ↔
    ∀ C : ℝ, C > 0 →
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
    (∀ S : Finset (Fin n), G.IsClique (↑S : Set (Fin n)) →
      (S.card : ℝ) ≤ C * Real.logb 2 (↑n : ℝ)) →
    (∀ S : Finset (Fin n), Gᶜ.IsClique (↑S : Set (Fin n)) →
      (S.card : ℝ) ≤ C * Real.logb 2 (↑n : ℝ)) →
    ((inducedSubgraphSignatures G).card : ℝ) ≥ c * (↑n : ℝ) ^ ((5 : ℝ) / 2) := by
  sorry

end Erdos636
