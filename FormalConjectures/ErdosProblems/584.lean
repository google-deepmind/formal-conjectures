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
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Domination

/-!
# Erdős Problem 584

*Reference:* [erdosproblems.com/584](https://www.erdosproblems.com/584)

A problem of Erdős, Duke, and Rödl.

[DuEr82] Duke, R.A. and Erdős, P., _Subgraphs in which each pair of edges lies in a short
common cycle_. Proceedings of the thirteenth Southeastern conference on combinatorics, graph
theory and computing (1982), 253-260.

[DER84] Duke, R.A., Erdős, P., and Rödl, V., _More results on subgraphs with many short
cycles_. Proceedings of the fifteenth Southeastern conference on combinatorics, graph theory
and computing (1984), 295-300.

[FoSu08b] Fox, J. and Sudakov, B., _On a problem of Duke-Erdős-Rödl on cycle-connected
subgraphs_. Journal of Combinatorial Theory, Series B (2008), 1056-1062.
-/

open SimpleGraph

namespace Erdos584

/-- Two edges of a graph lie on a common cycle of length at most $k$. -/
def EdgesOnCommonCycle {V : Type*} (G : SimpleGraph V)
    (e₁ e₂ : Sym2 V) (k : ℕ) : Prop :=
  ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ c.length ≤ k ∧
    e₁ ∈ c.edges ∧ e₂ ∈ c.edges

/-- Two edges of a graph lie on a common cycle of exactly length $k$. -/
def EdgesOnCommonCycleExact {V : Type*} (G : SimpleGraph V)
    (e₁ e₂ : Sym2 V) (k : ℕ) : Prop :=
  ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ c.length = k ∧
    e₁ ∈ c.edges ∧ e₂ ∈ c.edges

/--
Erdős Problem 584, Part 1:
For every graph $G$ on $n$ vertices with $\delta n^2$ edges, there exists a subgraph $H_1$
with $\gg \delta^3 n^2$ edges such that every two edges of $H_1$ lie on a common cycle of
length at most $6$ in $G$, and any two edges sharing a vertex lie on a common
cycle of length exactly $4$.

A problem of Erdős, Duke, and Rödl [DuEr82, DER84].
-/
@[category research open, AMS 5]
theorem erdos_584 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ), 0 < n →
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    ∀ (G : SimpleGraph (Fin n)),
      (G.edgeFinset.card : ℝ) ≥ δ * (n : ℝ) ^ 2 →
      ∃ H : SimpleGraph (Fin n),
        H ≤ G ∧
        (H.edgeFinset.card : ℝ) ≥ c * δ ^ 3 * (n : ℝ) ^ 2 ∧
        (∀ e₁ ∈ H.edgeFinset, ∀ e₂ ∈ H.edgeFinset,
          EdgesOnCommonCycle G e₁ e₂ 6) ∧
        (∀ e₁ ∈ H.edgeFinset, ∀ e₂ ∈ H.edgeFinset,
          edgesAdjacent e₁ e₂ → EdgesOnCommonCycleExact G e₁ e₂ 4) := by
  sorry

/--
Erdős Problem 584, Part 2:
For every graph $G$ on $n$ vertices with $\delta n^2$ edges, there exists a subgraph $H_2$
with $\gg \delta^2 n^2$ edges such that every two edges of $H_2$ lie on a common cycle of
length at most $8$ in $G$.

A problem of Erdős, Duke, and Rödl [DuEr82, DER84].
-/
@[category research open, AMS 5]
theorem erdos_584.variants.part2 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ), 0 < n →
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    ∀ (G : SimpleGraph (Fin n)),
      (G.edgeFinset.card : ℝ) ≥ δ * (n : ℝ) ^ 2 →
      ∃ H : SimpleGraph (Fin n),
        H ≤ G ∧
        (H.edgeFinset.card : ℝ) ≥ c * δ ^ 2 * (n : ℝ) ^ 2 ∧
        (∀ e₁ ∈ H.edgeFinset, ∀ e₂ ∈ H.edgeFinset,
          EdgesOnCommonCycle G e₁ e₂ 8) := by
  sorry

end Erdos584
