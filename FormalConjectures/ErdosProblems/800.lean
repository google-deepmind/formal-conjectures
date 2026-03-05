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
# Erdős Problem 800

*Reference:* [erdosproblems.com/800](https://www.erdosproblems.com/800)

If $G$ is a graph on $n$ vertices which has no two adjacent vertices of degree $\geq 3$ then
$R(G) \ll n$, where the implied constant is absolute.

A problem of Burr and Erdős [BuEr75]. Solved in the affirmative by Alon [Al94].
This is a special case of problem #163.

[BuEr75] Burr, S. A. and Erdős, P., _On the magnitude of generalized Ramsey numbers for graphs_,
1975.

[Al94] Alon, N., _Subdivided graphs have linear Ramsey numbers_, 1994.
-/

open SimpleGraph

namespace Erdos800

/-- A graph $G$ on $\text{Fin}(n)$ has a subgraph copy in $H$ if there is an injective function
that preserves adjacency. -/
def HasSubgraphCopy {n N : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin N)) : Prop :=
  ∃ f : Fin n → Fin N, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The graph Ramsey number $R(G)$: the minimum $N$ such that for every graph $H$ on
$\text{Fin}(N)$, either $G$ embeds into $H$ or $G$ embeds into $H^c$ as a subgraph. -/
noncomputable def graphRamseyNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)), HasSubgraphCopy G H ∨ HasSubgraphCopy G Hᶜ}

/--
Erdős Problem 800 (Burr–Erdős [BuEr75]):

If $G$ is a graph on $n$ vertices which has no two adjacent vertices of degree $\geq 3$,
then $R(G) \ll n$, where the implied constant is absolute.

Formally: there exists an absolute constant $C > 0$ such that for all $n$ and every
graph $G$ on $n$ vertices where no edge has both endpoints of degree $\geq 3$,
the graph Ramsey number $R(G) \leq C \cdot n$.

Proved by Alon [Al94].
-/
@[category research solved, AMS 5]
theorem erdos_800 :
    ∃ C : ℝ, C > 0 ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (h : DecidableRel G.Adj),
        haveI := h
        (∀ u v, G.Adj u v → G.degree u < 3 ∨ G.degree v < 3) →
        (graphRamseyNumber G : ℝ) ≤ C * (n : ℝ) := by
  sorry

end Erdos800
