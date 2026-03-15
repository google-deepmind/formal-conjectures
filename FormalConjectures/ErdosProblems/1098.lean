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
# Erdős Problem 1098

If the non-commuting graph of a group $G$ (with an edge between $g$ and $h$ iff $gh \neq hg$)
contains no infinite complete subgraph, then there is a finite bound on the size of its complete
subgraphs. Proved by Neumann, who showed this holds iff the centre of $G$ has finite index.

*Reference:* [erdosproblems.com/1098](https://www.erdosproblems.com/1098)

[Ne76] Neumann, B.H., _A problem of Paul Erdős on groups_, J. Austral. Math. Soc. Ser. A
21 (1976), 467-472.
-/

open SimpleGraph

namespace Erdos1098

/-- The non-commuting graph of a group $G$ has vertices the elements of $G$,
with an edge between $g$ and $h$ if and only if they do not commute ($gh \neq hg$). -/
def nonCommutingGraph (G : Type*) [Group G] : SimpleGraph G where
  Adj g h := g * h ≠ h * g
  symm := by intro _ _ hab; exact Ne.symm hab
  loopless := by intro a hab; exact hab rfl

/--
Erdős Problem 1098 (Proved by Neumann [Ne76]):
Let $G$ be a group and $\Gamma(G)$ be the non-commuting graph, with vertices the elements
of $G$ and an edge between $g$ and $h$ if and only if $gh \neq hg$. If $\Gamma$ contains no
infinite complete subgraph (i.e., no infinite set of pairwise non-commuting
elements), then there is a finite bound on the size of complete subgraphs of $\Gamma$.

This formalizes the forward direction of Neumann's result. The full result also
establishes that $\Gamma$ contains no infinite complete subgraph if and only if
the centre of $G$ has finite index, and if the centre has index $n$ then $\Gamma$
contains no complete subgraph on more than $n$ vertices.
-/
@[category research solved, AMS 5 20]
theorem erdos_1098 (G : Type*) [Group G] :
    (¬ ∃ S : Set G, S.Infinite ∧ (nonCommutingGraph G).IsClique S) →
    (∃ n : ℕ, ∀ S : Finset G, (nonCommutingGraph G).IsClique (S : Set G) → S.card ≤ n) := by
  sorry

end Erdos1098
