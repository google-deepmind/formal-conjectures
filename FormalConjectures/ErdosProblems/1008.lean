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
# Erdős Problem 1008

*Reference:* [erdosproblems.com/1008](https://www.erdosproblems.com/1008)

[CFS14b] Conlon, D., Fox, J., and Sudakov, B., _Large subgraphs without complete bipartite
graphs_. arXiv:1401.6711 (2014).

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proceedings of Conference, Oxford, 1969)
(1971), 97-109.

Additional thanks to Zach Hunter (simple proof in comments) and Boris Alexeev.
-/

open SimpleGraph Classical

namespace Erdos1008

/-- A simple graph contains a 4-cycle ($C_4$) if there exist four vertices
    $a, b, c, d$ forming the cycle $a$-$b$-$c$-$d$-$a$. Only two distinctness
    conditions ($a \ne c$ and $b \ne d$) are needed; the other four follow from
    irreflexivity of `SimpleGraph.Adj`. -/
def ContainsCycleFour {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c d : V, a ≠ c ∧ b ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- A simple graph is $C_4$-free if it contains no 4-cycle as a subgraph. -/
def CycleFourFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ContainsCycleFour G

/--
Erdős Problem 1008 (Proved by Conlon, Fox, and Sudakov [CFS14b]):
There exists an absolute constant $c > 0$ such that every graph with $m$ edges
contains a $C_4$-free subgraph with at least $c \cdot m^{2/3}$ edges.

Originally asked by Bollobás and Erdős with $m^{3/4}$ in place of $m^{2/3}$,
but Folkman showed the $m^{3/4}$ version is false (counterexample: $K_{n,n^2}$).
Erdős [Er71] revised the conjecture to $m^{2/3}$, noting $\gg m^{1/2}$ is trivial.
Erdős also noted in a footnote that Szemerédi proved this conjecture, but gave
no reference.
-/
@[category research solved, AMS 5]
theorem erdos_1008 :
    ∃ c : ℝ, c > 0 ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        ∃ H : SimpleGraph (Fin n),
          H ≤ G ∧
          CycleFourFree H ∧
          c * (G.edgeFinset.card : ℝ) ^ ((2 : ℝ) / 3) ≤ (H.edgeFinset.card : ℝ) := by
  sorry

end Erdos1008
