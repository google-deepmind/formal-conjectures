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

import FormalConjecturesUtil

/-!
# Erdős Problem 1008

*References:*
- [erdosproblems.com/1008](https://www.erdosproblems.com/1008)
- [CFS14b] Conlon, D. and Fox, J. and Sudakov, B., *Large subgraphs without complete bipartite
  graphs*. arXiv:1401.6711 (2014).
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
-/

open SimpleGraph

namespace Erdos1008

/--
Does every graph with $m$ edges contain a subgraph with $\gg m^{2/3}$ edges which contains
no $C_4$?

This problem was first solved in the affirmative by Conlon, Fox, and Sudakov [CFS14b]. A simple
proof is given by Hunter in the comments.
-/
@[category research solved, AMS 5]
theorem erdos_1008 : answer(True) ↔
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ H ≤ G, (cycleGraph 4).Free H ∧
        c * (G.edgeSet.ncard : ℝ) ^ (2 / 3 : ℝ) ≤ (H.edgeSet.ncard : ℝ) := by
  sorry

/--
Originally asked by Bollobás and Erdős in 'a colloquium on graph theory at Tihany' with $m^{2/3}$
replaced by $m^{3/4}$. Folkman showed this is false with the counterexample $K_{n,n^2}$, which has
$n^3$ edges, and yet every subgraph with $>n^2+\binom{n}{2}$ edges contains a $C_4$.
-/
@[category research solved, AMS 5]
theorem erdos_1008.variants.three_quarters : answer(False) ↔
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ H ≤ G, (cycleGraph 4).Free H ∧
        c * (G.edgeSet.ncard : ℝ) ^ (3 / 4 : ℝ) ≤ (H.edgeSet.ncard : ℝ) := by
  sorry

/--
Folkman's counterexample $K_{n,n^2}$, which has $n^3$ edges, and yet every subgraph with
$>n^2+\binom{n}{2}$ edges contains a $C_4$.
-/
@[category research solved, AMS 5]
theorem erdos_1008.variants.folkman (n : ℕ) :
    ((completeBipartiteGraph (Fin n) (Fin (n ^ 2))).edgeSet.ncard = n ^ 3) ∧
      ∀ H ≤ completeBipartiteGraph (Fin n) (Fin (n ^ 2)),
        n ^ 2 + n.choose 2 < H.edgeSet.ncard → cycleGraph 4 ⊑ H := by
  sorry

/--
In [Er71] Erdős revises the conjecture to $m^{2/3}$, and notes $\gg m^{1/2}$ is trivial.
-/
@[category research solved, AMS 5]
theorem erdos_1008.variants.lower_bound :
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ H ≤ G, (cycleGraph 4).Free H ∧
        c * (G.edgeSet.ncard : ℝ) ^ (1 / 2 : ℝ) ≤ (H.edgeSet.ncard : ℝ) := by
  sorry

end Erdos1008
