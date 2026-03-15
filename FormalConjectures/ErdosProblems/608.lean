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
# Erdős Problem 608

*Reference:* [erdosproblems.com/608](https://www.erdosproblems.com/608)

Let $G$ be a graph with $n$ vertices and more than $n^2/4$ edges. Are there at least
$(2/9)n^2$ edges of $G$ which are contained in a $C_5$?

This was disproved. Füredi and Maleki (unpublished, described in [GHV19]) constructed
graphs with more than $n^2/4$ edges where at most $c \cdot n^2 + O(n)$ edges are in a
$C_5$, with $c = (2 + \sqrt{2})/16 \approx 0.2134$. Grzesik, Hu, and Volec [GHV19]
proved this bound is tight: any graph with more than $n^2/4$ edges contains at least
$(c - o(1)) \cdot n^2$ edges in a $C_5$.

[EFR92] Erdős, P., Faudree, R. J., Rousseau, C. C., _Extremal problems involving
vertices and edges on odd cycles_. Discrete Mathematics (1992), 23–31.

[Er97d] Erdős, P., _Some recent problems and results in graph theory_. Discrete
Mathematics (1997), 81–85.

[GHV19] Grzesik, A., Hu, P., Volec, J., _Minimum number of edges that occur in odd
cycles_. Journal of Combinatorial Theory, Series B (2019), 65–103.
-/

open scoped Classical
open SimpleGraph

namespace Erdos608

/-- The number of edges of $G$ contained in some $5$-cycle. An edge $\{u, v\}$ is
in a $C_5$ if there exist vertices $w_1, w_2, w_3$ (all five pairwise distinct)
such that $u$-$w_1$-$w_2$-$w_3$-$v$-$u$ is a $5$-cycle in $G$. Edges are counted as
unordered edges $\{u, v\}$ (with $u < v$ as a canonical ordering) to avoid
double-counting. -/
noncomputable def numEdgesInC5 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ G.Adj p.1 p.2 ∧
    ∃ w₁ w₂ w₃ : Fin n,
      ({p.1, p.2, w₁, w₂, w₃} : Finset (Fin n)).card = 5 ∧
      G.Adj p.1 w₁ ∧ G.Adj w₁ w₂ ∧ G.Adj w₂ w₃ ∧ G.Adj w₃ p.2).card

/--
**Erdős Problem 608** (Disproved) [EFR92, Er97d]:

If $G$ is a graph on $n$ vertices with more than $n^2/4$ edges, then at least
$(2/9) \cdot n^2$ edges of $G$ are contained in a $C_5$.

This is false. The correct threshold is $c = (2+\sqrt{2})/16 \approx 0.2134$, proved
optimal by Grzesik, Hu, and Volec [GHV19].
-/
@[category research solved, AMS 5]
theorem erdos_608 : answer(False) ↔
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (G.edgeFinset.card : ℝ) > (n : ℝ) ^ 2 / 4 →
      (numEdgesInC5 G : ℝ) ≥ 2 / 9 * (n : ℝ) ^ 2 := by
  sorry

end Erdos608
