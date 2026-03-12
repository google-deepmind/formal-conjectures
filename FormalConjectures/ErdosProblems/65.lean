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
import FormalConjectures.ErdosProblems.«751»

/-!
# Erdős Problem 65

*Reference:* [erdosproblems.com/65](https://www.erdosproblems.com/65)

*Related:* Erdős Problem 57.

Is the sum of reciprocals of distinct cycle lengths in a graph on $n$ vertices with $kn$
edges minimised by the complete bipartite graph? Gyárfás, Komlós, and Szemerédi [GKS84]
proved $\sum 1/a_i \gg \log k$; Liu and Montgomery [LiMo20] proved the sharp bound.

Montgomery, Milojević, Pokrovskiy, and Sudakov [MMPS] showed that for sufficiently large
$k$, the sum $\sum 1/a_i$ is in fact *maximised* (not minimised) when $G$ is a complete
bipartite graph, suggesting the original minimisation conjecture is false.

[GKS84] Gyárfás, A., Komlós, J., and Szemerédi, E., *On the distribution of cycle lengths in
graphs*, J. Graph Theory 8 (1984), 441–462.

[LiMo20] Liu, H. and Montgomery, R., *A solution to Erdős and Hajnal's odd cycle problem*,
J. Amer. Math. Soc. 36 (2023), 1191–1234.

[MMPS] Montgomery, R., Milojević, A., Pokrovskiy, A., and Sudakov, B., *forthcoming*.
-/

open SimpleGraph Finset

namespace Erdos65

/--
Erdős Problem #65 (Erdős–Hajnal) [GKS84] [LiMo20]:
Let $G$ be a graph with $n$ vertices and $kn$ edges, and let $a_1 < a_2 < \cdots$ be the
distinct lengths of cycles in $G$. Is it true that $\sum 1/a_i \gg \log k$? Is the sum
$\sum 1/a_i$ minimised when $G$ is a complete bipartite graph?

The first question was proved by Gyárfás, Komlós, and Szemerédi [GKS84].
Liu and Montgomery [LiMo20] proved the asymptotically sharp lower bound
$\geq (1/2 - o(1)) \log k$.

Montgomery, Milojević, Pokrovskiy, and Sudakov [MMPS] showed that for sufficiently large
$k$, the sum is actually maximised by the complete bipartite graph, suggesting the original
minimisation conjecture is false.

The remaining open question is formalized below: for any graph $G$ on $n$ vertices whose edge
count equals $a \cdot b$ for some partition $a + b = n$, the sum of reciprocals of distinct cycle
lengths of $G$ is at least the corresponding sum for the complete bipartite graph $K_{a,b}$.
-/
@[category research open, AMS 5]
theorem erdos_65 : answer(sorry) ↔
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (a b : ℕ), a + b = n →
      ∀ [DecidableRel G.Adj], a * b = G.edgeFinset.card →
      ∀ (T_G : Finset ℕ),
        (↑T_G : Set ℕ) = Erdos751.cycleLengths G →
        ∀ (T_K : Finset ℕ),
          (↑T_K : Set ℕ) = Erdos751.cycleLengths (completeBipartiteGraph (Fin a) (Fin b)) →
          ∑ m ∈ T_K, (1 / (m : ℝ)) ≤ ∑ m ∈ T_G, (1 / (m : ℝ)) := by
  sorry

end Erdos65
