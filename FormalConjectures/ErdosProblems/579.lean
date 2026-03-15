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
# Erdős Problem 579

Erdős, Hajnal, Sós, and Szemerédi [EHSS83] conjectured that for any δ > 0, if n is sufficiently
large and G is a K_{2,2,2}-free graph on n vertices with at least δn² edges, then G contains an
independent set of size linear in n.

Erdős, Hajnal, Sós, and Szemerédi proved the conjecture for δ > 1/8.

Related to Problem 533.

*Reference:* [erdosproblems.com/579](https://www.erdosproblems.com/579)

**References:**

[EHSS83] Erdős, P., Hajnal, A., Sós, V. T., and Szemerédi, E.,
_More results on Ramsey-Turán type problems_. Combinatorica **3** (1983), 69–81.

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
467–478.

[Er91] Erdős, P., _Problems and results in combinatorial number theory_.

[Er93] Erdős, P., _On some of my favourite theorems_. Combinatorics, Paul Erdős is eighty,
Vol. 2 (Keszthely, 1993), 97–132, p.340.
-/

open SimpleGraph

namespace Erdos579

/--
Let $\delta > 0$. If $n$ is sufficiently large and $G$ is a graph on $n$ vertices with no
$K_{2,2,2}$ (the complete tripartite graph with three parts of size $2$, also known as the
octahedron) and at least $\delta n^2$ edges then $G$ contains an independent set of size
$\gg_\delta n$.

A problem of Erdős, Hajnal, Sós, and Szemerédi [EHSS83], who proved this for $\delta > 1/8$.
-/
@[category research open, AMS 5]
theorem erdos_579 :
    ∀ δ : ℝ, 0 < δ →
      ∃ c : ℝ, 0 < c ∧
        ∃ N : ℕ,
          ∀ n : ℕ, N ≤ n →
            ∀ G : SimpleGraph (Fin n),
              ¬(completeEquipartiteGraph 3 2).IsContained G →
              δ * (n : ℝ) ^ 2 ≤ (G.edgeSet.ncard : ℝ) →
                ∃ S : Finset (Fin n),
                  c * (n : ℝ) ≤ (S.card : ℝ) ∧
                  (G.induce (S : Set (Fin n))).CliqueFree 2 := by
  sorry

end Erdos579
