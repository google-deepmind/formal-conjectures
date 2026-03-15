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
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem 801

*Reference:* [erdosproblems.com/801](https://www.erdosproblems.com/801)

If a graph on $n$ vertices has no independent set of size $> \sqrt{n}$, then there
exists a set of $\leq \sqrt{n}$ vertices containing $\gg \sqrt{n} \log n$ edges.

[Er79g] Erdős, P., original problem statement (1979).

[Al96b] Alon, N., _Independence numbers of locally sparse graphs and a Ramsey type problem_.
Random Structures & Algorithms **9** (1996), 271–278.
-/

open SimpleGraph Real Classical

namespace Erdos801

/-- The number of edges in the subgraph of $G$ induced by a subset $S$ of vertices,
counted as the number of adjacent pairs $\{u, v\}$ with $u, v \in S$ and $u < v$. -/
noncomputable def inducedEdgeCount {n : ℕ}
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/--
Erdős Problem 801 [Er79g]:

If $G$ is a graph on $n$ vertices with no independent set of size $> \sqrt{n}$,
then there exists a set of $\leq \sqrt{n}$ vertices containing
$\gg \sqrt{n} \log n$ edges.

Formally: there exists a constant $C > 0$ such that for all sufficiently large $n$,
for every graph $G$ on $n$ vertices, if $G$ has no independent set of size
$> \lfloor\sqrt{n}\rfloor$, then there exists a subset $S$ with
$|S| \leq \lfloor\sqrt{n}\rfloor$ and the number of edges in $G[S]$ is at least
$C \cdot \sqrt{n} \cdot \log n$.

Proved by Alon [Al96b].
-/
@[category research solved, AMS 5]
theorem erdos_801 :
    ∃ C : ℝ, 0 < C ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ G : SimpleGraph (Fin n),
    α(G) ≤ Nat.sqrt n →
    ∃ S : Finset (Fin n),
      S.card ≤ Nat.sqrt n ∧
      C * (n : ℝ) ^ ((1 : ℝ) / 2) * Real.log (n : ℝ) ≤
        (inducedEdgeCount G S : ℝ) := by
  sorry

end Erdos801
