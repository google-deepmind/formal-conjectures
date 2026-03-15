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
# Erdős Problem 88

*Reference:* [erdosproblems.com/88](https://www.erdosproblems.com/88)

Erdős–McKay conjecture (proved by Kwan–Sah–Sauermann–Sawhney): if a graph on $n$ vertices
has no clique or independent set of size $\geq \varepsilon \log n$, then it contains an induced
subgraph with exactly $m$ edges for every $m \leq \delta n^2$.

Conjectured by Erdős and McKay [Er92b][Er95][Er97d]. Proved by
Kwan, Sah, Sauermann, and Sawhney [KSSS22].

[Er92b] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Matematiche (Catania) (1992), 231-240.

[Er95] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
Combinatorics, Paul Erdős is Eighty, vol. 2 (1995).

[Er97d] Erdős, P., _Some of my new and almost new problems and results in
combinatorics and graph theory_ (1997).

[KSSS22] Kwan, M., Sah, A., Sauermann, L., and Sawhney, M.,
_Anticoncentration in Ramsey graphs and a proof of the Erdős–McKay conjecture_,
Forum of Mathematics, Pi (2023).
-/

open SimpleGraph Finset Real

namespace Erdos88

/-- Count edges in the induced subgraph on vertex set $S$:
    the number of pairs $\{u, v\}$ with $u, v \in S$, $u < v$, and $G$ adjacent on $u$ and $v$. -/
def inducedEdgeCount {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/--
Erdős Problem 88 [KSSS22]:
For any $\varepsilon > 0$ there exists $\delta = \delta(\varepsilon) > 0$ such that if $G$ is a
graph on $n$ vertices with no independent set or clique of size $\geq \varepsilon \log n$ then $G$
contains an induced subgraph with exactly $m$ edges for all $m \leq \delta n^2$.

Conjectured by Erdős and McKay.
-/
@[category research solved, AMS 5]
theorem erdos_88 :
    ∀ ε : ℝ, ε > 0 →
      ∃ δ : ℝ, δ > 0 ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (h : DecidableRel G.Adj),
          haveI := h
          G.CliqueFree ⌈ε * Real.log n⌉₊ →
          Gᶜ.CliqueFree ⌈ε * Real.log n⌉₊ →
          ∀ m : ℕ, (m : ℝ) ≤ δ * (n : ℝ) ^ 2 →
            ∃ S : Finset (Fin n), inducedEdgeCount G S = m := by
  sorry

end Erdos88
