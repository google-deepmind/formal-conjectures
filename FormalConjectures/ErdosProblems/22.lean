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

open SimpleGraph

/-!
# Erdős Problem 22

*Reference:* [erdosproblems.com/22](https://www.erdosproblems.com/22)

Let $\varepsilon > 0$ and $n$ be sufficiently large depending on $\varepsilon$. Is there a graph on
$n$ vertices with $\geq n^2/8$ many edges which contains no $K_4$ such that the largest
independent set has size at most $\varepsilon n$?

Equivalently: $\mathrm{rt}(n; 4, \varepsilon n) \geq n^2/8$ for sufficiently large $n$, where
$\mathrm{rt}(n; k, \ell)$ is the Ramsey–Turán number.

Conjectured by Bollobás and Erdős [BoEr76], who proved the existence of such a graph with
$(1/8 + o(1))n^2$ many edges. Proved by Fox, Loh, and Zhao [FLZ15], who showed that for every
$n \geq 1$ there exists a $K_4$-free graph on $n$ vertices with $\geq n^2/8$ edges and
independence number $\ll (\log \log n)^{3/2} / (\log n)^{1/2} \cdot n$.

[BoEr76] Bollobás, B. and Erdős, P., _On a Ramsey–Turán type problem_, J. Combin. Theory Ser. B, 1976.

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
467-478.

[FLZ15] Fox, J., Loh, P.-S., and Zhao, Y., _The critical window for the classical Ramsey–Turán problem_, Combinatorica, 2015.

See also Erdős Problem 615.
-/

namespace Erdos22

/--
**Erdős Problem 22** (Bollobás–Erdős Conjecture on Ramsey–Turán numbers,
proved by Fox, Loh, and Zhao [FLZ15]):

For every $\varepsilon > 0$, for all sufficiently large $n$, there exists a graph $G$ on $n$
vertices such that:
- $G$ has at least $n^2/8$ edges,
- $G$ contains no $K_4$ (no clique of size 4),
- every independent set in $G$ has size at most $\varepsilon \cdot n$.
-/
@[category research solved, AMS 5]
theorem erdos_22 : answer(True) ↔
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ G : SimpleGraph (Fin n),
          (n : ℝ) ^ 2 / 8 ≤ (G.edgeFinset.card : ℝ) ∧
          G.CliqueFree 4 ∧
          (∀ s : Finset (Fin n), G.IsIndepSet ↑s → (s.card : ℝ) ≤ ε * (n : ℝ)) := by
  sorry

end Erdos22
