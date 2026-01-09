/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 566

Let $G$ be such that any subgraph on $k$ vertices has at most $2k-3$ edges.
Is it true that, if $H$ has $m$ edges and no isolated vertices, then
$$ \hat{r}(G,H) \ll m? $$

In other words, is $G$ Ramsey size linear?

*Reference:* [erdosproblems.com/566](https://www.erdosproblems.com/566)

[EFRS93] Erdős, Faudree, Rousseau and Schelp, _Ramsey size linear graphs_.
Combin. Probab. Comput. (1993), 389-399.
-/

namespace Erdos566

open SimpleGraph

/--
**Erdős Problem 566**

Let $G$ be such that any subgraph on $k$ vertices has at most $2k-3$ edges.
Is it true that, if $H$ has $m$ edges and no isolated vertices, then $\hat{r}(G,H) \ll m$?

In other words: if $G$ is sparse (every induced subgraph on $k$ vertices has $≤ 2k-3$ edges),
is $G$ Ramsey size linear?
-/
@[category research open, AMS 05]
theorem erdos_566 : answer(sorry) ↔
    ∀ (p : ℕ) (G : SimpleGraph (Fin p)),
      -- G is sparse: every induced subgraph on k ≥ 2 vertices has ≤ 2k - 3 edges
      (∀ S : Finset (Fin p), 2 ≤ S.card → (G.induce S).edgeSet.ncard ≤ 2 * S.card - 3) →
      -- Then G is Ramsey size linear
      ∃ c > (0 : ℝ), ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
        -- H has no isolated vertices
        (∀ v, 0 < H.degree v) →
        -- r̂(G,H) ≤ c · m
        (sizeRamsey G H : ℝ) ≤ c * H.edgeSet.ncard := by
  sorry

end Erdos566
