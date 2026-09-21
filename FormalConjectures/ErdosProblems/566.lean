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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 566

*References*:
- [erdosproblems.com/566](https://www.erdosproblems.com/566)
- [EFRS93] Erdős, Faudree, Rousseau and Schelp, _Ramsey size linear graphs_.
Combin. Probab. Comput. (1993), 389-399.
-/

@[expose] public section

namespace Erdos566

open SimpleGraph

/--
Let $G$ be such that any subgraph on $k$ vertices has at most $2k-3$ edges.
Is it true that, if $H$ has $m$ edges and no isolated vertices, then $R(G,H) \ll m$?

In other words: if $G$ is sparse (every induced subgraph on $k$ vertices has $≤ 2k-3$ edges),
is $G$ Ramsey size linear?
-/
@[category research open, AMS 5]
theorem erdos_566 : answer(sorry) ↔
    ∀ (p : ℕ) (G : SimpleGraph (Fin p)),
      (∀ S : Finset (Fin p), 2 ≤ S.card → (G.induce S).edgeSet.ncard ≤ 2 * S.card - 3) →
      G.IsRamseySizeLinear := by
  sorry

end Erdos566
