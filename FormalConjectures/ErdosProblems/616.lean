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
# Erdős Problem 616

*References:*
- [erdosproblems.com/616](https://www.erdosproblems.com/616)
- [EHT91] Erdős, Paul and Hajnal, András and Tuza, Zsolt, Local constraints ensuring small
  representing sets. J. Combin. Theory Ser. A (1991), 78-84.
-/

namespace Erdos616

open Filter Asymptotics

/--
Let $r\geq 3$. For an $r$-uniform hypergraph $G$ let $\tau(G)$ denote the covering number (or
transversal number), the minimum size of a set of vertices which includes at least one from each
edge in $G$. Determine the best possible $t$ such that, if $G$ is an $r$-uniform hypergraph $G$
where every subgraph $G'$ on at most $3r-3$ vertices has $\tau(G')\leq 1$, we have $\tau(G)\leq t$.
-/
@[category research open, AMS 5]
theorem erdos_616 :
    let f : ℕ → ℕ∞ := answer(sorry)
    ∀ r : ℕ, 3 ≤ r → Hypergraph.localTransversalBound r (3 * r - 3) 1 = f r := by
  sorry

end Erdos616
