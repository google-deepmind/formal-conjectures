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
# Erdős Problem 719

*References:*
- [erdosproblems.com/719](https://www.erdosproblems.com/719)
-/

namespace Erdos719

open Filter Asymptotics

/--
Let $r\geq 2$, and let $\mathrm{ex}_r(n;K_{r+1}^r)$ be the maximum number of $r$-edges that can
be placed on $n$ vertices without forming a $K_{r+1}^r$ (the $r$-uniform complete graph on
$r+1$ vertices). Is every
$r$-hypergraph $G$ on $n$ vertices the union of at most $\mathrm{ex}_{r}(n;K_{r+1}^r)$ many copies
of $K_r^r$ and $K_{r+1}^r$, no two of which share a $K_r^r$?
-/
@[category research open, AMS 5]
theorem erdos_719 :
    answer(sorry) ↔ ∀ r : ℕ, 2 ≤ r → ∀ (n : ℕ) (H : Finset (Finset (Fin n))),
    H.IsUniform r → ∃ D : Finset (Finset (Fin n)),
      H.IsCompleteHypergraphDecomposition r D ∧
        D.card ≤ Hypergraph.cliqueExtremalNumber n r (r + 1) := by
  sorry

end Erdos719
