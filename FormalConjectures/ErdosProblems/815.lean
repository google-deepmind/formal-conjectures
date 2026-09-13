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
# Erdős Problem 815

*Reference:* [erdosproblems.com/815](https://www.erdosproblems.com/815)
-/

open Filter SimpleGraph
open scoped Topology

namespace Erdos815

/--
Let $k\geq 3$ and $n$ be sufficiently large. Is it true that if $G$ is a graph with $n$ vertices
and $2n-2$ edges such that every proper induced subgraph has minimum degree $\leq 2$ then $G$
must contain a copy of $C_k$?
-/
@[category research open, AMS 5]
theorem erdos_815 :
    answer(sorry) ↔
      ∀ k ≥ 3, ∀ᶠ n : ℕ in atTop,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          G.edgeSet.ncard = 2 * n - 2 →
            (∀ S : Set (Fin n), S ≠ Set.univ →
              ∀ v ∈ S, (G.neighborSet v ∩ S).ncard ≤ 2) →
              (cycleGraph k).IsContained G := by
  sorry

end Erdos815
