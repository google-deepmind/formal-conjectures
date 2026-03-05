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
# Erdős Problem 583

*Reference:* [erdosproblems.com/583](https://www.erdosproblems.com/583)

Every connected graph on $n$ vertices can be partitioned into at most $\lceil n/2 \rceil$
edge-disjoint paths.

[ErGa59] Erdős, P. and Gallai, T., *On the minimal number of vertices representing the
edges of a graph*, 1959.
-/

open SimpleGraph

namespace Erdos583

/--
Erdős Problem 583 [ErGa59]:

Every connected graph on $n$ vertices can be partitioned into at most $\lceil n/2 \rceil$
edge-disjoint paths.
-/
@[category research open, AMS 5]
theorem erdos_583 (n : ℕ) (G : SimpleGraph (Fin n))
    (dG : DecidableRel G.Adj) (hconn : G.Connected) :
    haveI := dG
    ∃ (k : ℕ) (paths : Fin k → Σ (v w : Fin n), G.Walk v w),
      k ≤ (n + 1) / 2 ∧
      (∀ i, (paths i).2.2.IsPath) ∧
      (∀ i j : Fin k, i ≠ j →
        Disjoint (paths i).2.2.edges.toFinset (paths j).2.2.edges.toFinset) ∧
      (∀ e, e ∈ G.edgeFinset ↔ ∃ i, e ∈ (paths i).2.2.edges.toFinset) := by
  sorry

end Erdos583
