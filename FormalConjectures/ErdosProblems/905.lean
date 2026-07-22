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
# Erdős Problem 905

*References:*
- [erdosproblems.com/905](https://www.erdosproblems.com/905)
- [KhNi79] Khadzhiivanov, N. G. and Nikiforov, S. V., *Solution of a problem of P. Erdős about the
  maximum number of triangles with a common edge in a graph*. C. R. Acad. Bulgare Sci. (1979),
  1315-1318.
-/

namespace Erdos905

open Finset

/-- The triangles of `G` containing the edge `e`, that is, the `3`-cliques of `G` whose vertex
set contains both endpoints of `e`. -/
def trianglesContaining {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e : Sym2 (Fin n)) : Finset (Finset (Fin n)) :=
  (G.cliqueFinset 3).filter (fun t ↦ e.toFinset ⊆ t)

/--
Every graph with $n$ vertices and $>n^2/4$ edges contains an edge which is in at least $n/6$
triangles.

A conjecture of Bollobás and Erdős. This was proved independently by Edwards (unpublished) and
Khadzhiivanov and Nikiforov [KhNi79].
-/
@[category research solved, AMS 5]
theorem erdos_905 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) :
    ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(trianglesContaining G e) : ℝ) := by
  sorry

end Erdos905
