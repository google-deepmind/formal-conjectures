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
# Erdős Problem 905

Every graph on $n$ vertices with more than $n^2/4$ edges contains an edge
which is in at least $n/6$ triangles (Bollobás-Erdős conjecture).

*Reference:* [erdosproblems.com/905](https://www.erdosproblems.com/905)
-/

open SimpleGraph Finset

namespace Erdos905

/--
Erdős Problem 905 (Bollobás-Erdős conjecture):
Every graph with $n$ vertices and more than $n^2/4$ edges contains an edge
which is in at least $n/6$ triangles.

A triangle containing edge $\{u, v\}$ corresponds to a common neighbor of $u$ and $v$,
i.e., a vertex $w$ adjacent to both $u$ and $v$.
-/
@[category research open, AMS 5]
theorem erdos_905 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (G.edgeFinset.card : ℝ) > (n : ℝ) ^ 2 / 4 →
    ∃ u v : Fin n, G.Adj u v ∧
      ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) ≥ (n : ℝ) / 6 := by
  sorry

end Erdos905
