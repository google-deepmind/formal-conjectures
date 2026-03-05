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
# Erdős Problem 922

*Reference:* [erdosproblems.com/922](https://www.erdosproblems.com/922)

Let $k \geq 0$. Let $G$ be a graph such that every subgraph $H$ contains an independent
set of size $\geq (n - k) / 2$, where $n$ is the number of vertices of $H$. Must $G$ have
chromatic number at most $k + 2$?

A question of Erdős and Hajnal [ErHa67b]. This is true, and was proved by
Folkman [Fo70b].
-/

open SimpleGraph

namespace Erdos922

/--
Erdős Problem 922 [ErHa67b]:

If every induced subgraph of $G$ on $n$ vertices has an independent set of
size at least $(n - k) / 2$, then $G$ is $(k + 2)$-colorable.

The condition `2 * T.card + k ≥ S.card` encodes $|T| \geq (|S| - k) / 2$.
-/
@[category research solved, AMS 5]
theorem erdos_922 : answer(True) ↔
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (k : ℕ),
      (∀ S : Finset V, ∃ T : Finset V, T ⊆ S ∧
        (↑T : Set V).Pairwise (fun u v => ¬G.Adj u v) ∧
        2 * T.card + k ≥ S.card) →
      G.Colorable (k + 2) := by
  sorry

end Erdos922
