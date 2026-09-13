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
# Erdős Problem 922

*Reference:* [erdosproblems.com/922](https://www.erdosproblems.com/922)
-/

open SimpleGraph

namespace Erdos922

/--
Let $k\geq 0$. Let $G$ be a graph such that every subgraph $H$ contains an independent set of size
$\geq (n-k)/2$, where $n$ is the number of vertices of $H$. Must $G$ have chromatic number at most
$k+2$?
-/
@[category research open, AMS 5]
theorem erdos_922 :
    answer(sorry) ↔
      ∀ k : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ (S : Set V),
          ∃ I : Set V, I ⊆ S ∧ G.IsIndepSet I ∧
            ((S.ncard : ℤ) - k) / 2 ≤ I.ncard) →
          G.chromaticNumber ≤ k + 2 := by
  sorry

end Erdos922
