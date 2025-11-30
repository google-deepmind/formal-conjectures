/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
text

https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 613

*Reference:* [erdosproblems.com/613](https://www.erdosproblems.com/613)
-/

namespace Erdos613

/--
**Erdős Problem 613:**
Let $n \geq 3$ and $G$ be a graph with $\binom{2n+1}{2} - \binom{n}{2} - 1$ edges.
Must $G$ be the union of a bipartite graph and a graph with maximum degree less than $n$?
-/
@[category research open, AMS 05]
theorem erdos_613
    (n : ℕ)
    (hn : n ≥ 3)
    (G : SimpleGraph (Fin (2 * n + 1)))
    (hedges :
      G.edgeFinset.card =
        Nat.choose (2 * n + 1) 2 -
        Nat.choose n 2 - 1) :
    (∃ (B : SimpleGraph (Fin (2 * n + 1)))
       (D : SimpleGraph (Fin (2 * n + 1))),
         B ⊆ G ∧
         D ⊆ G ∧
         B.edgeFinset.card + D.edgeFinset.card = G.edgeFinset.card ∧
         B.IsBipartite ∧
         ∀ v, D.degree v < n)
    ↔ answer(sorry) := by
  sorry

end Erdos613
