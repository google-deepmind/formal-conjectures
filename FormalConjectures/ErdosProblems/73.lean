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
# Erdős Problem 73

*References:*
- [erdosproblems.com/73](https://www.erdosproblems.com/73)
- [Re99] Reed, B., A strengthening of Brooks' theorem. J. Combin. Theory Ser. B (1999), 167-173.
-/

namespace Erdos73

/--
Let $k\ge 0$. Let $G$ be a graph such that every subgraph $H$ contains an independent set of size
$\ge (n-k)/2$, where $n$ is the number of vertices of $H$. Must $G$ be the union of a bipartite
graph and $O_k(1)$ many vertices?

This was proved by Reed [Re99].
-/
@[category research solved, AMS 5]
theorem erdos_73 : answer(True) ↔
    ∀ (k : ℕ), ∃ (C : ℕ),
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
        (∀ (S : Finset V), ∃ (I : Finset V), I ⊆ S ∧ (G.induce (I : Set V)).edgeSet = ∅ ∧
          (I.card : ℝ) ≥ (S.card - k : ℝ) / 2) →
        ∃ (D : Finset V), D.card ≤ C ∧
          (G.induce (D : Set V)ᶜ).Colorable 2 := by
  sorry

-- TODO: Add variants of the problem if they exist on the website.

end Erdos73
