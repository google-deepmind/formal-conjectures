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
# Erdős Problem 628

*Reference:* [erdosproblems.com/628](https://www.erdosproblems.com/628)

Also known as the Erdős–Lovász Tihany conjecture.

[Er68b] Erdős, P., _On chromatic number of graphs and set-systems_ (1968).
-/

open SimpleGraph

namespace Erdos628

/--
Erdős Problem 628 (Erdős–Lovász Tihany Conjecture) [Er68b]:

Let $G$ be a graph with chromatic number $k$ containing no complete graph $K_k$.
If $a, b \geq 2$ and $a + b = k + 1$, then there exist two vertex-disjoint induced
subgraphs of $G$ with chromatic numbers $\geq a$ and $\geq b$ respectively.
-/
@[category research open, AMS 5]
theorem erdos_628 {V : Type*} (G : SimpleGraph V)
    (k : ℕ) (hk : G.chromaticNumber = k)
    (hclique : G.CliqueFree k)
    (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    ∃ (S T : Set V), Disjoint S T ∧
      (G.induce S).chromaticNumber ≥ a ∧
      (G.induce T).chromaticNumber ≥ b := by
  sorry

end Erdos628
