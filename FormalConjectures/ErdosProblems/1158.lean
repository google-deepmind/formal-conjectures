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
# Erdős Problem 1158

*References:*
- [erdosproblems.com/1158](https://www.erdosproblems.com/1158)
- [Er64f] Erdős, P., On extremal problems of graphs and generalized graphs. Israel J. Math. (1964),
  183--190.
-/

namespace Erdos1158

open Filter Asymptotics

/--
Let $K_{t}(r)$ be the complete $t$-partite $t$-uniform hypergraph with $r$ vertices in each class.
Is it true that
$$\mathrm{ex}_t(n,K_t(r)) \geq n^{t-r^{1-t}-o(1)}$$
for all $t,r\geq 2$? The restriction $r\geq 2$ excludes forbidding a single edge.
-/
@[category research open, AMS 5]
theorem erdos_1158 :
    answer(sorry) ↔ ∀ t r : ℕ, 2 ≤ t → 2 ≤ r →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ ((t : ℝ) - (r : ℝ) ^ (1 - (t : ℝ)) - ε) ≤
        (Hypergraph.partiteExtremalNumber n t r : ℝ) := by
  sorry

end Erdos1158
