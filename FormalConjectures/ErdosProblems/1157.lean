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
# Erdős Problem 1157

*References:*
- [erdosproblems.com/1157](https://www.erdosproblems.com/1157)
- [BES73] Brown, W. G. and Erdős, P. and S\'os, V. T., Some extremal problems on {$r$}-graphs.
(1973), 53--63.
-/

namespace Erdos1157

open Filter Asymptotics

/--
Let $s,k,r\geq 2$. Let $\mathcal{F}$ be the family of all $r$-uniform hypergraphs with $k$ vertices
and $s$ edges. Determine
$$\mathrm{ex}_r(n,\mathcal{F}).$$
-/
@[category research open, AMS 5]
theorem erdos_1157 :
    let f : ℕ → ℕ → ℕ → ℕ → ℕ := answer(sorry)
    ∀ r k s : ℕ, 2 ≤ r → 2 ≤ k → 2 ≤ s → ∀ n : ℕ,
      Hypergraph.configurationExtremalNumber n r k s = f n r k s := by
  sorry

end Erdos1157
