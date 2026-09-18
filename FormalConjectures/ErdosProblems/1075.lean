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
# Erdős Problem 1075

*References:*
- [erdosproblems.com/1075](https://www.erdosproblems.com/1075)
- [Er64f] Erdős, P., On extremal problems of graphs and generalized graphs. Israel J. Math. (1964),
  183--190.
-/

namespace Erdos1075

open Filter Asymptotics

/--
Let $r\geq 3$. There exists $c_r>r^{-r}$ such that, for any $\epsilon>0$, if $n$ is sufficiently
large, the following holds. Any $r$-uniform hypergraph on $n$ vertices with at least
$(1+\epsilon)(n/r)^r$ many edges contains a subgraph on $m$ vertices with at least $c_rm^r$ edges,
where $m=m(n)\to \infty$ as $n\to \infty$.
-/
@[category research open, AMS 5]
theorem erdos_1075 :
    ∀ r : ℕ, 3 ≤ r → ∃ c : ℝ, (r : ℝ)⁻¹ ^ r < c ∧
    ∀ ε : ℝ, 0 < ε → ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧
      ∀ᶠ n : ℕ in atTop, ∀ H : Finset (Finset (Fin n)),
        H.IsUniform r → (1 + ε) * ((n : ℝ) / r) ^ r ≤ H.card →
          ∃ S : Finset (Fin n), S.card = m n ∧
            c * (S.card : ℝ) ^ r ≤ (H.hypergraphInduce S).card := by
  sorry

end Erdos1075
