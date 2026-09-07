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
# Erdős Problem 569

*References:*
- [erdosproblems.com/569](https://www.erdosproblems.com/569)
- [EFRS93] Erdős, Paul and Faudree, R. J. and Rousseau, C. C. and Schelp, R. H., Ramsey size linear
  graphs. Combin. Probab. Comput. (1993), 389-399.
-/

namespace Erdos569

/--
Let $k\geq 1$. What is the best possible $c_k$ such that
$$R(C_{2k+1},H)\leq c_k m$$
for any graph $H$ on $m$ edges without isolated vertices?

This problem is #34 in Ramsey Theory in the graphs problem collection.
-/
@[category research open, AMS 5]
theorem erdos_569 :
    ∀ (k : ℕ) (hk : 1 ≤ k),
      sInf {c : ℝ | 0 < c ∧
        ∀ (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
          (∀ v, 0 < H.degree v) →
          H.edgeSet.ncard = m →
          (SimpleGraph.graphRamsey (SimpleGraph.cycleGraph (2 * k + 1)) H : ℝ) ≤ c * m} =
            answer(sorry) := by
  sorry

end Erdos569
