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
# Erdős Problem 546

*References:*
- [erdosproblems.com/546](https://www.erdosproblems.com/546)
- [Su11] Sudakov, B., A conjecture of Erdős on graph Ramsey numbers. Adv. Math. (2011), 3148-3155.
- [AKS03] Alon, N., Krivelevich, M. and Sudakov, B., Turán numbers of bipartite graphs and Ramsey
  graphs of bounded degree. Combin. Probab. Comput. (2003), 477-483.
-/

namespace Erdos546

/--
Let $G$ be a graph with no isolated vertices and $m$ edges. Is it true that
$$R(G) \leq 2^{O(m^{1/2})}?$$

This is true, and was proved by Sudakov [Su11].
-/
@[category research solved, AMS 5]
theorem erdos_546 : answer(True) ↔
    ∃ C > (0 : ℝ), ∀ (m : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v, 0 < G.degree v) →
      G.edgeSet.ncard = m →
      (SimpleGraph.diagonalGraphRamsey G : ℝ) ≤ 2 ^ (C * Real.sqrt m) := by
  sorry

-- TODO: Add variants of the problem if they exist on the website.

end Erdos546
