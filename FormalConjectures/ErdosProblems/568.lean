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
# Erdős Problem 568

*References:*
- [erdosproblems.com/568](https://www.erdosproblems.com/568)
- [EFRS93] Erdős, P. and Faudree, R. J. and Rousseau, C. C. and Schelp, R. H., Ramsey size linear
  graphs. Combin. Probab. Comput. (1993), 389-399.
-/

namespace Erdos568

/--
Let $G$ be a graph such that $R(G,T_n)\ll n$ for any tree $T_n$ on $n$ vertices and
$R(G,K_n)\ll n^2$. Is it true that, for any $H$ with $m$ edges and no isolated vertices,
$$R(G,H)\ll m?$$

In other words, is $G$ Ramsey size linear?

This problem is #17 in Ramsey Theory in the graphs problem collection.
-/
@[category research open, AMS 5]
theorem erdos_568 : answer(sorry) ↔
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (∃ c₁ > (0 : ℝ), ∀ (n : ℕ) (T : SimpleGraph (Fin n)),
        T.IsTree → (SimpleGraph.graphRamsey G T : ℝ) ≤ c₁ * n) →
      (∃ c₂ > (0 : ℝ), ∀ (n : ℕ),
        (SimpleGraph.graphRamsey G (SimpleGraph.completeGraph (Fin n)) : ℝ) ≤ c₂ * (n : ℝ) ^ 2) →
      ∃ c > (0 : ℝ), ∀ (m : ℕ) (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
        (∀ v, 0 < H.degree v) →
        H.edgeSet.ncard = m →
        (SimpleGraph.graphRamsey G H : ℝ) ≤ c * m := by
  sorry

end Erdos568
