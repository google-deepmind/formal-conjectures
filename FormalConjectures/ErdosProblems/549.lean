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
# Erdős Problem 549

*References:*
- [erdosproblems.com/549](https://www.erdosproblems.com/549)
- [Bu74] Burr, S. A., Generalized Ramsey theory for graphs—a survey. Graphs and combinatorics
  (Proc. Capital Conf., George Washington Univ., Washington, D.C., 1973) (1974), 52-75.
- [GHK79] Grossman, J. W., Harary, F. and Klawe, M., Generalized Ramsey theory for graphs. X.
  Double stars. Discrete Math. (1979), 273-283.
-/

namespace Erdos549

/--
If $T$ is a tree which is a bipartite graph with $k$ vertices in one class and $2k$ vertices
in the other class then
$$R(T)=4k-1.$$

This conjecture was disproved by Grossman, Harary, and Klawe [GHK79], who showed that for double
stars $S_{t_1, t_2}$ with $t_1 \ge 3t_2 - 2$, $R(T) = 2t_1$.
-/
@[category research solved, AMS 5]
theorem erdos_549 : answer(False) ↔
    ∀ (k : ℕ) (hk : 2 ≤ k) (T : SimpleGraph (Fin k ⊕ Fin (2 * k))),
      T.IsTree →
      (∀ x₁ x₂, ¬ T.Adj (Sum.inl x₁) (Sum.inl x₂)) →
      (∀ y₁ y₂, ¬ T.Adj (Sum.inr y₁) (Sum.inr y₂)) →
      SimpleGraph.diagonalGraphRamsey T = 4 * k - 1 := by
  sorry

end Erdos549
