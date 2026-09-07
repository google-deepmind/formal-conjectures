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
# Erdős Problem 86

*References:*
- [erdosproblems.com/86](https://www.erdosproblems.com/86)
- [BHLL14] Balogh, József and Hu, Ping and Lidický, Bernard and Liu, Hong, *Upper bounds on the size
  of 4- and 6-cycle-free subgraphs of the hypercube*. European J. Combin. (2014), 75-85.
- [BHN95] Brass, Peter and Harborth, Heiko and Nienborg, Hauke, *On the maximum number of edges in a
  {$C_4$}-free subgraph of {$Q_n$}*. J. Graph Theory (1995), 17--23.
- [Ba12b] R. Baber, *Turán densities of hypercubes*. arXiv:1201.3587 (2012).
- [Er91] Erdős, P., *Problems and results in combinatorial analysis and combinatorial number
  theory*. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397-406.
-/

open Filter SimpleGraph

namespace Erdos86

/--
Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has $2^n$ vertices and $n2^{n-1}$ edges). Is it true that every subgraph of $Q_n$ with $$\geq \left(\frac{1}{2}+o(1)\right)n2^{n-1}$$ many edges contains a $C_4$?
-/
@[category research open, AMS 5]
theorem erdos_86 : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ H : SimpleGraph (Fin n → Bool),
      H ≤ hypercube n →
        (1 / 2 + ε) * n * 2 ^ (n - 1 : ℕ) ≤ (H.edgeSet.ncard : ℝ) →
          cycleGraph 4 ⊑ H := by
  sorry

end Erdos86
