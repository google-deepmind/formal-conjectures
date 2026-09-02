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
# Erdős Problem 548

*References:*
- [erdosproblems.com/548](https://www.erdosproblems.com/548)
- [BrDo96] Brandt, Stephan and Dobson, Edward, *The Erdős-Sós conjecture for graphs of girth {$5$}*.
  Discrete Math. (1996), 411-414.
- [Er78] Erdős, Paul, *Problems and results in combinatorial analysis and combinatorial number
  theory*. Proceedings of the Ninth Southeastern Conference on Combinatorics, Graph Theory, and
  Computing (Florida Atlantic Univ., Boca Raton, Fla., 1978) (1978), 29-40.
- [ErGa59] Erdős, P. and Gallai, T., *On maximal paths and circuits of graphs*. Acta Math. Acad.
  Sci. Hungar. (1959), 337-356 (unbound insert).
- [SaWo97] Saclé, Jean-François and Woźniak, Mariusz, *The Erdős-Sós conjecture for graphs without
  {$C_4$}*. J. Combin. Theory Ser. B (1997), 367-372.
- [WLL00] Wang, Min and Li, Guo-jun and Liu, Ai-de, *A result of Erdős-Sós conjecture*. Ars Combin.
  (2000), 123-127.
- [YiLi04] Yin, Jian-hua and Li, Jiong-sheng, *The Erdős-Sós conjecture for graphs whose complements
  contain no {$C_4$}*. Acta Math. Appl. Sin. Engl. Ser. (2004), 397-400.
-/

open SimpleGraph

namespace Erdos548

/--
Let $n\geq k+1$. Every graph on $n$ vertices with at least $\frac{k-1}{2}n+1$ edges contains every tree on $k+1$ vertices.
-/
@[category research open, AMS 5]
theorem erdos_548 :
    ∀ (n k : ℕ), k + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
      ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ) →
        ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained G := by
  sorry

end Erdos548
